(* cex_eval.ml *)
open Yojson.Basic
open Yojson.Basic.Util

(* ── Generic value type ─────────────────────────────────────────────────── *)
type value =
  | VInt     of int
  | VBool    of bool
  | VString  of string
  | VVariant of string * value list
  | VRecord  of (string * value) list
  | VList    of value list
  | VTuple   of value list
  | VUnit
[@@warning "-37"]

type env = (string * value) list

let as_bool = function VBool b -> b | _ -> failwith "expected bool"
let as_int  = function VInt i  -> i | _ -> failwith "expected int"

(* ── Predicates ─────────────────────────────────────────────────────────── *)
let rec mem_bst tree y =
  match tree with
  | VVariant ("Leaf", []) -> false
  | VVariant ("Node", [v; l; r]) ->
    let nv = as_int v in
    if y = nv then true
    else if y < nv then mem_bst l y
    else mem_bst r y
  | VRecord fields ->
    let nv = as_int (List.assoc "v" fields) in
    if y = nv then true
    else if y < nv then mem_bst (List.assoc "left"  fields) y
    else               mem_bst (List.assoc "right" fields) y
  | _ -> failwith "mem_bst: unexpected shape"

let rec mem_list lst y =
  match lst with
  (* 1. Handles native JSON arrays *)
  | VList elements ->
      List.exists (fun v -> as_int v = y) elements

  (* 2. Handles ADT Empty List from Z3 *)
  | VVariant ("|[]|", []) -> false

  (* 3. Handles ADT Cons from Z3 (matching both |::| and ::) *)
  | VVariant ("|::|", [head; tail]) ->
      if as_int head = y then true else mem_list tail y
  | VVariant ("::", [head; tail]) ->
      if as_int head = y then true else mem_list tail y

  | _ -> failwith "mem_list: expected a list variant"


let rec len_list lst =
  match lst with
  (* 1. Handles native JSON arrays *)
  | VList elements -> List.length elements

  (* 2. Handles ADT Empty List from Z3 *)
  | VVariant ("|[]|", []) -> 0

  (* 3. Handles ADT Cons from Z3 (matching both |::| and ::) *)
  | VVariant ("|::|", [_; tail]) -> 1 + len_list tail
  | VVariant ("::", [_; tail]) -> 1 + len_list tail

  | _ -> failwith "len_list: expected a list variant"

let rec len_bst tree =
  match tree with
  | VVariant ("Leaf", []) -> 0
  | VVariant ("Node", [_; l; r]) -> 1 + len_bst l + len_bst r
  | VRecord fields -> 1 + len_bst (List.assoc "left" fields) + len_bst (List.assoc "right" fields)
  | _ -> failwith "len_bst: unexpected shape"

let eval_app name args =
  match name, args with
  | "mem_bst", [tree; VInt y] -> VBool (mem_bst tree y)
  | "mem_list", [lst; VInt y] -> VBool (mem_list lst y)
  | "len_bst", [tree] -> VInt (len_bst tree)
  | "len_list", [lst] -> VInt (len_list lst)
  (* Add other custom predicates here *)
  | _ -> failwith ("Unknown predicate: " ^ name)

(* ── JSON → Env ─────────────────────────────────────────────────────────── *)
(* Parses flat dicts like {"x": "1", "y": "0"} into VInt bindings *)
let rec value_of_json = function
  | `Int i -> VInt i
  | `Bool b -> VBool b
  | `String s ->
      (try VInt (int_of_string s)
       with Failure _ -> VString s)
  | `List l ->
      VList (List.map value_of_json l)
  | `Assoc fields ->
      (* Look for our clean "variant" and "args" keys *)
      (try
        let tag_json = List.assoc "variant" fields in
        let args_json = List.assoc "args" fields in
        match tag_json, args_json with
        | `String tag_name, `List args_list ->
            VVariant (tag_name, List.map value_of_json args_list)
        | _ -> raise Not_found
      with Not_found ->
        VRecord (List.map (fun (k, v) -> (k, value_of_json v)) fields))
  | `Null -> VUnit
  | _ -> VUnit

let env_of_json j =
  j |> Yojson.Basic.Util.to_assoc |> List.map (fun (k, v_json) ->
    (k, value_of_json v_json)
  )

let rec collect_ints v =
  match v with
  | VInt i -> [i]
  | VList l -> List.concat (List.map collect_ints l)
  | VVariant (_, args) -> List.concat (List.map collect_ints args)
  | VRecord fields -> List.concat (List.map (fun (_, v) -> collect_ints v) fields)
  | _ -> []

(* Extract the active domain of integers from the current environment *)
let get_domain env =
  let ints = List.concat (List.map (fun (_, v) -> collect_ints v) env) in
  (* Add 0 as a safe fallback in case the CEX structures are completely empty *)
  let ints = if ints = [] then [0] else ints in
  List.sort_uniq compare ints
(* ── Evaluator ───────────────────────────────────────────────────────────── *)
let rec eval_binop op v1 v2 =
  match op with
  | "add" -> VInt  (as_int v1 + as_int v2)
  | "sub" -> VInt  (as_int v1 - as_int v2)
  | "mul" -> VInt  (as_int v1 * as_int v2)
  | "eq"  -> VBool (v1 = v2)
  | "neq" -> VBool (v1 <> v2)
  | "lt"  -> VBool (as_int v1 < as_int v2)
  | "le"  -> VBool (as_int v1 <= as_int v2)
  | "gt"  -> VBool (as_int v1 > as_int v2)
  | "ge"  -> VBool (as_int v1 >= as_int v2)
  | "+" -> VInt (as_int v1 + as_int v2)
  | "-" -> VInt (as_int v1 - as_int v2)
  | "*" -> VInt (as_int v1 * as_int v2)
  | "/" -> VInt (as_int v1 / as_int v2)
  | _     -> failwith ("Unknown binop: " ^ op)

and eval (env : env) spec =
  match spec |> member "tag" |> to_string with
  | "Forall" ->
        let qvar = spec |> member "qvar" |> to_string in
        let body = spec |> member "body" in
        let domain = get_domain env in

        (* Wrap the native bool result in VBool *)
        VBool (
          List.for_all (fun i ->
            let env_with_qvar = (qvar, VInt i) :: env in
            as_bool (eval env_with_qvar body)
          ) domain
        )
  | "Lit" ->
      let v = spec |> member "val" in
      (match v |> member "type" |> to_string with
       | "int"  -> VInt  (v |> member "val" |> to_int)
       | "bool" -> VBool (v |> member "val" |> to_bool)
       | t -> failwith ("Unknown lit type: " ^ t))
  | "Var" ->
      let name = spec |> member "name" |> to_string in
      (try List.assoc name env
       with Not_found -> failwith ("Unbound variable: " ^ name))
  | "Not" ->
      VBool (not (as_bool (eval env (spec |> member "arg"))))
  | "BinOp" ->
      let op = spec |> member "op" |> to_string in
      let left_ast = spec |> member "left" in
      let right_ast = spec |> member "right" in

      (* Short-circuiting MUST live here inside 'eval' where 'env' is defined *)
      (match op with
       | "and" | "&&" ->
           if as_bool (eval env left_ast) then eval env right_ast else VBool false
       | "or" | "||" ->
           if as_bool (eval env left_ast) then VBool true else eval env right_ast
       | "implies" | "==>" ->
           if not (as_bool (eval env left_ast)) then VBool true else eval env right_ast
       | _ ->
           eval_binop op (eval env left_ast) (eval env right_ast))

  | "ITE" ->
      if as_bool (eval env (spec |> member "cond"))
      then eval env (spec |> member "then")
      else eval env (spec |> member "else")
  | "App" ->
      eval_app
        (spec |> member "name" |> to_string)
        (spec |> member "args" |> to_list |> List.map (eval env))
  | tag -> failwith ("Unknown spec tag: " ^ tag)
(* ── Server loop ─────────────────────────────────────────────────────────── *)
let () =
  try while true do
    let line = input_line stdin in
    if String.length (String.trim line) > 0 then
      (try
        let j   = from_string line in
        let env = env_of_json (j |> member "cex") in
        let res = as_bool (eval env (j |> member "spec")) in
        Printf.printf "%b\n%!" res
      with exn ->
        Printf.printf "error: %s\n%!" (Printexc.to_string exn))
  done with End_of_file -> ()
