(* ============================================================================ *)
(* NEW AST: With Embedded Base Types *)
(* File: src/ast.ml *)
(* ============================================================================ *)

(* Base types (OCaml types) *)
type basetype =
  | RInt
  | RBool
  | RUserType of string  (* For user-defined ADTs *)
  | RVar of string       (* For polymorphism: 'a *)
  | RArrow of basetype * basetype (* Function type *)
  | RTyCon    of string * basetype list

(* Binary operators *)
type binop =
  | Add | Sub | Mul | Div
  | Eq | Neq | Lt | Le | Gt | Ge
  | And | Or

type unop =
  | Neg   (* arithmetic negation: -x *)
  | Not
(* Expressions with embedded base types *)
(* Every node carries its OCaml base type *)
type expr =
  (* Constants *)
  | EInt of int
  | EBool of bool
  | EUnop of unop * expr

  (* Variables *)
  | EVar of string

  (* Operations *)
  | EBinOp of binop * expr * expr
  | EIf of expr * expr * expr

  (* Functions *)
  | EFun of string * expr  (* lambda x. e *)
  | EApp of expr * expr    (* e1 e2 *)

  (* Bindings *)
  | ELet of string * expr * expr
  | ELetRec of string * string * expr * expr

  (* ADTs / Pattern Matching *)
  | ECtor of string * expr list        (* C(e1, e2) *)
  | EMatch of expr * (string * string list * expr) list
    (* match e with | C(x1..xn) -> e_branch *)

  (* Annotated expression wrapper *)
  (* Allows us to attach types to any node without rewriting every constructor *)
  | EAnnot of expr * basetype
  | EForall of string list * expr

(* Top-level declarations *)
type declaration =
  | DLet of string * string list * expr  (* let f x y = e *)
  | DType of string * (string * basetype list) list (* type t = | C of int ... *)

type program = declaration list

(* --- Helper Functions --- *)

(* Get the type of an expression if annotated, or guess RInt as fallback *)
(* In the new system, parser should wrap almost everything in EAnnot *)
let rec get_type (e : expr) : basetype =
  match e with
  | EAnnot (_, t) -> t
  | EInt _ -> RInt
  | EBool _ -> RBool
  | EBinOp (op, _, _) ->
      (match op with
       | Add | Sub | Mul | Div -> RInt
       | _ -> RBool)
  | EIf (_, t, _) -> get_type t (* Assume branches match *)
  | EUnop (Neg, _) -> RInt
  | EUnop (Not, _) -> RBool
  | _ -> RInt (* Fallback/Unknown *)

(* Strip annotations to get raw expression *)
let rec strip_annot (e : expr) : expr =
  match e with
  | EAnnot (e', _) -> strip_annot e'
  | EBinOp (op, e1, e2) -> EBinOp (op, strip_annot e1, strip_annot e2)
  | EIf (c, t, e) -> EIf (strip_annot c, strip_annot t, strip_annot e)
  | EFun (x, e) -> EFun (x, strip_annot e)
  | EApp (e1, e2) -> EApp (strip_annot e1, strip_annot e2)
  | ELet (x, e1, e2) -> ELet (x, strip_annot e1, strip_annot e2)
  | ELetRec (f, x, e1, e2) -> ELetRec (f, x, strip_annot e1, strip_annot e2)
  | ECtor (c, args) -> ECtor (c, List.map strip_annot args)
  | EForall (vs, e) -> EForall (vs, strip_annot e)
  | EUnop (op, e) -> EUnop (op, strip_annot e)
  | EMatch (e, cases) ->
      EMatch (strip_annot e,
              List.map (fun (c, vars, body) -> (c, vars, strip_annot body)) cases)
  | e -> e

(* Pretty printer for types *)
let rec string_of_basetype = function
  | RInt -> "int"
  | RBool -> "bool"
  | RUserType s -> s
  | RVar s -> s
  | RArrow (t1, t2) ->
      Printf.sprintf "(%s -> %s)" (string_of_basetype t1) (string_of_basetype t2)
  | RTyCon (s, args) ->
      s ^ " " ^ String.concat " " (List.map string_of_basetype args)

(* Pretty printer for expressions (simplified) *)
let rec string_of_expr e =
  match e with
  | EAnnot (e, t) -> Printf.sprintf "(%s : %s)" (string_of_expr e) (string_of_basetype t)
  | EInt i -> string_of_int i
  | EBool b -> string_of_bool b
  | EVar s -> s
  | EBinOp (_, e1, e2) -> Printf.sprintf "(%s op %s)" (string_of_expr e1) (string_of_expr e2)
  | EUnop (Neg, e) -> Printf.sprintf "(-%s)" (string_of_expr e)
  | EUnop (Not, e) -> Printf.sprintf "(not %s)" (string_of_expr e)
  | EForall (vs, e) ->
      Printf.sprintf "(forall %s, %s)"
        (String.concat " " vs) (string_of_expr e)
  | _ -> "expr"
