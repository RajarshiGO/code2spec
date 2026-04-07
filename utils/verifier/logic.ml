(* ============================================================================ *)
(* LOGIC: Complete Z3 Interface with AST Support *)
(* ============================================================================ *)

open Z3
open Z3.Arithmetic
open Z3.Boolean
open Ast

let z3_ctor_map : (string, Z3.FuncDecl.func_decl) Hashtbl.t = Hashtbl.create 20
let z3_sort_map : (string, Z3.Sort.sort) Hashtbl.t = Hashtbl.create 20
let selector_registry : (string, Z3.FuncDecl.func_decl) Hashtbl.t = Hashtbl.create 20
let uninterpreted_func_map : (string, Z3.FuncDecl.func_decl) Hashtbl.t = Hashtbl.create 10
let registered_functions : (string, Z3.FuncDecl.func_decl) Hashtbl.t = Hashtbl.create 20
let z3_recognizer_map : (string, Z3.FuncDecl.func_decl) Hashtbl.t = Hashtbl.create 20
let shape_pred_registry : (string, Z3.FuncDecl.func_decl) Hashtbl.t = Hashtbl.create 20

type op =
  | Plus | Minus | Mult | Div
  | Eq | Neq | Lt | Le | Gt | Ge
  | And | Or | Implies

type formula =
  | FTrue | FFalse
  | FInt of int
  | FVar of string
  | FBinOp of op * formula * formula
  | FNot of formula
  | FIte of formula * formula * formula
  | FApp of string * formula list
  | FCtor of string * formula list
  | FIsA of string * formula
  | FField of string * int * formula
  | FForall of (string * basetype) list * formula

let binop_to_op = function
  | Add -> Plus | Sub -> Minus | Mul -> Mult | Div -> Div
  | Eq -> Eq | Neq -> Neq | Lt -> Lt | Le -> Le | Gt -> Gt | Ge -> Ge
  | And -> And | Or -> Or
  | Implies -> Implies

let rec subst x replacement f =
  match f with
  | FVar v -> if v = x then replacement else f
  | FBinOp(op, l, r) -> FBinOp(op, subst x replacement l, subst x replacement r)
  | FNot f -> FNot (subst x replacement f)
  | FIte(c, t, e) -> FIte(subst x replacement c, subst x replacement t, subst x replacement e)
  | FCtor(c, args) -> FCtor(c, List.map (subst x replacement) args)
  | FApp(n, args) -> FApp(n, List.map (subst x replacement) args)
  | FIsA(c, e) -> FIsA(c, subst x replacement e)
  | FField(c, i, e) -> FField(c, i, subst x replacement e)
  | FForall(binders, body) ->
      (* Don't substitute if x is captured by this forall's binders *)
      if List.exists (fun (v, _) -> v = x) binders then f
      else FForall(binders, subst x replacement body)
  | _ -> f

(* Convert AST expression to formula *)
let rec expr_to_formula e =
  match strip_annot e with
  | EInt i -> FInt i
  | EBool b -> if b then FTrue else FFalse
  | EVar x -> FVar x
  | EApp(EVar "not", arg) -> FNot (expr_to_formula arg)
  | EBinOp (op, e1, e2) -> FBinOp (binop_to_op op, expr_to_formula e1, expr_to_formula e2)
  | EIf (c, t, e) -> FIte (expr_to_formula c, expr_to_formula t, expr_to_formula e)
  | EApp _ as app ->
      let rec flatten e args =
        match strip_annot e with
        | EApp (f, a) -> flatten f (expr_to_formula a :: args)
        | EVar f -> FApp (f, args)
        | _ -> FApp ("unknown", args)
      in flatten app []
  | ECtor (c, args) -> FCtor (c, List.map expr_to_formula args)
  | EMatch(scrut, cases) ->
    let f_scrut = expr_to_formula scrut in
    let translated = List.map (fun (ctor_name, vars, body) ->
      let is_test = FIsA(ctor_name, f_scrut) in
      let f_body = expr_to_formula body in
      let f_body_subst = List.fold_left (fun b (i, var) ->
        subst var (FField(ctor_name, i, f_scrut)) b
      ) f_body (List.mapi (fun i v -> (i, v)) vars) in
      (is_test, f_body_subst)
    ) cases in
    (match List.rev translated with
      | [] -> FFalse
      | (_, last_body) :: rest ->
          List.fold_right (fun (is_test, body) acc ->
            FIte(is_test, body, acc)
          ) (List.rev rest) last_body)

  | EForall (qvars, body) ->
      FForall (List.map (fun v -> (v, RInt)) qvars,
               expr_to_formula body)
  | _ -> FTrue

let type_to_sort ctx t =
  match t with
  | RInt -> Arithmetic.Integer.mk_sort ctx
  | RBool -> Boolean.mk_sort ctx
  | RUserType name ->
      (try Hashtbl.find z3_sort_map name
       with Not_found -> Arithmetic.Integer.mk_sort ctx)
  | RVar _ -> Arithmetic.Integer.mk_sort ctx
  | RArrow _ -> Arithmetic.Integer.mk_sort ctx

let rec to_z3 ctx var_types f =
  match f with
  | FTrue -> mk_true ctx
  | FFalse -> mk_false ctx
  | FInt i -> Integer.mk_numeral_i ctx i
  | FVar x ->
      let sort =
        match List.assoc_opt x var_types with
        | Some t -> type_to_sort ctx t
        | None -> Arithmetic.Integer.mk_sort ctx
      in
      if Hashtbl.mem z3_ctor_map x then
        Expr.mk_app ctx (Hashtbl.find z3_ctor_map x) []
      else
        Expr.mk_const_s ctx x sort
  | FBinOp (op, l, r) ->
      let l_z3 = to_z3 ctx var_types l in
      let r_z3 = to_z3 ctx var_types r in
      begin match op with
      | Plus -> Arithmetic.mk_add ctx [l_z3; r_z3]
      | Minus -> Arithmetic.mk_sub ctx [l_z3; r_z3]
      | Mult -> Arithmetic.mk_mul ctx [l_z3; r_z3]
      | Div -> Arithmetic.mk_div ctx l_z3 r_z3
      | Eq -> Boolean.mk_eq ctx l_z3 r_z3
      | Neq -> Boolean.mk_not ctx (Boolean.mk_eq ctx l_z3 r_z3)
      | Lt -> Arithmetic.mk_lt ctx l_z3 r_z3
      | Le -> Arithmetic.mk_le ctx l_z3 r_z3
      | Gt -> Arithmetic.mk_gt ctx l_z3 r_z3
      | Ge -> Arithmetic.mk_ge ctx l_z3 r_z3
      | And -> Boolean.mk_and ctx [l_z3; r_z3]
      | Or -> Boolean.mk_or ctx [l_z3; r_z3]
      | Implies -> Boolean.mk_implies ctx l_z3 r_z3
      end
  | FNot f -> Boolean.mk_not ctx (to_z3 ctx var_types f)
  | FIte (c, t, e) ->
      Boolean.mk_ite ctx (to_z3 ctx var_types c) (to_z3 ctx var_types t) (to_z3 ctx var_types e)
  | FCtor (name, args) ->
      let func = Hashtbl.find z3_ctor_map name in
      let z_args = List.map (to_z3 ctx var_types) args in
      Expr.mk_app ctx func z_args
  | FApp(name, args) ->
      let zargs = List.map (to_z3 ctx var_types) args in
      let func =
        if Hashtbl.mem registered_functions name then
          Hashtbl.find registered_functions name
        else if Hashtbl.mem shape_pred_registry name then
          Hashtbl.find shape_pred_registry name
        else if Hashtbl.mem uninterpreted_func_map name then
          Hashtbl.find uninterpreted_func_map name
        else begin
          let domain = List.map Expr.get_sort zargs in
          (* Infer return sort from var_types if available *)
          let range =
            match List.assoc_opt (name ^ "::ret") var_types with
                | Some t -> type_to_sort ctx t
                | None   -> Arithmetic.Integer.mk_sort ctx
          in
          let f = FuncDecl.mk_func_decl_s ctx name domain range in
          Hashtbl.add uninterpreted_func_map name f; f
        end
      in
      Expr.mk_app ctx func zargs
  | FIsA(ctor_name, e) ->
      let recognizer = Hashtbl.find z3_recognizer_map ctor_name in
      Expr.mk_app ctx recognizer [to_z3 ctx var_types e]

  | FField(ctor_name, idx, e) ->
      let acc_name = Printf.sprintf "%s_f%d" ctor_name idx in
      let accessor = Hashtbl.find selector_registry acc_name in
      Expr.mk_app ctx accessor [to_z3 ctx var_types e]
  | FForall (binders, body) ->
      let n = List.length binders in
      let sorts = List.map (fun (_, bt) -> type_to_sort ctx bt) binders in
      (* de Bruijn: binder i (0-indexed from left) → mk_bound (n-1-i) *)
      (* We substitute named vars with their de Bruijn expressions BEFORE
         translating body, so to_z3 sees FVar "u" → looks up in a de-Bruijn
         environment rather than var_types. *)
      let db_env = List.mapi (fun i (name, bt) ->
        (name, (Quantifier.mk_bound ctx (n - 1 - i) (type_to_sort ctx bt), bt))
      ) binders in
      (* Translate body with de Bruijn substitution *)
      let rec to_z3_db env f =
        match f with
        | FVar x ->
            (match List.assoc_opt x env with
             | Some (db_expr, _) -> db_expr
             | None ->
                 let sort = match List.assoc_opt x var_types with
                   | Some t -> type_to_sort ctx t
                   | None   -> Arithmetic.Integer.mk_sort ctx
                 in
                 Expr.mk_const_s ctx x sort)
        | FBinOp (op, l, r) ->
            let l' = to_z3_db env l and r' = to_z3_db env r in
            (match op with   (* same as to_z3's BinOp cases *)
             | Plus -> Arithmetic.mk_add ctx [l'; r']
             | Minus -> Arithmetic.mk_sub ctx [l'; r']
             | Eq -> Boolean.mk_eq ctx l' r'
             | Lt -> Arithmetic.mk_lt ctx l' r'
             | Le -> Arithmetic.mk_le ctx l' r'
             | Gt -> Arithmetic.mk_gt ctx l' r'
             | Ge -> Arithmetic.mk_ge ctx l' r'
             | And -> Boolean.mk_and ctx [l'; r']
             | Or  -> Boolean.mk_or  ctx [l'; r']
             | Implies -> Boolean.mk_implies ctx l' r'
             | _ -> to_z3 ctx var_types f)
        | FNot f' -> Boolean.mk_not ctx (to_z3_db env f')
        | FApp (name, args) ->
            let z_args = List.map (to_z3_db env) args in
            let func =
              if Hashtbl.mem registered_functions name then
                Hashtbl.find registered_functions name
              else if Hashtbl.mem shape_pred_registry name then
                Hashtbl.find shape_pred_registry name
              else if Hashtbl.mem selector_registry name then
                Hashtbl.find selector_registry name
              else begin
                let domain = List.map Expr.get_sort z_args in
                let range = Boolean.mk_sort ctx in
                let f = FuncDecl.mk_func_decl_s ctx name domain range in
                Hashtbl.add uninterpreted_func_map name f; f
              end
            in
            Expr.mk_app ctx func z_args
        | _ -> to_z3 ctx var_types f
      in
      let body_z3 = to_z3_db db_env body in
      let symbols = List.map (fun (name, _) -> Symbol.mk_string ctx name) binders in
      let pattern_terms = (* collect all FApp nodes at top level for triggers *)
        let rec collect_apps acc = function
          | FApp (name, _) as app ->
              if Hashtbl.mem shape_pred_registry name then
                (to_z3_db db_env app) :: acc
              else acc
          | FBinOp (_, l, r) -> collect_apps (collect_apps acc l) r
          | FNot f' -> collect_apps acc f'
          | _ -> acc
        in
        collect_apps [] body
      in
      let patterns = match pattern_terms with
        | [] -> []
        | ts -> [Quantifier.mk_pattern ctx ts]
      in
      Quantifier.expr_of_quantifier
        (Quantifier.mk_forall ctx sorts symbols body_z3 None patterns [] None None)

let expr_to_z3_with_map ctx arg_map f =
  let var_types = arg_map in
  to_z3 ctx var_types f

let rec string_of_formula = function
  | FTrue -> "true"
  | FFalse -> "false"
  | FInt i -> string_of_int i
  | FVar x -> x
  | FBinOp (op, l, r) ->
      let sop = match op with
        | Plus -> "+" | Minus -> "-" | Mult -> "*" | Div -> "/"
        | Eq -> "=" | Neq -> "!=" | Lt -> "<" | Le -> "<=" | Gt -> ">" | Ge -> ">="
        | And -> "&&" | Or -> "||" | Implies -> "=>"
      in
      Printf.sprintf "(%s %s %s)" (string_of_formula l) sop (string_of_formula r)
  | FNot f -> Printf.sprintf "(not %s)" (string_of_formula f)
  | FIte (c, t, e) -> Printf.sprintf "(if %s then %s else %s)" (string_of_formula c) (string_of_formula t) (string_of_formula e)
  | FApp (f, args) ->
      let args_str = String.concat ", " (List.map string_of_formula args) in
      Printf.sprintf "%s(%s)" f args_str
  | FCtor (name, args) ->
      if args = [] then name else
      let args_str = String.concat ", " (List.map string_of_formula args) in
      Printf.sprintf "%s(%s)" name args_str
  | FIsA(c, e) -> Printf.sprintf "(is_%s %s)" c (string_of_formula e)
  | FField(c, i, e) -> Printf.sprintf "(%s_f%d %s)" c i (string_of_formula e)
  | FForall (binders, body) ->
      let binders_str = String.concat " " (List.map fst binders) in
      Printf.sprintf "(forall %s, %s)" binders_str (string_of_formula body)
