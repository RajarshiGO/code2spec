(* File: src/pprint.ml *)
open Format
open Ast

(* Flag to control standard output. 
   True: Only emit the final JSON result. 
   False: Emit CLI info logs and debug prints. *)
let api_mode = ref false

let rec pp_basetype ppf = function
  | RInt -> fprintf ppf "int"
  | RBool -> fprintf ppf "bool"
  | RUserType s -> fprintf ppf "%s" s
  | RVar s -> fprintf ppf "'%s" s
  | RArrow (t1, t2) -> 
      fprintf ppf "@[<hov 2>(%a@ -> %a)@]" pp_basetype t1 pp_basetype t2

let pp_binop ppf = function
  | Add -> fprintf ppf "+" | Sub -> fprintf ppf "-" 
  | Mul -> fprintf ppf "*" | Div -> fprintf ppf "/"
  | Eq -> fprintf ppf "="  | Neq -> fprintf ppf "<>" 
  | Lt -> fprintf ppf "<"  | Le -> fprintf ppf "<=" 
  | Gt -> fprintf ppf ">"  | Ge -> fprintf ppf ">="
  | And -> fprintf ppf "&&"| Or -> fprintf ppf "||"
  | Implies -> fprintf ppf "=>" | Iff -> fprintf ppf "<=>"

let rec pp_expr ppf = function
  | EInt i -> fprintf ppf "%d" i
  | EBool b -> fprintf ppf "%b" b
  | EVar s -> fprintf ppf "%s" s
  | EBinOp (op, e1, e2) -> 
      fprintf ppf "@[<hov 2>(%a@ %a@ %a)@]" pp_expr e1 pp_binop op pp_expr e2
  | EIf (c, t, e) -> 
      fprintf ppf "@[<hov 2>if %a@ then %a@ else %a@]" pp_expr c pp_expr t pp_expr e
  | EFun (x, e) -> 
      fprintf ppf "@[<hov 2>fun %s ->@ %a@]" x pp_expr e
  | EApp (e1, e2) -> 
      fprintf ppf "@[<hov 2>%a@ %a@]" pp_expr e1 pp_expr e2
  | ELet (x, e1, e2) -> 
      fprintf ppf "@[<v>let %s = %a in@,%a@]" x pp_expr e1 pp_expr e2
  | ELetRec (f, x, e1, e2) -> 
      fprintf ppf "@[<v>let rec %s %s = %a in@,%a@]" f x pp_expr e1 pp_expr e2
  | ECtor (c, args) ->
      if args = [] then fprintf ppf "%s" c
      else 
        fprintf ppf "@[<hov 2>%s(@,%a)@]" c 
          (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ",@ ") pp_expr) args
  | EMatch (e, cases) ->
      let pp_case ppf (c, vars, body) =
        let vars_str = if vars = [] then "" else "(" ^ String.concat ", " vars ^ ")" in
        fprintf ppf "@[<hov 2>| %s%s ->@ %a@]" c vars_str pp_expr body
      in
      fprintf ppf "@[<v 2>match %a with@,%a@]" 
        pp_expr e (pp_print_list ~pp_sep:pp_force_newline pp_case) cases
  | EAnnot (e, t) -> 
      fprintf ppf "@[<hov 2>(%a@ : %a)@]" pp_expr e pp_basetype t
  | EForall (vs, e) -> 
      fprintf ppf "@[<hov 2>(forall %s,@ %a)@]" (String.concat " " vs) pp_expr e

(* API-compliant logging helper *)
let log_info fmt =
  if not !api_mode then Printf.printf ("[Info] " ^^ fmt ^^ "\n")
  else Printf.ifprintf stdout fmt

(* Exposed string converters *)
let string_of_basetype ty = asprintf "%a" pp_basetype ty
let string_of_expr e = asprintf "%a" pp_expr e