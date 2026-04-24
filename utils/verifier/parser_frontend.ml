(* ============================================================================ *)
(* PARSER WITH TYPES - Extract Real Argument Names (OCaml 5.2 compatible) *)
(* ============================================================================ *)

open Ast
open Typedtree
open Types

let verbose = false
let log fmt = Printf.ksprintf (fun s -> if verbose then print_string s) fmt

exception ParseError of string

(* --- Helper: Extract Base Type from OCaml's Types.type_expr --- *)

type ocaml_type_summary =
  | OTInt
  | OTBool
  | OTArrow of ocaml_type_summary * ocaml_type_summary
  | OTVar of string
  | OTUser of string

let rec extract_type_summary (ty : Types.type_expr) =
  match Types.get_desc ty with
  | Tconstr (path, [], _) ->
      begin match Path.name path with
      | "int" -> OTInt
      | "bool" -> OTBool
      | name -> OTUser name
      end
  | Tconstr (path, _, _) -> OTUser (Path.name path)
  | Tarrow (_, t1, t2, _) -> OTArrow (extract_type_summary t1, extract_type_summary t2)
  | Tvar (Some name) -> OTVar name
  | Tvar None -> OTVar "'a"
  | Tlink ty' -> extract_type_summary ty'
  | Tsubst (ty', _) -> extract_type_summary ty'
  | _ -> OTInt

let rec summary_to_ast (s : ocaml_type_summary) : Ast.basetype =
  match s with
  | OTInt -> RInt
  | OTBool -> RBool
  | OTUser s -> RUserType s
  | OTVar s -> RVar s
  | OTArrow (t1, t2) -> RArrow (summary_to_ast t1, summary_to_ast t2)

let get_ast_type (ty : Types.type_expr) : Ast.basetype =
  summary_to_ast (extract_type_summary ty)

let strip_stdlib_prefix (name : string) : string =
  if String.length name > 7 && String.sub name 0 7 = "Stdlib." then
    String.sub name 7 (String.length name - 7)
  else
    name

(* --- Helper: Extract Parameter Names from function_param --- *)

let extract_param_name (fp : Typedtree.function_param) : string =
  Ident.name fp.fp_param


let rec extract_param_names_from_body (body : Typedtree.function_body) : string list =
  match body with
  | Tfunction_body expr ->
      (* Check if body is itself a function *)
      begin match expr.exp_desc with
      | Texp_function (params, inner_body) ->
          List.map extract_param_name params @ extract_param_names_from_body inner_body
      | _ -> []
      end
  | Tfunction_cases _ -> []

let extract_param_names (texp : Typedtree.expression) : string list =
  match texp.exp_desc with
  | Texp_function (params, body) ->
      let param_names = List.map extract_param_name params in
      let rest_params = extract_param_names_from_body body in
      param_names @ rest_params
  | _ -> []

(* --- Translation with EAnnot --- *)

let rec translate_expr (texp : Typedtree.expression) : Ast.expr =
  let base_ty = get_ast_type texp.exp_type in

  let raw_expr = match texp.exp_desc with
  | Texp_constant (Const_int i) -> EInt i

  | Texp_ident (path, _, _) ->
    let name = strip_stdlib_prefix (Path.name path) in
      if name = "true" then EBool true
      else if name = "false" then EBool false
      else EVar name

  | Texp_construct ({txt = Lident "true"; _}, _, _) -> EBool true
  | Texp_construct ({txt = Lident "false"; _}, _, _) -> EBool false

  | Texp_construct ({txt = Lident ctor; _}, _, args) ->
      ECtor (ctor, List.map translate_expr args)

  | Texp_apply (func, [(_, Some arg)]) ->
      begin match func.exp_desc with
      | Texp_ident (path, _, _) ->
          let op_name = strip_stdlib_prefix (Path.name path) in
          if op_name = "~-" then
            (* Transform -e into 0 - e *)
            EBinOp (Sub, EInt 0, translate_expr arg)
          else
            EApp (translate_expr func, translate_expr arg)
      | _ ->
          EApp (translate_expr func, translate_expr arg)
      end

  (* Special-case built-in binary operators *)
  | Texp_apply ({exp_desc = Texp_ident (path, _, _); _}, [(_, Some e1); (_, Some e2)])
    when
      let op_base = strip_stdlib_prefix (Path.name path) in
      List.mem op_base ["+"; "-"; "*"; "="; "<"; ">"; "<="; ">="; "<>"; "!="; "&&"; "||"; "==>"; "<==>"]
    ->
      let op_base = strip_stdlib_prefix (Path.name path) in
      let op = match op_base with
        | "+" -> Add | "-" -> Sub | "*" -> Mul
        | "==>" -> Implies
        | "<==>" -> Iff  (* Mapping the double implication operator *)
        | "=" -> Eq | "<>" | "!=" -> Neq
        | "<" -> Lt | ">" -> Gt | "<=" -> Le | ">=" -> Ge
        | "&&" -> And | "||" -> Or
        | _ -> Add
      in
      EBinOp (op, translate_expr e1, translate_expr e2)

  | Texp_apply (f, args) ->
      let func = translate_expr f in
      List.fold_left (fun acc (_, arg_opt) ->
        match arg_opt with
        | Some arg -> EApp (acc, translate_expr arg)
        | None -> acc
      ) func args

  | Texp_function (params, body) ->
      let param_names = List.map extract_param_name params in
      let body_expr = match body with
        | Tfunction_body expr -> translate_expr expr
        | Tfunction_cases _ -> EInt 0
      in

      (* Extract parameter AND return types *)
      let rec extract_param_and_return_types ty count =
        match ty, count with
        | ret_ty, 0 -> ([], ret_ty)  (* Base case: return the final return type *)
        | RArrow(t_param, t_rest), n ->
            let (rest_params, final_ret) = extract_param_and_return_types t_rest (n - 1) in
            (t_param :: rest_params, final_ret)
        | _ -> (List.init count (fun _ -> RVar "'a"), RVar "'a")
      in

      let (param_types, return_ty) = extract_param_and_return_types base_ty (List.length param_names) in

      (* Debug *)
      List.iter2 (fun pname pty ->
        log "[Parser] Parameter '%s' has type: %s\n" pname (Pprint.string_of_basetype pty)
      ) param_names param_types;

      (* Build nested EFun with individual annotations *)
      let rec build_nested params_with_types ret_ty =
        match params_with_types with
        | [] -> body_expr
        | (pname, pty) :: rest ->
            let inner = build_nested rest ret_ty in
            (* Use ret_ty for the innermost, otherwise extract from arrow *)
            let inner_ty = if rest = [] then ret_ty else get_type inner in
            EAnnot(EFun(pname, inner), RArrow(pty, inner_ty))
      in

      let nested = build_nested (List.combine param_names param_types) return_ty in
      nested


  | Texp_let (Nonrecursive, [{vb_pat; vb_expr; _}], body) ->
      let name = match vb_pat.pat_desc with
        | Tpat_var (id, _, _) -> Ident.name id
        | _ -> "_"
      in
      ELet (name, translate_expr vb_expr, translate_expr body)

  | Texp_let (Recursive, [{vb_pat; vb_expr = _; _}], body) ->
      let f_name = match vb_pat.pat_desc with
        | Tpat_var (id, _, _) -> Ident.name id
        | _ -> "_"
      in
      ELetRec (f_name, "x", EInt 0, translate_expr body)

  | Texp_ifthenelse (c, t, Some e) ->
      EIf (translate_expr c, translate_expr t, translate_expr e)

  | Texp_match (scrut, cases, _) ->
      let scrut' = translate_expr scrut in
      let cases' = List.map (fun (case : computation Typedtree.case) ->
        let value_pat_desc = match case.c_lhs.pat_desc with
          | Tpat_value v ->
              let v_public = (v :> value general_pattern) in
              v_public.pat_desc
          | _ -> Tpat_any
        in
        match value_pat_desc with
        | Tpat_construct (_, cd, pats, _) ->
            let ctor = cd.cstr_name in
            let args = List.map (fun p ->
              match p.pat_desc with
              | Tpat_var (id, _, _) -> Ident.name id
              | _ -> "_"
            ) pats in
            (ctor, args, translate_expr case.c_rhs)
        | _ -> ("_", [], translate_expr case.c_rhs)
      ) cases in
      EMatch (scrut', cases')

  | _ -> EInt 0
  in

  match texp.exp_desc with
  | Texp_function _ -> raw_expr  (* Already annotated, don't wrap again *)
  | _ -> EAnnot (raw_expr, base_ty)

(* Top-level items translation *)
let translate_structure_item (item : Typedtree.structure_item) =
  match item.str_desc with
  | Tstr_value (_, [{vb_pat; vb_expr; _}]) ->
      let name = match vb_pat.pat_desc with
        | Tpat_var (id, _, _) -> Ident.name id
        | _ -> "_"
      in

      (* Extract actual parameter names from Texp_function *)
      let args = extract_param_names vb_expr in

      let body_expr = translate_expr vb_expr in
      Some (Ast.DLet (name, args, body_expr))

  | Tstr_type (_, type_decls) ->
      List.fold_left (fun acc tdecl ->
        match tdecl.typ_kind with
        | Ttype_variant constrs ->
            let ctors = List.map (fun cd ->
              let name = cd.cd_name.txt in
              let args = match cd.cd_args with
                | Cstr_tuple core_types -> List.map (fun ct -> get_ast_type ct.ctyp_type) core_types
                | Cstr_record _ -> []
              in
              (name, args)
            ) constrs in
            Some (Ast.DType (tdecl.typ_name.txt, ctors))
        | _ -> acc
      ) None type_decls

  | _ -> None

let init_compiler () =
  Compmisc.init_path ()

let parse_program source =
  try
    init_compiler ();
    let lexbuf = Lexing.from_string source in
    lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname = "input.ml"};

    (* First try parsing as implementation *)
    try
      let parse_tree = Parse.implementation lexbuf in
      Env.reset_cache_toplevel ();
      let env = Compmisc.initial_env () in
      let (typed_str, _, _, _, _) = Typemod.type_structure env parse_tree in
      let items = List.filter_map translate_structure_item typed_str.str_items in

      (* If no items, try as expression *)
      if items = [] then raise Not_found else items
    with
    | Not_found | Syntaxerr.Error _ ->
        (* Try parsing as a single expression *)
        let expr_lexbuf = Lexing.from_string source in
        expr_lexbuf.lex_curr_p <- {expr_lexbuf.lex_curr_p with pos_fname = "expr"};
        let expr_parse_tree = Parse.expression expr_lexbuf in
        let env = Compmisc.initial_env () in
        let typed_expr = Typecore.type_expression env expr_parse_tree in
        let translated_expr = translate_expr typed_expr in
        [Ast.DLet ("main", [], translated_expr)]

  with
  | ParseError _ as e -> raise e
  | Syntaxerr.Error _ -> raise (ParseError "Syntax error in program")
  | Env.Error _ -> raise (ParseError "Environment error")
  | Typemod.Error _ -> raise (ParseError "Type module error")
  | Typecore.Error _ -> raise (ParseError "Type core error")
  | e -> raise (ParseError ("Parse error: " ^ Printexc.to_string e))

let parse_expr source =
  try
    init_compiler ();
    let lexbuf = Lexing.from_string source in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "expr" };
    let parsetree = Parse.expression lexbuf in
    let env = Compmisc.initial_env () in

    (* Use a fresh type variable instead of hardcoded Int *)
    let v_id = Ident.create_local "v" in
    let v_val = {
      val_type = Ctype.newvar ();
      val_kind = Val_reg;
      val_loc = Location.none;
      val_attributes = [];
      val_uid = Uid.internal_not_actually_unique;
    } in
    let env = Env.add_value v_id v_val env in

    let typed = Typecore.type_expression env parsetree in
    translate_expr typed
  with
  | Syntaxerr.Error _ -> raise (ParseError "Syntax error in expression")
  | Env.Error (err) -> raise (ParseError ("Env.Error: " ^ Format.asprintf "%a" Env.report_error err))
  | Typecore.Error (loc, env, err) ->
      raise (ParseError ("Typecore.Error: " ^
        Format.asprintf "%a" Location.print_report (Typecore.report_error env ~loc err)))
  | e -> raise (ParseError ("Expression parse error: " ^ Printexc.to_string e))


(* -------------------------------------------------------------------------- *)
(* Updated parse_spec_string with debug output                                *)
(* -------------------------------------------------------------------------- *)

let parse_spec_with_args (arg_names : string list) (spec_str : string) : Ast.expr =
  let spec_str = String.trim spec_str in
  (* Normalise C‑style != to OCaml <> *)
  let spec_str = Str.global_replace (Str.regexp "!=") "<>" spec_str in
  (* Also normalise unary minus for safety *)
  let spec_str = Str.global_replace (Str.regexp "~-") "-" spec_str in

  if String.length spec_str >= 6 && String.sub spec_str 0 6 = "forall" then begin
    let rest = String.trim (String.sub spec_str 6 (String.length spec_str - 6)) in
    let comma_idx = String.index rest ',' in
    let vars_str = String.sub rest 0 comma_idx in
    let body_str = String.sub rest (comma_idx + 1) (String.length rest - comma_idx - 1) in
    let qvars = String.split_on_char ' ' vars_str
                |> List.map String.trim
                |> List.filter (fun s -> s <> "") in

    let env_source =
      (List.map (fun p -> Printf.sprintf "let %s = 0 in " p) arg_names |> String.concat "")
      ^ (List.map (fun q -> Printf.sprintf "let %s = 0 in " q) qvars |> String.concat "")
    in
    let full_source = env_source ^ "(" ^ body_str ^ ")" in
    let body_expr = parse_expr full_source in
    Ast.EForall (qvars, body_expr)
  end else begin
    let full_source =
      (List.map (fun p -> Printf.sprintf "let %s = 0 in " p) arg_names |> String.concat "")
      ^ "(" ^ spec_str ^ ")"
    in
    parse_expr full_source
  end