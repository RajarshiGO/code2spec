(* liquid_test.ml
   Sections 1–4 (AST, Lexer, Parser) are removed.
   We now use Parser_frontend.parse_program which runs OCaml's
   own type inference and returns a typed Ast.decl list.        *)

open Ast

(* ================================================================
   5. Semantic Flow Graph Generation
   ================================================================ *)

type node_kind =
  | ExprNode
  | VarNode
  | MetaNode
  | UnkTypeNode
  | UnkRefNode
  | KnownTypeNode
  | OpNode
  | LitNode

type edge_kind =
  | ExprEdge
  | TypeEdge
  | RefEdge
  | VarEdge

let counter = ref 0
let fresh_name prefix =
  incr counter;
  prefix ^ "_" ^ string_of_int !counter

let string_of_binop = function
  | Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/"
  | Eq  -> "=" | Neq -> "<>"
  | Lt  -> "<" | Gt  -> ">" | Le  -> "<=" | Ge  -> ">="
  | And -> "&&" | Or -> "||"

let string_of_unop = function
  | Neg -> "-"
  | Not -> "not"

let rec string_of_expr_debug e =
  match e with
  | EAnnot (e, _)       -> string_of_expr_debug e          (* strip silently *)
  | EVar x              -> x
  | EInt i              -> string_of_int i
  | EApp (f, a)         -> Printf.sprintf "APP(%s, %s)" (string_of_expr_debug f) (string_of_expr_debug a)
  | ECtor (n, args)     -> Printf.sprintf "%s(%s)" n (String.concat "," (List.map string_of_expr_debug args))
  | EMatch (e, cases)   ->
      let cs = List.map (fun (c,_,body) ->
        Printf.sprintf "%s→%s" c (string_of_expr_debug body)) cases in
      Printf.sprintf "MATCH(%s,[%s])" (string_of_expr_debug e) (String.concat "|" cs)
  | EBinOp (_, e1, e2)  -> Printf.sprintf "BOP(%s,%s)" (string_of_expr_debug e1) (string_of_expr_debug e2)
  | EUnop (op, e) -> Printf.sprintf "UNOP(%s,%s)" (string_of_unop op) (string_of_expr_debug e)
  | EFun (p, body)      -> Printf.sprintf "FUN(%s,%s)" p (string_of_expr_debug body)
  | _                   -> "?"

let rec normalize_expr e =
  let is_stdlib_neg v =
    v = "Stdlib.~-" || v = "~-" || v = "Stdlib.(-)" in
  let norm = normalize_expr in
  match e with
  (* EApp(Stdlib.~-, arg)  →  EUnop(Neg, arg)  — handles EAnnot wrapping *)
  | EApp (f, arg) ->
      let rec unwrap_var e = match e with
        | EAnnot (e, _) -> unwrap_var e
        | EVar v -> Some v
        | _ -> None
      in
      (match unwrap_var f with
       | Some v when is_stdlib_neg v -> EUnop (Neg, norm arg)
       | _ -> EApp (norm f, norm arg))
  | EAnnot (e, t)              -> EAnnot (norm e, t)
  | EBinOp (op, e1, e2)        -> EBinOp (op, norm e1, norm e2)
  | EUnop (op, e)              -> EUnop (op, norm e)
  | EIf (c, t, el)             -> EIf (norm c, norm t, norm el)
  | EFun (p, e)                -> EFun (p, norm e)
  | ELet (x, rhs, body)        -> ELet (x, norm rhs, norm body)
  | ELetRec (f, p, rhs, body)  -> ELetRec (f, p, norm rhs, norm body)
  | ECtor (c, args)            -> ECtor (c, List.map norm args)
  | EMatch (e, cases)          ->
      EMatch (norm e,
              List.map (fun (c, vars, body) -> (c, vars, norm body)) cases)
  | EForall (vs, e)            -> EForall (vs, norm e)
  | e                          -> e

let normalize_decl = function
  | DLet (f, ps, body)              -> DLet (f, ps, normalize_expr body)
  | DType _ as d                    -> d

let generate_flow_graph decls =
  let decls = List.map normalize_decl decls in
  let nodes = ref [] in
  let edges = ref [] in

  let add_node id kind label =
    if not (List.exists (fun (i, _, _) -> i = id) !nodes) then
      nodes := (id, kind, label) :: !nodes
  in
  let add_edge from_id to_id kind =
    if not (List.exists (fun (f, t, k) ->
        f = from_id && t = to_id && k = kind) !edges)
    then
      edges := (from_id, to_id, kind) :: !edges
  in

  (* ── Type node helpers ───────────────────────────────────────────────
     type_node_of_name: always a KnownTypeNode (int, bool, tree, etc.)
     type_node_of_basetype: converts Ast.basetype to a graph node ID
       RInt / RBool / RUserType → KnownTypeNode
       RVar "'a"               → UnkTypeNode  (the type variable itself)
       RArrow                  → "" (function types have no graph node)
  ─────────────────────────────────────────────────────────────────── *)
  let type_node_of_name name =
    let t_id = "type_" ^ name in
    add_node t_id KnownTypeNode name;
    t_id
  in

  let rec type_node_of_basetype bt =
    match bt with
    | RInt        -> type_node_of_name "int"
    | RBool       -> type_node_of_name "bool"
    | RUserType s -> type_node_of_name s
    | RVar s      ->
        (* Type variable from inference, e.g. "'a" → UnkTypeNode labelled "'a" *)
        let clean = String.map (fun c -> if c = '\'' then '_' else c) s in
        let t_id  = "tvar_" ^ clean in
        add_node t_id UnkTypeNode s;
        t_id
    | RTyCon (name, args) ->
          let container_id = type_node_of_name name in
          List.iter (fun arg_bt ->
            let arg_id = type_node_of_basetype arg_bt in
            if arg_id <> "" && arg_id <> container_id then
              add_edge arg_id container_id TypeEdge
          ) args;
          container_id
    | RArrow _    -> ""
  in

  (* ── Build ctor_map from DType declarations ───────────────────────────
     Maps constructor name → (return_type_name, arg_basetypes)
     e.g. "Node" → ("tree", [RInt; RUserType "tree"; RUserType "tree"])
     These come directly from OCaml's typed AST — no token scanning needed.
  ─────────────────────────────────────────────────────────────────── *)
  let ctor_map =
    List.fold_left (fun acc decl ->
      match decl with
      | DType (type_name, ctors) ->
          List.fold_left (fun acc (ctor_name, arg_bts) ->
            (ctor_name, (type_name, arg_bts)) :: acc
          ) acc ctors
      | _ -> acc
    ) [] decls
  in

  (* Register KnownTypeNode for every declared return type *)
  List.iter (fun (_, (ret_type, _)) ->
    ignore (type_node_of_name ret_type)
  ) ctor_map;

  let seen_type_edges = Hashtbl.create 16 in
    List.iter (fun (_, (type_name, arg_bts)) ->
      let ret_id = type_node_of_name type_name in
      List.iter (fun bt ->
        let arg_id = type_node_of_basetype bt in
        if arg_id <> "" && arg_id <> ret_id then begin
          let key = (arg_id, ret_id) in
          if not (Hashtbl.mem seen_type_edges key) then begin
            Hashtbl.add seen_type_edges key ();
            add_edge arg_id ret_id TypeEdge          (* int → tree, etc. *)
          end
        end
      ) arg_bts
    ) ctor_map;

  (* ── register_var ────────────────────────────────────────────────────
       phi_x → x  [RefEdge]
       type_id → x [TypeEdge]   (type → var direction)
  ─────────────────────────────────────────────────────────────────── *)
  let register_var x type_id =
    let phi_node = "phi_" ^ x in
    add_node x        VarNode    x;
    add_node phi_node UnkRefNode phi_node;
    add_edge x phi_node RefEdge;
    if type_id <> "" then add_edge type_id x TypeEdge;
    x
  in

  (* ── Constructor type lookups ────────────────────────────────────── *)
  let get_return_type ctor_name =
    match List.assoc_opt ctor_name ctor_map with
    | Some (ret_type, _) -> type_node_of_name ret_type
    | None               -> ""
  in

  let get_arg_type ctor_name i =
    match List.assoc_opt ctor_name ctor_map with
    | Some (_, arg_bts) ->
        (match List.nth_opt arg_bts i with
         | Some bt -> type_node_of_basetype bt
         | None    -> "")
    | None -> ""
  in

  (* ── create_nu_phi ───────────────────────────────────────────────────
     Constructor output variable (lives inside ENV):
       phi → nu  [RefEdge]
       c_node → nu  [ExprEdge]
       return_type → nu  [TypeEdge]   ← now from ctor_map, not hardcoded
  ─────────────────────────────────────────────────────────────────── *)
  let create_nu_phi c_node nu_prefix ctor_name =
    let nu_id  = fresh_name nu_prefix in
    let phi_id = "phi_" ^ nu_id in
    add_node nu_id  VarNode    nu_id;
    add_node phi_id UnkRefNode phi_id;
    add_edge nu_id phi_id RefEdge ;
    add_edge c_node nu_id ExprEdge;
    let ret = get_return_type ctor_name in
    if ret <> "" then add_edge ret nu_id TypeEdge
  in

  (* ── Parameter type extraction ───────────────────────────────────────
     parser_frontend wraps function bodies as:
       EAnnot(EFun("t", EAnnot(EFun("accu", body), RArrow(t_accu,t_ret))),
              RArrow(t_t, RArrow(t_accu, t_ret)))
     extract_param_types peels these off to give [(param_name, basetype)].
     get_actual_body strips the EFun/EAnnot wrappers to reach the real body.
  ─────────────────────────────────────────────────────────────────── *)
  let rec extract_param_types expr =
    match expr with
    | EAnnot (EFun (p, inner), RArrow (t_p, _)) ->
        (p, t_p) :: extract_param_types inner
    | EAnnot (inner, _) -> extract_param_types inner
    | _ -> []
  in

  let rec get_actual_body expr =
    match expr with
    | EAnnot (EFun (_, inner), _) -> get_actual_body inner
    | EAnnot (inner, _)           -> get_actual_body inner
    | _                           -> expr
  in

  let rec get_return_basetype expr =
    match expr with
    | EAnnot (EFun (_, inner), RArrow (_, _)) -> get_return_basetype inner
    | EAnnot (_, RArrow (_, ret_ty))          -> ret_ty
    | EAnnot (_, bt)                          -> bt
    | _                                       -> RVar "'a"
  in

  (* ── analyze_expr ────────────────────────────────────────────────────
     Walks the expression and connects its result to output_var.
  ─────────────────────────────────────────────────────────────────── *)
  let rec analyze_expr expr env_node output_var =
    (* Helper: left-associative curried APP chain
        func_node is already in the graph.
        args are applied one at a time, each creating a fresh APP node. *)
    (* let rec apply_curried func_node args =
      match args with
      | [] ->
          add_edge func_node output_var ExprEdge
      | [last] ->
          let app = fresh_name "APP" in
          add_node app MetaNode "APP";
          add_edge func_node app ExprEdge;
          analyze_expr last env_node app;
          add_edge app output_var ExprEdge
      | arg :: rest ->
          let app = fresh_name "APP" in
          add_node app MetaNode "APP";
          add_edge func_node app ExprEdge;
          analyze_expr arg env_node app;
          apply_curried app rest                   (* recurse with APP as new func *)
    in *)

  let rec collect_app_args expr args =
    match expr with
    | EApp (f, a)   -> collect_app_args f (a :: args)
    | EAnnot (e, _) -> collect_app_args e args
    | _             -> (expr, args)
  in

  match expr with

    (* Strip type annotations — type info was used at declaration site *)
    | EAnnot (e, _) ->
        analyze_expr e env_node output_var

    | EVar x ->
      (* Ensure node exists for stdlib builtins e.g. Stdlib.~- *)
      add_node x ExprNode x;
      add_edge x output_var ExprEdge

    | EInt i ->
      let label  = string_of_int i in
      let san    = String.map (fun c -> if c = '-' then 'm' else c) label in
      let lit_id = "lit_int_" ^ san in
      add_node lit_id LitNode label;
      add_edge (type_node_of_name "int") lit_id TypeEdge;
      add_edge lit_id output_var ExprEdge

    | EBool b ->
      let label  = string_of_bool b in
      let lit_id = "lit_bool_" ^ label in
      add_node lit_id LitNode label;
      add_edge (type_node_of_name "bool") lit_id TypeEdge;
      add_edge lit_id output_var ExprEdge

    | EApp _ ->
        let (func, args) = collect_app_args expr [] in
        let app_node = fresh_name "APP" in
        add_node app_node MetaNode "APP";
        analyze_expr func env_node app_node;           (* flat → APP *)
        List.iter (fun arg ->
          analyze_expr arg env_node app_node           (* r → APP, result → APP *)
        ) args;
        add_edge app_node output_var ExprEdge

    | ECtor (name, args) ->
        let ctor_node = fresh_name name in
        add_node ctor_node ExprNode name;
        if args = [] then
          add_edge ctor_node output_var ExprEdge       (* Leaf — no APP needed *)
        else begin
          let app_node = fresh_name "APP" in
          add_node app_node MetaNode "APP";
          add_edge ctor_node app_node ExprEdge;        (* :: → APP *)
          List.iter (fun arg ->
            analyze_expr arg env_node app_node         (* x → APP, accu → APP *)
          ) args;
          add_edge app_node output_var ExprEdge
        end             (* curried: :: applied to x, then accu *)

    | EMatch (scrut, cases) ->
        let match_node = fresh_name "match" in
        add_node match_node ExprNode "match";
        analyze_expr scrut env_node match_node;

        List.iter (fun (ctor_name, arg_names, body) ->
          let case_node  = fresh_name "CASE"      in
          let let_block  = fresh_name "LET_BLOCK" in
          let branch_env = fresh_name "ENV"       in
          add_node case_node  MetaNode "CASE";
          add_node let_block  MetaNode "LET_BLOCK";
          add_node branch_env MetaNode "ENV";

          add_edge case_node  match_node ExprEdge;  (* CASE → match     *)
          add_edge let_block  case_node  ExprEdge;  (* LET_BLOCK → CASE *)
          add_edge branch_env case_node  ExprEdge;  (* ENV → CASE       *)

          if ctor_name <> "_" then begin
            (* Named constructor: create ExprNode → ENV, nu/phi inside ENV *)
            let c_node = fresh_name ctor_name in
            add_node c_node ExprNode ctor_name;
            add_edge c_node branch_env ExprEdge;
            create_nu_phi c_node ("nu_" ^ String.lowercase_ascii ctor_name) ctor_name;
            (* Bind each arg with its known type from ctor_map *)
            List.iteri (fun i arg_name ->
              let type_id = get_arg_type ctor_name i in
              let x_id    = register_var arg_name type_id in
              add_edge c_node x_id ExprEdge
            ) arg_names
          end else
            (* Wildcard/variable pattern — register vars with no type *)
            List.iter (fun name -> ignore (register_var name "")) arg_names;

          analyze_expr body branch_env let_block    (* body → LET_BLOCK *)
        ) cases;

        add_edge match_node output_var ExprEdge     (* match → output   *)

    | EBinOp (op, e1, e2) ->
        (* let op_node  = fresh_name (string_of_binop op) in  (* Creates +_1, +_2, etc. *)
        add_node op_node OpNode (string_of_binop op); *)
        let op_str = string_of_binop op in
        let op_node = "binop_" ^ op_str in
        add_node op_node OpNode op_str;
        let app_node = fresh_name "APP" in
        add_node app_node MetaNode "APP";
        add_edge op_node app_node ExprEdge;            (* > → APP *)
        analyze_expr e1 env_node app_node;             (* x → APP *)
        analyze_expr e2 env_node app_node;             (* y → APP *)
        add_edge app_node output_var ExprEdge            (* curried: op applied to e1, then e2 *)
    (* Not yet expanded in the graph — future work *)
    | EIf (cond, then_e, else_e) ->
        let if_node = fresh_name "IF" in
        add_node if_node ExprNode "IF";

        (* ── THEN branch ─────────────────────────────────────────────
           Condition  x > y  evaluated inside ENV_then               *)
        let case_then  = fresh_name "CASE"      in
        let block_then = fresh_name "LET_BLOCK" in
        let env_then   = fresh_name "ENV"       in
        add_node case_then  MetaNode "CASE";
        add_node block_then MetaNode "LET_BLOCK";
        add_node env_then   MetaNode "ENV";
        add_edge case_then  if_node     ExprEdge;   (* CASE  → IF        *)
        add_edge block_then case_then   ExprEdge;   (* BLOCK → CASE      *)
        add_edge env_then   case_then   ExprEdge;   (* ENV   → CASE      *)
        analyze_expr cond   env_node env_then;      (* x>y   → ENV_then  *)
        analyze_expr then_e env_then block_then;    (* x     → BLOCK     *)

        (* ── ELSE branch ─────────────────────────────────────────────
           Negated condition  x <= y  evaluated inside ENV_else      *)
        let case_else  = fresh_name "CASE"      in
        let block_else = fresh_name "LET_BLOCK" in
        let env_else   = fresh_name "ENV"       in
        add_node case_else  MetaNode "CASE";
        add_node block_else MetaNode "LET_BLOCK";
        add_node env_else   MetaNode "ENV";
        add_edge case_else  if_node     ExprEdge;   (* CASE  → IF        *)
        add_edge block_else case_else   ExprEdge;   (* BLOCK → CASE      *)
        add_edge env_else   case_else   ExprEdge;   (* ENV   → CASE      *)

        (* Negate BinOp operator for the else-branch condition:
           >  → <=,   <  → >=,   >= → <,   <= → >
           =  → <>,   <> → =                        *)
        (* let negate_op = function
          | Gt -> Le  | Lt -> Ge  | Ge -> Lt  | Le -> Gt
          | Eq -> Neq | Neq -> Eq | op -> op
        in
        let rec strip e = match e with EAnnot(e,_) -> strip e | _ -> e in
        let neg_cond = match strip cond with
          | EBinOp (op, e1, e2) -> EBinOp (negate_op op, e1, e2)
          | e                   -> e        (* non-BinOp: same condition *)
        in
        analyze_expr neg_cond env_node env_else;    (* x<=y  → ENV_else  *) *)
        analyze_expr (EUnop (Not, cond)) env_node env_else;
        analyze_expr else_e   env_else block_else;  (* y     → BLOCK     *)

        add_edge if_node output_var ExprEdge

    | ELetRec (fn_name, _param, rhs, body) ->
        (* ── Helper subgraph — mirrors DLet exactly ───────────────────
           The helper gets its own ExprNode, nu/phi, params, LET_BLOCK.
           rhs is the helper's body (wrapped in EAnnot/EFun layers).    *)
        add_node fn_name ExprNode fn_name;

        let nu_fn  = "nu_t_" ^ fn_name in
        let phi_fn = "phi_nu_t_" ^ fn_name in
        add_node nu_fn  VarNode    nu_fn;
        add_node phi_fn UnkRefNode phi_fn;
        add_edge nu_fn phi_fn RefEdge;
        add_edge fn_name nu_fn VarEdge;

        let ret_bt  = get_return_basetype rhs in
        let ret_tid = type_node_of_basetype ret_bt in
        if ret_tid <> "" then add_edge ret_tid nu_fn TypeEdge;

        let helper_block = fresh_name "LET_BLOCK" in
        add_node helper_block MetaNode "LET_BLOCK";
        add_edge helper_block fn_name ExprEdge;

        let param_types = extract_param_types rhs in
        List.iter (fun (p, bt) ->
          let type_id = type_node_of_basetype bt in
          let p_id    = register_var p type_id in
          add_edge p_id fn_name VarEdge
        ) param_types;

        let helper_body = get_actual_body rhs in
        analyze_expr helper_body ("env_" ^ fn_name) helper_block;

        (* ── Outer body — fn_name is now in scope as an ExprNode ──────
           Any EApp(EVar fn_name, ...) in body creates an APP node that
           connects to the fn_name ExprNode above.                       *)
        analyze_expr body env_node output_var
    | ELet (name, rhs, body) ->
        let param_types = extract_param_types rhs in

        if param_types <> [] then begin
          (* ── Local function definition ──────────────────────────────
             let double x = x * 2 in ...
             Mirrors ELetRec but without self-reference.               *)
          add_node name ExprNode name;

          let nu_fn  = "nu_t_" ^ name in
          let phi_fn = "phi_nu_t_" ^ name in
          add_node nu_fn  VarNode    nu_fn;
          add_node phi_fn UnkRefNode phi_fn;
          add_edge nu_fn   phi_fn  RefEdge;
          add_edge name nu_fn VarEdge;

          let ret_bt  = get_return_basetype rhs in
          let ret_tid = type_node_of_basetype ret_bt in
          if ret_tid <> "" then add_edge ret_tid nu_fn TypeEdge;

          let fn_block = fresh_name "LET_BLOCK" in
          add_node fn_block MetaNode "LET_BLOCK";
          add_edge fn_block name ExprEdge;

          List.iter (fun (p, bt) ->
            let type_id = type_node_of_basetype bt in
            let p_id    = register_var p type_id in
            add_edge p_id name VarEdge
          ) param_types;

          let fn_body = get_actual_body rhs in
          analyze_expr fn_body ("env_" ^ name) fn_block;

          (* Outer body — name is now in scope as an ExprNode *)
          analyze_expr body env_node output_var

        end else begin
          let let_node  = fresh_name "LET"       in
          let block_body = fresh_name "LET_BLOCK" in

          add_node let_node   ExprNode "LET";
          add_node block_body MetaNode "LET_BLOCK";

          let x_type_id = type_node_of_basetype (get_return_basetype rhs) in
          let x_id      = register_var name x_type_id in
          add_edge x_id       let_node  VarEdge;       (* y        → LET       *)
          add_edge block_body let_node  ExprEdge;      (* LET_BLOCK → LET      *)

          analyze_expr rhs  env_node let_node;         (* rhs      → LET       *)
          analyze_expr body env_node block_body;       (* body     → LET_BLOCK *)

          add_edge let_node output_var ExprEdge        (* LET      → output    *)
        end
    | EUnop (Neg, e) ->
        let op_id = "unop_neg" in
        add_node op_id OpNode "-";
        let app_node = fresh_name "APP" in
        add_node app_node MetaNode "APP";
        add_edge op_id app_node ExprEdge;
        analyze_expr e env_node app_node;
        add_edge app_node output_var ExprEdge

    | EUnop (Not, e) ->
        let negate_cmp = function
          | Gt -> Le | Lt -> Ge | Ge -> Lt | Le -> Gt
          | Eq -> Neq | Neq -> Eq | op -> op
        in
        let rec strip_a e = match e with EAnnot (e,_) -> strip_a e | _ -> e in
        (match strip_a e with
         | EBinOp (op, e1, e2) ->
             (* Simplify: not(x > y) → x <= y — keeps graph compact *)
             analyze_expr (EBinOp (negate_cmp op, e1, e2)) env_node output_var
         | _ ->
             let op_id = "unop_not" in
             add_node op_id OpNode "not";
             let app_node = fresh_name "APP" in
             add_node app_node MetaNode "APP";
             add_edge op_id app_node ExprEdge;
             analyze_expr e env_node app_node;
             add_edge app_node output_var ExprEdge)
    | EFun _ | EForall _ -> ()
  in

  (* ── Top-level declarations ────────────────────────────────────────── *)
  List.iter (fun decl ->
    match decl with
    | DLet (fn_name, _params, body_expr) ->

      add_node fn_name ExprNode fn_name;

      (* nu + phi for the function's output type — same structure as nu_leaf/nu_node *)
      let nu_fn  = "nu_t_" ^ fn_name in
      let phi_fn = "phi_nu_t_" ^ fn_name in
      add_node nu_fn  VarNode    nu_fn;
      add_node phi_fn UnkRefNode phi_fn;
      add_edge nu_fn phi_fn RefEdge;               (* phi → nu  [RefEdge]  *)
      add_edge fn_name nu_fn VarEdge;             (* nu  → fn  [VarEdge]  *)

      (* Connect return type → nu_t_flat [TypeEdge] *)
      let ret_bt  = get_return_basetype body_expr in
      let ret_tid = type_node_of_basetype ret_bt in
      if ret_tid <> "" then add_edge ret_tid nu_fn TypeEdge;

      let let_block = fresh_name "LET_BLOCK" in
      add_node let_block MetaNode "LET_BLOCK";
      add_edge let_block fn_name ExprEdge;

      let param_types = extract_param_types body_expr in
      List.iter (fun (p, bt) ->
        let type_id = type_node_of_basetype bt in
        let p_id    = register_var p type_id in
        add_edge p_id fn_name VarEdge
      ) param_types;

      let actual_body = get_actual_body body_expr in
      analyze_expr actual_body ("env_" ^ fn_name) let_block

    | DType _ -> ()   (* Already consumed into ctor_map above *)
  ) decls;

  (!nodes, List.rev !edges)


(* ================================================================
   6. Main Execution
   ================================================================ *)

let read_file filename =
  let ic  = open_in filename in
  let len = in_channel_length ic in
  let s   = really_input_string ic len in
  close_in ic; s

let string_of_node_kind = function
  | ExprNode      -> "exp"
  | VarNode       -> "var"
  | MetaNode      -> "ast"
  | UnkTypeNode   -> "type"
  | UnkRefNode    -> "ref"
  | KnownTypeNode -> "type"
  | OpNode        -> "op"
  | LitNode       -> "lit"


let string_of_edge_kind = function
  | ExprEdge -> "exp"
  | TypeEdge -> "type"
  | RefEdge  -> "ref"
  | VarEdge  -> "var"

let escape_json_string s =
  let buf = Buffer.create (String.length s) in
  String.iter (function
    | '"'  -> Buffer.add_string buf "\\\""
    | '\\' -> Buffer.add_string buf "\\\\"
    | '\n' -> Buffer.add_string buf "\\n"
    | '\r' -> Buffer.add_string buf "\\r"
    | '\t' -> Buffer.add_string buf "\\t"
    | '\b' -> Buffer.add_string buf "\\b"
    | '\x0C' -> Buffer.add_string buf "\\f"
    | c -> Buffer.add_char buf c
  ) s;
  Buffer.contents buf

let export_graph_to_json filename nodes edges =
  let oc = open_out filename in
  Printf.fprintf oc "{\n  \"nodes\": [\n";
  
  (* Format Nodes *)
  let node_strs = List.map (fun (id, kind, label) ->
    let display_label =
      if String.length label >= 4 && String.sub label 0 4 = "nu_t"
      then "v"
      else label
    in
    Printf.sprintf "    { \"id\": \"%s\", \"kind\": \"%s\", \"label\": \"%s\" }"
      (escape_json_string id)
      (escape_json_string (string_of_node_kind kind))
      (escape_json_string display_label)
  ) nodes in
  Printf.fprintf oc "%s\n  ],\n" (String.concat ",\n" node_strs);

  (* Format Edges *)
  Printf.fprintf oc "  \"edges\": [\n";
  let edge_strs = List.map (fun (from_id, to_id, kind) ->
    Printf.sprintf "    { \"source\": \"%s\", \"target\": \"%s\", \"kind\": \"%s\" }"
      (escape_json_string from_id)
      (escape_json_string to_id)
      (escape_json_string (string_of_edge_kind kind))
  ) edges in
  Printf.fprintf oc "%s\n  ]\n}\n" (String.concat ",\n" edge_strs);
  
  close_out oc;
  Printf.printf "Graph successfully exported to %s\n" filename

let process_file input =
  (* Real OCaml HM type inference via parser_frontend *)
  let decls = Parser_frontend.parse_program input in
  List.iter (fun decl ->
    match decl with
    | DLet (name, _, body) ->
        Printf.eprintf "[AST] %s = %s\n" name (string_of_expr_debug body)
    | _ -> ()
  ) decls;
  
  let (nodes, edges) = generate_flow_graph decls in

  (* Export to JSON instead of printing to console *)
  let output_filename = "flow_graph.json" in
  export_graph_to_json output_filename nodes edges ;

  Printf.printf "=== SEMANTIC FLOW GRAPH ===\n\n";
  Printf.printf "--- Nodes ---\n";
  List.iter (fun (id, kind, label) ->
    let display_label =
      if String.length label >= 4 && String.sub label 0 4 = "nu_t"
      then "v"
      else label
    in
    Printf.printf "%s\tID:%s\tLabel:%s\n" (string_of_node_kind kind) id display_label
  ) nodes;

  Printf.printf "\n--- Edges ---\n";
  List.iter (fun (from_id, to_id, kind) ->
    Printf.printf "%s -> %s [%s]\n" from_id to_id (string_of_edge_kind kind)
  ) edges

let () =
  let argc = Array.length Sys.argv in
  if argc < 2 then
    failwith "Usage: ./liquid_test <mode=api> <file.ml> OR ./liquid_test <file.ml>"
  else
    let is_api_mode  = (Sys.argv.(1) = "api") in
    let filename_idx = if is_api_mode then 2 else 1 in
    if filename_idx >= argc then
      failwith "Error: No input file provided."
    else
      let input = read_file Sys.argv.(filename_idx) in
      if is_api_mode then
        process_file input
      else begin
        Printf.printf "Input:\n%s\n\n" input;
        process_file input
      end
