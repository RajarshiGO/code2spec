open Ast
open Logic

let verbose = false
let log fmt = Printf.ksprintf (fun s -> if verbose then print_string s) fmt

let name_map : (string, string) Hashtbl.t = Hashtbl.create 50

exception TypeError of string

module StringSet = Set.Make(String)

type verification_result =
  | Valid
  | Invalid of (string * string) list
  | Unknown

type rtyp =
  | RRefined of string * basetype * expr
  | RArrow of string * rtyp * rtyp

type ob_kind =
  | BranchLeaf of string
  | CallSite   of string
  | LetBinding of string
  | ReturnPoint

type proof_obligation = {
  po_id        : int;
  po_label     : string;
  po_path      : Logic.formula;
  po_holds     : Logic.formula;
  po_goal      : Logic.formula;
  po_kind      : ob_kind;
  po_vartypes  : (string * basetype) list;
  po_ret_var   : string;
}

let proof_obligations : proof_obligation list ref = ref []
let spec_check_mode = ref false
let sub_spec_mode : bool ref = ref false
let current_ret_var    = ref "v"
let po_counter = ref 0

let fresh_po_id () =
  incr po_counter;
  !po_counter

type ctx = (string * rtyp) list

let empty_ctx = []

let lookup_ctx ctx x =
  try Some (List.assoc x ctx)
  with Not_found -> None

let add_to_ctx ctx x t = (x, t) :: ctx

let add_path_condition ctx p =
  add_to_ctx ctx "_" (RRefined("_", RBool, p))

type ctor_info = {
  c_name: string;
  c_args: basetype list;
  c_parent: string;
}

let global_ctor_env : (string, ctor_info) Hashtbl.t = Hashtbl.create 20
let global_fn_env : (string, (string * Ast.expr)) Hashtbl.t = Hashtbl.create 20

let register_adt type_name ctors =
  List.iter (fun (name, args) ->
    let info = { c_name = name; c_args = args; c_parent = type_name } in
    Hashtbl.replace global_ctor_env name info
  ) ctors;
  Solver.register_adt type_name ctors

let lookup_global_definition name =
  try Some (Hashtbl.find global_fn_env name)
  with Not_found -> None

let counter = ref 0

let fresh_name prefix =
  incr counter;
  let fresh = prefix ^ (string_of_int !counter) in
  Hashtbl.replace name_map fresh prefix;
  fresh

let rec is_value = function
  | EInt _ | EBool _ | EVar _ -> true
  | ECtor (_, args) -> List.for_all is_value args
  | EAnnot (e, _) -> is_value e
  | _ -> false

let rec typ_to_string_full = function
  | RRefined(v, b, p) ->
      Printf.sprintf "{%s:%s | %s}" v (Pprint.string_of_basetype b) (Pprint.string_of_expr p)
  | RArrow(x, t1, t2) ->
      Printf.sprintf "(%s:%s -> %s)" x (typ_to_string_full t1) (typ_to_string_full t2)

let rec subst_expr x replacement target =
  let target = strip_annot target in
  match target with
  | EVar v -> if v = x then replacement else target
  | EInt _ | EBool _ -> target
  | EBinOp (op, e1, e2) ->
      EBinOp (op, subst_expr x replacement e1, subst_expr x replacement e2)
  | EApp (e1, e2) ->
      EApp (subst_expr x replacement e1, subst_expr x replacement e2)
  | EIf (c, t, e) ->
      EIf (subst_expr x replacement c, subst_expr x replacement t, subst_expr x replacement e)
  | EFun (p, body) ->
      if p = x then target else EFun (p, subst_expr x replacement body)
  | ELet (v, e1, e2) ->
      let e1' = subst_expr x replacement e1 in
      if v = x then ELet (v, e1', e2)
      else ELet (v, e1', subst_expr x replacement e2)
  | ELetRec (f, arg, body, rest) ->
      if f = x || arg = x then target
      else ELetRec (f, arg, subst_expr x replacement body, subst_expr x replacement rest)
  | ECtor (n, args) -> ECtor (n, List.map (subst_expr x replacement) args)
  | EMatch (e, cases) ->
      let e' = subst_expr x replacement e in
      let cases' = List.map (fun (n, vars, body) ->
        if List.mem x vars then (n, vars, body)
        else (n, vars, subst_expr x replacement body)
      ) cases in
      EMatch (e', cases')
  | EAnnot (e, t) -> EAnnot (subst_expr x replacement e, t)
  | EForall (vs, body) ->
      if List.mem x vs then EForall (vs, body)
      else EForall (vs, subst_expr x replacement body)

let extract_path_from_ctx ctx =
  List.fold_left (fun acc (x, t) ->
    match t with
    | RRefined(v, RBool, p) when x = "_" ->
        let f = Logic.expr_to_formula (subst_expr v (EBool true) p) in
        Logic.FBinOp(Logic.And, acc, f)

    | RRefined(v, RInt, p) when p <> EBool true ->
        let f = Logic.expr_to_formula (subst_expr v (EVar x) p) in
        Logic.FBinOp(Logic.And, acc, f)
    | RRefined(v, RUserType _, p) when p <> EBool true ->
        let f = Logic.expr_to_formula (subst_expr v (EVar x) p) in
        Logic.FBinOp(Logic.And, acc, f)
    | _ -> acc
  ) Logic.FTrue ctx

let rec subst_in_type x replacement_expr t =
  match t with
  | RRefined (v, b, p) ->
      let v_fresh = fresh_name "v" in
      let p_renamed = subst_expr v (EVar v_fresh) p in
      RRefined (v_fresh, b, subst_expr x replacement_expr p_renamed)
  | RArrow (param, t_in, t_out) ->
      let t_in' = subst_in_type x replacement_expr t_in in
      if param = x then RArrow (param, t_in', t_out)
      else RArrow (param, t_in', subst_in_type x replacement_expr t_out)

let rec basetype_to_rtyp (bt : basetype) : rtyp =
  match bt with
  | RInt -> RRefined("v", RInt, EBool true)
  | RBool -> RRefined("v", RBool, EBool true)
  | RUserType s -> RRefined("v", RUserType s, EBool true)
  | RVar s -> RRefined("v", RVar s, EBool true)
  | RArrow(t1, t2) ->
      let param = "x" in
      RArrow(param, basetype_to_rtyp t1, basetype_to_rtyp t2)

let expr_to_formula e = Logic.expr_to_formula e

let rec get_free_vars e =
  let e = strip_annot e in
  match e with
  | EVar v -> [v]
  | EInt _ | EBool _ -> []
  | EBinOp(_, l, r) -> (get_free_vars l) @ (get_free_vars r)
  | EIf(c, t, f) -> (get_free_vars c) @ (get_free_vars t) @ (get_free_vars f)
  | EApp(l, r) -> (get_free_vars l) @ (get_free_vars r)
  | ELet(x, rhs, body) ->
      (get_free_vars rhs) @ (List.filter (fun v -> v <> x) (get_free_vars body))
  | EFun(x, body) -> List.filter (fun v -> v <> x) (get_free_vars body)
  | ECtor(_, args) -> List.flatten (List.map get_free_vars args)
  | EMatch(e, cases) ->
      (get_free_vars e) @ List.flatten (List.map (fun (_, vars, body) ->
        List.filter (fun v -> not (List.mem v vars)) (get_free_vars body)
      ) cases)
  | ELetRec(f, arg, body, rest) ->
      let body_fv = List.filter (fun v -> v <> f && v <> arg) (get_free_vars body) in
      let rest_fv = List.filter (fun v -> v <> f) (get_free_vars rest) in
      body_fv @ rest_fv
  | EAnnot (e, _) -> get_free_vars e
  | EForall (vs, body) ->
      List.filter (fun v -> not (List.mem v vs)) (get_free_vars body)


let rec is_pure e =
  let e = strip_annot e in
  match e with
  | EInt _ | EBool _ | EVar _ -> true
  | EBinOp(_, l, r) -> is_pure l && is_pure r
  | EIf(c, t, e) -> is_pure c && is_pure t && is_pure e
  | ECtor(_, args) -> List.for_all is_pure args
  | EApp(EVar f, r) ->

    let is_known = Hashtbl.mem global_fn_env f
                || Hashtbl.mem Logic.registered_functions f
                || Hashtbl.mem Logic.shape_pred_registry f in
    if not is_known then false
    else is_pure (EVar f) && is_pure r
  | EApp(l, r) -> is_pure l && is_pure r
  | EAnnot (e, _) -> is_pure e
  | EMatch(scrut, cases) ->
      is_pure scrut &&
      List.for_all (fun (_, _, body) -> is_pure body) cases
  | EForall (_, body) -> is_pure body
  | _ -> false

let rec extract_equality target_var p =
  let p = strip_annot p in
  match p with
  | EBinOp (Eq, EVar v, e) when v = target_var -> Some e
  | EBinOp (Eq, e, EVar v) when v = target_var -> Some e
  | EBinOp (And, p1, p2) ->
      (match extract_equality target_var p1 with
       | Some e -> Some e
       | None -> extract_equality target_var p2)
  | _ -> None

let join_types t1 t2 =
  match (t1, t2) with
  | (RRefined(_, b1, p1), RRefined(_, b2, p2)) when b1 = b2 ->
      let p1' = subst_expr "v" (EVar "v") p1 in
      let p2' = subst_expr "v" (EVar "v") p2 in
      RRefined("v", b1, EBinOp(Or, p1', p2'))
  | _ -> t1


let clean_z3_value raw_val =
  let s = String.trim raw_val in
  if String.length s > 4
     && s.[0] = '('
     && String.sub s 0 3 = "(- "
     && s.[String.length s - 1] = ')'
  then
    let inner = String.trim (String.sub s 3 (String.length s - 4)) in
    let all_digits str =
      String.length str > 0 &&
      (let ok = ref true in
       String.iter (fun c -> if c < '0' || c > '9' then ok := false) str;
       !ok)
    in
    if all_digits inner then "-" ^ inner else s
  else s

let parse_z3_raw_output input_str =
  let buf = Buffer.create (String.length input_str) in
  let prev_space = ref true in
  String.iter (fun c ->
    if c = ' ' || c = '\n' || c = '\r' || c = '\t' then begin
      if not !prev_space then Buffer.add_char buf ' ';
      prev_space := true
    end else begin
      Buffer.add_char buf c;
      prev_space := false
    end
  ) input_str;
  let norm = Buffer.contents buf in
  let len  = String.length norm in

  let read_token pos =
    if pos >= len then None
    else if norm.[pos] = '(' then begin
      let depth   = ref 0 in
      let in_pipe = ref false in
      let i       = ref pos in
      while !i < len && (!depth > 0 || !i = pos) do
        let c = norm.[!i] in
        if c = '|' then in_pipe := not !in_pipe
        else if not !in_pipe then
          (if c = '(' then incr depth else if c = ')' then decr depth);
        incr i
      done;
      if !depth = 0 then Some (String.sub norm pos (!i - pos), !i)
      else None
    end else begin
      let in_pipe = ref false in
      let i       = ref pos in
      while !i < len &&
            (norm.[!i] <> ' '  || !in_pipe) &&
            (norm.[!i] <> ')'  || !in_pipe) do
        if norm.[!i] = '|' then in_pipe := not !in_pipe;
        incr i
      done;
      if !i > pos then Some (String.sub norm pos (!i - pos), !i)
      else None
    end
  in

  let marker = "define-fun " in
  let mlen   = String.length marker in
  let find_next start =
    let found = ref None in
    let i     = ref start in
    while !found = None && !i + mlen <= len do
      if String.sub norm !i mlen = marker then found := Some !i
      else incr i
    done;
    !found
  in

  let rec loop pos acc =
    match find_next pos with
    | None -> acc
    | Some mpos ->
        let p = ref (mpos + mlen) in
        let name_start = !p in
        while !p < len && norm.[!p] <> ' ' do incr p done;
        let name = String.sub norm name_start (!p - name_start) in
        if !p < len then incr p;
        if !p + 2 <= len && norm.[!p] = '(' && norm.[!p + 1] = ')' then begin
          p := !p + 2;
          if !p < len && norm.[!p] = ' ' then incr p;
          while !p < len && norm.[!p] <> ' ' do incr p done;
          if !p < len && norm.[!p] = ' ' then incr p;
          match read_token !p with
          | Some (raw_value, next_pos) ->
              let value = clean_z3_value raw_value in
              loop next_pos ((name, value) :: acc)
          | None -> loop (mpos + 1) acc
        end else
          loop (mpos + 1) acc
  in
  loop 0 []



let compare_z3_names n1 n2 =
  let len1 = String.length n1 in
  let len2 = String.length n2 in
  if len1 <> len2 then compare len1 len2
  else compare n1 n2

let cex_ctor_head v =
  let v = String.trim v in
  if String.length v = 0 then None
  else if v.[0] = '(' then
    let inner = String.trim (String.sub v 1 (String.length v - 1)) in
    if String.length inner > 0 && inner.[0] = '|' then
      (match String.index_opt (String.sub inner 1 (String.length inner - 1)) '|' with
       | Some i -> Some (String.sub inner 1 i)
       | None   -> None)
    else
      let stop = (try String.index inner ' ' with Not_found -> String.length inner) in
      Some (String.sub inner 0 stop)
  else if String.length v >= 2 && v.[0] = '|' && v.[String.length v - 1] = '|' then
    Some (String.sub v 1 (String.length v - 2))
  else
    Some v

let cex_consistent_with_ctx (ctx : ctx) (cex_list : (string * string) list) : bool =
  let tbl = Hashtbl.create 8 in
  List.iter (fun (k, v) -> Hashtbl.replace tbl k v) cex_list;
  let check_atom p =
    match p with
    | EBinOp(Eq, EVar x, ECtor(expected, _))
    | EBinOp(Eq, ECtor(expected, _), EVar x) ->
        (match Hashtbl.find_opt tbl x with
         | Some cex_val ->
             (match cex_ctor_head cex_val with
              | Some actual -> actual = expected
              | None        -> true)
         | None -> true)
    | _ -> true
  in
  let rec walk p = match p with
    | EBinOp(And, p1, p2) -> walk p1 && walk p2
    | _ -> check_atom p
  in
  List.for_all (fun (_, ty) ->
    match ty with
    | RRefined(_, RBool, p) -> walk p
    | _                     -> true
  ) ctx


let find_ret_var p1 =
  let rec go e = match strip_annot e with
    | EBinOp(Eq, EVar v, _) -> Some v
    | EBinOp(And, e1, _)    -> go e1
    | _                     -> None
  in
  match go p1 with Some v -> v | None -> "v"


let abstract_ho_apps (var_types : (string * basetype) list) (formula : Logic.formula)
    : Logic.formula * (string * basetype) list =
  let ho_vars =
    List.filter_map (fun (k, _) ->
      let suffix = "::ret" in
      let slen = String.length suffix in
      let klen = String.length k in
      if klen > slen && String.sub k (klen - slen) slen = suffix
      then Some (String.sub k 0 (klen - slen))
      else None
    ) var_types
  in
  if ho_vars = [] then (formula, [])
  else begin
    let fresh_map : (string, string) Hashtbl.t = Hashtbl.create 4 in
    let extra_vars = ref [] in
    let rec go = function
      | Logic.FApp(name, args) ->
          let args' = List.map go args in
          let has_ho = List.exists (function
            | Logic.FVar v -> List.mem v ho_vars
            | _ -> false) args' in
          if has_ho then begin
            let key = name ^ "(" ^
              String.concat "," (List.map Logic.string_of_formula args') ^ ")" in
            let fresh_v = match Hashtbl.find_opt fresh_map key with
              | Some v -> v
              | None ->
                  let v = fresh_name "ho" in
                  let sort = match List.assoc_opt (name ^ "::ret") var_types with
                    | Some t -> t | None -> RInt
                  in
                  extra_vars := (v, sort) :: !extra_vars;
                  Hashtbl.add fresh_map key v; v
            in
            Logic.FVar fresh_v
          end else Logic.FApp(name, args')
      | Logic.FBinOp(op, l, r) -> Logic.FBinOp(op, go l, go r)
      | Logic.FNot f            -> Logic.FNot (go f)
      | Logic.FIte(c, t, e)     -> Logic.FIte(go c, go t, go e)
      | Logic.FForall(bvs, b)   -> Logic.FForall(bvs, go b)
      | Logic.FCtor(c, args)     -> Logic.FCtor(c, List.map go args)
      | Logic.FField(c, i, e)    -> Logic.FField(c, i, go e)
      | Logic.FIsA(c, e)         -> Logic.FIsA(c, go e)
      | f -> f
    in
    let f' = go formula in
    (f', !extra_vars)
  end

let abstract_recursive_apps rec_fnames var_types _p1 query =
  if rec_fnames = [] then (query, [])
  else begin
    let app_map : (string, string) Hashtbl.t = Hashtbl.create 4 in
    let extra_vars = ref [] in
    let extra_eqs = ref [] in
    let rec go = function
      | Logic.FApp(f, args) when List.mem f rec_fnames ->
          let args' = List.map go args in
          let key = f ^ "(" ^
            String.concat "," (List.map Logic.string_of_formula args') ^ ")" in
          let fresh_v = match Hashtbl.find_opt app_map key with
            | Some v -> v
            | None ->
                let v = fresh_name "rec" in
                let sort = match List.assoc_opt (f ^ "::ret") var_types with
                  | Some t -> t
                  | None   -> RInt
                in
                extra_vars := (v, sort) :: !extra_vars;
                Hashtbl.add app_map key v;
                v
          in
          let original_app = Logic.FApp(f, args') in
          extra_eqs := Logic.FBinOp(Logic.Eq, Logic.FVar fresh_v, original_app) :: !extra_eqs;
          Logic.FVar fresh_v
      | Logic.FBinOp(op, l, r) -> Logic.FBinOp(op, go l, go r)
      | Logic.FNot f            -> Logic.FNot (go f)
      | Logic.FForall(bvs, b)   -> Logic.FForall(bvs, go b)
      | Logic.FCtor(c, args)    -> Logic.FCtor(c, List.map go args)
      | f -> f
    in
    let query' = go query in
    let query_with_eqs = match query' with
      | Logic.FBinOp(Logic.Implies, antecedent, consequent) ->
          let new_antecedent = List.fold_left (fun acc eq ->
            Logic.FBinOp(Logic.And, acc, eq)) antecedent !extra_eqs
          in
          Logic.FBinOp(Logic.Implies, new_antecedent, consequent)
      | _ -> query'
    in
    (query_with_eqs, !extra_vars)
  end

let check_implication ctx p1 p2 =
  log "[Debug] check_implication: p2 = %s\n" (Pprint.string_of_expr p2);
  let var_types =
      let seen = Hashtbl.create 16 in
      List.filter_map (fun (x, t) ->
        match t with
        | RRefined (_, RBool, _)       -> Some (x, RBool)
        | RRefined (_, RInt, _)        -> Some (x, RInt)
        | RRefined (_, RUserType s, _) -> Some (x, RUserType s)
        | RRefined (_, RVar _, _)      -> Some (x, RInt)
        | RArrow _ as arr ->
            let rec final_ret = function
              | RArrow(_, _, t)          -> final_ret t
              | RRefined(_, RBool, _)    -> Some RBool
              | RRefined(_, RInt, _)     -> Some RInt
              | RRefined(_, RUserType s, _) -> Some (RUserType s)
              | _                        -> None
            in
            (match final_ret arr with
             | Some t -> Some (x ^ "::ret", t)
             | None   -> None)
        | _ -> None
      ) ctx
      |> List.filter (fun (name, _) ->
          if Hashtbl.mem seen name then false
          else (Hashtbl.add seen name (); true))
      |> List.filter (fun (name, _) -> name <> "_")
      |> List.filter (fun (name, _) ->
          not (Hashtbl.mem Logic.registered_functions name))
    in
    if !sub_spec_mode then begin
    if !spec_check_mode then begin
      let path = extract_path_from_ctx ctx in
      let holds = Logic.expr_to_formula p1 in
      proof_obligations := {
        po_id       = fresh_po_id ();
        po_label    = Pprint.string_of_expr p2;
        po_path     = path;
        po_holds    = holds;
        po_goal     = Logic.expr_to_formula p2;
        po_kind     = ReturnPoint;
        po_vartypes = var_types;
        po_ret_var  = !current_ret_var;
      } :: !proof_obligations
    end;
    Valid
  end else begin
    let ctx_formulas = List.map (fun (x, t) ->
      match t with
      | RRefined(v, _, p) -> subst_expr v (EVar x) p |> expr_to_formula
      | _ -> FTrue
    ) ctx in
    let assumption = List.fold_left (fun acc f -> FBinOp(And, acc, f)) FTrue ctx_formulas in
    let p1_logic = expr_to_formula p1 in
    let p2_logic = expr_to_formula p2 in
    let raw_query = FBinOp(Implies, FBinOp(And, assumption, p1_logic), p2_logic) in
    log "[Debug] vartypes before filter: [%s]\n"
      (String.concat "; " (List.map (fun (n, t) -> n ^ ":" ^ Pprint.string_of_basetype t) var_types));
    let var_types = List.filter (fun (name, _) ->
      not (Hashtbl.mem Logic.registered_functions name)
    ) var_types in
    log "[Debug] vartypes after filter: [%s]\n"
      (String.concat "; " (List.map (fun (n, t) -> n ^ ":" ^ Pprint.string_of_basetype t) var_types));
    let query, ho_extras = abstract_ho_apps var_types raw_query in
    let var_types = var_types @ ho_extras in
    let rec_fnames = List.filter_map (fun (k, _) ->
      let s = "::ret" in
      let klen = String.length k and slen = String.length s in
      if klen > slen && String.sub k (klen - slen) slen = s then
        let fname = String.sub k 0 (klen - slen) in
        if Hashtbl.mem global_fn_env fname then Some fname else None
      else None
    ) var_types in
    let query, rec_extras =
      abstract_recursive_apps rec_fnames var_types p1_logic query in
    let var_types = var_types @ rec_extras in
    match Solver.check_validity ~use_fallback:false var_types query with
    | Solver.V_Valid -> Valid
    | Solver.V_Invalid model_msg ->
        let raw_pairs = parse_z3_raw_output model_msg in
        (* Source names of ho/rec auxiliary variables produced by abstraction.
           These are internal to the verifier and must never appear in the CEX
           returned to the caller. *)
        let aux_source_names =
          List.fold_left (fun acc (name, _) ->
            let src = match Hashtbl.find_opt name_map name with
              | Some s -> s | None -> name
            in
            StringSet.add src acc
          ) StringSet.empty (ho_extras @ rec_extras)
        in
        let best_candidates = Hashtbl.create 10 in
        List.iter (fun (fresh_name, value) ->
          let source_name = match Hashtbl.find_opt name_map fresh_name with
            | Some s -> s
            | None -> fresh_name
          in
          match Hashtbl.find_opt best_candidates source_name with
          | None -> Hashtbl.add best_candidates source_name (fresh_name, value)
          | Some (existing_fresh, _) ->
              if compare_z3_names fresh_name existing_fresh < 0 then
                Hashtbl.replace best_candidates source_name (fresh_name, value)
        ) raw_pairs;
        let clean_cex = Hashtbl.fold (fun source_key (_, value) acc ->
          if StringSet.mem source_key aux_source_names then acc
          else (source_key, value) :: acc
        ) best_candidates [] in
        if cex_consistent_with_ctx ctx clean_cex then begin
          log "[CEX] Validated: CEX is consistent with path conditions\n";
          Invalid clean_cex
        end else begin
          log "[CEX] Rejected spurious CEX (contradicts path condition in ctx)\n";
          Unknown
        end
    | Solver.V_Unknown ->
      log "[Solver] Primary unknown → trying grounded fallback...\n";
      let (witness_pairs, p2_grounded) = match strip_annot p2 with
        | EForall(vars, body) ->
          let pairs = List.map (fun v -> (v, fresh_name v)) vars in
          let grounded = List.fold_left
            (fun e (v, w) -> subst_expr v (EVar w) e) body pairs in
          (pairs, grounded)
        | _ -> ([], p2)
      in
      let rec extract_eqs e = match strip_annot e with
        | EBinOp(Eq, EVar x, rhs) -> [(x, rhs)]
        | EBinOp(Eq, rhs, EVar x) -> [(x, rhs)]
        | EBinOp(And, a, b) -> extract_eqs a @ extract_eqs b
        | _ -> []
      in
      let path_eqs = extract_eqs p1 @
        List.concat_map (fun (_, ty) -> match ty with
          | RRefined(v, _, p) -> extract_eqs (subst_expr v (EVar v) p)
          | _ -> []) ctx
      in
      let p2_grounded = List.fold_left
        (fun e (x, rhs) -> subst_expr x rhs e) p2_grounded path_eqs in
      let witness_int_vars = List.filter_map (fun (orig_v, w) ->
        if List.mem_assoc orig_v path_eqs
        then None else Some w) witness_pairs in
      let (p2_final, _) = List.fold_left
      (fun (p, evs) (name, bt) ->
        match bt with
        | RUserType type_name when witness_int_vars <> [] ->
            let nil_ctor_opt = Hashtbl.fold (fun _ info acc ->
              match acc with
              | Some _ -> acc
              | None ->
                  if info.c_parent = type_name
                      && not (List.exists (fun a -> a = RUserType type_name) info.c_args)
                  then Some info.c_name
                  else None
            ) global_ctor_env None in
            let rec_ctor_opt = Hashtbl.fold (fun _ info acc ->
              match acc with
              | Some _ -> acc
              | None ->
                  if info.c_parent = type_name
                      && List.exists (fun a -> a = RUserType type_name) info.c_args
                  then Some info
                  else None
            ) global_ctor_env None in
            (match nil_ctor_opt, rec_ctor_opt with
              | Some nil_name, Some rec_info ->
                  let head = List.hd witness_int_vars in
                  let ctor_args = List.map (fun arg_type ->
                    if arg_type = RInt then EVar head
                    else if arg_type = RUserType type_name then ECtor(nil_name, [])
                    else EVar head
                  ) rec_info.c_args in
                  let concrete = ECtor(rec_info.c_name, ctor_args) in
                  (subst_expr name concrete p, evs)
              | _ -> (p, evs))
        | _ -> (p, evs))
      (p2_grounded, []) var_types
    in
      let p2_logic_final = expr_to_formula p2_final in
      let raw_query_grounded = FBinOp(Implies, FBinOp(And, assumption, p1_logic), p2_logic_final) in
      let extra_vars = List.map (fun (_, w) -> (w, RInt)) witness_pairs in
      let var_types_grounded = var_types @ extra_vars in
      let query_grounded, ho_extras2 = abstract_ho_apps var_types_grounded raw_query_grounded in
      let var_types_grounded = var_types_grounded @ ho_extras2 in
      begin match Solver.check_validity_simple var_types_grounded query_grounded with
        | Solver.V_Valid -> Valid
        | Solver.V_Unknown -> Unknown
        | Solver.V_Invalid model_msg ->
          let raw_pairs = parse_z3_raw_output model_msg in
          (* Exclude auxiliary source names from ho/rec abstraction and the
             grounded ho pass. Witness variables (extra_vars) are intentionally
             kept because they resolve to genuine user-variable source names. *)
          let aux_source_names =
            List.fold_left (fun acc (name, _) ->
              let src = match Hashtbl.find_opt name_map name with
                | Some s -> s | None -> name
              in
              StringSet.add src acc
            ) StringSet.empty (ho_extras @ rec_extras @ ho_extras2)
          in
          let best_candidates = Hashtbl.create 10 in
          List.iter (fun (fresh_name, value) ->
          let source_name = match Hashtbl.find_opt name_map fresh_name with
            | Some s -> s | None -> fresh_name in
          match Hashtbl.find_opt best_candidates source_name with
          | None -> Hashtbl.add best_candidates source_name (fresh_name, value)
          | Some (existing_fresh, _) ->
            if compare_z3_names fresh_name existing_fresh < 0 then
              Hashtbl.replace best_candidates source_name (fresh_name, value)
        ) raw_pairs;
        let clean_cex = Hashtbl.fold
          (fun source_key (_fresh, value) acc ->
            if StringSet.mem source_key aux_source_names then acc
            else (source_key, value) :: acc)
          best_candidates [] in
        if cex_consistent_with_ctx ctx clean_cex then begin
          log "[CEX] Validated: grounded CEX is consistent with path conditions\n";
          Invalid clean_cex
        end else begin
          log "[CEX] Rejected: grounded CEX contradicts path condition in ctx\n";
          Unknown
        end
      end
  end

let rec is_subtype ctx t1 t2 =
  match (t1, t2) with
  | (RRefined(v1, b1, p1), RRefined(v2, b2, p2)) ->
      let bases_compatible = match b1, b2 with
        | RVar _, RVar _ -> true
        | RVar _, _ -> true
        | _, RVar _ -> true
        | _ -> b1 = b2
      in
      if not bases_compatible then
        Invalid [("Error", "Base type mismatch")]
      else
        let p2_renamed = subst_expr v2 (EVar v1) p2 in
        log "[Debug] is_subtype: p1 = %s, p2_renamed = %s\n"
          (Pprint.string_of_expr p1) (Pprint.string_of_expr p2_renamed);
        let ctx' = add_to_ctx ctx v1 (RRefined(v1, b1, p1)) in
        let ctx_enriched = List.fold_left (fun acc_ctx var ->
          match lookup_ctx ctx var with
          | Some (RRefined(_, _, _) as refined_ty) ->
              if not (List.mem_assoc var acc_ctx) then add_to_ctx acc_ctx var refined_ty
              else acc_ctx
          | _ -> acc_ctx
        ) ctx' (get_free_vars p1) in
        current_ret_var := v1;
        check_implication ctx_enriched p1 p2_renamed

  | (RArrow(x1, s1, t1), RArrow(x2, s2, t2)) ->
      begin match is_subtype ctx s2 s1 with
      | Valid ->
          let t1_renamed = subst_in_type x1 (EVar x2) t1 in
          let ctx' = add_to_ctx ctx x2 s2 in
          is_subtype ctx' t1_renamed t2
      | err -> err
      end

  | _ -> Invalid [("Error", "Incompatible type structures")]


let base_type_to_sort_string = function
  | RInt -> "Int"
  | RBool -> "Bool"
  | RUserType s -> s
  | RVar _ -> "Int"
  | RArrow _ -> "Int"

let rec collect_fun_args expr =
  match expr with
  | EAnnot(EFun(arg, body), RArrow(t_arg, _)) ->
      let rest_args, final_body = collect_fun_args body in
      (arg, base_type_to_sort_string t_arg) :: rest_args, final_body
  | EAnnot(inner, _) -> collect_fun_args inner
  | EFun(arg, body) ->
      let rest_args, final_body = collect_fun_args body in
      (arg, "Int") :: rest_args, final_body
  | _ -> [], expr

let get_expr_return_type expr =
  let rec go bt = match bt with
    | Ast.RArrow(_, t2) -> go t2
    | Ast.RInt -> "Int"
    | Ast.RBool -> "Bool"
    | Ast.RUserType s -> s
    | Ast.RVar _ -> "Int"
  in
  match expr with
  | EAnnot(_, ann_ty) -> go ann_ty
  | _ -> "Int"


let register_global_definition ?full_expr ?(axiom_nonneg=false) name initial_arg body_expr =
  Hashtbl.replace global_fn_env name (initial_arg, body_expr);
  let collect_from = match full_expr with
    | Some e -> e
    | None -> EFun(initial_arg, body_expr)
  in
  let (args, final_body) = collect_fun_args collect_from in
  let return_type_str = get_expr_return_type collect_from in
  if is_pure final_body then begin
    log "[Solver] Defining function '%s' in Z3 logic...\n" name;
    Solver.define_function name args return_type_str (fun _z3_vars ->
      let arg_map = List.map (fun (var_name, type_str) ->
        let bt = match type_str with
          | "Int"  -> RInt
          | "Bool" -> RBool
          | s      -> RUserType s
        in (var_name, bt)
      ) args in
      let logic_formula = expr_to_formula final_body in
      Logic.expr_to_z3_with_map Solver.ctx arg_map logic_formula
    );
    if axiom_nonneg then
      Solver.assert_nonneg_axiom name args
  end else
    log "[Solver] Skipping '%s' (impure body)\n" name

let rec ast_substitute var_name replacement expr =
  let expr = strip_annot expr in
  match expr with
  | EVar x -> if x = var_name then replacement else EVar x
  | EApp (f, arg) ->
      EApp (ast_substitute var_name replacement f, ast_substitute var_name replacement arg)
  | EIf (c, t, e) ->
      EIf (ast_substitute var_name replacement c,
           ast_substitute var_name replacement t,
           ast_substitute var_name replacement e)
  | EBinOp (op, e1, e2) ->
      EBinOp (op, ast_substitute var_name replacement e1, ast_substitute var_name replacement e2)
  | ELet (x, e1, e2) ->
      let new_e1 = ast_substitute var_name replacement e1 in
      let new_e2 = if x = var_name then e2 else ast_substitute var_name replacement e2 in
      ELet (x, new_e1, new_e2)
  | EFun (param, body) ->
      if param = var_name then EFun (param, body)
      else EFun (param, ast_substitute var_name replacement body)
  | EInt _ | EBool _ -> expr
  | ECtor (c, args) -> ECtor (c, List.map (ast_substitute var_name replacement) args)
  | EMatch (scrut, cases) ->
      let new_scrut = ast_substitute var_name replacement scrut in
      let new_cases = List.map (fun (c, args, body) ->
        if List.mem var_name args then (c, args, body)
        else (c, args, ast_substitute var_name replacement body)
      ) cases in
      EMatch (new_scrut, new_cases)
  | ELetRec (f, arg, fbody, rest) ->
      if f = var_name || arg = var_name then
        ELetRec (f, arg, fbody, ast_substitute var_name replacement rest)
      else
        ELetRec (f, arg, ast_substitute var_name replacement fbody, ast_substitute var_name replacement rest)
  | EAnnot (e, t) -> EAnnot (ast_substitute var_name replacement e, t)
  | EForall (vs, body) ->
      if List.mem var_name vs then EForall (vs, body)
      else EForall (vs, ast_substitute var_name replacement body)

let rec resolve_function_body expr =
  let expr = strip_annot expr in
  match expr with
  | EFun (param, body) -> Some (param, body)
  | EVar name ->
      begin match lookup_global_definition name with
      | Some (p, b) -> Some (p, b)
      | None -> None
      end
  | EApp (func_expr, arg_expr) ->
      begin match resolve_function_body func_expr with
      | Some (param, body) ->
          let reduced_body = subst_expr param arg_expr body in
          resolve_function_body reduced_body
      | None -> None
      end
  | _ -> None

let value_type_infer ctx e =
  let e = strip_annot e in
  match e with
  | EInt _ -> RRefined("v", RInt, EBinOp(Eq, EVar "v", e))
  | EBool _ -> RRefined("v", RBool, EBinOp(Eq, EVar "v", e))
  | EVar x ->
      begin match List.assoc_opt x ctx with
      | Some t ->
          begin match t with
          | RRefined(_, b, _) -> RRefined("v", b, EBinOp(Eq, EVar "v", EVar x))
          | _ -> t
          end
      | None -> raise (TypeError ("Unbound variable: " ^ x))
      end
  | _ -> raise (TypeError "Not a value")

let rec is_recursive func_name body =
  let body = strip_annot body in
  match body with
  | EVar x -> x = func_name
  | EInt _ | EBool _ -> false
  | EBinOp (_, e1, e2) -> is_recursive func_name e1 || is_recursive func_name e2
  | EIf (c, t, e) -> is_recursive func_name c || is_recursive func_name t || is_recursive func_name e
  | EApp (f, arg) -> is_recursive func_name f || is_recursive func_name arg
  | EFun (_, body) -> is_recursive func_name body
  | ELet (_, e1, e2) -> is_recursive func_name e1 || is_recursive func_name e2
  | ECtor (_, args) -> List.exists (is_recursive func_name) args
  | EMatch (scrut, cases) ->
      is_recursive func_name scrut ||
      List.exists (fun (_, _, body) -> is_recursive func_name body) cases
  | ELetRec (f, _, fbody, rest) ->
      f = func_name || is_recursive func_name fbody || is_recursive func_name rest
  | EAnnot (e, _) -> is_recursive func_name e
  | EForall (_, body) -> is_recursive func_name body


let inlining_stack : string list ref = ref []

let rec specialize_type (ty : rtyp) (type_var : string) (concrete : basetype) : rtyp =
  match ty with
  | RRefined(v, RVar tv, p) when tv = type_var ->
      RRefined(v, concrete, p)
  | RRefined(v, b, p) -> RRefined(v, b, p)
  | RArrow(x, t1, t2) ->
      RArrow(x, specialize_type t1 type_var concrete, specialize_type t2 type_var concrete)

let rec beta_reduce expr =
  let expr = strip_annot expr in
  match expr with
  | EApp(func_expr, arg_expr) ->
      begin match resolve_function_body func_expr, arg_expr with
      | Some(param, body), EVar arg_name ->
          begin match lookup_global_definition arg_name with
          | Some _ ->
              log "[Inline] Beta-reducing: substituting '%s' for '%s'\n" arg_name param;
              let reduced = ast_substitute param (EVar arg_name) body in
              beta_reduce reduced
          | None ->
              EApp(beta_reduce func_expr, beta_reduce arg_expr)
          end
      | _ ->
          EApp(beta_reduce func_expr, beta_reduce arg_expr)
      end
  | ELet(x, e1, e2) ->
      ELet(x, beta_reduce e1, beta_reduce e2)
  | EIf(c, t, e) ->
      EIf(beta_reduce c, beta_reduce t, beta_reduce e)
  | _ -> expr

let rec beta_reduce_all expr =
  let expr = strip_annot expr in
  log "[BetaReduce] Processing: %s\n" (Pprint.string_of_expr expr);
  match expr with
  | EApp(f, arg) ->
      log "[BetaReduce] Reducing function and argument\n";
      let f' = beta_reduce_all f in
      let arg' = beta_reduce_all arg in
      log "[BetaReduce] After reduction, f' = %s\n" (Pprint.string_of_expr f');
      (match strip_annot f' with
       | EFun(param, body) ->
           log "[BetaReduce] Found lambda! Substituting %s\n" param;
           let reduced = subst_expr param arg' body in
           beta_reduce_all reduced
       | _ ->
           log "[BetaReduce] Not a lambda, keeping application\n";
           EApp(f', arg'))
  | ELet(x, e1, e2) ->
      let e1' = beta_reduce_all e1 in
      let e2_subst = subst_expr x e1' e2 in
      beta_reduce_all e2_subst
  | EIf(c, t, e) -> EIf(beta_reduce_all c, beta_reduce_all t, beta_reduce_all e)
  | EFun(x, body) -> EFun(x, beta_reduce_all body)
  | _ -> expr


let rec expand_lets expr =
  let expr = strip_annot expr in
  match expr with
  | ELet(x, e1, e2) ->
      let e1_expanded = expand_lets e1 in
      let e2_expanded = expand_lets e2 in
      subst_expr x e1_expanded e2_expanded
  | EApp(f, arg) -> EApp(expand_lets f, expand_lets arg)
  | EIf(c, t, e) -> EIf(expand_lets c, expand_lets t, expand_lets e)
  | EFun(x, body) -> EFun(x, expand_lets body)
  | EForall (vs, body) -> EForall (vs, expand_lets body)
  | _ -> expr


let rec term_type_infer ctx term =
  match term with
    | EInt _ | EBool _ -> value_type_infer ctx term
    | EForall (qvars, body) ->
        let _ = qvars in
        let _ = term_type_infer ctx body in
        RRefined ("v", RBool, EForall (qvars, body))

    | EAnnot(inner_expr, annot_ty) ->
        (match inner_expr with
         | EFun(arg, body) ->
             let arg_ty = (match annot_ty with
               | RArrow(t_arg, _) -> basetype_to_rtyp t_arg
               | _ -> RRefined(arg, RInt, EBool true)
             ) in
             log "[Info] Function '%s' with annotated type: %s\n"
               arg (typ_to_string arg_ty);
             let ctx' = (arg, arg_ty) :: ctx in
             let body_ty = term_type_infer ctx' body in
             RArrow(arg, arg_ty, body_ty)

         | EVar x ->
             (match annot_ty with
              | RArrow(t_arg, t_ret) ->
                  let param_ty = RArrow("x", basetype_to_rtyp t_arg, basetype_to_rtyp t_ret) in
                  log "[Info] Variable '%s' with arrow type\n" x;
                  param_ty
              | _ ->
                  term_type_infer ctx (EVar x))

         | _ ->
             term_type_infer ctx inner_expr)


  | _ ->
      let term = strip_annot term in
      match term with
      | EInt _ | EBool _ -> value_type_infer ctx term

      | EVar x ->
          log "[Debug] Looking up variable '%s'\n" x;
          begin match lookup_ctx ctx x with
          | Some (RArrow _ as arr_ty) ->
              log "[Debug] Found '%s' with arrow type\n" x;
              arr_ty
          | Some (RRefined(_, b, _)) ->
              log "[Debug] Found '%s' with refined type: %s\n" x (Pprint.string_of_basetype b);
              RRefined("v", b, EBinOp(Eq, EVar "v", EVar x))
          | None ->
              log "[Debug] Variable '%s' NOT FOUND in context!\n" x;
              raise (TypeError ("Variable '" ^ x ^ "' not found in context"))
          end

      | ECtor (cname, args) ->
          let info = try Hashtbl.find global_ctor_env cname
                     with Not_found -> raise (TypeError ("Unknown ctor: " ^ cname)) in
          if List.length args <> List.length info.c_args then
            raise (TypeError "Constructor arg length mismatch");
          let arg_types = List.map (fun arg -> term_type_infer ctx arg) args in
          let arg_refinements = List.map2 (fun arg_ty arg_expr ->
            match arg_ty with
            | RRefined(v, _, p) -> subst_expr v arg_expr p
            | _ -> EBool true
          ) arg_types args in
          let combined_arg_ref = List.fold_left
            (fun acc p -> EBinOp(And, acc, p)) (EBool true) arg_refinements in
          let eq_pred = EBinOp(Eq, EVar "v", ECtor(cname, args)) in
          RRefined("v", RUserType info.c_parent, EBinOp(And, eq_pred, combined_arg_ref))


      | EMatch (scrutinee, cases) ->
          let _ = term_type_infer ctx scrutinee in
          let scrut_var = match scrutinee with EVar x -> x | _ -> "temp_scrut" in
          let branch_results = List.map (fun (cname, arg_names, body) ->
            let info = try Hashtbl.find global_ctor_env cname
                       with Not_found -> raise (TypeError ("Unknown ctor in match: " ^ cname)) in
            if List.length arg_names <> List.length info.c_args then
              raise (TypeError "Pattern arg count mismatch");
            let ctx_branch = List.fold_left2 (fun acc arg_var arg_type ->
              add_to_ctx acc arg_var (RRefined(arg_var, arg_type, EBool true))
            ) ctx arg_names info.c_args in
            let ctor_args_expr = List.map (fun x -> EVar x) arg_names in
            let pattern_expr = ECtor(cname, ctor_args_expr) in
            let path_condition = EBinOp(Eq, EVar scrut_var, pattern_expr) in
            let ctx_refined = add_path_condition ctx_branch path_condition in
            term_type_infer ctx_refined body
          ) cases in
          begin match branch_results with
          | [] -> raise (TypeError "Empty match")
          | [t] -> t
          | t :: ts -> List.fold_left join_types t ts
          end

      | EBinOp (op, e1, e2) ->
          let t1 = term_type_infer ctx e1 in
          let t2 = term_type_infer ctx e2 in
          let ret_ty_base = match op with
            | Ast.Eq | Ast.Neq | Ast.Lt | Ast.Gt | Ast.Le | Ast.Ge | Ast.And | Ast.Or | Ast.Implies | Ast.Iff -> RBool
            | _ -> RInt
          in
          let result_var = fresh_name "v" in
          let extract_refinement t expr =
            match t with
            | RRefined(vt, _, pt) -> subst_expr vt expr pt
            | _ -> EBool true
          in
          let p1 = extract_refinement t1 e1 in
          let p2 = extract_refinement t2 e2 in
          let result_eq = EBinOp(Eq, EVar result_var, EBinOp(op, e1, e2)) in
          let combined = EBinOp(And, EBinOp(And, result_eq, p1), p2) in
          RRefined(result_var, ret_ty_base, combined)

      | EIf (cond, et, ef) ->
            let t_cond = term_type_infer ctx cond in
            let (v_cond, p_cond) = match t_cond with
              | RRefined(v, RBool, p) -> (v, p)
              | _ -> raise (TypeError "If condition must be boolean")
            in
            let p_true = subst_expr v_cond (EBool true) p_cond in
            let ctx_t = (fresh_name "_", RRefined("_", RBool, p_true)) :: ctx in
            let p_false = subst_expr v_cond (EBool false) p_cond in
            let ctx_f = (fresh_name "_", RRefined("_", RBool, p_false)) :: ctx in
            let tt = term_type_infer ctx_t et in
            let tf = term_type_infer ctx_f ef in
            begin match (tt, tf) with
            | (RRefined(vt, bt, pt), RRefined(vf, bf, pf)) ->
                if bt <> bf then raise (TypeError "Branches must have same base type");
                let new_var = fresh_name "ifres" in
                let joined_phi =
                  if is_pure et && is_pure ef then
                    EBinOp(Eq, EVar new_var, EIf(cond, et, ef))
                  else
                    let eq_t = extract_equality vt pt in
                    let eq_f = extract_equality vf pf in
                    match (eq_t, eq_f) with
                    | (Some et, Some ef) -> EBinOp(Eq, EVar new_var, EIf(cond, et, ef))
                    | _ ->
                        let pt_unified = subst_expr vt (EVar new_var) pt in
                        let pf_unified = subst_expr vf (EVar new_var) pf in
                        EBinOp(Or,
                          EBinOp(And, cond, pt_unified),
                          EBinOp(And, EBinOp(Eq, cond, EBool false), pf_unified))
                in
                RRefined(new_var, bt, joined_phi)
            | _ -> raise (TypeError "Branch types must match")
            end

      | EFun (arg, body) ->
          let arg_ty = match term with
            | EAnnot(_, RArrow(t_arg, _)) ->
                basetype_to_rtyp t_arg
            | _ ->
                RRefined(arg, RInt, EBool true)
          in

          let ctx' = (arg, arg_ty) :: ctx in
          let body_ty = term_type_infer ctx' body in
          RArrow(arg, arg_ty, body_ty)

      | EApp (f, arg) ->
          let reduced = beta_reduce term in
          if reduced <> term then begin
            log "[Debug] Beta-reduced application\n";
            term_type_infer ctx reduced
          end else begin
            let maybe_def = resolve_function_body f in
            begin match maybe_def with
            | Some (_, _) ->
                log "[Debug] Standard modular application (def found)\n";
                let f_ty = term_type_infer ctx f in
                let arg_ty = term_type_infer ctx arg in
                begin match f_ty with
                | RArrow (x, t_param, t_return) ->
                    begin match is_subtype ctx arg_ty t_param with
                    | Valid -> ()
                    | Invalid _ -> raise (TypeError "Type Mismatch")
                    | Unknown -> raise (TypeError "Verification Unknown")
                    end;

                    let t_return_specialized = match t_param with
                      | RRefined(_, RVar tv, _) ->
                          (match arg_ty with
                           | RRefined(_, concrete_base, _) -> specialize_type t_return tv concrete_base
                           | _ -> t_return)
                      | _ -> t_return
                    in

                    begin match t_return_specialized with
                    | RRefined(v_ret, b_ret, p_ret) ->
                        let result_var = fresh_name "v" in
                        let p_ret_instantiated = subst_expr x arg p_ret in
                        let p_final = subst_expr v_ret (EVar result_var) p_ret_instantiated in
                        let combined_refinement = EBinOp(And, EBinOp(Eq, EVar result_var, EApp(f, arg)), p_final) in
                        let arg_pred = match arg_ty with
                          | RRefined(v_arg, _, p_arg) -> subst_expr v_arg arg p_arg
                          | _ -> EBool true
                        in
                        RRefined(result_var, b_ret, EBinOp(And, arg_pred, combined_refinement))
                    | RArrow _ -> subst_in_type x arg t_return_specialized
                    end
                | RRefined _ -> raise (TypeError "Cannot apply non-function type")
                end

            | None ->
                log "[Debug] Standard modular application (no def)\n";
                let f_ty = term_type_infer ctx f in
                let arg_ty = term_type_infer ctx arg in
                begin match f_ty with
                | RArrow (x, t_param, t_return) ->
                    begin match is_subtype ctx arg_ty t_param with
                    | Valid -> ()
                    | Invalid _ -> raise (TypeError "Type Mismatch in application")
                    | Unknown -> raise (TypeError "Verification Unknown in application")
                    end;
                    begin match t_return with
                    | RRefined(v_ret, b_ret, p_ret) ->
                        let result_var = fresh_name "v" in
                        let p_ret_instantiated = subst_expr x arg p_ret in
                        let p_final = subst_expr v_ret (EVar result_var) p_ret_instantiated in
                        let combined_refinement = EBinOp(And, EBinOp(Eq, EVar result_var, EApp(f, arg)), p_final) in
                        let arg_pred = match arg_ty with
                          | RRefined(v_arg, _, p_arg) -> subst_expr v_arg arg p_arg
                          | _ -> EBool true
                        in
                        RRefined(result_var, b_ret, EBinOp(And, arg_pred, combined_refinement))
                    | RArrow _ -> subst_in_type x arg t_return
                    end
                | RRefined _ -> raise (TypeError "Cannot apply non-function type")
                end
            end
          end


      | ELetRec (f, arg, fbody, rest) ->
          register_global_definition f arg fbody;
          let t_arg = RRefined(arg, RInt, EBool true) in
          let t_ret = RRefined("v", RInt, EBool true) in
          let placeholder_type = RArrow(arg, t_arg, t_ret) in
          let ctx_recursive = (f, placeholder_type) :: ctx in
          let func_ty = term_type_infer ctx_recursive (EFun(arg, fbody)) in
          let ctx_with_f = (f, func_ty) :: ctx in
          term_type_infer ctx_with_f rest

      | ELet (x, e1, e2) ->
          log "[Debug] Processing Let '%s'\n" x;
          begin match e1 with
          | EFun(arg, body) | EAnnot(EFun(arg, body), _) ->
              log "[Debug] '%s' is a function. Registering in Z3\n" x;
              register_global_definition x arg body
          | _ -> log "[Debug] '%s' is not a function\n" x
          end;

          let t1 = term_type_infer ctx e1 in
          log "[Debug] Let '%s' has type: %s\n" x (typ_to_string_full t1);

          let t1_strong = match t1 with
            | RArrow _ -> t1
            | RRefined(v, b, p) ->
                let eq_pred = EBinOp(Eq, EVar v, e1) in
                RRefined(v, b, EBinOp(And, p, eq_pred))
          in
          log "[Debug] Strengthened type for '%s': %s\n" x (typ_to_string_full t1_strong);

          let ctx' = (x, t1_strong) :: ctx in
          let t2 = term_type_infer ctx' e2 in

          let has_ho_app expr =
            let rec check e = match strip_annot e with
              | EApp(EApp(_, EVar _), _) -> true
              | EApp(f, _) -> check f
              | _ -> false
            in check expr
          in

          let result = begin match t1 with
            | RArrow _ -> t2
            | _ ->
                if has_ho_app e1 then
                  t2  (* Don't substitute - keeps refinement clean *)
                else
                  subst_in_type x e1 t2
          end in
          log "[Debug] After let '%s' (after subst), result type: %s\n" x (typ_to_string_full result);
          result


      | EAnnot (inner, _) ->
          term_type_infer ctx inner
      | EForall (qvars, body) ->
          let _ = qvars in
          let _ = term_type_infer ctx body in
          RRefined ("v", RBool, EForall (qvars, body))

and term_type_check ctx e target =
  let e = strip_annot e in
  log "[Check] Checking against %s\n" (typ_to_string target);
  match e with
  | EFun (arg, body) ->
      begin match target with
      | RArrow (formal, t_in, t_out) ->
          log "[Bidir] Function check: pushing arg type into body\n";
          let t_out' = subst_in_type formal (EVar arg) t_out in
          let ctx' = add_to_ctx ctx arg t_in in
          term_type_check ctx' body t_out'
      | RRefined _ ->
          raise (TypeError (Printf.sprintf "Type Mismatch: Expected value of type %s, but found lambda" (typ_to_string target)))
      end

  | EIf (cond, et, ef) ->
      log "[Bidir] If-check: propagating target to both branches\n";
      let _ = term_type_infer ctx cond in
      let ctx_t = add_path_condition ctx cond in
      let ctx_f = add_path_condition ctx (EBinOp(Eq, cond, EBool false)) in
      term_type_check ctx_t et target;
      term_type_check ctx_f ef target

  | EMatch (scrutinee, cases) ->
      log "[Bidir] Match-check: propagating target to all branches\n";
      let _ = term_type_infer ctx scrutinee in
      let scrut_var = match scrutinee with EVar x -> x | _ -> "temp_scrut" in
      List.iter (fun (cname, arg_names, body) ->
        let info = try Hashtbl.find global_ctor_env cname
                   with Not_found -> raise (TypeError ("Unknown ctor: " ^ cname)) in
        let ctx_branch = List.fold_left2 (fun acc arg_var arg_type ->
          add_to_ctx acc arg_var (RRefined(arg_var, arg_type, EBool true))
        ) ctx arg_names info.c_args in
        let pattern_expr = ECtor(cname, List.map (fun x -> EVar x) arg_names) in
        let path_condition = EBinOp(Eq, EVar scrut_var, pattern_expr) in
        let ctx_refined = add_path_condition ctx_branch path_condition in
        term_type_check ctx_refined body target
      ) cases

  | ELet (x, rhs, body) ->
      log "[Bidir] Let-check: propagating target to body\n";
      let rhs_ty = term_type_infer ctx rhs in
      let rhs_ty_strong = match rhs_ty with
        | RArrow _ -> rhs_ty
        | RRefined(v, b, p) -> RRefined(v, b, EBinOp(And, p, EBinOp(Eq, EVar v, rhs)))
      in
      let ctx' = add_to_ctx ctx x rhs_ty_strong in
      term_type_check ctx' body target

  | ELetRec (f, arg, body, rest) ->
      log "[Bidir] LetRec-check: inferring function, checking rest\n";
      let t_arg = RRefined(arg, RInt, EBool true) in
      let t_ret = RRefined("v", RInt, EBool true) in
      let placeholder_type = RArrow(arg, t_arg, t_ret) in
      let ctx_rec = (f, placeholder_type) :: ctx in
      let func_ty = term_type_infer ctx_rec (EFun(arg, body)) in
      let ctx_next = add_to_ctx ctx f func_ty in
      term_type_check ctx_next rest target

  | _ ->
      let inferred = term_type_infer ctx e in
      spec_check_mode := true;
      Fun.protect
        ~finally:(fun () -> spec_check_mode := false)
        (fun () ->
          match is_subtype ctx inferred target with
          | Valid -> ()
          | Invalid cex_list ->
              let cex_json_parts = List.map (fun (k, v) ->
                Printf.sprintf "\"%s\": \"%s\"" k (String.escaped v)) cex_list in
              let json_msg = Printf.sprintf "JSON{%s}" (String.concat ", " cex_json_parts) in
              raise (TypeError json_msg)
          | Unknown ->
              raise (TypeError "JSON{\"Error\": \"Verification Failed: Solver returned Unknown\"}")
        )

and typ_to_string = function
  | RRefined (v, b, _) -> Printf.sprintf "{%s:%s | ...}" v (Pprint.string_of_basetype b)
  | RArrow (x, t1, t2) -> Printf.sprintf "(%s:%s -> %s)" x (typ_to_string t1) (typ_to_string t2)

let parse_precondition_with_args arg_names precond_str =
  let env_source = String.concat "" (List.map (fun arg ->
    Printf.sprintf "let %s = 0 in " arg
  ) arg_names) in
  let full_source = env_source ^ "(" ^ precond_str ^ ")" in
  let parsed = Parser_frontend.parse_expr full_source in
  let rec strip_wrappers e = match e with
    | EAnnot(inner, _) -> strip_wrappers inner
    | ELet(_, _, body) -> strip_wrappers body
    | _ -> e
  in
  strip_wrappers parsed

   let parse_spec_with_args (arg_names : string list) (spec_str : string) : Ast.expr =
     let spec_str = String.trim spec_str in
     let spec_str = Str.global_replace (Str.regexp "!=") "<>" spec_str in
     let spec_str = Str.global_replace (Str.regexp "~-") "-" spec_str in
     let starts_with pfx s =
       String.length s >= String.length pfx &&
       String.sub s 0 (String.length pfx) = pfx
     in
     let shape_stubs =
       Hashtbl.fold (fun name decl acc ->
         let arity = Z3.FuncDecl.get_arity decl in
         let dummy_args = String.concat " " (List.init arity (fun _ -> "_")) in
         (Printf.sprintf "let %s %s = false in " name dummy_args) :: acc
       ) Logic.shape_pred_registry []
       |> String.concat ""
     in

     let implies_stub = "let (==>) (a : bool) (b : bool) = if a then b else true in " in
     let iff_stub = "let (<==>) (a : bool) (b : bool) = a = b in " in

     let fn_stubs =
       Hashtbl.fold (fun name decl acc ->
         if Hashtbl.mem Logic.shape_pred_registry name then acc
         else
           let ret_sort = Z3.FuncDecl.get_range decl in
           let ret_val =
             if Z3.Sort.equal ret_sort (Z3.Boolean.mk_sort Solver.ctx)
             then "false" else "0"
           in
           let arity = Z3.FuncDecl.get_arity decl in
           let dummy_args =
             if arity = 0 then "_dummy"
             else String.concat " " (List.init arity (fun _ -> "_"))
           in
           (Printf.sprintf "let %s %s = %s in " name dummy_args ret_val) :: acc
       ) Logic.registered_functions []
       |> String.concat ""
     in
     if starts_with "forall" spec_str then begin
       let after_forall = String.trim (String.sub spec_str 6 (String.length spec_str - 6)) in
       let comma_idx = try String.index after_forall ','
         with Not_found -> raise (TypeError "Forall spec missing ','") in
       let vars_str = String.sub after_forall 0 comma_idx in
       let body_str = String.trim (String.sub after_forall (comma_idx+1)
         (String.length after_forall - comma_idx - 1)) in
       let qvars = String.split_on_char ' ' vars_str
         |> List.map String.trim |> List.filter (fun s -> s <> "") in
       let env_source =
         shape_stubs ^ fn_stubs ^ implies_stub ^ iff_stub
         ^ (List.map (fun a -> Printf.sprintf "let %s = 0 in " a) arg_names |> String.concat "")
         ^ (List.map (fun q -> Printf.sprintf "let %s = 0 in " q) qvars  |> String.concat "")
       in
       let body_expr = Parser_frontend.parse_expr (env_source ^ "(" ^ body_str ^ ")") in
       let rec strip e = match e with
         | EAnnot(i,_) -> strip i | ELet(_,_,b) -> strip b | _ -> e in
       EForall (qvars, strip body_expr)
     end else begin
       let env_source =
         shape_stubs ^ fn_stubs ^ implies_stub ^ iff_stub
         ^ (List.map (fun a -> Printf.sprintf "let %s = 0 in " a) arg_names |> String.concat "")
       in
       let parsed = Parser_frontend.parse_expr (env_source ^ "(" ^ spec_str ^ ")") in
       let rec strip e = match e with
         | EAnnot(i,_) -> strip i | ELet(_,_,b) -> strip b | _ -> e in
       strip parsed
     end

let rec instantiate_to_int (t : rtyp) : rtyp =
  match t with
  | RRefined(v, RVar _, p) ->
      RRefined(v, RInt, p)
  | RRefined(v, b, p) ->
      RRefined(v, b, p)
  | RArrow(x, t1, t2) ->
      RArrow(x, instantiate_to_int t1, instantiate_to_int t2)

let verify program spec_str precond_str_opt =
  Hashtbl.clear global_ctor_env;
  Hashtbl.clear global_fn_env;
  counter := 0;
  name_map |> Hashtbl.reset;
  Solver.reset ();
  try
    match List.rev program with
    | [] -> Invalid [("Error", "Empty program provided")]
    | target_decl :: rest_rev ->
        let helpers = List.rev rest_rev in

        register_adt "list" [
            ("[]",  []);
            ("::",  [RInt; RUserType "list"])
          ];
        let ctx_with_deps = List.fold_left (fun ctx decl ->
          match decl with
          | Ast.DType (name, ctors) ->
              log "[Info] Registering ADT: %s\n" name;
              register_adt name ctors;
              ctx
          | Ast.DLet (name, _, val_expr) ->
              log "[Verify] Processing helper '%s'\n" name;
              (match val_expr with
               | Ast.EAnnot(Ast.EFun(pname, _), ty) ->
                   log "[Verify] Helper has EAnnot(EFun('%s', ...), %s)\n"
                     pname (Pprint.string_of_basetype ty)
               | Ast.EFun(pname, _) ->
                   log "[Verify] Helper has bare EFun('%s', ...) NO ANNOTATION\n" pname
               | _ -> log "[Verify] Helper is not a function...\n"
              );
              begin match val_expr with
              | Ast.EAnnot(Ast.EFun(arg, fun_body), _) ->
                  register_global_definition ~full_expr:val_expr name arg fun_body
              | Ast.EFun(arg, fun_body) ->
                  register_global_definition name arg fun_body
              | _ -> ()
              end;

              let ctx_for_infer =
                if is_recursive name val_expr then
                  let placeholder = match val_expr with
                    | Ast.EAnnot (_, ty) -> basetype_to_rtyp ty
                    | _ ->
                        RArrow ("x",
                          RRefined ("x", RInt, EBool true),
                          RRefined ("v", RInt, EBool true))
                  in
                  add_to_ctx ctx name placeholder
                else ctx
              in
              let inferred_t = term_type_infer ctx_for_infer val_expr in
              log "[Verify] Helper '%s' inferred type: %s\n" name (typ_to_string_full inferred_t);
              log "[Info] Helper '%s' typed\n" name;
              let public_t = match val_expr with
                | Ast.EAnnot (_, bt) -> basetype_to_rtyp bt
                | _ -> inferred_t
              in
              let rec collect_arg_sorts_for_axiom = function
                | RArrow(x, RRefined(_, bt, _), rest) ->
                    (x, base_type_to_sort_string bt) :: collect_arg_sorts_for_axiom rest
                | _ -> []
              in
              let fn_args_for_axiom = collect_arg_sorts_for_axiom inferred_t in
              let rec get_ret_type = function
                | RArrow(_, _, r) -> get_ret_type r
                | t -> t
              in
              let ret_type_str = match get_ret_type inferred_t with
                | RRefined(_, RInt, _)        -> "Int"
                | RRefined(_, RBool, _)       -> "Bool"
                | RRefined(_, RUserType s, _) -> s
                | _                           -> "Int"
              in
              Solver.abstract_function name fn_args_for_axiom ret_type_str;
              (match get_ret_type inferred_t with
               | RRefined(_, RInt, ret_pred) when ret_pred <> EBool true ->
                   Solver.assert_ge_last_int_arg name fn_args_for_axiom
               | _ -> ());

                 let rec collect_arg_sorts_for_axiom = function
                    | RArrow(x, RRefined(_, bt, _), rest) ->
                        (x, base_type_to_sort_string bt) :: collect_arg_sorts_for_axiom rest
                    | _ -> []
                  in
                  let fn_args_for_axiom = collect_arg_sorts_for_axiom inferred_t in
                  let rec get_ret_type = function
                    | RArrow(_, _, r) -> get_ret_type r
                    | t -> t
                  in
                  (match get_ret_type inferred_t with
                  | RRefined(_, RInt, ret_pred) when ret_pred <> EBool true ->
                      Solver.assert_ge_last_int_arg name fn_args_for_axiom
                  | _ -> ());
              add_to_ctx ctx name public_t
            ) empty_ctx helpers
          in

        match target_decl with
        | Ast.DType _ -> Invalid [("Error", "Last declaration must be a function")]
        | Ast.DLet (name, args, val_expr) ->
            log "[Info] Verifying target: '%s'\n" name;
            let spec = parse_spec_with_args args spec_str in
            log "[Debug] Parsed spec: %s\n" (Pprint.string_of_expr spec);
            let full_expr = val_expr in

            begin match full_expr with
            | Ast.EAnnot(Ast.EFun(arg, fun_body), _) ->
                register_global_definition ~full_expr:full_expr name arg fun_body
            | Ast.EFun(arg, fun_body) ->
                register_global_definition name arg fun_body
            | _ -> ()
            end;

            let precond_expr_opt = match precond_str_opt with
              | None -> None
              | Some precond_str ->
                  log "[Info] Parsing precondition with args in scope: %s\n"
                    (String.concat ", " args);
                  Some (parse_precondition_with_args args precond_str)
            in
            let spec_base_type =
              let rec infer_from_expr e = match e with
                | Ast.EInt _ -> RInt
                | Ast.EBool _ -> RBool
                | Ast.EBinOp(Ast.Gt, _, _)
                | Ast.EBinOp(Ast.Lt, _, _)
                | Ast.EBinOp(Ast.Ge, _, _)
                | Ast.EBinOp(Ast.Le, _, _) -> RInt
                | Ast.EBinOp(Ast.Add, _, _)
                | Ast.EBinOp(Ast.Sub, _, _)
                | Ast.EBinOp(Ast.Mul, _, _) -> RInt
                | Ast.EBinOp(Ast.And, e1, _)
                | Ast.EBinOp(Ast.Or, e1, _) -> infer_from_expr e1
                | Ast.EBinOp(_, e1, _) -> infer_from_expr e1
                | _ -> RInt
              in
              infer_from_expr spec
            in
            log "[Info] Inferred type from spec: %s\n" (Pprint.string_of_basetype spec_base_type);

            let rec prepare_check ctx func_name e arg_names remaining_arrow =
              (match e with
                 | Ast.EAnnot(Ast.EAnnot(_, _), _) ->
                     log "[Verify] Matched nested EAnnot - double wrapped!\n"
                 | Ast.EAnnot(Ast.EFun(name, _), ty) ->
                     log "[Verify] Matched EAnnot(EFun('%s', ...), %s)\n"
                       name (Pprint.string_of_basetype ty)
                 | Ast.EAnnot(e', ty) ->
                     log "[Verify] Matched EAnnot(<other>, %s)\n" (Pprint.string_of_basetype ty);
                     (match e' with
                      | Ast.EFun(n, _) -> log "[Verify]    Inner is EFun('%s')\n" n
                      | _ -> log "[Verify]    Inner is NOT EFun\n")
                 | Ast.EFun(name, _) ->
                     log "[Verify] Matched bare EFun('%s', ...) - NO ANNOTATION!\n" name
                 | _ ->
                     log "[Verify] Matched something else (not EFun)\n");
              let instantiate_type_vars ty =
                let rec inst ty = match ty with
                  | RRefined(v, RVar _, p) -> RRefined(v, spec_base_type, p)
                  | RRefined(v, b, p) -> RRefined(v, b, p)
                  | RArrow(x, t1, t2) -> RArrow(x, inst t1, inst t2)
                in inst ty
              in
              match e, remaining_arrow with
              | Ast.EAnnot(Ast.EFun(arg_name, body), base_ty), _ ->
                  begin match basetype_to_rtyp base_ty with
                  | RArrow(_, t_arg, t_ret) ->
                      let t_arg_concrete = instantiate_type_vars t_arg in
                      let t_arg_with_precond = match precond_expr_opt with
                        | Some precond_expr ->
                            (match t_arg_concrete with
                             | RRefined(_, b, _) -> RRefined(arg_name, b, precond_expr)
                             | other -> other)
                        | None -> t_arg_concrete
                      in
                      log "[Verify] Adding param '%s' with type: %s\n"
                        arg_name (typ_to_string_full t_arg_with_precond);
                      let ctx' = add_to_ctx ctx arg_name t_arg_with_precond in
                      prepare_check ctx' func_name body (arg_name :: arg_names) (Some t_ret)
                  | other ->
                      let other_concrete = instantiate_type_vars other in
                      let other_with_precond = match precond_expr_opt with
                        | Some precond_expr -> RRefined(arg_name, spec_base_type, precond_expr)
                        | None -> other_concrete
                      in
                      let ctx' = add_to_ctx ctx arg_name other_with_precond in
                      prepare_check ctx' func_name body (arg_name :: arg_names) None
                  end

              | Ast.EFun(arg_name, body), Some (RArrow(_, t_arg, t_ret)) ->
                  let t_arg_concrete = instantiate_type_vars t_arg in
                  let ctx' = add_to_ctx ctx arg_name t_arg_concrete in
                  prepare_check ctx' func_name body (arg_name :: arg_names) (Some t_ret)
              | Ast.EFun(arg_name, body), _ ->
                  let arg_refinement = match precond_expr_opt with
                    | Some precond_expr -> precond_expr
                    | None -> EBool true
                  in
                  let arg_ty = RRefined(arg_name, RInt, arg_refinement) in
                  let ctx' = add_to_ctx ctx arg_name arg_ty in
                  prepare_check ctx' func_name body (arg_name :: arg_names) None
              | body, _ ->
                  log "[Debug] In base case, spec = %s\n" (Pprint.string_of_expr spec);
                  (ctx, body, List.rev arg_names)
            in
            let (ctx_body, body_expr, arg_names) = prepare_check ctx_with_deps name full_expr [] None in
            let rec final_base_type = function
              | Ast.RArrow (_, ret) -> final_base_type ret
              | t -> t
            in
            let target_base = match val_expr with
              | Ast.EAnnot (_, bt) -> final_base_type bt
              | _                  -> spec_base_type
            in
            let target_type = RRefined("v", target_base, spec) in
            let body_beta_reduced = beta_reduce body_expr in
            let body_fully_reduced = beta_reduce_all body_beta_reduced in
            log "[Debug] Fully reduced body: %s\n" (Pprint.string_of_expr body_fully_reduced);

            let ctx_final =
              if is_recursive name body_fully_reduced then begin
                let func_type = List.fold_right (fun arg_name acc ->
                  let arg_ty = match List.assoc_opt arg_name ctx_body with
                    | Some t -> t
                    | None -> RRefined(arg_name, RInt, EBool true)
                  in
                  RArrow(arg_name, arg_ty, acc)
                ) arg_names target_type in
                add_to_ctx ctx_body name func_type
              end else
                ctx_body
            in

            let direct_var_types =
              List.filter_map (fun pname ->
                match List.assoc_opt pname ctx_body with
                | Some (RRefined(_, bt, _)) ->
                    if Hashtbl.mem Logic.registered_functions pname then None
                    else Some (pname, bt)
                | _ -> None
              ) arg_names
            in

            let full_app =
              List.fold_left (fun acc pname -> EApp(acc, EVar pname)) (EVar name) arg_names
            in

            let direct_spec_expr =
              subst_expr "v" full_app spec
            in

            let build_small_adt_value type_name head_var =
              let nil_ctor_opt =
                Hashtbl.fold (fun _ info acc ->
                  match acc with
                  | Some _ -> acc
                  | None ->
                      if info.c_parent = type_name &&
                         not (List.exists (fun a -> a = RUserType type_name) info.c_args)
                      then Some info.c_name
                      else None
                ) global_ctor_env None
              in
              let rec_ctor_opt =
                Hashtbl.fold (fun _ info acc ->
                  match acc with
                  | Some _ -> acc
                  | None ->
                      if info.c_parent = type_name &&
                         List.exists (fun a -> a = RUserType type_name) info.c_args
                      then Some info
                      else None
                ) global_ctor_env None
              in
              match nil_ctor_opt, rec_ctor_opt with
              | Some nil_name, Some rec_info ->
                  let args =
                    List.map (function
                      | RInt -> EVar head_var
                      | RUserType s when s = type_name -> ECtor(nil_name, [])
                      | _ -> EVar head_var
                    ) rec_info.c_args
                  in
                  Some (ECtor(rec_info.c_name, args))
              | _ -> None
            in

            let (direct_var_types, direct_spec_formula) =
              match strip_annot direct_spec_expr with
              | EForall(qvars, body) ->
                  let witness_pairs = List.map (fun q -> (q, fresh_name q)) qvars in
                  let grounded_body =
                    List.fold_left
                      (fun e (q, w) -> subst_expr q (EVar w) e)
                      body witness_pairs
                  in
                  let witness_int_vars = List.map snd witness_pairs in
                  let grounded_body =
                    match witness_int_vars with
                    | [] -> grounded_body
                    | head :: _ ->
                        List.fold_left (fun e (x, bt) ->
                          match bt with
                          | RUserType type_name ->
                              (match build_small_adt_value type_name head with
                               | Some concrete -> subst_expr x concrete e
                               | None -> e)
                          | _ -> e
                        ) grounded_body direct_var_types
                  in
                  let extra_var_types =
                    List.map (fun (_, w) -> (w, RInt)) witness_pairs
                  in
                  (direct_var_types @ extra_var_types, expr_to_formula grounded_body)
              | _ ->
                  (direct_var_types, expr_to_formula direct_spec_expr)
            in


            let is_unknown_json msg =
              String.length msg >= 5
              && String.sub msg 0 5 = "JSON{"
              && (try let _ = Str.search_forward
                            (Str.regexp_string "Unknown")
                            (String.sub msg 5 (String.length msg - 6)) 0
                  in true
                  with Not_found -> false)
            in

            (try
              term_type_check ctx_final body_fully_reduced target_type;
              Valid
            with TypeError msg when is_unknown_json msg ->
              log
                "[CEX] Inductive proof Unknown — running direct falsification\n";
              match Solver.falsify_directly direct_var_types direct_spec_formula with
              | Solver.V_Valid ->
                  log "[CEX] Spec is semantically correct — IH too weak\n";
                  Unknown
              | Solver.V_Unknown ->
                  log "[CEX] Direct falsification timed out\n";
                  Unknown
              | Solver.V_Invalid model_msg ->
                  log "[CEX] Spec is genuinely wrong — reporting CEX\n";
                  let raw_pairs = parse_z3_raw_output model_msg in
                  let best = Hashtbl.create 8 in
                  List.iter (fun (k, v) ->
                    let src =
                      match Hashtbl.find_opt name_map k with Some s -> s | None -> k
                    in
                    match Hashtbl.find_opt best src with
                    | None -> Hashtbl.add best src (k, v)
                    | Some (ek, _) ->
                        if compare_z3_names k ek < 0
                        then Hashtbl.replace best src (k, v)
                  ) raw_pairs;
                  Invalid (Hashtbl.fold
                    (fun src (_, v) acc -> (src, v) :: acc) best []))



  with
  | TypeError msg ->
      if String.length msg >= 5 && String.sub msg 0 5 = "JSON{" then begin
        let json_content = String.sub msg 5 (String.length msg - 6) in
        let content = String.trim json_content in
        if content = "" then
          Invalid []
        else begin
          let parts = String.split_on_char ',' content in
          let parse_kv part =
            try
              let part = String.trim part in
              let idx = String.index part ':' in
              let key_raw = String.sub part 0 idx |> String.trim in
              let val_raw = String.sub part (idx+1) (String.length part - idx - 1) |> String.trim in
              let strip_quotes s =
                if String.length s >= 2 && s.[0] = '"' && s.[String.length s - 1] = '"' then
                  String.sub s 1 (String.length s - 2)
                else s
              in
              (strip_quotes key_raw, strip_quotes val_raw)
            with _ -> ("Error", "Failed to parse cex part: " ^ part)
          in
          Invalid (List.map parse_kv parts)
        end
      end else
        Invalid [("Error", msg)]

  | Parser_frontend.ParseError msg ->
      Invalid [("Error", "Parse error: " ^ msg)]
  | e -> Invalid [("Crash", Printexc.to_string e)]

  let rec decompose_spec expr =
    match strip_annot expr with
    | EBinOp(And, e1, e2) -> decompose_spec e1 @ decompose_spec e2
    | _                   -> [expr]

  let rec normalize_formula = function
    | Logic.FBinOp(Logic.Eq, f, Logic.FFalse)
    | Logic.FBinOp(Logic.Eq, Logic.FFalse, f) -> Logic.FNot (normalize_formula f)
    | Logic.FBinOp(Logic.Eq, f, Logic.FTrue)
    | Logic.FBinOp(Logic.Eq, Logic.FTrue,  f) -> normalize_formula f
    | Logic.FBinOp(op, l, r) ->
        Logic.FBinOp(op, normalize_formula l, normalize_formula r)
    | Logic.FNot f -> Logic.FNot (normalize_formula f)
    | other -> other

  let flatten_and f =
    let rec collect = function
      | Logic.FBinOp(Logic.And, l, r) -> collect l @ collect r
      | Logic.FTrue -> []
      | other ->
          let f = normalize_formula other in
          (match f with
            | Logic.FBinOp(Logic.Eq, a, b) when a = b -> []
            | _ -> [f])
        in
        collect f

  let rename_ret ob f =
    if ob.po_ret_var = "v" then f
    else Logic.subst ob.po_ret_var (Logic.FVar "v") f

  let check_sub_spec (program : Ast.declaration list) (spec_str : string) (precond_str_opt : string option) : int * int * (string * bool) list =
    proof_obligations := [];
    po_counter := 0;
    sub_spec_mode := true;
    (try ignore (verify program spec_str precond_str_opt) with _ -> ());
    sub_spec_mode := false;
    Hashtbl.clear Logic.uninterpreted_func_map;
    let obligations = !proof_obligations in
    let arg_names = match List.rev program with
      | Ast.DLet(_, args, _) :: _ -> args
      | _ -> []
    in
    let spec_expr   = parse_spec_with_args arg_names spec_str in
    let sub_specs   = decompose_spec spec_expr in
    let total       = List.length sub_specs in
    let sub_spec_results = List.mapi (fun i ss ->
      let ss_label = Pprint.string_of_expr ss in
      let any_pass = List.exists (fun ob ->
        let instantiated =
          Logic.expr_to_formula (subst_expr "v" (EVar ob.po_ret_var) ss) in

        let raw_query = Logic.FBinOp(Logic.Implies,
          Logic.FBinOp(Logic.And, ob.po_path, ob.po_holds), instantiated) in
        let query, ho_extras = abstract_ho_apps ob.po_vartypes raw_query in
        let vt_ext = ob.po_vartypes @ ho_extras in
        let rec_fnames = List.filter_map (fun (k, _) ->
          let s = "::ret" in
          let klen = String.length k and slen = String.length s in
          if klen > slen && String.sub k (klen - slen) slen = s then
            let fname = String.sub k 0 (klen - slen) in
            if Hashtbl.mem global_fn_env fname then Some fname else None
          else None
        ) vt_ext in
        let p1_for_ih = Logic.FBinOp(Logic.And, ob.po_path, ob.po_holds) in
        let query, rec_extras =
          abstract_recursive_apps rec_fnames vt_ext p1_for_ih query in
        let vt_ext = vt_ext @ rec_extras in
        match Solver.check_validity ~use_fallback:false vt_ext query with
        | Solver.V_Valid -> true
        | _ -> false
      ) obligations in
      log "[SubSpec]   sub_spec[%d] %s → %s\n"
        (i + 1) ss_label (if any_pass then "✓" else "✗");
      (ss_label, any_pass)
    ) sub_specs in
    let score = List.length (List.filter snd sub_spec_results) in
    log "[SubSpec] Score: %d / %d\n" score total;
    (score, total, sub_spec_results)