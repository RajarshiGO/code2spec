(* ============================================================================ *)
(* SOLVER: Debug Version V2 *)
(* ============================================================================ *)

open Z3
open Z3.Solver
open Ast

let verbose = false
let log fmt = Printf.ksprintf (fun s -> if verbose then print_string s) fmt

let cfg = [("model", "true"); ("proof", "false")]
let ctx = mk_context cfg
let solver = mk_solver ctx None
let axiom_registry : Z3.Expr.expr list ref = ref []
let abstracted_decl_cache : (string, Z3.FuncDecl.func_decl) Hashtbl.t = Hashtbl.create 8
let ge_axiom_idx : (string, int) Hashtbl.t = Hashtbl.create 4
type validity_result =
  | V_Valid
  | V_Invalid of string
  | V_Unknown

(* Called automatically from register_adt for each newly registered type *)
let derive_shape_predicates (type_name : string)
                             (ctors : (string * basetype list) list) =
  let list_sort = Hashtbl.find Logic.z3_sort_map type_name in
  let int_sort  = Arithmetic.Integer.mk_sort ctx in
  let bool_sort = Boolean.mk_sort ctx in

  (* Determine ADT shape: is it list-like or tree-like?
     List: exactly one recursive constructor with one int field + one self-recursive field
     Tree: exactly one recursive constructor with two self-recursive fields + one int field *)
  (* let recursive_ctors = List.filter (fun (_, args) ->
    List.exists (fun a -> a = RUserType type_name) args
  ) ctors in *)

  (* --- 1. CONTAINMENT PREDICATE: mem_<type_name>(d, u) --- *)
  let mem_name = "mem_" ^ type_name in
  let mem_decl = Z3.FuncDecl.mk_rec_func_decl_s ctx mem_name
    [list_sort; int_sort] bool_sort in
  Hashtbl.replace Logic.shape_pred_registry mem_name mem_decl;

  (* --- 2. ORDERING PREDICATE: ord_<type_name>(d, u, v) --- *)
  let ord_name = "ord_" ^ type_name in
  let ord_decl = Z3.FuncDecl.mk_rec_func_decl_s ctx ord_name
    [list_sort; int_sort; int_sort] bool_sort in
  Hashtbl.replace Logic.shape_pred_registry ord_name ord_decl;

  (* Helper to extract fields dynamically (matching your len_ logic) *)
  let extract_fields ctor_name args x_expr =
    let n = List.length args in
    let ctor_decl = Hashtbl.find Logic.z3_ctor_map ctor_name in
    List.mapi (fun i bt ->
      let acc_name = Printf.sprintf "%s_f%d" ctor_name i in
      match Hashtbl.find_opt Logic.selector_registry acc_name with
      | Some sel -> Expr.mk_app ctx sel [x_expr]
      | None ->
          let s = Logic.type_to_sort ctx bt in
          Expr.mk_app ctx ctor_decl
            (List.init n (fun j ->
              Expr.mk_const_s ctx (Printf.sprintf "_%s_f%d" ctor_name j) s))
    ) args
  in

  (* Native Bound Variables *)
  let x_expr = Expr.mk_const_s ctx "x" list_sort in
  let u_expr = Expr.mk_const_s ctx "u" int_sort in
  let v_expr = Expr.mk_const_s ctx "v" int_sort in

  (* --- Generate mem body --- *)
  let mem_body =
    List.fold_right (fun (ctor_name, args) acc ->
      let recognizer = Hashtbl.find Logic.z3_recognizer_map ctor_name in
      let is_match = Expr.mk_app ctx recognizer [x_expr] in
      let field_exprs = extract_fields ctor_name args x_expr in

      let int_eqs = ref [] in
      let rec_calls = ref [] in
      List.iteri (fun i bt ->
        let f_expr = List.nth field_exprs i in
        if bt = RInt then
          int_eqs := Boolean.mk_eq ctx u_expr f_expr :: !int_eqs
        else if bt = RUserType type_name then
          rec_calls := Expr.mk_app ctx mem_decl [f_expr; u_expr] :: !rec_calls
      ) args;

      let all_clauses = List.rev !int_eqs @ List.rev !rec_calls in
      let branch_val =
        if all_clauses = [] then Boolean.mk_false ctx
        else Boolean.mk_or ctx all_clauses
      in
      Boolean.mk_ite ctx is_match branch_val acc
    ) ctors (Boolean.mk_false ctx)
  in
  Z3.FuncDecl.add_rec_def ctx mem_decl [x_expr; u_expr] mem_body;

  (* --- Generate ord body --- *)
  let ord_body =
    List.fold_right (fun (ctor_name, args) acc ->
      let recognizer = Hashtbl.find Logic.z3_recognizer_map ctor_name in
      let is_match = Expr.mk_app ctx recognizer [x_expr] in
      let field_exprs = extract_fields ctor_name args x_expr in

      let int_fields = ref [] in
      let rec_fields = ref [] in
      List.iteri (fun i bt ->
        let f_expr = List.nth field_exprs i in
        if bt = RInt then int_fields := f_expr :: !int_fields
        else if bt = RUserType type_name then rec_fields := f_expr :: !rec_fields
      ) args;

      let int_fields = List.rev !int_fields in
      let rec_fields = List.rev !rec_fields in

      let head_clauses =
        List.concat_map (fun hi ->
          List.map (fun ri ->
            Boolean.mk_and ctx [
              Boolean.mk_eq ctx u_expr hi;
              Expr.mk_app ctx mem_decl [ri; v_expr]
            ]
          ) rec_fields
        ) int_fields
      in
      let rec_ord_clauses =
        List.map (fun ri ->
          Expr.mk_app ctx ord_decl [ri; u_expr; v_expr]
        ) rec_fields
      in

      let all_clauses = head_clauses @ rec_ord_clauses in
      let branch_val =
        if all_clauses = [] then Boolean.mk_false ctx
        else Boolean.mk_or ctx all_clauses
      in
      Boolean.mk_ite ctx is_match branch_val acc
    ) ctors (Boolean.mk_false ctx)
  in
  Z3.FuncDecl.add_rec_def ctx ord_decl [x_expr; u_expr; v_expr] ord_body;

  (* --- 3. LENGTH MEASURE: len_<type_name>(d) : Int --- *)
    let len_name = "len_" ^ type_name in
    let len_sort = Arithmetic.Integer.mk_sort ctx in
    let len_decl = Z3.FuncDecl.mk_rec_func_decl_s ctx
      (len_name ^ "__impl") [list_sort] len_sort in
    Hashtbl.replace Logic.registered_functions len_name len_decl;

    (* Build the recursive body using one bound variable x *)
    let x_expr = Expr.mk_const_s ctx "x" list_sort in
    let zero    = Arithmetic.Integer.mk_numeral_i ctx 0 in
    let one     = Arithmetic.Integer.mk_numeral_i ctx 1 in

    (* Base case: len(nil_ctor) = 0 *)
    (* Recursive case: len(cons_ctor(..., tail, ...)) = 1 + len(tail) *)
    let rec_len_of_args args_of_ctor ctor_args =
      (* Sum 1 + len(tail_i) for each recursive field *)
      let rec_terms = List.filter_map (fun (bt, arg_expr) ->
        if bt = RUserType type_name
        then Some (Expr.mk_app ctx len_decl [arg_expr])
        else None
      ) (List.combine args_of_ctor ctor_args) in
      Arithmetic.mk_add ctx (one :: rec_terms)
    in

    (* Build a nested ite: ite(is_nil, 0, ite(is_cons, 1+len(tail), 0)) *)
    let body =
      List.fold_right (fun (ctor_name, args) acc ->
        let recognizer = Hashtbl.find Logic.z3_recognizer_map ctor_name in
        let ctor_decl  = Hashtbl.find Logic.z3_ctor_map ctor_name in
        let n = List.length args in
        let field_exprs = List.mapi (fun i bt ->
          let acc_name = Printf.sprintf "%s_f%d" ctor_name i in
          match Hashtbl.find_opt Logic.selector_registry acc_name with
          | Some sel -> Expr.mk_app ctx sel [x_expr]
          | None ->
              let s = Logic.type_to_sort ctx bt in
              Expr.mk_app ctx ctor_decl
                (List.init n (fun j ->
                  Expr.mk_const_s ctx (Printf.sprintf "_%s_f%d" ctor_name j) s))
        ) args in
        let is_recursive_ctor =
          List.exists (fun bt -> bt = RUserType type_name) args in
        let branch_val =
          if is_recursive_ctor
          then rec_len_of_args args field_exprs
          else zero
        in
        Boolean.mk_ite ctx
          (Expr.mk_app ctx recognizer [x_expr])
          branch_val
          acc
      ) ctors zero
    in

    Z3.FuncDecl.add_rec_def ctx len_decl [x_expr] body;

    log "[Solver] Derived shape predicates for '%s': %s, %s, %s\n"
      type_name mem_name ord_name len_name


(* Register ADT with basetype *)
let register_adt (type_name : string) (ctors : (string * basetype list) list) =
if Hashtbl.mem Logic.z3_sort_map type_name then
    log "[Solver] ADT '%s' already registered, skipping\n" type_name
  else begin
    let z3_ctors = List.map (fun (name, args) ->
      let name_sym = Symbol.mk_string ctx name in
      let is_name = Symbol.mk_string ctx ("is_" ^ name) in
      let field_names = List.mapi (fun i _ ->
        Symbol.mk_string ctx (Printf.sprintf "%s_f%d" name i)) args in
      let field_sorts = List.map (fun t ->
          if t = RUserType type_name then None
          else Some (Logic.type_to_sort ctx t)
      ) args in
      let sort_refs = List.map (fun _ -> 0) args in
      Datatype.mk_constructor ctx name_sym is_name field_names field_sorts sort_refs
    ) ctors in

    let sort_name = Symbol.mk_string ctx type_name in
    let sort = Datatype.mk_sort ctx sort_name z3_ctors in

    Hashtbl.replace Logic.z3_sort_map type_name sort;

    let resulting_ctors = Datatype.get_constructors sort in
    let resulting_accessors = Datatype.get_accessors sort in

    List.iter2 (fun (name, _) func ->
      Hashtbl.replace Logic.z3_ctor_map name func
    ) ctors resulting_ctors;

    List.iter2 (fun (c_name, _) accessors ->
      List.iteri (fun i func ->
        let acc_name = Printf.sprintf "%s_f%d" c_name i in
        Hashtbl.replace Logic.selector_registry acc_name func
      ) accessors
    ) ctors resulting_accessors;
    let resulting_recognizers = Datatype.get_recognizers sort in
    List.iter2 (fun (name, _) func ->
      Hashtbl.replace Logic.z3_recognizer_map name func) ctors resulting_recognizers;

    log "[Solver] Registered ADT: %s\n" type_name;
    derive_shape_predicates type_name ctors
  end

(* Define function: args is (name, type_string) list *)
let define_function (name : string) (args : (string * string) list)
                    (ret_type : string)
                    (logic_builder : Z3.Expr.expr list -> Z3.Expr.expr) =
  if Hashtbl.mem Logic.registered_functions name then
      log "[Solver] Function '%s' already defined, skipping\n" name
    else begin
      let arg_sorts = List.map (fun (_, t_str) ->
        match t_str with
        | "Int" | "int"   -> Arithmetic.Integer.mk_sort ctx
        | "Bool" | "bool" -> Boolean.mk_sort ctx
        | type_name ->
            try Hashtbl.find Logic.z3_sort_map type_name
            with Not_found -> Arithmetic.Integer.mk_sort ctx
      ) args in

      let ret_sort = match ret_type with
        | "Bool" | "bool" -> Boolean.mk_sort ctx
        | "Int" | "int"   -> Arithmetic.Integer.mk_sort ctx
        | type_name ->
            try Hashtbl.find Logic.z3_sort_map type_name
            with Not_found -> Arithmetic.Integer.mk_sort ctx
      in

      (* Use a private __impl name for the recursive definition so that
        abstract_function can later register a clean uninterpreted 'name'
        as a distinct Z3 symbol — preventing recursive unfolding at call sites. *)
      let impl_name = name ^ "__impl" in
      let func_decl = Z3.FuncDecl.mk_rec_func_decl_s ctx impl_name arg_sorts ret_sort in
      Hashtbl.replace Logic.registered_functions name func_decl;
      let args_exprs = List.map2
        (fun (n, _) sort -> Expr.mk_const_s ctx n sort) args arg_sorts in
      let body = logic_builder args_exprs in
      Z3.FuncDecl.add_rec_def ctx func_decl args_exprs body;
      log "[Solver] Defined function: %s\n" name
    end

(* General axiom: ∀(args). conclusion(args)
   conclusion_builder receives the Z3 bound-var expressions and returns a Bool formula *)
let assert_custom_axiom (name : string) (args : (string * string) list)
                        (conclusion_builder : Z3.Expr.expr list -> Z3.Expr.expr) =
  match Hashtbl.find_opt Logic.registered_functions name with
  | None -> ()
  | Some func_decl ->
      let n = List.length args in
      let arg_sorts = List.map (fun (_, t_str) ->
        match t_str with
        | "Int" | "int"   -> Arithmetic.Integer.mk_sort ctx
        | "Bool" | "bool" -> Boolean.mk_sort ctx
        | type_name ->
            (try Hashtbl.find Logic.z3_sort_map type_name
             with Not_found -> Arithmetic.Integer.mk_sort ctx)
      ) args in
      let bound_vars = List.mapi (fun i sort ->
        Quantifier.mk_bound ctx (n - 1 - i) sort
      ) arg_sorts in
      let call    = Expr.mk_app ctx func_decl bound_vars in
      let concl   = conclusion_builder bound_vars in
      let pattern = Quantifier.mk_pattern ctx [call] in
      let symbols = List.mapi
        (fun i _ -> Symbol.mk_string ctx (Printf.sprintf "ax!%d" i)) args in
      let formula = match arg_sorts with
        | [] -> concl
        | _  ->
            Quantifier.expr_of_quantifier
              (Quantifier.mk_forall ctx arg_sorts symbols concl
                None [pattern] [] None None)
      in
      Solver.add solver [formula];
      axiom_registry := formula :: !axiom_registry;
      log "[Solver] Asserted custom axiom for '%s'\n" name

(* Keep assert_nonneg_axiom as a special case of assert_custom_axiom *)
let assert_nonneg_axiom (name : string) (args : (string * string) list) =
  match Hashtbl.find_opt Logic.registered_functions name with
  | None -> ()
  | Some func_decl ->
      let n = List.length args in
      let arg_sorts = List.map (fun (_, t_str) ->
        match t_str with
        | "Int" | "int"   -> Arithmetic.Integer.mk_sort ctx
        | "Bool" | "bool" -> Boolean.mk_sort ctx
        | type_name ->
            (try Hashtbl.find Logic.z3_sort_map type_name
             with Not_found -> Arithmetic.Integer.mk_sort ctx)
      ) args in
      let bound_vars = List.mapi (fun i sort ->
        Quantifier.mk_bound ctx (n - 1 - i) sort
      ) arg_sorts in
      let call    = Expr.mk_app ctx func_decl bound_vars in
      let zero    = Arithmetic.Integer.mk_numeral_i ctx 0 in
      let concl   = Arithmetic.mk_ge ctx call zero in
      let pattern = Quantifier.mk_pattern ctx [call] in
      let symbols = List.mapi
        (fun i _ -> Symbol.mk_string ctx (Printf.sprintf "nonneg!%d" i)) args in
      let formula_pat = Quantifier.expr_of_quantifier
        (Quantifier.mk_forall ctx arg_sorts symbols concl
          None [pattern] [] None None)
      in
      let formula_nopar = Quantifier.expr_of_quantifier
        (Quantifier.mk_forall ctx arg_sorts symbols concl
          None [] [] None None)
      in
      Solver.add solver [formula_pat];
      axiom_registry := formula_nopar :: !axiom_registry;
      log "[Solver] Asserted nonneg axiom for '%s'\n" name

(* After a helper is verified, replace its recursive Z3 definition with a plain
   uninterpreted symbol. Call sites then reason only via the axioms, not by
   unfolding — which lets MBQI enumerate counterexamples freely. *)
let abstract_function (name : string) (args : (string * string) list) (ret_type : string) =
  let mk_sort t_str =
    match t_str with
    | "Int" | "int"   -> Arithmetic.Integer.mk_sort ctx
    | "Bool" | "bool" -> Boolean.mk_sort ctx
    | tn -> (try Hashtbl.find Logic.z3_sort_map tn
             with Not_found -> Arithmetic.Integer.mk_sort ctx)
  in
  let arg_sorts = List.map (fun (_, t) -> mk_sort t) args in
  let ret_sort  = mk_sort ret_type in
  let func_decl = match Hashtbl.find_opt abstracted_decl_cache name with
      | Some cached ->
        log "[Solver] Reusing cached abstracted decl for '%s'\n" name;
        cached
      | None ->
        let fd = FuncDecl.mk_func_decl_s ctx name arg_sorts ret_sort in
        Hashtbl.add abstracted_decl_cache name fd;
        fd
    in
  Hashtbl.replace Logic.registered_functions name func_decl;
  log "[Solver] Abstracted '%s' (plain uninterpreted)\n" name

(* Reusable pattern stripper — needed in both falsify_directly and check_validity_simple *)
let rec strip_patterns expr =
  if Z3.AST.is_quantifier (Z3.Expr.ast_of_expr expr) then
    let q     = Z3.Quantifier.quantifier_of_expr expr in
    let body  = strip_patterns (Z3.Quantifier.get_body q) in
    let sorts = Z3.Quantifier.get_bound_variable_sorts q in
    let names = Z3.Quantifier.get_bound_variable_names q in
    Z3.Quantifier.expr_of_quantifier
      (if Z3.Quantifier.is_universal q
       then Z3.Quantifier.mk_forall ctx sorts names body None [] [] None None
       else Z3.Quantifier.mk_exists ctx sorts names body None [] [] None None)
  else
    let args = Z3.Expr.get_args expr in
    if args = [] then expr
    else
      (try Z3.Expr.mk_app ctx (Z3.Expr.get_func_decl expr)
                               (List.map strip_patterns args)
       with Z3.Error _ -> expr)


(* Fallback solver without persistent state *)

let check_validity_simple var_types f =
  let simple_solver = Solver.mk_solver ctx None in
  (* Load axioms WITH patterns — e-matching fires on concrete constructor ground terms *)
  Solver.add simple_solver !axiom_registry;
  let result =
    try
      let z3_expr = Logic.to_z3 ctx var_types f in
      let z3_expr = strip_patterns z3_expr in
      let not_f = Boolean.mk_not ctx z3_expr in
      let params = Params.mk_params ctx in
      Params.add_int   params (Symbol.mk_string ctx "timeout") 3000;
      Params.add_bool  params (Symbol.mk_string ctx "mbqi") true;
      Params.add_float params (Symbol.mk_string ctx "qi.eager_threshold") 10000.0;
      Solver.set_parameters simple_solver params;
      let rec add_ground_ge expr =
        (try
          let fd    = Z3.Expr.get_func_decl expr in
          let fname = Z3.Symbol.to_string (Z3.FuncDecl.get_name fd) in
          (match Hashtbl.find_opt ge_axiom_idx fname with
           | Some last_idx ->
               let sub = Z3.Expr.get_args expr in
               if last_idx < List.length sub then
                 Solver.add simple_solver
                   [Arithmetic.mk_ge ctx expr (List.nth sub last_idx)]
           | None -> ())
        with _ -> ());
        (try List.iter add_ground_ge (Z3.Expr.get_args expr) with _ -> ())
      in
      add_ground_ge not_f;
      Solver.add simple_solver [not_f];
      match Solver.check simple_solver [] with
      | Solver.UNSATISFIABLE -> V_Valid
      | Solver.SATISFIABLE ->
          begin match Solver.get_model simple_solver with
          | Some model ->
              log "[Solver] Fallback CEX found\n";
              V_Invalid (Model.to_string model)
          | None -> V_Invalid "No model"
          end
      | Solver.UNKNOWN -> V_Unknown
    with e ->
      log "[Solver] Simple check error: %s\n"
        (Printexc.to_string e);
      V_Unknown
  in
  result



(* Main validity checker with DEBUGGING *)
(* Main validity checker with DEBUGGING *)
let check_validity ?(use_fallback=true) var_types f =
  Solver.push solver;

  let result =
    try
      let z3_expr = Logic.to_z3 ctx var_types f in
      let z3_expr = strip_patterns z3_expr in
      let not_f = Boolean.mk_not ctx z3_expr in

      let params = Params.mk_params ctx in
      Params.add_int params (Symbol.mk_string ctx "timeout") 2000;
      Params.add_bool params (Symbol.mk_string ctx "mbqi") true;
      Params.add_float params (Symbol.mk_string ctx "qi.eager_threshold") 1000.0;
      Solver.set_parameters solver params;

      Solver.add solver [not_f];

      (* DEBUG: Print assertions *)
      log "[Solver] Current assertions: %s\n" (Solver.to_string solver);

      match Solver.check solver [] with
      | Solver.UNSATISFIABLE -> V_Valid
      | Solver.SATISFIABLE ->
          begin match Solver.get_model solver with
          | Some model ->
              log "[Solver] FAILED formula was: %s\n" (Expr.to_string z3_expr);
              V_Invalid (Model.to_string model)
          | None -> V_Invalid "No model"
          end
      | Solver.UNKNOWN ->
        if use_fallback then begin
          log "[Solver] Unknown -> Trying fallback solver...\n";
          check_validity_simple var_types f
          end else
                V_Unknown

    with e ->
      log "[Solver] Error: %s\n" (Printexc.to_string e);
      V_Unknown
  in

  Solver.pop solver 1;
  result

(* Assert: ∀(x0:s0)...(x_{n-1}:s_{n-1}). f(x0,...,x_{n-1}) >= x_k
   where x_k is the last Int-sorted argument.
   de-Bruijn rule: in ∀(x0:s0)...(x_{n-1}:s_{n-1}), variable x_i has index n-1-i. *)
let assert_ge_last_int_arg (name : string) (args : (string * string) list) =
  (* Guard: only assert once per function name *)
  if Hashtbl.mem ge_axiom_idx name then ()
  else
  match Hashtbl.find_opt Logic.registered_functions name with
  | None -> ()
  | Some func_decl ->
      let n = List.length args in
      let int_sort = Arithmetic.Integer.mk_sort ctx in
      let arg_sorts = List.map (fun (_, t_str) ->
        match t_str with
        | "Int" | "int"   -> int_sort
        | "Bool" | "bool" -> Boolean.mk_sort ctx
        | tn -> (try Hashtbl.find Logic.z3_sort_map tn
                with Not_found -> int_sort)
      ) args in
      let bound_vars = List.mapi (fun i sort ->
        Quantifier.mk_bound ctx (n - 1 - i) sort
      ) arg_sorts in
      let call = Expr.mk_app ctx func_decl bound_vars in
      (* Find index (in original order) of the last Int-sorted argument *)
      let last_int_idx = ref (-1) in
      List.iteri (fun i (_, t_str) ->
        match t_str with "Int" | "int" -> last_int_idx := i | _ -> ()
      ) args;
      if !last_int_idx >= 0 then begin
        let last_bv  = List.nth bound_vars !last_int_idx in
        let concl    = Arithmetic.mk_ge ctx call last_bv in
        let pattern  = Quantifier.mk_pattern ctx [call] in
        let symbols  = List.mapi
          (fun i _ -> Symbol.mk_string ctx (Printf.sprintf "ge!%d" i)) args in
        let formula  = Quantifier.expr_of_quantifier
          (Quantifier.mk_forall ctx arg_sorts symbols concl
            None [pattern] [] None None)
        in
        Solver.add solver [formula];
        axiom_registry := formula :: !axiom_registry;
        Hashtbl.replace ge_axiom_idx name !last_int_idx;
        log "[Solver] Asserted ge-last-int-arg axiom for '%s'\n" name
      end

let falsify_directly (var_types : (string * basetype) list)
                     (direct_spec : Logic.formula) : validity_result =
  let fresh = Solver.mk_solver ctx None in
  let params = Params.mk_params ctx in
  (* Short timeout: if Z3 can't find a CEX quickly, it won't find one *)
  Params.add_int  params (Symbol.mk_string ctx "timeout") 6000;
  (* Disable MBQI — it is for forall proofs, not existential CEX search *)
  Params.add_bool  params (Symbol.mk_string ctx "smt.mbqi") true;
  Params.add_float params (Symbol.mk_string ctx "qi.eager_threshold") 10000.0;
  Params.add_bool  params (Symbol.mk_string ctx "model") true;
  Solver.set_parameters fresh params;
  Solver.add fresh !axiom_registry;
  try
    let z3_spec  = Logic.to_z3 ctx var_types direct_spec in
    let stripped = strip_patterns z3_spec in
    let neg_spec = Boolean.mk_not ctx stripped in
    log "[CEX] Direct falsification query:\n  NOT %s\n"
      (Expr.to_string stripped);
    Solver.add fresh [neg_spec];
    match Solver.check fresh [] with
    | Solver.UNSATISFIABLE ->
        log "[CEX] Direct: UNSAT — spec is semantically valid\n";
        V_Valid
    | Solver.SATISFIABLE ->
        (match Solver.get_model fresh with
         | Some model ->
             log "[CEX] Direct: SAT — genuine CEX found\n";
             V_Invalid (Model.to_string model)
         | None -> V_Unknown)
    | Solver.UNKNOWN ->
        log "[CEX] Direct: timeout\n";
        V_Unknown
  with e ->
    log "[CEX] falsify_directly error: %s\n" (Printexc.to_string e);
    V_Unknown



let get_registered_function name =
  Hashtbl.find_opt Logic.registered_functions name
let reset () =
  Z3.Solver.reset solver;
  axiom_registry := [];          (* ← ADD THIS *)
  Hashtbl.reset ge_axiom_idx;

type sat_result = Sat | Unsat | SatUnknown

let check_sat var_types formula =
  let s = Z3.Solver.mk_solver ctx None in
  List.iter (fun (name, bt) ->
    let sort = match bt with
      | RInt -> Z3.Arithmetic.Integer.mk_sort ctx
      | RBool -> Z3.Boolean.mk_sort ctx
      | RUserType nm -> (try Hashtbl.find Logic.z3_sort_map nm
                         with Not_found -> Z3.Arithmetic.Integer.mk_sort ctx)
      | _ -> Z3.Arithmetic.Integer.mk_sort ctx
    in
    let _ = Z3.Expr.mk_const_s ctx name sort in ()
  ) var_types;
  let z3f = Logic.to_z3 ctx var_types formula in
  Z3.Solver.add s [z3f];
  match Z3.Solver.check s [] with
  | Z3.Solver.SATISFIABLE   -> Sat
  | Z3.Solver.UNSATISFIABLE -> Unsat
  | Z3.Solver.UNKNOWN       -> SatUnknown
