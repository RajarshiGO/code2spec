(* ============================================================================ *)
(* MAIN: Command-line Interface with Precondition Support *)
(* ============================================================================ *)

open Typechecker

let read_file file =
  let channel = open_in file in
  let length = in_channel_length channel in
  let contents = really_input_string channel length in
  close_in channel;
  contents

let () =
  try
    let args = Array.to_list Sys.argv in

    let (spec_str, file_path, precond_str_opt) =
      match args with
      | [_; spec; file] -> (spec, file, None)
      | [_; spec; file; "--requires"; precond] -> (spec, file, Some precond)
      | _ ->
          Printf.eprintf "Usage: %s <spec> <file.ml> [--requires <precondition>]\n" Sys.argv.(0);
          exit 1
    in

    (* Print precondition if provided *)
    begin match precond_str_opt with
    | Some p -> Printf.printf "[Info] Using precondition: %s\n" p
    | None -> ()
    end;

    let source = read_file file_path in
    let program = Parser_frontend.parse_program source in

    (* Parse spec *)
    (* Parse spec string later with parameters in scope *)

    (* Pass precondition as STRING (not parsed yet) *)
    (* typechecker.ml will parse it later when function args are known *)
    (* let (score, total, _) = Typechecker.check_sub_spec program spec_str precond_str_opt in *)
    let result = Typechecker.verify program spec_str precond_str_opt in

    let json = match result with
      | Valid ->
          "{\"status\": \"valid\"}"
      | Invalid cex ->
          let (score, total, _) = Typechecker.check_sub_spec program spec_str precond_str_opt in
          let cex_entries = List.map (fun (key, value) ->
            Printf.sprintf "\"%s\": \"%s\"" key value
          ) cex in
          let cex_json = String.concat ", " cex_entries in
          Printf.sprintf
                      "{\"status\": \"invalid\", \"cex\": {%s}, \"sub_spec_score\": \"%d/%d\"}"
                      cex_json score total
      | Unknown ->
          let (score, total, _) = Typechecker.check_sub_spec program spec_str precond_str_opt in
          Printf.sprintf {|{"status": "unknown", "sub_spec_score": "%d/%d"}|} score total
    in
    print_endline json

  with
  | Parser_frontend.ParseError msg ->
      Printf.printf "{\"status\": \"error\", \"message\": \"Parse error: %s\"}\n"
        (String.escaped msg)
  | Typechecker.TypeError msg ->
      Printf.printf "{\"status\": \"error\", \"message\": \"Type error: %s\"}\n"
        (String.escaped msg)
  | e ->
      Printf.printf "{\"status\": \"error\", \"message\": \"%s\"}\n"
        (String.escaped (Printexc.to_string e))
