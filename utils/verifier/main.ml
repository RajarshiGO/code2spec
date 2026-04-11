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

    (* 1. Add a flag parser for '--pretty' to separate JSON vs Terminal output *)
    let (spec_str, file_path, precond_str_opt, pretty_mode) =
      match args with
      | [_; spec; file] -> (spec, file, None, false)
      | [_; "--pretty"; spec; file] -> (spec, file, None, true)
      | [_; spec; file; "--requires"; precond] -> (spec, file, Some precond, false)
      | [_; "--pretty"; spec; file; "--requires"; precond] -> (spec, file, Some precond, true)
      | _ ->
          Printf.eprintf "Usage: %s [--pretty] <spec> <file.ml> [--requires <precondition>]\n" Sys.argv.(0);
          exit 1
    in

    if pretty_mode then begin match precond_str_opt with
      | Some p -> Printf.printf "\x1b[90m[Info]\x1b[0m Using precondition: %s\n" p
      | None -> ()
    end;

    let source = read_file file_path in
    let program = Parser_frontend.parse_program source in

    let result = Typechecker.verify program spec_str precond_str_opt in

    (* 2. Route the output based on the presentation mode *)
    if pretty_mode then begin
      (* Terminal Presentation Layer *)
      match result with
      | Valid -> 
          print_endline "\x1b[1;32m[SUCCESS]\x1b[0m Verification passed."
      | Invalid cex ->
          let (score, total, _) = Typechecker.check_sub_spec program spec_str precond_str_opt in
          print_endline "\x1b[1;31m[FAILED]\x1b[0m Verification failed.";
          print_endline "\x1b[1;35mCounterexample:\x1b[0m";
          (* Re-apply terminal colors to the counterexample keys and values *)
          List.iter (fun (k, v) -> 
            Printf.printf "  \x1b[32m%s\x1b[0m = \x1b[31m%s\x1b[0m\n" k v
          ) cex;
          Printf.printf "\x1b[90mSub-spec score:\x1b[0m %d/%d\n" score total
      | Unknown ->
          let (score, total, _) = Typechecker.check_sub_spec program spec_str precond_str_opt in
          print_endline "\x1b[1;33m[UNKNOWN]\x1b[0m Solver returned unknown state.";
          Printf.printf "\x1b[90mSub-spec score:\x1b[0m %d/%d\n" score total
    end else begin
      (* Original JSON Presentation Layer *)
      let json = match result with
        | Valid ->
            "{\"status\": \"valid\"}"
        | Invalid cex ->
            let (score, total, _) = Typechecker.check_sub_spec program spec_str precond_str_opt in
            let cex_entries = List.map (fun (key, value) ->
              Printf.sprintf "\"%s\": \"%s\"" key value
            ) cex in
            let cex_json = String.concat ", " cex_entries in
            Printf.sprintf "{\"status\": \"invalid\", \"cex\": {%s}, \"sub_spec_score\": \"%d/%d\"}" cex_json score total
        | Unknown ->
            let (score, total, _) = Typechecker.check_sub_spec program spec_str precond_str_opt in
            Printf.sprintf "{\"status\": \"unknown\", \"sub_spec_score\": \"%d/%d\"}" score total
      in
      print_endline json
    end

  with
  | Parser_frontend.ParseError msg ->
      Printf.printf "{\"status\": \"error\", \"message\": \"Parse error: %s\"}\n" (String.escaped msg)
  | Typechecker.TypeError msg ->
      Printf.printf "{\"status\": \"error\", \"message\": \"Type error: %s\"}\n" (String.escaped msg)
  | e ->
      Printf.printf "{\"status\": \"error\", \"message\": \"%s\"}\n" (String.escaped (Printexc.to_string e))