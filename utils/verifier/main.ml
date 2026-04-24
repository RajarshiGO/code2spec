(* File: src/main.ml *)
open Typechecker

let read_file file =
  let channel = open_in file in
  let length = in_channel_length channel in
  let contents = really_input_string channel length in
  close_in channel;
  contents

let () =
  let spec_str = ref "" in
  let file_path = ref "" in
  let precond_str_opt = ref None in

  let set_precond p = precond_str_opt := Some p in

  let anon_fun arg =
    if !spec_str = "" then spec_str := arg
    else if !file_path = "" then file_path := arg
    else raise (Arg.Bad "Too many positional arguments provided.")
  in

  let speclist = [
    ("--requires", Arg.String set_precond, "Set the precondition for verification");
    ("--api", Arg.Set Pprint.api_mode, "Enable API mode (suppresses logs, outputs only JSON)");
  ] in

  let usage_msg = "Usage: " ^ Sys.argv.(0) ^ " <spec> <file.ml> [--requires <precondition>] [--api]" in

  try
    Arg.parse speclist anon_fun usage_msg;

    if !spec_str = "" || !file_path = "" then (
      Arg.usage speclist usage_msg;
      exit 1
    );

    (* Log precondition if provided, suppressed in API mode *)
    begin match !precond_str_opt with
    | Some p -> Pprint.log_info "Using precondition: %s" p
    | None -> ()
    end;

    let source = read_file !file_path in
    let program = Parser_frontend.parse_program source in

    let result = Typechecker.verify program !spec_str !precond_str_opt in

    let json = match result with
      | Valid ->
          "{\"status\": \"valid\"}"
      | Invalid cex ->
          let (score, total, _) = Typechecker.check_sub_spec program !spec_str !precond_str_opt in
          let cex_entries = List.map (fun (key, value) ->
            Printf.sprintf "\"%s\": \"%s\"" key value
          ) cex in
          let cex_json = String.concat ", " cex_entries in
          Printf.sprintf
            "{\"status\": \"invalid\", \"cex\": {%s}, \"sub_spec_score\": \"%d/%d\"}"
            cex_json score total
      | Unknown ->
          let (score, total, _) = Typechecker.check_sub_spec program !spec_str !precond_str_opt in
          Printf.sprintf {|{"status": "unknown", "sub_spec_score": "%d/%d"}|} score total
    in
    
    (* Always print the final payload *)
    print_endline json

  with
  | Arg.Bad msg | Arg.Help msg ->
      print_endline msg;
      exit 1
  | Parser_frontend.ParseError msg ->
      Printf.printf "{\"status\": \"error\", \"message\": \"Parse error: %s\"}\n"
        (String.escaped msg)
  | Typechecker.TypeError msg ->
      Printf.printf "{\"status\": \"error\", \"message\": \"Type error: %s\"}\n"
        (String.escaped msg)
  | e ->
      Printf.printf "{\"status\": \"error\", \"message\": \"%s\"}\n"
        (String.escaped (Printexc.to_string e))