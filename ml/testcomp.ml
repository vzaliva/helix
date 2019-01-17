open Arg
open Compiler
open Camlcoq
open Core
open Tests

let verbose = ref false
let printtests = ref false
let output_file_prefix = "test_"
let single = ref ""

let output_ll_file filename ast =
  let open Format in
  let channel = Out_channel.create filename in
  let ppf = formatter_of_out_channel channel in
  Llvm_printer.toplevel_entities ppf ast;
  pp_force_newline ppf ();
  pp_print_flush ppf () ;
  Out_channel.close channel

let process_test { ft=ft; i=i ; o=o; name=name; op=op; globals=globals} =
  let module A=ANSITerminal in
  let oname = camlstring_of_coqstring name in
  match coq_LLVMGen i o ft globals op name with
  | Datatypes.Coq_inl msg ->
     A.printf [A.white; A.on_red] "Error" ;
     A.printf [A.yellow] ": %s" oname ;
     A.printf [] " : Error: " ;
     A.printf [A.red] "%s\n" (camlstring_of_coqstring msg) ;
     false
  | Datatypes.Coq_inr ast ->
     A.printf [A.black; A.on_green] "OK" ;
     A.printf [A.yellow] ": %s" oname ;
     A.printf [] " compilation succeeded.\n" ;
     output_ll_file (output_file_prefix ^ oname ^ ".ll") ast ;
     true

(* Use the --test option to run unit tests and the quit the program. *)
let args =
  [
    ("-t", Set_string single, "run single test") ;
    ("-v", Set verbose, "enables more verbose compilation output");
    ("-p", Set printtests, "print names of all tests (for automation)");
  ]

let _ =
  Arg.parse args (fun _ -> ())  "USAGE: ./testcomp [-v] [-p] [t <name>]\n";
  if !printtests
  then
    begin
      ignore (List.map all_tests
                ~f:(fun t -> Printf.printf "%s\n" (camlstring_of_coqstring (name t))));
      exit 0
    end
  else
    let t = if !single = "" then all_tests
            else List.filter all_tests ~f:(fun x -> camlstring_of_coqstring (name x) = !single) in
    exit (if List.fold (List.map t ~f:process_test) ~init:true ~f:(&&)
          then 0 else 1)
