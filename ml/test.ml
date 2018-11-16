open Arg
open ExtrOcamlIntConv
open FSigmaHCOLtoIR
open FSigmaHCOL
open Camlcoq
open Core
open Tests

let verbose = ref false
let output_file_prefix = "test_"

(* OCaml wrapper over extracted Coq code *)
let ocaml_LLVMGen
      (i:int) (o:int)
      (globalnames: (string*coq_FSHValType) list)
      fshcol (funname: string)
  =
  coq_LLVMGen
    (nat_of_int i) (nat_of_int o) Float64
    (List.map globalnames ~f:(fun (x,y) -> (coqstring_of_camlstring x, y)))
    fshcol (coqstring_of_camlstring funname)

let output_ll_file filename ast =
  let open Format in
  let channel = Out_channel.create filename in
  let ppf = formatter_of_out_channel channel in
  Llvm_printer.toplevel_entities ppf ast;
  pp_force_newline ppf ();
  pp_print_flush ppf () ;
  Out_channel.close channel

let process_test { i=i ; o=o; name=name; op=op; globals=globals} =
  let oname = camlstring_of_coqstring name in
  match coq_LLVMGen i o Float64 globals op name with
  | None ->
     Printf.printf "Error: %s compilation failed!\n" oname;
     false
  | Some ast ->
     Printf.printf "OK: %s compilation succeeded.\n" oname;
     output_ll_file (output_file_prefix ^ oname ^ ".ll") ast ;
     true

(* Use the --test option to run unit tests and the quit the program. *)
let args =
  [ ("-v", Set verbose, "enables more verbose compilation output")]

let _ =
  Arg.parse args (fun _ -> ())  "USAGE: ./test [-v]\n";
  if List.fold
       (List.map all_tests ~f:process_test)
       ~init:true ~f:(&&)
  then
    exit 0
  else
    exit 1
