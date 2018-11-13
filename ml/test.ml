open Arg
open ExtrOcamlIntConv
open FSigmaHCOLtoIR
open FSigmaHCOL
open Camlcoq
open Core

let verbose = ref false
let output_file_name = ref "aout.ll"

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

(* Use the --test option to run unit tests and the quit the program. *)
let args =
  [ ("-o", Set_string output_file_name, "name of .ll file for output")
  ; ("-v", Set verbose, "enables more verbose compilation output")]

let _ =
  Arg.parse args (fun _ -> ())  "USAGE: ./test [-v] [-o file.ll]\n";
  let ast = ocaml_LLVMGen (1+4) 1 [("D", FSHvecValType (Nat.of_int 3))] coq_DynWinFSHCOL "dynwin" in
  output_ll_file !output_file_name ast ;
  exit 0
