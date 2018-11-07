open Arg
open ExtrOcamlIntConv
open FSigmaHCOLtoIR
open FSigmaHCOL
open Camlcoq
open Llvm_printer
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
  let open Pervasives in
  let open Llvm_printer in
  let channel = open_out filename in
  toplevel_entities (Format.formatter_of_out_channel channel) ast;
  close_out channel

(* Use the --test option to run unit tests and the quit the program. *)
let args =
  [ ("-o", Set_string output_file_name, "name of .ll file for output")
  ; ("-v", Set verbose, "enables more verbose compilation output")]

let _ =
  Arg.parse args (fun _ -> ())  "USAGE: ./test [-v] [-o file.ll]\n";
  match ocaml_LLVMGen (1+4) 1 [("D", FSHvecValType (Nat.of_int 3))] coq_DynWinFSHCOL "dynwin" with
  | None ->
     Printf.printf "Error: Compilation FSHCOL compilation failed!\n";
     exit 1
  | Some ast ->
     output_ll_file !output_file_name ast ;
     exit 0
