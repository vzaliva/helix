open Core
open ExtrOcamlIntConv
open FSigmaHCOLtoIR
open FSigmaHCOL
open Camlcoq

(* OCaml wrapper over extracted Coq code *)
let ocaml_LLVMGen
      (i:int) (o:int)
      (st: float list) (globalnames: string list)
      fshcol (funname: string)
  =
  coq_LLVMGen
    (nat_of_int i) (nat_of_int o) Float64
    (List.map st ~f:(fun x -> FSHFloatVal (Float64V (coqfloat_of_camlfloat x))))
    (List.map globalnames ~f:coqstring_of_camlstring)
    fshcol (coqstring_of_camlstring funname)

let _ =
  match ocaml_LLVMGen (1+4) 1 [0.0] ["D"] coq_DynWinFSHCOL "dynwin" with
  | None ->
     Printf.printf "Error: Compilation FSHCOL compilation failed!\n";
     exit 1
  | Some _ ->
     exit 0
