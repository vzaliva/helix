open Arg
open Camlcoq
open Core
open Tests
open CoqUtil
open Format

let verbose = ref false
let printtests = ref false
let single = ref ""
let justcompile = ref false
let output_file_prefix = "test_"

module DV = Tests.IO.DV
module A = ANSITerminal

let output_ll_file filename ast =
  let open Format in
  let channel = Out_channel.create filename in
  let ppf = formatter_of_out_channel channel in
  Llvm_printer.toplevel_entities ppf ast;
  pp_force_newline ppf ();
  pp_print_flush ppf () ;
  Out_channel.close channel

(* TODO: probaly should be part of ADDRESS module interface*)
let pp_addr : Format.formatter -> M.addr -> unit
  = fun ppf _ -> fprintf ppf "DVALUE_Addr(?)"

let rec pp_dvalue : Format.formatter -> DV.dvalue -> unit =
  let pp_comma_space ppf () = pp_print_string ppf ", " in
  fun ppf ->
  function
  | DVALUE_Addr x -> pp_addr ppf x
  | DV.DVALUE_I1 x -> fprintf ppf "DVALUE_I1(%d)" (Camlcoq.Z.to_int (DynamicValues.Int1.unsigned x))
  | DV.DVALUE_I8 x -> fprintf ppf "DVALUE_I8(%d)" (Camlcoq.Z.to_int (DynamicValues.Int8.unsigned x))
  | DV.DVALUE_I32 x -> fprintf ppf "DVALUE_I32(%d)" (Camlcoq.Z.to_int (DynamicValues.Int32.unsigned x))
  | DV.DVALUE_I64 x -> fprintf ppf "DVALUE_I64(~%d)" (Camlcoq.Z.to_int (DynamicValues.Int64.unsigned x)) (* ~ means possible precision loss: converted to OCaml int *)
  | DVALUE_Double x -> fprintf ppf "DVALUE_Double(%f)" (camlfloat_of_coqfloat x)
  | DVALUE_Float x -> fprintf ppf "DVALUE_Float(%f)" (camlfloat_of_coqfloat32 x)
  | DVALUE_Undef -> fprintf ppf "DVALUE_Undef"
  | DVALUE_Poison -> fprintf ppf "DVALUE_Poison"
  | DVALUE_None -> fprintf ppf "DVALUE_None"
  | DVALUE_Struct l -> fprintf ppf "DVALUE_Struct(%a)" (pp_print_list ~pp_sep:pp_comma_space pp_dvalue) l
  | DVALUE_Packed_struct l -> fprintf ppf "DVALUE_Packet_struct(%a)" (pp_print_list ~pp_sep:pp_comma_space pp_dvalue) l
  | DVALUE_Array l -> fprintf ppf "DVALUE_Array(%a)" (pp_print_list ~pp_sep:pp_comma_space pp_dvalue) l
  | DVALUE_Vector l -> fprintf ppf "DVALUE_Vector(%a)" (pp_print_list ~pp_sep:pp_comma_space pp_dvalue) l

let rec step tname m =
  match Lazy.force m with
  | ITree.Tau x -> step tname x
  | ITree.Ret (Datatypes.Coq_inr v) -> Ok v
  | ITree.Ret (Datatypes.Coq_inl s) -> Error (Camlcoq.camlstring_of_coqstring s)
  | ITree.Vis (e, k) ->
     begin match Obj.magic e with
     | Tests.IO.Call(_, f, _) ->
        (A.printf [A.yellow] "UNINTERPRETED EXTERNAL CALL: %s - returning 0l to the caller\n" (Camlcoq.camlstring_of_coqstring f));
        step tname (k (Obj.magic (DV.DVALUE_I64 DynamicValues.Int64.zero)))
     | Tests.IO.GEP(_, _, _) -> Error "GEP failed"
     | _ -> Error "This should have been handled by the memory model"
     end

let process_test t =
  let oname = camlstring_of_coqstring t.name in
  Random.self_init () ;
  let randoms = List.init 1000 ~f:(const
                                     (let f = binary_float_of_camlfloat (Float.of_int (Random.int Int.max_value)) in
                                      match t.ft with
                                      | Float32 -> FSigmaHCOL.Float32V f
                                      | Float64 -> FSigmaHCOL.Float64V f)
                  ) in
  match Tests.runFSHCOLTest t randoms with
  | (None,_) ->
     A.printf [A.white; A.on_red] "Error" ;
     A.printf [A.yellow] ": %s" oname ;
     A.printf [] " F-HCOL Compilation failed" ;
     false
  | (Some ast, None) ->
     if !justcompile then
       (output_ll_file (output_file_prefix ^ oname ^ ".ll") ast ; true)
     else
       begin
         A.printf [A.white; A.on_red] "Error" ;
         A.printf [A.yellow] ": %s" oname ;
         A.printf [] " LLVM Compilation failed" ;
         false
       end
  | (Some ast, Some trace) ->
     if !justcompile then
       (output_ll_file (output_file_prefix ^ oname ^ ".ll") ast ; true)
     else
       match step oname trace with
       | Error msg ->
          A.printf [A.white; A.on_red] "Error";
          A.printf [A.yellow] ": %s :" oname ;
          A.printf [] "LLVM Intepretation failed with: %s\n" msg ;
          false
       | Ok dv ->
          A.printf [A.black; A.on_green] "OK" ;
          A.printf [A.yellow] ": %s :" oname ;
          A.printf [] "Result:\n" ;
          pp_dvalue std_formatter dv ;
          A.printf [] "\n" ;
          true

let args =
  [
    ("-t", Set_string single, "run single test") ;
    ("-c", Set justcompile, "save IR code to file and exit") ;
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
