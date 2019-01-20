open Arg
open Camlcoq
open Core
open Tests
open CoqUtil

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

let p_OK name =
  A.printf [A.black; A.on_green] "OK" ;
  A.printf [A.yellow] ": %s" name ;
  A.printf [] " Result:\n"

let print_dvalue dv : unit =
  match dv with
  | DV.DVALUE_I1 (x) -> A.printf [A.green] "DVALUE_I1(%d)\n" (Camlcoq.Z.to_int (DynamicValues.Int1.unsigned x))
  | DV.DVALUE_I8 (x) -> A.printf [A.green] "DVALUE_I8(%d)\n" (Camlcoq.Z.to_int (DynamicValues.Int8.unsigned x))
  | DV.DVALUE_I32 (x) -> A.printf [A.green] "DVALUE_I32(%d)\n" (Camlcoq.Z.to_int (DynamicValues.Int32.unsigned x))
  | DV.DVALUE_I64 (x) -> A.printf [A.green] "DVALUE_I64(%d) [possible precision loss: converted to OCaml int]\n"
                       (Camlcoq.Z.to_int (DynamicValues.Int64.unsigned x))
  | _ -> A.printf [A.green] "Program terminated with non-Integer value.\n"

let rec step tname m =
  match Lazy.force m with
  | ITree.Tau x -> step tname x
  | ITree.Ret (Datatypes.Coq_inr v) ->
     A.printf [A.black; A.on_green] "OK" ;
     A.printf [A.yellow] ": %s" tname ;
     A.printf [] " Result:\n" ;
     print_dvalue v ;
     true
  | ITree.Ret (Datatypes.Coq_inl s) -> A.printf [A.red] "ERROR: %s\n" (Camlcoq.camlstring_of_coqstring s) ; false
  | ITree.Vis (e, k) ->
    begin match Obj.magic e with
      | Tests.IO.Call(_, f, _) ->
        (A.printf [A.yellow] "UNINTERPRETED EXTERNAL CALL: %s - returning 0l to the caller\n" (Camlcoq.camlstring_of_coqstring f));
        step tname (k (Obj.magic (DV.DVALUE_I64 DynamicValues.Int64.zero)))
      | Tests.IO.GEP(_, _, _) -> A.printf [] "GEP failed" ; false
      | _ -> A.printf [A.red] "should have been handled by the memory model\n" ; false
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
  | None ->
     A.printf [A.white; A.on_red] "Error" ;
     A.printf [A.yellow] ": %s" oname ;
     false
  | Some (ast, trace) ->
     if !justcompile then
       (output_ll_file (output_file_prefix ^ oname ^ ".ll") ast ; true)
     else
         let res = step oname trace in
         if not res then
           begin
             A.printf [A.white; A.on_red] "Eval Error" ;
             A.printf [A.yellow] ": %s : \n" oname
           end ;
         res

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
