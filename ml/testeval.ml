open Arg
open Camlcoq
open Core
open Tests

let verbose = ref false
let printtests = ref false
let single = ref ""

module DV = Tests.IO.DV
module A = ANSITerminal

let p_OK name =
  A.printf [A.black; A.on_green] "OK" ;
  A.printf [A.yellow] ": %s" name ;
  A.printf [] " Result:\n"

let print_dvalue dv : unit =
  match dv with
  | DV.DVALUE_I1 (x) -> A.printf [] "DVALUE_I1(%d)\n" (Camlcoq.Z.to_int (DynamicValues.Int1.unsigned x))
  | DV.DVALUE_I8 (x) -> A.printf [] "DVALUE_I8(%d)\n" (Camlcoq.Z.to_int (DynamicValues.Int8.unsigned x))
  | DV.DVALUE_I32 (x) -> A.printf [] "DVALUE_I32(%d)\n" (Camlcoq.Z.to_int (DynamicValues.Int32.unsigned x))
  | DV.DVALUE_I64 (x) -> A.printf [] "DVALUE_I64(%d) [possible precision loss: converted to OCaml int]\n"
                       (Camlcoq.Z.to_int (DynamicValues.Int64.unsigned x))
  | _ -> A.printf [] "Program terminated with non-Integer value.\n"

let rec step tname m =
  match Lazy.force m with
  | ITree.Tau x -> step tname x
  | ITree.Ret (Datatypes.Coq_inr v) ->
     A.printf [A.black; A.on_green] "OK" ;
     A.printf [A.yellow] ": %s" tname ;
     A.printf [] " Result:\n" ;
     print_dvalue v ;
     true
  | ITree.Ret (Datatypes.Coq_inl s) -> A.printf [] "ERROR: %s\n" (Camlcoq.camlstring_of_coqstring s) ; false
  | ITree.Vis (e, k) ->
    begin match Obj.magic e with
      | Tests.IO.Call(_, f, _) ->
        (A.printf [] "UNINTERPRETED EXTERNAL CALL: %s - returning 0l to the caller\n" (Camlcoq.camlstring_of_coqstring f));
        step tname (k (Obj.magic (DV.DVALUE_I64 DynamicValues.Int64.zero)))
      | Tests.IO.GEP(_, _, _) -> A.printf [] "GEP failed" ; false
      | _ -> A.printf [] "should have been handled by the memory model\n" ; false
    end

let process_test t =
  let oname = camlstring_of_coqstring t.name in
  match Tests.runFSHCOLTest t [] with
  | None ->
     A.printf [A.white; A.on_red] "Error" ;
     A.printf [A.yellow] ": %s" oname ;
     false
  | Some trace ->
     step oname trace

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
