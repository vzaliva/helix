open Arg
open Camlcoq
open Core (* Jane Street Core, not ITree.Core! *)
open Tests
open Format

let verbose = ref false
let printtests = ref false
let single = ref ""
let justcompile = ref false
let output_file_prefix = "test_"

module AT = ANSITerminal

let output_ll_file filename ast =
  let open Format in
  let channel = Out_channel.create filename in
  let ppf = formatter_of_out_channel channel in
  Llvm_printer.toplevel_entities ppf ast;
  pp_force_newline ppf ();
  pp_print_flush ppf () ;
  Out_channel.close channel

let gsize t =
  let open Compiler in
  match t with
  | FSHnatValType -> 1
  | FSHFloatValType -> 1
  | FSHvecValType n -> Nat.to_int n

let string_of_FloatV fv =
  Float.to_string (camlfloat_of_coqfloat fv)

let randomFloat range =
  Random.float
    (if Random.bool ()
     then range
     else Float.neg range)

let string_of_float_full f =
  (* Due to the limited number of bits in the representation of doubles, the maximal precision is 324. See Wikipedia. *)
  let s = sprintf "%.350f" f in
  Str.global_replace (Str.regexp "0+$") "" s

let pp_binary64 ppf v =
    fprintf ppf "%s" (string_of_float_full (camlfloat_of_coqfloat v))

let process_test t =
  let oname = camlstring_of_coqstring t.name in
  Random.self_init () ;
  let rs = Nat.to_int t.i + (List.fold t.globals ~init:0 ~f:(fun v (_,g) -> v + gsize g )) in
  let randoms = List.init rs ~f:(fun _ -> coqfloat_of_camlfloat (randomFloat 3.14E8)) in
  if !Interpreter.debug_flag then
    begin
      Printf.printf "Generating %d floats:\n" rs ;
      List.iteri randoms ~f:(fun i v -> Printf.printf "\t%d\t-\t%s\n" i (string_of_FloatV v))
    end ;

  begin
    if !justcompile then
      match Tests.runFSHCOLTest t !justcompile randoms with
      | ((None, _) , msg) ->
         AT.printf [AT.white; AT.on_red] "Error" ;
         AT.printf [AT.yellow] ": %s" oname ;
         AT.printf [] " F-HCOL Compilation failed:" ;
         AT.printf [AT.magenta] " %s\n" (camlstring_of_coqstring msg)  ;
         false
      | ((Some ast, _), _) ->
         output_ll_file (output_file_prefix ^ oname ^ ".ll") ast ;
         true
    else
      let eres = Tests.evalFSHCOLTest t randoms in
      let rres = Tests.runFSHCOLTest t !justcompile randoms in

      let print_eres v =
        AT.printf [AT.green] "Evaluation Result:\n" ;
        let ppf = std_formatter in
        pp_print_list ~pp_sep:Llvm_printer.pp_comma_space pp_binary64 ppf v ;
        pp_force_newline ppf ();
        pp_print_flush ppf () in

      let print_dv dv =
        AT.printf [AT.green] "Interpretation Result:\n" ;
        let ppf = std_formatter in
        Interpreter.pp_dvalue ppf dv ;
        pp_force_newline ppf ();
        pp_print_flush ppf ()  in

      AT.printf [AT.yellow] "\n%s:\n" oname ;

      (* Compilation *)
      let cflag =
        (match rres with
         | ((Some _, _), _) ->
            AT.printf [AT.black; AT.on_green] "OK" ;
            AT.printf [] " F-HCOL Compilation passed\n" ;
            true
         | ((None, _) , msg) ->
            AT.printf [AT.white; AT.on_red] "Error" ;
            AT.printf [AT.yellow] " F-HCOL Compilation failed:" ;
            AT.printf [AT.magenta] " %s\n" (camlstring_of_coqstring msg)  ;
            false
        ) in
      (* Interpretation *)
      let (iflag,tres) =
        (match rres with
         | ((_, Some trace), _) ->
            begin
              let tres = Interpreter.step trace in
              match tres with
              | Error msg ->
                 AT.printf [AT.white; AT.on_red] "Error";
                 AT.printf [] " LLVM Intepretation failed with: %s\n" msg ;
                 (false, tres)
              | Ok (DVALUE_Array _) ->
                 AT.printf [AT.black; AT.on_green] "OK" ;
                 AT.printf [] " Interpretation passed\n" ;
                 (true, tres)
              | Ok dv ->
                 AT.printf [AT.white; AT.on_red] "Error";
                 AT.printf [] " LLVM Intepretation did not produce array\n";
                 print_dv dv;
                 (false, tres)
            end
         | ((_, None), msg) ->
            AT.printf [AT.white; AT.on_red] "Error" ;
            AT.printf [] " F-HCOL Interpretation did not produce trace:" ;
            AT.printf [AT.magenta] " %s\n" (camlstring_of_coqstring msg)  ;
            (false, Error "no trace produced")
        ) in
      let eflag =
        (match eres with
         | Coq_inr _ ->
            AT.printf [AT.black; AT.on_green] "OK" ;
            AT.printf [] " Evaluation passed\n" ;
            true
         | Coq_inl msg ->
            AT.printf [AT.white; AT.on_red] "Error" ;
            AT.printf [] " F-HCOL Evaluation failed:" ;
            AT.printf [AT.magenta] " %s\n" (camlstring_of_coqstring msg)  ;
            false
        ) in

      let dflag =
        (match tres, eres with
         | Ok (DVALUE_Array arr), Coq_inr v ->
            begin
              match List.fold2 v arr ~init:true ~f:(fun p ve de ->
                        match de with
                        | DVALUE_Double d -> p && (Floats.Float.cmp Ceq d ve)
                        | _ -> false
                      ) with
              | Ok bv ->
                 if bv then
                   begin
                     AT.printf [AT.black; AT.on_green] "OK" ;
                     AT.printf [] " Results match\n" ;
                     true
                   end
                 else
                   begin
                     AT.printf [AT.white; AT.on_red] "Error" ;
                     AT.printf [] " Value comparison failed: values differ" ;
                     print_dv (DVALUE_Array arr) ;
                     print_eres v ;
                     false
                   end
              | Unequal_lengths ->
                 AT.printf [AT.white; AT.on_red] "Error" ;
                 AT.printf [] " Value comparison failed: different vector length" ;
                 print_dv (DVALUE_Array arr) ;
                 print_eres v ;
                 false
            end
         | _,_ ->
            false
        ) in

      (cflag && iflag && eflag && dflag)
  end

let args =
  [
    ("-t", Set_string single, "run single test") ;
    ("-c", Set justcompile, "save IR code to file and exit") ;
    ("-v", Set verbose, "enables more verbose compilation output");
    ("-d", Set Interpreter.debug_flag, "enables debuging output");
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
    let open Core.String in
    let t = if !single = "" then all_tests
            else List.filter all_tests ~f:(fun x -> camlstring_of_coqstring (name x) = !single) in
    exit (if List.fold (List.map t ~f:process_test) ~init:true ~f:(&&)
          then 0 else 1)
