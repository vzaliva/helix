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
let debug_flag = ref false

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
  | DVALUE_Addr   x -> pp_addr ppf x
  | DVALUE_I1     x -> fprintf ppf "DVALUE_I1(%d)"  (Camlcoq.Z.to_int (DynamicValues.Int1.unsigned x))
  | DVALUE_I8     x -> fprintf ppf "DVALUE_I8(%d)"  (Camlcoq.Z.to_int (DynamicValues.Int8.unsigned x))
  | DVALUE_I32    x -> fprintf ppf "DVALUE_I32(%d)" (Camlcoq.Z.to_int (DynamicValues.Int32.unsigned x))
  | DVALUE_I64    x -> fprintf ppf "DVALUE_I64(%s)" (Int64.to_string (Z.to_int64 (DynamicValues.Int64.unsigned x)))
  | DVALUE_Double x -> fprintf ppf "DVALUE_Double(%F)" (camlfloat_of_coqfloat x)
  | DVALUE_Float  x -> fprintf ppf "DVALUE_Float(%F)"  (camlfloat_of_coqfloat32 x)
  | DVALUE_Undef    -> fprintf ppf "DVALUE_Undef"
  | DVALUE_Poison   -> fprintf ppf "DVALUE_Poison"
  | DVALUE_None     -> fprintf ppf "DVALUE_None"
  | DVALUE_Struct        l -> fprintf ppf "DVALUE_Struct(%a)"        (pp_print_list ~pp_sep:pp_comma_space pp_dvalue) l
  | DVALUE_Packed_struct l -> fprintf ppf "DVALUE_Packet_struct(%a)" (pp_print_list ~pp_sep:pp_comma_space pp_dvalue) l
  | DVALUE_Array         l -> fprintf ppf "DVALUE_Array(%a)"         (pp_print_list ~pp_sep:pp_comma_space pp_dvalue) l
  | DVALUE_Vector        l -> fprintf ppf "DVALUE_Vector(%a)"        (pp_print_list ~pp_sep:pp_comma_space pp_dvalue) l

let debug (msg:string) =
  if !debug_flag then
    Printf.printf "DEBUG: %s\n%!" msg

let rec step m =
  let open Core0 in (* ITree.Core *)
  match observe m with
  (* Internal steps compute as nothing *)
  | TauF x -> step x

  (* We finished the computation *)
  | RetF v -> Ok v

  (* The failE effect is a failure *)
  | VisF (OpenSum.Coq_inrE s, _) ->
     Error (Camlcoq.camlstring_of_coqstring s)

  (* The only visible effects from LLVMIO that should propagate to the interpreter are:
     - Call to external functions
     - Debug
   *)
  | VisF (OpenSum.Coq_inlE e, k) ->
     begin match Obj.magic e with

     | IO.Call(_, f, _) ->
        (Printf.printf "UNINTERPRETED EXTERNAL CALL: %s - returning 0l to the caller\n"
           (Camlcoq.camlstring_of_coqstring f));
        step (k (Obj.magic (DV.DVALUE_I64 DynamicValues.Int64.zero)))

     | IO.Debug(msg) ->
        (debug (Camlcoq.camlstring_of_coqstring msg);
         step (k (Obj.magic DV.DVALUE_None)))

     | IO.Alloca _   -> Error "top-level Alloca"
     | IO.Load (_,_) -> Error "top-level Load"
     | IO.Store (_,_) -> Error "top-level Store"
     | IO.GEP (_,_,_) -> Error "top-level GEP"
     | IO.ItoP _ -> Error "top-level ItoP"
     | IO.PtoI _ -> Error "top-level PtoI"
     end

let gsize t =
  let open FSigmaHCOL in
  match t with
  | FSHnatValType -> 1
  | FSHFloatValType -> 1
  | FSHvecValType n -> Nat.to_int n

let string_of_FloatV fv =
  Float.to_string
    (match fv with
    | FSigmaHCOL.Float32V x -> camlfloat_of_coqfloat x
    | FSigmaHCOL.Float64V x -> camlfloat_of_coqfloat32 x)

let process_test t =
  let oname = camlstring_of_coqstring t.name in
  Random.self_init () ;
  let rs = Nat.to_int t.i + (List.fold t.globals ~init:0 ~f:(fun v (_,g) -> v + gsize g )) in
  let randoms = List.init rs
                  ~f:(fun _ -> let f = binary_float_of_camlfloat (Float.of_int (Random.int Int.max_value)) in
                             match t.ft with
                             | Float32 -> FSigmaHCOL.Float32V f
                             | Float64 -> FSigmaHCOL.Float64V f
                  ) in
  if !debug_flag then
    begin
      Printf.printf "Generating %d floats:\n" rs ;
      List.iteri randoms ~f:(fun i v -> Printf.printf "\t%d\t-\t%s\n" i (string_of_FloatV v))
    end ;
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
       match step trace with
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
    ("-d", Set debug_flag, "enables debuging output");
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
