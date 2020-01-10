Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.BinNums. (* for Z scope *)
Require Import Coq.ZArith.BinInt.

Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.LLVMGen.Compiler.
Require Import Helix.LLVMGen.Externals.
Require Import Helix.Util.ErrorSetoid.

Require Import Vellvm.Numeric.Fappli_IEEE_extra.
Require Import Vellvm.LLVMEvents.
Require Import Vellvm.Denotation.
Require Import Vellvm.Handlers.Memory.
Require Import Vellvm.TopLevel.
Require Import Vellvm.LLVMAst.

Require Import ITree.ITree.

Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

Require Import ExtLib.Structures.Monads.

Require Import Helix.LLVMGen.Correctness.

Import ListNotations.

Import MDSHCOLOnFloat64.

(* sample definition to be moved to DynWin.v *)
Local Open Scope nat_scope.
Definition BinOp_less_test :=
  DSHBinOp 2 (PVar 1) (PVar 0) (AZless (AVar 1) (AVar 0)).

Definition BinOp_plus_test :=
  DSHBinOp 2 (PVar 1) (PVar 0) (APlus (AVar 1) (AVar 0)).

Definition IMap_plus1_test :=
  DSHIMap 8 (PVar 1) (PVar 0) (APlus (AConst Float64One) (AVar 0)).

Definition IMap_plusD_test :=
  DSHIMap 8 (PVar 2) (PVar 1) (APlus (AVar 0) (AVar 2)).

Definition Compose_pointwise_test :=
  DSHSeq IMap_plus1_test IMap_plus1_test.

Definition IReduction_test :=
  DSHAlloc 1
           (DSHSeq (DSHMemInit 1 (PVar 0) FSigmaHCOL.Float64Zero)
                   (DSHLoop 2
                            (DSHSeq
                               (DSHAlloc 2
                                         (DSHSeq (DSHIMap 2 (PVar 4) (PVar 0) (AAbs (AVar 0)))
                                                 (DSHBinOp 1 (PVar 0) (PVar 3)
                                                           (AAbs (AMinus (AVar 1) (AVar 0))))))
                               (DSHMemMap2 1 (PVar 1) (PVar 2) (PVar 2) (AMax (AVar 1) (AVar 0)))))).


Definition SUMUnion_test :=
DSHSeq (DSHIMap 4 (PVar 2) (PVar 1) (AAbs (AVar 0)))
       (DSHIMap 4 (PVar 2) (PVar 1) (AMult (AVar 0) (ANth (MPtrDeref (PVar 2)) (NVar 1)))).

Definition DynWin_test: DSHOperator :=
DSHAlloc 2
  (DSHSeq
     (DSHSeq
        (DSHAlloc 1
           (DSHSeq
              (DSHAlloc 1
                 (DSHSeq
                    (DSHMemInit 1 (PVar 0) FSigmaHCOL.Float64Zero)
                    (DSHLoop 3
                       (DSHSeq
                          (DSHAlloc 1
                             (DSHSeq
                                (DSHAssign (PVar 7, NConst 0)
                                   (PVar 0, NConst 0))
                                (DSHAlloc 1
                                   (DSHSeq
                                      (DSHPower (NVar 2)
                                         (PVar 1, NConst 0)
                                         (PVar 0, NConst 0)
                                         (AMult (AVar 1) (AVar 0))
                                         FSigmaHCOL.Float64One)
                                      (DSHIMap 1 (PVar 0) (PVar 4)
                                         (AMult (AVar 0)
                                            (ANth
                                               (MPtrDeref (PVar 8))
                                               (NVar 4))))))))
                          (DSHMemMap2 1 (PVar 1) (PVar 2) (PVar 2)
                             (APlus (AVar 1) (AVar 0)))))))
              (DSHAssign (PVar 0, NConst 0) (PVar 1, NConst 0))))
        (DSHAlloc 1
           (DSHSeq
              (DSHAlloc 1
                 (DSHSeq
                    (DSHMemInit 1 (PVar 0) FSigmaHCOL.Float64Zero)
                    (DSHLoop 2
                       (DSHSeq
                          (DSHAlloc 2
                             (DSHSeq
                                (DSHLoop 2
                                   (DSHAlloc 1
                                      (DSHSeq
                                         (DSHAssign
                                            (PVar 9,
                                            NPlus
                                              (NPlus (NConst 1)
                                                 (NMult (NVar 3)
                                                    (NConst 1)))
                                              (NMult (NVar 1)
                                                 (NMult (NConst 2)
                                                    (NConst 1))))
                                            (PVar 0, NConst 0))
                                         (DSHAssign
                                            (PVar 0, NConst 0)
                                            (PVar 2, NVar 1)))))
                                (DSHBinOp 1 (PVar 0) (PVar 3)
                                   (AAbs (AMinus (AVar 1) (AVar 0))))))
                          (DSHMemMap2 1 (PVar 1) (PVar 2) (PVar 2)
                             (AMax (AVar 1) (AVar 0)))))))
              (DSHAssign (PVar 0, NConst 0) (PVar 1, NConst 1)))))
     (DSHBinOp 1 (PVar 0) (PVar 2) (AZless (AVar 1) (AVar 0)))).


Local Close Scope nat_scope.


Record FSHCOLTest :=
  mkFSHCOLTest
    {
      i: nat;
      o: nat;
      name: string;
      globals: list (string * FSHValType) ;
      op: DSHOperator;
    }.

Local Open Scope string_scope.

Definition all_tests :=
  [
    {| i:=5; o:=1; name:="dynwin64"; op:=DynWin_test ; globals:=[("D", FSHvecValType 3)] |} ;
      {| i:=4; o:=2; name:="binop_less"; op:=BinOp_less_test; globals:=[] |} ;
      {| i:=4; o:=2; name:="binop_plus"; op:=BinOp_plus_test; globals:=[] |} ;
      {| i:=2; o:=1; name:="ireduction"; op:=IReduction_test; globals:=[] |} ;
      (*
      {| name:="iunion"; op:=IUnion_test; globals:=[] |} ;
      {| name:="inductor"; op:=Inductor_test; globals:=[] |} ;
       *)
      {| i:=4; o:=4; name:="sumunion"; op:=SUMUnion_test; globals:=[("D", FSHvecValType 4)] |} ;
      {| i:=8; o:=8; name:="pointwise_plus1"; op:=IMap_plus1_test; globals:=[] |} ;
      {| i:=8; o:=8; name:="pointwise_plusD"; op:=IMap_plusD_test; globals:=[("D", FSHFloatValType)] |} ;

      {| i:=8; o:=8; name:="compose_pointwise"; op:=Compose_pointwise_test ; globals:=[]|}
  ].


Import MonadNotation.

Import IO.
Export IO.DV.

Definition test_interpreter := TopLevelEnv.interpreter_user helix_intrinsics.


(* Returns a tuple [(Option p, Option d, e)] containting:
   - p: generated LLVM program
   - d: results of evaluation of LLVM program
   - e: error string (applicable if either of first two tuple's elements are [None]
*)
Definition runFSHCOLTest (t:FSHCOLTest) (just_compile:bool) (data:list binary64)
  :=
    match t return (list binary64 -> _) with
    | mkFSHCOLTest i o name globals op =>
      fun data' =>
        match initIRGlobals data' globals with
        | inl msg => (None,None,msg)
        | inr (data'', ginit) =>
          let ginit := app [TLE_Comment "Global variables"] ginit in
          let main := genMain i o name globals data'' in
          match LLVMGen i o globals just_compile op name with
          | inl msg => (None, None, msg)
          | inr prog =>
            if just_compile then
              (Some prog, None, "")
            else
              let code := app (app ginit prog) main in
              (Some prog, Some (test_interpreter code), "")
          end
        end
    end data.

Require Import Helix.Util.ListSetoid.
Require Import Helix.Util.ErrorSetoid.

Fixpoint initFSHGlobals
         (data: list binary64)
         (mem: memory)
         (globals: list (string * FSHValType))
  : err (memory * list binary64 * evalContext)
  :=
    match globals with
    | [] => ret (mem,data, [])
    | (_,gt)::gs => match gt with
                  | FSHnatValType => raise "Unsupported global type: nat"
                  | FSHFloatValType =>
                    '(mem,data,σ) <- initFSHGlobals data mem gs ;;
                    let '(x, data) := rotate Float64Zero data in
                    ret (mem, data, (DSHCTypeVal x)::σ)
                  | FSHvecValType n =>
                    '(mem,data,σ) <- initFSHGlobals data mem gs ;;
                     let (data,mb) := constMemBlock n data in
                     let k := memory_next_key mem in
                     let mem := memory_set mem k mb in
                     let p := DSHPtrVal k n in
                     ret (mem, data, (p::σ))
                  end
    end.

Definition evalFSHCOLOperator
           (i o: nat)
           (name: string)
           (globals: list (string * FSHValType))
           (op: DSHOperator)
           (data:list binary64)
  : err (list binary64)
  :=

    let mem := memory_empty in
    (* Initializes the input address *)
    '(mem, data, σ) <- initFSHGlobals data mem globals ;;
    let xindex := memory_next_key mem in
    let '(data, x) := constMemBlock i data in
    let mem := memory_set mem xindex x in
    (* Initializes the output address *)
    let yindex :=  memory_next_key mem in
    let mem := memory_set mem yindex mem_empty in

     let σ := List.app σ [DSHPtrVal yindex o; DSHPtrVal xindex i] in
     match evalDSHOperator σ op mem (estimateFuel op) with
     | Some (inr mem) =>
       yb <- trywith "No output memory block" (memory_lookup mem yindex) ;;
          mem_to_list "Invalid output memory block" o yb
     | Some (inl msg) => inl msg
     | None => raise "evalDSHOperator returns None"
     end.

(* Returns [sum string (list binary64)] *)
Definition evalFSHCOLTest (t:FSHCOLTest) (data:list binary64)
  : err (list binary64)
  :=
    @evalFSHCOLOperator t.(i) t.(o) t.(name) t.(globals) t.(op) data.

(*

Import DSHNotation.
Print DynWin_test.

Compute LLVMGen
        8 8
        [("D", FSHFloatValType)]
        true
        IMap_plusD_test
        "Pointwise_plusD".

Compute LLVMGen
        5 1
        [("D", FSHvecValType 3)]
        true
        DynWin_test
        "dynwin64".

Compute LLVMGen
        2 1
        []
        true
        IReduction_test
        "IReduction".
*)
