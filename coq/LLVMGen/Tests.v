Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.BinNums. (* for Z scope *)
Require Import Coq.ZArith.BinInt.

Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.FSigmaHCOL.Int64asNT.
Require Import Helix.LLVMGen.Compiler.
Require Import Helix.LLVMGen.Externals.
Require Import Helix.LLVMGen.Data.
Require Import Helix.Util.ErrorSetoid.
Require Import Helix.Util.ErrorWithState.

Require Import Vellvm.Numeric.Fappli_IEEE_extra.
Require Import Vellvm.LLVMEvents.
Require Import Vellvm.Denotation.
Require Import Vellvm.Handlers.Memory.
Require Import Vellvm.TopLevel.
Require Import Vellvm.LLVMAst.

Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

Require Import ExtLib.Structures.Monads.

Import ListNotations.

Import MDSHCOLOnFloat64.

(* sample definition to be moved to DynWin.v *)
Local Open Scope nat_scope.

(* Nop is generated, for example, for `IReduction 0` *)
Definition Nop_test := DSHNop.

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

Program Definition Int64_42:Int64.int := Int64.mkint 42%Z  _.
Next Obligation. cbv; auto. Qed.

Program Definition Int64_0:Int64.int := Int64.mkint 0%Z  _.
Next Obligation. cbv; auto. Qed.

Program Definition Int64_1:Int64.int := Int64.mkint 1%Z  _.
Next Obligation. cbv; auto. Qed.

Program Definition Int64_2:Int64.int := Int64.mkint 2%Z  _.
Next Obligation. cbv; auto. Qed.

Definition Inductor_test :=
  DSHPower (NConst Int64_42)
           ((PVar 1), (NConst Int64_0))
           ((PVar 0), (NConst Int64_0))
           (AMinus (AVar 1) (AVar 0))
           Float64One.

Definition IUnion_test :=
  DSHLoop 5 (DSHBinOp 2 (PVar 2) (PVar 1) (APlus (AVar 1) (AVar 0))).

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
                                (DSHAssign (PVar 7, NConst Int64_0)
                                   (PVar 0, NConst Int64_0))
                                (DSHAlloc 1
                                   (DSHSeq
                                      (DSHPower (NVar 2)
                                         (PVar 1, NConst Int64_0)
                                         (PVar 0, NConst Int64_0)
                                         (AMult (AVar 1) (AVar 0))
                                         FSigmaHCOL.Float64One)
                                      (DSHIMap 1 (PVar 0) (PVar 4)
                                         (AMult (AVar 0)
                                            (ANth
                                               (MPtrDeref (PVar 8))
                                               (NVar 4))))))))
                          (DSHMemMap2 1 (PVar 1) (PVar 2) (PVar 2)
                             (APlus (AVar 1) (AVar 0)))))))
              (DSHAssign (PVar 0, NConst Int64_0) (PVar 1, NConst Int64_0))))
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
                                              (NPlus (NConst Int64_1)
                                                 (NMult (NVar 3)
                                                    (NConst Int64_1)))
                                              (NMult (NVar 1)
                                                 (NMult (NConst Int64_2)
                                                    (NConst Int64_1))))
                                            (PVar 0, NConst Int64_0))
                                         (DSHAssign
                                            (PVar 0, NConst Int64_0)
                                            (PVar 2, NVar 1)))))
                                (DSHBinOp 1 (PVar 0) (PVar 3)
                                   (AAbs (AMinus (AVar 1) (AVar 0))))))
                          (DSHMemMap2 1 (PVar 1) (PVar 2) (PVar 2)
                             (AMax (AVar 1) (AVar 0)))))))
              (DSHAssign (PVar 0, NConst Int64_0) (PVar 1, NConst Int64_1)))))
     (DSHBinOp 1 (PVar 0) (PVar 2) (AZless (AVar 1) (AVar 0)))).


Local Close Scope nat_scope.


Local Open Scope string_scope.

Definition all_tests :=
  [
    {| i:=5; o:=1; name:="dynwin64"; op:=DynWin_test ; globals:=[("D", FSHvecValType 3)] |} ;
      {| i:=4; o:=2; name:="binop_less"; op:=BinOp_less_test; globals:=[] |} ;
      {| i:=4; o:=2; name:="binop_plus"; op:=BinOp_plus_test; globals:=[] |} ;
      {| i:=2; o:=1; name:="ireduction"; op:=IReduction_test; globals:=[] |} ;
      {| i:=5; o:=7; name:="nop"; op:=Nop_test; globals:=[] |} ;
      {| i:=4; o:=2; name:="iunion"; op:=IUnion_test; globals:=[] |} ;
      {| i:=1; o:=1; name:="inductor"; op:=Inductor_test; globals:=[] |} ;
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
Definition runFSHCOLTest (t:FSHCOLProgram) (just_compile:bool) (data:list binary64)
  :=
    match compile t just_compile data with
    | inl msg => (None, None, msg)
    | inr prog =>
      if just_compile then
        (Some prog, None, "")
      else
        (Some prog, Some (test_interpreter prog), "")
    end.

Require Import Helix.Util.ListSetoid.
Require Import Helix.Util.ErrorSetoid.

Definition evalFSHCOLOperator
           (i o: nat)
           (name: string)
           (globals: list (string * FSHValType))
           (op: DSHOperator)
           (data:list binary64)
  : err (list binary64)
  :=
    let p := mkFSHCOLProgram i o name globals op in
    '(mem, data, σ) <- helix_intial_memory p data ;;
    match evalDSHOperator σ op mem (estimateFuel op) with
    | Some (inr mem) =>
      let Y_mem_block_id : mem_block_id := S (length globals) in
      yb <- trywith "No output memory block" (memory_lookup mem Y_mem_block_id) ;;
      mem_to_list "Invalid output memory block" o yb
    | Some (inl msg) => inl msg
    | None => raise "evalDSHOperator run out of fuel!"
    end.

(* Returns [sum string (list binary64)] *)
Definition evalFSHCOLTest (t:FSHCOLProgram) (data:list binary64)
  : err (list binary64)
  :=
    @evalFSHCOLOperator t.(i) t.(o) t.(name) t.(globals) t.(op) data.

