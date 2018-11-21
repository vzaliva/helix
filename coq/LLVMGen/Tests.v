Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Vellvm.Numeric.Fappli_IEEE_extra.

Require Import Flocq.IEEE754.Binary.
Require Import Coq.Numbers.BinNums. (* for Z scope *)
Require Import Coq.ZArith.BinInt.

Import ListNotations.

Program Definition FloatV64Zero := Float64V (@FF2B _ _ (F754_zero false) _).

Program Definition FloatV64One := Float64V (BofZ _ _ _ _ 1%Z).
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

(* sample definition to be moved to DynWin.v *)
Definition DynWin_test: @FSHOperator Float64 (1 + 4) 1 :=
  FSHCompose (FSHBinOp (AZless (AVar 1) (AVar 0)))
   (FSHHTSUMUnion (APlus (AVar 1) (AVar 0))
      (FSHCompose (FSHeUnion (NConst 0) FloatV64Zero)
         (FSHIReduction 3 (APlus (AVar 1) (AVar 0)) FloatV64Zero
            (FSHCompose
               (FSHCompose (FSHPointwise (AMult (AVar 0) (ANth 3 (VVar 3) (NVar 2))))
                  (FSHInductor (NVar 0) (AMult (AVar 1) (AVar 0)) FloatV64One))
               (FSHeT (NConst 0)))))
      (FSHCompose (FSHeUnion (NConst 1) FloatV64Zero)
         (FSHIReduction 2 (AMax (AVar 1) (AVar 0)) FloatV64Zero
            (FSHCompose (FSHBinOp (AAbs (AMinus (AVar 1) (AVar 0))))
               (FSHIUnion 2 (APlus (AVar 1) (AVar 0)) FloatV64Zero
                  (FSHCompose (FSHeUnion (NVar 0) FloatV64Zero)
                     (FSHeT
                        (NPlus (NPlus (NConst 1) (NMult (NVar 1) (NConst 1)))
                           (NMult (NVar 0) (NMult (NConst 2) (NConst 1))))))))))).

Definition BinOp_less_test: @FSHOperator Float64 (2+2) 2 :=
  FSHBinOp (AZless (AVar 1) (AVar 0)).

Definition BinOp_plus_test: @FSHOperator Float64 (2+2) 2 :=
  FSHBinOp (APlus (AVar 1) (AVar 0)).

Definition Pointwise_plus1_test: @FSHOperator Float64 8 8 :=
  FSHPointwise (APlus (AConst FloatV64One) (AVar 0)).

Definition Pointwise_plusD_test: @FSHOperator Float64 8 8 :=
  FSHPointwise (APlus (AVar 0) (AVar 2)).

Record FSHCOLTest :=
  mkFSHCOLTest
    {
      i: nat;
      o: nat;
      name: string;
      globals: list (string * (@FSHValType Float64)) ;
      op: @FSHOperator Float64 i o;
    }.

Definition Reduction_test: @FSHOperator Float64 8 4 :=
  (FSHIReduction 5 (APlus (AVar 1) (AVar 0)) FloatV64Zero FSHDummy).

Local Open Scope string_scope.

Definition all_tests :=
  [
    {| name:="dynwin"; i:=1+4; o:=1; op:=DynWin_test ; globals:=[("D", @FSHvecValType Float64 3)] |} ;
    {| name:="reduction"; i:=8; o:=4; op:=Reduction_test; globals:=[] |} ;
    {| name:="binop_less"; i:=2+2; o:=2; op:=BinOp_less_test; globals:=[] |} ;
    {| name:="binop_plus"; i:=2+2; o:=2; op:=BinOp_plus_test; globals:=[] |} ;
    {| name:="pointwise_plus1"; i:=8; o:=8; op:=Pointwise_plus1_test; globals:=[] |} ;
    {| name:="pointwise_plusD"; i:=8; o:=8; op:=Pointwise_plusD_test; globals:=[("D", @FSHFloatValType Float64)] |}
  ].
