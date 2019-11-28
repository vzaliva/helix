Require Import ZArith.
Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.
Require Import Helix.FSigmaHCOL.Float64AasCT.

(* Defining these before importing math classes to avoid name collisions,
   e.g. on [Lt] *)
Section MinMax.

  (* TODO: Implement semantics as in LLVM:
     https://llvm.org/docs/LangRef.html#llvm-minimum-intrinsic
   *)
  Definition Float64Min (a b: binary64): binary64. Admitted.

  (* TODO: Implement IEEE-754 semantics for `maxNum` except for the
     handling of signaling `NaNs`. This matches the behavior of libm’s
     `fmax`.

     https://llvm.org/docs/LangRef.html#llvm-maxnum-intrinsic

   *)
  Definition Float64Max (a b: binary64): binary64. Admitted.

End MinMax.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.

Definition FT_Rounding:mode := mode_NE.

Instance Float64Zero : Zero binary64 := B754_zero 53 1024 true.
Instance Float64Plus : Plus binary64 := b64_plus FT_Rounding.
Instance Float64Neg  : Negate binary64. Admitted.
Instance Float64Mult : Mult binary64 :=  b64_mult FT_Rounding.
Instance   Float64Le            : Le binary64. Admitted.
Instance   Float64Lt            : Lt binary64. Admitted.
Instance   Float64Abs : Abs binary64. Admitted. (* := b64_abs.*)
Instance   Float64LeDec         : forall x y : binary64, Decision (x ≤ y). Admitted.
Definition Float64ZLess         : binary64 → binary64 → binary64. Admitted.
Definition Float64Sub           := b64_minus FT_Rounding.

Instance   Float64ZLess_proper : Proper (equiv ==> equiv ==> equiv) Float64ZLess.
Proof. solve_proper. Qed.

Instance   Float64Abs_proper   : Proper (equiv ==> equiv) abs.
Proof. solve_proper. Qed.
Instance   Float64Plus_proper  : Proper (equiv ==> equiv ==> equiv) plus.
Proof. solve_proper. Qed.

Instance   Float64Sub_proper   : Proper (equiv ==> equiv ==> equiv) Float64Sub.
Proof. solve_proper. Qed.
Instance   Float64Mult_proper  : Proper (equiv ==> equiv ==> equiv) mult.
Proof. solve_proper. Qed.
Instance   Float64Min_proper  : Proper (equiv ==> equiv ==> equiv) Float64Min.
Proof. solve_proper. Qed.
Instance   Float64Max_proper  : Proper (equiv ==> equiv ==> equiv) Float64Max.
Proof. solve_proper. Qed.


Module MDSigmaHCOLEvalSigFloat64 <: MDSigmaHCOLEvalSig(MFloat64AasCT).
  Import MFloat64AasCT.

  Definition CTypeZero     := Float64Zero.
  Definition CTypePlus     := Float64Plus.
  Definition CTypeNeg      := Float64Neg.
  Definition CTypeMult     := Float64Mult.
  Definition CTypeLe       := Float64Le.
  Definition CTypeLt       := Float64Lt.

  Definition CTypeLeDec    := Float64LeDec.

  Definition CTypeAbs      := Float64Abs.
  Definition CTypeZLess    := Float64ZLess.
  Definition CTypeMin      := Float64Min.
  Definition CTypeMax      := Float64Max.
  Definition CTypeSub      := Float64Sub.

  Definition Zless_proper  := Float64ZLess_proper.
  Definition abs_proper    := Float64Abs_proper.
  Definition plus_proper   := Float64Plus_proper.
  Definition sub_proper    := Float64Sub_proper.
  Definition mult_proper   := Float64Mult_proper.
  Definition min_proper    := Float64Min_proper.
  Definition max_proper    := Float64Max_proper.

End MDSigmaHCOLEvalSigFloat64.

Module Export MDSHCOLOnFloat64 := MDSigmaHCOLEval(MFloat64AasCT)(MDSigmaHCOLEvalSigFloat64).
