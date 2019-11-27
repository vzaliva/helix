Require Import ZArith.
Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.
Require Import Helix.FSigmaHCOL.Float64AasCT.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.

Open Scope Z.

Instance Float64Zero : Zero binary64 := B754_zero 53 1024 true.
Instance Float64Plus : Plus binary64 := b64_plus mode_NE.
Instance   Float64Neg           : Negate binary64. Admitted.
Instance   Float64Mult          : Mult binary64. Admitted.
Instance   Float64Le            : Le binary64. Admitted.
Instance   Float64Lt            : Lt binary64. Admitted.
Instance   Float64TO            : TotalOrder Float64Le. Admitted.
Instance   Float64Abs           : Abs binary64. Admitted.
Instance   Float64LeDec         : forall x y : binary64, Decision (x ≤ y). Admitted.
Definition Float64ZLess         : binary64 → binary64 → binary64. Admitted.
Instance   Float64ZLess_proper : Proper (equiv ==> equiv ==> equiv) Float64ZLess. Admitted.
Instance   Float64Abs_proper   : Proper (equiv ==> equiv) abs. Admitted.
Instance   Float64Plus_proper  : Proper (equiv ==> equiv ==> equiv) plus.
Proof.
  simpl_relation.
  unfold equiv, binary64_Equiv in *.
  unfold plus, Float64Plus, b64_plus.
  unfold b64_compare.
  Search Bplus.
Admitted.
Instance   Float64Sub_proper   : Proper (equiv ==> equiv ==> equiv) CarrierType.sub. Admitted.
Instance   Float64Mult_proper  : Proper (equiv ==> equiv ==> equiv) mult. Admitted.

Module MDSigmaHCOLEvalSigFloat64 <: MDSigmaHCOLEvalSig(MFloat64AasCT).
  Import MFloat64AasCT.

  Definition CTypeZero     := Float64Zero.
  Definition CTypePlus     := Float64Plus.
  Definition CTypeNeg      := Float64Neg.
  Definition CTypeMult     := Float64Mult.
  Definition CTypeLe       := Float64Le.
  Definition CTypeLt       := Float64Lt.
  Definition CTypeTO       := Float64TO.
  Definition CTypeAbs      := Float64Abs.
  Definition CTypeLeDec    := Float64LeDec.
  Definition CTypeZLess    := Float64ZLess.
  Definition Zless_proper  := Float64ZLess_proper.
  Definition abs_proper    := Float64Abs_proper.
  Definition plus_proper   := Float64Plus_proper.
  Definition sub_proper    := Float64Sub_proper.
  Definition mult_proper   := Float64Mult_proper.

End MDSigmaHCOLEvalSigFloat64.

Module Export MDSHCOLOnFloat64 := MDSigmaHCOLEval(MFloat64AasCT)(MDSigmaHCOLEvalSigFloat64).
