Require Import Helix.HCOL.CarrierType.
Require Import Helix.MSigmaHCOL.CarrierAasCT.
Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.minmax.

(* TODO: move =CarrierAabs_proper= to CarrierType.v *)
Require Import MathClasses.theory.abs.
Instance CarrierAabs_proper : Proper (equiv ==> equiv) abs.
Proof. typeclasses eauto. Qed.

Instance CarrierA_min_proper: Proper((=) ==> (=) ==> (=)) (@min CarrierA CarrierAle CarrierAledec).
Proof. typeclasses eauto. Qed.

Instance CarrierA_max_proper: Proper((=) ==> (=) ==> (=)) (@max CarrierA CarrierAle CarrierAledec).
Proof. typeclasses eauto. Qed.


Module MDSigmaHCOLEvalSigCarrierA <: MDSigmaHCOLEvalSig(CarrierAasCT).
  Definition CTypeZero := CarrierAz.
  Definition CTypePlus := CarrierAplus.
  Definition CTypeNeg  := CarrierAneg.
  Definition CTypeMult := CarrierAmult.
  Definition CTypeLe   := CarrierAle.
  Definition CTypeLt   := CarrierAlt.

  Definition CTypeLeDec:= CarrierAledec.

  Definition CTypeAbs  := abs.
  Definition CTypeZLess := Zless.
  Definition CTypeMin   := @min CarrierA CarrierAle CarrierAledec.
  Definition CTypeMax   := @max CarrierA CarrierAle CarrierAledec.
  Definition CTypeSub   := sub.

  Definition Zless_proper := CarrierType.Zless_proper.
  Definition abs_proper := CarrierAabs_proper.
  Definition plus_proper := CarrierAPlus_proper.
  Definition sub_proper := CarrierA_sub_proper.
  Definition mult_proper := CarrierAmult_proper.
  Definition min_proper := CarrierA_min_proper.
  Definition max_proper := CarrierA_max_proper.

End MDSigmaHCOLEvalSigCarrierA.

Module Export MDSHCOLOnCarrierA :=
  MDSigmaHCOLEval(CarrierAasCT)(MDSigmaHCOLEvalSigCarrierA).
