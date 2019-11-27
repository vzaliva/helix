Require Import Helix.HCOL.CarrierType.
Require Import Helix.MSigmaHCOL.CarrierAasCT.
Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.abstract_algebra.

(* TODO: move =CarrierAabs_proper= to CarrierType.v *)
Require Import MathClasses.theory.abs.
Instance CarrierAabs_proper : Proper (equiv ==> equiv) abs.
Proof.
    typeclasses eauto.
Qed.

Module MDSigmaHCOLEvalSigCarrierA <: MDSigmaHCOLEvalSig(CarrierAasCT).
  Definition CTypeZero := CarrierAz.
  Definition CTypePlus := CarrierAplus.
  Definition CTypeNeg  := CarrierAneg.
  Definition CTypeMult := CarrierAmult.
  Definition CTypeLe   := CarrierAle.
  Definition CTypeLt   := CarrierAlt.
  Definition CTypeTO   := CarrierAto.
  Definition CTypeAbs  := CarrierAabs.
  Definition CTypeLeDec:= CarrierAledec.

  Definition CTypeZLess := Zless.
  Definition Zless_proper := CarrierType.Zless_proper.
  Definition abs_proper := CarrierAabs_proper.
  Definition plus_proper := CarrierAPlus_proper.
  Definition sub_proper := CarrierA_sub_proper.
  Definition mult_proper := CarrierAmult_proper.

End MDSigmaHCOLEvalSigCarrierA.

Module Export MDSHCOLOnCarrierA :=
  MDSigmaHCOLEval(CarrierAasCT)(MDSigmaHCOLEvalSigCarrierA).
