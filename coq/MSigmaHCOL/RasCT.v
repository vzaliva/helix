Require Import ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rminmax.
Require Import micromega.RMicromega.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.

Require Import Helix.HCOL.CarrierType.
Require Import Helix.MSigmaHCOL.CType.
Require Import Helix.MSigmaHCOL.RasCarrierA.

Module MRasCT <: CType.

  Definition t := @CarrierA CarrierDefs_R.

  Definition CTypeEquiv := CarrierAe.
  Definition CTypeSetoid := CarrierAsetoid.
  Definition CTypeEquivDec := CarrierAequivdec.

  Definition CTypeZero  := CarrierAz.
  Definition CTypeOne   := CarrierA1.
  Definition CTypeZeroOneApart := CarrierA_Z_neq_One.
  Definition CTypePlus := CarrierAplus.

  Definition CTypeNeg   := CarrierAneg.
  Definition CTypeMult  := CarrierAmult.

  Definition CTypeAbs   := abs.
  Definition CTypeZLess := Zless.
  Definition CTypeMin   := @minmax.min CarrierA CarrierAle CarrierAledec.
  Definition CTypeMax   := @minmax.max CarrierA CarrierAle CarrierAledec.
  Definition CTypeSub   := sub.

  Definition Zless_proper := CarrierType.Zless_proper.
  Definition abs_proper := CarrierAabs_proper.
  Definition plus_proper := CarrierAPlus_proper.
  Definition sub_proper := CarrierA_sub_proper.
  Definition mult_proper := CarrierAmult_proper.
  Definition min_proper := CarrierA_min_proper.
  Definition max_proper := CarrierA_max_proper.

End MRasCT.

Global Hint Unfold
  MRasCT.CTypePlus
  MRasCT.CTypeMult
  MRasCT.CTypeSub
  MRasCT.CTypeAbs
  MRasCT.CTypeZero
  MRasCT.CTypeOne
  CarrierDefs_R
  CarrierAplus
  CarrierAmult
  CarrierType.sub
  CarrierAz
  CarrierA1 : unfold_RCT.

Require Import Coq.micromega.Psatz.
Require Import Helix.Tactics.StructTactics.

Lemma RCT_abs_Rabs (x : R) :
  MRasCT.CTypeAbs x ≡ Rabs x.
Proof.
  reflexivity.
Qed.

Lemma RCT_max_Rmax (x y : R) :
  MRasCT.CTypeMax x y ≡ Rmax x y.
Proof.
  cbv.
  repeat break_if; cbn.
  all: solve [intuition].
Qed.

Lemma R_MaxZeroAbs (x : R) :
  MRasCT.CTypeMax MRasCT.CTypeZero (MRasCT.CTypeAbs x)
  ≡ (MRasCT.CTypeAbs x).
Proof.
  rewrite RCT_abs_Rabs, RCT_max_Rmax.
  cbv.
  repeat break_if.
  all: solve [intuition].
Qed.

Lemma R_PlusZeroLeft (x : R) :
  MRasCT.CTypePlus MRasCT.CTypeZero x ≡ x.
Proof.
  cbv; lra.
Qed.

Lemma R_MultOneLeft (x : R) :
  MRasCT.CTypeMult MRasCT.CTypeOne x ≡ x.
Proof.
  cbv; lra.
Qed.
