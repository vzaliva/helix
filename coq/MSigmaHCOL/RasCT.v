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
