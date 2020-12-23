Require Import Helix.MSigmaHCOL.CType.

Require Import MathClasses.orders.minmax.
Require Import MathClasses.interfaces.canonical_names.

Require Import Helix.HCOL.CarrierType.

(* =CarrierA= as =CarrierType= *)
Module CarrierAasCT <: CType.
  Definition t := CarrierA.

  Definition CTypeEquiv := CarrierAe.
  Definition CTypeSetoid := CarrierAsetoid.
  Definition CTypeEquivDec := CarrierAequivdec.


  Definition CTypeZero  := CarrierAz.
  Definition CTypeOne   := CarrierA1.
  Definition CTypePlus  := CarrierAplus.
  Definition CTypeNeg   := CarrierAneg.
  Definition CTypeMult  := CarrierAmult.

  Definition CTypeAbs   := abs.
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

End CarrierAasCT.
