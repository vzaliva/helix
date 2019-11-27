Require Import Helix.MSigmaHCOL.CType.

Require Import Helix.HCOL.CarrierType.

(* =CarrierA= as =CarrierType= *)
Module CarrierAasCT <: CType.
  Definition t := CarrierA.

  Definition CTypeEquiv := CarrierAe.
  Definition CTypeSetoid := CarrierAsetoid.
End CarrierAasCT.
