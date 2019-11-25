Require Import Helix.MSigmaHCOL.MemSetoid.
Require Import Helix.MSigmaHCOL.CarrierAasCT.

(* CarrierA memory *)
Module MMemoryOfCarrierA : MMemSetoid(CarrierAasCT).
  Include MMemSetoid CarrierAasCT.
End MMemoryOfCarrierA.
