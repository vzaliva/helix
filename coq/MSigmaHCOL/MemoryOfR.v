Require Import Helix.MSigmaHCOL.MemSetoid.
Require Import Helix.MSigmaHCOL.RasCT.

(* Real memory *)
Module MMemoryOfR : MMemSetoid(MRasCT).
  Include MMemSetoid MRasCT.
End MMemoryOfR.
