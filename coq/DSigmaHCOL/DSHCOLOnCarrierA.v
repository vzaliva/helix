Require Import Helix.MSigmaHCOL.CarrierAasCT.
Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.
Require Import Helix.DSigmaHCOL.NatAsNT.

Module Export MDSHCOLOnCarrierA :=
  MDSigmaHCOLEval(CarrierAasCT)(MNatAsNT).
