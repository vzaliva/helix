Require Import Helix.MSigmaHCOL.CarrierAasCT.
Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.
Require Import Helix.ASigmaHCOL.NatAsNT.

Module Export AHCOL <: MDSigmaHCOL(CarrierAasCT)(MNatAsNT).
  Include MDSigmaHCOL CarrierAasCT MNatAsNT.
End AHCOL.

Module Export AHCOLEval <: MDSigmaHCOLEval(CarrierAasCT)(MNatAsNT)(AHCOL).
  Include MDSigmaHCOLEval CarrierAasCT MNatAsNT AHCOL.
End AHCOLEval.
