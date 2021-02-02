(* Deep-embedded SigmaHCOL with real arithmetics *)

Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.
Require Import Helix.RSigmaHCOL.RasCT.
Require Import Helix.ASigmaHCOL.NatAsNT.

Module Export RHCOL <: MDSigmaHCOL(MRasCT)(MNatAsNT).
  Include MDSigmaHCOL MRasCT MNatAsNT.
End RHCOL.

Module Export RHCOLEval <: MDSigmaHCOLEval(MRasCT)(MNatAsNT)(RHCOL).
  Include MDSigmaHCOLEval MRasCT MNatAsNT RHCOL.
End RHCOLEval.
