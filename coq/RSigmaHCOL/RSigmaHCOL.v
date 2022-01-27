(* Deep-embedded SigmaHCOL with real arithmetics *)

Require Import Helix.MSigmaHCOL.RasCT.
Require Import Helix.RSigmaHCOL.NatAsNT.
Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.

Module Export RHCOL <: MDSigmaHCOL(MRasCT)(MNatAsNT).
  Include MDSigmaHCOL MRasCT MNatAsNT.
End RHCOL.

Module Export RHCOLEval <: MDSigmaHCOLEval(MRasCT)(MNatAsNT)(RHCOL).
  Include MDSigmaHCOLEval MRasCT MNatAsNT RHCOL.
End RHCOLEval.
