(* Deep-embedded SigmaHCOL with symbolic arithmetics *)

Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.
Require Import Helix.DSigmaHCOL.DSigmaHCOLITree.
Require Import Helix.SymbolicDHCOL.SymbolicCT.
Require Import Helix.RSigmaHCOL.NatAsNT.

Module Export SDHCOL <: MDSigmaHCOL(MSymbolicCT)(MNatAsNT).
  Include MDSigmaHCOL MSymbolicCT MNatAsNT.
End SDHCOL.

Module Export SDHCOLEval <: MDSigmaHCOLEval(MSymbolicCT)(MNatAsNT)(SDHCOL).
  Include MDSigmaHCOLEval MSymbolicCT MNatAsNT SDHCOL.
End SDHCOLEval.
