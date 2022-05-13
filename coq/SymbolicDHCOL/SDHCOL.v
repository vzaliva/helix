(* Deep-embedded SigmaHCOL with symbolic arithmetics *)

Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.
Require Import Helix.DSigmaHCOL.DSigmaHCOLITree.
Require Import Helix.SymbolicDHCOL.SymbolicCT.
Require Import Helix.RSigmaHCOL.NatAsNT.

Module Export SDHCOL <: MDSigmaHCOL(MFloat64asCT)(MInt64asNT).
  Include MDSigmaHCOL MFloat64asCT MInt64asNT.
End SDHCOL.

Module Export SDHCOLEval <: MDSigmaHCOLEval(MFloat64asCT)(MInt64asNT)(FHCOL).
  Include MDSigmaHCOLEval MFloat64asCT MInt64asNT FHCOL.
End SDHCOLEval.
