(* Deep-embedded SigmaHCOL with floating point arithmetics *)

Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.
Require Import Helix.DSigmaHCOL.DSigmaHCOLITree.
Require Import Helix.FSigmaHCOL.Float64asCT.
Require Import Helix.FSigmaHCOL.Int64asNT.

Module Export FHCOL <: MDSigmaHCOL(MFloat64asCT)(MInt64asNT).
  Include MDSigmaHCOL MFloat64asCT MInt64asNT.
End FHCOL.

Module Export FHCOLEval <: MDSigmaHCOLEval(MFloat64asCT)(MInt64asNT)(FHCOL).
  Include MDSigmaHCOLEval MFloat64asCT MInt64asNT FHCOL.
End FHCOLEval.

Module FHCOLITree := MDSigmaHCOLITree(MFloat64asCT)(MInt64asNT)(FHCOL)(FHCOLEval).
