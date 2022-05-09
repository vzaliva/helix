(* Deep-embedded SigmaHCOL with floating point arithmetics *)

Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.
Require Import Helix.DSigmaHCOL.DSigmaHCOLITree.
Require Import Helix.FSigmaHCOL.Float64asCT.
Require Import Helix.FSigmaHCOL.LazyFloat64asCT.
Require Import Helix.FSigmaHCOL.Int64asNT.

(* A "lazy-valued" version of FHCOL, for analysis of
   numerical properties of floating-point algorithms *)
Module Export LFHCOL <: MDSigmaHCOL(MLazyFloat64asCT)(MInt64asNT).
  Include MDSigmaHCOL MLazyFloat64asCT MInt64asNT.
End LFHCOL.

Module Export LFHCOLEval <: MDSigmaHCOLEval(MLazyFloat64asCT)(MInt64asNT)(LFHCOL).
  Include MDSigmaHCOLEval MLazyFloat64asCT MInt64asNT LFHCOL.
End LFHCOLEval.

(* The regular "eager" 64-bit FHCOL *)
Module Export FHCOL <: MDSigmaHCOL(MFloat64asCT)(MInt64asNT).
  Include MDSigmaHCOL MFloat64asCT MInt64asNT.
End FHCOL.

Module Export FHCOLEval <: MDSigmaHCOLEval(MFloat64asCT)(MInt64asNT)(FHCOL).
  Include MDSigmaHCOLEval MFloat64asCT MInt64asNT FHCOL.
End FHCOLEval.

Module FHCOLITree := MDSigmaHCOLITree(MFloat64asCT)(MInt64asNT)(FHCOL)(FHCOLEval).
