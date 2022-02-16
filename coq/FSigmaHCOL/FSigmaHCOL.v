(* Deep-embedded SigmaHCOL with floating point arithmetics *)

Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.
Require Import Helix.DSigmaHCOL.DSigmaHCOLITree.
Require Import Helix.FSigmaHCOL.Float64asCT.
Require Import Helix.FSigmaHCOL.Int64asNT.

(* Default 64-bit version *)
Module Export FHCOL <: MDSigmaHCOL(MFloat64asCT)(MInt64asNT).
  Include MDSigmaHCOL MFloat64asCT MInt64asNT.
End FHCOL.

Module Export FHCOLEval <: MDSigmaHCOLEval(MFloat64asCT)(MInt64asNT)(FHCOL).
  Include MDSigmaHCOLEval MFloat64asCT MInt64asNT FHCOL.
End FHCOLEval.

Module FHCOLITree := MDSigmaHCOLITree(MFloat64asCT)(MInt64asNT)(FHCOL)(FHCOLEval).


(* 32-bit version, mostly used to data type conversion in numberic proofs *)

Require Import Helix.FSigmaHCOL.Float32asCT.
Require Import Helix.FSigmaHCOL.Int32asNT.

Module Export FHCOL32 <: MDSigmaHCOL(MFloat32asCT)(MInt32asNT).
  Include MDSigmaHCOL MFloat32asCT MInt32asNT.
End FHCOL32.

Module Export FHCOLEval32 <: MDSigmaHCOLEval(MFloat32asCT)(MInt32asNT)(FHCOL32).
  Include MDSigmaHCOLEval MFloat32asCT MInt32asNT FHCOL32.
End FHCOLEval32.
