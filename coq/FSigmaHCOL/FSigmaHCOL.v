(* Deep-embedded SigmaHCOL with floating point arithmetics *)

Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.
Require Import Helix.DSigmaHCOL.DSigmaHCOLITree.
Require Import Helix.FSigmaHCOL.Float64asCT.
Require Import Helix.FSigmaHCOL.Int64asNT.

Module Export MDSHCOLOnFloat64 := MDSigmaHCOLITree(MFloat64asCT)(MInt64asNT).
