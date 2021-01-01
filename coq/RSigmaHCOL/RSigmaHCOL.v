(* Deep-embedded SigmaHCOL with real arithmetics *)

Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.
Require Import Helix.DSigmaHCOL.DSigmaHCOLITree.
Require Import Helix.RSigmaHCOL.RasCT.
Require Import Helix.DSigmaHCOL.NatAsNT.

Module Export RHCOL := MDSigmaHCOLITree(MRasCT)(MNatAsNT).
