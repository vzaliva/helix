(* Translates RHCOL to FHCOL *)

Require Import Helix.MSigmaHCOL.RasCT.
Require Import Helix.RSigmaHCOL.NatAsNT.
Require Import Helix.FSigmaHCOL.Float64asCT.
Require Import Helix.FSigmaHCOL.Int64asNT.
Require Import Helix.RSigmaHCOL.RSigmaHCOL.
Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.DSigmaHCOL.DHCOLTypeTranslator.

(* Default, 64-bit version of FHCOL *)

Module Export RHCOLtoFHCOL := MDHCOLTypeTranslator
                                 (MRasCT)
                                 (MFloat64asCT)
                                 (MNatAsNT)
                                 (MInt64asNT)
                                 (RHCOL)
                                 (FHCOL)
                                 (RHCOLEval)
                                 (FHCOLEval).

(* 32-bit version, mostly used to data type conversion in numberic proofs *)

Require Import Helix.FSigmaHCOL.Float32asCT.
Require Import Helix.FSigmaHCOL.Int32asNT.

Module Export RHCOLtoFHCOL32 := MDHCOLTypeTranslator
                                 (MRasCT)
                                 (MFloat32asCT)
                                 (MNatAsNT)
                                 (MInt32asNT)
                                 (RHCOL)
                                 (FHCOL32)
                                 (RHCOLEval)
                                 (FHCOLEval32).
