(* Translates RHCOL to FHCOL *)

Require Import Helix.MSigmaHCOL.CarrierAasCT.
Require Import Helix.ASigmaHCOL.NatAsNT.
Require Import Helix.ASigmaHCOL.ASigmaHCOL.
Require Import Helix.RSigmaHCOL.RSigmaHCOL.
Require Import Helix.RSigmaHCOL.RasCT.
Require Import Helix.DSigmaHCOL.DHCOLTypeTranslator.

Module Export AHCOLtoRHCOL := MDHCOLTypeTranslator
                                 (CarrierAasCT)
                                 (MRasCT)
                                 (MNatAsNT)
                                 (MNatAsNT)
                                 (AHCOL)
                                 (RHCOL).
