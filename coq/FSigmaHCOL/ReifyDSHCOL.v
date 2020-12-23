(* Translates DHCOL on CarrierA to FHCOL *)

Require Import Helix.MSigmaHCOL.CarrierAasCT.
Require Import Helix.FSigmaHCOL.Float64asCT.
Require Import Helix.DSigmaHCOL.NatAsNT.
Require Import Helix.FSigmaHCOL.Int64asNT.
Require Import Helix.DSigmaHCOL.DSHCOLOnCarrierA.
Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.DSigmaHCOL.DHCOLTypeTranslator.

Module Export DSCHOLtoFHCOL := MDHCOLTypeTranslator
                                 (CarrierAasCT)
                                 (MFloat64asCT)
                                 (MNatAsNT)
                                 (MInt64asNT)
                                 (MDSHCOLOnCarrierA)
                                 (MDSHCOLOnFloat64).
