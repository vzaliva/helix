
Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

Require Import Helix.MSigmaHCOL.CarrierAasCT.
Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.

Require Import Helix.FSigmaHCOL.Float64AasCT.

Module Export MDSHCOLOnFloat64 := DSigmaHCOLEval.Make(MFloat64AasCT).
