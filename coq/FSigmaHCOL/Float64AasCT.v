Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

Require Import MathClasses.interfaces.abstract_algebra.

Require Import Helix.MSigmaHCOL.CType.

Module MFloat64AasCT <: CType.

  Definition t := binary64.

  Definition CTypeEquiv := @eq binary64.

  Definition CTypeSetoid: @Setoid t CTypeEquiv.
  Proof.
    split; auto.
  Defined.

End MFloat64AasCT.
