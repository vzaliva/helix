Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

Require Import MathClasses.interfaces.abstract_algebra.

Require Import Helix.MSigmaHCOL.CType.

Instance binary64_Equiv: Equiv binary64 :=
  fun f1 f2 => (b64_compare f1 f2 ≡ Some Eq).

Instance binary64_Setoid: Setoid binary64.
Admitted.

Module MFloat64AasCT <: CType.
  Definition t := binary64.
  Definition CTypeEquiv := binary64_Equiv.
  Definition CTypeSetoid := binary64_Setoid.
End MFloat64AasCT.
