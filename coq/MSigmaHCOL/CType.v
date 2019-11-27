(* Carrier type as module *)

Require Import MathClasses.interfaces.abstract_algebra.

(* Basic module wrapping carrier type.
   It just states it is a setoid.
 *)
Module Type CType.

  Parameter Inline t : Type.

  Declare Instance CTypeEquiv: Equiv t.
  Declare Instance CTypeSetoid: @Setoid t CTypeEquiv.

End CType.
