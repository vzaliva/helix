(* Carrier type as module *)

Require Import MathClasses.interfaces.abstract_algebra.

(* Basic module wrapping carrier type.
   It just states it is a setoid.
 *)
Module Type CType.

  Parameter Inline t : Type.

  Declare Instance CTypeEquiv: Equiv t.
  Declare Instance CTypeSetoid: @Setoid t CTypeEquiv.

  (* Values *)
  Parameter CTypeZero: t.
  Parameter CTypeOne: t.

  (* predicates *)
  Parameter CTypeLt: relation t.

  (* operations *)
  Parameter CTypePlus : t -> t -> t.
  Parameter CTypeNeg  : t -> t.
  Parameter CTypeMult : t -> t -> t.
  Parameter CTypeAbs  : t -> t.
  Parameter CTypeZLess: t -> t -> t.
  Parameter CTypeMin  : t -> t -> t.
  Parameter CTypeMax  : t -> t -> t.
  Parameter CTypeSub  : t -> t -> t.

  (* Proper *)
  Declare Instance Zless_proper: Proper ((=) ==> (=) ==> (=)) CTypeZLess.
  Declare Instance abs_proper: Proper ((=) ==> (=)) CTypeAbs.
  Declare Instance plus_proper: Proper((=) ==> (=) ==> (=)) CTypePlus.
  Declare Instance sub_proper: Proper((=) ==> (=) ==> (=)) CTypeSub.
  Declare Instance mult_proper: Proper((=) ==> (=) ==> (=)) CTypeMult.
  Declare Instance min_proper: Proper((=) ==> (=) ==> (=)) CTypeMin.
  Declare Instance max_proper: Proper((=) ==> (=) ==> (=)) CTypeMax.

End CType.
