Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.theory.setoids.

Section MonoidalRestriction.
  Context A {Ae : Equiv A}.

  Class MonRestriction A := rmonoid_P: A → Prop.

  Class RMonoid {Aop : SgOp A} {Aunit : MonUnit A} {Ares: MonRestriction A}: Prop :=
    {
      sg_setoid :> Setoid A
      ; sg_op_proper :> Proper ((=) ==> (=) ==> (=)) (&)

      ; rmonoid_ass: forall x y z,
          rmonoid_P x -> rmonoid_P y -> rmonoid_P z -> x & (y & z) = (x & y) & z
      ; rmonoid_left_id : forall y, rmonoid_P y -> mon_unit & y = y
      ; rmonoid_right_id : forall x, rmonoid_P x -> x & mon_unit = x

      ; rmonoid_unit_P: rmonoid_P mon_unit
      ; rmonoid_plus_closed: forall a b, rmonoid_P a -> rmonoid_P b -> rmonoid_P (a & b)
    }.
  
  Class CommutativeRMonoid {Aop Aunit Ares} : Prop :=
    {
      comrmonoid_rmon :> @RMonoid Aop Aunit Ares
      ; rcommutativity: forall x y, rmonoid_P x -> rmonoid_P y -> x & y = y & x
    }.

End MonoidalRestriction.
