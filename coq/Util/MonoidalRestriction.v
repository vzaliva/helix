
Require Import MathClasses.interfaces.abstract_algebra.


Section MonoidalRestriction.
  Context A {Ae : Equiv A}.

  (* Predicate on type [A] *)
  Class SgPred A := sg_P: A → Prop.

  (* Restriction of monoid operator and unit values *)
  Class MonRestriction {Aop : SgOp A} {Aunit : MonUnit A} {Apred: SgPred A}: Prop :=
    { rmonoid_unit_P: sg_P mon_unit
      ; rmonoid_plus_closed: forall a b, sg_P a -> sg_P b -> sg_P (a & b)
    }.

  Class RMonoid {Aop : SgOp A} {Aunit : MonUnit A} {Apred: SgPred A} :=
    {  sg_setoid :> Setoid A
       ; mon_restriction :> MonRestriction
       ; rsg_op_proper :> Proper ((=) ==> (=) ==> (=)) (&)

       ; rmonoid_ass: forall x y z,
           sg_P x -> sg_P y -> sg_P z -> x & (y & z) = (x & y) & z
       ; rmonoid_left_id : forall y, sg_P y -> mon_unit & y = y
       ; rmonoid_right_id : forall x, sg_P x -> x & mon_unit = x
    }.
  
  Class CommutativeRMonoid {Aop Aunit Ares} : Prop :=
    {
      comrmonoid_rmon :> @RMonoid Aop Aunit Ares
      ; rcommutativity: forall x y, sg_P x -> sg_P y -> x & y = y & x
    }.

  Global Instance ATT: SgPred A := fun _ => True.

  Global Instance ATT_proper:
    Proper (equiv ==> impl) ATT.
  Proof.
    intros x y E.
    unfold ATT, impl.
    tauto.
  Qed.

  (* A regular [CommutativeMonoid] with predicate which is always [True]
     is a [CommutativeRMonoid] *)
  Global Instance Monoid2CommutativeRMonoid
         `{@CommutativeMonoid _ _ Aop Aunit}:
    @CommutativeRMonoid Aop Aunit ATT.
  Proof.
    split.
    -
      split.
      + apply H.
      +
        split.
        cbv; tauto.
        intros a b _ _.
        cbv; tauto.
      +
        apply H.
      +
        intros x y z _ _ _.
        apply sg_ass, H.
      +
        intros y _.
        apply monoid_left_id, H.
      +
        intros y _.
        apply monoid_right_id, H.
    -
      intros x y H0 H1.
      apply commutativity.
  Qed.

End MonoidalRestriction.

Arguments rsg_op_proper {A Ae Aop Aunit Apred RMonoid}.

