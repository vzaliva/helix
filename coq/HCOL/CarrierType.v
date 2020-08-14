(*
Carrier type used in all our proofs. Could be real of Float in future.
 *)

Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.OrderedType.

Require Import CoLoR.Util.Vector.VecUtil.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.theory.rings.
Require Import MathClasses.theory.abs.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.orders.minmax.

Require Import Helix.Util.Misc.

Parameter CarrierA : Type.
Instance CarrierAe: Equiv CarrierA. Admitted.
Instance CarrierAsetoid: @Setoid CarrierA CarrierAe. Admitted.
Instance CarrierAz: Zero CarrierA. Admitted.
Instance CarrierA1: One CarrierA. Admitted.
Instance CarrierAplus: Plus CarrierA. Admitted.
Instance CarrierAmult: Mult CarrierA. Admitted.
Instance CarrierAneg: Negate CarrierA. Admitted.
Instance CarrierAle: Le CarrierA. Admitted.
Instance CarrierAlt: Lt CarrierA. Admitted.
Instance CarrierAto: @TotalOrder CarrierA CarrierAe CarrierAle. Admitted.
Instance CarrierAabs: @Abs CarrierA CarrierAe CarrierAle CarrierAz CarrierAneg. Admitted.
Instance CarrierAr: Ring CarrierA. Admitted.
Instance CarrierAltdec: ∀ x y: CarrierA, Decision (x < y). Admitted.
Instance CarrierAequivdec: ∀ x y: CarrierA, Decision (x = y). Admitted.
Instance CarrierASSO: @StrictSetoidOrder CarrierA CarrierAe CarrierAlt. Admitted.
Instance CarrierASRO: @SemiRingOrder CarrierA CarrierAe CarrierAplus CarrierAmult CarrierAz CarrierA1 CarrierAle. Admitted.

Instance CarrierFPSO: @orders.FullPseudoOrder CarrierA CarrierAe (@strong_setoids.default_apart CarrierA CarrierAe) CarrierALe CarrierALt. Admitted.

Instance CarrierAledec: ∀ x y: CarrierA, Decision (x ≤ y).
Proof.
  intros x y.
  unfold Decision.
  destruct (CarrierAltdec x y), (CarrierAequivdec x y).
  - left. apply orders.eq_le. assumption.
  - left. apply orders.not_lt_le_flip, orders.lt_flip. assumption.
  - left. apply orders.eq_le. assumption.
  - right. apply orders.lt_not_le_flip.
    apply orders.not_lt_apart_lt_flip; auto.
Qed.

Instance CarrierA_min_proper: Proper((=) ==> (=) ==> (=)) (@min CarrierA CarrierAle CarrierAledec).
Proof. typeclasses eauto. Qed.

Instance CarrierA_max_proper: Proper((=) ==> (=) ==> (=)) (@max CarrierA CarrierAle CarrierAledec).
Proof. typeclasses eauto. Qed.

(* Zero and One are two distrinct values *)
Axiom CarrierA_Z_neq_One: CarrierAz ≠ CarrierA1.

Add Ring RingA: (stdlib_ring_theory CarrierA).

Instance CarrierAPlus_proper:
  Proper ((=) ==> (=) ==> (=)) plus.
Proof.
  solve_proper.
Qed.

Instance CarrierAmult_proper:
  Proper((=) ==> (=) ==> (=)) CarrierAmult.
Proof.
  solve_proper.
Qed.

Instance CarrierAabs_proper : Proper ((=) ==> (=)) abs.
Proof.
  typeclasses eauto.
Qed.

Instance CommutativeMonoid_plus_zero:
  @MathClasses.interfaces.abstract_algebra.CommutativeMonoid CarrierA _ plus zero.
Proof.
  typeclasses eauto.
Qed.

Notation avector n := (vector CarrierA n) (only parsing).

Ltac decide_CarrierA_equality E NE :=
  let E' := fresh E in
  let NE' := fresh NE in
  match goal with
  | [ |- @equiv CarrierA CarrierAe ?A ?B ] => destruct (CarrierAequivdec A B) as [E'|NE']
  end.

(* Poor man's minus *)
Definition sub {T:Type}
           `{Plus T}
           `{Negate T}
  : T → T → T := plus∘negate.

(* The following is not strictly necessary as it follows from "properness" of composition, negation, and addition operations. Unfortunately Coq 8.4 class resolution could not find these automatically so we hint it by adding implicit instance. *)
Instance CarrierA_sub_proper:
  Proper ((=) ==> (=) ==> (=)) sub.
Proof.
  intros a b Ha x y Hx .
  unfold sub, compose.
  rewrite Hx, Ha.
  reflexivity.
Qed.

Definition Zless (a b: CarrierA): CarrierA
  := if CarrierAltdec a b then one else zero.

Instance Zless_proper:
  Proper ((=) ==> (=) ==> (=)) Zless.
Proof.
  unfold Proper.
  intros a a' aE z z' zE.
  unfold Zless.
  destruct (CarrierAltdec a z), (CarrierAltdec a' z'); auto.
  rewrite aE, zE in l; contradiction.
  rewrite <- aE, <- zE in l; contradiction.
Qed.

Definition CarrierA_beq (a b: CarrierA) : bool := bool_decide (a=b).

Lemma CarrierA_eqb_equiv : ∀ x y : CarrierA, CarrierA_beq x y ≡ true ↔ equiv x y.
Proof.
  intros x y.
  split.
  -
    intros H.
    unfold CarrierA_beq in H.
    apply bool_decide_true, H.
  -
    intros H.
    unfold CarrierA_beq.
    apply bool_decide_true, H.
Qed.

Module CarrierA_as_BooleanDecidableType <: BooleanDecidableType.
  Definition t := CarrierA.
  Definition eq := CarrierAe.
  Definition eq_equiv := @setoid_eq CarrierA CarrierAe CarrierAsetoid.
  Definition eq_dec : ∀ x y : t, {eq x y} + {¬ eq x y} := CarrierAequivdec.
  Definition eqb := CarrierA_beq.
  Definition eqb_eq := CarrierA_eqb_equiv.
End CarrierA_as_BooleanDecidableType.

(* Only needed for [CarrierAOrderedType] *)
Instance CarrierFPAO: @orders.FullPartialOrder CarrierA CarrierAe (@strong_setoids.default_apart CarrierA CarrierAe) CarrierALe CarrierALt. Admitted.

Module CarrierA_as_OT <: OrderedType.

  Definition t := CarrierA.
  Definition eq := CarrierAe.

  Lemma eq_dec : forall x y, { eq x y } + { ~ eq x y }. Proof. apply CarrierAequivdec. Qed.

  Definition lt := CarrierAlt.

  Lemma eq_refl : forall x : t, eq x x. Proof. apply CarrierAsetoid. Qed.
  Lemma eq_sym : forall x y : t, eq x y -> eq y x. Proof. apply CarrierAsetoid. Qed.
  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z. Proof. apply CarrierAsetoid. Qed.
  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z. Proof. apply CarrierASSO. Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros x y H.
    intros C.
    rewrite C in H.
    apply CarrierASSO in H.
    congruence.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros x y.
    destruct (CarrierAequivdec x y) as [E | NE].
    exact (EQ E).
    destruct (CarrierAltdec x y) as [L | NL].
    exact (LT L).
    apply GT.

    eapply orders.le_iff_not_lt_flip in NL.
    eapply orders.lt_iff_le_apart.
    split.
    apply NL.
    apply canonical_names.trivial_apart.
    intros C.
    symmetry in C.
    congruence.
  Qed.

End CarrierA_as_OT.
