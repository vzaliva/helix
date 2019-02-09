(*
Carrier type used in all our proofs. Could be real of Float in future.
 *)

Require Import Coq.Structures.Equalities.

Require Import CoLoR.Util.Vector.VecUtil.

Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.theory.rings.
Require Import MathClasses.interfaces.orders.

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
Instance CarrierAledec: ∀ x y: CarrierA, Decision (x ≤ y). Admitted.
Instance CarrierAequivdec: ∀ x y: CarrierA, Decision (x = y). Admitted.
Instance CarrierASSO: @StrictSetoidOrder CarrierA CarrierAe CarrierAlt. Admitted.
Instance CarrierASRO: @SemiRingOrder CarrierA CarrierAe CarrierAplus CarrierAmult CarrierAz CarrierA1 CarrierAle. Admitted.

Add Ring RingA: (stdlib_ring_theory CarrierA).

Global Instance CarrierAPlus_proper:
  Proper ((=) ==> (=) ==> (=)) (plus).
Proof.
  solve_proper.
Qed.

Global Instance CommutativeMonoid_plus_zero:
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
Definition sub: CarrierA → CarrierA → CarrierA := plus∘negate.

(* The following is not strictly necessary as it follows from "properness" of composition, negation, and addition operations. Unfortunately Coq 8.4 class resolution could not find these automatically so we hint it by adding implicit instance. *)
Global Instance CarrierA_sub_proper:
  Proper ((=) ==> (=) ==> (=)) (sub).
Proof.
  intros a b Ha x y Hx .
  unfold sub, compose.
  rewrite Hx, Ha.
  reflexivity.
Qed.

Definition Zless (a b: CarrierA): CarrierA
  := if CarrierAltdec a b then one else zero.

Global Instance Zless_proper:
  Proper ((=) ==> (=) ==> (=)) (Zless).
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
