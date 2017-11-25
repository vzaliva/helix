(*
Carrier type used in all our proofs. Could be real of Float in future.
 *)


Require Import CoLoR.Util.Vector.VecUtil.

Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.theory.rings.
Require Import MathClasses.interfaces.orders.

Parameter CarrierA: Type.
Parameter CarrierAe: Equiv CarrierA.
Parameter CarrierAsetoid: @Setoid CarrierA CarrierAe.
Parameter CarrierAz: Zero CarrierA.
Parameter CarrierA1: One CarrierA.
Parameter CarrierAplus: Plus CarrierA.
Parameter CarrierAmult: Mult CarrierA.
Parameter CarrierAneg: Negate CarrierA.
Parameter CarrierAle: Le CarrierA.
Parameter CarrierAlt: Lt CarrierA.
Parameter CarrierAto: @TotalOrder CarrierA CarrierAe CarrierAle.
Parameter CarrierAabs: @Abs CarrierA CarrierAe CarrierAle CarrierAz CarrierAneg.
Parameter CarrierAr: Ring CarrierA.
Parameter CarrierAltdec: ∀ x y: CarrierA, Decision (x < y).
Parameter CarrierAledec: ∀ x y: CarrierA, Decision (x ≤ y).
Parameter CarrierAequivdec: ∀ x y: CarrierA, Decision (x = y).
Parameter CarrierASSO: @StrictSetoidOrder CarrierA CarrierAe CarrierAlt.
Parameter CarrierASRO: @SemiRingOrder CarrierA CarrierAe CarrierAplus CarrierAmult CarrierAz CarrierA1 CarrierAle.

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


