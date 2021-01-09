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

Set Implicit Arguments.
Class CarrierDefs (CarrierA : Type) : Type :=
  {
  (* Relations *)
  CarrierAe    :> Equiv CarrierA
  ; CarrierAle :> Le CarrierA
  ; CarrierAlt :> Lt CarrierA
  (* Decidability *)
  ; CarrierAltdec     :> forall x y: CarrierA, Decision (x < y)
  ; CarrierAequivdec :> forall x y: CarrierA, Decision (x = y)
  (* Constants *)
  ; CarrierAz :> Zero CarrierA
  ; CarrierA1 :> One CarrierA
  (* operations *)
  ; CarrierAplus :> Plus CarrierA
  ; CarrierAmult :> Mult CarrierA
  ; CarrierAneg  :> Negate CarrierA
  ; CarrierAabs  :> @Abs CarrierA CarrierAe CarrierAle CarrierAz CarrierAneg
  }.

Class CarrierProperties (CarrierA : Type)(CADEFS: CarrierDefs CarrierA): Prop :=
  {
  (* Equality *)
  CarrierAsetoid :> @Setoid CarrierA CarrierAe
  (* Ring *)
  ; CarrierAr :> Ring CarrierA
  (* Orders *)
  ; CarrierAto  :> @TotalOrder CarrierA CarrierAe CarrierAle
  ; CarrierASSO :> @StrictSetoidOrder CarrierA CarrierAe CarrierAlt
  ; CarrierFPSO :> @FullPseudoOrder CarrierA CarrierAe (@strong_setoids.default_apart CarrierA CarrierAe) CarrierAle CarrierAlt
  }.

Section CarrierAExtraProperties.
  Context `{CAPROPS: @CarrierProperties CarrierA CADEFS}.

  Global Instance CarrierAledec: forall x y: CarrierA, Decision (x ≤ y).
  Proof.
    (* This proofs requires FullPseudoOrder *)
    intros x y.
    unfold Decision.
    destruct (CarrierAltdec x y), (CarrierAequivdec x y).
    - left. apply orders.eq_le. assumption.
    - left. apply orders.not_lt_le_flip, orders.lt_flip. assumption.
    - left. apply orders.eq_le. assumption.
    - right. apply orders.lt_not_le_flip.
      apply orders.not_lt_apart_lt_flip; auto.
  Qed.

  Global Instance CarrierA_min_proper: Proper((=) ==> (=) ==> (=)) (@min CarrierA CarrierAle CarrierAledec).
  Proof. typeclasses eauto. Qed.

  Global Instance CarrierA_max_proper: Proper((=) ==> (=) ==> (=)) (@max CarrierA CarrierAle CarrierAledec).
  Proof. typeclasses eauto. Qed.

  (* Zero and One are two distrinct values *)
  Axiom CarrierA_Z_neq_One: CarrierAz ≠ CarrierA1.

  Add Ring RingA: (stdlib_ring_theory CarrierA).

  Global Instance CarrierAPlus_proper:
    Proper ((=) ==> (=) ==> (=)) plus.
  Proof.
    solve_proper.
  Qed.

  Global Instance CarrierAmult_proper:
    Proper((=) ==> (=) ==> (=)) CarrierAmult.
  Proof.
    solve_proper.
  Qed.

  Global Instance CarrierAabs_proper : Proper ((=) ==> (=)) abs.
  Proof.
    typeclasses eauto.
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
  Definition sub {T:Type}
             `{Plus T}
             `{Negate T}
    : T → T → T := plus∘negate.

  (* The following is not strictly necessary as it follows from "properness" of composition, negation, and addition operations. Unfortunately Coq 8.4 class resolution could not find these automatically so we hint it by adding implicit instance. *)
  Global Instance CarrierA_sub_proper:
    Proper ((=) ==> (=) ==> (=)) sub.
  Proof.
    intros a b Ha x y Hx .
    unfold sub, compose.
    rewrite Hx, Ha.
    reflexivity.
  Qed.

  Definition Zless (a b: CarrierA): CarrierA
    := if CarrierAltdec a b then one else zero.

  Global Instance Zless_proper:
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

  Lemma CarrierA_eqb_equiv : forall x y : CarrierA, CarrierA_beq x y ≡ true ↔ equiv x y.
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

End CarrierAExtraProperties.
