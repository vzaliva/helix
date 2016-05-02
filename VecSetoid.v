Require Import Coq.Arith.Arith.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Program.Basics. (* for \circ notation *)
Require Import Coq.omega.Omega.
Require Export Coq.Vectors.Vector.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders.
Require Import MathClasses.orders.minmax MathClasses.orders.orders MathClasses.orders.rings.
Require Import MathClasses.theory.rings MathClasses.theory.abs.
Require Import MathClasses.theory.products.
Require Import MathClasses.theory.naturals.

(* CoLoR *)
Require Export CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

Require Import CaseNaming.
Require Import CpdtTactics.
Require Import JRWTactics.
Require Import SpiralTactics.

(* Various definitions related to vector equality and setoid rewriting *)

Section VectorSetoid.

  Global Instance vec_Equiv `{Equiv A} {n}: Equiv (vector A n)
    := Vforall2 (n:=n) equiv.

  Global Instance vec_Equivalence `{Ae: Equiv A} {n:nat}
         `{!Equivalence (@equiv A _)}
    : Equivalence (@vec_Equiv A Ae n).
  Proof.
    unfold vec_Equiv.
    apply Vforall2_equiv.
    assumption.
  Qed.

  Global Instance vec_Setoid `{Setoid A} {n}: Setoid (vector A n).
  Proof.
    unfold Setoid.
    apply vec_Equivalence.
  Qed.

End VectorSetoid.

(* TODO: check if needed for Coq-8.5 *)
Section Vfold_right.
  Context
    `{eqA: Equiv A}
    `{eqB: Equiv B}.

  Definition Vfold_right_reord {A B:Type} {n} (f:A->B->B) (v: vector A n) (initial:B): B := @Vfold_right A B f n v initial.

  Lemma Vfold_right_to_Vfold_right_reord: forall {A B:Type} {n} (f:A->B->B) (v: vector A n) (initial:B),
      Vfold_right f v initial ≡ Vfold_right_reord f v initial.
  Proof.
    crush.
  Qed.

  Global Instance Vfold_right_reord_proper n :
    Proper (((=) ==> (=) ==> (=)) ==> (@vec_Equiv A _ n ==> (=) ==> (=)))
           (@Vfold_right_reord A B n).
  Proof.
    intros f f' Ef v v' vEq i i' iEq.
    unfold Vfold_right_reord.
    induction v.
    Case "N=0".
    VOtac. simpl. assumption.
    Case "S(N)".
    revert vEq. VSntac v'. unfold vec_Equiv. rewrite Vforall2_cons_eq. intuition. simpl.
    apply Ef.
    SCase "Pf - 1".
    assumption.
    SCase "Pf - 2".
    apply IHv. unfold vec_Equiv.  assumption.
  Qed.

End Vfold_right.

(* TODO: check if needed for Coq-8.5 *)
Section VCons.
  Definition Vcons_reord {A} {n} (t: vector A n) (h:A): vector A (S n) := Vcons h t.

  Lemma Vcons_to_Vcons_reord: forall A n (t: t A n) (h:A), Vcons h t  ≡ Vcons_reord t h.
  Proof.
    crush.
  Qed.

  Global Instance Vcons_reord_proper `{Equiv A} n:
    Proper ((=) ==> (=) ==> (=))
           (@Vcons_reord A n).
  Proof.
    split.
    assumption.
    unfold vec_Equiv, Vforall2 in H0.  assumption.
  Qed.

End VCons.
