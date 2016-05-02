
Require Import VecUtil.

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

Instance Vapp_proper `{Sa: Setoid A} (n1 n2:nat):
  Proper ((=) ==>  (=) ==> (=)) (@Vapp A n1 n2).
Proof.
  intros a0 a1 aEq b0 b1 bEq.
  induction n1.
  VOtac. auto.

  dep_destruct a0.
  dep_destruct a1.
  rewrite 2!Vapp_cons.

  assert (h=h0).
  apply aEq.

  rewrite 2!Vcons_to_Vcons_reord.
  rewrite H.
  rewrite <- 2!Vcons_to_Vcons_reord.

  unfold equiv, vec_Equiv.
  apply Vforall2_cons_eq.
  split. reflexivity.

  unfold equiv, vec_Equiv in IHn1.
  apply IHn1.
  apply aEq.
Qed.

Instance Vhead_proper A `{H:Equiv A} n:
  Proper (@equiv (vector A (S n)) (@vec_Equiv A H (S n)) ==> @equiv A H) (@Vhead A n).
Proof.
  intros a b E.
  dep_destruct a.  dep_destruct b.
  unfold equiv, vec_Equiv, vec_Equiv, relation in E.
  rewrite Vforall2_cons_eq in E.
  intuition.
Defined.

Instance Vtail_proper `{Equiv A} n:
  Proper (@vec_Equiv A _ (S n) ==> @vec_Equiv A _ n)
         (@Vtail A n).
Proof.
  intros a b E.
  unfold equiv, vec_Equiv, vec_Equiv, relation in E.
  apply Vforall2_tail in E.
  unfold vec_Equiv.
  assumption.
Defined.

Instance Ptail_proper `{Sa: Setoid A} `{Sb: Setoid B} (n:nat):
  Proper ((=) ==> (=)) (@Ptail A B n).
Proof.
  intros x y E.
  destruct x as [xa xb].
  destruct y as [ya yb].
  destruct E as [E1 E2].
  simpl in E1. simpl in E2.
  unfold Ptail.
  rewrite E1, E2.
  reflexivity.
Qed.

Lemma Vmap_equiv_cons: forall A B `{Setoid B} (f:A->B) n (x:A) (xs: vector A n),
    Vmap f (Vcons x xs) = Vcons (f x) (Vmap f xs).
Proof.
  intros.
  constructor. reflexivity.
  fold (Vforall2 (n:=n) equiv (Vmap f xs) (Vmap f xs)).
  fold (vec_Equiv (Vmap f xs) (Vmap f xs)).
  fold (equiv (Vmap f xs) (Vmap f xs)).
  reflexivity.
Qed.

Lemma Vmap2_cons_hd: forall A B C `{Setoid C} (f:A->B->C) n (a:vector A (S n)) (b:vector B (S n)),
    Vmap2 f a b = Vcons (f (Vhead a) (Vhead b)) (Vmap2 f (Vtail a) (Vtail b)).
Proof.
  intros.
  dep_destruct a.
  dep_destruct b.
  reflexivity.
Qed.

Lemma Vmap2_cons: forall A B C `{Setoid C} (f:A->B->C) n (a:A) (b:B) (a':vector A n) (b':vector B n),
    Vmap2 f (Vcons a a') (Vcons b b') = Vcons (f a b) (Vmap2 f a' b').
Proof.
  intros.
  reflexivity.
Qed.

Lemma Vmap2_comm
      `{CO:Commutative B A f}
      `{SB: !Setoid B} {n:nat}:
  Commutative (Vmap2 f (n:=n)).
Proof.
  unfold Commutative.
  intros a b.
  induction n.
  dep_destruct a.
  dep_destruct b.
  reflexivity.
  rewrite Vmap2_cons_hd by apply SB.

  (* reorder LHS head *)

  rewrite Vcons_to_Vcons_reord.
  rewrite commutativity.
  rewrite <- IHn. (* reoder LHS tail *)
  setoid_rewrite <- Vmap2_cons.
  reflexivity.
  assumption.
Qed.

Lemma hd_equiv: forall `{Setoid A} {n} (u v: vector A (S n)), u=v -> (Vhead u) = (Vhead v).
Proof.
  intros.
  rewrite H0.
  f_equiv.
Qed.

Lemma Vcons_equiv_elim `{Equiv A}: forall a1 a2 n (v1 v2 : vector A n),
    Vcons a1 v1 = Vcons a2 v2 -> a1 = a2 /\ v1 = v2.
Proof.
  intros. auto.
Qed.

Lemma Vcons_equiv_intro `{Setoid A} : forall a1 a2 n (v1 v2 : vector A n),
    a1 = a2 -> v1 = v2 -> Vcons a1 v1 = Vcons a2 v2.
Proof.
  intros.
  rewrite 2!Vcons_to_Vcons_reord.
  rewrite H0.
  rewrite H1.
  reflexivity.
Qed.

Lemma Vcons_single_elim `{Equiv A} : forall a1 a2,
    Vcons a1 (@Vnil A) = Vcons a2 (@Vnil A) <-> a1 = a2.
Proof.
  intros a1 a2.
  unfold equiv, vec_Equiv.
  rewrite Vforall2_cons_eq.
  assert(Vforall2 equiv (@Vnil A) (@Vnil A)).
  constructor.
  split; tauto.
Qed.

(* TODO: Check if it is still needed in Coq-8.5 *)
Section VMap_reord.

  Definition Vmap_reord (A B: Type) (n:nat) (f:A->B) (x: vector A n): vector B n := Vmap f x.

  Lemma Vmap_to_Vmap_reord: forall (A B: Type) (n:nat) (f:A->B) (x: vector A n), @Vmap A B f n x ≡ @Vmap_reord A B n f x.
  Proof.
    crush.
  Qed.

  Global Instance Vmap_reord_proper n (M N:Type) `{Ne:!Equiv N, Me:!Equiv M}:
    Proper (((=) ==> (=)) ==> (=) ==> (=))
           (@Vmap_reord M N n).
  Proof.
    intros f g Eext a b Ev.
    induction n.
    Case "N=0".
    VOtac. auto.
    Case "S N".
    dep_destruct a. dep_destruct b.
    split.
    apply Eext, Ev.
    apply IHn, Ev.
  Qed.

  Global Instance Vmap_arg_proper  (M N:Type) `{Me:!Equiv M} `{Ne: !Equiv N} (f : M->N)
           `{fP: !Proper (Me ==> Ne) f} (n:nat):
    Proper ((@vec_Equiv M _ n) ==> (@vec_Equiv N _ n)) (@Vmap M N f n).
  Proof.
    intros a b Ea.
    unfold vec_Equiv.
    induction n.
    Case "N=0".
    VOtac. auto.
    Case "S N".
    dep_destruct a. dep_destruct b.
    split.
    apply fP, Ea.
    apply IHn, Ea.
  Qed.

End VMap_reord.


Instance VBreak_proper (A:Type) `{Setoid A} (n1 n2:nat) `{Plus nat}:
  Proper ((=) ==> (=)) (@Vbreak A n1 n2).
Proof.
  intros v v1 vE.
  induction n1.
  simpl. setoid_rewrite vE. reflexivity.
  assert (V1: v ≡ Vapp (fst (Vbreak (n1:=1) v)) (snd (Vbreak (n1:=1) v))).
  simpl. dep_destruct v. reflexivity.
  assert (V2: v1 ≡ Vapp (fst (Vbreak (n1:=1) v1)) (snd (Vbreak (n1:=1) v1))).
  simpl. dep_destruct v1. reflexivity.
  rewrite V1. clear V1. rewrite V2. clear V2.
  dep_destruct v. dep_destruct v1.
  simpl.

  rewrite 2!Vcons_to_Vcons_reord.
  assert (E: Vbreak x = Vbreak x0).
  apply IHn1.  apply vE.
  rewrite E.
  setoid_replace h with h0 by apply vE.
  reflexivity.
Qed.
