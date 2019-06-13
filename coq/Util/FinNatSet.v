
Require Export Coq.Init.Specif.
Require Export Coq.Sets.Ensembles.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Logic.Decidable.
Require Import Coq.Arith.Peano_dec.

Require Import Helix.Util.Misc.
Require Import Helix.Util.FinNat.
Require Import Helix.Tactics.HelixTactics.

Notation FinNatSet n := (Ensemble (FinNat n)).

Definition singleton {n:nat} (i:nat): FinNatSet n :=
  fun x => proj1_sig x = i.

Definition FinNatSet_dec {n: nat} (s: FinNatSet n) := forall x, decidable (s x).

Lemma Full_FinNatSet_dec:
  forall i : nat, FinNatSet_dec (Full_set (FinNat i)).
Proof.
  unfold FinNatSet_dec.
  intros i x.
  unfold decidable.
  left.
  split.
Qed.

Lemma Empty_FinNatSet_dec:
  forall i : nat, FinNatSet_dec (Empty_set (FinNat i)).
Proof.
  unfold FinNatSet_dec.
  intros i x.
  unfold decidable.
  right.
  unfold not.
  intros H.
  destruct H.
Qed.

Lemma Singleton_FinNatSet_dec:
  forall n i : nat, FinNatSet_dec (@singleton n i).
Proof.
  unfold FinNatSet_dec.
  intros n i x.
  unfold decidable.
  unfold singleton.
  destruct (eq_nat_dec (proj1_sig x) i); auto.
Qed.

Lemma Union_FinNatSet_dec
      {n}
      {a b: FinNatSet n}:
  FinNatSet_dec a -> FinNatSet_dec b ->
  FinNatSet_dec (Union _ a b).
Proof.
  intros A B.
  unfold FinNatSet_dec in *.
  intros x.
  specialize (A x).
  specialize (B x).
  destruct A.
  -
    unfold decidable.
    left.
    apply Union_introl.
    apply H.
  -
    unfold decidable.
    destruct B as [H0 | H1].
    + left.
      apply Union_intror.
      apply H0.
    +
      right.
      intros U.
      inversion U;  unfold In in H0;  congruence.
Qed.

Lemma Union_Empty_set_runit:
  forall n B, FinNatSet_dec B ->
         Same_set _ (Union (FinNat n) B (Empty_set (FinNat n))) B.
Proof.
  intros n B D.
  split.
  -
    unfold Included.
    intros x H.
    destruct H.
    apply H.
    destruct H.
  -
    unfold Included.
    intros x H.
    apply Union_introl.
    apply H.
Qed.

Lemma Union_Empty_set_lunit:
  forall n B, FinNatSet_dec B ->
         Same_set _ B (Union (FinNat n) B (Empty_set (FinNat n))).
Proof.
  intros n B D.
  split.
  -
    unfold Included.
    intros x H.
    apply Union_introl.
    apply H.
  -
    unfold Included.
    intros x H.
    destruct H.
    apply H.
    destruct H.
Qed.

Lemma Union_comm
      {U:Type}
      {B C: Ensemble U}:
  forall x, In _ (Union U B C) x <-> In _ (Union U C B) x.
Proof.
  intros x.
  split.
  -
    intros [H1 | H2].
    + apply Union_intror, H.
    + apply Union_introl, H.
  -
    intros [H1 | H2].
    + apply Union_intror, H.
    + apply Union_introl, H.
Qed.

Lemma Disjoined_singletons
      (q m n : nat)
      (H: not (m = n)):
  Disjoint (FinNat q) (singleton m) (singleton n).
Proof.
  apply Disjoint_intro.
  intros x.
  unfold In.
  unfold not.
  intros I.
  destruct I.
  unfold In, singleton in *.
  crush.
Qed.


(* The following are not FinNat specific, but they are kept here for a lack of better place *)

Lemma Disjoint_Included
      {T:Type}
      (A A' B B': Ensemble T)
      (D: Disjoint T A B):
  Included T A' A ->
  Included T B' B ->
  Disjoint T A' B'.
Proof.
  intros IA IB.
  apply Disjoint_intro.
  intros x.
  destruct D as [D].
  specialize (D x).
  intros C.
  unfold In in C.
  destruct C as [x I0 I1].
  unfold In in *.
  contradict D.
  apply Intersection_intro.
  - apply IA, I0.
  - apply IB, I1.
Qed.

Lemma Disjoint_Symmetric
      {T:Type}
      (A B: Ensemble T):
  Disjoint T A B <-> Disjoint T B A.
Proof.

  split; intros H;

    destruct H as [H0];
    apply Disjoint_intro;
    intros x;
    specialize (H0 x);
    intros H1;
    destruct H1 as [H1];
    contradict H0;
    crush.
Qed.

Lemma Disjoint_empty
      {T: Type}
      {B: Ensemble T}
  :
    Disjoint T (Empty_set T) B.
Proof.
  split.
  intros x H.
  unfold Ensembles.In in *.
  destruct H.
  apply Constructive_sets.Noone_in_empty in H.
  tauto.
Qed.

Lemma Union_comm_eq {T:Type} {a b}
  : Union T a b = Union T b a.
Proof.
  apply Extensionality_Ensembles.
  split; unfold Included; intros; apply Union_comm, H.
Qed.
