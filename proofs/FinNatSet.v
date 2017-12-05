
Require Export Coq.Init.Specif.
Require Export Coq.Sets.Ensembles.
Require Import Coq.Logic.Decidable.
Require Import Spiral.Spiral.

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
