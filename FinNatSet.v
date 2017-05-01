Require Export Coq.Init.Specif.
Require Export Coq.Sets.Ensembles.
Require Import Coq.Logic.Decidable.

Notation FinNat n := {x:nat | (x<n)}.
Notation FinNatSet n := (Ensemble (FinNat n)).

Definition mkFinNat {n} {j:nat} (jc:j<n) : FinNat n := exist (gt n) j jc.

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
