Require Export Coq.Init.Specif.
Require Export Coq.Sets.Ensembles.

Notation FinNat n := {x:nat | (x<n)}.
Notation FinNatSet n := (Ensemble (FinNat n)).

Definition mkFinNat {n} {j:nat} (jc:j<n) : FinNat n := exist (gt n) j jc.

Definition singleton {n:nat} (i:nat): FinNatSet n :=
  fun x => proj1_sig x = i.

