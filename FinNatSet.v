Require Import Coq.Init.Specif.
Require Import Coq.Sets.Ensembles.

Notation EFinNatSet n := (Ensemble {x:nat | (x<n)}).

Definition Nsingleton {n:nat} (i:nat): EFinNatSet n :=
  fun x => proj1_sig x = i.

