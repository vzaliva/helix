Require Import Coq.Sets.Ensembles.
Require Import Coq.Vectors.Fin.

(*
Inductive FinNatSet (n:nat) : Ensemble (Fin.t n) :=
  FinNatSet_defn : forall x:(Fin.t n), In (Fin.t n) (FinNatSet n) x.
*)

Definition FinNatSet (n:nat) := Ensemble (Fin.t n).

Definition singleS (x n:nat): FinNatSet n :=
  (fun fn : t n =>
     match (@to_nat n fn) return Prop with
     | exist _ i _ => i=x
     end).

Example Foo1: Disjoint (Fin.t 5) (singleS 1 5) (singleS 2 5).
Proof.
  split.
  intros x.
  unfold In.
  unfold not.
  intros H.
  destruct H as [x H1 H2].

    
  induction x.
  -

Qed.

