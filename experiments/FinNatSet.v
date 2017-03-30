Require Import Coq.Init.Specif.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.Compare_dec.

Section Ensemble_set.
  Require Import Coq.Sets.Ensembles.

  Definition EFinNatSet (n:nat) : Type := Ensemble {x:nat | (x<n)}.

  Definition singleS (n:nat) (i:nat): EFinNatSet n :=
    fun x => proj1_sig x = i.

  Example Foo: Disjoint _ (singleS 5 1) (singleS 5 2).
  Proof.
    split.
    intros x.
    unfold In.
    unfold not.
    intros H.
    destruct H as [x H1 H2].
    congruence.
  Qed.

End Ensemble_set.


Require Import Orders.
Require Import OrdersEx.
Require Import MSets.
Require Import Arith.

Module M := Make Nat_as_OT.

Section MSet_set.

  Definition has_upper_bound s n := M.fold (fun m b => (m <=? n) && b) s true.
  Definition MFinNatSet n := {s : M.t | has_upper_bound s n = true}.

  Definition MsingleS (n:nat) (i:nat): MFinNatSet n.
  Proof.
    unfold MFinNatSet.

    case (lt_dec i n); intros.
    -
      exists (M.singleton i).
      admit.
    -
      exists M.empty.
      auto.
  Defined.

  Example Foo: Disjoint _ (singleS 5 1) (singleS 5 2).
  Proof.
    split.
    intros x.
    unfold In.
    unfold not.
    intros H.
    destruct H as [x H1 H2].
    congruence.
  Qed.

End MSet_set.
