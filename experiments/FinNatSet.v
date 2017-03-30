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
Require Import Omega.

Module NatSet := Make Nat_as_OT.

Section MSet_set.

  Import NatSet.

  Definition has_upper_bound n
    := For_all (gt n).

  Definition MFinNatSet (n:nat) : Type
    := {s: t | has_upper_bound n s}.

  Definition MsingleS (n:nat) (i:nat): MFinNatSet n.
  Proof.
    unfold MFinNatSet.
    case (lt_dec i n); intros H.
    -
      exists (singleton i).
      unfold has_upper_bound, For_all.
      intros x I.
      apply singleton_spec in I.
      omega.
    -
      exists empty.
      unfold has_upper_bound, For_all.
      intros x I.
      apply empty_spec in I.
      contradiction I.
  Defined.

  Example MFoo: Empty (inter
                         (proj1_sig (MsingleS 5 2))
                         (proj1_sig (MsingleS 5 1))).
  Proof.
    simpl.
    unfold Empty.
    intros a.
    intros H.
    apply inter_spec in H.
    destruct H as [H1 H2].
    apply singleton_spec in H1.
    apply singleton_spec in H2.
    congruence.
  Qed.

End MSet_set.
