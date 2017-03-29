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


Require Import Coq.MSets.MSets.
Require Import Coq.MSets.MSetList.

Print OrderedTypeWithLeibniz.

Module OWL.
  Definition t := nat.
  Definition eq := @eq t.
  Instance eq_equiv : Equivalence eq := eq_equivalence.
  Definition lt := Peano.lt.
  Instance lt_strorder : StrictOrder lt := Nat_as_DT.lt_strorder.
  Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    now unfold eq; split; subst.
  Qed.
  Definition compare := Compare_dec.nat_compare.
  Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
  Proof.
    intros; case_eq (compare x y); constructor.
    now apply Compare_dec.nat_compare_eq.
    now apply Compare_dec.nat_compare_Lt_lt.
    now apply Compare_dec.nat_compare_Gt_gt.
  Qed.
  Definition eq_dec := Peano_dec.eq_nat_dec.
  Definition eq_leibniz a b (H:eq a b) := H.
End OWL.

Module NatSet := MakeWithLeibniz OWL.

Section MSet_set.

  Definition <FinNatSet (n:nat) : Type :=
    Ensemble {x:nat | (x<n)}.

  Definition singleS (n:nat) (i:nat): MFinNatSet n :=
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

End MSet_set.
