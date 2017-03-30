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

  Definition has_upper_bound s n : bool
    := M.fold (fun m b => (m <=? n) && b) s true.

  Definition MFinNatSet (n:nat) : Type
    := {s : M.t | has_upper_bound s n = true}.

  Definition MsingleS (n:nat) (i:nat): MFinNatSet n.
  Proof.
    unfold MFinNatSet.
    case (lt_dec i n); intros.
    -
      exists (M.singleton i).
      unfold has_upper_bound.
      rewrite M.fold_spec.
      simpl.
      assert(l1: i<=n).
      {
        apply Nat.le_lteq.
        left.
        apply l.
      }
      apply Nat_as_DT.leb_le in l1.
      rewrite l1.
      auto.
    -
      exists M.empty.
      auto.
  Defined.

  Example MFoo: M.is_empty (M.inter
                             (proj1_sig (MsingleS 5 2))
                             (proj1_sig (MsingleS 5 1))) = true.
  Proof.
    auto.
  Qed.

End MSet_set.
