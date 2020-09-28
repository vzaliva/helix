(* This file includes proof of some lemmas about Scatter and Gather operators.
   It is not critical to HELIX work and may contain admitted lemmas.
 *)

Require Import Helix.SigmaHCOL.SigmaHCOL.
Require Import Helix.SigmaHCOL.IndexFunctions.
Require Import Helix.SigmaHCOL.Rtheta.
Require Import Helix.SigmaHCOL.SigmaHCOLImpl.
Require Import Helix.Util.VecUtil.
Require Import Helix.Util.VecSetoid.
Require Import Helix.Util.Misc.
Require Import Helix.Util.FinNat.

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Decidable.

Require Import Helix.Tactics.HelixTactics.
Require Import Psatz.
Require Import Coq.micromega.Lia.

Require Import MathClasses.interfaces.abstract_algebra.

Require Import CoLoR.Util.Nat.NatUtil.

Import VectorNotations.

Open Scope vector_scope.
Open Scope nat_scope.


Notation "g ⊚ f" := (@SHCompose _ _ _ _ _ g f) (at level 40, left associativity) : type_scope.

Lemma ScatterGather_identity {n:nat}
      {f:index_map n n}
      {f_inj: index_map_injective f}
  :
    forall x, (op (svalue:=zero) Monoid_RthetaFlags (Gather _ f ⊚ Scatter (f_inj:=f_inj) _ f)) x = x.
Proof.
  intros x.
  simpl.
  unfold compose.
  vec_index_equiv j jc.
  rewrite Gather_impl_spec.
  rewrite <- Scatter_impl_spec.
  reflexivity.
Qed.

Definition n_nth (n : nat) (f : nat -> nat) : (nat -> nat) :=
  fun x => if x =? n
        then n
        else if f x =? n
             then f n
             else f x.

Lemma inj_n_nth_shrink_spec
      {f : nat -> nat} {n : nat}
      (f_inj : forall x y, x < (S n) -> y < (S n) -> f x ≡ f y → x ≡ y)
  :
    (forall x : nat, x < (S n) → f x < (S n)) ->
    (forall x : nat, x < n → (n_nth n f) x < n).
Proof.
  intros.
  unfold n_nth.
  repeat break_if;
    try rewrite Nat.eqb_neq in *;
    try rewrite Nat.eqb_eq in *.
  -
    lia.
  -
    specialize (H n).
    autospecialize H; [constructor |].
    destruct (Nat.eq_dec (f n) n); [| lia].
    specialize (f_inj x n).
    full_autospecialize f_inj; lia.
  -
    enough (f x < S n) by lia.
    apply H.
    lia.
Qed.

Lemma index_map_inj_surj
      {n: nat}
      {f: index_map n n}
      (f_inj: index_map_injective f):
  index_map_surjective f.
Proof.
  intros y yc.

  unfold index_map_injective in f_inj.
  destruct f as [f T]; cbn in *.
  assert (D : forall x1, x1 < n -> f x1 < n) by assumption.
  assert (INJ : forall x1 x2, x1 < n -> x2 < n -> f x1 ≡ f x2 -> x1 ≡ x2) by auto.
  clear f_inj T.

  enough (T : exists x, x < n /\ f x ≡ y) by (destruct T as [x [xc T]]; eauto).

  generalize dependent f.
  induction n.
  -
    lia.
  -
    intros.
    destruct (Nat.eq_dec y n).
    +
      subst.
      clear IHn yc.

      (* I don't think this can be avoided:
           IB: map size 0 - trivial
           IH: map size n maps all elements below n
           IS: map size n -> map size (S n)
               Consider the element to be found (y):
               1) y < n: can be found through "shrinking",
                         as shown in the rest of this proof
               2) y = n: this is the new part of the codomain,
                         IH is powerless

           We are in [2].
       *)
      admit.
    +
      assert (YN : y < n) by lia; clear n0 yc.
      autospecialize IHn; [assumption |].
      specialize (IHn (n_nth n f)).
      full_autospecialize IHn.
      {
        apply inj_n_nth_shrink_spec; auto.
      }
      {
        intros.
        apply INJ; try lia.
        unfold n_nth in *.
        repeat break_if;
          try rewrite Nat.eqb_neq in *;
          try rewrite Nat.eqb_eq in *;
          try (subst; lia).
        apply INJ in H1; lia.
        apply INJ in H1; lia.
      }
      destruct IHn as [x [xc R]].
      unfold n_nth in *.
      repeat break_if;
        try rewrite Nat.eqb_neq in *;
        try rewrite Nat.eqb_eq in *;
        try (subst; lia).
      exists n; auto.
      exists x; auto.
Admitted.

Lemma GatherScatter_identity {n:nat}
      {f:index_map n n}
      {f_inj: index_map_injective f}
  :
    forall x, (op (svalue:=zero) Monoid_RthetaFlags (Scatter (f_inj:=f_inj) _ f  ⊚ Gather _ f)) x = x.
Proof.
  intros x.
  simpl.
  unfold compose.
  vec_index_equiv j jc.
  pose proof Scatter_impl_spec as SS.
  unfold VnthIndexMapped in SS.
  specialize (SS Monoid_RthetaFlags n n f f_inj zero (Gather_impl f x)).
  setoid_rewrite Gather_impl_spec in SS.
  unfold VnthIndexMapped in SS.
  symmetry.
  assert(exists j' (jc:j'<n), ⟦ f ⟧ j' ≡ j) as JJ.
  {
    cut (index_map_surjective f).
    auto.
    apply index_map_inj_surj, f_inj.
  }
  destruct JJ as (j' & jc' & JJ).

  specialize (SS j' jc').
  erewrite Vnth_eq.
  erewrite SS.
  2:auto.
  clear SS.
  apply Vnth_equiv.
  auto.
  reflexivity.
Qed.

(* [g] is left inverse of [f] *)
Definition left_inverse {n} (g f: index_map n n) :=
  forall x (xc:x<n) y, ⟦ f ⟧ x = y -> ⟦ g ⟧ y = x.

(* [h] is right inverse of [f] *)
Definition right_inverse {n} (h f: index_map n n) :=
  forall x (xc:x<n) y, ⟦ h ⟧ y = x -> ⟦ f ⟧ x = y.

(* A function [f] with a left inverse is necessarily injective. *)
Lemma left_inverse_is_injective {n:nat} {f: index_map n n}:
  exists g, left_inverse g f -> index_map_injective f.
Proof.
  eexists.
  intros HI. unfold left_inverse in HI.
  intros x y xc yc H.
  (* not sure we need this lemma *)
Admitted.

Lemma ScatterGather
      {n:nat}
      {f h:index_map n n}
      {f_inj: index_map_injective f}
      {inv: right_inverse h f}
      {fm}
      {svalue}
  :
    Scatter (svalue:=svalue) (f_inj:=f_inj) fm f = Gather fm h.
Proof.
  unfold equiv, SHOperator_equiv.
  simpl.
  unfold equiv.
  intros x y E.
  vec_index_equiv j jc.
  rewrite Gather_impl_spec.
  unfold VnthIndexMapped.
  unfold right_inverse in inv.
  Set Printing Implicit.
Admitted.

(*
  Lemma ScatterGather
        {n:nat}
        {f g:index_map n n}
        {f_inj: index_map_injective f}
        {inv: left_inverse g f}
        {fm}
        {svalue}
    :
      Scatter (svalue:=svalue) (f_inj:=f_inj) fm f = Gather fm g.
  Proof.
    unfold equiv, SHOperator_equiv.
    simpl.
    unfold equiv.
    intros x y E.
    vec_index_equiv j jc.
    rewrite Gather_impl_spec.
    unfold VnthIndexMapped.
    unfold left_inverse in inv.
    Set Printing Implicit.
  Admitted.
 *)
