Require Import Helix.MSigmaHCOL.Memory.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.HCOL.CarrierType.

Require Import Coq.Classes.RelationClasses.
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.misc.decision.
Require Import MathClasses.misc.util.

Require Import Helix.Tactics.HelixTactics.

(* Custom equality of memory blocks using (@equiv CarrierA) on members *)
Global Instance mem_block_Equiv: Equiv (mem_block) :=
  fun m m' => forall k : NM.key, NM.find k m = NM.find k m'.

Global Instance mem_block_Equiv_Reflexive:
  Reflexive (mem_block_Equiv).
Proof.
  unfold mem_block_Equiv.
  unfold Reflexive.
  reflexivity.
Qed.

Global Instance mem_block_Equiv_Symmetric:
  Symmetric (mem_block_Equiv).
Proof.
  unfold mem_block_Equiv.
  unfold Symmetric.
  intros x y H k.
  specialize (H k).
  auto.
Qed.

Global Instance mem_block_Equiv_Transitive:
  Transitive (mem_block_Equiv).
Proof.
  unfold mem_block_Equiv.
  unfold Transitive.
  intros x y z H0 H1 k.
  specialize (H0 k).
  specialize (H1 k).
  auto.
Qed.

Global Instance mem_block_Equiv_Equivalence:
  Equivalence (mem_block_Equiv).
Proof.
  split; typeclasses eauto.
Qed.

Ltac mem_index_equiv k :=
  unfold equiv, mem_block_Equiv;
  intros k.

Global Instance mem_lookup_proper:
  Proper ((eq) ==> (=) ==> (=)) (mem_lookup).
Proof.
  simpl_relation.
  apply H0.
Qed.

Lemma MapsTo_In (k:nat) {A:Type} (e:A) (m:NatMap A):
  NM.MapsTo k e m -> NM.In k m.
Proof.
  intros H.
  apply NP.F.in_find_iff.
  apply NM.find_1 in H.
  congruence.
Qed.

Lemma In_MapsTo (k:nat) {A:Type} (m:NatMap A):
  NM.In k m -> exists e, NM.MapsTo k e m.
Proof.
  intros H.
  apply NP.F.in_find_iff in H.
  destruct (NM.find k m) as [e |] eqn:D.
  -
    eexists e.
    apply NM.find_2.
    apply D.
  -
    congruence.
Qed.

Lemma not_maps_to_find {A:Type}  {k v m}:
  ¬ (NM.MapsTo k v m) -> NM.find (elt:=A) k m <> Some v.
Proof.
  intros H.
  destruct (is_Some_dec (NM.find (elt:=A) k m)) as [S | N].
  -
    intros F.
    apply NM.find_2 in F.
    congruence.
  -
    unfold is_Some, not in N.
    break_match_hyp ; try some_none.
    tauto.
Qed.


Global Instance mem_in_proper:
  Proper ((eq) ==> (=) ==> iff) (mem_in).
Proof.
  simpl_relation.
  unfold mem_in.
  split.
  -
    intros H.
    apply NP.F.in_find_iff in H.
    apply NP.F.in_find_iff.
    apply None_nequiv_neq.
    rewrite <- H0.
    apply None_nequiv_neq in H.
    auto.
  -
    intros H.
    apply NP.F.in_find_iff in H.
    apply NP.F.in_find_iff.
    apply None_nequiv_neq.
    rewrite H0.
    apply None_nequiv_neq in H.
    auto.
Qed.
