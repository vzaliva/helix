Require Import Helix.SigmaHCOL.Memory.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.HCOL.CarrierType.

Require Import Coq.Classes.RelationClasses.
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.misc.decision.
Require Import MathClasses.misc.util.

Require Import Helix.Tactics.HelixTactics.

Global Instance mem_block_Equiv:
  Equiv (mem_block) := mem_block_equiv.

Global Instance mem_block_Equiv_Reflexive:
  Reflexive (mem_block_Equiv).
Proof.
  unfold mem_block_Equiv, mem_block_equiv.
  unfold Reflexive.
  apply NP.F.Equal_refl.
Qed.

Global Instance mem_block_Equiv_Symmetric:
  Symmetric (mem_block_Equiv).
Proof.
  unfold mem_block_Equiv, mem_block_equiv.
  unfold Symmetric.
  apply NP.F.Equal_sym.
Qed.

Global Instance mem_block_Equiv_Transitive:
  Transitive (mem_block_Equiv).
Proof.
  unfold mem_block_Equiv, mem_block_equiv.
  unfold Transitive.
  apply NP.F.Equal_trans.
Qed.

Global Instance mem_block_Equiv_Equivalence:
  Equivalence (mem_block_Equiv).
Proof.
  unfold mem_block_Equiv, mem_block_equiv.
  apply NP.F.Equal_ST.
Qed.

Global Instance mem_lookup_proper:
  Proper ((eq) ==> (=) ==> (=)) (mem_lookup).
Proof.
  simpl_relation.
  unfold equiv, mem_block_Equiv, mem_block_equiv, NM.Equal in H0.
  unfold mem_lookup.
  specialize (H0 y).

  destruct ((NM.find (elt:=CarrierA) y x0)) eqn:E1;
    destruct (NM.find (elt:=CarrierA) y y0) eqn:E2; simpl.
  -
    apply RelUtil.opt_r_Some.
    some_inv.
    rewrite <- H1.
    reflexivity.
  -
    some_none.
  -
    some_none.
  -
    reflexivity.
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

Global Instance mem_mapsto_proper:
  Proper ((eq) ==> (eq) ==> (=) ==> iff) (mem_mapsto).
Proof.
  simpl_relation.
  unfold mem_mapsto.

  unfold equiv,mem_block_Equiv,mem_block_equiv,NM.Equal in H1.
  specialize (H1 y).
  split.
  -
    intros H.
    apply NM.find_1 in H.
    apply NM.find_2.
    rewrite <- H1.
    rewrite H.
    f_equal.
  -
    intros H.
    apply NM.find_1 in H.
    apply NM.find_2.
    rewrite H1.
    rewrite H.
    f_equal.
Qed.

Global Instance mem_in_proper:
  Proper ((eq) ==> (=) ==> iff) (mem_in).
Proof.
  simpl_relation.
  unfold mem_in.
  split.
  -
    intros H.
    apply In_MapsTo in H.
    destruct H as [e H].
    apply MapsTo_In with (e:=e).
    rewrite <- H0.
    apply H.
  -
    intros H.
    apply In_MapsTo in H.
    destruct H as [e H].
    apply MapsTo_In with (e:=e).
    rewrite H0.
    apply H.
Qed.
