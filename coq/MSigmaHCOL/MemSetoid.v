Require Import Helix.Util.OptionSetoid.

Require Import Helix.MSigmaHCOL.Memory.
Require Import Helix.MSigmaHCOL.CType.

Require Import Coq.Classes.RelationClasses.
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.misc.decision.
Require Import MathClasses.misc.util.

Require Import Helix.Tactics.HelixTactics.

Module Make (CT : CType).
  Include Memory.Basics CT.

  (* Custom equality of memory blocks using (@equiv t) on members *)
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
      apply None_nequiv_neq in H.
      apply None_nequiv_neq.
      rewrite <- H0.
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

  Global Instance mem_add_proper:
    Proper ((eq) ==> (equiv) ==> (equiv) ==> (equiv)) (mem_add).
  Proof.
    simpl_relation.
    rename y into k'.
    unfold mem_add.
    unfold equiv, mem_block_Equiv in H1.
    specialize (H1 k).
    destruct_opt_r_equiv.
    -
      apply Some_inj_equiv.
      rewrite <- Ha, <- Hb; clear Ha Hb.
      destruct (PeanoNat.Nat.eq_dec k k').
      +
        rewrite 2!NP.F.add_eq_o by auto.
        f_equiv.
        apply H0.
      +
        rewrite 2!NP.F.add_neq_o by auto.
        apply H1.
    -
      destruct (PeanoNat.Nat.eq_dec k k').
      +
        rewrite NP.F.add_eq_o in Hb by auto.
        some_none.
      +
        rewrite NP.F.add_neq_o in Ha by auto.
        rewrite NP.F.add_neq_o in Hb by auto.
        rewrite Ha in H1.
        rewrite Hb in H1.
        some_none.
    -
      destruct (PeanoNat.Nat.eq_dec k k').
      +
        rewrite NP.F.add_eq_o in Ha by auto.
        some_none.
      +
        rewrite NP.F.add_neq_o in Ha by auto.
        rewrite NP.F.add_neq_o in Hb by auto.
        rewrite Ha in H1.
        rewrite Hb in H1.
        some_none.
  Qed.

  (* Equality of memory states *)
  Global Instance memory_Equiv: Equiv (memory) :=
    fun m m' => forall k : NM.key, NM.find k m = NM.find k m'.

  Global Instance memorey_Equiv_Reflexive:
    Reflexive (memory_Equiv).
  Proof.
    unfold memory_Equiv.
    unfold Reflexive.
    reflexivity.
  Qed.

  Global Instance memory_Equiv_Symmetric:
    Symmetric (memory_Equiv).
  Proof.
    unfold memory_Equiv.
    unfold Symmetric.
    intros x y H k.
    specialize (H k).
    auto.
  Qed.

  Global Instance memory_Equiv_Transitive:
    Transitive (memory_Equiv).
  Proof.
    unfold memory_Equiv.
    unfold Transitive.
    intros x y z H0 H1 k.
    specialize (H0 k).
    specialize (H1 k).
    auto.
  Qed.

  Global Instance memory_Equiv_Equivalence:
    Equivalence (memory_Equiv).
  Proof.
    split; typeclasses eauto.
  Qed.

  Global Instance memory_lookup_proper:
    Proper ((=) ==> (eq) ==> (=)) (memory_lookup).
  Proof.
    simpl_relation.
    apply H.
  Qed.

  Global Instance mem_block_exists_proper:
    Proper ((eq) ==> (=) ==> iff) (mem_block_exists).
  Proof.
    simpl_relation.
    unfold mem_block_exists, memory, mem_block in *.
    split.
    -
      intros H.
      apply NP.F.in_find_iff in H.
      apply NP.F.in_find_iff.
      apply None_nequiv_neq.
      apply None_nequiv_neq in H.
      unfold equiv, memory_Equiv in H0.
      rewrite <- H0.
      apply H.
    -
      intros H.
      apply NP.F.in_find_iff in H.
      apply NP.F.in_find_iff.
      apply None_nequiv_neq.
      unfold equiv, memory_Equiv in H0.
      rewrite H0.
      apply None_nequiv_neq in H.
      auto.
  Qed.

  Lemma mem_block_exists_exists_equiv (m:memory) (k:nat):
    mem_block_exists k m <-> exists y : mem_block, memory_lookup m k = Some y.
  Proof.
    split; intros H.
    -
      apply NP.F.in_find_iff, is_Some_ne_None, is_Some_equiv_def in H.
      eauto.
    -
      apply NP.F.in_find_iff, is_Some_ne_None, is_Some_equiv_def.
      eauto.
  Qed.

End Make.
