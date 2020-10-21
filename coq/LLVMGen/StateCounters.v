Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

(* TODO: Not sure where this should belong *)
Lemma resolve_PVar_simple : forall p s s' x v,
    resolve_PVar p s ≡ inr (s', (x, v)) ->
    exists sz n,
      nth_error (Γ s') n ≡ Some (x, TYPE_Pointer (TYPE_Array sz TYPE_Double)) /\
      MInt64asNT.from_Z sz ≡ inr v /\ p ≡ PVar n /\ s ≡ s'.
Proof.
  intros * H.
  unfold resolve_PVar in H.
  cbn* in H.
  simp.
  do 2 eexists; eauto.
Qed.

Ltac inv_resolve_PVar H :=
  apply resolve_PVar_simple in H;
  destruct H as (?sz & ?n & ?LUn & ?EQsz & -> & <-).


Global Opaque resolve_PVar.

(* TODO: Move this? *)
Lemma incVoid_block_count :
  forall s1 s2 bid,
    incVoid s1 ≡ inr (s2, bid) ->
    block_count s1 ≡ block_count s2.
Proof.
  intros s1 s2 bid H.
  Transparent incVoid.
  unfold incVoid in H.
  cbn in H.
  simp.
  destruct s1; cbn; auto.
  Opaque incVoid.
Qed.

(* TODO: Move this? *)
Lemma incLocal_block_count :
  forall s1 s2 bid,
    incLocal s1 ≡ inr (s2, bid) ->
    block_count s1 ≡ block_count s2.
Proof.
  intros s1 s2 bid H.
  Transparent incLocal.
  unfold incLocal in H.
  cbn in H.
  simp.
  destruct s1; cbn; auto.
  Opaque incLocal.
Qed.

(* TODO: uncertain if this belongs somewhere else *)
Lemma resolve_PVar_state :
  forall p s1 s2 x,
    resolve_PVar p s1 ≡ inr (s2, x) ->
    s1 ≡ s2.
Proof.
  intros p s1 s2 [x v] H.
  pose proof resolve_PVar_simple p s1 H as H0.
  destruct H0 as (sz & n & H0).
  intuition.
Qed.
