Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.
Require Import Helix.LLVMGen.Correctness_MExpr.
Require Import Helix.LLVMGen.Correctness_AExpr.
Require Import Helix.LLVMGen.Correctness_GenIR.
Require Import Helix.LLVMGen.IdLemmas.
Require Import Helix.LLVMGen.StateCounters.
Require Import Helix.LLVMGen.VariableBinding.
Require Import Helix.LLVMGen.BidBound.

Set Nested Proofs Allowed.

Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

Set Implicit Arguments.
Set Strict Implicit.

Global Opaque resolve_PVar.

Import ProofMode.

From Paco Require Import paco.
From ITree Require Import Basics.HeterogeneousRelations.

(* Remove this later, this lemma exists in Correctness_While as well *)
Lemma eutt_Proper_mono : forall {A B E},
        Proper ((@subrelationH A B) ==> (@subrelationH _ _)) (eutt (E := E)).
Proof.
  intros A B. do 3 red.
    intros E x y. pcofix CIH. pstep. red.
    intros sub a b H.
    do 2 red in H. punfold H. red in H.
    remember (observe a) as a'.
    remember (observe b) as b'.
    generalize dependent a. generalize dependent b.
    induction H; intros; eauto.
    + constructor. red in REL. destruct REL.
      right. apply CIH. assumption. assumption.
      destruct H.
    + constructor. red in REL. intros.
      specialize (REL v). unfold id.
      destruct REL. right. apply CIH. assumption. assumption.
      destruct H.
Qed.

Lemma interp_helix_MemAlloc :
  forall {E} size mem,
    interp_helix (E := E) (trigger (MemAlloc size)) mem ≈
    Ret (Some (mem, memory_next_key mem)).
Proof.
  intros.
  Transparent interp_helix.
  unfold interp_helix.
  Opaque interp_helix.
  setoid_rewrite interp_Mem_vis_eqit.
  cbn. rewrite Eq.bind_ret_l, tau_eutt.
  cbn; rewrite interp_Mem_ret, interp_fail_Ret, translate_ret.
  reflexivity.
Qed.

Lemma interp_helix_MemFree :
  forall {E} size mem,
    interp_helix (E := E) (trigger (MemFree size)) mem ≈
    Ret (Some (memory_remove mem size, ())).
Proof.
  intros.
  Transparent interp_helix.
  unfold interp_helix.
  Opaque interp_helix.
  setoid_rewrite interp_Mem_vis_eqit.
  cbn. rewrite Eq.bind_ret_l, tau_eutt.
  cbn; rewrite interp_Mem_ret, interp_fail_Ret, translate_ret.
  reflexivity.
Qed.

Lemma interp_Mem_MemAlloc :
  forall size mem,
    interp_Mem (trigger (MemAlloc size)) mem ≈
                Ret (mem, memory_next_key mem).
Proof.
  intros size mem.
  setoid_rewrite interp_Mem_vis_eqit; cbn.
  rewrite bind_ret_l.
  rewrite interp_Mem_ret.
  apply tau_eutt.
Qed.

Lemma DSHAlloc_correct:
  ∀ (size : Int64.int) (op : DSHOperator),
    (∀ (s1 s2 : IRState) (σ : evalContext) (memH : memoryH) (nextblock bid_in bid_from : block_id)
        (bks : list (LLVMAst.block typ)) (g : global_env) (ρ : local_env) (memV : memoryV),
        bid_bound s1 nextblock
        → GenIR_Rel σ s1 bid_in (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in))))
        → Gamma_safe σ s1 s2
        → @no_failure E_cfg (memoryH * ()) (interp_helix (denoteDSHOperator σ op) memH)
        → genIR op nextblock s1 ≡ inr (s2, (bid_in, bks))
        → eutt (succ_cfg (GenIR_Rel σ s2 nextblock)) (interp_helix (denoteDSHOperator σ op) memH)
                (interp_cfg (denote_bks (convert_typ [] bks) (bid_from, bid_in)) g ρ memV))
    → ∀ (s1 s2 : IRState) (σ : evalContext) (memH : memoryH) (nextblock bid_in bid_from : block_id)
        (bks : list (LLVMAst.block typ)) (g : global_env) (ρ : local_env) (memV : memoryV),
      bid_bound s1 nextblock
      → GenIR_Rel σ s1 bid_in (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in))))
      → Gamma_safe σ s1 s2
      → @no_failure E_cfg (memoryH * ()) (interp_helix (denoteDSHOperator σ (DSHAlloc size op)) memH)
      → genIR (DSHAlloc size op) nextblock s1 ≡ inr (s2, (bid_in, bks))
      → eutt (succ_cfg (GenIR_Rel σ s2 nextblock))
              (interp_helix (denoteDSHOperator σ (DSHAlloc size op)) memH)
              (interp_cfg (denote_bks (convert_typ [] bks) (bid_from, bid_in)) g ρ memV).
Proof.
  intros size op IHop s1 s2 σ memH nextblock bid_in bid_from bks g ρ memV NEXT PRE GAM NOFAIL GEN.
  cbn* in *.
  simp.
  cbn.
  clean_goal.
  hvred.

  Import ProofMode.

  rewrite interp_helix_MemAlloc.
  hred.
  rewrite interp_helix_MemSet.
  hred.
  unfold add_comments; cbn.
  unfold fmap, Fmap_block; cbn.
  hvred.

  rename Heqs0 into genIR_op.
  rename Heql1 into context_l0.

  destruct PRE as (state_inv & (from & branch_inv)).
  destruct state_inv.
  cbn* in *.
  inversion branch_inv. subst. clear branch_inv.

  (* Retrieving information from NOFAIL on denoting operator *)
  rewrite interp_helix_bind in NOFAIL.
  rewrite interp_helix_MemAlloc in NOFAIL.
  rewrite bind_ret_l in NOFAIL.
  rewrite interp_helix_bind in NOFAIL.
  rewrite interp_helix_MemSet in NOFAIL.
  rewrite bind_ret_l in NOFAIL.
  (* Retain info from both the prefix and bind of NOFAIL *)
  assert (NOFAIL_cont := NOFAIL).
  apply no_failure_helix_bind_prefix in NOFAIL.
  rename NOFAIL into NOFAIL_prefix.
  rewrite interp_helix_bind in NOFAIL_cont.

  (* Apply IH on generated IR op. *)
  eapply IHop in genIR_op; eauto; clear IHop; cycle 1.
  { (* GenIR_Rel *)
    red. split. cbn.
    split; cycle 1.
    - (* Well-formedness *)
      unfold WF_IRState. cbn. red. intros. destruct n.

      (* Pointer size variable *)
      cbn in *.
      exists (ID_Local (Name
          (append (String (Ascii.Ascii true false false false false true true false) EmptyString)
                  (string_of_nat (local_count s1))))).
      inversion H; subst. cbn. reflexivity.

      (* Original σ *)
      cbn in *.
      eapply WF. auto.

    - (* Memory inv *)
      Opaque memory_lookup.
      cbn. intros. destruct n.

      (* Pointer size variable *)
      cbn in *. inversion H; inversion H0; subst; clear H H0.
      (* Need to make sure that the memory is intialized properly, from NOFAIL_prefix *)
      (* eexists. eexists. split; [| split ]. *) admit. admit.
    - cbn. exists from. reflexivity.
  }
  {
    (* Gamma_safe *) admit.
  }

  (* Post condition weakening *)
  eapply eutt_Proper_mono.
  Unshelve.
  6 : exact (succ_cfg (GenIR_Rel (DSHPtrVal (memory_next_key mH) size :: σ) i nextblock)).
  (* TODO: Generalize this weakening relation in extending context *)
  {
    repeat intro. red. red. red in H. red in H. destruct x; try contradiction.
    split. red. destruct p0. destruct y. destruct p0. destruct p0.
    destruct H. destruct H. split.
    - cbn in MINV0.
      cbn. intros. eapply MINV0.
      Unshelve. 3 : exact (S n). cbn. auto. rewrite context_l0. cbn. auto.
    - unfold WF_IRState in *. cbn. rewrite context_l0 in WF0.
      unfold evalContext_typechecks in *. intros. 
      specialize (WF0 v (S n)). cbn in WF0. apply WF0 in H.
      apply H.
    - destruct H. apply H0.
  }

  hvred.

  (* Useful lemmas about rcompose. TODO: Move? *)
  Lemma rcompose_eq_r :
    forall A B (R: relationH A B), eq_rel (R) (rcompose R (@Logic.eq B)).
  Proof.
    repeat intro. red. split; repeat intro; auto. econstructor.
    apply H. reflexivity.
    inversion H. subst. auto.
  Qed.

  Lemma rcompose_eq_l :
    forall A B (R: relationH A B), eq_rel (R) (rcompose (@Logic.eq A) R).
  Proof.
    repeat intro. red. split; repeat intro; auto. econstructor.
    reflexivity. apply H.
    inversion H. subst. auto.
  Qed.

  setoid_rewrite rcompose_eq_r.
  eapply eqit_trans.
  eapply eutt_clo_bind_returns. apply genIR_op.
  intros [ [memH t ] | ] (? & ? & ? & ?) [] ret1 ret2.
  rewrite interp_helix_MemFree. cbn in *.
  Unshelve.
  6 : {
    intros (? & ? & ? & ?).
    refine (Ret _). red. eauto. } cbn.
  apply eqit_Ret. cbn. split. split.
  destruct H.
  cbn in *. intros.

  eapply MINV0 in H1. cbn in *.
  Unshelve.
  destruct v; eauto.

  intros.
  (* Next step: using eutt_clo_bind_returns (or something similar.. ) apply genIR_op *)

  (* apply genIR_op. rewrite genIR_op.  *)


  (* Handle the Vellvm side, starting with a jump to the appropriate block *)
  (* vjmp. *)
  (* rewrite find_block_eq; reflexivity. *)
  (* cbn. *)
  (* vred. *)
  (* vred. *)
  (* vred. *)
  (* edestruct denote_instr_alloca_exists as (mV' & addr & Alloc & EQAlloc); *)
  (*   [| rewrite EQAlloc; clear EQAlloc]. *)
  (* red; easy. *)
  (* vred. *)
  (* vred. *)
  (* vjmp. *)
  (* no_repeat assumption *)
  (* rename b into target. *)
  (* vjmp. *)
  (* { *)
  (*   rewrite find_block_ineq. *)

  (*   apply find_block_tail_wf. *)
  (*   admit. *)
Admitted.
