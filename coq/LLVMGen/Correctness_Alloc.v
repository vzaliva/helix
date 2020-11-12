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


From Paco Require Import paco.
From ITree Require Import Basics.HeterogeneousRelations.


Lemma not_bid_bound_genIR_entry :
  forall op s1 s2 nextblock bid bks σ,
    Gamma_safe σ s1 s2 ->
    genIR op nextblock s1 ≡ inr (s2, (bid, bks)) ->
    not (bid_bound s1 bid).
Proof.
  induction op;
    intros s1 s2 nextblock b bks GEN.
Admitted.

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


(* Import ProofMode.  *)

Lemma genIR_Rel_extend:
  ∀ (p : ident * typ) (l : list (LLVMAst.block typ)) (b : block_id) 
    (l0 : list (ident * typ)) (i : IRState) (nextblock branch_to : block_id) 
    (memH : memoryH) (σ : evalContext) (s1 : IRState) (op : DSHOperator) 
    (size : Int64.int) x',
    Γ i ≡ p :: l0
    → genIR op nextblock
      {|
        block_count := block_count s1;
        local_count := S (local_count s1);
        void_count := void_count s1;
        Γ := (ID_Local (Name ("a" @@ string_of_nat (local_count s1))),
              TYPE_Pointer (TYPE_Array (Int64.intval size) TYPE_Double)) :: Γ s1 |} ≡ inr (i, (b, l))
    → ∀ x0 x1 i',
        i' ≡ {| block_count := S (block_count i);
                local_count := local_count i;
                void_count := S (void_count i);
                Γ := l0 |}
        -> GenIR_Rel (x' :: σ) i branch_to x0 x1
        → GenIR_Rel σ i' branch_to x0 x1.
Proof.
  intros p l b l0 i nextblock memH σ s1 op size * context_l0 genIR_op.
  clear -genIR_op context_l0.

  intros * PRE.
  eapply genIR_Context in genIR_op. rewrite context_l0 in genIR_op.
  cbn in genIR_op. inversion genIR_op; subst. intros PRE.
  unfold GenIR_Rel in PRE. red in PRE. unfold succ_rel_l in PRE.
  destruct x0; try inversion PRE.

  rename H into state_PRE. rename H0 into branch_PRE. clear PRE.
  split; red; cbn; repeat break_let; subst.
  cbn in *.
  destruct state_PRE. cbn in MINV.
  split.
  - cbn. intros. eapply (MINV (S n)).
    cbn. auto. rewrite context_l0. cbn. auto.
  - unfold WF_IRState in *. cbn. rewrite context_l0 in WF.
    unfold evalContext_typechecks in *. intros.
    specialize (WF v (S n)). cbn in WF. apply WF in H.
    apply H.
  - destruct branch_PRE. exists x. apply H.
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

  (* Opaque incBlockNamed. *)
  (* Opaque incVoid. *)
  (* Opaque incLocal. *)
  (* Opaque newLocalVar. *)

  cbn* in *.
  simp.

  cbn.
  clean_goal.
  hvred.

  rewrite interp_helix_MemAlloc.
  hred.
  rewrite interp_helix_MemSet.
  hred.
  unfold add_comments; cbn.
  unfold fmap, Fmap_block; cbn.
  hvred.

  rename Heqs0 into genIR_op.
  rename Heql1 into context_l0.

  assert (GEN_IR := PRE).
  destruct PRE as (state_inv & (from & branch_inv)).
  cbn* in *.
  inversion branch_inv. subst. cbn.

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

  assert (genIR_op' := genIR_op).
  apply generates_wf_cfgs in genIR_op; cycle 1.
  {
    Transparent newLocalVar. cbn* in *. simp.
    solve_bid_bound. Opaque newLocalVar. auto.
  }

  (* Stepping Vellvm side *)
  vjmp.
  vred. vred. vred. vred.

  edestruct denote_instr_alloca_exists as (? & ? & EQ_alloca); eauto; cycle 1.

  destruct EQ_alloca as (? & EQ_alloca). rewrite EQ_alloca. clear EQ_alloca.
  vred. vred.
  2 : { intros VT ; inversion VT. }

  clear branch_inv.
  clear NOFAIL_cont. (* Re-check that this isn't necessary later in the proof*)
  rename genIR_op into wf.
  rename i into s2.
  rename b into op_entry.
  rename l into bk_op.
  rename l0 into s2_Gamma.
  rename H into alloc.
  Opaque allocate.
  rename x into memV_allocated.
  rename x0 into allocated_ptr_addr.


  assert (genIR_op := genIR_op').

  eapply genIR_Context in genIR_op'. cbn in *.
  inversion genIR_op'; subst; clear genIR_op'.

  rewrite (@list_cons_app _ _ (convert_typ [] bk_op)).

  rewrite denote_bks_app_no_edges; cycle 1.
  {
    (* op_blk_id is not in first part of computation. *)
    cbn.
    destruct GEN_IR. destruct H1. inversion H1. subst.
    assert (genIR_op' := genIR_op).
    apply bid_bound_genIR_entry in genIR_op.
    rewrite find_block_ineq. apply find_block_nil. cbn.


    admit.
  }
  { admit. }

  setoid_rewrite <- bind_ret_r at 5.

  rewrite context_l0 in *. inversion H0; subst. clear H0.

  (* Post condition weakening *)
  eapply eqit_mon with
      (RR := succ_cfg (GenIR_Rel (DSHPtrVal (memory_next_key memH) size :: σ)
                                 s1 nextblock)); auto.
  {
    (* Re-establish invariant *)

    intros.
    repeat red in PR. destruct x0.
    eapply genIR_Rel_extend; eauto. (* Why doesn't this work anymore? *)
    2: contradiction.
    admit.
  }

  clean_goal.

  eapply eutt_clo_bind_returns.
  {
    (* Prefix *)
    eapply IHop; try exact genIR_op; eauto.
    {
      (* Re-establish invariant *)
      clear -genIR_op context_l0 GEN_IR.
      split; red; cbn; repeat break_let; subst.
      cbn in *. destruct GEN_IR. cbn in H.
      destruct H. cbn in MINV.
      split.
      - admit.
      - unfold WF_IRState in *. cbn.
        (* rewrite context_l0. *)
        unfold evalContext_typechecks in *. intros.
        destruct n.
        exists (ID_Local (Name ("a" @@ string_of_nat (local_count s1)))).
        cbn. cbn in H. inversion H. subst. cbn. reflexivity.
        cbn in H.
        specialize (WF v n). cbn in WF. apply WF in H.
        apply H.
      - destruct GEN_IR. destruct H0. inversion H0. subst.
        eexists. reflexivity.
    }
    admit.
  }

  (* Continuation *)
  intros [ [memH' t ] | ] (? & ? & ? & ?) UU ret1 ret2.
  rewrite interp_helix_MemFree.
  apply eutt_Ret. cbn.
  2 : try_abs.

  destruct t. cbn in *. clear -UU ret1 ret2 context_l0.
  {
    split; red; cbn; repeat break_let; subst.
    cbn in *. destruct UU. cbn in H.
    destruct H. cbn in MINV.
    split.
    - repeat intro.
      (* rewrite context_l0 in H1. cbn in *. *)
      destruct n. cbn in *. inversion H; inversion H1; subst.
      admit.
      cbn in *. rewrite context_l0 in MINV.
      specialize (MINV (S n)). cbn in *.
      (* eapply MINV in H1; eauto. *)
      destruct v; eauto. admit.
      (* destruct H1 as (? & ? & ? & ? & ?). *)
      (* eexists. eexists. split; [ | split]; eauto. *)
      (* rewrite <- H1. *)
      (* admit. *) admit. admit.
    - admit.
      (* assumption. *)
    - destruct UU. destruct H0. inversion H0. subst.
      eexists. reflexivity.
  }

  Unshelve.
  all : eauto. 2 : exact nat. 2 : exact "".
Admitted.
