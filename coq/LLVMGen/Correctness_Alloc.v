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

Require Import Helix.LLVMGen.Freshness.
Require Import Helix.LLVMGen.LidBound.

Set Nested Proofs Allowed.

Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

Set Implicit Arguments.
Set Strict Implicit.

Global Opaque resolve_PVar.


From Paco Require Import paco.
From ITree Require Import Basics.HeterogeneousRelations.

(* TODO: Move to bidbound *)

Lemma bid_bound_between_sep :
  ∀ (bid : block_id) s1 s2 s3,
    bid_bound_between s1 s2 bid → ¬ (bid_bound_between s2 s3 bid).
Proof.
  intros. cbn in H. red in H.
  intro.
  assert (((bid ≡ bid) -> False) -> False). auto. apply H1. clear H1.
  eapply bid_bound_fresh; eauto.
  destruct H as (? & ? & ? & ? & ? & ? & ?).
  red. red. exists x. exists x0, x1. split; eauto.
Qed.

Lemma not_bid_bound_between :
  forall bid s1 s2, bid_bound s1 bid -> not (bid_bound_between s1 s2 bid).
Proof.
  repeat intro.
  assert (((bid ≡ bid) -> False) -> False). auto. apply H1. clear H1.
  eapply bid_bound_fresh; eauto.
Qed.

Lemma newLocalVar_block_count :
  ∀ (s1 s2 : IRState) bid p x,
    newLocalVar p x s1 ≡ inr (s2, bid) →
    block_count s1 ≡ block_count s2.
Proof.
  intros s1 s2 bid * H.
  Transparent newLocalVar.
  unfold newLocalVar in H.
  cbn in H.
  simp.
  destruct s1; cbn; auto.
  Opaque newLocalVar.
Qed.

Lemma bid_bound_newLocalVar_mono :
  forall s1 s2 bid bid' p x,
    bid_bound s1 bid ->
    newLocalVar p x s1 ≡ inr (s2, bid') ->
    bid_bound s2 bid.
Proof.
  intros s1 s2 bid bid' * BOUND INC.
  destruct BOUND as (n1 & s1' & s1'' & N_S1 & COUNT_S1 & GEN_bid).
  unfold bid_bound.
  exists n1. exists s1'. exists s1''.
  intuition.
  apply newLocalVar_block_count in INC.
  lia.
Qed.

Lemma bid_bound_incBlock_neq:
  forall i i' bid bid',
  incBlock i ≡ inr (i', bid) ->
  bid_bound i bid' ->
  bid ≢ bid'.
Proof.
  intros.
  destruct (rel_dec_p bid bid'); auto.
  subst; exfalso.
  cbn in H; inv H.
  destruct H0 as (? & ? & ? & ? & ? & ?).
  cbn in *.
  inv H1.
  apply valid_prefix_string_of_nat_forward in H4 as [? ?]; subst; cbn in *; auto.
  lia.
Qed.

Lemma get_logical_block_of_add_to_frame :
  forall m k x, get_logical_block (add_to_frame m k) x ≡ get_logical_block m x.
Proof.
  intros. destruct m. cbn. destruct m.
  destruct f; unfold get_logical_block; cbn; reflexivity.
Qed.

Lemma get_logical_block_of_add_logical_frame_ineq :
  forall x m k mv, m ≢ x ->
              get_logical_block (add_logical_block m k mv) x ≡ get_logical_block mv x.
Proof.
  intros.
  cbn in *.
  unfold get_logical_block, get_logical_block_mem in *.
  unfold add_logical_block. destruct mv. cbn.
  unfold add_logical_block_mem. destruct m0.
  Opaque lookup. Opaque Mem.add.
  cbn in *.
  rewrite lookup_add_ineq; auto.
Qed.

Lemma memory_invariant_Ptr:
  ∀ (memH : memoryH) (σ : evalContext) (size : Int64.int) (i0 : IRState) k
  (mH : config_helix) (mV : memoryV) (l1 : local_env) (g1 : global_env),
      memory_invariant (DSHPtrVal k size :: σ) i0 mH (mV, (l1, g1))
      → memory_invariant (DSHPtrVal k size :: σ) i0 (memory_remove mH k)
                          (mV, (l1, g1)).
Proof.
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

  Opaque incBlockNamed.
  Opaque incVoid.
  Opaque incLocal.
  Opaque newLocalVar.

  cbn* in *.
  simp.

  rename i into s2.
  rename b into op_entry.
  rename l into bk_op.

  cbn* in *; simp. clean_goal.

  assert (bid_in ≢ op_entry). {
    clean_goal.
    clear -Heqs NEXT GAM Heqs0 Heqs1 Heqs2 Heql1.
    Transparent newLocalVar. cbn in *. simp.

    apply bid_bound_genIR_entry in Heqs1. red in GAM.
    clear GAM. clear NEXT.
    eapply bid_bound_incVoid_mono in Heqs1; eauto.

    clear -Heqs2 Heqs1.
    eapply bid_bound_incBlock_neq; eauto.
  }

  assert (nextblock ≢ bid_in). {
    (* TODO: pull this out into automation *)
    eapply bid_bound_fresh; eauto.
    eapply bid_bound_bound_between; eauto.

    unfold incBlock in *.
    match goal with
    | H: incBlockNamed ?msg ?s1 ≡ inr (_, ?bid) |-
      bid_bound ?s2 bid_in =>
      idtac H
    end.
    eapply bid_bound_incBlockNamed; eauto; reflexivity.
    solve_not_bid_bound.
    block_count_replace. rewrite <- Heqs in *.
    Transparent newLocalVar. cbn in *. simp. cbn in *. lia.
    reflexivity.
  }

  assert (forall m, ρ ⊑ alist_add r m ρ). admit.

  Opaque newLocalVar.

  cbn* in *; simp.

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

  rename Heqs1 into genIR_op.
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
    Transparent newLocalVar. cbn in *. simp. cbn in *.
    solve_bid_bound. auto.
  }

  Opaque newLocalVar.

  rename genIR_op into wf.

  (* Stepping Vellvm side *)
  vjmp.
  vred. vred. vred. vred.

  edestruct denote_instr_alloca_exists as (? & ? & EQ_alloca); eauto; cycle 1.

  destruct EQ_alloca as (? & EQ_alloca). rewrite EQ_alloca. clear EQ_alloca.
  vred. vred.
  2 : { intros VT ; inversion VT. }

  assert (genIR_op := genIR_op').

  rename H into alloc.
  Opaque allocate.
  rename x into memV_allocated.
  rename x0 into allocated_ptr_addr.
  clear branch_inv.
  clear NOFAIL_cont. (* Re-check that this isn't necessary later in the proof*)

  eapply genIR_Context in genIR_op'. cbn in *.
  inversion genIR_op'; subst; clear genIR_op'.

  rewrite (@list_cons_app _ _ (convert_typ [] bk_op)).

  rewrite denote_bks_app_no_edges; cycle 1.
  {
    (* op_blk_id is not in first part of computation. *)
    cbn.
    destruct GEN_IR.
    rewrite find_block_ineq. apply find_block_nil. cbn.
    eauto.
  }
  {
    assert (genIR_op' := genIR_op)
.
    unfold no_reentrance.
    eapply outputs_bound_between in genIR_op.
    clear -NEXT Heqs2 Heqs genIR_op genIR_op' Heqs0.

    cbn.
    eapply Forall_disjoint. eassumption.

    Unshelve.
    3 : refine (fun bid : block_id => bid_bound_between i0 i2 bid).
    big_solve.

    clear genIR_op. clean_goal.
    intros. cbn in *. destruct H.
    eapply bid_bound_between_sep. eapply H.

    subst.
    eapply not_bid_bound_between; auto.
    solve_bid_bound; auto.

    eapply bid_bound_newLocalVar_mono; eauto.
  }

  setoid_rewrite <- bind_ret_r at 5.

  (* Post condition weakening *)
  eapply eqit_mon with
      (RR := succ_cfg (GenIR_Rel (DSHPtrVal (memory_next_key memH) size :: σ)
                                 i0 nextblock)); auto.
  {
    (* Re-establish invariant *)
    intros.
    repeat red in PR. destruct x0.
    Transparent incBlockNamed.
    Transparent incVoid.
    Transparent incLocal.
    Transparent newLocalVar.
    cbn* in *. simp. cbn* in *.
    eapply genIR_Rel_extend; eauto. contradiction.
  }

  Opaque incBlockNamed.
  Opaque incVoid.
  Opaque incLocal.
  Opaque newLocalVar.

  clean_goal.

  eapply eutt_clo_bind_returns.
  {
    (* Prefix *)
    eapply IHop; try exact genIR_op; eauto.
    {
      (* TODO: Add newLocalVar to solve_bid_bound.
          Need Ltac based on Typeclass definition?  *)
      Transparent newLocalVar.
      cbn* in *. simp. cbn* in *.
      solve_bid_bound. auto.
      Opaque newLocalVar.
    }

    {
      (* Re-establish invariant *)
      clear -genIR_op context_l0 GEN_IR Heqs Heqs0 Heqs2 H1 H2.
      split; red; cbn; repeat break_let; subst.
      cbn in *. destruct GEN_IR. cbn in H.

      inversion H. subst.
      split.
      - (* Import ProofMode. *)
        clean_goal. clear WF H0. clean_goal.
        assert (Γ s2 ≡ (ID_Local (Name ("a" @@ string_of_nat (local_count s1))),
            TYPE_Pointer (TYPE_Array (Int64.intval size) TYPE_Double)) :: Γ s1). {
          Transparent incBlockNamed.
          Transparent incVoid.
          Transparent incLocal.
          Transparent newLocalVar.
          cbn* in *. simp. cbn* in *. reflexivity.
          Opaque incBlockNamed.
          Opaque incVoid.
          Opaque incLocal.
          Opaque newLocalVar.
        }
        clear Heqs Heqs2 context_l0. clear -Heqs0 MINV genIR_op H H0 H1 H2.
        rename H2 into alloc. rename Heqs0 into locvar.
        rename H0 into gamma_ext. rename H1 into rho_ext.
        clean_goal.
        (* Now we have a clean context! *)

        (* Getting info out of allocate. *)
        assert (alloc' := alloc).
        apply allocate_inv in alloc'.
        destruct alloc' as (? & ? & ?).
        rewrite H1, H2. clear H1 H2.
        rename H0 into nv.

        Opaque next_logical_key.
        cbn. intros. rewrite gamma_ext in H1.
        destruct n.

        + (* "Base case" on the allocated pointer *)
          cbn in *. inversion H; inversion H0; subst. clear H H0. cbn.
          Transparent newLocalVar. cbn in locvar. simp.
          eexists mem_empty. eexists.
          split; [ | split].
          * rewrite Memory.NM.Raw.Proofs.add_find.
            Import Memory.NM.Raw.Proofs.
            pose proof L.MX.elim_compare_eq.
            edestruct H. reflexivity. rewrite H0.
            reflexivity. apply Memory.NM.is_bst.
          * assert (Name ("a" @@ string_of_nat (local_count s1))
                         ?[ Logic.eq ] Name ("a" @@ string_of_nat (local_count s1))). {
              apply rel_dec_eq_true. typeclasses eauto. reflexivity.
            } cbn. cbn in H. rewrite H. reflexivity.
          * intros. inversion H.

        + (* Rest of memory should be the same *)
          cbn* in *. simp.
          specialize (MINV _ _ _ _ H0 H1). cbn* in *.

          destruct v; clear -MINV rho_ext.
          * eapply in_local_or_global_scalar_ext_local in MINV; auto.
            unfold in_local_or_global_scalar in *.

            destruct x; intuition; eauto.
            {
              edestruct MINV as (? & ? & ? & ? & ?). clear MINV.
              eexists. eexists. split; eauto. split; eauto.
              subst. clean_goal.
              unfold read in H1. unfold read.

              (* [add_to_frame] adds an id that should be freed after the function returns. *)
              rewrite get_logical_block_of_add_to_frame. cbn.
              rewrite get_logical_block_of_add_logical_frame_ineq; auto.
              assert (forall id x, g @ id ≡ Some (DVALUE_Addr x) -> next_logical_key memV ≢ fst x). admit.
              eapply H; eauto.
            }
          * eapply in_local_or_global_scalar_ext_local in MINV; auto.
            unfold in_local_or_global_scalar in *.

            destruct x; intuition; eauto.
            {
              edestruct MINV as (? & ? & ? & ? & ?). clear MINV.
              eexists. eexists. split; eauto. split; eauto.
              subst. clean_goal.
              unfold read in H1. unfold read.

              (* [add_to_frame] adds an id that should be freed after the function returns. *)
              rewrite get_logical_block_of_add_to_frame. cbn.
              rewrite get_logical_block_of_add_logical_frame_ineq; auto.
              assert (forall id x, g @ id ≡ Some (DVALUE_Addr x) -> next_logical_key memV ≢ fst x). admit.
              eapply H; eauto.
            }
          * edestruct MINV as (bk_helix & ptr_llvm & mem_lookup & in_l & gac). clear MINV.
            eexists. eexists. split; [ | split]; cycle 1.
            -- eapply in_local_or_global_addr_ext_local. apply in_l. auto.
            -- intros. unfold get_array_cell. destruct ptr_llvm.
               rewrite get_logical_block_of_add_to_frame.
               rewrite get_logical_block_of_add_logical_frame_ineq; auto.
               apply gac. eauto.
               assert (next_logical_key memV ≢ z). admit.
               auto.
            -- rewrite add_find. 2 : apply Memory.NM.is_bst.
               assert (a ≢ memory_next_key memH). admit.
               pose proof L.MX.elim_compare_eq.
               destruct (OrderedTypeEx.Nat_as_OT.compare a (memory_next_key memH)); auto.
               inversion e. contradiction.
      - unfold WF_IRState in *. cbn.

        Transparent incBlockNamed.
        Transparent incVoid.
        Transparent incLocal.
        Transparent newLocalVar.
        cbn* in *. simp. cbn.
        unfold evalContext_typechecks in *. intros.
        destruct n.
        exists (ID_Local (Name ("a" @@ string_of_nat (local_count s1)))).
        cbn. cbn in *. inversion H3. subst. cbn.
        reflexivity.
        cbn in H.
        specialize (WF v n). cbn in WF.
        cbn in *.
        apply WF in H3.
        apply H3.
      - destruct GEN_IR. destruct H0. inversion H0. subst.
        eexists. reflexivity.
    }
    eapply Gamma_safe_shrink; eauto; cycle 1.
    red. cbn. lia.
    Unshelve.
    red. cbn. apply genIR_local_count in genIR_op. cbn in *. eauto.

    {
      (* Gamma_safe *)
      cbn* in *. simp. cbn* in *.
      unfold Gamma_safe in *. intros. intro.
      inversion H4; subst. cbn in *.
      admit.
    }
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
    destruct H.
    split.
    - clean_goal.
      clear WF H0 ret1 ret2 context_l0.
      clean_goal.
      apply memory_invariant_Ptr; eauto. (* TODO Check again that this is correct *)
    - assumption.
    - destruct UU. destruct H0. inversion H0. subst.
      eexists. reflexivity.
  }

  Unshelve.
  all : eauto. exact nat. exact "".
Admitted.
