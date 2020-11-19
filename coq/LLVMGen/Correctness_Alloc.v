Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.
(* Require Import Helix.LLVMGen.Correctness_MExpr. *)
(* Require Import Helix.LLVMGen.Correctness_AExpr. *)
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

Import Memory.NM.Raw.
Lemma remove_find : forall e m x y,
    bst m ->
    find (elt := e) y (remove x m) ≡
      match OrderedTypeEx.Nat_as_OT.compare y x with
        OrderedType.EQ _ => find y (remove x m) | _ => find y m end.
Proof.
intros.
assert (~OrderedTypeEx.Nat_as_OT.eq x y -> find (elt := e) y (remove x m) ≡ find y m).
intros. rewrite Proofs.find_mapsto_equiv; auto.
(*  split; eauto using Proofs.add_2, Proofs.add_3. *)
(* destruct X.compare; try (apply H0; order). *)
(* (* auto using find_1, add_1 with ordered_type. *) *)
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


Lemma no_dshptr_aliasing_cons :
  forall (memH : memoryH) (σ : evalContext) (size : Int64.int),
    no_dshptr_aliasing (DSHPtrVal (memory_next_key memH) size :: σ) ->
    no_dshptr_aliasing σ.
Proof.
  intros * st_no_dshptr_aliasing. repeat intro.
  specialize (st_no_dshptr_aliasing (S n) (S n')). cbn in *.
  specialize (st_no_dshptr_aliasing _ _ _ H H0).
  inversion st_no_dshptr_aliasing. subst. reflexivity.
Qed.

Lemma typ_to_dtyp_P : forall s i, typ_to_dtyp s (TYPE_Pointer i) ≡ DTYPE_Pointer.
Proof.
  intros; rewrite typ_to_dtyp_equation; reflexivity.
Qed.



Lemma newLocalVar_lid_bound_between :
  forall size s1 s2 r str,
    is_correct_prefix str ->
    newLocalVar (TYPE_Pointer (TYPE_Array (Int64.intval size) TYPE_Double)) str s1 ≡ inr (s2, r) ->
    lid_bound_between s1 s2 r.
Proof.
  Transparent newLocalVar.
  cbn. intros * E H. inversion H. subst. clear H.
  unfold lid_bound_between, state_bound_between.
  eexists. eexists. eexists.
  split; try split; try split; eauto.
  2 : cbn; reflexivity. auto.
  Opaque newLocalVar.
Qed.

Lemma DSHAlloc_correct:
  ∀ (size : Int64.int) (op : DSHOperator),
    (∀ (s1 s2 : IRState) (σ : evalContext) (memH : memoryH) (nextblock bid_in bid_from : block_id) 
        (bks : list (LLVMAst.block typ)) (g : global_env) (ρ : local_env) (memV : memoryV),
        genIR op nextblock s1 ≡ inr (s2, (bid_in, bks))
        → bid_bound s1 nextblock
        → state_invariant σ s1 memH (memV, (ρ, g))
        → Gamma_safe σ s1 s2
        → @no_failure E_cfg (memoryH * ()) (interp_helix (denoteDSHOperator σ op) memH)
        → eutt (succ_cfg (genIR_post σ s1 s2 nextblock ρ)) (interp_helix (denoteDSHOperator σ op) memH)
                (interp_cfg (denote_bks (convert_typ [] bks) (bid_from, bid_in)) g ρ memV))
    → ∀ (s1 s2 : IRState) (σ : evalContext) (memH : memoryH) (nextblock bid_in bid_from : block_id) 
        (bks : list (LLVMAst.block typ)) (g : global_env) (ρ : local_env) (memV : memoryV),
      genIR (DSHAlloc size op) nextblock s1 ≡ inr (s2, (bid_in, bks))
      → bid_bound s1 nextblock
      → state_invariant σ s1 memH (memV, (ρ, g))
      → Gamma_safe σ s1 s2
      → @no_failure E_cfg (memoryH * ()) (interp_helix (denoteDSHOperator σ (DSHAlloc size op)) memH)
      → eutt (succ_cfg (genIR_post σ s1 s2 nextblock ρ))
              (interp_helix (denoteDSHOperator σ (DSHAlloc size op)) memH)
              (interp_cfg (denote_bks (convert_typ [] bks) (bid_from, bid_in)) g ρ memV).
Proof.
  intros size op IHop s1 s2 σ memH nextblock bid_in bid_from bks g ρ memV GEN NEXT PRE GAM NOFAIL.

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
  cbn* in *.
  subst. cbn.

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
    assert (genIR_op' := genIR_op).
    assert (genIR_op'' := genIR_op).

    unfold no_reentrance.
    eapply outputs_bound_between in genIR_op.
    clear -NEXT Heqs2 Heqs genIR_op genIR_op' genIR_op'' Heqs0.

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


  Opaque incBlockNamed.
  Opaque incVoid.
  Opaque incLocal.
  Opaque newLocalVar.

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
      assert (genIR_op' := genIR_op).
      apply genIR_Context in genIR_op.
      rename Heqs0 into new_local_var.

      rename p into FOO.
      Transparent incBlockNamed.
      Transparent incVoid.
      Transparent incLocal.
      Transparent newLocalVar.
      cbn* in *. simp. cbn in *.
      rewrite context_l0 in genIR_op. inversion genIR_op; subst.

      eapply state_invariant_enter_scope_DSHPtr; eauto.
      - destruct GEN_IR.
        assert (not (in_Gamma σ s1 (Name ("a" @@ string_of_nat (local_count s1))))). {
          eapply GAM.

          unfold lid_bound_between, state_bound_between.
          eexists. eexists. eexists.
          apply genIR_local_count in genIR_op'. cbn in *.
          split; try split; try split; eauto. reflexivity.
        }
        intro. apply H.
        eapply In_nth_error in H3; destruct H3.
        destruct (nth_error (Γ s1) x) eqn: nth_destruct.
        2 : {
          eapply map_nth_error_none in nth_destruct.
          rewrite nth_destruct in H3.
          inversion H3.
        }

        destruct p.

        red in st_no_id_aliasing.
        specialize (st_no_id_aliasing _ _ _ _ _ nth_destruct nth_destruct).
        destruct st_no_id_aliasing as (? & ? & X).

        esplit.
        2 : {
          rewrite nth_destruct.
          eapply map_nth_error in nth_destruct.
          rewrite nth_destruct in H3. cbn in H3; inversion H3; subst.
          reflexivity.
        }
        2 : auto. exact X.
      - (* ∀ s : Int64.int, ¬ List.In (DSHPtrVal (memory_next_key memH) s) σ *)
        intros. (* Use fact about memory_next_key *)
        pose proof @mem_block_exists_memory_next_key.
        destruct PRE.
        red in st_id_allocated.
        specialize (H memH).
        intro. apply H.
        apply In_nth_error in H3. destruct H3.
        eapply st_id_allocated. apply H3.
      - destruct PRE. clear -st_no_llvm_ptr_aliasing.
        eauto.
    }

    Transparent incBlockNamed.
    Transparent incVoid.
    Transparent incLocal.
    Transparent newLocalVar.
    cbn* in *. simp. cbn* in *. rewrite H2.

    apply genIR_Context in genIR_op. cbn in *. rewrite context_l0 in *.
    inversion genIR_op. subst.
    clear -GAM context_l0.

    eapply Gamma_safe_Context_extend; eauto; cbn; try lia; try reflexivity.
    intros.

    eapply lid_bound_fresh; eauto.
    red. unfold state_bound. eexists. eexists. eexists.
    split; try split; try split; try split.
    cbn. eauto.
  }

  (* Continuation *)
  intros [ [memH' t ] | ] (? & ? & ? & ?) UU ret1 ret2.
  rewrite interp_helix_MemFree.
  apply eutt_Ret. cbn.
  2 : try_abs.

  rename ρ into RHO.
  rename l into LOCAL_ENV. 
  destruct t. clear ret1 ret2.
  cbn in *. simp. cbn in *.
  (* Establish something between i0 and s1 *)
  {
    assert (genIR_op'' := genIR_op).
    eapply genIR_Context in genIR_op. rewrite context_l0 in genIR_op.
    cbn in genIR_op. inversion genIR_op; subst.
    unfold genIR_post in UU. red in UU. unfold succ_rel_l in UU.
    try inversion UU.
    destruct UU as (state_PRE & branch_PRE & local_modif_PRE).

    split; red; cbn; repeat break_let; subst.
    cbn in *.
    destruct state_PRE. cbn in mem_is_inv.
    split.
    - cbn. intros. rewrite context_l0 in mem_is_inv.
      cbn in *. specialize (mem_is_inv (S n)). cbn in *.
      specialize (mem_is_inv _ _ _ H4 H5).
      destruct v; eauto.
      destruct PRE.
      clear -mem_is_inv st_id_allocated st_id_allocated0 H4 H5.

      destruct mem_is_inv as (? & ? & ? & ? & ? & ? & ? & ?).
      eexists. eexists. eexists.
      split; try split; try split; try split; eauto.
      rewrite remove_find.
      2 : apply Memory.NM.is_bst.

      unfold id_allocated in *.
      assert (a ≢ (memory_next_key memH)). {
        pose proof mem_block_exists_memory_next_key.
        intro. eapply H6. subst.
        eapply st_id_allocated0. apply H4.
      }
      break_match. auto. 2 : auto.
      exfalso. apply H6. rewrite e. reflexivity.
    - unfold WF_IRState in *. cbn. rewrite context_l0 in IRState_is_WF.
      unfold evalContext_typechecks in *. intros.
      specialize (IRState_is_WF v (S n)). cbn in IRState_is_WF. apply IRState_is_WF in H4.
      apply H4.
    - red. cbn in *. intros. red in st_no_id_aliasing.
      rewrite context_l0 in st_no_id_aliasing. specialize (st_no_id_aliasing (S n) (S n')).
      cbn in *. specialize (st_no_id_aliasing _ _ _ H4 H5). destruct st_no_id_aliasing.
      inv H1. split; auto.
    - unfold no_dshptr_aliasing in *. intros.
      specialize (st_no_dshptr_aliasing (S n) (S n')).
      cbn in st_no_dshptr_aliasing.
      specialize (st_no_dshptr_aliasing _ _ _ H4 H5).
      inv st_no_dshptr_aliasing. reflexivity.
    - unfold no_llvm_ptr_aliasing_cfg, no_llvm_ptr_aliasing in *.
      intros. cbn* in *.
      unfold no_llvm_ptr_aliasing in *.
      rewrite context_l0 in st_no_llvm_ptr_aliasing.
      intros. specialize (st_no_llvm_ptr_aliasing id1 ptrv1 id2 ptrv2 (S n1) (S n2)).
      cbn in *. specialize (st_no_llvm_ptr_aliasing _ _ _ _ H4 H5 H6 H7).
      apply st_no_llvm_ptr_aliasing; auto.
    - (* Get more information about the new memH. *)
      destruct GEN_IR.
      unfold id_allocated in *.
      intros.

      specialize (st_id_allocated (S n)). cbn in *.
      specialize (st_id_allocated _ _ H4).
      clear -st_id_allocated st_id_allocated0 H4.
      specialize (st_id_allocated0 _ _ _ H4).
      pose proof mem_block_exists_memory_next_key.

      rewrite <- mem_block_exists_memory_remove_neq. auto.
      intro. eapply H. subst. eauto.

    - split. destruct H3. cbn in H3.
      { apply H3. }
      destruct H3. cbn in *.

      pose proof local_scope_modif_refl.
      apply genIR_local_count in genIR_op''.
      cbn in *.

      eapply local_scope_modif_trans. 4 : eapply local_scope_modif_trans.
      6 : eauto.
      red; cbn; lia. red; cbn; lia.
      2 : red; cbn; lia. 2 : red; cbn; lia. 2 : apply local_scope_modif_refl.

      apply local_scope_modif_add.
      eapply newLocalVar_lid_bound_between.
      2 : cbn; reflexivity. reflexivity.
  }

  Unshelve.
  all : eauto. exact nat. exact "".
Qed.

