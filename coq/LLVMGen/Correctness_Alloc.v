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

Lemma get_logical_block_of_add_to_frame :
  forall m k x, get_logical_block (add_to_frame m k) x ≡ get_logical_block m x.
Proof.
  intros. destruct m. cbn. destruct m.
  destruct f; unfold get_logical_block; cbn; reflexivity.
Qed.


Import Memory.NM.Raw.

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

(* Lemma memory_invariant_Ptr: *)
(*   ∀ (memH : memoryH) (σ : evalContext) (size : Int64.int) (i0 : IRState) k *)
(*   (mH : config_helix) (mV : memoryV) (l1 : local_env) (g1 : global_env), *)
(*     (* Γ s2 ≡ -> *) *)
(*     memory_invariant (DSHPtrVal k size :: σ) i0 mH (mV, (l1, g1)) *)
(*       → memory_invariant σ i0 (memory_remove mH k) (mV, (l1, g1)). *)
(* Proof. *)
(*   intros. cbn in *. *)
(*   intros. *)
(*   (* specialize (H _ _ _ _ H0 H1). *) *)
(*   (* destruct v; eauto. *) *)
(*   (* destruct H as (? & ? & ? & ? & ?). *) *)
(*   (* eexists. exists x1. split; eauto. *) *)
(*   (* rewrite remove_find. 2 : apply Memory.NM.is_bst. *) *)
(*   (* break_match; eauto. *) *)
(*   (* inversion e. subst. *) *)
(* Admitted. *)

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
    → ∀ x0 x1 i' a,
        i' ≡ {| block_count := S (block_count i);
                local_count := local_count i;
                void_count := S (void_count i);
                Γ := l0 |}
        -> genIR_post (x' :: σ) s1 i branch_to x0 x1 a
        → genIR_post σ s1 i' branch_to x0 x1 a.
Proof.
  intros p l b l0 i nextblock memH σ s1 op size * context_l0 genIR_op.
  clear -genIR_op context_l0.

  intros * PRE.
  eapply genIR_Context in genIR_op. rewrite context_l0 in genIR_op.
  cbn in genIR_op. inversion genIR_op; subst. intros PRE.
  unfold genIR_post in PRE. red in PRE. unfold succ_rel_l in PRE.
  try inversion PRE.

  rename H into state_PRE. rename H0 into branch_PRE. clear PRE.
  split; red; cbn; repeat break_let; subst.
  cbn in *.
  destruct state_PRE. cbn in mem_is_inv.
  split.
  - cbn. intros. rewrite context_l0 in mem_is_inv.
    cbn in *. specialize (mem_is_inv (S n)). cbn in *.
    specialize (mem_is_inv _ _ _ H H0).
  (*   destruct v; eauto. admit. *)
  (* - unfold WF_IRState in *. cbn. rewrite context_l0 in IRState_is_WF. *)
  (*   unfold evalContext_typechecks in *. intros. *)
  (*   specialize (IRState_is_WF v (S n)). cbn in IRState_is_WF. apply IRState_is_WF in H. *)
  (*   apply H. *)
  (* - admit. *)
  (* - admit. *)
  (* - admit. *)
  (* - admit. *)
Admitted.

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
      assert (genIR_op' := genIR_op).
      apply genIR_Context in genIR_op.
      rename Heqs0 into new_local_var.

      eapply state_invariant_enter_scope_DSHPtr; eauto.
      2 : apply memory_lookup_memory_set_eq.
      - cbn.
        Transparent incBlockNamed.
        Transparent incVoid.
        Transparent incLocal.
        Transparent newLocalVar.
        cbn* in *. simp.
        Unshelve. 4 : exact s1. cbn.
        3 : exact (ID_Local (Name ("a" @@ string_of_nat (local_count s1)))).
        cbn. reflexivity. exact allocated_ptr_addr.

        Opaque incBlockNamed.
        Opaque incVoid.
        Opaque incLocal.
        Opaque newLocalVar.

      - red. pose proof allocated_get_logical_block.
        Transparent allocate.
        Unshelve.
        Opaque add_logical_block. Opaque next_logical_key.
        cbn in H1. inversion H1. subst. clear H1.
        rewrite get_logical_block_of_add_to_frame. cbn.
        rewrite get_logical_block_of_add_logical_block.
        rewrite typ_to_dtyp_P. cbn in *.

        eexists. eexists. eexists. split. cbn. reflexivity.

        cbn.
          (* 8 <= Int64.intval size * 8 TODO: Calvin will make this change. *)
        admit.
      - Opaque alist_add. cbn.
        Transparent newLocalVar. cbn* in *. simp.
        rewrite alist_add_find_eq. reflexivity.
      - intros. destruct GEN_IR. cbn in *. inversion H.
      - eapply Gamma_safe_shrink in GAM.
        Unshelve. 3 : red; reflexivity. 4 : exact s2.
        2 : reflexivity. 
        2 : { (* TODO : extend solve_local_count *)
          Transparent newLocalVar.
          Transparent incBlock. Transparent incVoid.
          Transparent incBlockNamed.
          cbn* in *. simp. cbn* in *.
          red; cbn; solve_local_count_tac.
          apply genIR_local_count in genIR_op'. cbn in *. lia.
        } intro.

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

        assert (lid_bound_between s1 s2 r). {
          eapply newLocalVar_lid_bound_between.
          2 : cbn; rewrite new_local_var.
          auto. reflexivity. }
        assert (r ≡ (Name ("a" @@ string_of_nat (local_count s1)))). {
          Transparent newLocalVar.
          cbn* in *. inversion new_local_var. reflexivity.
        }
        subst.
        unfold lid_bound_between, state_bound_between in H3.
        destruct H3 as (? & ? & ? & ? & ? & ? & ?).
        cbn in *. inversion H6. simp. cbn* in *. clear H10.

        admit.
        (* List.In (ID_Local (Name ("a" @@ string_of_nat (local_count s1)))) (List.map fst (Γ s1)) → False *)
        (* admit. *)
      - (* ∀ s : Int64.int, ¬ List.In (DSHPtrVal (memory_next_key memH) s) σ *)

        admit.
      - intros. destruct GEN_IR. red in H4.
        (* fst allocated_ptr_addr ≢ fst ptrv' *)
        admit.
      - (* state_invariant σ s1 (memory_set memH (memory_next_key memH) mem_empty) *)
        (*   (memV_allocated, *)
        (*   (alist_add (Name ("a" @@ string_of_nat (local_count s1))) (UVALUE_Addr allocated_ptr_addr) ρ, g)) *)
        admit.
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

  destruct memH'.
  destruct t. cbn in *. simp. cbn in *.
  (* Establish something between i0 and s1 *)
  eapply genIR_local_count in genIR_op.
  cbn in genIR_op.
  clear -UU ret1 ret2 context_l0 H2 genIR_op.
  {
    split; red; cbn; repeat break_let; subst.
    cbn in *. destruct UU. cbn in H.
    destruct H.
    split.
    - clean_goal.
      clear H0 ret1 ret2.
      clean_goal.
      cbn in *. intros.
      specialize (mem_is_inv (S n)).
      rewrite context_l0 in H2. inversion H2. subst.
      rewrite context_l0 in mem_is_inv.
      cbn in *. specialize (mem_is_inv _ _ _ H H0).
      destruct v; try eapply mem_is_inv.
      destruct mem_is_inv as (? & ? & ? & ? & ? & ? & ? & ?).
      eexists. eexists.
      esplit; try split; try split; try split; try split; eauto.
      rewrite remove_find. 2 : eauto.
      destruct (OrderedTypeEx.Nat_as_OT.compare a (memory_next_key memH)); eauto.

      (* absurd *) (* From ptr aliasing *)
      unfold no_llvm_ptr_aliasing in *.
      unfold no_dshptr_aliasing in *.
    (* specialize (st_no_dshptr_aliasing (S n) (S n)). cbn in st_no_dshptr_aliasing. *)
    (* specialize  *)
     (* specialize (st_no_llvm_ptr_aliasing x _ x _ (S n) (S n) _ _ _ _ _ _ ). *)
      admit.
    - red in IRState_is_WF. red in IRState_is_WF. repeat intro.
      specialize (IRState_is_WF v (S n)). cbn in *.
      apply IRState_is_WF in H. destruct H. exists x.
      destruct (Γ i0). inversion H. inversion context_l0; subst. auto.
    - unfold no_id_aliasing in *.

      cbn in *. intros.
      rewrite context_l0 in st_no_id_aliasing.
      specialize (st_no_id_aliasing (S n) (S n') _ _ _ H H1).
      inversion st_no_id_aliasing; subst; auto.
    - clear -st_no_dshptr_aliasing.
      eapply no_dshptr_aliasing_cons; eauto.
    - cbn in *.
      unfold no_llvm_ptr_aliasing in *.
      rewrite context_l0 in st_no_llvm_ptr_aliasing.
      clear -st_no_llvm_ptr_aliasing.
      intros. specialize (st_no_llvm_ptr_aliasing id1 ptrv1 id2 ptrv2 (S n1) (S n2)).
      cbn in *. specialize (st_no_llvm_ptr_aliasing _ _ _ _ _ _ H H0 H1 H2).
      apply st_no_llvm_ptr_aliasing; auto.
    - split. destruct UU. destruct H0. cbn in H0. apply H0.
      destruct UU. destruct H0. cbn in H1.
      (* We are also missing information about ρ and l at this point. *)
      rewrite context_l0 in H2. inversion H2; subst.
      clear -H1 context_l0 genIR_op.

      unfold local_scope_modif in *.

      (* s1 and i0 are both extensions of state and local state with the [Name (s1)].
         Maybe we want a [local_scope_modif_remove] ? *)
      (* eapply local_scope_modif_shrink in H1. Unshelve. 9 : exact i0. *)
      (* 3 : red; reflexivity. 7 : exact s1. 2 : red; cbn; lia. *)
      (* eapply local_scope_modif_shrink. *)
      (* Unshelve. *)
      (* 9 : exact i0. 2 :red; reflexivity. *)
      (* 2 : cbn; red; reflexivity. *)

      (* unfold local_scope_modif in *. *)
      admit.
 }

  Unshelve.
  all : eauto. exact nat. exact "".
Admitted.
