Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.
Require Import Helix.LLVMGen.Correctness_MExpr.
Require Import Helix.LLVMGen.Correctness_Assign.
Require Import Helix.LLVMGen.Correctness_Alloc.
Require Import Helix.LLVMGen.Correctness_While.
Require Import Helix.LLVMGen.Correctness_Loop.
Require Import Helix.LLVMGen.Correctness_IMap.
Require Import Helix.LLVMGen.Correctness_Power.
Require Import Helix.LLVMGen.Correctness_MemInit.
Require Import Helix.LLVMGen.IdLemmas.
Require Import Helix.LLVMGen.StateCounters.
Require Import Helix.LLVMGen.VariableBinding.
Require Import Helix.LLVMGen.BidBound.
Require Import Helix.LLVMGen.LidBound.
Require Import Helix.LLVMGen.StateCounters.
Require Import Helix.LLVMGen.Context.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Global Opaque resolve_PVar.
Opaque incBlockNamed.
Opaque incVoid.
Opaque incLocal.

Axiom int_eq_inv: forall a b, Int64.intval a ≡ Int64.intval b -> a ≡ b.

Arguments add_comment /.
Arguments add_comments /.
Section GenIR.

  (* The result is a branch *)
  Definition branches (to : block_id) (mh : memoryH * ()) (c : config_cfg_T (block_id * block_id + uvalue)) : Prop :=
    match c with
    | (m,(l,(g,res))) => exists from, res ≡ inl (from, to)
    end.

  Hint Resolve state_invariant_incBlockNamed : state_invariant.
  Hint Resolve state_invariant_incLocal : state_invariant.
  Hint Resolve state_invariant_incVoid : state_invariant.

  Tactic Notation "state_inv_auto" := eauto with state_invariant.

  Lemma assert_NT_lt_success :
    forall {s1 s2 x y v},
      assert_NT_lt s1 x y ≡ inr v ->
      assert_NT_lt s2 x y ≡ inr v.
  Proof.
    intros s1 s2 x y v H.
    unfold assert_NT_lt in *.
    destruct ((MInt64asNT.to_nat x <? MInt64asNT.to_nat y)%nat); inversion H.
    cbn in *. subst.
    auto.
  Qed.

  (* Import ProofMode. *)
  Notation "'gep' τ e" := (OP_GetElementPtr τ e) (at level 10, only printing).
  Notation "'double'" := (DTYPE_Double) (at level 10, only printing).
  Notation "'arr'" := (DTYPE_Array) (at level 10, only printing).
  Notation "'to_nat'" := (MInt64asNT.to_nat) (only printing).

  Import AlistNotations.

  Definition genIR_post (σ : evalContext) (s1 s2 : IRState) (to : block_id) (li : local_env)
    : Rel_cfg_T unit ((block_id * block_id) + uvalue) :=
    lift_Rel_cfg (state_invariant σ s2) ⩕
                 branches to ⩕
                 (fun sthf stvf => local_scope_modif s1 s2 li (fst (snd stvf))).

  Opaque alist_add.

  (* Correctness result for the compilation of operators.
     All core features of the language are tackled: assignment and allocation,
     sequence and looping, iterations over vectors with IMap and Power.
     Three operators remain to be handled: DSHBinop, DSHMemMap2, MemInit.
     They have all similar structures to IMap and Power, iterating over vectors:
     we do not anticipate the need for any extra meta-theory nor invariant.
   *)
  Lemma compile_FSHCOL_correct :
    forall (** Compiler bits *) (s1 s2: IRState)
      (** Helix bits    *) (op: DSHOperator) (σ : evalContext) (memH : memoryH)
      (** Vellvm bits   *) (nextblock bid_in bid_from : block_id) (bks : list (LLVMAst.block typ)) (g : global_env) (ρ : local_env) (memV : memoryV),
      genIR op nextblock s1 ≡ inr (s2,(bid_in,bks)) ->                        (* Compilation succeeds *)
      no_failure (E := E_cfg) (interp_helix (denoteDSHOperator σ op) memH) -> (* Evaluation succeeds *)
      bid_bound s1 nextblock ->
      state_invariant σ s1 memH (memV, (ρ, g)) ->
      Gamma_safe σ s1 s2 ->
      eutt (succ_cfg (genIR_post σ s1 s2 nextblock ρ))
           (interp_helix (denoteDSHOperator σ op) memH)
           (interp_cfg (D.denote_ocfg (convert_typ [] bks) (bid_from,bid_in))
                       g ρ memV).
  Proof.
    intros s1 s2 op; revert s1 s2; induction op; intros * GEN NOFAIL NEXT PRE GAM.

    - (* DSHNOp *)
      cbn* in *.
      simp.
      cbn*.
      hvred.
      vjmp.
      (* TODO :( *)
      cbn.
      (* unfold tfmap. TFmap_block; cbn. *)
      vred.
      vred.
      vred.
      vred.

      rewrite denote_ocfg_unfold_not_in; cycle 1.
      {
        (* TODO: auto and part of vjmp_out *)
        rewrite find_block_ineq; [apply find_block_nil | cbn].

        assert (nextblock ≢ bid_in).
        {
          (* TODO: pull this out into automation *)
          eapply bid_bound_fresh; eauto.
          eapply bid_bound_bound_between; eauto.

          eapply bid_bound_incBlockNamed; eauto; reflexivity.
          solve_not_bid_bound.
          block_count_replace. lia.
          reflexivity.
        }
        auto.
      }
      vred.

      apply eutt_Ret.
      split; [| split]; cbn in *; eauto.
      eapply state_invariant_incBlockNamed; eauto.

    - (* DSHAssign *)
      apply DSHAssign_correct; auto.

    - (* DSHIMap *)
      apply DSHIMap_correct; auto.

    - (* DSHBinop *)
      admit.

    - (* DSHMemMap2 *)
      admit.

    - (* DSHPower *)
      apply DSHPower_correct; auto. 

    - (* DSHLoop *)
      apply DSHLoop_correct; auto. 

    - (* DSHAlloc *)
      apply DSHAlloc_correct; auto. 

    - (* DSHMemInit *)
      apply MemInit_Correct; auto.

    - (* DSHSeq *)
      Opaque add_comment.
      cbn.

      pose proof GEN as GEN_DESTRUCT.
      cbn* in GEN_DESTRUCT; simp.

      rename i into s_op1, l0 into bk_op1, l into bk_op2.
      rename b into op2_entry, bid_in into op1_entry.
      rename Heqs0 into GEN_OP2, Heqs2 into GEN_OP1.
      rewrite add_comment_eutt.
      cbn.
      clean_goal.

      rewrite convert_typ_ocfg_app.
      rewrite denote_ocfg_app; eauto.
      2: {
        unfold no_reentrance.
        pose proof GEN_OP1 as GEN_OP1'.
        
        apply (inputs_not_earlier_bound _ _ _ NEXT) in GEN_OP1'.
        apply inputs_bound_between in GEN_OP1.
        apply outputs_bound_between in GEN_OP2.

        pose proof (Forall_and GEN_OP1 GEN_OP1') as INPUTS.
        cbn in INPUTS.
        eapply Forall_disjoint; eauto.
        intros x OUT_PRED [IN_BOUND IN_NEXT].
        destruct OUT_PRED as [OUT_PRED | OUT_PRED]; auto.
        eapply (state_bound_between_separate incBlockNamed_count_gen_injective OUT_PRED IN_BOUND).
        lia. auto.
        block_count_replace.
        lia.
      }
      hvred.

      cbn in *.
      pose proof PRE as SINV.
      simp.

      rename Heqs0 into GEN_OP2, Heqs1 into GEN_OP1.

      eapply eutt_clo_bind_returns.
      {
        eapply IHop1 with (s1:=s_op1) (s2:=s2); eauto.
        - eapply bid_bound_genIR_entry; eauto.
        - pose proof GEN_OP2 as GEN_OP2'.
          apply genIR_Γ in GEN_OP2'.
          apply genIR_local_count in GEN_OP2.
          eapply state_invariant_Γ; eauto.
        - eapply Gamma_safe_shrink; eauto.
          eauto using genIR_Γ.
          solve_local_count.
      }

      clear IHop1.
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      cbn in PRE0; destruct PRE0 as [INV2 [[from2 BRANCH2] POST]]; cbn in *; inv_eqs.
      subst.

      eapply eqit_mon; auto.
      2: {
        eapply IHop2. try exact GEN_OP2; eauto.
        - auto.
        - auto.
        - eapply state_invariant_Γ'; eauto.
          apply genIR_Γ in GEN_OP1; apply genIR_Γ in GEN_OP2; rewrite GEN_OP2; auto.
          destruct SINV; auto.
        - eapply Gamma_safe_shrink; eauto.
          eauto using genIR_Γ.
          solve_local_count.
      }
      clear IHop2.

      intros [[memH1 ?]|] (memV1 & l1 & g1 & res1) PR; [| inv PR].
      destruct PR as [? [? BR]].
      cbn in *.

      destruct res1 as [[from1 next] | v]; [| destruct H0; simp]. 
      split; cbn; eauto.
      eapply state_invariant_Γ; eauto.
      apply genIR_Γ in GEN_OP1; auto.
      apply genIR_local_count in GEN_OP1; auto.
      split; cbn; eauto.
      rename s_op1 into s2, s2 into s3.
      rename ρ into l1, l into l2, l1 into l3.

      apply genIR_local_count in GEN_OP1. 
      apply genIR_local_count in GEN_OP2.
      eapply local_scope_modif_trans'''; eauto.

  Admitted.


End GenIR.
