Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.
Require Import Helix.LLVMGen.Correctness_MExpr.
Require Import Helix.LLVMGen.IdLemmas.
Require Import Helix.LLVMGen.StateCounters.
Require Import Helix.LLVMGen.VariableBinding.
Require Import Helix.LLVMGen.BidBound.
Require Import Helix.LLVMGen.LidBound.
Require Import Helix.LLVMGen.StateCounters.
Require Import Helix.LLVMGen.Context.
Require Import Helix.LLVMGen.Correctness_While.


Set Implicit Arguments.
Set Strict Implicit.

Opaque dropVars.
Opaque newLocalVar.
Opaque resolve_PVar.
Opaque incBlockNamed.
Opaque incVoid.
Opaque incLocal.
Opaque genWhileLoop.

Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope nat_scope.

(* The result is a branch *)
Definition branches {T : Type} (to : block_id) (mh : memoryH * T) (c : config_cfg_T (block_id * block_id + uvalue)) : Prop :=
  match c with
  | (m,(l,(g,res))) => exists from, res ≡ inl (from, to)
  end.

Definition genIR_post {T} (σ : evalContext) (s1 s2 : IRState) (to : block_id) (li : local_env)
  : Rel_cfg_T T ((block_id * block_id) + uvalue) :=
  lift_Rel_cfg (state_invariant σ s2) ⩕
               branches to ⩕
               (fun sthf stvf => local_scope_modif s1 s2 li (fst (snd stvf))).

Lemma mem_union_mem_empty : forall x, mem_union mem_empty x ≡ x.
Admitted.
Lemma mem_union_mem_add_commut :
  forall i value x, mem_union (mem_add i value (mem_const_block i value)) x ≡ mem_add i value (mem_union (mem_const_block i value) x).
Admitted.

(* One step unrolling of the combinator *)
Lemma tfor_unroll_right: forall {E A} i j (body : nat -> A -> itree E A) a0,
    i <= j ->
    tfor body i (S j) a0 ≈
         a <- tfor body i j a0;; body j a.
Proof.
  intros * ineq.
  rewrite tfor_split; eauto.
  apply eutt_eq_bind; intros.
  rewrite tfor_unroll; [| lia].
  bind_ret_r2.
  apply eutt_eq_bind; intros.
  rewrite tfor_0; reflexivity.
Qed.

Lemma mem_union_tfor : 
  forall i value x,
    Ret (mem_union (mem_const_block i value) x) ≈
        tfor (E := Event) (fun k x => Ret (mem_add k value x)) 0 i x.
Proof.
  intros i value.
  induction i as [| i IH].
  - intros; cbn.
    rewrite tfor_0, mem_union_mem_empty.
    reflexivity.
  - intros; cbn.
    rewrite tfor_unroll_right; [| lia].
    rewrite <- IH.
    cbn; rewrite bind_ret_l.
    rewrite mem_union_mem_add_commut.
    reflexivity.
Qed.

Opaque dropVars.
Opaque newLocalVar.
Opaque resolve_PVar.
Opaque incLocalNamed.
Opaque incBlockNamed.
Opaque incVoid.
Opaque incLocal.
Opaque genWhileLoop.

Set Nested Proofs Allowed.
Lemma MemInit_Correct:
  ∀ (y_p : PExpr) (value : binary64) (s1 s2 : IRState) (σ : evalContext) 
    (memH : memoryH) (nextblock bid_in bid_from : block_id) (bks : list (LLVMAst.block typ)) 
    (g : global_env) (ρ : local_env) (memV : memoryV),
    genIR (DSHMemInit y_p value) nextblock s1 ≡ inr (s2, (bid_in, bks))
    → bid_bound s1 nextblock
    → state_invariant σ s1 memH (memV, (ρ, g))
    → Gamma_safe σ s1 s2
    → no_failure (E := E_cfg) (interp_helix (denoteDSHOperator σ (DSHMemInit y_p value)) memH)
    → eutt (succ_cfg (genIR_post σ s1 s2 nextblock ρ))
           (interp_helix (denoteDSHOperator σ (DSHMemInit y_p value)) memH)
           (interp_cfg (denote_ocfg (convert_typ [] bks) (bid_from, bid_in)) g ρ memV).
Proof.
  intros y_p value s1 s2 σ memH nextblock bid_in bid_from bks g ρ memV GEN NEXT PRE GAM NOFAIL.
  pose proof generates_wf_ocfg_bids _ NEXT GEN as WFOCFG.
  pose proof inputs_bound_between _ _ _ GEN as INPUTS_BETWEEN.

  (* STEP 1:
     We first massage the helix semantics to set it up correctly *)
  (* We execute symbolically the concrete prefix of the computation *)
  cbn in *.
  unfold denotePExpr in *.
  cbn* in *; simp.
  try_abs.
  hred.
  apply no_failure_Ret in NOFAIL.
  edestruct @no_failure_helix_LU as (? & NOFAIL' & ?); eauto; []; clear NOFAIL; rename NOFAIL' into NOFAIL; cbn in NOFAIL; eauto.
  hstep; eauto.
  hred.
  rename x into mem_bkH.
  (* The computation is now reduced to a single writing event, but of a vector built atomically.
     On the Vellvm side, each cell of this vector must be written 1 by 1: we hence rephrase this in terms of a [tfor].
   *)
  match goal with
  |- context[interp_helix ?t _] => 
  cut (x <- Ret (mem_union (mem_const_block (MInt64asNT.to_nat i) value) mem_bkH);; trigger (MemSet n x) ≈ t); [| cbn; rewrite bind_ret_l; reflexivity];
  intros EQ; rewrite <- EQ; clear EQ
  end.
  cbn; rewrite interp_helix_bind.
  rewrite mem_union_tfor.

  (* STEP 2:
     We now groom the VIR semantics: not much to do. *)
  rewrite add_comment_eutt.
  bind_ret_r2.
  assert (s1 ≡ i0) by (apply resolve_PVar_state in Heqs1; subst; auto); subst i0.

  (* We need to settle on the relation that holds at the end of the loops.
     It is not quite [state_invariant]: on the helix side, the memory has not been touched,
     we performed a pure computation.
     On the Vellvm side, we are done, everything is written in memory.
   *)
  eapply eutt_clo_bind with (UU := succ_cfg (genIR_post σ s1 s2 nextblock ρ)).

  -
    match type of Heqs2 with
    | genWhileLoop ?a _ _ ?b ?c ?d ?e _ ?f _ ≡ inr (_,(?g,?h)) =>
      set (prefix := a); set (body_blocks := e);
        rename b into loopvar, c into loopcontblock, d into body_entry, f into nextblock, g into entry_id, h into bks
    end.

    clean_goal.
    rename i2 into intV, i into intH.
    assert (intV ≡ intH).
    { clear - Heqs Heqs1.
      apply resolve_PVar_simple in Heqs1.
      destruct Heqs1 as (size & addr_n & LUn & EQsize & -> & _).
      cbn in *.
      simp.
      admit.
    }

    subst.
    rename i3 into s2, i4 into s3, i5 into s4, i6 into s5, i7 into s6, s2 into s7.

    pose proof
         @genWhileLoop_tfor_correct prefix loopvar loopcontblock body_entry body_blocks nextblock entry_id s6 s7 s1 s6 bks as LOOP.

    forward LOOP.
    {
      subst body_blocks; cbn; auto.
    }

    forward LOOP.
    {
      subst prefix; reflexivity.
    }

    forward LOOP.
    {
      eauto using wf_ocfg_bid_add_comment.
    }

    forward LOOP; [clear LOOP |].
    {
      apply resolve_PVar_state in Heqs1; subst.
      eapply lid_bound_between_shrink; [eapply lid_bound_between_incLocalNamed | | ]; eauto; try reflexivity; solve_local_count.
    }

    forward LOOP; [clear LOOP |].
    {
      clear -INPUTS_BETWEEN NEXT.
      intros IN; rewrite inputs_convert_typ, add_comment_inputs in INPUTS_BETWEEN.
      rewrite Forall_forall in INPUTS_BETWEEN; apply INPUTS_BETWEEN in IN; clear INPUTS_BETWEEN.
      eapply not_bid_bound_between; eauto.
    }      
    specialize (LOOP (Z.to_nat (DynamicValues.Int64.intval intH))).

    forward LOOP; [clear LOOP |].
    {
      subst body_blocks prefix.
      clear - Heqs2.
      rewrite intval_to_from_nat_id. 
      apply Heqs2.
    }

    rewrite interp_helix_tfor; [| lia].
    match goal with
      |- context[tfor ?bod] => 
      specialize (LOOP _ bod)
    end.

    forward LOOP; [clear LOOP |].
    {
      (* No overflow *)
      admit.
    }

    set (I := fun k o stV =>
                match o with
                | None => False
                | Some (mH,bkH) =>
                  bkH ≡ mem_union (mem_const_block k value) mem_bkH /\
                  state_invariant σ s6 mH stV
                end).

    set (P := fun o stV =>
                match o with
                | None => False
                | Some (mH,bkH) =>
                  bkH ≡ mem_union (mem_const_block 0 value) mem_bkH /\
                  state_invariant σ s6 mH stV
                end).

    set (Q := fun o stV =>
                match o with
                | None => False
                | Some (mH,bkH) =>
                  bkH ≡ mem_union (mem_const_block (MInt64asNT.to_nat intH) value) mem_bkH /\
                  state_invariant σ s6 mH stV
                end).

    specialize (LOOP I P Q (Some (memH,mem_bkH))).

    forward LOOP.
    {
      (* Relating bodies *)
      admit.
    }

    forward LOOP.
    {
      (* Local stability of I *)
      admit.
    }

    forward LOOP.
    {
      apply resolve_PVar_state in Heqs1; subst.
      solve_local_count.
    }

    forward LOOP; [reflexivity |].

    forward LOOP; [clear LOOP |].
    {
      subst P I.
      clear; red; intros; auto.
    }

    forward LOOP; [clear LOOP |].
    {
      subst Q I.
      clear; red; intros.
      break_match_goal; auto.
    }

    eapply eutt_mon; cycle 1.
    {
      apply LOOP.
      subst P; cbn; split; auto using mem_union_mem_empty.
      solve_state_invariant.
    }

    { subst Q.
      intros [[? []] | ] (? & ? & ? & ?) (H1 & H2 & H3); cbn; eauto.
      split; [| split]; cbn; eauto.
      - cbn.
        admit.
      - destruct H1; cbn; eauto.
    }

  - intros [[? []] | ] (? & ? & ? & ?); [| cbn in *; intuition].
    intros (H1 & H2 & H3); cbn in *; eauto.
    rewrite interp_helix_MemSet.
    apply eutt_Ret.
    split; [| split]; cbn; auto.
    (* Need to transport information about what has been written on the Vellvm side during the loop *)
    clear - H1.
    destruct H1; split; auto.
    + Opaque memory_set.
      cbn; intros * LU1 LU2.
      eapply mem_is_inv in LU2; eauto.
      destruct v; auto.
      destruct LU2 as (? & ? & ? & ?).
      destruct (n =? a) eqn:EQ.
      * apply beq_nat_true in EQ; subst.
        rewrite memory_lookup_memory_set_eq.
        do 2 eexists.
        split; [reflexivity |].
        (* do 2 (split; [reflexivity |]). *)
        admit.
      * rewrite memory_lookup_memory_set_neq; [| apply NPeano.Nat.eqb_neq in EQ; auto].
        eauto.
    + admit.

Admitted.
