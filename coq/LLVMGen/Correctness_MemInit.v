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
Require Import Helix.LLVMGen.StateCounters.

From Helix Require Import MSigmaHCOL.MemSetoid.

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
    eutt equiv (Ret (mem_union (mem_const_block i value) x))
        (tfor (E := Event) (fun k x => Ret (mem_add k value x)) 0 i x).
Proof.
  intros i value.
  induction i as [| i IH].
  - intros; cbn.
    rewrite tfor_0. apply eqit_Ret.
    apply mem_union_mem_empty.
  - intros; cbn.
    rewrite tfor_unroll_right; [| lia].
    unfold equiv.
    etransitivity; cycle 1.
    { eapply eutt_clo_bind. eapply IH.
      intros. apply eqit_Ret.
      eapply mem_add_proper.
      1, 2 : reflexivity. exact H. }
    rewrite bind_ret_l. apply eqit_Ret.
    apply mem_union_mem_add_commut.
Qed.


Lemma mem_union_tfor_interp i value x memH:
  eutt equiv
       (interp_helix (E := E_cfg) (Ret (mem_union (mem_const_block i value) x)) memH)
        (interp_helix (tfor (E := Event) (fun k x => Ret (mem_add k value x)) 0 i x) memH).
Proof.
  rewrite interp_helix_ret. revert x memH.
  induction i as [| i IH].
  - intros; cbn.
    rewrite tfor_0. rewrite interp_helix_ret.
    apply eqit_Ret. f_equiv.
    constructor; cbn; [ | apply mem_union_mem_empty].
    apply NM_Equiv_Reflexive.
  - intros; cbn.
    rewrite tfor_unroll_right; [| lia].
    unfold equiv.
    etransitivity; cycle 1.
    { setoid_rewrite interp_helix_bind. eapply eutt_clo_bind. eapply IH.
      intros. destruct u1, u2; inv H.
      - destruct p, p0. setoid_rewrite interp_helix_ret. inv H2; cbn in *.
        Unshelve.
        2 : { intros. destruct x0. destruct p.
              exact (Ret (Some (m, mem_add i value m0))).
              exact (Ret None). }
        apply eqit_Ret. do 2 constructor; eauto. cbn.
        eapply mem_add_proper; eauto.
     - apply eqit_Ret. reflexivity. }
    cbn. setoid_rewrite bind_ret_l. apply eqit_Ret.
    do 2 constructor; [ apply NM_Equiv_Reflexive | apply mem_union_mem_add_commut].
Qed.

Opaque dropVars.
Opaque newLocalVar.
Opaque resolve_PVar.
Opaque incLocalNamed.
Opaque incBlockNamed.
Opaque incVoid.
Opaque incLocal.
Opaque genWhileLoop.

From Paco Require Import paco.
From ITree Require Import Basics.HeterogeneousRelations.



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
  pose proof genIR_Γ _ _ _ GEN as GENIR_Γ.
  pose proof genIR_local_count _ _ _ GEN as GENIR_local.

  (* Clean up PVars *)
  cbn* in *; simp; cbn* in *.
  (* hide_cfg. *)
  inv_resolve_PVar Heqs0.
  unfold denotePExpr in *; cbn* in *.

  (* Renaming *)
  rename i1 into tptyp.

  rename r into pt.
  rename b into init_block_id.
  rename b0 into loopcontblock.
  rename r0 into loopvar.
  rename i7 into storeid.


  simp; try_abs.

  (* Clean up [no_failure] *)
  apply no_failure_Ret in NOFAIL.
  edestruct @no_failure_helix_LU as (? & NOFAIL' & ?); eauto; []; clear NOFAIL; rename NOFAIL' into NOFAIL; cbn in NOFAIL; eauto.
  hred.
  hstep; eauto.
  hred.

  rename x into mem_bkH.

  (* The computation is now reduced to a single writing event, but of a vector built atomically.
     On the Vellvm side, each cell of this vector must be written 1 by 1: we hence rephrase this in terms of a [tfor].
   *)
  match goal with
  |- context[interp_helix ?t _] => 
  cut (x <- Ret (mem_union (mem_const_block (MInt64asNT.to_nat i) value) mem_bkH);; trigger (MemSet n0 x) ≈ t); [| cbn; rewrite bind_ret_l; reflexivity];
  intros EQ; rewrite <- EQ; clear EQ
  end.
  cbn; rewrite interp_helix_bind.

  clean_goal.

  (* STEP 2:
    We now change the VIR semantics: not much to do. *)
  rewrite add_comment_eutt.
  bind_ret_r2.

  (* STEP 3:
    Memory invariant *)
  pose proof state_invariant_memory_invariant PRE as MINV_XOFF.
  unfold memory_invariant in MINV_XOFF.
  specialize (MINV_XOFF _ _ _ _ _ Heqo LUn). cbn in MINV_XOFF.
  destruct MINV_XOFF as (ptrll_xoff & τ_xoff & TEQ_xoff & FITS_xoff & INLG_xoff & bkh_xoff & MLUP_xoff & GETARRAYCELL_xoff); eauto.

  (* Duplicating, as we need to do the same inside the loop body *)
  assert (H' := H).
  rewrite MLUP_xoff in H; symmetry in H; inv H.

  inv TEQ_xoff. cbn.

 (* We need to settle on the relation that holds at the end of the loops.
     It is not quite [state_invariant]: on the helix side, the memory has not been touched,
     we performed a pure computation.
     On the Vellvm side, we are done, everything is written in memory.
   *)
  eapply eutt_clo_bind with (UU := succ_cfg (genIR_post σ s1 s2 nextblock ρ)).
  {
    match type of Heqs1 with
      | genWhileLoop ?a _ _ ?b ?c ?d ?e _ ?f _ ≡ inr (_,(?g,?h)) =>
        set (prefix := a); set (body_blocks := e);
          rename d into body_entry, f into nextblock, g into entry_id, h into bks
    end.

    clean_goal.

    rename s1 into s0, i6 into s1, i4 into sb1, i5 into sb2.
    pose proof
         @genWhileLoop_tfor_correct prefix loopvar loopcontblock body_entry body_blocks
         nextblock entry_id s1 s2 sb1 sb2 bks as LOOP.
    forward LOOP.
    { subst body_blocks; cbn; auto. }

    forward LOOP.
    { subst prefix; reflexivity. }

    forward LOOP.
    { eauto using wf_ocfg_bid_add_comment. }

    forward LOOP; [clear LOOP |].
    { solve_lid_bound_between. }

    forward LOOP; [clear LOOP |].
    { clear -INPUTS_BETWEEN NEXT.
      intros IN; rewrite inputs_convert_typ, add_comment_inputs in INPUTS_BETWEEN.
      rewrite Forall_forall in INPUTS_BETWEEN; apply INPUTS_BETWEEN in IN; clear INPUTS_BETWEEN.
      eapply not_bid_bound_between; eauto. }
    specialize (LOOP (Z.to_nat (DynamicValues.Int64.intval tptyp))).

    forward LOOP; [clear LOOP |].
    { subst body_blocks prefix.
      clear - Heqs1.
      rewrite intval_to_from_nat_id.
      apply Heqs1. }

    eapply eutt_Proper_mono; cycle 1.
    eapply eqit_trans.
    { eapply mem_union_tfor_interp. }
    { rewrite interp_helix_tfor; [| lia].
      match goal with
        |- context[tfor ?bod] =>
        specialize (LOOP _ bod)
      end.

      forward LOOP; [clear LOOP |].
      { rewrite Znat.Z2Nat.id.  edestruct DynamicValues.Int64.intrange; eauto.
        eapply Int64_intval_pos. }

    (* FIXME : loop invariant with partial write information *)
    set (I := (fun (k : nat) (mH : option (memoryH * mem_block)) (stV : memoryV * (local_env * global_env)) =>
                match mH with
                | None => False
                | Some (mH,bkH) => 
                let '(mV, (ρ, g')) := stV in
                 (* 1. Relaxed state invariant *)
                 state_invariant (protect σ n0) s0 mH stV /\
                 (* (* 2. Preserved state invariant *) *)
                 (* memory_invariant_partial_write' stV k n ptrll_yoff b y x_sz /\ *)
                 mH ≡ memH /\ g ≡ g' /\
                 allocated ptrll_xoff mV
                end)).

    set (P := fun o stV =>
                match o with
                | None => False
                | Some (mH,bkH) =>
                  bkH ≡ mem_union (mem_const_block 0 value) mem_bkH /\
                  state_invariant σ s0 mH stV
                end).

    set (Q := fun o stV =>
                match o with
                | None => False
                | Some (mH,bkH) =>
                  bkH ≡ mem_union (mem_const_block (MInt64asNT.to_nat i) value) mem_bkH /\
                  state_invariant σ s0 mH stV
                end).

    specialize (LOOP I P Q (Some (memH,mem_bkH))).

    forward LOOP.
    {
      (* Relating bodies *) clear LOOP.
      intros ? ? ? [[? ?]|] * (INV & LOOPVAR & BOUNDk & RET); [| inv INV].
      hred.

      rewrite denote_ocfg_unfold_in.
      2: {
        apply find_block_eq; auto.
      }

      cbn; vred. Transparent IntType. cbn.

      rewrite denote_no_phis.
      vred; cbn.

      rewrite denote_code_cons.
      unfold I in *. destruct INV as (mem_union & SI).
      assert (Heqo' := Heqo).


      pose proof state_invariant_memory_invariant as MINV_XOFF.
      unfold memory_invariant in MINV_XOFF.
      (* specialize (MINV_XOFF _ _ _ _ _ _ Heqo LUn). *)
      (* cbn in MINV_XOFF. *)

      (* Get mem information from PRE condition here (global and local state has changed). *)
      (* Needed for the following GEP and Store instructions *)

      admit.
    }

    forward LOOP.
    {
      (* Local stability of I *) clear LOOP.
      intros. unfold I in *; destruct a; eauto.
      destruct p; eauto. destruct H1. split; eauto.
      destruct H0.
      - eapply state_invariant_add_fresh'; eauto.
        admit.
      - eapply state_invariant_add_fresh'; eauto.
        admit.
    }

    forward LOOP; [solve_local_count|].
    forward LOOP; [solve_local_count|].

    forward LOOP; [clear LOOP |].
    {
      subst P I.
      clear; red; intros; auto.
    }

    forward LOOP; [clear LOOP |].
    {
      subst Q I.
      clear; red; intros.
      break_match_goal; auto. destruct p, H.
      split; eauto. admit.
    }

    eapply eutt_mon; cycle 1.
    { admit.
      (* apply LOOP. *)
      (* subst P; cbn; split; auto using mem_union_mem_empty. *)
      (* solve_state_invariant. *)
    }

    { subst Q. intros [[? ?] | ] (? & ? & ? & ?) ?; cbn; eauto. } }
    { admit. } }

  - intros [[? ?] | ] (? & ? & ? & ?); [| cbn in *; intuition].
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
      destruct LU2 as (? & ? & ? & ? & ? & ?).
      destruct (n0 =? a) eqn:EQ.
      * apply beq_nat_true in EQ; subst.
        do 2 eexists.
        split; [reflexivity |].
        do 2 (split; eauto).  intros.
        specialize (H2 H). destruct H2 as (?&?&?). exists x2; eauto.
        rewrite memory_lookup_memory_set_eq; eexists. admit.
        intros; eapply H3; eauto.
      * rewrite memory_lookup_memory_set_neq; [| apply NPeano.Nat.eqb_neq in EQ; auto].
        do 2 eexists ; eauto.
    + eapply id_allocated_memory_set; eauto.

Admitted.
