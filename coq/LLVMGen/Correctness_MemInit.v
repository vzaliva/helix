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
Definition branches (to : block_id) (mh : memoryH * ()) (c : config_cfg_T (block_id * block_id + uvalue)) : Prop :=
  match c with
  | (m,(l,(g,res))) => exists from, res ≡ inl (from, to)
  end.

Definition genIR_post (σ : evalContext) (s1 s2 : IRState) (to : block_id) (li : local_env)
  : Rel_cfg_T unit ((block_id * block_id) + uvalue) :=
  lift_Rel_cfg (state_invariant σ s2) ⩕
               branches to ⩕
               (fun sthf stvf => local_scope_modif s1 s2 li (fst (snd stvf))).

Lemma mem_union_tfor : 
  forall i value x,
    Ret (mem_union (mem_const_block (MInt64asNT.to_nat i) value) x) ≈
        tfor (E := Event) (fun k x => Ret (mem_add k value x)) 0 (S (MInt64asNT.to_nat i)) x.
Proof.
Admitted.


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

  (* We need to settle on the relation that holds at the end of the loops.
     It is not quite [state_invariant]: on the helix side, the memory has not been touched,
     we performed a pure computation.
     On the Vellvm side, we are done, everything is written in memory.
   *)
  eapply eutt_clo_bind.

  - match type of Heqs2 with
    | genWhileLoop ?a _ _ ?b ?c ?d ?e _ ?f _ ≡ inr (_,(?g,?h)) =>
      set (prefix := a); set (body_blocks := e);
        rename b into loopvar, c into loopcontblock, d into body_entry, f into nextblock, g into entry_id, h into bks
    end.

    clean_goal.
    rename i0 into s2, i3 into s3, i4 into s4, i5 into s5, i6 into s6, i7 into s7, s2 into s8.
    pose proof
         @genWhileLoop_tfor_correct prefix loopvar loopcontblock body_entry body_blocks nextblock entry_id s1 s8 s1 s8 bks as LOOP.

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

    (* Urg, need to rephrase i2 into some kind of int_of_ant *)

Admitted.
