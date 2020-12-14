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

Import ProofMode.

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

Section DSHLoop_is_tfor.

  (* The denotation of the [DSHLoop] combinator can be rewritten in terms of the [do_n] combinator.
     So if we specify [genWhileLoop] in terms of this same combinator, then we might be good to go
     with a generic spec that of [GenWhileLoop] that does not depend on Helix.
   *)
  Lemma DSHLoop_as_tfor: forall σ n op,
    denoteDSHOperator σ (DSHLoop n op)
                      ≈
                      tfor (fun p _ => vp <- lift_Serr (MInt64asNT.from_nat p) ;;
                                    denoteDSHOperator (DSHnatVal vp :: σ) op) 0 n tt.
  Proof.
    intros.
    unfold tfor.
    cbn.
    eapply (eutt_iter'' (fun a '(b,_) => a ≡ b) (fun a '(b,_) => a ≡ b)); auto.
    intros ? [? []] <-.
    cbn.
    break_match_goal.
    apply eutt_Ret; auto.
    rewrite bind_bind.
    eapply eutt_eq_bind; intros ?.
    eapply eutt_eq_bind; intros ?.
    apply eutt_Ret; auto.
  Qed.

  (* The denotation of the [DSHLoop] combinator can be rewritten in terms of the [do_n] combinator.
     So if we specify [genWhileLoop] in terms of this same combinator, then we might be good to go
     with a generic spec that of [GenWhileLoop] that does not depend on Helix.
   *)
  Lemma DSHLoop_interpreted_as_tfor:
    forall E σ n op m,
      interp_helix (E := E) (denoteDSHOperator σ (DSHLoop n op)) m
                   ≈
                   tfor (fun k x => match x with
                                 | None => Ret None
                                 | Some (m',_) => interp_helix (vp <- lift_Serr (MInt64asNT.from_nat k) ;;
                                                               denoteDSHOperator (DSHnatVal vp :: σ) op) m'
                                 end)
                   0 n (Some (m, ())).
  Proof.
    intros.
    rewrite DSHLoop_as_tfor.
    rewrite interp_helix_tfor; [|lia].
    cbn.
    apply eutt_tfor.
    intros [[m' _]|] i; [| reflexivity].
    rewrite interp_helix_bind.
    rewrite bind_bind.
    apply eutt_eq_bind; intros [[?m ?] |]; [| rewrite bind_ret_l; reflexivity].
    bind_ret_r2.
    apply eutt_eq_bind.
    intros [|]; reflexivity.
  Qed.

End DSHLoop_is_tfor.

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

Lemma DSHLoop_correct:
  ∀ (n : nat) (op : DSHOperator),
    (∀ (s1 s2 : IRState) (σ : evalContext) (memH : memoryH) (nextblock bid_in bid_from : block_id) (bks : list (LLVMAst.block typ)) (g : global_env) (ρ : local_env) (memV : memoryV),
        genIR op nextblock s1 ≡ inr (s2, (bid_in, bks))
        → bid_bound s1 nextblock
        → state_invariant σ s1 memH (memV, (ρ, g))
        → Gamma_safe σ s1 s2
        → no_failure (E := E_cfg) (interp_helix (denoteDSHOperator σ op) memH)
        → eutt (succ_cfg (genIR_post σ s1 s2 nextblock ρ)) (interp_helix (denoteDSHOperator σ op) memH) (interp_cfg (denote_ocfg (convert_typ [] bks) (bid_from, bid_in)) g ρ memV))
    → ∀ (s1 s2 : IRState) (σ : evalContext) (memH : memoryH) (nextblock bid_in bid_from : block_id) (bks : list (LLVMAst.block typ)) (g : global_env) (ρ : local_env) (memV : memoryV),
      genIR (DSHLoop n op) nextblock s1 ≡ inr (s2, (bid_in, bks))
      → bid_bound s1 nextblock
      → state_invariant σ s1 memH (memV, (ρ, g))
      → Gamma_safe σ s1 s2
      → no_failure (E := E_cfg) (interp_helix (denoteDSHOperator σ (DSHLoop n op)) memH)
      → eutt (succ_cfg (genIR_post σ s1 s2 nextblock ρ))
             (interp_helix (denoteDSHOperator σ (DSHLoop n op)) memH)
             (interp_cfg (denote_ocfg (convert_typ [] bks) (bid_from, bid_in)) g ρ memV).
Proof.
  intros n op IHop s1 s2 σ memH nextblock bid_in bid_from bks g ρ memV GEN NEXT PRE GAM NOFAIL.
  
  pose proof generates_wf_ocfg_bids _ NEXT GEN as WFOCFG.
  pose proof inputs_bound_between _ _ _ GEN as INPUTS_BETWEEN.
  pose proof genIR_Γ _ _ _ GEN as GENIR_Γ.
  pose proof genIR_local_count _ _ _ GEN as GENIR_local.

  (* We know that the Helix denotation can be expressed via the [tfor] operator *)
  rewrite DSHLoop_interpreted_as_tfor.
  rewrite DSHLoop_interpreted_as_tfor in NOFAIL.

  cbn* in *; simp; cbn in *.
  rewrite add_comment_eutt.
  clean_goal.
  rename i into s1, i0 into s2, i1 into s3, i2 into s4, i3 into s5, s2 into s6.
  destruct_unit.
  clean_goal.
  rename l0 into bks, r into loopvar.

  (* So really, it is a direct application of [genWhileLoop_tfor_correct] with
         our induction hypothesis filling in for the equivalence of bodies in the lemma.
         Except that the lemma is a mouthful, so doing so is a tad bit of work!
   *)

  (* Let's step through carefully: we provide manually the first batch of arguments *)
  pose proof
       @genWhileLoop_tfor_correct "Loop_loop" loopvar b b0 l nextblock bid_in s5 s6 s1 s5 bks as GENC.
  forward GENC; [clear GENC |].
  eauto using genWhileLoop_entry_in_scope.
  
  forward GENC; [clear GENC |].
  reflexivity.

  forward GENC; [clear GENC |].
  {
    eauto using wf_ocfg_bid_add_comment.
  }

  forward GENC; [clear GENC |].
  {
    eapply lid_bound_between_shrink; [eapply lid_bound_between_newLocalVar | | ]; eauto; try reflexivity; solve_local_count.
  }

  forward GENC; [clear GENC |].
  {
    clear -INPUTS_BETWEEN NEXT.
    intros IN; rewrite inputs_convert_typ, add_comment_inputs in INPUTS_BETWEEN.
    rewrite Forall_forall in INPUTS_BETWEEN; apply INPUTS_BETWEEN in IN; clear INPUTS_BETWEEN.
    eapply not_bid_bound_between; eauto.
  }

  specialize (GENC n Heqs6 (option (memoryH * unit)%type)).
  match goal with
    |- eutt _ (tfor ?bod _ _ _) _ => specialize (GENC bod)
  end.

  forward GENC; [clear GENC |].
  {
    clear -Heqs.
    unfold MInt64asNT.from_nat in Heqs.
    unfold MInt64asNT.from_Z in Heqs.
    simp.
    apply l0.
  }

  specialize (IHop s3 s4).

  (* Invariant at each iteration *)
  set (I := (fun (k : nat) (mH : option (memoryH * ())) (stV : memoryV * (local_env * global_env)) =>
               match mH with
               | None => False
               | Some (mH,tt) => state_invariant σ s2 mH stV
               end)).
  (* Precondition and postcondition *)
  set (P := (fun (mH : option (memoryH * ())) (stV : memoryV * (local_env * global_env)) =>
               match mH with
               | None => False
               | Some (mH,tt) => state_invariant σ s2 mH stV
               end)).

  specialize (GENC I P P (Some (memH, ()))).

  forward GENC; [clear GENC |].
  {
    subst I P; intros ? ? ? [[? []]|] * (INV & LOOPVAR & BOUNDk & RET); [| inv INV]; cbn in *.

    assert (EQk: MInt64asNT.from_nat k ≡ inr (Int64.repr (Z.of_nat k))).
    {clear - BOUNDk Heqs.
     destruct (MInt64asNT.from_nat k) eqn:EQ.
     - exfalso.
       unfold MInt64asNT.from_nat in *.
       unfold MInt64asNT.from_Z in *.
       simp; lia.
     - unfold MInt64asNT.from_nat in *.
       apply from_Z_intval in EQ.
       rewrite EQ, repr_intval.
       reflexivity.
    }

    rewrite EQk.
    hred.

    pose proof Heqs3 as GENIR.
    eapply IHop in Heqs3; clear IHop; cycle 1.
    - eapply bid_bound_mono.
      eapply bid_bound_incBlockNamed; eauto; reflexivity.
      erewrite newLocalVar_block_count; eauto.

    - eapply state_invariant_enter_scope_DSHnat; eauto.
      intros abs; eapply in_Gamma_Gamma_eq in abs; [| eapply incBlockNamed_Γ ; eauto].
      eapply GAM; eauto.
      eapply lid_bound_between_newLocalVar in Heqs2.
      2:reflexivity.
      eapply lid_bound_between_shrink; eauto.
      solve_local_count.
      apply dropVars_local_count in Heqs5.
      apply genWhile_local_count in  Heqs6.
      solve_local_count.

    - clear NOFAIL INPUTS_BETWEEN WFOCFG.
      intros ? BOUND IN.
      inv IN.
      destruct n0 as [| idx].
      + cbn in H. 
        erewrite newLocalVar_Γ in H0; eauto.
        inv H0.
        inv H.
        eapply lid_bound_earlier with (id1 := id) in BOUND.
        2: eapply newLocalVar_lid_bound; eauto; reflexivity.
        2: solve_local_count.
        apply BOUND; auto.

      + rewrite nth_error_Sn in H.
        eapply GAM; cycle 1. 
        econstructor; eauto.
        apply newLocalVar_Γ in Heqs2.
        apply incBlockNamed_Γ in Heqs1.
        rewrite <- Heqs1.
        rewrite Heqs2 in H0.
        rewrite nth_error_Sn in H0.
        eauto.
        eapply lid_bound_between_shrink.
        eauto.
        apply newLocalVar_local_count in Heqs2.
        solve_local_count.
        apply dropVars_local_count in Heqs5.
        apply genWhile_local_count in  Heqs6.
        solve_local_count.

    - pose proof no_failure_tfor _ _ _ _ NOFAIL; clear NOFAIL.
      specialize (H k (m,tt)).
      cbn in *.
      forward H; [lia |].
      forward H; auto.
      rewrite EQk in H.
      apply no_failure_Ret in H.
      auto.

    - eapply eutt_mon, Heqs3.
      clear Heqs3 NOFAIL INPUTS_BETWEEN WFOCFG.
      intros [[? []]|] (mVf & lf & gf & ?) POST; [destruct POST as (P1 & P2 & P3) | inv POST].
      split; [| split; [| split]].
      + rewrite <- LOOPVAR; eapply local_scope_modif_out; eauto.
        2: eapply lid_bound_between_newLocalVar; eauto.
        eapply newLocalVar_local_count in Heqs2; solve_local_count.
        reflexivity.
      + eauto.
      + cbn in P1.
        eapply state_invariant_escape_scope; eauto.
        erewrite <- genIR_Γ; eauto.
        eapply newLocalVar_Γ; eauto.
      + cbn in *.
        clear INV P1 P2.
        apply local_scope_modif_shrink with s3 s4; auto.
        apply newLocalVar_local_count in Heqs2; solve_local_count.
        solve_local_count.
  }

  forward GENC; [clear GENC |].
  {
    subst I P; cbn.
    intros _ * BOUND INV; simp; auto.
    apply state_invariant_Γ with s1; eauto using incBlockNamed_Γ.
    eapply state_invariant_Γ with (s2 := s1) in INV; [| symmetry; eauto using incBlockNamed_Γ].
    eapply state_invariant_Γ in INV; [| symmetry; eassumption].
    eapply state_invariant_add_fresh' with s6; eauto.
    destruct BOUND as [BOUND | BOUND].
    - eapply lid_bound_between_shrink_down; [| apply BOUND].
      apply newLocalVar_local_count in Heqs2.
      apply dropVars_local_count in Heqs5.
      solve_local_count.
    - apply genWhile_local_count in  Heqs6.
      apply newLocalVar_local_count in Heqs2.
      apply dropVars_local_count in Heqs5.
      eapply lid_bound_between_shrink_up; [| apply BOUND].
      solve_local_count.
    - eapply state_invariant_Γ; eauto.
  }

  forward GENC; [clear GENC |].
  {
    apply newLocalVar_local_count in Heqs2.
    apply dropVars_local_count in Heqs5.
    solve_local_count.
  }

  forward GENC; [clear GENC |].
  {
    reflexivity.
  }

  forward GENC; [clear GENC |].
  {
    subst P I; red; intros; auto. 
  }

  forward GENC; [clear GENC |].
  {
    subst I P; red; intros; auto. 
  }

  specialize (GENC g ρ memV bid_from).
  eapply eutt_mon; [| apply GENC].
  {
    (* state_invariant between s1 and s2 or s6? or something else? *)
    clear GENC NOFAIL INPUTS_BETWEEN IHop WFOCFG;subst P I.
    intros [[? []] | ] (? & ? & ? & ?) (H1 & H2 & H3); cbn.
    split; [| split]; cbn; eauto.
    - (* Need to enter scope,then escape it to link with s2 *)
      eapply state_invariant_Γ; eauto.
      apply incBlockNamed_Γ in Heqs1.
      rewrite <- GENIR_Γ, Heqs1; reflexivity.
    - destruct H1; eauto.
    - eauto.
  }
  { subst P; cbn.
    clear -PRE Heqs1.
    solve_state_invariant.
  }

Qed.

