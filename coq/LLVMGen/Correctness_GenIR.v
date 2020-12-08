Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.
Require Import Helix.LLVMGen.Correctness_MExpr.
Require Import Helix.LLVMGen.Correctness_Assign.
Require Import Helix.LLVMGen.Correctness_Alloc.
Require Import Helix.LLVMGen.Correctness_While.
Require Import Helix.LLVMGen.IdLemmas.
Require Import Helix.LLVMGen.StateCounters.
Require Import Helix.LLVMGen.VariableBinding.
Require Import Helix.LLVMGen.BidBound.
Require Import Helix.LLVMGen.LidBound.
Require Import Helix.LLVMGen.StateCounters.

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

  (* TODO: Move *)
  Lemma add_comment_eutt :
    forall comments bks ids,
      denote_ocfg (convert_typ [] (add_comment bks comments)) ids ≈ denote_ocfg (convert_typ [] bks) ids.
  Proof.
    intros comments bks ids.
    induction bks.
    - cbn. reflexivity.
    - cbn.
      destruct ids as (bid_from, bid_src); cbn.
      match goal with
      | |- context[denote_ocfg ?bks (_, ?bid_src)] =>
        destruct (find_block bks bid_src) eqn:FIND
      end.
  Admitted.

  (* TODO: Move *)
  (* Could probably have something more general... *)
  Lemma add_comments_eutt :
    forall bk comments bids,
      denote_ocfg
        [fmap (typ_to_dtyp [ ]) (add_comments bk comments)] bids ≈ denote_ocfg [fmap (typ_to_dtyp [ ]) bk] bids.
  Proof.
    intros bk comments bids.
  Admitted.

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
  Ltac remove_neq_locals :=
    match goal with
    | |- Maps.add ?x ?v ?l1 @ ?id ≡ ?l2 @ ?id =>
      assert (x ≢ id) by
          (eapply lid_bound_earlier; eauto;
           [eapply incLocal_lid_bound; eauto | solve_local_count]);
      setoid_rewrite maps_add_neq; eauto
    end.

  Lemma genWhileLoop_entry_in_scope : forall op b s1 s2 entry_body bodyV,
      genIR op b s1 ≡ inr (s2, (entry_body, bodyV)) ->
      In entry_body (inputs bodyV).
  Proof.
    induction op; intros *; try (cbn; intros GEN; clear -GEN; simp; cbn; auto; fail).
    Opaque add_comment.
    cbn; intros GEN; simp.
    rewrite add_comment_inputs, inputs_app.
    apply ListUtil.in_appl; eauto.
  Qed.
  Transparent add_comment.

  Definition genIR_post (σ : evalContext) (s1 s2 : IRState) (to : block_id) (li : local_env)
    : Rel_cfg_T unit ((block_id * block_id) + uvalue) :=
    lift_Rel_cfg (state_invariant σ s2) ⩕
                 branches to ⩕
                 (fun sthf stvf => local_scope_modif s1 s2 li (fst (snd stvf))).

  Opaque alist_add.
  Lemma compile_FSHCOL_correct :
    forall (** Compiler bits *) (s1 s2: IRState)
      (** Helix bits    *) (op: DSHOperator) (σ : evalContext) (memH : memoryH)
      (** Vellvm bits   *) (nextblock bid_in bid_from : block_id) (bks : list (LLVMAst.block typ))
      (* (env : list (ident * typ)) *)  (g : global_env) ((* ρi  *)ρ : local_env) (memV : memoryV),
      genIR op nextblock s1 ≡ inr (s2,(bid_in,bks)) ->
      bid_bound s1 nextblock ->
      state_invariant σ s1 memH (memV, (ρ, g)) ->
      Gamma_safe σ s1 s2 ->
      no_failure (E := E_cfg) (interp_helix (denoteDSHOperator σ op) memH) -> (* Evaluation succeeds *)
      eutt (succ_cfg (genIR_post σ s1 s2 nextblock ρ))
           (interp_helix (denoteDSHOperator σ op) memH)
           (interp_cfg (D.denote_ocfg (convert_typ [] bks) (bid_from,bid_in))
                       g ρ memV).
  Proof.
    intros s1 s2 op; revert s1 s2; induction op; intros * GEN NEXT PRE GAM NOFAIL.

    - (* DSHNOp *)
      cbn* in *.
      simp.
      cbn*.
      hvred.
      vjmp.
      (* TODO :( *)
      unfold fmap, Fmap_block; cbn.
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
      apply compile_DSHAssign_correct; auto.

    - admit.
    - admit.
    - admit.
    - admit.

    - (* DSHLoop *)
      Import ProofMode.

      Opaque add_comment.
      Opaque dropVars.
      Opaque newLocalVar.
      Opaque genWhileLoop.

      (* We know that the Helix denotation can be expressed via the [tfor] operator *)
      rewrite DSHLoop_interpreted_as_tfor.
      cbn* in *; simp; cbn in *.
      rewrite add_comment_eutt.
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

        Set Nested Proofs Allowed.
        Lemma genWhileLoop_wf_ocfg_bid :
          forall prefix from to loopvar loopcontblock body_entry body_blocks init_code nextblock s1 s2 entryblock bks,
            genWhileLoop prefix from to loopvar loopcontblock body_entry body_blocks init_code nextblock s1 ≡ inr (s2, (entryblock, bks)) ->
            wf_ocfg_bid bks.
        Admitted.
        eauto using genWhileLoop_wf_ocfg_bid.

      }

      forward GENC; [clear GENC |].
      {
        (* need lemma about newLocalVar *)
        (* solve_lid_bound_between. *)
        admit.
      }

      forward GENC; [clear GENC |].
      {
        (* need [free_in_cfg] for genWhileLoop and genIR *)
        admit.
      }

      specialize (GENC n Heqs6 (option (memoryH * unit)%type)).
      match goal with
        |- eutt _ (tfor ?bod _ _ _) _ => specialize (GENC bod)
      end.

      forward GENC; [clear GENC |].
      {
        rename n into foo.
        clear -Heqs.
        unfold MInt64asNT.from_nat in Heqs.
        unfold MInt64asNT.from_Z in Heqs.
        simp.
        apply l0.
      }

      admit.

      (* (* Invariant at each iteration *) *)
      (* specialize (GENC (fun k mH stV => *)
      (*                     match mH with *)
      (*                     | None => False *)
      (*                     | Some (mH,tt) => state_invariant σ s2 (* b *) mH stV *)
      (*                     end)). *)
      (* (* Precondition *) *)
      (* specialize (GENC (fun mH stV => *)
      (*                     match mH with *)
      (*                     | None => False *)
      (*                     | Some (mH,tt) => state_invariant σ s2 mH stV *)
      (*                     end)). *)
      (* (* Postcondition *) *)
      (* specialize (GENC (fun mH stV => *)
      (*                     match mH with *)
      (*                     | None => False *)
      (*                     | Some (mH,tt) => state_invariant σ s2 mH stV *)
      (*                     end)). *)

      (* { *)
      (*   clear GENC. *)
      (*   cbn. *)
      (*   intros x (? & ? & ? & ?). *)
      (*   intros (H1 & H2). *)
      (*   destruct x as [[mH []] | ?]; [| intuition]. *)
      (*   split; cbn; auto. *)
      (*   destruct H1; eauto. *)
      (* } *)

      (* { *)
      (*   clear GENC. *)
      (*   cbn. *)
      (*   intros x (? & ? & ? & ?). *)
      (*   intros [H1 H2]. *)
      (*   destruct x as [[mH []] | ?]; [| intuition]. *)
      (*   split; cbn; auto. *)
      (*   destruct H1; eauto. *)
      (*   admit. (* TODO: might have broken when adjusting meminv *) *)
      (*   admit. (* TODO: might have broken when adjusting meminv *) *)
      (* } *)

      (* { *)
      (*   (* Body correct *) *)
      (*   clear GENC. *)
      (*   intros * HPRE. *)
      (*   destruct a as [[mH[]] |]; cbn in HPRE; [| destruct HPRE as [abs _]; inv abs]. *)
      (*   break_match_goal. *)
      (*   - (* TODO: invariant that ~ k < n *) *)
      (*     exfalso. admit. *)
      (*   - hvred. *)
      (*     eapply eutt_mon. *)
      (*     2:eapply IHop. *)
      (*     2:eassumption. *)
      (*     { *)
      (*       intros [[?mH []] |] (? & ? & ? & ?) PRE'; cbn in PRE'; [| inv PRE']. *)
      (*       destruct PRE' as [SINV [? ->]] ; cbn in *. *)
      (*       split; [|split]; eauto. *)
      (*       (* TODO: add local_scope_modif to the postcondition of genIR *) *)
      (*       destruct HPRE as [SINVPRE LUPRE]. *)
      (*       match type of Heqs2 with *)
      (*       | genIR _ _ ?s1 ≡ inr (?s2, _) => *)
      (*         assert (local_scope_modif s1 s2 l2 a) *)
      (*       end. *)
      (*       admit. *)

      (*       { clear NOFAIL IHop. *)
      (*         rewrite <- LUPRE. *)
      (*         eapply local_scope_modif_out with (s1 := i0).  *)
      (*         3:eauto. *)
      (*         destruct i0; cbn; red; cbn; lia. *)
      (*         do 3 eexists; cbn; repeat split; eauto.  *)
      (*       }  *)
      (*       clean_goal. *)
      (*       rename i into s1, i0 into s2, s2 into s4, i3 into s3. *)
      (*       assert (l1 ≡ Γ s4) by admit. (* genWhileLoop_Γ *) *)
      (*       apply genIR_Context in Heqs2. *)
      (*       apply incBlockNamed_Γ in Heqs1. *)
      (*       cbn in *. *)
      (*       clear - Heqs2 Heql2 H SINV. *)
      (*       subst. *)
      (*       rewrite Heql2 in Heqs2. *)
      (*       inv Heqs2. *)
      (*       eapply state_invariant_escape_scope; eauto. *)
      (*     } *)
      (*     { *)
      (*       clear - Heqs1. *)
      (*       admit. *)
      (*     } *)
      (*     (* eapply state_invariant_enter_scope_DSHnat. *) *)
      (*     admit. *)
      (*     (* TODO: state_invariant stable by extension of both gamma and σ simultaneously *) *)
      (*     admit. *)
      (*     admit. *)
      (* } *)

      (* { *)
      (*   (* Rephrase this : really the invariant should be stable by modifications in [s1;s2] *) *)
      (*   admit. *)
      (* } *)
      (* { *)
      (*   intros ?; auto. *)
      (* } *)
      (* { *)
      (*   intros ?; auto. *)
      (* } *)
      (* { *)
      (*   admit. *)
      (* } *)
      (* *) 

    - (* DSHAlloc *)
      apply DSHAlloc_correct; auto. 


  (*   - admit. *)
  (*   - (* DSHSeq *) *)
  (*     Opaque add_comment. *)
  (*     cbn. *)

  (*     pose proof GEN as GEN_DESTRUCT. *)
  (*     cbn* in GEN_DESTRUCT; simp. *)

  (*     rename i into s_op1, l0 into bk_op1, l into bk_op2. *)
  (*     rename b into op2_entry, bid_in into op1_entry. *)
  (*     rename Heqs0 into GEN_OP2, Heqs2 into GEN_OP1. *)
  (*     rewrite add_comment_eutt. *)
  (*     cbn. *)
  (*     clean_goal. *)

  (*     rewrite convert_typ_ocfg_app. *)
  (*     rewrite denote_ocfg_app; eauto. *)
  (*     2: { *)
  (*       unfold no_reentrance. *)
  (*       pose proof GEN_OP1 as GEN_OP1'. *)

  (*       apply (inputs_not_earlier_bound _ _ _ NEXT) in GEN_OP1'. *)
  (*       apply inputs_bound_between in GEN_OP1. *)
  (*       apply outputs_bound_between in GEN_OP2. *)

  (*       pose proof (Forall_and GEN_OP1 GEN_OP1') as INPUTS. *)
  (*       cbn in INPUTS. *)

  (*       eapply (Forall_disjoint GEN_OP2 INPUTS). *)
  (*       intros x OUT_PRED [IN_BOUND IN_NEXT]. *)
  (*       destruct OUT_PRED as [OUT_PRED | OUT_PRED]; auto. *)
  (*       eapply (state_bound_between_separate incBlockNamed_count_gen_injective OUT_PRED IN_BOUND). *)
  (*       lia. auto. *)
  (*       block_count_replace. *)
  (*       lia. *)
  (*     } *)
  (*     hvred. *)

  (*     (* Helix generates code for op2 *first*, so op2 gets earlier *)
  (*       variables from the irstate. Helix needs to do this because it *)
  (*       passes the block id for the next block that an operator should *)
  (*       jump to when it's done executing... So it generates code for *)
  (*       op2, which goes to the next block of the entire sequence, and *)
  (*       then passes the entry point for op2 as the "nextblock" for *)
  (*       op1. *)
  (*     *) *)
  (*     cbn in *. *)
  (*     pose proof PRE as SINV. *)
  (*     simp. *)

  (*     rename Heqs0 into GEN_OP2, Heqs1 into GEN_OP1. *)

  (*     eapply eutt_clo_bind_returns. *)
  (*     { *)
  (*       eapply IHop1 with (s1:=s_op1) (s2:=s2); eauto. *)
  (*       - eapply bid_bound_genIR_entry; eauto. *)
  (*       - apply genIR_Context in GEN_OP2. *)
  (*         eapply state_invariant_Γ; eauto. *)
  (*       - eapply Gamma_safe_shrink; eauto. *)
  (*         eauto using genIR_Context. *)
  (*         solve_local_count. *)
  (*         solve_local_count. *)
  (*     } *)

  (*     clear IHop1. *)
  (*     introR; destruct_unit. *)
  (*     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET. *)
  (*     cbn in PRE0; destruct PRE0 as [INV2 [from2 BRANCH2]]; cbn in *; inv_eqs. *)
  (*     subst. *)

  (*     eapply eqit_mon; auto. *)
  (*     2: { *)
  (*       eapply IHop2; try exact GEN_OP2; eauto. *)
  (*       - eapply state_invariant_Γ; eauto. *)
  (*         apply genIR_Context in GEN_OP1; apply genIR_Context in GEN_OP2; rewrite GEN_OP2; auto. *)
  (*       - eapply Gamma_safe_shrink; eauto. *)
  (*         eauto using genIR_Context. *)
  (*         solve_local_count. *)
  (*         solve_local_count. *)
  (*     }           *)
  (*     clear IHop2. *)

  (*     intros [[memH1 ?]|] (memV1 & l1 & g1 & res1) PR; [| inv PR]. *)
  (*     destruct PR as [? [? BR]]. *)
  (*     cbn in *. *)

  (*     destruct res1 as [[from1 next] | v]; simp. *)

  (*     split; cbn; eauto. *)
  (*     eapply state_invariant_Γ; eauto. *)
  (*     apply genIR_Context in GEN_OP1; auto. *)

(*
    -
      Opaque genWhileLoop.
      cbn* in *.
      simp.
      unfold denotePExpr in *; cbn* in *.
      simp; try now (exfalso; clear -NOFAIL; try apply no_failure_Ret in NOFAIL; try_abs).
      apply no_failure_Ret in NOFAIL; simp; cbn in *; try_abs.
      hide_strings'.
      inv_resolve_PVar Heqs0.
      inv_resolve_PVar Heqs1.
      cbn* in *.
      simp.
      eutt_hide_right.
      repeat apply no_failure_Ret in NOFAIL.
      repeat (edestruct @no_failure_helix_LU as (? & NOFAIL' & ?); eauto; []; clear NOFAIL; rename NOFAIL' into NOFAIL; cbn in NOFAIL; eauto).
      rauto:L.
      all:eauto.
      Ltac rewrite_nth_error :=
        match goal with
        | h: nth_error _ _ ≡ _ |- _ => rewrite h
        end.
      Ltac rewrite_memory_lookup :=
        match goal with
        | h: memory_lookup _ _ ≡ _ |- _ => rewrite h
        end.
      subst; eutt_hide_left.
      Transparent genWhileLoop.
      cbn in *.
      simp.
      cbn in *.
      unfold add_comments; cbn.
      repeat rewrite fmap_list_app.
      cbn.
      match goal with
        |- context[denote_ocfg ?x] =>
        remember x as bks
      end.
(*
      erewrite denote_ocfg_unfold.
      2:{
        subst; cbn.
        clear.
        destruct (Eqv.eqv_dec_p bid_in bid_in) as [foo | foo].
        reflexivity.
        exfalso; apply foo; reflexivity.
      }
      Opaque find_block.
      cbn.
      norm_v.
      unfold IntType; rewrite typ_to_dtyp_I.
      cbn.
      focus_single_step_v; norm_v.
      cbn; norm_v.
      subst.
      norm_v.
      focus_single_step_v; norm_v.
      rewrite interp_cfg_to_L3_LW.
      cbn; norm_v.
      unfold endo.
      subst.
      repeat (norm_v; []).
      focus_single_step_v.
      (* onAllHyps move_up_types. *)
      unfold endo.
      focus_single_step_v.
      norm_v.
      2: apply lookup_alist_add_eq.
      cbn; norm_v.
      subst; cbn; norm_v.
      focus_single_step_v.
      (* Case analysis on whether we ever enter the loop or not *)
      unfold eval_int_icmp.
      cbn.
      break_match_goal.
      -- (* We enter the loop *)
        cbn; norm_v.
        subst; cbn; norm_v.
        rewrite find_block_ineq, find_block_eq.
        2: reflexivity.
        2:cbn; admit.
        norm_v.
        (* loopblock  *)
        rewrite denote_ocfg_unfold.
        2:{
          cbn.
          match goal with
            |- context[if ?p then true else false] =>
            destruct p as [EQ | INEQ]
          end.
          admit.
          match goal with
            |- context[if ?p then true else false] =>
            destruct p as [?EQ | ?INEQ]
          end.
          reflexivity.
          admit.
        }
*)
      (* Need to denote phis, I cannot denote the block directly :( *)
        admit.
      (* -- *)
      (*   (* from == to, we go from the entry block to the next one directly *) *)
      (*   cbn. *)
      (*   norm_v. *)
      (*   subst; cbn; norm_v. *)
      (*   repeat rewrite find_block_ineq. *)
      (*   2,3,4,5: cbn; admit. *)
      (*   cbn. *)
      (*   rewrite find_block_nil. *)
      (*   cbn; norm_v. *)
      (*   assert (n ≡ 0) by admit. *)
      (*   subst. *)
      (*   cbn; norm_h. *)
      (*   rewrite interp_Mem_MemSet. *)
      (*   norm_h. *)
      (*   apply eutt_Ret. *)
      (*   split; eauto. *)
      (*   { *)
      (*     admit. *)
      (*   } *)
      (*   { *)
      (*     admit. *)
      (*   } *)
    - (* DSHBinOp *)
      cbn* in *.
      simp.
      inv_resolve_PVar Heqs1.
      inv_resolve_PVar Heqs2.
      (* On the Helix side, the computation consists in:
         1. xi <- denotePExpr x
         2. yi <- denotePExpr y
         3. lookup xi in memory
         4. lookup yi in memory
         5. denoteDSHBinop on the values read
         6. write the result in memory at yi
       *)
      eutt_hide_right.
      rauto:L.
      subst; eutt_hide_left.
      unfold add_comments.
      cbn.
      match goal with
        |- context[denote_ocfg ?x] =>
        remember x as bks
      end.
      (* Lemma about while loop instead *)
      (* erewrite denote_ocfg_unfold. *)
      (* 2:{ *)
      (*   subst; cbn. *)
      (*   destruct (Eqv.eqv_dec_p bid_in bid_in).  *)
      (*   reflexivity. *)
      (*   exfalso. *)
      (*   apply n0. *)
      (*   reflexivity. *)
      (* } *)
      (* cbn. *)
      (* norm_v. *)
      (* unfold IntType; rewrite typ_to_dtyp_I. *)
      (* cbn. *)
      (* setoid_rewrite bind_ret_l. *)
      (* setoid_rewrite bind_ret_l. *)
      (* cbn. *)
      (* norm_v. *)
      (* rewrite interp_cfg_to_L3_LW. *)
      (* cbn*; norm_v. *)
      (* cbn*; norm_v. *)
      (* 2:{ *)
      (*   cbn. *)
      (*   unfold endo. *)
      (*   rewrite rel_dec_eq_true; eauto; typeclasses eauto. *)
      (* } *)
      (* cbn. *)
      (* unfold endo. *)
      (* unfold eval_int_icmp. *)
      (* cbn. *)
      (* focus_single_step_v. *)
      (* unfold Int64_eq_or_cerr, Z_eq_or_cerr, ErrorWithState.err2errS, Z_eq_or_err, memory_lookup_err in *. *)
      (* cbn* in *. *)
      (* simp. *)
      (* inv_resolve_PVar Heqs0. *)
      (* inv_resolve_PVar Heqs1. *)
      (* onAllHyps move_up_types.  *)
  (*     repeat match goal with *)
  (*            | h : Int64.intval _ ≡ Int64.intval _ |- _ => apply int_eq_inv in h; subst *)
  (*            end. *)
  (*     eutt_hide_left. *)
  (*     focus_single_step_v. *)
  (*     unfold MInt64asNT.from_nat in *. *)
  (*     rename n into index1. *)
  (*     break_if. *)
  (*     { *)
  (*       cbn. *)
  (*       norm_v. *)
  (*       subst. *)
  (*       cbn. *)
  (*       norm_v. *)
      admit.
    - (* DSHMemMap2 *) admit.
    - (* DSHPower *) admit.
    - (* DSHLoop *)
      Opaque genWhileLoop.
      Require Import Correctness_While.
      rewrite DSHLoop_interpreted_as_tfor.
      cbn* in *; simp.
      rewrite add_comment_eutt.
      (*
        sub_alist
       parameterized by some l_i
       start from l_i \subseteqeq_[s1;s2] l1
       end in l2 such that l2 | dom(l_i) ~~ l_i
        I l --> l ⊑ l' --> I l'
        forall l ⊑_[s1;s2] l',
        eutt op c
        gencode op s1 = (s2,c)
        pre: dom(l_i) ∩ [s1;s2] = nil
        {c}
        post: dom(l_f) \ dom(l_i) ⊆ [s1;s2]
       *)
      assert (IN: In b0 (block_ids l)).
      {
        (* Prpoerty of genIR *)
        admit.
      }
      assert (NOREPET: blk_id_norepet l0).
      {
        (* Prpoerty of genWhileLoop *)
        admit.
      }
      assert (FRESH: fresh_in_cfg l0 nextblock).
      {
        (* Property of? *)
        admit.
      }
      assert (NOTOVER: Z.of_nat n < Integers.Int64.modulus).
      {
        (* Property of no_failure of the source semantics, annoying to work with *)
        admit.
      }
      (* let (I := fun _ mH => *)
 (* nat → config_helix_OT () → memoryV * (alist raw_id uvalue * global_env) → Prop *)
      eapply eutt_mon; cycle 1.
      eapply (genWhileLoop_tfor_correct IN NOREPET FRESH _ Heqs4 _ NOTOVER).
      Unshelve.
      15:{
        refine (fun _ mh '(mv,(l,g)) =>
                  match mh with
                  | None => False
                  | Some mh => state_invariant σ s1 b mh _
                  end
               ).
        (*
          DSHLoop 2 ()
         *)
      admit.
      4: eassumption.
    
    - (* DSHMemInit *) admit.
    - (* DSHSeq *)
      cbn.
      pose proof GEN as GEN_DESTRUCT.
      cbn in GEN_DESTRUCT; simp.
      rename i into s_op1.
      rename l0 into bk_op1.
      rename l into bk_op2.
      rename b into op2_entry.
      rename bid_in into op1_entry.
      rename Heqs0 into GEN_OP2.
      rename Heqs2 into GEN_OP1.
      rewrite add_comment_eutt.
      cbn.
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
        eapply (Forall_disjoint GEN_OP2 INPUTS).
        intros x OUT_PRED [IN_BOUND IN_NEXT].
        destruct OUT_PRED as [OUT_PRED | OUT_PRED]; auto.
        eapply (state_bound_between_separate incBlockNamed_count_gen_injective OUT_PRED IN_BOUND).
        lia. auto.
        block_count_replace.
        lia.
      }
      rauto.
      (* Helix generates code for op2 *first*, so op2 gets earlier
        variables from the irstate. Helix needs to do this because it
        passes the block id for the next block that an operator should
        jump to when it's done executing... So it generates code for
        op2, which goes to the next block of the entire sequence, and
        then passes the entry point for op2 as the "nextblock" for
        op1.
      *)
      cbn in NOFAIL.
      pose proof BISIM as BISIM2.
      destruct BISIM as [[SINV (?from & EQ)] FRESH]; cbn in *; inv EQ.
      simp.
      rename Heqs0 into GEN_OP2.
      rename Heqs1 into GEN_OP1.
      eapply eutt_clo_bind_returns.
      {
        eapply IHop1 with (s1:=s_op1) (s2:=s2).
        - eapply bid_bound_genIR_entry; eauto.
        - split.
          + cbn.
            split.
            * cbn.
              apply genIR_Context in GEN_OP2.
              split.
              -- unfold memory_invariant.
                 rewrite <- GEN_OP2.
                 apply SINV.
              -- unfold WF_IRState.
                 rewrite <- GEN_OP2.
                 apply SINV.
              -- eapply no_id_aliasing_gamma; eauto.
                 eapply st_no_id_aliasing; eauto.
              -- eapply st_no_dshptr_aliasing; eauto.
              -- cbn in *.
                 eapply no_llvm_ptr_aliasing_gamma; eauto.
                 eapply st_no_llvm_ptr_aliasing in SINV. cbn in SINV.
                 eauto.
            * cbn. exists from.
              reflexivity.
          + cbn.
            solve_fresh.
        - eapply no_failure_helix_bind_prefix; eauto.
        - auto.
      }
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      cbn in PRE; destruct PRE as [[INV2 [from2 BRANCH2]] FRESH2]; cbn in *; inv_eqs.
      subst...
      eapply eqit_mon; auto.
      2: {
        eapply IHop2; eauto.
        destruct BISIM2 as [[SINV2 BRANCHES2] FRESHNESS2].
        cbn in SINV2, BRANCHES2, FRESHNESS2.
        split.
        - cbn.
          destruct SINV2.
          destruct INV2.
          split; cbn; auto.
          + split.
            * apply genIR_Context in GEN_OP2.
              apply genIR_Context in GEN_OP1.
              unfold memory_invariant.
              subst_contexts.
              cbn.
              apply mem_is_inv0.
            * apply SINV.
            * eapply st_no_id_aliasing; eauto.
            * eapply st_no_dshptr_aliasing; eauto.
            * (* TODO: turn this into a lemma *)
              cbn in st_no_llvm_ptr_aliasing0. cbn.
              unfold no_llvm_ptr_aliasing.
              assert (Γ s1 ≡ Γ s_op1) by (eapply genIR_Context; eauto).
              assert (Γ s_op1 ≡ Γ s2) by (eapply genIR_Context; eauto).
              assert (Γ s1 ≡ Γ s2) by congruence.
              rewrite H1.
              apply st_no_llvm_ptr_aliasing0.
          + exists from2. reflexivity.
        - cbn.
          (* TODO: make solve_fresh do this *)
          (* Nothing in ρ is bound between s1 and s2 *)
          unfold freshness_pre in FRESHNESS2.
          (* Everything new in l is bound between s_op1 and s2... *)
          unfold freshness_post in FRESH2.
          (* This is consistent so far... *)
          unfold freshness_pre.
          intros id v H.
          destruct (alist_In_dec id ρ v) as [AIN | ANIN].
          + pose proof (FRESHNESS2 _ _ AIN) as NBOUND.
            intros CONTRA.
            apply NBOUND.
            eapply state_bound_between_shrink; eauto.
            solve_local_count.
          + pose proof (FRESH2 _ _ H ANIN) as BOUND2.
            intros BOUND1.
            eapply (state_bound_between_id_separate incLocalNamed_count_gen_injective BOUND1 BOUND2).
            auto.
      }
      intros [[memH1 ?]|] (memV1 & l1 & g1 & res1) PR.
      2: {
        inversion PR.
      }
      destruct res1 as [[from1 next] | v].
      2: {
        destruct PR as [[? [? BR]] ?].
        inversion BR.
      }
      cbn in PR. destruct PR as [[SINV1 BRANCHES1] FRESH1].
      cbn.
      split; auto.
      cbn. cbn in SINV1.
      destruct SINV1 as [MINV1 WF1].
      destruct INV2 as [MINV2 WF2].
      split.
      split.
      + cbn.
        apply genIR_Context in GEN_OP1.
        rewrite <- GEN_OP1.
        apply MINV1.
      + auto.
      + eapply no_id_aliasing_gamma; eauto.
        eapply genIR_Context; eauto.
      + eauto.
      + eapply no_llvm_ptr_aliasing_gamma; eauto.
        eapply genIR_Context; eauto.
      + cbn. cbn in BRANCHES1.
        destruct BRANCHES1 as [from1' BRANCHES1].
        exists from1. inversion BRANCHES1.
        reflexivity.
      + cbn in *.
        unfold freshness_post in *.
        intros id v AIN ANIN.
        destruct (alist_In_dec id l v) as [AINL | ANINL].
        * pose proof (FRESH2 _ _ AINL ANIN).
          eapply state_bound_between_shrink; eauto.
          apply genIR_local_count in GEN_OP2; lia.
        * pose proof (FRESH1 _ _ AIN ANINL).
          eapply state_bound_between_shrink; eauto.
          apply genIR_local_count in GEN_OP1; lia. *)

  Admitted.


  End GenIR.
