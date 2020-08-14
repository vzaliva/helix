Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.
Require Import Helix.LLVMGen.Correctness_MExpr.

Set Implicit Arguments.
Set Strict Implicit.

Lemma resolve_PVar_simple : forall p s s' x v,
    resolve_PVar p s ≡ inr (s', (x, v)) ->
    exists sz n,
      nth_error (Γ s') n ≡ Some (x, TYPE_Pointer (TYPE_Array sz TYPE_Double)) /\
      MInt64asNT.from_Z sz ≡ inr v /\ p ≡ PVar n /\ s ≡ s'.
Proof.
  intros * H.
  unfold resolve_PVar in H.
  cbn* in H.
  simp.
  do 2 eexists; eauto.
Qed.

Ltac inv_resolve_PVar H :=
  apply resolve_PVar_simple in H;
  destruct H as (?sz & ?n & ?LUn & ?EQsz & -> & <-).

Global Opaque resolve_PVar.

Axiom int_eq_inv: forall a b, Int64.intval a ≡ Int64.intval b -> a ≡ b.

  Section GenIR.


  Definition branches (mh : memoryH * ()) (c : config_cfg_T (block_id * block_id + uvalue)) : Prop :=
    match c with
    | (m,(l,(g,res))) => exists bids, res ≡ inl bids
    end.

  Definition GenIR_Rel σ Γ : Rel_cfg_T unit ((block_id * block_id) + uvalue) :=
    lift_Rel_cfg (state_invariant σ Γ) ⩕ branches.

  Opaque denote_code.
 Lemma compile_FSHCOL_correct :
    forall (** Compiler bits *) (s1 s2: IRState)
      (** Helix bits    *) (op: DSHOperator) (σ : evalContext) (memH : memoryH) fuel v
      (** Vellvm bits   *) (nextblock bid_in bid_from : block_id) (bks : list (LLVMAst.block typ))
      (* (env : list (ident * typ)) *)  (g : global_env) (ρ : local_env) (memV : memoryV),
      nextblock ≢ bid_in -> (* YZ: not sure about this yet *)
      GenIR_Rel σ s1 (memH,tt) (memV, (ρ, (g, (inl (bid_from, bid_in))))) ->
      evalDSHOperator σ op memH fuel ≡ Some (inr v)            -> (* Evaluation succeeds *)
      genIR op nextblock s1 ≡ inr (s2,(bid_in,bks)) ->
      eutt (GenIR_Rel σ s1)
           (with_err_RB
              (interp_Mem (denoteDSHOperator σ op) memH))
           (with_err_LB
              (interp_cfg (D.denote_bks (convert_typ [] bks) (bid_from,bid_in))
                                g ρ memV)).
 Proof.
    intros s1 s2 op; revert s1 s2; induction op; intros * NEXT BISIM EVAL GEN.
    - cbn* in GEN.
      simp.
      hide_strings'.
      cbn*; norm_h.
      rewrite denote_bks_nil.
      cbn*; norm_v.
      apply eqit_Ret; auto.

    - (* Assign case.
         Helix side:
         1. x_i <- evalPExpr σ x_p ;;
         2. y_i <- evalPExpr σ y_p ;;
         3. x <- memory_lookup_err "Error looking up 'x' in DSHAssign" mem x_i ;;
         4. y <- memory_lookup_err "Error looking up 'y' in DSHAssign" mem y_i ;;
         5. src <- evalNExpr σ src_e ;;
         6. dst <- evalNExpr σ dst_e ;;
         7. v <- mem_lookup_err "Error looking up 'v' in DSHAssign" (to_nat src) x ;;
         8. ret (memory_set mem y_i (mem_add (to_nat dst) v y))
       *)

      destruct fuel as [| fuel]; [cbn in *; simp |].
      cbn* in GEN.
      unfold GenIR_Rel in BISIM; cbn in BISIM.
      destruct BISIM as [BISIM1 BISIM2].
      simp.
      hide_strings'.
      rename i into si, i2 into si',
      i0 into x, i3 into y,
      i1 into v1, i4 into v2.
      inv_resolve_PVar Heqs0.
      inv_resolve_PVar Heqs1.

      eutt_hide_right.
      cbn*.
      rename n1 into x_p, n2 into y_p.

      norm_h.
      unfold denotePExpr; cbn*.
      break_inner_match_goal; cbn* in *; simp.
      eutt_hide_right.
      rename m into x_i, m0 into y_i.

      norm_h.
      2,3:cbn*; apply memory_lookup_err_inr_Some_eq; eauto.

      subst; eutt_hide_left.
      unfold add_comments.
      cbn*.
      rewrite denote_bks_unfold_in; eauto.
      2: rewrite find_block_eq; reflexivity.
      cbn*.
      repeat rewrite fmap_list_app.
      norm_v.
      cbn.
      norm_v.
      rewrite denote_code_app.
      norm_v.
      subst.
      focus_single_step.
      rename x into x_p', y into y_p'.
      rename m1 into x, m2 into y.
      rename n into src_e, n0 into dst_e.
      rename b into v.

      (* Step 5. *)
      eapply eutt_clo_bind.
      eapply genNExpr_correct; try eassumption.
      do 3 (eapply state_invariant_incLocal; eauto).
      do 2 (eapply state_invariant_incVoid; eauto).
      do 1 (eapply state_invariant_incBlockNamed; eauto).

      intros [memH1 src] (memV1 & ρ1 & g1 & []) (INV1 & (EXP1 & <- & <- & <- & MONO1) & GAMMA1); cbn* in *.

      subst.

      rewrite denote_code_app.
      norm_v.
      norm_h.
      focus_single_step.

      (* Step 6. *)
      eapply eutt_clo_bind.
      eapply genNExpr_correct; eauto.

      intros [memH2 dst] (memV2 & ρ2 & g2 & []) (INV2 & (EXP2 & <- & <- & <- & MONO2) & GAMMA2); cbn in GAMMA2; cbn in INV2.
      subst.

      (* Step 7. *)
      eutt_hide_right.

      edestruct EXP1 as (EQ1 & EQ1'); [reflexivity |].
      rewrite EQ1' in Heqs11; inv Heqs11.
      rewrite Heqo0.
      eutt_hide_right.

      assert (i2 ≡ dst).
      { unfold genNExpr_exp_correct in EXP2.
        assert (ρ2 ⊑ ρ2) as LL by reflexivity.
        specialize (EXP2 _ LL) as (EXP2_EUTT & EXP2_EVAL).
        rewrite EXP2_EVAL in Heqs12.
        inversion Heqs12.
        auto.
      }
      subst.

      Set Nested Proofs Allowed.
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

      rewrite (assert_NT_lt_success Heqs13). 
      cbn*.
      norm_h.
      rewrite interp_Mem_MemSet.
      cbn*.
      norm_h.

      subst; eutt_hide_left.

      simpl.
      norm_v.
      norm_v.
      focus_single_step_v.
      cbn.
      norm_v.
      (* I am looking up an ident x, for which I find the type `TYPE_Pointer (TYPE_Array sz TYPE_Double)`
         in my typing context.
         Can it be a global?
       *)

      (* onAllHyps move_up_types. *)
      subst; focus_single_step_v; eutt_hide_left.
      unfold endo, Endo_ident.

      destruct x_p' as [x_p' | x_p']; [admit |];
        destruct y_p' as [y_p' | y_p']; cbn; [admit |].
      subst; focus_single_step_v; eutt_hide_left.
      edestruct memory_invariant_LLU_Ptr as (bk_x & ptr_x & LUx & INLGx & VEC_LUx); [| exact LUn | exact Heqo |]; eauto.
      rewrite LUx in Heqo2; symmetry in Heqo2; inv Heqo2.
      edestruct memory_invariant_LLU_Ptr as (bk_y & ptr_y & LUy & INLGy & VEC_LUy); [| exact LUn0 | eassumption |]; eauto.
      rewrite LUy in Heqo1; symmetry in Heqo1; inv Heqo1.

      focus_single_step_v; norm_v.
      admit.
    (*   2: apply MONO2, MONO1; eauto. *)
    (*   cbn; norm_v. *)
    (*   subst; focus_single_step_v; norm_v. *)
    (*   unfold IntType; rewrite typ_to_dtyp_I; cbn. *)
    (*   subst; focus_single_step_v; norm_v. *)
    (*   subst; focus_single_step_v; norm_vD. *)
    (*   focus_single_step_v. *)

    (*   destruct (EXP1 ρ2) as [EQe ?]; auto. *)
    (*   rewrite <- EQe. *)
    (*   norm_v. *)
    (*   subst; focus_single_step_v; norm_vD. *)
    (*   cbn. *)

    (*   rename i into index, v1 into size_array. *)
    (*   unfold ITree.map. *)
    (*   norm_v. *)

    (*   rewrite exp_E_to_instr_E_Memory, subevent_subevent. *)
    (*   rewrite typ_to_dtyp_D_array. *)

    (*   cbn in *. *)

    (*   (* onAllHyps move_up_types. *) *)

    (*   match goal with *)
    (*     |- context[interp_cfg_to_L3 ?defs (@ITree.trigger ?E _ (subevent _ (GEP (DTYPE_Array ?size ?t) (DVALUE_Addr ?a) _)))] => *)
    (*     edestruct (@interp_cfg_to_L3_GEP_array defs t a size g ρ2) as (add & ?EQ & READ); eauto *)
    (*   end. *)

    (*   assert (EQindex: Integers.Int64.repr (Z.of_nat (MInt64asNT.to_nat index)) ≡ index) by admit. *)
    (*   rewrite EQindex in *. *)
    (*   rewrite EQ. *)

    (*   norm_v. *)
    (*   cbn. *)
    (*   subst; cbn; norm_v. *)
    (*   focus_single_step_v. *)
    (*   rewrite interp_cfg_to_L3_LW. *)
    (*   cbn*; norm_v. *)
    (*   subst; simpl; norm_v. *)
    (*   focus_single_step_v. *)
    (*   cbn; norm_v. *)
    (*   subst; cbn; norm_v. *)
    (*   focus_single_step_v. *)

    (*   2: apply lookup_alist_add_eq. *)
    (*   cbn*; norm_v. *)
    (*   subst; cbn; norm_v; focus_single_step_v. *)
    (*   rewrite interp_cfg_to_L3_Load. *)
    (*   2: rewrite typ_to_dtyp_D; eassumption. *)
    (*   norm_v. *)
    (*   subst; cbn; norm_v; focus_single_step_v. *)
    (*   rewrite interp_cfg_to_L3_LW. *)
    (*   cbn; norm_v. *)
    (*   subst; cbn; norm_v. *)

    (*   2:{ *)
    (*     unfold endo. *)
    (*     assert (y_p' <> r1) by admit. *)
    (*     assert (y_p' <> r) by admit. *)
    (*     setoid_rewrite lookup_alist_add_ineq; eauto. *)
    (*     setoid_rewrite lookup_alist_add_ineq; eauto. *)
    (*     cbn in *. *)
    (*     apply MONO2, MONO1; eauto. *)
    (*   } *)
    (*   cbn. *)
    (*   subst. *)
    (*   unfold IntType;rewrite !typ_to_dtyp_I. *)
    (*   focus_single_step_v; norm_v. *)
    (*   subst; cbn; norm_v. *)
    (*   focus_single_step_v. *)

    (*   match goal with *)
    (*     |- eutt _ _ (ITree.bind (_ (interp_cfg _ _ ?l _)) _) => destruct (EXP2 l) as [EQe' ?]; auto *)
    (*   end. *)
    (*   rewrite <- sub_alist_add. *)
    (*   apply sub_alist_add. *)
    (*   rename r into foo. *)
    (*   (* Freshness, easy todo *) *)
    (*   admit. *)
    (*   admit. *)

    (*   rewrite <- EQe'. *)
    (*   norm_v. *)
    (*   subst; cbn*; norm_v. *)
    (*   focus_single_step_v. *)
    (*   norm_v; subst; focus_single_step_v. *)
    (*   norm_v; subst; focus_single_step_v. *)
    (*   cbn; unfold ITree.map. *)
    (*   norm_v; subst; focus_single_step_v. *)
    (*   rewrite exp_E_to_instr_E_Memory, subevent_subevent. *)
    (*   rewrite typ_to_dtyp_D_array. *)

    (*   Set Hyps Limit 50. *)

    (*   (* Need another GEP lemma? *)
    (*      The destination is not read on the Helix side, so that I do not know that the GEP succeeds *)
    (*    *) *)

    (*   (* *)
    (*   match goal with *)
    (*     |- context[interp_cfg_to_L3 ?defs (@ITree.trigger ?E _ (subevent _ (GEP (DTYPE_Array ?size ?t) (DVALUE_Addr ?a) _))) ?g ?l] => *)
    (*     edestruct (@interp_cfg_to_L3_GEP_array defs t a size g l) as (add' & ?EQ & READ'); eauto *)
    (*   end. *)

    (*   eapply VEC_LUy. *)
    (*    *) *)

    (*     admit. *)
    (* (* End of genFSHAssign, things are getting a bit complicated *) *)



    - destruct fuel as [| fuel]; [cbn in *; simp |].

      Opaque genWhileLoop.
      cbn* in GEN.
      unfold GenIR_Rel in BISIM; cbn in BISIM.
      simp.
      hide_strings'.
      inv_resolve_PVar Heqs0.
      inv_resolve_PVar Heqs1.
      cbn* in *.
      simp.
      (* Require Import LibHyps.LibHyps. *)
      (* onAllHyps move_up_types. *)

      eutt_hide_right.

      norm_h.
      unfold denotePExpr; cbn*.

      Ltac rewrite_nth_error :=
        match goal with
        | h: nth_error _ _ ≡ _ |- _ => rewrite h
        end.

      Ltac rewrite_memory_lookup :=
        match goal with
        | h: memory_lookup _ _ ≡ _ |- _ => rewrite h
        end.

      do 2 rewrite_nth_error.

      repeat (norm_h; []).
      norm_h.
      2: cbn*; rewrite_memory_lookup; reflexivity.

      norm_h.
      2: cbn*; rewrite_memory_lookup; reflexivity.

      subst; eutt_hide_left.
      Transparent genWhileLoop.
      cbn in *.
      simp.
      cbn in *.
      unfold add_comments; cbn.
      repeat rewrite fmap_list_app.
      cbn.


      match goal with
        |- context[denote_bks ?x] =>
        remember x as bks
      end.

(*      
      erewrite denote_bks_unfold.
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
        rewrite denote_bks_unfold.
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
      destruct fuel as [| fuel]; [cbn in *; simp |].
      cbn* in GEN.
      unfold GenIR_Rel in BISIM; cbn in BISIM.
      unfold ErrorWithState.err2errS in *.
      repeat (break_inner_match_hyp; cbn in *; repeat inv_sum; []).
      repeat match goal with
      | h: _ * _ |- _ => destruct h
      | h: () |- _ => destruct h
      end.
      repeat match goal with
      | h: (_,_) ≡ (_,_) |- _ => inv h
             end.
      cbn* in *.

      (* On the Helix side, the computation consists in:
         1. xi <- denotePExpr x
         2. yi <- denotePExpr y
         3. lookup xi in memory
         4. lookup yi in memory
         5. denoteDSHBinop on the values read
         6. write the result in memory at yi
       *)
      eutt_hide_right.
      norm_h.

     subst; eutt_hide_left.

      unfold add_comments.
      cbn.
      match goal with
        |- context[denote_bks ?x] =>
        remember x as bks
      end.

      (* Lemma about while loop instead *)
      (* erewrite denote_bks_unfold. *)
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
    - (* DSHLoop *) admit.
    - (* DSHAlloc *) admit.
    - (* DSHMemInit *) admit.
    - (* DSHSeq *)
      cbn.

      cbn in GEN.
      break_match_hyp; inversion GEN.
      break_match_hyp; inversion GEN.
      inversion Heqs.

      destruct p0, s.
      break_match_hyp; inversion Heqs.
      destruct p0, s.
      subst. cbn in *.
      inversion H2.

      Lemma add_comment_eutt :
        forall comments bks ids,
          denote_bks (convert_typ [] (add_comment bks comments)) ids ≈ denote_bks (convert_typ [] bks) ids.
      Proof.
        intros comments bks ids.
        induction bks.
        - cbn. reflexivity.
        - destruct ids as (bid_from, bid_src); cbn.
          match goal with
          | |- context[denote_bks ?bks (_, ?bid_src)] =>
            destruct (find_block dtyp bks bid_src) eqn:FIND
          end.
      Admitted.

      rewrite add_comment_eutt.

      Check ITree.bind _ _.

      (* Move these *)
      (* Kind of wonder if these should be traversals *)
      Definition bks_labels {t} (bks : list (LLVMAst.block t)) : list block_id
        := fmap blk_id bks.

      Definition terminator_targets {t} (term : LLVMAst.terminator t) : list block_id
        := match term with
           | TERM_Ret v => []
           | TERM_Ret_void => []
           | TERM_Br v br1 br2 => [br1; br2]
           | TERM_Br_1 br => [br]
           | TERM_Switch v default_dest brs => default_dest :: fmap snd brs
           | TERM_IndirectBr v brs => brs
           | TERM_Resume v => []
           | TERM_Invoke fnptrval args to_label unwind_label => [to_label; unwind_label]
           end.
      
      Definition bks_targets {t} (bks : list (LLVMAst.block t)) : list block_id
        := fold_left (fun acc bk => terminator_targets (snd (blk_term bk)) ++ acc) bks [].

      Lemma find_none_app:
        forall {A} (l1 l2 : list A) pred,
          find pred l1 ≡ None ->
          find pred (l1 ++ l2) ≡ find pred l2.
      Proof.
        induction l1; intros l2 pred FIND.
        - reflexivity.
        - cbn in FIND; cbn.
          destruct (pred a); inversion FIND.
          auto.
      Qed.

      Lemma find_some_app:
        forall {A} (l1 l2 : list A) a pred,
          find pred l1 ≡ Some a ->
          find pred (l1 ++ l2) ≡ Some a.
      Proof.
        induction l1 as [|x l1']; intros l2 a pred FIND.
        - inversion FIND.
        - cbn in FIND. destruct (pred x) eqn:PRED.
          + inversion FIND; cbn; subst.
            rewrite PRED. reflexivity.
          + cbn. rewrite PRED.
            auto.
      Qed.

      Lemma find_block_none_app:
        forall {t} l1 l2 bid,
          find_block t l1 bid ≡ None ->
          find_block t (l1 ++ l2) bid ≡ find_block t l2 bid.
      Proof.
        intros t l1 l2 bid FIND.
        apply find_none_app; auto.
      Qed.

      Lemma find_block_some_app:
        forall {t} l1 l2 bid bk,
          find_block t l1 bid ≡ Some bk ->
          find_block t (l1 ++ l2) bid ≡ Some bk.
      Proof.
        intros t l1 l2 bid bk FIND.
        apply find_some_app; auto.
      Qed.
      
      Lemma denote_bks_app_no_edges :
        forall l1 l2 fto,
          find_block dtyp l1 (snd fto) ≡ None ->
          (forall bk, In bk (bks_targets l2) -> ~ In bk (bks_labels l1)) ->
          denote_bks (l1 ++ l2) fto ≈ denote_bks l2 fto.
      Proof.
        intros l1 l2 [f to] FIND NOBACK.
        cbn in FIND.
        epose proof (find_block_none_app _ l2 _ FIND) as FIND_L1L2.
        destruct (find_block dtyp l2 to) eqn:FIND_L2.
        - rewrite denote_bks_unfold_in; eauto.
          rewrite denote_bks_unfold_in; eauto.
          eapply eutt_clo_bind.
          + reflexivity.
          + intros u1 u2 H.
            subst. destruct u2; try reflexivity.
            admit.
        - rewrite denote_bks_unfold_not_in; auto.
          rewrite denote_bks_unfold_not_in; auto.
          reflexivity.
      Admitted.

      Lemma denote_bks_app :
        forall l1 l2 fto,
          (* No edges from l2 to l1 *)
          (forall bk, In bk (bks_targets l2) -> ~ In bk (bks_labels l1)) ->
          denote_bks (l1 ++ l2) fto ≈ ITree.bind (denote_bks l1 fto)
                                       (fun x =>
                                          match x with
                                          | inl fto2 => denote_bks l2 fto2
                                          | inr v => ret (inr v)
                                          end).
      Proof.
        intros l1 l2 [f to] NOBACK.
        destruct (find_block dtyp l1 to) eqn:FIND.
        - pose proof denote_bks_unfold_in l1 f to b FIND as EQ.
          pose proof find_block_some_app l1 l2 to FIND as FIND_APP.

          rewrite denote_bks_unfold_in; eauto.
          rewrite denote_bks_unfold_in; eauto.

          cbn.
          repeat setoid_rewrite bind_bind.

          (* denote_phis *)
          eapply eutt_clo_bind; try reflexivity.
          intros u1 u2 H; subst.

          (* Writing phis *)
          eapply eutt_clo_bind; try reflexivity.
          intros u1 u0 H; subst.
          repeat rewrite bind_ret_l.

          (* denote_code *)
          eapply eutt_clo_bind; try reflexivity.
          intros u1 u3 H; subst.

          (* denote_terminator *)
          Definition branch_not_in {t} (r : block_id + uvalue) (l : list (LLVMAst.block t)) : Prop :=
            match r with
            | inl bid => find_block t l bid ≡ None
            | _ => True
            end.
          
          Definition branch_out {t} (l : list (LLVMAst.block t)) (r1 : block_id + uvalue) (r2 : block_id + uvalue) : Prop :=
            r1 ≡ r2 /\ branch_not_in r1 l.

          eapply eutt_clo_bind with (UU:=branch_out l1).
          { destruct (blk_term b) as [i t] eqn:TERM.
            (* destruct t. *)
            (* - cbn. *)
            (*   Transparent denote_terminator. *)


            eapply eqit_mon with (RR:=Logic.eq); intuition.
            unfold branch_out. intuition.
            cbn.
            admit. admit.
          }

          intros term' term [EQT BOUT]; subst.
          destruct term as [branch_to | retv].
          + (* b0 not in l1 due to bailing out of iter *)
            assert (find_block dtyp l1 branch_to ≡ None) as FIND_B0.
            admit.

            rewrite denote_bks_app_no_edges; eauto.

            rewrite (denote_bks_unfold_not_in l1); eauto.
            rewrite bind_ret_l.

            reflexivity.
          + rewrite bind_ret_l.
            reflexivity.
        - rewrite denote_bks_app_no_edges; eauto.

          rewrite (denote_bks_unfold_not_in l1); eauto.
          rewrite bind_ret_l.

          reflexivity.
      Admitted.

      cbn.

      Lemma convert_typ_block_app : forall (a b : list (LLVMAst.block typ)) env, (convert_typ env (a ++ b) ≡ convert_typ env a ++ convert_typ env b)%list.
      Proof.
        induction a as [| [] a IH]; cbn; intros; auto.
        rewrite IH; reflexivity.
      Qed.

      rewrite convert_typ_block_app.
      rewrite denote_bks_app; eauto.
      2: admit. (* TODO: should hold from compilation *)

      repeat norm_h.
      repeat norm_v.

      Lemma evalDSHSeq_split :
        forall {fuel σ op1 op2 mem mem''},
          evalDSHOperator σ (DSHSeq op1 op2) mem fuel ≡ Some (inr mem'') ->
          exists mem', evalDSHOperator σ op1 mem fuel ≡ Some (inr mem') /\
                  evalDSHOperator σ op2 mem' fuel ≡ Some (inr mem'').
      Proof.
        induction fuel;
          intros σ op1 op2 mem mem'' EVAL.
        - inversion EVAL.
        - cbn in EVAL.
          break_match_hyp; try break_match_hyp; inversion EVAL.
          exists m. split.
          * apply evalDSHOperator_fuel_monotone; auto.
          * erewrite evalDSHOperator_fuel_monotone; eauto.
      Qed.

      pose proof (evalDSHSeq_split EVAL) as [mem' [EVAL1 EVAL2]].

      subst.
      eapply eutt_clo_bind.
      { eapply (IHop1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EVAL1 Heqs1).
        Unshelve.
        admit.

        (* TODO: :(((( *)
        (* This one is annoying. Need to apply IHop1 to get GenIR_Rel
        of i... But need it to apply. Grrrr *)
        admit.
      }

      intros [u1 []] (u2 & le & ge & res) IRREL.
      pose proof IRREL as [STATE [[from to] BRANCH]].

      (* TODO: How can I know this? *)
      (* Probably need to extend GenIR_Rel? *)
      assert (b ≡ to). admit. subst.

      (* TODO: Need to match u1 up with mem' somehow *)
      assert (u1 ≡ mem').
      { epose proof (IHop1 _ _ σ memH _ _ _ bid_in from _ ge le u2 _ _ EVAL1 Heqs1) as IH.
        cbn in STATE.
        apply state_invariant_memory_invariant in STATE.
        admit.
      }
      subst.

      epose proof (IHop2 _ _ σ mem' _ _ _ to from _ ge le u2 _ _ EVAL2 Heqs0) as IH.
      apply IH.
  Admitted.
  End GenIR.


