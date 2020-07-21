Require Import Coq.Arith.Arith.
Require Import Psatz.

Require Import Coq.Strings.String.

Open Scope string_scope.
Open Scope char_scope.

Require Import Coq.Lists.List.

Require Import Coq.Numbers.BinNums. (* for Z scope *)
Require Import Coq.ZArith.BinInt.

Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.FSigmaHCOL.Int64asNT.
Require Import Helix.FSigmaHCOL.Float64asCT.
Require Import Helix.DSigmaHCOL.DSigmaHCOLITree.
Require Import Helix.LLVMGen.Compiler.
Require Import Helix.LLVMGen.Externals.
Require Import Helix.LLVMGen.Data.
Require Import Helix.LLVMGen.Utils.
Require Import Helix.LLVMGen.tmp_aux_Vellvm.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.Util.ErrorSetoid.
Require Import Helix.Util.ListUtil.
Require Import Helix.Tactics.HelixTactics.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Map.FMapAList.

Require Import Vellvm.Tactics.
Require Import Vellvm.Util.
Require Import Vellvm.LLVMEvents.
Require Import Vellvm.DynamicTypes.
Require Import Vellvm.Denotation.
Require Import Vellvm.Handlers.Handlers.
Require Import Vellvm.TopLevel.
Require Import Vellvm.LLVMAst.
Require Import Vellvm.CFG.
Require Import Vellvm.InterpreterMCFG.
Require Import Vellvm.InterpreterCFG.
Require Import Vellvm.TopLevelRefinements.
Require Import Vellvm.TypToDtyp.
Require Import Vellvm.LLVMEvents.
Require Import Vellvm.Denotation_Theory.

Require Import Ceres.Ceres.

Require Import ITree.Interp.TranslateFacts.
Require Import ITree.Basics.CategoryFacts.
Require Import ITree.Events.State.
Require Import ITree.Events.StateFacts.
Require Import ITree.ITree.
Require Import ITree.Eq.Eq.
Require Import ITree.Basics.Basics.
Require Import ITree.Interp.InterpFacts.

Require Import Flocq.IEEE754.Bits.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.misc.decision.

Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.
Require Import Helix.LLVMGen.Correctness_MExpr.

Set Implicit Arguments.
Set Strict Implicit.

Import MDSHCOLOnFloat64.
Import D.
Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

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


  Definition GenIR_Rel σ Γ : Rel_cfg_T unit ((block_id * block_id) + uvalue) :=
    lift_Rel_cfg (state_invariant σ Γ).

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
   (** 

    intros s1 s2 op; revert s1 s2; induction op; intros * NEXT BISIM EVAL GEN.
    - cbn* in GEN.
      simp.
      hide_strings'.
      cbn*; repeat norm_h.
      rewrite denote_bks_nil.
      cbn*; repeat norm_v.
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

      repeat norm_h.
      unfold denotePExpr; cbn*.
      break_inner_match_goal; cbn* in *; simp.
      eutt_hide_right.
      rename m into x_i, m0 into y_i.

      repeat norm_h.
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
      repeat norm_v.
      rewrite translate_ret. _ret_l.
      rewrite denote_code_app.
      repeat norm_v.
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
      repeat norm_v.
      repeat norm_h.
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
      (*
      assert (i2 ≡ val2).
      { unfold genNExpr_exp_correct in EXP2.
        assert (ρ2 ⊑ ρ2) as LL by reflexivity.
        specialize (EXP2 _ LL) as (EXP2_EUTT & EXP2_EVAL).
        rewrite EXP2_EVAL in Heqs12.
        inversion Heqs12.
        auto.
      }
      subst.
      rewrite Heqs13.
      cbn*.
      repeat norm_h.
      rewrite interp_Mem_MemSet.
      cbn*.
      repeat norm_h.

      subst; eutt_hide_left.

      simpl.
      norm_v.
      norm_v.
      focus_single_step_v.
      cbn.
      repeat norm_v.
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

      focus_single_step_v; repeat norm_v.
      2: apply MONO2, MONO1; eauto.
      cbn; repeat norm_v.
      subst; focus_single_step_v; repeat norm_v.
      unfold IntType; rewrite typ_to_dtyp_I; cbn.
      subst; focus_single_step_v; repeat norm_v.
      subst; focus_single_step_v; repeat norm_vD.
      focus_single_step_v.

      destruct (EXP1 ρ2) as [EQe ?]; auto.
      rewrite <- EQe.
      repeat norm_v.
      subst; focus_single_step_v; repeat norm_vD.
      cbn.

      rename i into index, v1 into size_array.
      unfold ITree.map.
      repeat norm_v.

      rewrite exp_E_to_instr_E_Memory, subevent_subevent.
      rewrite typ_to_dtyp_D_array.

      cbn in *.

      (* onAllHyps move_up_types. *)

      match goal with
        |- context[interp_cfg_to_L3 ?defs (@ITree.trigger ?E _ (subevent _ (GEP (DTYPE_Array ?size ?t) (DVALUE_Addr ?a) _)))] =>
        edestruct (@interp_cfg_to_L3_GEP_array defs t a size g ρ2) as (add & ?EQ & READ); eauto
      end.

      assert (EQindex: Integers.Int64.repr (Z.of_nat (MInt64asNT.to_nat index)) ≡ index) by admit.
      rewrite EQindex in *.
      rewrite EQ.

      repeat norm_v.
      cbn.
      subst; cbn; repeat norm_v.
      focus_single_step_v.
      rewrite interp_cfg_to_L3_LW.
      cbn*; repeat norm_v.
      subst; simpl; repeat norm_v.
      focus_single_step_v.
      cbn; repeat norm_v.
      subst; cbn; repeat norm_v.
      focus_single_step_v.

      2: apply lookup_alist_add_eq.
      cbn*; repeat norm_v.
      subst; cbn; repeat norm_v; focus_single_step_v.
      rewrite interp_cfg_to_L3_Load.
      2: rewrite typ_to_dtyp_D; eassumption.
      repeat norm_v.
      subst; cbn; repeat norm_v; focus_single_step_v.
      rewrite interp_cfg_to_L3_LW.
      cbn; repeat norm_v.
      subst; cbn; repeat norm_v.

      2:{
        unfold endo.
        assert (y_p' <> r1) by admit.
        assert (y_p' <> r) by admit.
        setoid_rewrite lookup_alist_add_ineq; eauto.
        setoid_rewrite lookup_alist_add_ineq; eauto.
        cbn in *.
        apply MONO2, MONO1; eauto.
      }
      cbn.
      subst.
      unfold IntType;rewrite !typ_to_dtyp_I.
      focus_single_step_v; repeat norm_v.
      subst; cbn; repeat norm_v.
      focus_single_step_v.

      match goal with
        |- eutt _ _ (ITree.bind (_ (interp_cfg _ _ ?l _)) _) => destruct (EXP2 l) as [EQe' ?]; auto
      end.
      rewrite <- sub_alist_add.
      apply sub_alist_add.
      rename r into foo.
      (* Freshness, easy todo *)
      admit.
      admit.

      rewrite <- EQe'.
      repeat norm_v.
      subst; cbn*; repeat norm_v.
      focus_single_step_v.
      repeat norm_v; subst; focus_single_step_v.
      repeat norm_v; subst; focus_single_step_v.
      cbn; unfold ITree.map.
      repeat norm_v; subst; focus_single_step_v.
      rewrite exp_E_to_instr_E_Memory, subevent_subevent.
      rewrite typ_to_dtyp_D_array.

      Set Hyps Limit 50.

      (* Need another GEP lemma?
         The destination is not read on the Helix side, so that I do not know that the GEP succeeds
       *)

      (*
      match goal with
        |- context[interp_cfg_to_L3 ?defs (@ITree.trigger ?E _ (subevent _ (GEP (DTYPE_Array ?size ?t) (DVALUE_Addr ?a) _))) ?g ?l] =>
        edestruct (@interp_cfg_to_L3_GEP_array defs t a size g l) as (add' & ?EQ & READ'); eauto
      end.

      eapply VEC_LUy.
       *)

        admit.
    (* End of genFSHAssign, things are getting a bit complicated *)



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

      repeat norm_h.
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

      repeat norm_h.
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
      repeat norm_v.
      unfold IntType; rewrite typ_to_dtyp_I.
      cbn.
      focus_single_step_v; repeat norm_v.
      cbn; repeat norm_v.
      subst.
      repeat norm_v.
      focus_single_step_v; repeat norm_v.
      rewrite interp_cfg_to_L3_LW.
      cbn; repeat norm_v.
      unfold endo.
      subst.
      repeat (norm_v; []).
      focus_single_step_v.
      (* onAllHyps move_up_types. *)
      unfold endo.
      focus_single_step_v.
      norm_v.
      2: apply lookup_alist_add_eq.
      cbn; repeat norm_v.
      subst; cbn; repeat norm_v.
      focus_single_step_v.

      (* Case analysis on whether we ever enter the loop or not *)
      unfold eval_int_icmp.
      cbn.
      break_match_goal.
      -- (* We enter the loop *)
        cbn; repeat norm_v.
        subst; cbn; repeat norm_v.

        rewrite find_block_ineq, find_block_eq.
        2: reflexivity.
        2:cbn; admit.

        repeat norm_v.
(*
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

      --
        (* from == to, we go from the entry block to the next one directly *)
        cbn.
        repeat norm_v.
        subst; cbn; repeat norm_v.

        repeat rewrite find_block_ineq.
        2,3,4,5: cbn; admit.
        cbn.
        rewrite find_block_nil.

        cbn; repeat norm_v.
        assert (n ≡ 0) by admit.

        subst.
        cbn; repeat norm_h.
        rewrite interp_Mem_MemSet.
        repeat norm_h.

        apply eutt_Ret.
        split; eauto.
        {
          admit.
        }
        {
          admit.
        }

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
      repeat norm_h.

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
      (* repeat norm_v. *)
      (* unfold IntType; rewrite typ_to_dtyp_I. *)
      (* cbn. *)
      (* setoid_rewrite bind_ret_l. *)
      (* setoid_rewrite bind_ret_l. *)
      (* cbn. *)
      (* repeat norm_v. *)
      (* rewrite interp_cfg_to_L3_LW. *)
      (* cbn*; repeat norm_v. *)
      (* cbn*; repeat norm_v. *)
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
  (*       repeat norm_v. *)
  (*       subst. *)
  (*       cbn. *)
  (*       repeat norm_v. *)





*)
*)
  Admitted.
  End GenIR.


