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

Set Implicit Arguments.
Set Strict Implicit.

Import MDSHCOLOnFloat64.
Import D.
Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

Require Import Vellvm.InstrLemmas.


Opaque incBlockNamed.
Opaque incVoid.
Opaque incLocal.

Typeclasses Opaque equiv.
Remove Hints
       equiv_default_relation
       abstract_algebra.sg_op_proper
       abstract_algebra.sm_proper
       abstract_algebra.comp_proper
       orders.po_preorder
       orders.total_order_po
       orders.le_total
       orders.join_sl_order
       orders.lattice_order_join
       orders.lattice_order_meet
       orders.strict_po_po
       orders.srorder_po
       strong_setoids.binary_strong_morphism_proper
       semirings.FullPseudoOrder_instance_0
       minmax.LatticeOrder_instance_0
       workarounds.equivalence_proper : typeclass_instances.

Section NExpr.

  (**
     We prove in this section the correctness of the compilation of numerical expressions, i.e. [NExpr].
     The corresponding compiling function is [inexpert].

     Helix side:
     * nexp: NExpr
     * σ: evalContext
     * s: IRState

The expression must be closed in [evalContext]. I.e. all variables are below the length of σ
Γ s1 = σ?

   *)
  (* NOTEYZ:
     These expressions are pure. As such, it is true that we do not need to interpret away
     the memory events on Helix side to establish the bisimulation.
     However at least in the current state of affair, I believe it's widely more difficult
     to lift the result before interpretation to the context we need than to simply plug in
     the interpreter.
     In particular we would need to have a clean enough lift that deduces that the memory has
     not been modified. I'm interested in having this, but I do not know how easy it is to get it.
     TODOYZ: Investigate this claim
   *)

  Definition memory_invariant_memory_mcfg (σ : evalContext) (s : IRState) : Rel_mcfg :=
    fun memH '(memV,((l,sl),g)) =>
      memory_invariant σ s memH (memV,(l,g)).

 (** YZ
      At the top level, the correctness of genNExpr is expressed as the denotation of the operator being equivalent
      to the bind of denoting the code followed by denoting the expression.
      However this is not inductively stable, we only want to plug the expression at the top level.
      We therefore instead carry the fact about the denotation of the expression in the invariant. (Is there another clever way?)
      TODO: how to make this (much) less ugly?
   *)
  Definition genNExpr_exp_correct σ (nexp : NExpr) (e: exp typ) : Rel_cfg_T DynamicValues.int64 unit :=
    fun '(_,i) '(memV,(l,(g,v))) =>
      forall l', l ⊑ l' ->
        Ret (memV,(l',(g,UVALUE_I64 i)))
        ≈
        (interp_cfg (translate exp_E_to_instr_E (denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] e))) g l' memV) /\ evalNExpr σ nexp ≡ inr i.

  (**
     We package the local specific invariants. Additionally to the evaluation of the resulting expression,
     we also state that evaluating the code preserves most of the state, except for the local state being
     allowed to be extended with fresh bindings.
   *)
  Record genNExpr_rel
         (σ : evalContext)
         (nexp : NExpr)
         (e : exp typ)
         (mi : memoryH) (sti : config_cfg)
         (mf : memoryH * DynamicValues.int64) (stf : config_cfg_T unit)
    : Prop :=
    {
    exp_correct : genNExpr_exp_correct σ nexp e mf stf;
    monotone : ext_local mi sti mf stf
    }.

  Opaque denote_code.
  Opaque denote_instr.
  Lemma genNExpr_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *)   (nexp: NExpr) (σ: evalContext) (memH: memoryH) (v : Int64.int)
      (* Vellvm bits *)   (e: exp typ) (c: code typ) (g : global_env) (l : local_env) (memV : memoryV),

      genNExpr nexp s1 ≡ inr (s2, (e, c))      -> (* Compilation succeeds *)
      evalNExpr σ nexp ≡ inr v                 -> (* Evaluation succeeds *)
      state_invariant σ s1 memH (memV, (l, g)) -> (* The main state invariant is initially true *)

      eutt (lift_Rel_cfg (state_invariant σ s2) ⩕
            genNExpr_rel σ nexp e memH (mk_config_cfg memV l g) ⩕
            lift_pure_cfg (Γ s1 ≡ Γ s2))
           (with_err_RB (interp_Mem (denoteNExpr σ nexp) memH))
           (with_err_LB (interp_cfg (denote_code (convert_typ [] c)) g l memV)).
  Proof.

    intros s1 s2 nexp; revert s1 s2; induction nexp; intros * COMPILE EVAL PRE.
    - (* Variable case *)
      (* Reducing the compilation *)
      cbn* in COMPILE; simp.

      + (* The variable maps to an integer in the IRState *)
        unfold denoteNExpr; cbn*.
        rewrite denote_code_nil; cbn.
        repeat norm_v.
        break_inner_match_goal.

        * break_inner_match_goal; try abs_by_WF.
          repeat norm_h.
          destruct i0.
          { (* Global -- Absurd, globals map to pointers, not integers *)
            abs_by_WF.
          }
         { (* Local *)
            apply eutt_Ret; split; [| split]; try now eauto.
            constructor; eauto.
            intros l' MONO; cbn*.
            split.
            { repeat norm_v.
              2: eapply memory_invariant_LLU; eauto.
              2: eapply memory_invariant_ext_local; eauto.
              cbn; repeat norm_v.
              reflexivity.
            }

            rewrite Heqo0.
            reflexivity.

          }

        * (* Variable not in context, [context_lookup] fails *)
          cbn* in EVAL; rewrite Heqo0 in EVAL; inv EVAL.

      + (* The variable maps to a pointer *)
        unfold denoteNExpr; cbn*.
        rewrite denote_code_sing.
        cbn.
        repeat norm_v.
        break_inner_match_goal; try abs_by_WF.
        * break_inner_match_goal; try abs_by_WF.
          subst.
          destruct i0; try abs_by_WF.
          edestruct memory_invariant_GLU as (ptr & LU & READ); eauto.
          cbn.
          rewrite denote_instr_load; cbn; eauto.

          (* Can this be cleaned up? *)
          2: {
            repeat rewrite translate_bind.
            rewrite interp_cfg_to_L3_bind.
            do 2 rewrite translate_trigger.
            rewrite lookup_E_to_exp_E_Global.
            rewrite subevent_subevent.
            rewrite exp_E_to_instr_E_Global.
            rewrite subevent_subevent.
            rewrite interp_cfg_to_L3_GR; eauto.
            cbn. rewrite bind_ret_l.
            repeat rewrite translate_ret.
            rewrite interp_cfg_to_L3_ret.
            reflexivity.
            }

          repeat norm_v.
          repeat norm_h.

          apply eutt_Ret; split; [| split].
          -- eapply state_invariant_add_fresh; eauto; reflexivity.
          -- split.
             {
               intros l' MONO; cbn*.
               split.
               { repeat norm_v.
                 2: eapply MONO, In_add_eq.
                 cbn; repeat norm_v.
                 reflexivity.
               }

               rewrite Heqo0.
               reflexivity.
             }
             {
               repeat (split; auto).
               apply sub_alist_add.
               destruct PRE.
               apply concrete_fresh_fresh in incLocal_is_fresh.
               unfold incLocal_fresh in incLocal_is_fresh.
               eapply incLocal_is_fresh; eauto.
             }
          -- symmetry; eapply incLocal_Γ; eauto.

        * cbn* in EVAL; rewrite Heqo0 in EVAL; inv EVAL.

    - (* Constant *)
      cbn* in COMPILE; simp.
      unfold denoteNExpr; cbn*.
      rewrite denote_code_nil; cbn.
      repeat norm_h.
      repeat norm_v.
      apply eutt_Ret; split; [| split]; try now eauto.
      split; eauto.
      intros l' MONO; cbn*.
      split; try reflexivity.
      rewrite repr_intval; repeat norm_v.
      reflexivity.

    - (* NDiv *)

      cbn* in COMPILE; simp.

      eutt_hide_right.
      unfold denoteNExpr in *; cbn*.

      cbn in EVAL.
      break_inner_match_goal; [| break_inner_match_goal].
      + inversion EVAL. (* Exception in subexpression *)
      + inversion EVAL. (* Division by 0 *)
      + (* Success, Heqs2 *)
        break_inner_match_goal.
        * inversion EVAL. (* Exception in subexpression *)
        * repeat norm_h.
          subst i1.

          (* TODO YZ: gets some super "specialize" tactics that do not require to provide variables *)
          specialize (IHnexp1 _ _ _ _ _ _ _ _ _ _ Heqs Heqs3 PRE).

          cbn* in IHnexp1; rewrite Heqs3 in IHnexp1.
          (* YZ TODO : Why is this one particularly slow? *)
          repeat norm_h in IHnexp1.

          rewrite convert_typ_app, denote_code_app.
          repeat norm_v.

          ret_bind_l_left (memH, i3).
          eapply eutt_clo_bind; [eassumption | clear IHnexp1].

          introR; destruct_unit.
          destruct PRE0 as (PREI & (EXPRI & <- & <- & <- & MONOI) & GAMMAI).
          cbn in *.

          specialize (IHnexp2 _ _ _ _ _ _ _ _ _ _ Heqs0 Heqs2 PREI).

          cbn* in IHnexp2;
            repeat norm_v in IHnexp2;
            repeat norm_h in IHnexp2.
          simpl_match in IHnexp2.
          repeat norm_h in IHnexp2.

          rewrite convert_typ_app, denote_code_app.
          repeat norm_v.
          subst.
          ret_bind_l_left (memH,i2).
          eapply eutt_clo_bind; [eassumption | clear IHnexp2].

          introR; destruct_unit.
          destruct PRE0 as (PREF & (EXPRF & <- & <- & <- & MONOF) & GAMMAF).
          (* cbn takes 5seconds instead of doing this instantaneously... *)
          simpl in *.
          cbn.

          rewrite denote_code_sing; cbn.
          repeat norm_v.
          simpl in *; unfold denote_op; simpl.
          unfold IntType; rewrite typ_to_dtyp_I.

          specialize (EXPRI _ MONOF) as [EXPRI EVAL_vH].
          rewrite Heqs3 in EVAL_vH.
          injection EVAL_vH; intros; subst.
          assert (l1 ⊑ l1) as L1L1. reflexivity.
          specialize (EXPRF _ L1L1) as [EXPRF EVAL_vH0].
          rewrite Heqs2 in EVAL_vH0.
          injection EVAL_vH0; intros; subst.

          rewrite denote_instr_op.

          (* Operator evaluation *)
          2: {
            eapply denote_ibinop_concrete; cbn; eauto; try reflexivity.
            cbn; break_inner_match_goal; try reflexivity.

            (* Division by 0 *)
            apply Z.eqb_eq in Heqb.
            exfalso. apply n.
            rewrite <- Int64.unsigned_zero in Heqb.
            unfold MInt64asNT.NTypeZero.
            apply unsigned_is_zero; auto.
          }

          repeat norm_v.
          apply eutt_Ret; split; [| split]; try now eauto.
          cbn. eapply state_invariant_add_fresh; eauto; reflexivity.
          split.
          {
            cbn; intros ? MONO.
            split.
            { repeat norm_v.
              2: apply MONO, In_add_eq.
              cbn; repeat norm_v.
              apply eutt_Ret.
              do 3 f_equal.
            }

            repeat match_rewrite.
            reflexivity.
          }
          {
            apply ext_local_subalist.
            etransitivity; eauto.
            etransitivity; eauto.
            apply sub_alist_add.
            apply incLocal_is_fresh,concrete_fresh_fresh in PREF.
            eapply PREF.
            eauto.
          }
          {
            rewrite GAMMAI, GAMMAF.
            symmetry; eapply incLocal_Γ; eauto.
          }
    - (* NMod *)

      cbn* in COMPILE; simp.

      eutt_hide_right.
      unfold denoteNExpr in *; cbn*.

      cbn in EVAL.
      break_inner_match_goal; [| break_inner_match_goal].
      + inversion EVAL. (* Exception in subexpression *)
      + inversion EVAL. (* Division by 0 *)
      + (* Success, Heqs2 *)
        break_inner_match_goal.
        * inversion EVAL. (* Exception in subexpression *)
        * repeat norm_h.
          subst i1.

          (* TODO YZ: gets some super "specialize" tactics that do not require to provide variables *)
          specialize (IHnexp1 _ _ _ _ _ _ _ _ _ _ Heqs Heqs3 PRE).

          cbn* in IHnexp1; rewrite Heqs3 in IHnexp1.
          (* YZ TODO : Why is this one particularly slow? *)
          repeat norm_h in IHnexp1.

          rewrite convert_typ_app, denote_code_app.
          repeat norm_v.

          ret_bind_l_left (memH, i3).
          eapply eutt_clo_bind; [eassumption | clear IHnexp1].

          introR; destruct_unit.
          destruct PRE0 as (PREI & (EXPRI & <- & <- & <- & MONOI) & GAMMAI).
          cbn in *.

          specialize (IHnexp2 _ _ _ _ _ _ _ _ _ _ Heqs0 Heqs2 PREI).

          cbn* in IHnexp2;
            repeat norm_v in IHnexp2;
            repeat norm_h in IHnexp2.
          simpl_match in IHnexp2.
          repeat norm_h in IHnexp2.

          rewrite convert_typ_app, denote_code_app.
          repeat norm_v.
          subst.
          ret_bind_l_left (memH,i2).
          eapply eutt_clo_bind; [eassumption | clear IHnexp2].

          introR; destruct_unit.
          destruct PRE0 as (PREF & (EXPRF & <- & <- & <- & MONOF) & GAMMAF).
          (* cbn takes 5seconds instead of doing this instantaneously... *)
          simpl in *.
          cbn.

          rewrite denote_code_sing; cbn.
          repeat norm_v.
          simpl in *; unfold denote_op; simpl.
          unfold IntType; rewrite typ_to_dtyp_I.

          specialize (EXPRI _ MONOF) as [EXPRI EVAL_vH].
          rewrite Heqs3 in EVAL_vH.
          injection EVAL_vH; intros; subst.
          assert (l1 ⊑ l1) as L1L1. reflexivity.
          specialize (EXPRF _ L1L1) as [EXPRF EVAL_vH0].
          rewrite Heqs2 in EVAL_vH0.
          injection EVAL_vH0; intros; subst.

          rewrite denote_instr_op.

          (* Operator evaluation *)
          2: {
            eapply denote_ibinop_concrete; cbn; eauto; try reflexivity.
            cbn; break_inner_match_goal; try reflexivity.

            (* Division by 0 *)
            apply Z.eqb_eq in Heqb.
            exfalso. apply n.
            rewrite <- Int64.unsigned_zero in Heqb.
            unfold MInt64asNT.NTypeZero.
            apply unsigned_is_zero; auto.
          }

          repeat norm_v.
          apply eutt_Ret; split; [| split]; try now eauto.
          cbn. eapply state_invariant_add_fresh; eauto; reflexivity.
          split.
          {
            cbn; intros ? MONO.
            split.
            { repeat norm_v.
              2: apply MONO, In_add_eq.
              cbn; repeat norm_v.
              apply eutt_Ret.
              do 3 f_equal.
            }

            repeat match_rewrite.
            reflexivity.
          }
          {
            apply ext_local_subalist.
            etransitivity; eauto.
            etransitivity; eauto.
            apply sub_alist_add.
            apply incLocal_is_fresh,concrete_fresh_fresh in PREF.
            eapply PREF.
            eauto.
          }
          {
            rewrite GAMMAI, GAMMAF.
            symmetry; eapply incLocal_Γ; eauto.
          }
   - (* NAdd *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in COMPILE; simp.

      eutt_hide_right.
      unfold denoteNExpr in *; cbn*.

      cbn in EVAL.
      break_inner_match_goal; [| break_inner_match_goal];
        try (exfalso; match goal with | h: genNExpr _ _ ≡ _ |- _ => eapply evalNexpr_WF_no_fail in h; now eauto end); try solve [inversion EVAL].

      repeat norm_h.
      (* TODO YZ: gets some super "specialize" tactics that do not require to provide variables *)
      specialize (IHnexp1 _ _ _ _ _ _ _ _ _ _ Heqs Heqs2 PRE).

      cbn* in IHnexp1;
        repeat norm_v in IHnexp1;
        repeat norm_h in IHnexp1.
      simpl_match in IHnexp1.
      (* YZ TODO : Why is this one particularly slow? *)
      repeat norm_h in IHnexp1.

      subst.
      cbn*.
      rewrite convert_typ_app, denote_code_app.
      repeat norm_v.
      subst.
      ret_bind_l_left (memH,i2).
      eapply eutt_clo_bind; [eassumption | clear IHnexp1].

      introR; destruct_unit.
      destruct PRE0 as (PREI & (EXPRI & <- & <- & <- & MONOI) & GAMMAI).
      cbn in *.

      specialize (IHnexp2 _ _ _ _ _ _ _ _ _ _ Heqs0 Heqs3 PREI).

      cbn* in IHnexp2;
        repeat norm_v in IHnexp2;
        repeat norm_h in IHnexp2.
      simpl_match in IHnexp2.
      repeat norm_h in IHnexp2.

      rewrite convert_typ_app, denote_code_app.
      repeat norm_v.
      subst.
      ret_bind_l_left (memH,i3).
      eapply eutt_clo_bind; [eassumption | clear IHnexp2].

      introR; destruct_unit.
      destruct PRE0 as (PREF & (EXPRF & <- & <- & <- & MONOF) & GAMMAF).
      (* cbn takes 5seconds instead of doing this instantaneously... *)
      simpl in *; unfold denote_op; simpl.
      cbn; rewrite denote_code_sing; cbn.
      unfold IntType; rewrite typ_to_dtyp_I.

      specialize (EXPRI _ MONOF) as [EXPRI EVAL_vH].
      rewrite Heqs2 in EVAL_vH; injection EVAL_vH; intros; subst.

      assert (l0 ⊑ l0) as L0L0 by reflexivity.
      specialize (EXPRF _ L0L0) as [EXPRF EVAL_vH0].
      rewrite Heqs3 in EVAL_vH0; injection EVAL_vH0; intros; subst.
      clear L0L0.

      cbn*.

      rewrite denote_instr_op.

      (* Operator evaluation *)
      2: eapply denote_ibinop_concrete; cbn; eauto; reflexivity.

      repeat norm_v.
      apply eutt_Ret; split; [| split].
      cbn; eapply state_invariant_add_fresh; eauto.
      split.
      {
        cbn; intros ? MONO.
        split.
        { repeat norm_v.
          2: apply MONO, In_add_eq.
          cbn; repeat norm_v.
          apply eutt_Ret.
          do 3 f_equal.
        }

        repeat match_rewrite.
        reflexivity.
      }
      {
        apply ext_local_subalist.
        etransitivity; eauto.
        etransitivity; eauto.
        apply sub_alist_add.
        apply incLocal_is_fresh,concrete_fresh_fresh in PREF.
        eapply PREF.
        eauto.
      }
      {
        rewrite GAMMAI, GAMMAF.
        symmetry; eapply incLocal_Γ; eauto.
      }
    - (* NMinus *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in COMPILE; simp.

      eutt_hide_right.
      unfold denoteNExpr in *; cbn*.

      cbn in EVAL.
      break_inner_match_goal; [| break_inner_match_goal];
        try (exfalso; match goal with | h: genNExpr _ _ ≡ _ |- _ => eapply evalNexpr_WF_no_fail in h; now eauto end); try solve [inversion EVAL].

      repeat norm_h.
      (* TODO YZ: gets some super "specialize" tactics that do not require to provide variables *)
      specialize (IHnexp1 _ _ _ _ _ _ _ _ _ _ Heqs Heqs2 PRE).

      cbn* in IHnexp1;
        repeat norm_v in IHnexp1;
        repeat norm_h in IHnexp1.
      simpl_match in IHnexp1.
      (* YZ TODO : Why is this one particularly slow? *)
      repeat norm_h in IHnexp1.

      subst.
      cbn*.
      rewrite convert_typ_app, denote_code_app.
      repeat norm_v.
      subst.
      ret_bind_l_left (memH,i2).
      eapply eutt_clo_bind; [eassumption | clear IHnexp1].

      introR; destruct_unit.
      destruct PRE0 as (PREI & (EXPRI & <- & <- & <- & MONOI) & GAMMAI).
      cbn in *.

      specialize (IHnexp2 _ _ _ _ _ _ _ _ _ _ Heqs0 Heqs3 PREI).

      cbn* in IHnexp2;
        repeat norm_v in IHnexp2;
        repeat norm_h in IHnexp2.
      simpl_match in IHnexp2.
      repeat norm_h in IHnexp2.

      rewrite convert_typ_app, denote_code_app.
      repeat norm_v.
      subst.
      ret_bind_l_left (memH,i3).
      eapply eutt_clo_bind; [eassumption | clear IHnexp2].

      introR; destruct_unit.
      destruct PRE0 as (PREF & (EXPRF & <- & <- & <- & MONOF) & GAMMAF).
      (* cbn takes 5seconds instead of doing this instantaneously... *)
      simpl in *; unfold denote_op; simpl.
      cbn; rewrite denote_code_sing; cbn.
      unfold IntType; rewrite typ_to_dtyp_I.

      specialize (EXPRI _ MONOF) as [EXPRI EVAL_vH].
      rewrite Heqs2 in EVAL_vH; injection EVAL_vH; intros; subst.

      assert (l0 ⊑ l0) as L0L0 by reflexivity.
      specialize (EXPRF _ L0L0) as [EXPRF EVAL_vH0].
      rewrite Heqs3 in EVAL_vH0; injection EVAL_vH0; intros; subst.
      clear L0L0.

      cbn*.

      rewrite denote_instr_op.

      (* Operator evaluation *)
      2: eapply denote_ibinop_concrete; cbn; eauto; reflexivity.

      repeat norm_v.
      apply eutt_Ret; split; [| split].
      cbn; eapply state_invariant_add_fresh; eauto.
      split.
      {
        cbn; intros ? MONO.
        split.
        { repeat norm_v.
          2: apply MONO, In_add_eq.
          cbn; repeat norm_v.
          apply eutt_Ret.
          do 3 f_equal.
        }

        repeat match_rewrite.
        reflexivity.
      }
      {
        apply ext_local_subalist.
        etransitivity; eauto.
        etransitivity; eauto.
        apply sub_alist_add.
        apply incLocal_is_fresh,concrete_fresh_fresh in PREF.
        eapply PREF.
        eauto.
      }
      {
        rewrite GAMMAI, GAMMAF.
        symmetry; eapply incLocal_Γ; eauto.
      }
    - (* NMult *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in COMPILE; simp.

      eutt_hide_right.
      unfold denoteNExpr in *; cbn*.

      cbn in EVAL.
      break_inner_match_goal; [| break_inner_match_goal];
        try (exfalso; match goal with | h: genNExpr _ _ ≡ _ |- _ => eapply evalNexpr_WF_no_fail in h; now eauto end); try solve [inversion EVAL].

      repeat norm_h.
      (* TODO YZ: gets some super "specialize" tactics that do not require to provide variables *)
      specialize (IHnexp1 _ _ _ _ _ _ _ _ _ _ Heqs Heqs2 PRE).

      cbn* in IHnexp1;
        repeat norm_v in IHnexp1;
        repeat norm_h in IHnexp1.
      simpl_match in IHnexp1.
      (* YZ TODO : Why is this one particularly slow? *)
      repeat norm_h in IHnexp1.

      subst.
      cbn*.
      rewrite convert_typ_app, denote_code_app.
      repeat norm_v.
      subst.
      ret_bind_l_left (memH,i2).
      eapply eutt_clo_bind; [eassumption | clear IHnexp1].

      introR; destruct_unit.
      destruct PRE0 as (PREI & (EXPRI & <- & <- & <- & MONOI) & GAMMAI).
      cbn in *.

      specialize (IHnexp2 _ _ _ _ _ _ _ _ _ _ Heqs0 Heqs3 PREI).

      cbn* in IHnexp2;
        repeat norm_v in IHnexp2;
        repeat norm_h in IHnexp2.
      simpl_match in IHnexp2.
      repeat norm_h in IHnexp2.

      rewrite convert_typ_app, denote_code_app.
      repeat norm_v.
      subst.
      ret_bind_l_left (memH,i3).
      eapply eutt_clo_bind; [eassumption | clear IHnexp2].

      introR; destruct_unit.
      destruct PRE0 as (PREF & (EXPRF & <- & <- & <- & MONOF) & GAMMAF).
      (* cbn takes 5seconds instead of doing this instantaneously... *)
      simpl in *; unfold denote_op; simpl.
      cbn; rewrite denote_code_sing; cbn.
      unfold IntType; rewrite typ_to_dtyp_I.

      specialize (EXPRI _ MONOF) as [EXPRI EVAL_vH].
      rewrite Heqs2 in EVAL_vH; injection EVAL_vH; intros; subst.

      assert (l0 ⊑ l0) as L0L0 by reflexivity.
      specialize (EXPRF _ L0L0) as [EXPRF EVAL_vH0].
      rewrite Heqs3 in EVAL_vH0; injection EVAL_vH0; intros; subst.
      clear L0L0.

      cbn*.

      rewrite denote_instr_op.

      (* Operator evaluation *)
      2: {
        eapply denote_ibinop_concrete; cbn; eauto; try reflexivity.
        cbn.
        break_inner_match; reflexivity.
      }

      repeat norm_v.
      apply eutt_Ret; split; [| split].
      cbn; eapply state_invariant_add_fresh; eauto.
      split.
      {
        cbn; intros ? MONO.
        split.
        { repeat norm_v.
          2: apply MONO, In_add_eq.
          cbn; repeat norm_v.
          apply eutt_Ret.
          do 3 f_equal.
        }

        repeat match_rewrite.
        reflexivity.
      }
      {
        apply ext_local_subalist.
        etransitivity; eauto.
        etransitivity; eauto.
        apply sub_alist_add.
        apply incLocal_is_fresh,concrete_fresh_fresh in PREF.
        eapply PREF.
        eauto.
      }
      {
        rewrite GAMMAI, GAMMAF.
        symmetry; eapply incLocal_Γ; eauto.
      }
    - (* NMin *)
      (* Non-implemented by the compiler *)
      inversion COMPILE.
    - (* NMax *)
      (* Non-implemented by the compiler *)
      inversion COMPILE.
Qed.

  Lemma genNExpr_memH : forall σ n e memH memV memH' memV' l g l' g' n',
      genNExpr_rel σ n e memH (mk_config_cfg memV l g) (memH', n')
                   (memV', (l', (g', ()))) ->
      memH ≡ memH'.
  Proof.
    intros σ n e memH memV memH' memV' l g l' g' n' H.
    destruct H; cbn in *; intuition.
  Qed.

  Lemma genNExpr_memV : forall σ n e memH memV memH' memV' l g l' g' n',
      genNExpr_rel σ n e memH (mk_config_cfg memV l g) (memH', n')
                   (memV', (l', (g', ()))) ->
      memV ≡ memV'.
  Proof.
    intros σ n e memH memV memH' memV' l g l' g' n' H.
    destruct H; cbn in *; intuition.
  Qed.

  Lemma genNExpr_g : forall σ n e memH memV memH' memV' l g l' g' n',
      genNExpr_rel σ n e memH (mk_config_cfg memV l g) (memH', n')
                   (memV', (l', (g', ()))) ->
      g ≡ g'.
  Proof.
    intros σ n e memH memV memH' memV' l g l' g' n' H.
    destruct H; cbn in *; intuition.
  Qed.

  Lemma genNExpr_l : forall σ n e memH memV memH' memV' l g l' g' n',
      genNExpr_rel σ n e memH (mk_config_cfg memV l g) (memH', n')
                   (memV', (l', (g', ()))) ->
      l ⊑ l'.
  Proof.
    intros σ n e memH memV memH' memV' l g l' g' n' H.
    destruct H; cbn in *; intuition.
  Qed.

End NExpr.

Ltac genNExpr_rel_subst LL :=
  match goal with
  | NEXP : genNExpr_rel ?σ ?n ?e ?memH (mk_config_cfg ?memV ?l ?g) (?memH', ?n') (?memV', (?l', (?g', ()))) |- _ =>
    let H := fresh in
    pose proof genNExpr_memH NEXP as H; subst memH';
    pose proof genNExpr_memV NEXP as H; subst memV';
    pose proof genNExpr_g NEXP as H; subst g';
    pose proof genNExpr_l NEXP as LL
  end.
