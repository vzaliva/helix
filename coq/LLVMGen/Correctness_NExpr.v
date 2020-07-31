Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Import ProofNotations.
Open Scope Z.

Set Implicit Arguments.
Set Strict Implicit.

(* YZ TODO: Check that this is global and factor it in prelude *)
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

(** * Correctness of the compilation of numerical expressions

     We prove in this section the correctness of the compilation of numerical expressions, i.e. [NExpr].
     The corresponding compiling function is [genNexpr].

     Helix side:
     * nexp: NExpr
     * σ: evalContext
     * s: IRState

 *)

Section NExpr.
  
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
            (interp_cfg (translate exp_E_to_instr_E
                                   (denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] e)))
                        g l' memV)
            /\ evalNExpr σ nexp ≡ inr i.

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

  Hint Resolve memory_invariant_ext_local: core.
  Ltac solve_lu :=
    match goal with
    | |- @Maps.lookup _ _ local_env _ ?id ?l ≡ Some _ =>
      eapply memory_invariant_LLU; [| eassumption | eassumption]; eauto
    | |- @Maps.lookup _ _ global_env _ ?id ?l ≡ Some _ =>
      eapply memory_invariant_GLU; [| eassumption | eassumption]; eauto
     end.

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

        norm_v.

        break_inner_match_goal.

        * break_inner_match_goal; try abs_by_WF.

          norm_h.
          destruct i0; try abs_by_WF.

          apply eutt_Ret; split; [| split]; try now eauto.
          constructor; eauto.
          intros l' MONO; cbn*.
          split.
          { norm_vr; [| solve_lu].
            reflexivity.
          }
          {match_rewrite.
           reflexivity.
          }

        * (* Variable not in context, [context_lookup] fails *)
          cbn* in EVAL; rewrite Heqo0 in EVAL; inv EVAL.
          
      + (* The variable maps to a pointer *)
        unfold denoteNExpr; cbn*.

        norm_v.

        rewrite denote_code_singleton.
        break_inner_match_goal; try abs_by_WF.

        * break_inner_match_goal; try abs_by_WF.
          subst.
          destruct i0; try abs_by_WF.
          edestruct memory_invariant_GLU as (ptr & LU & READ); eauto.
          rewrite typ_to_dtyp_equation in READ.
          rewrite denote_instr_load; cbn in *; eauto.
          2: {
            norm_vl; eauto.
            norm_vl; reflexivity.
          }

          norm_v.
          norm_h.
          apply eutt_Ret; split; [| split].
          -- eapply state_invariant_add_fresh; eauto; reflexivity. (* YZ TODO: automate *)
          -- split.
             {
               intros l' MONO; cbn*.
               split.
               { norm_vr.
                 2: eapply MONO, In_add_eq.
                 norm_vr; reflexivity.
               }
               match_rewrite.
               reflexivity.
             }
             {
               repeat (split; auto).
               (* YZ TODO: automate [sub_alist] goals *)
               apply sub_alist_add.
               (* YZ TODO: automate [alist_fresh] goals *)
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
      norm_h.
      norm_v.
      apply eutt_Ret; split; [| split]; try now eauto.
      split; eauto.
      intros l' MONO; cbn*.
      split; try reflexivity.
      rewrite repr_intval; norm_v.
      reflexivity.

    - (* NDiv *)

      cbn* in COMPILE; simp.
      unfold denoteNExpr in *; cbn*.
      cbn in EVAL.
      simp.
      norm_h.

      (* TODO YZ: gets some super "specialize" tactics that do not require to provide variables *)
      specialize (IHnexp1 _ _ _ _ _ _ _ _ _ _ Heqs Heqs3 PRE).

      cbn* in IHnexp1; rewrite Heqs3 in IHnexp1.
      (* YZ TODO : Why is this one particularly slow? *)
      repeat norm_h in IHnexp1.

      rewrite convert_typ_app, denote_code_app.
      norm_v.

      ret_bind_l_left (memH, i2).
      eapply eutt_clo_bind; [eassumption | clear IHnexp1].

      introR; destruct_unit.
      destruct PRE0 as (PREI & (EXPRI & <- & <- & <- & MONOI) & GAMMAI).
      cbn in *.

      specialize (IHnexp2 _ _ _ _ _ _ _ _ _ _ Heqs0 Heqs2 PREI).

      cbn* in IHnexp2;
        repeat norm_v in IHnexp2;
        repeat norm_h in IHnexp2.
      simp.
      repeat norm_h in IHnexp2.

      rewrite convert_typ_app, denote_code_app.
      norm_v.
      ret_bind_l_left (memH,i1).
      eapply eutt_clo_bind; [eassumption | clear IHnexp2].

      introR; destruct_unit.
      destruct PRE0 as (PREF & (EXPRF & <- & <- & <- & MONOF) & GAMMAF).
      cbn in *.

      rewrite denote_code_singleton; cbn.
      norm_v.

      specialize (EXPRI _ MONOF) as [EXPRI EVAL_vH].
      assert (l1 ⊑ l1) as L1L1 by reflexivity; specialize (EXPRF _ L1L1) as [EXPRF EVAL_vH0].
      rewrite Heqs3 in EVAL_vH.
      injection EVAL_vH; intros; subst.
      rewrite Heqs4 in EVAL_vH0.
      simp.
      rewrite denote_instr_op.
      2:{
        eapply denote_ibinop_concrete; cbn; eauto; try reflexivity.
        cbn; break_inner_match_goal; try reflexivity.
        exfalso; apply n.
        clear EXPRF EXPRI.
        apply Z.eqb_eq in Heqb.
        rewrite <- Int64.unsigned_zero in Heqb.
       unfold MInt64asNT.NTypeZero.
        apply unsigned_is_zero; auto.
      }
      
      norm_v.
      apply eutt_Ret; split; [| split]; try now eauto.
      cbn. eapply state_invariant_add_fresh; eauto; reflexivity.
      split.
      {
        cbn; intros ? MONO.
        split.
        { norm_v.
          2: apply MONO, In_add_eq.
          cbn; norm_v.
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
      unfold denoteNExpr in *; cbn*.
      cbn in EVAL; simp.

      norm_h.
     
      (* TODO YZ: gets some super "specialize" tactics that do not require to provide variables *)
      specialize (IHnexp1 _ _ _ _ _ _ _ _ _ _ Heqs Heqs3 PRE).

      cbn* in IHnexp1; rewrite Heqs3 in IHnexp1.
      (* YZ TODO : Why is this one particularly slow? *)
      repeat norm_h in IHnexp1.

      ret_bind_l_left (memH, i2).
      rewrite convert_typ_app, denote_code_app.
      norm_v.

      eapply eutt_clo_bind; [eassumption | clear IHnexp1].

      introR; destruct_unit.
      destruct PRE0 as (PREI & (EXPRI & <- & <- & <- & MONOI) & GAMMAI).
      cbn in *.

      specialize (IHnexp2 _ _ _ _ _ _ _ _ _ _ Heqs0 Heqs2 PREI).

      cbn* in IHnexp2;
        repeat norm_v in IHnexp2;
        repeat norm_h in IHnexp2.
      simp.
      repeat norm_h in IHnexp2.

      rewrite convert_typ_app, denote_code_app.
      norm_v.
      ret_bind_l_left (memH,i1).
      eapply eutt_clo_bind; [eassumption | clear IHnexp2].

      introR; destruct_unit.
      destruct PRE0 as (PREF & (EXPRF & <- & <- & <- & MONOF) & GAMMAF).
      (* cbn takes 5seconds instead of doing this instantaneously... *)
      cbn in *.

      rewrite denote_code_singleton; cbn.
      norm_v.

      (* I hate this painful unification with eval... Not sure how to do better *)
      specialize (EXPRI _ MONOF) as [EXPRI EVAL_vH].
      rewrite Heqs3 in EVAL_vH.
      injection EVAL_vH; intros; subst.
      assert (l1 ⊑ l1) as L1L1 by reflexivity.
      specialize (EXPRF _ L1L1) as [EXPRF EVAL_vH0].
      rewrite Heqs4 in EVAL_vH0.
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

      norm_v.
      apply eutt_Ret; split; [| split]; try now eauto.
      -- cbn. eapply state_invariant_add_fresh; eauto; reflexivity.
      -- split.
         {
           cbn; intros ? MONO.
           split.
           {  norm_v.
              2: apply MONO, In_add_eq.
              apply eutt_Ret.
              reflexivity.
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
      -- rewrite GAMMAI, GAMMAF.
         symmetry; eapply incLocal_Γ; eauto.

   - (* NAdd *)
      cbn* in COMPILE; simp.
      unfold denoteNExpr in *; cbn* in *.
      simp.
      norm_h.

      (* TODO YZ: gets some super "specialize" tactics that do not require to provide variables *)
      specialize (IHnexp1 _ _ _ _ _ _ _ _ _ _ Heqs Heqs2 PRE).
      simp.

      cbn* in IHnexp1;
        repeat norm_v in IHnexp1;
        repeat norm_h in IHnexp1.

      rewrite convert_typ_app, denote_code_app.
      norm_v.
      ret_bind_l_left (memH,i1).
      eapply eutt_clo_bind; [eassumption | clear IHnexp1].

      introR; destruct_unit.
      destruct PRE0 as (PREI & (EXPRI & <- & <- & <- & MONOI) & GAMMAI).
      cbn in *.

      specialize (IHnexp2 _ _ _ _ _ _ _ _ _ _ Heqs0 Heqs3 PREI).
      simp.

      cbn* in IHnexp2;
        repeat norm_v in IHnexp2;
        repeat norm_h in IHnexp2.

      rewrite convert_typ_app, denote_code_app.
      norm_v.
      ret_bind_l_left (memH,i2).
      eapply eutt_clo_bind; [eassumption | clear IHnexp2].

      introR; destruct_unit.
      destruct PRE0 as (PREF & (EXPRF & <- & <- & <- & MONOF) & GAMMAF).
      cbn in *.
      rewrite denote_code_singleton; cbn.
      norm_v.
    
      specialize (EXPRI _ MONOF) as [EXPRI EVAL_vH].
      rewrite Heqs4 in EVAL_vH; injection EVAL_vH; intros; subst.

      assert (l1 ⊑ l1) as L0L0 by reflexivity.
      specialize (EXPRF _ L0L0) as [EXPRF EVAL_vH0].
      rewrite Heqs2 in EVAL_vH0; injection EVAL_vH0; intros; subst.
      clear L0L0.

      rewrite denote_instr_op.

      (* Operator evaluation *)
      2: eapply denote_ibinop_concrete; cbn; eauto; reflexivity.

      norm_v.
      apply eutt_Ret; split; [| split].
      cbn; eapply state_invariant_add_fresh; eauto.
      split.
      {
        cbn; intros ? MONO.
        split.
        { norm_v.
          2: apply MONO, In_add_eq.
          norm_v.
          apply eutt_Ret.
          reflexivity.
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
      cbn* in COMPILE; simp.
      unfold denoteNExpr in *; cbn* in *.
      simp.

      norm_h.

      (* TODO YZ: gets some super "specialize" tactics that do not require to provide variables *)
      specialize (IHnexp1 _ _ _ _ _ _ _ _ _ _ Heqs Heqs2 PRE).
      simp.
      cbn* in IHnexp1;
        repeat norm_v in IHnexp1;
        repeat norm_h in IHnexp1.

      rewrite convert_typ_app, denote_code_app.
      norm_v.
      ret_bind_l_left (memH,i1).
      eapply eutt_clo_bind; [eassumption | clear IHnexp1].

      introR; destruct_unit.
      destruct PRE0 as (PREI & (EXPRI & <- & <- & <- & MONOI) & GAMMAI).
      cbn in *.

      specialize (IHnexp2 _ _ _ _ _ _ _ _ _ _ Heqs0 Heqs3 PREI).
      simp.
      cbn* in IHnexp2;
        repeat norm_v in IHnexp2;
        repeat norm_h in IHnexp2.

      rewrite convert_typ_app, denote_code_app.
      norm_v.

      ret_bind_l_left (memH,i2).
      eapply eutt_clo_bind; [eassumption | clear IHnexp2].

      introR; destruct_unit.
      destruct PRE0 as (PREF & (EXPRF & <- & <- & <- & MONOF) & GAMMAF).
      cbn in *.

      rewrite denote_code_singleton; cbn.

      specialize (EXPRI _ MONOF) as [EXPRI EVAL_vH].
      rewrite Heqs4 in EVAL_vH; simp. 

      assert (l1 ⊑ l1) as L0L0 by reflexivity.
      specialize (EXPRF _ L0L0) as [EXPRF EVAL_vH0].
      rewrite Heqs2 in EVAL_vH0; simp.
      clear L0L0.
      norm_v.

      rewrite denote_instr_op.

      (* Operator evaluation *)
      2: eapply denote_ibinop_concrete; cbn; eauto; reflexivity.

      norm_v.
      apply eutt_Ret; split; [| split].
      cbn; eapply state_invariant_add_fresh; eauto.
      split.
      {
        cbn; intros ? MONO.
        split.
        { norm_v.
          2: apply MONO, In_add_eq.
          apply eutt_Ret.
          reflexivity.
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
      cbn* in COMPILE; simp.
      unfold denoteNExpr in *; cbn* in *.
      simp.

      norm_h.

      specialize (IHnexp1 _ _ _ _ _ _ _ _ _ _ Heqs Heqs2 PRE).
      simp.

      cbn* in IHnexp1;
        repeat norm_v in IHnexp1;
        repeat norm_h in IHnexp1.

      rewrite convert_typ_app, denote_code_app.
      norm_v.

      ret_bind_l_left (memH,i1).
      eapply eutt_clo_bind; [eassumption | clear IHnexp1].

      introR; destruct_unit.
      destruct PRE0 as (PREI & (EXPRI & <- & <- & <- & MONOI) & GAMMAI).
      cbn in *.

      specialize (IHnexp2 _ _ _ _ _ _ _ _ _ _ Heqs0 Heqs3 PREI).
      simp.
      cbn* in IHnexp2;
        repeat norm_v in IHnexp2;
        repeat norm_h in IHnexp2.

      rewrite convert_typ_app, denote_code_app.
      norm_v.
     
      ret_bind_l_left (memH,i2).
      eapply eutt_clo_bind; [eassumption | clear IHnexp2].

      introR; destruct_unit.
      destruct PRE0 as (PREF & (EXPRF & <- & <- & <- & MONOF) & GAMMAF).
      cbn in *; rewrite denote_code_singleton; cbn.
      norm_v.

      specialize (EXPRI _ MONOF) as [EXPRI EVAL_vH].
      rewrite Heqs4 in EVAL_vH; injection EVAL_vH; intros; subst.

      assert (l1 ⊑ l1) as L0L0 by reflexivity.
      specialize (EXPRF _ L0L0) as [EXPRF EVAL_vH0].
      rewrite Heqs2 in EVAL_vH0; injection EVAL_vH0; intros; subst.
      clear L0L0.

      rewrite denote_instr_op.

      (* Operator evaluation *)
      2: {
        eapply denote_ibinop_concrete; cbn; eauto; try reflexivity.
        cbn.
        break_inner_match; reflexivity.
      }

      norm_v.
      apply eutt_Ret; split; [| split].
      cbn; eapply state_invariant_add_fresh; eauto.
      split.
      {
        cbn; intros ? MONO.
        split.
        { norm_v.
          2: apply MONO, In_add_eq.
          apply eutt_Ret.
          reflexivity.
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
