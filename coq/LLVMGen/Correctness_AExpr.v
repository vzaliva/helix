Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.
Require Import Helix.LLVMGen.Correctness_MExpr.

Set Implicit Arguments.
Set Strict Implicit.

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

Section AExpr.

  Definition R_AExpr_start (σ : evalContext) (s : IRState) (memH : memoryH) (vellvm : memoryV * (local_env * global_env)) : Prop
    := state_invariant σ s memH vellvm.

  Definition R_AExpr
             (σ : evalContext) (s : IRState)
             (helix : memoryH * binary64)
             (vellvm : memoryV * (local_env * res_L1)) : Prop
    :=
      let '(memH, b) := helix in
      let '(memV, (ρ, (g, res))) := vellvm in
      state_invariant σ s memH (memV, (ρ, g)) /\
      res ≡ UVALUE_Double b.

  Hint Unfold R_AExpr: core.

  (** ** Compilation of AExpr TODO
   *)
  Definition genAExpr_exp_correct σ (aexp : AExpr) (e: exp typ) : Rel_cfg_T binary64 unit :=
    fun '(memH,i) '(memV,(l,(g,v))) =>
      forall l', l ⊑ l' ->
        Ret (memV,(l',(g,UVALUE_Double i)))
        ≈
        interp_cfg (translate exp_E_to_instr_E (denote_exp (Some (DTYPE_Double)) (convert_typ [] e))) g l' memV /\ evalAExpr memH σ aexp ≡ inr i.

  Record genAExpr_rel
         (σ : evalContext)
         (aexp : AExpr)
         (e : exp typ)
         (mi : memoryH) (sti : config_cfg)
         (mf : memoryH * binary64) (stf : config_cfg_T unit)
    : Prop :=
    {
    aexp_correct : genAExpr_exp_correct σ aexp e mf stf;
    amonotone : ext_local mi sti mf stf
    }.

  Lemma genAExpr_memH : forall σ aexp e memH memV memH' memV' l g l' g' mb uv,
      genAExpr_rel σ aexp e memH (mk_config_cfg memV l g) (memH', mb)
                   (memV', (l', (g', uv))) ->
      memH ≡ memH'.
  Proof.
    intros * H.
    destruct H; cbn in *; intuition.
  Qed.

  Lemma genAExpr_memV : forall σ aexp e memH memV memH' memV' l g l' g' mb uv,
      genAExpr_rel σ aexp e memH (mk_config_cfg memV l g) (memH', mb)
                   (memV', (l', (g', uv))) ->
      memV ≡ memV'.
  Proof.
    intros * H.
    destruct H; cbn in *; intuition.
  Qed.

  Lemma genAExpr_g : forall σ aexp e memH memV memH' memV' l g l' g' mb uv,
      genAExpr_rel σ aexp e memH (mk_config_cfg memV l g) (memH', mb)
                   (memV', (l', (g', uv))) ->
      g ≡ g'.
  Proof.
    intros * H.
    destruct H; cbn in *; intuition.
  Qed.

  Lemma genAExpr_l : forall σ aexp e memH memV memH' memV' l g l' g' mb uv,
      genAExpr_rel σ aexp e memH (mk_config_cfg memV l g) (memH', mb)
                   (memV', (l', (g', uv))) ->
      l ⊑ l'.
  Proof.
    intros * H.
    destruct H; cbn in *; intuition.
  Qed.

  Ltac genAExpr_rel_subst_H AEXP LL :=
    match AEXP with
    | genAExpr_rel ?σ ?n ?e ?memH (mk_config_cfg ?memV ?l ?g) (?memH', ?n') (?memV', (?l', (?g', ()))) =>
      let H := fresh in
      pose proof genAExpr_memH AEXP as H; subst memH';
      pose proof genAExpr_memV AEXP as H; subst memV';
      pose proof genAExpr_g AEXP as H; subst g';
      pose proof genAExpr_l AEXP as LL
    end.

  Ltac genAExpr_rel_subst LL :=
    match goal with
    | NEXP : genAExpr_rel ?σ ?n ?e ?memH (mk_config_cfg ?memV ?l ?g) (?memH', ?n') (?memV', (?l', (?g', ()))) |- _ =>
      let H := fresh in
      pose proof genAExpr_memH NEXP as H; subst memH';
      pose proof genAExpr_memV NEXP as H; subst memV';
      pose proof genAExpr_g NEXP as H; subst g';
      pose proof genAExpr_l NEXP as LL
    end.


  (*
  Lemma genAExpr_preserves_WF:
    forall aexp s s' σ x,
      WF_IRState σ s ->
      genAExpr aexp s ≡ inr (s',x) ->
      WF_IRState σ s'.
  Proof.
    induction aexp; intros * WF GEN; cbn* in GEN; simp ; auto.
    { apply evalNexpr_preserves_WF with (σ:=σ) in Heqs0; auto.
      apply genMExpr_preserves_WF with (σ:=σ) in Heqs1; auto.
    }
    { pose proof IHaexp _ _ _ _ WF Heqs0.
      eauto.
    }

    all: eapply IHaexp1 in Heqs0; eapply IHaexp2 in Heqs1; eauto.
  Qed. *)

  (* TODO: move this *)
  Lemma int_of_nat :
    forall (i : Int64.int),
    exists (n : nat), i ≡ Int64.repr (Z.of_nat n).
  Proof.
    intros [val [LOWER UPPER]].
    Transparent Int64.repr.
    unfold Int64.repr.
    Opaque Int64.repr.
    exists (Z.to_nat val).
    rewrite Znat.Z2Nat.id by lia.

    match goal with
    | |- ?x ≡ ?y => assert (x = y) as EQ;
                    pose proof Int64.eq_spec x y as EQ_real
    end.

    { unfold equiv.
      unfold MInt64asNT.NTypeEquiv.
      unfold Int64.eq.
      cbn.
      rewrite Int64.Z_mod_modulus_eq.

      assert (val mod Int64.modulus ≡ val)%Z as H.
      apply Zdiv.Zmod_small; lia.

      rewrite H.
      apply Coqlib.zeq_true.
    }

    rewrite EQ in EQ_real.
    auto.
  Qed.

  (* TODO: move this *)
  Lemma to_nat_repr_of_nat :
    forall (n : nat),
      MInt64asNT.to_nat (Int64.repr (Z.of_nat n)) ≡ n.
  Proof.
    intros n.

    match goal with
    | |- ?x ≡ ?y => assert (x = y) as EQ
    end.

    { unfold equiv. unfold peano_naturals.nat_equiv.
      Transparent Int64.repr.
      unfold Int64.repr.
      Opaque Int64.repr.

      unfold MInt64asNT.to_nat.
      unfold Int64.intval.
      rewrite Int64.Z_mod_modulus_eq.
      assert (exists m, Int64.modulus ≡ Z.of_nat m) as (m & H).
      admit.

      rewrite H.
      rewrite <- Zdiv.mod_Zmod.
      rewrite Znat.Nat2Z.id.

      admit.
      admit.
    }

    rewrite EQ.
    auto.
  Admitted.

  Fact CTypeOne_of_longu:
    MFloat64asCT.CTypeOne ≡ Floats.Float.of_longu (DynamicValues.Int64.repr 1).
  Proof.
    Transparent DynamicValues.Int64.repr.
    unfold DynamicValues.Int64.repr.
    unfold MFloat64asCT.CTypeOne, Float64One.
    Transparent Floats.Float.of_longu.
    unfold Floats.Float.of_longu.
    unfold Binary.Bone, IEEE754_extra.BofZ, Binary.binary_normalize.
    cbn.
    f_equiv.
  Qed.

  Fact CTypeZero_of_longu:
    MFloat64asCT.CTypeZero ≡ Floats.Float.of_longu (DynamicValues.Int64.repr 0).
  Proof.
    Transparent DynamicValues.Int64.repr.
    unfold DynamicValues.Int64.repr.
    unfold MFloat64asCT.CTypeOne, Float64One.
    Transparent Floats.Float.of_longu.
    unfold Floats.Float.of_longu.
    unfold Binary.Bone, IEEE754_extra.BofZ, Binary.binary_normalize.
    cbn.
    f_equiv.
  Qed.

  (* TODO move this, possibly give it a better name. *)
  Lemma float_cmp :
    forall (a b : binary64),
    exists v,
      double_cmp FOlt a b ≡ DVALUE_I1 v /\ MFloat64asCT.CTypeZLess a b ≡ (Floats.Float.of_longu
                                                                           (DynamicValues.Int64.repr (DynamicValues.Int1.unsigned v))).
  Proof.
    intros a b.
    unfold double_cmp.
    destruct (ordered64 a b && Floats.Float.cmp Integers.Clt a b)%bool eqn:CMP.
    - exists DynamicValues.Int1.one.
      simpl.
      rewrite <- CTypeOne_of_longu.
      intuition; cbn.
      apply andb_prop in CMP.
      destruct CMP as [O C].
      unfold ordered64 in O.
      apply andb_prop in O.
      destruct O as [OA OB].
      unfold MFloat64asCT.CTypeZLess.
      Transparent Floats.Float.cmp.
      unfold Floats.Float.cmp, Floats.cmp_of_comparison, Floats.Float.compare in C.
      break_match_hyp; [|inversion C].
      break_match_hyp; inversion C; clear C.
      subst.
      unfold not_nan64 in OA, OB.
      apply Bool.negb_true_iff in OA.
      apply Bool.negb_true_iff in OB.
      destruct a; try inv OA; destruct b; try inv OB; reflexivity.
    - exists DynamicValues.Int1.zero.
      simpl.
      rewrite <- CTypeZero_of_longu.
      intuition; cbn.
      unfold MFloat64asCT.CTypeZLess.
      Transparent Floats.Float.cmp.
      unfold Floats.Float.cmp, Floats.cmp_of_comparison, Floats.Float.compare in CMP.
      unfold ordered64 in CMP.
      rewrite 2!BoolUtil.andb_eq_false in CMP.
      destruct CMP.
      +
        destruct H.
        *
          unfold not_nan64 in H.
          apply Bool.negb_false_iff in H.
          break_match.
          1,2,4: inversion H.
          reflexivity.
        *
          destruct b; try inversion H.
          unfold not_nan64 in H.
          break_match; reflexivity.
      +
        repeat break_match_hyp; subst; [| inversion H | |];
          destruct a,b; inversion Heqo; try reflexivity.
  Qed.

  Opaque denote_instr.
  Opaque denote_code.

  Lemma genAExpr_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *)   (aexp: AExpr) (σ: evalContext) (memH: memoryH) (v : binary64)
      (* Vellvm bits *)   (e: exp typ) (c: code typ) (g : global_env) (l : local_env) (memV : memoryV),

      genAExpr aexp s1 ≡ inr (s2, (e, c))      -> (* Compilation succeeds *)
      evalAExpr memH σ aexp ≡ inr v            -> (* Evaluation succeeds *)
      state_invariant σ s1 memH (memV, (l, g)) -> (* The main state invariant is initially true *)

      eutt (lift_Rel_cfg (state_invariant σ s2) ⩕ genAExpr_rel σ aexp e memH (mk_config_cfg memV l g))
           (with_err_RB (interp_Mem (denoteAExpr σ aexp) memH))
           (with_err_LB (interp_cfg (denote_code (convert_typ [] c)) g l memV)).
  Proof with rauto.
    intros s1 s2 aexp; revert s1 s2; induction aexp; intros * COMPILE EVAL PRE.
    - (* Variable case *)
      (* Reducing the compilation *)
      pose proof COMPILE as COMPILE'.
      cbn* in COMPILE; simp.

      + (* The variable maps to an integer in the IRState *)
        unfold denoteAExpr; cbn*.

        cbn...
        break_inner_match_goal.
        cbn...

        * pose proof PRE as SINV.
          destruct PRE.
          break_inner_match_goal; try abs_by_WF.

          cbn...
          destruct i0; try abs_by_WF.

          (* Globals *)
          cbn...

          epose proof (memory_invariant_GLU_AExpr _ mem_is_inv Heqo _).
          destruct H as (ptr & MAP & READ).
          rewrite typ_to_dtyp_equation in READ...

          (* rewrite denote_code_singleton; cbn. *)
          (* cbn... eauto. *)

          rewrite denote_instr_load; eauto.

          cbn...
          apply eqit_Ret.

          split.
          { cbn. eapply state_invariant_add_fresh; eauto.
          }
          {
            + split; split; intuition.
              * cbn. cbn... cbn. cbn...
                reflexivity.
                cbn.
                erewrite H; eauto.
                eapply In_add_eq.
              * cbn. unfold context_lookup.
                rewrite Heqo0.
                cbn. reflexivity.
              * apply sub_alist_add.
                apply concrete_fresh_fresh in incLocal_is_fresh.
                unfold incLocal_fresh in incLocal_is_fresh.
                eapply incLocal_is_fresh.
                cbn. eauto.
          }
          cbn... cbn... 2 : eauto. reflexivity.

        * (* Variable not in context, [context_lookup] fails *)
          cbn* in EVAL; rewrite Heqo0 in EVAL; inv EVAL.
      + (* The variable maps to a pointer *)
        unfold denoteAExpr; cbn*.
        rewrite denote_code_nil; cbn.
        cbn...
        destruct PRE.
        break_inner_match_goal; try abs_by_WF.
        * cbn...
          break_inner_match_goal; try abs_by_WF.
          subst.
          destruct i0; try abs_by_WF.
          cbn...
          apply eutt_Ret.
          split; split; eauto.
          -- split.
             { cbn... cbn...
               reflexivity.

               eapply memory_invariant_LLU_AExpr; eauto;
                 eapply memory_invariant_ext_local;
                 eauto.
             }

             cbn.
             unfold context_lookup.
             rewrite Heqo0. cbn.
             reflexivity.
        * cbn* in EVAL; rewrite Heqo0 in EVAL; inv EVAL.
    - (* Constant *)
      cbn* in COMPILE; simp.
      cbn. rewrite denote_code_nil; cbn.
      unfold denoteAExpr; cbn*.
      cbn...
      cbn...
      apply eutt_Ret.
      split; eauto.
      split; eauto.
      intros l' MONO; cbn*.
      split; try reflexivity.
      cbn in EVAL. inversion EVAL; subst.
      cbn...
      cbn...
      reflexivity.
    - (* ANth *)
      cbn* in COMPILE; simp.

      cbn* in EVAL.
      repeat (break_match; try discriminate EVAL).

      rewrite convert_typ_app.
      rewrite denote_code_app.

      (* I need to know something about c0, which is an NExpr. *)
      epose proof genNExpr_correct _ Heqs Heqs3 PRE as NEXP.

      eutt_hide_right i4.
      cbn*.
      cbn...

      subst i4.
      do 2 cbn...

      eapply eutt_clo_bind; eauto.
      intros [memH' n'] [memV' [l' [g' []]]] [SINV GENN_REL].

      (* Relate MExpr *)
      destruct GENN_REL as [NEXP_CORRECT VARS_s1_i].

      (* Need to know that memH'=memH and memV'=memV ... *)
      genNExpr_rel_subst LL'.

      cbn in SINV.

      (* Need to make sure that we pull e1 out so we can use genMExpr_correct *)
      epose proof genMExpr_correct _ Heqs0 Heqs4 SINV as MCODE.

      (* Should be able to pull e1 out from the denotation of GEP *)
      match goal with
      | |- context [ [?a; ?b] ] =>
        change [a; b] with
            ([a] ++ [b])%list
      end.

      rewrite app_assoc.
      rewrite convert_typ_app.
      rewrite denote_code_app.

      rewrite convert_typ_app.
      rewrite denote_code_app.

      eutt_hide_left i4.

      (* I want to deconstruct denote_code of OP_GetElementPtr in
         order to expose the underlying denote_exp of e1. *)
      setoid_rewrite denote_code_singleton.
      cbn.

      assert ((denote_exp (Some (typ_to_dtyp [ ] (TYPE_Pointer t)))
                          (Traversal.fmap (typ_to_dtyp [ ]) e1)) ≡ (denote_exp (Some DTYPE_Pointer) (convert_typ [ ] e1))) as He1.
      { rewrite typ_to_dtyp_equation.
        reflexivity.
      }

      pose proof (genMExpr_array Heqs0) as (sz & ARRAY); subst t.
      cbn in *.
      unfold IntType.
      repeat rewrite typ_to_dtyp_equation in *.
      cbn.

      cbn...
      subst i4.
      cbn...

      eapply eutt_clo_bind; eauto.
      unfold Traversal.endo, Traversal.Endo_id.
      intros [memH'' [b' bk_size]] [memV'' [l'' [g'' []]]] MINV.
      destruct MINV as (SINV'' & MINV).
      genMExpr_rel_subst.
      destruct MINV as [[MINV EVAL_MEXP] PRES].
      destruct MINV as (ptr & ptr_id & vid & mid & size & sz_array & EUTT_e1 & MINV).
      symmetry in EUTT_e1.
      epose proof denote_instr_gep_array r sz DTYPE_Double _ (Traversal.fmap (typ_to_dtyp [ ]) e0) (MInt64asNT.to_nat i2) _ _ _ _ _ _ EUTT_e1 as GEP.
      edestruct GEP as [ptr_res [READ EUTT_GEP]].
      3: {
        cbn...
        (* i2 / n'... *)
        rewrite EUTT_GEP.
        cbn...

        rewrite denote_instr_load; eauto.
        cbn...

        assert (mem_lookup (MInt64asNT.to_nat n') b' ≡ Some b) as LUPn'b'.
        { (* i2 = n', because:

           Heqs3: evalNExpr σ n = inr i2
           NEXP_CORRECT : genNExpr_rel σ n e0 memH (mk_config_cfg memV l g) (memH, n') (memV, (l', (g, ())))
           *)
          destruct NEXP_CORRECT as (NEXP_CORRECT & _).
          assert (l' ⊑ l') as L'L' by reflexivity.
          specialize (NEXP_CORRECT _ L'L') as (_ & NEXP_EVAL).
          rewrite Heqs3 in NEXP_EVAL; inv NEXP_EVAL.

          (* m0 = b', because:

           Heqs4 : evalMExpr memH σ m ≡ inr m0
           MINV : (lift_Rel_cfg (state_invariant σ i0) ⩕ genMExpr_rel σ i0 memH (mk_config_cfg memV l' g))
           (memH'', b') (memV'', (l'', (g'', uv'')))

           *)

          rewrite Heqs4 in EVAL_MEXP; inv EVAL_MEXP.
          auto.
        }

        rewrite LUPn'b'.
        cbn...

        apply eutt_Ret.
        split.
        + do 2 (eapply state_invariant_add_fresh; eauto).
        + split; split; intuition.
          * cbn. cbn... cbn. cbn...
            reflexivity.
            cbn.
            apply H.
            apply In_add_eq.
          * (* TODO: ltac, this is horrid *)
            cbn.
            rewrite Heqs3.
            rewrite Heqs4.
            rewrite Heqs5.
            apply mem_lookup_err_inr_Some_eq.
            auto.
          * eapply sub_alist_trans; eauto.
            eapply sub_alist_trans; eapply sub_alist_add.
            -- eapply concrete_fresh_fresh; eauto.
               eapply incLocal_is_fresh; eauto.
            -- eapply concrete_fresh_fresh; eauto.
               eapply incLocal_is_fresh; eauto.
               eapply state_invariant_add_fresh; eauto.
        + cbn.
          do 2 rewrite translate_trigger.
            rewrite lookup_E_to_exp_E_Local.
            rewrite subevent_subevent.
            rewrite exp_E_to_instr_E_Local.
            rewrite subevent_subevent.
            rewrite interp_cfg_to_L3_LR.
            cbn.
            reflexivity.
            apply lookup_alist_add_eq.
      }
      { destruct NEXP_CORRECT.
        unfold genNExpr_exp_correct in exp_correct.
        assert (l' ⊑ l') as L'L' by reflexivity.
        specialize (exp_correct _ L'L') as (EUTT_e0 & EVAL_n).
        rewrite <- EUTT_e0.

        (* can probably use Heqs5 (assert_NT_lt) for this... i2 = n'
        by Heqs3, and I think i3 is the size of a block. *)
        unfold assert_NT_lt in Heqs5.
        assert (i2 ≡ n') as N'.
        { rewrite Heqs3 in EVAL_n.
          inv EVAL_n.
          reflexivity.
        }

        rewrite N'.

        (* TODO: extract to lemma *)
        unfold MInt64asNT.to_nat.
        rewrite Znat.Z2Nat.id.
        rewrite repr_intval.

        reflexivity.

        pose proof Integers.Int64.intrange n'.
        lia.
      }
      { (* follows from mem_lookup, Heqo *)
        (* m0 = b' by evalMExpr hypotheses *)
        destruct MINV as (MLUP & INLG & NTH_σ_vid & NTH_Γ_vid).

        pose proof state_invariant_memory_invariant SINV'' as MEMINV.
        epose proof MEMINV _ _ _ _ NTH_σ_vid NTH_Γ_vid as GET_ARRAY.
        cbn in GET_ARRAY.
        destruct GET_ARRAY as (bk_h & ptr_v & MLUP' & ILG' & GET_ARRAY).

        (* Need to show that m0 = bk_h *)
        assert (m0 ≡ bk_h) as M0BK.
        { rewrite Heqs4 in EVAL_MEXP.
          inv EVAL_MEXP.
          rewrite MLUP in MLUP'.
          inv MLUP'.
          reflexivity.
        }
        subst.

        (* Need to show ptr = ptr_v *)
        assert (ptr ≡ ptr_v).
        { destruct ptr_id;
          cbn in INLG, ILG';
          rewrite INLG in ILG';
          inversion ILG';
          auto.
        }

        subst.

        auto.
      }
    - (* AAbs *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in COMPILE; simp.

      cbn in EVAL.
      break_match; try discriminate EVAL.

      cbn*.
      cbn...

      (* TODO: Ltac for this. *)
      rewrite convert_typ_app.
      rewrite denote_code_app.

      cbn...
      eapply eutt_clo_bind; try eapply IHaexp; eauto.

      intros [memH2 b2] [memV2 [l2 [g2 []]]] [SINV EXPR_REL].
      cbn in SINV.
      destruct EXPR_REL as [AEXPR EXT].
      unfold genAExpr_exp_correct in AEXPR.
      unfold ext_local in EXT.
      cbn in EXT.
      cbn...

      cbn.
      cbn...

      epose proof (AEXPR l2 _) as [EUTT EVAL'].
      (* rewrite denote_code_singleton. *)
      (* YZ TODO: should not have made assoc opaque *)
      Transparent assoc.
      rewrite denote_instr_intrinsic; cbn.
      2,3:reflexivity.
      4: {
        unfold Monad.eqm, ITreeMonad.EqM_ITree.
        cbn.
        setoid_rewrite bind_ret_l.
        rewrite interp_cfg_to_L3_bind.
        rewrite <- EUTT.
        setoid_rewrite bind_ret_l.
        rewrite interp_cfg_to_L3_ret.
        reflexivity.
      }
      2: {
        cbn.
        repeat rewrite bind_ret_l.
        rewrite interp_cfg_to_L3_ret.
        reflexivity.
      }
      2: {
        cbn. reflexivity.
      }

      cbn...

      apply eqit_Ret.

      (* TODO: This is repeated a lot... Ltac? *)
      split.
      + eapply state_invariant_add_fresh; eauto.
      + split; split; intuition.
        * cbn. cbn... cbn. cbn...
          reflexivity.
          cbn.

          apply H.
          apply In_add_eq.
        * (* TODO: ltac, this is horrid *)
          cbn. rewrite EVAL'.
          reflexivity.
        * rewrite H3.
          apply sub_alist_add.
          eapply concrete_fresh_fresh; eauto.
          eapply incLocal_is_fresh; eauto.
    - (* APlus *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in COMPILE; simp.

      (* YZ TODO Ltac for this *)
      cbn in EVAL.
      break_match; try discriminate EVAL.
      break_match; try discriminate EVAL.

      cbn*.
      cbn...

      rewrite convert_typ_app.
      rewrite denote_code_app.
      cbn...

      eapply eutt_clo_bind; try eapply IHaexp1; eauto.

      intros [memH' b'] [memV' [l' [g' []]]] [INV1 INV2].
      cbn in *.

      cbn...

      rewrite convert_typ_app.
      rewrite denote_code_app.
      cbn...

      inversion INV2.
      inversion amonotone0.
      subst.
      eapply eutt_clo_bind; try eapply IHaexp2; eauto.

      intros [memH'' b''] [memV'' [l'' [g'' []]]] [INV1' INV2'].
      inversion INV2'.
      inversion amonotone1.
      subst.

      cbn...
      cbn. cbn...

      unfold genAExpr_exp_correct in aexp_correct0.
      do 2 destruct H1.
      subst.
      specialize (aexp_correct0 l'').
      assert (Ret (memV'', (l'', (g'', UVALUE_Double b')))
                    ≈ interp_cfg
                    (translate exp_E_to_instr_E
                               (denote_exp (Some DTYPE_Double) (convert_typ [ ] e0))) g'' l'' memV'') as EUTT0.
      {
        apply aexp_correct0; eauto.
      }

      unfold genAExpr_exp_correct in aexp_correct1.
      assert (Ret (memV'', (l'', (g'', UVALUE_Double b'')))
                      ≈ interp_cfg
                      (translate exp_E_to_instr_E
                                 (denote_exp (Some DTYPE_Double) (convert_typ [ ] e1))) g'' l'' memV'') as EUTT1.
      { assert (l'' ⊑ l'') as L''L'' by reflexivity.
        apply aexp_correct1; eauto.
      }

      rewrite denote_instr_op.
      2: {
        eapply denote_fbinop_concrete; cbn; eauto; try reflexivity.
      }

      cbn.
      cbn...

      apply eqit_Ret.
      split; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
      + split; split; intuition.
        * cbn. cbn... cbn. cbn...
          reflexivity.
          cbn.

          apply H.
          apply In_add_eq.
        * (* TODO: ltac, this is horrid *)
          cbn. rewrite H6.
          epose proof (aexp_correct1 l'' _) as [[] H7].
          rewrite H7.

          reflexivity.
        * rewrite H3, H2.
          apply sub_alist_add.
          eapply concrete_fresh_fresh; eauto.
          eapply incLocal_is_fresh; eauto.
    - (* AMinus *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in COMPILE; simp.

      (* YZ TODO Ltac for this *)
      cbn in EVAL.
      break_match; try discriminate EVAL.
      break_match; try discriminate EVAL.

      Opaque denote_code.
      cbn*.
      cbn...

      rewrite convert_typ_app.
      rewrite denote_code_app.
      cbn...

      eapply eutt_clo_bind; try eapply IHaexp1; eauto.

      intros [memH' b'] [memV' [l' [g' []]]] [INV1 INV2].
      cbn in *.

      cbn...

      rewrite convert_typ_app.
      rewrite denote_code_app.
      cbn...

      inversion INV2.
      inversion amonotone0.
      subst.
      eapply eutt_clo_bind; try eapply IHaexp2; eauto.

      intros [memH'' b''] [memV'' [l'' [g'' []]]] [INV1' INV2'].
      inversion INV2'.
      inversion amonotone1.
      subst.

      cbn...
      cbn. cbn...

      unfold genAExpr_exp_correct in aexp_correct0.
      do 2 destruct H1.
      subst.
      specialize (aexp_correct0 l'').
      assert (Ret (memV'', (l'', (g'', UVALUE_Double b')))
                    ≈ interp_cfg
                    (translate exp_E_to_instr_E
                               (denote_exp (Some DTYPE_Double) (convert_typ [ ] e0))) g'' l'' memV'') as EUTT0.
      {
        apply aexp_correct0; eauto.
      }

      unfold genAExpr_exp_correct in aexp_correct1.
      assert (Ret (memV'', (l'', (g'', UVALUE_Double b'')))
                      ≈ interp_cfg
                      (translate exp_E_to_instr_E
                                 (denote_exp (Some DTYPE_Double) (convert_typ [ ] e1))) g'' l'' memV'') as EUTT1.
      { assert (l'' ⊑ l'') as L''L'' by reflexivity.
        apply aexp_correct1; eauto.
      }

      rewrite denote_instr_op.
      2: {
        eapply denote_fbinop_concrete; cbn; eauto; try reflexivity.
      }

      cbn.
      cbn...

      apply eqit_Ret.
      split; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
      + split; split; intuition.
        * cbn. cbn... cbn. cbn...
          reflexivity.
          cbn.

          apply H.
          apply In_add_eq.
        * (* TODO: ltac, this is horrid *)
          cbn. rewrite H6.
          epose proof (aexp_correct1 l'' _) as [[] H7].
          rewrite H7.

          reflexivity.
        * rewrite H3, H2.
          apply sub_alist_add.
          eapply concrete_fresh_fresh; eauto.
          eapply incLocal_is_fresh; eauto.
    - (* AMult *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in COMPILE; simp.

      (* YZ TODO Ltac for this *)
      cbn in EVAL.
      break_match; try discriminate EVAL.
      break_match; try discriminate EVAL.

      Opaque denote_code.
      cbn*.
      cbn...

      rewrite convert_typ_app.
      rewrite denote_code_app.
      cbn...

      eapply eutt_clo_bind; try eapply IHaexp1; eauto.

      intros [memH' b'] [memV' [l' [g' []]]] [INV1 INV2].
      cbn in *.

      cbn...

      rewrite convert_typ_app.
      rewrite denote_code_app.
      cbn...

      inversion INV2.
      inversion amonotone0.
      subst.
      eapply eutt_clo_bind; try eapply IHaexp2; eauto.

      intros [memH'' b''] [memV'' [l'' [g'' []]]] [INV1' INV2'].
      inversion INV2'.
      inversion amonotone1.
      subst.

      cbn...
      cbn. cbn...

      unfold genAExpr_exp_correct in aexp_correct0.
      do 2 destruct H1.
      subst.
      specialize (aexp_correct0 l'').
      assert (Ret (memV'', (l'', (g'', UVALUE_Double b')))
                    ≈ interp_cfg
                    (translate exp_E_to_instr_E
                               (denote_exp (Some DTYPE_Double) (convert_typ [ ] e0))) g'' l'' memV'') as EUTT0.
      {
        apply aexp_correct0; eauto.
      }

      unfold genAExpr_exp_correct in aexp_correct1.
      assert (Ret (memV'', (l'', (g'', UVALUE_Double b'')))
                      ≈ interp_cfg
                      (translate exp_E_to_instr_E
                                 (denote_exp (Some DTYPE_Double) (convert_typ [ ] e1))) g'' l'' memV'') as EUTT1.
      { assert (l'' ⊑ l'') as L''L'' by reflexivity.
        apply aexp_correct1; eauto.
      }

      rewrite denote_instr_op.
      2: {
        eapply denote_fbinop_concrete; cbn; eauto; try reflexivity.
      }

      cbn.
      cbn...

      apply eqit_Ret.
      split; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
      + split; split; intuition.
        * cbn. cbn... cbn. cbn...
          reflexivity.
          cbn.

          apply H.
          apply In_add_eq.
        * (* TODO: ltac, this is horrid *)
          cbn. rewrite H6.
          epose proof (aexp_correct1 l'' _) as [[] H7].
          rewrite H7.

          reflexivity.
        * rewrite H3, H2.
          apply sub_alist_add.
          eapply concrete_fresh_fresh; eauto.
          eapply incLocal_is_fresh; eauto.
    - (* AMin *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in COMPILE; simp.

      (* YZ TODO Ltac for this *)
      cbn in EVAL.
      break_match; try discriminate EVAL.
      break_match; try discriminate EVAL.

      Opaque denote_code.
      cbn*.
      cbn...

      rewrite convert_typ_app.
      rewrite denote_code_app.
      cbn...

      eapply eutt_clo_bind; try eapply IHaexp1; eauto.

      intros [memH' b'] [memV' [l' [g' []]]] [INV1 INV2].
      cbn in *.

      cbn...

      rewrite convert_typ_app.
      rewrite denote_code_app.
      cbn...

      inversion INV2.
      inversion amonotone0.
      subst.
      eapply eutt_clo_bind; try eapply IHaexp2; eauto.

      intros [memH'' b''] [memV'' [l'' [g'' []]]] [INV1' INV2'].
      inversion INV2'.
      inversion amonotone1.
      subst.

      cbn...
      cbn. cbn...

      unfold genAExpr_exp_correct in aexp_correct0.
      do 2 destruct H1.
      subst.
      specialize (aexp_correct0 l'').
      assert (Ret (memV'', (l'', (g'', UVALUE_Double b')))
                    ≈ interp_cfg
                    (translate exp_E_to_instr_E
                               (denote_exp (Some DTYPE_Double) (convert_typ [ ] e0))) g'' l'' memV'') as EUTT0.
      {
        apply aexp_correct0; eauto.
      }

      unfold genAExpr_exp_correct in aexp_correct1.
      assert (Ret (memV'', (l'', (g'', UVALUE_Double b'')))
                      ≈ interp_cfg
                      (translate exp_E_to_instr_E
                                 (denote_exp (Some DTYPE_Double) (convert_typ [ ] e1))) g'' l'' memV'') as EUTT1.
      { assert (l'' ⊑ l'') as L''L'' by reflexivity.
        apply aexp_correct1; eauto.
      }
      rewrite denote_instr_intrinsic; cbn; eauto.

      2: cbn; eauto.
      4: {
        rewrite interp_cfg_to_L3_bind.
        rewrite <- EUTT0.
        rewrite bind_ret_l.
        rewrite bind_bind.
        rewrite interp_cfg_to_L3_bind.
        rewrite <- EUTT1.
        repeat rewrite bind_ret_l.
        rewrite interp_cfg_to_L3_ret.
        reflexivity.
      }
      2: {
        cbn.
        repeat rewrite bind_ret_l.
        rewrite interp_cfg_to_L3_ret.
        reflexivity.
      }
      2: {
        cbn. reflexivity.
      }

      cbn.
      cbn...

      apply eqit_Ret.
      split; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
      + split; split; intuition.
        * cbn. cbn... cbn. cbn...
          reflexivity.
          cbn.

          apply H.

          (* TODO: Can't unfold Floats.Float.add ??? *)
          assert (Float_minimum b' b'' ≡ MFloat64asCT.CTypeMin b' b'').
          admit.

          rewrite H3.
          apply In_add_eq.
        * (* TODO: ltac, this is horrid *)
          cbn. rewrite H6.
          epose proof (aexp_correct1 l'' _) as [[] H7].
          rewrite H7.

          reflexivity.
        * rewrite H3, H2.
          apply sub_alist_add.
          eapply concrete_fresh_fresh; eauto.
          eapply incLocal_is_fresh; eauto.
    - (* AMax *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in COMPILE; simp.

      (* YZ TODO Ltac for this *)
      cbn in EVAL.
      break_match; try discriminate EVAL.
      break_match; try discriminate EVAL.

      Opaque denote_code.
      cbn*.
      cbn...

      rewrite convert_typ_app.
      rewrite denote_code_app.
      cbn...

      eapply eutt_clo_bind; try eapply IHaexp1; eauto.

      intros [memH' b'] [memV' [l' [g' []]]] [INV1 INV2].
      cbn in *.

      cbn...

      rewrite convert_typ_app.
      rewrite denote_code_app.
      cbn...

      inversion INV2.
      inversion amonotone0.
      subst.
      eapply eutt_clo_bind; try eapply IHaexp2; eauto.

      intros [memH'' b''] [memV'' [l'' [g'' []]]] [INV1' INV2'].
      inversion INV2'.
      inversion amonotone1.
      subst.

      cbn...
      cbn. cbn...

      unfold genAExpr_exp_correct in aexp_correct0.
      do 2 destruct H1.
      subst.
      specialize (aexp_correct0 l'').
      assert (Ret (memV'', (l'', (g'', UVALUE_Double b')))
                    ≈ interp_cfg
                    (translate exp_E_to_instr_E
                               (denote_exp (Some DTYPE_Double) (convert_typ [ ] e0))) g'' l'' memV'') as EUTT0.
      {
        apply aexp_correct0; eauto.
      }

      unfold genAExpr_exp_correct in aexp_correct1.
      assert (Ret (memV'', (l'', (g'', UVALUE_Double b'')))
                      ≈ interp_cfg
                      (translate exp_E_to_instr_E
                                 (denote_exp (Some DTYPE_Double) (convert_typ [ ] e1))) g'' l'' memV'') as EUTT1.
      { assert (l'' ⊑ l'') as L''L'' by reflexivity.
        apply aexp_correct1; eauto.
      }


      rewrite denote_instr_intrinsic; cbn; eauto.
      2: cbn; eauto.
      4: {
        rewrite interp_cfg_to_L3_bind.
        rewrite <- EUTT0.
        rewrite bind_ret_l.
        rewrite bind_bind.
        rewrite interp_cfg_to_L3_bind.
        rewrite <- EUTT1.
        repeat rewrite bind_ret_l.
        rewrite interp_cfg_to_L3_ret.
        reflexivity.
      }
      2: {
        cbn.
        repeat rewrite bind_ret_l.
        rewrite interp_cfg_to_L3_ret.
        reflexivity.
      }
      2: {
        cbn. reflexivity.
      }

      cbn.
      cbn...

      apply eqit_Ret.
      split; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
      + split; split; intuition.
        * cbn. cbn... cbn. cbn...
          reflexivity.
          cbn.

          apply H.

          (* TODO: Can't unfold Floats.Float.add ??? *)
          assert (Float_maxnum b' b'' ≡ MFloat64asCT.CTypeMax b' b'').
          admit.

          rewrite H3.
          apply In_add_eq.
        * (* TODO: ltac, this is horrid *)
          cbn. rewrite H6.
          epose proof (aexp_correct1 l'' _) as [[] H7].
          rewrite H7.

          reflexivity.
        * rewrite H3, H2.
          apply sub_alist_add.
          eapply concrete_fresh_fresh; eauto.
          eapply incLocal_is_fresh; eauto.
    - (* AZless *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in COMPILE; simp.
      (* YZ TODO Ltac for this *)
      cbn in EVAL.
      break_match; try discriminate EVAL.
      break_match; try discriminate EVAL.
      Opaque denote_code.
      cbn*.
      cbn...
      rewrite convert_typ_app.
      rewrite denote_code_app.
      cbn...
      eapply eutt_clo_bind; try eapply IHaexp1; eauto.
      intros [memH' b'] [memV' [l' [g' []]]] [INV1 INV2].
      cbn in *.
      cbn...
      rewrite convert_typ_app.
      rewrite denote_code_app.
      cbn...
      inversion INV2.
      inversion amonotone0.
      subst.
      eapply eutt_clo_bind; try eapply IHaexp2; eauto.
      intros [memH'' b''] [memV'' [l'' [g'' []]]] [INV1' INV2'].
      inversion INV2'.
      inversion amonotone1.
      subst.
      cbn...
      cbn. cbn...
      unfold genAExpr_exp_correct in aexp_correct0.
      do 2 destruct H1.
      subst.
      specialize (aexp_correct0 l'').
      assert (Ret (memV'', (l'', (g'', UVALUE_Double b')))
                    ≈ interp_cfg
                    (translate exp_E_to_instr_E
                               (denote_exp (Some DTYPE_Double) (convert_typ [ ] e0))) g'' l'' memV'') as EUTT0.
      {
        apply aexp_correct0; eauto.
      }
      unfold genAExpr_exp_correct in aexp_correct1.
      assert (Ret (memV'', (l'', (g'', UVALUE_Double b'')))
                      ≈ interp_cfg
                      (translate exp_E_to_instr_E
                                 (denote_exp (Some DTYPE_Double) (convert_typ [ ] e1))) g'' l'' memV'') as EUTT1.
      { assert (l'' ⊑ l'') as L''L'' by reflexivity.
        apply aexp_correct1; eauto.
      }
      match goal with
      | |- context [ denote_code [?a; ?b; ?c] ] =>
        change [a; b; c] with
            ([a] ++ [b] ++ [c])%list
      end.
      repeat setoid_rewrite denote_code_app.
      cbn...
      setoid_rewrite denote_code_singleton.
      rewrite denote_instr_op.
      2: {
        eapply denote_fcmp_concrete; cbn; eauto; try reflexivity.
      }
      cbn.
      cbn...
      setoid_rewrite denote_code_singleton.
      rewrite denote_instr_comment.
      cbn...

      pose proof (float_cmp b' b'') as (cmp_res & CMP_V & CMP_H).

      rewrite denote_instr_op.
      2: {
        (* TODO: clean this up... *)
        set (DVALUE_Double
       (Floats.Float.of_longu (DynamicValues.Int64.repr (DynamicValues.Int1.unsigned cmp_res)))) as x.
        set (alist_add (Traversal.endo r) (dvalue_to_uvalue (double_cmp (Traversal.endo FOlt) b' b'')) l'') as l'''.
        pose proof denote_conversion_concrete Uitofp (DTYPE_I 1) DTYPE_Double (EXP_Ident (ID_Local (Traversal.endo r))) g'' l''' memV'' x (dvalue_to_uvalue (double_cmp (Traversal.endo FOlt) b' b'')).
        cbn.
        (* YZ: Sorry I broke this one but this is too ugly to debug, we'll have to redo the proof anyway.
           The goal is to have Vellvm side automation in the style of norm for this.
         *)
        admit.

        (* rewrite H. *)
        (* reflexivity. *)
        (* rewrite uvalue_to_dvalue_of_dvalue_to_uvalue. reflexivity. *)
        (* cbn. *)
        (* unfold Traversal.endo. *)
        (* unfold Traversal.Endo_id. *)
        (* match_rewrite. *)
        (* reflexivity. *)

        (* cbn. *)
        (* rewrite translate_trigger. *)
        (* rewrite translate_trigger. *)
        (* rewrite lookup_E_to_exp_E_Local. *)
        (* rewrite subevent_subevent. *)
        (* rewrite exp_E_to_instr_E_Local. *)
        (* rewrite subevent_subevent. *)
        (* rewrite interp_cfg_to_L3_LR. *)
        (* cbn. *)

        (* reflexivity. *)

        (* (* Lookup *) *)
        (* unfold Traversal.endo, Traversal.Endo_id in *. *)
        (* subst l'''. *)
        (* apply In_add_eq. *)
      }

      cbn...

      apply eqit_Ret.
      split; cbn; eauto.
      + cbn.
        eapply state_invariant_incVoid; eauto.
        repeat (eapply state_invariant_add_fresh; eauto).
      + split; split; intuition.
          * cbn. cbn... cbn.
            reflexivity.
            cbn.
            apply H.
            rewrite CMP_H.

            apply In_add_eq.
          * cbn.

            repeat match_rewrite.
            epose proof (aexp_correct1 l'' _) as [[] EVAL'].
            rewrite Heqs5 in EVAL'.
            inv EVAL'.
            reflexivity.
          * assert (l1 ⊑ l') as L1L' by auto.
            assert (l' ⊑ l'') as L'L'' by auto.
            rewrite L1L', L'L''.

            cbn.

            assert (l'' ⊑ (alist_add r (UVALUE_I1 cmp_res) l'')) as TRANS.
            { apply sub_alist_add.
              eapply concrete_fresh_fresh; eauto.
              eapply incLocal_is_fresh; eauto.
            }

            eapply (sub_alist_trans _ _ _ TRANS).

            eapply sub_alist_add.
            eapply concrete_fresh_fresh; eauto.
            eapply incLocal_is_fresh; eauto.
            eapply state_invariant_add_fresh; eauto.
  Admitted.

End AExpr.
