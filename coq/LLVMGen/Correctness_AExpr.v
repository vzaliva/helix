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
Require Import Helix.LLVMGen.Correctness_NExpr.
Require Import Helix.LLVMGen.Correctness_MExpr.

Set Implicit Arguments.
Set Strict Implicit.

Import MDSHCOLOnFloat64.
Import D.
Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

Require Import Vellvm.InstrLemmas.

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
      intuition; cbn.
      admit.
    - exists DynamicValues.Int1.zero.
      intuition; cbn.
  Admitted.


  Opaque denote_instr.

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
  Proof.
    intros s1 s2 aexp; revert s1 s2; induction aexp; intros * COMPILE EVAL PRE.
    - (* Variable case *)
      (* Reducing the compilation *)
      pose proof COMPILE as COMPILE'.
      cbn* in COMPILE; simp.

      + (* The variable maps to an integer in the IRState *)
        unfold denoteAExpr; cbn*.

        repeat norm_v.
        break_inner_match_goal.
        repeat norm_h.

        * pose proof PRE as SINV.
          destruct PRE.
          break_inner_match_goal; try abs_by_WF.

          repeat norm_h.
          destruct i0; try abs_by_WF.

          (* Globals *)
          cbn.
          epose proof (memory_invariant_GLU_AExpr _ mem_is_inv Heqo Heqo0).
          destruct H as (ptr & MAP & READ).

          rewrite denote_code_sing; cbn.
          repeat norm_v; eauto.

          rewrite denote_instr_load; eauto.

          (* TODO: can this be cleaned up? *)
          2: {
            cbn.
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
            cbn.
            reflexivity.
          }

          cbn; norm_v.
          apply eqit_Ret.
          split.
          { cbn. eapply state_invariant_add_fresh; eauto.
          }
          {
            + split; split; intuition.
              * cbn. repeat norm_v. cbn. norm_v.
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
        * (* Variable not in context, [context_lookup] fails *)
          cbn* in EVAL; rewrite Heqo0 in EVAL; inv EVAL.
      + (* The variable maps to a pointer *)
        unfold denoteAExpr; cbn*.
        rewrite denote_code_nil; cbn.
        repeat norm_v.
        destruct PRE.
        break_inner_match_goal; try abs_by_WF.
        * repeat norm_h.
          break_inner_match_goal; try abs_by_WF.
          subst.
          destruct i0; try abs_by_WF.
          repeat norm_h.
          apply eutt_Ret.
          split; split; eauto.
          -- split.
             { cbn; repeat norm_v; cbn; repeat norm_v; eauto.
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
      repeat norm_h.
      repeat norm_v.
      apply eutt_Ret.
      split; eauto.
      split; eauto.
      intros l' MONO; cbn*.
      split; try reflexivity.
      cbn in EVAL. inversion EVAL; subst.
      repeat norm_h.
      repeat norm_v.
      reflexivity.
    - (* ANth *)
      cbn* in COMPILE; simp.

      cbn* in EVAL.
      repeat (break_match; try discriminate EVAL).

      rewrite convert_typ_app.
      rewrite denote_code_app.

      (* I need to know something about c0, which is an NExpr. *)
      epose proof genNExpr_correct _ Heqs Heqs3 PRE as NEXP.

      eutt_hide_right.
      cbn*.
      repeat norm_h.

      subst i4.
      do 2 norm_v.

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

      eutt_hide_left.

      (* I want to deconstruct denote_code of OP_GetElementPtr in
         order to expose the underlying denote_exp of e1. *)
      setoid_rewrite denote_code_sing.
      cbn.

      (* TODO: avoid this... Want to use GEP lemma for denote_instr *)
      Transparent denote_instr.
      unfold denote_instr at 2.
      Opaque denote_instr.
      cbn.

      assert ((denote_exp (Some (typ_to_dtyp [ ] (TYPE_Pointer t)))
                          (Traversal.fmap (typ_to_dtyp [ ]) e1)) ≡ (denote_exp (Some DTYPE_Pointer) (convert_typ [ ] e1))) as He1.
      { rewrite typ_to_dtyp_equation.
        reflexivity.
      }

      rewrite He1.

      repeat rewrite <- bind_bind.
      setoid_rewrite translate_bind.
      rewrite <- bind_bind.

      set (ITree.bind (denote_code (convert_typ [ ] c1))
                      (λ _ : (),
                             translate exp_E_to_instr_E
                                       (denote_exp (Some DTYPE_Pointer) (convert_typ [ ] e1)))) as MYBIND.

      repeat norm_v.
      subst i4.
      subst MYBIND.
      repeat norm_h.

      eapply eutt_clo_bind.
      apply MCODE.

      intros [memH'' [b' bk_size]] [memV'' [l'' [g'' uv'']]] MINV.

      clear He1.

      repeat norm_v.

      destruct MINV as (SINV'' & MINV).

      (* Need to know that genMExpr does not affect memH / memV / g / l *)
      genMExpr_rel_subst.

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

        destruct MINV as (MINV & _).
        destruct MINV as (MINV & EVAL_MEXP).
        rewrite Heqs4 in EVAL_MEXP; inv EVAL_MEXP.

        auto.
      }

      rewrite LUPn'b'.
      repeat norm_h.

      cbn*.
      repeat rewrite typ_to_dtyp_equation.
      cbn*. repeat norm_v.
      destruct NEXP_CORRECT.
      unfold genNExpr_exp_correct in exp_correct.
      subst.
      assert (l' ⊑ l') as L'L' by reflexivity.
      specialize (exp_correct _ L'L') as (NEXP_EUTT & NEXP_EVAL).
      setoid_rewrite <- NEXP_EUTT.

      repeat norm_v.

      destruct MINV as (MINV & PRESERVES).
      destruct MINV as ((ptr & i' & vid & mid & size & sz & RES & rest) & EVAL_MEXP).
      destruct rest as (MLUP & ILG & NTH_σ_vid & NTH_Γ_vid).
      subst uv''.

      cbn.
      unfold ITree.map.
      repeat norm_v.

      pose proof int_of_nat n' as (n'_nat & Hn').
      rewrite Hn'.

      (* Long path to rewriting with GEP lemma... *)
      pose proof genMExpr_array Heqs0 as (sz' & ARRAY).
      rewrite ARRAY.
      rewrite typ_to_dtyp_equation.
      rewrite exp_E_to_instr_E_Memory, subevent_subevent.
      epose proof interp_cfg_to_L3_GEP_array _ (DTYPE_Array sz' DTYPE_Double).

      destruct i'; cbn in ILG.
      { destruct ILG as (? & ? & CONTRA & REST).
        inv CONTRA. }

      cbn in SINV''.
      pose proof state_invariant_memory_invariant SINV'' as MINV.
      epose proof memory_invariant_LLU_Ptr vid MINV NTH_Γ_vid NTH_σ_vid as (bk_h & ptr_v & MLUP' & ILG' & GET_ARRAY).
      assert (ptr_v ≡ ptr).
      { (* ptr_v comes from memory_invariant_LLU_Ptr *)
        (* ILG : l' @ id = Some (UVALUE_Addr ptr) *)
        (* Use ILG' to relate... *)
        cbn in ILG'.
        rewrite ILG in ILG'.
        inversion ILG'.
        auto.
      }
      subst.

      rewrite MLUP in MLUP'. inv MLUP'.

      replace (MInt64asNT.to_nat (Int64.repr (Z.of_nat n'_nat))) with n'_nat in LUPn'b'.
      2: { symmetry. apply to_nat_repr_of_nat. }
      specialize (GET_ARRAY n'_nat b LUPn'b').
      epose proof interp_cfg_to_L3_GEP_array helix_intrinsics DTYPE_Double ptr sz' g l' memV _ n'_nat GET_ARRAY as (ptr' & EUTT_GEP & READ).

      rewrite EUTT_GEP.
      repeat norm_v.

      rewrite interp_cfg_to_L3_LW; cbn.
      repeat norm_v; cbn.

      rewrite denote_instr_load; cbn; eauto.

      2: {
        rewrite translate_trigger.
        rewrite translate_trigger.

        rewrite exp_E_to_instr_E_subevent.
        rewrite lookup_E_to_exp_E_Local.
        rewrite subevent_subevent.
        setoid_rewrite interp_cfg_to_L3_LR.
        cbn.
        reflexivity.
        apply lookup_alist_add_eq.
      }

      norm_v.

      (* TODO: Can probably be smarter about this *)
      Transparent incLocal.
      assert (r ≡ Name ("l" @@ string_of_nat (local_count i0))) as EQr.
      { unfold incLocal in Heqs1.
        cbn in Heqs1.
        inversion Heqs1.
        reflexivity.
      }
      assert (r0 ≡ Name ("l" @@ string_of_nat (local_count i1))) as EQr0.
      { unfold incLocal in Heqs2.
        cbn in Heqs2.
        inversion Heqs2.
        reflexivity.
      }
      Opaque incLocal.

      apply eqit_Ret.
      split.
      + do 2 (eapply state_invariant_add_fresh; eauto).
      + split; split; intuition.
        * cbn. repeat norm_v. cbn. norm_v.
          reflexivity.
          cbn.
          apply H0.
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
          -- unfold alist_fresh.
             apply alist_find_None.
             intros v0 IN.
             eapply In__alist_In in IN as [v' AIN].
             apply incLocal_is_fresh in SINV''.
             eapply SINV''; eauto.
          -- unfold alist_fresh.
             apply alist_find_None.
             intros v0 IN.
             eapply In__alist_In in IN as [v' AIN].
             epose proof (state_invariant_incLocal Heqs1 SINV'') as SINV_i1.
             apply incLocal_is_fresh in SINV_i1.
             eapply SINV_i1 with (id:=r0) (v:=v'); eauto.
             apply In_add_ineq_iff in AIN; auto.
             intros CONTRA; subst.
             (* TODO: don't do this :( *)
             Transparent incLocal.
             unfold incLocal in Heqs1.
             Opaque incLocal.
             cbn in Heqs1. inversion Heqs1.
             rewrite <- H2 in CONTRA.
             cbn in CONTRA.
             unfold Traversal.endo, Traversal.Endo_id in CONTRA.
             apply Name_inj, append_factor_left,string_of_nat_inj in CONTRA; lia.
    - (* AAbs *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in COMPILE; simp.

      cbn in EVAL.
      break_match; try discriminate EVAL.

      cbn*.
      repeat norm_h.

      (* TODO: Ltac for this. *)
      rewrite convert_typ_app.
      rewrite denote_code_app.

      repeat norm_v.
      eapply eutt_clo_bind; try eapply IHaexp; eauto.

      intros [memH2 b2] [memV2 [l2 [g2 []]]] [SINV EXPR_REL].
      cbn in SINV.
      destruct EXPR_REL as [AEXPR EXT].
      unfold genAExpr_exp_correct in AEXPR.
      unfold ext_local in EXT.
      cbn in EXT.
      repeat norm_h.

      cbn.
      repeat norm_v.
      rewrite typ_to_dtyp_equation.
      repeat norm_v.

      epose proof (AEXPR l2 _) as [EUTT EVAL'].
      rewrite denote_code_sing.

      rewrite denote_instr_intrinsic; cbn; eauto.
      2: cbn; eauto.
      4: {
        rewrite interp_cfg_to_L3_bind.
        rewrite <- EUTT.
        setoid_rewrite bind_ret_l.
        rewrite bind_ret_l.
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

      repeat norm_v.

      apply eqit_Ret.

      (* TODO: This is repeated a lot... Ltac? *)
      split.
      + eapply state_invariant_add_fresh; eauto.
      + split; split; intuition.
        * cbn. repeat norm_v. cbn. norm_v.
          reflexivity.
          cbn.

          apply H.

          (* TODO: Can't unfold Floats.Float.abs ??? *)
          (* TODO: Use Transparent... Still not obvious. *)
          assert (Floats.Float.abs b2 ≡ MFloat64asCT.CTypeAbs b2).
          admit.
          rewrite H3.
          apply In_add_eq.
        * (* TODO: ltac, this is horrid *)
          cbn. rewrite EVAL'.
          reflexivity.
        * rewrite H3.
          apply sub_alist_add.
          unfold alist_fresh.
          apply alist_find_None.
          intros v0. intros IN.
          eapply In__alist_In in IN as [v' AIN].
          apply incLocal_is_fresh in SINV.
          eapply SINV; eauto.
          (* TODO: there's probably a smarter way to do this case now *)
          Transparent incLocal.
          unfold incLocal in Heqs0.
          cbn in Heqs0.
          inversion Heqs0.
          reflexivity.
          Opaque incLocal.
    - (* APlus *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in COMPILE; simp.

      (* YZ TODO Ltac for this *)
      cbn in EVAL.
      break_match; try discriminate EVAL.
      break_match; try discriminate EVAL.

      Opaque denote_code.
      cbn*.
      repeat norm_h.

      rewrite convert_typ_app.
      rewrite denote_code_app.
      repeat norm_v.

      eapply eutt_clo_bind; try eapply IHaexp1; eauto.

      intros [memH' b'] [memV' [l' [g' []]]] [INV1 INV2].
      cbn in *.

      repeat norm_h.

      rewrite convert_typ_app.
      rewrite denote_code_app.
      repeat norm_v.

      inversion INV2.
      inversion amonotone0.
      subst.
      eapply eutt_clo_bind; try eapply IHaexp2; eauto.

      intros [memH'' b''] [memV'' [l'' [g'' []]]] [INV1' INV2'].
      inversion INV2'.
      inversion amonotone1.
      subst.

      repeat norm_h.
      cbn. repeat norm_v.
      rewrite typ_to_dtyp_equation.

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

      rewrite denote_code_sing.

      rewrite denote_instr_op.
      2: {
        eapply denote_fbinop_concrete; cbn; eauto; try reflexivity.
      }

      cbn.
      repeat norm_v.

      apply eqit_Ret.
      split; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
      + split; split; intuition.
        * cbn. repeat norm_v. cbn. norm_v.
          reflexivity.
          cbn.

          apply H.

          (* TODO: Can't unfold Floats.Float.add ??? *)
          assert (Floats.Float.add b' b'' ≡ MFloat64asCT.CTypePlus b' b'').
          admit.
          rewrite H3.
          apply In_add_eq.
        * (* TODO: ltac, this is horrid *)
          cbn. rewrite H6.
          epose proof (aexp_correct1 l'' _) as [[] H7].
          rewrite H7.

          reflexivity.
        * rewrite H3. rewrite H2.
          apply sub_alist_add.
          unfold alist_fresh.
          cbn in INV1'.
          destruct INV1'.
          unfold concrete_fresh_inv in incLocal_is_fresh.
          apply alist_find_None.
          intros v0. intros IN.
          eapply In__alist_In in IN as [v' AIN].
          eapply incLocal_is_fresh; eauto.
          (* TODO: there's probably a smarter way to do this case now *)
          Transparent incLocal.
          unfold incLocal in Heqs1.
          cbn in Heqs1.
          inversion Heqs1.
          reflexivity.
          Opaque incLocal.
    - (* AMinus *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in COMPILE; simp.

      (* YZ TODO Ltac for this *)
      cbn in EVAL.
      break_match; try discriminate EVAL.
      break_match; try discriminate EVAL.

      Opaque denote_code.
      cbn*.
      repeat norm_h.

      rewrite convert_typ_app.
      rewrite denote_code_app.
      repeat norm_v.

      eapply eutt_clo_bind; try eapply IHaexp1; eauto.

      intros [memH' b'] [memV' [l' [g' []]]] [INV1 INV2].
      cbn in *.

      repeat norm_h.

      rewrite convert_typ_app.
      rewrite denote_code_app.
      repeat norm_v.

      inversion INV2.
      inversion amonotone0.
      subst.
      eapply eutt_clo_bind; try eapply IHaexp2; eauto.

      intros [memH'' b''] [memV'' [l'' [g'' []]]] [INV1' INV2'].
      inversion INV2'.
      inversion amonotone1.
      subst.

      repeat norm_h.
      cbn. repeat norm_v.
      rewrite typ_to_dtyp_equation.

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

      rewrite denote_code_sing.

      rewrite denote_instr_op.
      2: {
        eapply denote_fbinop_concrete; cbn; eauto; try reflexivity.
      }

      cbn.
      repeat norm_v.

      apply eqit_Ret.
      split; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
      + split; split; intuition.
        * cbn. repeat norm_v. cbn. norm_v.
          reflexivity.
          cbn.

          apply H.

          (* TODO: Can't unfold Floats.Float.add ??? *)
          assert (Floats.Float.sub b' b'' ≡ MFloat64asCT.CTypeSub b' b'').
          admit.

          rewrite H3.
          apply In_add_eq.
        * (* TODO: ltac, this is horrid *)
          cbn. rewrite H6.
          epose proof (aexp_correct1 l'' _) as [[] H7].
          rewrite H7.

          reflexivity.
        * rewrite H3. rewrite H2.
          apply sub_alist_add.
          unfold alist_fresh.
          cbn in INV1'.
          destruct INV1'.
          unfold concrete_fresh_inv in incLocal_is_fresh.
          apply alist_find_None.
          intros v0. intros IN.
          eapply In__alist_In in IN as [v' AIN].
          eapply incLocal_is_fresh; eauto.
          (* TODO: there's probably a smarter way to do this case now *)
          Transparent incLocal.
          unfold incLocal in Heqs1.
          cbn in Heqs1.
          inversion Heqs1.
          reflexivity.
          Opaque incLocal.
    - (* AMult *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in COMPILE; simp.

      (* YZ TODO Ltac for this *)
      cbn in EVAL.
      break_match; try discriminate EVAL.
      break_match; try discriminate EVAL.

      Opaque denote_code.
      cbn*.
      repeat norm_h.

      rewrite convert_typ_app.
      rewrite denote_code_app.
      repeat norm_v.

      eapply eutt_clo_bind; try eapply IHaexp1; eauto.

      intros [memH' b'] [memV' [l' [g' []]]] [INV1 INV2].
      cbn in *.

      repeat norm_h.

      rewrite convert_typ_app.
      rewrite denote_code_app.
      repeat norm_v.

      inversion INV2.
      inversion amonotone0.
      subst.
      eapply eutt_clo_bind; try eapply IHaexp2; eauto.

      intros [memH'' b''] [memV'' [l'' [g'' []]]] [INV1' INV2'].
      inversion INV2'.
      inversion amonotone1.
      subst.

      repeat norm_h.
      cbn. repeat norm_v.
      rewrite typ_to_dtyp_equation.

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

      rewrite denote_code_sing.

      rewrite denote_instr_op.
      2: {
        eapply denote_fbinop_concrete; cbn; eauto; try reflexivity.
      }

      cbn.
      repeat norm_v.

      apply eqit_Ret.
      split; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
      + split; split; intuition.
        * cbn. repeat norm_v. cbn. norm_v.
          reflexivity.
          cbn.

          apply H.

          (* TODO: Can't unfold Floats.Float.add ??? *)
          assert (Floats.Float.mul b' b'' ≡ MFloat64asCT.CTypeMult b' b'').
          admit.

          rewrite H3.
          apply In_add_eq.
        * (* TODO: ltac, this is horrid *)
          cbn. rewrite H6.
          epose proof (aexp_correct1 l'' _) as [[] H7].
          rewrite H7.

          reflexivity.
        * rewrite H3. rewrite H2.
          apply sub_alist_add.
          unfold alist_fresh.
          cbn in INV1'.
          destruct INV1'.
          unfold concrete_fresh_inv in incLocal_is_fresh.
          apply alist_find_None.
          intros v0. intros IN.
          eapply In__alist_In in IN as [v' AIN].
          eapply incLocal_is_fresh; eauto.
          (* TODO: there's probably a smarter way to do this case now *)
          Transparent incLocal.
          unfold incLocal in Heqs1.
          cbn in Heqs1.
          inversion Heqs1.
          reflexivity.
          Opaque incLocal.
    - (* AMin *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in COMPILE; simp.

      (* YZ TODO Ltac for this *)
      cbn in EVAL.
      break_match; try discriminate EVAL.
      break_match; try discriminate EVAL.

      Opaque denote_code.
      cbn*.
      repeat norm_h.

      rewrite convert_typ_app.
      rewrite denote_code_app.
      repeat norm_v.

      eapply eutt_clo_bind; try eapply IHaexp1; eauto.

      intros [memH' b'] [memV' [l' [g' []]]] [INV1 INV2].
      cbn in *.

      repeat norm_h.

      rewrite convert_typ_app.
      rewrite denote_code_app.
      repeat norm_v.

      inversion INV2.
      inversion amonotone0.
      subst.
      eapply eutt_clo_bind; try eapply IHaexp2; eauto.

      intros [memH'' b''] [memV'' [l'' [g'' []]]] [INV1' INV2'].
      inversion INV2'.
      inversion amonotone1.
      subst.

      repeat norm_h.
      cbn. repeat norm_v.
      rewrite typ_to_dtyp_equation.

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

      rewrite denote_code_sing.

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
      repeat norm_v.

      apply eqit_Ret.
      split; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
      + split; split; intuition.
        * cbn. repeat norm_v. cbn. norm_v.
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
        * rewrite H3. rewrite H2.
          apply sub_alist_add.
          unfold alist_fresh.
          cbn in INV1'.
          destruct INV1'.
          unfold concrete_fresh_inv in incLocal_is_fresh.
          apply alist_find_None.
          intros v0. intros IN.
          eapply In__alist_In in IN as [v' AIN].
          eapply incLocal_is_fresh; eauto.
          (* TODO: there's probably a smarter way to do this case now *)
          Transparent incLocal.
          unfold incLocal in Heqs1.
          cbn in Heqs1.
          inversion Heqs1.
          reflexivity.
          Opaque incLocal.
    - (* AMax *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in COMPILE; simp.

      (* YZ TODO Ltac for this *)
      cbn in EVAL.
      break_match; try discriminate EVAL.
      break_match; try discriminate EVAL.

      Opaque denote_code.
      cbn*.
      repeat norm_h.

      rewrite convert_typ_app.
      rewrite denote_code_app.
      repeat norm_v.

      eapply eutt_clo_bind; try eapply IHaexp1; eauto.

      intros [memH' b'] [memV' [l' [g' []]]] [INV1 INV2].
      cbn in *.

      repeat norm_h.

      rewrite convert_typ_app.
      rewrite denote_code_app.
      repeat norm_v.

      inversion INV2.
      inversion amonotone0.
      subst.
      eapply eutt_clo_bind; try eapply IHaexp2; eauto.

      intros [memH'' b''] [memV'' [l'' [g'' []]]] [INV1' INV2'].
      inversion INV2'.
      inversion amonotone1.
      subst.

      repeat norm_h.
      cbn. repeat norm_v.
      rewrite typ_to_dtyp_equation.

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

      rewrite denote_code_sing.

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
      repeat norm_v.

      apply eqit_Ret.
      split; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
      + split; split; intuition.
        * cbn. repeat norm_v. cbn. norm_v.
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
        * rewrite H3. rewrite H2.
          apply sub_alist_add.
          unfold alist_fresh.
          cbn in INV1'.
          destruct INV1'.
          unfold concrete_fresh_inv in incLocal_is_fresh.
          apply alist_find_None.
          intros v0. intros IN.
          eapply In__alist_In in IN as [v' AIN].
          eapply incLocal_is_fresh; eauto.
          (* TODO: there's probably a smarter way to do this case now *)
          Transparent incLocal.
          unfold incLocal in Heqs1.
          cbn in Heqs1.
          inversion Heqs1.
          reflexivity.
          Opaque incLocal.
    - (* AZless *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in COMPILE; simp.

      (* YZ TODO Ltac for this *)
      cbn in EVAL.
      break_match; try discriminate EVAL.
      break_match; try discriminate EVAL.

      Opaque denote_code.
      cbn*.
      repeat norm_h.

      rewrite convert_typ_app.
      rewrite denote_code_app.
      repeat norm_v.

      eapply eutt_clo_bind; try eapply IHaexp1; eauto.

      intros [memH' b'] [memV' [l' [g' []]]] [INV1 INV2].
      cbn in *.

      repeat norm_h.

      rewrite convert_typ_app.
      rewrite denote_code_app.
      repeat norm_v.

      inversion INV2.
      inversion amonotone0.
      subst.
      eapply eutt_clo_bind; try eapply IHaexp2; eauto.

      intros [memH'' b''] [memV'' [l'' [g'' []]]] [INV1' INV2'].
      inversion INV2'.
      inversion amonotone1.
      subst.

      repeat norm_h.
      cbn. repeat norm_v.
      rewrite typ_to_dtyp_equation.

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

      repeat norm_v.
      setoid_rewrite denote_code_sing.

      rewrite denote_instr_op.
      2: {
        eapply denote_fcmp_concrete; cbn; eauto; try reflexivity.
      }

      cbn.
      repeat norm_v.
      setoid_rewrite denote_code_sing.
      rewrite denote_instr_comment.
      repeat norm_v.

      setoid_rewrite denote_code_sing.
      pose proof (float_cmp b' b'') as (cmp_res & CMP_V & CMP_H).

      rewrite denote_instr_op.
      2: {
        (* TODO: clean this up... *)
        set (DVALUE_Double
       (Floats.Float.of_longu (DynamicValues.Int64.repr (DynamicValues.Int1.unsigned cmp_res)))) as x.
        set (alist_add (Traversal.endo r) (dvalue_to_uvalue (double_cmp (Traversal.endo FOlt) b' b'')) l'') as l'''.
        pose proof denote_conversion_concrete Uitofp (DTYPE_I 1) DTYPE_Double (EXP_Ident (ID_Local (Traversal.endo r))) g'' l''' memV'' x (dvalue_to_uvalue (double_cmp (Traversal.endo FOlt) b' b'')).
        rewrite typ_to_dtyp_equation.
        rewrite H.
        reflexivity.
        rewrite uvalue_to_dvalue_of_dvalue_to_uvalue. reflexivity.
        cbn.
        unfold Traversal.endo.
        unfold Traversal.Endo_id.
        match_rewrite.
        reflexivity.

        cbn.
        rewrite translate_trigger.
        rewrite translate_trigger.
        rewrite lookup_E_to_exp_E_Local.
        rewrite subevent_subevent.
        rewrite exp_E_to_instr_E_Local.
        rewrite subevent_subevent.
        rewrite interp_cfg_to_L3_LR.
        cbn.

        reflexivity.

        (* Lookup *)
        unfold Traversal.endo, Traversal.Endo_id in *.
        subst l'''.
        apply In_add_eq.
      }

      norm_v.

      apply eqit_Ret.
      split; cbn; eauto.
      + cbn.
        eapply state_invariant_incVoid; eauto.
        repeat (eapply state_invariant_add_fresh; eauto).
      + split; split; intuition.
          * cbn. repeat norm_v. cbn. norm_v.
            reflexivity.
            cbn.
            apply H.
            rewrite <- CMP_H.

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

            cbn in INV1'.
            destruct INV1'.
            unfold concrete_fresh_inv in incLocal_is_fresh.

            cbn in INV1.
            destruct INV1.
            unfold concrete_fresh_inv in incLocal_is_fresh0.

            Transparent incLocal.
            unfold incLocal in Heqs1, Heqs2.
            inversion Heqs1.
            inversion Heqs2.
            Opaque incLocal.

            assert (l'' ⊑ (alist_add r (UVALUE_I1 cmp_res) l'')) as TRANS.
            { apply sub_alist_add.
              unfold alist_fresh.
              apply alist_find_None.
              intros v0 IN.
              eapply In__alist_In in IN as [v' AIN].
              eapply incLocal_is_fresh; eauto.
            }

            eapply (sub_alist_trans _ _ _ TRANS).
            unfold ext_local in *.
            cbn in *.

            subst. cbn.
            unfold Traversal.endo, Traversal.Endo_id.
            rewrite CMP_V.
            cbn.
            apply sub_alist_add.
            unfold alist_fresh.
            apply alist_find_None.
            intros v0 IN.
            eapply In__alist_In in IN as [v' AIN].

            eapply incLocal_is_fresh with (n:=S (local_count i0)); eauto.
            assert (Name ("l" @@ string_of_nat (S (local_count i0))) <> (Name ("l" @@ string_of_nat (local_count i0)))) as NEQ.
            { intros CONTRA.
              apply Name_inj, append_factor_left,string_of_nat_inj in CONTRA; lia.
            }
            apply (In_add_In_ineq _ _ _ _ _ NEQ AIN).
  Admitted.

End AExpr.
