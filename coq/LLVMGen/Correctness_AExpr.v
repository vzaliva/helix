Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Freshness.
Require Import Helix.LLVMGen.LidBound.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.
Require Import Helix.LLVMGen.Correctness_MExpr.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Typeclasses Opaque equiv.
Opaque incBlockNamed.
Opaque incVoid.
Opaque incLocal.

Section AExpr.

  (* Definition R_AExpr_start (σ : evalContext) (s : IRState) (memH : memoryH) (vellvm : memoryV * (local_env * global_env)) : Prop *)
  (*   := state_invariant σ s memH vellvm. *)

  (* Definition R_AExpr *)
  (*            (σ : evalContext) (s : IRState) *)
  (*            (helix : memoryH * binary64) *)
  (*            (vellvm : memoryV * (local_env * res_L1)) : Prop *)
  (*   := *)
  (*     let '(memH, b) := helix in *)
  (*     let '(memV, (ρ, (g, res))) := vellvm in *)
  (*     state_invariant σ s memH (memV, (ρ, g)) /\ *)
  (*     res ≡ UVALUE_Double b. *)

  (* Hint Unfold R_AExpr: core. *)

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

  Lemma min_float_correct: forall (a b: binary64), Float_minimum a b ≡ MFloat64asCT.CTypeMin a b.
  Proof.
    intros.
    Transparent Floats.Float.cmp.
    unfold Float_minimum, MFloat64asCT.CTypeMin, Float64Min, Floats.Float.cmp.
    unfold Floats.Float.compare, Floats.cmp_of_comparison.
    destruct a,b; try break_if; repeat break_match ;try reflexivity; crush.
  Qed.

  Lemma max_float_correct: forall (a b: binary64), Float_maxnum a b ≡ MFloat64asCT.CTypeMax a b.
  Proof.
    intros. 
    Transparent Floats.Float.cmp.
    unfold Float_maxnum, MFloat64asCT.CTypeMax, Float64Max, Floats.Float.cmp.
    unfold Floats.Float.compare, Floats.cmp_of_comparison.
    destruct a,b; try break_if; repeat break_match ;try reflexivity; crush.
  Qed.

  Lemma state_invariant_incVoid :
    forall σ s s' k memH stV,
      incVoid s ≡ inr (s', k) ->
      state_invariant σ s memH stV ->
      state_invariant σ s' memH stV.
  Proof.
    intros * INC INV; inv INV.
    split.
    - red; repeat break_let; intros * LUH LUV.
      erewrite incVoid_Γ in LUV; eauto.
      generalize LUV; intros INLG;
        eapply MINV in INLG; eauto.
    - unfold WF_IRState; erewrite incVoid_Γ; eauto; apply WF.
  Qed.

  Definition genAExpr_exp_correct σ s1 s2 (e: exp typ) 
    : Rel_cfg_T binary64 unit :=
    fun '(x,i) '(memV,(l,(g,v))) =>
      forall l',
        local_scope_preserved s1 s2 l l' ->
        Gamma_preserved σ s1 l l' ->
        interp_cfg
          (translate exp_E_to_instr_E (denote_exp (Some DTYPE_Double) (convert_typ [] e)))
          g l' memV ≈
          Ret (memV,(l',(g,UVALUE_Double i))).

  Record genAExpr_post
         (e : exp typ)
         σ s1 s2
         (mi : memoryH) (sti : config_cfg)
         (mf : memoryH * binary64) (stf : config_cfg_T unit)
    : Prop :=
    {
    exp_correct : genAExpr_exp_correct σ s1 s2 e mf stf;
    is_almost_pure : almost_pure mi sti mf stf; 
    extends : local_scope_modif s1 s2 (fst (snd sti)) (fst (snd stf));
    exp_in_scope : forall id, e ≡ EXP_Ident (ID_Local id) -> ((exists v, alist_In id (fst (snd sti)) v) \/ (lid_bound_between s1 s2 id /\ s1 << s2));
    Gamma_cst : Γ s2 ≡ Γ s1;
    Mono_IRState : s1 << s2 \/ fst (snd sti) ≡ fst (snd stf)
    }.

  Import ProofMode.
  Lemma genAExpr_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *)   (aexp: AExpr) (σ: evalContext) (memH: memoryH) 
      (* Vellvm bits *)   (e: exp typ) (c: code typ) (g : global_env) (l : local_env) (memV : memoryV),

      genAExpr aexp s1 ≡ inr (s2, (e, c))      -> (* Compilation succeeds *)
      state_invariant σ s1 memH (memV, (l, g)) -> (* The main state invariant is initially true *)
      Gamma_safe σ s1 s2 ->
      no_failure (interp_helix (E := E_cfg) (denoteAExpr σ aexp) memH) -> (* Source semantics defined *)

      eutt (succ_cfg (lift_Rel_cfg (state_invariant σ s2) ⩕ genAExpr_post e σ s1 s2 memH (mk_config_cfg memV l g)))
           (interp_helix (denoteAExpr σ aexp) memH)
           (interp_cfg (denote_code (convert_typ [] c)) g l memV).
  Proof. 
    intros s1 s2 aexp; revert s1 s2; induction aexp; intros * COMPILE PRE SAFE NOFAIL.
    - (* Variable case *)
      (* Reducing the compilation *)
      pose proof PRE as PRE'; inv PRE'.
      cbn* in COMPILE; simp.

      + (* The variable maps to an integer in the IRState *)
        unfold denoteAExpr in *; cbn* in *.
        simp; try_abs.
        
        hvred.
        break_inner_match_goal; try_abs.
        break_inner_match_goal; try_abs.
        hvred.
        edestruct memory_invariant_GLU_AExpr as (ptr & MAP & READ); eauto. 
        rewrite typ_to_dtyp_equation in READ.

        vstep.
        { vstep; eauto; reflexivity. }
        apply eutt_Ret; split; [| split]; cbn; eauto.
        * eapply state_invariant_add_fresh; eauto; split; eauto.
        * intros l' LOC GAM; cbn*.
          vstep; [ | reflexivity].
          cbn.
          red in LOC; rewrite LOC.
          rewrite alist_find_add_eq; reflexivity.
          eauto using lid_bound_between_incLocal.          
        * apply local_scope_modif_add.
          auto using lid_bound_between_incLocal.
        * intros * EQ; inv EQ; right.
          split; [auto using lid_bound_between_incLocal | solve_local_count].
        * eauto using incLocal_Γ.
        * left; solve_local_count.

      + (* The variable maps to a pointer *)
        unfold denoteAExpr in *; cbn* in *.
        simp; try_abs.
        hvred.
        break_match_goal; try_abs.
        clear NOFAIL.
        hvred.
        apply eutt_Ret; split; [| split]; cbn; eauto.
        * intros l' LOC GAM; cbn*.
          break_match_goal; try_abs.
          vstep.
          red in GAM; cbn in *.
          erewrite <- GAM.
          eapply memory_invariant_LLU_AExpr; eauto.
          econstructor;eauto.
          reflexivity.
        * intros * EQ; inv EQ.
          left.
          eexists.
          eapply memory_invariant_LLU_AExpr; eauto.

    - (* Constant *)
      cbn* in *; simp.
      hvred.
      apply eutt_Ret; split; [| split]; cbn; eauto.
      intros l' MONO; cbn*.
      vstep; reflexivity.
      intros * EQ; inv EQ.

    - (* ANth m n: lookup to m[n] *)

      cbn* in *; simp.
      edestruct @genMExpr_array as (?sz & ?EQ); eauto; subst.
      hvred.

      (* denoting [n] *)
      clean_goal.
      eapply eutt_clo_bind_returns; [eapply genNExpr_correct |..]; eauto.
      eapply Gamma_safe_shrink; eauto; solve_local_count.

      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (SINV1 & POST1); inv POST1.
      cbn* in *; inv_eqs.
      hvred.

      (* denoting [m] *)
      eapply eutt_clo_bind_returns; [eapply genMExpr_correct | ..]; eauto.
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct vH0, PRE0 as (SINV2 & [PRES2 (addr_m & EQEXPm & LU_ARRAY) <-]). 
      cbn* in *; inv_eqs.
      hvred.

      simp; try_abs.
      (* TODO: Fix try_abs to handle this case *)
      apply no_failure_Ret in NOFAIL; try_abs.
      hvred.

      (* [vstep] does not handle gep currently *)
      edestruct denote_instr_gep_array as (? & READ & EQ);
        [exact EQEXPm | | eapply LU_ARRAY; eauto |].
      { clear LU_ARRAY EQEXPm.
        assert (EQ: vH ≡ repr (Z.of_nat (MInt64asNT.to_nat vH))).
        { cbn.
          unfold MInt64asNT.to_nat.
          cbn.
          rewrite Znat.Z2Nat.id, repr_intval; auto.
          destruct (Int64.intrange vH); lia.
        }
        rewrite EQ in exp_correct0.
        apply exp_correct0; eauto using local_scope_preserved_refl, Gamma_preserved_refl.
      }

      rewrite EQ; clear EQ.
      hvred.
      hvred.
      vstep.
      {
        vstep.
        apply lookup_alist_add_eq. 
        reflexivity.
      }

      clear EQEXPm NOFAIL exp_correct0.
      destruct u; clean_goal.
      rename i0 into s2, i1 into s3, s2 into s4.
      apply eutt_Ret; split; [| split]; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
        eapply Gamma_safe_shrink; eauto.
        rewrite <- Gamma_cst0; symmetry; eauto using incLocal_Γ.
        solve_local_count.
        solve_local_count.
        eapply state_invariant_add_fresh; eauto.
        eapply Gamma_safe_shrink; eauto.
        solve_local_count.
        solve_local_count.
      + intros * SCO GAM.
        vstep; eauto.
        cbn.
        erewrite SCO,alist_find_add_eq.
        reflexivity.
        apply lid_bound_between_shrink_down with s3.
        solve_local_count.
        eapply lid_bound_between_incLocal; eauto.
        reflexivity.
      + eapply local_scope_modif_trans; eauto; [solve_local_count | solve_local_count |].
        apply local_scope_modif_trans with (s2 := s3) (l2 := alist_add r (UVALUE_Addr x) l0).
        solve_local_count.
        solve_local_count.
        eauto using local_scope_modif_add, lid_bound_between_incLocal.
        eauto using local_scope_modif_add, lid_bound_between_incLocal.
      + intros ? EQ; inv EQ.
        right; split; [| solve_local_count].
        apply lid_bound_between_shrink_down with s3; [solve_local_count |].
        eauto using lid_bound_between_incLocal.
      + rewrite <- Gamma_cst0.
        etransitivity; eapply incLocal_Γ; eauto.
      + left; solve_local_count.

    - (* AAbs *) 
      cbn* in *; simp.
      hvred.
      eapply eutt_clo_bind; try eapply IHaexp; eauto.
      eapply Gamma_safe_shrink; eauto; solve_local_count.
      introR; destruct_unit.
      destruct PRE0 as (SINV1 & [EXP1 EXT1 SCOPE1 VAR1 GAM1 MONO1]).
      cbn in *; inv_eqs.
      cbn in *; hvred.

      (* TO FIX *)
      Transparent assoc. 
      vstep; try reflexivity.
      {
        cbn.
        vred_l.
        rewrite (EXP1 l0); eauto using local_scope_preserved_refl, Gamma_preserved_refl.
        tred; vred_l.
        reflexivity.
      }
      {
        cbn; tred; vred_l.
        reflexivity.
      }
      reflexivity.

      clear EXP1 IHaexp.
      clean_goal.
      apply eutt_Ret; split; [| split]; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
        eapply Gamma_safe_shrink; eauto.
        solve_local_count.
        solve_local_count.
      + intros * SCO GAM.
        vstep; eauto.
        cbn.
        erewrite SCO,alist_find_add_eq.
        reflexivity.
        apply lid_bound_between_shrink_down with i.
        solve_local_count.
        eapply lid_bound_between_incLocal; eauto.
        reflexivity.
      + eapply local_scope_modif_trans; eauto; [solve_local_count | solve_local_count |].
        eauto using local_scope_modif_add, lid_bound_between_incLocal.
      + intros ? EQ; inv EQ.
        right; split; [| solve_local_count].
        apply lid_bound_between_shrink_down with i; [solve_local_count |].
        eauto using lid_bound_between_incLocal.
      + rewrite <- GAM1.
        eapply incLocal_Γ; eauto.
      + left; solve_local_count.
        
    - (* APlus *)
      cbn* in *; simp...
      hvred.

      eapply eutt_clo_bind_returns; try eapply IHaexp1; eauto.
      eapply Gamma_safe_shrink; eauto; solve_local_count.
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (SINV1 & [EXP1 EXT1 SCOPE1 VAR1 GAM1 MONO1]).
      cbn in *; inv_eqs.
      cbn in *; hvred.

      eapply eutt_clo_bind; try eapply IHaexp2; eauto.
      eapply Gamma_safe_shrink; eauto; solve_local_count.
      introR; destruct_unit.
      destruct PRE0 as (SINV2 & [EXP2 EXT2 SCOPE2 VAR2 GAM2 MONO2]).
      cbn in *; inv_eqs.
      hvred.

      rename i into s2, i0 into s3, s2 into s4.
      specialize (EXP1 l1) .
      specialize (EXP2 l1) .
      forward EXP2.
      auto using local_scope_preserved_refl.
      forward EXP2.
      auto using Gamma_preserved_refl.
      forward EXP1.
      {
        destruct MONO2 as [| <-]; [| apply local_scope_preserved_refl].
        eapply local_scope_preserve_modif; eauto.
      }
      forward EXP1.
      {
        clear EXP2 EXP1 IHaexp2 IHaexp1.
        clean_goal.
        apply Gamma_preserved_Gamma_eq with s2; auto.
        eapply Gamma_preserved_if_safe; eauto.
        eapply Gamma_safe_shrink; eauto; solve_local_count.
      }

      vstep.
      {
        vstep; eauto.
        all:reflexivity.
      }

      apply eutt_Ret; split; [| split]; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
        eapply Gamma_safe_shrink; eauto. rewrite GAM2; auto.
        solve_local_count.
        solve_local_count.
      + intros * SCO GAM.
        vstep; eauto.
        cbn.
        erewrite SCO,alist_find_add_eq.
        reflexivity.
        apply lid_bound_between_shrink_down with s3.
        solve_local_count.
        eapply lid_bound_between_incLocal; eauto.
        reflexivity.
      + eapply local_scope_modif_trans; eauto; [solve_local_count | solve_local_count |].
        eapply local_scope_modif_trans; eauto; [solve_local_count | solve_local_count |].
        eauto using local_scope_modif_add, lid_bound_between_incLocal.
      + intros ? EQ; inv EQ.
        right; split; [| solve_local_count].
        apply lid_bound_between_shrink_down with s3; [solve_local_count |].
        eauto using lid_bound_between_incLocal.
      + rewrite <- GAM1, <- GAM2.
        eapply incLocal_Γ; eauto.
      + left; solve_local_count.

    - (* AMinus *)
      cbn* in *; simp.
      hvred.

      eapply eutt_clo_bind_returns; try eapply IHaexp1; eauto.
      eapply Gamma_safe_shrink; eauto; solve_local_count.
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (SINV1 & [EXP1 EXT1 SCOPE1 VAR1 GAM1 MONO1]).
      cbn in *; inv_eqs.
      hvred.

      eapply eutt_clo_bind; try eapply IHaexp2; eauto.
      eapply Gamma_safe_shrink; eauto; solve_local_count.
      introR; destruct_unit.
      destruct PRE0 as (SINV2 & [EXP2 EXT2 SCOPE2 VAR2 GAM2 MONO2]).
      cbn in *; inv_eqs.
      hvred.

      rename i into s2, i0 into s3, s2 into s4.
      specialize (EXP1 l1) .
      specialize (EXP2 l1) .
      forward EXP2.
      auto using local_scope_preserved_refl.
      forward EXP2.
      auto using Gamma_preserved_refl.
      forward EXP1.
      {
        destruct MONO2 as [| <-]; [| apply local_scope_preserved_refl].
        eapply local_scope_preserve_modif; eauto.
      }
      forward EXP1.
      {
        clear EXP2 EXP1 IHaexp2 IHaexp1.
        clean_goal.
        apply Gamma_preserved_Gamma_eq with s2; auto.
        eapply Gamma_preserved_if_safe; eauto.
        eapply Gamma_safe_shrink; eauto; solve_local_count.
      }

      vstep.
      {
        vstep; eauto.
        all:reflexivity.
      }

      apply eutt_Ret; split; [| split]; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
        eapply Gamma_safe_shrink; eauto. rewrite GAM2; auto.
        solve_local_count.
        solve_local_count.
      + intros * SCO GAM.
        vstep; eauto.
        cbn.
        erewrite SCO,alist_find_add_eq.
        reflexivity.
        apply lid_bound_between_shrink_down with s3.
        solve_local_count.
        eapply lid_bound_between_incLocal; eauto.
        reflexivity.
      + eapply local_scope_modif_trans; eauto; [solve_local_count | solve_local_count |].
        eapply local_scope_modif_trans; eauto; [solve_local_count | solve_local_count |].
        eauto using local_scope_modif_add, lid_bound_between_incLocal.
      + intros ? EQ; inv EQ.
        right; split; [| solve_local_count].
        apply lid_bound_between_shrink_down with s3; [solve_local_count |].
        eauto using lid_bound_between_incLocal.
      + rewrite <- GAM1, <- GAM2.
        eapply incLocal_Γ; eauto.
      + left; solve_local_count.

    - (* AMult *)
      cbn* in *; simp.
      hvred.

      eapply eutt_clo_bind_returns; try eapply IHaexp1; eauto.
      eapply Gamma_safe_shrink; eauto; solve_local_count.
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (SINV1 & [EXP1 EXT1 SCOPE1 VAR1 GAM1 MONO1]).
      cbn in *; inv_eqs.
      hvred.

      eapply eutt_clo_bind; try eapply IHaexp2; eauto.
      eapply Gamma_safe_shrink; eauto; solve_local_count.
      introR; destruct_unit.
      destruct PRE0 as (SINV2 & [EXP2 EXT2 SCOPE2 VAR2 GAM2 MONO2]).
      cbn in *; inv_eqs.
      hvred.

      rename i into s2, i0 into s3, s2 into s4.
      specialize (EXP1 l1) .
      specialize (EXP2 l1) .
      forward EXP2.
      auto using local_scope_preserved_refl.
      forward EXP2.
      auto using Gamma_preserved_refl.
      forward EXP1.
      {
        destruct MONO2 as [| <-]; [| apply local_scope_preserved_refl].
        eapply local_scope_preserve_modif; eauto.
      }
      forward EXP1.
      {
        clear EXP2 EXP1 IHaexp2 IHaexp1.
        clean_goal.
        apply Gamma_preserved_Gamma_eq with s2; auto.
        eapply Gamma_preserved_if_safe; eauto.
        eapply Gamma_safe_shrink; eauto; solve_local_count.
      }

      vstep.
      {
        vstep; eauto.
        all:reflexivity.
      }

      apply eutt_Ret; split; [| split]; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
        eapply Gamma_safe_shrink; eauto. rewrite GAM2; auto.
        solve_local_count.
        solve_local_count.
      + intros * SCO GAM.
        vstep; eauto.
        cbn.
        erewrite SCO,alist_find_add_eq.
        reflexivity.
        apply lid_bound_between_shrink_down with s3.
        solve_local_count.
        eapply lid_bound_between_incLocal; eauto.
        reflexivity.
      + eapply local_scope_modif_trans; eauto; [solve_local_count | solve_local_count |].
        eapply local_scope_modif_trans; eauto; [solve_local_count | solve_local_count |].
        eauto using local_scope_modif_add, lid_bound_between_incLocal.
      + intros ? EQ; inv EQ.
        right; split; [| solve_local_count].
        apply lid_bound_between_shrink_down with s3; [solve_local_count |].
        eauto using lid_bound_between_incLocal.
      + rewrite <- GAM1, <- GAM2.
        eapply incLocal_Γ; eauto.
      + left; solve_local_count.

    - (* AMin *)
      cbn* in *; simp.
      hvred.

      eapply eutt_clo_bind_returns; try eapply IHaexp1; eauto.
      eapply Gamma_safe_shrink; eauto; solve_local_count.
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (SINV1 & [EXP1 EXT1 SCOPE1 VAR1 GAM1 MONO1]).
      cbn in *; inv_eqs.
      hvred.

      eapply eutt_clo_bind; try eapply IHaexp2; eauto.
      eapply Gamma_safe_shrink; eauto; solve_local_count.
      introR; destruct_unit.
      destruct PRE0 as (SINV2 & [EXP2 EXT2 SCOPE2 VAR2 GAM2 MONO2]).
      cbn in *; inv_eqs.
      hvred.

      rename i into s2, i0 into s3, s2 into s4.
      specialize (EXP1 l1) .
      specialize (EXP2 l1) .
      forward EXP2.
      auto using local_scope_preserved_refl.
      forward EXP2.
      auto using Gamma_preserved_refl.
      forward EXP1.
      {
        destruct MONO2 as [| <-]; [| apply local_scope_preserved_refl].
        eapply local_scope_preserve_modif; eauto.
      }
      forward EXP1.
      {
        clear EXP2 EXP1 IHaexp2 IHaexp1.
        clean_goal.
        apply Gamma_preserved_Gamma_eq with s2; auto.
        eapply Gamma_preserved_if_safe; eauto.
        eapply Gamma_safe_shrink; eauto; solve_local_count.
      }

      vstep; try reflexivity.
      { cbn; vred_l. 
        rewrite EXP1.
        autorewrite with itree.
        vred_l.
        rewrite EXP2.
        autorewrite with itree.
        vred_l.
        reflexivity.
      }
      cbn; tred; vred_l; reflexivity.
      reflexivity.

      apply eutt_Ret; split; [| split]; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
        eapply Gamma_safe_shrink; eauto. rewrite GAM2; auto.
        solve_local_count.
        solve_local_count.
      + intros * SCO GAM.
        vstep; eauto.
        cbn.
        erewrite SCO,alist_find_add_eq.
        reflexivity.
        apply lid_bound_between_shrink_down with s3.
        solve_local_count.
        eapply lid_bound_between_incLocal; eauto.
        rewrite min_float_correct. 
        reflexivity.
      + eapply local_scope_modif_trans; eauto; [solve_local_count | solve_local_count |].
        eapply local_scope_modif_trans; eauto; [solve_local_count | solve_local_count |].
        eauto using local_scope_modif_add, lid_bound_between_incLocal.
      + intros ? EQ; inv EQ.
        right; split; [| solve_local_count].
        apply lid_bound_between_shrink_down with s3; [solve_local_count |].
        eauto using lid_bound_between_incLocal.
      + rewrite <- GAM1, <- GAM2.
        eapply incLocal_Γ; eauto.
      + left; solve_local_count.
        
   - (* AMax *)
      cbn* in *; simp.
      hvred.

      eapply eutt_clo_bind_returns; try eapply IHaexp1; eauto.
      eapply Gamma_safe_shrink; eauto; solve_local_count.
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (SINV1 & [EXP1 EXT1 SCOPE1 VAR1 GAM1 MONO1]).
      cbn in *; inv_eqs.
      hvred.

      eapply eutt_clo_bind; try eapply IHaexp2; eauto.
      eapply Gamma_safe_shrink; eauto; solve_local_count.
      introR; destruct_unit.
      destruct PRE0 as (SINV2 & [EXP2 EXT2 SCOPE2 VAR2 GAM2 MONO2]).
      cbn in *; inv_eqs.
      hvred.

      rename i into s2, i0 into s3, s2 into s4.
      specialize (EXP1 l1) .
      specialize (EXP2 l1) .
      forward EXP2.
      auto using local_scope_preserved_refl.
      forward EXP2.
      auto using Gamma_preserved_refl.
      forward EXP1.
      {
        destruct MONO2 as [| <-]; [| apply local_scope_preserved_refl].
        eapply local_scope_preserve_modif; eauto.
      }
      forward EXP1.
      {
        clear EXP2 EXP1 IHaexp2 IHaexp1.
        clean_goal.
        apply Gamma_preserved_Gamma_eq with s2; auto.
        eapply Gamma_preserved_if_safe; eauto.
        eapply Gamma_safe_shrink; eauto; solve_local_count.
      }

      vstep; try reflexivity.
      { cbn; vred_l. 
        rewrite EXP1.
        autorewrite with itree.
        vred_l.
        rewrite EXP2.
        autorewrite with itree.
        vred_l.
        reflexivity.
      }
      cbn; tred; vred_l; reflexivity.
      reflexivity.

      apply eutt_Ret; split; [| split]; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
        eapply Gamma_safe_shrink; eauto. rewrite GAM2; auto.
        solve_local_count.
        solve_local_count.
      + intros * SCO GAM.
        vstep; eauto.
        cbn.
        erewrite SCO,alist_find_add_eq.
        reflexivity.
        apply lid_bound_between_shrink_down with s3.
        solve_local_count.
        eapply lid_bound_between_incLocal; eauto.
        rewrite max_float_correct. 
        reflexivity.
      + eapply local_scope_modif_trans; eauto; [solve_local_count | solve_local_count |].
        eapply local_scope_modif_trans; eauto; [solve_local_count | solve_local_count |].
        eauto using local_scope_modif_add, lid_bound_between_incLocal.
      + intros ? EQ; inv EQ.
        right; split; [| solve_local_count].
        apply lid_bound_between_shrink_down with s3; [solve_local_count |].
        eauto using lid_bound_between_incLocal.
      + rewrite <- GAM1, <- GAM2.
        eapply incLocal_Γ; eauto.
      + left; solve_local_count.
 
   - (* AZless *)
      cbn* in *; simp.
      hvred.

      eapply eutt_clo_bind_returns; try eapply IHaexp1; eauto.
      eapply Gamma_safe_shrink; eauto; solve_local_count.
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (SINV1 & [EXP1 EXT1 SCOPE1 VAR1 GAM1 MONO1]).
      cbn in *; inv_eqs.
      hvred.

      eapply eutt_clo_bind; try eapply IHaexp2; eauto.
      eapply Gamma_safe_shrink; eauto; solve_local_count.
      introR; destruct_unit.
      destruct PRE0 as (SINV2 & [EXP2 EXT2 SCOPE2 VAR2 GAM2 MONO2]).
      cbn in *; inv_eqs.
      hvred.

      rename i into s2, i0 into s3, s2 into s4.
      specialize (EXP1 l1) .
      specialize (EXP2 l1) .
      forward EXP2.
      auto using local_scope_preserved_refl.
      forward EXP2.
      auto using Gamma_preserved_refl.
      forward EXP1.
      {
        destruct MONO2 as [| <-]; [| apply local_scope_preserved_refl].
        eapply local_scope_preserve_modif; eauto.
      }
      forward EXP1.
      {
        clear EXP2 EXP1 IHaexp2 IHaexp1.
        clean_goal.
        apply Gamma_preserved_Gamma_eq with s2; auto.
        eapply Gamma_preserved_if_safe; eauto.
        eapply Gamma_safe_shrink; eauto; solve_local_count.
      }

      vstep.
      {
        vstep.
        rewrite EXP1; reflexivity.
        rewrite EXP2; reflexivity. 
        all: reflexivity.
      }

      hvred.
      destruct (float_cmp vH vH0) as (? & ? & ?).
      rewrite denote_instr_comment.
      vstep.
      unfold denote_exp; simpl.
      hvred.
      vstep.
      vstep.

      { vstep.
        apply In_add_eq.
        reflexivity.
      }
      rewrite uvalue_to_dvalue_of_dvalue_to_uvalue; reflexivity.
      cbn; match_rewrite; reflexivity.
      reflexivity.

      clear EXP1 EXP2 NOFAIL IHaexp1 IHaexp2.
      clean_goal.
      rename i1 into s4, i2 into s5, s4 into s6.
      
      apply eutt_Ret; split; [| split]; cbn; eauto.
      + eapply state_invariant_incVoid; [eauto | ..].
        eapply state_invariant_add_fresh; [eauto |..].
        eapply Gamma_safe_shrink; eauto.
        rewrite <- GAM1, <- GAM2; auto.
        symmetry; eapply incLocal_Γ; eauto.
        solve_local_count.
        solve_local_count.
        eapply state_invariant_add_fresh; [eauto |..].
        eapply Gamma_safe_shrink; eauto.
        rewrite <- GAM1, <- GAM2; auto.
        solve_local_count.
        solve_local_count.
        auto.
      + intros * SCO GAM.
        vstep; eauto.
        cbn.
        erewrite SCO,alist_find_add_eq.
        reflexivity.
        apply lid_bound_between_shrink_down with s4.
        solve_local_count.
        apply lid_bound_between_shrink_up with s5.
        solve_local_count.
        eapply lid_bound_between_incLocal; eauto.
        rewrite H0; reflexivity.
      + eapply local_scope_modif_trans; eauto; [solve_local_count | solve_local_count |].
        eapply local_scope_modif_trans; eauto; [solve_local_count | solve_local_count |].
        apply local_scope_modif_trans
          with (s2 := s4) (l2 := alist_add r (dvalue_to_uvalue (double_cmp FOlt vH vH0)) l1); [solve_local_count | solve_local_count | |].
        eauto using local_scope_modif_add, lid_bound_between_incLocal.
        apply local_scope_modif_trans with
            (s2 := s5)
            (l2 := alist_add r0 (UVALUE_Double (Floats.Float.of_longu (DynamicValues.Int64.repr (DynamicValues.Int1.unsigned x)))) (alist_add r (dvalue_to_uvalue (double_cmp FOlt vH vH0)) l1))
        ; [solve_local_count | solve_local_count | |].
        eauto using local_scope_modif_add, lid_bound_between_incLocal.
        eapply local_scope_modif_refl.
      + intros ? EQ; inv EQ.
        right; split; [| solve_local_count].
        apply lid_bound_between_shrink_down with s4; [solve_local_count |].
        apply lid_bound_between_shrink_up with s5; [solve_local_count |].
        eauto using lid_bound_between_incLocal.
      + rewrite <- GAM1, <- GAM2.
        apply incLocal_Γ in Heqs1; rewrite <- Heqs1.
        apply incLocal_Γ in Heqs2; rewrite <- Heqs2.
        apply incVoid_Γ in Heqs3; auto. 
      + left; solve_local_count.
  Qed.

End AExpr.
