Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.
Require Import Helix.LLVMGen.Correctness_MExpr.
(* Require Import LibHyps.LibHyps. *)

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Typeclasses Opaque equiv.

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
  Definition genAExpr_exp_correct (e: exp typ) : Rel_cfg_T binary64 unit :=
    fun '(memH,i) '(memV,(l,(g,v))) =>
      forall l', l ⊑ l' ->
        interp_cfg (translate exp_E_to_instr_E (denote_exp (Some (DTYPE_Double)) (convert_typ [] e))) g l' memV
        ≈
        Ret (memV,(l',(g,UVALUE_Double i)))
  .

  Record genAExpr_rel
         (σ : evalContext)
         (aexp : AExpr)
         (e : exp typ)
         (mi : memoryH) (sti : config_cfg)
         (mf : memoryH * binary64) (stf : config_cfg_T unit)
    : Prop :=
    {
    aexp_correct : genAExpr_exp_correct e mf stf;
    amonotone : ext_local mi sti mf stf
    }.

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

  Import ProofNotations.

  Lemma genAExpr_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *)   (aexp: AExpr) (σ: evalContext) (memH: memoryH) 
      (* Vellvm bits *)   (e: exp typ) (c: code typ) (g : global_env) (l : local_env) (memV : memoryV),

      genAExpr aexp s1 ≡ inr (s2, (e, c))      -> (* Compilation succeeds *)
      state_invariant σ s1 memH (memV, (l, g)) -> (* The main state invariant is initially true *)
      no_failure (interp_helix (E := E_cfg) (denoteAExpr σ aexp) memH) -> (* Source semantics defined *)

      eutt (succ_cfg (lift_Rel_cfg (state_invariant σ s2) ⩕ genAExpr_rel σ aexp e memH (mk_config_cfg memV l g)))
           (interp_helix (denoteAExpr σ aexp) memH)
           (interp_cfg (denote_code (convert_typ [] c)) g l memV).
  Proof with rauto.
    intros s1 s2 aexp; revert s1 s2; induction aexp; intros * COMPILE PRE NOFAIL.
    - (* Variable case *)
      (* Reducing the compilation *)
      pose proof COMPILE as COMPILE'.
      cbn* in COMPILE; simp.

      + (* The variable maps to an integer in the IRState *)
        unfold denoteAExpr in *; cbn* in *.
        simp; try_abs.
        
        cbn...
        break_inner_match_goal; try_abs.
        break_inner_match_goal; try_abs.
        cbn...
        edestruct memory_invariant_GLU_AExpr as (ptr & MAP & READ); eauto. 
        rewrite typ_to_dtyp_equation in READ.

        rewrite denote_instr_load; eauto; cycle -1.
        { cbn... 2:eauto. reflexivity. }
        apply eutt_Ret; cbn.
        split.
        { eapply state_invariant_add_fresh; eauto. }
        { split.
          - red; intros.
            cbn...
            reflexivity.
            cbn; erewrite H; eauto.
            eapply In_add_eq.
          - cbn; intuition.
            apply sub_alist_add.
            eapply concrete_fresh_fresh; eauto. 
            eapply incLocal_is_fresh; eauto.
        }

      + (* The variable maps to a pointer *)
        unfold denoteAExpr in *; cbn* in *.
        simp; try_abs.
        cbn...
        destruct d; try_abs.
        clear NOFAIL.
        cbn... 
        apply eutt_Ret.
        split; split; eauto using incLocal_is_fresh.
        cbn...
        break_match_goal; try_abs.
        intros; cbn...
        reflexivity.
        eapply memory_invariant_LLU_AExpr; eauto;
          eapply memory_invariant_ext_local;
          eauto.

    - (* Constant *)
      cbn* in COMPILE; simp.
      unfold denoteAExpr in *; cbn* in *.
      cbn... 
      apply eutt_Ret; split; [| split]; eauto.
      intros l' MONO; cbn*...
      all: reflexivity.
      
    - (* ANth m n: lookup to m[n] *)
      cbn* in COMPILE; simp.
      unfold denoteAExpr in *; cbn* in *.
      edestruct @genMExpr_array as (?sz & ?EQ); eauto; subst.

      (* denoting [n] *)
      (* onAllHyps move_up_types. *)
      rewrite convert_typ_app, denote_code_app...
      eapply eutt_clo_bind_returns; [eapply genNExpr_correct |..]; eauto.
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (SINV & EQEXP & ?).
      cbn* in *; inv_eqs.

      (* denoting [m] *)
      (* onAllHyps move_up_types. *)
      rewrite convert_typ_app, denote_code_app...
      eapply eutt_clo_bind_returns; [eapply genMExpr_correct | ..]; eauto.
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct vH0, PRE0 as (SINV' & ? & (addr_m & EQEXPm & LU_ARRAY)).
      cbn* in *; inv_eqs.

      simp; try_abs.
      (* TODO: Fix try_abs to handle this case *)
      apply no_failure_Ret in NOFAIL; try_abs.

      rewrite denote_code_cons...
      edestruct denote_instr_gep_array as (? & READ & EQ);
        [exact EQEXPm | | eapply LU_ARRAY; eauto |].
      { clear LU_ARRAY EQEXPm.
        assert (EQ: vH ≡ repr (Z.of_nat (MInt64asNT.to_nat vH))) by admit.
        rewrite EQ in EQEXP.
        exact EQEXP.
      }
      rewrite EQ...
      clear EQ.
      rewrite denote_instr_load; eauto.
      2:{
        cbn...
        reflexivity.
        apply lookup_alist_add_eq. 
      }
      clear EQEXP EQEXPm NOFAIL.
      apply eutt_Ret.
      split.
      ++ cbn; do 2 (eapply state_invariant_add_fresh; eauto).
      ++ split; cbn; intuition.
      * cbn... 
        reflexivity.
        cbn.
        apply H0.
        apply In_add_eq.
      * eapply sub_alist_trans; eauto.
        eapply sub_alist_trans; eapply sub_alist_add.
        -- eapply concrete_fresh_fresh; eauto.
           eapply incLocal_is_fresh; eauto.
        -- eapply concrete_fresh_fresh; eauto.
           eapply incLocal_is_fresh; eauto.
           eapply state_invariant_add_fresh; eauto.
           
    - (* AAbs *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in *; simp.
      cbn...
      rewrite convert_typ_app, denote_code_app...
      eapply eutt_clo_bind; try eapply IHaexp; eauto.
      introR; destruct_unit.
      cbn; rewrite denote_code_singleton...
      destruct PRE0 as (SINV & AEXP & MONO).
      cbn in MONO; inv_eqs.

      Transparent assoc.
      rewrite denote_instr_intrinsic; cbn; try reflexivity.
      4: {
        cbn...
        rewrite (AEXP l); [| reflexivity]. 
        cbn...
        reflexivity.
      }
      2: {
        cbn...
        reflexivity.
      }
      2: reflexivity.
      apply eutt_Ret.
      split.
      + eapply state_invariant_add_fresh; eauto.
      + split; cbn; intuition.
        * cbn...
          reflexivity.
          cbn. apply H0.
          apply In_add_eq.
        * rewrite H.
          apply sub_alist_add.
          eapply concrete_fresh_fresh; eauto.
          eapply incLocal_is_fresh; eauto.
          
    - (* APlus *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in *; simp...

      rewrite convert_typ_app, denote_code_app...
      eapply eutt_clo_bind_returns; try eapply IHaexp1; eauto.
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (SINV1 & AEXP1 & ext); cbn in *; inv_eqs.

      rewrite convert_typ_app, denote_code_app...
      eapply eutt_clo_bind; try eapply IHaexp2; eauto.
      introR; destruct_unit.
      destruct PRE0 as (SINV2 & AEXP2 & ext); cbn in *; inv_eqs.

      cbn; rewrite denote_code_singleton...
      rewrite denote_instr_op.
      2: {
        cbn...
        rewrite AEXP1; auto...
        rewrite AEXP2; [| reflexivity]...
        cbn...
        reflexivity.
      }

      apply eutt_Ret.
      split; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
      + split; cbn; intuition.
        * cbn...
          reflexivity.
          apply H1, In_add_eq.
        * rewrite H, H0.
          apply sub_alist_add.
          eapply concrete_fresh_fresh; eauto.
          eapply incLocal_is_fresh; eauto.

    - (* AMinus *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in *; simp...

      rewrite convert_typ_app, denote_code_app...
      eapply eutt_clo_bind_returns; try eapply IHaexp1; eauto.
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (SINV1 & AEXP1 & ext); cbn in *; inv_eqs.

      rewrite convert_typ_app, denote_code_app...
      eapply eutt_clo_bind; try eapply IHaexp2; eauto.
      introR; destruct_unit.
      destruct PRE0 as (SINV2 & AEXP2 & ext); cbn in *; inv_eqs.

      cbn; rewrite denote_code_singleton...
      rewrite denote_instr_op.
      2: {
        cbn...
        rewrite AEXP1; auto...
        rewrite AEXP2; [| reflexivity]...
        cbn...
        reflexivity.
      }

      apply eutt_Ret.
      split; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
      + split; cbn; intuition.
        * cbn...
          reflexivity.
          apply H1, In_add_eq.
        * rewrite H, H0.
          apply sub_alist_add.
          eapply concrete_fresh_fresh; eauto.
          eapply incLocal_is_fresh; eauto.

    - (* AMult *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in *; simp...

      rewrite convert_typ_app, denote_code_app...
      eapply eutt_clo_bind_returns; try eapply IHaexp1; eauto.
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (SINV1 & AEXP1 & ext); cbn in *; inv_eqs.

      rewrite convert_typ_app, denote_code_app...
      eapply eutt_clo_bind; try eapply IHaexp2; eauto.
      introR; destruct_unit.
      destruct PRE0 as (SINV2 & AEXP2 & ext); cbn in *; inv_eqs.

      cbn; rewrite denote_code_singleton...
      rewrite denote_instr_op.
      2: {
        cbn...
        rewrite AEXP1; auto...
        rewrite AEXP2; [| reflexivity]...
        cbn...
        reflexivity.
      }

      apply eutt_Ret.
      split; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
      + split; cbn; intuition.
        * cbn...
          reflexivity.
          apply H1, In_add_eq.
        * rewrite H, H0.
          apply sub_alist_add.
          eapply concrete_fresh_fresh; eauto.
          eapply incLocal_is_fresh; eauto.

   - (* AMin *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in *; simp...

      rewrite convert_typ_app, denote_code_app...
      eapply eutt_clo_bind_returns; try eapply IHaexp1; eauto.
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (SINV1 & AEXP1 & ext); cbn in *; inv_eqs.

      rewrite convert_typ_app, denote_code_app...
      eapply eutt_clo_bind; try eapply IHaexp2; eauto.
      introR; destruct_unit.
      destruct PRE0 as (SINV2 & AEXP2 & ext); cbn in *; inv_eqs.

      cbn; rewrite denote_code_singleton...
      rewrite denote_instr_intrinsic; cbn; try reflexivity.
      4:{ cbn...
          rewrite AEXP1; auto...
          rewrite AEXP2; [cbn; rauto; reflexivity | reflexivity].
      }
      2: cbn; rauto; reflexivity.
      2: reflexivity.
      apply eutt_Ret.
      cbn.
      split.
      + eapply state_invariant_add_fresh; eauto.
      + split; cbn; intuition.
        * cbn...
          reflexivity.
          cbn. apply H1.
          replace (Float_minimum vH vH0) with (MFloat64asCT.CTypeMin vH vH0) by admit.
          apply In_add_eq.
        * rewrite H,H0.
          apply sub_alist_add.
          eapply concrete_fresh_fresh; eauto.
          eapply incLocal_is_fresh; eauto.
 
   - (* AMax *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in *; simp...

      rewrite convert_typ_app, denote_code_app...
      eapply eutt_clo_bind_returns; try eapply IHaexp1; eauto.
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (SINV1 & AEXP1 & ext); cbn in *; inv_eqs.

      rewrite convert_typ_app, denote_code_app...
      eapply eutt_clo_bind; try eapply IHaexp2; eauto.
      introR; destruct_unit.
      destruct PRE0 as (SINV2 & AEXP2 & ext); cbn in *; inv_eqs.

      cbn; rewrite denote_code_singleton...
      rewrite denote_instr_intrinsic; cbn; try reflexivity.
      4:{ cbn...
          rewrite AEXP1; auto...
          rewrite AEXP2; [cbn; rauto; reflexivity | reflexivity].
      }
      2: cbn; rauto; reflexivity.
      2: reflexivity.
      apply eutt_Ret.
      cbn.
      split.
      + eapply state_invariant_add_fresh; eauto.
      + split; cbn; intuition.
        * cbn...
          reflexivity.
          cbn. apply H1.
          replace (Float_maxnum vH vH0) with (MFloat64asCT.CTypeMax vH vH0) by admit.
          apply In_add_eq.
        * rewrite H,H0.
          apply sub_alist_add.
          eapply concrete_fresh_fresh; eauto.
          eapply incLocal_is_fresh; eauto.

   - (* AZless *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in *; simp...

      rewrite convert_typ_app, denote_code_app...
      eapply eutt_clo_bind_returns; try eapply IHaexp1; eauto.
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (SINV1 & AEXP1 & ext); cbn in *; inv_eqs.

      rewrite convert_typ_app, denote_code_app...
      eapply eutt_clo_bind; try eapply IHaexp2; eauto.
      introR; destruct_unit.
      destruct PRE0 as (SINV2 & AEXP2 & ext); cbn in *; inv_eqs.

      cbn...
      cbn; rewrite denote_code_cons...
      rewrite denote_instr_op.
      2: {
        cbn...
        rewrite AEXP1; auto...
        rewrite AEXP2; [| reflexivity]...
        cbn...
        reflexivity.
      }

      cbn...
      cbn; rewrite denote_code_cons...
      destruct (float_cmp vH vH0) as (? & ? & ?).
      rewrite denote_instr_comment...
      rewrite denote_instr_op.
      2:{ simpl.
          autorewrite with itree.
          autorewrite with vellvm.
          2:apply In_add_eq.
          cbn...
          unfold uvalue_to_dvalue_uop.
          rewrite uvalue_to_dvalue_of_dvalue_to_uvalue; cbn...
          match_rewrite.
          cbn...
          reflexivity.
      }

      apply eutt_Ret.
      cbn.
      split.
      + cbn.
        eapply state_invariant_incVoid; eauto.
        repeat (eapply state_invariant_add_fresh; eauto).
      + split; cbn; intuition.
        * cbn...
          reflexivity.
          cbn. apply H3.
          match goal with
            |- alist_In _ (alist_add _ ?x _) ?y => replace x with y by admit
          end.
          apply In_add_eq.
        * rewrite H,H0.
          etransitivity; [apply sub_alist_add| apply sub_alist_add].
          eapply concrete_fresh_fresh; eauto; eapply incLocal_is_fresh; eauto.
          eapply concrete_fresh_fresh; eauto; eapply incLocal_is_fresh; eauto.
          match goal with
            |- state_invariant _ _ _ (_, (alist_add _ _ _, _)) =>
            eapply state_invariant_add_fresh; [now eauto | eassumption ]
          end.

  Admitted.

End AExpr.
