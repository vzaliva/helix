Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.StateCounters.
Require Import Helix.LLVMGen.Correctness_Invariants.
Import LidBound.

From Coq Require Import ZArith.

(* Import ProofNotations. *)
Import ListNotations.

Open Scope Z.
Open Scope list.

Set Implicit Arguments.
Set Strict Implicit.

(* YZ TODO: Check that this is global and factor it in prelude *)
Typeclasses Opaque equiv.

(** * Correctness of the compilation of numerical expressions

     We prove in this section the correctness of the compilation of numerical expressions, i.e. [NExpr].
     The corresponding compiling function is [ genNexpr].

     Helix side:
     * nexp: NExpr
     * σ: evalContext
     Compiler side:
     * s1 s2: IRState
     Vellvm side:
     * c : code
     * e : exp typ

 *)

Section NExpr.
  
(** * Tactics
    
  - [cbn*] : unfolds a fixed list of definitions we want to go under, and reduces via [cbn]
  - [simp] : systematically destruct [match] in the context. Used in particular to systematically
             derive from the success of the compilation the success of the compilation of the sub-components.
  - [try_abs] : attempts to automatically discharge absurd cases. Relies essentially on two sources to this end:
             type constraints provided by [memory_invariant], and success of the computation provided by
             [no_failure].

  - [solve_lu] : attempts to discharge goal of the shape [Maps.lookup id l = Some ?]
  - [solve_state_invariant] : attempts to discharge goal of the shape [state_invariant _ _ _ _] 

  - [hvred] : stands for helix-vellvm-reduction. Uses rewriting to "reduce" both side of the simulation
             being proved to a bind whose first component is either the denotation of a parameter,
             or of a concrete operation to be processed. 
  - [vred] : stands for vellvm-reduction. Similar to [hvred], but performing only [vellvm]-based reduction
             on the right hand-side of the simulation.
             In the context of this development, is a synonymous for [vstep_r].
             To perform it on the left-hand-side of [eutt], use [vstep_l].
   - [tred] :alias for [autorewrite with itree]. Useful to fill in defaults in the current automation,
             hopefully will be made useless soon.
   - [vstep]: stands for vellvm-step. Performs a single atomic forward-reasoning principle, processing for
             instance a single instruction or expression.
             Cycles goals so that it exhibits first the generated side conditions.
  - [hstep]: stands helix-step. Processes a single trigger of a memory event.

 *)

  (* Import ProofMode. *)
  Opaque incBlockNamed.
  Opaque incVoid.
  Opaque incLocal.

  Definition genNExpr_exp_correct σ s1 s2 (e: exp typ) 
    : Rel_cfg_T DynamicValues.int64 unit :=
    fun '(x,i) '(memV,(l,(g,v))) =>
      forall l',
        local_scope_preserved s1 s2 l l' ->
        Gamma_preserved σ s1 l l' ->
        interp_cfg
          (translate exp_E_to_instr_E (denote_exp (Some (DTYPE_I 64%N)) (convert_typ [] e)))
          g l' memV ≈
          Ret (memV,(l',(g,UVALUE_I64 i))).

  Record genNExpr_post
         (e : exp typ)
         σ s1 s2
         (mi : memoryH) (sti : config_cfg)
         (mf : memoryH * DynamicValues.int64) (stf : config_cfg_T unit)
    : Prop :=
    {
    exp_correct : genNExpr_exp_correct σ s1 s2 e mf stf;
    is_almost_pure : almost_pure mi sti mf stf; 
    extends : local_scope_modif s1 s2 (fst (snd sti)) (fst (snd stf));
    exp_in_scope : forall id, e ≡ EXP_Ident (ID_Local id) -> ((exists v, alist_In id (fst (snd sti)) v) \/ (lid_bound_between s1 s2 id /\ s1 << s2));
    Gamma_cst : Γ s2 ≡ Γ s1;
    Mono_IRState : s1 << s2 \/ fst (snd sti) ≡ fst (snd stf)
    }.

  Lemma genNExpr_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *)   (nexp: NExpr) (σ: evalContext) (memH: memoryH) 
      (* Vellvm bits *)   (e: exp typ) (c: code typ) (g : global_env) ((* li *) l : local_env) (memV : memoryV),

      genNExpr nexp s1 ≡ inr (s2, (e, c))      -> (* Compilation succeeds *)
      (state_invariant σ s1) memH (memV, (l, g)) -> (* The main state invariant is initially true *)
      Gamma_safe σ s1 s2 ->
      no_failure (interp_helix (E := E_cfg) (denoteNExpr σ nexp) memH) -> (* Source semantics defined *)
      (* eutt (succ_cfg (lift_Rel_cfg (state_invariant_post σ s1 s2 l) ⩕ *)
      eutt (succ_cfg (lift_Rel_cfg (state_invariant σ s2) ⩕
                     genNExpr_post e σ s1 s2 memH (mk_config_cfg memV l g)))
           (interp_helix (denoteNExpr σ nexp) memH)
           (interp_cfg (denote_code (convert_typ [] c)) g l memV).
  Proof.
    intros s1 s2 nexp; revert s1 s2; induction nexp; intros * COMPILE PRE SAFE NOFAIL.
    - (* Variable case *)
      (* Reducing the successful compilation *)
      cbn* in COMPILE; simp.

      + (* The variable maps to an integer in the IRState *)
        unfold denoteNExpr in *; cbn* in *; simp; try_abs. 
        hvred.

        (* The identifier has to be a local one *)
        destruct i0.
        inv PRE; try_abs.

        (* We establish the postcondition *)
        apply eutt_Ret; split; [| split]; cbn; eauto.
        * intros l' LOC GAM; cbn*.
          inv PRE.
          vstep.
          cbn.
          red in GAM.
          erewrite <- GAM.
          eapply memory_invariant_LLU; eauto.
          econstructor;eauto.
          reflexivity.
        * intros * EQ; inv EQ.
          left.
          eexists.
          eapply memory_invariant_LLU; eauto.

      + (* The variable maps to a pointer *)
        unfold denoteNExpr in *; cbn* in *; simp; try_abs.
        break_inner_match_goal; try_abs.
        hvred.
        (* We need to be a bit careful: when stepping the [load], we will need to provide the memory address
           at which we load. This address needs to be in scope when introducing the evar, we are therefore
           forced to look a bit ahead and first use [memory_invariant_GLU].
         *)

        edestruct memory_invariant_GLU as (ptr & LU & READ); eauto.
        rewrite typ_to_dtyp_equation in READ.
        vstep.
        vstep; eauto; reflexivity.
        apply eutt_Ret; cbn; split; [| split]; cbn; eauto.
        * eapply state_invariant_add_fresh; eauto.
          eapply WF_IRState_Γ; eauto.
          symmetry.
          eapply incLocal_Γ; eauto.
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

    - (* Constant *)
      cbn* in COMPILE; simp.
      unfold denoteNExpr in *; cbn*.
      hvred.

      apply eutt_Ret; split; [| split]; cbn; eauto.
      intros l' MONO; cbn*.
      vstep; reflexivity.
      intros * EQ; inv EQ.

    - (* NDiv *)
      cbn* in *; simp; try_abs.
      hvred.
      rename i into s2, i0 into s3, s2 into s4.
      clean_goal.

      specialize (IHnexp1 _ _ σ memH _ _ g l memV Heqs).
      forward IHnexp1.
      { inv PRE; split; auto.
        (* solve_fresh. *)
      }
      forward IHnexp1; eauto.
      eapply Gamma_safe_shrink; eauto; solve_local_count.
      forward IHnexp1; eauto.
     
      (* e1 *)
      eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp1].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (PRE1 & [EXP1 EXT1 SCOPE1 VAR1 GAM1 MONO1]).
      cbn* in *; inv_eqs.
      (* rename H into VAR1. *)
      hvred.

      (* e2 *)
      specialize (IHnexp2 _ _ σ memH _ _ g l0 memV Heqs0).
      forward IHnexp2; auto.
      forward IHnexp2; eauto.
      eapply Gamma_safe_shrink; eauto; solve_local_count.
      forward IHnexp2; eauto. 

      eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp2].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (PRE2 & [EXP2 EXT2 SCOPE2 VAR2 GAM2 MONO2]).
      cbn* in *; inv_eqs.
      (* rename H into VAR2. *)

      (* division *) 
      simp; try_abs.
      hvred.

      specialize (EXP1 l1) .
      specialize (EXP2 l1) .
      forward EXP2.
      auto using local_scope_preserved_refl.
      forward EXP2.
      auto using Gamma_preserved_refl.
      forward EXP1.
      {
        clear EXP1 EXP2 VAR1 VAR2.
        clean_goal.
        destruct MONO2 as [| <-]; [| apply local_scope_preserved_refl].
        eapply local_scope_preserve_modif; eauto.
      }
      forward EXP1.
      {
        apply Gamma_preserved_Gamma_eq with s2; auto.
        eapply Gamma_preserved_if_safe; eauto.
        eapply Gamma_safe_shrink; eauto; solve_local_count.
      }

      hvred.
      vstep.
      {
        vstep; eauto; try reflexivity.
        cbn; break_inner_match_goal; try reflexivity.
        exfalso; apply n.
        apply Z.eqb_eq in Heqb.
        rewrite <- Int64.unsigned_zero in Heqb.
        unfold MInt64asNT.NTypeZero.
        apply unsigned_is_zero; auto.
      }

      apply eutt_Ret; cbn; split; [| split]; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
        eapply WF_IRState_Γ; eauto.
        symmetry; eapply incLocal_Γ; eauto.
        
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

    - (* NMod *)
      cbn* in *; simp; try_abs.
      hvred.

      rename i into s2, i0 into s3, s2 into s4.
      clean_goal.

      specialize (IHnexp1 _ _ σ memH _ _ g l memV Heqs).
      forward IHnexp1.
      { inv PRE; split; auto.
        (* solve_fresh. *)
      }
      forward IHnexp1; eauto.
      eapply Gamma_safe_shrink; eauto; solve_local_count.
      forward IHnexp1; eauto.
     
      (* e1 *)
      eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp1].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (PRE1 & [EXP1 EXT1 SCOPE1 VAR1 GAM1 MONO1]).
      cbn* in *; inv_eqs.
      (* rename H into VAR1. *)
      hvred.

      (* e2 *)
      specialize (IHnexp2 _ _ σ memH _ _ g l0 memV Heqs0).
      forward IHnexp2; auto.

      forward IHnexp2; eauto.
      eapply Gamma_safe_shrink; eauto; solve_local_count.
      forward IHnexp2; eauto. 

      eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp2].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (PRE2 & [EXP2 EXT2 SCOPE2 VAR2 GAM2 MONO2]).
      cbn* in *; inv_eqs.
      (* rename H into VAR2. *)

      (* division *)
      simp; try_abs.
      hvred.

      specialize (EXP1 l1) .
      specialize (EXP2 l1) .
      forward EXP2.
      auto using local_scope_preserved_refl.
      forward EXP2.
      auto using Gamma_preserved_refl.
      forward EXP1.
      {
        clear EXP1 EXP2 VAR1 VAR2.
        clean_goal.
        destruct MONO2 as [| <-]; [| apply local_scope_preserved_refl].
        eapply local_scope_preserve_modif; eauto.
      }
      forward EXP1.
      {
        apply Gamma_preserved_Gamma_eq with s2; auto.
        eapply Gamma_preserved_if_safe; eauto.
        eapply Gamma_safe_shrink; eauto; solve_local_count.
      }

      hvred.
      vstep.
      {

        vstep; eauto; try reflexivity.
        cbn; break_inner_match_goal; try reflexivity.
        exfalso; apply n.

        apply Z.eqb_eq in Heqb.
        rewrite <- Int64.unsigned_zero in Heqb.
        unfold MInt64asNT.NTypeZero.
        apply unsigned_is_zero; auto.
      }

      apply eutt_Ret; cbn; split; [| split]; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
        eapply WF_IRState_Γ; eauto.
        symmetry; eapply incLocal_Γ; eauto.
        
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
   - (* NAdd *)

     cbn* in *; simp; try_abs.
     hvred.

     rename i into s2, i0 into s3, s2 into s4.
     clean_goal.

     specialize (IHnexp1 _ _ σ memH _ _ g l memV Heqs).
     forward IHnexp1; auto.
     
     forward IHnexp1; eauto.
     eapply Gamma_safe_shrink; eauto; solve_local_count.
     forward IHnexp1; eauto.
     
     (* e1 *)
     eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp1].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PRE1 & [EXP1 EXT1 SCOPE1 VAR1 GAM1 MONO1]).
     cbn* in *; inv_eqs.
     (* rename H into VAR1. *)
     hvred.

     (* e2 *)
     specialize (IHnexp2 _ _ σ memH _ _ g l0 memV Heqs0).
     forward IHnexp2; auto.

     forward IHnexp2; eauto.
     eapply Gamma_safe_shrink; eauto; solve_local_count.
     forward IHnexp2; eauto. 

     eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp2].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.

     destruct PRE0 as (PRE2 & [EXP2 EXT2 SCOPE2 VAR2 GAM2 MONO2]).
     cbn* in *; inv_eqs.

     specialize (EXP1 l1) .
     specialize (EXP2 l1) .
     forward EXP2.
     auto using local_scope_preserved_refl.
     forward EXP2.
     auto using Gamma_preserved_refl.
     forward EXP1.
     {
       clear EXP1 EXP2 VAR1 VAR2.
       clean_goal.
       destruct MONO2 as [| <-]; [| apply local_scope_preserved_refl].
       eapply local_scope_preserve_modif; eauto.
     }
     forward EXP1.
     {
       apply Gamma_preserved_Gamma_eq with s2; auto.
       eapply Gamma_preserved_if_safe; eauto.
       eapply Gamma_safe_shrink; eauto; solve_local_count.
     }

     hvred.
     vstep; cbn; eauto.
     vstep; cbn; eauto; reflexivity.

     apply eutt_Ret; cbn; split; [| split]; cbn; eauto.
     + eapply state_invariant_add_fresh; eauto.
       eapply WF_IRState_Γ; eauto.
       symmetry; eapply incLocal_Γ; eauto.
       
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
       
   - (* NMinus *)

     cbn* in *; simp; try_abs.
     hvred.

     rename i into s2, i0 into s3, s2 into s4.
     clean_goal.

     specialize (IHnexp1 _ _ σ memH _ _ g l memV Heqs).
     forward IHnexp1; auto.
     forward IHnexp1; eauto.
     eapply Gamma_safe_shrink; eauto; solve_local_count.
     forward IHnexp1; eauto.
     
     (* e1 *)
     eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp1].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PRE1 & [EXP1 EXT1 SCOPE1 VAR1 GAM1 MONO1]).
     cbn* in *; inv_eqs.
     (* rename H into VAR1. *)
     hvred.

     (* e2 *)
     specialize (IHnexp2 _ _ σ memH _ _ g l0 memV Heqs0).
     forward IHnexp2; auto.

     forward IHnexp2; eauto.
     eapply Gamma_safe_shrink; eauto; solve_local_count.
     forward IHnexp2; eauto. 

     eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp2].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PRE2 & [EXP2 EXT2 SCOPE2 VAR2 GAM2 MONO2]).
     cbn* in *; inv_eqs.

     specialize (EXP1 l1) .
     specialize (EXP2 l1) .
     forward EXP2.
     auto using local_scope_preserved_refl.
     forward EXP2.
     auto using Gamma_preserved_refl.
     forward EXP1.
     {
       clear EXP1 EXP2 VAR1 VAR2.
       clean_goal.
       destruct MONO2 as [| <-]; [| apply local_scope_preserved_refl].
       eapply local_scope_preserve_modif; eauto.
     }
     forward EXP1.
     {
       apply Gamma_preserved_Gamma_eq with s2; auto.
       eapply Gamma_preserved_if_safe; eauto.
       eapply Gamma_safe_shrink; eauto; solve_local_count.
     }

     hvred.
     vstep; cbn; eauto.
     vstep; cbn; eauto; reflexivity.

     apply eutt_Ret; cbn; split; [| split]; cbn; eauto.
     + eapply state_invariant_add_fresh; eauto.
       eapply WF_IRState_Γ; eauto.
       symmetry; eapply incLocal_Γ; eauto.
       
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

   - (* NMult *)
     
     cbn* in *; simp; try_abs.
     hvred.

     rename i into s2, i0 into s3, s2 into s4.
     clean_goal.

     specialize (IHnexp1 _ _ σ memH _ _ g l memV Heqs).
     forward IHnexp1; auto.
     forward IHnexp1; eauto.
     eapply Gamma_safe_shrink; eauto; solve_local_count.
     forward IHnexp1; eauto.
     
     (* e1 *)
     eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp1].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PRE1 & [EXP1 EXT1 SCOPE1 VAR1 GAM1 MONO1]).
     cbn* in *; inv_eqs.
     (* rename H into VAR1. *)
     hvred.

     (* e2 *)
     specialize (IHnexp2 _ _ σ memH _ _ g l0 memV Heqs0).
     forward IHnexp2; auto.

     forward IHnexp2; eauto.
     eapply Gamma_safe_shrink; eauto; solve_local_count.
     forward IHnexp2; eauto. 

     eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp2].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PRE2 & [EXP2 EXT2 SCOPE2 VAR2 GAM2 MONO2]).
     cbn* in *; inv_eqs.

     specialize (EXP1 l1) .
     specialize (EXP2 l1) .
     forward EXP2.
     auto using local_scope_preserved_refl.
     forward EXP2.
     auto using Gamma_preserved_refl.
     forward EXP1.
     {
       clear EXP1 EXP2 VAR1 VAR2.
       clean_goal.
       destruct MONO2 as [| <-]; [| apply local_scope_preserved_refl].
       eapply local_scope_preserve_modif; eauto.
     }
     forward EXP1.
     {
       apply Gamma_preserved_Gamma_eq with s2; auto.
       eapply Gamma_preserved_if_safe; eauto.
       eapply Gamma_safe_shrink; eauto; solve_local_count.
     }

     hvred.
     vstep; cbn; eauto.
     vstep; cbn; eauto; try reflexivity.
     cbn.
     break_inner_match; reflexivity.
     
     apply eutt_Ret; cbn; split; [| split]; cbn; eauto.
     + eapply state_invariant_add_fresh; eauto.
       eapply WF_IRState_Γ; eauto.
       symmetry; eapply incLocal_Γ; eauto.
       
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
   - (* NMin *)
      (* Non-implemented by the compiler *)
      inversion COMPILE.
    - (* NMax *)
      (* Non-implemented by the compiler *)
      inversion COMPILE.
  Qed.

End NExpr.
