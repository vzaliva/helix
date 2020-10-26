Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Freshness.
Require Import Helix.LLVMGen.Correctness_Invariants.

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
  
  (** At the top level, the correctness of genNExpr is expressed as the denotation of the operator being equivalent
      to the bind of denoting the code followed by denoting the expression.
      However this is not inductively stable, we only want to plug the expression at the top level.
      We therefore instead carry the fact about the denotation of the expression in the invariant. (Is there another clever way?)
   *)
  Definition genNExpr_exp_correct_ind (e: exp typ)
  : Rel_cfg_T DynamicValues.int64 unit :=
    fun '(x,i) '(memV,(l,(g,v))) =>
      forall l', l ⊑ l' ->
            interp_cfg
              (translate exp_E_to_instr_E (denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] e)))
              g l' memV ≈
              Ret (memV,(l',(g,UVALUE_I64 i))).

  (**
     We package the local specific invariants. Additionally to the evaluation of the resulting expression,
     we also state that evaluating the code preserves most of the state, except for the local state being
     allowed to be extended with fresh bindings.
   *)
  Record genNExpr_rel_ind
         (e : exp typ)
         (mi : memoryH) (sti : config_cfg)
         (mf : memoryH * DynamicValues.int64) (stf : config_cfg_T unit)
    : Prop :=
    {
    exp_correct : genNExpr_exp_correct_ind e mf stf;
    monotone : ext_local mi sti mf stf
    }.

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

  Import ProofMode.

  Lemma genNExpr_correct_ind :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *)   (nexp: NExpr) (σ: evalContext) (memH: memoryH) 
      (* Vellvm bits *)   (e: exp typ) (c: code typ) (g : global_env) (l : local_env) (memV : memoryV),

      genNExpr nexp s1 ≡ inr (s2, (e, c))      -> (* Compilation succeeds *)
      (state_invariant σ s1 ⩕ fresh_pre s1 s2) memH (memV, (l, g)) -> (* The main state invariant is initially true *)
      no_failure (interp_helix (E := E_cfg) (denoteNExpr σ nexp) memH) -> (* Source semantics defined *)
      eutt (succ_cfg (lift_Rel_cfg (state_invariant σ s2) ⩕
                     lift_Rel_cfg (fresh_post s1 s2 l) ⩕
                     genNExpr_rel_ind e memH (mk_config_cfg memV l g)))
           (interp_helix (denoteNExpr σ nexp) memH)
           (interp_cfg (denote_code (convert_typ [] c)) g l memV).
  Proof.
    intros s1 s2 nexp; revert s1 s2; induction nexp; intros * COMPILE [PRE PREF] NOFAIL.

    - (* Variable case *)
      (* Reducing the successful compilation *)
      cbn* in COMPILE; simp.

      + (* The variable maps to an integer in the IRState *)
        unfold denoteNExpr in *; cbn* in *; simp; try_abs. 
        hvred.

        (* The identifier has to be a local one *)
        destruct i0; try_abs.

        (* We establish the postcondition *)
        apply eutt_Ret; cbn; splits; cbn; auto.
        solve_fresh.
        split; auto.
        intros l' MONO; cbn*.
        vstep.
        solve_lu.
        reflexivity.

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

        apply eutt_Ret; cbn; splits; cbn; eauto with fresh.
        -- cbn.
           solve_state_invariant.
        -- split.
           intros l' MONO; cbn*.
           vstep; [solve_lu | reflexivity].
           repeat split.
           solve_sub_alist.

    - (* Constant *)
      cbn* in COMPILE; simp.
      unfold denoteNExpr in *; cbn*.
      hvred.

      apply eutt_Ret; cbn; splits; cbn; eauto with fresh.
      split; auto.
      intros l' MONO; cbn*.
      vstep; reflexivity.

    - (* NDiv *)
      cbn* in *; simp; try_abs.
      hvred.

      specialize (IHnexp1 _ _ σ memH _ _ g l memV Heqs).
      forward IHnexp1.
      { split; auto.

  match goal with
  | h: freshness_pre ?s ?s' ?l |- freshness_pre ?s _ ?l => apply freshness_pre_shrink_up with (1 := h) end.  solve_local_count.
  | h: freshness_pre _ ?s _ |- freshness_pre _ ?s _ => apply freshness_chain with (1 := h); solve_fresh
  | h: freshness_post _ ?s _ ?x |- freshness_pre ?s _ ?x => eapply freshness_chain with (2 := h); solve_fresh
  | |- freshness_post _ _ _ _ => first [eassumption | eapply freshness_post_inclocal; eassumption | eapply freshness_post_transitive; [eassumption |]]; solve_fresh
  end.

  
        solve_fresh.


        unfold IRState_lt, IRState_le in *; get_local_count_hyps. lia.
        solve_local_count_tac.
      }
      forward IHnexp1; eauto.
     
      (* e1 *)
      eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp1].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (PRE1 & PREF1 & (EXPR1 & <- & <- & <- & MONO1)). 
      hvred.
      cbn in *.

      (* e2 *)
      specialize (IHnexp2 _ _ σ memH _ _ g l0 memV Heqs0).
      forward IHnexp2.
      {
        split; auto.
        solve_fresh.
      }
      forward IHnexp2; eauto.

      eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp2].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (PRE2 & PREF2 & (EXPR2 & <- & <- & <- & MONO2)).
      cbn in *.

      (* division *)
      simp; try_abs.
      hvred.

      specialize (EXPR1 _ MONO2) .
      assert (l1 ⊑ l1) as L1L1 by reflexivity; specialize (EXPR2 _ L1L1). 
      cbn in *.
      hvred.
      vstep.
      {
        vstep; eauto; try reflexivity.
        cbn; break_inner_match_goal; try reflexivity.
        exfalso; apply n.
        clear EXPR2 EXPR1.
        apply Z.eqb_eq in Heqb.
        rewrite <- Int64.unsigned_zero in Heqb.
        unfold MInt64asNT.NTypeZero.
        apply unsigned_is_zero; auto.
      }

      apply eutt_Ret; cbn; splits; cbn.
      {
        solve_state_invariant.
      }
      {
        solve_fresh.
      }
      { split; auto.
        intros ? MONO; cbn.
        vstep; solve_lu; reflexivity.
        apply ext_local_subalist.
        etransitivity; eauto.
        etransitivity; eauto.
        apply sub_alist_add.
        eapply freshness_pre_alist_fresh_specialized; eauto.
        solve_fresh.
      }
        
    - (* NMod *)
      cbn* in *; simp; try_abs.
      hvred.

      specialize (IHnexp1 _ _ σ memH _ _ g l memV Heqs).
      forward IHnexp1.
      { split; auto.
        solve_fresh.
      }
      forward IHnexp1; eauto.

      eapply eutt_clo_bind_returns; [eassumption | clear IHnexp1].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      cbn in *.
      destruct PRE0 as (PRE1 & PREF1 & (EXPR1 & <- & <- & <- & MONO1)). 
      hvred.
      cbn in *.

      specialize (IHnexp2 _ _ σ memH _ _ g l0 memV Heqs0).
      forward IHnexp2.
      {
        split; auto.
        solve_fresh.
      }
      forward IHnexp2; eauto.
      eapply eutt_clo_bind_returns; [eassumption | clear IHnexp2].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (PRE2 & PREF2 & (EXPR2 & <- & <- & <- & MONO2)).
      cbn; hvred.
      break_match_goal; try_abs...
      hvred.
      
      vstep.
      (* Operator evaluation *)
      {
        vstep; cbn; eauto; try reflexivity.
        eapply EXPR2; reflexivity.
        reflexivity.
        cbn; break_inner_match_goal; try reflexivity.

        (* Division by 0 *)
        exfalso.
        apply Z.eqb_eq in Heqb.
        exfalso. apply n.
        rewrite <- Int64.unsigned_zero in Heqb.
        unfold MInt64asNT.NTypeZero.
        apply unsigned_is_zero; auto.
      }


      apply eutt_Ret; cbn; splits; cbn.
      {
        solve_state_invariant.
      }
      {
        solve_fresh.
      }
      { split; auto.
        intros ? MONO; cbn.
        vstep; solve_lu; reflexivity.
        apply ext_local_subalist.
        etransitivity; eauto.
        etransitivity; eauto.
        apply sub_alist_add.
        eapply freshness_pre_alist_fresh_specialized; eauto.
        solve_fresh.
      }
 
   - (* NAdd *)

     cbn* in *; simp; try_abs.
     hvred.

     specialize (IHnexp1 _ _ σ memH _ _ g l memV Heqs).
     forward IHnexp1.
     { split; auto.
       solve_fresh.
     }
     forward IHnexp1; eauto.

     eapply eutt_clo_bind_returns; [eassumption | clear IHnexp1].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PRE1 & PREF1 & (EXPR1 & <- & <- & <- & MONO1)). 
     hvred.
     cbn in *.

     specialize (IHnexp2 _ _ σ memH _ _ g l0 memV Heqs0).
     forward IHnexp2.
     {
       split; auto.
       solve_fresh.
     }
     forward IHnexp2; eauto.
     eapply eutt_clo_bind_returns; [eassumption | clear IHnexp2].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PRE2 & PREF2 & (EXPR2 & <- & <- & <- & MONO2)).
     cbn; hvred.

     vstep.
     vstep; cbn; try (eapply EXPR2 || eapply EXPR1); eauto; reflexivity.

     apply eutt_Ret; cbn; splits; cbn.
     {
       solve_state_invariant.
     }
     {
       solve_fresh.
     }
     { split; auto.
       intros ? MONO; cbn.
       vstep; solve_lu; reflexivity.
       apply ext_local_subalist.
       etransitivity; eauto.
       etransitivity; eauto.
       apply sub_alist_add.
       eapply freshness_pre_alist_fresh_specialized; eauto.
       solve_fresh.
     }
     
   - (* NMinus *)

     cbn* in *; simp; try_abs.
     hvred.

     specialize (IHnexp1 _ _ σ memH _ _ g l memV Heqs).
     forward IHnexp1.
     { split; auto.
       solve_fresh.
     }
     forward IHnexp1; eauto.
     eapply eutt_clo_bind_returns; [eassumption | clear IHnexp1].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PRE1 & PREF1 & (EXPR1 & <- & <- & <- & MONO1)). 
     hvred; cbn in *.

     specialize (IHnexp2 _ _ σ memH _ _ g l0 memV Heqs0).
     forward IHnexp2.
     { split; auto.
       solve_fresh.
     }
      forward IHnexp2; eauto.
     eapply eutt_clo_bind_returns; [eassumption | clear IHnexp2].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PRE2 & PREF2 & (EXPR2 & <- & <- & <- & MONO2)).
     cbn; hvred.

     vstep.
     vstep; cbn; try (eapply EXPR2 || eapply EXPR1); eauto; reflexivity.

     apply eutt_Ret; cbn; splits; cbn.
     {
       solve_state_invariant.
     }
     {
       solve_fresh.
     }
     { split; auto.
       intros ? MONO; cbn.
       vstep; solve_lu; reflexivity.
       apply ext_local_subalist.
       etransitivity; eauto.
       etransitivity; eauto.
       apply sub_alist_add.
       eapply freshness_pre_alist_fresh_specialized; eauto.
       solve_fresh.
     }
 
   - (* NMult *)
     
     cbn* in *; simp; try_abs.
     hvred.

     specialize (IHnexp1 _ _ σ memH _ _ g l memV Heqs).
     forward IHnexp1.
     { split; auto.
       solve_fresh.
     }
     forward IHnexp1; eauto.
     eapply eutt_clo_bind_returns; [eassumption | clear IHnexp1].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PRE1 & PREF1 & (EXPR1 & <- & <- & <- & MONO1)). 
     hvred; cbn in *.

     specialize (IHnexp2 _ _ σ memH _ _ g l0 memV Heqs0).
     forward IHnexp2.
     { split; auto.
       solve_fresh.
     }
      forward IHnexp2; eauto.
     eapply eutt_clo_bind_returns; [eassumption | clear IHnexp2].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PRE2 & PREF2 & (EXPR2 & <- & <- & <- & MONO2)).
     cbn; hvred.

     vstep.
     (* Operator evaluation *)
     {
        vstep; cbn; try (eapply EXPR2 || eapply EXPR1); eauto; try reflexivity.
        cbn.
        break_inner_match; reflexivity.
      }

     apply eutt_Ret; cbn; splits; cbn.
     {
       solve_state_invariant.
     }
     {
       solve_fresh.
     }
     { split; auto.
       intros ? MONO; cbn.
       vstep; solve_lu; reflexivity.
       apply ext_local_subalist.
       etransitivity; eauto.
       etransitivity; eauto.
       apply sub_alist_add.
       eapply freshness_pre_alist_fresh_specialized; eauto.
       solve_fresh.
     }
 
   - (* NMin *)
      (* Non-implemented by the compiler *)
      inversion COMPILE.
    - (* NMax *)
      (* Non-implemented by the compiler *)
      inversion COMPILE.
  Qed.

End NExpr.

Notation fresh_pre := (fun s1 s2 => lift_fresh (freshness_pre s1 s2)). 
Notation fresh_post := (fun s1 s2 l => lift_fresh (freshness_post s1 s2 l)). 
Definition genNExpr_exp_correct (σ : evalContext) (s : IRState) (e: exp typ)
  : Rel_cfg_T DynamicValues.int64 unit :=
  fun '(memH,i) '(memV,(l,(g,v))) => 
    eutt Logic.eq 
         (interp_cfg
            (translate exp_E_to_instr_E (denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] e)))
            g l memV)
         (Ret (memV,(l,(g,UVALUE_I64 i)))).

Lemma genNExpr_correct :
  forall (* Compiler bits *) (s1 s2: IRState)
    (* Helix  bits *)   (nexp: NExpr) (σ: evalContext) (memH: memoryH) 
    (* Vellvm bits *)   (e: exp typ) (c: code typ) (g : global_env) (l : local_env) (memV : memoryV),

    genNExpr nexp s1 ≡ inr (s2, (e, c))      -> (* Compilation succeeds *)
    (state_invariant σ s1 ⩕ fresh_pre s1 s2) memH (memV, (l, g)) -> (* The main state invariant is initially true *)
    no_failure (interp_helix (E := E_cfg) (denoteNExpr σ nexp) memH) -> (* Source semantics defined *)
    eutt (succ_cfg
            (lift_Rel_cfg (state_invariant σ s2 ⩕ fresh_post s1 s2 l) ⩕ ext_local memH (memV,(l,g)))
         )
         (interp_helix (denoteNExpr σ nexp) memH)
         (interp_cfg (denote_code (convert_typ [] c)) g l memV).
Proof.
  intros.
  eapply eutt_mon; cycle -1.
  eapply genNExpr_correct_ind; eauto.
  intros [(? & ?) |] (? & ? & ? & []) INV; [destruct INV as (SI & ? & EXP & ?) | inv INV].
  cbn in *.
  specialize (EXP l0).
  forward EXP; [reflexivity |].
  split; auto.
  split; auto.
Qed.
