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
  Definition genNExpr_exp_correct_ind (σ : evalContext) (s : IRState) (e: exp typ)
  : Rel_cfg_T DynamicValues.int64 unit :=
    fun '(x,i) '(memV,(l,(g,v))) =>
      forall l', sub_local_no_aliasing σ s l l' g ->
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
         (σ : evalContext)
         (s : IRState)
         (e : exp typ)
         (mi : memoryH) (sti : config_cfg)
         (mf : memoryH * DynamicValues.int64) (stf : config_cfg_T unit)
    : Prop :=
    {
    exp_correct : genNExpr_exp_correct_ind σ s e mf stf;
    monotone : ext_local_no_aliasing σ s mi sti mf stf
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
  Opaque incBlockNamed.
  Opaque incVoid.
  Opaque incLocal.

  Ltac split_post := split; [split | split]; [solve_state_invariant | solve_fresh | | cbn; intuition; try solve_sub_local_no_aliasing].

  Lemma genNExpr_correct_ind :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *)   (nexp: NExpr) (σ: evalContext) (memH: memoryH) 
      (* Vellvm bits *)   (e: exp typ) (c: code typ) (g : global_env) (l : local_env) (memV : memoryV),

      genNExpr nexp s1 ≡ inr (s2, (e, c))      -> (* Compilation succeeds *)
      (state_invariant_pre σ s1 s2) memH (memV, (l, g)) -> (* The main state invariant is initially true *)
      no_failure (interp_helix (E := E_cfg) (denoteNExpr σ nexp) memH) -> (* Source semantics defined *)
      eutt (succ_cfg (lift_Rel_cfg (state_invariant_post σ s1 s2 l) ⩕
                     genNExpr_rel_ind σ s2 e memH (mk_config_cfg memV l g)))
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
        apply eutt_Ret; cbn; split_post; eauto.
        intros l' [MONO ALIAS]; cbn*.
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

        apply eutt_Ret; cbn; split_post.

        intros l' [MONO ALIAS]; cbn*.
        vstep; [solve_lu | reflexivity].
    - (* Constant *)
      cbn* in COMPILE; simp.
      unfold denoteNExpr in *; cbn*.
      hvred.

      apply eutt_Ret; cbn; split_post. 
      intros l' [MONO ALIAS]; cbn*.
      vstep; reflexivity.
    - (* NDiv *)
      cbn* in *; simp; try_abs.
      hvred.

      specialize (IHnexp1 _ _ σ memH _ _ g l memV Heqs).
      forward IHnexp1.
      { split; auto.
        solve_fresh.
      }
      forward IHnexp1; eauto.
     
      (* e1 *)
      eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp1].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as ((PRE1 & PREF1) & (EXPR1 & <- & <- & <- & MONO1)). 
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
      destruct PRE0 as ((PRE2 & PREF2) & (EXPR2 & <- & <- & <- & MONO2)).
      cbn in *.

      (* division *)
      simp; try_abs.
      hvred.

      Set Nested Proofs Allowed.
      Lemma sub_local_no_aliasing_Γ :
        forall σ s1 s2 l1 l2 g,
        sub_local_no_aliasing σ s1 l1 l2 g ->
        Γ s2 ≡ Γ s1 ->
        sub_local_no_aliasing σ s2 l1 l2 g.
      Proof.
        intros σ s1 s2 l1 l2 g [L1L2 SUB] GAMMA.
        unfold sub_local_no_aliasing in *.
        rewrite GAMMA.
        auto.
      Qed.

      Lemma genNExpr_context :
        forall nexp s1 s2 e c,
          genNExpr nexp s1 ≡ inr (s2, (e,c)) ->
          Γ s1 ≡ Γ s2.
      Proof.
        induction nexp;
          intros s1 s2 e c GEN;
          cbn in GEN; simp;
            repeat
              match goal with
              | H: ErrorWithState.option2errS _ (nth_error (Γ ?s1) ?n) ?s1 ≡ inr (?s2, _) |- _ =>
                destruct (nth_error (Γ s1) n); inversion H; subst
              | H: incLocal ?s1 ≡ inr (?s2, _) |- _ =>
                rewrite incLocal_unfold in H; cbn in H; inversion H; cbn; auto
              | IH: ∀ (s1 s2 : IRState) (e : exp typ) (c : code typ), genNExpr ?nexp s1 ≡ inr (s2, (e, c)) → Γ s1 ≡ Γ s2,
          GEN: genNExpr ?nexp _ ≡ inr _ |- _ =>
        rewrite (IH _ _ _ _ GEN)
        end; auto.
      Qed.


      epose proof (genNExpr_context _ _ Heqs0) as GAMMA.
      epose proof (sub_local_no_aliasing_Γ _ MONO2 GAMMA) as SLNA.

      specialize (EXPR1 _ SLNA).
      assert (sub_local_no_aliasing σ i0 l1 l1 g) as L1L1 by solve_sub_local_no_aliasing; specialize (EXPR2 _ L1L1). 
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

      apply eutt_Ret; cbn; split_post.
      intros ? [MONO ALIAS]; cbn.
      vstep; solve_lu; reflexivity.

      { eapply sub_local_no_aliasing_add_non_ptr'.
        - solve_alist_fresh.
        - eapply state_invariant_no_llvm_ptr_aliasing; solve_state_invariant.
        - solve_no_local_global_alias.
        - assert (Γ s2 ≡ Γ i0).
          eauto with helix_context.
          eapply sub_local_no_aliasing_Γ; eauto.
          assert (Γ i0 ≡ Γ i).
          eauto with helix_context.
          eapply sub_local_no_aliasing_Γ; eauto.
          solve_sub_local_no_aliasing.
      }

  first [ solve [eapply state_invariant_sub_local_no_aliasing_refl; solve_state_invariant]
        | eapply sub_local_no_aliasing_add_non_ptr';
          [ solve_alist_fresh
          | eapply state_invariant_no_llvm_ptr_aliasing; solve_state_invariant
          | solve_no_local_global_alias
          | solve_sub_local_no_aliasing
          ]
        | solve [eapply sub_local_no_aliasing_transitive; eauto]].
      
      solve_sub_local_no_aliasing.
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
      destruct PRE0 as ((PRE1 & PREF1) & (EXPR1 & <- & <- & <- & MONO1)). 
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
      destruct PRE0 as ((PRE2 & PREF2) & (EXPR2 & <- & <- & <- & MONO2)).
      cbn; hvred.
      break_match_goal; try_abs...
      hvred.
      
      vstep.
      (* Operator evaluation *)
      {
        vstep; cbn; eauto; try reflexivity.
        cbn; break_inner_match_goal; try reflexivity.

        (* Division by 0 *)
        exfalso.
        apply Z.eqb_eq in Heqb.
        exfalso. apply n.
        rewrite <- Int64.unsigned_zero in Heqb.
        unfold MInt64asNT.NTypeZero.
        apply unsigned_is_zero; auto.
      }

      apply eutt_Ret; cbn; split_post.
      intros ? [MONO ALIAS]; cbn.
      vstep; solve_lu; reflexivity.
  
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
     destruct PRE0 as ((PRE1 & PREF1) & (EXPR1 & <- & <- & <- & MONO1)). 
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
     destruct PRE0 as ((PRE2 & PREF2) & (EXPR2 & <- & <- & <- & MONO2)).
     cbn; hvred.

     vstep.
     vstep; cbn; try (eapply EXPR2 || eapply EXPR1); eauto; reflexivity.

     apply eutt_Ret; cbn; split_post.
     intros ? [MONO ALIAS]; cbn.
     vstep; solve_lu; reflexivity.
  
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
     destruct PRE0 as ((PRE1 & PREF1) & (EXPR1 & <- & <- & <- & MONO1)). 
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
     destruct PRE0 as ((PRE2 & PREF2) & (EXPR2 & <- & <- & <- & MONO2)).
     cbn; hvred.

     vstep.
     vstep; cbn; try (eapply EXPR2 || eapply EXPR1); eauto; reflexivity.

     apply eutt_Ret; cbn; split_post.
     intros ? [MONO ALIAS]; cbn.
     vstep; solve_lu; reflexivity.
  
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
     destruct PRE0 as ((PRE1 & PREF1) & (EXPR1 & <- & <- & <- & MONO1)). 
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
     destruct PRE0 as ((PRE2 & PREF2) & (EXPR2 & <- & <- & <- & MONO2)).
     cbn; hvred.

     vstep.
     (* Operator evaluation *)
     {
        vstep; cbn; try (eapply EXPR2 || eapply EXPR1); eauto; try reflexivity.
        cbn.
        break_inner_match; reflexivity.
      }

     apply eutt_Ret; cbn; split_post.
     intros ? [MONO ALIAS]; cbn.
     vstep; solve_lu; reflexivity.
   - (* NMin *)
      (* Non-implemented by the compiler *)
      inversion COMPILE.
    - (* NMax *)
      (* Non-implemented by the compiler *)
      inversion COMPILE.
  Qed.

End NExpr.

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
    (state_invariant_pre σ s1 s2) memH (memV, (l, g)) -> (* The main state invariant is initially true *)
    no_failure (interp_helix (E := E_cfg) (denoteNExpr σ nexp) memH) -> (* Source semantics defined *)
    eutt (succ_cfg
            (lift_Rel_cfg (state_invariant_post σ s1 s2 l) ⩕
                          genNExpr_exp_correct σ s2 e ⩕
                          ext_local_no_aliasing memH (memV,(l,g)))
         )
         (interp_helix (denoteNExpr σ nexp) memH)
         (interp_cfg (denote_code (convert_typ [] c)) g l memV).
Proof.
  intros.
  eapply eutt_mon; cycle -1.
  eapply genNExpr_correct_ind; eauto.
  intros [(? & ?) |] (? & ? & ? & []) INV; [destruct INV as ((SI & ?) & EXP & ?) | inv INV].
  cbn in *.
  specialize (EXP l0).
  forward EXP; [solve_sub_local_no_aliasing |].
  split; auto.
  split; auto.
  split; auto.
Qed.

Opaque incBlockNamed.
Opaque incVoid.
Opaque incLocal.

Lemma state_invariant_genNExpr :
  ∀ (n : NExpr) (σ : evalContext) (s s' : IRState) (ec : exp typ * code typ) (memH : memoryH) (stV : config_cfg),
    genNExpr n s ≡ inr (s', ec) → state_invariant σ s memH stV → state_invariant σ s' memH stV.
Proof.
  induction n;
    intros σ s s' ec memH stV GEN SINV;
    cbn in GEN; simp;
      repeat
        match goal with
        | H: ErrorWithState.option2errS _ (nth_error (Γ ?s1) ?n) ?s1 ≡ inr (?s2, _) |- _ =>
          destruct (nth_error (Γ s1) n) eqn:FIND; inversion H; subst
        end;
      auto; try solve_state_invariant.
Qed.

Hint Extern 2 (state_invariant _ _ _ _) => eapply state_invariant_genNExpr; [eassumption | solve_state_invariant] : SolveStateInv.
