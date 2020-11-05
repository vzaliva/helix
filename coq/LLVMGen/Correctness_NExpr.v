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
  Opaque incBlockNamed.
  Opaque incVoid.
  Opaque incLocal.

  Ltac split_post := split; [split | split]; [solve_state_invariant | solve_fresh | | cbn; intuition].

  (* Variant precond σ (s1 s2 : IRState) (l_i : local_env): memoryH -> config_cfg -> Prop := *)
  (* | build_precond : forall mH mV l g *)
  (*                     (MINV: memory_invariant σ s1 mH (mV,(l_i,g))) *)
  (*                     (WF: WF_IRState σ s1) *)
  (*                     (FRESH: freshness s1 s2 l_i l), *)
  (*     precond σ s1 s2 l_i mH (mV,(l,g)). *)
 
  (* Variant postcond σ (s1 s2 : IRState) (l_i : local_env): memoryH -> config_cfg -> Prop := *)
  (* | build_postcond : forall mH mV l g *)
  (*                     (MINV: memory_invariant σ s2 mH (mV,(l_i,g))) *)
  (*                     (WF: WF_IRState σ s2) *)
  (*                     (FRESH: freshness s1 s2 l_i l), *)
  (*     postcond σ s1 s2 l_i mH (mV,(l,g)). *)


  Lemma state_invariant_sub_alist:
    forall σ s mH mV l1 l2 g,
      l1 ⊑ l2 ->
      state_invariant σ s mH (mV,(l1,g)) ->
      state_invariant σ s mH (mV,(l2,g)). 
  Proof.
    intros * SUB [MEM WF].
    split; auto.
    cbn; intros * LUH LUV.
    eapply MEM in LUH; eapply LUH in LUV; clear MEM LUH.
    destruct v, x; cbn in *; auto.
    - apply SUB in LUV; auto.
    - apply SUB in LUV; auto.
    - destruct LUV as (? & ? & ? & LU & ?); do 2 eexists; repeat split; eauto.
      apply SUB in LU; auto.
  Qed.

  Lemma freshness_ext : forall s1 s2 l1 l2,
      extends s1 s2 l1 l2 ->
      l1 ⊑ l2.
  Proof.
    intros * FRESH; apply FRESH.
  Qed.

  Lemma state_invariant_memory_invariant :
    forall σ s1 s2 s li mH mV l g,
      state_invariant' σ s1 s2 s li mH (mV,(l,g)) ->
      memory_invariant σ s mH (mV,(li,g)).
  Proof.
    intros * H; inv H; auto.
  Qed.
  Hint Resolve state_invariant_memory_invariant : core.
  Import LidBound.

  Lemma sub_alist_add' :
    forall {K V : Type} {RD:RelDec (@Logic.eq K)} {RDC:RelDec_Correct RD} k v (m1 m2 : alist K V),
      alist_fresh k m1 ->
      m1 ⊑ m2 ->
      m1 ⊑ (alist_add k v m2).
  Proof.
    repeat intro.
    unfold alist_In, alist_fresh in *.
    destruct (rel_dec_p k id).
    - subst; rewrite H in H1; inversion H1.
    - apply In_In_add_ineq; auto.
  Qed.



  Lemma state_invariant_add_fresh' :
    ∀ (σ : evalContext) (s1 s2 : IRState) (id : raw_id) (memH : memoryH) (memV : memoryV) 
      (li l : local_env) (g : global_env) (v : uvalue),
      incLocal s1 ≡ inr (s2, id)
      → state_invariant' σ s1 s2 s1 li memH (memV, (l, g))
      → state_invariant' σ s1 s2 s2 li memH (memV, (alist_add id v l, g)).
  Proof.
    intros * INC INV; inv INV.
    constructor.
    - red; intros * LUH LUV.
      erewrite incLocal_Γ in LUV; eauto.
      generalize LUV; intros INLG;
        eapply MINV in INLG; eauto.
    - unfold WF_IRState; erewrite incLocal_Γ; eauto; apply WF.
    - destruct EXT as [EXT DOM].
      split.
      + apply sub_alist_add'; auto.
        eapply is_fresh_alist_fresh; eauto.
      + intros * IN NIN.
        destruct (id ?[ Logic.eq ] id0) eqn:EQ.
        * rewrite rel_dec_correct in EQ; subst; auto using lid_bound_between_incLocal.
        * apply neg_rel_dec_correct in EQ.
          apply In_add_In_ineq in IN; eauto.
    - solve_fresh.
  Qed.

  Variant state_invariant'' (σ : evalContext) (s1 s2 s : IRState) (li: local_env): memoryH -> config_cfg -> Prop :=
  | mk_state_invariant' : forall mH mV l g
                            (MINV : memory_invariant σ s mH (mV, (li, g)))
                            (WF   : WF_IRState σ s)
                            (EXT  : li ⊑ l)
                            (FRESH: is_fresh s1 s2 li),
      state_invariant'' σ s1 s2 s li mH (mV,(l,g)).


  Lemma state_invariant_add_fresh'' :
    ∀ (σ : evalContext) (s1 s2 : IRState) (id : raw_id) (memH : memoryH) (memV : memoryV) 
      (li l : local_env) (g : global_env) (v : uvalue),
      incLocal s1 ≡ inr (s2, id)
      → state_invariant'' σ s1 s2 s1 li memH (memV, (l, g))
      → state_invariant'' σ s1 s2 s2 li memH (memV, (alist_add id v l, g)).
  Proof.
    intros * INC INV; inv INV.
    constructor.
    - red; intros * LUH LUV.
      erewrite incLocal_Γ in LUV; eauto.
      generalize LUV; intros INLG;
        eapply MINV in INLG; eauto.
    - unfold WF_IRState; erewrite incLocal_Γ; eauto; apply WF.
    - apply sub_alist_add'; auto.
      eapply is_fresh_alist_fresh; eauto.
    - solve_fresh.
  Qed.

  Lemma state_invariant_memory_invariant' :
    forall σ s1 s2 s li mH mV l g,
      state_invariant'' σ s1 s2 s li mH (mV,(l,g)) ->
      memory_invariant σ s mH (mV,(li,g)).
  Proof.
    intros * H; inv H; auto.
  Qed.
  Hint Resolve state_invariant_memory_invariant' : core.

  Lemma state_invariant_sub_alist' :
    forall σ s1 s2 s li mH mV l g,
      state_invariant'' σ s1 s2 s li mH (mV,(l,g)) ->
      li ⊑ l.
  Proof.
    intros * H; inv H; auto.
  Qed.
  Hint Resolve state_invariant_sub_alist' : core.

  Definition ext_local {R S} (e : exp typ) : config_helix -> config_cfg -> Rel_cfg_T R S :=
    fun mh '(mi,(li,gi)) '(mh',_) '(m,(l,(g,_))) =>
      mh ≡ mh' /\ mi ≡ m /\ gi ≡ g.
      (* /\ (forall id, e ≡ EXP_Ident (ID_Local id) -> alist_find id l ≡ alist_find id li). *)
      (* (s1 ≡ s2 \/ exists s id, incLocal s ≡ inr (s2,id) /\ alist_find id l ≡ alist_find id li). *)
      (* (forall id v, *)
      (*   alist_In id l v -> *)
      (*   ~ alist_In id li v -> *)
      (*   lid_bound_between s1 s2 id). *)

  Definition genNExpr_exp_correct (e: exp typ) (* (li : local_env) *)
  : Rel_cfg_T DynamicValues.int64 unit :=
    fun '(x,i) '(memV,(l,(g,v))) =>
      forall l',
        (* li ⊑ l' -> *)
        (forall id, e ≡ EXP_Ident (ID_Local id) -> alist_find id l' ≡ alist_find id l)
        ->
        interp_cfg
          (translate exp_E_to_instr_E (denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] e)))
          g l' memV ≈
          Ret (memV,(l',(g,UVALUE_I64 i))).

  Lemma incLocal_ineq: forall s1 s2 r,
      incLocal s1 ≡ inr (s2,r) -> s1 <> s2.
  Proof.
    intros.
    Transparent incLocal.
    cbn in *; inv H.
    Opaque incLocal.
    destruct s1; cbn.
    intros EQ; inv EQ.
    eapply Nat.neq_succ_diag_r; eauto.
  Qed.

  Lemma state_invariant_sub_alist_alist_add: forall s1 s2 s r σ li memH memV l g v,
      incLocal s1 ≡ inr (s2,r) ->
      state_invariant'' σ s1 s2 s li memH (memV, (l,g)) ->
      li ⊑ alist_add r v l.
  Proof.
    intros * INC PRE; inv PRE.
    apply sub_alist_add'; auto.
    eapply is_fresh_alist_fresh; eauto.
  Qed.

  Definition local_scoped_modif (s1 s2 : IRState) (l1 : local_env) : local_env -> Prop :=
    fun l2 =>
      forall id,
        alist_find id l2 <> alist_find id l1 ->
        lid_bound_between s1 s2 id.

  (**
     We package the local specific invariants. Additionally to the evaluation of the resulting expression,
     we also state that evaluating the code preserves most of the state, except for the local state being
     allowed to be extended with fresh bindings.
   *)
  Record genNExpr_post
         (e : exp typ)
         (li : local_env)
         s1 s2
         (mi : memoryH) (sti : config_cfg)
         (mf : memoryH * DynamicValues.int64) (stf : config_cfg_T unit)
    : Prop :=
    {
    exp_correct' : genNExpr_exp_correct e (* li *) mf stf;
    almost_pure : ext_local e mi sti mf stf; 
    extends : local_scoped_modif s1 s2 (fst (snd sti)) (fst (snd stf));
    exp_in_scope : forall id, e ≡ EXP_Ident (ID_Local id) ->
                         ((exists v, alist_In id li v) \/ (lid_bound_between s1 s2 id /\ s1 << s2));
    ext_li : li ⊑ (fst (snd stf))
    }.

  Set Nested Proofs Allowed.
  Lemma local_scoped_modif_refl: forall s1 s2 l, local_scoped_modif s1 s2 l l.
  Admitted.
  Hint Resolve local_scoped_modif_refl: core.

  Lemma local_scoped_modif_add: forall s1 s2 l r v,
      lid_bound_between s1 s2 r ->   
      local_scoped_modif s1 s2 l (alist_add r v l).
  Admitted.

  Lemma sub_alist_alist_find_in :
    forall (l2 l1 : local_env) id v,
      alist_In id l1 v ->
      l1 ⊑ l2 ->
      l2 @ id ≡ l1 @ id.
  Admitted.

  Lemma alist_find_eq_dec : 
    forall {K V : Type} {RD:RelDec (@Logic.eq K)} {RDC:RelDec_Correct RD}
      k (m1 m2 : alist K V),
      {m2 @ k ≡ m1 @ k} + {m2 @ k <> m1 @ k}.
  Admitted.

  Lemma local_scoped_modif_out:
    forall (l1 l2 : local_env) id s1 s2 s3,
      s1 << s2 ->
      lid_bound_between s1 s2 id ->
      local_scoped_modif s2 s3 l1 l2 ->
      l2 @ id ≡ l1 @ id.
  Proof.
    intros * LT BOUND SCOPE.
    red in SCOPE.
    edestruct @alist_find_eq_dec as [EQ | NEQ]; [| eassumption |]; [typeclasses eauto |].
    exfalso; apply SCOPE in NEQ; clear SCOPE.
    (* should be true *)
  Admitted.


  Lemma genNExpr_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *)   (nexp: NExpr) (σ: evalContext) (memH: memoryH) 
      (* Vellvm bits *)   (e: exp typ) (c: code typ) (g : global_env) (li l : local_env) (memV : memoryV),

      genNExpr nexp s1 ≡ inr (s2, (e, c))      -> (* Compilation succeeds *)
      (state_invariant'' σ s1 s2 s1 li) memH (memV, (l, g)) -> (* The main state invariant is initially true *)
      no_failure (interp_helix (E := E_cfg) (denoteNExpr σ nexp) memH) -> (* Source semantics defined *)
      eutt (succ_cfg (lift_Rel_cfg (state_invariant'' σ s1 s2 s2 li) ⩕
                     genNExpr_post e li s1 s2 memH (mk_config_cfg memV l g)))
           (interp_helix (denoteNExpr σ nexp) memH)
           (interp_cfg (denote_code (convert_typ [] c)) g l memV).
  Proof.
    intros s1 s2 nexp; revert s1 s2; induction nexp; intros * COMPILE PRE NOFAIL.
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
        * intros l' VAR; cbn*.
          inv PRE.
          vstep.
          cbn.
          rewrite VAR; auto.
          eapply memory_invariant_LLU; eauto.
          reflexivity.
        * intros * EQ; inv EQ.
          left.
          eexists.
          eapply memory_invariant_LLU; eauto.

      + (* The variable maps to a pointer *)
        unfold denoteNExpr in *; cbn* in *; simp; try_abs.
        break_inner_match_goal; try_abs.
        2:inv PRE; try_abs.
 
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
        * apply state_invariant_add_fresh''; auto.
        * intros l' VAR; cbn*.
          vstep; [ | reflexivity].
          cbn; erewrite VAR; eauto.
          rewrite eq_dec_eq; reflexivity.
        * apply local_scoped_modif_add.
          auto using lid_bound_between_incLocal.
        * intros * EQ; inv EQ; right.
          split; [auto using lid_bound_between_incLocal | solve_local_count].
        * eapply state_invariant_sub_alist_alist_add; eauto.
        (* eapply incLocal_ineq; eauto. *)

        (* * intuition. *)
        (*   inv H. *)
        (*   rewrite eq_dec_eq. *)

        (*   rename r into foo. *)
        (*   right; do 2 eexists; split; eauto. *)
        (*   rewrite eq_dec_eq. rename r into foo. *)
        (*   symmetry. *)

        (*   eauto. *)
          (* destruct (id0 ?[ Logic.eq ] r) eqn:EQ. *)
          (* rewrite rel_dec_correct in EQ; subst; auto using lid_bound_between_incLocal. *)
          (* apply neg_rel_dec_correct in EQ. *)
          (* apply In_add_In_ineq in H; intuition. *)

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

      specialize (IHnexp1 _ _ σ memH _ _ g li l memV Heqs).
      forward IHnexp1.
      { inv PRE; split; auto.
        solve_fresh.
      }
      forward IHnexp1; eauto.
     
      (* e1 *)
      eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp1].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (PRE1 & [EXP1 EXT1 SCOPE1 VAR1 EXTI1]).
      cbn* in *; inv_eqs.
      (* rename H into VAR1. *)
      hvred.

      (* e2 *)
      specialize (IHnexp2 _ _ σ memH _ _ g li l0 memV Heqs0).
      forward IHnexp2.
      {
        clean_goal.
        inv PRE; inv PRE1.
        constructor; auto.
        eapply is_fresh_shrink with (1 := FRESH). 
        solve_local_count.
        solve_local_count.
      }
      forward IHnexp2; eauto.

      eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp2].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (PRE2 & [EXP2 EXT2 SCOPE2 VAR2 EXTI2]).
      cbn* in *; inv_eqs.
      (* rename H into VAR2. *)

      (* division *)
      simp; try_abs.
      hvred.

      specialize (EXP1 l1) .
      specialize (EXP2 l1) .
      forward EXP2; [intros; reflexivity |].
      forward EXP1.
      {
        clear EXP1 EXP2.
        clean_goal.
        intros * EQE.
        apply VAR1 in EQE.
        destruct EQE as [[?v IN] | [BOUND LT]].
        erewrite sub_alist_alist_find_in; [| eauto | eauto].
        erewrite (@sub_alist_alist_find_in l0); [| eauto | eauto]; reflexivity.
        clear n Heqd NOFAIL VAR1 VAR2.
        eapply local_scoped_modif_out; eauto.
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
      + admit.
      + intros * VAREQ.
        specialize (VAREQ r eq_refl); rewrite eq_dec_eq in VAREQ.
        vstep; eauto; reflexivity.
      + admit.
      + admit.
      + admit.
        (* intros ? MONO; cbn. *)
        (* vstep; solve_lu; reflexivity. *)
        (* etransitivity; eauto. *)
        (* etransitivity; eauto. *)
        (* apply sub_alist_add. *)
        (* eapply freshness_pre_alist_fresh; eauto. *)
        (* solve_fresh. *)
        
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

      apply eutt_Ret; cbn; split_post.
      intros ? MONO; cbn.
      vstep; solve_lu; reflexivity.
      etransitivity; eauto.
      etransitivity; eauto.
      apply sub_alist_add.
      eapply freshness_pre_alist_fresh; eauto.
      solve_fresh.
  
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
     intros ? MONO; cbn.
     vstep; solve_lu; reflexivity.
     etransitivity; eauto.
     etransitivity; eauto.
     apply sub_alist_add.
     eapply freshness_pre_alist_fresh; eauto.
     solve_fresh.
  
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
     intros ? MONO; cbn.
     vstep; solve_lu; reflexivity.
     etransitivity; eauto.
     etransitivity; eauto.
     apply sub_alist_add.
     eapply freshness_pre_alist_fresh; eauto.
     solve_fresh.
  
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
     intros ? MONO; cbn.
     vstep; solve_lu; reflexivity.
     etransitivity; eauto.
     etransitivity; eauto.
     apply sub_alist_add.
     eapply freshness_pre_alist_fresh; eauto.
     solve_fresh.
  
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
                          ext_local memH (memV,(l,g)))
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
  forward EXP; [reflexivity |].
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
