Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import LibHyps.LibHyps.
Import ProofNotations.
Open Scope Z.
Open Scope list.

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
     The corresponding compiling function is [ genNexpr].

     Helix side:
     * nexp: NExpr
     * σ: evalContext
     * s: IRState

 *)

Section NExpr.
  
  (** At the top level, the correctness of genNExpr is expressed as the denotation of the operator being equivalent
      to the bind of denoting the code followed by denoting the expression.
      However this is not inductively stable, we only want to plug the expression at the top level.
      We therefore instead carry the fact about the denotation of the expression in the invariant. (Is there another clever way?)
      TODO: how to make this (much) less ugly?
   *)
  Definition genNExpr_exp_correct_ind (* (σ : evalContext) (nexp : NExpr) *) (e: exp typ)
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
         (σ : evalContext)
         (nexp : NExpr)
         (e : exp typ)
         (mi : memoryH) (sti : config_cfg)
         (mf : memoryH * DynamicValues.int64) (stf : config_cfg_T unit)
    : Prop :=
    {
    exp_correct : genNExpr_exp_correct_ind (* σ nexp *) e mf stf;
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

  Ltac check_state_invariant :=
    match goal with
      |- state_invariant _ _ _ (_, (alist_add _ _ _, _)) =>
      eapply state_invariant_add_fresh; [now eauto | (eassumption || check_state_invariant)]
    end.

  Lemma state_invariant_alist_fresh:
    forall σ s s' memH memV l g id,
      state_invariant σ s memH (memV, (l,g)) ->
      incLocal s ≡ inr (s',id) ->
      alist_fresh id l.
  Proof.
    intros * [] LOC.
    apply concrete_fresh_fresh in incLocal_is_fresh.
    eapply incLocal_is_fresh; eauto.
  Qed.

  Ltac solve_alist_fresh :=
    (reflexivity ||
     eapply state_invariant_alist_fresh; now eauto).

  Ltac solve_sub_alist :=
    (reflexivity ||
     apply sub_alist_add; solve_alist_fresh).

  Lemma genNExpr_correct_ind :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *)   (nexp: NExpr) (σ: evalContext) (memH: memoryH) 
      (* Vellvm bits *)   (e: exp typ) (c: code typ) (g : global_env) (l : local_env) (memV : memoryV),

      genNExpr nexp s1 ≡ inr (s2, (e, c))      -> (* Compilation succeeds *)
      state_invariant σ s1 memH (memV, (l, g)) -> (* The main state invariant is initially true *)
      no_failure (interp_helix (E := E_cfg) (denoteNExpr σ nexp) memH) -> (* Source semantics defined *)
      eutt (succ_cfg (lift_Rel_cfg (state_invariant σ s2) ⩕
                      genNExpr_rel_ind σ nexp e memH (mk_config_cfg memV l g)))
           (interp_helix (denoteNExpr σ nexp) memH)
           (interp_cfg (denote_code (convert_typ [] c)) g l memV).
  Proof with (rauto).

    intros s1 s2 nexp; revert s1 s2; induction nexp; intros * COMPILE PRE NOFAIL.
    - (* Variable case *)
      (* Reducing the compilation *)
      cbn* in COMPILE; simp.

      + (* The variable maps to an integer in the IRState *)
        unfold denoteNExpr in *; cbn* in *...
        simp; try_abs.

        (* The identifier has to be a local one *)
        destruct i0; try_abs... 

        (* We establish the postcondition *)
        apply eutt_Ret; split; [| split]; try now eauto.
        intros l' MONO; cbn*...
        2:solve_lu.
        reflexivity.

      + (* The variable maps to a pointer *)
        unfold denoteNExpr in *; cbn* in *.
        simp; try_abs.
        break_inner_match_goal; try_abs.
        cbn...

        (* YZ : TODO load tactic?
           at least reorder the goals afters the rewrite denote_instr_load
         *)
        edestruct memory_invariant_GLU as (ptr & LU & READ); eauto.
        rewrite typ_to_dtyp_equation in READ.
        rewrite denote_instr_load; eauto; cycle 1.

        {
          cbn...
          2 : eauto. 
          reflexivity.
        }

        apply eutt_Ret; split; [| split].
        -- cbn; check_state_invariant.

        -- intros l' MONO; cbn*...
           reflexivity.
           eapply MONO, In_add_eq.
        -- repeat (split; auto); solve_sub_alist.

    - (* Constant *)
      cbn* in COMPILE; simp.
      unfold denoteNExpr in *; cbn*.
      rewrite denote_code_nil; cbn...

      apply eutt_Ret; split; [| split]; try now eauto.
      intros l' MONO; cbn*...
      rewrite repr_intval...
      reflexivity.

    - (* NDiv *)
      cbn* in *; simp; try_abs.
      cbn...
      (* TODO YZ: gets some super "specialize" tactics that do not require to provide variables *)
      specialize (IHnexp1 _ _ _ _ _ _ _ _ _ Heqs PRE). 
      forward IHnexp1; eauto. 
      simp.
      onAllHyps move_up_types.

      rewrite convert_typ_app, denote_code_app.
      rauto:R.
      eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp1].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      cbn in *.
      destruct PRE0 as (PREI & (EXPRI & <- & <- & <- & MONOI)).

      specialize (IHnexp2 _ _ _ _ _ _ _ _ _ Heqs0 PREI).
      forward IHnexp2; eauto. 
      onAllHyps move_up_types.
      rewrite convert_typ_app, denote_code_app.
      rauto.
      eapply eutt_clo_bind_returns ; [eassumption | clear IHnexp2].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      cbn in *.
      destruct PRE0 as (PREF & (EXPRF & <- & <- & <- & MONOF)).
      simp; try_abs.

      rewrite denote_code_singleton; cbn...

      specialize (EXPRI _ MONOF) .
      assert (l1 ⊑ l1) as L1L1 by reflexivity; specialize (EXPRF _ L1L1). 
      (* rewrite Heqs2 in EVAL_vH. *)
      (* injection EVAL_vH; intros; subst. *)
      cbn in *.
      (* rewrite Heqs4 in EVAL_vH0. *)
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
      cbn...
      apply eutt_Ret; split; [| split].
      cbn. eapply state_invariant_add_fresh; eauto; reflexivity.
      {
        cbn; intros ? MONO...
        apply eutt_Ret.
        do 3 f_equal.
        apply MONO, In_add_eq.
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

    - (* NMod *)
      cbn* in *; simp; try_abs.
      cbn...
      (* TODO YZ: gets some super "specialize" tactics that do not require to provide variables *)
      specialize (IHnexp1 _ _ _ _ _ _ _ _ _ Heqs PRE). 
      forward IHnexp1; eauto.
      onAllHyps move_up_types.

      rewrite convert_typ_app, denote_code_app.
      rauto:R.
      eapply eutt_clo_bind_returns; [eassumption | clear IHnexp1].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      cbn in *.
      destruct PRE0 as (PREI & (EXPRI & <- & <- & <- & MONOI)).

      specialize (IHnexp2 _ _ _ _ _ _ _ _ _ Heqs0 PREI).
      forward IHnexp2; eauto. 
      rewrite convert_typ_app, denote_code_app...
      eapply eutt_clo_bind_returns; [eassumption | clear IHnexp2].
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      cbn in *.
      destruct PRE0 as (PREF & (EXPRF & <- & <- & <- & MONOF)). 
      rewrite denote_code_singleton; cbn...
      break_match_goal; try_abs...

      rewrite denote_instr_op.

      (* Operator evaluation *)
      2: {
        cbn in EXPRF.
        eapply denote_ibinop_concrete; cbn; eauto; try reflexivity.
        3: eapply EXPRF; reflexivity.
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
 
      apply eutt_Ret; split; [| split]; try now eauto.
      -- cbn. eapply state_invariant_add_fresh; eauto; reflexivity.
      -- cbn; intros ? MONO...
         2: apply MONO, In_add_eq.
         reflexivity.
      -- apply ext_local_subalist.
         etransitivity; eauto.
         etransitivity; eauto.
         apply sub_alist_add.
         apply incLocal_is_fresh,concrete_fresh_fresh in PREF.
         eapply PREF.
         eauto.

   - (* NAdd *)

     cbn* in *; simp; try_abs.

     (* TODO YZ: gets some super "specialize" tactics that do not require to provide variables *)
     specialize (IHnexp1 _ _ _ _ _ _ _ _ _ Heqs PRE). 
     forward IHnexp1; eauto. 
     rewrite convert_typ_app, denote_code_app...
     eapply eutt_clo_bind_returns; [eassumption | clear IHnexp1].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PREI & (EXPRI & <- & <- & <- & MONOI)). 

     specialize (IHnexp2 _ _ _ _ _ _ _ _ _ Heqs0 PREI). 
     forward IHnexp2; eauto. 
     rewrite convert_typ_app, denote_code_app...
     eapply eutt_clo_bind_returns; [eassumption | clear IHnexp2].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PREF & (EXPRF & <- & <- & <- & MONOF)). 

     cbn...
     rewrite denote_instr_op.
     2: eapply denote_ibinop_concrete; cbn; try (eapply EXPRF || eapply EXPRI); eauto; reflexivity.
     cbn...

     apply eutt_Ret; split; [| split].
     cbn; eapply state_invariant_add_fresh; eauto.
     {
       cbn; intros ? MONO...
       2:apply MONO, In_add_eq.
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
     
   - (* NMinus *)

     cbn* in *; simp; try_abs.

     (* TODO YZ: gets some super "specialize" tactics that do not require to provide variables *)
     specialize (IHnexp1 _ _ _ _ _ _ _ _ _ Heqs PRE). 
     forward IHnexp1; eauto. 
     rewrite convert_typ_app, denote_code_app...
     eapply eutt_clo_bind_returns; [eassumption | clear IHnexp1].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PREI & (EXPRI & <- & <- & <- & MONOI)). 

     specialize (IHnexp2 _ _ _ _ _ _ _ _ _ Heqs0 PREI). 
     forward IHnexp2; eauto. 
     rewrite convert_typ_app, denote_code_app...
     eapply eutt_clo_bind_returns; [eassumption | clear IHnexp2].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PREF & (EXPRF & <- & <- & <- & MONOF)). 

     cbn...
     rewrite denote_instr_op.
     2: eapply denote_ibinop_concrete; cbn; try (eapply EXPRF || eapply EXPRI); eauto; reflexivity.
     cbn...

     apply eutt_Ret; split; [| split].
     cbn; eapply state_invariant_add_fresh; eauto.
     {
       cbn; intros ? MONO...
       2:apply MONO, In_add_eq.
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

    - (* NMult *)
     
     cbn* in *; simp; try_abs.

     (* TODO YZ: gets some super "specialize" tactics that do not require to provide variables *)
     specialize (IHnexp1 _ _ _ _ _ _ _ _ _ Heqs PRE). 
     forward IHnexp1; eauto. 
     rewrite convert_typ_app, denote_code_app...
     eapply eutt_clo_bind_returns; [eassumption | clear IHnexp1].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PREI & (EXPRI & <- & <- & <- & MONOI)). 

     specialize (IHnexp2 _ _ _ _ _ _ _ _ _ Heqs0 PREI). 
     forward IHnexp2; eauto. 
     rewrite convert_typ_app, denote_code_app...
     eapply eutt_clo_bind_returns; [eassumption | clear IHnexp2].
     introR; destruct_unit.
     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
     destruct PRE0 as (PREF & (EXPRF & <- & <- & <- & MONOF)). 

     cbn...
     rewrite denote_instr_op.
      (* Operator evaluation *)
      2: {
        eapply denote_ibinop_concrete; cbn; try (eapply EXPRF || eapply EXPRI); eauto; try reflexivity.
        cbn.
        break_inner_match; reflexivity.
      }
      cbn...

      apply eutt_Ret; split; [| split].
      cbn; eapply state_invariant_add_fresh; eauto.
      {
        cbn; intros ? MONO...
        2:apply MONO, In_add_eq.
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

    - (* NMin *)
      (* Non-implemented by the compiler *)
      inversion COMPILE.
    - (* NMax *)
      (* Non-implemented by the compiler *)
      inversion COMPILE.
  Qed.

  (* CLEAN UP *)
  (*
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

   *)

End NExpr.

(* CLEAN UP *)
(*
Ltac genNExpr_rel_subst LL :=
  match goal with
  | NEXP : genNExpr_rel ?σ ?n ?e ?memH (mk_config_cfg ?memV ?l ?g) (?memH', ?n') (?memV', (?l', (?g', ()))) |- _ =>
    let H := fresh in
    pose proof genNExpr_memH NEXP as H; subst memH';
    pose proof genNExpr_memV NEXP as H; subst memV';
    pose proof genNExpr_g NEXP as H; subst g';
    pose proof genNExpr_l NEXP as LL
  end.
 *)

(*
Definition genNExpr_exp_correct' (σ : evalContext) (s : IRState) (nexp : NExpr) (e: exp typ)
  : Rel_cfg_T DynamicValues.int64 unit :=
  fun '(memH,i) '(memV,(l,(g,v))) => 
            eutt (succ_cfg (lift_Rel_cfg (state_invariant σ s)))
                 (interp_helix (denoteNExpr σ nexp) memH)
                 (interp_cfg
                    (translate exp_E_to_instr_E (denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] e)))
                    g l memV). 

  Lemma genNExpr_correct' :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *)   (nexp: NExpr) (σ: evalContext) (memH: memoryH) 
      (* Vellvm bits *)   (e: exp typ) (c: code typ) (g : global_env) (l : local_env) (memV : memoryV),

      genNExpr nexp s1 ≡ inr (s2, (e, c))      -> (* Compilation succeeds *)
      state_invariant σ s1 memH (memV, (l, g)) -> (* The main state invariant is initially true *)
      no_failure (interp_helix (E := E_cfg) (denoteNExpr σ nexp) memH) -> (* Source semantics defined *)
      eutt (succ_cfg (genNExpr_exp_correct' σ s2 nexp e))
           (interp_helix (denoteNExpr σ nexp) memH)
           (interp_cfg (denote_code (convert_typ [] c)) g l memV).
  Proof.
    intros.
    eapply eqit_mon; [eauto | eauto | ..].
    2: eapply genNExpr_correct; eauto.
    intros [(? & ?) |] (? & ? & ? & ?) INV; [destruct INV as (SI & EXP & ?) | inv INV].
    destruct u; cbn in *.
    destruct EXP as (EXP & MONO).
    cbn in *.
    specialize (EXP l0).
    forward EXP; [reflexivity |].
    destruct EXP as (EXP & EQ).
    unfold denoteNExpr; rewrite EQ; cbn.
    rewrite interp_helix_Ret.
    cbn.
    rewrite <- EXP.
    apply eutt_Ret.
    cbn.
    eauto.
  Qed.

 *)

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
    state_invariant σ s1 memH (memV, (l, g)) -> (* The main state invariant is initially true *)
    no_failure (interp_helix (E := E_cfg) (denoteNExpr σ nexp) memH) -> (* Source semantics defined *)
    eutt (succ_cfg
            (lift_Rel_cfg (state_invariant σ s2) ⩕
                          genNExpr_exp_correct σ s2 e ⩕
                          ext_local memH (memV,(l,g))
         ))
         (interp_helix (denoteNExpr σ nexp) memH)
         (interp_cfg (denote_code (convert_typ [] c)) g l memV).
Proof.
  intros.
  eapply eutt_mon; cycle -1.
  eapply genNExpr_correct_ind; eauto.
  intros [(? & ?) |] (? & ? & ? & []) INV; [destruct INV as (SI & EXP & ?) | inv INV].
  cbn in *.
  cbn in *.
  specialize (EXP l0).
  forward EXP; [reflexivity |].
  split; auto.
  split; auto.
Qed.

