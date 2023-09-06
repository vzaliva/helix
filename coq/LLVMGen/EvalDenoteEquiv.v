Require Export Helix.DSigmaHCOL.DSigmaHCOLITree.
Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Paco.paco.
Import MInt64asNT.

Section Eval_Denote_Equiv.

  Hint Rewrite interp_Mem_bind : itree.
  Hint Rewrite interp_Mem_ret : itree.
  Hint Rewrite @interp_Mem_MemLU : itree.

  Ltac go := unfold denotePExpr, evalIUnCType, denoteIUnCType; autorewrite with itree.

  Ltac inv_sum :=
    match goal with
    | h: inl _ = inl _ |-  _ => inv h
    | h: inr _ = inr _ |-  _ => inv h
    | h: inl _ = inr _ |-  _ => inv h
    | h: inr _ = inl _ |-  _ => inv h
    | h: inl _ ≡ inl _ |-  _ => inv h
    | h: inr _ ≡ inr _ |-  _ => inv h
    | h: inl _ ≡ inr _ |-  _ => inv h
    | h: inr _ ≡ inl _ |-  _ => inv h
    end.

  Ltac inv_option :=
    match goal with
    | h: Some _ = Some _ |-  _ => inv h
    | h: None   = Some _ |-  _ => inv h
    | h: Some _ = None   |-  _ => inv h
    | h: None   = None   |-  _ => inv h
    | h: Some _ ≡ Some _ |-  _ => inv h
    | h: None   ≡ Some _ |-  _ => inv h
    | h: Some _ ≡ None   |-  _ => inv h
    | h: None   ≡ None   |-  _ => inv h
    end.

  Ltac simp' := repeat (inv_sum || inv_option || break_and || break_match_hyp).

  Lemma bind_ret_l_equiv
    (E : Type -> Type)
    (A B : Type)
    (RA : Equiv A)
    (RB : Equiv B)
    (x : itree E A)
    (a : A)
    (k : A -> itree E B)
    (r : itree E B)
    :
    (forall a', RA a' a -> eutt RB (k a') r) -> (* rewrite TO *)
    eutt RA x (Ret a) ->                   (* rewrite WITH *)
    eutt RB (ITree.bind x k) r.            (* current goal *)
  Proof.
    intros T W.

    assert (eutt (fun a1 a2 => RA a1 a /\ a2 ≡ a) x (Ret a)).
    {
      clear - W.
      revert x W.
      pcofix CIH; intros x H.
      punfold H.
      red in H; cbn in H.
      pfold.
      red; cbn.
      dependent induction H.
      - rewrite <- x.
        constructor.
        split; auto.
      - rewrite <- x.
        apply EqTauL; auto.
    }

    match goal with
      |- eutt _ _ ?t =>
        rewrite <- (bind_ret_l a (fun _ => t))
    end.
    eapply eutt_clo_bind.
    apply H.
    intros * [U <-].
    intuition.
  Qed.

  Lemma interp_Mem_MemLU :
    forall str mem m x,
      memory_lookup_err str mem x = inr m ->
      eutt equiv (interp_Mem (trigger (MemLU str x)) mem) (interp_Mem (Ret m) mem).
  Proof.
    intros str mem m x H.
    unfold trigger.
    setoid_rewrite interp_Mem_vis_eqit.
    cbn.
    break_match_goal; simp'.
    cbn; go.
    rewrite tau_eutt.
    cbn.
    apply eutt_Ret.
    now split.
  Qed.

  Lemma Denote_Eval_Equiv_MExpr_eq : forall mem σ e bk size,
      evalMExpr mem σ e ≡ inr (bk,size) ->
      eutt Logic.eq
        (interp_Mem (denoteMExpr σ e) mem)
        (Ret (mem, (bk,size))).
  Proof.
    intros mem σ [] * EVAL; cbn* in *; simp; go; try reflexivity.
    rewrite Heqs; cbn*; go.
    reflexivity.
    cbn*; match_rewrite; reflexivity.
  Qed.

  Lemma Denote_Eval_Equiv_MExpr: forall mem σ e bk size,
      evalMExpr mem σ e = inr (bk,size) ->
      eutt equiv
        (interp_Mem (denoteMExpr σ e) mem)
        (Ret (mem, (bk,size))).
  Proof.
    intros mem σ [] * EVAL.
    - cbn* in *; simp'.
      inv H1; cbn in *.
      go.
      rewrite Heqs.
      cbn.
      go.
      2: eapply memory_lookup_err_inr_Some_eq; eauto.
      apply eutt_Ret.
      split; cbn. reflexivity.
      now split; cbn.
    - cbn in EVAL.
      simp'.
      cbn; go.
      now apply eutt_Ret.
  Qed.

  Ltac ret_bind_l_right v :=
    match goal with
      |- eutt _ _ ?t =>
        rewrite <- (bind_ret_l v (fun _ => t))
    end.

  Definition eq_relation_het {A B} (R S : A -> B -> Prop) :=
    R <2= S /\ S <2= R.

  Lemma eqrel_simpl {A B} (R S : A -> B -> Prop) :
    eq_relation_het R S <->
      (forall a b, R a b <-> S a b).
  Proof.
    unfold eq_relation_het.
    split; intros; intuition.
    all: now apply H.
  Qed.

  Instance eutt_EQ_REL_Proper_het {E} {A B} :
    Proper (eq_relation_het ==> @eutt E A A eq ==> @eutt E B B eq ==> iff) (@eutt E A B).
  Proof.
    repeat red.
    intros; split; intros.
    -  rewrite <- H0. rewrite <- H1.
       clear H0 H1.
       destruct H.
       eapply eqit_mon; eauto.
    - rewrite H0, H1.
      destruct H.
      eapply eqit_mon; eauto.
  Qed.

  Instance eutt_equiv_Proper {E} `{@Equivalence A ea} :
    Proper ((@eutt E A A ea) ==> (@eutt E A A ea) ==> (iff)) (@eutt E A A ea).
  Proof.
    intros x1 x2 EX y1 y2 EY.
    split; intros.
    now rewrite <-EX, <-EY.
    now rewrite EX, EY.
  Qed.

  (* TODO: rename or replace with existing *)
  Definition pointwise_impl {A B : Type} (RA : relation A) (RB : relation B)
    : relation (A -> B) :=
    fun f1 f2 => forall a1 a2, RA a1 a2 -> RB (f1 a1) (f2 a2).

  Instance pointwise_impl_Symmetric
    {A B : Type}
    `{Symmetric A RA}
    `{Symmetric B RB}
    :
    Symmetric (pointwise_impl RA RB).
  Proof.
    repeat red.
    intros.
    intuition.
  Qed.

  Instance pointwise_impl_Transitive
    {A B : Type}
    `{Reflexive A RA}
    `{Transitive B RB}
    :
    Transitive (pointwise_impl RA RB).
  Proof.
    repeat red.
    intros.
    etransitivity.
    eapply H1.
    reflexivity.
    now apply H2.
  Qed.

  (*
    Add Parametric Relation
    (A B : Type)
    (EA : relation A)
    (EB : relation B)
    (RA : @Reflexive A EA)
    (SA : @Symmetric A EA)
    (SB : @Symmetric B EB)
    (TB : @Transitive B EB)
    :
    (A -> B) (@pointwise_impl A B EA EB)
    symmetry proved by (@pointwise_impl_Symmetric A B EA SA EB SB)
    transitivity proved by (@pointwise_impl_Transitive A B EA RA EB TB)
    as pointwise_impl_Param.
   *)

  Instance ITree_bind_equiv_Proper {E} `{ea : relation A} `{eb : relation B} :
    Proper (@eutt E A A ea ==>
              pointwise_impl ea (@eutt E B B eb) ==>
              @eutt E B B eb)
      ITree.bind.
  Proof.
    intros x1 x2 X f1 f2 F.
    eapply eutt_clo_bind; eassumption.
  Qed.

  Definition pointwise_impl' {A B : Type} (RA : relation A) (RB : relation B)
    : relation (A -> B) :=
    fun f1 f2 => f1 ≡ f2 /\ Proper (RA ==> RB) f1.

  Lemma pointwise_impl_eq :
    forall {A B : Type} (RA : relation A) (RB : relation B) f1 f2,
      pointwise_impl' RA RB f1 f2 -> pointwise_impl RA RB f1 f2.
  Proof.
    unfold pointwise_impl', pointwise_impl.
    intros.
    destruct H; subst f2.
    eapply H1.
    assumption.
  Qed.

  Lemma pointwise_impl'_simp :
    forall {A B : Type} (RA : relation A) (RB : relation B) f,
      Proper (RA ==> RB) f ->
      pointwise_impl' RA RB f f.
  Proof.
    red.
    tauto.
  Qed.

  (* TODO : MOVE THIS TO ITREE *)
  Instance eutt_interp_state_eq {E F: Type -> Type} {S : Type} {R}
    (h : E ~> Monads.stateT S (itree F)) :
    Proper (eutt Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp_state E (itree F) S _ _ _ h R).
  Proof.
    repeat intro. subst. revert_until R.
    einit. ecofix CIH. intros.

    rewrite !unfold_interp_state. punfold H0. red in H0.
    induction H0; intros; subst; simpl; pclearbot.
    - eret.
    - etau.
    - ebind. econstructor; [reflexivity|].
      intros; subst.
      etau. ebase.
    - rewrite tau_euttge, unfold_interp_state; eauto.
    - rewrite tau_euttge, unfold_interp_state; eauto.
  Qed.

  Instance NTypeEquiv_Equivalence : Equivalence NTypeEquiv.
  Proof.
    (* REASON: [Fail typeclasses eauto.] *)
    apply NTypeSetoid.
  Qed.

  Definition decide_MemEventT_equiv {T : Type} (e : MemEvent T) : Equiv T :=
    match e with
    | MemLU _ _ => NM_Equiv
    | _ => equiv
    end.

  Instance decide_MemEventT_equiv_Equivalence `{e : MemEvent T} :
    Equivalence (decide_MemEventT_equiv e).
  Proof.
    destruct e; cbn.
    all: typeclasses eauto.
  Qed.

  Instance Mem_handler_Proper {T : Type} :
    forall e,
      Proper (equiv ==>
                eutt (@products.prod_equiv
                        memoryH equiv
                        T (decide_MemEventT_equiv e)))
        (Mem_handler T e).
  Proof.
    intros e m1 m2 M.
    unfold decide_MemEventT_equiv.
    destruct e; cbn.
    -
      pose proof (M id) as MID.
      unfold memory_lookup_err, memory_lookup, trywith.
      repeat break_match;
        try some_none; repeat some_inv;
        try inl_inr; repeat inl_inr_inv.
      cbn.
      +
        subst.
        reflexivity.
      +
        subst.
        cbn.
        erewrite <-eutt_Ret.
        now constructor.
    -
      erewrite <-eutt_Ret.
      constructor.
      now rewrite M.
      cbn.
      reflexivity.
    -
      erewrite <-eutt_Ret.
      constructor.
      assumption.
      cbn.
      match goal with
      | |- ?x = ?y => enough (T : x ≡ y) by now rewrite T
      end.
      eapply memory_next_key_struct.
      intros.
      now rewrite M.
    -
      erewrite <-eutt_Ret.
      constructor.
      now rewrite M.
      reflexivity.
  Qed.

  (* See [interp_Mem_proper]

    A === nat
    e === eq
    eutt eq
    mem_equiv memories
    eutt (e × mem_equiv) after interpretation



   *)
  (*
  Global Instance interp_state_proper_gen {E F: Type -> Type} {S : Type}
    (equiv : S -> S -> Prop)
    (h : E ~> Monads.stateT S (itree F))
    (magic : True)
    R RR :
    Proper (eutt RR ==> equiv ==> eutt (HeterogeneousRelations.prod_rel equiv RR)) (@interp_state E (itree F) S _ _ _ h R).
  Proof.
    unfold interp_Mem.
    einit. ecofix CIH. intros * EUTT m1 m2 EQM.
    rewrite !unfold_interp_state. punfold EUTT. red in EUTT.
    induction EUTT; intros; subst; simpl; pclearbot.
    - eret.
    - etau.
    -
      Import HeterogeneousRelations.
      assert (forall {X} (e : E X) m1 m2, equiv m1 m2 -> eutt (prod_rel equiv eq) (h X e m1) (h X e m2)) by admit.
      ebind.
      econstructor.
      apply H; auto.
      intros [] [] ?.
      etau.
      cbn.


      destruct e0 as [? | [? | ?]].
      + cbn.
        destruct m.
        * cbn.
          repeat break_match_goal.
          ** cbn.
             unfold memory_lookup_err, trywith in *.
             repeat break_match; try inl_inr.
             rewrite Heqs0 in Heqs; inv Heqs.
             unfold throw; rewrite !bind_vis; cbn.
             evis; intros [].
          ** unshelve epose proof memory_lookup_err_proper msg msg _ m1 m2 EQM id id _; try reflexivity.
             rewrite Heqs, Heqs0 in H; try inl_inr.
          ** unshelve epose proof memory_lookup_err_proper msg msg _ m1 m2 EQM id id _; try reflexivity.
             rewrite Heqs, Heqs0 in H; try inl_inr.
          ** unshelve epose proof memory_lookup_err_proper msg msg _ m1 m2 EQM id id _; try reflexivity.
             rewrite Heqs, Heqs0 in H.
             inv H.
             cbn.
             rewrite !bind_ret_l.
             etau.
             cbn.
             ebase; right.
             apply CIH.
             2:eauto.
             apply REl.
               in Heqs. rewrite EQM in Heqs. unfold memory_lookup_err, trywith in *.
             repeat break_match; try inl_inr.
      + destruct s. cbn. unfold pure_state.
        rewrite !bind_vis.
        evis; intros [].
      + destruct d. cbn. unfold pure_state.
        rewrite !bind_vis.
        evis; intros [].
(* MARK *)
         intors ?.
        ebind.
        econstructor.
        cbn.
      unshelve econstructor.
      exact (prod_rel equiv eq). [reflexivity|].
      intros; subst.
      etau. ebase.
    - rewrite tau_euttge, unfold_interp_state; eauto.
    - rewrite tau_euttge, unfold_interp_state; eauto.
  Qed.
*)


   Global Instance interp_Mem_equiv_proper {A} {e : Equiv A} {EQ : @Equivalence A e} :
    Proper ((eutt e) ==> equiv ==> (eutt equiv)) (@interp_Mem A).
   Proof.
    unfold interp_Mem.
    einit. ecofix CIH. intros * EUTT m1 m2 EQM.
    rewrite !unfold_interp_state. punfold EUTT. red in EUTT.
    induction EUTT; intros; subst; simpl; pclearbot.
    - eret. constructor; cbn; auto.
    - etau.
    - destruct e0 as [? | [? | ?]].
      + cbn.
        destruct m.
        * cbn.
          repeat break_match_goal.
          ** cbn.
             unfold memory_lookup_err, trywith in *.
             repeat break_match; try inl_inr.
             rewrite Heqs0 in Heqs; inv Heqs.
             unfold throw; rewrite !bind_vis; cbn.
             evis; intros [].
          ** unshelve epose proof memory_lookup_err_proper msg msg _ m1 m2 EQM id id _; try reflexivity.
             rewrite Heqs, Heqs0 in H; try inl_inr.
          ** unshelve epose proof memory_lookup_err_proper msg msg _ m1 m2 EQM id id _; try reflexivity.
             rewrite Heqs, Heqs0 in H; try inl_inr.
          ** unshelve epose proof memory_lookup_err_proper msg msg _ m1 m2 EQM id id _; try reflexivity.
             rewrite Heqs, Heqs0 in H.
             inv H.
             cbn.
             rewrite !bind_ret_l.
             etau.
             cbn.
             ebase; right.
             apply CIH.
             2: assumption.

             enough (∀ m1 m2 : mem_block,
                       m1 = m2 →
                     ∀ k1 k2 : mem_block → itree Event A,
                       (forall m, eutt e (k1 m) (k2 m)) →
                     eutt e (k1 m1) (k2 m2))
               as H by (apply H; assumption).
             
             clear.
             intros.

             (* apply REl.
               in Heqs. rewrite EQM in Heqs. unfold memory_lookup_err, trywith in *.
             repeat break_match; try inl_inr. *)
             admit.
        * cbn.
          rewrite !bind_ret_l.
          etau.
          cbn.
          ebase; right.
          apply CIH; [apply REL |].
          rewrite EQM; auto.
        * cbn.
          rewrite !bind_ret_l.
          etau.
          cbn.
          ebase; right.
          apply CIH.
          2: assumption.
          assert (Proper ((=) ==> (≡)) memory_next_key).
          { clear.
            intros m1 m2 EQM.
            unfold equiv, NM_Equiv in EQM.
            apply memory_next_key_struct.
            intro k; split; intro H.
            all: specialize (EQM k).
            all: apply memory_is_set_is_Some in H.
            all: apply memory_is_set_is_Some.
            all: unfold util.is_Some in *.
            all: unfold memory_lookup in *.
            all: do 2 break_match; auto || inv EQM.
          }
          rewrite EQM.
          apply REL.
        * cbn.
          rewrite !bind_ret_l.
          etau.
          cbn.
          ebase; right.
          apply CIH; [apply REL |].
          rewrite EQM; auto.
      + destruct s. cbn. unfold pure_state.
        rewrite !bind_vis.
        evis; intros [].
      + destruct d. cbn. unfold pure_state.
        rewrite !bind_vis.
        evis; intros [].
(* MARK *)
      (* intors ?.
        ebind.
        econstructor.
        cbn.
      unshelve econstructor.
      exact (prod_rel equiv eq). [reflexivity|].
      intros; subst.
      etau. ebase. *)
    - rewrite tau_euttge, unfold_interp_state; eauto.
    - rewrite tau_euttge, unfold_interp_state; eauto.
  Admitted.

  Lemma Denote_Eval_Equiv_NExpr: forall mem σ e v,
      evalNExpr σ e ≡ inr v ->
      eutt Logic.eq
        (interp_Mem (denoteNExpr σ e) mem)
        (Ret (mem, v)).
  Proof.
    induction e; cbn; intros * HEval; cbn* in *; simp; go;
      try (reflexivity ||
             (rewrite IHe1; [| reflexivity]; go; rewrite IHe2; [| reflexivity]; go; try (match_rewrite; go); reflexivity)).
  Qed.

  Ltac bind_ret_l_with H :=
    let EH := fresh "EH" in
    eapply bind_ret_l_equiv; [intros * EH | eapply H; eauto].

  Lemma Denote_Eval_Equiv_AExpr: forall mem σ e v,
      evalAExpr mem σ e = inr v ->
      eutt equiv
        (interp_Mem (denoteAExpr σ e) mem)
        (Ret (mem, v)).
  Proof.
    induction e; cbn; intros * HEval; cbn* in *; simp; go;
      try inv_option; try inv_sum.
    all: try rewrite <-eutt_Ret.
    -
      constructor; now cbn.
    -
      constructor; now cbn.
    -
      cbv in H1; subst b.
      rewrite Denote_Eval_Equiv_NExpr; [| eassumption].
      rewrite bind_ret_l, interp_Mem_bind.
      rewrite Denote_Eval_Equiv_MExpr_eq; [| eassumption].
      repeat (go; match_rewrite).
      rewrite interp_Mem_ret.
      reflexivity.
    -
      specialize (IHe b); autospecialize IHe; [reflexivity |].
      bind_ret_l_with IHe.
      destruct a'; invc EH.
      cbv in H0; subst b0.
      cbn in H.
      rewrite interp_Mem_ret, <-eutt_Ret.
      now constructor.
    -
      rename H1 into V.

      specialize (IHe1 b).
      autospecialize IHe1; [reflexivity|].
      specialize (IHe2 b0).
      autospecialize IHe2; [reflexivity|].

      bind_ret_l_with IHe1.
      destruct a' as (mem', b'); invc EH.
      cbv in H0; subst.
      rename H into MEM'; cbn in MEM'.

      rewrite interp_Mem_bind.

      symmetry in MEM'.
      assert (T : eutt equiv (denoteAExpr σ e2) (denoteAExpr σ e2))
        by reflexivity.
      rewrite (interp_Mem_equiv_proper
                 (denoteAExpr σ e2) (denoteAExpr σ e2) T
                 mem mem' MEM') in IHe2.
      clear T.

      bind_ret_l_with IHe2.
      destruct a' as (mem'', b0'); invc EH.
      cbv in H0; subst.
      rename H into MEM''; cbn in MEM''.

      rewrite interp_Mem_ret, <-eutt_Ret.
      now constructor.
    -
      rename H1 into V.

      specialize (IHe1 b).
      autospecialize IHe1; [reflexivity|].
      specialize (IHe2 b0).
      autospecialize IHe2; [reflexivity|].

      bind_ret_l_with IHe1.
      destruct a' as (mem', b'); invc EH.
      cbv in H0; subst.
      rename H into MEM'; cbn in MEM'.

      rewrite interp_Mem_bind.

      symmetry in MEM'.
      assert (T : eutt equiv (denoteAExpr σ e2) (denoteAExpr σ e2))
        by reflexivity.
      rewrite (interp_Mem_equiv_proper
                 (denoteAExpr σ e2) (denoteAExpr σ e2) T
                 mem mem' MEM') in IHe2.
      clear T.

      bind_ret_l_with IHe2.
      destruct a' as (mem'', b0'); invc EH.
      cbv in H0; subst.
      rename H into MEM''; cbn in MEM''.

      rewrite interp_Mem_ret, <-eutt_Ret.
      now constructor.
    -
      rename H1 into V.

      specialize (IHe1 b).
      autospecialize IHe1; [reflexivity|].
      specialize (IHe2 b0).
      autospecialize IHe2; [reflexivity|].

      bind_ret_l_with IHe1.
      destruct a' as (mem', b'); invc EH.
      cbv in H0; subst.
      rename H into MEM'; cbn in MEM'.

      rewrite interp_Mem_bind.

      symmetry in MEM'.
      assert (T : eutt equiv (denoteAExpr σ e2) (denoteAExpr σ e2))
        by reflexivity.
      rewrite (interp_Mem_equiv_proper
                 (denoteAExpr σ e2) (denoteAExpr σ e2) T
                 mem mem' MEM') in IHe2.
      clear T.

      bind_ret_l_with IHe2.
      destruct a' as (mem'', b0'); invc EH.
      cbv in H0; subst.
      rename H into MEM''; cbn in MEM''.

      rewrite interp_Mem_ret, <-eutt_Ret.
      now constructor.
    -
      rename H1 into V.

      specialize (IHe1 b).
      autospecialize IHe1; [reflexivity|].
      specialize (IHe2 b0).
      autospecialize IHe2; [reflexivity|].

      bind_ret_l_with IHe1.
      destruct a' as (mem', b'); invc EH.
      cbv in H0; subst.
      rename H into MEM'; cbn in MEM'.

      rewrite interp_Mem_bind.

      symmetry in MEM'.
      assert (T : eutt equiv (denoteAExpr σ e2) (denoteAExpr σ e2))
        by reflexivity.
      rewrite (interp_Mem_equiv_proper
                 (denoteAExpr σ e2) (denoteAExpr σ e2) T
                 mem mem' MEM') in IHe2.
      clear T.

      bind_ret_l_with IHe2.
      destruct a' as (mem'', b0'); invc EH.
      cbv in H0; subst.
      rename H into MEM''; cbn in MEM''.

      rewrite interp_Mem_ret, <-eutt_Ret.
      now constructor.
    -
      rename H1 into V.

      specialize (IHe1 b).
      autospecialize IHe1; [reflexivity|].
      specialize (IHe2 b0).
      autospecialize IHe2; [reflexivity|].

      bind_ret_l_with IHe1.
      destruct a' as (mem', b'); invc EH.
      cbv in H0; subst.
      rename H into MEM'; cbn in MEM'.

      rewrite interp_Mem_bind.

      symmetry in MEM'.
      assert (T : eutt equiv (denoteAExpr σ e2) (denoteAExpr σ e2))
        by reflexivity.
      rewrite (interp_Mem_equiv_proper
                 (denoteAExpr σ e2) (denoteAExpr σ e2) T
                 mem mem' MEM') in IHe2.
      clear T.

      bind_ret_l_with IHe2.
      destruct a' as (mem'', b0'); invc EH.
      cbv in H0; subst.
      rename H into MEM''; cbn in MEM''.

      rewrite interp_Mem_ret, <-eutt_Ret.
      now constructor.
    -
      rename H1 into V.

      specialize (IHe1 b).
      autospecialize IHe1; [reflexivity|].
      specialize (IHe2 b0).
      autospecialize IHe2; [reflexivity|].

      bind_ret_l_with IHe1.
      destruct a' as (mem', b'); invc EH.
      cbv in H0; subst.
      rename H into MEM'; cbn in MEM'.

      rewrite interp_Mem_bind.

      symmetry in MEM'.
      assert (T : eutt equiv (denoteAExpr σ e2) (denoteAExpr σ e2))
        by reflexivity.
      rewrite (interp_Mem_equiv_proper
                 (denoteAExpr σ e2) (denoteAExpr σ e2) T
                 mem mem' MEM') in IHe2.
      clear T.

      bind_ret_l_with IHe2.
      destruct a' as (mem'', b0'); invc EH.
      cbv in H0; subst.
      rename H into MEM''; cbn in MEM''.

      rewrite interp_Mem_ret, <-eutt_Ret.
      now constructor.
  Qed.

  Lemma Denote_Eval_Equiv_IMap: forall mem n f σ m1 m2 id,
      evalDSHIMap mem n f σ m1 m2 = inr id ->
      eutt equiv
        (interp_Mem (denoteDSHIMap n f σ m1 m2) mem)
        (Ret (mem, id)).
  Proof.
    induction n; intros; cbn* in *; simp; go; try reflexivity.
    all: try inv_sum.
    apply eutt_Ret.
    now constructor.

    bind_ret_l_with Denote_Eval_Equiv_AExpr.
    2: {
      unfold evalIUnCType in Heqs1.
      rewrite Heqs1.
      reflexivity.
    }
    destruct a' as [mem' ?]; invc EH.
    cbv in H1; subst.
    rename H0 into MEM'; cbn in MEM'.

    eapply IHn in H.

    symmetry in MEM'.
    remember (denoteDSHIMap n f σ m1 (mem_add n b0 m2)) as t.
    assert (T : eutt equiv t t)
      by reflexivity.
    rewrite (interp_Mem_equiv_proper t t T mem mem' MEM') in H.
    subst t; clear T.

    rewrite H.
    reflexivity.
  Qed.

  Lemma Denote_Eval_Equiv_BinCType: forall mem σ f i a b v,
      evalIBinCType mem σ f i a b = inr v ->
      eutt equiv
        (interp_Mem (denoteIBinCType σ f i a b) mem)
        (Ret (mem, v)).
  Proof.
    unfold evalIBinCType, denoteIBinCType; intros.
    eapply Denote_Eval_Equiv_AExpr; eauto.
  Qed.

  Lemma Denote_Eval_Equiv_BinOp: forall mem n off σ f x y blk,
      evalDSHBinOp mem n off f σ x y = inr blk ->
      eutt equiv
        (interp_Mem (denoteDSHBinOp n off f σ x y) mem)
        (Ret (mem, blk)).
  Proof.
    induction n as [| n IH]; intros; cbn* in *; simp; go; try reflexivity.
    all: try inl_inr; repeat inl_inr_inv.
    apply eutt_Ret.
    now constructor.

    eapply eutt_equiv_Proper.
    eapply ITree_bind_equiv_Proper.
    2: {
      match goal with
      | |- pointwise_impl _ _ ?f _ => instantiate (1:=f)
      end.
      instantiate (1:=equiv).
      apply pointwise_impl_eq.
      eapply pointwise_impl'_simp.
      clear.
      intros (mem1, v1) (mem2, v2) [M V].
      cbn in M, V.
      eapply interp_Mem_equiv_proper.
      2: assumption.
      cbv in V; subst.
      reflexivity.
    }
    rewrite Denote_Eval_Equiv_BinCType.
    reflexivity.
    rewrite Heqs2; reflexivity.
    reflexivity.
    rewrite bind_ret_l.
    eapply IH.
    assumption.
  Qed.

  Import MonadNotation.
  Local Open Scope monad_scope.

  Definition denote_Loop_for_i_to_N σ body (i N: nat) :=
    iter (fun (p: nat) =>
            if EqNat.beq_nat p N
            then ret (inr tt)
            else
              vp <- lift_Serr (from_nat p) ;;
              denoteDSHOperator ((DSHnatVal vp , false):: σ) body;;
              Ret (inl (S p))
      ) i.

  Lemma denote_Loop_for_0_to_N:
    forall σ body N, eutt equiv (denote_Loop_for_i_to_N σ body 0 N) (denoteDSHOperator σ (DSHLoop N body)).
  Proof.
    unfold denote_Loop_for_i_to_N; reflexivity.
  Qed.

  (* loop over [i .. N)
     Some boundary cases:
     - i<N => either [Some _] or [None] if runs out of fuel
     - i>N => same as [eval_Loop_for_0_to_N]
     - N=0 =>
     - fuel=0 => [None]
     - fuel>0 => [Some (ret mem)] no-op
     - i=N =>
     - fuel=0 => [None]
     - fuel>0 => [Some (ret mem)] no-op

     NOTE: Struct [{struct N}] works instead of [{struct fuel}] here as well.
   *)
  Fixpoint eval_Loop_for_i_to_N σ body (i N: nat) mem fuel {struct fuel} :=
    match fuel with
    | O => None
    | S fuel =>
        match N with
        | O => Some (ret mem)
        | S N =>
            if EqNat.beq_nat i (S N) then
              Some (ret mem)
            else
              match eval_Loop_for_i_to_N σ body i N mem fuel with
              | Some (inr mem) =>
                  match from_nat N with
                  | inl msg => Some (inl msg)
                  | inr vN =>
                      evalDSHOperator ((DSHnatVal vN , false) :: σ) body mem fuel
                  end
              | Some (inl msg) => Some (inl msg)
              | None => None
              end
        end
    end.

  Lemma eval_Loop_for_N_to_N: forall fuel σ op N mem,
      eval_Loop_for_i_to_N σ op N N mem (S fuel) ≡ Some (ret mem).
  Proof.
    intros fuel σ op [| N] mem; [reflexivity |].
    simpl; rewrite Nat.eqb_refl; reflexivity.
  Qed.

  (*
    Lemma eval_Loop_for_i_to_N_invert: forall σ i ii N op fuel mem_i mem_f,
    i < N ->
    from_nat i ≡ inr ii ->
    eval_Loop_for_i_to_N σ op i N mem_i fuel ≡ Some (inr mem_f) ->
    exists mem_aux,
    evalDSHOperator ((DSHnatVal ii , false) :: σ) op mem_i fuel ≡ Some (inr mem_aux) /\
    eval_Loop_for_i_to_N σ op (S i) N mem_aux fuel ≡ Some (inr mem_f).
    Proof.
    (* This proof is surprisingly painful to go through *)
    intros.
    (* Induction on the number of steps remaining *)
    remember (N - i) as k.
    revert σ fuel i ii N Heqk mem_i mem_f H0 H1 H.
    induction k as [| k IH];
    intros σ fuel i ii N EQ mem_i mem_f Hn Heval ineq;[lia|].

    (* N > 0 for us to be able to take a step *)
    destruct N as [| N]; [lia |].
    (* We got some fuel since the computation succeeded *)
    destruct fuel as [| fuel]; [inv Heval |].
    (* We can now reduce *)
    simpl in Heval.

    (* We know there's still a step to be taken *)
    destruct (i =? S N)%nat eqn:EQ'; [apply beq_nat_true in EQ'; lia | apply beq_nat_false in EQ'].
    (* And that the recursive call succeeded since the computation did *)
    destruct (eval_Loop_for_i_to_N σ op i N mem_i fuel) eqn: HEval'; [| inv Heval].
    destruct s; inv Heval.

    (* Now there are two cases:
    either a single step was remaining and we should be able to conclude directly;
    or more were remaining, and we should be able to conclude by induction
   *)

   destruct (i =? N)%nat eqn: EQ''; [apply beq_nat_true in EQ''; subst; clear IH |].
   - clear EQ' EQ ineq.
   rewrite Hn in H0.
   destruct fuel as [| fuel]; [inv HEval' |].
   rewrite eval_Loop_for_N_to_N in HEval'.
   setoid_rewrite eval_Loop_for_N_to_N.
   inv HEval'.
   exists mem_f.
   split; [apply evalDSHOperator_fuel_monotone; auto | auto ].
   rewrite Hn.
   auto.
   - destruct (from_nat N) eqn:NN.
   +
   eapply IH in HEval';[|lia|eauto|apply beq_nat_false in EQ''; lia].
   destruct HEval' as (mem_aux & STEP & TAIL).
   exists mem_aux; split; [apply evalDSHOperator_fuel_monotone; auto |].
   cbn; rewrite EQ'', TAIL.
   rewrite NN.
   reflexivity.
   +
   eapply IH in HEval';[|lia|eauto|apply beq_nat_false in EQ''; lia].
   destruct HEval' as (mem_aux & STEP & TAIL).
   exists mem_aux; split; [apply evalDSHOperator_fuel_monotone; auto |].
   cbn; rewrite EQ'', TAIL.
   rewrite NN.
   reflexivity.
   Qed.
   *)

  Lemma eval_Loop_for_i_to_N_invert: forall σ i ii N op fuel mem_i mem_f,
      i < N ->
      from_nat i ≡ inr ii ->
      eval_Loop_for_i_to_N σ op i N mem_i fuel = Some (inr mem_f) ->
      exists mem_aux,
        evalDSHOperator ((DSHnatVal ii , false) :: σ) op mem_i fuel = Some (inr mem_aux) /\
          eval_Loop_for_i_to_N σ op (S i) N mem_aux fuel = Some (inr mem_f).
  Proof.
    (* This proof is surprisingly painful to go through *)
    intros.
    (* Induction on the number of steps remaining *)
    remember (N - i) as k.
    revert σ fuel i ii N Heqk mem_i mem_f H0 H1 H.
    induction k as [| k IH];
      intros σ fuel i ii N EQ mem_i mem_f Hn Heval ineq;[lia|].

    (* N > 0 for us to be able to take a step *)
    destruct N as [| N]; [lia |].
    (* We got some fuel since the computation succeeded *)
    destruct fuel as [| fuel]; [inv Heval |].
    (* We can now reduce *)
    simpl in Heval.

    (* We know there's still a step to be taken *)
    destruct (i =? S N)%nat eqn:EQ'; [apply beq_nat_true in EQ'; lia | apply beq_nat_false in EQ'].
    (* And that the recursive call succeeded since the computation did *)
    destruct (eval_Loop_for_i_to_N σ op i N mem_i fuel) eqn: HEval'; [| inv Heval].
    destruct s; inv Heval.
    1: solve [inv H1].

    (* Now there are two cases:
       either a single step was remaining and we should be able to conclude directly;
       or more were remaining, and we should be able to conclude by induction
     *)

    destruct (i =? N)%nat eqn: EQ''; [apply beq_nat_true in EQ''; subst; clear IH |].
    - clear EQ' EQ ineq.
      rewrite Hn in H.
      destruct fuel as [| fuel]; [inv HEval' |].
      rewrite eval_Loop_for_N_to_N in HEval'.
      setoid_rewrite eval_Loop_for_N_to_N.
      inv HEval'.
      exists mem_f.
      split; [| reflexivity].
      apply evalDSHOperator_fuel_monotone_equiv.
      rewrite <-H.
      inv H1.
      now rewrite H3.
    - destruct (from_nat N) eqn:NN.
      +
        invc H.
        invc H1.
      +
        apply Option_equiv_eq in HEval'.
        eapply IH in HEval';[|lia|eauto|apply beq_nat_false in EQ''; lia].
        destruct HEval' as (mem_aux & STEP & TAIL).
        exists mem_aux; split; [apply evalDSHOperator_fuel_monotone_equiv; auto |].
        cbn.
        rewrite EQ'', NN.
        repeat break_match_goal; invc TAIL; invc H3.
        rewrite H4.
        rewrite <-H.
        invc H1.
        now rewrite H3.
  Qed.

  Lemma eval_Loop_for_i_to_N_i_gt_N σ op i N fuel mem:
    i > N ->
    eval_Loop_for_i_to_N σ op i N mem fuel ≡ eval_Loop_for_i_to_N σ op 0 N mem fuel.
  Proof.
    revert fuel.
    induction N; intros.
    +
      destruct fuel;reflexivity.
    +
      destruct fuel; [ reflexivity|].
      cbn.
      break_if; [apply beq_nat_true in Heqb; lia| ].
      apply beq_nat_false in Heqb.
      rewrite IHN.
      reflexivity.
      lia.
  Qed.

  Lemma eval_Loop_for_0_to_N:
    forall σ body N mem mem' fuel,
      evalDSHOperator σ (DSHLoop N body) mem fuel = Some (inr mem') ->
      eval_Loop_for_i_to_N σ body 0 N mem fuel = Some (inr mem').
  Proof.
    induction N as [| N IH]; intros.
    - destruct fuel; auto.
    - destruct fuel as [| fuel ]; [auto |].
      cbn in *.
      repeat break_match_hyp;
        try some_none; repeat some_inv;
        try inl_inr; repeat inl_inr_inv.
      apply Option_equiv_eq in Heqo.
      apply IH in Heqo.
      repeat break_match;
        try some_none; repeat some_inv;
        try inl_inr; repeat inl_inr_inv.
      now rewrite Heqo.
  Qed.

  Lemma eval_Loop_for_i_to_N_fuel_monotone:
    forall res σ op i N fuel mem,
      eval_Loop_for_i_to_N σ op i N mem fuel = Some res ->
      eval_Loop_for_i_to_N σ op i N mem (S fuel) = Some res.
  Proof.
    intros res σ op i N fuel mem H.
    revert H.
    revert res σ i fuel.
    induction N; intros.
    -
      destruct fuel; cbn in *; [some_none| apply H].
    -
      cbn.
      destruct fuel; [cbn in H; some_none|].
      break_if.
      +
        apply beq_nat_true in Heqb.
        subst.
        cbn in H.
        rewrite Nat.eqb_refl in H.
        apply H.
      +
        repeat break_match_goal; subst; cbn in H; rewrite Heqb in H.
        *
          rewrite <- Heqo.
          repeat break_match_hyp; subst;
            apply Option_equiv_eq in Heqo0.
          --
            rewrite <- H.
            apply IHN.
            apply Heqo0.
          --
            apply IHN in Heqo0.
            rewrite Heqo in Heqo0.
            inv Heqo0.
            inv H2.
          --
            apply IHN in Heqo0.
            rewrite Heqo in Heqo0.
            inv Heqo0.
            inv H2.
          --
            some_none.
        *
          repeat break_match_hyp; subst;
            apply Option_equiv_eq in Heqo0.
          --
            apply IHN in Heqo0.
            rewrite Heqo in Heqo0.
            inv Heqo0.
            inv H2.
          --
            apply IHN in Heqo0.
            rewrite Heqo in Heqo0.
            inv Heqo.
            inv Heqs1.
            apply H.
          --
            inv Heqs1.
          --
            some_none.
        *
          repeat break_match_hyp; subst;
            apply Option_equiv_eq in Heqo0.
          --
            apply IHN in Heqo0.
            rewrite Heqo in Heqo0.
            inv Heqo0.
            inv H2.
          --
            inv Heqs1.
          --
            apply IHN in Heqo0.
            rewrite Heqo in Heqo0.
            repeat some_inv; repeat inl_inr_inv; subst.
            rewrite Heqo0.
            destruct evalDSHOperator eqn:E in H; [| some_none].
            erewrite evalDSHOperator_fuel_monotone; eassumption.
          --
            some_none.
        *
          exfalso.
          break_match_hyp.
          --
            apply Option_equiv_eq in Heqo0.
            apply IHN in Heqo0.
            rewrite Heqo in Heqo0.
            some_none.
          --
            some_none.
  Qed.

  Lemma eval_Loop_for_i_to_N_fuel_monotone_gt:
    forall res σ op i N fuel fuel' mem,
      fuel'>fuel ->
      eval_Loop_for_i_to_N σ op i N mem fuel = Some res ->
      eval_Loop_for_i_to_N σ op i N mem fuel' = Some res.
  Proof.
    intros H.
    intros σ op i N fuel fuel' mem H0 H1.
    remember (fuel'-fuel) as d.
    assert(F: fuel' ≡ fuel + d) by lia.
    subst fuel'.
    clear H0 Heqd.
    induction d.
    -
      replace (fuel + 0) with fuel by lia.
      auto.
    -
      replace (fuel + S d) with (S (fuel + d)) by lia.
      apply eval_Loop_for_i_to_N_fuel_monotone.
      auto.
  Qed.

  (* Extend [from_nat_lt] to [le] *)
  Lemma from_nat_le:
    forall x xi y,
      from_nat x ≡ inr xi ->
      y<=x ->
      exists yi, from_nat y ≡ inr yi.
  Proof.
    intros.
    destruct (Nat.eq_dec x y).
    -
      subst.
      eexists.
      eauto.
    -
      eapply from_nat_lt; eauto.
      unfold lt, peano_naturals.nat_lt.
      lia.
  Qed.

  Lemma Loop_is_Iter_aux:
    ∀ (op : DSHOperator)
      (IHop: ∀ (σ : evalContext) (mem' : memory) (fuel : nat) (mem : memory),
          evalDSHOperator σ op mem (S fuel) = Some (inr mem')
          → eutt equiv (interp_Mem (denoteDSHOperator σ op) mem) (Ret (mem', ())))

      (i N: nat)
      (σ : evalContext) (mem : memory) (fuel : nat) (mem' : memory) {nn},
      from_nat N ≡ inr nn ->
      i <= (S N) ->
      eval_Loop_for_i_to_N σ op i (S N) mem (S fuel) = Some (inr mem')
      → eutt equiv
          (interp_state (case_ Mem_handler pure_state) (denote_Loop_for_i_to_N σ op i (S N)) mem) (Ret (mem', ())).
  Proof.
    intros op IHop i N σ mem fuel mem' nn NN ineq HEval.
    remember ((S N) - i) as k.
    revert Heqk σ mem mem' HEval.
    revert i ineq NN.
    induction k as [| k IH].
    - intros i ineq NN EQ.
      assert ((S N) ≡ i) by lia; clear EQ ineq; subst.
      intros.
      cbn in HEval.
      rewrite Nat.eqb_refl in HEval.
      inv HEval.
      unfold denote_Loop_for_i_to_N.
      (* poor man's [iter_unfold_pointed] *)
      match goal with
      | |- context[eutt equiv (interp_state ?h (iter ?k ?i) _) _] =>
          generalize (ITree.Basics.CategoryTheory.iter_unfold k);
          let EQ := fresh "EQ" in intros EQ; rewrite (EQ i); clear EQ
      end.
      cbn; go.
      rewrite Nat.eqb_refl.
      go. cbn; go.
      apply eutt_Ret.
      invc H1.
      now constructor.
    - intros i ineq NN EQ σ mem mem' HEval.
      destruct (i =? S N)%nat eqn:EQ'.
      * unfold eval_Loop_for_i_to_N in HEval; rewrite EQ' in HEval.
        inv HEval.
        unfold denote_Loop_for_i_to_N.
        (* poor man's [iter_unfold_pointed] *)
        match goal with
        | |- context[eutt equiv (interp_state ?h (iter ?k ?i) _) _] =>
            generalize (ITree.Basics.CategoryTheory.iter_unfold k);
            let EQ := fresh "EQ" in intros EQ; rewrite (EQ i); clear EQ
        end.
        cbn; go.
        rewrite EQ'.
        cbn; go.
        cbn; go.
        apply eutt_Ret.
        invc H1.
        now constructor.
      * unfold denote_Loop_for_i_to_N.
        (* poor man's [iter_unfold_pointed] *)
        match goal with
        | |- context[eutt equiv (interp_state ?h (iter ?k ?i) _) _] =>
            generalize (ITree.Basics.CategoryTheory.iter_unfold k);
            let EQ := fresh "EQ" in intros EQ; rewrite (EQ i); clear EQ
        end.
        cbn; go.
        rewrite EQ'; cbn*; go.
        apply beq_nat_false in EQ'.
        assert(exists ii : t, from_nat i ≡ inr ii) as II.
        {
          assert(i<=N) by lia.
          eapply from_nat_le;
            eauto.
        }
        destruct II as [ii II].
        rewrite II.
        cbn.
        apply eval_Loop_for_i_to_N_invert with (ii:=ii) in HEval; [|lia| apply II].
        destruct HEval as (mem_aux & Eval_body & Eval_tail).
        apply evalDSHOperator_fuel_monotone_equiv in Eval_body.
        apply IHop in Eval_body.
        go.

        bind_ret_l_with Eval_body.
        destruct a' as (mem_aux', ?); invc EH.
        clear H0.
        rename H into MEM_AUX'; cbn in MEM_AUX'.
        cbn; go.
        cbn; go.
        apply IH in Eval_tail; try lia; auto.
        clear - MEM_AUX' Eval_tail.
        
        symmetry in MEM_AUX'.
        remember (denote_Loop_for_i_to_N σ op (S i) (S N)) as t.
        assert (T : eutt equiv t t)
          by reflexivity.
        rewrite (interp_Mem_equiv_proper t t T mem_aux mem_aux' MEM_AUX')
          in Eval_tail.
        subst t; clear T.
        assumption.
  Qed.

  Lemma Loop_is_Iter:
    ∀ (op : DSHOperator)
      (IHop: ∀ (σ : evalContext) (mem' : memory) (fuel : nat) (mem : memory),
          evalDSHOperator σ op mem (S fuel) = Some (inr mem')
          → eutt equiv (interp_Mem (denoteDSHOperator σ op) mem) (Ret (mem', ())))
      (N: nat) (σ : evalContext) (mem : memory) (fuel : nat) (mem' : memory),
      evalDSHOperator σ (DSHLoop N op) mem (S fuel) = Some (inr mem') ->
      eutt equiv (interp_state (case_ Mem_handler pure_state) (denoteDSHOperator σ (DSHLoop N op)) mem) (Ret (mem', ())).
  Proof.
    intros.
    destruct N.
    -
      cbn in H; inv H.
      cbn; go.
      (* poor man's [iter_unfold_pointed] *)
      match goal with
      | |- context[eutt equiv (interp_state ?h (iter ?k ?i) _) _] =>
          generalize (ITree.Basics.CategoryTheory.iter_unfold k);
          let EQ := fresh "EQ" in intros EQ; rewrite (EQ i); clear EQ
      end.
      cbn; go.
      cbn; go.
      apply eutt_Ret.
      invc H2.
      now constructor.
    -
      edestruct @evalDSHLoop_SN_in_range_equiv; eauto.
      apply eval_Loop_for_0_to_N in H.
      cbn; go.
      eapply Loop_is_Iter_aux;eauto.
      lia.
  Qed.

  Lemma Denote_Eval_Equiv_DSHMap2:
    forall n (σ: evalContext) mem f m1 m2 m3 m4,
      evalDSHMap2 mem n f σ m1 m2 m3  = inr m4 ->
      eutt equiv
        (interp_Mem (denoteDSHMap2 n f σ m1 m2 m3) mem)
        (Ret (mem, m4)).
  Proof.
    induction n as [| n IH]; intros σ mem f m1 m2 m3 m4 HEval; cbn in HEval.
    - inv_sum; cbn; go.
      apply eutt_Ret.
      now constructor.
    - cbn* in *; simp; go.
      all: try some_none; repeat some_inv; try inl_inr; repeat inl_inr_inv.
      unfold denoteBinCType, evalBinCType in *; cbn.

      bind_ret_l_with Denote_Eval_Equiv_AExpr; [| now rewrite Heqs1].
      destruct a' as (mem', b'); invc EH.
      cbv in H0; subst.
      rename H into MEM'; cbn in MEM'.

      rewrite IH; [| rewrite MEM'; eassumption].
      rewrite <-eutt_Ret.
      now constructor.
  Qed.

  Lemma Denote_Eval_Equiv_DSHPower:
    forall n (σ: evalContext) mem f x y xoff yoff m,
      evalDSHPower mem σ n f x y xoff yoff = inr m ->
      eutt equiv
        (interp_Mem (denoteDSHPower σ n f x y xoff yoff) mem)
        (Ret (mem, m)).
  Proof.
    induction n as [| n IH]; intros σ mem f x y xoff yoff m HEval; cbn in HEval.
    - inv_sum; cbn; go.
      apply eutt_Ret.
      now constructor.
    - cbn* in *; simp; go.
      all: try some_none; repeat some_inv; try inl_inr; repeat inl_inr_inv.
      unfold denoteBinCType, evalBinCType in *; cbn.

      bind_ret_l_with Denote_Eval_Equiv_AExpr; [| now rewrite Heqs1].
      destruct a' as (mem', b'); invc EH.
      cbv in H0; subst.
      rename H into MEM'; cbn in MEM'.

      rewrite IH; [| rewrite MEM'; eassumption].
      rewrite <-eutt_Ret.
      now constructor.
  Qed.

  Lemma assert_nat_le_assert_NT_le
    (s : string)
    (n : nat)
    (n' i : t)
    :
    from_nat n ≡ inr n' ->
    assert_nat_le s n (to_nat i) ≡ assert_NT_le s n' i.
  Proof.
    intros.
    unfold assert_nat_le, assert_NT_le, assert_true_to_err.
    pose proof to_nat_from_nat n n' as [H' _].
    rewrite H' by now rewrite H; clear H H'.
    reflexivity.
  Qed.

  Theorem Denote_Eval_Equiv:
    forall (σ: evalContext) (op: DSHOperator) (mem: memory) (fuel: nat) (mem': memory),
      evalDSHOperator σ op mem fuel = Some (inr mem') ->
      eutt equiv (interp_Mem (denoteDSHOperator σ op) mem) (Ret (mem', tt)).
  Proof.
    intros ? ? ? ? ? H; destruct fuel as [| fuel]; [inversion H |].
    revert σ mem' fuel mem H.
    induction op; intros σ mem fuel mem' HEval; cbn in HEval.
    - simp; cbn; go.
      apply eutt_Ret.
      invc HEval; invc H1.
      now constructor.
    - cbn* in *; simp; go.
      all: try some_none; repeat some_inv; try inl_inr; repeat inl_inr_inv.
      rewrite Heqs0; cbn; go.
      rewrite Heqs; cbn.
      go.
      3: cbn*; rewrite Heqo1; reflexivity.
      2: cbn*; rewrite Heqo0; reflexivity.
      rewrite Denote_Eval_Equiv_NExpr; eauto; go.
      rewrite Denote_Eval_Equiv_NExpr; eauto; go.
      repeat match_rewrite; go.
      rewrite interp_Mem_MemSet.
      apply eutt_Ret.
      now constructor.
    - cbn* in *; simp; go.
      all: try some_none; repeat some_inv; try inl_inr; repeat inl_inr_inv.
      cbn*; repeat match_rewrite; go.
      rewrite Heqs2. repeat match_rewrite; go.
      unfold assert_NT_le, assert_true_to_err in Heqs3.
      unfold assert_nat_le. unfold assert_true_to_err.
      break_if.
      go.
      3: cbn*; match_rewrite; eauto.
      2: cbn*; match_rewrite; eauto.
      2: {
        exfalso.
        apply leb_complete_conv in Heqb.
        unfold to_nat in Heqb. break_if. 2 : inv Heqs3.
        eapply leb_complete in Heqb0.
        unfold to_nat in Heqb0. revert Heqb.
        apply le_not_lt. clear -Heqs Heqb0.
        unfold from_nat in Heqs.
        apply from_Z_intval in Heqs.
        rewrite <- Heqs in Heqb0.
        lia.
      }
      bind_ret_l_with Denote_Eval_Equiv_IMap; [| now rewrite Heqs6].
      destruct a'; invc EH; cbn in *.
      rewrite interp_Mem_MemSet.
      rewrite <-eutt_Ret.
      constructor; cbn; [| reflexivity].
      now rewrite H, H0.
    - cbn* in *; simp; go.
      all: try some_none; repeat some_inv; try inl_inr; repeat inl_inr_inv.
      cbn*; repeat match_rewrite; go.
      rewrite Heqs2.
      erewrite assert_nat_le_assert_NT_le by eassumption.
      rewrite Heqs3.
      repeat match_rewrite; go.
      2,3: cbn*; match_rewrite; eauto.
      bind_ret_l_with Denote_Eval_Equiv_BinOp; [| now rewrite Heqs6].
      destruct a'; invc EH; cbn in *.
      rewrite interp_Mem_MemSet.
      rewrite <-eutt_Ret.
      constructor; cbn; [| reflexivity].
      now rewrite H, H0.
    - cbn* in *; simp; go.
      all: try some_none; repeat some_inv; try inl_inr; repeat inl_inr_inv.
      cbn*; repeat match_rewrite; go.
      erewrite assert_nat_le_assert_NT_le by eassumption.
      rewrite Heqs3.
      cbn*; repeat match_rewrite; go.
      2,3,4: cbn*; match_rewrite; eauto.
      bind_ret_l_with Denote_Eval_Equiv_DSHMap2; [| now rewrite Heqs7].
      destruct a'; invc EH; cbn in *.
      rewrite interp_Mem_MemSet.
      rewrite <-eutt_Ret.
      constructor; cbn; [| reflexivity].
      now rewrite H, H0.
    - cbn* in *; simp; go.
      all: try some_none; repeat some_inv; try inl_inr; repeat inl_inr_inv.
      cbn*; repeat match_rewrite; go.
      rewrite Heqs1.
      repeat match_rewrite; go.
      rewrite Denote_Eval_Equiv_NExpr; eauto; go.
      rewrite Denote_Eval_Equiv_NExpr; eauto; go.
      rewrite Denote_Eval_Equiv_NExpr; eauto; go.

      rewrite Heqs7. rewrite interp_Mem_ret. rewrite bind_ret_l.
      rewrite interp_Mem_bind.
      bind_ret_l_with Denote_Eval_Equiv_DSHPower; [| now rewrite Heqs8].
      destruct a'; invc EH; cbn in *.
      rewrite interp_Mem_MemSet.
      rewrite <-eutt_Ret.
      constructor; cbn; [| reflexivity].
      now rewrite H, H0.
      {
        unfold memory_lookup_err.
        now rewrite Heqo.
      }
      {
        unfold memory_lookup_err.
        now rewrite Heqo0.
      }
    - eapply Loop_is_Iter; eauto.
    - cbn; simp; go.
      all: try some_none; repeat some_inv; try inl_inr; repeat inl_inr_inv.
      Transparent interp_Mem.
      unfold interp_Mem.
      rewrite interp_state_trigger; cbn.
      Opaque interp_Mem.
      go.
      rewrite interp_Mem_MemSet; go.
      destruct fuel as [| fuel]; [inv Heqo |].
      bind_ret_l_with IHop; [| now rewrite Heqo].
      destruct a'; invc EH; cbn in H; clear u H0.
      Transparent interp_Mem.
      unfold interp_Mem.
      rewrite interp_state_trigger; cbn.
      rewrite <-eutt_Ret.
      constructor.
      now rewrite H.
      reflexivity.
      Opaque interp_Mem.
    - cbn* in *; simp.
      all: try some_none; repeat some_inv; try inl_inr; repeat inl_inr_inv.
      unfold denotePExpr; cbn*; match_rewrite; go.
      2:cbn*; match_rewrite; eauto.
      rewrite interp_Mem_MemSet, <-eutt_Ret.
      now constructor.
    - cbn; simp; go.
      all: try some_none; repeat some_inv; try inl_inr; repeat inl_inr_inv.

      bind_ret_l_with IHop1;
        [| eapply evalDSHOperator_fuel_monotone_equiv;
           now rewrite Heqo].
      destruct a'; invc EH; cbn in H; clear u H0.
      
      erewrite IHop2;
        [| eapply evalDSHOperator_fuel_monotone_equiv;
           now rewrite H, HEval].
      reflexivity.
  Qed.

End Eval_Denote_Equiv.

Module interp_Mem_equiv_proper_False.

  Definition bin0 : binary64 := B754_zero 53 1024 true.

  (*        x                 y       
                                      
            3                 2       
           / \               / \      
          2   *            1     3    
         / \              / \   / \   
        1   *            *   * *   *  
       / \                            
      *   *                           
  *)

  Definition x_tree : Memory.NM.Raw.tree binary64 :=
    Memory.NM.Raw.Node
      (Memory.NM.Raw.Node
        (Memory.NM.Raw.Node
          (Memory.NM.Raw.Leaf binary64)
          1
          bin0
          (Memory.NM.Raw.Leaf binary64)
          0%Z)
        2
        bin0
        (Memory.NM.Raw.Leaf binary64)
        0%Z)
      3
      bin0
      (Memory.NM.Raw.Leaf binary64)
      0%Z.

  Definition y_tree : Memory.NM.Raw.tree binary64 :=
    Memory.NM.Raw.Node
      (Memory.NM.Raw.Node
        (Memory.NM.Raw.Leaf binary64)
        1
        bin0
        (Memory.NM.Raw.Leaf binary64)
        0%Z)
      2
      bin0
      (Memory.NM.Raw.Node
        (Memory.NM.Raw.Leaf binary64)
        3
        bin0
        (Memory.NM.Raw.Leaf binary64)
        0%Z)
      0%Z.

  Ltac derive_bst :=
    repeat intro;
    repeat (inv_prop Memory.NM.Raw.In; auto).

  Lemma x_tree_is_bst: Memory.NM.Raw.bst x_tree.
  Proof.
    apply Memory.NM.Raw.BSNode.
    - apply Memory.NM.Raw.BSNode.
      + apply Memory.NM.Raw.BSNode.
        * apply Memory.NM.Raw.BSLeaf.
        * apply Memory.NM.Raw.BSLeaf.
        * derive_bst.
        * derive_bst.
      + apply Memory.NM.Raw.BSLeaf.
      + derive_bst.
      + derive_bst.
    - apply Memory.NM.Raw.BSLeaf.
    - derive_bst.
    - derive_bst.
  Qed.

  Lemma y_tree_is_bst: Memory.NM.Raw.bst y_tree.
  Proof.
    apply Memory.NM.Raw.BSNode.
    - apply Memory.NM.Raw.BSNode.
      + apply Memory.NM.Raw.BSLeaf.
      + apply Memory.NM.Raw.BSLeaf.
      + derive_bst.
      + derive_bst.
    - apply Memory.NM.Raw.BSNode.
      + apply Memory.NM.Raw.BSLeaf.
      + apply Memory.NM.Raw.BSLeaf.
      + derive_bst.
      + derive_bst.
    - derive_bst.
    - derive_bst.
  Qed.

  Definition x_mb : mem_block := Memory.NM.Bst x_tree_is_bst.
  Definition y_mb : mem_block := Memory.NM.Bst y_tree_is_bst.

  Lemma x_y_mb_neq: ~ (x_mb ≡ y_mb).
  Proof.
    intro H; inv H.
  Qed.

  Lemma x_y_mb_equiv: x_mb = y_mb.
  Proof.
    intro k.
    do 4 (destruct k; [reflexivity |]).
    reflexivity.
  Qed.

  Definition x_mem_tree : Memory.NM.Raw.tree mem_block :=
    Memory.NM.Raw.Node
      (Memory.NM.Raw.Leaf mem_block)
      0
      x_mb
      (Memory.NM.Raw.Leaf mem_block)
      0%Z.

  Definition y_mem_tree : Memory.NM.Raw.tree mem_block :=
    Memory.NM.Raw.Node
      (Memory.NM.Raw.Leaf mem_block)
      0
      y_mb
      (Memory.NM.Raw.Leaf mem_block)
      0%Z.

  Lemma x_mem_tree_is_bst: Memory.NM.Raw.bst x_mem_tree.
  Proof.
    apply Memory.NM.Raw.BSNode.
    - apply Memory.NM.Raw.BSLeaf.
    - apply Memory.NM.Raw.BSLeaf.
    - derive_bst.
    - derive_bst.
  Qed.

  Lemma y_mem_tree_is_bst: Memory.NM.Raw.bst y_mem_tree.
  Proof.
    apply Memory.NM.Raw.BSNode.
    - apply Memory.NM.Raw.BSLeaf.
    - apply Memory.NM.Raw.BSLeaf.
    - derive_bst.
    - derive_bst.
  Qed.

  Definition x_mem : memoryH := Memory.NM.Bst x_mem_tree_is_bst.
  Definition y_mem : memoryH := Memory.NM.Bst y_mem_tree_is_bst.

  Lemma x_y_mem_equiv: x_mem = y_mem.
  Proof.
    intro k.
    destruct k.
    - cbn.
      constructor.
      apply x_y_mb_equiv.
    - reflexivity.
  Qed.

  Definition t_itree : itree Event bool.
    constructor.
    eapply VisF.
    - left.
      apply (MemLU "" 0).
    - intro m.
      constructor.
      apply RetF.
      destruct m as [m _].    
      destruct m eqn:E.
      + apply false.
      + destruct (Nat.eq_dec k 2).
        * apply true.
        * apply false.
  Defined.

  Lemma interp_Mem_equiv_proper_False:
    ~ (∀ (A : Type) (e : Equiv A), Equivalence e →
      Proper (eutt e ==> equiv ==> eutt equiv) interp_Mem).
  Proof.
    intro H.
    unfold Proper, respectful in H.
    specialize (H bool eq eq_equivalence).
    specialize (H t_itree t_itree (reflexivity t_itree)).
    specialize (H x_mem y_mem x_y_mem_equiv).
    unfold t_itree in H.
    pose proof interp_Mem_MemLU_vis as Hmlu.
    unfold subevent, resum, ReSum_inl, cat,
           Cat_IFun, resum, ReSum_id, inl_,
           Inl_sum1, id_, Id_IFun in Hmlu.
    rewrite 2 Hmlu in H.
    2, 3: reflexivity.
    rewrite 2 interp_Mem_ret in H.
    apply eutt_Ret in H.
    destruct H as [H1 H2].
    cbn in H1, H2.
    discriminate H2.
  Qed.

  Fact falseness: False.
  Proof.
    apply interp_Mem_equiv_proper_False.
    intros.
    apply interp_Mem_equiv_proper.
  Qed.

End interp_Mem_equiv_proper_False.
