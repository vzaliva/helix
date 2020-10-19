Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.
Require Import Helix.LLVMGen.Correctness_MExpr.
Require Import Helix.LLVMGen.IdLemmas.
Require Import Helix.LLVMGen.StateCounters.
Require Import Helix.LLVMGen.VariableBinding.
Require Import Helix.LLVMGen.StateInvariant.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Global Opaque resolve_PVar.

Axiom int_eq_inv: forall a b, Int64.intval a ≡ Int64.intval b -> a ≡ b.

  Section GenIR.


  (* The result is a branch *)
  Definition branches (to : block_id) (mh : memoryH * ()) (c : config_cfg_T (block_id * block_id + uvalue)) : Prop :=
    match c with
    | (m,(l,(g,res))) => exists from, res ≡ inl (from, to)
    end.

  Definition GenIR_Rel σ (s1 s2 : IRState) (l : local_env) to : Rel_cfg_T unit ((block_id * block_id) + uvalue) :=
    lift_Rel_cfg (new_state_invariant σ s1 s2 l) ⩕ branches to. 

  Definition GenIR_Rel' σ (s : IRState) to : Rel_cfg_T unit ((block_id * block_id) + uvalue) :=
    lift_Rel_cfg (state_invariant σ s) ⩕ branches to. 


  Hint Resolve state_invariant_incBlockNamed : state_invariant.
  Hint Resolve state_invariant_incLocal : state_invariant.
  Hint Resolve state_invariant_incVoid : state_invariant.

  Lemma state_invariant_genNExpr :
    forall exp s1 s2 e c σ memH conf,
      genNExpr exp s1 ≡ inr (s2, (e, c)) ->
      state_invariant σ s1 memH conf ->
      state_invariant σ s2 memH conf.
  Proof.
    intros exp; induction exp;
      intros * GEN SINV;
      cbn in GEN; simp; eauto with state_invariant.
    - destruct (nth_error (Γ s1) v); cbn in *; inversion Heqs; subst;
        eauto with state_invariant.
    - destruct (nth_error (Γ s1) v); cbn in *; inversion Heqs; subst;
        eauto with state_invariant.
  Qed.

  Hint Resolve state_invariant_genNExpr : state_invariant.

  Tactic Notation "state_inv_auto" := eauto with state_invariant.

  (* TODO: Move this, and remove Transparent / Opaque *)
  Lemma incLocal_unfold :
    forall s,
      incLocal s ≡ inr
               ({|
                   block_count := block_count s;
                   local_count := S (local_count s);
                   void_count := void_count s;
                   Γ := Γ s
                 |}
                , Name ("l" @@ string_of_nat (local_count s))).
  Proof.
    intros s.
    Transparent incLocal.
    cbn.
    reflexivity.
    Opaque incLocal.
  Qed.

  (* TODO: Move this, and remove Transparent / Opaque *)
  Lemma incVoid_unfold :
    forall s,
      incVoid s ≡ inr
               ({|
                   block_count := block_count s;
                   local_count := local_count s;
                   void_count := S (void_count s);
                   Γ := Γ s
                 |}
                , Z.of_nat (void_count s)).
  Proof.
    intros s.
    Transparent incVoid.
    cbn.
    reflexivity.
    Opaque incVoid.
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

  Lemma genMExpr_context :
    forall mexp s1 s2 e c,
      genMExpr mexp s1 ≡ inr (s2, (e,c)) ->
      Γ s1 ≡ Γ s2.
  Proof.
    induction mexp;
      intros s1 s2 e c GEN;
      cbn in GEN; simp;
        repeat
          match goal with
          | H: ErrorWithState.option2errS _ (nth_error (Γ ?s1) ?n) ?s1 ≡ inr (?s2, _) |- _ =>
            destruct (nth_error (Γ s1) n); inversion H; subst
          | H: incLocal ?s1 ≡ inr (?s2, _) |- _ =>
            rewrite incLocal_unfold in H; cbn in H; inversion H; cbn; auto
          | IH: ∀ (s1 s2 : IRState) (e : exp typ) (c : code typ), genMExpr ?nexp s1 ≡ inr (s2, (e, c)) → Γ s1 ≡ Γ s2,
      GEN: genMExpr ?nexp _ ≡ inr _ |- _ =>
    rewrite (IH _ _ _ _ GEN)
    end; auto.
  Qed.

  Hint Resolve genNExpr_context : helix_context.
  Hint Resolve genMExpr_context : helix_context.
  Hint Resolve incVoid_Γ        : helix_context.
  Hint Resolve incLocal_Γ       : helix_context.
  Hint Resolve incBlockNamed_Γ  : helix_context.

  Lemma genAExpr_context :
    forall aexp s1 s2 e c,
      genAExpr aexp s1 ≡ inr (s2, (e,c)) ->
      Γ s1 ≡ Γ s2.
  Proof.
    induction aexp;
      intros s1 s2 e c GEN;
      cbn in GEN; simp;
        repeat
          match goal with
          | H: ErrorWithState.option2errS _ (nth_error (Γ ?s1) ?n) ?s1 ≡ inr (?s2, _) |- _ =>
            destruct (nth_error (Γ s1) n); inversion H; subst
          | H: incLocal ?s1 ≡ inr (?s2, _) |- _ =>
            rewrite incLocal_unfold in H; cbn in H; inversion H; cbn; auto
          | H: incVoid ?s1 ≡ inr (?s2, _) |- _ =>
            rewrite incVoid_unfold in H; cbn in H; inversion H; cbn; auto
          | IH: ∀ (s1 s2 : IRState) (e : exp typ) (c : code typ), genAExpr ?aexp s1 ≡ inr (s2, (e, c)) → Γ s1 ≡ Γ s2,
      GEN: genAExpr ?aexp _ ≡ inr _ |- _ =>
    rewrite (IH _ _ _ _ GEN)
  | GEN: genNExpr _ _ ≡ inr _ |- _ =>
    rewrite (genNExpr_context _ _ GEN)
  | GEN: genMExpr _ _ ≡ inr _ |- _ =>
    rewrite (genMExpr_context _ _ GEN)
    end; subst; auto.
  Qed.

  Lemma genNExpr_local_count :
    forall nexp s1 s2 e c,
      genNExpr nexp s1 ≡ inr (s2, (e, c)) ->
      (local_count s2 >= local_count s1)%nat.
  Proof.
    induction nexp;
      intros s1 s2 e c GEN;
      cbn in GEN; simp;
        repeat
          match goal with
          | H: ErrorWithState.option2errS _ (nth_error (Γ ?s1) ?n) ?s1 ≡ inr (?s2, _) |- _ =>
            destruct (nth_error (Γ s1) n) eqn:FIND; inversion H; subst
          | H : incLocal ?s1 ≡ inr (?s2, _) |- _ =>
            apply incLocal_local_count in H
          | IH : ∀ (s1 s2 : IRState) (e : exp typ) (c : code typ),
              genNExpr ?n s1 ≡ inr (s2, (e, c)) → local_count s2 ≥ local_count s1,
      GEN: genNExpr ?n _ ≡ inr _ |- _ =>
    apply IH in GEN
    end;
      try lia.
  Qed.

  Lemma genMExpr_local_count :
    forall mexp s1 s2 e c,
      genMExpr mexp s1 ≡ inr (s2, (e, c)) ->
      (local_count s2 >= local_count s1)%nat.
  Proof.
    induction mexp;
      intros s1 s2 e c GEN;
      cbn in GEN; simp;
        repeat
          match goal with
          | H: ErrorWithState.option2errS _ (nth_error (Γ ?s1) ?n) ?s1 ≡ inr (?s2, _) |- _ =>
            destruct (nth_error (Γ s1) n) eqn:FIND; inversion H; subst
          | H : incLocal ?s1 ≡ inr (?s2, _) |- _ =>
            apply incLocal_local_count in H
          | IH : ∀ (s1 s2 : IRState) (e : exp typ) (c : code typ),
              genMExpr ?n s1 ≡ inr (s2, (e, c)) → local_count s2 ≥ local_count s1,
      GEN: genMExpr ?n _ ≡ inr _ |- _ =>
    apply IH in GEN
    end;
      try lia.
  Qed.

  Lemma genAExpr_local_count :
    forall aexp s1 s2 e c,
      genAExpr aexp s1 ≡ inr (s2, (e, c)) ->
      (local_count s2 >= local_count s1)%nat.
  Proof.
    induction aexp;
      intros s1 s2 e c GEN;
      cbn in GEN; simp;
        repeat
          match goal with
          | H: ErrorWithState.option2errS _ (nth_error (Γ ?s1) ?n) ?s1 ≡ inr (?s2, _) |- _ =>
            destruct (nth_error (Γ s1) n) eqn:FIND; inversion H; subst
          | H : incLocal ?s1 ≡ inr (?s2, _) |- _ =>
            apply incLocal_local_count in H
          | H : incVoid ?s1 ≡ inr (?s2, _) |- _ =>
            apply incVoid_local_count in H
          | GEN : genNExpr _ _ ≡ inr _ |- _ =>
            apply genNExpr_local_count in GEN
          | GEN : genMExpr _ _ ≡ inr _ |- _ =>
            apply genMExpr_local_count in GEN
          | IH : ∀ (s1 s2 : IRState) (e : exp typ) (c : code typ),
              genAExpr ?a s1 ≡ inr _ → local_count s2 ≥ local_count s1,
      GEN : genAExpr ?a _ ≡ inr _ |- _ =>
    apply IH in GEN
    end; try lia.
  Qed.

  Lemma genIR_local_count :
    forall op s1 s2 nextblock b bk_op,
      genIR op nextblock s1 ≡ inr (s2, (b, bk_op)) ->
      local_count s2 ≥ local_count s1.
  Proof.
    induction op;
      intros s1 s2 nextblock b bk_op H;
      cbn in H; simp;
        repeat
          (match goal with
           | H: inl _ ≡ inr _ |- _ =>
             inversion H
           | H: ErrorWithState.option2errS _ (nth_error (Γ ?s1) ?n) ?s1 ≡ inr (?s2, _) |- _ =>
             destruct (nth_error (Γ s1) n) eqn:?; inversion H; subst
           | H : ErrorWithState.err2errS (MInt64asNT.from_nat ?n) ?s1 ≡ inr (?s2, _) |- _ =>
             destruct (MInt64asNT.from_nat n) eqn:?; inversion H; subst
           | H : incLocal ?s1 ≡ inr (?s2, _) |- _ =>
             apply incLocal_local_count in H
           | H : incVoid ?s1 ≡ inr (?s2, _) |- _ =>
             apply incVoid_local_count in H
           | H : incBlockNamed _ _ ≡ inr _ |- _ =>
             apply incBlockNamed_local_count in H
           | H : incBlock _ ≡ inr _ |- _ =>
             apply incBlockNamed_local_count in H
           | H : resolve_PVar _ _ ≡ inr _ |- _ =>
             apply resolve_PVar_state in H; subst
           | GEN : genNExpr _ _ ≡ inr _ |- _ =>
             apply genNExpr_local_count in GEN
           | GEN : genMExpr _ _ ≡ inr _ |- _ =>
             apply genMExpr_local_count in GEN
           | GEN : genAExpr _ _ ≡ inr _ |- _ =>
             apply genAExpr_local_count in GEN
           | IH : ∀ (s1 s2 : IRState) (nextblock b : block_id) (bk_op : list (LLVMAst.block typ)),
               genIR ?op nextblock s1 ≡ inr (s2, (b, bk_op)) → local_count s2 ≥ local_count s1,
             GEN: genIR ?op _ _ ≡ inr _ |- _ =>
             apply IH in GEN
           end; cbn in *);
           try lia.
  Qed.

  Ltac subst_contexts :=
    repeat match goal with
           | H : Γ ?s1 ≡ Γ ?s2 |- _ =>
             rewrite H in *; clear H
           end.

  Lemma genIR_Context:
    ∀ (op : DSHOperator) (s1 s2 : IRState) (nextblock b : block_id) (bk_op : list (LLVMAst.block typ)),
      genIR op nextblock s1 ≡ inr (s2, (b, bk_op)) →
      Γ s1 ≡ Γ s2.
  Proof.
    induction op;
      intros s1 s2 nextblock b bk_op H;
      cbn in H; simp;
        repeat
          (match goal with
           | H : ErrorWithState.err2errS (MInt64asNT.from_nat ?n) ?s1 ≡ inr (?s2, _) |- _ =>
             destruct (MInt64asNT.from_nat n); inversion H; subst
           | H: _ :: Γ ?s1 ≡ Γ ?s2,
                R: Γ ?s2 ≡ _ |- _ =>
             rewrite <- H in R; inversion R; subst
           | H: _ :: _ :: Γ ?s1 ≡ Γ ?s2,
                R: Γ ?s2 ≡ _ |- _ =>
             rewrite <- H in R; inversion R; subst
           | H: _ :: _ :: _ :: Γ ?s1 ≡ Γ ?s2,
                R: Γ ?s2 ≡ _ |- _ =>
             rewrite <- H in R; inversion R; subst
           | H: inl _ ≡ inr _ |- _ =>
             inversion H
           | H: inr (?i1, Γ ?s1) ≡ inr (?i2, Γ ?s2) |- _ =>
             inversion H; clear H
           | RES : resolve_PVar ?p ?s1 ≡ inr (?s2, ?x) |- _ =>
             rewrite <- (@resolve_PVar_state p s1 s2 x RES) in *
           | H: incBlockNamed _ _ ≡ inr _ |- _ =>
             apply incBlockNamed_Γ in H
           | H: incLocal _ ≡ inr _ |- _ =>
             apply incLocal_Γ in H
           | H: incVoid _ ≡ inr _ |- _ =>
             apply incVoid_Γ in H
           | GEN: genNExpr _ _ ≡ inr _ |- _ =>
             apply genNExpr_context in GEN; cbn in GEN; inversion GEN; subst
           | GEN: genMExpr _ _ ≡ inr _ |- _ =>
             apply genMExpr_context in GEN; cbn in GEN; inversion GEN; subst
           | GEN: genAExpr _ _ ≡ inr _ |- _ =>
             apply genAExpr_context in GEN; cbn in GEN; inversion GEN; subst
           | GEN : genIR ?op ?b ?s1 ≡ inr _ |- _ =>
             apply IHop in GEN; cbn in GEN; eauto
           end; cbn in *; subst);
        subst_contexts;
        auto.
    - inversion Heqs; subst.
      apply incBlockNamed_Γ in Heqs3.
      subst_contexts.
      rewrite <- Heqs0 in Heql1.
      inversion Heql1.
      reflexivity.
    - eapply IHop1 in Heqs2; eauto.
      eapply IHop2 in Heqs0; eauto.
      subst_contexts.
      reflexivity.
  Qed.

  (* TODO: Move *)
  Lemma add_comment_eutt :
    forall comments bks ids,
      denote_bks (convert_typ [] (add_comment bks comments)) ids ≈ denote_bks (convert_typ [] bks) ids.
  Proof.
    intros comments bks ids.
    induction bks.
    - cbn. reflexivity.
    - cbn.
      destruct ids as (bid_from, bid_src); cbn.
      match goal with
      | |- context[denote_bks ?bks (_, ?bid_src)] =>
        destruct (find_block dtyp bks bid_src) eqn:FIND
      end.
  Admitted.

  (* TODO: Move *)
  (* Could probably have something more general... *)
  Lemma add_comments_eutt :
    forall bk comments bids,
      denote_bks
        [fmap (typ_to_dtyp [ ]) (add_comments bk comments)] bids ≈ denote_bks [fmap (typ_to_dtyp [ ]) bk] bids.
  Proof.
    intros bk comments bids.
  Admitted.

  (* TODO: Move *)
  Lemma convert_typ_block_app : forall (a b : list (LLVMAst.block typ)) env, (convert_typ env (a ++ b) ≡ convert_typ env a ++ convert_typ env b)%list.
  Proof.
    induction a as [| [] a IH]; cbn; intros; auto.
    rewrite IH; reflexivity.
  Qed.

  Lemma assert_NT_lt_success :
    forall {s1 s2 x y v},
      assert_NT_lt s1 x y ≡ inr v ->
      assert_NT_lt s2 x y ≡ inr v.
  Proof.
    intros s1 s2 x y v H.
    unfold assert_NT_lt in *.
    destruct ((MInt64asNT.to_nat x <? MInt64asNT.to_nat y)%nat); inversion H.
    cbn in *. subst.
    auto.
  Qed.

  (* TODO: move, add a file for disjoint list stuff? *)
  Lemma Forall_disjoint :
    forall {A} (l1 l2 : list A) (P1 P2 : A -> Prop),
      Forall P1 l1 ->
      Forall P2 l2 ->
      (forall x, P1 x -> ~(P2 x)) ->
      l1 ⊍ l2.
  Proof.
    induction l1;
      intros l2 P1 P2 L1 L2 P1NP2.
    - intros ? ? CONTRA. inversion CONTRA.
    - apply Coqlib.list_disjoint_cons_l.
      + eapply IHl1; eauto using Forall_inv_tail.
      + apply Forall_inv in L1.
        apply P1NP2 in L1.
        intros IN.
        eapply Forall_forall in L2; eauto.
  Qed.

  Lemma no_failure_helix_LU : forall {E X} s a (k : _ -> itree _ X) m,
      no_failure (E := E) (interp_helix (ITree.bind (trigger (MemLU s a)) k) m) ->
      exists v,
        no_failure (E := E) (interp_helix (k v) m) /\ memory_lookup m a ≡ Some v.
  Proof.
    intros * NOFAIL.
    rewrite interp_helix_bind in NOFAIL.
    Transparent interp_helix interp_Mem.
    unfold interp_helix in NOFAIL.
    unfold interp_Mem in NOFAIL.
    rewrite interp_state_trigger in NOFAIL.
    cbn* in *.
    simp.
    - unfold throw in *.
      rewrite interp_fail_vis in NOFAIL.
      cbn in *.
      rewrite bind_ret_l, translate_ret, bind_ret_l in NOFAIL.
      apply eutt_Ret in NOFAIL; contradiction NOFAIL; auto.
    - rewrite interp_fail_ret in NOFAIL.
      cbn in *; rewrite translate_ret, bind_ret_l in NOFAIL.
      eexists; split; eauto.
  Qed.
  Opaque interp_helix interp_Mem.

  Import ProofMode.
  Notation "'gep' τ e" := (OP_GetElementPtr τ e) (at level 10, only printing).
  Notation "'double'" := (DTYPE_Double) (at level 10, only printing).
  Notation "'arr'" := (DTYPE_Array) (at level 10, only printing).
  Notation "'to_nat'" := (MInt64asNT.to_nat) (only printing).

  Variant hidden_cont  (T: Type) : Type := boxh_cont (t: T).
  Variant visible_cont (T: Type) : Type := boxv_cont (t: T).
  Ltac hide_cont :=
    match goal with
    | h : visible_cont _ |- _ =>
      let EQ := fresh "HK" in
      destruct h as [EQ];
      apply boxh_cont in EQ
    | |- context[ITree.bind _ ?k] =>
      remember k as K eqn:VK;
      apply boxh_cont in VK
    end.
  Ltac show_cont :=
    match goal with
    | h: hidden_cont _ |- _ =>
      let EQ := fresh "VK" in
      destruct h as [EQ];
      apply boxv_cont in EQ
    end.
  Notation "'hidden' K" := (hidden_cont (K ≡ _)) (only printing, at level 10).
  Ltac subst_cont :=
    match goal with
    | h: hidden_cont _ |- _ =>
      destruct h; subst
    | h: visible_cont _ |- _ =>
      destruct h; subst
    end.
  
  Lemma compile_FSHCOL_correct :
    forall (** Compiler bits *) (s1 s2: IRState)
      (** Helix bits    *) (op: DSHOperator) (σ : evalContext) (memH : memoryH) 
      (** Vellvm bits   *) (nextblock bid_in bid_from : block_id) (bks : list (LLVMAst.block typ))
      (* (env : list (ident * typ)) *)  (g : global_env) (ρ : local_env) (memV : memoryV),
      bid_bound s1 nextblock ->
      GenIR_Rel σ s1 s1 ρ bid_in (memH,tt) (memV, (ρ, (g, (inl (bid_from, bid_in))))) ->
      no_failure (E := E_cfg) (interp_helix (denoteDSHOperator σ op) memH) -> (* Evaluation succeeds *)
      genIR op nextblock s1 ≡ inr (s2,(bid_in,bks)) ->
      eutt (succ_cfg (GenIR_Rel σ s1 s2 ρ nextblock))
           (interp_helix (denoteDSHOperator σ op) memH)
           (interp_cfg (D.denote_bks (convert_typ [] bks) (bid_from,bid_in))
                       g ρ memV).
  Proof.
    intros s1 s2 op; revert s1 s2; induction op; intros * NEXT BISIM NOFAIL GEN.
    - cbn* in *.
      simp.
      cbn*.
      hvred.
      vjmp.
      (* TODO :( *)
      unfold fmap, Fmap_block; cbn.
      vred.
      vred.
      vred.
      vred.

      rewrite denote_bks_unfold_not_in; cycle 1.
      {
        (* TODO: auto and part of vjmp_out *)
        rewrite find_block_ineq; [apply find_block_nil | cbn].

        assert (nextblock ≢ bid_in).
        {
          (* TODO: pull this out into automation *)
          eapply bid_bound_fresh; eauto.
          eapply bid_bound_bound_between; eauto.

          match goal with
          | H: incBlockNamed ?msg ?s1 ≡ inr (_, ?bid) |-
            bid_bound ?s2 bid_in =>
            idtac H
          end.
          eapply bid_bound_incBlockNamed; eauto;
            solve_not_ends_with.
          solve_not_bid_bound.
          block_count_replace. lia.
          solve_not_ends_with.
        }
        auto.
      }
      vred.

      apply eutt_Ret; auto.
      destruct BISIM as (STATE & (from & BRANCH)).
      cbn in STATE, BRANCH.
      split; cbn; eauto.

      (* I have:

         new_state_invariant σ s1 s1 ρ memH (memV, (ρ, g))

         But now I have a new state that is the result of doing
         incVoid / incBlockNamed etc, and I want to know that my new
         state has a valid state invariant as well.

         new_state_invariant σ s1 s2 ρ memH (memV, (ρ, g))

         But, my state invariant is not actually strong enough to
         conclude this alone, because I don't have a high water mark.

       *)

      (* TODO *)
      (* This should actually hold here because the local_count does
      not change, so after unfolding new_state_invariant it should be
      the same as STATE *)


      (* YZ TODO: move to prelude *)
      Ltac solve_state_invariant :=
        cbn;
        match goal with
          |- state_invariant _ _ _ _ =>
          first [eassumption |
                 eapply state_invariant_add_fresh; [eassumption | solve_state_invariant] |
                 eapply state_invariant_incVoid; [eassumption | solve_state_invariant] |
                 eapply state_invariant_incBlockNamed; [eassumption | solve_state_invariant]
                ]
        end.

      admit. (* solve_state_invariant. *)
    - (* ** DSHAssign (x_p, src_e) (y_p, dst_e):
         Helix side:
         1. x_i <- evalPExpr σ x_p ;;
         2. y_i <- evalPExpr σ y_p ;;
         3. x <- memory_lookup_err "Error looking up 'x' in DSHAssign" mem x_i ;;
         4. y <- memory_lookup_err "Error looking up 'y' in DSHAssign" mem y_i ;;
         5. src <- evalNExpr σ src_e ;;
         6. dst <- evalNExpr σ dst_e ;;
         7. v <- mem_lookup_err "Error looking up 'v' in DSHAssign" (to_nat src) x ;;
         8. ret (memory_set mem y_i (mem_add (to_nat dst) v y))

         Vellm side:
         src_nexpcode ++
         dst_nexpcode ++
         px <- gep "src_p"[src_nexpr] ;;
         v  <- load px ;;
         py <- gep "dst_p"[dst_nexpr] ;;
         store v py
       *)
      destruct BISIM as [BISIM1 [_bid EQ]]; inv EQ.
      cbn* in *; simp.
      hide_cfg.
      inv_resolve_PVar Heqs0.
      inv_resolve_PVar Heqs1.
      unfold denotePExpr in *; cbn* in *.
      simp. Time all:try_abs.
      all: apply no_failure_Ret in NOFAIL; try_abs.
      clean_goal.
      repeat apply no_failure_Ret in NOFAIL.
      edestruct @no_failure_helix_LU as (? & NOFAIL' & ?); eauto; []; clear NOFAIL; rename NOFAIL' into NOFAIL; cbn in NOFAIL; eauto.
      edestruct @no_failure_helix_LU as (? & NOFAIL' & ?); eauto; []; clear NOFAIL; rename NOFAIL' into NOFAIL; cbn in NOFAIL; eauto.
      rename s1 into si, s2 into sf,
      i5 into s1, i6 into s2,
      i8 into s3, i10 into s4,
      i11 into s5, i12 into s6,
      i13 into s7.
      rename n1 into x_p, n2 into y_p.
      rename a into x_i, a0 into y_i.
      rename x0 into y.
      clean_goal.

      hred.
      hstep; [eauto |].
      hred; hstep; [eauto |].
      hred.

      subst; eutt_hide_left.
      vjmp.
      unfold fmap, Fmap_block; cbn.
      vred.
      vred.
      vred.

      (* Step 5. *)
      subst; eapply eutt_clo_bind_returns; [eapply genNExpr_correct_ind |..]; eauto.
      eauto 7 with state_invariant.
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      cbn in PRE; destruct PRE as (INV1 & EXP1 & ?); cbn in *; inv_eqs.
      hvred.

      (* Step 6. *)
      eapply eutt_clo_bind_returns; [eapply genNExpr_correct_ind |..]; eauto.
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      cbn in PRE; destruct PRE as (INV2 & EXP2 & ?); cbn in *; inv_eqs.
      hvred.
      break_inner_match_hyp; break_inner_match_hyp; try_abs.
      2: apply no_failure_Ret in NOFAIL; try_abs.
      destruct_unit.

      rename vH into src, vH0 into dst, b into v.
      clean_goal.
      (* Step 7. *)
      hvred.
      hstep.
      unfold assert_NT_lt,assert_true_to_err in *; simp.
      hide_cont.
      clear NOFAIL.
      rename i1 into vsz.
      rename i0 into vx_p, i3 into vy_p.
      rename e into esrc.
      clean_goal.

      (* Question 1: is [vx_p] global, local, or can be either? *)
      (* We access in memory vx_p[e] *)
      edestruct memory_invariant_Ptr as (membk & ptr & LU & INLG & GETCELL); [| eauto | eauto |]; eauto.
      rewrite LU in H; symmetry in H; inv H.
      specialize (GETCELL _ _ Heqo1).
      clean_goal.
      (* I find some pointer either in the local or global environment *)
      destruct vx_p as [vx_p | vx_p]; cbn in INLG.
      {
        edestruct denote_instr_gep_array as (ptr' & READ & EQ); cycle -1; [rewrite EQ; clear EQ | ..]; cycle 1.
        3:apply GETCELL.
        { vstep; solve_lu; reflexivity. }
        { rewrite EXP1; auto.
          Set Printing Implicit.
          cbn. 
          (* replace (repr (Z.of_nat (MInt64asNT.to_nat src))) with src by admit. *)
          (* reflexivity. *)
          admit.
        }
        clear EXP1.
        clean_goal.
          
        subst_cont; vred.
        vred.
        (* load *)
        vstep.
        { vstep; solve_lu. }
        vred.
        hide_cont.
        (* destruct vy_p as [vy_p | vy_p]. *)
        (* {  *)
        (*   edestruct memory_invariant_Ptr as (ymembk & yptr & yLU & yINLG & yGETCELL); [| eapply Heqo0 | eapply LUn0 |]; [solve_state_invariant |]. *)
        (*   clean_goal. *)
        (*   rewrite yLU in H0; symmetry in H0; inv H0. *)
        (*   cbn in yINLG. *)
        (*   (* How do we know that ymembk is allocated? *)
        (*      yGETCELL does not contain any information here. *)
        (*    *) *)
        (*   (* Oooh we don't, we're using [gep] but not for reading a cell here? *)
        (*      Not true though, the cell must be allocated, we are about to write in it. *)
        (*      We need another lemma about [OP_GetElementPtr] then. *)
        (*    *) *)
        (*   (* edestruct denote_instr_gep_array as (yptr' & yREAD & yEQ); cycle -1; [rewrite yEQ; clear yEQ | ..]; cycle 1. *) *)
        (*   (* { vstep; solve_lu. *) *)
        (*   (*   cbn; reflexivity. *) *)
        (*   (* } *) *)
        (*   (* { rewrite EXP2. *) *)
        (*   (*   2:{ cbn. etransitivity. apply sub_alist_add. *) *)
        (*   (*       2: apply sub_alist_add. *) *)
        (*   (*       admit. admit. *) *)
        (*   (*   } *) *)
        (*   (*   replace (repr (Z.of_nat (MInt64asNT.to_nat dst))) with dst by admit. *) *)
        (*   (*   cbn; reflexivity. *) *)

        (*   (* } *) *)
        (*   (* eapply yGETCELL. *) *)
        admit. }
      admit.
>>>>>>> master
    -
      Opaque genWhileLoop.
      cbn* in *.
      simp.
      unfold denotePExpr in *; cbn* in *.
      simp; try now (exfalso; clear -NOFAIL; try apply no_failure_Ret in NOFAIL; try_abs).
      apply no_failure_Ret in NOFAIL; simp; cbn in *; try_abs.

      hide_strings'.
      inv_resolve_PVar Heqs0.
      inv_resolve_PVar Heqs1.
      cbn* in *.
      simp.

      eutt_hide_right.
      repeat apply no_failure_Ret in NOFAIL.
      repeat (edestruct @no_failure_helix_LU as (? & NOFAIL' & ?); eauto; []; clear NOFAIL; rename NOFAIL' into NOFAIL; cbn in NOFAIL; eauto). 

      rauto:L.
      all:eauto.
      Ltac rewrite_nth_error :=
        match goal with
        | h: nth_error _ _ ≡ _ |- _ => rewrite h
        end.

      Ltac rewrite_memory_lookup :=
        match goal with
        | h: memory_lookup _ _ ≡ _ |- _ => rewrite h
        end.


      subst; eutt_hide_left.
      Transparent genWhileLoop.
      cbn in *.
      simp.
      cbn in *.
      unfold add_comments; cbn.
      repeat rewrite fmap_list_app.
      cbn.


      match goal with
        |- context[denote_bks ?x] =>
        remember x as bks
      end.

(*
      erewrite denote_bks_unfold.
      2:{
        subst; cbn.
        clear.
        destruct (Eqv.eqv_dec_p bid_in bid_in) as [foo | foo].
        reflexivity.
        exfalso; apply foo; reflexivity.
      }

      Opaque find_block.

      cbn.
      norm_v.
      unfold IntType; rewrite typ_to_dtyp_I.
      cbn.
      focus_single_step_v; norm_v.
      cbn; norm_v.
      subst.
      norm_v.
      focus_single_step_v; norm_v.
      rewrite interp_cfg_to_L3_LW.
      cbn; norm_v.
      unfold endo.
      subst.
      repeat (norm_v; []).
      focus_single_step_v.
      (* onAllHyps move_up_types. *)
      unfold endo.
      focus_single_step_v.
      norm_v.
      2: apply lookup_alist_add_eq.
      cbn; norm_v.
      subst; cbn; norm_v.
      focus_single_step_v.

      (* Case analysis on whether we ever enter the loop or not *)
      unfold eval_int_icmp.
      cbn.
      break_match_goal.
      -- (* We enter the loop *)
        cbn; norm_v.
        subst; cbn; norm_v.

        rewrite find_block_ineq, find_block_eq.
        2: reflexivity.
        2:cbn; admit.

        norm_v.
        (* loopblock  *)
        rewrite denote_bks_unfold.
        2:{
          cbn.
          match goal with
            |- context[if ?p then true else false] =>
            destruct p as [EQ | INEQ]
          end.
          admit.
          match goal with
            |- context[if ?p then true else false] =>
            destruct p as [?EQ | ?INEQ]
          end.
          reflexivity.
          admit.
        }
*)
      (* Need to denote phis, I cannot denote the block directly :( *)

        admit.

      (* -- *)
      (*   (* from == to, we go from the entry block to the next one directly *) *)
      (*   cbn. *)
      (*   norm_v. *)
      (*   subst; cbn; norm_v. *)

      (*   repeat rewrite find_block_ineq. *)
      (*   2,3,4,5: cbn; admit. *)
      (*   cbn. *)
      (*   rewrite find_block_nil. *)

      (*   cbn; norm_v. *)
      (*   assert (n ≡ 0) by admit. *)

      (*   subst. *)
      (*   cbn; norm_h. *)
      (*   rewrite interp_Mem_MemSet. *)
      (*   norm_h. *)

      (*   apply eutt_Ret. *)
      (*   split; eauto. *)
      (*   { *)
      (*     admit. *)
      (*   } *)
      (*   { *)
      (*     admit. *)
      (*   } *)

    - (* DSHBinOp *)
      cbn* in *.
      simp.
      inv_resolve_PVar Heqs1.
      inv_resolve_PVar Heqs2.

      (* On the Helix side, the computation consists in:
         1. xi <- denotePExpr x
         2. yi <- denotePExpr y
         3. lookup xi in memory
         4. lookup yi in memory
         5. denoteDSHBinop on the values read
         6. write the result in memory at yi
       *)
      eutt_hide_right.
      rauto:L.

      subst; eutt_hide_left.

      unfold add_comments.
      cbn.
      match goal with
        |- context[denote_bks ?x] =>
        remember x as bks
      end.

      (* Lemma about while loop instead *)
      (* erewrite denote_bks_unfold. *)
      (* 2:{ *)
      (*   subst; cbn. *)
      (*   destruct (Eqv.eqv_dec_p bid_in bid_in).  *)
      (*   reflexivity. *)
      (*   exfalso. *)
      (*   apply n0. *)
      (*   reflexivity. *)
      (* } *)
      (* cbn. *)
      (* norm_v. *)
      (* unfold IntType; rewrite typ_to_dtyp_I. *)
      (* cbn. *)
      (* setoid_rewrite bind_ret_l. *)
      (* setoid_rewrite bind_ret_l. *)
      (* cbn. *)
      (* norm_v. *)
      (* rewrite interp_cfg_to_L3_LW. *)
      (* cbn*; norm_v. *)
      (* cbn*; norm_v. *)
      (* 2:{ *)
      (*   cbn. *)
      (*   unfold endo. *)
      (*   rewrite rel_dec_eq_true; eauto; typeclasses eauto. *)
      (* } *)
      (* cbn. *)
      (* unfold endo. *)
      (* unfold eval_int_icmp. *)
      (* cbn. *)

      (* focus_single_step_v. *)

      (* unfold Int64_eq_or_cerr, Z_eq_or_cerr, ErrorWithState.err2errS, Z_eq_or_err, memory_lookup_err in *. *)
      (* cbn* in *. *)
      (* simp. *)
      (* inv_resolve_PVar Heqs0. *)
      (* inv_resolve_PVar Heqs1. *)

      (* onAllHyps move_up_types.  *)

  (*     repeat match goal with *)
  (*            | h : Int64.intval _ ≡ Int64.intval _ |- _ => apply int_eq_inv in h; subst *)
  (*            end. *)

  (*     eutt_hide_left. *)
  (*     focus_single_step_v. *)
  (*     unfold MInt64asNT.from_nat in *. *)

  (*     rename n into index1. *)
  (*     break_if. *)
  (*     { *)
  (*       cbn. *)
  (*       norm_v. *)
  (*       subst. *)
  (*       cbn. *)
  (*       norm_v. *)

      admit.
    - (* DSHMemMap2 *) admit.
    - (* DSHPower *) admit.
    - (* DSHLoop *) admit.
    - (* DSHAlloc *) admit.
    - (* DSHMemInit *) admit.
    - (* DSHSeq *)
      cbn.

      pose proof GEN as GEN_DESTRUCT.
      cbn in GEN_DESTRUCT; simp.

      rename i into s_op1.
      rename l0 into bk_op1.
      rename l into bk_op2.

      rename b into op2_entry.
      rename bid_in into op1_entry.

      rename Heqs0 into GEN_OP2.
      rename Heqs2 into GEN_OP1.
      rewrite add_comment_eutt.
      cbn.

      rewrite convert_typ_block_app.
      rewrite denote_bks_app; eauto.
      2: {
        unfold no_reentrance.
        pose proof GEN_OP1 as GEN_OP1'.

        apply (inputs_not_earlier_bound _ _ _ NEXT) in GEN_OP1'.
        apply inputs_bound_between in GEN_OP1.
        apply outputs_bound_between in GEN_OP2.

        pose proof (Forall_and GEN_OP1 GEN_OP1') as INPUTS.
        cbn in INPUTS.

        eapply (Forall_disjoint GEN_OP2 INPUTS).
        intros x OUT_PRED [IN_BOUND IN_NEXT].
        destruct OUT_PRED as [OUT_PRED | OUT_PRED]; auto.
        eapply (state_bound_between_separate incBlockNamed_count_gen_injective OUT_PRED IN_BOUND).
        lia. auto.
        block_count_replace.
        lia.
      }

      rauto.

      (* Helix generates code for op2 *first*, so op2 gets earlier
        variables from the irstate. Helix needs to do this because it
        passes the block id for the next block that an operator should
        jump to when it's done executing... So it generates code for
        op2, which goes to the next block of the entire sequence, and
        then passes the entry point for op2 as the "nextblock" for
        op1.
      *)
      cbn in NOFAIL.
      pose proof BISIM as BISIM2.
      destruct BISIM as [SINV (?from & EQ)]; cbn in *; inv EQ.
      simp.

      rename Heqs0 into GEN_OP2.
      rename Heqs1 into GEN_OP1.

      eapply eutt_clo_bind_returns.
      {
        eapply IHop1 with (s1:=s_op1) (s2:=s2).
        - eapply bid_bound_genIR_entry; eauto.
        - split.
          + cbn.
            split.
            * cbn.
              apply genIR_Context in GEN_OP2.
              rewrite <- GEN_OP2.
              apply SINV.
            * eapply WF_IRState_Γ.
              eapply SINV.
              eapply genIR_Context; eauto.
            * apply freshness_ss_ρ.
          + cbn. exists from.
            reflexivity.
        - eapply no_failure_helix_bind_prefix; eauto.
        - auto.
      }

      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      cbn in PRE; destruct PRE as (INV2 & EXP2 & ?); cbn in *; inv_eqs.
      subst...

      eapply eqit_mon; auto.
      2: {
        eapply IHop2; eauto.
        destruct BISIM2 as (SINV2 & BRANCHES2).
        cbn in SINV2, BRANCHES2.
        split.
        - cbn.
          destruct SINV2.
          destruct INV2.
          split; auto.
          + apply genIR_Context in GEN_OP2.
            apply genIR_Context in GEN_OP1.
            unfold memory_invariant.
            subst_contexts.
            apply mem_is_inv1.
          + apply freshness_ss_ρ.
        - cbn. exists EXP2.
          reflexivity.
      }

      intros [[memH1 ?]|] (memV1 & l1 & g1 & res1) PR.
      2: {
        inversion PR.
      }

      destruct res1 as [[from1 next] | v].
      2: {
        destruct PR as [? [? BR]].        
        inversion BR.
      }

      cbn in PR. destruct PR as (SINV1 & BRANCHES1).
      cbn.

      split; auto.
      cbn. cbn in SINV1.
      destruct SINV1 as [MINV1 WF1 FRESH1].
      destruct INV2 as [MINV2 WF2 FRESH2].
      split.
      + cbn.
        apply genIR_Context in GEN_OP1.
        rewrite <- GEN_OP1.
        apply MINV1.
      + auto.
      + eapply freshness_split; eauto.
        apply genIR_local_count in GEN_OP2; lia.
        apply genIR_local_count in GEN_OP1; lia.
  Admitted.
  End GenIR.
 
