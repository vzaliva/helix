Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.
Require Import Helix.LLVMGen.Correctness_MExpr.

Set Implicit Arguments.
Set Strict Implicit.

Lemma resolve_PVar_simple : forall p s s' x v,
    resolve_PVar p s ≡ inr (s', (x, v)) ->
    exists sz n,
      nth_error (Γ s') n ≡ Some (x, TYPE_Pointer (TYPE_Array sz TYPE_Double)) /\
      MInt64asNT.from_Z sz ≡ inr v /\ p ≡ PVar n /\ s ≡ s'.
Proof.
  intros * H.
  unfold resolve_PVar in H.
  cbn* in H.
  simp.
  do 2 eexists; eauto.
Qed.

Ltac inv_resolve_PVar H :=
  apply resolve_PVar_simple in H;
  destruct H as (?sz & ?n & ?LUn & ?EQsz & -> & <-).

Global Opaque resolve_PVar.

Axiom int_eq_inv: forall a b, Int64.intval a ≡ Int64.intval b -> a ≡ b.

  Section GenIR.


  (* The result is a branch *)
  Definition branches (mh : memoryH * ()) (c : config_cfg_T (block_id * block_id + uvalue)) : Prop :=
    match c with
    | (m,(l,(g,res))) => exists bids, res ≡ inl bids
    end.

  Definition GenIR_Rel σ Γ : Rel_cfg_T unit ((block_id * block_id) + uvalue) :=
    lift_Rel_cfg (state_invariant σ Γ) ⩕ branches.


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

  Lemma GenIR_incBlockedNamed :
    forall σ s1 s2 memH memV ρ g bid_from bid_in msg b,
      incBlockNamed msg s1 ≡ inr (s2, b) ->
      GenIR_Rel σ s1 (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))) ->
      GenIR_Rel σ s2 (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))).
  Proof.
    intros * INC [STATE BRANCH].
    split; cbn; state_inv_auto.
  Qed.

  Lemma GenIR_incLocal :
    forall σ s1 s2 memH memV ρ g bid_from bid_in b,
      incLocal s1 ≡ inr (s2, b) ->
      GenIR_Rel σ s1 (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))) ->
      GenIR_Rel σ s2 (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))).
  Proof.
    intros * INC [STATE BRANCH].
    split; cbn; state_inv_auto.
  Qed.

  Lemma GenIR_incVoid :
    forall σ s1 s2 memH memV ρ g bid_from bid_in x,
      incVoid s1 ≡ inr (s2, x) ->
      GenIR_Rel σ s1 (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))) ->
      GenIR_Rel σ s2 (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))).
  Proof.
    intros * INC [STATE BRANCH].
    split; cbn; state_inv_auto.
  Qed.

  Lemma GenIR_genNExpr :
    forall σ s1 s2 memH memV ρ g bid_from bid_in e c exp,
      genNExpr exp s1 ≡ inr (s2, (e, c)) ->
      GenIR_Rel σ s1 (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))) ->
      GenIR_Rel σ s2 (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))).
  Proof.
    intros * INC [STATE BRANCH].
    split; cbn; state_inv_auto.
  Qed.

  Hint Resolve GenIR_incBlockedNamed : GenIR_Rel.
  Hint Resolve GenIR_incLocal : GenIR_Rel.
  Hint Resolve GenIR_incVoid : GenIR_Rel.
  Hint Resolve GenIR_genNExpr : GenIR_Rel.

  Tactic Notation "gen_ir_rel_auto" := eauto with GenIR_Rel.

  Lemma resolve_PVar_state :
    forall p s1 s2 x,
      resolve_PVar p s1 ≡ inr (s2, x) ->
      s1 ≡ s2.
  Proof.
    intros p s1 s2 [x v] H.
    pose proof resolve_PVar_simple p s1 H as H0.
    destruct H0 as (sz & n & H0).
    intuition.
  Qed.

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

  Lemma GenIR_Rel_S_local_count :
    forall σ s memH memV ρ g bid_from bid_in,
      GenIR_Rel σ s (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))) ->
      GenIR_Rel σ {| block_count := block_count s; local_count := S (local_count s); void_count := void_count s; Γ := Γ s |} (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))).
  Proof.
    intros σ s memH memV ρ g bid_from bid_in GEN.
    eapply GenIR_incLocal in GEN; eauto.
    apply incLocal_unfold.
  Qed.

  Lemma GenIR_Rel_S_void_count :
    forall σ s memH memV ρ g bid_from bid_in,
      GenIR_Rel σ s (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))) ->
      GenIR_Rel σ {| block_count := block_count s; local_count := local_count s; void_count := S (void_count s); Γ := Γ s |} (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))).
  Proof.
    intros σ s memH memV ρ g bid_from bid_in GEN.
    eapply GenIR_incVoid in GEN; eauto.
    apply incVoid_unfold.
  Qed.

  Lemma GenIR_Rel_monotone :
    forall σ s memH memV ρ g bid_from bid_in bc lc vc,
      lc ≥ local_count s ->
      GenIR_Rel σ s (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))) ->
      GenIR_Rel σ {| block_count := bc; local_count := lc; void_count := vc; Γ := Γ s |} (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))).
  Proof.
    intros σ s memH memV ρ g bid_from bid_in bc lc vc LC [STATE BRANCH].
    split; cbn in *; auto.
    apply Build_state_invariant;
      try eapply STATE; eauto.

    apply incLocal_is_fresh in STATE.
    unfold concrete_fresh_inv in STATE.
    unfold concrete_fresh_inv.
    intros id v n IN GT.
    cbn in GT.
    eapply STATE; eauto.
    lia.
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
    end;
      try lia.
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

  Ltac solve_gen_ir_rel :=
    repeat
      match goal with
      | GEN : genNExpr ?n ?s1 ≡ inr (?s2, _) |- GenIR_Rel _ ?s2 _ _ =>
        eapply (GenIR_genNExpr _ GEN)
      | LOC : incLocal ?s1 ≡ inr (?s2, _) |- GenIR_Rel _ ?s2 _ _ =>
        eapply (GenIR_incLocal LOC)
      | VOID : incVoid ?s1 ≡ inr (?s2, _) |- GenIR_Rel _ ?s2 _ _ =>
        eapply (GenIR_incVoid VOID)
      | NAMED : incBlockNamed _ ?s1 ≡ inr (?s2, _) |- GenIR_Rel _ ?s2 _ _ =>
        eapply (GenIR_incBlockedNamed NAMED)
      | RES : resolve_PVar ?p ?s1 ≡ inr (?s2, ?x) |- GenIR_Rel _ ?s2 _ _ =>
        rewrite <- (@resolve_PVar_state p s1 s2 x RES)
      | |- GenIR_Rel _ {| block_count := block_count ?s; local_count := S (local_count ?s); void_count := void_count ?s; Γ := Γ ?s |} _ _ =>
        apply GenIR_Rel_S_local_count
      | GEN: genAExpr _
             {|
             block_count := block_count ?s1;
             local_count := local_count ?s1;
             void_count := void_count ?s1;
             Γ := _ :: _ :: Γ ?s1 |} ≡ inr (?s2, _),
        CTX: Γ ?s2 ≡ _ :: _ :: ?l |- _ =>
        rewrite <- (genAExpr_context _ _ GEN) in CTX;
          cbn in CTX; inversion CTX; subst;
            apply genAExpr_local_count in GEN; cbn in GEN;
              apply GenIR_Rel_monotone; auto
      | GEN: genAExpr _
             {|
             block_count := block_count ?s1;
             local_count := local_count ?s1;
             void_count := void_count ?s1;
             Γ := _ :: _ :: _ :: Γ ?s1 |} ≡ inr (?s2, _),
        CTX: Γ ?s2 ≡ _ :: _ :: _ :: ?l |- _ =>
        rewrite <- (genAExpr_context _ _ GEN) in CTX;
          cbn in CTX; inversion CTX; subst;
            apply genAExpr_local_count in GEN; cbn in GEN;
              apply GenIR_Rel_monotone; auto
      end; auto.

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

  Lemma genIR_GenIR_Rel:
    ∀ (op : DSHOperator) (s1 s2 : IRState) (σ : evalContext) (memH : memoryH) (nextblock bid_in bid_from b : block_id) (g : global_env)
      (ρ : local_env) (memV : memoryV) (bk_op : list (LLVMAst.block typ)),
      genIR op nextblock s1 ≡ inr (s2, (b, bk_op)) →
      GenIR_Rel σ s1 (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))) ->
      GenIR_Rel σ s2 (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))).
  Proof.
    induction op;
      intros s1 s2 σ memH nextblock bid_in bid_from g ρ memV s_op1 bk_op GEN BISIM;
      cbn in GEN; simp; eauto with GenIR_Rel;
      repeat (solve_gen_ir_rel;
              match goal with
              | H : ErrorWithState.err2errS (MInt64asNT.from_nat ?n) ?s1 ≡ inr (?s2, _) |- _ =>
                destruct (MInt64asNT.from_nat n); inversion H; subst
              | H : ErrorWithState.err2errS (inl _) _ ≡ inr _ |- _ =>
                inversion H
              | H : ErrorWithState.err2errS (inr _) _ ≡ inr _ |- _ =>
                inversion H; subst
              end;
              solve_gen_ir_rel); solve_gen_ir_rel.
    (* TODO: might be able to automate these cases away too. *)
    - pose proof (genIR_local_count _ _ _ Heqs1) as LOC; cbn in LOC.

      apply genIR_Context in Heqs1; cbn in Heqs1; eauto.
      rewrite <- Heqs1 in Heql1.
      inversion Heql1.
      subst_contexts.
      solve_gen_ir_rel.
      match goal with
      | H : ErrorWithState.err2errS (inr _) _ ≡ inr _ |- _ =>
        inversion H; subst
      end.

      epose proof GenIR_incBlockedNamed Heqs0 BISIM.
      eapply GenIR_Rel_monotone; eauto.
      lia.
    -
      assert (local_count i1 ≥ local_count s1).
      { pose proof (genIR_local_count _ _ _ Heqs0) as LOC; cbn in LOC.
        apply incVoid_local_count in Heqs1.
        apply incBlockNamed_local_count in Heqs3.
        lia.
      }

      eapply genIR_Context in Heqs0; cbn in Heqs0; eauto.

      apply incVoid_Γ in Heqs1.
      apply incBlockNamed_Γ in Heqs3.
      subst_contexts.

      rewrite <- Heqs0 in Heql1.
      inversion Heql1; subst.

      eapply GenIR_Rel_monotone; eauto.
  Qed.

  Opaque denote_code.
 Lemma compile_FSHCOL_correct :
    forall (** Compiler bits *) (s1 s2: IRState)
      (** Helix bits    *) (op: DSHOperator) (σ : evalContext) (memH : memoryH) fuel v
      (** Vellvm bits   *) (nextblock bid_in bid_from : block_id) (bks : list (LLVMAst.block typ))
      (* (env : list (ident * typ)) *)  (g : global_env) (ρ : local_env) (memV : memoryV),
      nextblock ≢ bid_in -> (* YZ: not sure about this yet *)
      GenIR_Rel σ s1 (memH,tt) (memV, (ρ, (g, (inl (bid_from, bid_in))))) ->
      evalDSHOperator σ op memH fuel ≡ Some (inr v)            -> (* Evaluation succeeds *)
      genIR op nextblock s1 ≡ inr (s2,(bid_in,bks)) ->
      eutt (GenIR_Rel σ s2)
           (with_err_RB
              (interp_Mem (denoteDSHOperator σ op) memH))
           (with_err_LB
              (interp_cfg (D.denote_bks (convert_typ [] bks) (bid_from,bid_in))
                                g ρ memV)).
 Proof.
    intros s1 s2 op; revert s1 s2; induction op; intros * NEXT BISIM EVAL GEN.
    - cbn* in GEN.
      simp.
      hide_strings'.
      cbn*; rauto:L.
      rewrite denote_bks_nil.
      cbn*; rauto:R.
      apply eqit_Ret; auto.
      gen_ir_rel_auto.
    - (* Assign case.
         Helix side:
         1. x_i <- evalPExpr σ x_p ;;
         2. y_i <- evalPExpr σ y_p ;;
         3. x <- memory_lookup_err "Error looking up 'x' in DSHAssign" mem x_i ;;
         4. y <- memory_lookup_err "Error looking up 'y' in DSHAssign" mem y_i ;;
         5. src <- evalNExpr σ src_e ;;
         6. dst <- evalNExpr σ dst_e ;;
         7. v <- mem_lookup_err "Error looking up 'v' in DSHAssign" (to_nat src) x ;;
         8. ret (memory_set mem y_i (mem_add (to_nat dst) v y))
       *)

      destruct fuel as [| fuel]; [cbn in *; simp |].
      cbn* in GEN.
      unfold GenIR_Rel in BISIM; cbn in BISIM.
      destruct BISIM as [BISIM1 BISIM2].
      simp.
      hide_strings'.
      rename i into si, i2 into si',
      i0 into x, i3 into y,
      i1 into v1, i4 into v2.
      inv_resolve_PVar Heqs0.
      inv_resolve_PVar Heqs1.

      eutt_hide_right.
      cbn*.
      rename n1 into x_p, n2 into y_p.

      rauto:L.
      unfold denotePExpr; cbn*.
      break_inner_match_goal; cbn* in *; simp.
      eutt_hide_right.
      rename m into x_i, m0 into y_i.
      focus_single_step_h.
      rauto:L.
      subst.
      rauto:L.
      2,3:cbn*; apply memory_lookup_err_inr_Some_eq; eauto.

      subst; eutt_hide_left.
      unfold add_comments.
      cbn*.
      rewrite denote_bks_unfold_in; eauto.
      2: rewrite find_block_eq; reflexivity.
      cbn*.
      repeat rewrite fmap_list_app.
      rauto:R.
      cbn.
      rauto:R.
      rewrite denote_code_app.
      rauto:R.
      subst.
      focus_single_step.
      rename x into x_p', y into y_p'.
      rename n into src_e, n0 into dst_e.
      rename b into v.

      (* Step 5. *)
      eapply eutt_clo_bind.
      eapply genNExpr_correct; try eassumption.
      eauto 7 with state_invariant.

      intros [memH1 src] (memV1 & ρ1 & g1 & []) (INV1 & (EXP1 & <- & <- & <- & MONO1) & GAMMA1); cbn* in *.

      subst.

      rewrite denote_code_app.
      rauto.
      focus_single_step.

      (* Step 6. *)
      eapply eutt_clo_bind.
      eapply genNExpr_correct; eauto.

      intros [memH2 dst] (memV2 & ρ2 & g2 & []) (INV2 & (EXP2 & <- & <- & <- & MONO2) & GAMMA2); cbn in GAMMA2; cbn in INV2.
      subst.

      (* Step 7. *)
      eutt_hide_right.

      edestruct EXP1 as (EQ1 & EQ1'); [reflexivity |].
      rewrite EQ1' in Heqs11; inv Heqs11.
      rewrite Heqo0.
      eutt_hide_right.

      assert (i2 ≡ dst).
      { unfold genNExpr_exp_correct in EXP2.
        assert (ρ2 ⊑ ρ2) as LL by reflexivity.
        specialize (EXP2 _ LL) as (EXP2_EUTT & EXP2_EVAL).
        rewrite EXP2_EVAL in Heqs12.
        inversion Heqs12.
        auto.
      }
      subst.

      Set Nested Proofs Allowed.
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

      rewrite (assert_NT_lt_success Heqs13).
      cbn*.
      rauto:L.

      rewrite interp_Mem_MemSet.
      cbn*.
      rauto:L.

      subst; eutt_hide_left.

      simpl.
      rauto:R.
      focus_single_step_v.
      cbn.

      (* I am looking up an ident x, for which I find the type `TYPE_Pointer (TYPE_Array sz TYPE_Double)`
         in my typing context.
         Can it be a global?
       *)

      (* onAllHyps move_up_types. *)
      subst; focus_single_step_v; eutt_hide_left.
      unfold endo, Endo_ident.

      destruct x_p' as [x_p' | x_p']; [admit |];
        destruct y_p' as [y_p' | y_p']; cbn; [admit |].
      subst; focus_single_step_v; eutt_hide_left.
      edestruct memory_invariant_LLU_Ptr as (bk_x & ptr_x & LUx & INLGx & VEC_LUx); [| exact LUn | exact Heqo |]; eauto.
      rewrite LUx in Heqo2; symmetry in Heqo2; inv Heqo2.
      edestruct memory_invariant_LLU_Ptr as (bk_y & ptr_y & LUy & INLGy & VEC_LUy); [| exact LUn0 | eassumption |]; eauto.
      rewrite LUy in Heqo1; symmetry in Heqo1; inv Heqo1.

      focus_single_step_v; rauto:R.
      admit.
    (*   2: apply MONO2, MONO1; eauto. *)
    (*   cbn; norm_v. *)
    (*   subst; focus_single_step_v; norm_v. *)
    (*   unfold IntType; rewrite typ_to_dtyp_I; cbn. *)
    (*   subst; focus_single_step_v; norm_v. *)
    (*   subst; focus_single_step_v; norm_vD. *)
    (*   focus_single_step_v. *)

    (*   destruct (EXP1 ρ2) as [EQe ?]; auto. *)
    (*   rewrite <- EQe. *)
    (*   norm_v. *)
    (*   subst; focus_single_step_v; norm_vD. *)
    (*   cbn. *)

    (*   rename i into index, v1 into size_array. *)
    (*   unfold ITree.map. *)
    (*   norm_v. *)

    (*   rewrite exp_E_to_instr_E_Memory, subevent_subevent. *)
    (*   rewrite typ_to_dtyp_D_array. *)

    (*   cbn in *. *)

    (*   (* onAllHyps move_up_types. *) *)

    (*   match goal with *)
    (*     |- context[interp_cfg_to_L3 ?defs (@ITree.trigger ?E _ (subevent _ (GEP (DTYPE_Array ?size ?t) (DVALUE_Addr ?a) _)))] => *)
    (*     edestruct (@interp_cfg_to_L3_GEP_array defs t a size g ρ2) as (add & ?EQ & READ); eauto *)
    (*   end. *)

    (*   assert (EQindex: Integers.Int64.repr (Z.of_nat (MInt64asNT.to_nat index)) ≡ index) by admit. *)
    (*   rewrite EQindex in *. *)
    (*   rewrite EQ. *)

    (*   norm_v. *)
    (*   cbn. *)
    (*   subst; cbn; norm_v. *)
    (*   focus_single_step_v. *)
    (*   rewrite interp_cfg_to_L3_LW. *)
    (*   cbn*; norm_v. *)
    (*   subst; simpl; norm_v. *)
    (*   focus_single_step_v. *)
    (*   cbn; norm_v. *)
    (*   subst; cbn; norm_v. *)
    (*   focus_single_step_v. *)

    (*   2: apply lookup_alist_add_eq. *)
    (*   cbn*; norm_v. *)
    (*   subst; cbn; norm_v; focus_single_step_v. *)
    (*   rewrite interp_cfg_to_L3_Load. *)
    (*   2: rewrite typ_to_dtyp_D; eassumption. *)
    (*   norm_v. *)
    (*   subst; cbn; norm_v; focus_single_step_v. *)
    (*   rewrite interp_cfg_to_L3_LW. *)
    (*   cbn; norm_v. *)
    (*   subst; cbn; norm_v. *)

    (*   2:{ *)
    (*     unfold endo. *)
    (*     assert (y_p' <> r1) by admit. *)
    (*     assert (y_p' <> r) by admit. *)
    (*     setoid_rewrite lookup_alist_add_ineq; eauto. *)
    (*     setoid_rewrite lookup_alist_add_ineq; eauto. *)
    (*     cbn in *. *)
    (*     apply MONO2, MONO1; eauto. *)
    (*   } *)
    (*   cbn. *)
    (*   subst. *)
    (*   unfold IntType;rewrite !typ_to_dtyp_I. *)
    (*   focus_single_step_v; norm_v. *)
    (*   subst; cbn; norm_v. *)
    (*   focus_single_step_v. *)

    (*   match goal with *)
    (*     |- eutt _ _ (ITree.bind (_ (interp_cfg _ _ ?l _)) _) => destruct (EXP2 l) as [EQe' ?]; auto *)
    (*   end. *)
    (*   rewrite <- sub_alist_add. *)
    (*   apply sub_alist_add. *)
    (*   rename r into foo. *)
    (*   (* Freshness, easy todo *) *)
    (*   admit. *)
    (*   admit. *)

    (*   rewrite <- EQe'. *)
    (*   norm_v. *)
    (*   subst; cbn*; norm_v. *)
    (*   focus_single_step_v. *)
    (*   norm_v; subst; focus_single_step_v. *)
    (*   norm_v; subst; focus_single_step_v. *)
    (*   cbn; unfold ITree.map. *)
    (*   norm_v; subst; focus_single_step_v. *)
    (*   rewrite exp_E_to_instr_E_Memory, subevent_subevent. *)
    (*   rewrite typ_to_dtyp_D_array. *)

    (*   Set Hyps Limit 50. *)

    (*   (* Need another GEP lemma? *)
    (*      The destination is not read on the Helix side, so that I do not know that the GEP succeeds *)
    (*    *) *)

    (*   (* *)
    (*   match goal with *)
    (*     |- context[interp_cfg_to_L3 ?defs (@ITree.trigger ?E _ (subevent _ (GEP (DTYPE_Array ?size ?t) (DVALUE_Addr ?a) _))) ?g ?l] => *)
    (*     edestruct (@interp_cfg_to_L3_GEP_array defs t a size g l) as (add' & ?EQ & READ'); eauto *)
    (*   end. *)

    (*   eapply VEC_LUy. *)
    (*    *) *)

    (*     admit. *)
    (* (* End of genFSHAssign, things are getting a bit complicated *) *)



    - destruct fuel as [| fuel]; [cbn in *; simp |].

      Opaque genWhileLoop.
      cbn* in GEN.
      unfold GenIR_Rel in BISIM; cbn in BISIM.
      simp.
      hide_strings'.
      inv_resolve_PVar Heqs0.
      inv_resolve_PVar Heqs1.
      cbn* in *.
      simp.
      (* Require Import LibHyps.LibHyps. *)
      (* onAllHyps move_up_types. *)

      eutt_hide_right.

      rauto:L.
      unfold denotePExpr; cbn*.

      Ltac rewrite_nth_error :=
        match goal with
        | h: nth_error _ _ ≡ _ |- _ => rewrite h
        end.

      Ltac rewrite_memory_lookup :=
        match goal with
        | h: memory_lookup _ _ ≡ _ |- _ => rewrite h
        end.

      do 2 rewrite_nth_error.

      repeat (rauto:L; []).
      rauto:L.
      2: cbn*; rewrite_memory_lookup; reflexivity.

      rauto:L.
      2: cbn*; rewrite_memory_lookup; reflexivity.

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
      destruct fuel as [| fuel]; [cbn in *; simp |].
      cbn* in GEN.
      unfold GenIR_Rel in BISIM; cbn in BISIM.
      unfold ErrorWithState.err2errS in *.
      repeat (break_inner_match_hyp; cbn in *; repeat inv_sum; []).
      repeat match goal with
      | h: _ * _ |- _ => destruct h
      | h: () |- _ => destruct h
      end.
      repeat match goal with
      | h: (_,_) ≡ (_,_) |- _ => inv h
             end.
      cbn* in *.

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

      rewrite add_comment_eutt.
      cbn.

      Lemma convert_typ_block_app : forall (a b : list (LLVMAst.block typ)) env, (convert_typ env (a ++ b) ≡ convert_typ env a ++ convert_typ env b)%list.
      Proof.
        induction a as [| [] a IH]; cbn; intros; auto.
        rewrite IH; reflexivity.
      Qed.

      rewrite convert_typ_block_app.
      rewrite denote_bks_app; eauto.
      2: admit. (* TODO: should hold from compilation *)

      rauto.

      Lemma evalDSHSeq_split :
        forall {fuel σ op1 op2 mem mem''},
          evalDSHOperator σ (DSHSeq op1 op2) mem fuel ≡ Some (inr mem'') ->
          exists mem', evalDSHOperator σ op1 mem fuel ≡ Some (inr mem') /\
                  evalDSHOperator σ op2 mem' fuel ≡ Some (inr mem'').
      Proof.
        induction fuel;
          intros σ op1 op2 mem mem'' EVAL.
        - inversion EVAL.
        - cbn in EVAL.
          break_match_hyp; try break_match_hyp; inversion EVAL.
          exists m. split.
          * apply evalDSHOperator_fuel_monotone; auto.
          * erewrite evalDSHOperator_fuel_monotone; eauto.
      Qed.

      (* Evaluation of operators in sequence *)
      pose proof (evalDSHSeq_split EVAL) as [mem' [EVAL1 EVAL2]].

      eapply eutt_clo_bind.
      { eapply (IHop1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EVAL1 GEN_OP1).
        Unshelve.
        admit. (* Should come from freshness *)

        eapply genIR_GenIR_Rel; eauto.
      }

      intros [memH' []] (memV' & le & ge & res) IRREL.
      pose proof IRREL as [STATE [[from to] BRANCH]].
      cbn in STATE.

      (* TODO: How can I know this? *)
      (* Probably need to extend GenIR_Rel? *)
      (* - op2_entry comes from genIR of the sequence destructed with simp...
         - to comes from GenIR_Rel σ s2 (memH', ()) (memV', (le, (ge, (from, to))))         
       *)
      assert (op2_entry ≡ to).
      { unfold GenIR_Rel in IRREL.
        cbv in IRREL. destruct IRREL as [IRREL_STATE IRREL_BRANCHES].
        
        unfold GenIR_Rel in BISIM.
        cbv in BISIM. destruct BISIM as [BISIM_STATE BISIM_BRANCHES].
        subst.

        cbv in STATE.

        admit.
      }

      (* TODO: How can I know this? *)
      (* memH' comes from eutt_clo_bind
         mem' comes from evalDSHSeq_split...
       *)
      assert (memH' ≡ mem').
      { epose proof (IHop1 _ _ σ memH _ _ _ op1_entry from _ ge le memV' _ _ EVAL1 GEN_OP1) as IH.
        cbn in STATE.
        apply state_invariant_memory_invariant in STATE.

        unfold memory_invariant in STATE.
        admit.
      }
      subst.

      epose proof (IHop2 _ _ σ mem' _ _ _ to from _ ge le memV' _ _ EVAL2 GEN_OP2) as IH2.
      epose proof (IHop1 _ _ σ _ _ _ _ _ _ _ ge le _ _ _ EVAL1 GEN_OP1) as IH1.

      eapply eqit_mon.
      4: apply IH2.
      all: eauto.
      intros [memH_mon []] (memV_mon & l_mon & g_mon & res) PR.

      pose proof GEN_OP1 as LOC; apply genIR_local_count in LOC.
      pose proof GEN_OP1 as CONT; apply genIR_Context in CONT.

      replace s2 with {| block_count := block_count s2; local_count := local_count s2; void_count := void_count s2; Γ := Γ s_op1 |}.
      2: { rewrite CONT. destruct s2. cbn.
           reflexivity.
      }

      destruct res as [[from_mon to_mon] | ].
      + (* returned a branch, all good *) 
        eapply GenIR_Rel_monotone in PR.
        eapply PR. eapply LOC.
      + destruct PR as [PR_STATE [? PR_BRANCH]].
        inversion PR_BRANCH.
  Admitted.
  End GenIR.
