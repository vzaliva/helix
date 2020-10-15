Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.
Require Import Helix.LLVMGen.Correctness_MExpr.
Require Import Helix.LLVMGen.IdLemmas.
Require Import Helix.LLVMGen.StateCounters.
Require Import Helix.LLVMGen.VariableBinding.

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

  Definition GenIR_Rel σ Γ to : Rel_cfg_T unit ((block_id * block_id) + uvalue) :=
    lift_Rel_cfg (state_invariant σ Γ) ⩕ branches to. 


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
    forall σ s1 s2 memH memV ρ g to bid_from bid_in msg b,
      incBlockNamed msg s1 ≡ inr (s2, b) ->
      GenIR_Rel σ s1 to (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))) ->
      GenIR_Rel σ s2 to (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))).
  Proof.
    intros * INC [STATE BRANCH].
    split; cbn; state_inv_auto.
  Qed.

  Lemma GenIR_incLocal :
    forall σ s1 s2 memH memV ρ g to bid_from bid_in b,
      incLocal s1 ≡ inr (s2, b) ->
      GenIR_Rel σ s1 to (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))) ->
      GenIR_Rel σ s2 to (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))).
  Proof.
    intros * INC [STATE BRANCH].
    split; cbn; state_inv_auto.
  Qed.

  Lemma GenIR_incVoid :
    forall σ s1 s2 memH memV ρ g to bid_from bid_in x,
      incVoid s1 ≡ inr (s2, x) ->
      GenIR_Rel σ s1 to (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))) ->
      GenIR_Rel σ s2 to (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))).
  Proof.
    intros * INC [STATE BRANCH].
    split; cbn; state_inv_auto.
  Qed.

  Lemma GenIR_genNExpr :
    forall σ s1 s2 memH memV ρ g to bid_from bid_in e c exp,
      genNExpr exp s1 ≡ inr (s2, (e, c)) ->
      GenIR_Rel σ s1 to (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))) ->
      GenIR_Rel σ s2 to (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))).
  Proof.
    intros * INC [STATE BRANCH].
    split; cbn; state_inv_auto.
  Qed.

  Hint Resolve GenIR_incBlockedNamed : GenIR_Rel.
  Hint Resolve GenIR_incLocal : GenIR_Rel.
  Hint Resolve GenIR_incVoid : GenIR_Rel.
  Hint Resolve GenIR_genNExpr : GenIR_Rel.

  Tactic Notation "gen_ir_rel_auto" := eauto with GenIR_Rel.

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
    forall σ s memH memV ρ g to bid_from bid_in,
      GenIR_Rel σ s to (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))) ->
      GenIR_Rel σ {| block_count := block_count s; local_count := S (local_count s); void_count := void_count s; Γ := Γ s |} to (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))).
  Proof.
    intros σ s memH memV ρ g to bid_from bid_in GEN.
    eapply GenIR_incLocal in GEN; eauto.
    apply incLocal_unfold.
  Qed.

  Lemma GenIR_Rel_S_void_count :
    forall σ s memH memV ρ g to bid_from bid_in,
      GenIR_Rel σ s to (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))) ->
      GenIR_Rel σ {| block_count := block_count s; local_count := local_count s; void_count := S (void_count s); Γ := Γ s |} to (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))).
  Proof.
    intros σ s memH memV ρ g to bid_from bid_in GEN.
    eapply GenIR_incVoid in GEN; eauto.
    apply incVoid_unfold.
  Qed.

  Lemma GenIR_Rel_monotone :
    forall σ s memH memV ρ g to bid_from bid_in bc lc vc,
      lc ≥ local_count s ->
      GenIR_Rel σ s to (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))) ->
      GenIR_Rel σ {| block_count := bc; local_count := lc; void_count := vc; Γ := Γ s |} to (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))).
  Proof.
    intros σ s memH memV ρ g to bid_from bid_in bc lc vc LC [STATE BRANCH].
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

  Ltac solve_gen_ir_rel :=
    repeat
      match goal with
      | GEN : genNExpr ?n ?s1 ≡ inr (?s2, _) |- GenIR_Rel _ ?s2 _ _ _ _ =>
        eapply (GenIR_genNExpr _ GEN)
      | LOC : incLocal ?s1 ≡ inr (?s2, _) |- GenIR_Rel _ ?s2 _ _ _ _ =>
        eapply (GenIR_incLocal LOC)
      | VOID : incVoid ?s1 ≡ inr (?s2, _) |- GenIR_Rel _ ?s2 _ _ _ _ =>
        eapply (GenIR_incVoid VOID)
      | NAMED : incBlockNamed _ ?s1 ≡ inr (?s2, _) |- GenIR_Rel _ ?s2 _ _ _ _ =>
        eapply (GenIR_incBlockedNamed NAMED)
      | RES : resolve_PVar ?p ?s1 ≡ inr (?s2, ?x) |- GenIR_Rel _ ?s2 _ _ _ _ =>
        rewrite <- (@resolve_PVar_state p s1 s2 x RES)
      | |- GenIR_Rel _ {| block_count := block_count ?s; local_count := S (local_count ?s); void_count := void_count ?s; Γ := Γ ?s |} _ _ _ _ =>
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
    (* Admitted for speed *)
  Admitted.
  (*   induction op; *)
  (*     intros s1 s2 nextblock b bk_op H; *)
  (*     cbn in H; simp; *)
  (*       repeat *)
  (*         (match goal with *)
  (*          | H : ErrorWithState.err2errS (MInt64asNT.from_nat ?n) ?s1 ≡ inr (?s2, _) |- _ => *)
  (*            destruct (MInt64asNT.from_nat n); inversion H; subst *)
  (*          | H: _ :: Γ ?s1 ≡ Γ ?s2, *)
  (*               R: Γ ?s2 ≡ _ |- _ => *)
  (*            rewrite <- H in R; inversion R; subst *)
  (*          | H: _ :: _ :: Γ ?s1 ≡ Γ ?s2, *)
  (*               R: Γ ?s2 ≡ _ |- _ => *)
  (*            rewrite <- H in R; inversion R; subst *)
  (*          | H: _ :: _ :: _ :: Γ ?s1 ≡ Γ ?s2, *)
  (*               R: Γ ?s2 ≡ _ |- _ => *)
  (*            rewrite <- H in R; inversion R; subst *)
  (*          | H: inl _ ≡ inr _ |- _ => *)
  (*            inversion H *)
  (*          | H: inr (?i1, Γ ?s1) ≡ inr (?i2, Γ ?s2) |- _ => *)
  (*            inversion H; clear H *)
  (*          | RES : resolve_PVar ?p ?s1 ≡ inr (?s2, ?x) |- _ => *)
  (*            rewrite <- (@resolve_PVar_state p s1 s2 x RES) in * *)
  (*          | H: incBlockNamed _ _ ≡ inr _ |- _ => *)
  (*            apply incBlockNamed_Γ in H *)
  (*          | H: incLocal _ ≡ inr _ |- _ => *)
  (*            apply incLocal_Γ in H *)
  (*          | H: incVoid _ ≡ inr _ |- _ => *)
  (*            apply incVoid_Γ in H *)
  (*          | GEN: genNExpr _ _ ≡ inr _ |- _ => *)
  (*            apply genNExpr_context in GEN; cbn in GEN; inversion GEN; subst *)
  (*          | GEN: genMExpr _ _ ≡ inr _ |- _ => *)
  (*            apply genMExpr_context in GEN; cbn in GEN; inversion GEN; subst *)
  (*          | GEN: genAExpr _ _ ≡ inr _ |- _ => *)
  (*            apply genAExpr_context in GEN; cbn in GEN; inversion GEN; subst *)
  (*          | GEN : genIR ?op ?b ?s1 ≡ inr _ |- _ => *)
  (*            apply IHop in GEN; cbn in GEN; eauto  *)
  (*          end; cbn in *; subst); *)
  (*       subst_contexts; *)
  (*       auto. *)
  (*   - inversion Heqs; subst. *)
  (*     apply incBlockNamed_Γ in Heqs3. *)
  (*     subst_contexts. *)
  (*     rewrite <- Heqs0 in Heql1. *)
  (*     inversion Heql1. *)
  (*     reflexivity. *)
  (*   - eapply IHop1 in Heqs2; eauto. *)
  (*     eapply IHop2 in Heqs0; eauto. *)
  (*     subst_contexts. *)
  (*     reflexivity. *)
  (* Qed. *)

  Lemma genIR_GenIR_Rel:
    ∀ (op : DSHOperator) (s1 s2 : IRState) (σ : evalContext) (memH : memoryH) (nextblock bid_in bid_from b : block_id) (g : global_env)
      (ρ : local_env) (memV : memoryV) (bk_op : list (LLVMAst.block typ)),
      genIR op nextblock s1 ≡ inr (s2, (b, bk_op)) →
      GenIR_Rel σ s1 nextblock (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))) ->
      GenIR_Rel σ s2 nextblock (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))).
  Proof.
    (* Admitted for speed right now *)
  Admitted.
  (*   induction op; *)
  (*     intros s1 s2 σ emh memH nextblock bid_in bid_from g ρ memV s_op1 bk_op GEN BISIM; *)
  (*     cbn in GEN; simp; eauto with GenIR_Rel; *)
  (*     repeat (solve_gen_ir_rel; *)
  (*             match goal with *)
  (*             | H : ErrorWithState.err2errS (MInt64asNT.from_nat ?n) ?s1 ≡ inr (?s2, _) |- _ => *)
  (*               destruct (MInt64asNT.from_nat n); inversion H; subst *)
  (*             | H : ErrorWithState.err2errS (inl _) _ ≡ inr _ |- _ => *)
  (*               inversion H *)
  (*             | H : ErrorWithState.err2errS (inr _) _ ≡ inr _ |- _ => *)
  (*               inversion H; subst *)
  (*             end; *)
  (*             solve_gen_ir_rel); solve_gen_ir_rel. *)
  (*   (* TODO: might be able to automate these cases away too. *) *)
  (*   - pose proof (genIR_local_count  _ _ _ Heqs1) as LOC; cbn in LOC. *)

  (*     apply genIR_Context in Heqs1; cbn in Heqs1; eauto. *)
  (*     rewrite <- Heqs1 in Heql1. *)
  (*     inversion Heql1. *)
  (*     subst_contexts. *)
  (*     solve_gen_ir_rel. *)
  (*     match goal with *)
  (*     | H : ErrorWithState.err2errS (inr _) _ ≡ inr _ |- _ => *)
  (*       inversion H; subst *)
  (*     end. *)

  (*     epose proof GenIR_incBlockedNamed Heqs0 BISIM. *)
  (*     eapply GenIR_Rel_monotone; eauto. *)
  (*     lia. *)
  (*   - *)
  (*     assert (local_count i1 ≥ local_count s1). *)
  (*     { pose proof (genIR_local_count _ _ _ Heqs0) as LOC; cbn in LOC. *)
  (*       apply incVoid_local_count in Heqs1. *)
  (*       apply incBlockNamed_local_count in Heqs3. *)
  (*       lia. *)
  (*     } *)

  (*     eapply genIR_Context in Heqs0; cbn in Heqs0; eauto. *)

  (*     apply incVoid_Γ in Heqs1. *)
  (*     apply incBlockNamed_Γ in Heqs3. *)
  (*     subst_contexts. *)

  (*     rewrite <- Heqs0 in Heql1. *)
  (*     inversion Heql1; subst. *)

  (*     eapply GenIR_Rel_monotone; eauto. *)
  (*   - pose proof Heqs0 as IH2. *)
  (*     eapply IHop2 in IH2; eauto. *)
  (*     destruct IH2 as (STATE2 & (from2 & BRANCHES2) & MEM2). *)
  (*     cbn in STATE2, BRANCHES2, MEM2; inversion BRANCHES2; subst. *)
  (*     (* pose proof Heqs2 as IH1. *) *)
  (*     (* eapply IHop1 in IH1; eauto. *) *)
  (*     replace s2 with *)
  (*            {|block_count := block_count s2; *)
  (*              local_count := local_count s2; *)
  (*              void_count := void_count s2; *)
  (*              Γ := Γ s1|}. *)
  (*     2: { *)
  (*       apply genIR_Context in Heqs0. *)
  (*       apply genIR_Context in Heqs2. *)
  (*       subst_contexts. *)
  (*       destruct s2; reflexivity. *)
  (*     } *)
  (*     eapply GenIR_Rel_monotone in BISIM; eauto. *)

  (*     apply genIR_local_count in Heqs0. *)
  (*     apply genIR_local_count in Heqs2. *)
  (*     lia. *)
  (* Qed. *)


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

  (* TODO: move this (or get rid of it) *)
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

  Require Import LibHyps.LibHyps.

  Ltac clean_goal :=
    try match goal with
        | h1 : incVoid _ ≡ _,
               h2 : incVoid _ ≡ _,
                    h3 : incVoid _ ≡ _
          |- _ => move h1 at top; move h2 at top; move h3 at top
        | h1 : incVoid _ ≡ _, h2 : incVoid _ ≡ _ |- _ => move h1 at top; move h2 at top
        | h : incVoid _ ≡ _ |- _ => move h at top
        end;

    try match goal with
        | h1 : incLocal _ ≡ _,
               h2 : incLocal _ ≡ _,
                    h3 : incLocal _ ≡ _
          |- _ => move h1 at top; move h2 at top; move h3 at top
        | h1 : incLocal _ ≡ _, h2 : incLocal _ ≡ _ |- _ => move h1 at top; move h2 at top
        | h : incLocal _ ≡ _ |- _ => move h at top
        end;

    try match goal with
        | h1 : incBlockNamed _ _ ≡ _,
               h2 : incBlockNamed _ _ ≡ _,
                    h3 : incBlockNamed _ _ ≡ _
          |- _ => move h1 at top; move h2 at top; move h3 at top
        | h1 : incBlockNamed _ _ ≡ _, h2 : incBlockNamed _ _ ≡ _ |- _ => move h1 at top; move h2 at top
        | h : incBlockNamed _ _ ≡ _ |- _ => move h at top
        end;

    onAllHyps move_up_types.
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
      GenIR_Rel σ s1 bid_in (memH,tt) (memV, (ρ, (g, (inl (bid_from, bid_in))))) ->
      no_failure (E := E_cfg) (interp_helix (denoteDSHOperator σ op) memH) -> (* Evaluation succeeds *)
      genIR op nextblock s1 ≡ inr (s2,(bid_in,bks)) ->
      eutt (succ_cfg (GenIR_Rel σ s2 nextblock))
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
          eapply gen_not_state_bound; eauto using incBlockNamed_count_gen_injective;
            solve_not_ends_with.
        }
        auto.
      }
      vred.

      apply eutt_Ret; auto.
      destruct BISIM as (STATE & (from & BRANCH)).
      cbn in STATE, BRANCH.
      split; cbn; eauto.

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

      solve_state_invariant.

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
      apply no_failure_Ret in NOFAIL; try_abs.
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
          cbn. repr_intval
          replace (repr (Z.of_nat (MInt64asNT.to_nat src))) with src by admit.
          reflexivity.
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
        destruct vy_p as [vy_p | vy_p].
        { 
          edestruct memory_invariant_Ptr as (ymembk & yptr & yLU & yINLG & yGETCELL); [| eapply Heqo0 | eapply LUn0 |]; [solve_state_invariant |].
          clean_goal.
          rewrite yLU in H0; symmetry in H0; inv H0.
          cbn in yINLG.
          (* How do we know that ymembk is allocated?
             yGETCELL does not contain any information here.
           *)
          (* Oooh we don't, we're using [gep] but not for reading a cell here?
             Not true though, the cell must be allocated, we are about to write in it.
             We need another lemma about [OP_GetElementPtr] then.
           *)
          (* edestruct denote_instr_gep_array as (yptr' & yREAD & yEQ); cycle -1; [rewrite yEQ; clear yEQ | ..]; cycle 1. *)
          (* { vstep; solve_lu. *)
          (*   cbn; reflexivity. *)
          (* } *)
          (* { rewrite EXP2. *)
          (*   2:{ cbn. etransitivity. apply sub_alist_add. *)
          (*       2: apply sub_alist_add. *)
          (*       admit. admit. *)
          (*   } *)
          (*   replace (repr (Z.of_nat (MInt64asNT.to_nat dst))) with dst by admit. *)
          (*   cbn; reflexivity. *)

          (* } *)
          (* eapply yGETCELL. *)

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
        (* TODO: need to make sure IN_NEXT is actually nextblock... *)
        intros x OUT_PRED [IN_BOUND IN_NEXT].
        destruct OUT_PRED as [OUT_PRED | OUT_PRED]; auto.
        eapply (state_bound_between_separate incBlockNamed_count_gen_injective OUT_PRED IN_BOUND).
        lia. auto.
        admit.
      }

      rauto.

      (* Evaluation of operators in sequence *)
      (* pose proof (evalDSHSeq_split EVAL) as [mem' [EVAL1 EVAL2]]. *)
      (* Helix generates code for op2 *first*, so op2 gets earlier
        variables from the irstate. Helix needs to do this because it
        passes the block id for the next block that an operator should
        jump to when it's done executing... So it generates code for
        op2, which goes to the next block of the entire sequence, and
        then passes the entry point for op2 as the "nextblock" for
        op1.
        YZ: I got lost, I'll try to refix it later
      *)
      cbn in NOFAIL.
      pose proof BISIM as BISIM2.
      destruct BISIM as [SINV (?from & EQ)]; cbn in *; inv EQ.
      simp.
      eapply eutt_clo_bind_returns; [eapply IHop1; try exact Heqs1; eauto |].  
      eapply bid_bound_genIR_entry; eauto.
      (* { split; cbn; cbn. *)
      (*   - eapply genIR_GenIR_Rel in Heqs1; eauto. *)
      (*     cbn in *. *)
      (*     destruct GEN_OP2 as (STATE & _). *)
      (*     cbn in STATE. *)
      (*     apply STATE. *)
      (*     split; auto. *)
      (*     split; cbn; auto. *)
      (*     eauto. *)
      (*   - split; cbn. *)
      (*     + (* Already had to prove that nextblock <> op2_entry... So, *) *)
      (* (*          that's probably a problem *) *)
      (*       exists from. *)
      (*       reflexivity. *)
      (*     + reflexivity. *)
      (* } *)
      admit.

      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      cbn in PRE; destruct PRE as (INV2 & EXP2 & ?); cbn in *; inv_eqs.
      subst...
      eapply IHop2; try eapply Heqs1; eauto.
      admit.
      admit.
   
      (* eapply eutt_clo_bind. *)
      (* { *)
      (*   eapply (IHop1 _ _ _ _ _ _ op2_entry _ _ _ _ _ _ _ _ EVAL1 GEN_OP1). *)
      (*   Unshelve. *)
      (*   eapply bid_bound_genIR_entry; eauto. *)
      (*   split; cbn. *)
      (*   - eapply genIR_GenIR_Rel in GEN_OP2; eauto. *)
      (*     destruct GEN_OP2 as (STATE & _). *)
      (*     cbn in STATE. *)
      (*     apply STATE. *)
      (*     split; auto. *)
      (*     split; cbn; auto. *)
      (*     exists from. eauto. *)
      (*   - split; cbn. *)
      (*     + (* Already had to prove that nextblock <> op2_entry... So, *)
      (*          that's probably a problem *) *)
      (*       exists from. *)
      (*       reflexivity. *)
      (*     + reflexivity. *)
      (* } *)

      (* intros [memH' []] (memV' & le & ge & res) IRREL. *)
      (* pose proof IRREL as [STATE [[from' BRANCH] MEM]]. *)
      (* cbn in STATE, BRANCH, MEM. *)
      (* subst. *)

      (* eapply eqit_mon. *)
      (* intros. apply H. *)
      (* intros. apply H. *)
      (* 2: { *)
        (* TODO: this might be wrong *)
        (* This is setting me up for failure, I think...

           I end up having to prove:


           GenIR_Rel σ s1 memH' op2_entry (memH', ()) (memV', (le, (ge, inl (from', op2_entry))))

           Which leaves me with:

           concrete_fresh_inv s1 le

           Which is not true.

         *)

      (* eapply genIR_GenIR_Rel; eauto. *)
      (* introR; destruct_unit. *)
      (* intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET. *)
      (* cbn in PRE; destruct PRE as (STATE & [from to] & BRANCH); cbn in *; inv_eqs; subst. *)
      (* simp. *)
      (* clear IHop1. *)
      (* TODO: How can I know this? *)
      (* Probably need to extend GenIR_Rel? *)
      (* - bid_op2 comes from genIR of the sequence destructed with simp...
         - to comes from GenIR_Rel σ s2 (memH', ()) (memV', (le, (ge, (from, to))))

         
       *)
      (* eapply IHop2; try apply Heqs0; eauto. *)
      (* admit. *)
      (* admit. *)
      (* admit. *)
  (*     assert (bid_op2 ≡ to). *)
  (*     { unfold GenIR_Rel in IRREL. *)
  (*       cbv in IRREL. destruct IRREL as [IRREL_STATE IRREL_BRANCHES]. *)
        
  (*       unfold GenIR_Rel in BISIM. *)
  (*       cbv in BISIM. destruct BISIM as [BISIM_STATE BISIM_BRANCHES]. *)
  (*       subst. *)

  (*       cbv in STATE. *)

  (*       (* *) *)

  (*     admit. *)
  (*     } *)
  (*     (* TODO: Need to match u1 up with mem' somehow *) *)
  (*     assert (memH' ≡ mem'). *)
  (*     { epose proof (IHop1 _ _ σ memH _ _ _ bid_in from _ ge le memV' _ _ EVAL1 GEN_OP1) as IH. *)
  (*       cbn in STATE. *)
  (*       apply state_invariant_memory_invariant in STATE. *)

  (*       unfold memory_invariant in STATE. *)
  (*       admit. *)
  (*     } *)
  (*     subst. *)

  (*     epose proof (IHop2 _ _ σ mem' _ _ _ to from _ ge le memV' _ _ EVAL2 GEN_OP2) as IH2. *)
  (*     epose proof (IHop1 _ _ σ _ _ _ _ _ _ _ ge le _ _ _ EVAL1 GEN_OP1) as IH1. *)

  (*     eapply eqit_mon. *)
  (*     4: apply IH2. *)
  (*     all: eauto. *)
  (*     intros [memH_mon []] (memV_mon & l_mon & g_mon & res) PR. *)

      (*   epose proof (IHop2 _ _ σ memH' _ _ _ _ _ _ ge le memV' _ _ EVAL2 GEN_OP2) as IH2. *)
      (*   apply IH2. *)
      (*   Unshelve. *)
      (*   auto. *)

      (*   eapply genIR_GenIR_Rel in GEN_OP2; eauto. *)
      (*   2: { *)
      (*     split; cbn; eauto. *)
      (*     split; cbn; eauto. *)
      (*   } *)

      (*   destruct GEN_OP2 as (STATE_OP2 & (from_op2 & BRANCH_OP2) & MEM_OP2). *)
      (*   cbn in STATE_OP2, BRANCH_OP2, MEM_OP2. *)

      (*   (* TODO: can I clean this part up? *) *)
      (*   split; cbn. *)
      (*   - split. *)
      (*     + apply state_invariant_memory_invariant in STATE. *)
      (*       unfold memory_invariant. *)
      (*       intros n v0 τ x H H0. *)

      (*       eapply STATE; eauto. *)
      (*       rewrite <- (genIR_Context _ _ _ GEN). *)
      (*       auto. *)
      (*     + eapply IRState_is_WF; eauto. *)
      (*     + *)
      (*       (* This doesn't seem true? *)

      (*          le should be the local environment after denoting op1... *)

      (*          So, I should hope to have *)

      (*          concrete_fresh_inv s_op1 le, *)

      (*          instead of *)

      (*          concrete_fresh_inv s1 le... *)

      (*          Because we generated names between s1 and s_op1... *)
      (*        *) *)
      (*       eapply incLocal_is_fresh in STATE_BIS. *)
      (*       cbn in STATE_BIS. *)
      (*       cbn. *)
      (*       intros id v0 n H H0. *)
      (*       eapply STATE_BIS; eauto. *)

      (*       (* Does le = ρ ? *) *)
      (*       admit. (* TODO: ugh, freshness *) *)
      (*   - split; cbn; eauto. *)
      (* } *)
      (* intros [memH_mon []] (memV_mon & l_mon & g_mon & res) PR. *)


  (*     pose proof GEN_OP1 as LOC; apply genIR_local_count in LOC. *)
  (*     pose proof GEN_OP1 as CONT; apply genIR_Context in CONT. *)


  (*     replace s2 with {| block_count := block_count s2; local_count := local_count s2; void_count := void_count s2; Γ := Γ s_op1 |} by admit. *)

  (*     destruct res as [[from_mon to_mon] | ]. *)
  (*     + (* returned a branch, all good *)  *)
  (*       eapply GenIR_Rel_monotone in PR. *)
  (*       eapply PR. eapply LOC. *)
  (*     + destruct PR as [PR_STATE [? PR_BRANCH]]. *)
  (*       inversion PR_BRANCH. *)
           

      (* replace s2 with {| block_count := block_count s2; local_count := local_count s2; void_count := void_count s2; Γ := Γ s_op1 |}. *)
      (* 2: { rewrite CONT. destruct s2. cbn. *)
      (*      reflexivity. *)
      (* } *)

      (* { *)
      (* destruct res as [[from_mon to_mon] | ]. *)
      (* + (* returned a branch, all good *)  *)
      (*   eapply GenIR_Rel_monotone in PR. *)
      (*   eapply PR. eapply LOC. *)
      (* + destruct PR as [PR_STATE [[? PR_BRANCH] ?]]. *)
      (*   inversion PR_BRANCH. *)
      (* } *)

      (* Unshelve. *)
      (* all: eauto. *)
  Admitted.
  End GenIR.
 
