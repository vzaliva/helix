Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.
Require Import Helix.LLVMGen.Correctness_MExpr.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

(* TODO: Move this *)
Lemma incVoid_block_count :
  forall s1 s2 bid,
    incVoid s1 ≡ inr (s2, bid) ->
    block_count s1 ≡ block_count s2.
Proof.
  intros s1 s2 bid H.
  Transparent incVoid.
  unfold incVoid in H.
  cbn in H.
  simp.
  destruct s1; cbn; auto.
  Opaque incVoid.
Qed.

(* TODO: Move this *)
Lemma incLocal_block_count :
  forall s1 s2 bid,
    incLocal s1 ≡ inr (s2, bid) ->
    block_count s1 ≡ block_count s2.
Proof.
  intros s1 s2 bid H.
  Transparent incLocal.
  unfold incLocal in H.
  cbn in H.
  simp.
  destruct s1; cbn; auto.
  Opaque incLocal.
Qed.

(* TODO: Move this *)
Lemma genNExpr_block_count :
  ∀ (nexp : NExpr) (s1 s2 : IRState) (e : exp typ) (c : code typ),
    genNExpr nexp s1 ≡ inr (s2, (e, c)) → (block_count s2 ≡ block_count s1)%nat.
Proof.
  induction nexp;
    intros s1 s2 e c GEN;
    cbn in GEN; simp; cbn;
      repeat
        match goal with
        | H: ErrorWithState.option2errS _ (nth_error (Γ ?s1) ?n) ?s1 ≡ inr (?s2, _) |- _ =>
          destruct (nth_error (Γ s1) n) eqn:FIND; inversion H; subst
        | H : incLocal ?s1 ≡ inr (?s2, _) |- _ =>
          apply incLocal_block_count in H
        | IH : ∀ (s1 s2 : IRState) (e : exp typ) (c : code typ),
            genNExpr ?n s1 ≡ inr (s2, (e, c)) → block_count s2 ≡ block_count s1,
    GEN: genNExpr ?n _ ≡ inr _ |- _ =>
  apply IH in GEN
  end; subst; auto; try lia.
Qed.

(* TODO: Move this *)
Lemma genMExpr_block_count :
  ∀ (mexp : MExpr) (s1 s2 : IRState) (e : exp typ * code typ) (c : typ),
    genMExpr mexp s1 ≡ inr (s2, (e, c)) → block_count s2 ≡ block_count s1.
Proof.
  induction mexp;
    intros s1 s2 e c GEN;
    cbn in GEN; simp; cbn;
      repeat
        match goal with
        | H: ErrorWithState.option2errS _ (nth_error (Γ ?s1) ?n) ?s1 ≡ inr (?s2, _) |- _ =>
          destruct (nth_error (Γ s1) n) eqn:FIND; inversion H; subst
        | H : incLocal ?s1 ≡ inr (?s2, _) |- _ =>
          apply incLocal_block_count in H
        | IH : ∀ (s1 s2 : IRState) (e : exp typ) (c : code typ),
            genMExpr ?n s1 ≡ inr (s2, (e, c)) → block_count s2 ≡ block_count s1,
    GEN: genMExpr ?n _ ≡ inr _ |- _ =>
  apply IH in GEN
  end; subst; auto; try lia.
Qed.

(* TODO: Move this *)
Lemma genAExpr_block_count :
  ∀ (aexp : AExpr) (s1 s2 : IRState) (e : exp typ) (c : code typ),
    genAExpr aexp s1 ≡ inr (s2, (e, c)) → block_count s2 ≡ block_count s1.
Proof.
  induction aexp;
    intros s1 s2 e c GEN;
    cbn in GEN; simp; cbn;
      repeat
        match goal with
        | H: ErrorWithState.option2errS _ (nth_error (Γ ?s1) ?n) ?s1 ≡ inr (?s2, _) |- _ =>
          destruct (nth_error (Γ s1) n) eqn:FIND; inversion H; subst
        | H : incLocal ?s1 ≡ inr (?s2, _) |- _ =>
          apply incLocal_block_count in H
        | H : incVoid ?s1 ≡ inr (?s2, _) |- _ =>
          apply incVoid_block_count in H
        | GEN : genNExpr _ _ ≡ inr _ |- _ =>
          apply genNExpr_block_count in GEN
        | GEN : genMExpr _ _ ≡ inr _ |- _ =>
          apply genMExpr_block_count in GEN
        | IH : ∀ (s1 s2 : IRState) (e : exp typ) (c : code typ),
            genAExpr ?n s1 ≡ inr (s2, (e, c)) → block_count s2 ≡ block_count s1,
    GEN: genAExpr ?n _ ≡ inr _ |- _ =>
  apply IH in GEN
  end; subst; auto; try lia.
Qed.

(* TODO: move this *)
Lemma genIR_block_count :
  forall op s1 s2 nextblock b bk_op,
    genIR op nextblock s1 ≡ inr (s2, (b, bk_op)) ->
    block_count s2 ≥ block_count s1.
Proof.
  (* TODO: after moving this it seems to be looping forever...? *)
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
           apply incLocal_block_count in H
         | H : incVoid ?s1 ≡ inr (?s2, _) |- _ =>
           apply incVoid_block_count in H
         | H : incBlockNamed _ _ ≡ inr _ |- _ =>
           apply incBlockNamed_block_count in H
         | H : incBlock _ ≡ inr _ |- _ =>
           apply incBlockNamed_block_count in H
         | H : resolve_PVar _ _ ≡ inr _ |- _ =>
           apply resolve_PVar_state in H; subst
         | GEN : genNExpr _ _ ≡ inr _ |- _ =>
           apply genNExpr_block_count in GEN
         | GEN : genMExpr _ _ ≡ inr _ |- _ =>
           apply genMExpr_block_count in GEN
         | GEN : genAExpr _ _ ≡ inr _ |- _ =>
           apply genAExpr_block_count in GEN
         | IH : ∀ (s1 s2 : IRState) (nextblock b : block_id) (bk_op : list (LLVMAst.block typ)),
             genIR ?op nextblock s1 ≡ inr (s2, (b, bk_op)) → block_count s2 ≥ block_count s1,
           GEN: genIR ?op _ _ ≡ inr _ |- _ =>
         apply IH in GEN
         end; cbn in *);
         try lia.
Qed.
