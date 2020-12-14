Require Import Helix.LLVMGen.Correctness_Prelude.
Set Implicit Arguments.
Set Strict Implicit.

(** We can relate the context statically for all compilation units *)

Lemma incLocal_Γ:
  forall s s' id,
    incLocal s ≡ inr (s', id) ->
    Γ s' ≡ Γ s.
Proof.
  intros; cbn in *; inv_sum; reflexivity.
Qed.

Lemma incLocalNamed_Γ:
  forall s s' msg id,
    incLocalNamed msg s ≡ inr (s', id) ->
    Γ s' ≡ Γ s.
Proof.
  intros; cbn in *; inv_sum; reflexivity.
Qed.

Lemma incVoid_Γ:
  forall s s' id,
    incVoid s ≡ inr (s', id) ->
    Γ s' ≡ Γ s.
Proof.
  intros; cbn in *; inv_sum; reflexivity.
Qed.

Lemma incBlock_Γ:
  forall s s' id,
    incBlock s ≡ inr (s', id) ->
    Γ s' ≡ Γ s.
Proof.
  intros; cbn in *; inv_sum; reflexivity.
Qed.

Lemma incBlockNamed_Γ:
  forall s s' msg id,
    incBlockNamed msg s ≡ inr (s', id) ->
    Γ s' ≡ Γ s.
Proof.
  intros; cbn in *; inv_sum; reflexivity.
Qed.

Lemma newLocalVar_Γ : forall τ prefix s1 s2 x,
    newLocalVar τ prefix s1 ≡ inr (s2,x) ->
    Γ s2 ≡ (ID_Local x,τ) :: Γ s1.
Proof.
  intros * EQ; inv EQ; reflexivity.
Qed.

Lemma dropVars_Γ :
  forall s1 s2 hd tl,
    dropVars 1 s1 ≡ inr (s2,tt) ->
    Γ s1 ≡ hd::tl ->
    Γ s2 ≡ tl.
Proof.
  intros * DR EQ. cbn in *.
  rewrite EQ in DR; cbn in *; inv DR.
  reflexivity.
Qed.

Lemma resolve_PVar_Γ :
  forall p s1 s2 x,
    resolve_PVar p s1 ≡ inr (s2, x) ->
    Γ s1 ≡ Γ s2.
Proof.
  intros p s1 s2 [x v] H.
  destruct p.
  cbn* in *; simp.
  reflexivity.
Qed.

Lemma genNExpr_Γ :
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

Lemma genMExpr_Γ :
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

Lemma genAExpr_Γ :
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
  rewrite (genNExpr_Γ _ _ GEN)
| GEN: genMExpr _ _ ≡ inr _ |- _ =>
  rewrite (genMExpr_Γ _ _ GEN)
  end; subst; auto.
  
Qed.

Ltac subst_Γs :=
  repeat match goal with
         | H : Γ ?s1 ≡ Γ ?s2 |- _ =>
           rewrite H in *; clear H
         end.

Opaque incLocal.
Opaque incVoid.
Opaque incBlockNamed.
Opaque newLocalVar.
Opaque resolve_PVar.

Lemma genIR_Γ:
  ∀ (op : DSHOperator) (s1 s2 : IRState) (nextblock b : block_id) (bk_op : list (LLVMAst.block typ)),
    genIR op nextblock s1 ≡ inr (s2, (b, bk_op)) →
    Γ s1 ≡ Γ s2.
Proof.
  induction op;
    intros s1 s2 nextblock b bk_op H;
    cbn in H; simp.
      all:repeat
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
         | H: incBlock _ ≡ inr _ |- _ =>
           apply incBlock_Γ in H
         | H: incBlockNamed _ _ ≡ inr _ |- _ =>
           apply incBlockNamed_Γ in H
         | H: incLocal _ ≡ inr _ |- _ =>
           apply incLocal_Γ in H
         | H: incVoid _ ≡ inr _ |- _ =>
           apply incVoid_Γ in H
         | H: newLocalVar _ _ _ ≡ inr _ |- _ =>
           apply newLocalVar_Γ in H
         | RES : resolve_PVar ?p ?s1 ≡ inr (?s2, ?x) |- _ =>
           apply resolve_PVar_Γ in RES; inv RES
         | GEN: genNExpr _ _ ≡ inr _ |- _ =>
           apply genNExpr_Γ in GEN; cbn in GEN; inversion GEN; subst
         | GEN: genMExpr _ _ ≡ inr _ |- _ =>
           apply genMExpr_Γ in GEN; cbn in GEN; inversion GEN; subst
         | GEN: genAExpr _ _ ≡ inr _ |- _ =>
           apply genAExpr_Γ in GEN; cbn in GEN; inversion GEN; subst
         | GEN : genIR ?op ?b ?s1 ≡ inr _ |- _ =>
           apply IHop in GEN; cbn in GEN; eauto
         end; cbn in *; subst);
      subst_Γs;
      auto.
  - simp.
    rewrite Heqs2 in Heql1; inv Heql1; auto.
  - simp; rewrite Heqs0 in Heql1; inv Heql1; auto.
  - eapply IHop1 in Heqs2; eauto.
    eapply IHop2 in Heqs0; eauto.
    subst_Γs.
    reflexivity.
Qed.

Ltac get_gammas :=
  repeat
    match goal with
    | H: incBlock _ ≡ inr _ |- _ =>
      apply incBlock_Γ in H
    | H: newLocalVar _ _ _ ≡ inr _ |- _ =>
      apply newLocalVar_Γ in H
    | H: dropVars _ _ ≡ inr _ |- _ =>
      apply dropVars in H
     | H: incLocal _ ≡ inr (_, _) |- _ =>
      eapply incLocal_Γ in H
    | H: incVoid _ ≡ inr (_, _) |- _ =>
      eapply incVoid_Γ in H
    | H: incBlockNamed _ _ ≡ inr (_, _) |- _ =>
      eapply incBlockNamed_Γ in H

    | GEN: genNExpr _ _ ≡ inr (_, _) |- _ =>
      eapply genNExpr_Γ in GEN
    | GEN: genMExpr _ _ ≡ inr _ |- _ =>
      apply genMExpr_Γ in GEN
    | GEN: genAExpr _ _ ≡ inr _ |- _ =>
      apply genAExpr_Γ in GEN
    | GEN : genIR _ _ _ ≡ inr _ |- _ =>
      apply genIR_Γ in GEN
    end.

Ltac solve_gamma := solve [get_gammas; congruence].

