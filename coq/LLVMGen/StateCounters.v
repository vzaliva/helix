(** * Compilation units and IRState

    This file contains a bunch of lemmas describing how various compilation subroutines
    impact the freshness part of the [IRState].
    The file [Context.v] is the pendant for the context part of the [IRState].
 *)

Require Import Helix.LLVMGen.Correctness_Prelude.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Transparent resolve_PVar.
(* TODO: Not sure where this should belong *)
Lemma resolve_PVar_simple : forall p s s' x v,
    resolve_PVar p s ≡ inr (s', (x, v)) ->
    exists sz n,
      nth_error (Γ s') n ≡ Some (x, TYPE_Pointer (TYPE_Array sz TYPE_Double)) /\
      MInt64asNT.from_N sz ≡ inr v /\ p ≡ PVar n /\ s ≡ s'.
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

Global Opaque resolve_PVar.

Section BlockCount.

  Lemma incVoid_block_count :
    forall s1 s2 bid,
      incVoid s1 ≡ inr (s2, bid) ->
      block_count s1 ≡ block_count s2.
  Proof.
    intros s1 s2 bid H.
    unfold incVoid in H.
    cbn in H.
    simp.
    destruct s1; cbn; auto.
  Qed.

  Lemma incLocal_block_count :
    forall s1 s2 bid,
      incLocal s1 ≡ inr (s2, bid) ->
      block_count s1 ≡ block_count s2.
  Proof.
    intros s1 s2 bid H.
    unfold incLocal in H.
    cbn in H.
    simp.
    destruct s1; cbn; auto.
  Qed.

  Lemma incLocalNamed_block_count :
    forall s s1 s2 bid,
      incLocalNamed s s1 ≡ inr (s2, bid) ->
      block_count s1 ≡ block_count s2.
  Proof.
    intros * H.
    cbn in H.
    simp.
    destruct s1; cbn; auto.
  Qed.

  Lemma incBlockNamed_block_count:
    forall s s' msg id,
      incBlockNamed msg s ≡ inr (s', id) ->
      block_count s' ≡ S (block_count s).
  Proof.
    intros; cbn in *; inv_sum; reflexivity.
  Qed.
  
  Lemma newLocalVar_block_count :
    ∀ (s1 s2 : IRState) bid p x,
      newLocalVar p x s1 ≡ inr (s2, bid) →
      block_count s1 ≡ block_count s2.
  Proof.
    intros s1 s2 bid * H.
    unfold newLocalVar in H.
    cbn in H.
    simp.
    destruct s1; cbn; auto.
  Qed.

  Lemma dropVars_block_count :
    ∀ (s1 s2 : IRState) bid x,
      dropVars x s1 ≡ inr (s2, bid) →
      block_count s1 ≡ block_count s2.
  Proof.
    intros s1 s2 bid * H.
    cbn in H.
    simp.
    destruct s1; cbn; auto.
  Qed.

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

  Ltac __local_ltac' := (repeat
      (match goal with
       | H: inl _ ≡ inr _ |- _ =>
         inversion H
       | H: ErrorWithState.option2errS _ (nth_error (Γ ?s1) ?n) ?s1 ≡ inr (?s2, _) |- _ =>
         destruct (nth_error (Γ s1) n) eqn:?; inversion H; subst
       | H : ErrorWithState.err2errS (MInt64asNT.from_nat ?n) ?s1 ≡ inr (?s2, _) |- _ =>
         destruct (MInt64asNT.from_nat n) eqn:?; inversion H; subst
       | H : incLocal ?s1 ≡ inr (?s2, _) |- _ =>
         apply incLocal_block_count in H
       | H : newLocalVar _ _ ?s1 ≡ inr (?s2, _) |- _ =>
         apply newLocalVar_block_count in H
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
       end; cbn in *)).

  Opaque incLocal.
  Opaque incVoid.
  Opaque incBlockNamed.
  Opaque newLocalVar.
  Opaque resolve_PVar.

  Lemma genIR_block_count :
    forall op s1 s2 nextblock b bk_op,
      genIR op nextblock s1 ≡ inr (s2, (b, bk_op)) ->
      block_count s2 ≥ block_count s1.
  Proof.
    induction op; intros; cbn in H; simp; __local_ltac'; try lia.
  Qed.
  
End BlockCount.
       
Section LocalCount.

  Lemma newLocalVar_local_count :
    ∀ (s1 s2 : IRState) bid p x,
      newLocalVar p x s1 ≡ inr (s2, bid) →
      local_count s2 ≡ S (local_count s1).
  Proof.
    intros * EQ; inv EQ; reflexivity.
  Qed.

  Lemma incBlockNamed_local_count:
    forall s s' msg id,
      incBlockNamed msg s ≡ inr (s', id) ->
      local_count s' ≡ local_count s.
  Proof.
    intros; cbn in *; inv_sum; reflexivity.
  Qed.

  Lemma incVoid_local_count:
    forall s s' id,
      incVoid s ≡ inr (s', id) ->
      local_count s' ≡ local_count s.
  Proof.
    Transparent incVoid.
    intros; cbn in *; inv_sum; reflexivity.
    Opaque incVoid.
  Qed.

  Lemma incLocal_local_count: forall s s' x,
      incLocal s ≡ inr (s',x) ->
      local_count s' ≡ S (local_count s).
  Proof.
    Transparent incLocal.
    intros; cbn in *; inv_sum; reflexivity.
    Opaque incLocal.
  Qed.

  Lemma dropVars_local_count:
    forall s s' k,
      dropVars k s ≡ inr (s', tt) ->
      local_count s' ≡ local_count s.
  Proof.
    intros; cbn in *; simp; reflexivity.
  Qed.

  Lemma incLocalNamed_local_count: forall s s' msg x,
      incLocalNamed msg s ≡ inr (s',x) ->
      local_count s' ≡ S (local_count s).
  Proof.
    intros; cbn in *; inv_sum; reflexivity.
  Qed.

  Lemma genNExpr_local_count :
    forall nexp s1 s2 e c,
      genNExpr nexp s1 ≡ inr (s2, (e, c)) ->
      (local_count s2 >= local_count s1)%nat.
  Proof.
    induction nexp;
      intros s1 s2 e c GEN;
      cbn* in *; simp; cbn in *;
        repeat
          match goal with
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
      cbn* in *; simp; cbn in *;
        repeat
          match goal with
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
      cbn* in *; simp; cbn in *;
        repeat
          match goal with
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

  Opaque incLocal.
  Opaque incVoid.
  Opaque incBlockNamed.
  Opaque newLocalVar.
  Opaque resolve_PVar.
  Arguments append: simpl never.

  Ltac __local_ltac :=
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
       | H : newLocalVar _ _ ?s1 ≡ inr (?s2, _) |- _ =>
         apply newLocalVar_local_count in H
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
       end; cbn in *).

  Lemma genWhile_local_count :
    forall prefix from to loopvar loopcontblock body_entry body_blocks init_code nextblock s1 s2 seg,
      genWhileLoop prefix from to loopvar loopcontblock body_entry body_blocks init_code nextblock s1 ≡ inr (s2, seg) ->
      local_count s2 ≥ local_count s1.
  Proof.
    intros.
    cbn in H; simp; __local_ltac; lia. 
  Qed.

  Lemma genIR_local_count :
    forall op s1 s2 nextblock b bk_op,
      genIR op nextblock s1 ≡ inr (s2, (b, bk_op)) ->
      local_count s2 ≥ local_count s1.
  Proof.
    induction op; intros; cbn in H; simp; __local_ltac; try lia. 
  Qed.

End LocalCount.

  (* (* We define the obvious total order on IRStates *) *)
  (* Definition IRState_lt (s1 s2 : IRState) : Prop := *)
  (*   (local_count s1 < local_count s2)%nat. *)
  (* Infix "<<" := IRState_lt (at level 10). *)

  (* Definition IRState_le (s1 s2 : IRState) : Prop := *)
  (*   (local_count s1 <= local_count s2)%nat. *)
  (* Infix "<<=" := IRState_le (at level 10). *)

  (* Lemma incLocal_lt : forall s1 s2 x, *)
  (*     incLocal s1 ≡ inr (s2,x) -> *)
  (*     s1 << s2. *)
  (* Proof. *)
  (*   intros s1 s2 x INC. *)
  (*   apply incLocal_local_count in INC. *)
  (*   unfold IRState_lt. *)
  (*   lia. *)
  (* Qed. *)

  (* Create HintDb irs_lt. *)
  (* Hint Resolve incLocal_lt : irs_lt. *)


  (* Tactics *)

Ltac get_local_count_hyps :=
  repeat
    match goal with
    | H: incBlockNamed ?n ?s1 ≡ inr (?s2, _) |- _ =>
      apply incBlockNamed_local_count in H
    | H: incLocalNamed ?n ?s1 ≡ inr (?s2, _) |- _ =>
      apply incLocalNamed_local_count in H
    | H: incVoid ?s1 ≡ inr (?s2, _) |- _ =>
      apply incVoid_local_count in H
    | H: incLocal ?s1 ≡ inr (?s2, _) |- _ =>
      apply incLocal_local_count in H
    | H: newLocalVar _ _ ?s1 ≡ inr (?s2, _) |- _ =>
      apply newLocalVar_local_count in H
    | H: dropVars _ ?s1 ≡ inr (?s2, _) |- _ =>
      apply dropVars_local_count in H

    | H: genNExpr ?n ?s1 ≡ inr (?s2, _) |- _ =>
      apply genNExpr_local_count in H
    | H: genMExpr ?m ?s1 ≡ inr (?s2, _) |- _ =>
      apply genMExpr_local_count in H
    | H: genAExpr ?a ?s1 ≡ inr (?s2, _) |- _ =>
      apply genAExpr_local_count in H
    | H: genWhileLoop _ _ _ _ _ _ _ _ _ _ ≡ inr _ |- _ =>
      apply genWhile_local_count in H
     | H: genIR ?op ?id ?s1 ≡ inr (?s2, _) |- _ =>
      apply genIR_local_count in H
    end.

Ltac get_block_count_hyps :=
  repeat
    match goal with
    | H: incBlockNamed ?n ?s1 ≡ inr (?s2, _) |- _ =>
      apply incBlockNamed_block_count in H
    | H: incLocalNamed ?n ?s1 ≡ inr (?s2, _) |- _ =>
      apply incLocalNamed_block_count in H
    | H: incVoid ?s1 ≡ inr (?s2, _) |- _ =>
      apply incVoid_block_count in H
    | H: incLocal ?s1 ≡ inr (?s2, _) |- _ =>
      apply incLocal_block_count in H
    | H: newLocalVar _ _ ?s1 ≡ inr (?s2, _) |- _ =>
      apply newLocalVar_block_count in H
    | H: dropVars _ ?s1 ≡ inr (?s2, _) |- _ =>
      apply dropVars_block_count in H

    | H: genNExpr ?n ?s1 ≡ inr (?s2, _) |- _ =>
      apply genNExpr_block_count in H
    | H: genMExpr ?m ?s1 ≡ inr (?s2, _) |- _ =>
      apply genMExpr_block_count in H
    | H: genAExpr ?a ?s1 ≡ inr (?s2, _) |- _ =>
      apply genAExpr_block_count in H
     | H: genIR ?op ?id ?s1 ≡ inr (?s2, _) |- _ =>
      apply genIR_block_count in H
    end.

Ltac solve_local_count := try solve [get_local_count_hyps; lia].

Ltac solve_block_count := try solve [get_block_count_hyps; lia].

Notation "s1 << s2" := (local_count s1 < local_count s2) (at level 50).
Notation "s1 <<= s2" := (local_count s1 <= local_count s2) (at level 50).

