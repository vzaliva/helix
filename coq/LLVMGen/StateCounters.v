(** * Compilation units and IRState

    This file contains a bunch of lemmas describing how various compilation subroutines
    impact the [IRStated].

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

(* TODO: Move this? *)
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

(* TODO: Move this? *)
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

(* TODO: uncertain if this belongs somewhere else *)
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

Lemma incLocalNamed_local_count: forall s s' msg x,
    incLocalNamed msg s ≡ inr (s',x) ->
    local_count s' ≡ S (local_count s).
Proof.
  intros; cbn in *; inv_sum; reflexivity.
Qed.

(* We define the obvious total order on IRStates *)
Definition IRState_lt (s1 s2 : IRState) : Prop :=
  (local_count s1 < local_count s2)%nat.
Infix "<<" := IRState_lt (at level 10).

Definition IRState_le (s1 s2 : IRState) : Prop :=
  (local_count s1 <= local_count s2)%nat.
Infix "<<=" := IRState_le (at level 10).

Lemma incLocal_lt : forall s1 s2 x,
    incLocal s1 ≡ inr (s2,x) ->
    s1 << s2.
Proof.
  intros s1 s2 x INC.
  apply incLocal_local_count in INC.
  unfold IRState_lt.
  lia.
Qed.

Create HintDb irs_lt.
Hint Resolve incLocal_lt : irs_lt.

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

Arguments append: simpl never.
Opaque incBlockNamed.
Opaque incVoid.
Opaque incLocal.

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

Lemma genIR_local_count :
  forall op s1 s2 nextblock b bk_op,
    genIR op nextblock s1 ≡ inr (s2, (b, bk_op)) ->
    local_count s2 ≥ local_count s1.
Proof.
  induction op; intros; cbn in H; simp; __local_ltac; lia. 
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

Transparent incBlockNamed.
Lemma incBlockNamed_Γ:
  forall s s' msg id,
    incBlockNamed msg s ≡ inr (s', id) ->
    Γ s' ≡ Γ s.
Proof.
  intros; cbn in *; inv_sum; reflexivity.
Qed.

Lemma incBlockNamed_block_count:
  forall s s' msg id,
    incBlockNamed msg s ≡ inr (s', id) ->
    block_count s' ≡ S (block_count s).
Proof.
  intros; cbn in *; inv_sum; reflexivity.
Qed.
Opaque incBlockNamed.

Ltac __local_ltac' :=
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
     end; cbn in *).

Lemma genIR_block_count :
  forall op s1 s2 nextblock b bk_op,
    genIR op nextblock s1 ≡ inr (s2, (b, bk_op)) ->
    block_count s2 ≥ block_count s1.
Proof.
  induction op; intros; cbn in H; simp; __local_ltac'; lia. 
Qed.

Transparent incBlockNamed.
Transparent incVoid.
Transparent incLocal.

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
    | H: genNExpr ?n ?s1 ≡ inr (?s2, _) |- _ =>
      apply genNExpr_local_count in H
    | H: genMExpr ?m ?s1 ≡ inr (?s2, _) |- _ =>
      apply genMExpr_local_count in H
    | H: genAExpr ?a ?s1 ≡ inr (?s2, _) |- _ =>
      apply genAExpr_local_count in H
    | H: genIR ?op ?id ?s1 ≡ inr (?s2, _) |- _ =>
      apply genIR_local_count in H
    end.

Ltac solve_local_count_tac := try solve [unfold IRState_lt, IRState_le in *; get_local_count_hyps; lia].

Ltac solve_local_count :=
  match goal with
  | |- (local_count ?s1 > local_count ?s2)%nat =>
    solve_local_count_tac
  | |- (local_count ?s1 < local_count ?s2)%nat =>
    solve_local_count_tac
  | |- (local_count ?s1 >= local_count ?s2)%nat =>
    solve_local_count_tac
  | |- (local_count ?s1 <= local_count ?s2)%nat =>
    solve_local_count_tac
  | |- ?s1 << ?s2 =>
    solve_local_count_tac
  | |- ?s1 <<= ?s2 =>
    solve_local_count_tac
  | |- local_count ?s1 ≡ local_count ?s2 =>
    solve_local_count_tac
  | |- local_count ?s1 ≢ local_count ?s2 =>
    solve_local_count_tac
  end.

