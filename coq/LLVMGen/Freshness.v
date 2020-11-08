Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.IdLemmas.
Require Import Helix.LLVMGen.VariableBinding.
Require Import Helix.LLVMGen.LidBound.
Require Import Helix.LLVMGen.StateCounters.

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

(** * Freshness scheme
    We axiomatize in this file everything we need to reason
    about VIR identifiers generated by the compiler. We need to do some
    annoyingly fine grained reasoning due to:
    - the freshness monad employed being quite simple (it uses a strictly
    monotonic seed, and hence do not allow for introducing new fresh idents in a
    previously generated window)
    - however the compiler has to generate code in the opposite order of evaluation
    (for the sequence case), hence forcing us to explicitly reason about windows of
    freshness
 *)

Definition extends (s1 s2 : IRState) (l1 : local_env) : local_env -> Prop :=
  fun l2 =>
    l1 ⊑ l2 /\
    forall id v,
      alist_In id l2 v ->
      ~ alist_In id l1 v ->
      lid_bound_between s1 s2 id.

(* The freshness precondition of a computation [c] such that
   "gen_computation c s1 = T(c), s2"
   It states that the scope of variables generated by the seeds contained in [s1;s2]
   is currently fresh in the initial local state.
   i.e. dom(l) ∩ [s1;s2] = ∅
 *)
Definition is_fresh (s1 s2 : IRState) : local_env -> Prop :=
  fun l => (forall id v, alist_In id l v -> ~(lid_bound_between s1 s2 id)). 

(* The freshness postcondition of the same computation as above.
   It is this time parameterized additionally by the local state from which we
   started the computation, and asserts that all extensions to the domain of l
   that we have performed has been taken from the freshness window provided.
   i.e. dom(l2) \ dom(l1) ⊆ [s1;s2]
 *)
Definition freshness_post (s1 s2 : IRState) (l1 : local_env) : local_env -> Prop :=
  fun l2 => (forall id v, alist_In id l2 v -> ~(alist_In id l1 v) -> lid_bound_between s1 s2 id).

(** ** Fresh identifier generator invariant
      Low and high level invariants ensuring that calls to [incLocal] indeed generate fresh variables.
 *)
Definition incLocal_fresh (l : local_env) (s : IRState) : Prop :=
  forall s' id, incLocal s ≡ inr (s',id) ->
           alist_fresh id l.

Definition concrete_fresh_inv (s : IRState) : config_cfg -> Prop :=
  fun '(_, (l,g)) =>
    forall id v n, alist_In id l v -> n >= local_count s -> id <> Name ("l" @@ string_of_nat n).

(* We need to preserve the concrete invariant, but it is sufficient to get the abstract one of interest *)
Lemma concrete_fresh_fresh: forall s memV l g,
    concrete_fresh_inv s (memV,(l,g)) ->
    incLocal_fresh l s.
Proof.
  intros * FRESH ? ? LU.
  unfold incLocal, incLocalNamed in LU; cbn in *; inv LU.
  unfold alist_fresh.
  match goal with
  | |- ?x ≡ None => destruct x eqn:EQ; auto; exfalso
  end.
  eapply FRESH; eauto.
Qed.

(** * Freshness interface

Let us note FP (resp. FQ) for is_fresh (resp. freshness_post). We have the following lemmas axiomatizing how these two predicates evolve.

     P1. FP s s l

     i.e.  if we give ourself an empty freshness window, the precondition is trivially true
     [is_fresh_empty_window]

     P2. FP s1 s3 l ->
         s2 << s3 ->
         FP s1 s2 l

     i.e. we can always shrink the freshness window
     [is_fresh_shrink_up]

     P3. FP s1 s2 l ->
         incLocal s1 = (s2,r) ->
         alist_fresh r l

     i.e. the whole point of the endeavor, the freshness window indeed generates fresh ids 
     [is_fresh_alist_fresh]

     Q1. FQ s1 s2 l l

     i.e. if we don't extend the state, the postcondition is trivially true
     [freshness_pots_no_extension]

     Q2. FQ s1 s2 l1 l2 ->
         FQ s2 s3 l2 l3 ->
         FQ s1 s3 l1 l3

     i.e. the postcondition is transitive
     [freshness_post_transitive]

     Q3: incLocal s1 = (s2,r) ->
         FQ s1 s2 l l[r->v]

     i.e. the postcondition is compatible with extension by generated variables
     [freshness_post_incLocal]

     PQ. FP s1 s3 l1 ->
         FQ s1 s2 l1 l2 ->
         FP s2 s3 l2

     i.e. linking the pre and postcondition: if we have the precondition for a long computation,
                                 and establish the postcondition at a mid point, we can recover the precondition at this point for the remaining of the computation.
                                 (freshness_chain)

 *)

Section Freshness_Interface.

  (** * P1 *)
  Lemma is_fresh_empty_window :
    forall s l,
      is_fresh s s l.
  Proof.
    intros; red; intros.
    unfold lid_bound_between, state_bound_between.
    intros (? & ? & ? & ? & ? & ?).
    lia.
  Qed.

  (** * P2 *)
  Lemma is_fresh_shrink_up:
    forall s1 s2 s3 l,
      is_fresh s1 s3 l ->
      s2 <<= s3 ->
      is_fresh s1 s2 l.
  Proof.
    intros s1 s2 s3 l FRESH LT.
    unfold is_fresh in *.
    intros id v AIN BOUND.

    eapply (FRESH _ _ AIN).
    eapply state_bound_between_shrink; eauto.
  Qed.

  Lemma is_fresh_shrink:
    forall s1 s2 s3 s4 l,
      is_fresh s1 s4 l ->
      s1 <<= s2 ->
      s3 <<= s4 ->
      is_fresh s2 s3 l.
  Proof.
    intros s1 s2 s3 s4 l FRESH LE1 LE2.
    unfold is_fresh in *.
    intros id v AIN BOUND.

    eapply (FRESH _ _ AIN).
    eapply state_bound_between_shrink; eauto.
  Qed.

  Lemma freshness_fresh: forall s1 s2 l,
      is_fresh s1 s2 l ->
      s1 << s2 ->
      incLocal_fresh l s1.
  Proof.
    intros * NIN LT.
    unfold incLocal_fresh.
    intros s' id GEN.

    (* id is bound in s', which should be between s1 and s2 *)
    assert (lid_bound_between s1 s2 id) as BETWEEN.
    { eapply state_bound_between_shrink.
      -  apply lid_bound_between_incLocal; eauto.
      - lia.
      - unfold IRState_lt in LT.
        apply incLocal_local_count in GEN.
        lia.
    }

    unfold alist_fresh.
    apply alist_find_None.
    intros v IN'.
    eapply In__alist_In in IN'.
    destruct IN' as (v' & IN).
    apply NIN in IN.
    contradiction.
    Unshelve.
    exact Logic.eq.
  Qed.

  Lemma is_fresh_alist_fresh_gen:
    forall s1 s' s2 l id,
      s1 << s2 ->
      is_fresh s1 s2 l ->
      incLocal s1 ≡ inr (s',id) ->
      alist_fresh id l.
  Proof.
    intros * ? ? INCL. 
    eapply freshness_fresh in INCL; eauto.
  Qed.

  (** * P3 *)
  Lemma is_fresh_alist_fresh :
    forall s1 s2 l id,
      is_fresh s1 s2 l ->
      incLocal s1 ≡ inr (s2,id) ->
      alist_fresh id l.
  Proof.
    intros * ? INCL.
    eapply is_fresh_alist_fresh_gen; eauto with irs_lt.
  Qed.

  Lemma is_fresh_incLocal:
    forall s1 s2 s3 r v l,
      incLocal s1 ≡ inr (s2, r) ->
      is_fresh s1 s3 l ->
      is_fresh s2 s3 (alist_add r v l).
  Proof.
    intros * INC FRESH.
    unfold is_fresh in *.
    pose proof INC as INCBAK.
    eapply gen_state_bound_between in INC;
      eauto using incLocalNamed_count_gen_injective, incLocalNamed_count_gen_mono.
    2: solve_not_ends_with.

    intros id v0 H.
    intros BOUND.

    assert ({r ≡ id} + {r ≢ id}) as [eqr | neqr] by apply rel_dec_p.
    - subst.
      eapply (state_bound_between_id_separate incLocalNamed_count_gen_injective INC BOUND).
      auto.
    - apply In_add_In_ineq in H; eauto.
      apply FRESH in H.
      apply H.
      eapply incLocal_local_count in INCBAK.
      eapply state_bound_between_shrink; eauto.
      lia.
  Qed.

  (** * Q1 *)
  Lemma freshness_post_no_extension: forall s1 s2 l, freshness_post s1 s2 l l.
  Proof.
    intros; red; intros.
    intuition.
  Qed.

  (** * Q2 *)
  Lemma freshness_post_transitive :
    forall s1 s2 s3 l1 l2 l3,
      freshness_post s1 s2 l1 l2 ->
      freshness_post s2 s3 l2 l3 ->
      s1 <<= s2 ->
      s2 <<= s3 ->
      freshness_post s1 s3 l1 l3.
  Proof.
    intros s1 s2 s3 l1 l2 l3 FRESH1 FRESH2 LT1 LT2.
    unfold freshness_post in *.
    intros id v AIN ANIN.

    destruct (alist_In_dec id l2 v) as [INl2 | NINl2].
    - pose proof (FRESH1 _ _ INl2 ANIN).
      eapply state_bound_between_shrink; eauto.
    - pose proof (FRESH2 _ _ AIN NINl2).
      eapply state_bound_between_shrink; eauto.
  Qed.

  (** * Q3 *)
  Lemma freshness_post_inclocal : forall s1 s2 l x v,
      incLocal s1 ≡ inr (s2,x) ->
      freshness_post s1 s2 l (alist_add x v l).
  Proof.
    intros * INC.
    cbn in *.
    apply lid_bound_between_incLocal in INC.
    red; intros.
    destruct (id ?[ Logic.eq ] x) eqn:EQ.
    - rewrite rel_dec_correct in EQ; subst; auto.
    - apply neg_rel_dec_correct in EQ.
      apply In_add_In_ineq in H; auto.
      intuition.
  Qed.

  Lemma freshness_post_incVoid : forall s1 s2 s3 r l l',
      incVoid s2 ≡ inr (s3,r) ->
      freshness_post s1 s2 l l' ->
      freshness_post s1 s3 l l'.
  Proof.
    unfold freshness_post. 
    intros * INC FRESH * IN NIN.
    cbn in *.
    inv INC.
    do 2 red.
    edestruct FRESH; eauto.
  Qed.
  
  (** * PQ *)
  Lemma freshness_chain: forall s1 s2 s3 l1 l2 ,
      is_fresh s1 s3 l1 ->
      freshness_post s1 s2 l1 l2 ->
      s1 <<= s2 ->
      is_fresh s2 s3 l2.
  Proof.
    intros s1 s2 s3 l1 l2 PRE POST LT.
    unfold is_fresh in *.
    unfold freshness_post in *.
    intros id v AIN BOUND.

    destruct (alist_In_dec id l1 v) as [INl1 | NINl1].
    - eapply (PRE _ _ INl1).
      eapply state_bound_between_shrink; eauto.
    - pose proof (POST _ _ AIN NINl1) as BOUND'.
      eapply state_bound_between_separate.
      3: eapply BOUND.
      2: eapply BOUND'.

      apply incLocalNamed_count_gen_injective.
      all: auto.
  Qed.

End Freshness_Interface.

(* Tactic to solve goals of the shape [alist_fresh]  *)
Ltac solve_alist_fresh :=
  (eapply is_fresh_alist_fresh; now eauto with irs_lt).

(* Tactic to solve goals of the shape l ⊑ l' *)
Ltac solve_sub_alist :=
  (reflexivity
   || (apply sub_alist_add; solve_alist_fresh)
   || (etransitivity; try eassumption; []; solve_sub_alist)
  ).


Create HintDb fresh.
Hint Resolve freshness_post_no_extension: fresh.
Hint Resolve freshness_post_inclocal : fresh.

Definition lift_fresh (P: local_env -> Prop) : Rel_cfg := fun _ '(_,(l,_)) => P l.

Notation fresh_pre := (fun s1 s2 => lift_fresh (is_fresh s1 s2)). 
Notation fresh_post := (fun s1 s2 l => lift_fresh (freshness_post s1 s2 l)). 
Ltac splits :=
  repeat match goal with
         | |- _ /\ _ => split
         | |- (_ ⩕ _) _ _ => split
         end.

Arguments is_fresh : simpl never.
Arguments freshness_post : simpl never.
Arguments lift_fresh /.

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
  end.

(* Tactic to solve freshness goals *)
Ltac solve_fresh :=
  cbn;
  eauto with fresh;
  match goal with
  | h: is_fresh ?s ?s' ?l |- is_fresh ?s _ ?l => apply is_fresh_shrink_up with (1 := h); solve_local_count
  | h: is_fresh _ ?s _ |- is_fresh _ ?s _ => apply freshness_chain with (1 := h); try solve_local_count; solve_fresh
  | h: freshness_post _ ?s _ ?x |- is_fresh ?s _ ?x => eapply freshness_chain with (2 := h); try solve_local_count; solve_fresh
  | |- freshness_post _ _ _ (alist_add _ _ _) => first [eassumption | eapply freshness_post_inclocal; eassumption | eapply freshness_post_transitive; [ | eapply freshness_post_inclocal; eassumption | solve_local_count | solve_local_count]]; solve_fresh
  | |- freshness_post _ _ _ _ => first [eassumption | eapply freshness_post_transitive; [eassumption | | solve_local_count | solve_local_count]]; solve_fresh
  end.