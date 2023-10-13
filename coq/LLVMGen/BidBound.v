(** * Block labels and freshness frames

    Specialization of [VariableBinding] to block labels.
 *)
Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.VariableBinding.
Require Import Helix.LLVMGen.IdLemmas.
Require Import Helix.LLVMGen.StateCounters.

From Coq Require Import ZArith.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Opaque incBlockNamed.
Opaque incVoid.
Opaque incLocal.

Section BidBound.
  (* Block id has been generated by an earlier IRState *)
  Definition bid_bound (s : IRState) (bid: block_id) : Prop
    := state_bound block_count incBlockNamed s bid.

  (* If an id has been bound between two states.

     The primary use for this is in lemmas like, bid_bound_fresh,
     which let us know that since a id was bound between two states,
     it can not possibly collide with an id from an earlier state.
   *)
  Definition bid_bound_between (s1 s2 : IRState) (bid : block_id) : Prop
    := state_bound_between block_count incBlockNamed s1 s2 bid.

  Lemma incBlockNamed_count_gen_injective :
    count_gen_injective block_count incBlockNamed.
  Proof.
    unfold count_gen_injective.
    intros s1 s1' s2 s2' name1 name2 id1 id2 GEN1 GEN2 H1 H2 H3.

    Transparent incBlockNamed.
    inv GEN1.
    inv GEN2.
    Opaque incBlockNamed.
    cbn in *.

    intros CONTRA.
    apply Name_inj in CONTRA.
    apply valid_prefix_neq_differ in CONTRA; eauto.
  Qed.

  Lemma bid_bound_only_block_count :
    forall s lc vc γ bid,
      bid_bound s bid ->
      bid_bound {| block_count := block_count s; local_count := lc; void_count := vc; Γ := γ |} bid.
  Proof.
    intros s lc vc γ bid BOUND.
    destruct BOUND as (n1 & s1' & s1'' & N_S1 & COUNT_S1 & GEN_bid).
    unfold bid_bound.
    exists n1. exists s1'. exists s1''.
    repeat (split; auto).
  Qed.

  Lemma bid_bound_between_only_block_count_r :
    forall s1 s2 lc vc γ bid,
      bid_bound_between s1 s2 bid ->
      bid_bound_between s1 {| block_count := block_count s2; local_count := lc; void_count := vc; Γ := γ |} bid.
  Proof.
    intros s1 s2 lc vc γ bid BOUND.
    destruct BOUND as (n1 & s1' & s1'' & N_S1 & COUNT_S1 & GEN_bid).
    unfold bid_bound.
    exists n1. exists s1'. exists s1''.
    repeat (split; auto).
  Qed.

  Lemma bid_bound_mono : forall s1 s2 b,
      bid_bound s1 b ->
      (block_count s1 <= block_count s2)%nat ->
      bid_bound s2 b.
  Proof.
    intros; eapply state_bound_mono; eauto.
  Qed.

  Lemma bid_bound_fresh :
    forall (s1 s2 : IRState) (bid bid' : block_id),
      bid_bound s1 bid ->
      bid_bound_between s1 s2 bid' ->
      bid ≢ bid'.
  Proof.
    intros s1 s2 bid bid' BOUND BETWEEN.
    eapply state_bound_fresh; eauto.
    apply incBlockNamed_count_gen_injective.
  Qed.

  Lemma bid_bound_fresh' :
    forall (s1 s2 s3 : IRState) (bid bid' : block_id),
      bid_bound s1 bid ->
      (block_count s1 <= block_count s2)%nat ->
      bid_bound_between s2 s3 bid' ->
      bid ≢ bid'.
  Proof.
    intros s1 s2 s3 bid bid' BOUND COUNT BETWEEN.
    destruct BOUND as (n1 & s1' & s1'' & N_S1 & COUNT_S1 & GEN_bid).
    destruct BETWEEN as (n2 & sm' & sm'' & N_S2 & COUNT_Sm_ge & COUNT_Sm_lt & GEN_bid').

    inversion GEN_bid.
    destruct s1'. cbn in *.

    inversion GEN_bid'.
    intros CONTRA.
    apply Name_inj in CONTRA.
    apply valid_prefix_neq_differ in CONTRA; eauto.
    cbn.
    lia.
  Qed.

  Lemma bid_bound_bound_between :
    forall (s1 s2 : IRState) (bid : block_id),
      bid_bound s2 bid ->
      ~(bid_bound s1 bid) ->
      bid_bound_between s1 s2 bid.
  Proof.
    intros s1 s2 bid BOUND NOTBOUND.
    destruct BOUND as (n1 & s1' & s1'' & N_S1 & COUNT_S1 & GEN_bid).
    unfold bid_bound_between.
    exists n1. exists s1'. exists s1''.
    repeat (split; auto).
    pose proof (NatUtil.lt_ge_dec (block_count s1') (block_count s1)) as [LT | GE].
    - (* If this is the case, I must have a contradiction, which would mean that
         bid_bound s1 bid... *)
      assert (bid_bound s1 bid).
      unfold bid_bound.
      exists n1. exists s1'. exists s1''.
      auto.
      contradiction.
    - auto.
  Qed.

  Lemma bid_bound_between_bound_earlier :
    forall s1 s2 bid,
      bid_bound_between s1 s2 bid ->
      bid_bound s2 bid.
  Proof.
    intros s1 s2 bid BOUND.
    unfold bid_bound_between, state_bound_between in BOUND.
    destruct BOUND as (name & s1' & s2' & PREF' & COUNT1 & COUNT2 & GEN).
    exists name. exists s1'. exists s2'.
    repeat (split; auto).
  Qed.

  Lemma not_bid_bound_incBlockNamed :
    forall s1 s2 n bid,
      is_correct_prefix n ->
      incBlockNamed n s1 ≡ inr (s2, bid) ->
      ~ (bid_bound s1 bid).
  Proof.
    intros s1 s2 n bid NEND GEN BOUND.
    unfold bid_bound, state_bound in BOUND.
    destruct BOUND as (n' & s' & s'' & NEND' & COUNT & GEN').
    Transparent incBlockNamed.
    unfold incBlockNamed in *.
    Opaque incBlockNamed.
    cbn in *.
    simp.
    apply valid_prefix_string_of_nat_forward in H1; auto.
    lia.
  Qed.

  Lemma bid_bound_name :
    forall s1 n x,
      is_correct_prefix n ->
      bid_bound s1 (Name (n @@ string_of_nat x)) ->
      (x < block_count s1)%nat.
  Proof.
    intros s1 s2 n PREF BOUND.
    unfold bid_bound, state_bound in BOUND.
    destruct BOUND as (name & s' & s'' & PREF' & COUNT & GEN).
    cbn in GEN.
    inv GEN.
    eapply valid_prefix_string_of_nat_forward in H1; eauto; lia.
  Qed.

  Lemma bid_bound_incBlockNamed :
    forall name s1 s2 bid,
      is_correct_prefix name ->
      incBlockNamed name s1 ≡ inr (s2, bid) ->
      bid_bound s2 bid.
  Proof.
    intros name s1 s2 bid ENDS INC.
    exists name. exists s1. exists s2.
    repeat (split; auto).
    erewrite incBlockNamed_block_count with (s':=s2); eauto.
  Qed.

  Lemma incBlockNamed_bound_between :
    forall s1 s2 n bid,
      is_correct_prefix n ->
      incBlockNamed n s1 ≡ inr (s2, bid) ->
      bid_bound_between s1 s2 bid.
  Proof.
    intros s1 s2 n bid NEND GEN.
    apply bid_bound_bound_between.
    - eapply bid_bound_incBlockNamed; eauto.
    - eapply not_bid_bound_incBlockNamed; eauto.
  Qed.

  (* TODO: typeclasses for these mono lemmas to make automation easier? *)
  Lemma bid_bound_incVoid_mono :
    forall s1 s2 bid bid',
      bid_bound s1 bid ->
      incVoid s1 ≡ inr (s2, bid') ->
      bid_bound s2 bid.
  Proof.
    intros s1 s2 bid bid' BOUND INC.
    destruct BOUND as (n1 & s1' & s1'' & N_S1 & COUNT_S1 & GEN_bid).
    unfold bid_bound.
    exists n1. exists s1'. exists s1''.
    intuition.
    apply incVoid_block_count in INC.
    lia.
  Qed.

  Lemma bid_bound_incLocal_mono :
    forall s1 s2 bid bid',
      bid_bound s1 bid ->
      incLocal s1 ≡ inr (s2, bid') ->
      bid_bound s2 bid.
  Proof.
    intros s1 s2 bid bid' BOUND INC.
    destruct BOUND as (n1 & s1' & s1'' & N_S1 & COUNT_S1 & GEN_bid).
    unfold bid_bound.
    exists n1. exists s1'. exists s1''.
    intuition.
    apply incLocal_block_count in INC.
    lia.
  Qed.

  Lemma bid_bound_between_sep :
    ∀ (bid : block_id) s1 s2 s3,
      bid_bound_between s1 s2 bid → ¬ (bid_bound_between s2 s3 bid).
  Proof.
    intros. cbn in H. red in H.
    intro.
    assert (((bid ≡ bid) -> False) -> False). auto. apply H1. clear H1.
    eapply bid_bound_fresh; eauto.
    destruct H as (? & ? & ? & ? & ? & ? & ?).
    red. red. exists x. exists x0, x1. split; eauto.
  Qed.

  Lemma not_bid_bound_between :
    forall bid s1 s2, bid_bound s1 bid -> not (bid_bound_between s1 s2 bid).
  Proof.
    repeat intro.
    assert (((bid ≡ bid) -> False) -> False). auto. apply H1. clear H1.
    eapply bid_bound_fresh; eauto.
  Qed.

  Lemma bid_bound_newLocalVar_mono :
    forall s1 s2 bid bid' p x,
      bid_bound s1 bid ->
      newLocalVar p x s1 ≡ inr (s2, bid') ->
      bid_bound s2 bid.
  Proof.
    intros s1 s2 bid bid' * BOUND INC.
    destruct BOUND as (n1 & s1' & s1'' & N_S1 & COUNT_S1 & GEN_bid).
    unfold bid_bound.
    exists n1. exists s1'. exists s1''.
    intuition.
    apply newLocalVar_block_count in INC.
    lia.
  Qed.

  Lemma bid_bound_incBlock_neq:
    forall i i' bid bid',
      incBlock i ≡ inr (i', bid) ->
      bid_bound i bid' ->
      bid ≢ bid'.
  Proof.
    intros.
    destruct (rel_dec_p bid bid'); auto.
    subst; exfalso.
    cbn in H; inv H.
    destruct H0 as (? & ? & ? & ? & ? & ?).
    cbn in *.
    inv H1.
    apply valid_prefix_string_of_nat_forward in H4 as [? ?]; subst; cbn in *; auto.
    lia.
  Qed.

 Lemma bid_bound_incBlockNamed_mono :
    forall name s1 s2 bid bid',
      bid_bound s1 bid ->
      incBlockNamed name s1 ≡ inr (s2, bid') ->
      bid_bound s2 bid.
  Proof.
    intros name s1 s2 bid bid' BOUND INC.
    destruct BOUND as (n1 & s1' & s1'' & N_S1 & COUNT_S1 & GEN_bid).
    unfold bid_bound.
    exists n1. exists s1'. exists s1''.
    intuition.
    apply incBlockNamed_block_count in INC.
    lia.
  Qed.

  Lemma bid_bound_genNExpr_mono :
    forall s1 s2 bid nexp e c,
      bid_bound s1 bid ->
      genNExpr nexp s1 ≡ inr (s2, (e, c)) ->
      bid_bound s2 bid.
  Proof.
    intros s1 s2 bid nexp e c BOUND GEN.
    apply genNExpr_block_count in GEN.
    destruct BOUND as (n1 & s1' & s1'' & N_S1 & COUNT_S1 & GEN_bid).
    unfold bid_bound.
    exists n1. exists s1'. exists s1''.
    repeat (split; auto).
    rewrite GEN.
    auto.
  Qed.

  Lemma bid_bound_genMExpr_mono :
    forall s1 s2 bid mexp e c,
      bid_bound s1 bid ->
      genMExpr mexp s1 ≡ inr (s2, (e, c)) ->
      bid_bound s2 bid.
  Proof.
    intros s1 s2 bid mexp e c BOUND GEN.
    apply genMExpr_block_count in GEN.
    destruct BOUND as (n1 & s1' & s1'' & N_S1 & COUNT_S1 & GEN_bid).
    unfold bid_bound.
    exists n1. exists s1'. exists s1''.
    repeat (split; auto).
    rewrite GEN.
    auto.
  Qed.

  Lemma bid_bound_genAExpr_mono :
    forall s1 s2 bid aexp e c,
      bid_bound s1 bid ->
      genAExpr aexp s1 ≡ inr (s2, (e, c)) ->
      bid_bound s2 bid.
  Proof.
    intros s1 s2 bid nexp e c BOUND GEN.
    apply genAExpr_block_count in GEN.
    destruct BOUND as (n1 & s1' & s1'' & N_S1 & COUNT_S1 & GEN_bid).
    unfold bid_bound.
    exists n1. exists s1'. exists s1''.
    repeat (split; auto).
    rewrite GEN.
    auto.
  Qed.

  Lemma bid_bound_genIR_mono :
    forall s1 s2 bid op nextblock b bks,
      bid_bound s1 bid ->
      genIR op nextblock s1 ≡ inr (s2, (b, bks)) ->
      bid_bound s2 bid.
  Proof.
    intros s1 s2 bid op nextblock b bks BOUND GEN.
    apply genIR_block_count in GEN.
    destruct BOUND as (n1 & s1' & s1'' & N_S1 & COUNT_S1 & GEN_bid).
    unfold bid_bound.
    exists n1. exists s1'. exists s1''.
    repeat (split; auto).
    lia.
  Qed.

End BidBound.

#[global] Hint Resolve incBlockNamed_count_gen_injective : CountGenInj.

Ltac solve_bid_bound :=
  repeat
    match goal with
    | H: incBlockNamed ?msg ?s1 ≡ inr (?s2, ?bid) |-
      bid_bound ?s2 ?bid =>
      eapply bid_bound_incBlockNamed; try eapply H; solve_prefix
    | H: incBlock ?s1 ≡ inr (?s2, ?bid) |-
      bid_bound ?s2 ?bid =>
      eapply bid_bound_incBlockNamed; try eapply H; solve_prefix

    | H: incBlockNamed ?msg ?s1 ≡ inr (_, ?bid) |-
      ~(bid_bound ?s1 ?bid) =>
      eapply gen_not_state_bound; try eapply H; solve_prefix
    | H: incBlock ?s1 ≡ inr (_, ?bid) |-
      ~(bid_bound ?s1 ?bid) =>
      eapply gen_not_state_bound; try eapply H; solve_prefix

    (* Monotonicity *)
    | |- bid_bound {| block_count := block_count ?s; local_count := ?lc; void_count := ?vc; Γ := ?γ |} ?bid =>
      apply bid_bound_only_block_count

    | H: incVoid ?s1 ≡ inr (?s2, _) |-
      bid_bound ?s2 _ =>
      eapply bid_bound_incVoid_mono; try eapply H
    | H: incLocal ?s1 ≡ inr (?s2, _) |-
      bid_bound ?s2 _ =>
      eapply bid_bound_incLocal_mono; try eapply H
    | H: incBlockNamed _ ?s1 ≡ inr (?s2, _) |-
      bid_bound ?s2 _ =>
      eapply bid_bound_incBlockNamed_mono; try eapply H
    | H: incBlock ?s1 ≡ inr (?s2, _) |-
      bid_bound ?s2 _ =>
      eapply bid_bound_incBlockNamed_mono; try eapply H
    | H: genNExpr ?n ?s1 ≡ inr (?s2, _) |-
      bid_bound ?s2 _ =>
      eapply bid_bound_genNExpr_mono; try eapply H
    | H: genMExpr ?n ?s1 ≡ inr (?s2, _) |-
      bid_bound ?s2 _ =>
      eapply bid_bound_genMExpr_mono; try eapply H
    | H: genAExpr ?n ?s1 ≡ inr (?s2, _) |-
      bid_bound ?s2 _ =>
      eapply bid_bound_genAExpr_mono; try eapply H
    | H: genIR ?op ?n ?s1 ≡ inr (?s2, _) |-
      bid_bound ?s2 _ =>
      eapply bid_bound_genIR_mono; try eapply H
    | H : resolve_PVar _ _ ≡ inr _ |- _ =>
      apply resolve_PVar_state in H; subst
    end.


Ltac invert_err2errs :=
  match goal with
  | H : ErrorWithState.err2errS (MInt64asNT.from_nat ?n) ?s1 ≡ inr (?s2, _) |- _ =>
    destruct (MInt64asNT.from_nat n); inversion H; subst
  | H : ErrorWithState.err2errS (inl _) _ ≡ inr _ |- _ =>
    inversion H
  | H : ErrorWithState.err2errS (inr _) _ ≡ inr _ |- _ =>
    inversion H; subst
  end.

Ltac block_count_replace :=
  repeat match goal with
         | H : incVoid ?s1 ≡ inr (?s2, ?bid) |- _
           => apply incVoid_block_count in H; cbn in H
         | H : incBlockNamed ?name ?s1 ≡ inr (?s2, ?bid) |- _
           => apply incBlockNamed_block_count in H; cbn in H
         | H : incBlock ?s1 ≡ inr (?s2, ?bid) |- _
           => apply incBlockNamed_block_count in H; cbn in H
         | H : incLocal ?s1 ≡ inr (?s2, ?bid) |- _
           => apply incLocal_block_count in H; cbn in H
         | H: genNExpr ?n ?s1 ≡ inr (?s2, _) |- _
           => eapply genNExpr_block_count in H; cbn in H
         | H: genMExpr ?n ?s1 ≡ inr (?s2, _) |- _
           => eapply genMExpr_block_count in H; cbn in H
         | H: genAExpr ?n ?s1 ≡ inr (?s2, _) |- _
           => eapply genAExpr_block_count in H; cbn in H
         | H: genIR ?op ?nextblock ?s1 ≡ inr (?s2, _) |- _
           => eapply genIR_block_count in H; cbn in H
         end.

Ltac solve_block_count :=
  match goal with
  | |- (block_count ?s1 <= block_count ?s2)%nat
    => block_count_replace; cbn; lia
  | |- (block_count ?s1 >= block_count ?s2)%nat
    => block_count_replace; cbn; lia
  end.

Ltac solve_not_bid_bound :=
  match goal with
  | H: incBlockNamed ?name ?s1 ≡ inr (?s2, ?bid) |-
    ~(bid_bound ?s3 ?bid) =>
    eapply (not_id_bound_gen_mono incBlockNamed_count_gen_injective); [eassumption |..]
  | H: incBlock ?s1 ≡ inr (?s2, ?bid) |-
    ~(bid_bound ?s3 ?bid) =>
    eapply (not_id_bound_gen_mono incBlockNamed_count_gen_injective); [eassumption |..]
  end.

Ltac solve_count_gen_injective :=
  match goal with
  | |- count_gen_injective _ _
    => eauto with CountGenInj
  end.

Ltac big_solve :=
  repeat
    (try invert_err2errs;
     try solve_block_count;
     try solve_not_bid_bound;
     try solve_prefix;
     try solve_count_gen_injective;
     try match goal with
         | |- Forall _ (?x::?xs) =>
           apply Forall_cons; eauto
         | |- bid_bound_between ?s1 ?s2 ?bid =>
           eapply bid_bound_bound_between; solve_bid_bound
         | |- bid_bound_between ?s1 ?s2 ?bid ∨ ?bid ≡ ?nextblock =>
           try auto; try left
         end).

Lemma bid_bound_genIR_entry :
  forall op s1 s2 nextblock bid bks,
    genIR op nextblock s1 ≡ inr (s2, (bid, bks)) ->
    bid_bound s2 bid.
Proof.
  induction op;
    intros s1 s2 nextblock b bks GEN.
  10: {
    cbn in GEN; simp.
    eapply IHop1; eauto.
  }
  all: cbn in GEN; simp; solve_bid_bound.
Qed.

Section Inputs.

  (* Lemmas about the inputs to blocks *)
  Lemma inputs_bound_between :
    forall (op : DSHOperator) (s1 s2 : IRState) (nextblock op_entry : block_id) (bk_op : list (LLVMAst.block typ)),
      genIR op nextblock s1 ≡ inr (s2, (op_entry, bk_op)) ->
      Forall (bid_bound_between s1 s2) (inputs (convert_typ [ ] bk_op)).
  Proof.
    induction op;
      intros s1 s2 nextblock op_entry bk_op GEN;
      pose proof GEN as BACKUP_GEN;
      cbn in GEN; simp; cbn.
    all: try (solve [big_solve]).
    - big_solve; cbn in *; try solve_not_bid_bound; cbn in *; big_solve.

      rewrite convert_typ_ocfg_app.

      (* TODO: clean this up *)
      unfold tfmap.
      rewrite map_app.

      apply Forall_app.
      split.
      + eapply all_state_bound_between_shrink.
        eapply IHop; eauto.
        solve_block_count.
        solve_block_count.
      + cbn.
        rewrite List.Forall_cons_iff.
        split.
        2: { apply List.Forall_nil. }
        big_solve.
    - apply Forall_cons.
      + big_solve.
      + eapply Forall_impl.
        apply bid_bound_between_only_block_count_r.
        eapply all_state_bound_between_shrink.
        eapply IHop; eapply Heqs0.
        cbn. auto.
        block_count_replace.
        lia.
    - rewrite add_comment_inputs_typ.
      rewrite convert_typ_ocfg_app.

      unfold inputs.
      setoid_rewrite map_app.

      apply Forall_app.
      split.
      + eapply all_state_bound_between_shrink.
        eapply IHop1; eauto.
        all: solve_block_count.
      + eapply all_state_bound_between_shrink.
        eapply IHop2; eauto.
        all: solve_block_count.
  Qed.

  Lemma inputs_not_earlier_bound :
    forall (op : DSHOperator) (s1 s2 s3 : IRState) (bid nextblock op_entry : block_id) (bk_op : list (LLVMAst.block typ)),
      bid_bound s1 bid ->
      (block_count s1 <= block_count s2)%nat ->
      genIR op nextblock s2 ≡ inr (s3, (op_entry, bk_op)) ->
      Forall (fun x => x ≢ bid) (inputs (convert_typ [ ] bk_op)).
  Proof.
    intros op s1 s2 s3 bid nextblock op_entry bk_op BOUND COUNT GEN.
    pose proof (inputs_bound_between _ _ _ GEN) as BETWEEN.
    apply Forall_forall.
    intros x H.
    assert (bid ≢ x) as BIDX; auto.
    { eapply state_bound_fresh'.
      - apply incBlockNamed_count_gen_injective.
      - assert (bid_bound_between s2 s3 x).
        eapply Forall_forall. apply BETWEEN.
        auto.
        apply BOUND.
      - apply COUNT.
      - eapply Forall_forall.
        apply BETWEEN.
        auto.
    }
  Qed.

  (* TODO: may not actually needs this. *)
  Lemma inputs_nextblock :
    forall (op : DSHOperator) (s1 s2 s3 : IRState) (nextblock op_entry : block_id) (bk_op : list (LLVMAst.block typ)),
      bid_bound s1 nextblock ->
      (block_count s1 <= block_count s2)%nat ->
      genIR op nextblock s2 ≡ inr (s3, (op_entry, bk_op)) ->
      Forall (fun bid => bid ≢ nextblock) (inputs (convert_typ [ ] bk_op)).
  Proof.
    intros op s1 s2 s3 nextblock op_entry bk_op BOUND COUNT GEN.
    eapply inputs_not_earlier_bound; eauto.
  Qed.
End Inputs.

Section Outputs.
  Lemma entry_bound_between :
    forall (op : DSHOperator) (s1 s2 : IRState) (nextblock op_entry : block_id) (bk_op : list (LLVMAst.block typ)),
      genIR op nextblock s1 ≡ inr (s2, (op_entry, bk_op)) ->
      bid_bound_between s1 s2 op_entry.
  Proof.
    induction op;
      intros s1 s2 nextblock op_entry bk_op GEN;
      pose proof GEN as BACKUP_GEN;
      cbn in GEN; simp; cbn.
    all: try (solve [big_solve]).

    apply IHop1 in Heqs2.
    eapply state_bound_between_shrink; eauto.
    solve_block_count.
  Qed.

Opaque incBlockNamed.
Opaque incVoid.
Opaque incLocal.


  Lemma outputs_bound_between :
    forall (op : DSHOperator) (s1 s2 : IRState) (nextblock op_entry : block_id) (bk_op : list (LLVMAst.block typ)),
      genIR op nextblock s1 ≡ inr (s2, (op_entry, bk_op)) ->
      Forall (fun bid => bid_bound_between s1 s2 bid \/ bid ≡ nextblock) (outputs (convert_typ [ ] bk_op)).
  Proof.
    induction op;
      intros s1 s2 nextblock op_entry bk_op GEN;
      pose proof GEN as BACKUP_GEN;
      cbn in GEN; simp; cbn.
    all: try (solve [big_solve]).
    - cbn.
      clear BACKUP_GEN.
      cbn* in *; simp.
      rename i into s1, i6 into s2.
      rewrite convert_typ_ocfg_app.
      rewrite fold_left_app.
      cbn.
      clean_goal.

      assert (bid_bound_between s1 s2 b2) as B2.
      { eapply incBlockNamed_bound_between in Heqs3.
        eapply state_bound_between_shrink; eauto.
        solve_block_count.
        solve_block_count.
        reflexivity.
      }

      assert (bid_bound_between s1 s2 b0) as B0.
      { eapply entry_bound_between in Heqs2.
        eapply state_bound_between_shrink; eauto.
        solve_block_count.
        solve_block_count.
      }

      rewrite outputs_acc.
      (* Can probably prove stuff for b2 and nextblock to save space *)
      rewrite Forall_app.
      split.
      rewrite Forall_app.
      split.

      + auto.
      + epose proof (IHop _ _ _ _ _ Heqs2).

        (* TODO: may want to pull this out as a lemma *)
        eapply Forall_impl; [| eapply H].
        intros bid BOUND.
        destruct BOUND.
        * left.
          eapply state_bound_between_shrink; eauto.
          solve_block_count.
          solve_block_count.
        * left; subst.
          eapply incBlockNamed_bound_between in Heqs1.
          eapply state_bound_between_shrink; eauto.
          solve_block_count.
          reflexivity.
      + auto.
    -
      (* Should show me that the outputs of l (genIR op result) are all bound between s1 and i *)
      epose proof (IHop _ _ _ _ _ Heqs0).
      cbn in H.
      unfold outputs in H.

      cbn in Heqs; inversion Heqs; subst.

      rewrite outputs_acc.
      apply Forall_app.
      split.
      + apply Forall_cons; [|apply Forall_nil].
        cbn in Heqs.
        left.
        eapply entry_bound_between in Heqs0.
        eapply state_bound_between_shrink; eauto.
        cbn. solve_block_count.
      +
        (* TODO: may want to pull this out as a lemma *)
        assert (forall bid, bid_bound_between s1 i bid \/ bid ≡ nextblock -> bid_bound_between s1 i1 bid \/ bid ≡ nextblock) as WEAKEN.
        { intros bid BOUND.
          destruct BOUND.
          - left.
            eapply state_bound_between_shrink; eauto.
            solve_block_count.
          - right; auto.
        }

        eapply Forall_impl.
        * eapply WEAKEN.
        * eauto.
    - rewrite add_comment_outputs_typ.
      rewrite convert_typ_ocfg_app.
      setoid_rewrite outputs_app.
      apply Forall_app.
      split.
      +
        (* TODO: may want to pull this out as a lemma *)
        assert (forall bid, bid_bound_between i s2 bid \/ bid ≡ b -> bid_bound_between s1 s2 bid \/ bid ≡ nextblock) as WEAKEN.
        { intros bid BOUND.
          destruct BOUND.
          - left.
            eapply state_bound_between_shrink; eauto.
            solve_block_count.
          - left.
            eapply entry_bound_between in Heqs0.
            subst.
            eapply state_bound_between_shrink; eauto.
            solve_block_count.
        }

        eapply Forall_impl.
        * eapply WEAKEN.
        * eauto.
      +
        (* TODO: may want to pull this out as a lemma *)
        assert (forall bid, bid_bound_between s1 i bid \/ bid ≡ nextblock -> bid_bound_between s1 s2 bid \/ bid ≡ nextblock) as WEAKEN.
        { intros bid BOUND.
          destruct BOUND.
          - left.
            eapply state_bound_between_shrink; eauto.
            solve_block_count.
          - right; auto.
        }

        eapply Forall_impl.
        * eapply WEAKEN.
        * eauto.
  Qed.
End Outputs.

Ltac get_block_count_hyps :=
  repeat
    match goal with
    (* | H: incBlockNamed ?n ?s1 ≡ inr (?s2, _) |- _ => *)
      (* apply incBlockNamed_block_count in H *)
    (* | H: incLocalNamed ?n ?s1 ≡ inr (?s2, _) |- _ => *)
    (* apply incLocalNamed_block_count in H *)
    | H: resolve_PVar _ _ ≡ _ |- _ => apply resolve_PVar_state in H
    | H: incVoid ?s1 ≡ inr (?s2, _) |- _ =>
      apply incVoid_block_count in H
    | H: incLocal ?s1 ≡ inr (?s2, _) |- _ =>
      apply incLocal_block_count in H
    | H : genNExpr _ _ ≡ inr _ |- _ =>
      apply genNExpr_local_count in H
    | H: genMExpr ?m ?s1 ≡ inr (?s2, _) |- _ =>
      apply genMExpr_block_count in H
    | H: genAExpr ?a ?s1 ≡ inr (?s2, _) |- _ =>
      apply genAExpr_block_count in H
    | H: genIR ?op ?id ?s1 ≡ inr (?s2, _) |- _ =>
      apply genIR_block_count in H
    end.

(* This establishes that the generated code does not contain any two blocks with the same id. *)
Transparent incBlockNamed.
Lemma generates_wf_ocfg_bids :
  ∀ (op : DSHOperator) (s1 s2 : IRState) (nextblock b : block_id) (bk_op : list (LLVMAst.block typ)),
    bid_bound s1 nextblock ->
    genIR op nextblock s1 ≡ inr (s2, (b, bk_op)) →
    wf_ocfg_bid bk_op.
Proof.
  induction op; intros * NEXT GEN.
  - cbn* in *; simp; cbn.
    eapply wf_ocfg_bid_singleton.
  - cbn* in *; simp; cbn in *.
    eapply wf_ocfg_bid_singleton.
  - destruct NEXT as (? & [?bid ? ? ?] & [?bid ? ? ?] & ? & ? & ?).
    cbn* in *.
    simp.
    cbn* in *; simp; cbn in *.
    clean_goal.
    get_block_count_hyps; subst; cbn in *.
    repeat match goal with
           | h: IRState |- _ => destruct h as [?bid ? ? ?]
           end; cbn in *.
    subst.
    eapply wf_ocfg_bid_cons'.
    { cbn.
      intuition;
        match goal with
        | h: Name _ ≡ Name _ |- _ => apply Name_inj in h; inv h
        end.
    }
    eapply wf_ocfg_bid_cons'.
    { cbn.
      intuition;
        match goal with
        | h: Name _ ≡ Name _ |- _ => apply Name_inj in h; inv h
        end.
    }
    eapply wf_ocfg_bid_cons'.
    { cbn.
      intuition;
        match goal with
        | h: Name _ ≡ Name _ |- _ => apply Name_inj in h; inv h
        end.
    }
    eapply wf_ocfg_bid_singleton.
  - destruct NEXT as (? & [?bid ? ? ?] & [?bid ? ? ?] & ? & ? & ?).
    cbn* in *.
    simp.
    cbn* in *; simp; cbn in *.
    clean_goal.
    get_block_count_hyps; subst; cbn in *.
    repeat match goal with
           | h: IRState |- _ => destruct h as [?bid ? ? ?]
           end; cbn in *.
    subst.
    eapply wf_ocfg_bid_cons'.
    { cbn.
      intuition;
        match goal with
        | h: Name _ ≡ Name _ |- _ => apply Name_inj in h; inv h
        end.
    }
    eapply wf_ocfg_bid_cons'.
    { cbn.
      intuition;
        match goal with
        | h: Name _ ≡ Name _ |- _ => apply Name_inj in h; inv h
        end.
    }
    eapply wf_ocfg_bid_cons'.
    { cbn.
      intuition;
        match goal with
        | h: Name _ ≡ Name _ |- _ => apply Name_inj in h; inv h
        end.
    }
    eapply wf_ocfg_bid_singleton.

  - destruct NEXT as (? & [?bid ? ? ?] & [?bid ? ? ?] & ? & ? & ?).
    cbn* in *.
    simp.
    cbn* in *; simp; cbn in *.
    clean_goal.
    get_block_count_hyps; subst; cbn in *.
    repeat match goal with
           | h: IRState |- _ => destruct h as [?bid ? ? ?]
           end; cbn in *.
    subst.
    eapply wf_ocfg_bid_cons'.
    { cbn.
      intuition;
        match goal with
        | h: Name _ ≡ Name _ |- _ => apply Name_inj in h; inv h
        end.
    }
    eapply wf_ocfg_bid_cons'.
    { cbn.
      intuition;
        match goal with
        | h: Name _ ≡ Name _ |- _ => apply Name_inj in h; inv h
        end.
    }
    eapply wf_ocfg_bid_cons'.
    { cbn.
      intuition;
        match goal with
        | h: Name _ ≡ Name _ |- _ => apply Name_inj in h; inv h
        end.
    }
    eapply wf_ocfg_bid_singleton.

  - destruct NEXT as (? & [?bid ? ? ?] & [?bid ? ? ?] & ? & ? & ?).
    cbn* in *.
    simp.
    cbn* in *; simp; cbn in *.
    clean_goal.
    get_block_count_hyps; subst; cbn in *.
    repeat match goal with
           | h: IRState |- _ => destruct h as [?bid ? ? ?]
           end; cbn in *.
    subst.
    eapply wf_ocfg_bid_cons'.
    { cbn.
      intuition;
        match goal with
        | h: Name _ ≡ Name _ |- _ => apply Name_inj in h; inv h
        end.
    }
    eapply wf_ocfg_bid_cons'.
    { cbn.
      intuition;
        match goal with
        | h: Name _ ≡ Name _ |- _ => apply Name_inj in h; inv h
        end.
    }
    eapply wf_ocfg_bid_cons'.
    { cbn.
      intuition;
        match goal with
        | h: Name _ ≡ Name _ |- _ => apply Name_inj in h; inv h
        end.
    }
    eapply wf_ocfg_bid_singleton.

  - cbn* in *.
    simp.
    clean_goal.

    pose proof Heqs1.
    eapply inputs_bound_between in H.

    apply IHop in Heqs1.
    2:{
      eapply bid_bound_incBlockNamed with (name := "Loop_lcont")
                                         (s1 := {|
                                             block_count := (block_count i);
                                             local_count := S (local_count i);
                                             void_count := void_count i;
                                             Γ := (ID_Local (Name ("Loop_i" @@ string_of_nat (local_count i))), TYPE_I 64%N) :: Γ i |}); reflexivity.
    }
    clear IHop; clean_goal.
    cbn in *.
    simp.
    cbn in *.
    eapply wf_ocfg_bid_cons'.
    { cbn.
      intuition.
      match goal with
      | h: Name _ ≡ Name _ |- _ =>
        apply Name_inj in h;
          first [now inv h | apply valid_prefix_string_of_nat_forward in h as [abs _]; intuition]
      end.

      rewrite map_app in H1.
      eapply in_app_or in H1.
      destruct H1.
      - rewrite inputs_convert_typ in H.

        eapply Forall_forall in H0; eauto.
        eapply bid_bound_between_bound_earlier in H0.

        eapply bid_bound_name in H0; [lia | solve_prefix].
      - cbn in H0. destruct H0; inversion H0.
    }

    (* TODO: Automate this... *)
    eapply wf_ocfg_bid_cons'.
    { cbn.
      intuition.

      rewrite inputs_app in H0.
      eapply in_app_or in H0.
      destruct H0.
      - rewrite inputs_convert_typ in H.

        eapply Forall_forall in H0; eauto.
        eapply bid_bound_between_bound_earlier in H0.

        eapply bid_bound_name in H0; [lia | solve_prefix].
      - cbn in H0. destruct H0; inversion H0.
    }

    unfold wf_ocfg_bid.
    rewrite inputs_app. cbn.
    apply Coqlib.list_norepet_append; eauto.

    { constructor.
      intros CONTRA; inv CONTRA.
      constructor.
    }

    unfold Coqlib.list_disjoint.
    intros x y H0 H1.

    cbn in H1. destruct H1; inv H1.

    rewrite inputs_convert_typ in H.

    eapply Forall_forall in H0; eauto.

    destruct H0 as (name & s' & s'' & PREF & COUNT & GEN).
    cbn in GEN; inv GEN.
    intros NAME. inv H1.
    rename H4 into NAME.
    apply Name_inj in NAME.
    eapply valid_prefix_string_of_nat_forward in NAME; eauto.
    destruct NAME; subst.
    lia.

  - rename nextblock into entryblock, b into nextblock.
    simpl in GEN.
    break_match_hyp; [simp |].
    inv GEN.
    break_match_hyp; [simp |].
    destruct s1 as [bid1  lid1  void1  Γ1]; cbn in *.
    destruct NEXT as (? & [?bid ? ? ?] & [?bid ? ? ?] & ? & ? & ?); cbn in *.
    inv H1; cbn in *.
    destruct p as [s' [bblock bcode]].
    destruct s' as [bid2  lid2  void2  Γ2]; cbn in *.
    simp.
    cbn* in *; simp; cbn in *.
    clean_goal.
    cbn* in *; simp; cbn in *.
    generalize Heqs0; intros GEN.
    apply genIR_block_count in Heqs0.
    cbn in *.
    assert (BOUND:bid_bound
                    {|
                      block_count := bid1;
                      local_count := S lid1;
                      void_count := void1;
                      Γ := (ID_Local (Name ("a" @@ string_of_nat lid1)),
                            TYPE_Pointer (TYPE_Array (Z.to_N (Int64.intval size)) TYPE_Double)) :: Γ1 |}
                    (Name (x @@ string_of_nat bid))).
    {
      do 2 red.
      exists x.
      exists {|
          block_count := bid;
          local_count := S lid1;
          void_count := void1;
          Γ := (ID_Local (Name ("a" @@ string_of_nat lid1)),
                TYPE_Pointer (TYPE_Array (Z.to_N (Int64.intval size)) TYPE_Double)) :: Γ1 |}.
      eexists; repeat split; cbn; eauto.
    }
    generalize GEN; intros WF;
    apply IHop in WF; auto; clear IHop.
    apply wf_ocfg_bid_cons'; auto; clear WF.
    cbn.
    cbn in *; intros abs; apply ListUtil.in_map_elim in abs as (? & ? & ?).
    cbn in *.
    clean_goal.

    eapply inputs_bound_between in GEN.
    rewrite inputs_convert_typ in GEN.

    assert (In (blk_id x0) (map blk_id bcode)).
    { apply in_map; eauto. }

    eapply Forall_forall in GEN; eauto.
    rewrite <- H2 in GEN.
    destruct GEN as (n & s' & s'' & PREF & COUNT1 & COUNT2 & GEN').
    cbn in *.

    inv GEN'.
    eapply valid_prefix_string_of_nat_forward in H6; eauto.
    destruct H6; subst.
    lia.
  - rename nextblock into entryblock, b into nextblock.
    simpl in GEN.
    break_match_hyp; [simp |].
    inv GEN.
    break_match_hyp; [simp |].
    destruct s1 as [bid1  lid1  void1  Γ1]; cbn in *.
    destruct NEXT as (? & [?bid ? ? ?] & [?bid ? ? ?] & ? & ? & ?); cbn in *.
    inv H1; cbn in *.
    destruct p as [s' [bblock bcode]].
    destruct s' as [bid2  lid2  void2  Γ2]; cbn in *.
    simp.
    cbn* in *; simp; cbn in *.
    clean_goal.
    cbn* in *; simp; cbn in *.
    generalize Heqs0; intros GEN.
    apply resolve_PVar_state in Heqs0.
    inv Heqs0.
    cbn in *.

    apply wf_ocfg_bid_cons'; cbn.
    { intros CONTRA.
      destruct CONTRA; inv H1.
      inv H2.
      inv H2.
      inv H1.
      auto.
    }

    apply wf_ocfg_bid_cons'; cbn.
    { intros CONTRA.
      destruct CONTRA; inv H1.
      inv H2.
      inv H2.
    }

    apply wf_ocfg_bid_cons'; cbn.
    { intros CONTRA.
      destruct CONTRA; auto.

      rename H1 into NAME.
      eapply Name_inj in NAME.
      eapply valid_prefix_string_of_nat_forward in NAME; eauto.
      destruct NAME. inv H2.
    }

    unfold wf_ocfg_bid.
    cbn.
    constructor.
    auto.
    constructor.
  - rename nextblock into entryblock, b into nextblock.
    simpl in GEN.
    break_match_hyp; [simp |].
    inv GEN.
    break_match_hyp; [simp |].
    destruct s1 as [bid1  lid1  void1  Γ1]; cbn in *.
    destruct NEXT as (? & s' & s'' & ? & ? & ?); cbn in *.
    inv H1; cbn in *.
    destruct p as [s''' [bblock bcode]].
    simp.
    cbn* in *; simp; cbn in *.
    clean_goal.
    cbn* in *; simp; cbn in *.
    generalize Heqs0; intros GEN.
    apply genIR_block_count in Heqs0.
    cbn in *.

    unfold wf_ocfg_bid.
    unfold add_comment; cbn.
    break_match_goal.
    constructor.
    cbn.

    pose proof Heqs1 as OP1BOUND; eapply inputs_bound_between in OP1BOUND.
    pose proof GEN as OP2BOUND; eapply inputs_bound_between in OP2BOUND.

    eapply IHop1 in Heqs1.
    eapply IHop2 in GEN.

    change (blk_id b :: map blk_id l0) with (map blk_id (b :: l0)).
    rewrite <- Heql0.

    rewrite map_app.
    rewrite inputs_convert_typ in *.

    {  apply Coqlib.list_norepet_append_commut.
       unfold wf_ocfg_bid in *.
       eapply state_bound_between_disjoint_norepet; eauto.
       apply incBlockNamed_count_gen_injective.
    }

    { exists x. do 2 eexists.
      repeat split; eauto.
    }

    { eapply bid_bound_genIR_entry; eauto.
    }
Qed.

Lemma genWhileLoop_entry_in_scope : forall op b s1 s2 entry_body bodyV,
    genIR op b s1 ≡ inr (s2, (entry_body, bodyV)) ->
    In entry_body (inputs bodyV).
Proof.
  induction op; intros *; try (cbn; intros GEN; clear -GEN; simp; cbn; auto; fail).
  cbn; intros GEN; simp.
  rewrite add_comment_inputs, inputs_app.
  apply ListUtil.in_appl; eauto.
Qed.
