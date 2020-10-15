Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.
Require Import Helix.LLVMGen.Correctness_MExpr.
Require Import Helix.LLVMGen.IdLemmas.
Require Import Helix.LLVMGen.StateCounters.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Global Opaque resolve_PVar.

(** Reasoning about when identifiers are bound in certain states *)
Section StateBound.
  Variable count :  IRState -> nat.
  Variable gen : string -> cerr raw_id.

  (* TODO: Injective is sort of a lie... Is there a better thing to call this? *)
  Definition count_gen_injective : Prop
    := forall s1 s1' s2 s2' name1 name2 id1 id2,
      inr (s1', id1) ≡ gen name1 s1 ->
      inr (s2', id2) ≡ gen name2 s2 ->
      count s1 ≢ count s2 ->
      not_ends_with_nat name1 ->
      not_ends_with_nat name2 ->
      id1 ≢ id2.

  Definition count_gen_mono : Prop
    := forall s1 s2 name id,
      inr (s2, id) ≡ gen name s1 ->
      (count s2 > count s1)%nat.

  Variable INJ : count_gen_injective.
  Variable MONO : count_gen_mono.

  (* Says whether or not a variable has been generated by an earlier IRState,

     I.e., this holds when `id` can be generated using `gen` from a
     state with an earlier counter. The intuition is that `id` ends
     with a number that is *lower* than the count for the current
     state.
   *)
  Definition state_bound (s : IRState) (id : raw_id) : Prop
    := exists name s' s'', not_ends_with_nat name /\ (count s' < count s)%nat /\ inr (s'', id) ≡ gen name s'.

  (* If an id has been bound between two states.

     The primary use for this is in lemmas like, bid_bound_fresh,
     which let us know that since a id was bound between two states,
     it can not possibly collide with an id from an earlier state.
   *)
  Definition state_bound_between (s1 s2 : IRState) (id : raw_id) : Prop
    := exists name s' s'', not_ends_with_nat name /\ (count s' < count s2)%nat /\ count s' ≥ count s1 /\ inr (s'', id) ≡ gen name s'.

  Lemma state_bound_fresh :
    forall (s1 s2 : IRState) (id id' : raw_id),
      state_bound s1 id ->
      state_bound_between s1 s2 id' ->
      id ≢ id'.
  Proof.
    intros s1 s2 id id' BOUND BETWEEN.
    destruct BOUND as (n1 & s1' & s1'' & N_S1 & COUNT_S1 & GEN_id).
    destruct BETWEEN as (n2 & sm' & sm'' & N_S2 & COUNT_Sm_ge & COUNT_Sm_lt & GEN_id').

    eapply INJ.
    apply GEN_id.
    apply GEN_id'.
    lia.
    all: auto.
  Qed.

  Lemma state_bound_fresh' :
    forall (s1 s2 s3 : IRState) (id id' : raw_id),
      state_bound s1 id ->
      (count s1 <= count s2)%nat ->
      state_bound_between s2 s3 id' ->
      id ≢ id'.
  Proof.
    intros s1 s2 s3 id id' BOUND COUNT BETWEEN.
    destruct BOUND as (n1 & s1' & s1'' & N_S1 & COUNT_S1 & GEN_id).
    destruct BETWEEN as (n2 & sm' & sm'' & N_S2 & COUNT_Sm_ge & COUNT_Sm_lt & GEN_id').

    eapply INJ.
    apply GEN_id.
    apply GEN_id'.
    lia.
    all: auto.
  Qed.

  Lemma state_bound_bound_between :
    forall (s1 s2 : IRState) (bid : block_id),
      state_bound s2 bid ->
      ~(state_bound s1 bid) ->
      state_bound_between s1 s2 bid.
  Proof.
    intros s1 s2 bid BOUND NOTBOUND.
    destruct BOUND as (n1 & s1' & s1'' & N_S1 & COUNT_S1 & GEN_bid).
    unfold state_bound_between.
    exists n1. exists s1'. exists s1''.
    repeat (split; auto).
    pose proof (NatUtil.lt_ge_dec (count s1') (count s1)) as [LT | GE].
    - (* If this is the case, I must have a contradiction, which would mean that
         bid_bound s1 bid... *)
      assert (state_bound s1 bid).
      unfold state_bound.
      exists n1. exists s1'. exists s1''.
      auto.
      contradiction.
    - auto.
  Qed.

  Lemma state_bound_mono :
    forall s1 s2 bid,
      state_bound s1 bid ->
      (count s1 <= count s2)%nat ->
      state_bound s2 bid.
  Proof.
    intros s1 s2 bid BOUND COUNT.
    destruct BOUND as (n1 & s1' & s1'' & N_S1 & COUNT_S1 & GEN_bid).
    unfold state_bound.
    exists n1. exists s1'. exists s1''.
    intuition.
  Qed.

  Lemma state_bound_between_shrink :
    forall s1 s2 s1' s2' id,
      state_bound_between s1 s2 id ->
      (count s1' <= count s1)%nat ->
      (count s2' >= count s2)%nat ->
      state_bound_between s1' s2' id.
  Proof.
    intros s1 s2 s1' s2' id BOUND_BETWEEN S1LE S2GE.
    unfold state_bound_between.
    destruct BOUND_BETWEEN as (n & s' & s'' & NEND & LT & GE & INC).
    exists n. exists s'. exists s''.
    repeat (split; auto).
    all: lia.
  Qed.

  Lemma all_state_bound_between_shrink :
    forall s1 s2 s1' s2' ids,
      Forall (state_bound_between s1 s2) ids ->
      (count s1' <= count s1)%nat ->
      (count s2' >= count s2)%nat ->
      Forall (state_bound_between s1' s2') ids.
  Proof.
    intros s1 s2 s1' s2' bids BOUND_BETWEEN S1LE S2GE.
    apply Forall_forall.
    intros x IN.
    eapply Forall_forall in BOUND_BETWEEN; eauto.
    eapply state_bound_between_shrink; eauto.
  Qed.
  
  Lemma state_bound_between_separate :
    forall s1 s2 s3 s4 id id',
      state_bound_between s1 s2 id ->
      state_bound_between s3 s4 id' ->
      (count s2 <= count s3)%nat ->
      id ≢ id'.
  Proof.
    intros s1 s2 s3 s4 id id' BOUND1 BOUND2 BC.
    destruct BOUND1 as (n1 & s1' & s1'' & NEND1 & LT1 & GE1 & INC1).
    destruct BOUND2 as (n2 & s2' & s2'' & NEND2 & LT2 & GE2 & INC2).

    assert (count s1' ≢ count s2') as NEQ by lia.
    eapply INJ.
    apply INC1.
    apply INC2.
    all: eauto.
  Qed.

  Lemma not_state_bound_between_split :
    forall (s1 s2 s3 : IRState) id,
      ~ state_bound_between s1 s2 id ->
      ~ state_bound_between s2 s3 id ->
      ~ state_bound_between s1 s3 id.
  Proof.
    intros s1 s2 s3 id S1S2 S2S3.
    intros BOUND.
    unfold state_bound_between in BOUND.
    destruct BOUND as (name & s' & s'' & NEND & COUNT1 & COUNT2 & GEN).
    assert (count s' < count s2 \/ count s' >= count s2)%nat as COUNT_MID by lia.
    destruct COUNT_MID as [COUNT_MID | COUNT_MID].
    - apply S1S2.
      unfold state_bound_between.
      exists name. exists s'. exists s''.
      auto.
    - apply S2S3.
      unfold state_bound_between.
      exists name. exists s'. exists s''.
      auto.
  Qed.

  Lemma gen_not_state_bound :
    forall name s1 s2 id,
      not_ends_with_nat name ->
      gen name s1 ≡ inr (s2, id) ->
      ~(state_bound s1 id).
  Proof.
    intros name s1 s2 id ENDS INC.
    intros BOUND.
    destruct BOUND as (n1 & s1' & s1'' & N_S1 & COUNT_S1 & GEN_id).
    symmetry in INC.

    eapply (INJ INC GEN_id); auto.
    lia.
  Qed.

  Lemma not_id_bound_gen_mono :
    forall name s1 s2 s' id,
      gen name s1 ≡ inr (s2, id) ->
      (count s' <= count s1)%nat ->
      not_ends_with_nat name ->
      ~ (state_bound s' id).
  Proof.
    intros name s1 s2 s' id INC LE NE.
    intros BOUND.
    destruct BOUND as (n1 & s1' & s1'' & N_S1 & COUNT_S1 & GEN_id).
    assert (count s1 ≢ count s1') as NEQ by lia.
    eapply INJ.
    symmetry; apply INC.
    apply GEN_id.
    all: auto.
  Qed.
End StateBound.

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
    inversion GEN1.
    inversion GEN2.
    Opaque incBlockNamed.
    cbn in *.
    subst.

    intros CONTRA.
    apply Name_inj in CONTRA.

    match goal with
    | H : ?s1 @@ string_of_nat ?n ≡ ?s2 @@ string_of_nat ?k,
          NS1 : not_ends_with_nat ?s1,
                NS2 : not_ends_with_nat ?s2
      |- _ =>
      eapply (@not_ends_with_nat_neq s1 s2 n k NS1 NS2); eauto
    end.
  Qed.

  Lemma bid_bound_genIR_entry :
    forall op s1 s2 nextblock bid bks,
      genIR op nextblock s1 ≡ inr (s2, (bid, bks)) ->
      bid_bound s2 bid.
  Proof.
    induction op;
      intros s1 s2 nextblock b bks GEN.
  Admitted.

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
    intros H.
    apply Name_inj in H.
    match goal with
    | H : ?s1 @@ string_of_nat ?n ≡ ?s2 @@ string_of_nat ?k,
          NS1 : not_ends_with_nat ?s1,
                NS2 : not_ends_with_nat ?s2
      |- _ =>
      eapply (@not_ends_with_nat_neq s1 s2 n k NS1 NS2); eauto
    end.

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

  Lemma bid_bound_incBlockNamed :
    forall name s1 s2 bid,
      not_ends_with_nat name ->
      incBlockNamed name s1 ≡ inr (s2, bid) ->
      bid_bound s2 bid.
  Proof.
    intros name s1 s2 bid ENDS INC.
    exists name. exists s1. exists s2.
    repeat (split; auto).
    erewrite incBlockNamed_block_count with (s':=s2); eauto.
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

Section LidBound.  
  (* Says that a given local id would have been generated by an earlier IRState *)
  Definition lid_bound (s : IRState) (lid: local_id) : Prop
    := state_bound local_count incLocalNamed s lid.

  Definition lid_bound_between (s1 s2 : IRState) (lid : local_id) : Prop
    := state_bound_between local_count incLocalNamed s1 s2 lid.

  Lemma incLocalNamed_count_gen_injective :
    count_gen_injective local_count incLocalNamed.
  Proof.
    unfold count_gen_injective.
    intros s1 s1' s2 s2' name1 name2 id1 id2 GEN1 GEN2 H1 H2 H3.

    inversion GEN1.
    inversion GEN2.
    cbn in *.
    subst.

    intros CONTRA.
    apply Name_inj in CONTRA.

    match goal with
    | H : ?s1 @@ string_of_nat ?n ≡ ?s2 @@ string_of_nat ?k,
          NS1 : not_ends_with_nat ?s1,
                NS2 : not_ends_with_nat ?s2
      |- _ =>
      eapply (@not_ends_with_nat_neq s1 s2 n k NS1 NS2); eauto
    end.
  Qed.
End LidBound.

Hint Resolve incBlockNamed_count_gen_injective : CountGenInj.
Hint Resolve incLocalNamed_count_gen_injective : CountGenInj.

Ltac solve_bid_bound :=
  repeat
    match goal with
    | H: incBlockNamed ?msg ?s1 ≡ inr (?s2, ?bid) |-
      bid_bound ?s2 ?bid =>
      eapply bid_bound_incBlockNamed; try eapply H; solve_not_ends_with
    | H: incBlock ?s1 ≡ inr (?s2, ?bid) |-
      bid_bound ?s2 ?bid =>
      eapply bid_bound_incBlockNamed; try eapply H; solve_not_ends_with

    | H: incBlockNamed ?msg ?s1 ≡ inr (_, ?bid) |-
      ~(bid_bound ?s1 ?bid) =>
      eapply gen_not_state_bound; try eapply H; solve_not_ends_with
    | H: incBlock ?s1 ≡ inr (_, ?bid) |-
      ~(bid_bound ?s1 ?bid) =>
      eapply gen_not_state_bound; try eapply H; solve_not_ends_with

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
    eapply (not_id_bound_gen_mono incBlockNamed_count_gen_injective _ H)
  | H: incBlock ?s1 ≡ inr (?s2, ?bid) |-
    ~(bid_bound ?s3 ?bid) =>
    eapply (not_id_bound_gen_mono incBlockNamed_count_gen_injective _ H)
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
     try solve_not_ends_with;
     try solve_count_gen_injective;
     try match goal with
         | |- Forall _ (?x::?xs) =>
           apply Forall_cons; eauto
         | |- bid_bound_between ?s1 ?s2 ?bid =>
           eapply bid_bound_bound_between; solve_bid_bound
         | |- bid_bound_between ?s1 ?s2 ?bid ∨ ?bid ≡ ?nextblock =>
           try auto; try left
         end).

Section Inputs.

  (* TODO: Move this to Vellvm *)
  Lemma convert_typ_app_list :
    forall {F} `{Traversal.Fmap F} (a b : list (F typ)) (env : list (ident * typ)),
      convert_typ env (a ++ b) ≡ convert_typ env a ++ convert_typ env b.
  Proof.
    intros F H a.
    induction a; cbn; intros; auto.
    rewrite IHa; reflexivity.
  Qed.

  (* TODO: move this *)
  Lemma add_comment_inputs :
    forall (bs : list (LLVMAst.block typ)) env (comments : list string),
      inputs (convert_typ env (add_comment bs comments)) ≡ inputs (convert_typ env bs).
  Proof.
    induction bs; intros env comments; auto.
  Qed.

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

      rewrite convert_typ_app_list.

      (* TODO: clean this up *)
      unfold fmap.
      unfold Fmap_list.
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
    - rewrite add_comment_inputs.
      rewrite convert_typ_app_list.

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
      rewrite convert_typ_app_list.
      rewrite fold_left_app.
      cbn.

      epose proof (IHop _ _ _ _ _ Heqs1).
      cbn in H.
  Admitted.
End Outputs.
