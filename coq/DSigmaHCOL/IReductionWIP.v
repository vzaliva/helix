Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Omega.
Require Import Psatz.
Require Import CoLoR.Util.Nat.NatUtil.

Require Import Helix.HCOL.CarrierType.

Require Import Helix.MSigmaHCOL.Memory.
Require Import Helix.MSigmaHCOL.MemSetoid.
Require Import Helix.MSigmaHCOL.MSigmaHCOL.
Require Import Helix.MSigmaHCOL.MemoryOfCarrierA.

Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.
Require Import Helix.DSigmaHCOL.DSHCOLOnCarrierA.

(* When proving concrete functions we need to use
   some implementation defs from this packages *)
Require Import Helix.HCOL.HCOL.
Require Import Helix.Util.VecUtil.
Require Import Helix.Util.FinNat.

Require Import MathClasses.misc.util.
Require Import MathClasses.misc.decision.
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.implementations.peano_naturals.
Require Import MathClasses.orders.orders.

Require Import Helix.Util.OptionSetoid.
Require Import Helix.Util.ErrorSetoid.
Require Import Helix.MSigmaHCOL.MemSetoid.
Require Import Helix.Tactics.HelixTactics.

Open Scope string_scope.
Open Scope list_scope.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope nat_scope.

Import DSHCOLOnCarrierA.

Require Import Helix.DSigmaHCOL.ReifyProofs.

(** * MSHIReduction *)

(* TODO: move *)
Lemma memory_set_overwrite (m : memory) (k k' : mem_block_id) (mb mb' : mem_block) :
  k = k' ->
  memory_set (memory_set m k mb) k' mb' = memory_set m k' mb'.
Proof.
  intros E; cbv in E; subst k'.
  unfold memory_set, equiv, memory_Equiv.
  intros j.
  destruct (Nat.eq_dec k j).
  -
    repeat rewrite NP.F.add_eq_o by assumption.
    reflexivity.
  -
    repeat rewrite NP.F.add_neq_o by assumption.
    reflexivity.
Qed.

Global Instance memory_remove_proper :
  Proper ((=) ==> (=) ==> (=)) memory_remove.
Proof.
  intros m1 m2 ME k1 k2 KE.
  unfold memory_remove, equiv, memory_Equiv.
  intros k.
  destruct (Nat.eq_dec k1 k).
  -
    assert (k2 ≡ k) by (unfold equiv, nat_equiv in KE; congruence).
    repeat rewrite NP.F.remove_eq_o by assumption.
    reflexivity.
  -
    assert (k2 ≢ k) by (unfold equiv, nat_equiv in KE; congruence).
    repeat rewrite NP.F.remove_neq_o by assumption.
    apply ME.
Qed.

Lemma memory_remove_memory_set_eq (m : memory) (k k' : mem_block_id) (mb : mem_block) :
  k = k' ->
  memory_remove (memory_set m k mb) k' = memory_remove m k.
Proof.
  intros; cbv in H; subst k'.
  unfold memory_remove, memory_set, equiv, memory_Equiv.
  intros j.
  destruct (Nat.eq_dec k j).
  -
    repeat rewrite NP.F.remove_eq_o by assumption.
    reflexivity.
  -
    repeat rewrite NP.F.remove_neq_o by assumption.
    rewrite NP.F.add_neq_o by assumption.
    reflexivity.
Qed.

Lemma memory_remove_nonexistent_key (m : memory) (k : mem_block_id) :
  not (mem_block_exists k m) -> memory_remove m k = m.
Proof.
  intros.
  unfold mem_block_exists, memory_remove in *.
  intros j.
  rewrite NP.F.remove_o.
  break_match; try reflexivity.
  subst.
  apply NP.F.not_find_in_iff in H.
  rewrite H.
  reflexivity.
Qed.

Global Instance Seq_DSH_pure
       {dop1 dop2 : DSHOperator}
       {y_p : PExpr}
       (P1: DSH_pure dop1 y_p)
       (P2: DSH_pure dop2 y_p)
  :
    DSH_pure (DSHSeq dop1 dop2) y_p.
Proof.
  split.
  -
    intros σ m0 m2 fuel M2 k.

    destruct fuel; [inversion M2 |].
    cbn in *.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    subst.
    rename m into m1, Heqo into M1.
    eq_to_equiv_hyp.

    inversion P1; clear P1 mem_write_safe;
      rename mem_stable into P1.
    apply P1 with (k:=k) in M1; clear P1.
    inversion P2; clear P2 mem_write_safe;
      rename mem_stable into P2.
    apply P2 with (k:=k) in M2; clear P2.
    rewrite M1, M2.
    reflexivity.
  -
    intros σ m0 m2 fuel M2 y_i Y.

    destruct fuel; [inversion M2 |].
    cbn in *.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    subst.
    rename m into m1, Heqo into M1.
    eq_to_equiv_hyp.

    inversion P1; clear P1 mem_stable;
      rename mem_write_safe into P1.
    eapply P1 with (y_i := y_i) in M1; [| assumption].
    inversion P2; clear P2 mem_stable;
      rename mem_write_safe into P2.
    eapply P2 with (y_i := y_i) in M2; [| assumption].
    clear - M1 M2.
    eapply memory_equiv_except_trans; eassumption.
Qed.

Global Instance MemMap2_DSH_pure
       {x0_p x1_p y_p : PExpr}
       {n : nat}
       {a : AExpr}
  :
    DSH_pure (DSHMemMap2 n x0_p x1_p y_p a) y_p.
Proof.
  constructor.
  -
    intros.
    destruct fuel; cbn in *; try some_none.
    unfold memory_lookup_err, trywith in *.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    subst.

    rewrite <-H; clear H m'.

    split; [apply mem_block_exists_memory_set | intros].
    apply mem_block_exists_memory_set_inv in H.
    destruct H; [assumption | subst].
    apply memory_is_set_is_Some.
    rewrite Heqo.
    reflexivity.
  -
    intros.
    destruct fuel; cbn in *; try some_none.
    unfold memory_lookup_err, trywith in *.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    cbv in H0.
    subst.

    unfold memory_equiv_except; intros.
    rewrite <-H; clear H m'.
    unfold memory_lookup, memory_set.
    rewrite NP.F.add_neq_o by congruence.
    reflexivity.
Qed.

Global Instance Alloc_DSH_pure
       {size : nat}
       {dop : DSHOperator}
       {y_p : PExpr}
       (P : DSH_pure dop (incrPVar 0 y_p))
  :
  DSH_pure (DSHAlloc size dop) y_p.
Proof.
  constructor.
  -
    intros.
    destruct fuel; cbn in *; try some_none.
    unfold memory_lookup_err, trywith in *.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    subst.
    rewrite <-H; clear H m'.

    inversion_clear P as [S T]; clear T.
    eq_to_equiv_hyp.
    apply S with (k:=k) in Heqo; clear S.
    destruct (Nat.eq_dec k (memory_next_key m)) as [EQ | NEQ].
    +
      subst.
      clear.
      split; intros.
      *
        contradict H.
        apply mem_block_exists_memory_next_key.
      *
        contradict H.
        apply mem_block_exists_memory_remove.
    +
      split; intros.
      *
        rewrite <-mem_block_exists_memory_remove_neq by assumption.
        apply Heqo.
        apply mem_block_exists_memory_set.
        assumption.
      *
        enough (T : mem_block_exists k (memory_set m (memory_next_key m) mem_empty))
          by (apply mem_block_exists_memory_set_inv in T; destruct T; congruence).
        apply Heqo.
        erewrite mem_block_exists_memory_remove_neq.
        eassumption.
        assumption.
  -
    intros.
    destruct fuel; cbn in *; try some_none.
    unfold memory_lookup_err, trywith in *.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    subst.
    unfold memory_equiv_except.
    intros.
    rewrite <-H; clear H m'.

    inversion_clear P as [T S]; clear T.
    eq_to_equiv_hyp.
    apply S with (y_i:=y_i) in Heqo; clear S;
      [| rewrite evalPexp_incrPVar; assumption].

    unfold memory_equiv_except in Heqo.
    specialize (Heqo k H1).
    destruct (Nat.eq_dec k (memory_next_key m)) as [EQ | NEQ].
    +
      subst.
      unfold memory_lookup, memory_remove, memory_set in *.
      rewrite NP.F.add_eq_o in Heqo by reflexivity.
      rewrite NP.F.remove_eq_o by reflexivity.
      pose proof memory_lookup_memory_next_key_is_None m.
      apply is_None_def in H.
      rewrite <-H.
      reflexivity.
    +
      unfold memory_lookup, memory_remove, memory_set in *.
      rewrite NP.F.add_neq_o in Heqo by congruence.
      rewrite NP.F.remove_neq_o by congruence.
      assumption.
Qed.

Global Instance MemInit_DSH_pure
       {size : nat}
       {y_p : PExpr}
       {init : CarrierA}
  :
    DSH_pure (DSHMemInit size y_p init) y_p.
Proof.
  constructor.
  -
    intros.
    destruct fuel; cbn in *; try some_none.
    unfold memory_lookup_err, trywith in *.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    subst.

    rewrite <-H; clear H m'.

    split; [apply mem_block_exists_memory_set | intros].
    apply mem_block_exists_memory_set_inv in H.
    destruct H; [assumption | subst].
    apply memory_is_set_is_Some.
    rewrite Heqo.
    reflexivity.
  -
    intros.
    destruct fuel; cbn in *; try some_none.
    unfold memory_lookup_err, trywith in *.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    cbv in H0.
    subst.

    unfold memory_equiv_except; intros.
    rewrite <-H; clear H m'.
    unfold memory_lookup, memory_set.
    rewrite NP.F.add_neq_o by congruence.
    reflexivity.
Qed.

Lemma memory_lookup_memory_set_eq (m : memory) (k k' : mem_block_id) (mb : mem_block) :
  k = k' ->
  memory_lookup (memory_set m k mb) k' ≡ Some mb.
Proof.
  intros.
  rewrite H; clear H.
  unfold memory_lookup, memory_set.
  rewrite NP.F.add_eq_o by reflexivity.
  reflexivity.
Qed.

Lemma memory_lookup_memory_set_neq (m : memory) (k k' : mem_block_id) (mb : mem_block) :
  k <> k' ->
  memory_lookup (memory_set m k mb) k' ≡ memory_lookup m k'.
Proof.
  intros.
  unfold memory_lookup, memory_set.
  rewrite NP.F.add_neq_o by assumption.
  reflexivity.
Qed.

Lemma memory_lookup_memory_remove_eq (m : memory) (k k' : mem_block_id) :
  k = k' ->
  memory_lookup (memory_remove m k) k' = None.
Proof.
  intros.
  rewrite <-H; clear H.
  unfold memory_lookup, memory_remove.
  rewrite NP.F.remove_eq_o; reflexivity.
Qed.

Lemma memory_lookup_memory_remove_neq (m : memory) (k k' : mem_block_id) :
  k <> k' ->
  memory_lookup (memory_remove m k) k' = memory_lookup m k'.
Proof.
  intros.
  unfold memory_lookup, memory_remove.
  rewrite NP.F.remove_neq_o.
  reflexivity.
  assumption.
Qed.

Ltac eq_to_equiv := err_eq_to_equiv_hyp; eq_to_equiv_hyp.

Ltac simplify_memory_hyp :=
  match goal with
  | [ H : memory_lookup (memory_set _ _ _) _ = _ |- _ ] =>
    try rewrite memory_lookup_memory_set_neq in H by congruence;
    try rewrite memory_lookup_memory_set_eq in H by congruence
  | [H : memory_lookup (memory_remove _ _) _ = _ |- _ ] =>
    try rewrite memory_lookup_memory_remove_neq in H by congruence;
    try rewrite memory_lookup_memory_remove_eq in H by congruence
  | [H : memory_set (memory_set _ _ _) _ _ = _ |- _] =>
    try rewrite memory_set_overwrite in H by congruence
  | [H : memory_remove (memory_set _ _ _) _ = _ |- _] =>
    try rewrite memory_remove_memory_set_eq in H by congruence
  end.

Global Instance NOP_DSH_pure
       {y_p : PExpr}
  :
    DSH_pure DSHNop y_p.
Proof.
  constructor.
  -
    intros.
    destruct fuel; cbn in *; try some_none.
    some_inv; inl_inr_inv.
    rewrite H.
    reflexivity.
  -
    intros.
    destruct fuel; cbn in *; try some_none.
    some_inv; inl_inr_inv.
    intros k NE.
    rewrite H.
    reflexivity.
Qed.

Global Instance IReduction_DSH_pure
       {no nn : nat}
       {y_p y_p'': PExpr}
       {init : CarrierA}
       {rr : DSHOperator}
       {df : AExpr}
       (Y: y_p'' ≡ incrPVar 0 (incrPVar 0 y_p))
       (P: DSH_pure rr (PVar 1))
  :
    DSH_pure
      (DSHSeq
         (DSHMemInit no y_p init)
         (DSHAlloc no
                   (DSHLoop nn
                            (DSHSeq
                               rr
                               (DSHMemMap2 no y_p''
                                           (PVar 1)
                                           y_p''
                                           df)))))
      y_p.
Proof.
  subst.
  apply Seq_DSH_pure.
  apply MemInit_DSH_pure.

  (* we don't care what operator it is so long as it's pure *)
  remember (DSHMemMap2 no (incrPVar 0 (incrPVar 0 y_p)) (PVar 1)
                (incrPVar 0 (incrPVar 0 y_p)) df)
    as dop.
  assert (DSH_pure dop (incrPVar 0 (incrPVar 0 y_p)))
    by (subst; apply MemMap2_DSH_pure).
  clear Heqdop.

  constructor; intros.
  -
    generalize dependent m'.
    induction nn.
    +
      intros.
      do 2 (destruct fuel; [cbn in *; some_none |]).
      cbn in *.
      some_inv; inl_inr_inv.
      eq_to_equiv; simplify_memory_hyp.
      rewrite memory_remove_nonexistent_key in H0
        by (apply mem_block_exists_memory_next_key).
      rewrite H0.
      reflexivity.
    +
      intros.
      do 2 (destruct fuel; [cbn in *; some_none |]).
      cbn in H0.
      repeat break_match;
        try some_none; repeat some_inv;
        try inl_inr; repeat inl_inr_inv.
      subst.
      rename m1 into loop_m, m0 into step_m.
      specialize (IHnn (memory_remove loop_m (memory_next_key m))).
      full_autospecialize IHnn.
      *
        remember (S fuel) as t; cbn; subst t. (* poor man's partial unfold *)
        apply evalDSHOperator_fuel_ge with (f' := S fuel) in Heqo0;
          [| constructor; reflexivity].
        rewrite Heqo0.
        reflexivity.
      *
        rewrite <-H0.
        clear Heqo0 H0 m'.
        destruct fuel; cbn in *; try some_none.
        repeat break_match;
          try some_none; repeat some_inv;
          try inl_inr; repeat inl_inr_inv.
        subst.
        rename m0 into rr_m.
        eq_to_equiv.
        inversion_clear P as [S T]; clear T.
        apply S with (k:=k) in Heqo0; clear S.
        inversion_clear H as [S T]; clear T.
        apply S with (k:=k) in Heqo; clear S.
        rewrite IHnn.
        destruct (Nat.eq_dec k (memory_next_key m)).
        --
          rewrite <-e in *.
          pose proof mem_block_exists_memory_remove k loop_m.
          pose proof mem_block_exists_memory_remove k step_m.
          intuition.
        --
          repeat rewrite <-mem_block_exists_memory_remove_neq by congruence.
          rewrite Heqo0, Heqo.
          reflexivity.
  -
    generalize dependent m'.
    induction nn.
    +
      intros.
      do 2 (destruct fuel; [cbn in *; some_none |]).
      cbn in *.
      some_inv; inl_inr_inv.
      eq_to_equiv; simplify_memory_hyp.
      rewrite memory_remove_nonexistent_key in H0
        by (apply mem_block_exists_memory_next_key).
      unfold memory_equiv_except.
      intros.
      rewrite H0.
      reflexivity.
    +
      intros.
      do 2 (destruct fuel; [cbn in *; some_none |]).
      cbn in H0.
      repeat break_match;
        try some_none; repeat some_inv;
        try inl_inr; repeat inl_inr_inv.
      subst.
      rename m1 into loop_m, m0 into step_m.
      specialize (IHnn (memory_remove loop_m (memory_next_key m))).
      full_autospecialize IHnn.
      *
        remember (S fuel) as t; cbn; subst t. (* poor man's partial unfold *)
        apply evalDSHOperator_fuel_ge with (f' := S fuel) in Heqo0;
          [| constructor; reflexivity].
        rewrite Heqo0.
        reflexivity.
      *
        unfold memory_equiv_except.
        intros.
        rewrite <-H0.
        clear Heqo0 H0 m'.
        destruct fuel; cbn in Heqo; try some_none.
        repeat break_match;
          try some_none; repeat some_inv;
          try inl_inr; repeat inl_inr_inv.
        subst.
        rename m0 into rr_m.
        eq_to_equiv.
        inversion_clear P as [T S]; clear T.
        apply S with (y_i:=memory_next_key m) in Heqo0; clear S; [| reflexivity].
        inversion_clear H as [T S]; clear T.
        apply S with (y_i:=y_i) in Heqo; clear S;
          [| repeat rewrite evalPexp_incrPVar; assumption].
        rewrite IHnn by assumption.
        destruct (Nat.eq_dec k (memory_next_key m)).
        --
          rewrite <-e in *.
          repeat rewrite memory_lookup_memory_remove_eq by reflexivity.
          reflexivity.
        --
          repeat rewrite memory_lookup_memory_remove_neq by congruence.
          rewrite Heqo0 by congruence.
          rewrite Heqo by congruence.
          reflexivity.
Qed.

Instance MSH_DSH_compat_R_proper {σ : evalContext} {mb : mem_block} {y_p : PExpr} :
  Proper ((=) ==> (=) ==> iff)
             (fun md m' => err_p (fun ma => SHCOL_DSHCOL_mem_block_equiv mb ma md)
                              (lookup_Pexp σ m' y_p)).
Proof.
  intros md1 md2 MDE m1' m2' ME.
  assert (P : forall md, Proper ((=) ==> iff)
                       (λ ma : mem_block, SHCOL_DSHCOL_mem_block_equiv mb ma md)).
  {
    intros md ma1 ma2 MAE.
    unfold SHCOL_DSHCOL_mem_block_equiv.
    split; intros.
    -
      specialize (H i).
      inversion H;
        [constructor 1 | constructor 2].
      assumption.
      rewrite <-MAE.
      assumption.
      assumption.
      rewrite <-MAE.
      assumption.
    -
      specialize (H i).
      inversion H;
        [constructor 1 | constructor 2].
      assumption.
      rewrite MAE.
      assumption.
      assumption.
      rewrite MAE.
      assumption.
  }
  split; intros.
  -
    inversion H; clear H.
    eq_to_equiv.
    rewrite ME in H0.
    rewrite <-H0.
    constructor.
    rewrite <-MDE.
    assumption.
  -
    inversion H; clear H.
    eq_to_equiv.
    rewrite <-ME in H0.
    rewrite <-H0.
    constructor.
    rewrite MDE.
    assumption.
Qed.

Lemma memory_lookup_not_next_equiv (m : memory) (k : mem_block_id) (mb : mem_block) :
  memory_lookup m k = Some mb -> k <> memory_next_key m.
Proof.
  intros S C.
  subst.
  pose proof memory_lookup_memory_next_key_is_None m.
  unfold is_None in H.
  break_match.
  trivial.
  some_none.
Qed.

Global Instance IReduction_MSH_DSH_compat_O
       {i o : nat}
       {init : CarrierA}
       {dot : CarrierA -> CarrierA -> CarrierA}
       {pdot : Proper ((=) ==> (=) ==> (=)) dot}
       {op_family : @MSHOperatorFamily i o 0}
       {df : AExpr}
       {x_p y_p : PExpr}
       {rr : DSHOperator}
       {σ : evalContext}
       {m : memory}
       {DP}
  :
    @MSH_DSH_compat
      _ _
      (@MSHIReduction i o 0 init dot pdot op_family)
      DSHNop
      σ m x_p y_p DP.
Proof.
  constructor.
  intros.
  cbn.
  constructor.
  break_match.
  all: unfold lookup_Pexp in H0.
  all: rewrite Heqs in H0.
  all: cbn in H0.
  1: inl_inr.
  destruct memory_lookup_err; try inl_inr; inl_inr_inv.
  repeat constructor.
  rewrite H0.
  reflexivity.
Qed.

Lemma memory_next_key_struct
      (m m' : memory):
  (forall k, mem_block_exists k m <-> mem_block_exists k m') ->
       memory_next_key m = memory_next_key m'.
Proof.
  intros H.
  unfold memory_next_key.
  destruct (NS.max_elt (memory_keys_set m)) as [k1|] eqn:H1;
    destruct (NS.max_elt (memory_keys_set m')) as [k2|] eqn:H2.
  -
    f_equiv.
    cut(¬ k1 < k2 /\ ¬ k2 < k1);[lia|].
    split.
    +
      apply (NS.max_elt_2 H1), memory_keys_set_In, H.
      apply NS.max_elt_1, memory_keys_set_In in H2.
      apply H2.
    +
      apply (NS.max_elt_2 H2), memory_keys_set_In, H.
      apply NS.max_elt_1, memory_keys_set_In in H1.
      apply H1.
  - exfalso.
    apply NS.max_elt_1 in H1.
    apply NS.max_elt_3 in H2.
    apply memory_keys_set_In in H1.
    apply H in H1.
    apply memory_keys_set_In in H1.
    apply  NSP.empty_is_empty_1 in H2.
    rewrite H2 in H1.
    apply NSP.FM.empty_iff in H1.
    tauto.
  - exfalso.
    apply NS.max_elt_1 in H2.
    apply NS.max_elt_3 in H1.
    apply memory_keys_set_In in H2.
    apply H in H2.
    apply memory_keys_set_In in H2.
    apply  NSP.empty_is_empty_1 in H1.
    rewrite H1 in H2.
    apply NSP.FM.empty_iff in H2.
    tauto.
  -
    reflexivity.
Qed.


Lemma memory_next_key_override (k : mem_block_id) (m : memory) (mb : mem_block) :
  mem_block_exists k m ->
  memory_next_key (memory_set m k mb) = memory_next_key m.
Proof.
  intros H.
  apply memory_next_key_struct.
  intros k0.
  split; intros.
  -
    destruct (Nat.eq_dec k k0).
    +
      subst k0.
      assumption.
    +
      apply mem_block_exists_memory_set_neq in H0; auto.
  -
    apply mem_block_exists_memory_set.
    assumption.
Qed.

Global Instance evalDSHOperator_proper :
  Proper ((=) ==> (≡) ==> (=) ==> (=) ==> (=)) evalDSHOperator.
(*
Proof.
  intros σ1 σ2 Σ.
  intros dop dop' DOP; subst dop'.
  intros m1 m2 M.
  intros f f' F; cbv in F; subst f'.
  destruct f; try reflexivity.

  induction dop; cbn.
  -
    rewrite M; reflexivity.
  -
    repeat break_match.
    all: repeat constructor.
    all: admit.
  -
*)
Admitted.

Lemma lookup_Pexp_eval_lookup (σ : evalContext) (m : memory) (x : PExpr) (mb : mem_block) :
  lookup_Pexp σ m x = inr mb ->
  exists x_id, evalPexp σ x = inr x_id /\ memory_lookup m x_id = Some mb.
Proof.
  intros.
  unfold lookup_Pexp, memory_lookup_err, trywith in H.
  cbn in *.
  repeat break_match; try inl_inr; inl_inr_inv.
  exists m0.
  intuition.
  rewrite Heqo, H.
  reflexivity.
Qed.

Global Instance evalDSHMap2_proper :
  Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=)) evalDSHMap2.
Proof.
  intros m1 m2 M n1 n2 N df1 df2 DF σ1 σ2 Σ l1 l2 L r1 r2 R y1 y2 Y.
  cbv in N; subst; rename n2 into n.
  generalize dependent y2.
  generalize dependent y1.
  induction n.
  -
    intros.
    cbn.
    rewrite Y.
    reflexivity.
  -
    intros.
    cbn [evalDSHMap2].
    generalize ("Error reading 2nd arg memory in evalDSHMap2 @" ++
     Misc.string_of_nat n ++ " in " ++ string_of_mem_block_keys r1)%string.
    generalize ("Error reading 2nd arg memory in evalDSHMap2 @" ++
     Misc.string_of_nat n ++ " in " ++ string_of_mem_block_keys r2)%string.
    generalize ("Error reading 1st arg memory in evalDSHMap2 @" ++
     Misc.string_of_nat n ++ " in " ++ string_of_mem_block_keys l1)%string.
    generalize ("Error reading 1st arg memory in evalDSHMap2 @" ++
     Misc.string_of_nat n ++ " in " ++ string_of_mem_block_keys l2)%string.
    intros.
    cbn.
    assert (mem_lookup_err s0 n l1 = mem_lookup_err s n l2).
    {
      clear - L.
      unfold mem_lookup_err, trywith.
      repeat break_match; try constructor.
      all: eq_to_equiv.
      all: rewrite L in *.
      all: rewrite Heqo in Heqo0; try some_none.
      some_inv.
      assumption.
    }
    assert (mem_lookup_err s2 n r1 = mem_lookup_err s1 n r2).
    {
      clear - R.
      unfold mem_lookup_err, trywith.
      repeat break_match; try constructor.
      all: eq_to_equiv.
      all: rewrite R in *.
      all: rewrite Heqo in Heqo0; try some_none.
      some_inv.
      assumption.
    }
    repeat break_match; try inl_inr; repeat inl_inr_inv; try constructor.
    +
      eq_to_equiv.
      rewrite H, H0, DF, M, Σ in Heqs1.
      inl_inr.
    +
      eq_to_equiv.
      rewrite H, H0, DF, M, Σ in Heqs1.
      inl_inr.
    +
      apply IHn.
      eq_to_equiv.
      rewrite H, H0, DF, M, Σ in Heqs1.
      rewrite Heqs1 in Heqs5.
      inl_inr_inv.
      rewrite Heqs5, Y.
      reflexivity.
Qed.

Global Instance memory_set_proper :
  Proper ((=) ==> (=) ==> (=)) memory_set.
Proof.
  intros m1 m2 M k1 k2 K mb1 mb2 MB.
  cbv in K; subst; rename k2 into k.
  unfold equiv, memory_Equiv, memory_set.
  intros k'.
  destruct (Nat.eq_dec k' k).
  -
    repeat rewrite NP.F.add_eq_o by congruence.
    f_equiv.
    assumption.
  -
    repeat rewrite NP.F.add_neq_o by congruence.
    apply M.
Qed.

Lemma evalDSHMap2_rest_preserved
      (x1 x2 y y' : mem_block)
      (m : memory)
      (df : AExpr)
      (σ : evalContext)
      (n : nat)
  :
    evalDSHMap2 m n df σ x1 x2 y = inr y' ->
    forall k, n <= k -> mem_lookup k y' = mem_lookup k y.
Proof.
  intros.

  generalize dependent k.
  generalize dependent y.
  induction n.
  -
    intros.
    cbn in *.
    inl_inr_inv.
    rewrite H.
    reflexivity.
  -
    intros.
    cbn [evalDSHMap2] in H.
    remember ("Error reading 1st arg memory in evalDSHMap2 @" ++
      Misc.string_of_nat n ++ " in " ++ string_of_mem_block_keys x1)%string as t1;
      clear Heqt1.
    remember ("Error reading 2nd arg memory in evalDSHMap2 @" ++
      Misc.string_of_nat n ++ " in " ++ string_of_mem_block_keys x2)%string as t2;
      clear Heqt2.
    cbn in *.
    repeat break_match; try inl_inr.
    rewrite IHn with (y := mem_add n c1 y); [| assumption | lia].
    unfold mem_lookup, mem_add.
    rewrite NP.F.add_neq_o by lia.
    reflexivity.
Qed.

Lemma evalDSHMap2_result
      (x1 x2 y y' : mem_block)
      (m : memory)
      (df : AExpr)
      (σ : evalContext)
      (n : nat)
      (dot : CarrierA -> CarrierA -> CarrierA)
      (DF : MSH_DSH_BinCarrierA_compat dot σ df m)
  :
    evalDSHMap2 m n df σ x1 x2 y = inr y' ->
    forall k, k < n -> exists a1 a2,
        mem_lookup k x1 = Some a1 /\
        mem_lookup k x2 = Some a2 /\
        mem_lookup k y' = Some (dot a1 a2).
Proof.
  intros.

  generalize dependent k.
  generalize dependent y.
  induction n.
  -
    lia.
  -
    intros.
    cbn [evalDSHMap2] in H.
    remember ("Error reading 1st arg memory in evalDSHMap2 @" ++
      Misc.string_of_nat n ++ " in " ++ string_of_mem_block_keys x1)%string as t1;
      clear Heqt1.
    remember ("Error reading 2nd arg memory in evalDSHMap2 @" ++
      Misc.string_of_nat n ++ " in " ++ string_of_mem_block_keys x2)%string as t2;
      clear Heqt2.
    cbn in *.
    repeat break_match; try inl_inr.
    destruct (Nat.eq_dec k n).
    +
      subst; clear H0.
      exists c, c0.
      split; [| split].
      1,2: unfold mem_lookup_err, trywith in *.
      1,2: repeat break_match; try inl_inr; repeat inl_inr_inv.
      1,2: reflexivity.
      apply evalDSHMap2_rest_preserved with (k:=n) in H; [| reflexivity].
      rewrite H.
      unfold mem_lookup, mem_add.
      rewrite NP.F.add_eq_o by reflexivity.
      inversion_clear DF as [D].
      eq_to_equiv.
      rewrite D in Heqs1.
      inl_inr_inv.
      rewrite Heqs1.
      reflexivity.
    +
      eapply IHn.
      eassumption.
      lia.
Qed.


Lemma mem_in_mem_lookup (k : NM.key) (mb : mem_block) :
  mem_in k mb <-> is_Some (mem_lookup k mb).
Proof.
  unfold mem_in, mem_lookup.
  rewrite is_Some_ne_None, NP.F.in_find_iff.
  reflexivity.
Qed.

Lemma DSHMap2_succeeds 
      (x1_p x2_p y_p : PExpr)
      (x1_m x2_m y_m : mem_block)
      (σ : evalContext)
      (m : memory)
      (df : AExpr)
      (init : CarrierA)
      (o : nat)
      (LX1 : lookup_Pexp σ m x1_p = inr x1_m)
      (LX2 : lookup_Pexp σ m x2_p = inr x2_m)
      (LY : lookup_Pexp σ m y_p = inr y_m)
      (D1 : forall k, k < o -> mem_in k x1_m)
      (D2 : forall k, k < o -> mem_in k x2_m)

      (dot : CarrierA -> CarrierA -> CarrierA)
      (DC : MSH_DSH_BinCarrierA_compat dot σ df m)
  :
    exists m', evalDSHOperator σ (DSHMemMap2 o x1_p x2_p y_p df) m
                    (estimateFuel (DSHMemMap2 o x1_p x2_p y_p df)) = Some (inr m').
Proof.
  apply lookup_Pexp_eval_lookup in LX1.
  destruct LX1 as [x1_id [X1_ID X1_M]].
  apply lookup_Pexp_eval_lookup in LX2.
  destruct LX2 as [x2_id [X2_ID X2_M]].
  apply lookup_Pexp_eval_lookup in LY.
  destruct LY as [y_id [Y_ID Y_M]].
  cbn.
  unfold memory_lookup_err, trywith.
  repeat break_match;
    try some_none; repeat some_inv;
    try inl_inr; repeat inl_inr_inv.
  all: eq_to_equiv.
  all: rewrite X1_ID, X2_ID, Y_ID in *; clear X1_ID X2_ID Y_ID m0 m1 m2.
  all: rename Heqs into X1_ID, Heqs0 into X2_ID, Heqs1 into Y_ID.
  all: try some_none.
  all: subst.
  all: rewrite Heqo2, Heqo1, Heqo0 in *; repeat some_inv.
  all: rewrite X1_M, X2_M, Y_M in *; clear X1_M X2_M Y_M m3 m4 m5.
  all: rename Heqo2 into X1_M, Heqo1 into X2_M, Heqo0 into Y_M.
  all: rename Heqs5 into M.
  - (* evalDSHMap2 fails *)
    exfalso.
    contradict M; generalize s; apply is_OK_neq_inl.

    clear Y_M.
    generalize dependent y_m.
    induction o.
    +
      cbn [evalDSHMap2].
      generalize ("Error reading 2nd arg memory in evalDSHMap2 @" ++
       Misc.string_of_nat 0 ++ " in " ++ string_of_mem_block_keys x2_m)%string.
      generalize ("Error reading 1st arg memory in evalDSHMap2 @" ++
       Misc.string_of_nat 0 ++ " in " ++ string_of_mem_block_keys x1_m)%string.
      intros.
      cbn.
      constructor.
    +
      autospecialize IHo; [intros; apply D1; lia |].
      autospecialize IHo; [intros; apply D2; lia |].
      cbn [evalDSHMap2].
      generalize ("Error reading 1st arg memory in evalDSHMap2 @" ++
       Misc.string_of_nat o ++ " in " ++ string_of_mem_block_keys x1_m)%string.
      generalize ("Error reading 2nd arg memory in evalDSHMap2 @" ++
       Misc.string_of_nat o ++ " in " ++ string_of_mem_block_keys x2_m)%string.
      specialize (D1 o); autospecialize D1; [lia |].
      specialize (D2 o); autospecialize D2; [lia |].
      rewrite mem_in_mem_lookup in *.
      rewrite is_Some_def in D1, D2.
      destruct D1 as [x1_mb D1], D2 as [x2_mb D2].
      unfold mem_lookup_err.
      rewrite D1, D2.
      intros.
      cbn.

      inversion_clear DC as [D].
      pose proof D x1_mb x2_mb as D'.
      break_match; try inl_inr.
      apply IHo.
  -
    eexists.
    reflexivity.
Qed.

Lemma mem_merge_with_def_empty_const
      (dot : CarrierA -> CarrierA -> CarrierA)
      (init : CarrierA)
      (mb : mem_block)
      (o : nat)
      (MD : forall k, k < o -> mem_in k mb)
  :
    forall k, k < o ->
    mem_lookup k (mem_merge_with_def dot init mem_empty mb) =
    mem_lookup k (mem_merge_with_def dot init (mem_const_block o init) mb).
Proof.
  intros.
  unfold mem_lookup, mem_merge_with_def.
  repeat rewrite NP.F.map2_1bis by reflexivity.
  rewrite mem_const_block_find by assumption.
  cbn.
  break_match; try reflexivity.
  exfalso.
  specialize (MD k H).
  apply mem_in_mem_lookup in MD.
  unfold mem_lookup in MD.
  rewrite Heqo0 in MD.
  some_none.
Qed.

Definition mem_firstn (n : nat) (mb : mem_block) :=
  NP.filter_dom (elt:=CarrierA) (fun k => Nat.ltb k n) mb.

Lemma MemMap2_merge_with_def
      (x1_p x2_p y_p : PExpr)
      (x1_m x2_m y_m y_m': mem_block)
      (σ : evalContext)
      (m m' : memory)
      (dot : CarrierA -> CarrierA -> CarrierA)
      (PF : Proper ((=) ==> (=) ==> (=)) dot)
      (df : AExpr)
      (init : CarrierA)
      (o : nat)
      (LX1 : lookup_Pexp σ m x1_p = inr x1_m)
      (LX2 : lookup_Pexp σ m x2_p = inr x2_m)
      (LY : lookup_Pexp σ m y_p = inr y_m)

      (DC : MSH_DSH_BinCarrierA_compat dot σ df m)
  :
    evalDSHOperator σ (DSHMemMap2 o x1_p x2_p y_p df) m
                    (estimateFuel (DSHMemMap2 o x1_p x2_p y_p df)) = Some (inr m') ->
    lookup_Pexp σ m' y_p = inr y_m' ->
    forall k, k < o -> mem_lookup k y_m' =
                 mem_lookup k (mem_merge_with_def dot init x1_m x2_m).
Proof.
  apply lookup_Pexp_eval_lookup in LX1.
  destruct LX1 as [x1_id [X1_ID X1_M]].
  apply lookup_Pexp_eval_lookup in LX2.
  destruct LX2 as [x2_id [X2_ID X2_M]].
  apply lookup_Pexp_eval_lookup in LY.
  destruct LY as [y_id [Y_ID Y_M]].
  cbn [evalDSHOperator estimateFuel].
  remember evalDSHMap2 as t1; remember mem_lookup as t2;
    cbn; subst t1 t2. (* poor man's selective cbv *)

  unfold memory_lookup_err, trywith.
  repeat break_match;
    try some_none; repeat some_inv;
    try inl_inr; repeat inl_inr_inv.
  all: eq_to_equiv.
  all: rewrite X1_ID, X2_ID, Y_ID in *; clear X1_ID X2_ID Y_ID m0 m1 m2.
  all: rename Heqs into X1_ID, Heqs0 into X2_ID, Heqs1 into Y_ID.
  all: try some_none.
  all: intros; try some_none; repeat some_inv; try inl_inr; inl_inr_inv.
  all: inversion H3; clear H3.
  subst.
  rewrite Heqo3, Heqo2, Heqo1 in *; repeat some_inv.
  rewrite H7 in *; clear H7 m7.
  rewrite X1_M, X2_M, Y_M in *; clear X1_M X2_M Y_M m3 m4 m5.
  rename Heqo3 into X1_M, Heqo2 into X2_M, Heqo1 into Y_M.
  rename Heqs5 into M.
  rewrite <-H in Heqo0.
  rewrite memory_lookup_memory_set_eq in Heqo0 by reflexivity.
  some_inv.
  rewrite Heqo0 in *; clear Heqo0 m6.
  
  apply evalDSHMap2_result with (k:=k) (dot:=dot) in M; try assumption.
  destruct M as [a1 [a2 [X1 [X2 Y]]]].
  unfold mem_lookup in Y.
  rewrite Y.
  unfold mem_lookup, mem_merge_with_def.
  repeat rewrite NP.F.map2_1bis by reflexivity.
  unfold mem_lookup in X1, X2.
  repeat break_match; try some_none; repeat some_inv.
  rewrite X1, X2.
  reflexivity.
Qed.

Lemma mem_firstn_def (k n : nat) (mb : mem_block) (a : CarrierA) :
  mem_lookup k (mem_firstn n mb) = Some a <-> k < n /\ mem_lookup k mb = Some a.
Proof.
  split; intros.
  -
    unfold mem_firstn, mem_lookup, NP.filter_dom in *.
    destruct NM.find eqn:F in H; try some_none; some_inv.
    apply NP.F.find_mapsto_iff, NP.filter_iff in F.
    2: intros k1 k2 EK a1 a2 EA; subst; reflexivity.
    destruct F.
    admit.
  -
    unfold mem_firstn, mem_lookup, NP.filter_dom in *.
    destruct H as [H1 H2].
    destruct (NM.find (elt:=CarrierA) k
                      (NP.filter (λ (k0 : NM.key) (_ : CarrierA), k0 <? n) mb)) eqn:F.
    +
      apply NP.F.find_mapsto_iff, NP.filter_iff in F.
      2: intros k1 k2 EK a1 a2 EA; subst; reflexivity.
      destruct F.
      admit.
    +
      destruct NM.find eqn:H in H2; try some_none; some_inv.
      contradict F.
      apply is_Some_ne_None, is_Some_def.
      eexists.
      apply NP.F.find_mapsto_iff, NP.filter_iff.
      1: intros k1 k2 EK a1 a2 EA; subst; reflexivity.
      split.
      2: admit.
      instantiate (1:=c).
      apply NP.F.find_mapsto_iff.
      assumption.
Admitted.

Lemma mem_firstn_def_eq (k n : nat) (mb : mem_block) (a : CarrierA) :
  mem_lookup k (mem_firstn n mb) ≡ Some a <-> k < n /\ mem_lookup k mb ≡ Some a.
Proof.
  split; intros.
  -
    unfold mem_firstn, mem_lookup, NP.filter_dom in *.
    destruct NM.find eqn:F in H; try some_none; some_inv.
    apply NP.F.find_mapsto_iff, NP.filter_iff in F.
    2: intros k1 k2 EK a1 a2 EA; subst; reflexivity.
    destruct F.
    subst.
    admit.
  -
    unfold mem_firstn, mem_lookup, NP.filter_dom in *.
    destruct H as [H1 H2].
    destruct (NM.find (elt:=CarrierA) k
                      (NP.filter (λ (k0 : NM.key) (_ : CarrierA), k0 <? n) mb)) eqn:F.
    +
      apply NP.F.find_mapsto_iff, NP.filter_iff in F.
      2: intros k1 k2 EK a1 a2 EA; subst; reflexivity.
      destruct F.
      admit.
    +
      destruct NM.find eqn:H in H2; try some_none; some_inv.
      subst.
      contradict F.
      apply is_Some_ne_None, is_Some_def.
      eexists.
      apply NP.F.find_mapsto_iff, NP.filter_iff.
      1: intros k1 k2 EK a1 a2 EA; subst; reflexivity.
      split.
      2: admit.
      eapply NP.F.find_mapsto_iff.
      eassumption.
Admitted.

Lemma mem_firstn_lookup (k n : nat) (mb : mem_block) :
  k < n ->
  mem_lookup k (mem_firstn n mb) ≡ mem_lookup k mb.
Proof.
  intros.
  destruct (mem_lookup k mb) eqn:L.
  -
    rewrite mem_firstn_def_eq.
    auto.
  -
    apply is_None_def.
    enough (not (is_Some (mem_lookup k (mem_firstn n mb))))
      by (unfold is_None, is_Some in *; break_match; auto).
    intros C.
    apply is_Some_def in C.
    destruct C as [mb' MB].
    apply mem_firstn_def_eq in MB.
    destruct MB; some_none.
Qed.

Lemma mem_firstn_lookup_oob (k n : nat) (mb : mem_block) :
  n <= k ->
  mem_lookup k (mem_firstn n mb) ≡ None.
Proof.
  intros.
  apply is_None_def.
  enough (not (is_Some (mem_lookup k (mem_firstn n mb))))
    by (unfold is_None, is_Some in *; break_match; auto).
  intros C.
  apply is_Some_def in C.
  destruct C as [mb' MB]; eq_to_equiv.
  apply mem_firstn_def in MB.
  lia.
Qed.

Lemma firstn_mem_const_block_union (o : nat) (init : CarrierA) (mb : mem_block) :
  mem_firstn o (mem_union (mem_const_block o init) mb) = mem_const_block o init.
Proof.
  intros k.
  destruct (le_lt_dec o k).
  -
    rewrite mem_firstn_lookup_oob, mem_const_block_find_oob by assumption.
    reflexivity.
  -
    rewrite mem_firstn_lookup by assumption.
    unfold mem_union, mem_lookup.
    rewrite NP.F.map2_1bis by reflexivity.
    rewrite mem_const_block_find; auto.
Qed.

Lemma MemMap2_merge_with_def_firstn
      (x1_p x2_p y_p : PExpr)
      (x1_m x2_m y_m : mem_block)
      (σ : evalContext)
      (m : memory)
      (dot : CarrierA -> CarrierA -> CarrierA)
      (PF : Proper ((=) ==> (=) ==> (=)) dot)
      (df : AExpr)
      (init : CarrierA)
      (o : nat)
      (y_id : nat)
      (LX1 : lookup_Pexp σ m x1_p = inr x1_m)
      (LX2 : lookup_Pexp σ m x2_p = inr x2_m)
      (Y_ID : evalPexp σ y_p = inr y_id)
      (YID_M : memory_lookup m y_id = Some y_m)
      (D1 : forall k, k < o -> mem_in k x1_m)
      (D2 : forall k, k < o -> mem_in k x2_m)

      (DC : MSH_DSH_BinCarrierA_compat dot σ df m)
  :
    evalDSHOperator σ (DSHMemMap2 o x1_p x2_p y_p df) m
                    (estimateFuel (DSHMemMap2 o x1_p x2_p y_p df))
    = Some (inr
              (memory_set m y_id (mem_union (mem_merge_with_def dot init
                                                                (mem_firstn o x1_m)
                                                                (mem_firstn o x2_m))
                                            y_m))).
Proof.
  assert (exists m', evalDSHOperator σ (DSHMemMap2 o x1_p x2_p y_p df) m
                  (estimateFuel (DSHMemMap2 o x1_p x2_p y_p df)) = Some (inr m')).
  {
    eapply DSHMap2_succeeds; try eassumption.
    cbn.
    break_match; try inl_inr.
    inl_inr_inv.
    rewrite Y_ID.
    unfold memory_lookup_err.
    rewrite YID_M.
    cbn.
    reflexivity.
  }
  destruct H as [ma MA].
  rewrite MA.
  do 2 f_equiv.
  intros b_id.
  destruct (Nat.eq_dec b_id y_id).
  -
    subst b_id.
    unfold memory_set.
    rewrite NP.F.add_eq_o by reflexivity.
    assert (exists y_ma, lookup_Pexp σ ma y_p = inr y_ma).
    {
      apply equiv_Some_is_Some, memory_is_set_is_Some,
      (mem_stable _ _ _ _ MA), mem_block_exists_exists in YID_M.
      destruct YID_M as [y_ma H].
      exists y_ma.
      cbn.
      break_match; try inl_inr.
      apply memory_lookup_err_inr_Some.
      inv Y_ID.
      rewrite H2, H.
      reflexivity.
    }
    destruct H as [y_ma Y_MA].
    assert (T : NM.find (elt:=mem_block) y_id ma = Some y_ma)
      by admit. (* Y_ID + Y_MA *) (* @lord *)
    rewrite T; clear T.
    f_equiv.
    intros k.
    destruct (le_lt_dec o k).
    +
      unfold mem_union.
      rewrite NP.F.map2_1bis by reflexivity.
      assert (NM.find (elt:=CarrierA) k
                      (mem_merge_with_def dot init (mem_firstn o x1_m)
                                          (mem_firstn o x2_m)) = None).
      {
        unfold mem_merge_with_def.
        rewrite NP.F.map2_1bis by reflexivity.
        repeat rewrite mem_firstn_lookup_oob by assumption; reflexivity.
      }
      break_match; try some_none.
      clear Heqo0 H.
      admit. (* follows from [MA] by [evalDSHMap2_rest_preserved] *) (* @lord *)
    +
      erewrite MemMap2_merge_with_def.
      7: eapply MA.
      all: try eassumption.
      2: {
        unfold lookup_Pexp, memory_lookup_err, trywith.
        cbn.
        repeat break_match; try some_none; try inl_inr.
        all: inl_inr_inv.
        all: eq_to_equiv.
        all: rewrite Y_ID in Heqo0.
        all: rewrite Heqo0 in YID_M.
        all: try some_none; some_inv.
        rewrite YID_M.
        reflexivity.
      }
      instantiate (1:=init).
      unfold mem_lookup, mem_union, mem_merge_with_def.
      repeat rewrite NP.F.map2_1bis by reflexivity.
      assert (exists k_x1m, mem_lookup k x1_m = Some k_x1m) by admit.
      destruct H as [k_x1m K_X1M].
      assert (exists k_x2m, mem_lookup k x2_m = Some k_x2m) by admit.
      destruct H as [k_x2m K_X2M].
      repeat rewrite mem_firstn_lookup by assumption.
      unfold mem_lookup in *.
      repeat break_match; try some_none.
  -
    unfold memory_set.
    rewrite NP.F.add_neq_o by congruence.
    admit. (* pure + MA *) (* @lord *)
Admitted.

Global Instance eq_equiv_subrelation `{Equivalence A EqA} :
  subrelation (@eq A) (@equiv A EqA).
Proof.
  intros a b E.
  subst.
  reflexivity.
Qed.

Lemma is_OK_def {A : Type} {e : err A} :
  is_OK e <-> exists a, e ≡ inr a.
Proof.
  split; intros.
  -
    destruct e; inversion H.
    exists a.
    reflexivity.
  -
    destruct H.
    subst.
    constructor.
Qed.

(*
Lemma IReduction_MSH_no_output
      (i n : nat)
      (init : CarrierA)
      (dot : CarrierA -> CarrierA -> CarrierA)
      (pdot : Proper ((=) ==> (=) ==> (=)) dot)
      (op_family : @MSHOperatorFamily i 0 n)
      (xb mb : mem_block)
      (MF : MSHOperator_Facts (@MSHIReduction i 0 n init dot _ op_family))
  :
    mem_op (@MSHIReduction i 0 n init dot _ op_family) xb = Some mb ->
    mb = mem_empty.
Proof.
  intros.
  inversion_clear MF as [T1 T2 OOB]; clear T1 T2.
  destruct mem_op eqn:MOP; try some_none; some_inv.
  intros k.
  apply OOB with (j:=k) in MOP; [| lia].
  rewrite H in MOP.
  clear - MOP.
  unfold MMemoryOfCarrierA.mem_in in MOP.
  apply NP.F.not_find_in_iff in MOP.
  rewrite MOP.
  reflexivity.
Qed.
*)

Lemma evalDSHOperator_mem_proper
      (σ : evalContext)
      (dop : DSHOperator)
      (m1 m2 rm1 rm2 : memory)
      (fuel : nat)
  :
    m1 = m2 ->
    evalDSHOperator σ dop m1 fuel = Some (inr rm1) ->
    evalDSHOperator σ dop m2 fuel = Some (inr rm2) ->
    rm1 = rm2.
Proof.
  intros ME M1 M2.
  destruct fuel; [cbn in M1; some_none |].
  induction dop.
  7,8,11:  admit.
  all: cbn in M1, M2.
  1: do 2 (some_inv; inl_inr_inv); rewrite <-M1, <-M2; assumption.
  all: repeat break_match;
    try some_none; repeat some_inv;
    try inl_inr; repeat inl_inr_inv.
  all: eq_to_equiv; memory_lookup_err_to_option.
  -
    rewrite ME in *; clear ME m1.
    rewrite <-M1, <-M2.
    f_equiv.
    rewrite Heqs1 in Heqs6; some_inv.
    rewrite Heqs6 in Heqs5.
    rewrite Heqs5 in Heqs8; inl_inr_inv.
    rewrite Heqs8.
    rewrite Heqs2 in Heqs7; some_inv.
    rewrite Heqs7.
    reflexivity.
  -
    
Admitted.

Lemma memory_set_same (m : memory) (k : mem_block_id) (mb : mem_block) :
  memory_lookup m k = Some mb ->
  memory_set m k mb = m.
Proof.
  intros H k'.
  unfold memory_set, memory_lookup in *.
  destruct (Nat.eq_dec k k').
  -
    subst.
    rewrite NP.F.add_eq_o by congruence.
    auto.
  -
    rewrite NP.F.add_neq_o by congruence.
    reflexivity.
Qed.

Lemma evalDSHOperator_fuel_ge_equiv
      (f f' : nat)
      (σ : evalContext)
      (op : DSHOperator)
      (m : memory)
      (res : err memory)
  :
    f' ≥ f →
    evalDSHOperator σ op m f = Some res →
    evalDSHOperator σ op m f' = Some res.
Proof.
  intros.
  destruct (evalDSHOperator σ op m f) eqn:D,
           (evalDSHOperator σ op m f') eqn:D';
    try some_none.
  all: apply evalDSHOperator_fuel_ge with (f':=f') in D; [| assumption].
  all: rewrite D in D'; some_inv; subst.
  assumption.
  some_none.
Qed.

(** not used anymore, left in for future reference *)
(*
Lemma MemMap2_merge_with_def_O
      (x1_p x2_p y_p : PExpr)
      (x1_m x2_m y_m: mem_block)
      (y_id : mem_block_id)
      (σ : evalContext)
      (m : memory)
      (df : AExpr)
      (LX1 : lookup_Pexp σ m x1_p = inr x1_m)
      (LX2 : lookup_Pexp σ m x2_p = inr x2_m)
      (Y_ID : evalPexp σ y_p = inr y_id)
      (Y_M : memory_lookup m y_id = Some y_m)
  :
    evalDSHOperator σ (DSHMemMap2 0 x1_p x2_p y_p df) m
                    (estimateFuel (DSHMemMap2 0 x1_p x2_p y_p df)) =
    Some (inr m).
Proof.
  apply lookup_Pexp_eval_lookup in LX1.
  destruct LX1 as [x1_id [X1_ID X1_M]].
  apply lookup_Pexp_eval_lookup in LX2.
  destruct LX2 as [x2_id [X2_ID X2_M]].
  cbn.

  unfold memory_lookup_err, trywith.
  repeat break_match;
    try some_none; repeat some_inv;
    try inl_inr; repeat inl_inr_inv.
  all: eq_to_equiv.
  all: rewrite X1_ID, X2_ID, Y_ID in *; clear X1_ID X2_ID Y_ID m0 m1 m2.
  all: try some_none.
  subst.
  repeat f_equiv.
  clear - Heqo.
  unfold memory_lookup, memory_set in *.
  intros k.
  destruct (Nat.eq_dec k y_id).
  -
    subst.
    rewrite NP.F.add_eq_o by reflexivity.
    auto.
  -
    rewrite NP.F.add_neq_o by congruence.
    reflexivity.
Qed.

Lemma MemInit_O
      (σ : evalContext)
      (y_p : PExpr)
      (init : CarrierA)
      (dop : DSHOperator)
      (m m' : memory)
      (fuel : nat)
  :
    evalDSHOperator σ (DSHSeq (DSHMemInit 0 y_p init) dop) m fuel = Some (inr m') ->
    evalDSHOperator σ dop m fuel = Some (inr m').
Proof.
  intros.
  destruct fuel; [cbn in H; some_none |].
  cbn in H.
  repeat break_match; try some_none; repeat some_inv; try inl_inr; repeat inl_inr_inv.
  subst.
  destruct fuel; [cbn in Heqo; some_none |].
  cbn in Heqo.
  some_inv.
  repeat break_match; try inl_inr; repeat inl_inr_inv.
  enough (T : m = m0)
    by (rewrite T; eapply evalDSHOperator_fuel_ge_equiv; [repeat constructor | eassumption]).
  rewrite <-H2; clear H2 H m0.
  assert (T : mem_union mem_empty m2 = m2);
    [| rewrite T; clear T].
  {
    clear.
    unfold mem_union.
    intros k.
    rewrite NP.F.map2_1bis by reflexivity.
    cbn.
    reflexivity.
  }
  memory_lookup_err_to_option; eq_to_equiv.
  rewrite memory_set_same by assumption.
  reflexivity.
Qed.

Lemma MemMap2_O
      (σ : evalContext)
      (x1_p x2_p y_p : PExpr)
      (df : AExpr)
      (m m' : memory)
      (fuel : nat)
  :
    evalDSHOperator σ (DSHMemMap2 0 x1_p x2_p y_p df) m fuel = Some (inr m') ->
    m' = m.
Proof.
  intros.
  destruct fuel; cbn in H; [some_none |].
  repeat break_match;
    try some_none; repeat some_inv;
    try inl_inr; repeat inl_inr_inv.
  memory_lookup_err_to_option.
  rewrite <-H.
  apply memory_set_same.
  eq_to_equiv.
  assumption.
Qed.

Lemma IReduction_DSH_no_change
      (n : nat)
      (init : CarrierA)
      (df : AExpr)
      (σ : evalContext)
      (y_p y_p'': PExpr)
      (Y : y_p'' ≡ incrPVar 0 (incrPVar 0 y_p))
      (rr : DSHOperator)
      (m m' : memory)
      (P: DSH_pure rr (PVar 1))
  :
   evalDSHOperator σ
        (DSHSeq (DSHMemInit 0 y_p init)
           (DSHAlloc 0 (DSHLoop n (DSHSeq rr (DSHMemMap2 0 (PVar 1) y_p'' y_p'' df))))) m
        (estimateFuel
           (DSHSeq (DSHMemInit 0 y_p init)
              (DSHAlloc 0 (DSHLoop n (DSHSeq rr (DSHMemMap2 0 (PVar 1) y_p'' y_p'' df)))))) =
      Some (inr m') ->
  m' = m.
Proof.
  intros.
  apply MemInit_O in H.
  rewrite evalDSHOperator_estimateFuel_ge in H by (cbn; lia).
  remember (DSHLoop n (DSHSeq rr (DSHMemMap2 0 (PVar 1) y_p'' y_p'' df))) as loop.
  cbn in H.
  repeat break_match;
    try some_none; repeat some_inv;
    try inl_inr; repeat inl_inr_inv.
  subst.
  rewrite <-H; clear H m'; rename m0 into m', Heqo into DOP.
  eq_to_equiv.

  generalize dependent m.
  generalize dependent m'.
  induction n; intros.
  -
    cbn in DOP.
    some_inv; inl_inr_inv.
    rewrite <-DOP.
    rewrite memory_remove_memory_set_eq by reflexivity.
    rewrite memory_remove_nonexistent_key by (apply mem_block_exists_memory_next_key).
    reflexivity.
  -
    cbn [evalDSHOperator estimateFuel] in DOP.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv; subst.
    eq_to_equiv.
    rewrite evalDSHOperator_estimateFuel_ge in * by (cbn; nia).
    eapply IHn in Heqo; clear IHn.
    rewrite <-Heqo at 2; clear Heqo.

    cbn [evalDSHOperator estimateFuel] in DOP.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv; subst.
    eq_to_equiv.
    rewrite evalDSHOperator_estimateFuel_ge in * by (cbn; nia).
    apply MemMap2_O in DOP.
    rewrite DOP; clear DOP m'.
    inversion_clear P as [T S]; clear T.
    remember (memory_next_key m) as j.
    apply S with (y_i:=j) in Heqo; [| reflexivity].
    clear S.
    intros k.
    unfold memory_remove.
    destruct (Nat.eq_dec k j).
    +
      repeat rewrite NP.F.remove_eq_o by congruence.
      reflexivity.
    +
      repeat rewrite NP.F.remove_neq_o by congruence.
      specialize (Heqo k n0).
      auto.
Qed.

Global Instance IReduction_MSH_DSH_compat_oO
       {i n: nat}
       {init : CarrierA}
       {dot: CarrierA -> CarrierA -> CarrierA}
       {pdot: Proper ((=) ==> (=) ==> (=)) dot}
       {op_family: @MSHOperatorFamily i 0 (S n)}
       {df : AExpr}
       {σ : evalContext}
       {x_p y_p y_p'': PExpr}
       {XY : evalPexp σ x_p <> evalPexp σ y_p}
       {Y : y_p'' ≡ incrPVar 0 (incrPVar 0 y_p)}
       {rr : DSHOperator}
       {m : memory}
       {DP}
       (P: DSH_pure rr (PVar 1))
       (DC : forall m' y_id d1 d2,
           evalPexp σ y_p ≡ inr y_id ->
           memory_subset_except y_id m m'  ->
           MSH_DSH_BinCarrierA_compat dot (d1 :: d2 :: σ) df m')
       (FC : forall m' tmpk t y_id,
           evalPexp σ y_p ≡ inr y_id ->
           memory_subset_except y_id m m'  ->
           tmpk ≡ memory_next_key m' ->
           @MSH_DSH_compat _ _ (op_family t) rr
                           (DSHnatVal (proj1_sig t) :: DSHPtrVal tmpk 0 :: σ)
                           (memory_set m' tmpk (mem_empty))
                           (incrPVar 0 (incrPVar 0 x_p)) (PVar 1) P)
       (MF : MSHOperator_Facts (@MSHIReduction i 0 (S n) init dot _ op_family))
  :
    @MSH_DSH_compat
      _ _
      (@MSHIReduction i 0 (S n) init dot _ op_family)
      (DSHSeq
         (DSHMemInit 0 y_p init)
         (DSHAlloc 0
                   (DSHLoop (S n)
                            (DSHSeq
                               rr
                               (DSHMemMap2 0 (PVar 1)
                                           y_p''
                                           y_p''
                                           df)))))
      σ m x_p y_p DP.
Proof.
  subst.
  constructor.
  intros x_m y_m X_M Y_M.
  destruct mem_op as [mma |] eqn:MOP.
  all: destruct evalDSHOperator as [r |] eqn:DOP; [destruct r as [msg | dma] |].
  all: repeat constructor.
  1,3,4: exfalso; admit.
  - (* MSH succeeds, DSH succeeds *)
    assert (Proper ((=) ==> iff)
                   (λ ma : mem_block, SHCOL_DSHCOL_mem_block_equiv y_m ma mma))
      by (intros m1 m2 ME; rewrite ME; reflexivity).

    eq_to_equiv.
    apply IReduction_DSH_no_change in DOP; auto.
    rewrite DOP.
    rewrite Y_M.
    constructor.
    apply IReduction_MSH_no_output in MOP; auto.
    rewrite MOP.
    constructor; reflexivity.
Admitted.
*)

Lemma IReduction_Some_family_inv
      (i o n : nat)
      (op_family: @MSHOperatorFamily i o n)
      (init : CarrierA)
      (dot : CarrierA -> CarrierA -> CarrierA)
      (pdot: Proper ((=) ==> (=) ==> (=)) dot)
      (mb : mem_block)
  :
    is_Some (mem_op (@MSHIReduction i o n init dot pdot op_family) mb) ->
    forall t, is_Some (mem_op (op_family t) mb).
Proof.
  intros.
  cbn in H.
  unfold Apply_mem_Family, get_family_mem_op in H.
  break_match; try some_none.
  clear H; rename Heqo0 into H.
  destruct t as [t tc].
  pose proof H as H1.
  apply ListSetoid.monadic_Lbuild_opt_length in H.
  apply ListSetoid.monadic_Lbuild_op_eq_Some with (i0:=t) (ic:=tc) in H1.
  assert ((t ↾ tc) ≡ mkFinNat tc) by reflexivity.
  rewrite H0; clear H0.
  rewrite <-H1; clear H1.
  clear - H tc.

  generalize dependent t.
  generalize dependent n.
  induction l.
  -
    intros.
    cbn in H; subst.
    inversion tc.
  -
    intros.
    destruct t; [reflexivity |].
    destruct n; [discriminate |].
    apply IHl with (n:=n).
    cbn in H; lia.
    lia.
Qed.

Lemma fold_left_rev_invariant
      {A : Type}
      (f : A -> A -> A)
      (init : A)
      (l : list A)
      (P : A -> Prop)
  :
    (forall a b, P a \/ P b -> P (f a b)) ->
    (exists a, P a /\ List.In a l) ->
    P (ListUtil.fold_left_rev f init l).
Proof.
  intros.
  destruct H0 as [x [Px XL]].
  induction l; [inversion XL |].
  cbn in *.
  destruct XL as [AX | XX]; subst; auto.
Qed.


(*
Lemma IReduction_family_OOB
      (i o n : nat)
      (op_family: @MSHOperatorFamily i o n)

      (init : CarrierA)
      (dot : CarrierA -> CarrierA -> CarrierA)
      {pdot: Proper ((=) ==> (=) ==> (=)) dot}

      (mb : mem_block)
      (MF : MSHOperator_Facts (@MSHIReduction i o n init dot pdot op_family))
  :
    is_Some (mem_op (@MSHIReduction i o n init dot _ op_family) mb) ->
    forall t rm, mem_op (op_family t) mb ≡ Some rm ->
            ∀ j, j ≥ o → ¬ mem_in j rm.
Proof.
  intros.
  apply is_Some_def in H; destruct H as [rrm H].
  inversion_clear MF as [T1 T2 OOB]; clear T1 T2.
  pose proof H as RRM.
  apply OOB with (j:=j) in H; clear OOB; [| assumption].
  intros I; contradict H.
  cbn in RRM.
  unfold Apply_mem_Family, get_family_mem_op in RRM.
  break_match; try some_none; some_inv.

  apply fold_left_rev_invariant.
  +
    intros.
    apply MMemoryOfCarrierA.mem_merge_with_def_as_Union.
    assumption.
  +
    exists rm.
    split; auto.
    destruct t as [t tc].
    apply ListSetoid.monadic_Lbuild_op_eq_Some with (i0:=t) (ic:=tc) in Heqo0.
    assert ((t ↾ tc) ≡ mkFinNat tc) by reflexivity.
    rewrite H in *.
    rewrite H0 in Heqo0.
    eapply List.nth_error_In.
    eassumption.
Qed.
 *)

Lemma mem_not_in_mem_lookup (k : NM.key) (mb : mem_block) :
  not (mem_in k mb) <-> is_None (mem_lookup k mb).
Proof.
  rewrite is_None_def.
  apply NP.F.not_find_in_iff.
Qed.

Lemma SHCOL_DSHCOL_mem_block_equiv_keys_union (ma mb md : mem_block) :
  SHCOL_DSHCOL_mem_block_equiv mb ma md ->
  forall k, mem_in k mb \/ mem_in k md <-> mem_in k ma.
Proof.
  intros.
  specialize (H k).
  inversion H.
  all: repeat rewrite mem_in_mem_lookup in *.
  all: repeat rewrite mem_not_in_mem_lookup in *.
  all: unfold is_None, is_Some in *.
  all: repeat break_match; try some_none.
  all: intuition.
Qed.

Lemma MemMap2_rest_preserved 
      (x1_p x2_p y_p : PExpr)
      (y_m y_m' : mem_block)
      (m m' : memory)
      (df : AExpr)
      (σ : evalContext)
      (o : nat)
      (Y_M : lookup_Pexp σ m y_p = inr y_m)
      (Y_M' : lookup_Pexp σ m' y_p = inr y_m')
  :
    evalDSHOperator σ (DSHMemMap2 o x1_p x2_p y_p df) m
                    (estimateFuel (DSHMemMap2 o x1_p x2_p y_p df)) = Some (inr m') ->
    forall k, o <= k → mem_lookup k y_m' = mem_lookup k y_m.
Proof.
  intros.
  cbn in H.
  cbn in Y_M, Y_M'.
  repeat break_match;
    try some_none; repeat some_inv;
    try inl_inr; repeat inl_inr_inv.
  eq_to_equiv.
  apply evalDSHMap2_rest_preserved with (k:=k) in Heqs5; [| assumption].
  repeat break_match; try inl_inr.
  memory_lookup_err_to_option.
  rewrite <-H in Y_M'.
  rewrite memory_lookup_memory_set_eq in Y_M' by reflexivity.
  some_inv; rewrite Y_M' in *; clear Y_M' m6.
  rewrite Heqs4 in Y_M.
  some_inv; rewrite Y_M in *; clear Y_M m5.
  assumption.
Qed.

Lemma IReduction_MSH_step
      {i o n : nat}
      (mb : mem_block)
      (dot : CarrierA -> CarrierA -> CarrierA)
      (pdot : Proper ((=) ==> (=) ==> (=)) dot)
      (init : CarrierA)
      (S_opf : @MSHOperatorFamily i o (S n))
  :
    let opf := shrink_m_op_family S_opf in
    let fn := mkFinNat (Nat.lt_succ_diag_r n) in
    mem_op (MSHIReduction init dot S_opf) mb =
    mb' <- mem_op (MSHIReduction init dot opf) mb ;;
    mbn <- mem_op (S_opf fn) mb ;;
    Some (mem_merge_with_def dot init mb' mbn).
Proof.
  simpl.
  unfold IReduction_mem.
  simpl.
  unfold Apply_mem_Family in *.
  repeat break_match;
    try discriminate; try reflexivity.
  all: repeat some_inv; subst.
  -
    rename l into S_lb, l0 into lb.

    (* poor man's apply to copy and avoid evars *)
    assert (S_LB : ∀ (j : nat) (jc : (j < S n)%mc),
               List.nth_error S_lb j ≡ get_family_mem_op S_opf j jc mb)
      by (apply ListSetoid.monadic_Lbuild_op_eq_Some; assumption).
    assert (LB : ∀ (j : nat) (jc : (j < n)%mc),
               List.nth_error lb j ≡ get_family_mem_op (shrink_m_op_family S_opf) j jc mb)
      by (apply ListSetoid.monadic_Lbuild_op_eq_Some; assumption).

    apply ListSetoid.monadic_Lbuild_opt_length in Heqo0; rename Heqo0 into S_L.
    apply ListSetoid.monadic_Lbuild_opt_length in Heqo3; rename Heqo3 into L.
    rename m0 into mbn, Heqo2 into MBN.

    unfold get_family_mem_op in *.
    assert (H : forall j, j < n -> List.nth_error lb j ≡ List.nth_error S_lb j)
      by (intros; erewrite S_LB, LB; reflexivity).
    Unshelve. 2: assumption.

    assert (N_MB : is_Some (mem_op (S_opf (mkFinNat (Nat.lt_succ_diag_r n))) mb)).
    {
      apply is_Some_ne_None.
      intro C.
      rewrite <-S_LB in C.
      apply List.nth_error_None in C.
      lia.
    }
    apply is_Some_def in N_MB.
    destruct N_MB as [n_mb N_MB].

    assert (H1 : S_lb ≡ lb ++ [n_mb]).
    {
      apply list_eq_nth;
        [rewrite List.app_length; cbn; lia |].
      intros k KC.
      (* extensionality *)
      enough (forall d, List.nth k S_lb d ≡ List.nth k (lb ++ [n_mb]) d)
        by (apply Logic.FunctionalExtensionality.functional_extensionality; assumption).
      rewrite S_L in KC.
      destruct (Nat.eq_dec k n).
      -
        subst k.
        intros.
        apply List_nth_nth_error.
        replace n with (0 + Datatypes.length lb).
        rewrite ListNth.nth_error_length.
        cbn.
        rewrite L.
        rewrite S_LB with (jc := (Nat.lt_succ_diag_r n)).
        rewrite <-N_MB.
        reflexivity.
      -
        assert (k < n) by lia; clear KC n0.
        intros.
        apply List_nth_nth_error.
        rewrite <-H by lia.
        rewrite List.nth_error_app1 by lia.
        reflexivity.
    }

    rewrite H1.
    rewrite List.fold_left_app.
    cbn.

    rewrite MBN in N_MB; some_inv.
    reflexivity.
  -
    rename l into S_lb, l0 into lb.

    (* poor man's apply to copy and avoid evars *)
    assert (S_LB : ∀ (j : nat) (jc : (j < S n)%mc),
               List.nth_error S_lb j ≡ get_family_mem_op S_opf j jc mb)
      by (apply ListSetoid.monadic_Lbuild_op_eq_Some; assumption).
    apply ListSetoid.monadic_Lbuild_opt_length in Heqo0; rename Heqo0 into S_L.

    assert (N_MB : is_Some (mem_op (S_opf (mkFinNat (Nat.lt_succ_diag_r n))) mb)).
    {
      apply is_Some_ne_None.
      intro C.
      unfold get_family_mem_op in *.
      rewrite <-S_LB in C.
      apply List.nth_error_None in C.
      lia.
    }

    rewrite Heqo2 in N_MB.
    some_none.
  -
    exfalso; clear Heqo1.

    pose proof Heqo0 as L; apply ListSetoid.monadic_Lbuild_opt_length in L.

    apply ListSetoid.monadic_Lbuild_op_eq_None in Heqo2.
    destruct Heqo2 as [k [KC N]].
    apply ListSetoid.monadic_Lbuild_op_eq_Some
      with (i0:=k) (ic:=le_S KC)
      in Heqo0.
    unfold get_family_mem_op, shrink_m_op_family in *.
    cbn in *.
    rewrite N in Heqo0.
    apply ListNth.nth_error_length_ge in Heqo0.
    assert (k < n) by assumption.
    lia.
  -
    exfalso.

    pose proof Heqo3 as S_L; apply ListSetoid.monadic_Lbuild_opt_length in S_L.

    apply ListSetoid.monadic_Lbuild_op_eq_None in Heqo0.
    destruct Heqo0 as [k [KC N]].
    destruct (Nat.eq_dec k n).
    +
      subst k.
      unfold get_family_mem_op in *.
      assert (KC ≡ (Nat.lt_succ_diag_r n)) by (apply lt_unique).
      rewrite <-H, N in Heqo2.
      some_none.
    +
      assert (k < n) by (assert (k < S n) by assumption; lia); clear n0.
      apply ListSetoid.monadic_Lbuild_op_eq_Some
        with (i0:=k) (ic:=H)
        in Heqo3.
      unfold get_family_mem_op, shrink_m_op_family in *.
      cbn in Heqo3.
      assert (le_S H ≡ KC) by (apply lt_unique).
      rewrite H0, N in Heqo3.
      apply ListNth.nth_error_length_ge in Heqo3.
      rewrite S_L in Heqo3.
      omega.
Qed.

(* [body] here corresponds to IReduction's [seq rr memmap2] *)
Lemma IReduction_DSH_step
      (o n : nat)
      (body : DSHOperator)
      (m loopN_m iterSN_m : memory)
      (σ : evalContext)
      (t_id : mem_block_id)
      (T_ID : t_id ≡ memory_next_key m)
      (body_mem_stable : ∀ σ m m' fuel,
          evalDSHOperator σ body m fuel = Some (inr m')
          → ∀ k, mem_block_exists k m ↔ mem_block_exists k m')

      (LoopN : evalDSHOperator σ
                               (DSHAlloc o (DSHLoop n body)) m
                               (estimateFuel (DSHAlloc o (DSHLoop n body)))
               = Some (inr loopN_m))
      (IterSN : evalDSHOperator (DSHnatVal n :: DSHPtrVal t_id o :: σ)
                                body
                                (memory_set loopN_m t_id mem_empty)
                                (estimateFuel body) = Some (inr iterSN_m))

      (* execution of [body] does not depend on block under [t_id] *)
      (BS : forall mb, evalDSHOperator (DSHnatVal n :: DSHPtrVal t_id o :: σ)
                                    body
                                    (memory_set loopN_m t_id mb)
                                    (estimateFuel body) =
                    evalDSHOperator (DSHnatVal n :: DSHPtrVal t_id o :: σ)
                                    body
                                    (memory_set loopN_m t_id mem_empty)
                                    (estimateFuel body))
  :
    evalDSHOperator σ (DSHAlloc o (DSHLoop (S n) body)) m
                  (estimateFuel (DSHAlloc o (DSHLoop (S n) body))) = 
    Some (inr (memory_remove iterSN_m t_id)).
Proof.
  cbn.
  remember (DSHLoop n body) as loop_n.
  cbn in LoopN.
  rewrite <-T_ID in *.
  rewrite evalDSHOperator_estimateFuel_ge
    by (pose proof estimateFuel_positive body; subst; cbn; lia).
  destruct (evalDSHOperator (DSHPtrVal t_id o :: σ) loop_n
                            (memory_set m t_id mem_empty) (estimateFuel loop_n))
           as [t|] eqn:LoopN'; [destruct t as [|loopN_m'] |];
    try some_none; some_inv; try inl_inr; inl_inr_inv.
  assert (T : exists t_loopN_m', memory_lookup loopN_m' t_id = Some t_loopN_m');
    [| destruct T as [t_loopN_m' T_loopN_m']].
  {
    subst loop_n.
    clear - LoopN' body_mem_stable.
    enough (loopn_mem_stable : ∀ σ m m' fuel,
               evalDSHOperator σ (DSHLoop n body) m fuel = Some (inr m')
               → ∀ k, mem_block_exists k m ↔ mem_block_exists k m').
    {
      apply is_Some_equiv_def.
      apply memory_is_set_is_Some.
      eq_to_equiv.
      apply loopn_mem_stable with (k:=t_id) in LoopN'.
      apply LoopN'.
      apply mem_block_exists_memory_set_eq.
      reflexivity.
    }

    clear - body_mem_stable.
    intros.
    destruct fuel; [inversion H |].
    generalize dependent m'.
    induction n.
    -
      intros.
      cbn in H.
      some_inv; inl_inr_inv.
      rewrite H.
      reflexivity.
    -
      intros.
      cbn in H.
      repeat break_match;
        try some_none; repeat some_inv;
        try inl_inr; repeat inl_inr_inv.
      subst.
      specialize (IHn m0).
      apply evalDSHOperator_fuel_ge with (f':=S fuel) in Heqo; [| auto].
      eq_to_equiv.
      apply IHn in Heqo; clear IHn.
      rewrite Heqo.
      eapply body_mem_stable.
      eassumption.
  }
  assert (loopN_m' = memory_set loopN_m t_id t_loopN_m').
  {
    clear - T_loopN_m' LoopN.
    intros k.
    destruct (Nat.eq_dec k t_id).
    -
      subst.
      unfold memory_set.
      rewrite NP.F.add_eq_o by reflexivity.
      apply T_loopN_m'.
    -
      unfold memory_set.
      rewrite NP.F.add_neq_o by congruence.
      specialize (LoopN k).
      unfold memory_remove in LoopN.
      rewrite NP.F.remove_neq_o in LoopN by congruence.
      assumption.
  }

  specialize (BS t_loopN_m').
  rewrite <-H in BS. (* PROPER *)
  rewrite evalDSHOperator_estimateFuel_ge
    by (pose proof estimateFuel_positive body; subst; cbn; nia).
  rewrite IterSN in BS.
  destruct (evalDSHOperator (DSHnatVal n :: DSHPtrVal t_id o :: σ) body
                            loopN_m' (estimateFuel body))
           as [t|] eqn:IterSN'; [destruct t as [|iterSN_m'] |];
    try some_none; some_inv; try inl_inr; inl_inr_inv.
  repeat f_equiv.
  assumption.
Qed.

Global Instance IReduction_MSH_DSH_compat_S
       {i o n: nat}
       {init : CarrierA}
       {dot: CarrierA -> CarrierA -> CarrierA}
       {pdot: Proper ((=) ==> (=) ==> (=)) dot}
       {op_family: @MSHOperatorFamily i o (S n)}
       {df : AExpr}
       {σ : evalContext}
       {x_p y_p y_p'': PExpr}
       {XY : evalPexp σ x_p <> evalPexp σ y_p}
       {Y : y_p'' ≡ incrPVar 0 (incrPVar 0 y_p)}
       {rr : DSHOperator}
       {m : memory}
       {DP}
       (P: DSH_pure rr (PVar 1))
       (DC : forall m' y_id d1 d2,
           evalPexp σ y_p ≡ inr y_id ->
           memory_subset_except y_id m m'  ->
           MSH_DSH_BinCarrierA_compat dot (d1 :: d2 :: σ) df m')
       (FC : forall m' tmpk t y_id,
           evalPexp σ y_p ≡ inr y_id ->
           memory_subset_except y_id m m'  ->
           tmpk ≡ memory_next_key m' ->
           @MSH_DSH_compat _ _ (op_family t) rr
                           (DSHnatVal (proj1_sig t) :: DSHPtrVal tmpk o :: σ)
                           (memory_set m' tmpk (mem_empty))
                           (incrPVar 0 (incrPVar 0 x_p)) (PVar 1) P)
       (MF : MSHOperator_Facts (@MSHIReduction i o (S n) init dot _ op_family))
       (FMF : ∀ (j : nat) (jc : j < (S n)), MSHOperator_Facts (op_family (mkFinNat jc)))
       (FD : ∀ (j : nat) (jc : j < (S n)),
           Same_set (FinNat o) (m_out_index_set (op_family (mkFinNat jc)))
                    (Full_set (FinNat o)))
  :
    @MSH_DSH_compat
      _ _
      (@MSHIReduction i o (S n) init dot pdot op_family)
      (DSHSeq
         (DSHMemInit o y_p init)
         (DSHAlloc o
                   (DSHLoop (S n)
                            (DSHSeq
                               rr
                               (DSHMemMap2 o y_p''
                                           (PVar 1)
                                           y_p''
                                           df)))))
      σ m x_p y_p DP.
Proof.
  subst.
  constructor.
  intros x_m y_m X_M Y_M.

  (** * prepare context and memory lookups *)
  destruct (evalPexp σ x_p) as [| x_id] eqn:X_ID;
    [unfold lookup_Pexp in X_M; rewrite X_ID in X_M; inversion X_M |].
  destruct (evalPexp σ y_p) as [| y_id] eqn:Y_ID;
    [unfold lookup_Pexp in Y_M; rewrite Y_ID in Y_M; inversion Y_M |].
  assert (XID_M : memory_lookup m x_id = Some x_m)
    by (unfold lookup_Pexp in X_M; rewrite X_ID in X_M;
        cbn in X_M; memory_lookup_err_to_option; assumption).
  assert (YID_M : memory_lookup m y_id = Some y_m)
    by (unfold lookup_Pexp in Y_M; rewrite Y_ID in Y_M;
        cbn in Y_M; memory_lookup_err_to_option; assumption).

  (** * go through init *)
  remember (DSHLoop (S n)
                (DSHSeq rr
                   (DSHMemMap2 o (PVar 1) (incrPVar 0 (incrPVar 0 y_p))
                               (incrPVar 0 (incrPVar 0 y_p)) df)))
    as loop eqn:LOOP.
  remember (DSHAlloc o loop) as dop.
  cbn [evalDSHOperator estimateFuel].
  rewrite evalDSHOperator_estimateFuel_ge by (subst; cbn; lia).
  cbn [evalDSHOperator estimateFuel].
  simpl bind.
  rewrite Y_ID.
  unfold memory_lookup_err.
  destruct (memory_lookup m y_id) eqn:YID_M'; try some_none.
  replace (trywith "Error looking up 'y' in DSHMemInit" (Some m0))
    with (@inr string mem_block m0)
    by reflexivity.
  rewrite evalDSHOperator_estimateFuel_ge by (subst; cbn; lia).
  some_inv.
  rename m0 into y_m'.
  remember (memory_set m y_id
                       (mem_union (mem_const_block (NatAsNT.MNatAsNT.to_nat o) init)
                                  y_m'))
    as init_m eqn:INIT_M; symmetry in INIT_M.
  remember (memory_next_key init_m) as t_id eqn:T_ID; symmetry in T_ID.
  subst dop.

  (** * deal with y_m and y_m' (get rid of one) *)
  remember (λ (md : mem_block) (m' : memory),
            err_p (λ ma : mem_block, SHCOL_DSHCOL_mem_block_equiv y_m ma md)
                  (lookup_Pexp σ m' y_p))
    as Rel'.
  rename y_m' into t, y_m into y_m';
    rename t into y_m, YID_M into YM_YM', YID_M' into YID_M.
  rewrite <-YM_YM' in Y_M.
  remember (λ (md : mem_block) (m' : memory),
             err_p (λ ma : mem_block, SHCOL_DSHCOL_mem_block_equiv y_m ma md)
                   (lookup_Pexp σ m' y_p)) as Rel.
  assert (T : forall omb oem, h_opt_opterr_c Rel omb oem <-> h_opt_opterr_c Rel' omb oem);
    [| apply T; clear T HeqRel' Rel' YM_YM' y_m'].
  {
    assert (forall mb m, Rel' mb m <-> Rel mb m).
    {
      subst; clear - YM_YM'.
      split; intros.
      all: inversion H; constructor.
      all: rewrite YM_YM' in *; assumption.
    }
    clear - H.
    split; intros.
    all: inversion H0; try constructor.
    all: apply H.
    all: assumption.
  }

  
  (** * useful facts about init *)
  assert (T_next_M : memory_next_key m ≡ t_id).
  {
    subst.
    rewrite memory_next_key_override.
    reflexivity.
    apply mem_block_exists_exists_equiv.
    eexists.
    eq_to_equiv.
    eassumption.
  }
  assert (TX_neq : t_id <> x_id)
    by (apply memory_lookup_not_next_equiv in XID_M; congruence).
  assert (TY_neq : t_id <> y_id)
    by (eq_to_equiv; apply memory_lookup_not_next_equiv in YID_M; congruence).
  rename XY into T; assert (XY_neq : x_id <> y_id) by congruence; clear T.
  assert (INIT_equiv_M : memory_equiv_except init_m m y_id)
    by (intros k H; subst init_m;
        rewrite memory_lookup_memory_set_neq by congruence; reflexivity).
  assert (RP : Proper (equiv ==> equiv ==> iff) Rel).
  {
    subst; clear.
    intros m1 m2 E1 m3 m4 E2.
    split; intros H; inversion H; clear H; err_eq_to_equiv_hyp.
    -
      assert (Proper ((=) ==> iff)
                     (λ ma : mem_block, SHCOL_DSHCOL_mem_block_equiv y_m ma m2))
        by (intros m m' ME; rewrite ME; reflexivity).
      rewrite <-E2.
      rewrite <-H0.
      constructor.
      rewrite <-E1.
      assumption.
    -
      assert (Proper ((=) ==> iff)
                     (λ ma : mem_block, SHCOL_DSHCOL_mem_block_equiv y_m ma m1))
        by (intros m m' ME; rewrite ME; reflexivity).
      rewrite E2.
      rewrite <-H0.
      constructor.
      rewrite E1.
      assumption.
  }

  (*** INDUCTION **)
  generalize dependent m.
  induction n.
  -
    intros.

    (** * specialize FC *)
    remember (Nat.lt_0_succ 0) as o1 eqn:O1.
    specialize (FC init_m t_id (mkFinNat o1) y_id).
    full_autospecialize FC; try congruence.
    {
      intros k v L.
      subst init_m.
      destruct (Nat.eq_dec k y_id).
      -
        rewrite memory_lookup_memory_set_eq by congruence.
        eexists.
        split.
        reflexivity.
        congruence.
      -
        exists v.
        rewrite memory_lookup_memory_set_neq by congruence.
        intuition.
    }
    cbn in FC.
    inversion_clear FC as [T]; rename T into FC.
    specialize (FC x_m mem_empty).
    full_autospecialize FC.
    {
      repeat rewrite lookup_Pexp_incrPVar.
      unfold lookup_Pexp.
      rewrite X_ID.
      cbn.
      unfold memory_lookup_err.
      subst init_m.
      repeat rewrite memory_lookup_memory_set_neq by congruence.
      rewrite XID_M.
      reflexivity.
    }
    {
      cbn.
      unfold memory_lookup_err.

      rewrite memory_lookup_memory_set_eq by congruence.
      reflexivity.
    }

    
    cbn in FC.
    inversion FC as [M D | msg M D | mm dm R M D ]; clear FC.
    + (* DSH runs out of fuel *)
      exfalso; clear - D.
      symmetry in D.
      contradict D.
      apply is_Some_ne_None.
      apply evalDSHOperator_estimateFuel.
    + (* both MSH and DSH fail *)
      cbn.

      (* simplify mem_op to None *)
      unfold get_family_mem_op.
      rewrite <-O1.
      destruct mem_op; try some_none.

      (* simplify dop *)
      subst loop.
      cbn.
      rewrite T_ID.
      rewrite evalDSHOperator_estimateFuel_ge by lia.
      rewrite <-D.
      constructor.
    +
      (** * both MSH and DSH succeed *)
      cbn.

      (* simplify mem_op down to fold *)
      unfold get_family_mem_op.
      rewrite <-O1.
      destruct mem_op as [m'|] eqn:MM; 
        [some_inv; subst m' | some_none].
      cbn.

      (* simplify dop down to MemMap2*)
      subst loop.
      cbn.
      rewrite T_ID.
      rewrite evalDSHOperator_estimateFuel_ge by lia.
      rewrite <-D.
      rewrite evalDSHOperator_estimateFuel_ge
        by (cbn; pose proof estimateFuel_positive rr; lia).

      (* asserts to be used by MemMap2_merge_with_def *)
      assert (M_subs_DM : memory_subset_except y_id m dm).
      {
        clear - P D T_next_M INIT_M TY_neq.
        subst init_m.
        unfold memory_subset_except; intros.
        assert (KT_neq : k <> t_id)
          by (apply memory_lookup_not_next_equiv in H; congruence).
        clear T_next_M.
        inversion_clear P as [T S]; clear T.
        symmetry in D; eq_to_equiv.
        apply S with (y_i:=t_id) in D; [| reflexivity]; clear S.
        specialize (D k KT_neq).
        destruct (Nat.eq_dec k y_id).
        -
          eexists.
          rewrite <-D; clear D.
          rewrite memory_lookup_memory_set_neq by congruence.
          rewrite memory_lookup_memory_set_eq by congruence.
          split.
          reflexivity.
          congruence.
        -
          eexists.
          rewrite <-D; clear D.
          repeat rewrite memory_lookup_memory_set_neq by congruence.
          split.
          eassumption.
          reflexivity.
      }
      assert (T : exists t_dm,
                   lookup_Pexp (DSHnatVal 0 :: DSHPtrVal t_id o :: σ) dm (PVar 1) = inr t_dm);
        [| destruct T as [t_dm T_DM]].
      {
        cbn.
        intros.
        clear - D P.
        inversion_clear P as [S T]; clear T.
        symmetry in D; eq_to_equiv.
        apply S with (k:=t_id) in D; clear S.
        assert (mem_block_exists t_id (memory_set init_m t_id mem_empty))
          by (apply mem_block_exists_memory_set_eq; reflexivity).
        apply D in H; clear D.
        apply memory_is_set_is_Some in H.
        apply is_Some_def in H.
        destruct H.
        exists x.
        unfold memory_lookup_err.
        rewrite H.
        constructor.
        reflexivity.
      }
      assert (YID_DM : memory_lookup dm y_id =
                      Some (mem_union (mem_const_block o init) y_m)).
      {
        clear - D P INIT_M TY_neq.
        subst init_m.
        inversion_clear P as [T S]; clear T.
        symmetry in D; eq_to_equiv.
        apply S with (y_i:=t_id) in D; [| reflexivity]; clear S.
        unfold memory_equiv_except in D.
        rewrite <-D by congruence; clear D.
        rewrite memory_lookup_memory_set_neq by congruence.
        rewrite memory_lookup_memory_set_eq by congruence.
        reflexivity.
      }
      assert (Y_ID_in_dm : evalPexp (DSHnatVal 0 :: DSHPtrVal t_id 0 :: σ)
                                    (incrPVar 0 (incrPVar 0 y_p)) = inr y_id)
        by (repeat rewrite evalPexp_incrPVar; rewrite Y_ID; reflexivity).
      assert (Y_DM : lookup_Pexp (DSHnatVal 0 :: DSHPtrVal t_id o :: σ)
                               dm (incrPVar 0 (incrPVar 0 y_p)) =
                     inr (mem_union (mem_const_block o init) y_m)).
      {
        clear - YID_DM Y_ID.
        repeat rewrite lookup_Pexp_incrPVar.
        unfold lookup_Pexp, memory_lookup_err.
        rewrite Y_ID.
        cbn.
        rewrite YID_DM.
        reflexivity.
      }
      assert (Dot_compat_dm : MSH_DSH_BinCarrierA_compat dot
                                               (DSHnatVal 0 :: DSHPtrVal t_id o :: σ)
                                               df dm);
        [| clear DC].
      {
        eapply DC.
        reflexivity.
        assumption.
      }
      assert (T_DM_dense : ∀ k : nat, k < o → mem_in k t_dm).
      {
        intros.
        inversion R.
        assert (x = t_dm) by admit.
        rewrite H2 in H1.
        eapply SHCOL_DSHCOL_mem_block_equiv_keys_union.
        eassumption.
        right.
        clear - MM FMF FD H.
        specialize (FMF 0 o1); specialize (FD 0 o1).
        inversion_clear FMF as [T1 FILL T2]; clear T1 T2.
        apply FILL with (jc:=H) (m0:=x_m).
        assumption.
        unfold Same_set, Included in FD.
        destruct FD as [T FD]; clear T.
        apply FD.
        constructor.
      }
      assert (IY_dense : ∀ k : nat, k < o → mem_in k (mem_union (mem_const_block o init) y_m)).
      {
        intros.
        eapply mem_union_as_Union.
        reflexivity.
        left.
        apply mem_in_mem_lookup.
        erewrite mem_const_block_find.
        constructor.
        assumption.
      }
      
      repeat break_match; eq_to_equiv.
      * (* Map2 fails *)
        exfalso.
        enough (exists m', evalDSHOperator (DSHnatVal 0 :: DSHPtrVal t_id o :: σ)
            (DSHMemMap2 o (incrPVar 0 (incrPVar 0 y_p)) (PVar 1)
               (incrPVar 0 (incrPVar 0 y_p)) df) dm
            (estimateFuel
               (DSHMemMap2 o (incrPVar 0 (incrPVar 0 y_p)) (PVar 1) 
                  (incrPVar 0 (incrPVar 0 y_p)) df)) = Some (inr m'))
          by (destruct H; rewrite H in Heqo0; some_inv; inl_inr).
        eapply DSHMap2_succeeds; eassumption.
      * (* Map2 succeeds *)
        rename m0 into ma, Heqo0 into MA; clear Heqs0 s.
        constructor.
        subst Rel.

        destruct (lookup_Pexp σ (memory_remove ma t_id) y_p) eqn:Y_MA.
        {
          (* [y_p] disappeared in [ma] - not pure behavior *)
          exfalso.
          pose proof @MemMap2_DSH_pure
               (incrPVar 0 (incrPVar 0 y_p)) (PVar 1) (incrPVar 0 (incrPVar 0 y_p)) o df.
          eq_to_equiv.
          cbn in Y_MA.
          unfold memory_lookup_err, trywith in Y_MA.
          repeat break_match; try inl_inr; repeat inl_inr_inv.
          1: inversion Y_MA.
          eq_to_equiv.
          rewrite Y_ID in Heqo0.
          rewrite memory_lookup_memory_remove_neq in Heqo0 by congruence.
          clear - Heqo0 MA H YID_DM.
          inversion_clear H as [S T]; clear T.
          apply S with (k:=y_id) in MA; clear S.
          contradict Heqo0.
          apply is_Some_nequiv_None.
          repeat rewrite memory_is_set_is_Some in *.
          apply MA.
          unfold is_Some; break_match; try some_none.
          trivial.
        }
        constructor.

        rewrite MemMap2_merge_with_def_firstn with (init:=init) in MA; try eassumption.
        2: repeat rewrite evalPexp_incrPVar; assumption.
        some_inv; inl_inr_inv.
        eq_to_equiv.
        rewrite <-MA in Y_MA; clear MA ma.
        assert (m0 = mem_union (mem_merge_with_def dot init
                                 (mem_firstn o (mem_union (mem_const_block o init) y_m))
                                 (mem_firstn o t_dm))
                               (mem_union (mem_const_block o init) y_m)) by admit.
        rewrite H.
        clear Y_MA H m0.
        intros k.
        destruct (le_lt_dec o k).
        --
          constructor 1.
          admit. (* oob *)
          unfold mem_lookup, mem_union, mem_merge_with_def.
          repeat rewrite NP.F.map2_1bis by reflexivity.
          repeat rewrite mem_firstn_lookup_oob by assumption.
          rewrite mem_const_block_find_oob by assumption.
          reflexivity.
        --
          constructor 2.
          admit. (* dense *)
          rewrite firstn_mem_const_block_union.
          unfold mem_lookup, mem_union, mem_merge_with_def.
          unfold MMemoryOfCarrierA.mem_merge_with_def.
          repeat rewrite NP.F.map2_1bis by reflexivity.
          rewrite mem_const_block_find by assumption.
          rewrite mem_firstn_lookup by assumption.
          specialize (T_DM_dense k l).
          apply mem_in_mem_lookup, is_Some_def in T_DM_dense.
          destruct T_DM_dense as [k_tdm K_TDM].
          rewrite K_TDM.
          cbn.

          inversion R.
          eq_to_equiv; symmetry in H; memory_lookup_err_to_option.
          assert (T : x = t_dm) by admit; rewrite T in *; clear T x.
          assert (exists k_mm, mem_lookup k mm = Some k_mm)
            by admit. (* from FD and MM *)
          destruct H1 as [k_mm K_MM].
          break_match.
          all: eq_to_equiv; rewrite K_MM in Heqo0.
          all: try some_none; some_inv.
          rewrite <-Heqo0 in *; clear c Heqo0.
          
          specialize (H0 k).
          rewrite K_MM, K_TDM in H0.
          inversion H0; try some_none.
          some_inv.
          rewrite H2.
          reflexivity.
      * (* Map2 runs out of fuel *)
        clear - Heqo0.
        assert (is_Some (evalDSHOperator (DSHnatVal 0 :: DSHPtrVal t_id o :: σ)
            (DSHMemMap2 o (incrPVar 0 (incrPVar 0 y_p)) (PVar 1)
               (incrPVar 0 (incrPVar 0 y_p)) df) dm
            (estimateFuel
               (DSHMemMap2 o (incrPVar 0 (incrPVar 0 y_p)) (PVar 1)
                           (incrPVar 0 (incrPVar 0 y_p)) df))))
          by apply evalDSHOperator_estimateFuel.
        unfold is_Some in H.
        break_match; try some_none.
        contradiction.
  -
    rename n into n'; remember (S n') as n.
    
Admitted.
