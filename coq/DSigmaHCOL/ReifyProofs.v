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
Require Import Helix.DSigmaHCOL.TypeSig.
Require Import Helix.DSigmaHCOL.DSHCOLOnCarrierA.

(* When proving concrete functions we need to use some implementation defs from this packages *)
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

(* Type signatures of expressions as binary or unary functions with
optional index *)

Definition DSHIBinCarrierA_TypeSig :=
  TP.of_list [(0,DSHCType) ; (1,DSHCType) ; (2,DSHnat)].

Definition DSHUnCarrierA_TypeSig :=
  TP.of_list [(0,DSHCType)].

Definition DSHIUnCarrierA_TypeSig :=
  TP.of_list [(0,DSHCType) ; (1,DSHnat)].

Definition DSHBinCarrierA_TypeSig :=
  TP.of_list [(0,DSHCType) ; (1,DSHCType)].

(* Instances of this class ensure that given [AExpr]
   could be propely typed, and it's type signaure includes
   given [TypeSig].

   This could be viewed as a subtyping relation...
*)
Class AExprTypeSigIncludes (a:AExpr) (ts:TypeSig) : Prop
  := atypesigincl: exists dfs, (TypeSigAExpr a = Some dfs) /\ TypeSigIncluded dfs ts.

Class NExprTypeSigIncludes (n:NExpr) (ts:TypeSig) : Prop
  := ntypesigincl: exists dfs, (TypeSigNExpr n = Some dfs) /\ TypeSigIncluded dfs ts.

Class MExprTypeSigIncludes (m:MExpr) (ts:TypeSig) : Prop
  := mtypesigincl: exists dfs, (TypeSigMExpr m = Some dfs) /\ TypeSigIncluded dfs ts.

Class DSHIBinCarrierA (a:AExpr) : Prop :=
  DSHIBinCarrierA_atypesigincl :> AExprTypeSigIncludes a DSHIBinCarrierA_TypeSig.

Class DSHUnCarrierA (a:AExpr) : Prop :=
  DSHUnCarrierA_atypesigincl :> AExprTypeSigIncludes a DSHUnCarrierA_TypeSig.

Class DSHIUnCarrierA (a:AExpr) : Prop :=
  DSHIUnCarrierA_atypesigincl :> AExprTypeSigIncludes a DSHIUnCarrierA_TypeSig.

Class DSHBinCarrierA (a:AExpr) : Prop :=
  DSHBinCarrierA_atypesigincl :> AExprTypeSigIncludes a DSHBinCarrierA_TypeSig.

Lemma evalMExpr_is_OK
      {σ: evalContext}
      {m: MExpr}
      (mem : memory)
      (tm: TypeSig)
      (TS : TypeSigMExpr m = Some tm)
      (TC : typecheck_env 0 tm σ):
  is_OK (evalMexp mem σ m).
Proof.
  (*
  destruct m; simpl in *; [|trivial].
  some_inv.
  rewrite <- TS in TC. clear TS.
  unfold typecheck_env, typecheck_env_bool, TP.for_all in TC.
  eapply TP.for_all_iff with (k:=v) (e:=DSHMemBlock) in TC .
  -
    destruct (v <? 0) eqn:K; [inversion K|].
    inversion TC; clear TC.
    apply bool_decide_true in H0.
    rewrite Nat.sub_0_r in H0.
    unfold contextEnsureType in H0.
    break_match; [| trivial].
    inversion H0.
    inl_inr.
  -
    solve_proper.
  -
    apply TM.add_1.
    reflexivity.
   *)
Abort.

Lemma evalNExpr_is_OK
      {σ: evalContext}
      {n: NExpr}
      (tn: TypeSig)
      (TS : TypeSigNExpr n = Some tn)
      (TC : typecheck_env 0 tn σ):
  is_OK (evalNexp σ n).
Proof.
  dependent induction n; simpl in *.
  -
    unfold TypeSig_safe_add in TS.
    rewrite TP.F.empty_o in TS.
    some_inv.
    rewrite <- TS in TC. clear TS.
    unfold typecheck_env, typecheck_env_bool, TP.for_all in TC.
    eapply TP.for_all_iff with (k:=v) (e:=DSHnat) in TC .
    +
      destruct (v <? 0) eqn:K; [inversion K|].
      inversion TC; clear TC.
      apply bool_decide_true in H0.
      rewrite Nat.sub_0_r in H0.
      unfold contextEnsureType in H0.
      repeat break_match; try inl_inr.
      all: unfold context_lookup in Heqe.
      all: rewrite Heqo in Heqe.
      all: cbn in Heqe.
      all: inversion Heqe; subst.
      all: inversion H0.
    +
      solve_proper.
    +
      apply TM.add_1.
      reflexivity.
  -
    trivial.
  -
    unfold TypeSigUnion_error' in TS.
    simpl in TS.
    repeat break_match_hyp; try some_none.
    rename t into t1.
    rename t0 into t2.
    eapply TypeSigUnion_error_typecheck_env in TC; eauto.
    destruct TC as [T1 T2].
    assert(T1T: Some t1 = Some t1) by reflexivity.
    specialize (IHn1 t1 T1T T1).
    assert(T2T: Some t2 = Some t2) by reflexivity.
    specialize (IHn2 t2 T2T T2).
    repeat break_match; inl_inr.
  -
    (* TODO: copy-pasted goal. See if could be factorized into sub-lemma. *)
    unfold TypeSigUnion_error' in TS.
    simpl in TS.
    repeat break_match_hyp; try some_none.
    rename t into t1.
    rename t0 into t2.
    eapply TypeSigUnion_error_typecheck_env in TC; eauto.
    destruct TC as [T1 T2].
    assert(T1T: Some t1 = Some t1) by reflexivity.
    specialize (IHn1 t1 T1T T1).
    assert(T2T: Some t2 = Some t2) by reflexivity.
    specialize (IHn2 t2 T2T T2).
    repeat break_match; inl_inr.
  -
    (* TODO: copy-pasted goal. See if could be factorized into sub-lemma. *)
    unfold TypeSigUnion_error' in TS.
    simpl in TS.
    repeat break_match_hyp; try some_none.
    rename t into t1.
    rename t0 into t2.
    eapply TypeSigUnion_error_typecheck_env in TC; eauto.
    destruct TC as [T1 T2].
    assert(T1T: Some t1 = Some t1) by reflexivity.
    specialize (IHn1 t1 T1T T1).
    assert(T2T: Some t2 = Some t2) by reflexivity.
    specialize (IHn2 t2 T2T T2).
    repeat break_match; inl_inr.
  -
    (* TODO: copy-pasted goal. See if could be factorized into sub-lemma. *)
    unfold TypeSigUnion_error' in TS.
    simpl in TS.
    repeat break_match_hyp; try some_none.
    rename t into t1.
    rename t0 into t2.
    eapply TypeSigUnion_error_typecheck_env in TC; eauto.
    destruct TC as [T1 T2].
    assert(T1T: Some t1 = Some t1) by reflexivity.
    specialize (IHn1 t1 T1T T1).
    assert(T2T: Some t2 = Some t2) by reflexivity.
    specialize (IHn2 t2 T2T T2).
    repeat break_match; inl_inr.
  -
    (* TODO: copy-pasted goal. See if could be factorized into sub-lemma. *)
    unfold TypeSigUnion_error' in TS.
    simpl in TS.
    repeat break_match_hyp; try some_none.
    rename t into t1.
    rename t0 into t2.
    eapply TypeSigUnion_error_typecheck_env in TC; eauto.
    destruct TC as [T1 T2].
    assert(T1T: Some t1 = Some t1) by reflexivity.
    specialize (IHn1 t1 T1T T1).
    assert(T2T: Some t2 = Some t2) by reflexivity.
    specialize (IHn2 t2 T2T T2).
    repeat break_match; inl_inr.
  -
    (* TODO: copy-pasted goal. See if could be factorized into sub-lemma. *)
    unfold TypeSigUnion_error' in TS.
    simpl in TS.
    repeat break_match_hyp; try some_none.
    rename t into t1.
    rename t0 into t2.
    eapply TypeSigUnion_error_typecheck_env in TC; eauto.
    destruct TC as [T1 T2].
    assert(T1T: Some t1 = Some t1) by reflexivity.
    specialize (IHn1 t1 T1T T1).
    assert(T2T: Some t2 = Some t2) by reflexivity.
    specialize (IHn2 t2 T2T T2).
    repeat break_match; inl_inr.
  -
    (* TODO: copy-pasted goal. See if could be factorized into sub-lemma. *)
    unfold TypeSigUnion_error' in TS.
    simpl in TS.
    repeat break_match_hyp; try some_none.
    rename t into t1.
    rename t0 into t2.
    eapply TypeSigUnion_error_typecheck_env in TC; eauto.
    destruct TC as [T1 T2].
    assert(T1T: Some t1 = Some t1) by reflexivity.
    specialize (IHn1 t1 T1T T1).
    assert(T2T: Some t2 = Some t2) by reflexivity.
    specialize (IHn2 t2 T2T T2).
    repeat break_match; inl_inr.
Qed.

(*
  =AExpr= evaluation could return error only for technical reason:
  missing or incorrectly typed values in
  environent. It could not return an error based on values of
  parameters. The reason for this is that =AExpr= model =CarrierA=
  expressions which could not return error. An exampe in case BinOp
  function types =A -> A -> A= in MSCHOL and =A -> A -> option A= in
  DSCHOL. This "option" is to hold DSHCOL memory/environment errors.
 *)
Lemma evalAExpr_is_OK'
      {σ: evalContext}
      {e: AExpr}
      (mem : memory)
      (ts: TypeSig)
      (TS : TypeSigAExpr e = Some ts)
      (TC : typecheck_env 0 ts σ):
  is_OK (evalAexp mem σ e).
Proof.
  (*
  dependent induction e; simpl in *.
  -
    unfold TypeSig_safe_add in TS.
    rewrite TP.F.empty_o in TS.
    some_inv.
    rewrite <- TS in TC. clear TS.
    unfold typecheck_env, typecheck_env_bool, TP.for_all in TC.
    eapply TP.for_all_iff with (k:=v) (e:=DSHCType) in TC .
    +
      destruct (v <? 0) eqn:K; [inversion K|].
      inversion TC; clear TC.
      apply bool_decide_true in H0.
      rewrite Nat.sub_0_r in H0.
      unfold contextEnsureType in H0.
      repeat break_match; try inl_inr.
      all: unfold context_lookup in Heqe.
      all: rewrite Heqo in Heqe.
      all: cbn in Heqe.
      all: inversion Heqe; subst.
      all: inversion H0.
    +
      solve_proper.
    +
      apply TM.add_1.
      reflexivity.
  -
    trivial.
  -
    unfold TypeSigUnion_error' in TS.
    simpl in TS.
    repeat break_match_hyp; try some_none.
    rename t into tm.
    rename t0 into tn.
    eapply TypeSigUnion_error_typecheck_env in TC; eauto.
    destruct TC as [TM TN].
    eq_to_equiv_hyp.
    break_match.
    +
      pose proof evalMExpr_is_OK tm Heqo TM.
      rewrite Heqe in H.
      inl_inr.
    +
      break_match.
      *
        pose proof evalNExpr_is_OK tn Heqo0 TN.
        rewrite Heqe0 in H.
        inl_inr.
      *
        break_match; inl_inr.
  -
    specialize (IHe ts TS TC).
    break_match; inl_inr.
  -
    unfold TypeSigUnion_error' in TS.
    simpl in TS.
    repeat break_match_hyp; try some_none.
    rename t into t1.
    rename t0 into t2.
    eapply TypeSigUnion_error_typecheck_env in TC; eauto.
    destruct TC as [T1 T2].
    assert(T1T: Some t1 = Some t1) by reflexivity.
    specialize (IHe1 t1 T1T T1).
    assert(T2T: Some t2 = Some t2) by reflexivity.
    specialize (IHe2 t2 T2T T2).
    repeat break_match; inl_inr.
  -
    (* TODO: copy-paste from previous bullet. see if it could be factored out as separate lemma or Ltac script *)
    unfold TypeSigUnion_error' in TS.
    simpl in TS.
    repeat break_match_hyp; try some_none.
    rename t into t1.
    rename t0 into t2.
    eapply TypeSigUnion_error_typecheck_env in TC; eauto.
    destruct TC as [T1 T2].
    assert(T1T: Some t1 = Some t1) by reflexivity.
    specialize (IHe1 t1 T1T T1).
    assert(T2T: Some t2 = Some t2) by reflexivity.
    specialize (IHe2 t2 T2T T2).
    repeat break_match; inl_inr.
  -
    (* TODO: copy-paste from previous bullet. see if it could be factored out as separate lemma or Ltac script *)
    unfold TypeSigUnion_error' in TS.
    simpl in TS.
    repeat break_match_hyp; try some_none.
    rename t into t1.
    rename t0 into t2.
    eapply TypeSigUnion_error_typecheck_env in TC; eauto.
    destruct TC as [T1 T2].
    assert(T1T: Some t1 = Some t1) by reflexivity.
    specialize (IHe1 t1 T1T T1).
    assert(T2T: Some t2 = Some t2) by reflexivity.
    specialize (IHe2 t2 T2T T2).
    repeat break_match; inl_inr.
  -
    (* TODO: copy-paste from previous bullet. see if it could be factored out as separate lemma or Ltac script *)
    unfold TypeSigUnion_error' in TS.
    simpl in TS.
    repeat break_match_hyp; try some_none.
    rename t into t1.
    rename t0 into t2.
    eapply TypeSigUnion_error_typecheck_env in TC; eauto.
    destruct TC as [T1 T2].
    assert(T1T: Some t1 = Some t1) by reflexivity.
    specialize (IHe1 t1 T1T T1).
    assert(T2T: Some t2 = Some t2) by reflexivity.
    specialize (IHe2 t2 T2T T2).
    repeat break_match; inl_inr.
  -
    (* TODO: copy-paste from previous bullet. see if it could be factored out as separate lemma or Ltac script *)
    unfold TypeSigUnion_error' in TS.
    simpl in TS.
    repeat break_match_hyp; try some_none.
    rename t into t1.
    rename t0 into t2.
    eapply TypeSigUnion_error_typecheck_env in TC; eauto.
    destruct TC as [T1 T2].
    assert(T1T: Some t1 = Some t1) by reflexivity.
    specialize (IHe1 t1 T1T T1).
    assert(T2T: Some t2 = Some t2) by reflexivity.
    specialize (IHe2 t2 T2T T2).
    repeat break_match; inl_inr.
  -
    (* TODO: copy-paste from previous bullet. see if it could be factored out as separate lemma or Ltac script *)
    unfold TypeSigUnion_error' in TS.
    simpl in TS.
    repeat break_match_hyp; try some_none.
    rename t into t1.
    rename t0 into t2.
    eapply TypeSigUnion_error_typecheck_env in TC; eauto.
    destruct TC as [T1 T2].
    assert(T1T: Some t1 = Some t1) by reflexivity.
    specialize (IHe1 t1 T1T T1).
    assert(T2T: Some t2 = Some t2) by reflexivity.
    specialize (IHe2 t2 T2T T2).
    repeat break_match; inl_inr.
*)
Abort.

Lemma evalAExpr_is_OK
      {σ : evalContext}
      {a : AExpr}
      (mem : memory)
      `{TSI : AExprTypeSigIncludes a ts}
      (TC : typecheck_env 0 ts σ) :
  is_OK (evalAexp mem σ a).
Proof.
  (*
  inversion TSI; clear TSI.
  rename x into ats; destruct H as [ATS TSI].
  eapply typecheck_env_TypeSigIncluded in TC.
  eapply evalAExpr_is_OK'.
  all: eassumption.
   *)
Abort.

Global Instance TypeSigCompat_Symmetric :
  Symmetric TypeSigCompat.
Proof.
  unfold Symmetric.
  intros.
  unfold TypeSigCompat, findTypeSigConflicts in *.
  rewrite find_Empty in *.
  intro k; specialize (H k).
  rewrite TP.F.map2_1bis in * by reflexivity.
  repeat break_match; try congruence.
  exfalso; clear - Heqb Heqb0.
  unfold bool_decide in *.
  repeat break_if; try congruence.
  clear - e n.
  cbv in e, n.
  congruence.
Qed.

Lemma TypeSigUnion_error_sym (ts1 ts2 : TypeSig) :
  TypeSigUnion_error ts1 ts2 = TypeSigUnion_error ts2 ts1.
Proof.
  unfold TypeSigUnion_error.
  repeat break_if; try some_none.
  -
    clear - t t0; rename t into Compat12, t0 into Compat21; constructor.

    assert (H12 : ∀ (k : TM.key) (e : DSHType),
               TM.MapsTo k e ts1 → TM.In (elt:=DSHType) k ts2 → TM.MapsTo k e ts2)
     by (eapply TypeSigCompat_at; eassumption).
    assert (H21 : ∀ (k : TM.key) (e : DSHType),
               TM.MapsTo k e ts2 → TM.In (elt:=DSHType) k ts1 → TM.MapsTo k e ts1)
     by (eapply TypeSigCompat_at; eassumption).
    clear Compat12 Compat21.
    unfold TypeSig_Equiv, TypeSigUnion.
    intros; specialize (H12 k); specialize (H21 k).
    destruct TM.find eqn:F12 at 1; destruct TM.find eqn:F21 at 1.
    all: try constructor.
    2,3: exfalso.
    +
      cbv.
      rewrite <-TP.F.find_mapsto_iff, ->TP.update_mapsto_iff in *.
      destruct F12 as [F12 | [F12 F12']],
               F21 as [F21 | [F21 F21']].
      *
        apply H12 in F21.
        eapply TP.F.MapsTo_fun; eassumption.
        eapply TypeSig.MapsTo_In; eassumption.
      *
        eapply TP.F.MapsTo_fun; eassumption.
      *
        eapply TP.F.MapsTo_fun; eassumption.
      *
        contradict F12'.
        eapply TypeSig.MapsTo_In; eassumption.
    +
      rewrite <-TP.F.not_find_in_iff in F21.
      contradict F21.
      apply TP.update_in_iff.
      rewrite <-TP.F.find_mapsto_iff, ->TP.update_mapsto_iff in *.
      destruct F12 as [F12 | [F12 F12']].
      left; eapply TypeSig.MapsTo_In; eassumption.
      right; eapply TypeSig.MapsTo_In; eassumption.
    +
      rewrite <-TP.F.not_find_in_iff in F12.
      contradict F12.
      apply TP.update_in_iff.
      rewrite <-TP.F.find_mapsto_iff, ->TP.update_mapsto_iff in *.
      destruct F21 as [F21 | [F21 F21']].
      left; eapply TypeSig.MapsTo_In; eassumption.
      right; eapply TypeSig.MapsTo_In; eassumption.
  -
    clear - t n.
    contradict n.
    symmetry.
    assumption.
  -
    clear - t n.
    contradict n.
    symmetry.
    assumption.
Qed.

Lemma empty_TypeSigCompat (t : TypeSig) :
  TypeSigCompat (TM.empty DSHType) t.
Proof.
  unfold TypeSigCompat, findTypeSigConflicts.
  apply find_Empty; intro.
  rewrite TP.F.map2_1bis by reflexivity.
  reflexivity.
Qed.

Lemma TypeSig_update_empty (t : TypeSig) :
  TP.update (TM.empty DSHType) t = t.
Proof.
    unfold equiv, TypeSig_Equiv; intros.
    destruct TM.find eqn:H1 at 1, TM.find eqn:H2 at 1.
    all: try rewrite <-TP.F.find_mapsto_iff in *.
    all: try rewrite <-TP.F.not_find_in_iff in *.
    1,2: apply TP.update_mapsto_iff in H1.
    1,2: destruct H1 as [H1 | [C _]]; [| inversion C].
    4: reflexivity.
    +
      pose proof TP.F.MapsTo_fun H1 H2.
      subst; reflexivity.
    +
      apply TypeSig.MapsTo_In in H1.
      congruence.
    +
      contradict H1.
      apply TP.update_in_iff.
      right.
      eapply TypeSig.MapsTo_In; eassumption.
Qed.

Lemma eq_equiv_err_nat (n1 n2 : err nat) :
  n1 = n2 <-> n1 ≡ n2.
Proof.
  split; intros.
  -
    inversion H; inversion H0.
    reflexivity.
    apply String.eqb_eq in H4; congruence.
  -
    subst; reflexivity.
Qed.

Lemma eq_equiv_option_nat (n1 n2 : option nat) :
  n1 = n2 <-> n1 ≡ n2.
Proof.
  split; intros.
  inversion H; congruence.
  subst; reflexivity.
Qed.

Lemma evalNExpr_context_equiv_at_TypeSig
      (n : NExpr)
      {σ0 σ1 : evalContext}
      {ts : TypeSig}
      `{TSI : NExprTypeSigIncludes n ts}
      (E : context_equiv_at_TypeSig ts σ0 σ1) :
  evalNexp σ0 n = evalNexp σ1 n.
Proof.
  inversion TSI; subst; clear TSI.
  destruct H as [Heqx TSI].

  copy_apply context_equiv_at_TypeSig_both_typcheck E;
    destruct H as [TC0 TC1].

  destruct_err_equiv.
  -
    admit.
  -
    eq_to_equiv_hyp.
    (* eapply evalNExpr_is_OK in TC0. *)
    admit.
  -
    eq_to_equiv_hyp.
    (* eapply evalNExpr_is_OK in TC1. *)
    admit.
  -
    cbv.

    dependent induction n; cbn in *.
    
    (* first "base case" *)
    repeat break_match; try inl_inr.
    repeat some_inv; repeat inl_inr_inv; subst; rewrite <-Heqx in *; clear Heqx.
    assert (T : TM.MapsTo v DSHnat ts).
    {
      eapply TypeSigIncluded_at.
      eassumption.
      apply TM.add_1.
      reflexivity.
    }
    unfold context_equiv_at_TypeSig in E.
    specialize (E v DSHnat T).
    destruct E as [E1 [E2 E3]].
    unfold context_lookup in *.

    apply trywith_inr_any_exc with (e':="") in Heqe.
    apply trywith_inr_any_exc with (e':="") in Heqe0.
    unfold trywith in *.
    repeat break_match;
      inversion Heqe; inversion Heqe0; clear Heqe Heqe0.
    subst.
    inversion E3; subst.
    inversion H1; subst.
    cbv in H2; assumption.
 
    (* second "base case" *)
    congruence.

    (* all "inductive cases" are the same *)
    all: unfold TypeSigUnion_error in Heqx.
    all: repeat break_match; try inl_inr; try some_none.
    all: rename n5 into n10, n6 into n20,
                n  into n11, n4 into n21.
    all: rename t into tn1, t0 into tn2.
    all: repeat some_inv; subst; rewrite <-Heqx in *.
    all: copy_apply TypeSigIncluded_TypeSigUnion_left TSI;
      [| assumption]; rename H into I1.
    all: copy_apply TypeSigIncluded_TypeSigUnion_right TSI;
      rename H into I2.
    all: assert (n10 = n11)
      by (eapply IHn1; try apply I1; try eassumption; reflexivity).
    all: assert (n20 = n21)
      by (eapply IHn2; try apply I2; try eassumption; reflexivity).
    all: congruence.
Admitted.

Lemma evalMExpr_context_equiv_at_TypeSig
      (m : MExpr)
      {σ0 σ1 : evalContext}
      (mem : memory)
      `{TSI : MExprTypeSigIncludes m ts}
      (E : context_equiv_at_TypeSig ts σ0 σ1):
  evalMexp mem σ0 m = evalMexp mem σ1 m.
Proof.
  inversion TSI; clear TSI.
  rename x into mts; destruct H as [MTS TSI].
  destruct m; cbn in *; [| reflexivity].
  destruct p; cbn in *.
  some_inv.
  assert (T : TM.MapsTo v DSHPtr ts).
  {
    eapply TypeSigIncluded_at.
    eassumption.
    rewrite <-MTS.
    apply TM.add_1.
    reflexivity.
  }
  specialize (E v DSHPtr T).
  destruct E as [E1 [E2 H]].
  unfold context_lookup in H.
  destruct (List.nth_error σ0 v) eqn:H0; destruct (List.nth_error σ1 v) eqn:H1;
    inversion H; try reflexivity.
  subst.
  destruct d0, d; inversion H4; try reflexivity.
  subst.
  rewrite H5.
  reflexivity.
Qed.

Lemma evalAExpr_context_equiv_at_TypeSig
      (a : AExpr)
      {σ0 σ1 : evalContext}
      (mem : memory)
      `{TSI : AExprTypeSigIncludes a ts}
      (E : context_equiv_at_TypeSig ts σ0 σ1):
  evalAexp mem σ0 a = evalAexp mem σ1 a.
Proof.
  inversion TSI; subst; clear TSI.
  rename x into ats; destruct H as [ATS TSI].

  copy_apply context_equiv_at_TypeSig_both_typcheck E;
    destruct H as [TC0 TC1].

  destruct_err_equiv.
  -
    admit.
  -
    (*
    contradict Hb.
    apply is_Some_ne_None.
    eapply evalAExpr_is_OK'.
    eassumption.
    eapply typecheck_env_TypeSigIncluded; eassumption.
     *)
    admit.
  -
    (*
    contradict Ha.
    apply is_Some_ne_None.
    eapply evalAExpr_is_OK'.
    eassumption.
    eapply typecheck_env_TypeSigIncluded; eassumption.
     *)
    admit.
  -
    dependent induction a; cbn in *.
    
    (* first "base case" *)
    (*
    repeat break_match; try some_none.
    repeat some_inv; subst.
    enough (List.nth_error σ0 v = List.nth_error σ1 v)
      by (rewrite Heqo, Heqo0 in H;
          some_inv; inversion H; assumption).
    clear - E ATS TSI.
    assert (T : TM.MapsTo v DSHCType ts).
    {
      eapply TypeSigIncluded_at.
      eassumption.
      rewrite <-ATS.
      apply TM.add_1.
      reflexivity.
    }
    specialize (E v DSHCType T).
    destruct E as [E1 [E2 H]].
    assumption.
     *)
    admit.

    (* second "base case" *)
    (* repeat some_inv; subst; reflexivity. *)
    admit.

    (* third "base case" *)
    (*
    destruct TypeSigMExpr eqn:MTS in ATS; [rename t into mts | some_none].
    destruct TypeSigNExpr eqn:NTS in ATS; [rename t into nts | some_none].
    unfold TypeSigUnion_error in ATS; break_if; try some_none.
    clear Heqd.
    some_inv; rewrite <-ATS in *.
    assert (MTSI : MExprTypeSigIncludes m ts).
    {
      exists mts. split.
      eq_to_equiv_hyp; assumption.
      eapply TypeSigIncluded_TypeSigUnion_left; eassumption.
    }
    assert (NTSI : NExprTypeSigIncludes n ts).
    {
      exists nts. split.
      eq_to_equiv_hyp; assumption.
      eapply TypeSigIncluded_TypeSigUnion_right; eassumption.
    }
    eapply evalMExpr_context_equiv_at_TypeSig in MTSI; [| eassumption].
    eapply evalNExpr_context_equiv_at_TypeSig in NTSI; [| eassumption].
    rewrite eq_equiv_option_nat in NTSI; rewrite NTSI in *.
    destruct evalMexp eqn:M0 in Ha; [| some_none].
    destruct evalMexp eqn:M1 in Hb; [| some_none].
    rewrite M0, M1 in MTSI; some_inv.
    break_match; [| some_none].
    repeat break_match; repeat some_inv; subst.
    1: enough (Some c = Some c0) by (some_inv; assumption).
    2: enough (None = Some c0) by some_none.
    3: enough (None = Some c) by some_none.
    1-3: rewrite <-Heqo0, <-Heqo1, MTSI; reflexivity.
    reflexivity.
     *)
    admit.

    (* inductive 1 *)
    repeat break_match;
      try some_none; try inl_inr;
      repeat some_inv; repeat inl_inr_inv.
    enough (CarrierAe c1 c2) by (rewrite H; reflexivity).
    symmetry.
    eapply IHa; eassumption.

    (* rest inductive *)
    all: repeat break_match;
           try some_none; try inl_inr;
           repeat some_inv; repeat inl_inr_inv.
    all: assert (TypeSigIncluded t ts) by
        (unfold TypeSigUnion_error in ATS; break_if; [| some_none];
         some_inv; rewrite <-ATS in *;
         eapply TypeSigIncluded_TypeSigUnion_left; eassumption).
    all: assert (TypeSigIncluded t0 ts) by
        (unfold TypeSigUnion_error in ATS; break_if; [| some_none];
         some_inv; rewrite <-ATS in *;
         eapply TypeSigIncluded_TypeSigUnion_right; eassumption).
    all: assert (CarrierAe c3 c1)
      by (eapply IHa1; try reflexivity; try eassumption).
    all: assert (CarrierAe c4 c2)
      by (eapply IHa2; try reflexivity; try eassumption).
    all: rewrite H3, H4; reflexivity.
Abort.
 
Lemma evalNExpr_context_equiv_at_exact_TypeSig
      (σ0 σ1 : evalContext)
      (n : NExpr)
      {ts : TypeSig}
      `{TS : TypeSigNExpr n = Some ts}
      (E : context_equiv_at_TypeSig ts σ0 σ1) :
  evalNexp σ0 n = evalNexp σ1 n.
Proof.
  eapply evalNExpr_context_equiv_at_TypeSig; [| eassumption].
  exists ts.
  split; try assumption.
  apply TypeSigIncluded_reflexive.
Qed.

Lemma evalMExpr_context_equiv_at_exact_TypeSig
      (m : MExpr)
      {σ0 σ1 : evalContext}
      (mem : memory)
      `{TS : TypeSigMExpr m = Some ts}
      (E : context_equiv_at_TypeSig ts σ0 σ1):
  evalMexp mem σ0 m = evalMexp mem σ1 m.
Proof.
  eapply evalMExpr_context_equiv_at_TypeSig; [| eassumption].
  exists ts.
  split; try assumption.
  apply TypeSigIncluded_reflexive.
Qed.

Lemma evalAExpr_context_equiv_at_exact_TypeSig
      (a : AExpr)
      {σ0 σ1 : evalContext}
      (mem : memory)
      `{TS : TypeSigAExpr a = Some ts}
      (E : context_equiv_at_TypeSig ts σ0 σ1):
  evalAexp mem σ0 a = evalAexp mem σ1 a.
Proof.
  (*
  eapply evalAExpr_context_equiv_at_TypeSig; [| eassumption].
  exists ts.
  split; try assumption.
  apply TypeSigIncluded_reflexive.
   *)
Abort.

(* Shows relations of cells before ([b]) and after ([a]) evaluating
   DSHCOL operator and a result of evaluating [mem_op] as [d] *)
Inductive MemOpDelta (b a d: option CarrierA) : Prop :=
| MemPreserved: is_None d -> b = a -> MemOpDelta b a d (* preserving memory state *)
| MemExpected: is_Some d -> a = d -> MemOpDelta b a d (* expected results *).

Global Instance MemOpDelta_proper:
  Proper ((=) ==> (=) ==> (=) ==> (iff)) MemOpDelta.
Proof.
  intros b b' Eb a a' Ea d d' Ed.
  split; intros H.
  -
    destruct H.
    +
      apply is_None_def in H.
      subst d.
      inversion_clear Ed.
      apply MemPreserved.
      *
        some_none.
      *
        rewrite <- Eb, <- Ea.
        assumption.
    +
      norm_some_none.
      subst d.
      rewrite Ea in H0. clear Ea a.
      dep_destruct d'; try some_none.
      apply MemExpected.
      *
        some_none.
      *
        rewrite H0.
        assumption.
  -
    destruct H.
    +
      apply is_None_def in H.
      subst d'.
      inversion_clear Ed.
      apply MemPreserved.
      *
        some_none.
      *
        rewrite Eb, Ea.
        assumption.
    +
      norm_some_none.
      subst d'.
      rewrite <-Ea in H0. clear Ea a'.
      dep_destruct d; try some_none.
      apply MemExpected.
      *
        some_none.
      *
        rewrite H0.
        symmetry.
        assumption.
Qed.

(* Shows relations of memory blocks before ([mb]) and after ([ma]) evaluating
   DSHCOL operator and a result of evaluating [mem_op] as [md] *)
Definition SHCOL_DSHCOL_mem_block_equiv (mb ma md: mem_block) : Prop :=
  forall i,
    MemOpDelta
      (mem_lookup i mb)
      (mem_lookup i ma)
      (mem_lookup i md).

Require Import CoLoR.Util.Relation.RelUtil.

(*
TODO: move
 *)
Section opt_p.

  Variables (A : Type) (P : A -> Prop).

  (* lifting Predicate to option. error is not allowed *)
  Inductive opt_p : (option A) -> Prop :=
  | opt_p_intro : forall x, P x -> opt_p (Some x).

  (* lifting Predicate to option. errors is allowed *)
  Inductive opt_p_n : (option A) -> Prop :=
  | opt_p_None_intro: opt_p_n None
  | opt_p_Some_intro : forall x, P x -> opt_p_n (Some x).

  Global Instance opt_p_proper
         `{Ae: Equiv A}
         {Pp: Proper ((=) ==> (iff)) P}
    :
      Proper ((=) ==> (iff)) opt_p.
  Proof.
    intros a b E.
    split.
    -
      intros H.
      destruct a,b; try some_none.
      inversion H.
      subst x.
      constructor.
      some_inv.
      rewrite <- E.
      assumption.
      inversion H.
    -
      intros H.
      destruct a,b; try some_none.
      inversion H.
      subst x.
      constructor.
      some_inv.
      rewrite E.
      assumption.
      inversion H.
  Qed.

End opt_p.
Arguments opt_p {A} P.
Arguments opt_p_n {A} P.

Section err_p.

  Variables (A : Type) (P : A -> Prop).

  (* lifting Predicate to option. None is not allowed *)
  Inductive err_p : (err A) -> Prop :=
  | err_p_intro : forall x, P x -> err_p (inr x).

  (* lifting Predicate to option. None is allowed *)
  Inductive err_p_n : (err A) -> Prop :=
  | err_p_inl_intro: forall x, err_p_n (inl x)
  | err_p_inr_intro : forall x, P x -> err_p_n (inr x).

  Global Instance err_p_proper
         `{Ae: Equiv A}
         {Pp: Proper ((=) ==> (iff)) P}
    :
      Proper ((=) ==> (iff)) err_p.
  Proof.
    intros a b E.
    split; intro.
    -
      destruct a,b; try inl_inr; inversion H.
      inl_inr_inv.
      subst.
      constructor.
      rewrite <-E.
      assumption.
    -
      destruct a,b; try inl_inr; inversion H.
      inl_inr_inv.
      subst.
      constructor.
      rewrite E.
      assumption.
  Qed.

End err_p.
Arguments err_p {A} P.
Arguments err_p_n {A} P.

(* Extension to [option _] of a heterogenous relation on [A] [B]
TODO: move
 *)
Section hopt.

  Variables (A B : Type) (R: A -> B -> Prop).

  (** Reflexive on [None]. *)
  Inductive hopt_r : (option A) -> (option B) -> Prop :=
  | hopt_r_None : hopt_r None None
  | hopt_r_Some : forall a b, R a b -> hopt_r (Some a) (Some b).

  (** Non-Reflexive on [None]. *)
  Inductive hopt : (option A) -> (option B) -> Prop :=
  | hopt_Some : forall a b, R a b -> hopt (Some a) (Some b).

  (** implication-like. *)
  Inductive hopt_i : (option A) -> (option B) -> Prop :=
  | hopt_i_None_None : hopt_i None None
  | hopt_i_None_Some : forall a, hopt_i None (Some a)
  | hopt_i_Some : forall a b, R a b -> hopt_i (Some a) (Some b).

End hopt.
Arguments hopt {A B} R.
Arguments hopt_r {A B} R.
Arguments hopt_i {A B} R.

Section herr.

  Variables (A B : Type) (R: A -> B -> Prop).

  (** Complete on [inl]. *)
  Inductive herr_c : (err A) -> (err B) -> Prop :=
  | herr_c_inl : forall e1 e2, herr_c (inl e1) (inl e2)
  | herr_c_inr : forall a b, R a b -> herr_c (inr a) (inr b).

  (** Empty on [inl]. *)
  Inductive herr : (err A) -> (err B) -> Prop :=
  | herr_inr : forall a b, R a b -> herr (inr a) (inr b).

  (** implication-like. *)
  Inductive herr_i : (err A) -> (err B) -> Prop :=
  | herr_i_inl_inl : forall e1 e2, herr_i (inl e1) (inl e2)
  | herr_i_inl_inr : forall e a, herr_i (inl e) (inr a)
  | herr_i_inr_inr : forall a b, R a b -> herr_i (inr a) (inr b).

End herr.
Arguments herr {A B} R.
Arguments herr_c {A B} R.
Arguments herr_i {A B} R.

Section h_opt_err.

  Variables (A B : Type) (R: A -> B -> Prop).

  (** Complete on [inl]. *)
  Inductive h_opt_err_c : (option A) -> (err B) -> Prop :=
  | h_opt_err_c_None : forall e, h_opt_err_c None (inl e)
  | h_opt_err_c_Some : forall a b, R a b -> h_opt_err_c (Some a) (inr b).

  (** Empty on [inl]. *)
  Inductive h_opt_err : (option A) -> (err B) -> Prop :=
  | h_opt_err_Some : forall a b, R a b -> h_opt_err (Some a) (inr b).

  (** implication-like. *)
  Inductive h_opt_err_i : (option A) -> (err B) -> Prop :=
  | herr_i_None_inl : forall e, h_opt_err_i None (inl e)
  | herr_i_None_inr : forall a, h_opt_err_i None (inr a)
  | herr_i_Some_inr : forall a b, R a b -> h_opt_err_i (Some a) (inr b).

End h_opt_err.
Arguments h_opt_err {A B} R.
Arguments h_opt_err_c {A B} R.
Arguments h_opt_err_i {A B} R.

Definition lookup_Pexp (σ:evalContext) (m:memory) (p:PExpr) :=
  a <- evalPexp σ p ;;
    memory_lookup_err "block_id not found" m a.

Definition valid_Pexp (σ:evalContext) (m:memory) (p:PExpr) :=
  err_p (fun k => mem_block_exists k m) (evalPexp σ p).

(* Simplified version. Uses [equiv] only for memory. Could be proven more generally *)
Global Instance valid_Pexp_proper:
  Proper ((eq) ==> (=) ==> (eq) ==> iff) (valid_Pexp).
Proof.
  intros s0 s1 Es m0 m1 Em p0 p1 Ep.
  subst.
  split; intros H.
  -
    unfold valid_Pexp in *.
    destruct (evalPexp s1 p1).
    +
      inversion H.
    +
      inversion H.
      subst.
      constructor.
      rewrite <- Em.
      apply H1.
  -
    unfold valid_Pexp in *.
    destruct (evalPexp s1 p1).
    +
      inversion H.
    +
      inversion H.
      subst.
      constructor.
      rewrite Em.
      apply H1.
Qed.

Lemma valid_Pexp_incrPVar
      (p : PExpr)
      (m : memory)
      (σ : evalContext)
      (foo: DSHVal)
  :
    valid_Pexp σ m p  -> valid_Pexp (foo :: σ) m (incrPVar 0 p).
Proof.
  unfold valid_Pexp.
  intros H.
  inversion H. clear H.
  rewrite <- evalPexp_incrPVar with (foo:=foo) in H0.
  rewrite <- H0.
  constructor.
  apply H1.
Qed.

(*
   - [evalPexp σ p] must not to fail
   - [memory_lookup] must succeed
 *)
Definition blocks_equiv_at_Pexp (σ0 σ1:evalContext) (p:PExpr): rel (memory)
  := fun m0 m1 =>
       herr (fun a b => (opt equiv (memory_lookup m0 a) (memory_lookup m1 b)))
           (evalPexp σ0 p) (evalPexp σ1 p).

(* This relations represents consistent memory/envirnment combinations. That means all pointer variables should resolve to existing memory blocks *)
Inductive EnvMemoryConsistent: evalContext -> memory -> Prop :=
| EmptyEnvConsistent: forall m, EnvMemoryConsistent [] m
| DSHPtrValConsistent: forall σ m a,
    mem_block_exists a m ->
    EnvMemoryConsistent σ m -> EnvMemoryConsistent (DSHPtrVal a :: σ) m
(* the remaining case does not depend on memory and just recurse over environment *)
| DSHnatValConsistent : forall σ m n, EnvMemoryConsistent σ m -> EnvMemoryConsistent (DSHnatVal n :: σ) m
| DSHCTypeValConsistent: forall σ m a, EnvMemoryConsistent σ m -> EnvMemoryConsistent (DSHCTypeVal a :: σ) m
| DSHMemValConsistent: forall σ b m, EnvMemoryConsistent σ m -> EnvMemoryConsistent (DSHMemVal b :: σ) m.

(* TODO: move *)
(* Two memory locations equivalent on all addresses except one *)
Definition memory_equiv_except (m m': memory) (e:mem_block_id)
  := forall k, k≢e -> memory_lookup m k = memory_lookup m' k.

Lemma memory_equiv_except_memory_set {m m' b k}:
  m' ≡ memory_set m k b -> memory_equiv_except m m' k.
Proof.
  intros H.
  subst.
  intros k' kc.
  unfold memory_set.
  unfold memory_lookup.
  rewrite NP.F.add_neq_o.
  reflexivity.
  auto.
Qed.

Lemma memory_equiv_except_trans {m m' m'' k}:
  memory_equiv_except m m' k ->
  memory_equiv_except m' m'' k ->
  memory_equiv_except m m'' k.
Proof.
  intros H H0.
  intros k' kc.
  specialize (H0 k' kc).
  rewrite <- H0. clear H0.
  apply H.
  apply kc.
Qed.

(* DSH expression as a "pure" function by enforcing the memory
   invariants guaranteeing that it depends only input memory block and
   modifies only output memory block.

   It is assumed that the memory and envirnment are consistent and
   [PExp] successfuly resolve to valid memory locations for [x_p] and
   [y_p] which must be allocated.

 *)
Class DSH_pure
      (d: DSHOperator)
      (dsig: TypeSig)
      (x_p y_p: PExpr)
  := {

      (* does not free or allocate any memory *)
      mem_stable: forall σ m m' fuel,
        evalDSHOperator σ d m fuel = inr m' ->
        forall k, mem_block_exists k m <-> mem_block_exists k m';

      (* depends only [x_p], which must be valid in [σ], in all
         consistent memory configurations *)
      mem_read_safe: forall σ0 σ1 m0 m1 fuel,
          (*
            EnvMemoryConsistent σ0 m0 ->
            EnvMemoryConsistent σ1 m1 ->
           *)
          context_equiv_at_TypeSig dsig σ0 σ1 ->
          blocks_equiv_at_Pexp σ0 σ1 x_p m0 m1 ->
          blocks_equiv_at_Pexp σ0 σ1 y_p m0 m1 ->
          herr_c
            (blocks_equiv_at_Pexp σ0 σ1 y_p)
            (evalDSHOperator σ0 d m0 fuel)
            (evalDSHOperator σ1 d m1 fuel);

      (* modifies only [y_p], which must be valid in [σ] *)
      mem_write_safe: forall σ m m' fuel,
          evalDSHOperator σ d m fuel = inr m' ->
          (forall y_i , evalPexp σ y_p = inr y_i ->
                   memory_equiv_except m m' y_i)
    }.


(* Given MSHCOL and DSHCOL operators are quivalent, if wrt [x_i] and
  input memory block addres and [y_i] as output.

  It is assumed that we know what memory blocks are used as input
  [x_i] and output [y_i], of the operator. They both must exists (be
  allocated) prior to execution.

  We do not require input block to be structurally correct, because
  [mem_op] will just return an error in this case.  *)
Class MSH_DSH_compat
      {i o: nat}
      (mop: @MSHOperator i o)
      (dop: DSHOperator)
      {dsig: TypeSig}
      (σ: evalContext)
      (m: memory)
      (x_p y_p: PExpr)
      `{DSH_pure dop dsig x_p y_p}
  := {
      eval_equiv
      :
        forall (mx mb: mem_block),
          (lookup_Pexp σ m x_p = inr mx) (* input exists *) ->
          (lookup_Pexp σ m y_p = inr mb) (* output before *) ->

          (h_opt_err_c (fun md (* memory diff *) m' (* memory state after execution *) =>
                     err_p (fun ma => SHCOL_DSHCOL_mem_block_equiv mb ma md
                           ) (lookup_Pexp σ m' y_p)
                  ) (mem_op mop mx) (evalDSHOperator σ dop m (estimateFuel dop)));
    }.

Inductive context_pos_typecheck: evalContext -> var_id -> DSHType -> Prop :=
| context0_tc {v: DSHVal} {t: DSHType} (cs:evalContext):
    DSHValType v t -> context_pos_typecheck (v::cs) 0 t
| contextS_tc {v: DSHVal} {t: DSHType} (n:nat) (cs:evalContext):
    context_pos_typecheck cs n t ->
    DSHValType v t -> context_pos_typecheck (v::cs) (S n) t.

(* Check if [MExpr] is properly typed in given evaluation context *)
Inductive NExpr_typecheck: NExpr -> evalContext -> Prop :=
| NVar_tc (σ: evalContext) (n:var_id):
    context_pos_typecheck σ n DSHnat ->  NExpr_typecheck (NVar n) σ
| NConst_tc (σ: evalContext) {a}: NExpr_typecheck (NConst a) σ
| NDiv_tc (σ: evalContext) (a b:NExpr):
    NExpr_typecheck a σ ->
    NExpr_typecheck b σ ->
    NExpr_typecheck (NDiv a b) σ
| NMod_tc (σ: evalContext) (a b:NExpr):
    NExpr_typecheck a σ ->
    NExpr_typecheck b σ ->
    NExpr_typecheck (NMod a b) σ
| NPlus_tc (σ: evalContext) (a b:NExpr):
    NExpr_typecheck a σ ->
    NExpr_typecheck b σ ->
    NExpr_typecheck (NPlus a b) σ
| NMinus_tc (σ: evalContext) (a b:NExpr):
    NExpr_typecheck a σ ->
    NExpr_typecheck b σ ->
    NExpr_typecheck (NMinus a b) σ
| NMult_tc (σ: evalContext) (a b:NExpr):
    NExpr_typecheck a σ ->
    NExpr_typecheck b σ ->
    NExpr_typecheck (NMult a b) σ
| NMin_tc (σ: evalContext) (a b:NExpr):
    NExpr_typecheck a σ ->
    NExpr_typecheck b σ ->
    NExpr_typecheck (NMin a b) σ
| NMax_tc (σ: evalContext) (a b:NExpr):
    NExpr_typecheck a σ ->
    NExpr_typecheck b σ ->
    NExpr_typecheck (NMax a b) σ.

(* Check if [MExpr] is properly typed in given evaluation context *)
Inductive MExpr_typecheck: MExpr -> evalContext -> Prop :=
| MVar_tc (σ: evalContext) (n:var_id):
    context_pos_typecheck σ n DSHMemBlock -> MExpr_typecheck (MVar n) σ
| MConst_tc (σ: evalContext) {a}: MExpr_typecheck (MConst a) σ.

(* Check if [MExpr] is properly typed in given evaluation context *)
Inductive PExpr_typecheck: PExpr -> evalContext -> Prop :=
| PVar_tc (σ: evalContext) (n:var_id):
    context_pos_typecheck σ n DSHPtr -> PExpr_typecheck (PVar n) σ.

(* Check if [AExpr] is properly typed in given evaluation context *)
Inductive AExpr_typecheck: AExpr -> evalContext -> Prop
  :=
  | AVar_tc (σ: evalContext) (n:var_id):
      context_pos_typecheck σ n DSHCType ->  AExpr_typecheck (AVar n) σ
  | AConst_tc (σ: evalContext) {a}: AExpr_typecheck (AConst a) σ
  | ANth_tc (σ: evalContext) (me:MExpr) (ne:NExpr) :
      MExpr_typecheck me σ ->
      NExpr_typecheck ne σ ->
      AExpr_typecheck (ANth me ne) σ
  | AAbs_tc (σ: evalContext) (e:AExpr):
      AExpr_typecheck e σ -> AExpr_typecheck (AAbs e) σ
  | APlus_tc  (σ: evalContext) (a b:AExpr):
      AExpr_typecheck a σ ->
      AExpr_typecheck b σ ->
      AExpr_typecheck (APlus  a b) σ
  | AMinus_tc (σ: evalContext) (a b:AExpr):
      AExpr_typecheck a σ ->
      AExpr_typecheck b σ ->
      AExpr_typecheck (AMinus a b) σ
  | AMult_tc  (σ: evalContext) (a b:AExpr):
      AExpr_typecheck a σ ->
      AExpr_typecheck b σ ->
      AExpr_typecheck (AMult  a b) σ
  | AMin_tc   (σ: evalContext) (a b:AExpr):
      AExpr_typecheck a σ ->
      AExpr_typecheck b σ ->
      AExpr_typecheck (AMin   a b) σ
  | AMax_tc   (σ: evalContext) (a b:AExpr):
      AExpr_typecheck a σ ->
      AExpr_typecheck b σ ->
      AExpr_typecheck (AMax   a b) σ
  | AZless_tc (σ: evalContext) (a b:AExpr):
      AExpr_typecheck a σ ->
      AExpr_typecheck b σ ->
      AExpr_typecheck (AZless a b) σ.

Class MSH_DSH_BinCarrierA_compat
      {o: nat}
      (f: {n:nat|n<o} -> CarrierA -> CarrierA -> CarrierA)
      (σ: evalContext)
      (df : AExpr)
      `{dft : DSHIBinCarrierA df}
  :=
    {
      ibin_typechecks:
        forall n a b,
          AExpr_typecheck df (DSHCTypeVal b :: DSHCTypeVal a :: DSHnatVal n :: σ);

      ibin_equiv:
        forall nc a b, evalIBinCType σ df (proj1_sig nc) a b = inr (f nc a b)
    }.

Instance AAbs_DSHIBinCarrierA:
  DSHIBinCarrierA (AAbs (AMinus (AVar 1) (AVar 0))).
Proof.
  unfold DSHIBinCarrierA.
  unfold AExprTypeSigIncludes.
  exists (TP.of_list [(0,DSHCType) ; (1,DSHCType)]).
  split.
  -
    unfold TP.uncurry.
    cbn.
    unfold TypeSigUnion_error.
    break_match; [reflexivity |].
    clear Heqd; contradict n.
    cbv.
    intros.
    inversion H.
  -
    cbv.
    repeat break_match; try congruence.
    contradict f; reflexivity.
Qed.

Instance Abs_MSH_DSH_BinCarrierA_compat
  :
    forall σ,
      MSH_DSH_BinCarrierA_compat
        (λ i (a b : CarrierA),
         IgnoreIndex abs i
                     (HCOL.Fin1SwapIndex2 (n:=2)
                                          jf
                                          (IgnoreIndex2 sub) i a b))
        σ
        (AAbs (AMinus (AVar 1) (AVar 0))).
Proof.
  split.
  -
    intros n a b.
    repeat constructor.
  -
    intros nc a b.
    unfold evalIBinCType.
    f_equiv.
Qed.

Lemma evalDSHBinOp_mem_lookup_mx
      {n off: nat}
      {df : AExpr}
      `{dft : DSHIBinCarrierA df}
      {σ : evalContext}
      {mx mb ma : mem_block}
      (E: evalDSHBinOp n off df σ mx mb = inr ma)
      (k: nat)
      (kc:k<n):
  is_Some (mem_lookup k mx) /\ is_Some (mem_lookup (k+off) mx).
Proof.
  (*
  apply equiv_Some_is_Some in E.
  revert mb E k kc.
  induction n; intros.
  -
    inversion kc.
  -
    destruct (Nat.eq_dec k n).
    +
      subst.
      simpl in *.
      repeat break_match_hyp; try some_none.
      split;constructor.
    +
      simpl in *.
      repeat break_match_hyp; try some_none.
      apply eq_Some_is_Some in Heqo. rename Heqo into H1.
      apply eq_Some_is_Some in Heqo0. rename Heqo0 into H2.
      clear Heqo1 c c0.
      apply IHn with (mb:=mem_add n c1 mb); clear IHn.
      *
        apply E.
      *
        lia.
   *)
Admitted.


(* TODO: Move to Memory.v *)
Lemma mem_add_comm
      (k1 k2: NM.key)
      (v1 v2: CarrierA)
      (N: k1≢k2)
      (m: mem_block):
  mem_add k1 v1 (mem_add k2 v2 m) = mem_add k2 v2 (mem_add k1 v1 m).
Proof.
  intros y.
  unfold mem_add.
  destruct (Nat.eq_dec y k1) as [K1| NK1].
  -
    subst.
    rewrite NP.F.add_eq_o by reflexivity.
    rewrite NP.F.add_neq_o by auto.
    symmetry.
    apply Option_equiv_eq.
    apply NP.F.add_eq_o.
    reflexivity.
  -
    rewrite NP.F.add_neq_o by auto.
    destruct (Nat.eq_dec y k2) as [K2| NK2].
    subst.
    rewrite NP.F.add_eq_o by reflexivity.
    rewrite NP.F.add_eq_o by reflexivity.
    reflexivity.
    rewrite NP.F.add_neq_o by auto.
    rewrite NP.F.add_neq_o by auto.
    rewrite NP.F.add_neq_o by auto.
    reflexivity.
Qed.

Fact evalDSHBinOp_preservation
     {n off k: nat}
     {kc: k>=n}
     {df : AExpr}
     `{dft : DSHIBinCarrierA df}
     {σ : evalContext}
     {mx ma mb : mem_block}
     {c : CarrierA}:
  evalDSHBinOp n off df σ mx (mem_add k c mb) = inr ma
  → mem_lookup k ma = Some c.
Proof.
  revert mb k kc.
  induction n; intros mb k kc E.
  -
    simpl in *.
    inl_inr_inv.
    unfold mem_lookup, mem_add in *.
    rewrite <- E.
    apply Option_equiv_eq.
    apply NP.F.add_eq_o.
    reflexivity.
  -
    simpl in E.
    repeat break_match_hyp; try inl_inr.
    apply IHn with (mb:=mem_add n c2 mb).
    lia.
    rewrite mem_add_comm by auto.
    apply E.
Qed.

Lemma evalDSHBinOp_nth
      {n off: nat}
      {df : AExpr}
      `{dft : DSHIBinCarrierA df}
      {σ : evalContext}
      {mx mb ma : mem_block}
      (k: nat)
      (kc: k<n)
      {a b : CarrierA}:
  (mem_lookup k mx = Some a) ->
  (mem_lookup (k + off) mx = Some b) ->
  (evalDSHBinOp n off df σ mx mb = inr ma) ->
  h_opt_err_c (=) (mem_lookup k ma) (evalIBinCType σ df k a b).
Proof.
  (*
  intros A B E.
  revert mb a b A B E.
  induction n; intros.
  -
    inversion kc.
  -
    simpl in *.
    repeat break_match_hyp; try some_none.
    destruct (Nat.eq_dec k n).
    +
      clear IHn.
      subst k.
      rewrite Heqo in A. clear Heqo.
      rewrite Heqo0 in B. clear Heqo0.
      repeat some_inv.

      opt_hyp_to_equiv.
      rewrite B in Heqo1; clear B c0.
      rewrite A in Heqo1; clear A c.
      rewrite Heqo1. clear Heqo1.
      clear - E dft.
      unshelve eapply (evalDSHBinOp_preservation E).
      lia.
    +
      apply IHn with (mb:=mem_add n c1 mb); auto.
      lia.
      *)
Admitted.

Lemma evalDSHBinOp_oob_preservation
      {n off: nat}
      {df : AExpr}
      `{dft : DSHIBinCarrierA df}
      {σ : evalContext}
      {mx mb ma : mem_block}
      (ME: evalDSHBinOp n off df σ mx mb = inr ma):
  ∀ (k : NM.key) (kc:k>=n), mem_lookup k mb = mem_lookup k ma.
Proof.
  intros k kc.
  revert mb ME.
  induction n; intros.
  -
    inversion kc; simpl in ME; inl_inr_inv; rewrite ME; reflexivity.
  -
    simpl in *.
    repeat break_match_hyp; try inl_inr.
    destruct (Nat.eq_dec k n).
    +
      apply IHn; lia.
    +
      replace (mem_lookup k mb) with
          (mem_lookup k (mem_add n c1 mb)).
      apply IHn. clear IHn.
      lia.
      apply ME.
      apply NP.F.add_neq_o.
      auto.
Qed.

Lemma mem_block_to_avector_nth
      {n : nat}
      {mx : mem_block}
      {vx : vector CarrierA n}
      (E: mem_block_to_avector mx ≡ Some vx)
      {k: nat}
      {kc: (k < n)%nat}:
  mem_lookup k mx ≡ Some (Vnth vx kc).
Proof.
  unfold mem_block_to_avector in E.
  apply vsequence_Vbuild_eq_Some in E.
  apply Vnth_arg_eq with (ip:=kc) in E.
  rewrite Vbuild_nth in E.
  rewrite Vnth_map in E.
  apply E.
Qed.

Lemma mem_op_of_hop_x_density
      {i o: nat}
      {op: vector CarrierA i -> vector CarrierA o}
      {x: mem_block}
  :
    is_Some (mem_op_of_hop op x) -> (forall k (kc:k<i), is_Some (mem_lookup k x)).
Proof.
  intros H k kc.
  unfold mem_op_of_hop in H.
  break_match_hyp; try some_none.
  apply mem_block_to_avector_nth with (kc0:=kc) in Heqo0.
  apply eq_Some_is_Some in Heqo0.
  apply Heqo0.
Qed.

(* This is generalized version of [evalDSHBinOp_nth]
   TODO see if we can replace [evalDSHBinOp_nth] with it
   or at lease simplify its proof using this lemma.
*)
Lemma evalDSHBinOp_equiv_inr_spec
      {off n: nat}
      {df : AExpr}
      `{dft : DSHIBinCarrierA df}
      {σ : evalContext}
      {mx mb ma : mem_block}:
  (evalDSHBinOp n off df σ mx mb = inr ma)
  ->
  (∀ k (kc: k < n),
      ∃ a b,
        (mem_lookup k mx = Some a /\
         mem_lookup (k+off) mx = Some b /\
         (exists c,
             mem_lookup k ma = Some c /\
             evalIBinCType σ df k a b = inr c))
  ).
Proof.
  (*
  intros E k kc.
  pose proof (evalDSHBinOp_mem_lookup_mx E) as [A B] ; eauto.
  apply is_Some_equiv_def in A.
  destruct A as [a A].
  apply is_Some_equiv_def in B.
  destruct B as [b B].
  exists a.
  exists b.
  repeat split; auto.

  revert mb a b A B E.
  induction n; intros.
  -
    inversion kc.
  -
    simpl in *.
    repeat break_match_hyp; try some_none.
    destruct (Nat.eq_dec k n).
    +
      clear IHn.
      subst k.
      rewrite Heqo in A. clear Heqo.
      rewrite Heqo0 in B. clear Heqo0.
      repeat some_inv.

      opt_hyp_to_equiv.
      rewrite B in Heqo1; clear B c0.
      rewrite A in Heqo1; clear A c.
      exists c1.
      rewrite Heqo1. clear Heqo1.
      clear - E dft.
      split; try reflexivity.
      unshelve eapply (evalDSHBinOp_preservation E).
      lia.
    +
      apply IHn with (mb:=mem_add n c1 mb); auto.
      lia.
   *)
Admitted.

(* TODO: generalize this *)
Lemma is_OK_evalDSHBinOp_mem_equiv
      (n off : nat)
      (df : AExpr)
      (σ : evalContext)
      (mx ma mb : mem_block) :
  ma = mb ->
  is_OK (evalDSHBinOp n off df σ mx ma) =
  is_OK (evalDSHBinOp n off df σ mx mb).
Proof.
  intros.
  pose proof evalDSHBinOp_proper n off df σ mx mx.
  unfold Proper, respectful in H0.
  assert (T : mx = mx) by reflexivity;
    specialize (H0 T ma mb H); clear T.
  unfold is_Some.
  repeat break_match; try reflexivity; inversion H0.
  reflexivity.
  reflexivity.
Qed.

(* TODO: move *)
Lemma mem_add_overwrite
      (k : NM.key)
      (v1 v2 : CarrierA)
      (m : NM.t CarrierA) :
  mem_add k v2 (mem_add k v1 m) = mem_add k v2 m.
Proof.
  intros.
  unfold mem_add, equiv, mem_block_Equiv.
  intros.
  destruct (Nat.eq_dec k k0).
  -
    repeat rewrite NP.F.add_eq_o by assumption.
    reflexivity.
  -
    repeat rewrite NP.F.add_neq_o by assumption.
    reflexivity.
Qed.

Lemma is_OK_evalDSHBinOp_mem_add
      (n off : nat)
      (df : AExpr)
      (σ : evalContext)
      (mx mb : mem_block)
      (k : NM.key)
      (v : CarrierA) :
  is_OK (evalDSHBinOp n off df σ mx (mem_add k v mb)) =
  is_OK (evalDSHBinOp n off df σ mx mb).
Proof.
  dependent induction n; [reflexivity |].
  cbn.
  repeat break_match; try reflexivity.
  destruct (Nat.eq_dec n k).
  -
    subst.
    apply is_OK_evalDSHBinOp_mem_equiv.
    apply mem_add_overwrite.
  -
    rewrite is_OK_evalDSHBinOp_mem_equiv
      with (ma := mem_add n c1 (mem_add k v mb))
           (mb := mem_add k v (mem_add n c1 mb)).
    apply IHn.
    apply mem_add_comm.
    assumption.
Qed.

Lemma evalIBinCarrierA_value_independent
      (σ : evalContext)
      (df : AExpr)
      (n : nat) :
  (exists a b, is_OK (evalIBinCType σ df n a b)) ->
  forall c d, is_OK (evalIBinCType σ df n c d).
Proof.
  (*
  intros.
  destruct H as [a [b H]].
  induction df; cbn in *.
  
  (* base case 1 *)
  destruct v.
  reflexivity.
  destruct v.
  reflexivity.
  apply H.
  
  (* base case 2 *)
  trivial.
  
  (* base case 3 *)
  {
    repeat break_match; try some_none; exfalso.
    -
      contradict Heqo0.
      apply is_Some_ne_None.
      apply eq_Some_is_Some in Heqo2.
      clear - Heqo2; rename Heqo2 into H,
                               n0 into e.
      induction e; cbn in *.
      (* base 1 *)
      destruct v; [| destruct v].
      inversion H.
      inversion H.
      apply H.
      (* base 2 *)
      trivial.
      (* inductive *)
      all: repeat break_match; try reflexivity; try some_none.
      all: try apply IHe; try apply IHe1; try apply IHe2.
      all: trivial.
    -
      contradict Heqo0.
      apply is_Some_ne_None.
      apply eq_Some_is_Some in Heqo2.
      clear - Heqo2; rename Heqo2 into H,
                               n0 into e.
      induction e; cbn in *.
      (* base 1 *)
      destruct v; [| destruct v].
      inversion H.
      inversion H.
      apply H.
      (* base 2 *)
      trivial.
      (* inductive *)
      all: repeat break_match; try reflexivity; try some_none.
      all: try apply IHe; try apply IHe1; try apply IHe2.
      all: trivial.
    -
      contradict Heqo.
      apply is_Some_ne_None.
      apply eq_Some_is_Some in Heqo0.
      clear - Heqo0; rename Heqo0 into H.
      destruct m; cbn in *.
      +
        destruct v; [| destruct v].
        inversion H.
        inversion H.
        apply H.
      +
        trivial.
    -
      contradict Heqo.
      apply is_Some_ne_None.
      apply eq_Some_is_Some in Heqo0.
      clear - Heqo0; rename Heqo0 into H.
      destruct m; cbn in *.
      +
        destruct v; [| destruct v].
        inversion H.
        inversion H.
        apply H.
      +
        trivial.
  }
  
  (* inductive cases *)
  all: unfold evalIBinCType in *.
  all: repeat break_match; try reflexivity; try some_none.
  all: try apply IHdf; try apply IHdf1; try apply IHdf2.
  all: trivial.
   *)
Admitted.

(* TODO: move *)
Lemma is_OK_neq_inl {A : Type} (s : string) (v : err A) :
  is_OK v -> v ≢ inl s.
Proof.
  destruct v.
  auto.
  discriminate.
Qed.

Lemma evalDSHBinOp_is_OK_inv
      {off n: nat}
      {df : AExpr}
      `{dft : DSHIBinCarrierA df}
      {σ : evalContext}
      {dfs: TypeSig}
      `{TS : AExprTypeSigIncludes df dfs}
      (TC: typecheck_env 3 dfs σ)
      {mx mb: mem_block}:
  (∀ k (kc: k < n),
      ∃ a b,
        (mem_lookup k mx = Some a /\
         mem_lookup (k+off) mx = Some b /\
         is_OK (evalIBinCType σ df k a b)
        )
  ) -> (is_OK (evalDSHBinOp n off df σ mx mb)).
Proof.
  intros H.
  induction n; [reflexivity |].
  simpl.
  repeat break_match.
  1-3: exfalso.
  -
    assert (T : n < S n) by omega.
    specialize (H n T).
    destruct H as [a [b [L1 [L2 S]]]].
    unfold mem_lookup_err, trywith in Heqe.
    break_match; try inversion Heqe; try some_none.
  -
    assert (T : n < S n) by omega.
    specialize (H n T).
    destruct H as [a [b [L1 [L2 S]]]].
    unfold mem_lookup_err, trywith in Heqe0.
    break_match; try inversion Heqe0; try some_none.
  -
    contradict Heqe1.
    assert (T : n < S n) by omega.
    specialize (H n T).
    apply is_OK_neq_inl.
    apply evalIBinCarrierA_value_independent.
    destruct H as [a [b H]].
    exists a, b.
    apply H.
  -
    rewrite is_OK_evalDSHBinOp_mem_add.
    apply IHn.
    intros.
    apply H.
    omega.
Qed.

Lemma AExprTypeSigIncludes_exact
      (df : AExpr)
      (dfs : TypeSig)
      (TS : TypeSigAExpr df = Some dfs) :
  AExprTypeSigIncludes df dfs.
Proof.
  exists dfs.
  split; [assumption | apply TypeSigIncluded_reflexive].
Qed.

Lemma evalDSHBinOp_is_OK_inv'
      {off n: nat}
      {df : AExpr}
      `{dft : DSHIBinCarrierA df}
      {σ : evalContext}
      {dfs: TypeSig}
      (TS : TypeSigAExpr df = Some dfs)
      (TC: typecheck_env 3 dfs σ)
      {mx mb: mem_block}:
  (∀ k (kc: k < n),
      ∃ a b,
        (mem_lookup k mx = Some a /\
         mem_lookup (k+off) mx = Some b /\
         is_OK (evalIBinCType σ df k a b)
        )
  ) -> (is_OK (evalDSHBinOp n off df σ mx mb)).
Proof.
  pose proof AExprTypeSigIncludes_exact df dfs TS; clear TS.
  apply evalDSHBinOp_is_OK_inv.
  assumption.
Qed.

Lemma evalDSHBinOp_is_Err
      (off n: nat)
      (nz: n≢0)
      (df : AExpr)
      `{dft : DSHIBinCarrierA df}
      (σ : evalContext)
      (mx mb : mem_block):
  (exists k (kc:k<n),
      is_None (mem_lookup k mx) \/ is_None (mem_lookup (k+off) mx))
  ->
  is_Err (evalDSHBinOp n off df σ mx mb).
Proof.
  revert mb.
  induction n; intros mb DX.
  +
    crush.
  +
    destruct DX as [k [kc DX]].
    destruct (Nat.eq_dec k n).
    *
      clear IHn.
      subst k.
      simpl.
      repeat break_match; try constructor.
      crush.
      all: unfold is_None in H.
      all: break_match; inversion H.
      all: unfold mem_lookup_err in Heqe, Heqe0.
      all: try rewrite Heqo in Heqe; try rewrite Heqo in Heqe0.
      all: cbn in *; inl_inr.
    *
      simpl.
      repeat break_match; try constructor.
      apply IHn.
      lia.
      exists k.
      assert(k < n) as kc1 by lia.
      exists kc1.
      apply DX.
Qed.

(* This is an inverse of [evalDSHBinOp_is_Err] but it takes
   additional assumption [typecheck_env].

   Basically, it states that in valid environment, the only reason for
   [evalDSHBinOp] to fail is missing data in memory.
 *)
Lemma evalDSHBinOp_is_Err_inv
      (off n: nat)
      (df : AExpr)
      `{dft : DSHIBinCarrierA df}
      (σ : evalContext)
      {dfs:TypeSig}
      (TS : TypeSigAExpr df = Some dfs)
      (TC: typecheck_env 3 dfs σ)
      (mx mb : mem_block):
  is_Err (evalDSHBinOp n off df σ mx mb) ->
  (exists k (kc:k<n),
      is_None (mem_lookup k mx) \/ is_None (mem_lookup (k+off) mx)).
Proof.
  revert mb.
  induction n.
  -
    crush.
  -
    intros mb N.
    simpl in *.
    repeat break_match_hyp; try some_none.
    +
      unfold mem_lookup_err, trywith in Heqe.
      break_match; inversion Heqe.
      exists n.
      eexists. lia.
      left; rewrite Heqo; reflexivity.
    +
      unfold mem_lookup_err, trywith in Heqe0.
      break_match; inversion Heqe0.
      exists n.
      eexists. lia.
      right; rewrite Heqo; reflexivity.
    +
      clear N.
      contradict Heqe1.
      apply is_OK_neq_inl.
      unfold evalIBinCType.
      eapply evalAExpr_is_OK'.
      eauto.
      destruct dft as [dfs' [TS' TI]].
      assert(dfs' = dfs) as DE.
      {
        rewrite TS in TS'.
        some_inv.
        symmetry.
        apply TS'.
      }
      rewrite DE in TI.
      clear dfs' DE TS'.

      apply typecheck_env_S.
      apply MaybeMapsTo_Included with (haystack:=DSHIBinCarrierA_TypeSig); eauto.
      cbn; unfold TP.uncurry; simpl.
      apply TM.add_1; reflexivity.

      apply typecheck_env_S.
      apply MaybeMapsTo_Included with (haystack:=DSHIBinCarrierA_TypeSig); eauto.
      cbn; unfold TP.uncurry; simpl.
      repeat (apply TM.add_2; [lia|]).
      apply TM.add_1; reflexivity.

      apply typecheck_env_S.
      apply MaybeMapsTo_Included with (haystack:=DSHIBinCarrierA_TypeSig); eauto.
      cbn; unfold TP.uncurry; simpl.
      repeat (apply TM.add_2; [lia|]).
      apply TM.add_1; reflexivity.

      apply TC.
    +
      specialize (IHn _ N).
      destruct IHn as [k [kc IHn]].
      exists k.
      assert(k<S n) as kc1 by lia.
      exists kc1.
      apply IHn.
Qed.

Lemma evalDSHBinOp_context_equiv
      (n off : nat)
      (df : AExpr)
      `{dft : DSHIBinCarrierA df}
      {dfs: TypeSig}
      (σ0 σ1 : evalContext) (m0 m1: mem_block):
  TypeSigAExpr df = Some dfs ->
  context_equiv_at_TypeSig_off dfs 3 σ0 σ1 ->
  evalDSHBinOp n off df σ0 m0 m1 = evalDSHBinOp n off df σ1 m0 m1.
Proof.
  intros H E.
  unfold equiv, option_Equiv.
  destruct_err_equiv.
  -
    admit.
  -
    destruct n.
    +
      simpl in Ha.
      inl_inr.
    +
      apply eq_inl_is_Err in Ha.
      eapply evalDSHBinOp_is_Err_inv in Ha; eauto.
      2:{ eapply context_equiv_at_TypeSig_off_both_typcheck in E.
          eapply E.
      }
      apply eq_inr_is_OK in Hb.

      apply evalDSHBinOp_is_Err with (df:=df) (σ:=σ1) (mb:=m1) in Ha.
      clear - Ha Hb.
      unfold is_Err, is_OK in *.
      break_match.
      all: auto.
  -
    destruct n.
    +
      simpl in Hb.
      inl_inr.
    +
      apply eq_inl_is_Err in Hb.
      eapply evalDSHBinOp_is_Err_inv in Hb; eauto.
      2:{ eapply context_equiv_at_TypeSig_off_both_typcheck in E.
          eapply E.
      }
      apply eq_inr_is_OK in Ha.

      apply evalDSHBinOp_is_Err with (df:=df) (σ:=σ0) (mb:=m1) in Hb.
      clear - Ha Hb.
      unfold is_Err, is_OK in *.
      break_match.
      all: auto.
  -
    destruct n.
    +
      simpl in *.
      repeat inl_inr_inv.
      subst.
      reflexivity.
    +
      rename m0 into x, m1 into y.
      rename m into m0, m2 into m1.
      intros k.

      apply err_equiv_eq in Ha.
      apply err_equiv_eq in Hb.
      destruct (Nat.lt_decidable k (S n)) as [kc|kc].
      *
        eapply evalDSHBinOp_equiv_inr_spec in Ha; eauto.
        eapply evalDSHBinOp_equiv_inr_spec in Hb; eauto.

        destruct Ha as [a0 [b0 [A0 [B0 [c0 [C0 E0]]]]]].
        destruct Hb as [a1 [b1 [A1 [B1 [c1 [C1 E1]]]]]].

        rewrite A0 in A1; clear A0.
        rewrite B0 in B1; clear B0.
        repeat some_inv.
        rewrite A1, B1 in E0; clear A1 B1 a0 b0.
        enough (evalIBinCType σ0 df k a1 b1 = evalIBinCType σ1 df k a1 b1)
         by (rewrite C0, C1; rewrite E0, E1 in H0; inl_inr_inv; rewrite H0; reflexivity).
        rename a1 into a, b1 into b.
        unfold evalIBinCType in *.

        apply evalAExpr_context_equiv_at_exact_TypeSig with (ts:=dfs).
        apply H.

        apply context_equiv_at_TypeSig_0.
        destruct dft as [dfs' [D0 D1]].
        assert(DE: dfs' = dfs).
        {
          apply Some_inj_equiv.
          rewrite <- D0, <- H.
          reflexivity.
        }
        rewrite DE in D1.
        clear DE D0 dfs'.

        replace (DSHCTypeVal b :: DSHCTypeVal a :: DSHnatVal k :: σ0) with
            ([DSHCTypeVal b ; DSHCTypeVal a ; DSHnatVal k] ++ σ0) by reflexivity.
        replace (DSHCTypeVal b :: DSHCTypeVal a :: DSHnatVal k :: σ1) with
            ([DSHCTypeVal b ; DSHCTypeVal a ; DSHnatVal k] ++ σ1) by reflexivity.

        apply context_equiv_at_TypeSig_split.
        apply E.
        reflexivity.
        simpl.
        unfold DSHIBinCarrierA_TypeSig in D1.

        clear -D1.
        rename k into nv.
        unfold context_equiv_at_TypeSig_head.
        intros k t kc M.
        apply TypeSigIncluded_at with (k:=k) (v:=t) in D1; eauto.
        clear dfs M.

        unfold contextEnsureType.
        break_match; [|contradict Heqo; apply ListUtil.nth_in; auto].
        destruct k.
        --
          simpl in *.
          some_inv.
          subst d. clear kc.
          unfold TP.uncurry in *; simpl in *.
          apply TP.F.add_mapsto_iff in D1.
          destruct D1.
          ++
            destruct H.
            subst t.
            split; constructor.
            constructor.
            reflexivity.
          ++
            destruct H.
            congruence.
        --
          destruct k.
          simpl in *.
          some_inv.
          subst d. clear kc.
          unfold TP.uncurry in *; simpl in *.
          apply TP.F.add_neq_mapsto_iff in D1.
          apply TP.F.add_mapsto_iff in D1.
          destruct D1.
          ++
            destruct H.
            subst t.
            split; constructor.
            constructor.
            reflexivity.
          ++
            destruct H.
            congruence.
          ++
            auto.
          ++
            destruct k.
            simpl in *.
            some_inv.

            subst d. clear kc.
            unfold TP.uncurry in *; simpl in *.
            apply TP.F.add_neq_mapsto_iff in D1.
            apply TP.F.add_neq_mapsto_iff in D1.
            apply TP.F.add_mapsto_iff in D1.
            destruct D1.
            **
              destruct H.
              subst t.
              split; constructor.
              constructor.
              reflexivity.
            **
              destruct H.
              congruence.
            **
              auto.
            **
              auto.
            **
              lia.
      *
        apply evalDSHBinOp_oob_preservation with (k0:=k) in Ha; try lia.
        apply evalDSHBinOp_oob_preservation with (k0:=k) in Hb; try lia.
        rewrite <- Ha, <- Hb.
        reflexivity.
Admitted.


Lemma memory_lookup_err_inr_is_Some {s : string} (m : memory) (mbi : mem_block_id) :
  forall mb, memory_lookup_err s m mbi ≡ inr mb → is_Some (memory_lookup m mbi).
Proof.
  intros.
  unfold memory_lookup_err, trywith in H.
  break_match.
  reflexivity.
  inversion H.
Qed.

Global Instance Assign_DSH_pure
       (x_n y_n : NExpr)
       (x_p y_p : PExpr)
       {ts : TypeSig}
       `{XN : NExprTypeSigIncludes x_n ts}
       `{YN : NExprTypeSigIncludes y_n ts}
  :
    DSH_pure (DSHAssign (x_p, x_n) (y_p, y_n)) ts x_p y_p.
Proof.
  split.
  -
    intros.
    destruct fuel; [inversion H |].
    cbn in H.
    repeat break_match; try inl_inr.
    inl_inr_inv; rewrite <-H.
    split; intros.
    +
      apply mem_block_exists_memory_set; assumption.
    +
      apply mem_block_exists_memory_set_inv in H0.
      destruct H0; [assumption |].
      subst.
      apply memory_is_set_is_Some.
      apply memory_lookup_err_inr_is_Some in Heqe2.
      assumption.
  -
    intros until fuel; intros CE BEx BEy.
    eapply evalNExpr_context_equiv_at_TypeSig in XN;
      [apply eq_equiv_err_nat in XN | eassumption].
    eapply evalNExpr_context_equiv_at_TypeSig in YN;
      [apply eq_equiv_err_nat in YN | eassumption].
    unfold blocks_equiv_at_Pexp in *;
      inversion BEx; clear BEx; inversion H1; clear H1;
      inversion BEy; clear BEy; inversion H6; clear H6.
    destruct (evalDSHOperator σ0) eqn:OE1,
             (evalDSHOperator σ1) eqn:OE2.
    all: repeat constructor.
    all: destruct fuel; try (cbn in *; some_none; fail).
    all: cbn in *.
    all: try inl_inr.
    all: unfold memory_lookup_err, mem_lookup_err, trywith in *.
    all: rewrite <-H, <-H0, <-H1, <-H2, <-H3, <-H5, <-H7, <-H8, XN, YN in *.
    all: repeat break_match; try some_none; try inl_inr.
    all: repeat some_inv; repeat inl_inr_inv; subst.
    +
      assert (C : mem_lookup n m4 = mem_lookup n m2) by apply H4.
      rewrite Heqo0, Heqo in C.
      some_none.
    +
      assert (C : mem_lookup n m4 = mem_lookup n m2) by apply H4.
      rewrite Heqo0, Heqo in C.
      some_none.
    +
      unfold memory_lookup, memory_set.
      repeat (rewrite NP.F.add_eq_o by reflexivity).
      constructor.
      unfold mem_add, equiv, mem_block_Equiv; intros.
      destruct (Nat.eq_dec n0 k).
      *
        repeat (rewrite NP.F.add_eq_o with (x := n0) by assumption).
        rewrite <-Heqo, <-Heqo0.
        apply H4.
      *
        repeat (rewrite NP.F.add_neq_o with (x := n0) by assumption).
        apply H9.
  -
    intros.
    unfold memory_equiv_except, memory_lookup; intros.
    destruct fuel; [inversion H |].
    cbn in H.
    repeat break_match; try some_none; try inl_inr.
    repeat some_inv; repeat inl_inr_inv; subst.
    unfold equiv, memory_Equiv, memory_set, mem_add in H.
    specialize (H k).
    rewrite <-H.
    destruct (Nat.eq_dec m1 k), (Nat.eq_dec n0 k);
        try (rewrite NP.F.add_eq_o with (x := m1) by assumption);
        try (rewrite NP.F.add_eq_o with (x := n0) by assumption);
        try (rewrite NP.F.add_neq_o with (x := m1) by assumption);
        try (rewrite NP.F.add_neq_o with (x := n0) by assumption).
    all: subst.
    all: try congruence.
    all: reflexivity.
Qed.

Global Instance BinOp_DSH_pure
       (o : nat)
       (x_p y_p : PExpr)
       (a: AExpr)
       `{dft : DSHIBinCarrierA a}
       {ts: TypeSig}
       `{TSI: AExprTypeSigIncludes a ts}
  :
    DSH_pure (DSHBinOp o x_p y_p a) (TypeSig_decr_n ts 3) x_p y_p.
Proof.
  split.
  -
    intros.
    destruct fuel; [inversion H |].
    cbn in H.
    repeat break_match; try some_none; try inl_inr.
    inl_inr_inv; rewrite <-H.
    split; intros.
    +
      apply mem_block_exists_memory_set; assumption.
    +
      apply mem_block_exists_memory_set_inv in H0.
      destruct H0; [assumption |].
      subst.
      apply memory_is_set_is_Some.
      apply memory_lookup_err_inr_is_Some in Heqe2.
      assumption.
  -
    intros until fuel; intros CE BEx BEy.
    inversion TSI; clear TSI.
    rename x into ats; destruct H as [ATS TSI].

    unfold blocks_equiv_at_Pexp in *;
      inversion BEx; clear BEx; inversion H1; clear H1;
      inversion BEy; clear BEy; inversion H6; clear H6.
    destruct (evalDSHOperator σ0) eqn:OE1,
             (evalDSHOperator σ1) eqn:OE2.
    all: repeat constructor.
    all: destruct fuel; try (cbn in *; some_none; fail).
    all: cbn in *.
    all: try inl_inr.
    all: unfold memory_lookup_err, mem_lookup_err, trywith in *.
    all: rewrite <-H, <-H0, <-H1, <-H2, <-H3, <-H5, <-H7, <-H8 in *.
    all: repeat break_match; try some_none; try inl_inr.
    all: repeat some_inv; repeat inl_inr_inv; subst.
    +
      enough (inl s = inr m4) by inl_inr.
      rewrite <-Heqe4, <-Heqe1.
      rewrite evalDSHBinOp_context_equiv with (σ1 := σ1).
      rewrite H4, H9; reflexivity.
      assumption.
      eassumption.
      apply context_equiv_at_TypeSig_off_decr.
      enough (TypeSigIncluded (TypeSig_decr_n ats 3) (TypeSig_decr_n ts 3)).
      eapply context_equiv_at_TypeSigIncluded; eassumption.
      apply TypeSig_decr_n_Included; assumption.
    +
      enough (inr m6 = inl s) by inl_inr.
      rewrite <-Heqe4, <-Heqe1.
      rewrite evalDSHBinOp_context_equiv with (σ1 := σ1).
      rewrite H4, H9; reflexivity.
      assumption.
      eassumption.
      apply context_equiv_at_TypeSig_off_decr.
      enough (TypeSigIncluded (TypeSig_decr_n ats 3) (TypeSig_decr_n ts 3)).
      eapply context_equiv_at_TypeSigIncluded; eassumption.
      apply TypeSig_decr_n_Included; assumption.
    +
      unfold memory_lookup, memory_set.
      repeat (rewrite NP.F.add_eq_o by reflexivity).
      constructor.
      unfold mem_add, equiv, mem_block_Equiv; intros.
      enough (T : inr m8 = inr m5) by (inl_inr_inv; rewrite T; reflexivity).
      rewrite <-Heqe4, <-Heqe1.
      rewrite evalDSHBinOp_context_equiv with (σ1 := σ1).
      rewrite H4, H9; reflexivity.
      assumption.
      eassumption.
      apply context_equiv_at_TypeSig_off_decr.
      enough (TypeSigIncluded (TypeSig_decr_n ats 3) (TypeSig_decr_n ts 3)).
      eapply context_equiv_at_TypeSigIncluded; eassumption.
      apply TypeSig_decr_n_Included; assumption.
  -
    intros σ m m' fuel E y_i P.
    destruct fuel; simpl in E; [inl_inr |].

    repeat break_match; try some_none; try inl_inr.
    repeat some_inv; repeat inl_inr_inv.
    apply err_equiv_eq in Heqe0;
    apply err_equiv_eq in Heqe1;
    apply err_equiv_eq in Heqe2.
    rewrite P in Heqe0, Heqe2, E.
    clear P m1.
    rename m0 into x_i, m2 into x, m3 into y, m4 into y'.

    intros k NKY.
    rewrite <- E.
    clear E m'.
    unfold memory_lookup, memory_set in *.
    rewrite NP.F.add_neq_o by auto.
    reflexivity.    
Qed.

Lemma eq_equiv_option_CarrierA (a1 a2 : option CarrierA) :
  a1 = a2 <-> a1 ≡ a2.
Proof.
  split; intros.
  -
    unfold equiv, option_Equiv in H.
    inversion H; [reflexivity |].
    f_equal.
    rewrite H0.
    reflexivity.
  -
    rewrite H.
    reflexivity.
Qed.

Global Instance Power_DSH_pure
       (n : NExpr)
       (x_n y_n : NExpr)
       (x_p y_p : PExpr)
       (a : AExpr)
       (ts : TypeSig)
       `{AI : AExprTypeSigIncludes a (TypeSig_incr_n ts 2)}
       `{NI : NExprTypeSigIncludes n ts}
       `{XNI : NExprTypeSigIncludes x_n ts}
       `{YNI : NExprTypeSigIncludes y_n ts}
       (initial : CarrierA)
  :
    DSH_pure (DSHPower n (x_p, x_n) (y_p, y_n) a initial) ts x_p y_p.
Proof.
  split.
  -
    intros.
    destruct fuel; [inversion H |].
    cbn in H.
    repeat break_match; try some_none; try inl_inr.
    inl_inr_inv; rewrite <-H.
    split; intros.
    +
      apply mem_block_exists_memory_set; assumption.
    +
      apply mem_block_exists_memory_set_inv in H0.
      destruct H0; [assumption |].
      subst.
      apply memory_is_set_is_Some.
      apply memory_lookup_err_inr_is_Some in Heqe2.
      assumption.
  -
    intros until fuel; intros CE BEx BEy.
    pose proof (evalNExpr_context_equiv_at_TypeSig n CE) as NE.
    pose proof (evalNExpr_context_equiv_at_TypeSig x_n CE) as XNE.
    pose proof (evalNExpr_context_equiv_at_TypeSig y_n CE) as YNE.
    rewrite eq_equiv_err_nat in NE, XNE, YNE.

    unfold blocks_equiv_at_Pexp in *;
      inversion BEx; clear BEx; inversion H1; clear H1;
      inversion BEy; clear BEy; inversion H6; clear H6.
    destruct (evalDSHOperator σ0) eqn:OE1,
             (evalDSHOperator σ1) eqn:OE2.
    all: repeat constructor.
    all: destruct fuel; try (cbn in *; some_none; fail).
    all: cbn in *.
    all: try inl_inr.
    all: unfold memory_lookup_err, mem_lookup_err, trywith in *.
    all: rewrite <-H, <-H0, <-H1, <-H2, <-H3, <-H5, <-H7, <-H8, XNE, YNE, NE in *.
    all: repeat break_match; try some_none; try inl_inr.
    all: repeat some_inv; repeat inl_inr_inv; subst.
    +
      exfalso.
      enough (inr m4 = inl s) by inl_inr.
      rewrite <-Heqe7, <-Heqe4; clear Heqe7 Heqe4.
      (*
      clear H7; generalize dependent x2.
      clear H8; generalize dependent y2.
      generalize dependent initial.
      clear Heqo NE.
      induction n0;
        [intros; cbn in *; repeat some_inv; rewrite H9; reflexivity |].
      intros.
      cbn.
      repeat rewrite NM.Raw.Proofs.add_find by apply NM.is_bst; cbn.
      replace (mem_lookup 0 x0) with (mem_lookup 0 y0)
        by (rewrite <-eq_equiv_option_CarrierA, H4; reflexivity).
      break_match; [| reflexivity].
      assert (evalBinCType σ0 a c initial ≡ evalBinCType σ1 a c initial).
      {
        rewrite <-eq_equiv_option_CarrierA.
        unfold evalBinCType.
        eapply evalAExpr_context_equiv_at_TypeSig.
        eassumption.
        repeat (rewrite TypeSig_incr_TypeSig_incr_n;
                apply context_equiv_at_TypeSig_widening).
        rewrite TypeSig_incr_n_0.
        assumption.
      }
      rewrite H6.
      break_match; [| reflexivity].
      eapply IHn0.
      rewrite H9.
      reflexivity.
    +
      (* TODO: this is copy-paste from previous bullet *)
      exfalso.
      enough (Some m2 = None) by some_none.
      rewrite <-Heqo2, <-Heqo3; clear Heqo2 Heqo3.
      clear H7; generalize dependent x2.
      clear H8; generalize dependent y2.
      generalize dependent initial.
      clear Heqo NE.
      induction n0;
        [intros; cbn in *; repeat some_inv; rewrite H9; reflexivity |].
      intros.
      cbn.
      repeat rewrite NM.Raw.Proofs.add_find by apply NM.is_bst; cbn.
      replace (mem_lookup 0 x0) with (mem_lookup 0 y0)
        by (rewrite <-eq_equiv_option_CarrierA, H4; reflexivity).
      break_match; [| reflexivity].
      assert (evalBinCType σ0 a c initial ≡ evalBinCType σ1 a c initial).
      {
        rewrite <-eq_equiv_option_CarrierA.
        unfold evalBinCType.
        eapply evalAExpr_context_equiv_at_TypeSig.
        eassumption.
        repeat (rewrite TypeSig_incr_TypeSig_incr_n;
                apply context_equiv_at_TypeSig_widening).
        rewrite TypeSig_incr_n_0.
        assumption.
      }
      rewrite H6.
      break_match; [| reflexivity].
      eapply IHn0.
      rewrite H9.
      reflexivity.
    +
      unfold memory_lookup, memory_set.
      repeat (rewrite NP.F.add_eq_o by reflexivity).
      constructor.
      enough (Some m4 = Some m3) by (some_inv; assumption).
      rewrite <-Heqo2, <-Heqo3; clear Heqo2 Heqo3.

      clear H7; generalize dependent x2.
      clear H8; generalize dependent y2.
      generalize dependent initial.
      clear Heqo NE.
      induction n0;
        [intros; cbn in *; repeat some_inv; rewrite H9; reflexivity |].
      intros.
      cbn.
      repeat rewrite NM.Raw.Proofs.add_find by apply NM.is_bst; cbn.
      replace (mem_lookup 0 x0) with (mem_lookup 0 y0)
        by (rewrite <-eq_equiv_option_CarrierA, H4; reflexivity).
      break_match; [| reflexivity].
      assert (evalBinCType σ0 a c initial ≡ evalBinCType σ1 a c initial).
      {
        rewrite <-eq_equiv_option_CarrierA.
        unfold evalBinCType.
        eapply evalAExpr_context_equiv_at_TypeSig.
        eassumption.
        repeat (rewrite TypeSig_incr_TypeSig_incr_n;
                apply context_equiv_at_TypeSig_widening).
        rewrite TypeSig_incr_n_0.
        assumption.
      }
      rewrite H6.
      break_match; [| reflexivity].
      eapply IHn0.
      rewrite H9.
      reflexivity.
  -
    intros.
    unfold memory_equiv_except, memory_lookup; intros.
    destruct fuel; [inversion H |].
    cbn in H.
    repeat break_match; try some_none.
    repeat some_inv; subst.
    unfold equiv, memory_Equiv, memory_set, mem_add in H.
    specialize (H k).
    rewrite <-H.
    destruct (Nat.eq_dec m1 k), (Nat.eq_dec n0 k);
        try (rewrite NP.F.add_eq_o with (x := m1) by assumption);
        try (rewrite NP.F.add_eq_o with (x := n0) by assumption);
        try (rewrite NP.F.add_neq_o with (x := m1) by assumption);
        try (rewrite NP.F.add_neq_o with (x := n0) by assumption).
    all: subst.
    all: try congruence.
    all: reflexivity.
       *)
Admitted.

Global Instance Embed_MSH_DSH_compat
       {o b: nat}
       (bc: b < o)
       (σ: evalContext)
       (y_n : NExpr)
       (x_p y_p : PExpr)
       (tm' : TypeSig)
       (dfs : TypeSig)
       (m : memory)
       (BP : DSH_pure (DSHAssign (x_p, NConst 0) (y_p, y_n)) dfs x_p y_p)
       (Y: evalNexp σ y_n = inr b)
  :
    @MSH_DSH_compat _ _ (MSHEmbed bc) (DSHAssign (x_p, NConst 0) (y_p, y_n)) dfs σ m x_p y_p BP.
Proof.
  (*
  constructor; intros mx mb MX MB.
  destruct mem_op as [md |] eqn:MD, evalDSHOperator as [fma |] eqn:FMA; try constructor.
  2,3: exfalso.
  all: unfold lookup_Pexp in MX, MB.
  all: cbn in *.
  all: destruct evalPexp eqn:XP in MX; try some_none; rewrite XP in *.
  all: destruct evalPexp eqn:YP in MB; try some_none; rewrite YP in *.
  all: unfold Embed_mem,
              map_mem_block_elt,
              MMemoryOfCarrierA.mem_lookup,
              MMemoryOfCarrierA.mem_add,
              MMemoryOfCarrierA.mem_empty
         in MD.
  all: repeat break_match; try some_none.
  all: repeat some_inv.
  -
    inversion Y; subst; clear Y.
    unfold SHCOL_DSHCOL_mem_block_equiv,
      memory_lookup, memory_set, mem_add, mem_lookup.
    rewrite NP.F.add_eq_o by reflexivity.
    constructor.
    intros.
    destruct (Nat.eq_dec b i);
      [ repeat rewrite NP.F.add_eq_o by assumption
      | repeat rewrite NP.F.add_neq_o by assumption ].
    +
      constructor 2; [reflexivity |].
      rewrite <-Heqo3, <-Heqo4.
      unfold mem_lookup.
      apply MX.
    +
      constructor 1; [reflexivity |].
      symmetry; apply MB.
  -
    enough (None = Some c) by some_none.
    rewrite <-Heqo3, <-Heqo4.
    apply MX.
  -
    enough (Some c = None) by some_none.
    rewrite <-Heqo3, <-Heqo4.
    apply MX.
   *)
Admitted.

Global Instance Pick_MSH_DSH_compat
       {i b: nat}
       (bc: b < i)
       (σ: evalContext)
       (x_n : NExpr)
       (x_p y_p : PExpr)
       (tm' : TypeSig)
       (dfs : TypeSig)
       (m : memory)
       (BP : DSH_pure (DSHAssign (x_p, x_n) (y_p, NConst 0)) dfs x_p y_p)
       (X: evalNexp σ x_n = inr b)
  :
    @MSH_DSH_compat _ _ (MSHPick bc) (DSHAssign (x_p, x_n) (y_p, NConst 0)) dfs σ m x_p y_p BP.
Proof.
  (*
  constructor; intros mx mb MX MB.
  destruct mem_op as [md |] eqn:MD, evalDSHOperator as [fma |] eqn:FMA; try constructor.
  2,3: exfalso.
  all: unfold lookup_Pexp in MX, MB.
  all: cbn in *.
  all: destruct evalPexp eqn:XP in MX; try some_none; rewrite XP in *.
  all: destruct evalPexp eqn:YP in MB; try some_none; rewrite YP in *.
  all: unfold Pick_mem,
              map_mem_block_elt,
              MMemoryOfCarrierA.mem_lookup,
              MMemoryOfCarrierA.mem_add,
              MMemoryOfCarrierA.mem_empty
         in MD.
  all: repeat break_match; try some_none.
  all: repeat some_inv.
  all: inversion X; subst; clear X.
  -
    unfold SHCOL_DSHCOL_mem_block_equiv,
      memory_lookup, memory_set, mem_add, mem_lookup.
    rewrite NP.F.add_eq_o by reflexivity.
    constructor.
    intros.
    destruct (Nat.eq_dec 0 i0);
      [ repeat rewrite NP.F.add_eq_o by assumption
      | repeat rewrite NP.F.add_neq_o by assumption ].
    +
      constructor 2; [reflexivity |].
      rewrite <-Heqo2, <-Heqo3.
      apply MX.
    +
      constructor 1; [reflexivity |].
      symmetry; apply MB.
  -
    enough (None = Some c) by some_none.
    rewrite <-Heqo2, <-Heqo3.
    apply MX.
  -
    enough (Some c = None) by some_none.
    rewrite <-Heqo2, <-Heqo3.
    apply MX.
   *)
Admitted.

Global Instance BinOp_MSH_DSH_compat
       {o: nat}
       (f: {n:nat|n<o} -> CarrierA -> CarrierA -> CarrierA)
       `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
       (x_p y_p : PExpr)
       (df : AExpr)
       `{dft : DSHIBinCarrierA df}
       {dfs: TypeSig}
       {DTS: TypeSigAExpr df = Some dfs}
       (σ: evalContext)
       (TC: typecheck_env 3 dfs σ)
       (m: memory)
       `{MSH_DSH_BinCarrierA_compat _ f σ df}
       `{BP: DSH_pure (DSHBinOp o x_p y_p df) dfs x_p y_p}
  :
    @MSH_DSH_compat _ _ (MSHBinOp f) (DSHBinOp o x_p y_p df) dfs σ m x_p y_p BP.
Proof.
  (*
  split.
  intros mx mb MX MB.
  simpl.
  destruct (mem_op_of_hop (HCOL.HBinOp f) mx) as [md|] eqn:MD.
  -
    unfold lookup_Pexp in *.
    simpl in *.
    repeat break_match; subst; try some_none.
    +
      constructor.
      unfold memory_lookup, memory_set.
      rewrite NP.F.add_eq_o by reflexivity.
      constructor.
      repeat some_inv.

      opt_hyp_to_equiv.

      rewrite MB in Heqo3, Heqo4; clear MB m3. (* poor man's subst *)
      rewrite MX in Heqo2, Heqo4; clear MX m2. (* poor man's subst *)

      rename Heqo4 into ME.
      intros k.

      unfold mem_op_of_hop in MD.
      break_match_hyp; try some_none.
      some_inv.
      rewrite <- MD.
      clear MD md.
      rename t into vx.

      unfold avector_to_mem_block.

      avector_to_mem_block_to_spec md HD OD.
      destruct (NatUtil.lt_ge_dec k o) as [kc | kc].
      *
        (* k<o, which is normal *)
        clear OD.
        simpl in *.
        unfold MMemoryOfCarrierA.mem_lookup in HD.
        unfold mem_lookup.
        rewrite HD with (ip:=kc).
        clear HD md.
        apply MemExpected.
        --
          unfold is_Some.
          tauto.
        --
          inversion_clear H as [_ FV].

          assert (k < o + o)%nat as kc1 by omega.
          assert (k + o < o + o)%nat as kc2 by omega.
          rewrite HBinOp_nth with (jc1:=kc1) (jc2:=kc2).

          pose proof (evalDSHBinOp_mem_lookup_mx ME k kc) as [A B].

          apply is_Some_equiv_def in A. destruct A as [a A].
          apply is_Some_equiv_def in B. destruct B as [b B].

          rewrite (evalDSHBinOp_nth k kc A B ME).
          specialize FV with (nc:=mkFinNat kc) (a:=a) (b:=b).
          simpl in FV.
          rewrite FV.

          pose proof (mem_block_to_avector_nth Heqo4 (kc:=kc1)) as MVA.
          pose proof (mem_block_to_avector_nth Heqo4 (kc:=kc2)) as MVB.

          repeat f_equiv.
          apply Some_inj_equiv ; rewrite <- A; apply Option_equiv_eq; apply MVA.
          apply Some_inj_equiv; rewrite <- B; apply Option_equiv_eq; apply MVB.
      *
        (* k >= 0 *)
        simpl in *.
        clear HD.
        rewrite OD by assumption.
        apply MemPreserved.
        --
          unfold is_None.
          tauto.
        --
          specialize (OD k kc).
          apply (evalDSHBinOp_oob_preservation ME),kc.
    +
      (* mem_op succeeded with [Some md] while evaluation of DHS failed *)
      exfalso.
      repeat some_inv.


      opt_hyp_to_equiv.
      rewrite MB in Heqo3, Heqo4; clear MB m3. (* poor man's subst *)
      rewrite MX in Heqo2, Heqo4; clear MX m2. (* poor man's subst *)

      rename Heqo4 into E.

      (* TODO may be not needed *)
      apply equiv_Some_is_Some in MD.
      pose proof (mem_op_of_hop_x_density MD) as DX.
      clear MD pF.

      inversion_clear H as [_ FV].

      contradict E.
      apply is_Some_nequiv_None.

      eapply evalDSHBinOp_is_OK_inv; try eauto.
      intros k kc.

      assert(DX1:=DX).
      assert(kc1: k < o + o) by lia.
      specialize (DX k kc1).
      apply is_Some_equiv_def in DX.
      destruct DX as [a DX].

      assert(kc2: k + o < o + o) by lia.
      specialize (DX1 (k+o) kc2).
      apply is_Some_equiv_def in DX1.
      destruct DX1 as [b DX1].
      exists a.
      exists b.
      repeat split; eauto.

      specialize (FV (FinNat.mkFinNat kc) a b).
      apply equiv_Some_is_Some in FV.
      apply FV.
  -
    unfold lookup_Pexp in *.
    simpl in *.
    repeat break_match; try some_none.
    +
      apply Some_ne_None in Heqo2.
      contradict Heqo2.
      repeat some_inv.

      opt_hyp_to_equiv.
      rewrite MB in Heqo3, Heqo4; clear MB m3. (* poor man's subst *)
      rewrite MX in Heqo4; clear MX m2. (* poor man's subst *)

      unfold mem_op_of_hop in MD.
      break_match_hyp; try some_none.
      clear MD.
      rename Heqo2 into MX.
      unfold mem_block_to_avector in MX.
      apply vsequence_Vbuild_eq_None in MX.
      apply is_None_def.
      destruct o.
      *
        destruct MX as [k [kc MX]].
        inversion kc.
      *
        contradict Heqo4.
        apply None_nequiv_Some.
        apply is_None_equiv_def.
        apply mem_block_Equiv_Equivalence.

        apply evalDSHBinOp_is_Err; try typeclasses eauto.
        lia.
        destruct MX as [k MX].
        destruct (NatUtil.lt_ge_dec k (S o)) as [kc1 | kc2].
        --
          exists k.
          exists kc1.
          left.
          destruct MX as [kc MX].
          apply is_None_def in MX.
          eapply MX.
        --
          exists (k-(S o)).
          destruct MX as [kc MX].
          assert(kc3: k - S o < S o) by lia.
          exists kc3.
          right.
          apply is_None_def in MX.
          replace (k - S o + S o) with k.
          apply MX.
          lia.
    +
      constructor.
   *)
Admitted.

(* Simple wrapper. *)
Definition memory_alloc_empty m i :=
  memory_set m i (mem_empty).

Lemma blocks_equiv_at_Pexp_incrVar
      (p : PExpr)
      (σ0 σ1 : evalContext)
      (m0 m1: memory)
      {foo0 foo1: DSHVal}
  : blocks_equiv_at_Pexp σ0 σ1 p m0 m1 <->
    blocks_equiv_at_Pexp (foo0::σ0) (foo1::σ1) (incrPVar 0 p) m0 m1.
Proof.
  split.
  -
    intros H.
    unfold blocks_equiv_at_Pexp.
    rewrite 2!evalPexp_incrPVar.
    apply H.
  -
    intros H.
    unfold blocks_equiv_at_Pexp in *.
    setoid_rewrite evalPexp_incrPVar in H.
    apply H; exact (DSHnatVal 0).
Qed.

Lemma blocks_equiv_at_Pexp_remove
      (y_p : PExpr)
      (σ0 σ1 : evalContext)
      (t0_i t1_i : mem_block_id)
      (m0'' m1'' : memory)
      (NY0: evalPexp σ0 y_p ≢ inr t0_i)
      (NY1: evalPexp σ1 y_p ≢ inr t1_i):
  blocks_equiv_at_Pexp σ0 σ1 y_p m0'' m1''
  → blocks_equiv_at_Pexp σ0 σ1 y_p (memory_remove m0'' t0_i) (memory_remove m1'' t1_i).
Proof.
  (*
  intros EE.
  unfold blocks_equiv_at_Pexp in *.
  destruct (evalPexp σ0 y_p), (evalPexp σ1 y_p).
  -
    constructor.
    inversion_clear EE.
    rewrite Some_neq in NY0.
    rewrite Some_neq in NY1.
    unfold memory_lookup, memory_remove in *.
    rewrite 2!NP.F.remove_neq_o; auto.
  -
    inversion EE.
  -
    inversion EE.
  -
    inversion EE.
   *)
Admitted.

Lemma blocks_equiv_at_Pexp_add_mem
      (p : PExpr)
      (σ0 σ1 : evalContext)
      (m0 m1 : memory)
      (t0 t1 : mem_block_id)
      (foo0 foo1: mem_block)
  :
    evalPexp σ0 p ≢ inr t0 ->
    evalPexp σ1 p ≢ inr t1 ->
    blocks_equiv_at_Pexp σ0 σ1 p m0 m1 ->
    blocks_equiv_at_Pexp σ0 σ1 p
                         (memory_set m0 t0 foo0)
                         (memory_set m1 t1 foo1).
Proof.
  (*
  intros E0 E1 EE.
  unfold blocks_equiv_at_Pexp in *.
  destruct (evalPexp σ0 p), (evalPexp σ1 p).
  -
    constructor.
    inversion_clear EE.
    inversion H. clear H.
    symmetry in H0, H1.
    rewrite Some_neq in E0.
    rewrite Some_neq in E1.
    unfold memory_lookup, memory_set in *.
    rewrite 2!NP.F.add_neq_o; auto.
    rewrite H0, H1.
    constructor.
    apply H2.
  -
    inversion EE.
  -
    inversion EE.
  -
    inversion EE.
   *)
Admitted.

Instance Compose_DSH_pure
         {n: nat}
         {x_p y_p: PExpr}
         {dop1 dop2: DSHOperator}
         {dsig1 dsig2: TypeSig}
         (TC: TypeSigCompat dsig1 dsig2)
         `{P2: DSH_pure dop2 (TypeSig_incr dsig1) (incrPVar 0 x_p) (PVar 0)}
         `{P1: DSH_pure dop1 (TypeSig_incr dsig2) (PVar 0) (incrPVar 0 y_p)}
  : DSH_pure (DSHAlloc n (DSHSeq dop2 dop1)) (TypeSigUnion dsig1 dsig2) x_p y_p.
Proof.
  (*
  split.
  - (* mem_stable *)
    intros σ m m' fuel H k.
    destruct P1 as [MS1 _ _].
    destruct P2 as [MS2 _ _].
    destruct fuel; simpl in *; try some_none.
    break_match_hyp; try some_none.
    destruct fuel; simpl in *; try some_none.
    break_match_hyp; try some_none.
    rename Heqo into D1, Heqo0 into D2.
    some_inv. rewrite <- H. clear m' H.
    remember (memory_new m) as k'.

    destruct(Nat.eq_dec k k') as [E|NE].
    +
      subst k'.
      rewrite <- E in D1.
      rewrite <- E in D2.
      apply Option_equiv_eq in D1.
      apply Option_equiv_eq in D2.
      rewrite <- E.
      apply MS2 with (k:=k) in D2.
      apply MS1 with (k:=k) in D1.
      clear MS1 MS2.
      split; intros H.
      *
        contradict H.
        subst k.
        apply mem_block_exists_memory_new.
      *
        contradict H.
        subst k.
        apply mem_block_exists_memory_remove.
    +
      apply Option_equiv_eq in D1.
      apply Option_equiv_eq in D2.
      apply MS2 with (k:=k) in D2.
      apply MS1 with (k:=k) in D1.
      clear MS1 MS2.
      split; intros H.
      *
        eapply mem_block_exists_memory_set in H.
        apply D2 in H.
        apply D1 in H.
        erewrite <- mem_block_exists_memory_remove_neq; eauto.
      *
        eapply mem_block_exists_memory_set_neq.
        eauto.
        eapply D2.
        eapply D1.
        eapply mem_block_exists_memory_remove_neq; eauto.
  -
    intros σ0 σ1 m0 m1 fuel TE EX EY.
    destruct fuel; try constructor.
    simpl.
    repeat break_match; try some_none; try constructor.
    +
      rename m into m0''',  m2 into m1'''.

      unfold blocks_equiv_at_Pexp in EX, EY.

      destruct (evalPexp σ0 x_p) eqn:P0X, (evalPexp σ1 x_p) eqn:P1X; try inversion EX.
      destruct (evalPexp σ0 y_p) eqn:P0Y, (evalPexp σ1 y_p) eqn:P1Y; try inversion EY.
      rename m into x0_i, m2 into x1_i, m3 into y0_i, m4 into y1_i.
      clear EX EY.
      subst x y x0 y0.
      inversion H1.
      inversion H4.
      clear H1 H4.
      symmetry_option_hyp.
      rename x0 into y0, y0 into y1, x into x0, y into x1.

      remember (memory_new m0) as t0_i.
      remember (memory_new m1) as t1_i.
      remember (DSHPtrVal t0_i) as t0_v.
      remember (DSHPtrVal t1_i) as t1_v.

      remember (memory_set m0 t0_i mem_empty) as m0'.
      remember (memory_set m1 t1_i mem_empty) as m1'.

      remember (t0_v :: σ0) as σ0'.
      remember (t1_v :: σ1) as σ1'.

      destruct fuel;  simpl in *; try  some_none.
      break_match_hyp; try some_none.
      break_match_hyp; try some_none.

      rename Heqo1 into E12, Heqo0 into E11.
      rename Heqo2 into E02, Heqo into E01.
      rename m2 into m0''.
      rename m into m1''.

      destruct P1, P2.

      pose proof (Option_equiv_eq _ _ E02) as E02'.
      pose proof (Option_equiv_eq _ _ E12) as E12'.

      assert(evalPexp σ0 y_p ≢ Some t0_i) as NYT0.
      {
        rewrite P0Y.
        apply Some_neq.
        intros C.
        subst.
        apply eq_Some_is_Some, memory_is_set_is_Some, mem_block_exists_memory_new in H3.
        tauto.
      }

      assert(evalPexp σ1 y_p ≢ Some t1_i) as NYT1.
      {
        rewrite P1Y.
        apply Some_neq.
        intros C.
        subst.
        apply eq_Some_is_Some, memory_is_set_is_Some, mem_block_exists_memory_new in H5.
        tauto.
      }

      apply blocks_equiv_at_Pexp_remove; auto.

      cut (opt_r (blocks_equiv_at_Pexp σ0' σ1' (incrPVar 0 y_p)) (Some m0''') (Some m1''')).
      intros H1; inversion H1.

      apply blocks_equiv_at_Pexp_incrVar with (foo0:=DSHPtrVal t0_i) (foo1:=DSHPtrVal t1_i); auto.
      replace (DSHPtrVal t0_i :: σ0) with σ0' by crush.
      replace (DSHPtrVal t1_i :: σ1) with σ1' by crush.
      apply H8.

      specialize (mem_read_safe0 σ0' σ1' m0'' m1'' fuel).
      rewrite E01 in mem_read_safe0.
      rewrite E11 in mem_read_safe0.
      apply mem_read_safe0; clear mem_read_safe0.

      subst σ0' σ1'.
      apply context_equiv_at_TypeSig_widening.
      eapply context_equiv_at_TypeSigUnion_right.
      eapply TC.
      eapply TE.

      cut (opt_r (blocks_equiv_at_Pexp σ0' σ1' (PVar 0)) (Some m0'') (Some m1'')).
      intros H1;  inversion H1.
      apply H8.
      specialize (mem_read_safe1 σ0' σ1' m0' m1' fuel).
      rewrite E02 in mem_read_safe1.
      rewrite E12 in mem_read_safe1.
      apply mem_read_safe1; clear mem_read_safe1.

      subst σ0' σ1'.
      apply context_equiv_at_TypeSig_widening.
      eapply context_equiv_at_TypeSigUnion_left.
      eapply TC.
      eapply TE.

      subst σ0' σ1' t0_v t1_v.
      apply blocks_equiv_at_Pexp_incrVar; auto.
      subst m0' m1'.

      assert(evalPexp σ0 x_p ≢ Some t0_i) as NXT0.
      {
        rewrite P0X.
        apply Some_neq.
        intros C.
        subst.
        apply eq_Some_is_Some, memory_is_set_is_Some, mem_block_exists_memory_new in H.
        congruence.
      }

      assert(evalPexp σ1 x_p ≢ Some t1_i) as NXT1.
      {
        rewrite P1X.
        apply Some_neq.
        intros C.
        subst.
        apply eq_Some_is_Some, memory_is_set_is_Some, mem_block_exists_memory_new in H0.
        congruence.
      }
      apply blocks_equiv_at_Pexp_add_mem; auto.

      unfold blocks_equiv_at_Pexp.
      rewrite P0X, P1X.
      constructor.
      rewrite H, H0.
      constructor.
      auto.

      subst σ0' σ1' t0_v t1_v.
      unfold blocks_equiv_at_Pexp.
      simpl.
      constructor.
      subst.
      simpl.
      unfold memory_lookup, memory_set.
      rewrite 2!NP.F.add_eq_o by reflexivity.
      constructor.
      reflexivity.

      unfold blocks_equiv_at_Pexp.
      rewrite Heqσ1', Heqσ0'.
      rewrite 2!evalPexp_incrPVar.
      rewrite P0Y, P1Y.
      constructor.

      rename mem_write_safe1 into mem_write_safe10.
      assert (mem_write_safe11 := mem_write_safe10).

      assert(YT0': evalPexp σ0' (PVar 0) = Some t0_i) by (subst; reflexivity).
      assert(YT1': evalPexp σ1' (PVar 0) = Some t1_i) by (subst; reflexivity).
      rewrite P0Y in NYT0; rewrite Some_neq in NYT0.
      rewrite P1Y in NYT1; rewrite Some_neq in NYT1.
      specialize (mem_write_safe10 σ0' m0' m0'' fuel E02' t0_i YT0' y0_i NYT0).
      specialize (mem_write_safe11 σ1' m1' m1'' fuel E12' t1_i YT1' y1_i NYT1).
      rewrite <- mem_write_safe10, <- mem_write_safe11.
      subst m0' m1'.
      unfold memory_lookup, memory_set in *.
      rewrite 2!NP.F.add_neq_o by auto.
      rewrite H3, H5.
      constructor.
      apply H6.
    +
      exfalso.
      rename m into m0'''.

      unfold blocks_equiv_at_Pexp in EX, EY.
      destruct (evalPexp σ0 x_p) eqn:P0X, (evalPexp σ1 x_p) eqn:P1X; try inversion EX.
      destruct (evalPexp σ0 y_p) eqn:P0Y, (evalPexp σ1 y_p) eqn:P1Y; try inversion EY.
      rename m into x0_i, m2 into x1_i, m3 into y0_i, m4 into y1_i.
      clear EX EY.
      subst x y x0 y0.
      inversion H1.
      inversion H4.
      clear H1 H4.
      symmetry_option_hyp.
      rename x0 into y0, y0 into y1, x into x0, y into x1.

      remember (memory_new m0) as t0_i.
      remember (memory_new m1) as t1_i.
      remember (DSHPtrVal t0_i) as t0_v.
      remember (DSHPtrVal t1_i) as t1_v.

      remember (memory_set m0 t0_i mem_empty) as m0'.
      remember (memory_set m1 t1_i mem_empty) as m1'.

      remember (t0_v :: σ0) as σ0'.
      remember (t1_v :: σ1) as σ1'.

      destruct fuel;  simpl in *; try some_none.
      repeat break_match_hyp; try some_none.
      *
        rename Heqo1 into E12, Heqo0 into E11.
        rename Heqo2 into E02, Heqo into E01.
        rename m2 into m0''.
        rename m into m1''.
        destruct P1, P2.

        pose proof (Option_equiv_eq _ _ E02) as E02'.
        pose proof (Option_equiv_eq _ _ E12) as E12'.

        assert(evalPexp σ0 y_p ≢ Some t0_i) as NYT0.
        {
          rewrite P0Y.
          apply Some_neq.
          intros C.
          subst.
          apply eq_Some_is_Some, memory_is_set_is_Some, mem_block_exists_memory_new in H3.
          tauto.
        }

        assert(evalPexp σ1 y_p ≢ Some t1_i) as NYT1.
        {
          rewrite P1Y.
          apply Some_neq.
          intros C.
          subst.
          apply eq_Some_is_Some, memory_is_set_is_Some, mem_block_exists_memory_new in H5.
          tauto.
        }
        specialize (mem_read_safe0 σ0' σ1' m0'' m1'' fuel).
        rewrite E01 in mem_read_safe0.
        rewrite E11 in mem_read_safe0.

        assert(blocks_equiv_at_Pexp σ0' σ1' (PVar 0) m0'' m1'') as VIP0.
        {
          cut (opt_r (blocks_equiv_at_Pexp σ0' σ1' (PVar 0)) (Some m0'') (Some m1'')).
          intros H1;  inversion H1.
          apply H8.
          specialize (mem_read_safe1 σ0' σ1' m0' m1' fuel).
          rewrite E02 in mem_read_safe1.
          rewrite E12 in mem_read_safe1.
          apply mem_read_safe1; clear mem_read_safe1.

          subst σ0' σ1'.
          apply context_equiv_at_TypeSig_widening.
          eapply context_equiv_at_TypeSigUnion_left.
          eapply TC.
          eapply TE.

          subst σ0' σ1' t0_v t1_v.
          apply blocks_equiv_at_Pexp_incrVar; auto.
          subst m0' m1'.

          assert(evalPexp σ0 x_p ≢ Some t0_i) as NXT0.
          {
            rewrite P0X.
            apply Some_neq.
            intros C.
            subst.
            apply eq_Some_is_Some, memory_is_set_is_Some, mem_block_exists_memory_new in H.
            congruence.
          }

          assert(evalPexp σ1 x_p ≢ Some t1_i) as NXT1.
          {
            rewrite P1X.
            apply Some_neq.
            intros C.
            subst.
            apply eq_Some_is_Some, memory_is_set_is_Some, mem_block_exists_memory_new in H0.
            congruence.
          }
          apply blocks_equiv_at_Pexp_add_mem; auto.

          unfold blocks_equiv_at_Pexp.
          rewrite P0X, P1X.
          constructor.
          rewrite H, H0.
          constructor.
          auto.

          subst σ0' σ1' t0_v t1_v.
          unfold blocks_equiv_at_Pexp.
          simpl.
          constructor.
          subst.
          simpl.
          unfold memory_lookup, memory_set.
          rewrite 2!NP.F.add_eq_o by reflexivity.
          constructor.
          reflexivity.
        }

        assert(blocks_equiv_at_Pexp σ0' σ1' (incrPVar 0 y_p) m0'' m1'') as VIP1.
        {
          unfold blocks_equiv_at_Pexp.
          rewrite Heqσ1', Heqσ0'.
          rewrite 2!evalPexp_incrPVar.
          rewrite P0Y, P1Y.
          constructor.

          rename mem_write_safe1 into mem_write_safe10.
          assert (mem_write_safe11 := mem_write_safe10).

          assert(YT0': evalPexp σ0' (PVar 0) = Some t0_i) by (subst; reflexivity).
          assert(YT1': evalPexp σ1' (PVar 0) = Some t1_i) by (subst; reflexivity).
          rewrite P0Y in NYT0; rewrite Some_neq in NYT0.
          rewrite P1Y in NYT1; rewrite Some_neq in NYT1.
          specialize (mem_write_safe10 σ0' m0' m0'' fuel E02' t0_i YT0' y0_i NYT0).
          specialize (mem_write_safe11 σ1' m1' m1'' fuel E12' t1_i YT1' y1_i NYT1).
          rewrite <- mem_write_safe10, <- mem_write_safe11.
          subst m0' m1'.
          unfold memory_lookup, memory_set in *.
          rewrite 2!NP.F.add_neq_o by auto.
          rewrite H3, H5.
          constructor.
          apply H6.
        }

        assert(TE2': context_equiv_at_TypeSig (TypeSig_incr dsig2) σ0' σ1').
        {
          subst σ0' σ1'.
          apply context_equiv_at_TypeSig_widening.
          eapply context_equiv_at_TypeSigUnion_right.
          eapply TC.
          eapply TE.
        }

        specialize (mem_read_safe0 TE2' VIP0 VIP1).
        inversion mem_read_safe0.
      *
        rename Heqo1 into E12, Heqo0 into E11.
        rename Heqo2 into E02, Heqo into E01.
        rename m into m0''.
        destruct P1, P2.

        pose proof (Option_equiv_eq _ _ E02) as E02'.
        pose proof (Option_equiv_eq _ _ E12) as E12'.

        assert(evalPexp σ0 y_p ≢ Some t0_i) as NYT0.
        {
          rewrite P0Y.
          apply Some_neq.
          intros C.
          subst.
          apply eq_Some_is_Some, memory_is_set_is_Some, mem_block_exists_memory_new in H3.
          tauto.
        }

        assert(evalPexp σ1 y_p ≢ Some t1_i) as NYT1.
        {
          rewrite P1Y.
          apply Some_neq.
          intros C.
          subst.
          apply eq_Some_is_Some, memory_is_set_is_Some, mem_block_exists_memory_new in H5.
          tauto.
        }
        specialize (mem_read_safe1 σ0' σ1' m0' m1' fuel).
        rewrite E02 in mem_read_safe1.
        rewrite E12 in mem_read_safe1.

        assert(blocks_equiv_at_Pexp σ0' σ1' (incrPVar 0 x_p) m0' m1') as VIP0.
        {
          subst σ0' σ1'.
          apply blocks_equiv_at_Pexp_incrVar.
          subst m0' m1'.

          assert(evalPexp σ0 x_p ≢ Some t0_i) as NXT0.
          {
            rewrite P0X.
            apply Some_neq.
            intros C.
            subst.
            apply eq_Some_is_Some, memory_is_set_is_Some, mem_block_exists_memory_new in H.
            congruence.
          }

          assert(evalPexp σ1 x_p ≢ Some t1_i) as NXT1.
          {
            rewrite P1X.
            apply Some_neq.
            intros C.
            subst.
            apply eq_Some_is_Some, memory_is_set_is_Some, mem_block_exists_memory_new in H0.
            congruence.
          }
          apply blocks_equiv_at_Pexp_add_mem; auto.

          unfold blocks_equiv_at_Pexp.
          rewrite P0X, P1X.
          constructor.
          rewrite H, H0.
          constructor.
          auto.
        }

        assert(blocks_equiv_at_Pexp σ0' σ1' (PVar 0) m0' m1') as VIP1.
        {
          subst σ0' σ1' t0_v t1_v.
          unfold blocks_equiv_at_Pexp.
          simpl.
          constructor.
          subst.
          simpl.
          unfold memory_lookup, memory_set.
          rewrite 2!NP.F.add_eq_o by reflexivity.
          constructor.
          reflexivity.
        }

        assert(TE1': context_equiv_at_TypeSig (TypeSig_incr dsig1) σ0' σ1').
        {
          subst σ0' σ1'.
          apply context_equiv_at_TypeSig_widening.
          eapply context_equiv_at_TypeSigUnion_left.
          eapply TC.
          eapply TE.
        }

        specialize (mem_read_safe1 TE1' VIP0 VIP1).
        inversion mem_read_safe1.
    +
      exfalso.
      rename m into m1'''.

      unfold blocks_equiv_at_Pexp in EX, EY.
      destruct (evalPexp σ0 x_p) eqn:P0X, (evalPexp σ1 x_p) eqn:P1X; try inversion EX.
      destruct (evalPexp σ0 y_p) eqn:P0Y, (evalPexp σ1 y_p) eqn:P1Y; try inversion EY.
      rename m into x0_i, m2 into x1_i, m3 into y0_i, m4 into y1_i.
      clear EX EY.
      subst x y x0 y0.
      inversion H1.
      inversion H4.
      clear H1 H4.
      symmetry_option_hyp.
      rename x0 into y0, y0 into y1, x into x0, y into x1.

      remember (memory_new m0) as t0_i.
      remember (memory_new m1) as t1_i.
      remember (DSHPtrVal t0_i) as t0_v.
      remember (DSHPtrVal t1_i) as t1_v.

      remember (memory_set m0 t0_i mem_empty) as m0'.
      remember (memory_set m1 t1_i mem_empty) as m1'.

      remember (t0_v :: σ0) as σ0'.
      remember (t1_v :: σ1) as σ1'.

      destruct fuel;  simpl in *; try  some_none.
      break_match_hyp; try some_none.
      break_match_hyp; try some_none.
      *
        rename Heqo1 into E12, Heqo0 into E11.
        rename Heqo2 into E02, Heqo into E01.
        rename m2 into m0''.
        rename m into m1''.

        destruct P1, P2.

        pose proof (Option_equiv_eq _ _ E02) as E02'.
        pose proof (Option_equiv_eq _ _ E12) as E12'.

        specialize (mem_read_safe0 σ0' σ1' m0'' m1'' fuel).
        rewrite E01 in mem_read_safe0.
        rewrite E11 in mem_read_safe0.

        assert(blocks_equiv_at_Pexp σ0' σ1' (PVar 0) m0'' m1'') as VIP0.
        {
          cut (opt_r (blocks_equiv_at_Pexp σ0' σ1' (PVar 0)) (Some m0'') (Some m1'')).
          intros H1;  inversion H1.
          apply H8.
          specialize (mem_read_safe1 σ0' σ1' m0' m1' fuel).
          rewrite E02 in mem_read_safe1.
          rewrite E12 in mem_read_safe1.
          apply mem_read_safe1; clear mem_read_safe1.

          subst σ0' σ1'.
          apply context_equiv_at_TypeSig_widening.
          eapply context_equiv_at_TypeSigUnion_left.
          eapply TC.
          eapply TE.

          subst σ0' σ1' t0_v t1_v.
          apply blocks_equiv_at_Pexp_incrVar; auto.
          subst m0' m1'.

          assert(evalPexp σ0 x_p ≢ Some t0_i) as NXT0.
          {
            rewrite P0X.
            apply Some_neq.
            intros C.
            subst.
            apply eq_Some_is_Some, memory_is_set_is_Some, mem_block_exists_memory_new in H.
            congruence.
           }

          assert(evalPexp σ1 x_p ≢ Some t1_i) as NXT1.
          {
            rewrite P1X.
            apply Some_neq.
            intros C.
            subst.
            apply eq_Some_is_Some, memory_is_set_is_Some, mem_block_exists_memory_new in H0.
            congruence.
          }
          apply blocks_equiv_at_Pexp_add_mem; auto.

          unfold blocks_equiv_at_Pexp.
          rewrite P0X, P1X.
          constructor.
          rewrite H, H0.
          constructor.
          auto.

          subst σ0' σ1' t0_v t1_v.
          unfold blocks_equiv_at_Pexp.
          simpl.
          constructor.
          subst.
          simpl.
          unfold memory_lookup, memory_set.
          rewrite 2!NP.F.add_eq_o by reflexivity.
          constructor.
          reflexivity.
        }

        assert(evalPexp σ0 y_p ≢ Some t0_i) as NYT0.
        {
          rewrite P0Y.
          apply Some_neq.
          intros C.
          subst.
          apply eq_Some_is_Some, memory_is_set_is_Some, mem_block_exists_memory_new in H3.
          tauto.
        }

        assert(evalPexp σ1 y_p ≢ Some t1_i) as NYT1.
        {
          rewrite P1Y.
          apply Some_neq.
          intros C.
          subst.
          apply eq_Some_is_Some, memory_is_set_is_Some, mem_block_exists_memory_new in H5.
          tauto.
        }

        assert(blocks_equiv_at_Pexp σ0' σ1' (incrPVar 0 y_p) m0'' m1'') as VIP1.
        {
          unfold blocks_equiv_at_Pexp.
          rewrite Heqσ1', Heqσ0'.
          rewrite 2!evalPexp_incrPVar.
          rewrite P0Y, P1Y.
          constructor.

          rename mem_write_safe1 into mem_write_safe10.
          assert (mem_write_safe11 := mem_write_safe10).

          assert(YT0': evalPexp σ0' (PVar 0) = Some t0_i) by (subst; reflexivity).
          assert(YT1': evalPexp σ1' (PVar 0) = Some t1_i) by (subst; reflexivity).
          rewrite P0Y in NYT0; rewrite Some_neq in NYT0.
          rewrite P1Y in NYT1; rewrite Some_neq in NYT1.
          specialize (mem_write_safe10 σ0' m0' m0'' fuel E02' t0_i YT0' y0_i NYT0).
          specialize (mem_write_safe11 σ1' m1' m1'' fuel E12' t1_i YT1' y1_i NYT1).
          rewrite <- mem_write_safe10, <- mem_write_safe11.
          subst m0' m1'.
          unfold memory_lookup, memory_set in *.
          rewrite 2!NP.F.add_neq_o by auto.
          rewrite H3, H5.
          constructor.
          apply H6.
        }

        assert(TE2': context_equiv_at_TypeSig (TypeSig_incr dsig2) σ0' σ1').
        {
          subst σ0' σ1'.
          apply context_equiv_at_TypeSig_widening.
          eapply context_equiv_at_TypeSigUnion_right.
          eapply TC.
          eapply TE.
        }

        specialize (mem_read_safe0 TE2' VIP0 VIP1).
        inversion mem_read_safe0.
      *
        rename Heqo1 into E12, Heqo0 into E11.
        rename Heqo2 into E02, Heqo into E01.
        rename m into m1''.
        destruct P1, P2.

        pose proof (Option_equiv_eq _ _ E02) as E02'.
        pose proof (Option_equiv_eq _ _ E12) as E12'.

        assert(evalPexp σ0 y_p ≢ Some t0_i) as NYT0.
        {
          rewrite P0Y.
          apply Some_neq.
          intros C.
          subst.
          apply eq_Some_is_Some, memory_is_set_is_Some, mem_block_exists_memory_new in H3.
          tauto.
        }

        assert(evalPexp σ1 y_p ≢ Some t1_i) as NYT1.
        {
          rewrite P1Y.
          apply Some_neq.
          intros C.
          subst.
          apply eq_Some_is_Some, memory_is_set_is_Some, mem_block_exists_memory_new in H5.
          tauto.
        }
        specialize (mem_read_safe1 σ0' σ1' m0' m1' fuel).
        rewrite E02 in mem_read_safe1.
        rewrite E12 in mem_read_safe1.


        assert(blocks_equiv_at_Pexp σ0' σ1' (incrPVar 0 x_p) m0' m1') as VIP0.
        {
          subst σ0' σ1'.
          apply blocks_equiv_at_Pexp_incrVar.
          subst m0' m1'.

          assert(evalPexp σ0 x_p ≢ Some t0_i) as NXT0.
          {
            rewrite P0X.
            apply Some_neq.
            intros C.
            subst.
            apply eq_Some_is_Some, memory_is_set_is_Some, mem_block_exists_memory_new in H.
            congruence.
           }

          assert(evalPexp σ1 x_p ≢ Some t1_i) as NXT1.
          {
            rewrite P1X.
            apply Some_neq.
            intros C.
            subst.
            apply eq_Some_is_Some, memory_is_set_is_Some, mem_block_exists_memory_new in H0.
            congruence.
          }
          apply blocks_equiv_at_Pexp_add_mem; auto.

          unfold blocks_equiv_at_Pexp.
          rewrite P0X, P1X.
          constructor.
          rewrite H, H0.
          constructor.
          auto.
        }
        assert(blocks_equiv_at_Pexp σ0' σ1' (PVar 0) m0' m1') as VIP1.
        {
          subst σ0' σ1' t0_v t1_v.
          unfold blocks_equiv_at_Pexp.
          simpl.
          constructor.
          subst.
          simpl.
          unfold memory_lookup, memory_set.
          rewrite 2!NP.F.add_eq_o by reflexivity.
          constructor.
          reflexivity.
        }

        assert(TE1': context_equiv_at_TypeSig (TypeSig_incr dsig1) σ0' σ1').
        {
          subst σ0' σ1'.
          apply context_equiv_at_TypeSig_widening.
          eapply context_equiv_at_TypeSigUnion_left.
          eapply TC.
          eapply TE.
        }

        specialize (mem_read_safe1 TE1' VIP0 VIP1).
        inversion mem_read_safe1.
  -
    (* mem_write_safe *)
    intros σ m0 m4 fuel H y_i H0.
    destruct fuel;  simpl in * ; try  some_none.
    break_match_hyp; try some_none.
    destruct fuel;  simpl in * ; try  some_none.
    break_match_hyp; try some_none.
    some_inv.
    rename m1 into m2, m into m3.
    rename Heqo into E1, Heqo0 into E2.
    remember (memory_new m0) as t_i.
    remember (memory_set m0 t_i mem_empty) as m1.
    remember (DSHPtrVal t_i :: σ) as σ'.
    intros k ky.


    destruct (Nat.eq_dec k t_i) as [kt|kt].
    1:{

      subst k.
      pose proof (mem_block_exists_memory_new m0) as H1.
      rewrite <- Heqt_i in H1.

      unfold mem_block_exists in H1.
      apply NP.F.not_find_in_iff in H1.
      unfold memory_lookup.
      rewrite_clear H1.
      symmetry.

      pose proof (mem_block_exists_memory_remove t_i m3) as H4.
      unfold mem_block_exists in H4.
      apply NP.F.not_find_in_iff in H4.
      unfold equiv, memory_Equiv in H.
      rewrite <- H.
      rewrite H4.
      reflexivity.
    }

    destruct P1 as [P1p _ P1w].
    destruct P2 as [P2p _ P2w].
    apply Option_equiv_eq in E1.
    apply Option_equiv_eq in E2.
    specialize (P1p _ _ _ _ E1).
    specialize (P1w _ _ _ _ E1).
    specialize (P2p _ _ _ _ E2).
    specialize (P2w _ _ _ _ E2).

    destruct(decidable_mem_block_exists k m0) as [F0|NF0]; symmetry.
    2:{

      assert(¬ mem_block_exists k m1) as NF1.
      {
        revert NF0.
        apply not_iff_compat.
        subst m1.
        symmetry.
        apply mem_block_exists_memory_set_neq.
        apply kt.
      }

      specialize (P2p k).
      apply not_iff_compat in P2p.
      apply P2p in NF1.

      specialize (P1p k).
      apply not_iff_compat in P1p.
      apply P1p in NF1.

      assert(¬ mem_block_exists k m4) as NF4.
      {
        rewrite <- H.
        erewrite <- mem_block_exists_memory_remove_neq; eauto.
      }

      unfold mem_block_exists in NF4.
      apply NP.F.not_find_in_iff in NF4.
      unfold memory_lookup.
      rewrite NF4.

      unfold mem_block_exists in NF0.
      apply NP.F.not_find_in_iff in NF0.
      rewrite NF0.
      reflexivity.
    }

    assert (V := F0).
    apply NP.F.in_find_iff, is_Some_ne_None, is_Some_def in V.
    destruct V as [v V].
    unfold memory_lookup.
    rewrite V.

    cut(NM.find (elt:=mem_block) k m3 = Some v).
    intros F3.
    unfold equiv, memory_Equiv in H.
    rewrite <- H.
    unfold memory_remove.
    rewrite NP.F.remove_neq_o; auto.

    cut(NM.find (elt:=mem_block) k m2 = Some v).
    intros F2.
    unfold memory_equiv_except, memory_lookup in P1w.
    specialize (P1w y_i).
    erewrite <- P1w; auto.
    subst σ'.
    rewrite evalPexp_incrPVar.
    assumption.

    cut(NM.find (elt:=mem_block) k m1 = Some v).
    intros F1.
    unfold memory_equiv_except, memory_lookup in P2w.
    specialize (P2w t_i).
    erewrite <- P2w; auto.
    subst σ'.
    reflexivity.

    unfold equiv, memory_Equiv in Heqm1.
    rewrite Heqm1.
    unfold memory_set.
    rewrite NP.F.add_neq_o; auto.
    rewrite V.
    reflexivity.
   *)
Admitted.

(* Also could be proven in other direction *)
Lemma SHCOL_DSHCOL_mem_block_equiv_mem_empty {a b: mem_block}:
  SHCOL_DSHCOL_mem_block_equiv mem_empty a b -> a = b.
Proof.
  intros H.
  unfold SHCOL_DSHCOL_mem_block_equiv in H.
  intros k.
  specialize (H k).
  unfold mem_lookup, mem_empty in H.
  rewrite NP.F.empty_o in H.
  inversion H.
  -
    rewrite <- H1.
    apply is_None_def in H0.
    rewrite H0.
    reflexivity.
  -
    assumption.
Qed.

Instance Compose_MSH_DSH_compat
         {i1 o2 o3: nat}
         {mop1: @MSHOperator o2 o3}
         {mop2: @MSHOperator i1 o2}
         (* {compat: Included _ (in_index_set fm op1) (out_index_set fm op2)} *)
         {σ: evalContext}
         {m: memory}
         {dop1 dop2: DSHOperator}
         {dsig1 dsig2: TypeSig}
         {x_p y_p: PExpr}
         `{P: DSH_pure (DSHAlloc o2 (DSHSeq dop2 dop1)) (TypeSigUnion dsig1 dsig2) x_p y_p}
         `{P2: DSH_pure dop2 (TypeSig_incr dsig2) (incrPVar 0 x_p) (PVar 0)}
         `{P1: DSH_pure dop1 (TypeSig_incr dsig1) (PVar 0) (incrPVar 0 y_p)}
         `{C2: @MSH_DSH_compat _ _ mop2 dop2 (TypeSig_incr dsig2)
                              (DSHPtrVal (memory_new m) :: σ)
                              (memory_alloc_empty m (memory_new m))
                              (incrPVar 0 x_p) (PVar 0)
                              P2
          }
         `{C1: forall m'', memory_equiv_except m m'' (memory_new m) ->
                      MSH_DSH_compat mop1 dop1
                                     (DSHPtrVal (memory_new m) :: σ)
                                     m''
                                     (PVar 0) (incrPVar 0 y_p)}
  :
    MSH_DSH_compat
      (MSHCompose mop1 mop2)
      (DSHAlloc o2 (DSHSeq dop2 dop1))
      σ m x_p y_p.
Proof.
  (*
  split.
  intros mx mb MX MB.
  simpl.

  remember (memory_new m) as t_i.
  remember (DSHPtrVal t_i :: σ) as σ'.
  unfold memory_alloc_empty in *.
  remember (memory_set m t_i mem_empty) as m'.

  destruct (option_compose (mem_op mop1) (mem_op mop2) mx) as [md|] eqn:MD;
    repeat break_match; try some_none.

  -
    rename m1 into m''.
    rename m0 into m'''.
    constructor.
    unfold lookup_Pexp in *.
    simpl in MX, MB.
    repeat break_match_hyp; try some_none.
    simpl.
    rename m1 into x_i, m0 into y_i.
    rename Heqo0 into E2, Heqo into E1.
    rewrite evalDSHOperator_estimateFuel_ge in E1 by lia.
    rewrite evalDSHOperator_estimateFuel_ge in E2 by lia.

    assert(t_i ≢ y_i).
    {
      destruct (Nat.eq_dec t_i y_i); auto.
      subst.
      exfalso.
      contradict MB.
      pose proof (memory_lookup_memory_new_is_None m) as F.
      apply is_None_def in F.
      rewrite F.
      some_none.
    }

    assert(t_i ≢ x_i).
    {
      destruct (Nat.eq_dec t_i x_i); auto.
      subst.
      exfalso.
      contradict MX.
      pose proof (memory_lookup_memory_new_is_None m) as F.
      apply is_None_def in F.
      rewrite F.
      some_none.
    }

    unfold memory_lookup, memory_remove.
    rewrite NP.F.remove_neq_o by assumption.

    assert(mem_block_exists y_i m) as EY.
    {
      apply mem_block_exists_exists_equiv.
      eexists.
      eapply MB.
    }

    assert(mem_block_exists y_i m') as EY'.
    {
      subst m'.
      apply mem_block_exists_memory_set.
      eauto.
    }

    assert(mem_block_exists y_i m'') as EY''.
    {
      destruct P2.
      eapply (mem_stable0  _ m' m'').
      apply Option_equiv_eq in E2.
      eapply E2.
      assumption.
    }

    assert(mem_block_exists y_i m''') as EY'''.
    {
      destruct P1.
      eapply (mem_stable0  _ m'' m''').
      apply Option_equiv_eq in E1.
      eapply E1.
      assumption.
    }

    destruct (NM.find (elt:=mem_block) y_i m''') as [ma|] eqn:MA .
    2:{
      apply memory_is_set_is_Some, is_Some_ne_None in EY'''.
      unfold memory_lookup in EY'''.
      congruence.
    }
    constructor.
    unfold SHCOL_DSHCOL_mem_block_equiv.
    intros k.

    unfold option_compose in MD.
    destruct (mem_op mop2 mx) as [mt|] eqn:MT; try some_none.

    destruct C2 as [C2].
    specialize (C2 mx (mem_empty)).

    assert(MX': lookup_Pexp σ' m' (incrPVar 0 x_p) = Some mx).
    {
      rewrite Heqσ'.
      unfold lookup_Pexp.
      rewrite evalPexp_incrPVar.
      simpl.
      rewrite Heqo2.
      subst m'.
      unfold memory_lookup, memory_set.
      rewrite NP.F.add_neq_o.
      apply MX.
      auto.
    }
    specialize (C2 MX').

    assert(MT': lookup_Pexp σ' m' (PVar 0) = Some mem_empty).
    {
      rewrite Heqσ'.
      unfold lookup_Pexp.
      subst m'.
      simpl.
      unfold memory_lookup, memory_set.
      rewrite NP.F.add_eq_o; reflexivity.
    }
    specialize (C2 MT').

    rewrite E2 in C2.
    rewrite MT in C2.
    inversion C2; subst a b; clear C2 ; rename H3 into C2.

    assert(mem_block_exists t_i m') as ET'.
    {
      subst m'.
      apply mem_block_exists_memory_set_eq.
      reflexivity.
    }

    assert(mem_block_exists t_i m'') as ET''.
    {
      destruct P2.
      eapply (mem_stable0  _ m' m'').
      apply Option_equiv_eq in E2.
      eapply E2.
      assumption.
    }

    inversion C2 as [mt' HC2 MT'']; clear C2; rename HC2 into C2.
    symmetry in MT''.

    apply SHCOL_DSHCOL_mem_block_equiv_mem_empty in C2.
    apply Option_equiv_eq in MT''.
    rewrite C2 in MT''.
    clear C2 mt'.

    specialize (C1 m'').
    destruct C1 as [C1].

    1:{
      eapply memory_equiv_except_trans.
      eapply memory_equiv_except_memory_set.
      eapply Heqm'.
      intros.
      destruct P2.
      eapply mem_write_safe0.
      rewrite E2.
      reflexivity.
      subst σ'.
      reflexivity.
    }

    specialize (C1 mt mb MT'').
    assert(lookup_Pexp σ' m'' (incrPVar 0 y_p) = Some mb) as MB''.
    {
      subst σ'.
      unfold lookup_Pexp.
      rewrite evalPexp_incrPVar.
      simpl.
      rewrite Heqo1.

      destruct P2 as [_ _ mem_write_safe2].
      apply Option_equiv_eq in E2.
      specialize (mem_write_safe2 _ _ _ _ E2).

      assert(TS: evalPexp (DSHPtrVal t_i :: σ) (PVar 0) = Some t_i)
        by reflexivity.
      specialize (mem_write_safe2 _ TS).

      assert(MB': memory_lookup m' y_i = Some mb).
      {
        rewrite <- MB.
        subst m'.
        unfold memory_lookup, memory_set.
        rewrite NP.F.add_neq_o.
        reflexivity.
        assumption.
      }

      rewrite <- MB'.
      symmetry.
      apply mem_write_safe2.
      auto.
    }

    specialize (C1 MB'').
    rewrite MD, E1 in C1.

    inversion C1 as [C1N | ab bm HC1 HA HB];
      clear C1; rename HC1 into C1;
        subst ab; subst bm.

    assert(MA''': lookup_Pexp σ' m''' (incrPVar 0 y_p) = Some ma).
    {
      subst σ'.
      unfold lookup_Pexp.
      rewrite evalPexp_incrPVar.
      simpl.
      rewrite Heqo1.
      unfold memory_lookup.
      rewrite MA.
      reflexivity.
    }

    assert(PC1: Proper ((=) ==> iff)
                       (λ z : mem_block, SHCOL_DSHCOL_mem_block_equiv mb z md)).
    {
      unfold SHCOL_DSHCOL_mem_block_equiv.
      simpl_relation.
      split.
      -
        intros H4 i.
        specialize (H4 i).
        rewrite <- H1.
        auto.
      -
        intros H4 i.
        specialize (H4 i).
        rewrite H1.
        auto.
    }
    rewrite MA''' in C1.
    inversion C1.
    auto.
  -
    exfalso.
    rename m0 into m''.
    unfold lookup_Pexp in *.
    simpl in MX, MB.
    repeat break_match_hyp; try some_none.
    rename m1 into x_i, m0 into y_i.
    rename Heqo0 into E2, Heqo into E1.
    rewrite evalDSHOperator_estimateFuel_ge in E1 by lia.
    rewrite evalDSHOperator_estimateFuel_ge in E2 by lia.

    assert(t_i ≢ y_i).
    {
      destruct (Nat.eq_dec t_i y_i); auto.
      subst.
      exfalso.
      contradict MB.
      pose proof (memory_lookup_memory_new_is_None m) as F.
      apply is_None_def in F.
      rewrite F.
      some_none.
    }

    assert(t_i ≢ x_i).
    {
      destruct (Nat.eq_dec t_i x_i); auto.
      subst.
      exfalso.
      contradict MX.
      pose proof (memory_lookup_memory_new_is_None m) as F.
      apply is_None_def in F.
      rewrite F.
      some_none.
    }
    assert(mem_block_exists y_i m) as EY.
    {
      apply mem_block_exists_exists_equiv.
      eexists.
      eapply MB.
    }

    assert(mem_block_exists y_i m') as EY'.
    {
      subst m'.
      apply mem_block_exists_memory_set.
      eauto.
    }

    assert(mem_block_exists y_i m'') as EY''.
    {
      destruct P2.
      eapply (mem_stable0  _ m' m'').
      apply Option_equiv_eq in E2.
      eapply E2.
      assumption.
    }

    unfold option_compose in MD.
    destruct (mem_op mop2 mx) as [mt|] eqn:MT; try some_none.

    destruct C2 as [C2].
    specialize (C2 mx (mem_empty)).

    assert(MX': lookup_Pexp σ' m' (incrPVar 0 x_p) = Some mx).
    {
      rewrite Heqσ'.
      unfold lookup_Pexp.
      rewrite evalPexp_incrPVar.
      simpl.
      rewrite Heqo2.
      subst m'.
      unfold memory_lookup, memory_set.
      rewrite NP.F.add_neq_o.
      apply MX.
      auto.
    }
    specialize (C2 MX').

    assert(MT': lookup_Pexp σ' m' (PVar 0) = Some mem_empty).
    {
      rewrite Heqσ'.
      unfold lookup_Pexp.
      subst m'.
      simpl.
      unfold memory_lookup, memory_set.
      rewrite NP.F.add_eq_o; reflexivity.
    }
    specialize (C2 MT').

    rewrite E2 in C2.
    rewrite MT in C2.
    inversion C2; subst a b; clear C2; rename H3 into C2.

    assert(mem_block_exists t_i m') as ET'.
    {
      subst m'.
      apply mem_block_exists_memory_set_eq.
      reflexivity.
    }

    assert(mem_block_exists t_i m'') as ET''.
    {
      destruct P2.
      eapply (mem_stable0  _ m' m'').
      apply Option_equiv_eq in E2.
      eapply E2.
      assumption.
    }

    inversion C2 as [mt' HC2 MT'']; clear C2; rename HC2 into C2.
    symmetry in MT''.

    apply SHCOL_DSHCOL_mem_block_equiv_mem_empty in C2.
    apply Option_equiv_eq in MT''.
    rewrite C2 in MT''.
    clear C2 mt'.

    specialize (C1 m'').
    destruct C1 as [C1].

    1:{
      eapply memory_equiv_except_trans.
      eapply memory_equiv_except_memory_set.
      eapply Heqm'.
      intros.
      destruct P2.
      eapply mem_write_safe0.
      rewrite E2.
      reflexivity.
      subst σ'.
      reflexivity.
    }

    specialize (C1 mt mb MT'').
    assert(lookup_Pexp σ' m'' (incrPVar 0 y_p) = Some mb) as MB''.
    {
      subst σ'.
      unfold lookup_Pexp.
      rewrite evalPexp_incrPVar.
      simpl.
      rewrite Heqo1.

      destruct P2 as [_ _ mem_write_safe2].
      apply Option_equiv_eq in E2.
      specialize (mem_write_safe2 _ _ _ _ E2).

      assert(TS: evalPexp (DSHPtrVal t_i :: σ) (PVar 0) = Some t_i)
        by reflexivity.
      specialize (mem_write_safe2 _ TS).

      assert(MB': memory_lookup m' y_i = Some mb).
      {
        rewrite <- MB.
        subst m'.
        unfold memory_lookup, memory_set.
        rewrite NP.F.add_neq_o.
        reflexivity.
        assumption.
      }

      rewrite <- MB'.
      symmetry.
      apply mem_write_safe2.
      auto.
    }

    specialize (C1 MB'').
    rewrite MD, E1 in C1.

    inversion C1.
  -
    exfalso.
    unfold lookup_Pexp in *.
    simpl in MX, MB.
    repeat break_match_hyp; try some_none.
    rename m1 into x_i, m0 into y_i.
    clear Heqo.
    rename Heqo0 into E2.
    rewrite evalDSHOperator_estimateFuel_ge in E2 by lia.

    assert(t_i ≢ y_i).
    {
      destruct (Nat.eq_dec t_i y_i); auto.
      subst.
      exfalso.
      contradict MB.
      pose proof (memory_lookup_memory_new_is_None m) as F.
      apply is_None_def in F.
      rewrite F.
      some_none.
    }

    assert(t_i ≢ x_i).
    {
      destruct (Nat.eq_dec t_i x_i); auto.
      subst.
      exfalso.
      contradict MX.
      pose proof (memory_lookup_memory_new_is_None m) as F.
      apply is_None_def in F.
      rewrite F.
      some_none.
    }

    unfold memory_lookup, memory_remove.

    assert(mem_block_exists y_i m) as EY.
    {
      apply mem_block_exists_exists_equiv.
      eexists.
      eapply MB.
    }

    assert(mem_block_exists y_i m') as EY'.
    {
      subst m'.
      apply mem_block_exists_memory_set.
      eauto.
    }


    unfold option_compose in MD.
    destruct (mem_op mop2 mx) as [mt|] eqn:MT; try some_none.

    destruct C2 as [C2].
    specialize (C2 mx (mem_empty)).

    assert(MX': lookup_Pexp σ' m' (incrPVar 0 x_p) = Some mx).
    {
      rewrite Heqσ'.
      unfold lookup_Pexp.
      rewrite evalPexp_incrPVar.
      simpl.
      rewrite Heqo2.
      subst m'.
      unfold memory_lookup, memory_set.
      rewrite NP.F.add_neq_o.
      apply MX.
      auto.
    }
    specialize (C2 MX').

    assert(MT': lookup_Pexp σ' m' (PVar 0) = Some mem_empty).
    {
      rewrite Heqσ'.
      unfold lookup_Pexp.
      subst m'.
      simpl.
      unfold memory_lookup, memory_set.
      rewrite NP.F.add_eq_o; reflexivity.
    }
    specialize (C2 MT').

    rewrite E2 in C2.
    rewrite MT in C2.
    inversion C2.
  -
    exfalso.
    rename m1 into m''.
    rename m0 into m'''.
    unfold lookup_Pexp in *.
    simpl in MX, MB.
    repeat break_match_hyp; try some_none.
    rename m1 into x_i, m0 into y_i.
    rename Heqo0 into E2, Heqo into E1.
    rewrite evalDSHOperator_estimateFuel_ge in E1 by lia.
    rewrite evalDSHOperator_estimateFuel_ge in E2 by lia.

    assert(t_i ≢ y_i).
    {
      destruct (Nat.eq_dec t_i y_i); auto.
      subst.
      exfalso.
      contradict MB.
      pose proof (memory_lookup_memory_new_is_None m) as F.
      apply is_None_def in F.
      rewrite F.
      some_none.
    }

    assert(t_i ≢ x_i).
    {
      destruct (Nat.eq_dec t_i x_i); auto.
      subst.
      exfalso.
      contradict MX.
      pose proof (memory_lookup_memory_new_is_None m) as F.
      apply is_None_def in F.
      rewrite F.
      some_none.
    }

    assert(mem_block_exists y_i m) as EY.
    {
      apply mem_block_exists_exists_equiv.
      eexists.
      eapply MB.
    }

    assert(mem_block_exists y_i m') as EY'.
    {
      subst m'.
      apply mem_block_exists_memory_set.
      eauto.
    }

    assert(mem_block_exists y_i m'') as EY''.
    {
      destruct P2.
      eapply (mem_stable0  _ m' m'').
      apply Option_equiv_eq in E2.
      eapply E2.
      assumption.
    }

    assert(mem_block_exists y_i m''') as EY'''.
    {
      destruct P1.
      eapply (mem_stable0  _ m'' m''').
      apply Option_equiv_eq in E1.
      eapply E1.
      assumption.
    }

    destruct (NM.find (elt:=mem_block) y_i m''') as [ma|] eqn:MA .
    2:{
      apply memory_is_set_is_Some, is_Some_ne_None in EY'''.
      unfold memory_lookup in EY'''.
      congruence.
    }

    destruct C2 as [C2].
    specialize (C2 mx (mem_empty)).

    unfold option_compose in MD.

    destruct (mem_op mop2 mx) as [mt|] eqn:MT; try some_none.
    +
      (* mop2 = Some, mop1 = None *)
      assert(MX': lookup_Pexp σ' m' (incrPVar 0 x_p) = Some mx).
      {
        rewrite Heqσ'.
        unfold lookup_Pexp.
        rewrite evalPexp_incrPVar.
        simpl.
        rewrite Heqo2.
        subst m'.
        unfold memory_lookup, memory_set.
        rewrite NP.F.add_neq_o.
        apply MX.
        auto.
      }
      specialize (C2 MX').

      assert(MT': lookup_Pexp σ' m' (PVar 0) = Some mem_empty).
      {
        rewrite Heqσ'.
        unfold lookup_Pexp.
        subst m'.
        simpl.
        unfold memory_lookup, memory_set.
        rewrite NP.F.add_eq_o; reflexivity.
      }
      specialize (C2 MT').

      rewrite E2 in C2.
      inversion C2; subst a b; clear C2; rename H3 into C2.

      assert(mem_block_exists t_i m') as ET'.
      {
        subst m'.
        apply mem_block_exists_memory_set_eq.
        reflexivity.
      }

      assert(mem_block_exists t_i m'') as ET''.
      {
        destruct P2.
        eapply (mem_stable0  _ m' m'').
        apply Option_equiv_eq in E2.
        eapply E2.
        assumption.
      }

      inversion C2 as [mt' HC2 MT'']; clear C2; rename HC2 into C2.
      symmetry in MT''.

      apply SHCOL_DSHCOL_mem_block_equiv_mem_empty in C2.
      apply Option_equiv_eq in MT''.
      rewrite C2 in MT''.
      clear C2 mt'.

      specialize (C1 m'').
      destruct C1 as [C1].

      1:{
        eapply memory_equiv_except_trans.
        eapply memory_equiv_except_memory_set.
        eapply Heqm'.
        intros.
        destruct P2.
        eapply mem_write_safe0.
        rewrite E2.
        reflexivity.
        subst σ'.
        reflexivity.
      }

      specialize (C1 mt mb MT'').
      assert(lookup_Pexp σ' m'' (incrPVar 0 y_p) = Some mb) as MB''.
      {
        subst σ'.
        unfold lookup_Pexp.
        rewrite evalPexp_incrPVar.
        simpl.
        rewrite Heqo1.

        destruct P2 as [_ _ mem_write_safe2].
        apply Option_equiv_eq in E2.
        specialize (mem_write_safe2 _ _ _ _ E2).

        assert(TS: evalPexp (DSHPtrVal t_i :: σ) (PVar 0) = Some t_i)
          by reflexivity.
        specialize (mem_write_safe2 _ TS).

        assert(MB': memory_lookup m' y_i = Some mb).
        {
          rewrite <- MB.
          subst m'.
          unfold memory_lookup, memory_set.
          rewrite NP.F.add_neq_o.
          reflexivity.
          assumption.
        }

        rewrite <- MB'.
        symmetry.
        apply mem_write_safe2.
        auto.
      }

      specialize (C1 MB'').
      rewrite MD, E1 in C1.

      inversion C1.
    +
      (* mop2 = None, no mop1 *)

      assert(MX': lookup_Pexp σ' m' (incrPVar 0 x_p) = Some mx).
      {
        rewrite Heqσ'.
        unfold lookup_Pexp.
        rewrite evalPexp_incrPVar.
        simpl.
        rewrite Heqo2.
        subst m'.
        unfold memory_lookup, memory_set.
        rewrite NP.F.add_neq_o.
        apply MX.
        auto.
      }
      specialize (C2 MX').

      assert(MT': lookup_Pexp σ' m' (PVar 0) = Some mem_empty).
      {
        rewrite Heqσ'.
        unfold lookup_Pexp.
        subst m'.
        simpl.
        unfold memory_lookup, memory_set.
        rewrite NP.F.add_eq_o; reflexivity.
      }
      specialize (C2 MT').

      rewrite E2 in C2.
      inversion C2; subst a b; clear C2; rename H4 into C2.
  -
    constructor.
  -
    constructor.
   *)
Admitted.
