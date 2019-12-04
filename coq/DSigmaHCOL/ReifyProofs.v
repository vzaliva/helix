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
Require Import Helix.MSigmaHCOL.MemSetoid.
Require Import Helix.Tactics.HelixTactics.

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

Class DSHIBinCarrierA (a:AExpr) : Prop :=
  DSHIBinCarrierA_atypesigincl :> AExprTypeSigIncludes a DSHIBinCarrierA_TypeSig.

Class DSHUnCarrierA (a:AExpr) : Prop :=
  DSHUnCarrierA_atypesigincl :> AExprTypeSigIncludes a DSHUnCarrierA_TypeSig.

Class DSHIUnCarrierA (a:AExpr) : Prop :=
  DSHIUnCarrierA_atypesigincl :> AExprTypeSigIncludes a DSHIUnCarrierA_TypeSig.

Class DSHBinCarrierA (a:AExpr) : Prop :=
  DSHBinCarrierA_atypesigincl :> AExprTypeSigIncludes a DSHBinCarrierA_TypeSig.

Lemma evalMExpr_is_Some
      {σ: evalContext}
      {m: MExpr}
      (tm: TypeSig)
      (TS : TypeSigMExpr m = Some tm)
      (TC : typecheck_env 0 tm σ):
  is_Some (evalMexp σ m).
Proof.
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
    some_none.
  -
    solve_proper.
  -
    apply TM.add_1.
    reflexivity.
Qed.

Lemma evalNExpr_is_Some
      {σ: evalContext}
      {n: NExpr}
      (tn: TypeSig)
      (TS : TypeSigNExpr n = Some tn)
      (TC : typecheck_env 0 tn σ):
  is_Some (evalNexp σ n).
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
      break_match; [| trivial].
      inversion H0.
      some_none.
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
    repeat break_match; try some_none.
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
    repeat break_match; try some_none.
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
    repeat break_match; try some_none.
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
    repeat break_match; try some_none.
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
    repeat break_match; try some_none.
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
    repeat break_match; try some_none.
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
    repeat break_match; try some_none.
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
Lemma evalAExpr_is_Some
      {σ: evalContext}
      {e: AExpr}
      (ts: TypeSig)
      (TS : TypeSigAExpr e = Some ts)
      (TC : typecheck_env 0 ts σ):
  is_Some (evalAexp σ e).
Proof.
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
      break_match; [| trivial].
      inversion H0.
      some_none.
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
    break_match.
    +
      break_match.
      *
        break_match;   some_none.
      *
        contradict Heqo2.
        apply is_Some_ne_None.
        eq_to_equiv_hyp.
        eapply evalNExpr_is_Some with (tn0:=tn); eauto.
    +
      contradict Heqo1.
      apply is_Some_ne_None.
      eq_to_equiv_hyp.
      eapply evalMExpr_is_Some with (tm0:=tm); eauto.
  -
    specialize (IHe ts TS TC).
    break_match; some_none.
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
    repeat break_match; try some_none.
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
    repeat break_match; try some_none.
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
    repeat break_match; try some_none.
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
    repeat break_match; try some_none.
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
    repeat break_match; try some_none.
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
    repeat break_match; try some_none.
Qed.

Lemma evalNExpr_context_equiv_at_TypeSig
      (e: NExpr)
      {σ0 σ1: evalContext}
      {ts: TypeSig}
      (TS : TypeSigNExpr e = Some ts)
      (E : context_equiv_at_TypeSig ts σ0 σ1):
  evalNexp σ0 e = evalNexp σ1 e.
Proof.
  copy_apply context_equiv_at_TypeSig_both_typcheck E;
    destruct H as [TC1 TC2].
  (* get rid of errors *)
  apply Equiv_to_opt_r; destruct_opt_r_equiv;
    [ cbv; rename n0 into n1, n into n0
    | pose proof evalNExpr_is_Some ts TS TC2 as C; rewrite Hb in C; inversion C
    | pose proof evalNExpr_is_Some ts TS TC1 as C; rewrite Ha in C; inversion C].
  
  dependent induction e; simpl in *.
  
  (* first "base case" *)
  repeat break_match; try some_none.
  repeat some_inv; subst.
  unfold context_equiv_at_TypeSig in E.
  assert (T : TM.MapsTo v DSHnat ts).
  {
    unfold TypeSig_safe_add in TS.
    repeat break_match; try (rewrite TP.F.empty_o in Heqo1; some_none).
    some_inv; rewrite <-TS.
    apply TM.add_1.
    reflexivity.
  }
  specialize (E v DSHnat T).
  destruct E as [E1 [E2 E3]].
  unfold context_lookup in *.
  rewrite Heqo0, Heqo in E3.
  some_inv.
  inversion E3.
  congruence.
 
  (* second "base case" *)
  congruence.
 
  (* all "inductive cases" are the same *)
  all: repeat break_match; try some_none.
  all: rename n3 into n01, n4 into n02,
              n  into n11, n2 into n12.
  all: cbn in TS; unfold TypeSigUnion_error in TS.
  all: repeat break_match_hyp; try some_none.
  all: repeat some_inv.
  all: rewrite <-TS in *.
  all: assert (n01 = n11)
       by (eapply IHe1;
           [ reflexivity
           | eapply context_equiv_at_TypeSigUnion_left; eauto
           | apply typecheck_env_TypeSigUnion with (t0 := t) (t1 := t0); assumption
           | apply typecheck_env_TypeSigUnion with (t0 := t) (t1 := t0); assumption
           | assumption
           | assumption]).
  all: assert (n02 = n12)
       by (eapply IHe2;
           [ reflexivity
           | eapply context_equiv_at_TypeSigUnion_right; eauto
           | apply typecheck_env_TypeSigUnion with (t0 := t) (t1 := t0); assumption
           | apply typecheck_env_TypeSigUnion with (t0 := t) (t1 := t0); assumption
           | assumption
           | assumption]).
  all: congruence.
Qed.

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

Lemma evalNExpr_context_equiv_at_TypeSig'
      (e : NExpr)
      (ts' ts : TypeSig)
      (σ0 σ1 : evalContext)
      (TSU : TypeSigUnion_error ts' =<< (TypeSigNExpr e) = Some ts)
      (E : context_equiv_at_TypeSig ts σ0 σ1)
  :
    evalNexp σ0 e = evalNexp σ1 e.
Proof.
  unfold TypeSigUnion_error in TSU; cbn in TSU.
  repeat break_match; try some_none.
  some_inv.
  rename Heqo into TS, t0 into Compat; clear Heqd.

  copy_apply context_equiv_at_TypeSig_both_typcheck E;
    destruct H as [TC0 TC1].

  apply Equiv_to_opt_r; destruct_opt_r_equiv.
  -
    cbv; rename n0 into n1, n into n0.
    
    dependent induction e; simpl in *.
    
    (* first "base case" *)
    repeat break_match; try some_none.
    repeat some_inv; subst.
    assert (T : TM.MapsTo v DSHnat ts).
    {
      unfold TypeSig_safe_add in TS.
      repeat break_match; try (rewrite TP.F.empty_o in Heqo1; some_none).
      rewrite <-TSU in *; clear TSU ts.
      some_inv; subst t.
      unfold TypeSigUnion in *.
      apply TP.update_mapsto_iff.
      left.
      apply TM.add_1.
      reflexivity.
    }
    unfold context_equiv_at_TypeSig in E.
    specialize (E v DSHnat T).
    destruct E as [E1 [E2 E3]].
    unfold context_lookup in *.
    rewrite Heqo0, Heqo in E3.
    some_inv.
    inversion E3.
    congruence.
 
    (* second "base case" *)
    congruence.

    (* all "inductive cases" are the same *)
    all: cbn in TS.
    all: repeat break_match; try some_none.
    all: rename n3 into n01, n4 into n02,
                n  into n11, n2 into n12.
    all: rewrite <-TSU in *; clear TSU.
    all: apply Option_equiv_eq in TS.
    all: assert (n01 = n11) by
          (rewrite TypeSigUnion_error_sym in TS;
           unfold TypeSigUnion_error in TS; break_if; try some_none;
           repeat some_inv;
           eapply IHe1;
             [ reflexivity
             | eassumption
             | eassumption
             | eapply context_equiv_at_TypeSigUnion_right; eassumption
             | eapply typecheck_env_TypeSigUnion; eassumption
             | eapply typecheck_env_TypeSigUnion; eassumption
             | assumption
             | assumption ]).
    all: assert (n02 = n12) by
          (unfold TypeSigUnion_error in TS; break_if; try some_none;
           repeat some_inv;
           eapply IHe2;
             [ reflexivity
             | eassumption
             | eassumption
             | eapply context_equiv_at_TypeSigUnion_right; eassumption
             | eapply typecheck_env_TypeSigUnion; eassumption
             | eapply typecheck_env_TypeSigUnion; eassumption
             | assumption
             | assumption ]).
    all: congruence.
  -
    eq_to_equiv_hyp.
    rewrite <-TSU in *.
    contradict Hb.
    apply is_Some_nequiv_None.
    eapply evalNExpr_is_Some.
    eassumption.
    eapply typecheck_env_TypeSigUnion; eassumption.
  -
    eq_to_equiv_hyp.
    rewrite <-TSU in *.
    contradict Ha.
    apply is_Some_nequiv_None.
    eapply evalNExpr_is_Some.
    eassumption.
    eapply typecheck_env_TypeSigUnion; eassumption.
Qed.

Lemma evalMExpr_context_equiv_at_TypeSig
      (e: MExpr)
      {σ0 σ1: evalContext}
      {ts: TypeSig}
      (TS : TypeSigMExpr e = Some ts)
      (E : context_equiv_at_TypeSig ts σ0 σ1):
  evalMexp σ0 e = evalMexp σ1 e.
Proof.
  assert(E':=E).
  apply context_equiv_at_TypeSig_both_typcheck in E'.
  destruct E' as [TC0 TC1].
  apply Equiv_to_opt_r.
  destruct_opt_r_equiv.
  -
    destruct e; simpl in *.
    +
      unfold context_equiv_at_TypeSig in E.
      repeat break_match_hyp; try some_none.
      repeat some_inv; subst.
      rewrite <- TS in TC0.
      rewrite <- TS in TC1.
      unfold typecheck_env, typecheck_env_bool, TP.for_all in *.
      eapply TP.for_all_iff with (k:=v) (e:=DSHMemBlock) in TC0 ;
        eapply TP.for_all_iff with (k:=v) (e:=DSHMemBlock) in TC1 ;
        try solve_proper; try (apply TM.add_1; reflexivity).

      destruct (v <? 0) eqn:K; [inversion K|].
      clear K.
      inversion TC0; clear TC0.
      inversion TC1; clear TC1.
      apply bool_decide_true in H0.
      apply bool_decide_true in H1.
      rewrite Nat.sub_0_r in H0.
      rewrite Nat.sub_0_r in H1.
      unfold contextEnsureType in H0.
      unfold contextEnsureType in H1.
      repeat break_match; try tauto.
      repeat some_inv; subst.

      assert(M: TM.MapsTo v DSHMemBlock ts).
      {
        rewrite <- TS.
        apply TM.add_1.
        reflexivity.
      }
      specialize (E v DSHMemBlock M).
      destruct E as [_ [_ EE]].
      unfold context_lookup in EE.
      rewrite Heqo2, Heqo1 in EE.
      some_inv.
      inversion EE.
      auto.
    +
      apply Some_inj_equiv.
      rewrite <- Ha, <- Hb.
      reflexivity.
  -
    contradict Hb.
    apply is_Some_ne_None.
    eapply evalMExpr_is_Some; eauto.
  -
    contradict Ha.
    apply is_Some_ne_None.
    eapply evalMExpr_is_Some; eauto.
Qed.

Lemma evalAExpr_context_equiv_at_TypeSig
      (e: AExpr)
      {σ0 σ1: evalContext}
      {ts: TypeSig}
      (TS : TypeSigAExpr e = Some ts)
      (E : context_equiv_at_TypeSig ts σ0 σ1):
  evalAexp σ0 e = evalAexp σ1 e.
Proof.
  assert(E':=E).
  apply context_equiv_at_TypeSig_both_typcheck in E'.
  destruct E' as [TC0 TC1].
  apply Equiv_to_opt_r.
  destruct_opt_r_equiv.
  -
    dependent induction e; simpl in *.
    +
      unfold context_equiv_at_TypeSig in E.
      repeat break_match_hyp; try some_none.
      repeat some_inv; subst.
      unfold TypeSig_safe_add in TS.
      rewrite TP.F.empty_o in TS.
      some_inv.
      rewrite <- TS in TC0.
      rewrite <- TS in TC1.
      unfold typecheck_env, typecheck_env_bool, TP.for_all in *.
      eapply TP.for_all_iff with (k:=v) (e:=DSHCType) in TC0 ;
        eapply TP.for_all_iff with (k:=v) (e:=DSHCType) in TC1 ;
        try solve_proper; try (apply TM.add_1; reflexivity).

      destruct (v <? 0) eqn:K; [inversion K|].
      clear K.
      inversion TC0; clear TC0.
      inversion TC1; clear TC1.
      apply bool_decide_true in H0.
      apply bool_decide_true in H1.
      rewrite Nat.sub_0_r in H0.
      rewrite Nat.sub_0_r in H1.
      unfold contextEnsureType in H0.
      unfold contextEnsureType in H1.
      repeat break_match; try tauto.
      repeat some_inv; subst.

      assert(M: TM.MapsTo v DSHCType ts).
      {
        rewrite <- TS.
        apply TM.add_1.
        reflexivity.
      }
      specialize (E v DSHCType M).
      destruct E as [_ [_ EE]].
      unfold context_lookup in EE.
      rewrite Heqo2, Heqo1 in EE.
      some_inv.
      inversion EE.
      auto.
    +
      apply Some_inj_equiv.
      rewrite <- Ha, <- Hb.
      reflexivity.
    +
      eq_to_equiv_hyp.
      unfold TypeSigUnion_error' in TS.
      simpl in TS.
      repeat break_match_hyp; try some_none.
      rename t into mts.
      rename t0 into nts.

      repeat break_match; try some_none.
      *
        eq_to_equiv_hyp.
        rename n0 into n1, n1 into n0.
        assert(NE: n0=n1).
        {
          apply Some_inj_equiv.
          eq_to_equiv_hyp.
          rewrite <- Heqo0, <- Heqo3.
          eapply evalNExpr_context_equiv_at_TypeSig; eauto.
          unfold TypeSigUnion_error in TS.
          break_if; try some_none. clear Heqd.
          apply Some_inj_equiv in TS.
          rewrite <- TS in E.
          apply context_equiv_at_TypeSigUnion_right in E; auto.
        }
        rewrite NE in Heqo3, Heqo4.
        clear NE n0. rename n1 into nv.

        rename m0 into m1, m1 into m0.
        assert(ME: m0=m1).
        {
          apply Some_inj_equiv.
          eq_to_equiv_hyp.
          rewrite <- Heqo2, <- Heqo.
          eapply evalMExpr_context_equiv_at_TypeSig; eauto.
          unfold TypeSigUnion_error in TS.
          break_if; try some_none. clear Heqd.
          apply Some_inj_equiv in TS.
          rewrite <- TS in E.
          apply context_equiv_at_TypeSigUnion_left in E; auto.
        }
        rewrite ME in Heqo2, Heqo4.
        clear ME m0. rename m1 into mv.

        apply Some_inj_equiv.
        rewrite <- Hb, <- Ha.
        rewrite <- Heqo1, <- Heqo4.
        reflexivity.
      *
        exfalso.
        (* TODO: copy-paste from previous goal. refactor! *)
        eq_to_equiv_hyp.
        rename n0 into n1, n1 into n0.
        assert(NE: n0=n1).
        {
          apply Some_inj_equiv.
          eq_to_equiv_hyp.
          rewrite <- Heqo0, <- Heqo3.
          eapply evalNExpr_context_equiv_at_TypeSig; eauto.
          unfold TypeSigUnion_error in TS.
          break_if; try some_none. clear Heqd.
          apply Some_inj_equiv in TS.
          rewrite <- TS in E.
          apply context_equiv_at_TypeSigUnion_right in E; auto.
        }
        rewrite NE in Heqo3, Heqo4.
        clear NE n0. rename n1 into nv.

        rename m0 into m1, m1 into m0.
        assert(ME: m0=m1).
        {
          apply Some_inj_equiv.
          eq_to_equiv_hyp.
          rewrite <- Heqo2, <- Heqo.
          eapply evalMExpr_context_equiv_at_TypeSig; eauto.
          unfold TypeSigUnion_error in TS.
          break_if; try some_none. clear Heqd.
          apply Some_inj_equiv in TS.
          rewrite <- TS in E.
          apply context_equiv_at_TypeSigUnion_left in E; auto.
        }
        rewrite ME in Heqo2, Heqo4.
        clear ME m0. rename m1 into mv.

        some_none.
      *
        exfalso.
        (* TODO: copy-paste from previous goal. refactor! *)
        eq_to_equiv_hyp.
        rename n0 into n1, n1 into n0.
        assert(NE: n0=n1).
        {
          apply Some_inj_equiv.
          eq_to_equiv_hyp.
          rewrite <- Heqo0, <- Heqo3.
          eapply evalNExpr_context_equiv_at_TypeSig; eauto.
          unfold TypeSigUnion_error in TS.
          break_if; try some_none. clear Heqd.
          apply Some_inj_equiv in TS.
          rewrite <- TS in E.
          apply context_equiv_at_TypeSigUnion_right in E; auto.
        }
        rewrite NE in Heqo3, Heqo4.
        clear NE n0. rename n1 into nv.

        rename m0 into m1, m1 into m0.
        assert(ME: m0=m1).
        {
          apply Some_inj_equiv.
          eq_to_equiv_hyp.
          rewrite <- Heqo2, <- Heqo.
          eapply evalMExpr_context_equiv_at_TypeSig; eauto.
          unfold TypeSigUnion_error in TS.
          break_if; try some_none. clear Heqd.
          apply Some_inj_equiv in TS.
          rewrite <- TS in E.
          apply context_equiv_at_TypeSigUnion_left in E; auto.
        }
        rewrite ME in Heqo2, Heqo4.
        clear ME m0. rename m1 into mv.

        some_none.
      *
        eq_to_equiv_hyp.
        rename n0 into n1, n1 into n0.
        assert(NE: n0=n1).
        {
          apply Some_inj_equiv.
          eq_to_equiv_hyp.
          rewrite <- Heqo0, <- Heqo3.
          eapply evalNExpr_context_equiv_at_TypeSig; eauto.
          unfold TypeSigUnion_error in TS.
          break_if; try some_none. clear Heqd.
          apply Some_inj_equiv in TS.
          rewrite <- TS in E.
          apply context_equiv_at_TypeSigUnion_right in E; auto.
        }
        rewrite NE in Heqo3, Heqo4.
        clear NE n0. rename n1 into nv.

        rename m0 into m1, m1 into m0.
        assert(ME: m0=m1).
        {
          apply Some_inj_equiv.
          eq_to_equiv_hyp.
          rewrite <- Heqo2, <- Heqo.
          eapply evalMExpr_context_equiv_at_TypeSig; eauto.
          unfold TypeSigUnion_error in TS.
          break_if; try some_none. clear Heqd.
          apply Some_inj_equiv in TS.
          rewrite <- TS in E.
          apply context_equiv_at_TypeSigUnion_left in E; auto.
        }
        rewrite ME in Heqo2, Heqo4.
        clear ME m0. rename m1 into mv.

        apply Some_inj_equiv.
        rewrite <- Hb, <- Ha.
        reflexivity.
    +
      repeat break_match_hyp; try some_none.
      repeat some_inv.
      subst c c0.
      setoid_replace c2 with c1 by (eapply IHe; eauto).
      reflexivity.
    +
      repeat break_match_hyp; try some_none.
      repeat some_inv.
      subst c c0.

      unfold TypeSigUnion_error' in TS.
      simpl in TS.
      repeat break_match_hyp; try some_none.
      rename t into ts0.
      rename t0 into ts1.

      assert(TS':=TS).
      unfold TypeSigUnion_error in TS.
      break_if; try some_none.
      clear Heqd.
      some_inv.
      rewrite <- TS in E.

      assert(E1: c3=c1).
      {
        eapply IHe1 with (ts:=ts0); eauto.
        -
          apply (context_equiv_at_TypeSigUnion_left t), E.
        -
          eapply TypeSigUnion_error_typecheck_env in TS'.
          eapply TS'.
          eauto.
        -
          eapply TypeSigUnion_error_typecheck_env in TS'.
          eapply TS'.
          eauto.
      }
      assert(E2: c4=c2).
      {
        eapply IHe2 with (ts:=ts1); eauto.
        -
          apply (context_equiv_at_TypeSigUnion_right t), E.
        -
          eapply TypeSigUnion_error_typecheck_env in TS'.
          eapply TS'.
          eauto.
        -
          eapply TypeSigUnion_error_typecheck_env in TS'.
          eapply TS'.
          eauto.
      }
      rewrite E1, E2.
      reflexivity.
    +
      (* TODO: copy-paste from previous branch. Refactor! *)
      repeat break_match_hyp; try some_none.
      repeat some_inv.
      subst c c0.

      unfold TypeSigUnion_error' in TS.
      simpl in TS.
      repeat break_match_hyp; try some_none.
      rename t into ts0.
      rename t0 into ts1.

      assert(TS':=TS).
      unfold TypeSigUnion_error in TS.
      break_if; try some_none.
      clear Heqd.
      some_inv.
      rewrite <- TS in E.

      assert(E1: c3=c1).
      {
        eapply IHe1 with (ts:=ts0); eauto.
        -
          apply (context_equiv_at_TypeSigUnion_left t), E.
        -
          eapply TypeSigUnion_error_typecheck_env in TS'.
          eapply TS'.
          eauto.
        -
          eapply TypeSigUnion_error_typecheck_env in TS'.
          eapply TS'.
          eauto.
      }
      assert(E2: c4=c2).
      {
        eapply IHe2 with (ts:=ts1); eauto.
        -
          apply (context_equiv_at_TypeSigUnion_right t), E.
        -
          eapply TypeSigUnion_error_typecheck_env in TS'.
          eapply TS'.
          eauto.
        -
          eapply TypeSigUnion_error_typecheck_env in TS'.
          eapply TS'.
          eauto.
      }
      rewrite E1, E2.
      reflexivity.
    +
      (* TODO: copy-paste from previous branch. Refactor! *)
      repeat break_match_hyp; try some_none.
      repeat some_inv.
      subst c c0.

      unfold TypeSigUnion_error' in TS.
      simpl in TS.
      repeat break_match_hyp; try some_none.
      rename t into ts0.
      rename t0 into ts1.

      assert(TS':=TS).
      unfold TypeSigUnion_error in TS.
      break_if; try some_none.
      clear Heqd.
      some_inv.
      rewrite <- TS in E.

      assert(E1: c3=c1).
      {
        eapply IHe1 with (ts:=ts0); eauto.
        -
          apply (context_equiv_at_TypeSigUnion_left t), E.
        -
          eapply TypeSigUnion_error_typecheck_env in TS'.
          eapply TS'.
          eauto.
        -
          eapply TypeSigUnion_error_typecheck_env in TS'.
          eapply TS'.
          eauto.
      }
      assert(E2: c4=c2).
      {
        eapply IHe2 with (ts:=ts1); eauto.
        -
          apply (context_equiv_at_TypeSigUnion_right t), E.
        -
          eapply TypeSigUnion_error_typecheck_env in TS'.
          eapply TS'.
          eauto.
        -
          eapply TypeSigUnion_error_typecheck_env in TS'.
          eapply TS'.
          eauto.
      }
      rewrite E1, E2.
      reflexivity.
    +
      (* TODO: copy-paste from previous branch. Refactor! *)
      repeat break_match_hyp; try some_none.
      repeat some_inv.
      subst c c0.

      unfold TypeSigUnion_error' in TS.
      simpl in TS.
      repeat break_match_hyp; try some_none.
      rename t into ts0.
      rename t0 into ts1.

      assert(TS':=TS).
      unfold TypeSigUnion_error in TS.
      break_if; try some_none.
      clear Heqd.
      some_inv.
      rewrite <- TS in E.

      assert(E1: c3=c1).
      {
        eapply IHe1 with (ts:=ts0); eauto.
        -
          apply (context_equiv_at_TypeSigUnion_left t), E.
        -
          eapply TypeSigUnion_error_typecheck_env in TS'.
          eapply TS'.
          eauto.
        -
          eapply TypeSigUnion_error_typecheck_env in TS'.
          eapply TS'.
          eauto.
      }
      assert(E2: c4=c2).
      {
        eapply IHe2 with (ts:=ts1); eauto.
        -
          apply (context_equiv_at_TypeSigUnion_right t), E.
        -
          eapply TypeSigUnion_error_typecheck_env in TS'.
          eapply TS'.
          eauto.
        -
          eapply TypeSigUnion_error_typecheck_env in TS'.
          eapply TS'.
          eauto.
      }
      rewrite E1, E2.
      reflexivity.
    +
      (* TODO: copy-paste from previous branch. Refactor! *)
      repeat break_match_hyp; try some_none.
      repeat some_inv.
      subst c c0.

      unfold TypeSigUnion_error' in TS.
      simpl in TS.
      repeat break_match_hyp; try some_none.
      rename t into ts0.
      rename t0 into ts1.

      assert(TS':=TS).
      unfold TypeSigUnion_error in TS.
      break_if; try some_none.
      clear Heqd.
      some_inv.
      rewrite <- TS in E.

      assert(E1: c3=c1).
      {
        eapply IHe1 with (ts:=ts0); eauto.
        -
          apply (context_equiv_at_TypeSigUnion_left t), E.
        -
          eapply TypeSigUnion_error_typecheck_env in TS'.
          eapply TS'.
          eauto.
        -
          eapply TypeSigUnion_error_typecheck_env in TS'.
          eapply TS'.
          eauto.
      }
      assert(E2: c4=c2).
      {
        eapply IHe2 with (ts:=ts1); eauto.
        -
          apply (context_equiv_at_TypeSigUnion_right t), E.
        -
          eapply TypeSigUnion_error_typecheck_env in TS'.
          eapply TS'.
          eauto.
        -
          eapply TypeSigUnion_error_typecheck_env in TS'.
          eapply TS'.
          eauto.
      }
      rewrite E1, E2.
      reflexivity.
    +
      (* TODO: copy-paste from previous branch. Refactor! *)
      repeat break_match_hyp; try some_none.
      repeat some_inv.
      subst c c0.

      unfold TypeSigUnion_error' in TS.
      simpl in TS.
      repeat break_match_hyp; try some_none.
      rename t into ts0.
      rename t0 into ts1.

      assert(TS':=TS).
      unfold TypeSigUnion_error in TS.
      break_if; try some_none.
      clear Heqd.
      some_inv.
      rewrite <- TS in E.

      assert(E1: c3=c1).
      {
        eapply IHe1 with (ts:=ts0); eauto.
        -
          apply (context_equiv_at_TypeSigUnion_left t), E.
        -
          eapply TypeSigUnion_error_typecheck_env in TS'.
          eapply TS'.
          eauto.
        -
          eapply TypeSigUnion_error_typecheck_env in TS'.
          eapply TS'.
          eauto.
      }
      assert(E2: c4=c2).
      {
        eapply IHe2 with (ts:=ts1); eauto.
        -
          apply (context_equiv_at_TypeSigUnion_right t), E.
        -
          eapply TypeSigUnion_error_typecheck_env in TS'.
          eapply TS'.
          eauto.
        -
          eapply TypeSigUnion_error_typecheck_env in TS'.
          eapply TS'.
          eauto.
      }
      rewrite E1, E2.
      reflexivity.
  -
    contradict Hb.
    apply is_Some_ne_None.
    eapply evalAExpr_is_Some; eauto.
  -
    contradict Ha.
    apply is_Some_ne_None.
    eapply evalAExpr_is_Some; eauto.
Qed.


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

  (* lifting Predicate to option. None is not allowed *)
  Inductive opt_p : (option A) -> Prop :=
  | opt_p_intro : forall x, P x -> opt_p (Some x).

  (* lifting Predicate to option. None is allowed *)
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

Definition lookup_Pexp (σ:evalContext) (m:memory) (p:PExpr) :=
  a <- evalPexp σ p ;;
    memory_lookup m a.

Definition valid_Pexp (σ:evalContext) (m:memory) (p:PExpr) :=
  opt_p (fun k => mem_block_exists k m) (evalPexp σ p).

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
      subst.
      constructor.
      rewrite <- Em.
      apply H1.
    +
      inversion H.
  -
    unfold valid_Pexp in *.
    destruct (evalPexp s1 p1).
    +
      inversion H.
      subst.
      constructor.
      rewrite Em.
      apply H1.
    +
      inversion H.
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
       opt (fun a b => (opt equiv (memory_lookup m0 a) (memory_lookup m1 b)))
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
        evalDSHOperator σ d m fuel = Some m' ->
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
          opt_r
            (blocks_equiv_at_Pexp σ0 σ1 y_p)
            (evalDSHOperator σ0 d m0 fuel)
            (evalDSHOperator σ1 d m1 fuel);

      (* modifies only [y_p], which must be valid in [σ] *)
      mem_write_safe: forall σ m m' fuel,
          evalDSHOperator σ d m fuel = Some m' ->
          (forall y_i , evalPexp σ y_p = Some y_i ->
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
          (lookup_Pexp σ m x_p = Some mx) (* input exists *) ->
          (lookup_Pexp σ m y_p = Some mb) (* output before *) ->

          (hopt_r (fun md (* memory diff *) m' (* memory state after execution *) =>
                     opt_p (fun ma => SHCOL_DSHCOL_mem_block_equiv mb ma md
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
    context_pos_typecheck σ n DSHPtr -> PExpr_typecheck (PVar n) σ
| PConst_tc (σ: evalContext) {a}: PExpr_typecheck (PConst a) σ.

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
        forall nc a b, evalIBinCType σ df (proj1_sig nc) a b = Some (f nc a b)
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
      (E: evalDSHBinOp n off df σ mx mb = Some ma)
      (k: nat)
      (kc:k<n):
  is_Some (mem_lookup k mx) /\ is_Some (mem_lookup (k+off) mx).
Proof.
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
Qed.

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
  evalDSHBinOp n off df σ mx (mem_add k c mb) = Some ma
  → mem_lookup k ma = Some c.
Proof.
  revert mb k kc.
  induction n; intros mb k kc E.
  -
    simpl in *.
    some_inv.
    unfold mem_lookup, mem_add in *.
    rewrite <- E.
    apply Option_equiv_eq.
    apply NP.F.add_eq_o.
    reflexivity.
  -
    simpl in E.
    repeat break_match_hyp; try some_none.
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
  (evalDSHBinOp n off df σ mx mb = Some ma) ->
  (mem_lookup k ma = evalIBinCType σ df k a b).
Proof.
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
Qed.

Lemma evalDSHBinOp_oob_preservation
      {n off: nat}
      {df : AExpr}
      `{dft : DSHIBinCarrierA df}
      {σ : evalContext}
      {mx mb ma : mem_block}
      (ME: evalDSHBinOp n off df σ mx mb = Some ma):
  ∀ (k : NM.key) (kc:k>=n), mem_lookup k mb = mem_lookup k ma.
Proof.
  intros k kc.
  revert mb ME.
  induction n; intros.
  -
    inversion kc; simpl in ME; some_inv; rewrite ME; reflexivity.
  -
    simpl in *.
    repeat break_match_hyp; try some_none.
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
Lemma evalDSHBinOp_equiv_Some_spec
      {off n: nat}
      {df : AExpr}
      `{dft : DSHIBinCarrierA df}
      {σ : evalContext}
      {mx mb ma : mem_block}:
  (evalDSHBinOp n off df σ mx mb = Some ma)
  ->
  (∀ k (kc: k < n),
      ∃ a b,
        (mem_lookup k mx = Some a /\
         mem_lookup (k+off) mx = Some b /\
         (exists c,
             mem_lookup k ma = Some c /\
             evalIBinCType σ df k a b = Some c))
  ).
Proof.
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
Qed.

(* TODO: generalize this *)
Lemma is_Some_evalDSHBinOp_mem_equiv
      (n off : nat)
      (df : AExpr)
      (σ : evalContext)
      (mx ma mb : mem_block) :
  ma = mb ->
  is_Some (evalDSHBinOp n off df σ mx ma) =
  is_Some (evalDSHBinOp n off df σ mx mb).
Proof.
  intros.
  pose proof evalDSHBinOp_proper n off df σ mx mx.
  unfold Proper, respectful in H0.
  assert (T : mx = mx) by reflexivity;
    specialize (H0 T ma mb H); clear T.
  unfold is_Some.
  repeat break_match; try reflexivity; inversion H0.
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

Lemma is_Some_evalDSHBinOp_mem_add
      (n off : nat)
      (df : AExpr)
      (σ : evalContext)
      (mx mb : mem_block)
      (k : NM.key)
      (v : CarrierA) :
  is_Some (evalDSHBinOp n off df σ mx (mem_add k v mb)) =
  is_Some (evalDSHBinOp n off df σ mx mb).
Proof.
  dependent induction n; [reflexivity |].
  cbn.
  repeat break_match; try reflexivity.
  destruct (Nat.eq_dec n k).
  -
    subst.
    apply is_Some_evalDSHBinOp_mem_equiv.
    apply mem_add_overwrite.
  -
    rewrite is_Some_evalDSHBinOp_mem_equiv
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
  (exists a b, is_Some (evalIBinCType σ df n a b)) ->
  forall c d, is_Some (evalIBinCType σ df n c d).
Proof.
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
Qed.

Lemma evalDSHBinOp_is_Some_inv
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
         is_Some (evalIBinCType σ df k a b)
        )
  ) -> (is_Some (evalDSHBinOp n off df σ mx mb)).
Proof.
  intros H.
  induction n; [reflexivity |].
  simpl.
  repeat break_match.
  -
    rewrite is_Some_evalDSHBinOp_mem_add.
    apply IHn.
    intros.
    apply H.
    omega.
  -
    contradict Heqo1.
    apply is_Some_ne_None.
    assert (T : n < S n) by omega.
    specialize (H n T).
    apply evalIBinCarrierA_value_independent.
    destruct H as [a [b H]].
    exists a, b.
    apply H.
  -
    contradict Heqo0.
    apply is_Some_ne_None.
    assert (T : n < S n) by omega.
    specialize (H n T).
    destruct H as [a [b [L1 [L2 S]]]].
    unfold is_Some; break_match; [trivial | some_none].
  -
    contradict Heqo.
    apply is_Some_ne_None.
    assert (T : n < S n) by omega.
    specialize (H n T).
    destruct H as [a [b [L1 [L2 S]]]].
    unfold is_Some; break_match; [trivial | some_none].
Qed.

Lemma evalDSHBinOp_is_None
      (off n: nat)
      (nz: n≢0)
      (df : AExpr)
      `{dft : DSHIBinCarrierA df}
      (σ : evalContext)
      (mx mb : mem_block):
  (exists k (kc:k<n),
      is_None (mem_lookup k mx) \/ is_None (mem_lookup (k+off) mx))
  ->
  is_None (evalDSHBinOp n off df σ mx mb).
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

(* This is an inverse of [evalDSHBinOp_is_None] but it takes
   additional assumption [typecheck_env].

   Basically, it states that in valid environment, the only reason for
   [evalDSHBinOp] to fail is missing data in memory.
 *)
Lemma evalDSHBinOp_is_None_inv
      (off n: nat)
      (df : AExpr)
      `{dft : DSHIBinCarrierA df}
      (σ : evalContext)
      {dfs:TypeSig}
      (TS : TypeSigAExpr df = Some dfs)
      (TC: typecheck_env 3 dfs σ)
      (mx mb : mem_block):
  is_None (evalDSHBinOp n off df σ mx mb) ->
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
      specialize (IHn _ N).
      destruct IHn as [k [kc IHn]].
      exists k.
      assert(k<S n) as kc1 by lia.
      exists kc1.
      apply IHn.
    +
      clear N.
      contradict Heqo1.
      apply is_Some_ne_None.
      unfold evalIBinCType.
      eapply evalAExpr_is_Some.
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
      apply is_None_def in Heqo0.
      exists n.
      eexists. lia.
      auto.
    +
      apply is_None_def in Heqo.
      exists n.
      eexists. lia.
      auto.
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
  destruct_opt_r_equiv.
  -
    destruct n.
    +
      simpl in *.
      repeat some_inv.
      subst.
      reflexivity.
    +
      rename m0 into x, m1 into y.
      rename m into m0, m2 into m1.
      intros k.

      opt_hyp_to_equiv.
      destruct (Nat.lt_decidable k (S n)) as [kc|kc].
      *
        eapply evalDSHBinOp_equiv_Some_spec in Ha; eauto.
        eapply evalDSHBinOp_equiv_Some_spec in Hb; eauto.

        destruct Ha as [a0 [b0 [A0 [B0 [c0 [C0 E0]]]]]].
        destruct Hb as [a1 [b1 [A1 [B1 [c1 [C1 E1]]]]]].

        rewrite A0 in A1; clear A0.
        rewrite B0 in B1; clear B0.
        repeat some_inv.
        rewrite A1, B1 in E0; clear A1 B1 a0 b0.
        rewrite C0, C1, <- E0, <- E1; clear C0 C1 E0 E1 c0 c1.
        rename a1 into a, b1 into b.
        unfold evalIBinCType in *.

        apply evalAExpr_context_equiv_at_TypeSig with (ts:=dfs).
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
  -
    destruct n.
    +
      simpl in Hb.
      some_none.
    +
      opt_hyp_to_equiv.
      apply is_None_equiv_def in Hb; try typeclasses eauto.

      eapply evalDSHBinOp_is_None_inv in Hb; eauto.
      2:{
        eapply context_equiv_at_TypeSig_off_both_typcheck in E.
        eapply E.
      }
      apply equiv_Some_is_Some in Ha.
      apply evalDSHBinOp_is_None with (df:=df) (σ:=σ0) (mb:=m1) in Hb.
      some_none.
      auto.
      apply dft.
  -
    destruct n.
    +
      simpl in Ha.
      some_none.
    +
      opt_hyp_to_equiv.
      apply is_None_equiv_def in Ha; try typeclasses eauto.
      eapply evalDSHBinOp_is_None_inv in Ha; eauto.
      2:{ eapply context_equiv_at_TypeSig_off_both_typcheck in E.
          eapply E.
      }
      apply equiv_Some_is_Some in Hb.

      apply evalDSHBinOp_is_None with (df:=df) (σ:=σ1) (mb:=m1) in Ha.
      some_none.
      auto.
      auto.
Qed.
 
Global Instance Assign_DSH_pure
       (x_n y_n : NExpr)
       (x_p y_p : PExpr)
       (tm : TypeSig)
       (TM : TypeSigNExpr x_n = Some tm /\ TypeSigNExpr y_n = Some tm)
  :
    DSH_pure (DSHAssign (x_p, x_n) (y_p, y_n)) tm x_p y_p.
Proof.
  split.
  -
    intros.
    destruct fuel; [inversion H |].
    cbn in H.
    repeat break_match; try some_none.
    some_inv; rewrite <-H.
    split; intros.
    +
      apply mem_block_exists_memory_set; assumption.
    +
      apply mem_block_exists_memory_set_inv in H0.
      destruct H0; [assumption |].
      subst.
      apply memory_is_set_is_Some.
      rewrite Heqo2.
      reflexivity.
  -
    intros until fuel; intros CE BEx BEy.
    destruct (evalDSHOperator σ0) eqn:OE1,
             (evalDSHOperator σ1) eqn:OE2.
    all: try constructor.
    2,3: exfalso.
    +
      destruct fuel; [inversion OE1|].
      unfold blocks_equiv_at_Pexp in *.
      inversion BEx; clear BEx; inversion H1; clear H1.
      inversion BEy; clear BEy; inversion H6; clear H6.
      cbn in OE1, OE2.
      rewrite <-H, <-H0, <-H1, <-H2, <-H3, <-H5, <-H7, <-H8 in *.
      rename H4 into XY0, H9 into XY2.
      clear - TM CE OE1 OE2 XY0 XY2.
      move OE1 before OE2; move CE before OE1.
      constructor.
      rename m into rm0, m2 into rm1.

      repeat break_match; try some_none.
      repeat some_inv.
      clear H0 H1.
      rename n1 into xn0, n2 into yn0,
             n  into xn1, n0 into yn1.

      unfold memory_lookup, memory_set.
      repeat (rewrite NP.F.add_eq_o by reflexivity).
      constructor.
      
      unfold mem_add, equiv, mem_block_Equiv.
      intros.
      destruct (Nat.eq_dec yn0 k), (Nat.eq_dec yn1 k);
        try (rewrite NP.F.add_eq_o with (x := yn0) by assumption);
        try (rewrite NP.F.add_eq_o with (x := yn1) by assumption);
        try (rewrite NP.F.add_neq_o with (x := yn0) by assumption);
        try (rewrite NP.F.add_neq_o with (x := yn1) by assumption).
      *
        rewrite <-Heqo1, <-Heqo4.
        rewrite XY0.
        pose proof evalNExpr_context_equiv_at_TypeSig.

(*
        Search evalNexp.
        specialize (H x_n σ0 σ1 tm TM CE).
        rewrite Heqo2, Heqo in H.
        some_inv.
        inversion H; subst.
        reflexivity.
      *
*)
        
Admitted.

Global Instance BinOp_DSH_pure
       (o : nat)
       (x_p y_p : PExpr)
       (df: AExpr)
       `{dft : DSHIBinCarrierA df}
       {dfs: TypeSig}
       {DTS: TypeSigAExpr df = Some dfs}
  :
    DSH_pure (DSHBinOp o x_p y_p df) (TypeSig_decr_n dfs 3) x_p y_p.
Proof.
  split.
  -
    (* mem_stable *)
    intros σ m m' fuel E k.
    split; intros H.
    +
      destruct fuel; simpl in E.
      *
        some_none.
      *
        repeat break_match; try some_none.
        rename m0 into x_i, m1 into y_i.
        rename m2 into mx, m3 into my.
        rename m4 into mxy.
        some_inv.
        rewrite <- E; clear E.
        destruct (Nat.eq_dec k y_i) as [kc | kc].
        --
          subst k.
          apply mem_block_exists_memory_set_eq.
          reflexivity.
        --
          apply mem_block_exists_memory_set.
          apply H.
    +
      destruct fuel; simpl in E.
      *
        some_none.
      *
        repeat break_match; try some_none.
        rename m0 into x_i, m1 into y_i.
        rename m2 into mx, m3 into my.
        rename m4 into mxy.
        some_inv.
        rewrite <- E in H; clear E.
        destruct (Nat.eq_dec k y_i) as [kc | kc].
        --
          subst k.
          apply mem_block_exists_memory_set_inv in H.
          destruct H.
          ++ auto.
          ++
            apply memory_is_set_is_Some.
            apply eq_Some_is_Some in Heqo3.
            assumption.
        --
          apply mem_block_exists_memory_set_neq in H; auto.
  -
    (* mem_read_safe *)
    intros σ0 σ1 m0 m1 fuel TE EX EY.
    destruct fuel; try constructor.

    unfold blocks_equiv_at_Pexp in EX, EY.

    destruct (evalPexp σ0 x_p) eqn:P0X, (evalPexp σ1 x_p) eqn:P1X; try inversion EX.
    destruct (evalPexp σ0 y_p) eqn:P0Y, (evalPexp σ1 y_p) eqn:P1Y; try inversion EY.
    rename m into x0_i, m2 into x1_i, m3 into y0_i, m4 into y1_i.
    clear EX EY.
    subst x y x0 y0.

    inversion H1; clear H1.
    inversion H4; clear H4.
    symmetry_option_hyp.
    rename x into x0, y into x1, x0 into y0, y0 into y1.
    rename H into LX0, H0 into LX1, H1 into LY0, H3 into LY1.

    simpl.
    unfold blocks_equiv_at_Pexp.
    rewrite P0X, P1X, P0Y, P1Y.
    rewrite LX0, LX1, LY0, LY1.
    repeat break_match.
    +
      constructor.
      rename m into m0', m2 into m1'.
      constructor.
      unfold memory_lookup, memory_set.
      rewrite 2!NP.F.add_eq_o by reflexivity.
      eq_to_equiv_hyp.
      rewrite H2, H5 in Heqo0.
      constructor.
      apply Some_inj_equiv.
      rewrite <- Heqo0, <- Heqo1.
      eapply evalDSHBinOp_context_equiv; eauto.
      apply context_equiv_at_TypeSig_off_decr.
      auto.
    +
      exfalso.
      eq_to_equiv_hyp.
      rewrite H2, H5 in Heqo0.
      erewrite evalDSHBinOp_context_equiv with (σ1:=σ1) in Heqo0; try eauto.
      some_none.
      apply context_equiv_at_TypeSig_off_decr.
      auto.
    +
      exfalso.
      eq_to_equiv_hyp.
      rewrite H2, H5 in Heqo0.
      erewrite evalDSHBinOp_context_equiv with (σ1:=σ1) in Heqo0; try eauto.
      some_none.
      apply context_equiv_at_TypeSig_off_decr.
      auto.
    +
      constructor.
  -
    (* mem_write_safe *)
    intros σ m m' fuel E y_i P.
    destruct fuel; simpl in E; [some_none|].

    repeat break_match; try some_none.
    repeat some_inv.
    opt_hyp_to_equiv.
    rewrite P in Heqo1, Heqo3, E.
    clear P m1.
    rename m0 into x_i, m2 into x, m3 into y, m4 into y'.

    intros k NKY.
    rewrite <- E.
    clear E m'.
    unfold memory_lookup, memory_set in *.
    rewrite NP.F.add_neq_o by auto.
    reflexivity.
Qed.

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

      eapply evalDSHBinOp_is_Some_inv; try eauto.
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

        apply evalDSHBinOp_is_None; try typeclasses eauto.
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
Qed.

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
      (NY0: evalPexp σ0 y_p ≢ Some t0_i)
      (NY1: evalPexp σ1 y_p ≢ Some t1_i):
  blocks_equiv_at_Pexp σ0 σ1 y_p m0'' m1''
  → blocks_equiv_at_Pexp σ0 σ1 y_p (memory_remove m0'' t0_i) (memory_remove m1'' t1_i).
Proof.
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
Qed.

Lemma blocks_equiv_at_Pexp_add_mem
      (p : PExpr)
      (σ0 σ1 : evalContext)
      (m0 m1 : memory)
      (t0 t1 : mem_block_id)
      (foo0 foo1: mem_block)
  :
    evalPexp σ0 p ≢ Some t0 ->
    evalPexp σ1 p ≢ Some t1 ->
    blocks_equiv_at_Pexp σ0 σ1 p m0 m1 ->
    blocks_equiv_at_Pexp σ0 σ1 p
                         (memory_set m0 t0 foo0)
                         (memory_set m1 t1 foo1).
Proof.
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
Qed.

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
Qed.

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
Qed.

(*
  (* High-level equivalence *)
  Instance dynwin_SHCOL_DSHCOL
           (a: vector CarrierA 3):
    @SHCOL_DSHCOL_equiv _ _ _ _ (dynwin_SHCOL1 a) _
                        (DynWinSigmaHCOL1_Mem a)
                        dynwin_DSHCOL1
                        [DSHvecVal a]
                        (* assuming reification uses [x_i=0] and [y_i=1] *)
                        (NM.add 1 mem_empty
                                (NM.add 0 mem_empty (NM.empty mem_block)))
                        0 1.
  Proof.
    unfold dynwin_DSHCOL1, dynwin_SHCOL1.
    unfold DynWinSigmaHCOL1_Mem, DynWinSigmaHCOL1_Facts.

    (* Normalize by unfolding [@zero] instances: *)
    unfold zero in *.
    (* Normalize dimensionality in DHSCOL. Due to refication,
       for example [o2:=1+1] in SHCOL is replaced with [2] in DHSCOL: *)
    (* simpl in *. *)


    Typeclasses eauto := 1.
    unfold In.
    eapply SHCompose_SHCOL_DSHCOL.
    eapply SafeCast_SHCOL_DSHCOL.


    match goal with
    | [|-  SHCOL_DSHCOL_equiv
            (facts:=?facts)
            (SHCompose ?fm ?op1 ?op2 (o2:=?o2))
            (DSHSeq (DSHAlloc ?o2 ?t_i) (DSHSeq ?d1 ?d2))
            ?σ ?m ?x_i ?y_i] =>
      unshelve eapply (SHCompose_SHCOL_DSHCOL 0 1
                                     (fm:=fm)
                                     (op1:=op1)
                                     (op2:=op2)
                                     (m:=m)
                                     (d1:=d1)
                                     (d2:=d2)
                                     (t_i:=t_i)
                                     (σ:=σ)
                                     (facts:=facts)

             )

    end.


    apply SafeCast_SHCOL_DSHCOL.
  Qed.



     "@SHCOL_DSHCOL_equiv (1 + (2 + 2)) 1 0 Monoid_RthetaFlags
    (?op1 ⊚ ?op2) ?facts
    (@SHCompose_Mem Monoid_RthetaFlags 0 (1 + (2 + 2)) ?o2 1
       ?op1 ?op2 ?compat ?facts1 ?Meq1 ?facts2 ?Meq2 ?facts)
    (DSHAlloc ?o2 ?t_i; ?d1; ?d2) [@DSHvecVal 3 a] ?m 0 1" with

    eapply (SHCompose_SHCOL_DSHCOL 0 1
                                   (i1:=1 + (2 + 2))
                                   (o3:=1)
                                   (svalue:=zero)
                                   (fm:=Monoid_RthetaFlags)
                                   (σ:=[DSHvecVal a])
           ).
    apply SafeCast_SHCOL_DSHCOL.
  Qed.

 *)

(* Heterogenous relation of semantic equivalence of structurally correct SHCOL and DSHCOL operators *)

(*
Open Scope list_scope.
Definition SHCOL_DSHCOL_equiv {i o:nat} {svalue:CarrierA} {fm}
           (σ: evalContext)
           (s: @SHOperator fm i o svalue)
           `{facts: !SHOperator_Facts fm s}
           `{SHM: !SHOperator_Mem  s}
           (d: DSHOperator) (x_i y_i: nat): Prop
  := forall (Γ: evalContext) (x:svector fm i),

    let Γ := σ ++ in

    (List.nth_error Γ' x_i = Some (svector_to_mem_block x)) ->
    match evalDSHOperator Γ' d (estimateFuel d), mem_op xm with
    | Some Γ', Some ym' => match List.nth_error Γ' y_i with
                          | Some (DSHmemVal ym) => ym' = ym
                          | _ => False
                          end.


    let xm := svector_to_mem_block x in (* input as mem_block *)
    let ym := mem_empty in (* placeholder for output *)
    let x_i := List.length (σ ++ Γ) in
    let y_i := x_i + 1 in
    let Γ := σ ++ Γ ++ [DSHmemVal xm ; DSHmemVal ym]  in (* add them to context *)
    let fuel := estimateFuel d in
    match evalDSHOperator Γ d fuel, mem_op xm with
    | Some Γ', Some ym' => match List.nth_error Γ' y_i with
                          | Some (DSHmemVal ym) => ym' = ym
                          | _ => False
                          end
    | None, None  => True
    | _, _ => False
    end.
 *)

(*
Theorem SHCompose_DSHCompose
        {i1 o2 o3} {svalue} {fm}
        (σ: evalContext)
        (f: @SHOperator fm o2 o3 svalue)
        (g: @SHOperator fm i1 o2 svalue)
        (df: DSHOperator o2 o3)
        (dg: DSHOperator i1 o2)
  :
    SHCOL_DSHCOL_equiv σ f df ->
    SHCOL_DSHCOL_equiv σ g dg ->
    SHCOL_DSHCOL_equiv σ
                       (SHCompose fm f g)
                       (DSHCompose df dg).
Proof.
  intros Ef Eg.
  intros Γ x.
  simpl.
  break_match.
  -
    unfold compose.
    specialize (Eg Γ x).
    specialize (Ef Γ (op fm g x)).
    rewrite Ef.
    apply evalDSHOperator_arg_proper.
    apply Some_inj_equiv.
    rewrite <- Heqo.
    apply Eg.
  -
    specialize (Eg Γ x).
    rewrite Heqo in Eg.
    some_none.
Qed.

Theorem SHCOL_DSHCOL_equiv_SafeCast
        {i o: nat}
        {svalue: CarrierA}
        (σ: evalContext)
        (s: @SHOperator Monoid_RthetaSafeFlags i o svalue)
        (d: DSHOperator i o):
  SHCOL_DSHCOL_equiv σ s d ->
  SHCOL_DSHCOL_equiv σ (TSigmaHCOL.SafeCast s) d.
Proof.
  intros P.
  intros Γ x.
  specialize (P Γ (rvector2rsvector _ x)).
  rewrite densify_rvector2rsvector_eq_densify in P.
  rewrite <- P. clear P.
  simpl.
  f_equiv.
  unfold densify.
  unfold equiv, vec_Equiv.
  apply Vforall2_intro_nth.
  intros j jc.
  rewrite 2!Vnth_map.
  unfold SafeCast', compose, rsvector2rvector, rvector2rsvector.
  rewrite Vnth_map.
  unfold RStheta2Rtheta, Rtheta2RStheta.
  reflexivity.
Qed.

Theorem SHCOL_DSHCOL_equiv_UnSafeCast
        {i o: nat}
        {svalue: CarrierA}
        (σ: evalContext)
        (s: @SHOperator Monoid_RthetaFlags i o svalue)
        (d: DSHOperator i o):
  SHCOL_DSHCOL_equiv σ s d ->
  SHCOL_DSHCOL_equiv σ (TSigmaHCOL.UnSafeCast s) d.
Proof.
  intros P.
  intros Γ x.
  specialize (P Γ (rsvector2rvector _ x)).
  rewrite densify_rsvector2rvector_eq_densify in P.
  rewrite <- P. clear P.
  simpl.
  f_equiv.
  unfold densify.
  unfold equiv, vec_Equiv.
  apply Vforall2_intro_nth.
  intros j jc.
  rewrite 2!Vnth_map.
  unfold UnSafeCast', compose, rsvector2rvector, rvector2rsvector.
  rewrite Vnth_map.
  unfold RStheta2Rtheta, Rtheta2RStheta.
  reflexivity.
Qed.

Theorem SHBinOp_DSHBinOp
        {o: nat}
        {svalue: CarrierA}
        {fm}
        (σ: evalContext)
        (f: FinNat o -> CarrierA -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
        (df: DSHIBinCarrierA)
  :
    (forall (Γ: evalContext) j a b, Some (f j a b) = evalIBinCType
                                                       (σ ++ Γ)
                                                       df (proj1_sig j) a b) ->
    @SHCOL_DSHCOL_equiv (o+o) o svalue fm σ
                        (@SHBinOp fm svalue o f pF)
                        (DSHBinOp df).
Proof.
  intros H.
  intros Γ x.
  simpl.
  unfold evalDSHBinOp.
  unfold SHBinOp_impl.
  break_let.
  rename t into x0, t0 into x1.

  unfold densify.
  rewrite Vmap_Vbuild.

  break_let.
  unfold vector2pair in *.

  apply Vbreak_arg_app in Heqp.
  subst x.
  rewrite Vmap_app in Heqp0.
  apply Vbreak_arg_app in Heqp0.
  apply Vapp_eq in Heqp0.
  destruct Heqp0 as [H0 H1].
  subst t. subst t0.
  setoid_rewrite Vnth_map.

  symmetry.
  apply vsequence_Vbuild_equiv_Some.
  rewrite Vmap_Vbuild with (fm:=Some).

  vec_index_equiv j jc.
  rewrite 2!Vbuild_nth.
  rewrite evalWriter_Rtheta_liftM2.
  symmetry.
  specialize (H Γ (mkFinNat jc)).
  rewrite H.
  reflexivity.
Qed.

Theorem HTSUMUnion_DSHHTSUMUnion
        {i o: nat}
        {svalue: CarrierA}
        {fm}
        (dot: CarrierA -> CarrierA -> CarrierA)
        `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
        `{scompat: BFixpoint svalue dot}
        (ddot: DSHBinCarrierA)
        (σ: evalContext)
        (f g: @SHOperator fm i o svalue)
        (df dg: DSHOperator i o)
  :
    SHCOL_DSHCOL_equiv σ f df ->
    SHCOL_DSHCOL_equiv σ g dg ->
    (forall (Γ:evalContext) a b, Some (dot a b) = evalBinCarrierA (σ++Γ) ddot a b) ->
    SHCOL_DSHCOL_equiv σ
                       (@HTSUMUnion fm i o svalue dot dot_mor scompat f g)
                       (DSHHTSUMUnion ddot df dg).
Proof.
  intros Ef Eg Edot.
  intros Γ x.
  specialize (Ef Γ).
  specialize (Eg Γ).
  specialize (Edot Γ).
  simpl.
  repeat break_match.
  -
    rewrite Vmap2_as_Vbuild.
    symmetry.
    apply vsequence_Vbuild_equiv_Some.
    unfold HTSUMUnion', Vec2Union.
    unfold densify.
    rewrite Vmap_map.
    rewrite Vmap2_as_Vbuild.
    rewrite Vmap_Vbuild.
    unfold Union.

    vec_index_equiv j jc.
    rewrite 2!Vbuild_nth.
    rewrite evalWriter_Rtheta_liftM2.
    symmetry.

    specialize (Ef x). specialize (Eg x).
    rewrite Heqo0 in Ef; clear Heqo0; some_inv.
    rewrite Heqo1 in Eg; clear Heqo1; some_inv.
    rewrite Edot; clear Edot.
    apply evalBinCarrierA_proper; try reflexivity.

    apply Vnth_arg_equiv with (ip:=jc) in Ef.
    rewrite <- Ef.
    unfold densify.
    rewrite Vnth_map.
    reflexivity.

    apply Vnth_arg_equiv with (ip:=jc) in Eg.
    rewrite <- Eg.
    unfold densify.
    rewrite Vnth_map.
    reflexivity.
  -
    specialize (Eg x).
    rewrite Heqo1 in Eg.
    some_none.
  -
    specialize (Ef x).
    rewrite Heqo0 in Ef.
    some_none.
Qed.

Theorem Pick_DSHPick
        {fm}
        (σ: evalContext)
        {o b:nat}
        (bc: b < o)
        (svalue: CarrierA)
        (db: NExpr)
  :
    (forall Γ, Some b = evalNexp (σ++Γ) db) ->
    SHCOL_DSHCOL_equiv σ (svalue:=svalue)
                       (Pick fm bc)
                       (DSHPick db svalue).
Proof.
  intros H.
  intros Γ x.
  specialize (H Γ).
  simpl.
  break_match; try some_none.
  break_match; some_inv; repeat nat_equiv_to_eq; subst n.
  -
    f_equiv.
    unfold unLiftM_HOperator', compose.
    vec_index_equiv j jc.
    unfold densify, sparsify.
    repeat rewrite Vnth_map.
    rewrite Vmap_map.

    apply castWriter_equiv.
    unfold Pick_impl.
    repeat rewrite Vbuild_nth.
    break_if.
    +
      subst.
      rewrite Vhead_Vmap.
      apply castWriter_mkValue_evalWriter.
    +
      apply castWriter_mkStruct.
  -
    destruct n0; auto.
Qed.

 *)

(*
Definition SHOperatorFamily_DSHCOL_equiv
           {i o n:nat}
           {svalue: CarrierA}
           {fm}
           (Γ: evalContext)
           (op_family: @SHOperatorFamily fm i o n svalue)
           {op_family_facts: forall j (jc:j<n), SHOperator_Facts fm (op_family (mkFinNat jc))}
           (op_family_mem: forall j (jc:j<n), SHOperator_Mem (op_family (mkFinNat jc)))
           (d: DSHOperator) : Prop :=
  forall (j:nat) (jc:j<n), SHCOL_DSHCOL_equiv (DSHnatVal j :: Γ)
                                       (op_family (mkFinNat jc))
                                       d.
 *)

(*
Section Expr_NVar_subst_S.

  Local Ltac twoarg := simpl;
                       repeat break_match; auto; try some_none;
                       f_equiv;
                       repeat some_inv;
                       crush.

  Fact NExpr_NVar_subst_S
       (Γ Γs: evalContext)
       (pos: nat)
       (exp : NExpr)
       (j : nat):
    listsDiffByOneElement Γ Γs pos ->
    isNth Γ pos (DSHnatVal j) ->
    isNth Γs pos (DSHnatVal (S j)) ->
    evalNexp Γs exp =
    evalNexp Γ (NExpr_var_subst pos (NPlus (NVar pos) (NConst 1)) exp).
  Proof.
    intros H H0 H1.
    induction exp.
    -
      simpl.
      unfold listsDiffByOneElement, isNth in *.
      break_if.
      +
        (* accessing variable at pos *)
        subst n.
        simpl.
        destruct (nth_error Γs pos); try contradiction.
        destruct (nth_error Γ pos); try contradiction.
        clear H.
        rename d0 into a, d into b.
        simpl.
        repeat break_match ; subst; try reflexivity; try some_none.
        *
          some_inv.
          inversion H0. inversion H1. subst.
          f_equiv.
          repeat nat_equiv_to_eq; subst.
          apply peano_naturals.S_nat_plus_1.
        * inversion H0.
        * inversion H0.
        * inversion H1.
        * inversion H1.
      +
        (* accessing some other variable *)
        clear H0 H1.
        simpl.
        specialize (H n n0).
        inversion H.
        reflexivity.
        inversion H2; try reflexivity.
        f_equiv.
        symmetry.
        apply H3.
    -
      reflexivity.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
  Qed.

  Fact VExpr_NVar_subst_S
       {d: nat}
       (Γ Γs: evalContext)
       (pos: nat)
       (exp : VExpr d)
       (j : nat):
    listsDiffByOneElement Γ Γs pos ->
    isNth Γ pos (DSHnatVal j) ->
    isNth Γs pos (DSHnatVal (S j)) ->
    evalVexp Γs exp =
    evalVexp Γ (VExpr_natvar_subst pos (NPlus (NVar pos) (NConst 1)) exp).
  Proof.
    intros H H0 H1.
    induction exp.
    -
      simpl.
      unfold listsDiffByOneElement, isNth in *.
      destruct (PeanoNat.Nat.eq_dec n0 pos).
      +
        (* accessing variable at pos *)
        subst n0.
        destruct (nth_error Γs pos); try contradiction.
        destruct (nth_error Γ pos); try contradiction.
        clear H.
        rename d0 into a, d into b.
        simpl.
        repeat break_match ; subst; try reflexivity.
        * inversion H0.
        * inversion H0.
        * inversion H1.
        * inversion H1.
        * inversion H1.
        * inversion H0.
        * inversion H0.
      +
        (* accessing some other variable *)
        clear H0 H1.
        simpl.
        specialize (H n0 n1).
        inversion H.
        reflexivity.
        inversion H2; try reflexivity.
        repeat break_match; try reflexivity.
        subst.
        symmetry.
        compute.
        f_equiv.
        apply H3.
    -
      reflexivity.
  Qed.

  Fact AExpr_NVar_subst_S
       (Γ Γs: evalContext)
       (pos: nat)
       (exp : AExpr)
       (j : nat):
    listsDiffByOneElement Γ Γs pos ->
    isNth Γ pos (DSHnatVal j) ->
    isNth Γs pos (DSHnatVal (S j)) ->
    evalAexp Γs exp =
    evalAexp Γ (AExpr_natvar_subst pos (NPlus (NVar pos) (NConst 1)) exp).
  Proof.
    intros H H0 H1.
    induction exp.
    -
      simpl.
      unfold listsDiffByOneElement, isNth in *.
      destruct (PeanoNat.Nat.eq_dec n pos).
      +
        (* accessing variable at pos *)
        subst n.
        destruct (nth_error Γs pos); try contradiction.
        destruct (nth_error Γ pos); try contradiction.
        clear H.
        rename d0 into a, d into b.
        simpl.
        repeat break_match ; subst; try reflexivity.
        * inversion H0.
        * inversion H0. subst. inversion H1.
        * inversion H1.
        * inversion H1.
        * inversion H1.
      +
        (* accessing some other variable *)
        clear H0 H1.
        simpl.
        specialize (H n n0).
        inversion H.
        reflexivity.
        inversion H2; try reflexivity.
        f_equiv.
        symmetry.
        apply H3.
    -
      reflexivity.
    -
      rename n0 into ne.
      simpl.
      assert(V:evalVexp Γs v = evalVexp Γ (VExpr_natvar_subst pos (NPlus (NVar pos) (NConst 1)) v)) by (apply VExpr_NVar_subst_S with (j0:=j); auto).
      unfold listsDiffByOneElement, isNth in *.
      assert (C: evalNexp Γs ne = evalNexp Γ (NExpr_var_subst pos (NPlus (NVar pos) (NConst 1)) ne)) by (apply NExpr_NVar_subst_S with (j:=j); auto).
      twoarg.
      repeat nat_equiv_to_eq.
      subst.
      replace l0 with l by apply proof_irrelevance; clear l0.
      apply Vnth_proper, V.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
    - twoarg.
  Qed.

End Expr_NVar_subst_S.

Fact evalDiamond_NVar_subst_S:
  ∀ (i o n : nat) (dot : DSHBinCarrierA) (initial : CarrierA)
    (dop_family : DSHOperator i o) (y : vector CarrierA i)
    (j : nat), (∀ (y0 : vector CarrierA i) (pos : nat) (Γ Γs : evalContext),
                   listsDiffByOneElement Γ Γs pos
                   → isNth Γ pos (DSHnatVal j)
                   → isNth Γs pos (DSHnatVal (S j))
                   → evalDSHOperator Γs dop_family y0 =
                     evalDSHOperator Γ
                                     (DSHOperator_NVar_subt pos (NPlus (NVar pos) (NConst 1))
                                                            dop_family) y0)
               → ∀ (pos : nat) (Γ Γs : evalContext), listsDiffByOneElement Γ Γs pos
                                                     → isNth Γ pos (DSHnatVal j)
                                                     → isNth Γs pos (DSHnatVal (S j))
                                                     →
                                                     evalDiamond
                                                       (evalBinCarrierA Γs dot)
                                                       initial
                                                       (Vbuild
                                                          (λ (j0 : nat) (_ : j0 < n),
                                                           evalDSHOperator
                                                             (DSHnatVal j0 :: Γs)
                                                             dop_family y)) =
                                                     evalDiamond
                                                       (evalBinCarrierA Γ
                                                                        (AExpr_natvar_subst
                                                                           (pos + 2)
                                                                           (NPlus
                                                                              (if
                                                                                  PeanoNat.Nat.eq_dec pos pos
                                                                                then NVar (pos + 2)
                                                                                else NVar pos)
                                                                              (NConst 1)) dot)) initial
                                                       (Vbuild
                                                          (λ (j0 : nat) (_ : j0 < n),
                                                           evalDSHOperator
                                                             (DSHnatVal j0 :: Γ)
                                                             (DSHOperator_NVar_subt
                                                                (S pos)
                                                                (NPlus
                                                                   (if
                                                                       PeanoNat.Nat.eq_dec pos pos
                                                                     then NVar (S pos)
                                                                     else NVar pos)
                                                                   (NConst 1)) dop_family) y)).
Proof.
  intros i o n dot initial dop_family y j IHdop_family pos Γ Γs L L0 L1.


  dep_destruct (PeanoNat.Nat.eq_dec pos pos); try congruence; clear e.

  replace (pos+2)%nat with (S (S pos)).
  2:{
    rewrite <- 2!plus_n_Sm.
    rewrite PeanoNat.Nat.add_0_r.
    reflexivity.
  }

  assert(D: evalBinCarrierA Γs dot =
            evalBinCarrierA Γ
                            (AExpr_natvar_subst (S (S pos))
                                                (NPlus (NVar (S (S pos)))
                                                       (NConst 1)) dot)).
  {
    unfold evalBinCarrierA.
    intros a a' Ea b b' Eb.
    apply AExpr_NVar_subst_S with (j:=j).
    apply listsDiffByOneElement_Sn; try (constructor; symmetry; apply Eb).
    apply listsDiffByOneElement_Sn; try (constructor; symmetry; apply Ea).
    apply L.
    -- apply L0.
    -- apply L1.
  }

  induction n.
  + reflexivity.
  +
    unfold evalDiamond in *.
    rewrite 2!Vbuild_cons.
    rewrite 2!Vfold_left_rev_cons.
    apply optDot_proper.
    *
      apply D.
    *
      eapply Vfold_left_rev_proper.
      --
        apply optDot_proper.
        unfold evalBinCarrierA.
        intros a a' Ea b b' Eb.

        apply AExpr_NVar_subst_S with (j:=j).
        ++
          apply listsDiffByOneElement_Sn; try (constructor; symmetry; apply Eb).
          apply listsDiffByOneElement_Sn; try (constructor; symmetry; apply Ea).
          apply L.
        ++ apply L0.
        ++ apply L1.
      --
        reflexivity.
      --
        vec_index_equiv j jc.
        rewrite 2!Vbuild_nth.
        apply IHdop_family.
        apply listsDiffByOneElement_Sn; try (constructor; symmetry; reflexivity).
        apply L.
        apply L0.
        apply L1.
    *
      apply IHdop_family.
      apply listsDiffByOneElement_Sn; try (constructor; symmetry; reflexivity).
      apply L.
      apply L0.
      apply L1.
Qed.

Fact DSHOperator_NVar_subst_S
     {i o : nat}
     (Γ Γs : evalContext)
     (dop_family : DSHOperator i o)
     (pos:nat)
     (y : vector CarrierA i)
     (j : nat):
  listsDiffByOneElement Γ Γs pos ->
  isNth Γ pos (DSHnatVal j) ->
  isNth Γs pos (DSHnatVal (S j)) ->
  evalDSHOperator Γs dop_family y =
  evalDSHOperator Γ
                  (DSHOperator_NVar_subt pos (NPlus (NVar pos) (NConst 1)) dop_family) y.
Proof.
  revert Γ Γs.
  revert pos.
  induction dop_family; intros pos Γ Γs L L0 L1.
  -
    simpl.
    pose proof (NExpr_NVar_subst_S Γ Γs pos b j) as H.
    repeat break_match;crush; try some_none; try some_inv; try congruence.
    f_equiv.
    repeat nat_equiv_to_eq; subst.
    reflexivity.
  -
    simpl.
    pose proof (NExpr_NVar_subst_S Γ Γs pos b j) as H.
    repeat break_match;crush; try some_none; try some_inv; try congruence.
    f_equiv.
    repeat nat_equiv_to_eq; subst.
    replace l0 with l by apply proof_irrelevance.
    reflexivity.
  -
    simpl.
    unfold evalDSHPointwise, evalIUnCarrierA.
    apply vsequence_option_proper.
    apply Vbuild_proper.
    intros t tc.
    dep_destruct (PeanoNat.Nat.eq_dec pos pos); try congruence; clear e.

    replace (pos+2)%nat with (S (S pos)).
    2:{
      rewrite <- 2!plus_n_Sm.
      rewrite PeanoNat.Nat.add_0_r.
      reflexivity.
    }
    apply AExpr_NVar_subst_S with (j:=j).
    +
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply L.
    + apply L0.
    + apply L1.
  -
    simpl.
    unfold evalDSHBinOp, evalIBinCType.
    break_let.
    apply vsequence_option_proper.
    apply Vbuild_proper.
    intros m mc.
    dep_destruct (PeanoNat.Nat.eq_dec pos pos); try congruence; clear e.
    replace (pos+3)%nat with (S (S (S pos))).
    2:{
      rewrite <- 3!plus_n_Sm.
      rewrite PeanoNat.Nat.add_0_r.
      reflexivity.
    }
    apply AExpr_NVar_subst_S with (j:=j).
    +
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply L.
    + apply L0.
    + apply L1.
  -
    simpl.
    pose proof (NExpr_NVar_subst_S Γ Γs pos n j) as Hn.
    specialize (Hn L L0 L1).

    dep_destruct (PeanoNat.Nat.eq_dec pos pos); try congruence; clear e.
    replace (pos+2)%nat with (S (S pos)).
    2:{
      rewrite <- 2!plus_n_Sm.
      rewrite PeanoNat.Nat.add_0_r.
      reflexivity.
    }

    match goal with
    | [ |- match ?a with _ => _ end = match ?b with _ => _ end] =>
      destruct a ; destruct b
    end; try some_none; try reflexivity.


    some_inv.
    nat_equiv_to_eq.
    subst n0.
    generalize (Vhead y); intros y'; clear y; rename y' into y.

    match goal with
    | [ |- match ?a with _ => _ end = match ?b with _ => _ end] =>
      assert (C: a = b)
    end.
    {
      induction n1.
      * reflexivity.
      *
        rewrite 2!evalDSHInductor_Sn.
        Opaque evalDSHInductor. simpl.
        repeat break_match; try reflexivity.
        unfold evalBinCarrierA.
        apply AExpr_NVar_subst_S with (j:=j).
        Transparent evalDSHInductor.
        --
          some_inv.
          apply listsDiffByOneElement_Sn; try reflexivity.
          apply listsDiffByOneElement_Sn; try (constructor; symmetry; apply IHn1).
          apply L.
        -- apply L0.
        -- apply L1.
        -- some_none.
        -- some_none.
    }

    repeat break_match; try some_none; try reflexivity.
    f_equiv.
    f_equiv.
    some_inv.
    apply C.
  -
    simpl.
    apply evalDiamond_NVar_subst_S with (j:=j); auto.
  -
    simpl.
    eapply evalDiamond_NVar_subst_S with (j:=j); auto.
  -
    simpl.
    match goal with
    | [ |- match ?a with _ => _ end = match ?b with _ => _ end] =>
      assert (C: a = b) by (apply IHdop_family2; auto)
    end.
    repeat break_match; try reflexivity; try some_none.
    some_inv.
    rewrite <- C.
    eapply IHdop_family1; auto.
  -
    simpl.
    match goal with
    | [ |- match ?a with _ => _ end = match ?b with _ => _ end] =>
      assert (C0: a = b) by (apply IHdop_family1; auto)
    end.

    assert(C1: evalDSHOperator Γs dop_family2 y = evalDSHOperator Γ
                                                                  (DSHOperator_NVar_subt pos (NPlus (NVar pos) (NConst 1)) dop_family2) y) by (apply IHdop_family2; auto).

    repeat break_match; try reflexivity; try some_none; try contradiction.
    repeat some_inv.
    rewrite C0, C1.
    apply vsequence_option_proper.
    rewrite 2!Vmap2_as_Vbuild.
    apply Vbuild_proper.
    intros m mc.
    unfold evalBinCarrierA.
    replace (pos+2)%nat with (S (S pos)).
    2:{
      rewrite <- 2!plus_n_Sm.
      rewrite PeanoNat.Nat.add_0_r.
      reflexivity.
    }
    apply AExpr_NVar_subst_S with (j:=j).
    --
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply listsDiffByOneElement_Sn; try reflexivity.
      apply L.
    -- apply L0.
    -- apply L1.
Qed.

Theorem IReduction_DSHIReduction
        {i o n: nat}
        {svalue: CarrierA}
        (dot: CarrierA -> CarrierA -> CarrierA)
        `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
        `{scompat: BFixpoint svalue dot}
        (op_family: @SHOperatorFamily Monoid_RthetaSafeFlags i o n svalue)
        (ddot: DSHBinCarrierA)
        (dop_family: DSHOperator i o)
        (σ: evalContext)
  :
    (forall Γ a b, Some (dot a b) = evalBinCarrierA (σ++Γ) ddot a b) ->
    SHOperatorFamily_DSHCOL_equiv σ op_family dop_family ->
    SHCOL_DSHCOL_equiv σ
                       (@IReduction svalue i o n dot pdot scompat op_family)
                       (@DSHIReduction i o n ddot svalue dop_family).
Proof.
  intros Hdot Hfam Γ x.
  simpl.
  unfold Diamond, MUnion, Apply_Family', evalDiamond, densify.

  revert op_family dop_family Hfam.
  induction n.
  -
    intros op_family dop_family Hfam.
    simpl.
    f_equiv.
    vec_index_equiv j jc.
    rewrite Vnth_map.
    rewrite 2!Vnth_const.
    rewrite evalWriter_mkStruct.
    reflexivity.
  -
    intros op_family dop_family Hfam.

    assert(E: SHOperatorFamily_DSHCOL_equiv σ
                                            (shrink_op_family_up Monoid_RthetaSafeFlags op_family)
                                            (DSHOperator_NVar_subt 0 (NPlus (NVar 0) (NConst 1)) dop_family)).
    {
      clear IHn pdot Hdot ddot x Γ.
      intros jf Γ x.
      unfold shrink_op_family_up.
      specialize (Hfam (mkFinNat (Lt.lt_n_S (proj2_sig jf))) Γ x).
      rewrite_clear Hfam.
      simpl.
      destruct jf as [j jc].
      apply DSHOperator_NVar_subst_S with (j0:=j).
      -
        intros pos H.
        destruct pos. congruence.
        destruct pos; simpl; repeat constructor; auto.
      - compute; reflexivity.
      - compute; reflexivity.
    }

    specialize (IHn (shrink_op_family_up _ op_family)
                    (DSHOperator_NVar_subt 0 (NPlus (NVar 0) (NConst 1)) dop_family)
                    E
               ).

    rewrite 2!Vbuild_cons.
    rewrite 2!Vfold_left_rev_cons.

    unfold Vec2Union, get_family_op, shrink_op_family_up in *.

    match goal with
    | [IHn: ?a = ?b |- _ = optDot ?f ?c ?d] =>
      setoid_replace c with b
    end.
    2:{
      eapply Vfold_left_rev_arg_proper.
      - typeclasses eauto.
      - apply optDot_arg_proper; try reflexivity.
      - apply Vbuild_proper.
        intros j jc.
        remember (@Vmap (Rtheta' Monoid_RthetaSafeFlags) CarrierA
                        (@evalWriter RthetaFlags CarrierA Monoid_RthetaSafeFlags) i x) as y.
        apply DSHOperator_NVar_subst_S with (j0:=j).
        +
          intros pos H.
          destruct pos. congruence.
          destruct pos; simpl; repeat constructor; auto.
        + compute; reflexivity.
        + compute; reflexivity.
    }

    rewrite <- IHn. clear IHn.

    setoid_replace
      (evalDSHOperator (DSHnatVal 0 :: σ ++ Γ) dop_family
                       (Vmap (evalWriter (Monoid_W:=Monoid_RthetaSafeFlags)) x))
      with
        (Some
           (densify Monoid_RthetaSafeFlags
                    (op Monoid_RthetaSafeFlags
                        (op_family (mkFinNat (Misc.zero_lt_Sn n))) x)))
      by (symmetry; apply Hfam).

    clear dop_family Hfam E.

    unfold optDot, densify.
    simpl.

    repeat rewrite Vmap2_as_Vbuild.
    repeat rewrite Vmap_Vbuild.
    setoid_rewrite Vnth_map.
    unfold Union.

    setoid_rewrite <- Hdot.
    clear ddot Hdot Γ σ.

    repeat rewrite <- Vmap_Vbuild.
    rewrite vsequence_Vmap_Some.

    f_equiv.
    repeat rewrite Vmap_Vbuild.
    apply Vbuild_proper.

    intros j jc.
    rewrite evalWriter_Rtheta_liftM2.
    apply pdot.
    +
      f_equiv.
    +
      f_equiv.
      apply Vnth_arg_equiv.
      f_equiv.
      f_equiv.
      f_equiv.
      apply proof_irrelevance.
Qed.

Theorem SHPointwise_DSHPointwise
        {fm}
        {svalue: CarrierA}
        {n: nat}
        (f: FinNat n -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}
        (df: DSHIUnCarrierA)
        (σ: evalContext)
  :
    (forall Γ j a, Some (f j a) = evalIUnCarrierA (σ++Γ) df (proj1_sig j) a) ->
    SHCOL_DSHCOL_equiv σ
                       (@SHPointwise fm svalue  n f pF)
                       (DSHPointwise df).
Proof.
  intros H.
  intros Γ x.
  specialize (H Γ).
  simpl.
  unfold evalDSHPointwise.
  symmetry.
  apply vsequence_Vbuild_equiv_Some.
  unfold densify.
  rewrite Vmap_map.
  simpl.
  unfold SHPointwise_impl.
  rewrite Vmap_Vbuild.
  apply Vbuild_proper.
  intros j jc.
  rewrite Vnth_map.
  rewrite evalWriter_Rtheta_liftM.
  specialize (H (mkFinNat jc)).
  rewrite <- H.
  reflexivity.
Qed.

Lemma evalDSHInductor_not_None
      (n : nat)
      (initial : CarrierA)
      (df : DSHBinCarrierA)
      (σ Γ : evalContext)
      (Edot: forall a b : CarrierA, is_Some (evalBinCarrierA (σ ++ Γ) df a b)) :
  forall x : CarrierA, is_Some (evalDSHInductor (σ ++ Γ) n df initial x).
Proof.
  intros x.
  induction n.
  -
    crush.
  -
    simpl.
    break_match; crush.
Qed.

Theorem SHInductor_DSHInductor
        {fm}
        {svalue: CarrierA}
        (n:nat)
        (f: CarrierA -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}
        (initial: CarrierA)
        (dn:NExpr)
        (df: DSHBinCarrierA)
        (σ: evalContext)
  :
    (forall Γ, Some n = evalNexp (σ++Γ) dn) ->
    (forall  Γ a b, Some (f a b) = evalBinCarrierA (σ++Γ) df a b) ->
    SHCOL_DSHCOL_equiv σ
                       (@SHInductor fm svalue n f pF initial)
                       (DSHInductor dn df initial).
Proof.
  intros E Edot.
  intros Γ x.
  specialize (E Γ).
  specialize (Edot Γ).
  simpl evalDSHOperator.
  break_match; try some_none.
  apply Some_inj_equiv in E.
  unfold equiv, peano_naturals.nat_equiv in E.
  subst n0.

  simpl op.
  unfold SHInductor_impl, Lst, Vconst, densify.
  rewrite Vmap_cons.
  rewrite evalWriter_Rtheta_liftM.
  simpl.
  dep_destruct x.
  simpl.
  clear x0 x.
  generalize (WriterMonadNoT.evalWriter h). intros x. clear h.

  break_match.
  -
    f_equiv.
    apply Vcons_proper; try reflexivity.
    clear dn Heqo.
    dependent induction n.
    +
      crush.
    +
      simpl.
      specialize (IHn f pF initial df σ Γ Edot).
      simpl in Heqo0.
      break_match.
      *
        rewrite IHn with (x:=x) (c:=c0).
        specialize (Edot c0 x).
        rewrite Heqo0 in Edot.
        some_inv; auto.
        auto.
      *
        some_none.
  -
    contradict Heqo0.
    apply is_Some_ne_None.
    apply evalDSHInductor_not_None.
    intros a b.
    specialize (Edot a b).
    symmetry in Edot.
    apply equiv_Some_is_Some in Edot.
    apply Edot.
Qed.

Theorem Embed_DSHEmbed
        {fm}
        {svalue: CarrierA}
        {i b:nat}
        (bc: b < i)
        (db: NExpr)
        (σ: evalContext)
  :
    (forall (Γ:evalContext), Some b = evalNexp (σ++Γ) db) ->
    SHCOL_DSHCOL_equiv σ
                       (@Embed fm svalue i b bc)
                       (@DSHEmbed i (db:NExpr)).
Proof.
  intros H.
  intros Γ x.
  specialize (H Γ).
  simpl.
  break_match; try some_none.
  break_match; some_inv; unfold equiv, peano_naturals.nat_equiv in H; subst n.
  -
    f_equiv.
    unfold unLiftM_HOperator', compose.
    vec_index_equiv j jc.
    unfold densify, sparsify.
    repeat rewrite Vnth_map.
    rewrite Vmap_map.
    dep_destruct jc;try inversion x0.
    rewrite Vnth_cons.
    break_match. inversion l0.
    apply castWriter_equiv.
    simpl.
    rewrite Vnth_map.
    replace l with bc by apply proof_irrelevance.
    apply castWriter_mkValue_evalWriter.
  -
    destruct n0; auto.
Qed.

Theorem ISumUnion_DSHISumUnion
        {i o n: nat}
        (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n zero)
        (dop_family: DSHOperator i o)
        (σ: evalContext)
  :
    SHOperatorFamily_DSHCOL_equiv σ op_family dop_family ->
    SHCOL_DSHCOL_equiv σ
                       (@ISumUnion i o n op_family)
                       (@DSHIUnion i o n (APlus (AVar 1) (AVar 0)) 0 dop_family).
Proof.
  (* significant code duplication with `IReduction_DSHIReduction` *)
  intros Hfam Γ x.
  simpl.
  unfold Diamond, MUnion, Apply_Family', evalDiamond, densify.

  revert op_family dop_family Hfam.
  induction n.
  -
    intros op_family dop_family Hfam.
    simpl.
    f_equiv.
    vec_index_equiv j jc.
    rewrite Vnth_map.
    rewrite 2!Vnth_const.
    rewrite evalWriter_mkStruct.
    reflexivity.
  -
    intros op_family dop_family Hfam.

    assert(E: SHOperatorFamily_DSHCOL_equiv σ
                                            (shrink_op_family_up Monoid_RthetaFlags op_family)
                                            (DSHOperator_NVar_subt 0 (NPlus (NVar 0) (NConst 1)) dop_family)).
    {
      clear IHn x Γ.
      intros jf Γ x.
      unfold shrink_op_family_up.
      specialize (Hfam (mkFinNat (Lt.lt_n_S (proj2_sig jf))) Γ x).
      rewrite_clear Hfam.
      simpl.
      destruct jf as [j jc].
      apply DSHOperator_NVar_subst_S with (j0:=j).
      -
        intros pos H.
        destruct pos. congruence.
        destruct pos; simpl; repeat constructor; auto.
      - compute; reflexivity.
      - compute; reflexivity.
    }

    specialize (IHn (shrink_op_family_up _ op_family)
                    (DSHOperator_NVar_subt 0 (NPlus (NVar 0) (NConst 1)) dop_family)
                    E
               ).

    rewrite 2!Vbuild_cons.
    rewrite 2!Vfold_left_rev_cons.

    unfold Vec2Union, get_family_op, shrink_op_family_up in *.

    match goal with
    | [IHn: ?a = ?b |- _ = optDot ?f ?c ?d] =>
      setoid_replace c with b
    end.
    2:{
      eapply Vfold_left_rev_arg_proper.
      - typeclasses eauto.
      - apply optDot_arg_proper; try reflexivity.
      - apply Vbuild_proper.
        intros j jc.
        remember (@Vmap (Rtheta' Monoid_RthetaFlags) CarrierA
                        (@evalWriter RthetaFlags CarrierA Monoid_RthetaFlags) i x) as y.
        apply DSHOperator_NVar_subst_S with (j0:=j).
        +
          intros pos H.
          destruct pos. congruence.
          destruct pos; simpl; repeat constructor; auto.
        + compute; reflexivity.
        + compute; reflexivity.
    }

    rewrite <- IHn. clear IHn.

    setoid_replace
      (evalDSHOperator (DSHnatVal 0 :: σ ++ Γ) dop_family
                       (Vmap (evalWriter (Monoid_W:=Monoid_RthetaFlags)) x))
      with
        (Some
           (densify Monoid_RthetaFlags
                    (op Monoid_RthetaFlags
                        (op_family (mkFinNat (Misc.zero_lt_Sn n))) x)))
      by (symmetry; apply Hfam).

    clear dop_family Hfam E.

    unfold optDot, densify.
    simpl.

    repeat rewrite Vmap2_as_Vbuild.
    repeat rewrite Vmap_Vbuild.
    setoid_rewrite Vnth_map.
    unfold Union.

    assert(Hdot: forall Γ a b, Some (CarrierAplus a b) = evalBinCarrierA (σ++Γ) (APlus (AVar 1) (AVar 0))  a b) by reflexivity.

    setoid_rewrite <- Hdot.

    repeat rewrite <- Vmap_Vbuild.
    rewrite vsequence_Vmap_Some.

    f_equiv.
    repeat rewrite Vmap_Vbuild.
    apply Vbuild_proper.

    intros j jc.
    rewrite evalWriter_Rtheta_liftM2.
    apply CarrierAPlus_proper.
    +
      f_equiv.
    +
      f_equiv.
      apply Vnth_arg_equiv.
      f_equiv.
      f_equiv.
      f_equiv.
      apply proof_irrelevance.
Qed.

(* Attemts to solve evaluation lemmas on DSHCOL Aexpr *)
Ltac solve_evalAexp :=
  repeat match goal with
         | [ |- forall x, _] => intros
         | [ H: FinNat _ |- _ ] => destruct H
         | [ |- evalAexp _ _ = Some _] =>
           unfold Fin1SwapIndex, const, mult_by_nth; simpl;
           try (repeat break_match; try some_none; try congruence)
         | [H: Some ?A ≡ Some ?b |- _ ] => inversion H; clear H
         | [H: Some ?A = Some ?b |- _ ] => apply Some_inj_equiv in H
         | [ |- ?a _ = ?a _ ] => f_equiv
         | [ |- Vnth ?a _ ≡ Vnth ?a _] => try apply Vnth_eq
         | [ |- _ ] => auto
         end.

(* Solves obligations generated by `reifySHCOL` *)
Ltac solve_reifySHCOL_obligations E :=
  intros ;
  unfold E ;
  match goal with
  | [ |- SHCOL_DSHCOL_equiv _ _ ?d] => unfold d
  end ;
  repeat match goal with
         | [ |- forall x, _] => intros
         | [ |- SHCOL_DSHCOL_equiv _ (SHCompose _ _ _) (DSHCompose _ _)] => apply SHCompose_DSHCompose
         | [ |- SHCOL_DSHCOL_equiv _ (SafeCast _) _ ] => apply SHCOL_DSHCOL_equiv_SafeCast
         | [ |- SHCOL_DSHCOL_equiv _ (UnSafeCast _) _ ] => apply SHCOL_DSHCOL_equiv_UnSafeCast
         | [ |- SHCOL_DSHCOL_equiv _ (SHBinOp _ _) (DSHBinOp _) ] => apply SHBinOp_DSHBinOp
         | [ |- SHCOL_DSHCOL_equiv _ (HTSUMUnion _ _ _ _) (DSHHTSUMUnion _ _ _) ] => apply HTSUMUnion_DSHHTSUMUnion
         | [ |- SHCOL_DSHCOL_equiv _ (Pick _ _) (DSHPick _ _)] => apply Pick_DSHPick
         | [  |- SHCOL_DSHCOL_equiv _ (IReduction _ _) (DSHIReduction _ _ _ _)] => apply IReduction_DSHIReduction
         | [ |- SHOperatorFamily_DSHCOL_equiv _ _ _ ] => unfold SHOperatorFamily_DSHCOL_equiv
         | [ |- SHCOL_DSHCOL_equiv _ (SHFamilyOperatorCompose _ _ _ _) (DSHCompose _ _)] => apply SHCompose_DSHCompose
         | [ |- SHCOL_DSHCOL_equiv _ (SHPointwise _ _) (DSHPointwise _) ] =>  apply SHPointwise_DSHPointwise
         | [ |- SHCOL_DSHCOL_equiv _ (SHInductor _ _ _ _) (DSHInductor _ _ _)] => apply SHInductor_DSHInductor
         | [ |- SHCOL_DSHCOL_equiv _ (Embed _ _) (DSHEmbed _)] => apply Embed_DSHEmbed
         | [ |- SHCOL_DSHCOL_equiv _(ISumUnion _) (DSHIUnion _ _ _ _) ] => apply ISumUnion_DSHISumUnion
         | [ |- Some _ = evalIUnCarrierA _ _ _ _ ] => unfold evalIUnCarrierA; symmetry; solve_evalAexp
         | [ |- _ ] => try reflexivity
         end.
 *)
