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

(* TODO: move to Memory.v *)
(* problem: these depend on MemSetoid.v, which depends on Memory.v *)
Section memory_aux.

  (* Two memory locations equivalent on all addresses except one *)
  Definition memory_equiv_except (m m': memory) (e:mem_block_id)
    := forall k, k ≢ e -> memory_lookup m k = memory_lookup m' k.
  
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

  Lemma memory_lookup_err_inr_is_Some {s : string} (m : memory) (mbi : mem_block_id) :
    forall mb, memory_lookup_err s m mbi ≡ inr mb → is_Some (memory_lookup m mbi).
  Proof.
    intros.
    unfold memory_lookup_err, trywith in H.
    break_match.
    reflexivity.
    inversion H.
  Qed.

End memory_aux.

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

(* Instances of following classes ensure that given [*Expr]
   could be propely typed, and its type signaure includes
   given [TypeSig].

   This could be viewed as a subtyping relation...
 *)

Class AExprTypeSigIncludes (a:AExpr) (ts:TypeSig) : Prop
  := atypesigincl: exists dfs, (TypeSigAExpr a = Some dfs) /\ TypeSigIncluded dfs ts.

Class NExprTypeSigIncludes (n:NExpr) (ts:TypeSig) : Prop
  := ntypesigincl: exists dfs, (TypeSigNExpr n = Some dfs) /\ TypeSigIncluded dfs ts.

Class MExprTypeSigIncludes (m:MExpr) (ts:TypeSig) : Prop
  := mtypesigincl: exists dfs, (TypeSigMExpr m = Some dfs) /\ TypeSigIncluded dfs ts.

(* The following classes ensure expression type signature compatibility with given signature *)

Class AExprTypeSigCompat (a:AExpr) (ts:TypeSig) : Prop
  := atypesigcompat: exists dfs, (TypeSigAExpr a = Some dfs) /\ TypeSigCompat dfs ts.

Class NExprTypeSigCompat (n:NExpr) (ts:TypeSig) : Prop
  := ntypesigcompat: exists dfs, (TypeSigNExpr n = Some dfs) /\ TypeSigCompat dfs ts.

Class MExprTypeSigCompat (m:MExpr) (ts:TypeSig) : Prop
  := mtypesigcompat: exists dfs, (TypeSigMExpr m = Some dfs) /\ TypeSigCompat dfs ts.


(* Instances of following classes ensure that given expression could
   be used as a function of specified arity. In particular it ensures
   that arguments, if used, have expected types.

   This implementation allows function to ignore arguments.

   This implementation only check types expected function
   arguments. The expression may reference other arbitrary variables.
*)

Class DSHIBinCarrierA (a:AExpr) : Prop :=
  DSHIBinCarrierA_atypesigincl :> AExprTypeSigCompat a DSHIBinCarrierA_TypeSig.

Class DSHUnCarrierA (a:AExpr) : Prop :=
  DSHUnCarrierA_atypesigincl :> AExprTypeSigCompat a DSHUnCarrierA_TypeSig.

Class DSHIUnCarrierA (a:AExpr) : Prop :=
  DSHIUnCarrierA_atypesigincl :> AExprTypeSigCompat a DSHIUnCarrierA_TypeSig.

Class DSHBinCarrierA (a:AExpr) : Prop :=
  DSHBinCarrierA_atypesigincl :> AExprTypeSigCompat a DSHBinCarrierA_TypeSig.


(* This relations represents consistent memory/envirnment combinations.
   That means all pointer variables should resolve to existing memory blocks *)
Inductive EnvMemoryConsistent: evalContext -> memory -> Prop :=
| EmptyEnvConsistent: forall m, EnvMemoryConsistent [] m
| DSHPtrValConsistent: forall σ m a n,
    mem_block_exists a m ->
    EnvMemoryConsistent σ m ->
    EnvMemoryConsistent (DSHPtrVal a n :: σ) m

(* the remaining case does not depend on memory and just recurses over environment *)
| DSHnatValConsistent : forall σ m n, EnvMemoryConsistent σ m ->
                                 EnvMemoryConsistent (DSHnatVal n :: σ) m
| DSHCTypeValConsistent: forall σ m a, EnvMemoryConsistent σ m ->
                                  EnvMemoryConsistent (DSHCTypeVal a :: σ) m.

Lemma EnvMemoryConsistent_inv (a : DSHVal) (σ : evalContext) (mem : memory) :
  EnvMemoryConsistent (a :: σ) mem -> EnvMemoryConsistent σ mem.
Proof.
  intros; inversion H; auto.
Qed.

Lemma EnvMemoryConsistent_memory_lookup
      {σ : evalContext}
      {mem : memory}
      {EC : EnvMemoryConsistent σ mem}
      (v : var_id)
      (a : mem_block_id)
      (n : nat) :
  List.nth_error σ v = Some (DSHPtrVal a n) →
  is_Some (memory_lookup mem a).
Proof.
  intros.
  dependent induction σ; [destruct v; inversion H |].
  destruct v.
  -
    clear IHσ.
    cbn in H; some_inv.
    destruct a; inversion H; clear H; subst.
    inversion EC; subst.
    apply memory_is_set_is_Some.
    destruct H1.
    rewrite <-H0.
    assumption.
  -
    eapply IHσ.
    eapply EnvMemoryConsistent_inv; eassumption.
    cbn in H; eassumption.
Qed.

Lemma evalMExpr_is_OK
      `{EC : EnvMemoryConsistent σ mem}
      {m: MExpr}
      (tm: TypeSig)
      (TSI : MExprTypeSigIncludes m tm)
      (TC : typecheck_env 0 tm σ):
  is_OK (evalMexp mem σ m).
Proof.
  inversion TSI; clear TSI.
  rename x into mts; destruct H as [MTS TSI].
  eapply typecheck_env_TypeSigIncluded in TC.
  2: eassumption.
  clear TSI tm; rename MTS into TS, mts into ts.
  destruct m; cbn in *; [| constructor].
  destruct p; cbn in *.
  some_inv.
  rewrite <-TS in TC; clear TS.
  unfold typecheck_env, typecheck_env_bool, TP.for_all in TC.
  eapply TP.for_all_iff with (k:=v) (e:=DSHPtr) in TC ;
    [| solve_proper | apply TM.add_1; reflexivity].
  cbn in TC.
  apply bool_decide_true in TC.
  rewrite Nat.sub_0_r in TC.
  unfold contextEnsureType in TC.
  break_match_hyp; [| inversion TC].
  inversion TC; subst d.
  unfold memory_lookup_err.
  assert (is_Some (memory_lookup mem a)).
  eapply EnvMemoryConsistent_memory_lookup with (v0:=v).
  rewrite <-Heqo.
  reflexivity.
  apply is_Some_def in H; destruct H as [b H].
  rewrite H.
  constructor.
  Unshelve.
  assumption.
Qed.

Lemma evalNExpr_is_OK
      {σ: evalContext}
      {n: NExpr}
      (tn: TypeSig)
      (TSI : NExprTypeSigIncludes n tn)
      (TC : typecheck_env 0 tn σ):
  is_OK (evalNexp σ n).
Proof.
  inversion TSI; clear TSI.
  rename x into nts; destruct H as [NTS TSI].
  eapply typecheck_env_TypeSigIncluded in TC.
  2: eassumption.
  clear TSI tn; rename NTS into TS, nts into ts.
  dependent induction n; simpl in *.

  (* base case 1 *)
  { 
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
  }

  (* base case 2 *)
  {
    constructor.
  }
  
  (* all inductive cases *)
  all: unfold TypeSigUnion_error' in TS.
  all: simpl in TS.
  all: repeat break_match_hyp; try some_none.
  all: rename t into t1.
  all: rename t0 into t2.
  all: eapply TypeSigUnion_error_typecheck_env in TC; eauto.
  all: destruct TC as [T1 T2].
  all: assert(T1T: Some t1 = Some t1) by reflexivity.
  all: specialize (IHn1 t1 T1T T1).
  all: assert(T2T: Some t2 = Some t2) by reflexivity.
  all: specialize (IHn2 t2 T2T T2).
  all: repeat break_match; inl_inr.
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
Lemma evalAExpr_is_OK
      {mem : memory}
      {σ : evalContext}
      {EC : EnvMemoryConsistent σ mem}
      {a : AExpr}
      `{TSI : AExprTypeSigIncludes a ts}
      (TC : typecheck_env 0 ts σ) :
  is_OK (evalAexp mem σ a).
Proof.
  inversion TSI; clear TSI.
  rename x into ats; destruct H as [ATS TSI].
  eapply typecheck_env_TypeSigIncluded in TC.
  2: eassumption.
  clear TSI ts; rename ATS into TS, ats into ts.

  dependent induction a; simpl in *.

  {
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
  }
  
  {
    constructor.
  }
  
  {
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
      apply err_equiv_eq in Heqe.
      contradict Heqe.
      eapply is_OK_neq_inl.
      eapply evalMExpr_is_OK.
      unfold MExprTypeSigIncludes.
      exists tm. split.
      assumption.
      eapply TypeSigIncluded_reflexive.
      assumption.
    +
      break_match.
      *
        apply err_equiv_eq in Heqe0.
        contradict Heqe0.
        eapply is_OK_neq_inl.
        eapply evalNExpr_is_OK.
        unfold MExprTypeSigIncludes.
        exists tn. split.
        assumption.
        eapply TypeSigIncluded_reflexive.
        assumption.
        Unshelve.
        assumption.
      *
        break_match; inl_inr.
  }
  
  {
    specialize (IHa ts TS TC).
    break_match; inl_inr.
  }
  
  all: unfold TypeSigUnion_error' in TS.
  all: simpl in TS.
  all: repeat break_match_hyp; try some_none.
  all: rename t into t1.
  all: rename t0 into t2.
  all: eapply TypeSigUnion_error_typecheck_env in TC; eauto.
  all: destruct TC as [T1 T2].
  all: assert(T1T: Some t1 = Some t1) by reflexivity.
  all: specialize (IHa1 t1 T1T T1).
  all: assert(T2T: Some t2 = Some t2) by reflexivity.
  all: specialize (IHa2 t2 T2T T2).
  all: repeat break_match; inl_inr.
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
    eq_to_equiv_hyp.
    eapply evalNExpr_is_OK in TC0.
    erewrite Ha in TC0; inversion TC0.
    unfold NExprTypeSigIncludes.
    eauto.
  -
    eq_to_equiv_hyp.
    eapply evalNExpr_is_OK in TC1.
    erewrite Hb in TC1; inversion TC1.
    unfold NExprTypeSigIncludes.
    eauto.
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
Qed.

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
  destruct H3.
  rewrite H3.
  reflexivity.
Qed.

Lemma evalAExpr_context_equiv_at_TypeSig
      {mem : memory}
      {σ0 σ1 : evalContext}
      {EC0 : EnvMemoryConsistent σ0 mem}
      {EC1 : EnvMemoryConsistent σ1 mem}
      (a : AExpr)
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
    err_eq_to_equiv_hyp.
    contradict Ha.
    apply is_OK_neq_inl.
    eapply evalAExpr_is_OK.
    Unshelve.
    eassumption.
    eassumption.
    unfold AExprTypeSigIncludes; eexists; split; eassumption.
  -
    err_eq_to_equiv_hyp.
    contradict Hb.
    apply is_OK_neq_inl.
    eapply evalAExpr_is_OK.
    Unshelve.
    eassumption.
    eassumption.
    unfold AExprTypeSigIncludes; eexists; split; eassumption.
  -
    dependent induction a; cbn in *.
    
    (* first "base case" *)
    unfold context_lookup, trywith in *.
    repeat break_match; try some_none; try inl_inr.
    repeat some_inv; repeat inl_inr_inv; subst.
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
    unfold context_lookup, trywith in *.
    repeat break_match; inversion H; try reflexivity.
    rewrite H2.
    reflexivity.

    (* second "base case" *)
    repeat some_inv; repeat inl_inr_inv; subst; reflexivity.

    (* third "base case" *)
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
    eapply evalMExpr_context_equiv_at_TypeSig with (mem:=mem) in MTSI; [| eassumption].
    eapply evalNExpr_context_equiv_at_TypeSig in NTSI; [| eassumption].
    destruct evalMexp eqn:M0 in Ha; [inl_inr |].
    destruct evalMexp eqn:M1 in Hb; [inl_inr |].
    rewrite M0, M1 in MTSI; inl_inr_inv.
    destruct evalNexp eqn:N0 in NTSI;
      destruct evalNexp eqn:N1 in NTSI;
      rewrite N0, N1 in *;
      try inl_inr.
    inl_inr_inv.
    inversion NTSI; subst.
    repeat break_match; repeat inl_inr_inv; subst.
    1: enough (Some c = Some c0) by (some_inv; assumption).
    2: enough (None = Some c0) by some_none.
    3: enough (None = Some c) by some_none.
    1-3: rewrite <-Heqo0, <-Heqo, MTSI; reflexivity.
    reflexivity.

    (* inductive 1 *)
    repeat break_match;
      try some_none; try inl_inr;
      repeat some_inv; repeat inl_inr_inv.
    enough (CarrierAe c1 c2) by (rewrite H; reflexivity).
    symmetry.
    eapply IHa; try eassumption; reflexivity.

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

Definition lookup_Pexp (σ:evalContext) (m:memory) (p:PExpr) :=
  a <- evalPexp σ p ;;
    memory_lookup_err "block_id not found" m a.

(*
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
*)

(*
   - [evalPexp σ p] must not to fail
   - [memory_lookup] must succeed
 *)
Definition blocks_equiv_at_Pexp (σ0 σ1:evalContext) (p:PExpr): rel (memory)
  := fun m0 m1 =>
       herr (fun a b => (opt equiv (memory_lookup m0 a) (memory_lookup m1 b)))
           (evalPexp σ0 p) (evalPexp σ1 p).

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
        evalDSHOperator σ d m fuel = Some (inr m') ->
        forall k, mem_block_exists k m <-> mem_block_exists k m';

      (* modifies only [y_p], which must be valid in [σ] *)
      mem_write_safe: forall σ m m' fuel,
          evalDSHOperator σ d m fuel = Some (inr m') ->
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

          (* [md] - memory diff *) 
          (* [m'] - memory state after execution *) 
          (h_opt_opterr_c
             (fun md m' => err_p (fun ma => SHCOL_DSHCOL_mem_block_equiv mb ma md)
                              (lookup_Pexp σ m' y_p))
             (mem_op mop mx)
             (evalDSHOperator σ dop m (estimateFuel dop)));
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

(* Check if [PExpr] is properly typed in given evaluation context *)
Inductive PExpr_typecheck: PExpr -> evalContext -> Prop :=
| PVar_tc (σ: evalContext) (n:var_id):
    context_pos_typecheck σ n DSHPtr -> PExpr_typecheck (PVar n) σ.

(* Check if [MExpr] is properly typed in given evaluation context *)
Inductive MExpr_typecheck: MExpr -> evalContext -> Prop :=
| MPtrDeref_tc (σ: evalContext) (n:var_id):
    PExpr_typecheck (PVar n) σ -> MExpr_typecheck (MPtrDeref (PVar n)) σ
| MConst_tc (σ: evalContext) {a}: MExpr_typecheck (MConst a) σ.

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

Section BinCarrierA.

  Class MSH_DSH_BinCarrierA_compat
        (f : CarrierA -> CarrierA -> CarrierA)
        (σ : evalContext)
        (df : AExpr)
        (mem : memory)
        `{dft : DSHBinCarrierA df}
    :=
      {
        bin_typechecks:
          forall a b,
            AExpr_typecheck df (DSHCTypeVal b :: DSHCTypeVal a :: σ);
  
        bin_equiv:
          forall a b, evalBinCType mem σ df a b = inr (f a b)
      }.
  
  Class MSH_DSH_IBinCarrierA_compat
        {o: nat}
        (f: {n:nat|n<o} -> CarrierA -> CarrierA -> CarrierA)
        (σ: evalContext)
        (df : AExpr)
        (mem : memory)
        `{dft : DSHIBinCarrierA df}
    :=
      {
        ibin_typechecks:
          forall n a b,
            AExpr_typecheck df (DSHCTypeVal b :: DSHCTypeVal a :: DSHnatVal n :: σ);
  
        ibin_equiv:
          forall nc a b, evalIBinCType mem σ df (proj1_sig nc) a b = inr (f nc a b)
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
      unfold DSHIBinCarrierA_TypeSig.
      (*
      cbv.
      repeat break_match; try congruence.
      contradict f; reflexivity.
       *)
  Admitted.
  
  Instance Abs_MSH_DSH_IBinCarrierA_compat
    :
      forall σ mem,
        MSH_DSH_IBinCarrierA_compat
          (λ i (a b : CarrierA),
           IgnoreIndex abs i
                       (HCOL.Fin1SwapIndex2 (n:=2)
                                            jf
                                            (IgnoreIndex2 sub) i a b))
          σ
          (AAbs (AMinus (AVar 1) (AVar 0))) mem.
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
        {mem : memory}
        {mx mb ma : mem_block}
        (E: evalDSHBinOp mem n off df σ mx mb = inr ma)
        (k: nat)
        (kc:k<n):
    is_Some (mem_lookup k mx) /\ is_Some (mem_lookup (k+off) mx).
  Proof.
    apply inr_is_OK in E.
    revert mb E k kc.
    induction n; intros.
    -
      inversion kc.
    -
      destruct (Nat.eq_dec k n).
      +
        subst.
        cbn in *.
        unfold mem_lookup_err, trywith in *.
        repeat break_match_hyp; try inl_inr.
        split; reflexivity.
      +
        simpl in *.
        repeat break_match_hyp; try inl_inr.
        apply eq_inr_is_OK in Heqe. rename Heqe into H1.
        apply eq_inr_is_OK in Heqe0. rename Heqe0 into H2.
        clear Heqe1 c c0.
        apply IHn with (mb:=mem_add n c1 mb); clear IHn.
        *
          apply E.
        *
          lia.
  Qed.
  
  Fact evalDSHBinOp_preservation
       {n off k: nat}
       {kc: k>=n}
       {df : AExpr}
       `{dft : DSHIBinCarrierA df}
       {σ : evalContext}
       {mem : memory}
       {mx ma mb : mem_block}
       {c : CarrierA}:
    evalDSHBinOp mem n off df σ mx (mem_add k c mb) = inr ma
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
        (mem : memory)
        (k: nat)
        (kc: k<n)
        {a b : CarrierA}:
    (mem_lookup k mx = Some a) ->
    (mem_lookup (k + off) mx = Some b) ->
    (evalDSHBinOp mem n off df σ mx mb = inr ma) ->
    h_opt_err_c (=) (mem_lookup k ma) (evalIBinCType mem σ df k a b).
  Proof.
    intros A B E.
    revert mb a b A B E.
    induction n; intros.
    -
      inversion kc.
    -
      simpl in *.
      repeat break_match_hyp; try some_none; try inl_inr.
      destruct (Nat.eq_dec k n).
      +
        clear IHn.
        subst k.
        unfold mem_lookup_err, trywith in *.
        repeat break_match; try inl_inr.
        repeat some_inv; repeat inl_inr_inv; subst.
        eq_to_equiv_hyp.
        err_eq_to_equiv_hyp.
        rewrite A in *; clear A c.
        rewrite B in *; clear B c0.

        assert (mem_lookup n ma = Some c1).
        {
          eapply evalDSHBinOp_preservation.
          eassumption.
          Unshelve.
          reflexivity.
        }

        clear - Heqe1 H.
        rewrite Heqe1, H.
        constructor.
        reflexivity.
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
        (mem : memory)
        (ME: evalDSHBinOp mem n off df σ mx mb = inr ma):
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
  
  
  (* This is generalized version of [evalDSHBinOp_nth]
     TODO see if we can replace [evalDSHBinOp_nth] with it
     or at lease simplify its proof using this lemma.
  *)
  Lemma evalDSHBinOp_equiv_inr_spec
        {off n: nat}
        {df : AExpr}
        `{dft : DSHIBinCarrierA df}
        {σ : evalContext}
        {mem : memory}
        {mx mb ma : mem_block}:
    (evalDSHBinOp mem n off df σ mx mb = inr ma)
    ->
    (∀ k (kc: k < n),
        ∃ a b,
          (mem_lookup k mx = Some a /\
           mem_lookup (k+off) mx = Some b /\
           (exists c,
               mem_lookup k ma = Some c /\
               evalIBinCType mem σ df k a b = inr c))
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
      repeat break_match_hyp; try some_none; try inl_inr.
      destruct (Nat.eq_dec k n).
      +
        clear IHn.
        subst k.
        unfold mem_lookup_err, trywith in *.
        repeat break_match; try inl_inr.
        repeat some_inv; repeat inl_inr_inv; subst.
        eq_to_equiv_hyp.
        err_eq_to_equiv_hyp.
        rewrite A in *; clear A c.
        rewrite B in *; clear B c0.
        exists c1.

        assert (mem_lookup n ma = Some c1).
        {
          eapply evalDSHBinOp_preservation.
          eassumption.
          Unshelve.
          reflexivity.
        }

        rewrite Heqe1, H.
        auto.
      +
        apply IHn with (mb:=mem_add n c1 mb); auto.
        lia.
  Qed.
  
  (* TODO: generalize this *)
  Lemma is_OK_evalDSHBinOp_mem_equiv
        (n off : nat)
        (df : AExpr)
        (σ : evalContext)
        (mem : memory)
        (mx ma mb : mem_block) :
    ma = mb ->
    is_OK (evalDSHBinOp mem n off df σ mx ma) <->
    is_OK (evalDSHBinOp mem n off df σ mx mb).
  Proof.
    intros.
    pose proof evalDSHBinOp_proper mem n off df σ mx mx.
    unfold Proper, respectful in H0.
    assert (T : mx = mx) by reflexivity;
      specialize (H0 T ma mb H); clear T.
    unfold is_Some.
    repeat break_match; try reflexivity; inversion H0.
    split; constructor.
    split; intros C; inversion C.
  Qed.
  
  Lemma is_OK_evalDSHBinOp_mem_add
        (n off : nat)
        (df : AExpr)
        (mem : memory)
        (σ : evalContext)
        (mx mb : mem_block)
        (k : NM.key)
        (v : CarrierA) :
    is_OK (evalDSHBinOp mem n off df σ mx (mem_add k v mb)) <->
    is_OK (evalDSHBinOp mem n off df σ mx mb).
  Proof.
    dependent induction n; [split; constructor |].
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
        (mem : memory)
        (σ : evalContext)
        (df : AExpr)
        (n : nat) :
    (exists a b, is_OK (evalIBinCType mem σ df n a b)) ->
    forall c d, is_OK (evalIBinCType mem σ df n c d).
  Proof.
    intros.
    destruct H as [a [b H]].
    induction df; cbn in *.
    
    (* base case 1 *)
    destruct v.
    constructor.
    destruct v.
    constructor.
    apply H.
    
    (* base case 2 *)
    trivial.
    
    (* base case 3 *)
    {
      repeat break_match; try some_none; try inl_inr; exfalso.
      -
        apply err_equiv_eq in Heqe.
        contradict Heqe.
        apply is_OK_neq_inl.
        apply eq_inr_is_OK in Heqe0.
        clear - Heqe0; rename Heqe0 into H.
        destruct m; cbn in *.
        +
          destruct p.
          destruct v; [| destruct v].
          inversion H.
          inversion H.
          apply H.
        +
          trivial.
      -
        apply err_equiv_eq in Heqe.
        contradict Heqe.
        apply is_OK_neq_inl.
        apply eq_inr_is_OK in Heqe0.
        clear - Heqe0; rename Heqe0 into H.
        destruct m; cbn in *.
        +
          destruct p.
          destruct v; [| destruct v].
          inversion H.
          inversion H.
          apply H.
        +
          trivial.
      -
        apply err_equiv_eq in Heqe0.
        contradict Heqe0.
        apply is_OK_neq_inl.
        apply eq_inr_is_OK in Heqe2.
        clear - Heqe2; rename Heqe2 into H,
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
        all: repeat break_match; try reflexivity; try some_none; try inl_inr.
        all: try apply IHe; try apply IHe1; try apply IHe2.
        all: constructor.
      -
        apply err_equiv_eq in Heqe0.
        contradict Heqe0.
        apply is_OK_neq_inl.
        apply eq_inr_is_OK in Heqe2.
        clear - Heqe2; rename Heqe2 into H,
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
        all: repeat break_match; try reflexivity; try some_none; try inl_inr.
        all: try apply IHe; try apply IHe1; try apply IHe2.
        all: constructor.
    }
    
    (* inductive cases *)
    all: unfold evalIBinCType in *.
    all: repeat break_match; try reflexivity; try some_none; try inl_inr.
    all: try apply IHdf; try apply IHdf1; try apply IHdf2.
    all: constructor.
  Qed.
  
  Lemma evalDSHBinOp_is_OK_inv
        {mem : memory}
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
           is_OK (evalIBinCType mem σ df k a b)
          )
    ) -> (is_OK (evalDSHBinOp mem n off df σ mx mb)).
  Proof.
    intros H.
    induction n; [constructor |].
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
      err_eq_to_equiv_hyp.
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

  Lemma evalDSHBinOp_is_Err
        (mem : memory)
        (off n: nat)
        (nz: n≢0)
        (df : AExpr)
        `{dft : DSHIBinCarrierA df}
        (σ : evalContext)
        (mx mb : mem_block):
    (exists k (kc:k<n),
        is_None (mem_lookup k mx) \/ is_None (mem_lookup (k+off) mx))
    ->
    is_Err (evalDSHBinOp mem n off df σ mx mb).
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
        (mem : memory)
        (off n: nat)
        (df : AExpr)
        `{dft : DSHIBinCarrierA df}
        (σ : evalContext)
        {EC : EnvMemoryConsistent σ mem}
        {dfs:TypeSig}
        (TS : TypeSigAExpr df = Some dfs)
        (TC: typecheck_env 3 dfs σ)
        (mx mb : mem_block):
    is_Err (evalDSHBinOp mem n off df σ mx mb) ->
    (exists k (kc:k<n),
        is_None (mem_lookup k mx) \/ is_None (mem_lookup (k+off) mx)).
  Proof.
    revert mb.
    induction n.
    -
      crush.
      inversion H.
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
        err_eq_to_equiv_hyp.
        contradict Heqe1.
        apply is_OK_neq_inl.
        unfold evalIBinCType.
        assert (AExprTypeSigIncludes df dfs)
          by (unfold AExprTypeSigIncludes;
              eexists; split; [eassumption | apply TypeSigIncluded_reflexive]).
        eapply evalAExpr_is_OK.
        Unshelve.
        2: {repeat constructor. assumption. }
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
        apply MaybeMapsTo_Compat with (t1:=DSHIBinCarrierA_TypeSig); eauto.
        cbn; unfold TP.uncurry; simpl.
        apply TM.add_1; reflexivity.
  
        apply typecheck_env_S.
        apply MaybeMapsTo_Compat with (t1:=DSHIBinCarrierA_TypeSig); eauto.
        cbn; unfold TP.uncurry; simpl.
        repeat (apply TM.add_2; [lia|]).
        apply TM.add_1; reflexivity.
  
        apply typecheck_env_S.
        apply MaybeMapsTo_Compat with (t1:=DSHIBinCarrierA_TypeSig); eauto.
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
        (mem : memory)
        (n off : nat)
        (df : AExpr)
        `{dft : DSHIBinCarrierA df}
        {dfs: TypeSig}
        (σ0 σ1 : evalContext)
        {EC0 : EnvMemoryConsistent σ0 mem}
        {EC1 : EnvMemoryConsistent σ1 mem}
        (m0 m1: mem_block):
    TypeSigAExpr df = Some dfs ->
    context_equiv_at_TypeSig_off dfs 3 σ0 σ1 ->
    evalDSHBinOp mem n off df σ0 m0 m1 = evalDSHBinOp mem n off df σ1 m0 m1.
  Proof.
    intros H E.
    unfold equiv, option_Equiv.
    destruct_err_equiv.
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
  
        apply evalDSHBinOp_is_Err with (mem:=mem) (df:=df) (σ:=σ1) (mb:=m1) in Ha.
        clear - Ha Hb.
        inversion Ha; inversion Hb.
        rewrite <-H0 in H1.
        inl_inr.
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
  
        apply evalDSHBinOp_is_Err with (mem:=mem) (df:=df) (σ:=σ0) (mb:=m1) in Hb.
        clear - Ha Hb.
        inversion Ha; inversion Hb.
        rewrite <-H0 in H1.
        inl_inr.
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
          enough (evalIBinCType mem σ0 df k a1 b1 = evalIBinCType mem σ1 df k a1 b1)
           by (rewrite C0, C1; rewrite E0, E1 in H0; inl_inr_inv; rewrite H0; reflexivity).
          rename a1 into a, b1 into b.
          unfold evalIBinCType in *.
  
          eapply evalAExpr_context_equiv_at_TypeSig with (ts:=dfs).
          unfold AExprTypeSigIncludes.
          eexists. split.
          eassumption.
          apply TypeSigIncluded_reflexive.
  
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
          apply TypeSigCompat_at with (k:=k) (e:=t) in D1; eauto.
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
          --
            destruct k; [| destruct k; [| destruct k; [| lia]]].
            all: clear; cbv; eexists.
            do 2 constructor 2; repeat constructor.
            constructor 2; repeat constructor.
            repeat constructor.
        *
          apply evalDSHBinOp_oob_preservation with (k0:=k) in Ha; try lia.
          apply evalDSHBinOp_oob_preservation with (k0:=k) in Hb; try lia.
          rewrite <- Ha, <- Hb.
          reflexivity.
  
          Unshelve.
          all: do 3 constructor; assumption.
  Qed.

End BinCarrierA.

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
  intros EE.
  unfold blocks_equiv_at_Pexp in *.
  destruct (evalPexp σ0 y_p), (evalPexp σ1 y_p); try (inversion EE; fail).
  constructor.
  inversion_clear EE.
  rewrite inr_neq in NY0.
  rewrite inr_neq in NY1.
  unfold memory_lookup, memory_remove in *.
  rewrite 2!NP.F.remove_neq_o; auto.
Qed.

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
  intros E0 E1 EE.
  unfold blocks_equiv_at_Pexp in *.
  destruct (evalPexp σ0 p), (evalPexp σ1 p); try (inversion EE; fail).
  constructor.
  inversion_clear EE.
  inversion H. clear H.
  symmetry in H0, H1.
  rewrite inr_neq in E0.
  rewrite inr_neq in E1.
  unfold memory_lookup, memory_set in *.
  rewrite 2!NP.F.add_neq_o; auto.
  rewrite H0, H1.
  constructor.
  apply H2.
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

Lemma SHCOL_DSHCOL_mem_block_equiv_comp (m0 m1 m2 d01 d12 : mem_block) :
  SHCOL_DSHCOL_mem_block_equiv m0 m1 d01 →
  SHCOL_DSHCOL_mem_block_equiv m1 m2 d12 →
  SHCOL_DSHCOL_mem_block_equiv m0 m2 (MMemoryOfCarrierA.mem_union d12 d01).
Proof.
  intros D01' D12'.
  unfold SHCOL_DSHCOL_mem_block_equiv in *.
  intro k.
  specialize (D01' k); specialize (D12' k).
  unfold mem_lookup, MMemoryOfCarrierA.mem_union in *.
  rewrite NP.F.map2_1bis by reflexivity.
  inversion_clear D01' as [D01 E01| D01 E01];
  inversion_clear D12' as [D12 E12| D12 E12].
  all: try apply is_None_def in D01.
  all: try apply is_None_def in D12.
  all: try apply is_Some_def in D01.
  all: try apply is_Some_def in D12.
  -
    constructor 1.
    rewrite D01, D12; reflexivity.
    rewrite E01, E12; reflexivity.
  -
    destruct D12 as [x D12].
    constructor 2.
    rewrite D01, D12; reflexivity.
    rewrite E12, D12; reflexivity.
  -
    destruct D01 as [x D01].
    constructor 2.
    rewrite D12, D01; reflexivity.
    rewrite D12, <-E01, E12; reflexivity.
  -
    destruct D01 as [x1 D01].
    destruct D12 as [x2 D12].
    constructor 2.
    rewrite D12; reflexivity.
    rewrite D12, E12, D12; reflexivity.
Qed.

Definition compose2 {A B C D : Type} (g : C -> D) (f : A -> B -> C) : A -> B -> D :=
  fun a b => g (f a b).

Fact eq_equiv_option_CarrierA (a1 a2 : option CarrierA) :
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

Lemma memory_lookup_err_inl_None
      (msg msg' : string)
      (mem : memory)
      (n : mem_block_id)
  :
    memory_lookup_err msg mem n = inl msg' <->
    memory_lookup mem n = None.
Proof.
  unfold memory_lookup_err, trywith.
  split; intros.
  all: break_match.
  all: inversion H.
  all: constructor.
Qed.

Lemma memory_lookup_err_inr_Some
      (msg : string)
      (mem : memory)
      (n : mem_block_id)
      (mb : mem_block)
  :
    memory_lookup_err msg mem n = inr mb <->
    memory_lookup mem n = Some mb.
Proof.
  unfold memory_lookup_err, trywith.
  split; intros.
  all: break_match.
  all: inversion H.
  all: rewrite H2.
  all: reflexivity.
Qed.


(** * MSHEmbed, MSHPick **)

Global Instance Assign_DSH_pure
       {x_n y_n : NExpr}
       {x_p y_p : PExpr}
       {ts : TypeSig}
  :
    DSH_pure (DSHAssign (x_p, x_n) (y_p, y_n)) ts x_p y_p.
Proof.
  split.
  -
    intros.
    destruct fuel; [inversion H |].
    cbn in H.
    repeat break_match; repeat some_inv; try inl_inr.
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
    intros.
    unfold memory_equiv_except, memory_lookup; intros.
    destruct fuel; [inversion H |].
    cbn in H.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
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
  constructor; intros mx mb MX MB.
  destruct mem_op as [md |] eqn:MD, evalDSHOperator as [fma |] eqn:FMA; try constructor.
  2: exfalso.
  all: unfold lookup_Pexp in MX, MB.
  all: cbn in *.
  all: destruct evalPexp eqn:XP in MX; try some_none; try inl_inr; rewrite XP in *.
  all: destruct evalPexp eqn:YP in MB; try some_none; try inl_inr; rewrite YP in *.
  all: unfold Embed_mem,
              map_mem_block_elt,
              MMemoryOfCarrierA.mem_lookup,
              MMemoryOfCarrierA.mem_add,
              MMemoryOfCarrierA.mem_empty
         in MD.
  all: unfold memory_lookup_err, trywith in *.
  all: repeat break_match;
    try some_none; repeat some_inv;
    try inl_inr; repeat inl_inr_inv.
  all: try (inversion MX; fail).
  all: try (inversion MB; fail).
  all: subst.
  -
    exfalso.
    unfold mem_lookup_err, trywith in *.
    break_match; try inl_inr.
    enough (None = Some c) by some_none.
    rewrite <-Heqo2, <-Heqo3.
    unfold mem_lookup.
    inversion MX.
    apply H1.
  -
    repeat constructor.
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
      unfold mem_lookup_err, trywith in Heqe2.
      break_match_hyp; try inl_inr; inl_inr_inv; subst.
      rewrite <-Heqo2, <-Heqo3.
      unfold mem_lookup.
      inversion MX.
      apply H1.
    +
      constructor 1; [reflexivity |].
      symmetry.
      inversion MB.
      apply H1.
  -
    constructor.
  -
    exfalso.
    unfold mem_lookup_err, trywith in Heqe2.
    break_match; try inl_inr.
    enough (Some c0 = None) by some_none.
    rewrite <-Heqo2, <-Heqo3.
    unfold mem_lookup.
    inversion MX.
    apply H1.
Qed.

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
  constructor; intros mx mb MX MB.
  destruct mem_op as [md |] eqn:MD, evalDSHOperator as [fma |] eqn:FMA; try constructor.
  2: exfalso.
  all: unfold lookup_Pexp in MX, MB.
  all: cbn in *.
  all: destruct evalPexp eqn:XP in MX; try some_none; try inl_inr; rewrite XP in *.
  all: destruct evalPexp eqn:YP in MB; try some_none; try inl_inr; rewrite YP in *.
  all: unfold Pick_mem,
              map_mem_block_elt,
              MMemoryOfCarrierA.mem_lookup,
              MMemoryOfCarrierA.mem_add,
              MMemoryOfCarrierA.mem_empty
         in MD.
  all: unfold memory_lookup_err, trywith in *.
  all: repeat break_match;
    try some_none; repeat some_inv;
    try inl_inr; repeat inl_inr_inv.
  all: try (inversion MX; fail).
  all: try (inversion MB; fail).
  all: subst.
  all: repeat constructor.
  1,3: exfalso.
  -
    enough (None = Some c) by some_none.
    unfold mem_lookup_err, trywith in Heqe2.
    break_match; try inl_inr.
    rewrite <-Heqo1, <-Heqo2.
    unfold mem_lookup.
    rewrite X.
    inversion MX.
    apply H1.
  -
    unfold mem_lookup_err, trywith in Heqe2.
    break_match; try inl_inr.
    enough (Some c0 = None) by some_none.
    rewrite <-Heqo1, <-Heqo2.
    unfold mem_lookup.
    rewrite X.
    inversion MX.
    apply H1.
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
      unfold mem_lookup_err, trywith in Heqe2.
      break_match; try inl_inr.
      inversion Heqe2; subst.
      rewrite <-Heqo2, <-Heqo1.
      inversion MX.
      rewrite X.
      apply H1.
    +
      constructor 1; [reflexivity |].
      symmetry.
      inversion MB.
      apply H1.
Qed.


(** * MSHPointwise  *)

Global Instance IMap_DSH_pure
       {nn : nat}
       {x_p y_p : PExpr}
       {a : AExpr}
       {ts : TypeSig}
  :
    DSH_pure (DSHIMap nn x_p y_p a) ts x_p y_p.
Proof.
  constructor.
  -
    intros.
    destruct fuel; [inversion H |].
    cbn in H.
    repeat break_match; repeat some_inv; try inl_inr.
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
    intros.
    unfold memory_equiv_except, memory_lookup; intros.
    destruct fuel; [inversion H |].
    cbn in H.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    unfold equiv, memory_Equiv, memory_set, mem_add in H.
    specialize (H k).
    rewrite <-H.
    cbv in H0; subst.
    rewrite NP.F.add_neq_o by congruence.
    reflexivity.
Qed.

Global Instance Pointwise_MSH_DSH_compat
       {n: nat}
       (f: FinNat n -> CarrierA -> CarrierA)
       `{pF: !Proper ((=) ==> (=) ==> (=)) f}
       (a : AExpr)
       (x_p y_p : PExpr)
       (σ : evalContext)
       (m : memory)
       (ts: TypeSig)
       `{TSI: AExprTypeSigIncludes a ts}
       {P : DSH_pure (DSHIMap n x_p y_p a) ts x_p y_p}
  :
    MSH_DSH_compat (@MSHPointwise n f pF) (DSHIMap n x_p y_p a) σ m x_p y_p.
Admitted.

(** * MSHBinOp  *)

Global Instance BinOp_DSH_pure
       {o : nat}
       {x_p y_p : PExpr}
       {a: AExpr}
       {ts: TypeSig}
  :
    DSH_pure (DSHBinOp o x_p y_p a) ts x_p y_p.
Proof.
  split.
  -
    intros.
    destruct fuel; [inversion H |].
    cbn in H.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    rewrite <-H.
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
    intros σ m m' fuel E y_i P.
    destruct fuel; cbn in E; [some_none |].

    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    err_eq_to_equiv_hyp.
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
       `{MSH_DSH_IBinCarrierA_compat _ f σ df m}
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
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv;
      subst.
    1-3: exfalso.
    +
      clear - MX Heqe1.
      err_eq_to_equiv_hyp.
      rewrite memory_lookup_err_inr_Some in *.
      rewrite memory_lookup_err_inl_None in *.
      rewrite MX in Heqe1.
      some_none.
    +
      clear - MB Heqe2.
      err_eq_to_equiv_hyp.
      rewrite memory_lookup_err_inr_Some in *.
      rewrite memory_lookup_err_inl_None in *.
      rewrite MB in Heqe2.
      some_none.
    +
      (* mem_op succeeded with [Some md] while evaluation of DHS failed *)

      eq_to_equiv_hyp; err_eq_to_equiv_hyp.
      rewrite memory_lookup_err_inr_Some in *.
      rewrite MB, MX in *.
      repeat some_inv.
      rewrite <-Heqe1, <-Heqe2 in *.
      clear Heqe1 Heqe2 m2 m3.

      rename Heqe3 into E.

      apply equiv_Some_is_Some in MD.
      pose proof (mem_op_of_hop_x_density MD) as DX.
      clear MD pF.

      inversion_clear H as [_ FV].

      contradict E.
      apply is_OK_neq_inl.


      assert (TS : AExprTypeSigIncludes df dfs)
        by (unfold AExprTypeSigIncludes; exists dfs;
            split; [assumption | apply TypeSigIncluded_reflexive]).
      apply evalDSHBinOp_is_OK_inv; [assumption |].

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
      cbn in FV.
      eapply inr_is_OK.
      eassumption.
    +
      constructor.
      unfold memory_lookup_err, trywith, memory_lookup, memory_set.
      rewrite NP.F.add_eq_o by reflexivity.
      constructor.
      repeat some_inv.

      eq_to_equiv_hyp; err_eq_to_equiv_hyp.
      rewrite memory_lookup_err_inr_Some in *.
      rewrite MB, MX in *.
      repeat some_inv.
      rewrite <-Heqe1, <-Heqe2 in *.
      clear Heqe1 Heqe2 m2 m3.

      rename Heqe3 into ME.
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


          specialize FV with (nc:=mkFinNat kc) (a:=a) (b:=b).
          cbn in FV.

          pose proof (evalDSHBinOp_nth m k kc A B ME) as T.
          inversion T; [rewrite <-H in FV; inl_inr | clear T].
          unfold mem_lookup in H.
          rewrite <-H.
          rewrite <-H0 in FV.
          inversion FV.
          subst.
          
          pose proof (mem_block_to_avector_nth Heqo0 (kc:=kc1)) as MVA.
          pose proof (mem_block_to_avector_nth Heqo0 (kc:=kc2)) as MVB.
          rewrite MVA, MVB in *.
          repeat some_inv.
          rewrite A, B.
          rewrite <-H4.
          rewrite H1.
          reflexivity.
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
          apply (evalDSHBinOp_oob_preservation m ME), kc.
  -
    unfold lookup_Pexp in *.
    simpl in *.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    all: try constructor.
    exfalso.


    eq_to_equiv_hyp; err_eq_to_equiv_hyp.
    rewrite memory_lookup_err_inr_Some in *.
    rewrite MB, MX in *.
    repeat some_inv.
    rewrite <-Heqe1, <-Heqe2 in *.
    clear Heqe1 Heqe2 m2 m3.

    apply Some_nequiv_None in MX.
    contradict MX.

    unfold mem_op_of_hop in MD.
    break_match_hyp; try some_none.
    clear MD.
    rename Heqo0 into MX.
    unfold mem_block_to_avector in MX.
    apply vsequence_Vbuild_eq_None in MX.
    apply is_None_equiv_def; [typeclasses eauto |].
    destruct o.
    *
      destruct MX as [k [kc MX]].
      inversion kc.
    *
      contradict Heqe3.
      enough (T : is_Err (evalDSHBinOp m (S o) (S o) df σ mx mb))
        by (destruct (evalDSHBinOp m (S o) (S o) df σ mx mb);
            [intros C; inl_inr | inversion T ]).
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
Qed.

(** * MSHInductor *)

Global Instance Power_DSH_pure
       {n : NExpr}
       {x_n y_n : NExpr}
       {x_p y_p : PExpr}
       {a : AExpr}
       {ts : TypeSig}
       {initial : CarrierA}
  :
    DSH_pure (DSHPower n (x_p, x_n) (y_p, y_n) a initial) ts x_p y_p.
Proof.
  split.
  -
    intros.
    destruct fuel; [inversion H |].
    cbn in H.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    rewrite <-H.
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
    intros.
    unfold memory_equiv_except, memory_lookup; intros.
    destruct fuel; [inversion H |].
    cbn in H.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    subst.
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

Global Instance evalDSHPower_Proper :
  Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=)) evalDSHPower.
Proof.
  unfold Proper, respectful.
  intros m m' M σ σ' Σ n n' N
         f f' F x x' X y y' Y
         xo xo' XO yo yo' YO.
  inversion_clear N; inversion_clear XO; inversion_clear YO.
  clear n xo yo.
  rename n' into n, xo' into xo, yo' into yo.
  generalize dependent y.
  generalize dependent y'.
  induction n; intros.
  -
    cbn.
    rewrite Y.
    reflexivity.
  -
    cbn.
    repeat break_match; try constructor.
    all: err_eq_to_equiv_hyp.

    (* memory lookups *)
    all: try rewrite X in Heqe.
    all: try rewrite Y in Heqe0.
    all: try rewrite Heqe in *.
    all: try rewrite Heqe0 in *.
    all: try inl_inr; repeat inl_inr_inv.
    all: rewrite Heqe2 in *.
    all: rewrite Heqe3 in *.

    (* AExp evaluation (evalBinCType *)
    all: rewrite M, Σ, F in Heqe1.
    all: rewrite Heqe1 in Heqe4.
    all: try inl_inr; repeat inl_inr_inv.

    eapply IHn.
    rewrite Y, Heqe4.
    reflexivity.
Qed.

(* likely to change *)
Global Instance Inductor_MSH_DSH_compat
       (σ : evalContext)
       (n : nat)
       (nx : NExpr)
       (N : evalNexp σ nx = inr n)
       (m : memory)
       (f : CarrierA -> CarrierA -> CarrierA)
       `{PF : !Proper ((=) ==> (=) ==> (=)) f}
       (ts : TypeSig)
       (init : CarrierA)
       (a : AExpr)
       `{FA : MSH_DSH_BinCarrierA_compat f σ a m}
       (x_p y_p : PExpr)
       `{PD : DSH_pure (DSHPower nx (x_p, NConst 0) (y_p, NConst 0) a init) ts x_p y_p}
  :
    @MSH_DSH_compat _ _
      (MSHInductor n f init)
      (DSHPower nx (x_p, NConst 0) (y_p, NConst 0) a init)
      ts σ m x_p y_p PD.
Proof.
  constructor; intros x_m y_m X_M Y_M.
  assert (T : evalNexp σ nx ≡ inr n)
    by (inversion N; inversion H1; reflexivity);
    clear N; rename T into N.
  destruct mem_op as [mma |] eqn:MOP.
  all: destruct evalDSHOperator as [r |] eqn:DOP; [destruct r as [msg | dma] |].
  all: repeat constructor.
  1,3,4: exfalso; admit.
  -
    unfold lookup_Pexp; cbn.
    cbn in DOP.
    destruct (evalPexp σ x_p) as [| x_id] eqn:X;
      [unfold lookup_Pexp in X_M; rewrite X in X_M; inversion X_M |].
    destruct (evalPexp σ y_p) as [| y_id] eqn:Y;
      [unfold lookup_Pexp in Y_M; rewrite Y in Y_M; inversion Y_M |].
    destruct (memory_lookup dma y_id) as [y_dma |] eqn:Y_DMA.
    unfold memory_lookup_err.
    +
      rewrite Y_DMA.
      constructor.
      unfold SHCOL_DSHCOL_mem_block_equiv.
      intro k.


      cbn in X_M; rewrite X in X_M.
      cbn in Y_M; rewrite Y in Y_M.

      unfold memory_lookup_err, trywith in *.

      destruct (memory_lookup m x_id) eqn:X_M'; inversion X_M; subst;
        clear X_M; rename m0 into x_m', H1 into XME.
      destruct (memory_lookup m y_id) eqn:y_M'; inversion Y_M; subst;
        clear Y_M; rename m0 into y_m', H1 into YME.

      (* simplify DOP down to evalDSHPower *)
      cbn in DOP; some_inv; rename H0 into DOP.
      rewrite N in DOP.
      repeat break_match; try inl_inr.
      inl_inr_inv.
      rename m0 into pm, Heqe into PM,
             H0 into DMA.
      rewrite <-DMA in *.
      unfold memory_lookup, memory_set in Y_DMA.
      rewrite NP.F.add_eq_o in Y_DMA by reflexivity.
      replace pm with y_dma in * by congruence; clear Y_DMA; rename PM into Y_DMA.

      (* make use of MOP *)
      cbn in MOP.
      unfold mem_op_of_hop in MOP.
      break_match; try some_none.
      some_inv.
      rename t into x_v, Heqo into X_V.

      destruct (Nat.eq_dec k 0) as [KO | KO].
      * (* the changed part of the block*)
        subst.
        cbn.
        constructor 2; [reflexivity |].
        destruct (mem_lookup 0 y_dma) as [ydma0 |] eqn:YDMA0.
        --
          clear N PD.
          err_eq_to_equiv_hyp.
          generalize dependent y_dma.
          generalize dependent init.
          induction n; intros.
          ++ (* induction base *)
            cbn in Y_DMA.
            inl_inr_inv.
            rewrite <-YDMA0.
            clear ydma0 YDMA0.
            rewrite <-Y_DMA; clear Y_DMA.
            unfold mem_lookup, mem_add.
            rewrite NP.F.add_eq_o by reflexivity.
            reflexivity.
          ++ (* inductive step *)

            (* simplify Y_DMA *)
            cbn in Y_DMA.
            unfold mem_lookup_err in Y_DMA.
            replace (mem_lookup 0 (mem_add 0 init y_m'))
              with (Some init)
              in Y_DMA
              by (unfold mem_lookup, mem_add;
                  rewrite NP.F.add_eq_o by reflexivity;
                  reflexivity).
            cbn in Y_DMA.
            destruct (mem_lookup 0 x_m') as [xm'0|] eqn:XM'0;
              cbn in Y_DMA; try inl_inr.
            inversion FA; clear bin_typechecks0 FA;
              rename bin_equiv0 into FA; specialize (FA init xm'0 ).
            destruct (evalBinCType m σ a init xm'0 ) as [|df] eqn:DF;
              try inl_inr; inl_inr_inv.
            (* abstract: this gets Y_DMA to "the previous step" for induction *)
            rewrite mem_add_overwrite in Y_DMA.

            apply mem_block_to_avector_nth with (kc:=le_n 1) (k := 0) in X_V.
            rewrite Vnth_1_Vhead in X_V.
            assert (T : xm'0 = Vhead x_v).
            {
              enough (Some xm'0 = Some (Vhead x_v)) by (some_inv; assumption).
              rewrite <-X_V, <-XM'0, XME; reflexivity.
            }
            rewrite T in FA; clear T.
            
            (* applying induction hypothesis *)
            apply IHn in Y_DMA; [| assumption].

            rewrite Y_DMA, FA.

            unfold HCOLImpl.Inductor.
            rewrite nat_rect_succ_r.
            reflexivity.
        --
          clear - Y_DMA YDMA0.
          eq_to_equiv_hyp.
          err_eq_to_equiv_hyp.
          contradict YDMA0.
          generalize dependent init.
          induction n; cbn in *.
          ++
            intros.
            inversion Y_DMA; subst.
            rewrite <-H1.
            unfold mem_lookup, mem_add.
            rewrite NP.F.add_eq_o by reflexivity.
            intros C; inversion C.
          ++
            intros.
            repeat break_match; try inl_inr.
            eapply IHn.
            rewrite <-Y_DMA.
            f_equiv.
            rewrite mem_add_overwrite.
            reflexivity.
      * (* the preserved part of the block *)
        constructor 1;
          [cbn; break_match; try reflexivity;
           contradict KO; rewrite e; reflexivity |].
        inversion PD; clear PD mem_stable0; rename mem_write_safe0 into MWS.
        specialize (MWS σ m dma).
        admit.
    +
      exfalso.
      admit.
Admitted.


(** * MSHIUnion *)

Global Instance Loop_DSH_pure
       {n : nat}
       {dop : DSHOperator}
       {ts : TypeSig}
       {x_p y_p : PExpr}
       (P : DSH_pure dop (TypeSig_add ts DSHnat) (incrPVar 0 x_p) (incrPVar 0 y_p))
  :
    DSH_pure (DSHLoop n dop) ts x_p y_p.
Proof.
  split.
  -
    intros.
    destruct fuel; [inversion H |].
    generalize dependent fuel.
    generalize dependent m'.
    induction n.
    +
      intros.
      cbn in *.
      some_inv; inl_inr_inv.
      rewrite H; reflexivity.
    +
      intros.
      cbn in H.
      repeat break_match;
        try some_none; repeat some_inv;
        try inl_inr; repeat inl_inr_inv.
      subst.
      destruct fuel; [inversion Heqo |].
      eq_to_equiv_hyp.
      apply IHn in Heqo.
      rewrite Heqo.
      clear - P H.
      inversion P.
      eapply mem_stable0.
      eassumption.
  -
    intros.
    destruct fuel; [inversion H |].
    generalize dependent fuel.
    generalize dependent m'.
    induction n.
    +
      intros.
      cbn in *.
      some_inv; inl_inr_inv.
      unfold memory_equiv_except.
      intros.
      rewrite H.
      reflexivity.
    +
      intros.
      cbn in H.
      repeat break_match;
        try some_none; repeat some_inv;
        try inl_inr; repeat inl_inr_inv.
      subst.
      destruct fuel; [inversion Heqo |].
      eq_to_equiv_hyp.
      apply IHn in Heqo.
      unfold memory_equiv_except in *.
      intros.
      rewrite Heqo by assumption.
      inversion P.
      unfold memory_equiv_except in *.
      eapply mem_write_safe0.
      eassumption.
Admitted.

(* NOTE: requires connection between [opf] and [dop] *)
Global Instance IUnion_MSH_DSH_compat
       {i o n : nat}
       {dop : DSHOperator}
       {ts : TypeSig}
       {x_p y_p : PExpr}
       {σ : evalContext}
       {m : memory}
       {opf : MSHOperatorFamily}
       (P : DSH_pure (DSHLoop n dop) ts x_p y_p)
  :
    @MSH_DSH_compat _ _ (@MSHIUnion i o n opf) (DSHLoop n dop) ts σ m x_p y_p P.
Proof.
  constructor.
  intros x_m y_m XM YM.
  destruct (mem_op (MSHIUnion opf) x_m) as [mm |] eqn:MM.
  all: destruct (evalDSHOperator σ (DSHLoop n dop) m (estimateFuel (DSHLoop n dop)))
    as [dm |] eqn:DM; [destruct dm as [| dm] |].
  all: repeat constructor.
  1,3,4: exfalso; admit.
  -
    destruct (lookup_Pexp σ dm y_p) as [| y_dm] eqn:YDM.
    +
      exfalso. admit.
    +
      constructor.
      unfold SHCOL_DSHCOL_mem_block_equiv.
      intro k.
      destruct (mem_lookup k mm) as [kmm |] eqn:KMM.
      *
        constructor 2; [reflexivity |].
        cbn in MM.
        break_match; [some_inv | some_none].
        rename l into xmbl, Heqo0 into XMBL, H0 into MM.


        induction n.
        --
          cbn in *.
          repeat some_inv; repeat inl_inr_inv; subst.
          cbn in *.
          inversion KMM.
        --
          cbn in DM.
          repeat break_match;
            try some_none; repeat some_inv;
            try inl_inr; repeat inl_inr_inv.
          subst.
          rewrite <-KMM in *; clear KMM.
          admit.
          (*
          specialize (IHn opf).
          eapply IHn.
          admit.
          instantiate (1 := opf).
          eapply XMBL.
          assumption.
           *)
      *
        constructor 1; [reflexivity |].
        admit.
Admitted.

(** * MSHIReduction *)

(* NOTE : this might require additional instances, e.g. [MemMap2_DSH_pure] *)
(* NOTE: is [mem_stable] provable here at all? Given the Alloc and Init *)
Global Instance IReduction_DSH_pure
       {no nn : nat}
       {x_p y_p y_p'': PExpr}
       {init : CarrierA}
       {rr : DSHOperator}
       {df : AExpr}
       {ts : TypeSig}
       (Y: y_p'' ≡ incrPVar 0 (incrPVar 0 y_p))
       (P: DSH_pure rr
                    (TypeSig_add (TypeSig_add ts DSHPtr) DSHnat)
                    (incrPVar 0 (incrPVar 0 x_p)) y_p'')
  :
    DSH_pure (DSHAlloc no
                       (DSHSeq
                          (DSHMemInit no (PVar 0) init)
                          (DSHLoop nn
                                   (DSHSeq
                                      rr
                                      (DSHMemMap2 no (PVar 1)
                                                  y_p''
                                                  y_p''
                                                  df)))))
             ts x_p y_p.
Proof.
  constructor.
  -
    intros.
    destruct fuel; [inversion H |].
    cbn in *.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    subst.

    destruct fuel; [inversion Heqo |].
    cbn in *.
    repeat break_match;
      try some_none; repeat some_inv;
      try inl_inr; repeat inl_inr_inv.
    subst.

    destruct fuel; [inversion Heqo |].
    induction nn.
    +
      cbn in *.
      repeat break_match;
        try some_none; repeat some_inv;
        try inl_inr; repeat inl_inr_inv.
      subst.
      admit.
    +
      admit.
  -
    admit.
Admitted.

Global Instance IReduction_MSH_DSH_compat
       {i o n no nn : nat}
       (initial: CarrierA)
       (dot: CarrierA -> CarrierA -> CarrierA)
       `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
       (op_family: @MSHOperatorFamily i o n)
       (df : AExpr)
       (ts : TypeSig)
       (x_p y_p t_i : PExpr)
       (rr : DSHOperator)
       {P : DSH_pure 
              (DSHAlloc no
                        (DSHSeq
                           (DSHMemInit no t_i initial)
                           (DSHLoop nn
                                    (DSHSeq
                                       rr
                                       (DSHMemMap2 no t_i y_p y_p df)))))
              ts x_p y_p}
       (σ : evalContext)
       (m : memory)
  :
    @MSH_DSH_compat
      _ _
      (@MSHIReduction i o n initial dot pdot op_family)
      (DSHAlloc no
                (DSHSeq
                   (DSHMemInit no t_i initial)
                   (DSHLoop nn
                            (DSHSeq
                               rr
                               (DSHMemMap2 no t_i y_p y_p df)))))
      ts σ m x_p y_p P.
Admitted.
      

(** * MSHCompose *)
Global Instance Compose_DSH_pure
         {n: nat}
         {x_p y_p: PExpr}
         {dop1 dop2: DSHOperator}
         {ts: TypeSig}
         (P2: DSH_pure dop2 (TypeSig_add ts DSHnat) (incrPVar 0 x_p) (PVar 0))
         (P1: DSH_pure dop1 (TypeSig_add ts DSHnat) (PVar 0) (incrPVar 0 y_p))
  : DSH_pure (DSHAlloc n (DSHSeq dop2 dop1)) ts x_p y_p.
Proof.
  split.
  - (* mem_stable *)
    intros σ m m' fuel H k.
    destruct P1 as [MS1 _].
    destruct P2 as [MS2 _].
    destruct fuel; simpl in *; try some_none.
    repeat break_match_hyp; try some_none.
    inversion H; inversion H2.
    destruct fuel; simpl in *; try some_none.
    break_match_hyp; try some_none; repeat some_inv; try inl_inr.
    rename Heqo into D1, Heqe0 into D2.
    inl_inr_inv. rewrite <- H. clear m' H.
    remember (memory_next_key m) as k'.

    destruct(Nat.eq_dec k k') as [E|NE].
    +
      break_match; [inversion D1 |].
      subst.
      split; intros H.
      *
        contradict H.
        apply mem_block_exists_memory_next_key.
      *
        contradict H.
        apply mem_block_exists_memory_remove.
    +
      break_match; [inversion D1 |].
      subst.
      rename Heqo0 into D2.
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
    (* mem_write_safe *)
    intros σ m0 m4 fuel H y_i H0.
    destruct fuel; simpl in *; try some_none.
    repeat break_match_hyp;
      try some_none; repeat some_inv; try inl_inr; repeat inl_inr_inv.
    destruct fuel; simpl in *; try some_none.
    repeat break_match_hyp;
      try some_none; repeat some_inv; try inl_inr; repeat inl_inr_inv.
    subst.
    rename m1 into m2, m into m3.
    rename Heqo into E1, Heqo0 into E2.
    remember (memory_next_key m0) as t_i.
    remember (memory_set m0 t_i mem_empty) as m1.
    remember (DSHPtrVal t_i n :: σ) as σ'.
    intros k ky.


    destruct (Nat.eq_dec k t_i) as [kt|kt].
    1:{

      subst k.
      pose proof (mem_block_exists_memory_next_key m0) as H1.
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

    destruct P1 as [P1p P1w].
    destruct P2 as [P2p P2w].
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

Global Instance Compose_MSH_DSH_compat
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
                              (DSHPtrVal (memory_next_key m) o2 :: σ)
                              (memory_alloc_empty m (memory_next_key m))
                              (incrPVar 0 x_p) (PVar 0)
                              P2
          }
         `{C1: forall m'', memory_equiv_except m m'' (memory_next_key m) ->
                      MSH_DSH_compat mop1 dop1
                                     (DSHPtrVal (memory_next_key m) o2 :: σ)
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

  remember (memory_next_key m) as t_i.
  remember (DSHPtrVal t_i o2 :: σ) as σ'.
  unfold memory_alloc_empty in *.
  remember (memory_set m t_i mem_empty) as m'.

  destruct (option_compose (mem_op mop1) (mem_op mop2) mx) as [md|] eqn:MD;
    repeat break_match;
    try some_none; repeat some_inv;
    try inl_inr; repeat inl_inr_inv;
    repeat constructor.

  -
    exfalso.
    unfold lookup_Pexp in *.
    simpl in MX, MB.
    repeat break_match_hyp; try some_none; repeat some_inv; try inl_inr.
    rename m1 into x_i, m0 into y_i.
    rename Heqo0 into E2.
    rewrite evalDSHOperator_estimateFuel_ge in E2 by lia.

    assert(t_i ≢ y_i).
    {
      destruct (Nat.eq_dec t_i y_i); auto.
      subst.
      exfalso.
      contradict MB.
      pose proof (memory_lookup_memory_next_key_is_None m) as F.
      apply is_None_def in F.
      unfold memory_lookup_err.
      rewrite F.
      intro C.
      inversion C.
    }

    assert(t_i ≢ x_i).
    {
      destruct (Nat.eq_dec t_i x_i); auto.
      subst.
      exfalso.
      contradict MX.
      pose proof (memory_lookup_memory_next_key_is_None m) as F.
      apply is_None_def in F.
      unfold memory_lookup_err.
      rewrite F.
      intro C.
      inversion C.
    }

    unfold memory_lookup, memory_remove.

    assert(mem_block_exists y_i m) as EY.
    {
      clear - MB.
      apply mem_block_exists_exists_equiv.
      unfold memory_lookup_err, trywith in MB.
      break_match; try inl_inr.
      exists m0; reflexivity.
      inversion MB.
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

    assert(MX': lookup_Pexp σ' m' (incrPVar 0 x_p) = inr mx).
    {
      rewrite Heqσ'.
      unfold lookup_Pexp.
      rewrite evalPexp_incrPVar.
      simpl.
      rewrite Heqe3.
      subst m'.
      unfold memory_lookup_err, memory_lookup, memory_set.
      rewrite NP.F.add_neq_o.
      apply MX.
      auto.
    }
    specialize (C2 MX').

    assert(MT': lookup_Pexp σ' m' (PVar 0) = inr mem_empty).
    {
      rewrite Heqσ'.
      unfold lookup_Pexp.
      subst m'.
      simpl.
      unfold memory_lookup_err, memory_lookup, memory_set.
      rewrite NP.F.add_eq_o; reflexivity.
    }
    specialize (C2 MT').

    rewrite E2 in C2.
    rewrite MT in C2.
    inversion C2.
  -
    exfalso.
    rename m0 into m''.
    unfold lookup_Pexp in *.
    simpl in MX, MB.
    repeat break_match_hyp; try some_none; repeat some_inv; try inl_inr.
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
      pose proof (memory_lookup_memory_next_key_is_None m) as F.
      apply is_None_def in F.
      unfold memory_lookup_err.
      rewrite F.
      intro C.
      inversion C.
    }

    assert(t_i ≢ x_i).
    {
      destruct (Nat.eq_dec t_i x_i); auto.
      subst.
      exfalso.
      contradict MX.
      pose proof (memory_lookup_memory_next_key_is_None m) as F.
      apply is_None_def in F.
      unfold memory_lookup_err.
      rewrite F.
      intro C.
      inversion C.
    }

    assert(mem_block_exists y_i m) as EY.
    {
      clear - MB.
      apply mem_block_exists_exists_equiv.
      unfold memory_lookup_err, trywith in MB.
      break_match; try inl_inr.
      exists m0; reflexivity.
      inversion MB.
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

    assert(MX': lookup_Pexp σ' m' (incrPVar 0 x_p) = inr mx).
    {
      rewrite Heqσ'.
      unfold lookup_Pexp.
      rewrite evalPexp_incrPVar.
      simpl.
      rewrite Heqe3.
      subst m'.
      unfold memory_lookup_err, memory_lookup, memory_set.
      rewrite NP.F.add_neq_o.
      apply MX.
      auto.
    }
    specialize (C2 MX').

    assert(MT': lookup_Pexp σ' m' (PVar 0) = inr mem_empty).
    {
      rewrite Heqσ'.
      unfold lookup_Pexp.
      subst m'.
      simpl.
      unfold memory_lookup_err, memory_lookup, memory_set.
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
    apply err_equiv_eq in MT''.
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
    assert(lookup_Pexp σ' m'' (incrPVar 0 y_p) = inr mb) as MB''.
    {
      subst σ'.
      unfold lookup_Pexp.
      rewrite evalPexp_incrPVar.
      simpl.
      rewrite Heqe2.

      destruct P2 as [_ mem_write_safe2].
      apply Option_equiv_eq in E2.
      specialize (mem_write_safe2 _ _ _ _ E2).

      assert(TS: evalPexp (DSHPtrVal t_i o2 :: σ) (PVar 0) = inr t_i)
        by reflexivity.
      specialize (mem_write_safe2 _ TS).

      assert(MB': memory_lookup m' y_i = Some mb).
      {
        assert (memory_lookup m y_i = Some mb).
        {
         clear - MB.
         unfold memory_lookup_err, trywith in MB.
         break_match; inversion MB.
         rewrite H1; reflexivity.
        }

        rewrite <-H1.
        subst m'.
        unfold memory_lookup, memory_set.
        rewrite NP.F.add_neq_o.
        reflexivity.
        assumption.
      }

      enough (T : memory_lookup m'' y_i = Some mb)
        by (unfold memory_lookup_err; rewrite T; reflexivity).
      rewrite <- MB'.
      symmetry.
      apply mem_write_safe2.
      auto.
    }

    specialize (C1 MB'').
    rewrite MD, E1 in C1.

    inversion C1.
  -
    rename m1 into m''.
    rename m0 into m'''.
    unfold lookup_Pexp in *.
    simpl in MX, MB.
    repeat break_match_hyp; try some_none; repeat some_inv; try inl_inr.
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
      pose proof (memory_lookup_memory_next_key_is_None m) as F.
      apply is_None_def in F.
      unfold memory_lookup_err.
      rewrite F.
      cbn.
      intros C; inl_inr.
    }

    assert(t_i ≢ x_i).
    {
      destruct (Nat.eq_dec t_i x_i); auto.
      subst.
      exfalso.
      contradict MX.
      pose proof (memory_lookup_memory_next_key_is_None m) as F.
      apply is_None_def in F.
      unfold memory_lookup_err.
      rewrite F.
      cbn.
      intros C; inl_inr.
    }

    unfold memory_lookup_err, memory_lookup, memory_remove.
    rewrite NP.F.remove_neq_o by assumption.

    assert(mem_block_exists y_i m) as EY.
    {
      apply mem_block_exists_exists_equiv.
      eexists.
      unfold memory_lookup_err, trywith in MB.
      break_match_hyp; inversion MB.
      constructor.
      apply H3.
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

    assert(MX': lookup_Pexp σ' m' (incrPVar 0 x_p) = inr mx).
    {
      rewrite Heqσ'.
      unfold lookup_Pexp.
      rewrite evalPexp_incrPVar.
      simpl.
      rewrite Heqe3.
      subst m'.
      unfold memory_lookup_err, memory_lookup, memory_set.
      rewrite NP.F.add_neq_o.
      apply MX.
      auto.
    }
    specialize (C2 MX').

    assert(MT': lookup_Pexp σ' m' (PVar 0) = inr mem_empty).
    {
      rewrite Heqσ'.
      unfold lookup_Pexp.
      subst m'.
      simpl.
      unfold memory_lookup_err, memory_lookup, memory_set.
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
    apply err_equiv_eq in MT''.
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
    assert(lookup_Pexp σ' m'' (incrPVar 0 y_p) = inr mb) as MB''.
    {
      subst σ'.
      unfold lookup_Pexp.
      rewrite evalPexp_incrPVar.
      simpl.
      rewrite Heqe2.

      destruct P2 as [_ mem_write_safe2].
      apply Option_equiv_eq in E2.
      specialize (mem_write_safe2 _ _ _ _ E2).

      assert(TS: evalPexp (DSHPtrVal t_i o2 :: σ) (PVar 0) = inr t_i)
        by reflexivity.
      specialize (mem_write_safe2 _ TS).

      assert(MB': memory_lookup m' y_i = Some mb).
      {
        unfold memory_lookup_err, trywith in MB.
        break_match_hyp; inversion MB; subst.
        rewrite <-H3.
        rewrite <-Heqo.
        unfold memory_lookup, memory_set.
        rewrite NP.F.add_neq_o.
        reflexivity.
        assumption.
      }


      unfold memory_lookup_err.
      enough (T : memory_lookup m'' y_i = Some mb) by (rewrite T; reflexivity).
      rewrite <- MB'.
      symmetry.
      apply mem_write_safe2.
      auto.
    }

    specialize (C1 MB'').
    rewrite MD, E1 in C1.

    inversion C1 as [ | | ab bm HC1 HA HB];
      clear C1; rename HC1 into C1;
        subst ab; subst bm.

    assert(MA''': lookup_Pexp σ' m''' (incrPVar 0 y_p) = inr ma).
    {
      subst σ'.
      unfold lookup_Pexp.
      rewrite evalPexp_incrPVar.
      simpl.
      rewrite Heqe2.
      unfold memory_lookup_err.
      enough (T : memory_lookup m''' y_i = Some ma) by (rewrite T; reflexivity).
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
    repeat break_match_hyp; try some_none; repeat some_inv; try inl_inr.
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
      pose proof (memory_lookup_memory_next_key_is_None m) as F.
      apply is_None_def in F.
      unfold memory_lookup_err.
      rewrite F.
      intro C.
      inversion C.
    }

    assert(t_i ≢ x_i).
    {
      destruct (Nat.eq_dec t_i x_i); auto.
      subst.
      exfalso.
      contradict MX.
      pose proof (memory_lookup_memory_next_key_is_None m) as F.
      apply is_None_def in F.
      unfold memory_lookup_err.
      rewrite F.
      intro C.
      inversion C.
    }

    assert(mem_block_exists y_i m) as EY.
    {
      clear - MB.
      apply mem_block_exists_exists_equiv.
      unfold memory_lookup_err, trywith in MB.
      break_match; try inl_inr.
      exists m0; reflexivity.
      inversion MB.
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

    assert(MX': lookup_Pexp σ' m' (incrPVar 0 x_p) = inr mx).
    {
      rewrite Heqσ'.
      unfold lookup_Pexp.
      rewrite evalPexp_incrPVar.
      simpl.
      rewrite Heqe2.
      subst m'.
      unfold memory_lookup_err, memory_lookup, memory_set.
      rewrite NP.F.add_neq_o.
      apply MX.
      auto.
    }
    specialize (C2 MX').

    assert(MT': lookup_Pexp σ' m' (PVar 0) = inr mem_empty).
    {
      rewrite Heqσ'.
      unfold lookup_Pexp.
      subst m'.
      simpl.
      unfold memory_lookup_err, memory_lookup, memory_set.
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
    apply err_equiv_eq in MT''.
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
    assert(lookup_Pexp σ' m'' (incrPVar 0 y_p) = inr mb) as MB''.
    {
      subst σ'.
      unfold lookup_Pexp.
      rewrite evalPexp_incrPVar.
      simpl.
      rewrite Heqe1.

      destruct P2 as [_ mem_write_safe2].
      apply Option_equiv_eq in E2.
      specialize (mem_write_safe2 _ _ _ _ E2).

      assert(TS: evalPexp (DSHPtrVal t_i o2 :: σ) (PVar 0) = inr t_i)
        by reflexivity.
      specialize (mem_write_safe2 _ TS).

      assert(MB': memory_lookup m' y_i = Some mb).
      {
        assert (memory_lookup m y_i = Some mb).
        {
         clear - MB.
         unfold memory_lookup_err, trywith in MB.
         break_match; inversion MB.
         rewrite H1; reflexivity.
        }

        rewrite <-H1.
        subst m'.
        unfold memory_lookup, memory_set.
        rewrite NP.F.add_neq_o.
        reflexivity.
        assumption.
      }

      enough (T : memory_lookup m'' y_i = Some mb)
        by (unfold memory_lookup_err; rewrite T; reflexivity).
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
    repeat break_match_hyp; try some_none; repeat some_inv; try inl_inr.
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
      pose proof (memory_lookup_memory_next_key_is_None m) as F.
      apply is_None_def in F.
      unfold memory_lookup_err.
      rewrite F.
      intro C.
      inversion C.
    }

    assert(t_i ≢ x_i).
    {
      destruct (Nat.eq_dec t_i x_i); auto.
      subst.
      exfalso.
      contradict MX.
      pose proof (memory_lookup_memory_next_key_is_None m) as F.
      apply is_None_def in F.
      unfold memory_lookup_err.
      rewrite F.
      intro C.
      inversion C.
    }

    unfold memory_lookup, memory_remove.

    assert(mem_block_exists y_i m) as EY.
    {
      clear - MB.
      apply mem_block_exists_exists_equiv.
      unfold memory_lookup_err, trywith in MB.
      break_match; try inl_inr.
      exists m0; reflexivity.
      inversion MB.
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

    assert(MX': lookup_Pexp σ' m' (incrPVar 0 x_p) = inr mx).
    {
      rewrite Heqσ'.
      unfold lookup_Pexp.
      rewrite evalPexp_incrPVar.
      simpl.
      rewrite Heqe0.
      subst m'.
      unfold memory_lookup_err, memory_lookup, memory_set.
      rewrite NP.F.add_neq_o.
      apply MX.
      auto.
    }
    specialize (C2 MX').

    assert(MT': lookup_Pexp σ' m' (PVar 0) = inr mem_empty).
    {
      rewrite Heqσ'.
      unfold lookup_Pexp.
      subst m'.
      simpl.
      unfold memory_lookup_err, memory_lookup, memory_set.
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
    repeat break_match_hyp; try some_none; repeat some_inv; try inl_inr.
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
      pose proof (memory_lookup_memory_next_key_is_None m) as F.
      apply is_None_def in F.
      unfold memory_lookup_err.
      rewrite F.
      cbn.
      intros C; inl_inr.
    }

    assert(t_i ≢ x_i).
    {
      destruct (Nat.eq_dec t_i x_i); auto.
      subst.
      exfalso.
      contradict MX.
      pose proof (memory_lookup_memory_next_key_is_None m) as F.
      apply is_None_def in F.
      unfold memory_lookup_err.
      rewrite F.
      cbn.
      intros C; inl_inr.
    }

    assert(mem_block_exists y_i m) as EY.
    {
      clear - MB.
      apply mem_block_exists_exists_equiv.
      unfold memory_lookup_err, trywith in MB.
      break_match; try inl_inr.
      exists m0; reflexivity.
      inversion MB.
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
      assert(MX': lookup_Pexp σ' m' (incrPVar 0 x_p) = inr mx).
      {
        rewrite Heqσ'.
        unfold lookup_Pexp.
        rewrite evalPexp_incrPVar.
        simpl.
        rewrite Heqe3.
        subst m'.
        unfold memory_lookup_err, memory_lookup, memory_set.
        rewrite NP.F.add_neq_o.
        apply MX.
        auto.
      }
      specialize (C2 MX').

      assert(MT': lookup_Pexp σ' m' (PVar 0) = inr mem_empty).
      {
        rewrite Heqσ'.
        unfold lookup_Pexp.
        subst m'.
        simpl.
        unfold memory_lookup_err, memory_lookup, memory_set.
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
      apply err_equiv_eq in MT''.
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
    assert(lookup_Pexp σ' m'' (incrPVar 0 y_p) = inr mb) as MB''.
    {
      subst σ'.
      unfold lookup_Pexp.
      rewrite evalPexp_incrPVar.
      simpl.
      rewrite Heqe2.

      destruct P2 as [_ mem_write_safe2].
      apply Option_equiv_eq in E2.
      specialize (mem_write_safe2 _ _ _ _ E2).

      assert(TS: evalPexp (DSHPtrVal t_i o2 :: σ) (PVar 0) = inr t_i)
        by reflexivity.
      specialize (mem_write_safe2 _ TS).

      assert(MB': memory_lookup m' y_i = Some mb).
      {
        assert (memory_lookup m y_i = Some mb).
        {
         clear - MB.
         unfold memory_lookup_err, trywith in MB.
         break_match; inversion MB.
         rewrite H1; reflexivity.
        }

        rewrite <-H1.
        subst m'.
        unfold memory_lookup, memory_set.
        rewrite NP.F.add_neq_o.
        reflexivity.
        assumption.
      }

      enough (T : memory_lookup m'' y_i = Some mb)
        by (unfold memory_lookup_err; rewrite T; reflexivity).
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

      assert(MX': lookup_Pexp σ' m' (incrPVar 0 x_p) = inr mx).
      {
        rewrite Heqσ'.
        unfold lookup_Pexp.
        rewrite evalPexp_incrPVar.
        simpl.
        rewrite Heqe3.
        subst m'.
        unfold memory_lookup_err, memory_lookup, memory_set.
        rewrite NP.F.add_neq_o.
        apply MX.
        auto.
      }
      specialize (C2 MX').

      assert(MT': lookup_Pexp σ' m' (PVar 0) = inr mem_empty).
      {
        rewrite Heqσ'.
        unfold lookup_Pexp.
        subst m'.
        simpl.
        unfold memory_lookup_err, memory_lookup, memory_set.
        rewrite NP.F.add_eq_o; reflexivity.
      }
      specialize (C2 MT').

      rewrite E2 in C2.
      inversion C2; subst a b; clear C2; rename H4 into C2.
Qed.


(** * MHTSUMUnioin *)

Global Instance DSHSeq_DSH_pure
       {ts: TypeSig}
       {dop1 dop2 : DSHOperator}
       {x_p y_p : PExpr}
       (P1: DSH_pure dop1 ts x_p y_p)
       (P2: DSH_pure dop2 ts x_p y_p)
  :
    DSH_pure (DSHSeq dop1 dop2) ts x_p y_p.
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

    inversion P1; clear P1 mem_write_safe0;
      rename mem_stable0 into P1.
    apply P1 with (k:=k) in M1; clear P1.
    inversion P2; clear P2 mem_write_safe0;
      rename mem_stable0 into P2.
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

    inversion P1; clear P1 mem_stable0;
      rename mem_write_safe0 into P1.
    eapply P1 with (y_i := y_i) in M1; [| assumption].
    inversion P2; clear P2 mem_stable0;
      rename mem_write_safe0 into P2.
    eapply P2 with (y_i := y_i) in M2; [| assumption].
    clear - M1 M2.
    eapply memory_equiv_except_trans; eassumption.
Qed.

Global Instance HTSUMUnion_MSH_DSH_compat
         {i o : nat}
         {mop1: @MSHOperator i o}
         {mop2: @MSHOperator i o}
         {m: memory}
         {σ: evalContext}
         {dop1 dop2: DSHOperator}
         {dsig1 dsig2: TypeSig}
         `{P: DSH_pure (DSHSeq dop1 dop2) (TypeSigUnion dsig1 dsig2) x_p y_p}
         `{D : herr_f nat nat (compose2 not equiv) (evalPexp σ x_p) (evalPexp σ y_p)}
         `{P1: DSH_pure dop1 dsig1 x_p y_p}
         `{P2: DSH_pure dop2 dsig2 x_p y_p}
         `{C1: @MSH_DSH_compat _ _ mop1 dop1 dsig1 σ m x_p y_p P1}
         `{C2: forall m', lookup_Pexp σ m x_p = lookup_Pexp σ m' x_p ->
                      @MSH_DSH_compat _ _ mop2 dop2 dsig2 σ m' x_p y_p P2}
  :
    MSH_DSH_compat
      (MHTSUMUnion dot mop2 mop1)
      (DSHSeq dop1 dop2)
      σ m x_p y_p.
Proof.
  constructor; intros x_m y_m X_M Y_M.

  destruct (evalPexp σ x_p) as [| x_id] eqn:X;
    [unfold lookup_Pexp in X_M; rewrite X in X_M; inversion X_M |].
  destruct (evalPexp σ y_p) as [| y_id] eqn:Y;
    [unfold lookup_Pexp in Y_M; rewrite Y in Y_M; inversion Y_M |].
  assert (XY : x_id <> y_id).
  {
    clear - D.
    cbv in D.
    inversion D.
    intros C.
    apply H1 in C.
    inversion C.
  }

  destruct mem_op as [mma |] eqn:MOP.
  all: destruct evalDSHOperator as [r |] eqn:DOP; [destruct r as [msg | dma] |].
  all: repeat constructor.

  1,3,4: exfalso.
  -
    cbn in MOP.
    destruct (mem_op mop2 x_m) as [mma2 |] eqn:MOP2; [| some_none].
    destruct (mem_op mop1 x_m) as [mma1 |] eqn:MOP1; [| some_none].
    some_inv; subst.

    cbn in DOP.
    destruct evalDSHOperator as [r |] eqn:DOP1 in DOP; [| some_none];
      destruct r as [msg1 | dma1]; inversion DOP; subst; clear DOP.
    +
      cbn in X_M; rewrite X in X_M.
      cbn in Y_M; rewrite Y in Y_M.

      (* make use of C1 *)
      inversion C1; clear C1; rename eval_equiv0 into C1.
      assert (TC1 : lookup_Pexp σ m x_p = inr x_m)
        by (clear - X X_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite X; cbn; rewrite X_M; reflexivity).
      assert (TC2 : lookup_Pexp σ m y_p = inr y_m)
        by (clear - Y Y_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite Y; cbn; rewrite Y_M; reflexivity).
      specialize (C1 x_m y_m TC1 TC2); clear TC1 TC2.
      rewrite evalDSHOperator_estimateFuel_ge in DOP1 by lia.
      rewrite DOP1, MOP1 in C1.
      inversion C1.
    +
      rename H0 into DOP2.

      cbn in X_M; rewrite X in X_M.
      cbn in Y_M; rewrite Y in Y_M.

      (* make use of C1 *)
      inversion C1; clear C1; rename eval_equiv0 into C1.
      assert (TC1 : lookup_Pexp σ m x_p = inr x_m)
        by (clear - X X_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite X; cbn; rewrite X_M; reflexivity).
      assert (TC2 : lookup_Pexp σ m y_p = inr y_m)
        by (clear - Y Y_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite Y; cbn; rewrite Y_M; reflexivity).
      specialize (C1 x_m y_m TC1 TC2); clear TC1 TC2.
      rewrite evalDSHOperator_estimateFuel_ge in DOP1 by lia.
      rewrite DOP1, MOP1 in C1.
      inversion C1; subst.
      inversion H1; clear C1 H1.
      rename x into y_dma1, H into Y_DMA1, H0 into C1; symmetry in Y_DMA1.

      (* make use of C2 *)
      assert (T : lookup_Pexp σ m x_p = lookup_Pexp σ dma1 x_p).
      {
        clear - X X_M P1 DOP1 Y XY.
        inversion P1; clear P1 mem_stable0; rename mem_write_safe0 into P1.
        eq_to_equiv_hyp.
        apply P1 with (y_i := y_id) in DOP1;
          [| err_eq_to_equiv_hyp; assumption]; clear P1.
        unfold lookup_Pexp, memory_lookup_err.
        rewrite X.
        cbn.
        unfold memory_equiv_except in DOP1.
        specialize (DOP1 x_id XY).
        rewrite DOP1.
        reflexivity.
      }
      specialize (C2 dma1 T).
      inversion C2; clear C2; rename eval_equiv0 into C2.
      specialize (C2 x_m y_dma1).
      rewrite <-T in C2; clear T.
      assert (TC1 : lookup_Pexp σ m x_p = inr x_m) by
          (unfold lookup_Pexp, memory_lookup_err;
           rewrite X; cbn; rewrite X_M; reflexivity).
      assert (TC2 : lookup_Pexp σ dma1 y_p = inr y_dma1)
        by (rewrite Y_DMA1; reflexivity).
      specialize (C2 TC1 TC2); clear TC1 TC2.
      rewrite evalDSHOperator_estimateFuel_ge in DOP2 by lia.
      rewrite DOP2, MOP2 in C2.
      inversion C2.
  -
    cbn in MOP.
    destruct (mem_op mop2 x_m) as [mma2 |] eqn:MOP2; [| some_none].
    destruct (mem_op mop1 x_m) as [mma1 |] eqn:MOP1; [| some_none].
    some_inv; subst.

    cbn in DOP.
    destruct evalDSHOperator as [r |] eqn:DOP1 in DOP.
    +
      destruct r as [| dma1]; inversion DOP; subst; clear DOP.
      rename H0 into DOP2.

      cbn in X_M; rewrite X in X_M.
      cbn in Y_M; rewrite Y in Y_M.

      (* make use of C1 *)
      inversion C1; clear C1; rename eval_equiv0 into C1.
      assert (TC1 : lookup_Pexp σ m x_p = inr x_m)
        by (clear - X X_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite X; cbn; rewrite X_M; reflexivity).
      assert (TC2 : lookup_Pexp σ m y_p = inr y_m)
        by (clear - Y Y_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite Y; cbn; rewrite Y_M; reflexivity).
      specialize (C1 x_m y_m TC1 TC2); clear TC1 TC2.
      rewrite evalDSHOperator_estimateFuel_ge in DOP1 by lia.
      rewrite DOP1, MOP1 in C1.
      inversion C1; subst.
      inversion H1; clear C1 H1.
      rename x into y_dma1, H into Y_DMA1, H0 into C1; symmetry in Y_DMA1.

      (* make use of C2 *)
      assert (T : lookup_Pexp σ m x_p = lookup_Pexp σ dma1 x_p).
      {
        clear - X X_M P1 DOP1 Y XY.
        inversion P1; clear P1 mem_stable0; rename mem_write_safe0 into P1.
        eq_to_equiv_hyp.
        apply P1 with (y_i := y_id) in DOP1;
          [| err_eq_to_equiv_hyp; assumption]; clear P1.
        unfold lookup_Pexp, memory_lookup_err.
        rewrite X.
        cbn.
        unfold memory_equiv_except in DOP1.
        specialize (DOP1 x_id XY).
        rewrite DOP1.
        reflexivity.
      }
      specialize (C2 dma1 T).
      inversion C2; clear C2; rename eval_equiv0 into C2.
      specialize (C2 x_m y_dma1).
      rewrite <-T in C2; clear T.
      assert (TC1 : lookup_Pexp σ m x_p = inr x_m) by
          (unfold lookup_Pexp, memory_lookup_err;
           rewrite X; cbn; rewrite X_M; reflexivity).
      assert (TC2 : lookup_Pexp σ dma1 y_p = inr y_dma1)
        by (rewrite Y_DMA1; reflexivity).
      specialize (C2 TC1 TC2); clear TC1 TC2.
      rewrite evalDSHOperator_estimateFuel_ge in DOP2 by lia.
      rewrite DOP2, MOP2 in C2.
      inversion C2.
    +
      clear DOP.

      cbn in X_M; rewrite X in X_M.
      cbn in Y_M; rewrite Y in Y_M.

      (* make use of C1 *)
      inversion C1; clear C1; rename eval_equiv0 into C1.
      assert (TC1 : lookup_Pexp σ m x_p = inr x_m)
        by (clear - X X_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite X; cbn; rewrite X_M; reflexivity).
      assert (TC2 : lookup_Pexp σ m y_p = inr y_m)
        by (clear - Y Y_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite Y; cbn; rewrite Y_M; reflexivity).
      specialize (C1 x_m y_m TC1 TC2); clear TC1 TC2.
      rewrite evalDSHOperator_estimateFuel_ge in DOP1 by lia.
      rewrite DOP1, MOP1 in C1.
      inversion C1.
  -
    cbn in DOP.
    destruct evalDSHOperator as [r |] eqn:DOP1 in DOP; [| some_none].
    destruct r as [| dma1]; [some_inv; inl_inr |].
    rename DOP into DOP2.
    
    cbn in MOP.
    destruct (mem_op mop1 x_m) as [mma1 |] eqn:MOP1.
    +
      destruct (mem_op mop2 x_m) eqn:MOP2; [some_none |].
      clear MOP.

      cbn in X_M; rewrite X in X_M.
      cbn in Y_M; rewrite Y in Y_M.
      
      (* make use of C1 *)
      inversion C1; clear C1; rename eval_equiv0 into C1.
      assert (TC1 : lookup_Pexp σ m x_p = inr x_m)
        by (clear - X X_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite X; cbn; rewrite X_M; reflexivity).
      assert (TC2 : lookup_Pexp σ m y_p = inr y_m)
        by (clear - Y Y_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite Y; cbn; rewrite Y_M; reflexivity).
      specialize (C1 x_m y_m TC1 TC2); clear TC1 TC2.
      rewrite evalDSHOperator_estimateFuel_ge in DOP1 by lia.
      rewrite DOP1, MOP1 in C1.
      inversion C1; subst.
      inversion H1; clear C1 H1.
      rename x into y_dma1, H into Y_DMA1, H0 into C1; symmetry in Y_DMA1.

      (* make use of C2 *)
      assert (T : lookup_Pexp σ m x_p = lookup_Pexp σ dma1 x_p).
      {
        clear - X X_M P1 DOP1 Y XY.
        inversion P1; clear P1 mem_stable0; rename mem_write_safe0 into P1.
        eq_to_equiv_hyp.
        apply P1 with (y_i := y_id) in DOP1;
          [| err_eq_to_equiv_hyp; assumption]; clear P1.
        unfold lookup_Pexp, memory_lookup_err.
        rewrite X.
        cbn.
        unfold memory_equiv_except in DOP1.
        specialize (DOP1 x_id XY).
        rewrite DOP1.
        reflexivity.
      }
      specialize (C2 dma1 T).
      inversion C2; clear C2; rename eval_equiv0 into C2.
      specialize (C2 x_m y_dma1).
      rewrite <-T in C2; clear T.
      assert (TC1 : lookup_Pexp σ m x_p = inr x_m) by
          (unfold lookup_Pexp, memory_lookup_err;
           rewrite X; cbn; rewrite X_M; reflexivity).
      assert (TC2 : lookup_Pexp σ dma1 y_p = inr y_dma1)
        by (rewrite Y_DMA1; reflexivity).
      specialize (C2 TC1 TC2); clear TC1 TC2.
      rewrite evalDSHOperator_estimateFuel_ge in DOP2 by lia.
      rewrite DOP2, MOP2 in C2.
      inversion C2.
    +
      clear MOP.
      
      cbn in X_M; rewrite X in X_M.
      cbn in Y_M; rewrite Y in Y_M.
      
      (* make use of C1 *)
      inversion C1; clear C1; rename eval_equiv0 into C1.
      assert (TC1 : lookup_Pexp σ m x_p = inr x_m)
        by (clear - X X_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite X; cbn; rewrite X_M; reflexivity).
      assert (TC2 : lookup_Pexp σ m y_p = inr y_m)
        by (clear - Y Y_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite Y; cbn; rewrite Y_M; reflexivity).
      specialize (C1 x_m y_m TC1 TC2); clear TC1 TC2.
      rewrite evalDSHOperator_estimateFuel_ge in DOP1 by lia.
      rewrite DOP1, MOP1 in C1.
      inversion C1.
  -
    unfold lookup_Pexp; cbn.
    rewrite Y.
    unfold memory_lookup_err.
    destruct (memory_lookup dma y_id) as [y_dma |] eqn:Y_DMA.
    +
      constructor.
      unfold SHCOL_DSHCOL_mem_block_equiv.
      intro k.

      cbn in X_M; rewrite X in X_M.
      cbn in Y_M; rewrite Y in Y_M.

      unfold memory_lookup_err, trywith in X_M, Y_M.
      assert (X_M' : memory_lookup m x_id = Some x_m)
        by (clear - X_M; break_match; inversion X_M; rewrite H1; reflexivity).
      assert (Y_M' : memory_lookup m y_id = Some y_m)
        by (clear - Y_M; break_match; inversion Y_M; rewrite H1; reflexivity).
      clear X_M Y_M; rename X_M' into X_M, Y_M' into Y_M.


      cbn in MOP.
      destruct (mem_op mop2 x_m) as [mma2 |] eqn:MOP2; [| some_none].
      destruct (mem_op mop1 x_m) as [mma1 |] eqn:MOP1; [| some_none].
      some_inv; subst.

      cbn in DOP.
      destruct evalDSHOperator as [r |] eqn:DOP1 in DOP; [| some_none].
      destruct r as [| dma1]; [some_inv; inl_inr |].
      rename DOP into DOP2.

      (* make use of C1 *)
      inversion C1; clear C1; rename eval_equiv0 into C1.
      assert (TC1 : lookup_Pexp σ m x_p = inr x_m)
        by (clear - X X_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite X; cbn; rewrite X_M; reflexivity).
      assert (TC2 : lookup_Pexp σ m y_p = inr y_m)
        by (clear - Y Y_M; unfold lookup_Pexp, memory_lookup_err;
            rewrite Y; cbn; rewrite Y_M; reflexivity).
      specialize (C1 x_m y_m TC1 TC2); clear TC1 TC2.
      rewrite evalDSHOperator_estimateFuel_ge in DOP1 by lia.
      rewrite DOP1, MOP1 in C1.
      inversion C1; subst.
      inversion H1; clear C1 H1.
      rename x into y_dma1, H into Y_DMA1, H0 into C1; symmetry in Y_DMA1.

      (* make use of C2 *)
      assert (T : lookup_Pexp σ m x_p = lookup_Pexp σ dma1 x_p).
      {
        clear - X X_M P1 DOP1 Y XY.
        inversion P1; clear P1 mem_stable0; rename mem_write_safe0 into P1.
        eq_to_equiv_hyp.
        apply P1 with (y_i := y_id) in DOP1;
          [| err_eq_to_equiv_hyp; assumption]; clear P1.
        unfold lookup_Pexp, memory_lookup_err.
        rewrite X.
        cbn.
        unfold memory_equiv_except in DOP1.
        specialize (DOP1 x_id XY).
        rewrite DOP1.
        reflexivity.
      }
      specialize (C2 dma1 T).
      inversion C2; clear C2; rename eval_equiv0 into C2.
      specialize (C2 x_m y_dma1).
      rewrite <-T in C2; clear T.
      assert (TC1 : lookup_Pexp σ m x_p = inr x_m) by
          (unfold lookup_Pexp, memory_lookup_err;
           rewrite X; cbn; rewrite X_M; reflexivity).
      assert (TC2 : lookup_Pexp σ dma1 y_p = inr y_dma1)
        by (rewrite Y_DMA1; reflexivity).
      specialize (C2 TC1 TC2); clear TC1 TC2.
      rewrite evalDSHOperator_estimateFuel_ge in DOP2 by lia.
      rewrite DOP2, MOP2 in C2.
      inversion C2; subst.
      inversion H1; clear C2 H1.
      rename x into y_dma2, H into Y_DMA2, H0 into C2; symmetry in Y_DMA2.
      replace y_dma2 with y_dma in *.
      2: {
        clear - Y Y_DMA Y_DMA2.
        unfold lookup_Pexp, memory_lookup_err in Y_DMA2.
        rewrite Y in Y_DMA2.
        cbn in Y_DMA2.
        rewrite Y_DMA in Y_DMA2.
        inversion Y_DMA2.
        reflexivity.
      }
      clear y_dma2 Y_DMA2.

      eapply SHCOL_DSHCOL_mem_block_equiv_comp; eassumption.
    +
      exfalso.
      clear - P DOP Y Y_M Y_DMA.

      rewrite <-mem_block_not_exists_exists in Y_DMA.
      contradict Y_DMA.

      inversion P; clear mem_write_safe0; rename mem_stable0 into MS.
      apply Option_equiv_eq in DOP.
      apply MS with (k := y_id) in DOP; clear MS.

      apply DOP, mem_block_exists_exists_equiv.
      exists y_m.
      unfold lookup_Pexp in Y_M.
      rewrite Y in Y_M.
      cbn in Y_M.
      unfold memory_lookup_err, trywith in Y_M.
      break_match; inversion Y_M.
      rewrite H1; reflexivity.
Qed.
