(* Definitions and lemmas related to correcntess of memory initialization *)

Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Context.
Require Import ITree.Basics.HeterogeneousRelations.

Require Import MathClasses.misc.util.

Require Import Vellvm.Semantics.IntrinsicsDefinitions.

From Coq Require Import ZArith.

Import AlistNotations.
Import ListNotations.
Import MonadNotation.
Import ITreeNotations.

Set Implicit Arguments.
Set Strict Implicit.
Import List.

Section EnvironmentConsistency.

  (* Consistency check to gurantee that there is no intrinsic named "main" *)
  Fact main_is_not_in_intrinsics:
    is_None (List.find (fun x => eqb "main" x) (declaration_names defined_intrinsics_decls)).
  Proof.
    cbn.
    tauto.
  Qed.

  (* Consistency check to gurantee that there are no duplicate intrinsic names *)
  Fact intrinsics_unique:
    list_uniq id (declaration_names defined_intrinsics_decls).
  Proof.
    cbn.
    unfold list_uniq.
    intros.
    cbv in H1; subst b.
    repeat match goal with
           | [H : context[nth_error _ ?x] |- _ ] =>
             destruct x; cbn in H
           end.
    all: congruence.
  Qed.

End EnvironmentConsistency.

(* ZX TODO: remove this *)
Opaque int64FromData.

Lemma list_app_eqlen_eq_l
      {A : Type}
      (l r l' r' : list A)
  :
    l ++ r ≡ l' ++ r' ->
    length l ≡ length l' ->
    l ≡ l' /\ r ≡ r'.
Proof.
  intros EQ L.
  split.
  -
    apply f_equal with (f:=firstn (length l + 0)) in EQ.
    rewrite firstn_app_2 in EQ.
    rewrite L in EQ.
    rewrite firstn_app_2 in EQ.
    cbn in EQ.
    rewrite !app_nil_r in EQ.
    assumption.
  -
    apply f_equal with (f:=skipn (length l)) in EQ.
    rewrite skipn_length_app in EQ.
    rewrite L in EQ.
    rewrite skipn_length_app in EQ.
    assumption.
Qed.

Lemma list_app_eqlen_eq_r
      {A : Type}
      (l r l' r' : list A)
  :
    l ++ r ≡ l' ++ r' ->
    length r ≡ length r' ->
    l ≡ l' /\ r ≡ r'.
Proof.
  intros EQ R.
  enough (L : length l ≡ length l')
    by now apply list_app_eqlen_eq_l.
  assert (length (l ++ r) ≡ length (l' ++ r'))
    by now rewrite EQ.
  rewrite !ListUtil.length_app in H.
  lia.
Qed.

Lemma nth_error_firstn_in
      {A : Type}
      (n k : nat)
      (l : list A)
  :
    k < n ->
    nth_error (firstn n l) k ≡ nth_error l k.
Proof.
  intros.
  destruct (le_lt_dec (length l) k) as [L|L].
  - (* OOB *)
    now rewrite firstn_all2 by lia.
  - (* INB *)
    remember (firstn n l) as t.
    rewrite <-firstn_skipn with (l:=l) (n:=n).
    subst t.
    now rewrite nth_error_app1
      by (rewrite firstn_length; lia).
Qed.

Lemma nth_error_firstn_some
      {A : Type}
      (a : A)
      (n k : nat)
      (l : list A)
  :
    nth_error (firstn n l) k ≡ Some a <->
    nth_error l k ≡ Some a /\ k < n.
Proof.
  split; intros.
  destruct (le_lt_dec n k) as [L|L].
  now rewrite ListUtil.nth_beyond in H
    by (rewrite firstn_length; lia).
  now rewrite nth_error_firstn_in in H.
  now rewrite nth_error_firstn_in.
Qed.

Lemma rev_inj
      {A : Type}
      (l1 l2 : list A)
  :
    rev l1 ≡ rev l2 ->
    l1 ≡ l2.
Proof.
  intros.
  dependent induction l1.
  -
    cbn in H.
    apply rev_nil_rev in H.
    congruence.
  -
    rename a into a1.
    cbn in H.
    destruct l2 as [|a2 l2].
    +
      apply app_eq_nil in H.
      destruct H as [_ H].
      inv H.
    +
      cbn in H.
      apply list_app_eqlen_eq_r in H; [| reflexivity].
      destruct H.
      apply IHl1 in H.
      congruence.
Qed.

Lemma rev_firstn_len
      {A : Type}
      (n : nat)
      (l : list A)
  :
    length (rev_firstn n l) ≡ length l.
Proof.
  unfold rev_firstn.
  now rewrite ListUtil.length_app,
              rev_length,
              <-ListUtil.length_app,
              firstn_skipn.
Qed.

Lemma rev_firstn_Γ_len
      (n : nat)
      (st : IRState)
  :
    length (Γ (rev_firstn_Γ n st)) ≡ length (Γ st).
Proof.
  unfold rev_firstn_Γ.
  destruct st; cbn.
  apply rev_firstn_len.
Qed.

Lemma rev_firstn_inj
      {A : Type}
      (n : nat)
      (l1 l2 : list A)
  :
    rev_firstn n l1 ≡ rev_firstn n l2 →
    l1 ≡ l2.
Proof.
  intros H.

  assert (L : length (rev_firstn n l1) ≡ length (rev_firstn n l2))
    by now f_equal.
  rewrite !rev_firstn_len in L.
    
  destruct (le_lt_dec (length l1) n) as [L1|L1];
    destruct (le_lt_dec (length l2) n) as [L2|L2];
    try lia.
  unfold rev_firstn in *.
  all: repeat try rewrite firstn_all2 in H by assumption.
  all: repeat try rewrite skipn_all2 in H by assumption.
  -
    apply rev_inj.
    rewrite !app_nil_r in H.
    assumption.
  -
    apply list_app_eqlen_eq_l in H.
    2: now rewrite !rev_length, !firstn_length_le by lia.
    rewrite <-(firstn_skipn n l1), <-(firstn_skipn n l2).
    destruct H as [LEQ REQ].
    apply rev_inj in LEQ.
    congruence.
Qed.
    
Lemma rev_firstn_Γ_inj
      (n : nat)
      (st1 st2 : IRState)
  :
    rev_firstn_Γ n st1 ≡ rev_firstn_Γ n st2 ->
    st1 ≡ st2.
Proof.
  intros.
  unfold rev_firstn_Γ in *.
  inv H.
  destruct st1, st2.
  cbn in *.
  f_equal; try assumption.
  eapply rev_firstn_inj.
  eassumption.
Qed.

Lemma rev_firstn_involutive
      {A : Type}
      (n : nat)
      (l : list A)
  :
    rev_firstn n (rev_firstn n l) ≡ l.
Proof.
  unfold rev_firstn.
  destruct (le_lt_dec (length l) n) as [L|L].
  -
    rewrite firstn_app.
    rewrite !skipn_all2 by assumption.
    rewrite !firstn_nil, !app_nil_r.
    rewrite !skipn_all2
      by (rewrite rev_length; apply firstn_le_length).
    rewrite firstn_all2
      by (rewrite rev_length; apply firstn_le_length).
    rewrite rev_involutive.
    rewrite firstn_all2 by assumption.
    now apply app_nil_r.
  -
    rewrite firstn_app, skipn_app.
    rewrite rev_length, firstn_length_le by lia.
    rewrite Nat.sub_diag; cbn; rewrite app_nil_r.
    rewrite skipn_all2
      by now rewrite rev_length, firstn_length_le by lia.
    rewrite app_nil_l.
    rewrite firstn_rev.
    rewrite rev_involutive.
    replace (Datatypes.length (firstn n l) - n)
      with 0
      by (rewrite firstn_length_le; lia).
    rewrite skipn_O.
    apply firstn_skipn.
Qed.

Lemma rev_firstn_Γ_involutive
      (n : nat)
      (st : IRState)
  :
    rev_firstn_Γ n (rev_firstn_Γ n st) ≡ st.
Proof.
  unfold rev_firstn_Γ.
  cbn.
  rewrite rev_firstn_involutive.
  destruct st; reflexivity.
Qed.

Lemma skipn_rev_firstn
      {A : Type}
      (n : nat)
      (l : list A)
  :
    skipn n (rev_firstn n l) ≡ skipn n l.
Proof.
  unfold rev_firstn.
  rewrite skipn_app.
  rewrite rev_length.
  rewrite skipn_all2
    by (rewrite rev_length; apply firstn_le_length).
  rewrite app_nil_l.
  destruct (le_lt_dec (length l) n) as [L|L].
  -
    rewrite !skipn_all2; try congruence.
    rewrite firstn_length, skipn_length.
    lia.
  -
    rewrite firstn_length.
    replace (n - min n (length l)) with 0 by lia.
    now rewrite skipn_O.
Qed.

Lemma firstn_rev_firstn
      {A : Type}
      (n : nat)
      (l : list A)
  :
    firstn n (rev_firstn n l) ≡ rev (firstn n l).
Proof.
  unfold rev_firstn.
  rewrite firstn_app.
  rewrite rev_length.
  rewrite firstn_all2
    by (rewrite rev_length; apply firstn_le_length).
  destruct (le_lt_dec (length l) n) as [L|L].
  -
    rewrite !skipn_all2; try congruence.
    rewrite firstn_nil.
    now rewrite app_nil_r.
  -
    rewrite firstn_length.
    replace (n - min n (length l)) with 0 by lia.
    rewrite firstn_O.
    now rewrite app_nil_r.
Qed.

Ltac fold_initIRGlobals_rev :=
  repeat match goal with
         | [H : context[init_with_data initOneIRGlobal global_uniq_chk ?l ?globals ?s] |- _ ] =>
           replace (init_with_data initOneIRGlobal global_uniq_chk l globals s)
             with (initIRGlobals_rev l globals s)
             in *
             by reflexivity
         | [|- context[init_with_data initOneIRGlobal global_uniq_chk ?l ?globals ?s]] =>
           replace (init_with_data initOneIRGlobal global_uniq_chk l globals s)
             with (initIRGlobals_rev l globals s)
             in *
             by reflexivity
         end.

Lemma initIRGlobals_inl
      (data : list binary64)
      (globals : list (string * DSHType))
      (st : IRState)
      (s : string)
  :
    initIRGlobals_rev data globals st ≡ inl s
    <->
    initIRGlobals data globals st ≡ inl s.
Proof.
  unfold initIRGlobals, initIRGlobals_rev.
  repeat break_match.
  intuition.
  split; intros C; inv C.
Qed.

Lemma initIRGlobals_rev_inr
      (data : list binary64)
      (globals : list (string * DSHType))
      (st st' : IRState)
      w
  :
    initIRGlobals_rev data globals st ≡ inr (st', w)
    <->
    initIRGlobals data globals st ≡ inr (rev_firstn_Γ (length globals) st', w).
Proof.
  unfold initIRGlobals, initIRGlobals_rev.
  repeat break_match.
  split; intros C; inv C.
  subst.
  split.
  -
    intros.
    invc H.
    reflexivity.
  -
    intros.
    clear - H.
    invc H.
    apply rev_firstn_inj in H4.
    destruct i, st'; cbn in *.
    repeat f_equal; assumption.
Qed.

Lemma initIRGlobals_inr
      (data : list binary64)
      (globals : list (string * DSHType))
      (st st' : IRState)
      w
  :
    initIRGlobals_rev data globals st ≡ inr (rev_firstn_Γ (length globals) st', w)
    <->
    initIRGlobals data globals st ≡ inr (st', w).
Proof.
  remember (rev_firstn_Γ (length globals) st') as x.
  replace st' with (rev_firstn_Γ (length globals)
                                 (rev_firstn_Γ (length globals) st')).
  subst x.
  apply initIRGlobals_rev_inr.
  apply rev_firstn_Γ_involutive.
Qed.

Fact initIRGlobals_rev_cons_head_uniq :
  ∀ (a : string * DSHType) (globals : list (string * DSHType))
    (data : list binary64)
    (st: IRState)
    {res},
    initIRGlobals_rev data (a :: globals) st ≡ inr res ->
    forall (j : nat) (n : string) (v : DSHType),
      (nth_error globals j ≡ Some (n, v) /\ n ≡ fst a) → False.
Proof.
  intros a globals data st res H j n v C.
  unfold initIRGlobals_rev, global_uniq_chk in H.
  cbn in H.
  repeat break_match_hyp; repeat try inl_inr.
  unfold assert_false_to_err in Heqs.
  subst.
  break_if.
  -
    cbn in Heqs.
    inl_inr.
  -
    inl_inr_inv.
    subst.
    assert(globals_name_present (fst a) globals ≡ true).
    {
      clear -C.
      apply nth_to_globals_name_present.
      exists (n,v).
      exists j.
      apply C.
    }
    congruence.
Qed.

Fact initIRGlobals_cons_head_uniq :
  ∀ (a : string * DSHType) (globals : list (string * DSHType))
    (data : list binary64)
    (st: IRState)
    {res},
    initIRGlobals data (a :: globals) st ≡ inr res ->
    forall (j : nat) (n : string) (v : DSHType),
      (nth_error globals j ≡ Some (n, v) /\ n ≡ fst a) → False.
Proof.
  intros.
  unfold initIRGlobals in H.
  break_match; try inl_inr.
  eapply initIRGlobals_rev_cons_head_uniq; eassumption.
Qed.

Lemma initIRGlobals_rev_names_unique {globals data st res}:
  initIRGlobals_rev data globals st ≡ inr res → list_uniq fst globals.
Proof.
  revert st res data.
  induction globals; intros.
  -
    cbn in H.
    inv H.
    apply list_uniq_nil.
  -
    apply list_uniq_cons.
    split.
    +
      cbn in H.
      break_match_hyp;[inl_inr|].
      break_let.
      break_match_hyp;[inl_inr|].
      repeat break_let; subst.
      break_match_hyp;[inl_inr|].
      repeat break_let; subst.
      inv H.
      eapply IHglobals.
      eauto.
    +
      (* [a] must not be present in [globals] *)
      unfold not.
      intros C.
      destruct C as (j & [n v] & C); cbn in C.
      eapply initIRGlobals_rev_cons_head_uniq; eauto.
Qed.


(* If [initIRGlobals] suceeds, the names of variables in [globals] were unique *)
Lemma initIRGlobals_names_unique {globals data st res}:
  initIRGlobals data globals st ≡ inr res → list_uniq fst globals.
Proof.
  intros.
  destruct res.
  eapply initIRGlobals_rev_names_unique, initIRGlobals_inr.
  eassumption.
Qed.

(* Note: this could not be proben for arbitrary [chk] function,
   so we prove this only for [no_chk] *)
Lemma init_with_data_app
      {A: Type} (* input values *)
      {B: Type} (* output values we collect *)
      {C: Type} (* data *)
      (f: C -> A -> err (C*B))
      (c c': C) (* initial data *)
      (l0 l1: list A)
      (b: list B)
  :
    init_with_data f no_chk c (l0++l1) ≡ inr (c',b) ->
    ∃ c1 b1 b2,
      (init_with_data f no_chk c l0 ≡ inr (c1,b1) /\
       init_with_data f no_chk c1 l1 ≡ inr (c',b2) /\
       b ≡ (b1 ++ b2)%list).
Proof.
  revert l0 l1 c c' b.
  induction l0; intros.
  -
    cbn in H.
    repeat eexists.
    eauto.
  -
    cbn in H.
    repeat break_match_hyp; try inl_inr.
    inl_inr_inv.
    subst.
    apply IHl0 in Heqs0; clear IHl0.
    destruct Heqs0 as (c1 & b1 & b2 & H1 & H2 & E).
    repeat eexists; cbn.
    +
      rewrite Heqs.
      rewrite H1.
      eauto.
    +
      eauto.
    +
      cbn.
      f_equiv.
      auto.
Qed.

Lemma monadic_fold_left_err_app
         {A B : Type}
         (f : A -> B -> err A)
         (s0 s2 : A)
         (l0 l1 : list B):
  ListSetoid.monadic_fold_left f s0 (l0++l1) ≡ inr s2
  ->
  ∃ s1,
  ListSetoid.monadic_fold_left f s0 l0 ≡ inr s1 /\
  ListSetoid.monadic_fold_left f s1 l1 ≡ inr s2.
Proof.
  revert l0 l1 s0 s2 f.
  induction l0; intros.
  -
    cbn in *.
    eexists; auto.
  -
    cbn in H.
    break_match_hyp; [inl_inr|].
    eapply IHl0 in H.
    destruct H as [s1 [H1 H2]].
    eexists.
    split; [|eauto].
    cbn.
    rewrite Heqs.
    apply H1.
Qed.

(* TODO: This is general-purpose. Move elsewhere? *)
Lemma mapsto_alist_app_1st
      {K V: Type}
      (R : K → K → Prop)
      `{RD: RelDec.RelDec _ R}
      `{RDC: @RelDec.RelDec_Correct K R RD}
      (g g' : alist K V)
      (v : V)
      (n : K):
  mapsto_alist RD g n v ->
  mapsto_alist RD (g ++ g')%list n v.
Proof.
  revert v n.
  induction g; intros.
  -
    inversion H.
  -
    cbn.
    destruct a as [k0 v0].
    apply mapsto_alist_cons; [apply RDC|].
    destruct (RelDec.rel_dec n k0) eqn:K0.
    +
      right.
      split.
      *
        rewrite RelDec.rel_dec_correct in K0.
        apply K0.
      *
        apply mapsto_alist_cons in H ; [| auto].
        destruct H.
        destruct H.
        rewrite RelDec.rel_dec_correct in K0.
        congruence.
        apply H.
    +
      left.
      split.
      *
        apply IHg.
        apply mapsto_alist_cons in H ; [| auto].
        destruct H.
        apply H.
        destruct H.
        apply RelDec.rel_dec_correct in H.
        congruence.
      *
        apply RelDec.neg_rel_dec_correct in K0.
        apply K0.
Qed.

Lemma alist_find_nth_error_list_uniq
      (g : global_env)
      (x : nat)
      (n: raw_id)
      (v : dvalue)
      (U: list_uniq fst g):
  nth_error g x ≡ Some (n, v) →
  alist_find n g ≡ Some v.
Proof.
  revert U.
  revert x v n.
  induction g; intros.
  -
    rewrite nth_error_nil in H.
    some_none.
  -
    cbn.
    break_let.
    break_if.
    +
      unfold RelDec.rel_dec, AstLib.eq_dec_raw_id in Heqb.
      cbn in Heqb.
      break_match; [| inversion Heqb].
      subst.
      destruct x.
      *
        cbn in H.
        some_inv.
        reflexivity.
      *
        cbn in H.
        clear - U H.
        exfalso.
        apply list_uniq_cons in U.
        destruct U.
        contradict H1.
        eexists.
        eexists.
        eauto.
    +
      destruct x.
      *
        clear IHg.
        cbn in *.
        some_inv.
        subst.
        clear - Heqb.
        unfold RelDec.rel_dec, AstLib.eq_dec_raw_id in Heqb.
        cbn in Heqb.
        break_if.
        inversion Heqb.
        contradict n0.
        reflexivity.
      *
        cbn in H.
        eapply IHg.
        eapply list_uniq_de_cons; eauto.
        eapply H.
Qed.

Definition state_invariant_mcfg (σ : evalContext) (s : IRState) : Rel_mcfg_T unit unit :=
  fun '(memH,_) '(memV,((l,sl),(g,_))) =>
    state_invariant σ s memH (memV,(l,g)).

Definition post_init_invariant_mcfg (fnname:string) (σ : evalContext) (s : IRState) : Rel_mcfg_T unit unit :=
  fun '(memH,_) '(memV,((l,sl),(g,_))) =>
    post_init_invariant fnname σ s memH (memV,(l,g)).

Definition declarations_invariant_mcfg (fnname:string) : Pred_mcfg_T unit :=
  fun '(memV,((l,sl),(g,_))) =>
    declarations_invariant fnname (memV,(l,g)).

(* YZ TODO : Move *)
Arguments allocate : simpl never.

Local Ltac pose_interp_to_L3_alloca m' a' A AE:=
  match goal with
  | [|-context[interp_to_L3 ?defs (trigger (Alloca ?t)) ?g ?l ?m]] =>
    pose proof (interp_to_L3_alloca
                  defs
                  m t g l)
      as [m' [a' [A AE]]]
  end.

(* [global_uniq_chk] in succeeds, does not modify state *)
Fact global_uniq_chk_preserves_st:
  forall a globals i0 i1 u,
    global_uniq_chk a globals i0 ≡ inr (i1, u) ->
    i0 ≡ i1.
Proof.
  intros a globals i0 i1 u H.
  unfold global_uniq_chk in H.
  unfold ErrorWithState.err2errS in H.
  break_match_hyp;inv H.
  reflexivity.
Qed.

Definition addVar (a : string * DSHType) (s : IRState) : IRState :=
  let '(nm, t) := a in
  {| block_count := block_count s;
     local_count := local_count s;
     void_count := void_count s;
     Γ := (ID_Global (Name nm), TYPE_Pointer (getIRType t)) :: Γ s |}.

Lemma initOneIRGlobal_state_change
      (data0 data1 : list binary64)
      (a : string * DSHType)
      (s0 s1 : IRState)
      r
  :
    initOneIRGlobal data0 a s0 ≡ inr (s1, (data1, r)) ->
    s1 ≡ addVar a s0.
Proof.
  intros.
  destruct a.
  cbn in *.
  repeat break_match.
  all: now invc H.
Qed.

Lemma getStateVar_preserves_st
      {s : string}
      {n : nat}
      {st st' r} :
  getStateVar s n st ≡ inr (st', r) ->
  st ≡ st'.
Proof.
  intros.
  unfold getStateVar in H.
  cbn in H.
  unfold ErrorWithState.option2errS in H.
  break_match; inversion H; subst.
  reflexivity.
Qed.

Lemma genMExpr_preserves_Γ
      {m : MExpr}
      {s s' r} :
  genMExpr m s ≡ inr (s', r) ->
  Γ s ≡ Γ s'.
Proof.
  intros.
  unfold genMExpr in H.
  destruct m; [| inversion H].
  destruct p.
  unfold bind in H.
  break_let.
  inversion Heqm; subst ret bind; clear Heqm.
  repeat break_match; inversion H.
  subst.
  apply getStateVar_preserves_st in Heqs0.
  congruence.
Qed.

Transparent incLocal.
Transparent incVoid.
Transparent incBlock.
Transparent incBlockNamed.

Lemma genNExpr_preserves_Γ
      {n : NExpr}
      {s s' r} :
  genNExpr n s ≡ inr (s', r) ->
  Γ s ≡ Γ s'.
Proof.
  intros.
  generalize dependent r.
  generalize dependent s.
  generalize dependent s'.
  induction n.

  { (* base case 1 *)
    intros.
    unfold genNExpr in H.
    unfold bind in H.
    repeat break_let.
    inversion Heqm; subst ret bind; clear Heqm.
    repeat break_match; inversion H; subst; clear H.
    +
      apply getStateVar_preserves_st in Heqs0.
      subst; reflexivity.
    +
      apply getStateVar_preserves_st in Heqs0; subst i.
      apply incLocal_Γ in Heqs1.
      congruence.
  }

  { (* base case 2 *)
    intros.
    cbn in H.
    inversion H; reflexivity.
  }

  (* inductive cases *)
  all: intros; cbn in H.
  all: destruct (genNExpr n1 s)  as [t | [s1 [ae1 ac1]]] eqn:N1; [inl_inr |].
  all: destruct (genNExpr n2 s1) as [t | [s2 [ae2 ac2]]] eqn:N2; [inl_inr |].
  all: inversion_clear H. (* clear H H1 H2. *)
  all: apply IHn1 in N1.
  all: apply IHn2 in N2.
  all: cbn; congruence.
Qed.

Lemma genAExpr_preserves_Γ
      {a : AExpr}
      {s s' r} :
  genAExpr a s ≡ inr (s', r) ->
  Γ s ≡ Γ s'.
Proof.
  intros.
  generalize dependent r.
  generalize dependent s.
  generalize dependent s'.
  induction a.

  { (* base case 1 *)
    intros.
    unfold genAExpr in H.
    unfold bind in H.
    repeat break_let.
    inversion Heqm; subst ret bind; clear Heqm.
    repeat break_match; inversion H; subst; clear H.
    +
      apply getStateVar_preserves_st in Heqs0.
      apply incLocal_Γ in Heqs1.
      congruence.
    +
      apply getStateVar_preserves_st in Heqs0.
      congruence.
  }

  { (* base case 2 *)
    intros.
    cbn in H.
    inversion H; reflexivity.
  }

  {
    intros.
    cbn in H.
    repeat break_match; inversion_clear H.
    subst.
    apply genNExpr_preserves_Γ in Heqs0.
    apply genMExpr_preserves_Γ in Heqs1.
    cbn.
    congruence.
  }

  {
    intros.
    cbn in H.
    destruct (genAExpr a s)  as [t | [s1 [ae1 ac1]]] eqn:A; [inl_inr |].
    apply IHa in A.
    inversion H.
    cbn.
    congruence.
  }

  (* inductive cases *)
  all: intros; cbn in H.
  all: destruct (genAExpr a1 s)  as [t | [s1 [ae1 ac1]]] eqn:A1; [inl_inr |].
  all: destruct (genAExpr a2 s1) as [t | [s2 [ae2 ac2]]] eqn:A2; [inl_inr |].
  all: inversion_clear H. (* clear H H1 H2. *)
  all: apply IHa1 in A1.
  all: apply IHa2 in A2.
  all: cbn; congruence.
Qed.

Transparent resolve_PVar.
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
Opaque resolve_PVar.

Lemma initIRGlobals_rev_Γ_len
      (globals : list (string * DSHType))
      (d d' : list binary64)
      (s s': IRState)
      (gdecls : list (toplevel_entity typ (LLVMAst.block typ * list (LLVMAst.block typ))))
  :
    initIRGlobals_rev d globals s ≡ inr (s', (d', gdecls)) →
    length (Γ s') ≡
    length globals + length (Γ s).
Proof.
  intros.
  dependent induction globals.
  -
    cbn in *.
    invc H.
    lia.
  -
    cbn in H.
    repeat break_match; invc H.
    rename i into s0,
           i0 into s1.
    apply IHglobals in Heqs2.
    rewrite_clear Heqs2.
    apply global_uniq_chk_preserves_st in Heqs0.
    subst s0.
    enough (length (Γ s1) ≡ length (Γ s) + 1)
      by (cbn; lia).
    clear - Heqs1.
    destruct a.
    eapply initOneIRGlobal_state_change in Heqs1.
    invc Heqs1.
    cbn.
    lia.
Qed.

Lemma initIRGlobals_Γ_len
      (globals : list (string * DSHType))
      (d d' : list binary64)
      (s s': IRState)
      (gdecls : list (toplevel_entity typ (LLVMAst.block typ * list (LLVMAst.block typ))))
  :
    initIRGlobals d globals s ≡ inr (s', (d', gdecls)) →
    length (Γ s') ≡
    length globals + length (Γ s).
Proof.
  intros.
  rewrite <-rev_firstn_Γ_len with (n:=length globals) (st:=s').
  eapply initIRGlobals_rev_Γ_len.
  apply initIRGlobals_inr in H.
  eassumption.
Qed.
  
Lemma split_hd_len {A : Type} (l l1 l2 : list A) (n : nat) :
  ListUtil.split l n ≡ Some (l1, l2) -> length l1 ≡ n.
Proof.
  enough (forall acc, ListUtil.split_aux acc l n ≡ Some (l1, l2) -> length l1 ≡ n + length acc).
  {
    intros.
    rewrite H with (acc:=[]).
    cbn.
    apply Nat.add_0_r.
    assumption.
  }
  generalize dependent l.
  induction n.
  -
    intros.
    destruct l.
    all: inversion H; subst.
    all: rewrite ListUtil.rev_append_rev, app_nil_r, rev_length.
    all: reflexivity.
  -
    intros.
    destruct l; [inversion H |].
    cbn in H.
    apply IHn in H.
    cbn in H.
    rewrite plus_Snm_nSm.
    assumption.
Qed.

Lemma split_tl_len {A : Type} (l l1 l2 : list A) (n : nat) :
  ListUtil.split l n ≡ Some (l1, l2) -> length l2 ≡ (length l - n)%nat.
Proof.
  intros.
  copy_apply ListUtil.split_correct H.
  apply split_hd_len in H.
  subst.
  rewrite ListUtil.length_app.
  lia.
Qed.

From ITree Require Import
     Basics.Monad. 

(* similar to [map_monad_app] but for [map_monad_],
   without unnecessary bindings *)
Lemma map_monad_app_
      {m : Type -> Type}
      {Mm : Monad m}
      {EqMm : Eq1 m}
      {HEQP: Eq1Equivalence m}
      {ML: MonadLawsE m}
      {A : Type}
      (f : A -> m unit)
      (l1 l2 : list A)
  :
    (map_monad_ f (l1 ++ l2) ≈
    map_monad_ f l1 ;;
    map_monad_ f l2)%monad.
Proof.
  unfold map_monad_.
  rewrite map_monad_app.
  generalize (map_monad f l1);
    generalize (map_monad f l2);
    intros L1 L2.
  repeat setoid_rewrite bind_bind.
  setoid_rewrite bind_ret_l.
  reflexivity.
Qed.

(* all allocations and initializations operate using [map_monad_].
   It is nicer to work with than [map_monad], so fold it whenver possible *)
Local Ltac fold_map_monad_ :=
  repeat
  match goal with
  | |- context [map_monad ?f ?L;; Ret ()] =>
    replace (map_monad f L;; Ret ())
      with (map_monad_ f L)
      in *
      by reflexivity
  end.

Local Ltac fold_initialization :=
  repeat
  match goal with
  | |- context[map_monad_ allocate_global ?l] =>
    replace (map_monad_ allocate_global l)
      with (allocate_globals l)
      in *
      by reflexivity
  | |- context[map_monad_ allocate_declaration ?l] =>
    replace (map_monad_ allocate_declaration l)
      with (allocate_declarations l)
      in *
      by reflexivity
  | |- context[map_monad_ initialize_global ?l] =>
    replace (map_monad_ initialize_global l)
      with (initialize_globals l)
      in *
      by reflexivity
  end.

Lemma eutt_clo_bind_skip_l
      (E : Type → Type)
      (LT1 LT2 RT1 RT2 RT3 : Type)
      (l1 : itree E LT1)
      (r1 : itree E RT1)
      (ls1 : LT1 → itree E LT2)
      (rs1 : RT1 → itree E RT2)
      (rs2 : RT2 → itree E RT3)
      R1 R2 R3
  :
    eutt R1 l1 r1 ->
    (∀ xl1 xr1, R1 xl1 xr1 -> eutt R2 (ls1 xl1) (rs1 xr1)) ->
    (∀ xl2 xr2, R2 xl2 xr2 → eutt R3 (ret xl2) (rs2 xr2)) ->
    eutt R3 (x <- l1;; ls1 x) (x <- r1;; x' <- rs1 x ;; rs2 x').
Proof.
  intros.
  eapply eutt_clo_bind.
  -
    eassumption.
  -
    intros.
    rewrite <-bind_ret_r.
    eapply eutt_clo_bind.
    +
      eauto.
    +
      eauto.
Qed.

Definition in_global_addr (g : global_env) (x : raw_id) (a : Addr.addr) := 
  g @ x ≡ Some (DVALUE_Addr a).

Definition allocated_xy (memV : memoryV) (g : global_env) :=
  exists ptr0 ptr1,
      allocated ptr0 memV
    /\ allocated ptr1 memV
    /\ in_global_addr g (Anon 0%Z) ptr0
    /\ in_global_addr g (Anon 1%Z) ptr1.

Definition allocated_globals
           (memV : memoryV)
           (g : global_env)
           (globals : list (string * DSHType))
  :=
    forall j (jc : j < length globals),
    exists ptr_llvm,
      allocated ptr_llvm memV
      /\ in_global_addr g (Name (fst (ListUtil.ith jc))) ptr_llvm.
 
(* ZX TODO: consider checking [forall i, globals[i] ~~~ σ[i]] *)
Definition post_alloc_invariant_mcfg
           (globals : list (string * DSHType))
  : Rel_mcfg_T unit unit :=
  fun _ '(memV, (_, (g, _))) =>
    allocated_xy memV g /\
    allocated_globals memV g globals.

Lemma allocate_allocated (m1 m2 : memoryV) (d : dtyp) (a : Addr.addr) :
  allocate m1 d ≡ inr (m2, a) → allocated a m2.
Proof.
  intros AS.
  unfold allocate, allocated in *.
  destruct d; invc AS.
  all: repeat break_let; subst.
  all: unfold add_logical_block, add_logical_block_mem, add_to_frame in *.
  all: repeat break_match; invc Heqm; invc Heqm0.
  all: apply member_add_eq.
Qed.

Lemma allocated_allocate_allocated (m1 m2 : memoryV) (d : dtyp) (a a' : Addr.addr) :
  allocated a m1 -> allocate m1 d ≡ inr (m2, a') → allocated a m2.
Proof.
  intros A AS.
  unfold allocate, allocated in *.
  destruct d; invc AS.
  all: repeat break_let; subst.
  all: unfold add_logical_block, add_logical_block_mem, add_to_frame in *.
  all: repeat break_match; invc Heqm1.
  all: apply member_add_ineq; [| assumption].
  all: unfold next_logical_key, next_logical_key_mem.
  all: simpl.
  all: intros C; rewrite C in A; contradict A.
  all: apply next_logical_key_fresh.
Qed.

(* ZX TODO: move to ListUtil *)
Lemma ith_eq_app_r
      {A : Type} (m l : list A)
      (j : nat)
      (hi : (Datatypes.length l) + j < Datatypes.length (l ++ m)) 
      (hj : j < Datatypes.length m)
  :
    ListUtil.ith (l:=l ++ m) (i:=(Datatypes.length l) + j) hi ≡
    ListUtil.ith (l:=m) (i:=j) hj.
Proof.
  dependent induction l.
  -
    cbn in *.
    apply ListUtil.ith_eq.
    reflexivity.
  -
    cbn in *.
    apply IHl.
Qed.

Lemma eutt_weaken_left: forall {E A B} (R : A -> A -> Prop) (S : A -> B -> Prop)
             (t t' : itree E A) (s : itree E B),
    (* i.e. sub_rel (rcompose R S) S *)
    (forall a a' b, S a' b -> R a a' -> S a b) ->
    eutt R t t' ->
    eutt S t' s ->
    eutt S t s.
Proof.
  intros * LEFTUNIT EQt EQ.
  (* YZ TODO: specialize eqit_mon to eutt *)
  (* ZX: also look at the lemma below, I just copied this *)
  eapply eqit_mon; [reflexivity | reflexivity | | eapply eqit_trans; eauto].
  intros ? ? []; eauto.
Qed.

Lemma eutt_weaken_right: forall {E A B} (R : B -> B -> Prop) (S : A -> B -> Prop)
             (t : itree E A) (s s' : itree E B),
    (* i.e. sub_rel (rcompose R S) S *)
    (forall a b b', S a b' -> R b' b -> S a b) ->
    eutt R s' s ->
    eutt S t s' ->
    eutt S t s.
Proof.
  intros * RIGHTUNIT EQt EQ.
  eapply eqit_mon; [reflexivity | reflexivity | | eapply eqit_trans; eauto].
  intros ? ? []; eauto.
Qed.

Lemma initOneIRGlobal_is_global
      (data data' : list binary64)
      (r : toplevel_entity typ (LLVMAst.block typ * list (LLVMAst.block typ))) 
      (nmt : string * DSHType)
      (s s' : IRState)
  :
    initOneIRGlobal data nmt s ≡ inr (s', (data', r)) ->
    exists g, r ≡ TLE_Global g.
Proof.
  intro R.
  unfold initOneIRGlobal in R.
  repeat break_match; invc R.
  all: eexists; eauto.
Qed.

Lemma global_uniq_chk_app
      (a : string * DSHType)
      (g1 g2 : list (string * DSHType))
      (s : IRState)
  :
    global_uniq_chk a (g1 ++ g2) s ≡ inr (s, ()) ->
    global_uniq_chk a g1 s ≡ inr (s, ()).
Proof.
  intros.
  unfold global_uniq_chk, globals_name_present in *.
  destruct fold_right eqn:FA in H;
    inversion_clear H.
  match goal with
  | [ |- context [fold_right ?f' _ _ ]] => remember f' as f
  end.
  enough (fold_right f false g1 ≡ false) by (now rewrite H).
  rewrite fold_right_app in FA.
  destruct (fold_right f false g2) eqn:FG2; [| assumption].
  contradict FA.
  rewrite Bool.not_false_iff_true.
  induction g1.
  - reflexivity.
  - cbn. rewrite IHg1. now subst.
Qed.

Lemma initIRGlobals_rev_app_inv
      (pre post : list (string * DSHType))
      (s0 s1 : IRState)
      (l0 l1 : list binary64)
      (g : list (toplevel_entity typ (LLVMAst.block typ * list (LLVMAst.block typ)))) 
  :
    initIRGlobals_rev l0 (pre ++ post) s0 ≡ inr (s1, (l1, g)) →
    ∃ l' s' g1 g2,
      initIRGlobals_rev l0 pre s0 ≡ inr (s', (l', g1)) ∧
      initIRGlobals_rev l' post s' ≡ inr (s1, (l1, g2)) ∧
      g ≡ g1 ++ g2.
Proof.
  unfold initIRGlobals_rev.
  dependent induction pre; intros A.
  -
    intros.
    cbn in *.
    repeat eexists.
    assumption.
  -
    rename pre into pre'.
    cbn in A.
    repeat break_match_hyp;
      try inl_inr; repeat inl_inr_inv; subst.
    apply IHpre in Heqs1; clear IHpre.
    destruct Heqs1 as (l' & s' & g1 & g2 & PRE & POST & G).
    repeat eexists.
    2: eassumption.
    2: { instantiate (1:=t :: g1). now rewrite G. }

    copy_apply global_uniq_chk_preserves_st Heqs; subst i.
    cbn.
    erewrite global_uniq_chk_app;
      [| destruct u; eassumption].
    rewrite Heqs0.
    rewrite PRE.
    reflexivity.
Qed.

Lemma initFSHGlobals_no_overwrite
      (m0 m : memoryH)
      (hdata0 hdata : list binary64)
      (globals : list (string * DSHType)) 
      (σ : list (DSHVal * bool))
  :
    initFSHGlobals hdata0 m0 globals ≡ inr (m, hdata, σ) →
    m = memory_union m0 m.
Proof.
  intros I k.
  unfold memory_union.
  rewrite Memory.NP.F.map2_1bis by reflexivity.
  break_match; [| reflexivity].
  rename m1 into mb, Heqo into MB.
  move I after mb.

  move globals at top.
  dependent induction globals; intros.
  -
    invc I.
    now rewrite MB.
  -
    cbn in I.
    repeat break_match; invc I.
    unfold initOneFSHGlobal in Heqs.
    repeat break_match; invc Heqs.
    1: break_match; invc H0.
    all: eapply IHglobals; try eassumption.
    destruct (Nat.eq_dec k (memory_next_key m0)).
    *
      subst.
      pose proof memory_lookup_memory_next_key_is_None m0.
      unfold memory_lookup in H.
      rewrite util.is_None_def in H.
      now rewrite H in MB.
    *
      unfold memory_set.
      now rewrite Memory.NP.F.add_neq_o by congruence.
Qed.

Lemma initOneFSHGlobal_no_overwrite
      (m0 m : memoryH)
      (hdata0 hdata : list binary64)
      (g : string * DSHType)
      (e : DSHVal * bool)
  :
    initOneFSHGlobal (m0, hdata0) g ≡ inr (m, hdata, e) →
    m = memory_union m0 m.
Proof.
  intros.
  eapply initFSHGlobals_no_overwrite
    with (globals:=[g]).
  cbn.
  now rewrite H.
Qed.

Lemma list_uniq_global_uniq_chk (h : string * DSHType) (tl : list (string * DSHType)) :
  list_uniq fst (h::tl) ->
  forall s, is_OK (global_uniq_chk h tl s).
Proof.
  intros.
  unfold global_uniq_chk.
  unfold ErrorWithState.err2errS.
  break_match; try constructor.
  exfalso.
  unfold assert_false_to_err in Heqs0.
  break_match; invc Heqs0.
  unfold globals_name_present in Heqb.
  assert (exists h', In h' tl /\ Misc.string_beq (fst h') (fst h)).
  {
    clear - Heqb.
    generalize dependent tl.
    intros.
    induction tl; [inv Heqb |].
    -
      cbn in Heqb.
      apply Bool.orb_prop in Heqb.
      destruct Heqb.
      +
        specialize (IHtl H).
        destruct IHtl as (h' & IH & EQH).
        exists h'.
        split.
        apply in_cons; assumption.
        assumption.
      +
        exists a.
        intuition.
  }
  destruct H0 as (h' & IH & EQH).
  unfold list_uniq in H.
  apply In_nth_error in IH.
  destruct IH as [n' NH].
  specialize (H (S n') 0 h' h).
  full_autospecialize H.
  cbn.
  assumption.
  reflexivity.
  unfold Misc.string_beq in EQH.
  break_if; intuition.
  lia.
Qed.

Lemma initIRGlobals_rev_app
      (pre post : list (string * DSHType))
      (s0 s' s1 : IRState)
      (l0 l' l1 : list binary64)
      (g1 g2 : list (toplevel_entity typ (LLVMAst.block typ * list (LLVMAst.block typ))))
  :
    list_uniq fst (pre ++ post) ->
    initIRGlobals_rev l0 pre s0 ≡ inr (s', (l', g1)) ->
    initIRGlobals_rev l' post s' ≡ inr (s1, (l1, g2)) ->
    initIRGlobals_rev l0 (pre ++ post) s0
    ≡ inr (s1, (l1, g1 ++ g2)).
Proof.
  unfold initIRGlobals_rev.
  intros.
  dependent induction pre.
  -
    cbn in *.
    invc H0.
    assumption.
  -
    cbn in *.
    repeat break_match_hyp; invc H0.
    pose proof H as H'.
    apply list_uniq_global_uniq_chk with (s:=s0) in H.
    inversion H.
    break_let; subst.
    symmetry in H2.
    apply global_uniq_chk_preserves_st in Heqs.
    apply global_uniq_chk_preserves_st in H2.
    subst i i1.
    rewrite Heqs0.
    erewrite IHpre.
    +
      reflexivity.
    +
      clear - H'.
      unfold list_uniq in *.
      intros.
      specialize (H' (S x) (S y) a0 b).
      full_autospecialize H'.
      cbn; assumption.
      cbn; assumption.
      assumption.
      lia.
    +
      eassumption.
    +
      eassumption.
Qed.

(* ZX TODO: might want to move to vellvm *)
(* similar to [interp_cfg_to_L3_GR] *)
Lemma interp_to_L3_GR : forall defs id g l m v,
  Maps.lookup id g ≡ Some v ->
  interp_to_L3 defs (trigger (GlobalRead id)) g l m ≈ Ret (m,(l,(g,v))).
Proof.
  intros * LU.
  unfold interp_to_L3.
  rewrite interp_intrinsics_trigger.
  cbn.
  unfold Intrinsics.F_trigger.
  rewrite interp_global_trigger.
  cbn in *; rewrite LU.
  rewrite interp_local_stack_ret, interp_memory_ret.
  reflexivity.
Qed.

(* ZX TODO: might want to move to vellvm *)
(* similar to [denote_exp_double] *)
Lemma denote_exp_double_mcfg : forall t g l m,
    interp_mcfg
      (translate _exp_E_to_L0
                 (denote_exp (Some (DTYPE_Double))
                             (EXP_Double t)))
      g l m
    ≈
    Ret (m, (l, (g, UVALUE_Double t))).
Proof.
  intros; unfold denote_exp; cbn.
  rewrite translate_ret, interp_to_L3_ret.
  reflexivity.
Qed.


(* ZX TODO: might want to move to vellvm *)
(* similar to [denote_exp_i64] *)
Lemma denote_exp_i64_mcfg : forall t g l m,
    interp_mcfg
      (translate _exp_E_to_L0
                 (denote_exp (Some (DTYPE_I 64))
                             (EXP_Integer (unsigned t))))
       g l m
    ≈
    Ret (m, (l, (g, UVALUE_I64 (DynamicValues.Int64.repr (unsigned t))))).
Proof.
  intros; unfold denote_exp; cbn.
  rewrite translate_ret, interp_to_L3_ret.
  reflexivity.
Qed.

(* ZX TODO: might want to move to vellvm *)
(* similar to [interp_cfg_to_L3_store] *)
Lemma interp_mcfg_store:
  ∀ (m m' : memoryV) (val : dvalue) (a : addr) g l,
    write m a val ≡ inr m' →
    interp_mcfg (trigger (Store (DVALUE_Addr a) val)) g l m ≈ Ret (m', (l, (g, ()))).
Proof.
  intros m m' val a g l WRITE.
  unfold interp_to_L3.
  rewrite interp_intrinsics_trigger.
  cbn.
  unfold Intrinsics.F_trigger.
  rewrite interp_global_trigger.
  rewrite subevent_subevent.
  cbn.
  rewrite interp_local_stack_bind, interp_local_stack_trigger.
  cbn; rewrite subevent_subevent.
  rewrite Eq.bind_bind.
  rewrite interp_memory_bind, interp_memory_store; eauto.
  cbn; rewrite Eq.bind_ret_l.
  rewrite interp_memory_bind, interp_memory_ret, Eq.bind_ret_l.
  rewrite interp_local_stack_ret, interp_memory_ret.
  reflexivity.
Qed.

Lemma _exp_E_to_L0_Global : forall {X} (e : LLVMGEnvE X),
    _exp_E_to_L0 (subevent X e) ≡ subevent X e.
Proof.
  reflexivity.
Qed.

Lemma _exp_E_to_L0_Memory : forall {X} (e : MemoryE X),
    _exp_E_to_L0 (subevent X e) ≡ subevent X e.
Proof.
  reflexivity.
Qed.

Lemma body_non_empty_cast_preserves_st
      (l : list (LLVMAst.block typ))
      (s s' : IRState)
      (r : LLVMAst.block typ * list (LLVMAst.block typ))
  :
    body_non_empty_cast l s ≡ inr (s', r) ->
    s ≡ s'.
Proof.
  intro H.
  unfold body_non_empty_cast in H.
  break_match; invc H.
  reflexivity.
Qed.

Lemma initOneIRGlobal_some_g_exp
      (data data' : list binary64)
      (nmt : string * DSHType)
      (tg : global typ) 
      (s s' : IRState)
  :
    initOneIRGlobal data nmt s ≡ inr (s', (data', TLE_Global tg)) →
    is_Some (g_exp tg).
Proof.
  intros.
  unfold initOneIRGlobal in H.
  repeat break_match; inv H.
  all: reflexivity.
Qed.

Lemma skipn_skipn
      {A : Type}
      (n1 n2 : nat)
      (l : list A)
  :
    skipn n1 (skipn n2 l) ≡ skipn (n1 + n2) l.
Proof.
  move l before A.
  dependent induction l.
  -
    rewrite !skipn_nil.
    reflexivity.
  -
    destruct n2.
    +
      cbn.
      rewrite Nat.add_0_r.
      reflexivity.
    +
      rewrite Nat.add_succ_r.
      rewrite !skipn_cons.
      apply IHl.
Qed.

Definition IR_of_global (g : string * DSHType) :=
  let '(nm, t) := g in
  (ID_Global (Name nm), TYPE_Pointer (getIRType t)).

Lemma initIRGlobals_rev_Γ_preserved
      (globals : list (string * DSHType))
      (data0 data1 : list binary64)
      (s0 s1 : IRState)
      ginit
  :
    initIRGlobals_rev data0 globals s0 ≡ inr (s1, (data1, ginit)) ->
    skipn (length globals) (Γ s1) ≡ Γ s0.
Proof.
  intros.
  dependent induction globals.
  -
    cbn in *.
    invc H.
    reflexivity.
  -
    cbn in H.
    repeat break_match; try inl_inr.
    invc H.
    apply global_uniq_chk_preserves_st in Heqs; subst i.
    rename Heqs0 into I0,
           Heqs1 into I1,
           t into ts,
           l into data',
           i0 into s'.
    eapply IHglobals in I1.
    destruct a as (nm, t).
    eapply initOneIRGlobal_state_change in I0.
    cbn in I0.
    invc I0.
    cbn [Γ] in *.

    apply f_equal with (f:=skipn 1) in I1.
    rewrite skipn_skipn in I1.
    cbn in *.
    assumption.
Qed.

Lemma Γ_rev_firstn_Γ (n : nat) (st : IRState) :
  Γ (rev_firstn_Γ n st) ≡ rev_firstn n (Γ st).
Proof.
  now compute.
Qed.

Lemma initIRGlobals_Γ_preserved
      (globals : list (string * DSHType))
      (data0 data1 : list binary64)
      (s0 s1 : IRState)
      ginit
  :
    initIRGlobals data0 globals s0 ≡ inr (s1, (data1, ginit)) ->
    skipn (length globals) (Γ s1) ≡ Γ s0.
Proof.
  intros.
  apply initIRGlobals_inr in H.
  eapply initIRGlobals_rev_Γ_preserved in H.
  rewrite Γ_rev_firstn_Γ in H.
  rewrite skipn_rev_firstn in H.
  assumption.
Qed.

Lemma initIRGlobals_rev_Γ_appended
      (globals : list (string * DSHType))
      (data0 data1 : list binary64)
      (s0 s1 : IRState)
      ginit
  :
    initIRGlobals_rev data0 globals s0 ≡ inr (s1, (data1, ginit)) ->
    firstn (length globals) (Γ s1) ≡
    map IR_of_global (rev globals).
Proof.
  intros I.
  dependent induction globals. (* using list_rev_ind. *)
  -
    reflexivity.
  -
    rewrite list_cons_app in I.
    apply initIRGlobals_rev_app_inv in I.
    destruct I as (data' & s' & g1 & g2 & I1 & I2 & G).
    copy_apply initIRGlobals_rev_Γ_len I1; rename H into L1.
    copy_apply initIRGlobals_rev_Γ_len I2; rename H into L2.
    cbn in L1.

    cbn [rev length].
    rewrite ListUtil.map_app.
    cbn [map].

    erewrite <-IHglobals with (s1:=s1).
    2: eassumption.
    clear IHglobals.

    rewrite <-(firstn_skipn (length globals) (Γ s1)).
    rewrite firstn_app.
    rewrite (firstn_skipn (length globals) (Γ s1)).
    replace (S (Datatypes.length globals) -
     Datatypes.length (firstn (Datatypes.length globals) (Γ s1)))
      with 1
      by (rewrite firstn_length_le; lia).
    rewrite firstn_firstn.
    rewrite Min.min_r by lia.
    enough
      (firstn 1 (skipn (Datatypes.length globals) (Γ s1)) ≡
       [IR_of_global a])
      by congruence.

    cbn in I1.
    repeat break_match; invc I1.
    rename t into ts, Heqs into I1.
    destruct a as (nm', t').
    apply initOneIRGlobal_state_change in I1.
    cbn in I1.
    invc I1.
    cbn [Γ] in *.
    apply initIRGlobals_rev_Γ_preserved in I2.
    rewrite I2.
    reflexivity.
Qed.

Lemma initIRGlobals_Γ_appended
      (globals : list (string * DSHType))
      (data0 data1 : list binary64)
      (s0 s1 : IRState)
      ginit
  :
    initIRGlobals data0 globals s0 ≡ inr (s1, (data1, ginit)) ->
    firstn (length globals) (Γ s1) ≡
    map IR_of_global globals.
Proof.
  intros.
  apply initIRGlobals_inr in H.
  eapply initIRGlobals_rev_Γ_appended in H.
  rewrite Γ_rev_firstn_Γ in H.
  rewrite firstn_rev_firstn in H.
  rewrite map_rev in H.
  apply rev_inj in H.
  assumption.
Qed.

Lemma initIRGlobals_rev_Γ
      (globals : list (string * DSHType))
      (data0 data1 : list binary64)
      (s0 s1 : IRState)
      ginit
  :
    initIRGlobals_rev data0 globals s0 ≡ inr (s1, (data1, ginit)) ->
    Γ s1 ≡ map IR_of_global (rev globals) ++ (Γ s0).
Proof.
  intros.
  rewrite <-(firstn_skipn (length globals) (Γ s1)).
  erewrite initIRGlobals_rev_Γ_appended by eassumption.
  erewrite initIRGlobals_rev_Γ_preserved by eassumption.
  reflexivity.
Qed.

Lemma initIRGlobals_Γ
      (globals : list (string * DSHType))
      (data0 data1 : list binary64)
      (s0 s1 : IRState)
      ginit
  :
    initIRGlobals data0 globals s0 ≡ inr (s1, (data1, ginit)) ->
    Γ s1 ≡ map IR_of_global globals ++ (Γ s0).
Proof.
  intros.
  intros.
  rewrite <-(firstn_skipn (length globals) (Γ s1)).
  erewrite initIRGlobals_Γ_appended by eassumption.
  erewrite initIRGlobals_Γ_preserved by eassumption.
  reflexivity.
Qed.

Definition append_to_Γ
           (globals : list (string * DSHType))
           (s : IRState)
  : IRState
  :=
    {| block_count := block_count s;
       local_count := local_count s;
       void_count := void_count s;
       Γ := map IR_of_global globals ++ (Γ s) |}.

Definition append_to_Γ_rev
           (globals : list (string * DSHType))
           (s : IRState)
  : IRState
  :=
    rev_firstn_Γ (length globals) (append_to_Γ globals s).

Lemma initIRGlobals_rev_state_change
      (globals : list (string * DSHType))
      (data0 data1 : list binary64)
      (s0 s1 : IRState)
      ginit
  :
    initIRGlobals_rev data0 globals s0 ≡ inr (s1, (data1, ginit)) ->
    s1 ≡ append_to_Γ_rev globals s0.
Proof.
  intros.
  destruct s1.
  unfold append_to_Γ_rev, append_to_Γ, rev_firstn_Γ.
  f_equal.
  4: {
    cbn.
    unfold rev_firstn.
    rewrite firstn_app, skipn_app.
    assert (L : length globals ≡ length (map IR_of_global globals))
           by now rewrite map_length.
    replace (length globals - length (map IR_of_global globals))
      with 0
      by lia.
    rewrite firstn_all2 by lia.
    rewrite skipn_all2 by lia.
    cbn.
    rewrite app_nil_r.
    rewrite <-map_rev.
    now apply initIRGlobals_rev_Γ in H.
  }
  all: dependent induction globals; [now invc H |].
  all: cbn in *.
  all: repeat break_match; invc H.
  all: copy_apply global_uniq_chk_preserves_st Heqs; subst i.
  all: copy_apply initOneIRGlobal_state_change Heqs0; subst i0.
  all: apply IHglobals in Heqs1.
  all: subst.
  all: unfold addVar; break_let; reflexivity.
Qed.

Lemma initIRGlobals_state_change
      (globals : list (string * DSHType))
      (data0 data1 : list binary64)
      (s0 s1 : IRState)
      ginit
  :
    initIRGlobals data0 globals s0 ≡ inr (s1, (data1, ginit)) ->
    s1 ≡ append_to_Γ globals s0.
Proof.
  intros.
  apply initIRGlobals_inr in H.
  apply initIRGlobals_rev_state_change in H.
  unfold append_to_Γ_rev in H.
  now apply rev_firstn_Γ_inj in H.
Qed.

Lemma initOneIRglobal_state_writer
      (data0 data1 : list binary64)
      (s0 s1 : IRState)
      (a : string * DSHType)
      (r : toplevel_entity typ (LLVMAst.block typ * list (LLVMAst.block typ)))
  :
    initOneIRGlobal data0 a s0 ≡ inr (s1, (data1, r)) →
    forall s',
      initOneIRGlobal data0 a s' ≡ inr (addVar a s', (data1, r)).
Proof.
  intros.
  destruct a.
  cbn in *.
  repeat break_match.
  all: now invc H.
Qed.

Lemma initIRGlobals_rev_state_writer
      (globals : list (string * DSHType))
      (s0 s1 : IRState)
      (data0 : list binary64)
      r
  :
    initIRGlobals_rev data0 globals s0 ≡ inr (s1, r) →
    forall s',
      initIRGlobals_rev data0 globals s' ≡ inr (append_to_Γ_rev globals s', r).
Proof.
  unfold append_to_Γ_rev.
  dependent induction globals; intros I s'; cbn in *.
  -
    invc I.
    now destruct s'.
  -
    break_match_goal; break_match_hyp; try congruence.
    { (* [global_uniq_chk] inconsistent *)
      exfalso; clear - Heqs Heqs2.
      unfold global_uniq_chk in *.
      destruct (assert_false_to_err ("duplicate global name: " @@ fst a)
                                    (globals_name_present (fst a) globals) ()).
      all: cbn in *; congruence.
    }
    repeat break_let; subst.

    break_match_goal; break_match_hyp; try congruence.
    { (* [initOnrIRGlobal] inconsistent *)
      exfalso; clear - Heqs1 Heqs2.
      destruct a.
      cbn in *.
      repeat break_match; congruence.
    }
    repeat break_let; subst.

    copy_apply global_uniq_chk_preserves_st Heqs0; subst i.
    copy_apply global_uniq_chk_preserves_st Heqs; subst i0.
    repeat destruct_unit.
    copy_apply initOneIRGlobal_state_change Heqs1; subst i2.
    copy_apply initOneIRGlobal_state_change Heqs2; subst i1.

    apply initOneIRglobal_state_writer with (s':=s') in Heqs2.
    rewrite Heqs1 in Heqs2.
    inversion Heqs2; clear Heqs2; subst l0 t0.
    break_match_goal; break_match_hyp; try congruence.
    { (* [init_with_data] inconsistent *)
      exfalso.
      repeat break_let; subst.
      inversion I; clear I; subst i r.
      fold_initIRGlobals_rev.
      apply IHglobals with (s':=addVar a s') in Heqs3.
      congruence.
    }
    repeat break_let; subst.
    invc I.
    apply IHglobals with (s':=addVar a s') in Heqs3.
    fold_initIRGlobals_rev.
    rewrite Heqs2 in Heqs3.
    invc Heqs3.
    unfold addVar.
    destruct a.
    cbn.
    unfold append_to_Γ, rev_firstn_Γ; cbn.
    do 3 f_equal.
    rewrite <-app_assoc.
    unfold rev_firstn.
    assert (L : length globals ≡ length (map IR_of_global globals))
           by now rewrite map_length.
    rewrite !firstn_app, !skipn_app.
    replace (length globals - length (map IR_of_global globals))
      with 0
      by lia.
    cbn.
    rewrite !firstn_all2 by lia.
    rewrite !skipn_all2 by lia.
    reflexivity.
Qed.

Lemma initIRGlobals_rev_state_writer'
      (globals : list (string * DSHType))
      (s0 s1 s0' s1' : IRState)
      (data : list binary64)
      r r'
  :
    initIRGlobals_rev data globals s0 ≡ inr (s1, r) →
    initIRGlobals_rev data globals s0' ≡ inr (s1', r') →
    r ≡ r'.
Proof.
  intros.
  apply initIRGlobals_rev_state_writer with (s':=s0') in H.
  congruence.
Qed.

Lemma list_uniq_initIRGlobals_rev_OK (globals : list (string * DSHType)) :
  list_uniq fst globals ->
  forall data s,
    is_OK (initIRGlobals_rev data globals s).
Proof.
  intros.
  dependent induction globals;
    [constructor |].
  cbn.
  repeat break_match; subst.
  -
    apply list_uniq_global_uniq_chk with (s:=s) in H.
    inv H.
    congruence.
  -
    unfold initOneIRGlobal in Heqs1.
    repeat break_match; inv Heqs1.
  -
    autospecialize IHglobals;
      [now apply list_uniq_de_cons in H |].
    specialize (IHglobals l i0).
    inv IHglobals.
    fold_initIRGlobals_rev.
    congruence.
  -
    constructor.
Qed.

Ltac dedup_states :=
  repeat match goal with
         | [ H : global_uniq_chk _ _ _ ≡ inr (?s, _) |- _] =>
           copy_apply global_uniq_chk_preserves_st H; subst s
         | [ H : initOneIRGlobal _ _ _ ≡ inr (?s, _) |- _] =>
           copy_apply initOneIRGlobal_state_change H; subst s
         | [ H : initIRGlobals_rev _ _ _ ≡ inr (?s, _) |- _] =>
           copy_apply initIRGlobals_rev_state_change H; subst s
         | [ H : initIRGlobals _ _ _ ≡ inr (?s, _) |- _] =>
           copy_apply initIRGlobals_state_change H; subst s
         end.

Lemma initFSHGlobals_app_inv
      (m0 m : memoryH)
      (hdata0 hdata : list binary64)
      (pre post : list (string * DSHType)) 
      (σ : evalContext)
  :
    initFSHGlobals hdata0 m0 (pre ++ post) ≡ inr (m, hdata, σ) ->
    ∃ m' hdata' σ1 σ2,
      initFSHGlobals hdata0 m0 pre ≡ inr (m', hdata', σ1) /\
      initFSHGlobals hdata' m' post ≡ inr (m, hdata, σ2) /\
      σ ≡ σ1 ++ σ2.
Proof.
  unfold initFSHGlobals.
  intros.
  apply init_with_data_app in H.
  destruct H as ((m', hdata') & σ1 & σ2 & PRE & POST & Σ).
  repeat eexists; eassumption.
Qed.

Lemma initFSHGlobals_app
      (pre post : list (string * DSHType)) 
      (σ1 σ2 : evalContext)
      (m0 m' m : memoryH)
      (hdata0 hdata' hdata : list binary64)
  :
      initFSHGlobals hdata0 m0 pre ≡ inr (m', hdata', σ1) ->
      initFSHGlobals hdata' m' post ≡ inr (m, hdata, σ2) ->
      initFSHGlobals hdata0 m0 (pre ++ post) ≡ inr (m, hdata, (σ1 ++ σ2)).
Proof.
  unfold initFSHGlobals.
  intros.
  dependent induction pre.
  -
    cbn in *.
    invc H.
    assumption.
  -
    cbn in *.
    repeat break_match_hyp; invc H.
    destruct p0 as (m1, hdata1).
    now erewrite IHpre; eauto.
Qed.

Lemma initFSHGlobals_evalContext_typechecks
      (globals : list (string * DSHType)) 
      (σ : list (DSHVal * bool))
      (m0 m : memoryH)
      (hdata0 hdata : list binary64)
  :
    initFSHGlobals hdata0 m0 globals ≡ inr (m, hdata, σ) →
    evalContext_typechecks σ (map IR_of_global globals).
Proof.
  intros.
  unfold evalContext_typechecks.
  dependent induction globals.
  -
    cbn in *.
    invc H.
    intros.
    rewrite nth_error_nil in H.
    discriminate.
  -
    intros.
    cbn in H.
    repeat break_match; invc H.
    destruct n.
    +
      cbn in H0.
      invc H0.
      destruct a.
      cbn.
      eexists.
      do 2 f_equal.
      cbn.
      unfold initOneFSHGlobal in Heqs.
      repeat break_match.
      all: invc Heqs; cbn in *.
      all: try congruence.
      all: repeat break_match; invc H0; cbn in *.
      all: try congruence.
    +
      cbn [map].
      rewrite nth_error_Sn in *.
      destruct p0.
      unfold initFSHGlobals in *.
      specialize (IHglobals _ _ _ _ _ Heqs0 _ _ _ H0).
      eauto.
Qed.

Lemma initFSHGlobals_id_allocated
      (globals : list (string * DSHType))
      (m0 m : memoryH)
      (hdata0 hdata : list binary64) 
      (σ : evalContext)
  :
    initFSHGlobals hdata0 m0 globals ≡ inr (m, hdata, σ) →
    id_allocated σ m.
Proof.
  intros.
  unfold id_allocated.
  dependent induction globals.
  -
    cbn in H.
    invc H.
    intros.
    rewrite nth_error_nil in H.
    discriminate.
  -
    intros.
    cbn in H.
    repeat break_match; invc H.
    destruct n.
    +
      cbn in H0.
      invc H0.
      unfold initOneFSHGlobal in Heqs.
      repeat break_match; inv Heqs.
      break_match; inv H0.
      apply initFSHGlobals_no_overwrite in Heqs0.
      clear - Heqs0.
      admit. (* [Proper mem_block_exists] *)
    +
      rewrite nth_error_Sn in H0.
      destruct p0.
      eapply IHglobals; eassumption.
Admitted.

Lemma initFSHGlobals_id_allocated_preserve
      (globals : list (string * DSHType))
      (m0 m : memoryH)
      (hdata0 hdata : list binary64) 
      (σ σ' : evalContext)
  :
    id_allocated σ m0 ->
    initFSHGlobals hdata0 m0 globals ≡ inr (m, hdata, σ') →
    id_allocated σ m.
Proof.
  unfold id_allocated.
  intros IA0 I; intros.
  induction globals.
  -
    cbn in I.
    invc I.
    eapply IA0.
    eassumption.
  -
    intros.
    cbn in I.
    repeat break_match; invc I.
    destruct p0 as (m1, hdata1).
    apply initOneFSHGlobal_no_overwrite in Heqs.
    apply initFSHGlobals_no_overwrite in Heqs0.
    apply IA0 in H.
    clear - H Heqs Heqs0.
Admitted.

(** [memory_invariant] relation must holds after initialization of global variables *)
Lemma memory_invariant_after_init
      (p: FSHCOLProgram)
      (data: list binary64) :
  forall hmem σ s hdata pll,
    helix_initial_memory p data ≡ inr (hmem,hdata,σ) /\
    compile_w_main p data newState ≡ inr (s,pll) ->
    eutt
      (post_init_invariant_mcfg p.(name) σ s)
      (Ret (hmem, ()))
      (interp_to_L3 defined_intrinsics
                    (build_global_environment (convert_types (mcfg_of_tle pll)))
                    [] ([],[]) empty_memory_stack).
Proof.
  intros hmem σ s hdata pll [HI LI].

  unfold post_init_invariant_mcfg.
  unfold helix_initial_memory in HI.
  cbn in HI.
  repeat break_match_hyp ; try inl_inr.
  rename Heqp0 into Co, Heqp1 into Ci.
  inv HI.
  rename m1 into mg, Heqs0 into G.
  cbn in LI.
  unfold ErrorWithState.option2errS in *.
  unfold initFSHGlobals in *.
  assert (LGE : length globals ≡ length e)
    by (apply init_with_data_len in G; assumption).

  destruct (valid_program _) eqn:VFN.
  2: inversion LI.

  repeat break_match_hyp; try inl_inr;
    inv LI; repeat inv_sum; inv Heqs5; inv Heqs4.
  rename Heqs0 into LX, Heqs1 into LG, Heqs6 into IR, Heqs8 into BC, l3 into gdecls.
  rename Heqo1 into Sg. (* split globals *)
  rename Heqo0 into Sxy. (* split fake_x, fake_y *)

  (*  [s0] - state after [initXYplaceholders] *)
  rename i0 into s0.
  (*  [s1] - state after [initIRGlobals], which
      was generated starting with X,Y arguments added to [s0] *)
  rename i1 into s1.
  (*  [s2] - state after [genIR] *)
  rename i6 into s2.
  (*  [s3] - the final state. (after [body_non_empty_cast]) *)
  rename i5 into s3.

  (* [s3] contains two local for X,Y parameter which we drop: *)

  rename l5 into Γ_globals.
  (* these ones are dropped *)
  rename l8 into Γ_fake_xy,
         l6 into Γ_xy_fake_xy,
         l7 into Γ_xy.

  assert (ΓXYFXY : exists x y fake_x fake_y, Γ_xy_fake_xy ≡ [x; y; fake_x; fake_y]).
  {
    clear - Sg Heqb.
    apply split_tl_len in Sg.
    apply Nat.leb_gt in Heqb.
    assert (Datatypes.length Γ_xy_fake_xy ≡ 4)%nat by lia.
    clear - H.
    repeat (destruct Γ_xy_fake_xy; inversion H).
    repeat eexists.
  }
  destruct ΓXYFXY as [x [y [fake_x [fake_y ΓXYFXY]]]].
  subst Γ_xy_fake_xy.
  invc Sxy.
  apply ListUtil.split_correct in Sg.
  rename Sg into Vs3.

  copy_apply body_non_empty_cast_preserves_st BC.
  subst s3.

  repeat rewrite app_assoc.
  unfold build_global_environment.
  setoid_rewrite interp_to_L3_bind.

  repeat rewrite app_assoc.
  unfold allocate_globals, map_monad_.
  simpl.
  repeat rewrite ListUtil.flat_map_app.
  simpl.
  (* no more [genMain] *)

  destruct s2.

  rename m into mo, m0 into mi.
  rename p13 into body_instr.

  cbn in *.

  (* only globals defined by [initXYplaceholders] *)
  replace (flat_map (type_defs_of typ) t) with (@nil (ident * typ)) in *.
  2:{
    clear - LX.
    unfold initXYplaceholders in LX.
    repeat break_let.
    cbn in LX.
    inv LX.
    reflexivity.
  }
  replace (flat_map (declarations_of typ) t) with (@nil (declaration typ)) in *.
  2:{
    clear - LX.
    unfold initXYplaceholders in LX.
    repeat break_let.
    cbn in LX.
    inv LX.
    reflexivity.
  }
  replace (flat_map (definitions_of typ) t)
    with (@nil (definition typ (LLVMAst.block typ * list (LLVMAst.block typ))))
    in *.
  2:{
    clear - LX.
    unfold initXYplaceholders in LX.
    repeat break_let.
    cbn in LX.
    inv LX.
    reflexivity.
  }

  (* only globals defined by [initIRGlobals] *)
  replace (flat_map (type_defs_of typ) gdecls) with (@nil (ident * typ)) in *.
  2:{
    clear - LX LG.
    symmetry.

    unfold initXYplaceholders in LX.
    repeat break_let.
    cbn in LX.
    inv LX.

    clear - LG.
    rename l1 into data, l2 into data'.
    revert gdecls data data' LG.
    unfold initIRGlobals.

    cbn.

    generalize [(ID_Local (Name "Y"),
                 TYPE_Pointer (TYPE_Array (Z.to_N (Int64.intval o)) TYPE_Double));
                (ID_Local (Name "X"),
                 TYPE_Pointer (TYPE_Array (Z.to_N (Int64.intval i)) TYPE_Double));
                (ID_Global (Anon 1%Z), TYPE_Array (Z.to_N (Int64.intval o)) TYPE_Double);
                (ID_Global (Anon 0%Z), TYPE_Array (Z.to_N (Int64.intval i)) TYPE_Double)] as v.
    generalize dependent s1.
    induction globals; intros s v gdecls data data' H.
    -
      cbn in *.
      inl_inr_inv.
      reflexivity.
    -
      cbn in H.
      repeat break_match_hyp; try inl_inr.
      apply global_uniq_chk_preserves_st in Heqs1; subst i1.
      repeat inl_inr_inv; subst.
      invc H3.
      cbn.
      apply ListUtil.app_nil.
      +
        clear - Heqs2.
        rename Heqs2 into H.
        unfold initOneIRGlobal in H.
        cbn in *.
        repeat break_match.
        all: inv H.
        all: reflexivity.
      +
        destruct a.
        copy_apply initOneIRGlobal_state_change Heqs2; subst i2.
        erewrite IHglobals with
            (data:=l)
            (data':=data')
            (v:=(ID_Global (Name s), TYPE_Pointer (getIRType d)) :: v)
        ; clear IHglobals; try reflexivity.

        fold_initIRGlobals_rev.
        unfold addVar in *; cbn in *.
        rewrite Heqs3.
        reflexivity.
  }
  replace (flat_map (declarations_of typ) gdecls) with (@nil (declaration typ)) in *.
  2:{
    clear - LX LG.
    symmetry.

    unfold initXYplaceholders in LX.
    repeat break_let.
    cbn in LX.
    inv LX.

    clear - LG.
    rename l1 into data, l2 into data'.
    revert gdecls data data' LG.
    unfold initIRGlobals.

    cbn.

    generalize [(ID_Local (Name "Y"),
                 TYPE_Pointer (TYPE_Array (Z.to_N (Int64.intval o)) TYPE_Double));
                (ID_Local (Name "X"),
                 TYPE_Pointer (TYPE_Array (Z.to_N (Int64.intval i)) TYPE_Double));
                (ID_Global (Anon 1%Z), TYPE_Array (Z.to_N (Int64.intval o)) TYPE_Double);
                (ID_Global (Anon 0%Z), TYPE_Array (Z.to_N (Int64.intval i)) TYPE_Double)] as v.
    generalize dependent s1.
    induction globals; intros s v gdecls data data' H.
    -
      cbn in *.
      inl_inr_inv.
      reflexivity.
    -
      cbn in H.
      repeat break_match_hyp; try inl_inr.
      apply global_uniq_chk_preserves_st in Heqs1; subst i1.
      repeat inl_inr_inv; subst.
      invc H3.
      cbn.
      apply ListUtil.app_nil.
      +
        clear - Heqs2.
        rename Heqs2 into H.
        unfold initOneIRGlobal in H.
        cbn in *.
        repeat break_match.
        all: inv H.
        all: reflexivity.
      +
        destruct a.
        copy_apply initOneIRGlobal_state_change Heqs2; subst i2.
        erewrite IHglobals with
            (data:=l)
            (data':=data')
            (v:=(ID_Global (Name s), TYPE_Pointer (getIRType d)) :: v)
        ; clear IHglobals; try reflexivity.

        fold_initIRGlobals_rev.
        unfold addVar in *; cbn in *.
        rewrite Heqs3.
        reflexivity.
  }
  replace (flat_map (definitions_of typ) gdecls)
    with (@nil (definition typ (LLVMAst.block typ * list (LLVMAst.block typ))))
    in *.
  2:{
    clear - LX LG.
    symmetry.

    unfold initXYplaceholders in LX.
    repeat break_let.
    cbn in LX.
    inv LX.

    clear - LG.
    rename l1 into data, l2 into data'.
    revert gdecls data data' LG.
    unfold initIRGlobals.

    cbn.

    generalize [(ID_Local (Name "Y"),
                 TYPE_Pointer (TYPE_Array (Z.to_N (Int64.intval o)) TYPE_Double));
                (ID_Local (Name "X"),
                 TYPE_Pointer (TYPE_Array (Z.to_N (Int64.intval i)) TYPE_Double));
                (ID_Global (Anon 1%Z), TYPE_Array (Z.to_N (Int64.intval o)) TYPE_Double);
                (ID_Global (Anon 0%Z), TYPE_Array (Z.to_N (Int64.intval i)) TYPE_Double)] as v.
    generalize dependent s1.
    induction globals; intros s v gdecls data data' H.
    -
      cbn in *.
      inl_inr_inv.
      reflexivity.
    -
      cbn in H.
      repeat break_match_hyp; try inl_inr.
      apply global_uniq_chk_preserves_st in Heqs1; subst i1.
      repeat inl_inr_inv; subst.
      invc H3.
      cbn.
      apply ListUtil.app_nil.
      +
        clear - Heqs2.
        rename Heqs2 into H.
        unfold initOneIRGlobal in H.
        cbn in *.
        repeat break_match.
        all: inv H.
        all: reflexivity.
      +
        destruct a.
        copy_apply initOneIRGlobal_state_change Heqs2; subst i2.
        erewrite IHglobals with
            (data:=l)
            (data':=data')
            (v:=(ID_Global (Name s), TYPE_Pointer (getIRType d)) :: v)
        ; clear IHglobals; try reflexivity.

        fold_initIRGlobals_rev.
        unfold addVar in *; cbn in *.
        rewrite Heqs3.
        reflexivity.
  }

  repeat rewrite app_nil_r.
  repeat rewrite app_nil_l.

  cbn.
  eutt_hide_left LHS.

  assert (FB : (LHS ≈ LHS ;; LHS)%monad); [| rewrite FB; clear FB].
  {
    subst LHS.
    generalize (memory_set (memory_set mg (S (Datatypes.length globals)) mo)
        (Datatypes.length globals) mi, ()).
    clear.
    generalize (memoryH * ())%type.
    cbn.
    intros A a.
    rewrite Eq.bind_ret_l.
    reflexivity.
  }

  apply eutt_clo_bind with (UU:=fun _ => declarations_invariant_mcfg name).
  (* proving this goal will guarantee that [declarations_invariant_mcfg]
     is satisfied after [allocate_declarations] step *)

  1:{

    subst LHS.
    clear - VFN.
    generalize dependent
               (memory_set (memory_set mg (S (Datatypes.length globals)) mo)
                           (Datatypes.length globals) mi, ());
      intro p.
    eutt_hide_rel R.


    autorewrite with itree.

    unfold allocate_declaration.
    cbn.

    repeat match goal with
           | [ |- context[eqb name ?s]] =>
             destruct (eqb name s) eqn:TMP; [
               (apply eqb_eq in TMP;
                subst name;
                unfold valid_program in VFN;
                cbn in VFN;
                rewrite !Bool.andb_false_r in VFN;
                discriminate) | clear TMP]
           end.

    autorewrite with itree.

    rewrite interp_to_L3_bind.

    pose_interp_to_L3_alloca m' a' A AE.
    1:{
      unfold non_void.
      intros C. inversion C.
    }
    rewrite AE.
    cbn. repeat setoid_rewrite Eq.bind_ret_l.
    rewrite interp_to_L3_bind.
    rewrite interp_to_L3_GW.
    cbn; rewrite !ITree.Eq.Eq.bind_ret_l.
    autorewrite with itree.
    cbn.
    unfold alist_add.
    cbn.

    rewrite interp_to_L3_bind.

    pose_interp_to_L3_alloca m'' a'' A' AE'.
    1:{
      unfold non_void.
      intros C. inversion C.
    }
    rewrite AE'.
    cbn; rewrite !ITree.Eq.Eq.bind_ret_l.
    rewrite interp_to_L3_bind.
    rewrite interp_to_L3_GW.
    cbn; rewrite !ITree.Eq.Eq.bind_ret_l.
    cbn.
    replace (alist_add (Name "main") (DVALUE_Addr a'') [(Name name, DVALUE_Addr a')])
      with
        [(Name "main", DVALUE_Addr a'') ; (Name name, DVALUE_Addr a')].
    2:{
      assert(eqb name "main" ≡ false) as M.
      {
        clear - VFN.
        apply eqb_neq.
        intros C.
        rewrite C in VFN.
        cbn in VFN.
        inv VFN.
      }
      clear - M.
      unfold alist_add.
      apply eqb_neq in M.
      cbv.
      break_match.
      reflexivity.
      break_if.
      break_if.
      crush.
      crush.
      crush.
    }

    rewrite interp_to_L3_ret.
    apply eutt_Ret.
    subst R.
    unfold declarations_invariant_mcfg, declarations_invariant.
    unfold global_named_ptr_exists.
    split.
    -
      exists a''.
      reflexivity.
    -
      exists a'.
      rewrite alist_find_cons_neq.
      rewrite alist_find_cons_eq.
      reflexivity.
      reflexivity.
      crush.

  }

  intros.

  eutt_hide_rel REL.
  
  fold_map_monad_.
  repeat unfold fmap, Fmap_list'.

  (* splitting the lists in (1) and (3) *)
  (* just [rewrite map_app] doesn't work for some reason *)
  replace (map (Fmap_global typ dtyp (typ_to_dtyp [ ]))
               (flat_map (globals_of typ) gdecls ++ flat_map (globals_of typ) t))
    with (map (Fmap_global typ dtyp (typ_to_dtyp [ ])) (flat_map (globals_of typ) gdecls) ++
              map (Fmap_global typ dtyp (typ_to_dtyp [ ])) (flat_map (globals_of typ) t))
    by (rewrite map_app; reflexivity).

  (* splitting (1) and (3) into binds *)
  repeat break_match_goal.
  setoid_rewrite map_monad_app_.

  fold_initialization.
  simpl.

  remember (map (Fmap_global typ dtyp (typ_to_dtyp [ ]))
                (flat_map (globals_of typ) t))
    as XY.
  remember (map (Fmap_global typ dtyp (typ_to_dtyp [ ]))
                (flat_map (globals_of typ) gdecls))
    as GLOB.

  assert (FB : (LHS ≈ LHS ;; LHS)%monad); [| rewrite FB; clear FB].
  {
    subst LHS.
    clear.
    cbn.
    rewrite Eq.bind_ret_l.
    reflexivity.
  }
  rewrite interp_to_L3_bind.

  subst LHS REL.
  destruct p0 as [le0 stack0].
  destruct x as [x_id x_typ].

  remember (Datatypes.length globals) as lg.

  pose (fun '(memH, t0) '(memV, (l, t1, (g, t2))) =>
          post_alloc_invariant_mcfg globals (memH, t0) (memV, (l, t1, (g, t2)))
          /\
          declarations_invariant_mcfg name (memV, (l, t1, (g, t2))))
    as post_alloc_invariant_mcfg'.

  (* split the goal:
     1) allocate
     2) initialize
   *)
  apply eutt_clo_bind with (UU:=post_alloc_invariant_mcfg').
  - (* allocate (globals ++ yx) *)
    assert (TMP_EQ: eutt
             (fun '(m,_) '(m',_) => m = m')
             (ret (memory_set (memory_set mg (S lg) mo) lg mi, ()))
             (ITree.bind' (E:=E_mcfg)
                          (fun mg' => ret (memory_set
                                          (memory_set (fst mg') (S lg) mo)
                                          lg mi, ()))
                          (ret (mg, ()))))
      by (setoid_rewrite Eq.bind_ret_l; apply eutt_Ret; reflexivity).

    eapply eutt_weaken_left; [| exact TMP_EQ |]; clear TMP_EQ.
    {
      intros (?, ?) (?, ?) (? & [? ?] & ? & []).
      now cbn.
    }

    rewrite interp_to_L3_bind.
    cbn.

    pose (fun globals => (fun _ '(memV, (_, (g, _))) =>
                             allocated_globals memV g globals) : Rel_mcfg_T () ())
      as allocated_globals_mcfg.

    (* split the goal:
       1) allocate globals
       2) allocate yx
     *)
    apply eutt_clo_bind
      with (UU:=allocated_globals_mcfg globals).
    + (* allocate globals *)
      subst.

      fold_map_monad_.

      remember {|
          block_count := Compiler.block_count s0;
          local_count := Compiler.local_count s0;
          void_count := Compiler.void_count s0;
          Γ := (ID_Local (Name "Y"), TYPE_Pointer (TYPE_Array (Z.to_N (Int64.intval o)) TYPE_Double))
               :: (ID_Local (Name "X"),
                  TYPE_Pointer (TYPE_Array (Z.to_N (Int64.intval i)) TYPE_Double)) :: 
                  Γ s0 |} as s_yx.
     
      enough (
          forall pre post gdecls1 gdecls2 s' l',
            globals ≡ pre ++ post -> 
            gdecls ≡ gdecls1 ++ gdecls2 ->
            initIRGlobals_rev l1 pre s_yx ≡ inr (s', (l', gdecls1)) ->
            initIRGlobals_rev l' post s' ≡ inr (rev_firstn_Γ (length globals) s1,
                                                (l2, gdecls2)) ->
            allocated_globals_mcfg pre (mg, ())
                                      (m, (le0, stack0, (g, ()))) ->
            eutt (allocated_globals_mcfg (pre ++ post))
                 (Ret (mg, ()))
                    (interp_mcfg
                       (map_monad_ allocate_global
                                   (map (Fmap_global typ dtyp (typ_to_dtyp []))
                                        (flat_map (globals_of typ) gdecls2)))
                       g (le0, stack0) m)).
      {
        apply initIRGlobals_inr in LG.
        replace (globals) with ([] ++ globals) in * by reflexivity.
        apply initIRGlobals_rev_app_inv in LG.
        destruct LG as (l' & s' & gdecls1 & gdecls2 & PRE & POST & GDECLS).
        specialize (H0 [] globals gdecls1 gdecls2 s' l').
        full_autospecialize H0; try congruence.
        {
          cbn.
          unfold allocated_globals.
          intros.
          cbn in jc.
          lia.
        }
        inv PRE.
        apply H0.
      }

      intros pre post; revert pre.
      generalize dependent g.
      generalize dependent le0.
      generalize dependent stack0.
      generalize dependent m.
      induction post;
        intros m stack0 le0 g DI pre gdecls1 gdecls2 s' l' GLOBALS GDECLS PRE POST INV.
      *
        inv POST.
        cbn.
        rewrite interp_to_L3_bind.
        rewrite interp_to_L3_ret.
        rewrite Eq.bind_ret_l.
        rewrite interp_to_L3_ret.
        apply eutt_Ret.
        now rewrite app_nil_r.
      *
        cbn in POST.
        repeat break_match_hyp; try inl_inr.
        inversion POST; clear POST.
        rename l5 into gdecls2', t0 into g2';
          subst gdecls2.
        subst p p0 p1 p2 p3.
        subst i2 l4.
        
        replace (g2' :: gdecls2')
          with ([g2'] ++ gdecls2')
          in * by reflexivity.
        rewrite flat_map_app, map_app, map_monad_app_.
        simpl.
        rewrite app_nil_r.

        copy_apply initOneIRGlobal_is_global Heqs0.
        destruct H as [tg2 G2]; subst g2'.
        simpl.
        repeat rewrite Eq.bind_bind.
        do 2 setoid_rewrite Eq.bind_ret_l.

        rewrite GLOBALS in G.
        move G after INV.
        apply init_with_data_app in G.
        destruct G as ((m_pre & hdata_pre) & e_pre & e_post & IPRE & IPOST & E).
        cbn in IPOST.

        repeat break_match; try inl_inr.
        inversion IPOST; clear IPOST.
        subst.
        (* rename d into ne', *)
        rename l4 into e_post'.
        (* subst p1 p2 e_post. *)
        destruct p0 as [mg0 hdata0].

        cbn.
        rewrite interp_to_L3_bind.

        eutt_hide_left LHS.
        assert (FB : (LHS ≈ LHS ;; LHS)%monad); [| rewrite FB; clear FB; subst LHS].
        {
          subst LHS.
          clear.
          cbn.
          rewrite Eq.bind_ret_l.
          reflexivity.
        }
        
        pose (fun globals =>
                    (fun _ '(memV, (l, _, (g, _))) =>
                       allocated_globals memV g globals /\
                       declarations_invariant name (memV, (l, g))) : Rel_mcfg_T () ())
          as alloc_glob_decl_inv_mcfg.

        apply eutt_clo_bind with (UU:=alloc_glob_decl_inv_mcfg (pre ++ [a])).
        --
          cbn.
          repeat rewrite interp_to_L3_bind.
          (* Alloca ng *)
          pose_interp_to_L3_alloca m'' a'' A' AE'.
          {
            clear - Heqs0.
            unfold initOneIRGlobal in Heqs0.
            repeat break_match; invc Heqs0; cbn.
            now rewrite typ_to_dtyp_I.
            now rewrite typ_to_dtyp_D.
            now rewrite typ_to_dtyp_D_array.
          }
          rewrite AE'.

          (* GlobalWrite ng *)
          cbn; rewrite !ITree.Eq.Eq.bind_ret_l.
          rewrite interp_to_L3_GW.

          apply eutt_Ret.
          unfold alloc_glob_decl_inv_mcfg.
          split.

          ++
            unfold allocated_globals.
            intros.
            destruct (Nat.eq_dec j (length pre)).
            {
              replace (ListUtil.ith (l:=pre ++ [a]) (i:=j) jc)
                with a.
              2: {
                pose proof jc as jc'.
                rewrite ListUtil.length_app in jc'.
                erewrite ListUtil.ith_eq with (j:=length pre + 0); [| lia].
                erewrite ith_eq_app_r.
                reflexivity.
              }
              
              exists a''.
              split.
              -
                eapply allocate_allocated.
                eassumption.
              -
                cbn.
                unfold alist_add, in_global_addr.
                setoid_rewrite alist_find_cons_eq.
                reflexivity.
                clear - Heqs0.
                unfold initOneIRGlobal in Heqs0.
                repeat break_match; invc Heqs0.
                all: try lia; try reflexivity.
            }

            {
              pose proof jc as T.
              rewrite ListUtil.length_app in T; cbn in T.
              assert (jc' : j < length pre) by lia.
              rewrite ListUtil.ith_eq_app with (j:=j) (hj:=jc') by reflexivity.
              unfold allocated_globals_mcfg in *.
              clear - INV A'.
              unfold allocated_globals in INV.
              specialize (INV j jc').
              destruct INV as (ptr & AP & G).
              generalize dependent (Name (fst (ListUtil.ith (l:=pre) (i:=j) jc'))).
              intros id ?.
              destruct (RawIDOrd.eq_dec (g_ident tg2) id).
              -
                exists a''.
                split.
                +
                  eapply allocate_allocated; eassumption.
                +
                  cbn.
                  unfold in_global_addr, alist_add in *.
                  rewrite alist_find_cons_eq; congruence.
              -
                exists ptr.
                split.
                +
                  eapply allocated_allocate_allocated; eassumption.
                +
                  cbn.
                  unfold in_global_addr, alist_add in *.
                  rewrite alist_find_cons_neq by congruence.
                  rewrite remove_neq_alist; eauto.
                  all: typeclasses eauto.
            }
          ++
            cbn in *.
            unfold declarations_invariant, global_named_ptr_exists in *.
            destruct DI as [[mf__m MFM] [mf__n MFN]].
            clear - MFM MFN A'.
            split.
            **
              unfold alist_add.
              destruct (RawIDOrd.eq_dec (g_ident tg2) (Name "main")).
              rewrite alist_find_cons_eq; eauto.
              rewrite alist_find_cons_neq, remove_neq_alist; eauto.
              all: typeclasses eauto.
            **
              unfold alist_add.
              destruct (RawIDOrd.eq_dec (g_ident tg2) (Name name)).
              rewrite alist_find_cons_eq; eauto.
              rewrite alist_find_cons_neq, remove_neq_alist; eauto.
              all: typeclasses eauto.
        --
          intros.
          cbn in *.
          move IHpost at bottom.

          rewrite <-ListUtil.list_app_first_last.
          destruct u3 as (m' & le' & g'' & ?).
          repeat break_let.
          destruct le' as [le' stack'].

          copy_apply global_uniq_chk_preserves_st Heqs.
          subst i0.

          (* rewrite GLOBALS in LG. *)
          move LG at bottom.
          rewrite <-ListUtil.list_app_first_last in LG.
          apply initIRGlobals_inr in LG.
          apply initIRGlobals_rev_app_inv in LG.
          destruct LG as (l'' & s'' & g1'' & g2'' & PRE'' & POST'' & G'').

          eapply IHpost.
          ++
            clear - H.
            unfold alloc_glob_decl_inv_mcfg in H.
            intuition.
          ++
            rewrite ListUtil.list_app_first_last. reflexivity.
          ++
            rewrite ListUtil.list_app_first_last. reflexivity.
          ++
            (* [clear - PRE Heqs Heqs0.] doesn't work for some reason? *)
            clear IHpost; move PRE at bottom; move Heqs0 at bottom.

            eapply initIRGlobals_rev_app.
            eapply initIRGlobals_names_unique.
            eapply initIRGlobals_rev_inr.
            eapply PRE''.
            eassumption.
            cbn.
            rewrite Heqs0.
            reflexivity.
          ++
            eassumption.
          ++
            clear - H INV.
            unfold alloc_glob_decl_inv_mcfg in H.
            intuition.
    + (* allocate yx *)
      intros.
      unfold initXYplaceholders, addVars in LX.
      cbn in LX.
      repeat break_let.
      invc LX.
      cbn.
      repeat rewrite interp_to_L3_bind. 
      
      (* Alloca Y *)
      pose_interp_to_L3_alloca m'' a'' A' AE';
        [rewrite typ_to_dtyp_equation; congruence |].
      rewrite AE'.
      
      (* GlobalWrite Y *)
      cbn; rewrite !ITree.Eq.Eq.bind_ret_l.
      rewrite interp_to_L3_GW.
      cbn; rewrite !ITree.Eq.Eq.bind_ret_l.
      
      repeat rewrite interp_to_L3_bind.
      
      (* Alloca X *)
      pose_interp_to_L3_alloca m''' a''' A'' AE'';
        [rewrite typ_to_dtyp_equation; congruence |].
      rewrite AE''.
      
      (* GlobalWrite X *)
      cbn; rewrite !ITree.Eq.Eq.bind_ret_l.
      rewrite interp_to_L3_GW.
      cbn; rewrite !ITree.Eq.Eq.bind_ret_l.
      
      repeat rewrite interp_to_L3_ret, !ITree.Eq.Eq.bind_ret_l.
      cbn.
      rewrite interp_to_L3_ret.

      apply eutt_Ret.
      unfold post_alloc_invariant_mcfg', post_alloc_invariant_mcfg in *.
      break_let.
      split; [| admit].
      split.
      *
        unfold allocated_xy.
        do 2 eexists.
        repeat split.
        --
          eapply allocate_allocated.
          eassumption.
        --
          eapply allocated_allocate_allocated; [| eassumption].
          eapply allocate_allocated.
          eassumption.
        --
          unfold in_global_addr.
          unfold alist_add.
          rewrite alist_find_cons_eq; reflexivity.
        --
          unfold in_global_addr.
          unfold alist_add.
          rewrite alist_find_cons_neq by discriminate.
          rewrite remove_neq_alist; try typeclasses eauto; [| discriminate].
          rewrite alist_find_cons_eq; reflexivity.
      *
        unfold allocated_globals_mcfg, allocated_globals in *.
        intros.
        specialize (H0 j jc).
        destruct H0 as [ptr_llvm P].
        unfold in_global_addr in *.
        destruct P as [P1 P2].
        exists ptr_llvm.
        unfold alist_add.
        rewrite alist_find_cons_neq by discriminate.
        rewrite remove_neq_alist;
          try typeclasses eauto;
          try discriminate.
        rewrite alist_find_cons_neq
          by (intros C; inversion C; lia).
        rewrite remove_neq_alist;
          try typeclasses eauto;
          try (intros C; inversion C; lia).
        split.
        eapply allocated_allocate_allocated.
        eapply allocated_allocate_allocated.
        eassumption.
        eassumption.
        eassumption.
        erewrite ListUtil.ith_eq; [eassumption | reflexivity].
  - (* initialize (globals ++ yx) *)
    intros.

    assert (T : Ret (memory_set (memory_set mg (S lg) mo) lg mi, ())
                ≈
                ITree.bind' (E:=E_mcfg)
                            (fun mg' => ret (memory_set
                                            (memory_set (fst mg') (S lg) mo)
                                            lg mi, ()))
                            (ret (mg, ())))
      by (cbn; now rewrite Eq.bind_ret_l).
    rewrite T; clear T.

    destruct_unit.
    unfold post_alloc_invariant_mcfg' in H0.
    destruct u3 as (m', ((l', st'), (g', TU))); destruct_unit.
    cbn in H0.
    destruct u0 as (_ & _).
    subst p p1 u2.
    clear u1.
    rename H0 into POST_ALLOC.
    
    rewrite translate_bind, interp_to_L3_bind.
    subst.

    pose (fun globals : list (string * DSHType) =>
            (fun '(memH, _) '(memV, (l, t1, (g, t2))) =>
               post_init_invariant
                 name
                 (firstn (length globals) (e ++ [(DSHPtrVal (S (Datatypes.length globals)) o, true);
                        (DSHPtrVal (Datatypes.length globals) i, true)]))
                 {|
                   block_count := block_count;
                   local_count := local_count;
                   void_count := void_count;
                   Γ := firstn (length globals) Γ_globals |} memH (memV, (l, g)))
            : Rel_mcfg_T () ())
      as post_init_invariant'.

    apply eutt_clo_bind with (UU:=post_init_invariant' globals).
    +
      subst.
      unfold initialize_globals.

      remember {|
          block_count := Compiler.block_count s0;
          local_count := Compiler.local_count s0;
          void_count := Compiler.void_count s0;
          Γ := (ID_Local (Name "Y"),
                TYPE_Pointer (TYPE_Array (Z.to_N (Int64.intval o)) TYPE_Double))
               :: (ID_Local (Name "X"),
                  TYPE_Pointer (TYPE_Array (Z.to_N (Int64.intval i)) TYPE_Double))
               :: Γ s0 |}
        as s_yx.

      enough (
          forall pre post gdecls1 gdecls2 s' l1',
            globals ≡ pre ++ post -> 

            gdecls ≡ gdecls1 ++ gdecls2 ->

            initIRGlobals_rev l1 pre s_yx ≡ inr (s', (l1', gdecls1)) ->

            initIRGlobals_rev l1' post s' ≡ inr (rev_firstn_Γ (length globals) s1,
                                                 (l2, gdecls2)) ->

            post_init_invariant' pre (mg, ())
                                      (m', (l', st', (g', ()))) ->

            eutt (post_init_invariant' (pre ++ post))
                 (Ret (mg, ()))
                    (interp_mcfg
                       (translate _exp_E_to_L0
                          (map_monad_ initialize_global
                                      (map (Fmap_global typ dtyp (typ_to_dtyp []))
                                           (flat_map (globals_of typ) gdecls2))))
                       g' (l', st') m')).
      {
        replace (globals) with ([] ++ globals) in * by reflexivity.
        replace (Γ_globals) with ([] ++ Γ_globals) in * by reflexivity.
        apply initIRGlobals_inr in LG.
        apply initIRGlobals_rev_app_inv in LG.
        destruct LG as (l'' & s' & gdecls1 & gdecls2 & PRE & POST & GDECLS).
        specialize (H0 [] globals gdecls1 gdecls2 s' l'').
        full_autospecialize H0; try congruence.
        {
          cbn.
          split.
          -
            constructor.
            +
              cbn.
              intros ? ? ? ? ? C.
              rewrite nth_error_nil in C.
              inversion C.
            + repeat intro.
              econstructor.
              rewrite nth_error_nil in H0.
              inversion H0.
            +
              unfold no_id_aliasing.
              intros.
              rewrite nth_error_nil in H0.
              inversion H0.
            +
              unfold no_dshptr_aliasing.
              intros.
              rewrite nth_error_nil in H0.
              inversion H0.
            +
              cbn.
              unfold no_llvm_ptr_aliasing.
              intros.
              rewrite nth_error_nil in H0.
              inversion H0.
            +
              econstructor.
              rewrite nth_error_nil in H0.
              inversion H0.
            + solve_gamma_bound.
          -
            intuition.
        }
        inv PRE.
        replace ([] ++ gdecls2)
          with gdecls2
          by apply app_nil_l.
        apply H0.
      }

      intros pre post; revert pre.
      generalize dependent g'.
      generalize dependent l'.
      generalize dependent st'.
      generalize dependent m'.
      induction post;
        intros ? ? ? ? GINV ? ? ? ? ? GLOBALS GDECLS PRE POST PINV.
      *
        cbn in POST.
        inv POST.
        cbn.
        autorewrite with itree.
        rewrite interp_to_L3_ret.
        apply eutt_Ret.
        rewrite app_nil_r.
        apply PINV.
      *
        cbn in POST.
        repeat break_match_hyp; try inl_inr.
        inversion POST; clear POST.
        rename l5 into gdecls2', t0 into g2';
          subst gdecls2.
        subst p p0 p1 p2 p3.
        subst i2 l4.
        
        replace (g2' :: gdecls2')
          with ([g2'] ++ gdecls2')
          in * by reflexivity.
        rewrite flat_map_app, map_app, map_monad_app_.
        simpl.
        rewrite app_nil_r.

        copy_apply initOneIRGlobal_is_global Heqs0.
        destruct H0 as [tg2 G2]; subst g2'.
        simpl.
        repeat rewrite Eq.bind_bind.
        do 2 setoid_rewrite Eq.bind_ret_l.

        rewrite GLOBALS in G.
        move G after PINV.
        apply init_with_data_app in G.
        destruct G as ((m_pre & hdata_pre) & e_pre & e_post & IPRE & IPOST & E).
        cbn in IPOST.

        repeat break_match; try inl_inr.
        inversion IPOST; clear IPOST.
        (* rename d into ne', *)
        rename l4 into e_post'. subst.
        (* subst p p1 p2 e_post. *)
        destruct p0 as [mg0 hdata0].

        rewrite translate_bind.
        rewrite interp_to_L3_bind.

        eutt_hide_left LHS.
        assert (FB : (LHS ≈ LHS ;; LHS)%monad); [| rewrite FB; clear FB; subst LHS].
        {
          subst LHS.
          clear.
          cbn.
          rewrite Eq.bind_ret_l.
          reflexivity.
        }

        (* some state/Γ simplification *)
        copy_apply genIR_Γ IR.
        dedup_states.
        cbn [Γ append_to_Γ] in *.
        apply list_app_eqlen_eq_r in H0.
        2: {
          cbn.
          subst.
          clear - LX.
          unfold initXYplaceholders in LX.
          cbn in LX.
          repeat break_match; inv LX.
          reflexivity.
        }
        destruct H0 as [ΓG XY].

        subst.

        cbn in XY.
        inversion XY; clear XY.
        rename H1 into YID, H2 into YT, x_id into y_id, x_typ into y_typ.
        destruct y as (x_id, x_typ).
        inversion H3; clear H3.
        rename H1 into XID, H2 into XT.
        rename H4 into Γ0.
        rewrite !XID, !YID, !XT, !YT in *.

        cbn in *.
        remember
          {|
            block_count := Compiler.block_count s0;
            local_count := Compiler.local_count s0;
            void_count := Compiler.void_count s0;
            Γ := (y_id, y_typ) :: (x_id, x_typ) :: Γ s0 |}
          as s_yx.

        (* ZX TODO: might want to change the relation here *)
        apply eutt_clo_bind with (UU:=post_init_invariant' (pre ++ [a])).
        -- (* initialize the "new" global [a] *)
          cbn.
          autorewrite with itree.

          pose IPRE as E_PRE_LEN;
            apply init_with_data_len in E_PRE_LEN.

          rewrite _exp_E_to_L0_Global, subevent_subevent.
          rewrite interp_to_L3_bind.

          inversion_clear GINV as ((AXY & AG) & DI).
          destruct a as (a_nm, a_t).

          assert (T : exists v, Maps.lookup (g_ident tg2) g' ≡ Some v);
            [| destruct T as [av AV]].
          {
            unfold allocated_globals in AG.
            cbn in *.
            unfold in_global_addr in AG.
            specialize (AG (length pre)).
            autospecialize AG;
              [subst; rewrite ListUtil.length_app; cbn; lia |].
            destruct AG as [a_ptr [AA AIG]].
            erewrite ListUtil.ith_eq with (j:=length pre + 0)
              in AIG; [| lia].
            erewrite ith_eq_app_r in AIG.
            cbn in AIG.
            enough (TNM : g_ident tg2 ≡ Name a_nm).
            rewrite TNM.
            rewrite AIG.
            eexists.
            reflexivity.

            clear - Heqs0.
            repeat break_match;
              inv Heqs0;
              reflexivity.
          }
          rewrite (interp_to_L3_GR) by apply AV.

          autorewrite with itree.

          rename Heqs0 into IA.
          move IA at bottom.
          cbn in IA.
          repeat break_match_hyp;
            inv IA; cbn.
          ++
            rewrite typ_to_dtyp_I.
            rewrite interp_to_L3_bind.
            rewrite denote_exp_i64_mcfg.
            autorewrite with itree.
            cbn.
            autorewrite with itree.

            rewrite _exp_E_to_L0_Memory.
            rewrite subevent_subevent.

            cbn in AV.
            unfold allocated_globals in AG.
            specialize (AG (length pre)).
            autospecialize AG;
              [rewrite ListUtil.length_app; cbn; lia |].
            destruct AG as [a_ptr [AL IG]].
            erewrite ListUtil.ith_eq with (j:=length pre + 0)
              in IG; [| lia].
            erewrite ith_eq_app_r in IG.
            cbn in IG.
            unfold write.
            unfold in_global_addr in IG.
            replace av with (DVALUE_Addr a_ptr) in * by congruence; clear IG.
            destruct a_ptr as (a_ptr, a_off).
            copy_apply allocated_get_logical_block AL;
              rename H0 into AMB.
            destruct AMB as [[a_sz a_bytes a_id] AMB].
            rewrite interp_mcfg_store
              with
                (m' :=
                   add_logical_block a_ptr
                         (LBlock a_sz
                            (add_all_index
                               (serialize_dvalue
                                  (DVALUE_I64 (DynamicValues.Int64.repr (unsigned i0))))
                               a_off a_bytes) a_id) m')
            by (unfold write; rewrite AMB; reflexivity).
            apply eutt_Ret.
            constructor.
            **

              replace
                (firstn (Datatypes.length (pre ++ [(a_nm, DSHnat)]))
                   ((e_pre ++ p1 :: e_post') ++
                    [(DSHPtrVal (S (Datatypes.length (pre ++ [(a_nm, DSHnat)]))) o, true);
                    (DSHPtrVal (Datatypes.length (pre ++ [(a_nm, DSHnat)])) i , true)]))
                with
                  (e_pre ++ [p1]).
              2:{
                rewrite !app_length; cbn.
                rewrite list_cons_app with (l4:=e_post').
                rewrite <-!app_assoc, ->app_assoc.
                rewrite firstn_app.
                replace (length pre + 1 - length (e_pre ++ [p1]))
                  with 0
                  by (rewrite app_length; cbn; lia).
                rewrite firstn_O, firstn_all2, app_nil_r.
                reflexivity.
                rewrite app_length; cbn; lia.
              }

              replace (firstn (Datatypes.length (pre ++ [(a_nm, DSHnat)]))
                              (map IR_of_global (pre ++ (a_nm, DSHnat) :: post)))
                with (map IR_of_global (pre ++ [(a_nm, DSHnat)]))
              in *.
              2:{
                rewrite list_cons_app with (l4:=post).
                rewrite app_assoc, !map_app, firstn_app.
                replace
                  (length (pre ++ [(a_nm, DSHnat)]) -
                   length (map IR_of_global pre ++ map IR_of_global [(a_nm, DSHnat)]))
                  with 0
                  by (rewrite !app_length, !map_length; lia).
                rewrite firstn_O, firstn_all2, app_nil_r.
                reflexivity.
                rewrite !app_length, !map_length; lia.
              }

              constructor.
              ---
                unfold memory_invariant.
                intros.
                cbn in H1.
                destruct (Nat.eq_dec n (length e_pre)).
                +++
                  subst n.
                  rewrite nth_error_app2 in H0 by reflexivity.
                  rewrite Nat.sub_diag in H0.
                  cbn in H0.
                  some_inv; subst.
                  move Heqs2 at bottom.
                  unfold initOneFSHGlobal in Heqs2.
                  cbn in Heqs2.
                  repeat break_match_hyp; try inl_inr.
                  inversion Heqs2; clear Heqs2.
                  rename t0 into ne.
                  subst mg0 l4 .
                  unfold in_local_or_global_scalar.

                  apply nth_map_inv in H1.
                  destruct H1 as [a' [A' AX']].
                  rewrite nth_error_app2 in A'.
                  replace (length e_pre - length pre)
                    with 0 in * by lia.
                  cbn in A'.
                  inversion A'; clear A'; subst a'.
                  cbn in AX'.
                  invc AX'.
                  repeat eexists; eauto.
                  2: lia.
                  unfold read.
                  cbn [fst snd].
                  rewrite get_logical_block_of_add_logical_block.
                  unfold read_in_mem_block.
                  rewrite deserialize_serialize
                    by (rewrite typ_to_dtyp_I; constructor).
                  cbn.
                  do 3 f_equal.
                  (*
                  Search i2.       (* l1' -[rotate]-> i2 *)
                  Search l1'.      (* l1 -[initIRGlobals]-> l1' *)
                  Search l1.       (* data -[initXYplaceholders]-> l1 *)

                  Search ne.        (* b0 -[from_Z . bits_of_b46]-> ne *)
                  Search b0.        (* hdata_pre -[rotate]-> b0 *)
                  Search hdata_pre. (* l0 -[initFSHglobals]-> hdata_pre *)
                  Search l0.        (* l -[constMemBlock]-> l0 *)
                  Search l.         (* data -[constMemBlock]-> l *)
                   *)
                  admit.
                +++
                  admit.
              ---
                unfold WF_IRState.
                cbn.
                clear - Heqs2 IPRE.
                eapply initFSHGlobals_evalContext_typechecks.
                eapply initFSHGlobals_app.
                eassumption.
                unfold initFSHGlobals.
                unfold init_with_data.
                rewrite Heqs2.
                reflexivity.
              ---
                unfold no_id_aliasing.
                cbn.
                intros.
                admit.
              ---
                unfold no_dshptr_aliasing.
                admit.
              ---
                cbn.
                unfold no_llvm_ptr_aliasing.
                cbn.
                admit.
              ---
                eapply initFSHGlobals_id_allocated_preserve.
                2: eassumption.
                eapply initFSHGlobals_id_allocated.
                eapply initFSHGlobals_app with (post:=[(a_nm, DSHnat)]).
                eassumption.
                unfold initFSHGlobals.
                unfold init_with_data.
                rewrite Heqs2.
                reflexivity.
              --- admit. (* TODO: figure out gamma_bound here *)
            **
              constructor.
              all: cbn; clear - DI.
              all: unfold declarations_invariant in DI.
              all: intuition.
          ++ (* ZX TODO: see how these bullets can be done all in one *)
            admit.
          ++
            admit.
        -- (* initialize [post] *)
          admit.
    +
      intros.

      move LX at bottom.
      unfold initXYplaceholders, addVars in LX.
      cbn in LX.
      repeat break_let.
      invc LX.
      cbn.

      repeat rewrite translate_bind, interp_to_L3_bind.
      rewrite translate_trigger, _exp_E_to_L0_Global, subevent_subevent.
      (*
      inversion_clear H1 as [[[MI] DI] AXY].
      destruct AXY as (px & py & APX & APY & IX & IY).

      rewrite interp_to_L3_GR.
      2:{
        unfold in_global_addr in IY.
        unfold Maps.lookup.
        break_let.
        inversion Heqm2.
        eassumption.
      }
      memory_invariant
      rewrite Eq.bind_ret_l.
       *)
      admit.
Abort.

(* with init step  *)
Lemma compiler_correct_aux:
  forall (p:FSHCOLProgram)
    (data:list binary64)
    (pll: toplevel_entities typ (LLVMAst.block typ * list (LLVMAst.block typ))),
    forall s, compile_w_main p data newState ≡ inr (s,pll) ->
    eutt (succ_mcfg (bisim_full [] s)) (semantics_FSHCOL p data) (semantics_llvm pll).
Proof.
Abort.

(** Relation bewteen the final states of evaluation and execution
    of DHCOL program.

    At this stage we do not care about memory or environemnts, and
    just compare return value of [main] function in LLVM with
    evaulation results of DSHCOL.
 *)

Lemma bisim_partial_memory_subrelation: forall σ helix_state llvm_state,
    let '(mem_helix, _) := helix_state in
    let '(mem_llvm, (ρ, (g, _))) := llvm_state in
    bisim_partial σ newState helix_state llvm_state -> memory_invariant σ newState mem_helix (mem_llvm, (ρ, g)).
Proof.
  intros σ helix_state llvm_state.
  repeat break_let.
  subst.
  intros H.
  auto.
Qed.

(* Lemma bisim_full_partial_subrelation: forall σ helix_state llvm_state, *)
(*     let '(mem_helix, v_helix) := helix_state in *)
(*     let '(m, ((ρ,_), (g, v))) := llvm_state in *)
(*     bisim_full σ helix_state llvm_state -> bisim_partial σ (mem_helix, tt) (mk_LLVM_sub_state_partial_from_mem (inr v) (m, (ρ, g))). *)
(* Proof. *)
(*   intros σ helix_state llvm_state. *)
(*   repeat break_let. *)
(*   subst. *)
(*   intros H. *)
(*   unfold mk_LLVM_sub_state_partial_from_mem. *)
(*   auto. *)
(* Qed. *)

Set Nested Proofs Allowed.

Lemma initXYplaceholders_no_definitions :
  forall i o d x τ y τ' σ σ' b t,
    initXYplaceholders i o d x τ y τ' σ ≡ inr (σ', (b,t)) ->
    m_definitions (convert_types (mcfg_of_tle t)) ≡ [].
Proof.
  unfold initXYplaceholders; cbn; intros; simp; cbn in *; simp.
  reflexivity.
Qed.

Lemma initOneIRGlobal_no_definitions :
  forall l a σ σ' l' t,
    initOneIRGlobal l a σ ≡ inr (σ', (l', t)) ->
    m_definitions (convert_types (mcfg_of_tle [t])) ≡ [ ].
Proof.
  unfold initOneIRGlobal; cbn; intros; simp; cbn in *; auto.
Qed.

Opaque mcfg_of_tle.
Opaque convert_types.
Lemma init_with_data_initOneIRGlobal_no_definitions :
  forall g l x σ σ' b t,
    init_with_data initOneIRGlobal x l g σ ≡ inr (σ', (b, t)) ->
    m_definitions (convert_types (mcfg_of_tle t)) ≡ []. 
Proof.
  induction g as [| ? g IH]; intros; cbn in *; [simp; cbn; auto |].
  simp.
  apply IH in Heqs2.
  erewrite list_cons_app, mcfg_of_tle_app, m_definitions_app, Heqs2, <- app_nil_end, initOneIRGlobal_no_definitions; eauto.
Qed.

Lemma initIRGlobals_no_definitions :
  forall l g σ σ' b t,
    initIRGlobals l g σ ≡ inr (σ', (b,t)) -> 
    m_definitions (convert_types (mcfg_of_tle t)) ≡ [].
Proof.
  unfold initIRGlobals; cbn; intros; simp.
  eauto using init_with_data_initOneIRGlobal_no_definitions.
Qed.

Transparent mcfg_of_tle.
Lemma genMain_no_type_defs :
  forall s x τ τ' τ'' y t,
    genMain s x τ y τ' τ'' ≡ t ->
    m_type_defs (convert_types (mcfg_of_tle t)) ≡ [].
Proof.
  unfold genMain; cbn; intros; simp; subst; reflexivity.
Qed.

Lemma initXYplaceholders_no_type_defs :
  forall i o d x τ y τ' σ σ' b t,
    initXYplaceholders i o d x τ y τ' σ ≡ inr (σ', (b,t)) ->
    m_type_defs (convert_types (mcfg_of_tle t)) ≡ [].
Proof.
  unfold initXYplaceholders; cbn; intros; simp; cbn in *; simp.
  reflexivity.
Qed.

Lemma initOneIRGlobal_no_type_defs :
  forall l a σ σ' l' t,
    initOneIRGlobal l a σ ≡ inr (σ', (l', t)) ->
    m_type_defs (convert_types (mcfg_of_tle [t])) ≡ [ ].
Proof.
  unfold initOneIRGlobal; cbn; intros; simp; cbn in *; auto.
Qed.

Opaque mcfg_of_tle.
Lemma init_with_data_initOneIRGlobal_no_type_defs :
  forall g l x σ σ' b t,
    init_with_data initOneIRGlobal x l g σ ≡ inr (σ', (b, t)) ->
    m_type_defs (convert_types (mcfg_of_tle t)) ≡ []. 
Proof.
  induction g as [| ? g IH]; intros; cbn in *; [simp; cbn; auto |].
  simp.
  apply IH in Heqs2.
  erewrite list_cons_app, mcfg_of_tle_app, m_type_defs_app, Heqs2, <- app_nil_end, initOneIRGlobal_no_type_defs; eauto.
Qed.

Lemma initIRGlobals_no_type_defs :
  forall l g σ σ' b t,
    initIRGlobals l g σ ≡ inr (σ', (b,t)) -> 
    m_type_defs (convert_types (mcfg_of_tle t)) ≡ [].
Proof.
  unfold initIRGlobals; cbn; intros; simp.
  eauto using init_with_data_initOneIRGlobal_no_type_defs.
Qed.

Transparent mcfg_of_tle.


Hint Rewrite @translate_bind : local.
Hint Rewrite @interp_bind : local.
Hint Rewrite @translate_ret : local.
Hint Rewrite @interp_ret : local.
Hint Rewrite @translate_trigger : local.
Hint Rewrite @interp_trigger : local.
Hint Rewrite @bind_bind : local.
Hint Rewrite @bind_ret_l : local.
Hint Rewrite interp_to_L3_bind : local.
Hint Rewrite interp_to_L3_ret : local.

  (* Top-level compiler correctness lemma  *)
  Theorem compiler_correct:
    forall (p:FSHCOLProgram)
      (data:list binary64)
      (pll: toplevel_entities typ (LLVMAst.block typ * list (LLVMAst.block typ))),
    forall s, compile_w_main p data newState ≡ inr (s,pll) ->
      eutt (succ_mcfg (bisim_final [])) (semantics_FSHCOL p data) (semantics_llvm pll).
  Proof.
    intros * COMPILE.
    unfold compile_w_main, compile in COMPILE.
    cbn* in *; simp.

    unfold semantics_llvm, semantics_llvm_mcfg.
    cbn.
    unfold model_to_L3.
    unfold denote_vellvm_init.
    match goal with
      |- context[convert_types (mcfg_of_tle ?x)] => remember x as M
    end.

    assert (m_type_defs (convert_types (mcfg_of_tle M)) ≡ []).
    {
      subst M.
      rewrite ! mcfg_of_tle_app, !m_type_defs_app.
      erewrite initIRGlobals_no_type_defs; eauto.
      erewrite initXYplaceholders_no_type_defs; eauto.
    }

    match type of HeqM with
      context [TLE_Comment "Top-level operator definition" :: ?name :: ?main] =>
      let x := fresh "body" in
      let y := fresh "main" in
      remember name as x; remember main as y
    end.

    assert (EQ: m_definitions (convert_types (mcfg_of_tle M)) ≡
                              m_definitions (convert_types (mcfg_of_tle (body::main)))).
    { subst M.
      rewrite ! mcfg_of_tle_app, !m_definitions_app.
      erewrite initIRGlobals_no_definitions; eauto.
      erewrite initXYplaceholders_no_definitions; eauto.
    }

    unfold denote_vellvm.
    (* Require Import LibHyps.LibHyps. *)
    (* onAllHyps move_up_types. *)
    eutt_hide_left.

    rewrite EQ.
    unfold genMain in Heqmain.

    (* TODO : Is is true that P is preserved?
       TODO : Move this, that's completely orthogonal, was just thinking about it.
     *)
    Lemma post_condition_pure_to_state :
      forall {E F X S} (t : itree E X) (P : S -> Prop) Q (h: E ~> Monads.stateT S (itree F)),
      t ⤳ Q ->
      forall s, P s ->
           ((interp_state h t s) ⤳ (prod_pred P Q)).
    Proof.
      intros * POST s.
      unfold has_post in *.
      eapply eutt_interp_state in POST.
    Abort.


    
(* Arguments fmap /. *)
(* Arguments Fmap_list' /. *)
(* Arguments Fmap_definition /. *)
(* Arguments Fmap_declaration /. *)
(* Arguments Fmap_cfg /. *)
(* Arguments Fmap_block /. *)
(* (* Arguments Fmap_list /. *) *)
(* (* Arguments Fmap_phi /. *) *)
(* Arguments Fmap_code /. *)
(* (* Arguments Fmap_exp /. *) *)
(* (* Arguments Fmap_instr /. *) *)
(* (* Arguments Fmap_terminator /. *) *)
(* Arguments Fmap_option /. *)
(* Arguments Fmap_texp /. *)
(* Arguments Fmap_tident /. *)
(* subst main body. *)
(* simpl m_definitions. *)

      (* simpl. *)

      (* clear. *)
      (* progress cbn. *)
      (* unfold fmap, Fmap_definition. *)
      (* cbn. *)
      (* unfold fmap. *)
      (* unfold Fmap_declaration, Fmap_cfg. *)
      (* progress cbn. *)
      (* unfold fmap, Fmap_block. *)
      (* cbn. *)

(*     unfold semantics_FSHCOL. *)
(*     unfold denote_FSHCOL. *)

(*     subst. *)
(*     repeat rewrite mcfg_of_tle_app.  *)
(*     repeat rewrite m_definitions_app. *)


(* erewrite initXYplaceholders_no_definitions; eauto. *)
(* erewrite initIRGlobals_no_definitions; eauto. *)
(* simpl app. *)
     
(* repeat rewrite m_definitions_app. *)
(* simpl. *)

(*     subst. *)
(*     cbn. *)
(*     rewrite interp_to_L3_bind. *)
(*     autorewrite with local. *)

(*     apply eutt_clo_bind. *)


(*     simpl mcfg_of_tle. *)
(*     simpl m_definitions. *)
(*     simpl. *)
(*     Set Printing . *)
(*     rewrite interp_to_L3_bind. *)
    
(*     autorewrite with local. *)

    (*
    break_let; cbn in *; inv_sum.
    repeat (break_match_hyp || break_let); try inv_sum.

    eutt_hide_left.
    repeat rewrite app_assoc.
    repeat rewrite <- app_assoc.
    match goal with
      |- context[_ :: ?x ++ ?y ++ ?z ++ ?t] => remember x as f1; remember y as f2; remember t as f3; remember z as f4
    end.

    unfold semantics_llvm.
     *)

    (* break_match_goal. *)
    (* mcfg_of_modul *)
    (* Lemma semantics_llvm_red : *)
    (*   forall p, semantics_llvm p ≈ semantics_llvm p. *)
    (* Proof. *)
    (*   unfold semantics_llvm. *)
    (*   intros p. *)
    (*   unfold lift_sem_to_mcfg. *)
    (*   break_match_goal. *)
    (*   { *)
    (*     unfold semantics_llvm_mcfg, model_to_L3, denote_vellvm_init, denote_vellvm, translate_E_vellvm_mcfg. *)
    (*     simpl bind. *)
    (*     rewrite interp_to_L3_bind, translate_bind. *)
    (*     match goal with *)
    (*     | ?t ≈ _ => assert (t ≈ ITree.bind (lift_sem_to_mcfg (fun p =>  *)


    (* setoid_rewrite bind_bind. *)
    (*   unfold translate_E_vellvm_mcfg. *)
    (* setoid_rewrite (interp_to_L3_bind defined_intrinsics . *)

    (* unfold lift_sem_to_mcfg. *)
    (* break_match_goal. *)
    (* { *)
    (*   unfold semantics_llvm_mcfg, model_to_L3, denote_vellvm_init, denote_vellvm. *)
    (*   simpl bind. *)
    (*   unfold translate_E_vellvm_mcfg. *)
    (*   rewrite interp_to_L3_bind, translate_bind. *)

    (*   rewrite modul_of_toplevel_entities *)
    (*           cons, !modul_of_toplevel_entities_app in Heqo0. *)


    (*   repeat match goal with *)
    (*          | h: mcfg_of_modul _ (_ @ _) ≡ _ |- _ => *)
    (*            apply mcfg_of_app_modul in h; *)
    (*              destruct h as (? & ? & ?EQ & ?EQ & <-) *)
    (*          end. *)
    (*   Transparent map_option. *)
    (*   cbn in EQ. *)
    (*   injection EQ; clear EQ; intro EQ. *)
    (*   subst. l0. f1 . *)
    (*   cbn in EQ0. *)


    (* } *)

    (* { *)
    (*   (* The conversion from top level entities to modul failed *) *)
    (*   (* There is a toplevel entity with an empty list of instruction *) *)
    (*   admit. *)
    (* } *)



    (*         unfold global_YX,constArray in EQ1. *)
Abort.
