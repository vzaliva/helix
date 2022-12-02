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

Definition fun_declarations_invariant_mcfg (fnname:string) : Pred_mcfg_T unit :=
  fun '(memV,((l,sl),(g,_))) =>
    fun_declarations_invariant fnname (memV,(l,g)).

Definition anon_declarations_invariant_mcfg : Pred_mcfg_T unit :=
  fun '(memV,((l,sl),(g,_))) =>
    anon_declarations_invariant (memV,(l,g)).

(* YZ TODO : Move *)
Arguments allocate : simpl never.

Local Ltac pose_interp3_alloca m' a' A AE:=
  match goal with
  | [|-context[interp_mcfg (trigger (Alloca ?t)) ?g ?l ?m]] =>
    pose proof (interp3_alloca
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

Definition IR_of_global (g : string * DSHType) :=
  let '(nm, t) := g in
  (ID_Global (Name nm), TYPE_Pointer (getIRType t)).

Definition in_global_addr (g : global_env) (x : raw_id) (a : Addr.addr) := 
  g @ x ≡ Some (DVALUE_Addr a).

Definition allocated_xy (i o : Int64.int) (memV : memoryV) (g : global_env) :=
  exists ptr0 ptr1,
    dtyp_fits memV ptr0
              (typ_to_dtyp [] (TYPE_Array (Z.to_N (Int64.intval i)) TYPE_Double))
    /\ dtyp_fits memV ptr1
              (typ_to_dtyp [] (TYPE_Array (Z.to_N (Int64.intval o)) TYPE_Double))
    /\ in_global_addr g (Anon 0%Z) ptr0
    /\ in_global_addr g (Anon 1%Z) ptr1
    /\ fst ptr0 ≢ fst ptr1.

Definition allocated_globals
           (memV : memoryV)
           (g : global_env)
           (globals : list (string * DSHType))
           (l : local_env)
           (σ : evalContext)
           (s : IRState)
  :=
    (forall j (jc : j < length globals),
    exists ptr_llvm,
      dtyp_fits memV ptr_llvm (typ_to_dtyp [] (getIRType (snd (ListUtil.ith jc))))
      /\ in_global_addr g (Name (fst (ListUtil.ith jc))) ptr_llvm)
      /\ no_llvm_ptr_aliasing (firstn (length globals) σ) s l g.
 
Definition post_alloc_invariant_mcfg
           (i o : Int64.int)
           (globals : list (string * DSHType))
           (σ : evalContext)
           (s : IRState)
  : Rel_mcfg_T unit unit :=
  fun _ '(memV, (l, _, (g, _))) =>
    allocated_xy i o memV g /\
    allocated_globals memV g globals l σ s.

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

Lemma initFSHGlobals_no_overwrite_eq
      (m0 m : memoryH)
      (hdata0 hdata : list binary64)
      (globals : list (string * DSHType)) 
      (σ : list (DSHVal * bool))
  :
    initFSHGlobals hdata0 m0 globals ≡ inr (m, hdata, σ) →
    forall k b, memory_lookup m0 k ≡ Some b ->
           memory_lookup m k ≡ Some b.
Proof.
  intros I k b M0K.

  move globals at top.
  dependent induction globals; intros.
  -
    invc I.
    assumption.
  -
    cbn in I.
    repeat break_match; invc I.
    unfold initOneFSHGlobal in Heqs.
    repeat break_match; invc Heqs.
    all: eapply IHglobals; try eassumption.
    destruct (Nat.eq_dec k (memory_next_key m0)).
    *
      subst.
      exfalso; clear - M0K.
      pose proof memory_lookup_memory_next_key_is_None m0 as C.
      rewrite M0K in C.
      inv C.
    *
      unfold memory_set.
      unfold memory_lookup.
      rewrite Memory.NP.F.add_neq_o by congruence.
      assumption.
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

Lemma initOneFSHGlobal_no_overwrite_eq
      (m0 m : memoryH)
      (hdata0 hdata : list binary64)
      (g : string * DSHType)
      (e : DSHVal * bool)
  :
    initOneFSHGlobal (m0, hdata0) g ≡ inr (m, hdata, e) →
    forall k b, memory_lookup m0 k ≡ Some b ->
           memory_lookup m k ≡ Some b.
Proof.
  intros.
  eapply initFSHGlobals_no_overwrite_eq
    with (globals:=[g]).
  cbn.
  now rewrite H.
  assumption.
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
(* similar to [interp_cfg3_GR] *)
Lemma interp3_GR : forall id g l m v,
  Maps.lookup id g ≡ Some v ->
  interp_mcfg3 (trigger (GlobalRead id)) g l m ≈ Ret (m,(l,(g,v))).
Proof.
  intros * LU.
  unfold interp_mcfg3.
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
      (translate exp_to_L0
                 (denote_exp (Some (DTYPE_Double))
                             (EXP_Double t)))
      g l m
    ≈
    Ret (m, (l, (g, UVALUE_Double t))).
Proof.
  intros; unfold denote_exp; cbn.
  rewrite translate_ret, interp3_ret.
  reflexivity.
Qed.


(* ZX TODO: might want to move to vellvm *)
(* similar to [denote_exp_i64] *)
Lemma denote_exp_i64_mcfg : forall t g l m,
    interp_mcfg
      (translate exp_to_L0
                 (denote_exp (Some (DTYPE_I 64))
                             (EXP_Integer (unsigned t))))
       g l m
    ≈
    Ret (m, (l, (g, UVALUE_I64 (DynamicValues.Int64.repr (unsigned t))))).
Proof.
  intros; unfold denote_exp; cbn.
  rewrite translate_ret, interp3_ret.
  reflexivity.
Qed.

Lemma denote_exp_ID :forall g l m id τ ptr,
    in_local_or_global_addr l g id ptr ->
    interp_cfg3 (translate exp_to_instr (denote_exp (Some τ) (EXP_Ident id))) g l m
    ≈
    Ret (m,(l,(g,UVALUE_Addr ptr))).
Proof.
  intros. destruct id eqn: Hh; [ rewrite denote_exp_GR | rewrite denote_exp_LR ] ; eauto; try reflexivity.
Qed.

(* ZX TODO: might want to move to vellvm *)
(* similar to [interp_cfg_to_L3_store] *)
Lemma interp_mcfg_store:
  ∀ (m m' : memoryV) (val : dvalue) (a : addr) g l,
    write m a val ≡ inr m' →
    interp_mcfg (trigger (Store (DVALUE_Addr a) val)) g l m ≈ Ret (m', (l, (g, ()))).
Proof.
  intros m m' val a g l WRITE.
  unfold interp_mcfg3.
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

Lemma exp_to_L0_Global : forall {X} (e : LLVMGEnvE X),
    exp_to_L0 (subevent X e) ≡ subevent X e.
Proof.
  reflexivity.
Qed.

Lemma exp_to_L0_Memory : forall {X} (e : MemoryE X),
    exp_to_L0 (subevent X e) ≡ subevent X e.
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
      eapply initFSHGlobals_no_overwrite_eq in Heqs0.
      2: {
        rewrite memory_lookup_memory_set_eq.
        reflexivity.
      }
      apply memory_is_set_is_Some.
      rewrite Heqs0.
      reflexivity.
    +
      rewrite nth_error_Sn in H0.
      destruct p0.
      eapply IHglobals; eassumption.
Qed.

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
  dependent induction globals.
  all: unfold id_allocated.
  all: intros IA0 I * NTH.
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
    assert (IA1 : id_allocated σ m1).
    {
      unfold id_allocated.
      intros * NTH0.
      apply IA0 in NTH0.
      apply memory_is_set_is_Some in NTH0.
      apply is_Some_def in NTH0.
      destruct NTH0 as [m0a1 M0A1].
      copy_eapply initOneFSHGlobal_no_overwrite_eq Heqs.
      apply memory_is_set_is_Some.
      now rewrite H.
      eassumption.
    }
    clear Heqs IA0.

    eapply IA1 in NTH.
    eapply memory_is_set_is_Some in NTH.
    apply is_Some_def in NTH.
    destruct NTH as [m1a0 M1A0].
    copy_eapply initFSHGlobals_no_overwrite_eq Heqs0.
    apply memory_is_set_is_Some.
    now rewrite H.
    eassumption.
Qed.

Lemma initFSHGlobals_no_id_aliasing
      (globals : list (string * DSHType))
      (m0 m : memoryH)
      (hdata0 hdata : list binary64) 
      (σ : evalContext)
  :
    list_uniq fst globals ->
    initFSHGlobals hdata0 m0 globals ≡ inr (m, hdata, σ) →
    ∀ (n1 n2 : nat) (id : ident) (τ τ' : typ) (v1 v2 : DSHVal * bool),
      nth_error σ n1 ≡ Some v1 ->
      nth_error σ n2 ≡ Some v2 ->
      nth_error (map IR_of_global globals) n1 ≡ Some (id, τ) ->
      nth_error (map IR_of_global globals) n2 ≡ Some (id, τ') ->
      n2 ≡ n1.
Proof.
  intros Q I; intros.
  dependent induction globals.
  -
    cbn in *.
    rewrite nth_error_nil in *.
    discriminate.
  -
    cbn in *.
    repeat break_match;
      invc I.
    destruct p0 as (m1, hdata1).
    destruct (Nat.eq_dec n1 0) as [N1|N1],
             (Nat.eq_dec n2 0) as [N2|N2].
    + (* 0, 0 *)
      congruence.
    + (* 0, S *)
      exfalso; clear IHglobals; subst n1.
      apply Nat.neq_0_r in N2.
      destruct N2 as [t N2]; subst n2; rename t into n2.
      cbn in *.
      inversion H; clear H; subst v1.
      destruct a as (a_nm, a_t).
      inversion H1; clear H1; subst id τ.

      clear - Q H2.
      apply list_uniq_cons in Q.
      destruct Q as [_ C].
      apply nth_map_inv in H2.
      destruct H2 as (a & [A IA]).
      contradict C.
      exists n2; exists a.
      destruct a as (a_nm', a_t').
      cbn in IA; invc IA.
      intuition.
    + (* S, 0 *)
      exfalso; clear IHglobals; subst n2.
      apply Nat.neq_0_r in N1.
      destruct N1 as [t N1]; subst n1; rename t into n1.
      cbn in *.
      inversion H0; clear H0; subst v2.
      destruct a as (a_nm, a_t).
      inversion H2; clear H2; subst id τ'.

      clear - Q H1.
      apply list_uniq_cons in Q.
      destruct Q as [_ C].
      apply nth_map_inv in H1.
      destruct H1 as (a & [A IA]).
      contradict C.
      exists n1; exists a.
      destruct a as (a_nm', a_t').
      cbn in IA; invc IA.
      intuition.
    + (* S, S *)
      apply Nat.neq_0_r in N1.
      apply Nat.neq_0_r in N2.
      destruct N1 as [t1 N1], N2 as [t2 N2].
      subst n1 n2; rename t1 into n1, t2 into n2.
      f_equal.
      cbn in *.
      eapply IHglobals.
      1: eapply list_uniq_de_cons.
      all: eassumption.
Qed.

Lemma list_uniq_app
      {A B : Type}
      (f : A -> B)
      (l1 l2 : list A)
  :
    list_uniq f (l1 ++ l2) ->
    list_uniq f l1 /\ list_uniq f l2.
Proof.
  intros.
  unfold list_uniq in *.
  split; intros.
  -
    specialize (H x y a b).
    full_autospecialize H.
    1,2: apply ListNth.nth_error_weaken; assumption.
    all: assumption.
  -
    specialize (H (length l1 + x) (length l1 + y) a b).
    full_autospecialize H.
    1,2: rewrite ListUtil.app_nth_error2 by lia.
    1: replace (length l1 + x - length l1) with x by lia.
    2: replace (length l1 + y - length l1) with y by lia.
    1,2,3: assumption.
    lia.
Qed.

Lemma allocated_add_logical_block
      (m : memoryV)
      (a : addr)
      (id : Z)
      (lb : logical_block)
  :
    allocated a m → 
    allocated a (add_logical_block id lb m).
Proof.
  intros.
  unfold add_logical_block, add_logical_block_mem.
  unfold allocated in *.
  repeat break_let.
  invc Heqm0.
  now apply member_add_preserved.
Qed.

Lemma memory_next_key_le_S (m : memoryH) (mb : mem_block) :
  memory_next_key (memory_set m (memory_next_key m) mb) <=
  S (memory_next_key m).
Proof.
  remember (memory_next_key m) as n.
  remember (memory_next_key (memory_set m n mb)) as nn.
  enough (not (nn > S n)) by lia.
  intros C.
  assert (exists k, k > n /\ nn ≡ S k).
  {
    exists (nn - (S n) + n).
    lia.
  }
  destruct H as [k [K MS]].
  subst.
  apply memory_next_key_S in MS.
  apply memory_is_set_is_Some in MS.
  rewrite memory_lookup_memory_set_neq
    in MS
    by lia.
  apply memory_is_set_is_Some in MS.
  apply mem_block_exists_next_key_gt in MS.
  lia.
Qed.

Lemma initOneFSHGlobal_memory_next_key
      (m m' : memoryH)
      (data data' : list binary64)
      (g : string * FHCOL.DSHType) 
      (r : FHCOL.DSHVal * bool)
  :
    initOneFSHGlobal (m, data) g ≡ inr (m', data', r) ->
    memory_next_key m <= memory_next_key m' <= S (memory_next_key m).
Proof.
  intros.
  unfold initOneFSHGlobal in H.
  repeat break_match; invc H;
    try lia.
  split.
  -
    enough (memory_next_key
              (memory_set m (memory_next_key m) m0)
            > memory_next_key m)
      by lia.
    now eapply memory_set_memory_next_key_gt.
  -
    apply memory_next_key_le_S.
Qed.

Lemma initFSHGlobals_memory_keys
      (globals : list (string * FHCOL.DSHType)) 
      (data data' : list binary64)
      (m m' : memoryH)
      (σ : FHCOLEval.evalContext)
  :
    initFSHGlobals data m globals ≡ inr (m', data', σ) ->
    memory_next_key m <= memory_next_key m' <= memory_next_key m + length globals.
Proof.
  intros.
  split.
  -
    revert_until globals.
    induction globals;
      intros * I.
    + now invc I.
    +
      cbn in I.
      repeat break_match; invc I.
      destruct p0.
      apply initOneFSHGlobal_memory_next_key in Heqs.
      apply IHglobals in Heqs0.
      lia.
  -
    revert_until globals.
    induction globals;
      intros * I.
    + invc I; cbn; lia.
    +
      cbn in I.
      repeat break_match; invc I.
      destruct p0.
      apply initOneFSHGlobal_memory_next_key in Heqs.
      apply IHglobals in Heqs0.
      cbn; lia.
Qed.


Lemma initFSHGlobals_addr_lower_bound
      (globals : list (string * FHCOL.DSHType)) 
      (data data' : list binary64)
      (m m' : memoryH)
      (σ : FHCOLEval.evalContext)
  :
    initFSHGlobals data m globals ≡ inr (m', data', σ) ->
    forall n a sz f,
      nth_error σ n ≡ Some (DSHPtrVal a sz, f) ->
      memory_next_key m <= a.
Proof.
  revert_until globals.
  induction globals as [| ng globals].
  -
    intros.
    cbn in H; invc H.
    now rewrite nth_error_nil in H0.
  -
    intros * INIT * AN.
    cbn in INIT.
    repeat break_match; invc INIT.
    destruct n.
    +
      cbn in AN; invc AN.
      clear - Heqs.
      unfold initOneFSHGlobal in Heqs.
      repeat break_match; invc Heqs.
      reflexivity.
    +
      cbn in AN.
      destruct p0 as (m1, data1).
      eapply IHglobals in Heqs0.
      2: eassumption.
      clear - Heqs Heqs0.
      unfold initOneFSHGlobal in Heqs.
      repeat break_match; invc Heqs;
        try lia.
      enough (memory_next_key
                (memory_set m (memory_next_key m) m0)
              > (memory_next_key m))
        by lia.
      now eapply memory_set_memory_next_key_gt.
Qed.

Lemma initFSHGlobals_addr_upper_bound
      (globals : list (string * FHCOL.DSHType)) 
      (data data' : list binary64)
      (m m' : memoryH)
      (σ : FHCOLEval.evalContext)
  :
    initFSHGlobals data m globals ≡ inr (m', data', σ) ->
    forall n a sz f,
      nth_error σ n ≡ Some (DSHPtrVal a sz, f) ->
      a < memory_next_key m'.
Proof.
  revert_until globals.
  induction globals as [| ng globals] using list_rev_ind.
  -
    intros.
    cbn in H; invc H.
    now rewrite nth_error_nil in H0.
  -
    intros * INIT * AN.
    apply initFSHGlobals_app_inv in INIT.
    destruct INIT as (m1 & data1 & σ1 & σ' & I & IN & Σ).
    subst σ.
    cbn in IN.
    repeat break_match; invc IN; rename Heqs into IN.
    destruct (Nat.eq_dec n (length σ1)).
    +
      subst.
      rewrite ListNth.nth_error_app_R, Nat.sub_diag in AN;
        [| reflexivity].
      invc AN.
      unfold initOneFSHGlobal in IN.
      repeat break_match; invc IN.
      enough (memory_next_key
                (memory_set m1 (memory_next_key m1) m0)
              > memory_next_key m1)
        by lia.
      now eapply memory_set_memory_next_key_gt.
    +
      rewrite ListNth.nth_error_app_L in AN.
      2: {
        apply nth_error_in in AN.
        rewrite app_length in AN; cbn in AN.
        lia.
      }
      clear n0.
      eapply IHglobals with (a:=a) in I; [| eassumption].
      apply initOneFSHGlobal_memory_next_key in IN.
      lia.
Qed.

Lemma initFSHGlobals_addr_bound
      (globals : list (string * FHCOL.DSHType)) 
      (data data' : list binary64)
      (m m' : memoryH)
      (σ : FHCOLEval.evalContext)
  :
    initFSHGlobals data m globals ≡ inr (m', data', σ) ->
    forall n a sz f,
      nth_error σ n ≡ Some (DSHPtrVal a sz, f) ->
      memory_next_key m <= a < memory_next_key m + length globals.
Proof.
  intros.
  split.
  - eapply initFSHGlobals_addr_lower_bound in H;
      eassumption.
  - copy_eapply initFSHGlobals_addr_upper_bound H;
      [| eassumption].
    apply initFSHGlobals_memory_keys in H.
    lia.
Qed.

Lemma nth_error_in_app
      {A : Type}
      (l1 l2 : list A)
      (a : A)
      (n : nat)
  :
    nth_error (l1 ++ l2) n ≡ Some a ->
    (n < length l1 /\ nth_error l1 n ≡ Some a) \/
    (length l1 <= n /\ nth_error l2 (n - length l1) ≡ Some a).
Proof.
  intros N.
  destruct (le_lt_dec (length l1) n).
  -
    right.
    intuition.
    erewrite <-nth_error_app2;
      eassumption.
  -
    left.
    intuition.
    erewrite <-nth_error_app1;
      eassumption.
Qed.

Lemma nth_error_in_list_of_two
      {A : Type}
      (e a1 a2 : A)
      (n : nat)
  :
    nth_error [a1; a2] n ≡ Some e ->
    (n ≡ 0 /\ a1 ≡ e) \/ (n ≡ 1 /\ a2 ≡ e).
Proof.
  intro E.
  destruct n; [| destruct n];
    invc E; auto.
  now rewrite nth_error_nil in H0.
Qed.

Lemma alist_add_find_some
      {K V : Type}
      {RD : RelDec eq}
      {RC : RelDec_Correct RD}
      (k k' : K)
      (v v' : V)
      (al : alist K V)
  :
    alist_add k v al @ k' ≡ Some v' ->
    (k' ≡ k /\ v' ≡ v) \/ (k' ≢ k /\ al @ k' ≡ Some v').
Proof.
  intros A.
  destruct (rel_dec k k') eqn:KR.
  - left.
    rewrite rel_dec_correct in KR; subst k'.
    rewrite alist_find_add_eq in A.
    now invc A.
  - right.
    rewrite <-neg_rel_dec_correct in KR.
    rewrite alist_find_neq in A by auto.
    auto.
Qed.

Lemma initFSHGlobals_no_dshptr_aliasing
      (globals : list (string * DSHType))
      (m0 m : memoryH)
      (hdata0 hdata : list binary64) 
      (σ : evalContext)
  :
    initFSHGlobals hdata0 m0 globals ≡ inr (m, hdata, σ) →
    no_dshptr_aliasing σ.
Proof.
  intros I.
  unfold no_dshptr_aliasing.
  intros.
  dependent induction globals.
  -
    cbn in I.
    invc I.
    rewrite nth_error_nil in *.
    discriminate.
  -
    cbn in I.
    repeat break_match; invc I.
    destruct p0 as (m1, hdata1).
    rename n' into n1, n into n2.
    destruct (Nat.eq_dec n1 0) as [N1|N1],
             (Nat.eq_dec n2 0) as [N2|N2].
    + (* 0, 0 *)
      congruence.
    + (* 0, S *)
      exfalso; clear IHglobals; subst n1.
      apply Nat.neq_0_r in N2.
      destruct N2 as [t N2]; subst n2; rename t into n2.
      cbn in *.
      inversion H0; clear H0; subst p1.

      destruct a as (a_nm, a_t).
      cbn in Heqs.
      repeat break_match; invc Heqs.
      generalize dependent (memory_next_key m0).
      intros k I N.
      copy_eapply initFSHGlobals_addr_bound I.
      2: eassumption.
      destruct H as [C _].
      clear - C.
      enough (memory_next_key (FHCOL.memory_set m0 k m2) > k)
        by lia.
      now eapply memory_set_memory_next_key_gt.
    + (* S, 0 *)
      exfalso; clear IHglobals; subst n2.
      apply Nat.neq_0_r in N1.
      destruct N1 as [t N1]; subst n1; rename t into n1.
      cbn in *.
      inversion H; clear H; subst p1.

      destruct a as (a_nm, a_t).
      cbn in Heqs.
      repeat break_match; invc Heqs.
      generalize dependent (memory_next_key m0).
      intros k I N.
      clear - I N.
      copy_eapply initFSHGlobals_addr_bound I.
      2: eassumption.
      destruct H as [C _].
      clear - C.
      enough (memory_next_key (FHCOL.memory_set m0 k m2) > k)
        by lia.
      now eapply memory_set_memory_next_key_gt.
    + (* S, S *)
      apply Nat.neq_0_r in N1.
      apply Nat.neq_0_r in N2.
      destruct N1 as [t1 N1], N2 as [t2 N2].
      subst n1 n2; rename t1 into n1, t2 into n2.
      f_equal.
      cbn in *.
      eapply IHglobals; eassumption.
Qed.

Lemma nth_error_ith
      {A : Type}
      (a : A)
      (l : list A)
      (i : nat)
      (ic : i < length l)
  :
    ListUtil.ith (l:=l) (i:=i) ic ≡ a
    <->
    nth_error l i ≡ Some a.
Proof.
  dependent induction l.
  -
    inv ic.
  -
    cbn.
    break_match; subst; cbn in *.
    + split; congruence.
    + eapply IHl.
Qed.

Lemma initOneIRGlobal_ident
      (data0 data1 : list binary64)
      (s0 s1 : IRState)
      (a_nm : string) 
      (a_t : DSHType)
      (ag : global typ)
  :
    initOneIRGlobal data0 (a_nm, a_t) s0 ≡ inr (s1, (data1, TLE_Global ag)) ->
    g_ident ag ≡ Name a_nm.
Proof.
  intros.
  cbn in H.
  repeat break_match;
    now invc H.
Qed.

Lemma mem_block_exists_union (m1 m2 : memory) (n : nat) :
  mem_block_exists n m1 \/ mem_block_exists n m2 ->
  mem_block_exists n (memory_union m1 m2).
Proof.
  intros [M | M].
  all: rewrite mem_block_exists_exists in *.
  all: destruct M as [mb M].
  all: unfold memory_lookup, memory_union in *.
  all: rewrite Memory.NP.F.map2_1bis by reflexivity.
  all: break_match; try some_none; eauto.
Qed.

Lemma initOneFSHGlobal_mem_block_exists
      (addr : nat)
      (m0 m1 : memoryH)
      (data0 data1 : list binary64) 
      (n : Int64.int)
      (f : bool)
      (a : string * DSHType)
  :
      initOneFSHGlobal (m0, data0) a ≡ inr (m1, data1, (DSHPtrVal addr n, f)) ->
      mem_block_exists addr m1.
Proof.
  intros.
  destruct a as (a_nm, a_t).
  cbn in H.
  repeat break_match; invc H.
  apply mem_block_exists_exists.
  rewrite memory_lookup_memory_set_eq.
  eauto.
Qed.

(* [map_monad] unfolds into its [loop] otherwise *)
Lemma map_monad_cons
      {A B : Type}
      `{Monad m}
      (f : A -> m B)
      (x : A)
      (xs : list A)
  :
    map_monad f (x::xs) ≡ (b <- f x ;;
                         bs <- map_monad f xs ;;
                         ret (b::bs))%monad.
Proof.
  reflexivity.
Qed.

Lemma map_monad_map
      {A B C : Type}
      `{Monad m}
      (f : B -> m C)
      (g : A -> B)
      (l : list A)
  :
    map_monad f (map g l) ≡ map_monad (fun x => f (g x)) l.
Proof.
  induction l.
  reflexivity.
  now rewrite map_cons, !map_monad_cons, IHl.
Qed.

(* 1) This could be more general than itrees
   2) A stronger version: [forall "a in l"] *)
Lemma map_monad_ret_map
      {A B : Type}
      {E : Type -> Type}
      (f : A -> itree E B)
      (g : A -> B)
      (l : list A)
  :
    (forall a, f a ≈ Ret (g a)) ->
    map_monad f l ≈ Ret (map g l).
Proof.
  intros FG.
  induction l.
  - reflexivity.
  - rewrite map_monad_cons, map_cons.
    cbn.
    rewrite FG.
    cbn in IHl.
    setoid_rewrite IHl.
    now rewrite !Eq.bind_ret_l.
Qed.

(* ZX TODO: this really needs to be generalized with MonadLaws. see above. *)
Lemma map_monad_inr_map
      {A B : Type}
      (f : A -> err B)
      (g : A -> B)
      (l : list A)
  :
    (forall a, f a ≡ inr (g a)) ->
    map_monad f l ≡ inr (map g l).
Proof.
  intros FG.
  induction l.
  - reflexivity.
  - now rewrite map_monad_cons, map_cons, FG, IHl.
Qed.

(* ZX TODO: might want to move to vellvm *)
(* similar to [interp_cfg_to_L3_concretize_or_pick_concrete] *)
Lemma interp_mcfg_concretize_or_pick_concrete :
  forall (uv : uvalue) (dv : dvalue) P g ρ m,
    is_concrete uv ->
    uvalue_to_dvalue uv ≡ inr dv ->
    interp_mcfg (concretize_or_pick uv P) g ρ m ≈ Ret (m, (ρ, (g, dv))).
Proof.
  intros uv dv P g ρ m CONC CONV.
  unfold concretize_or_pick.
  rewrite CONC.
  cbn.
  unfold lift_err.
  now rewrite CONV, interp3_ret.
Qed.

(* ZX TODO: might want to move to vellvm *)
(* similar to [interp_cfg_to_L3_concretize_or_pick_concrete_exists] *)
Lemma interp_mcfg_concretize_or_pick_concrete_exists :
  forall (uv : uvalue) P g ρ m,
    is_concrete uv ->
    exists dv, uvalue_to_dvalue uv ≡ inr dv /\
          interp_mcfg (concretize_or_pick uv P) g ρ m ≈ Ret (m, (ρ, (g, dv))).
Proof.
  intros uv P g ρ m CONC.
  pose proof is_concrete_uvalue_to_dvalue uv CONC as (dv & CONV).
  exists dv.
  split; auto.
  now apply interp_mcfg_concretize_or_pick_concrete.
Qed.

Lemma initIRGlobals_rev_data
      (globals : list (string * DSHType))
      (s s' : IRState)
      (data data' : list binary64)
      r
  :
    initIRGlobals_rev data globals s ≡ inr (s', (data', r)) →
    exists n, data' ≡ rotateN n data.
Proof.
  revert s s' data data' r.
  induction globals.
  -
    intros * I.
    invc I.
    exists 0.
    reflexivity.
  -
    intros * I.
    cbn in I.
    repeat break_match; invc I.
    eapply IHglobals in Heqs2.
    destruct Heqs2 as [n1 N1]; subst data'.

    clear - Heqs1.
    destruct a as (a_nm, a_t).
    destruct a_t; cbn in *;
      repeat break_match; invc Heqs1.
    +
      apply int64FromData_data in Heqp; subst.
      rewrite rotateN_add; eauto.
    +
      apply rotate_data in Heqp; subst.
      rewrite rotateN_add; eauto.
    +
      apply constArray_data in Heqp; subst.
      rewrite rotateN_add; eauto.
Qed.

Lemma initFSHGlobals_data
      (globals : list (string * DSHType))
      (m m' : memoryH)
      (data data' : list binary64)
      r
  :
    initFSHGlobals data m globals ≡ inr (m', data', r) →
    exists n, data' ≡ rotateN n data.
Proof.
  revert m m' data data' r.
  induction globals.
  -
    intros * I.
    invc I.
    exists 0.
    reflexivity.
  -
    intros * I.
    cbn in I.
    repeat break_match; invc I.
    destruct p0 as (m1, data1).
    eapply IHglobals in Heqs0.
    destruct Heqs0 as [n1 N1]; subst data'.

    clear - Heqs.
    destruct a as (a_nm, a_t).
    destruct a_t; cbn in *;
      repeat break_match; invc Heqs.
    +
      apply int64FromData_data in Heqp; subst.
      rewrite rotateN_add; eauto.
    +
      apply rotate_data in Heqp; subst.
      rewrite rotateN_add; eauto.
    +
      apply constMemBlock_data in Heqp; subst.
      rewrite rotateN_add; eauto.
Qed.

Lemma initFSHGlobals_initIRGlobals_rev_data
      (globals : list (string * DSHType))
      (s s' : IRState)
      (m m' : memoryH)
      (data data_ir data_fsh : list binary64)
      r_ir r_fsh
  :
    initIRGlobals_rev data globals s ≡ inr (s', (data_ir, r_ir)) →
    initFSHGlobals data m globals ≡ inr (m', data_fsh, r_fsh) →
    data_ir ≡ data_fsh.
Proof.
  revert s s' m m' data data_ir data_fsh r_ir r_fsh.
  induction globals.
  -
    intros * IIR IFSH.
    invc IIR; invc IFSH.
    reflexivity.
  -
    intros * IIR IFSH.
    cbn in IIR; cbn in IFSH.
    repeat break_match; invc IIR; invc IFSH.

    destruct p0 as (m1_fsh, data1_fsh).
    rename l0 into data1_ir.
    dedup_states.

    eapply IHglobals.
    eassumption.
    unfold initIRGlobals_rev in *.
    enough (T : data1_ir ≡ data1_fsh) by (rewrite T; eassumption).
    clear - Heqs3 Heqs0.
    rename Heqs0 into FSH, Heqs3 into IR.
    destruct a as (a_nm, a_t).
    destruct a_t; cbn in *;
      repeat break_match;
      invc IR; invc FSH; auto.
    autounfold with unfold_FCT in *; congruence.
    apply constMemBlock_data in Heqp; subst.
    apply constArray_data in Heqp0; subst.
    reflexivity.
Qed.

Lemma initXYplaceholders_data
      (i o : Int64.int)
      (data data' : list binary64)
      (xid yid : raw_id) 
      (x y : typ)
      (s s' : IRState)
      t
  :
    initXYplaceholders i o data xid x yid y s ≡ inr (s', (data', t)) ->
    data' ≡ rotateN (MInt64asNT.to_nat i + MInt64asNT.to_nat o) data.
Proof.
  intros I.
  unfold initXYplaceholders in *.
  repeat break_match; invc I.
  apply constArray_data in Heqp.
  apply constArray_data in Heqp0.
  subst.
  apply rotateN_add.
Qed.

Ltac simpl_data :=
  repeat match goal with
         | [H : constList _ _ ≡ (?data', _) |- _] =>
           copy_apply constList_data H; subst data'
         | [H : constArray _ _ ≡ (?data', _) |- _] =>
           copy_apply constArray_data H; subst data'
         | [H : constMemBlock _ _ ≡ (?data', _) |- _] =>
           copy_apply constMemBlock_data H; subst data'
         | [H : int64FromData _ ≡ (_, ?data') |- _] =>
           copy_apply int64FromData_data H; subst data'
         | [H : rotate _ _ ≡ (_, ?data') |- _] =>
           copy_apply rotate_data H; subst data'
         | [H : initXYplaceholders _ _ _ _ _ _ _ _ ≡ inr (_, (?data', _)) |- _] =>
           copy_apply initXYplaceholders_data H; subst data'
         end.

Lemma get_logical_block_allocated :
  forall (a : addr) (m : memoryV) (b : logical_block),
    get_logical_block m (fst a) ≡ Some b ->
    allocated a m.
Proof.
  intros * LB.
  unfold allocated, get_logical_block, get_logical_block_mem in *.
  repeat break_let; subst; cbn in *.
  eapply lookup_member; eauto.
Qed.

Lemma dtyp_fits_allocated :
  forall (m : memoryV) (a : addr) (τ : dtyp),
    dtyp_fits m a τ ->
    allocated a m.
Proof.
  intros * AF.
  unfold dtyp_fits in *.
  destruct AF as (? & ? & ? & [LB _]).
  now apply get_logical_block_allocated in LB.
Qed.

Lemma initOneIRGlobal_g_typ
      (a : string * FHCOL.DSHType)
      (t : global typ)
      (data data' : list binary64) 
      (s s' : IRState)
  :
    initOneIRGlobal data a s ≡ inr (s', (data', TLE_Global t)) →
    snd (IR_of_global a) ≡ TYPE_Pointer (g_typ t).
Proof.
  intros.
  destruct a as (a_nm, a_t).
  cbn in H.
  repeat break_match;
    now invc H.
Qed.

Lemma mem_block_of_list_lookup (id : Memory.NM.key) (ml : list binary64) :
  mem_lookup id (mem_block_of_list ml) ≡ nth_error ml id.
Proof.
  pose (fix f l n m := match l with
                       | [] => m
                       | x :: xs => f xs (S n) (mem_add n x m)
                       end)
    as mbl_fix.
  replace (mem_block_of_list ml)
    with (mbl_fix ml 0 mem_empty)
    by reflexivity.

  assert (mbl_fix_preserve :
            forall l n mb,
              (forall i, n <= i -> mem_lookup i mb ≡ None) ->
              forall j, j < n -> mem_lookup j (mbl_fix l n mb) ≡ mem_lookup j mb).
  {
    clear.
    induction l;
      intros * BOUND j JN.
    -
      reflexivity.
    -
      cbn.
      rewrite IHl.
      +
        now rewrite mem_lookup_mem_add_neq by lia.
      +
        intros i IN.
        erewrite <-BOUND, mem_lookup_mem_add_neq.
        reflexivity.
        lia.
        lia.
      +
        lia.
  }

  assert (mbl_fix_inv_update :
            forall l n mb,
              (forall i, n <= i -> mem_lookup i mb ≡ None) ->
              forall j, n <= j -> mem_lookup j (mbl_fix l n mb) ≡ nth_error l (j - n)).
  {
    clear - mbl_fix_preserve.
    induction l;
      intros * BOUND j JN.
    -
      now rewrite BOUND, nth_error_nil.
    -
      cbn.
      destruct (Nat.eq_dec j n) as [|JN'].
      +
        subst; clear JN.
        rewrite mbl_fix_preserve, mem_lookup_mem_add_eq, Nat.sub_diag.
        reflexivity.
        intros i IN.
        rewrite mem_lookup_mem_add_neq by lia.
        apply BOUND.
        lia.
        lia.
      +
        rewrite IHl.
        destruct j; [lia |].
        now rewrite Nat.sub_succ, <-minus_Sn_m by lia.
        intros i IN.
        rewrite mem_lookup_mem_add_neq by lia.
        apply BOUND.
        lia.
        lia.
  }

  rewrite mbl_fix_inv_update.
  now rewrite Nat.sub_0_r.
  reflexivity.
  lia.
Qed.

Lemma constList_length (n : nat) (data data' cl : list binary64) :
  constList n data ≡ (data', cl) ->
  length cl ≡ n.
Proof.
  intros CL.
  dependent induction n.
  - now invc CL.
  -
    cbn in CL.
    repeat break_let; invc CL.
    cbn; f_equal.
    eauto.
Qed.

Lemma constMemBlock_bound
      (n : nat)
      (data data' : list binary64)
      (mb : mem_block)
      (id : nat)
      (v : binary64)
  :
    constMemBlock n data ≡ (data', mb) →
    mem_lookup id mb ≡ Some v →
    id < n.
Proof.
  intros MB V.
  unfold constMemBlock, mem_lookup in *.
  break_let.
  inversion MB; subst l mb; clear MB.
  rename l0 into cl, Heqp into CL.
  rewrite mem_block_of_list_lookup in V.
  apply constList_length in CL; subst.
  eauto using nth_error_in.
Qed.

Lemma int64_unsigned_repr_eq (n : Z) :
  (0 <= n)%Z /\ (n < Int64.modulus)%Z ->
  Int64.unsigned (Int64.repr n) ≡ n.
Proof.
  intros B.
  symmetry.
  apply Int64.eqm_small_eq.
  apply Int64.eqm_unsigned_repr.
  assumption.
  generalize dependent (Int64.repr n); clear; intros n.
  destruct n.
  cbn.
  lia.
Qed.

Lemma flat_map_fold_right {A B : Type} (f : B -> list A) (l : list B) :
  fold_right (fun b acc => f b ++ acc) [] l ≡ flat_map f l.
Proof.
  now induction l.
Qed.

Lemma flat_map_length_mul
      {A B : Type}
      (f : A -> list B)
      (l : list A)
      (n : nat)
  :
    (forall x, length (f x) ≡ n) ->
    length (flat_map f l) ≡ n * (length l).
Proof.
  intros.
  induction l.
  - cbn; lia.
  - cbn.
    rewrite app_length, H, IHl, Nat.mul_succ_r; lia.
Qed.

Lemma flat_map_nth
      {A B : Type}
      (f : A -> list B)
      (l : list A)
      `(BL : forall x, length (f x) ≡ bl)
  :
    forall i k,
      i < bl ->
      nth_error (flat_map f l) (bl * k + i) ≡
      (b <- nth_error l k ;; nth_error (f b) i)%monad.
Proof.
  cbn.
  induction l; intros.
  - now rewrite !nth_error_nil.
  - cbn.
    destruct k.
    + rewrite Nat.mul_0_r.
      now rewrite nth_error_app1 by now rewrite BL.
    +
      cbn.
      rewrite <-IHl by assumption.
      rewrite nth_error_app2 by (rewrite BL; lia).
      rewrite BL.
      f_equal.
      lia.
Qed.

Lemma list_nth_z_nth_error {A : Type} (l : list A) (n : Z) :
  (0 <= n)%Z ->
  Coqlib.list_nth_z l n ≡ nth_error l (Z.to_nat n).
Proof.
  intros.
  generalize dependent n.
  induction l.
  - intros; now rewrite nth_error_nil.
  -
    intros; cbn.
    break_if.
    now subst.
    replace (Z.to_nat n) with (S (Z.to_nat (n - 1))) by lia.
    apply IHl; lia.
Qed.

(* ZX TODO: see [serialize_deserialize]. duplication. *)
Lemma deserialize_serialize_double (v : binary64) :
  deserialize_sbytes (serialize_dvalue (DVALUE_Double v)) DTYPE_Double ≡
  UVALUE_Double v.
Proof.
  rewrite <-deserialize_sbytes_defined_dvalue.
  cbn.
  f_equal.
  remember (Floats.Float.to_bits v) as bv.
  pose proof (unsigned_I64_in_range bv) as B.
  rewrite !Integers.Byte.unsigned_repr_eq.
  unfold Integers.Byte.modulus,
         Integers.Byte.wordsize,
         Integers.Wordsize_8.wordsize.
  replace (two_power_nat 8) with 256%Z by reflexivity.
  remember (Int64.unsigned bv) as ibv.
  match goal with
  | [|- context[Int64.repr ?zv]] => replace zv with ibv
  end.
  -
    subst.
    rewrite Int64.repr_unsigned.
    apply Floats.Float.of_to_bits.
  -
    clear - B.
    rewrite Z.add_0_r.
    unfold Z.modulo.
    repeat break_let.
    repeat match goal with
           | [H : Z.div_eucl _ _ ≡ _ |- _] => apply Z_div_mod' in H; [destruct H | lia]
           end.
    repeat (subst;
            rewrite Z.add_comm, Z.mul_comm, Z_div_plus in * by lia;
            match goal with
            | [H : (?z / 256 + _)%Z ≡ _ |- _] =>
              rewrite Zdiv_small with (a:=z) in * by lia
            end;
            rewrite Z.add_0_l in *).
    lia.
Qed.

Lemma nth_error_list_eq {A : Type} (l1 l2 : list A) :
  (forall n, nth_error l1 n ≡ nth_error l2 n) ->
  l1 ≡ l2.
Proof.
  generalize dependent l2.
  induction l1; intros l2 E;
    destruct l2.
  - reflexivity.
  - now specialize (E 0).
  - now specialize (E 0).
  - f_equal.
    + specialize (E 0).
      cbn in E.
      congruence.
    + apply IHl1.
      intros n; specialize (E (S n)).
      cbn in E.
      assumption.
Qed.

Lemma Zseq_nth (k len : nat) (b : Z) :
  k < len ->
  nth_error (Zseq b len) k ≡ Some (b + Z.of_nat k)%Z.
Proof.
  revert k b.
  induction len; intros * K.
  - inv K.
  - destruct k.
    now rewrite Z.add_0_r.
    cbn [Zseq nth_error].
    rewrite IHlen by lia.
    f_equal.
    lia.
Qed.

Lemma lookup_all_index_elem
      {A B : Type}
      (l : list A)
      (off : Z)
      (mb : IntMap B) 
      (d : B)
      (b : A → list B)
      `(BS : ∀ x : A, Datatypes.length (b x) ≡ bs)
  :
    forall n v, nth_error l n ≡ Some v ->
    lookup_all_index (off + Z.of_nat (n * bs)) (N.of_nat bs)
                     (add_all_index (flat_map b l) off mb) d ≡ b v.
Proof.
  intros * V.

  unfold lookup_all_index.
  rewrite Nnat.Nat2N.id.

  apply nth_error_list_eq; intros k.
  destruct (le_lt_dec bs k) as [K | K].
  1:{
    rewrite !ListUtil.nth_beyond.
    reflexivity.
    now rewrite BS.
    now rewrite map_length, Zseq_length.
  }

  match goal with
  | [_ : _ |- nth_error ?m ?k ≡ _] =>
    pose proof nth_error_succeeds m (n:=k) as KM
  end.
  autospecialize KM; [now rewrite map_length, Zseq_length |].
  destruct KM as [kb KB].
  pose proof nth_error_succeeds (b v) (n:=k) as KV.
  autospecialize KV; [now rewrite BS |].
  destruct KV as [kv KV].

  erewrite map_nth_error by now rewrite Zseq_nth by assumption.

  rewrite KV.
  f_equal.

  erewrite lookup_add_all_index_in.
  -
    reflexivity.
  -
    split; [lia |].
    apply nth_error_in in V.
    rewrite Zlength_correct.
    rewrite flat_map_length_mul with (n0:=bs) by assumption.
    nia.
  -
    rewrite list_nth_z_nth_error by lia.
    replace (Z.to_nat (off + Z.of_nat (n * bs) + Z.of_nat k - off))
      with (bs * n + k) by lia.
    rewrite flat_map_nth; try assumption; try lia.
    cbn.
    now rewrite V.
Qed.

Lemma deserialize_vector
      (ml : list binary64)
      (off : Z)
      (bytes : Mem.mem_block)
  :
    forall id v,
      nth_error ml id ≡ Some v ->
      deserialize_sbytes
        (lookup_all_index (off + Z.of_nat id * 8) 8
           (add_all_index
              (serialize_dvalue (DVALUE_Vector (map DVALUE_Double ml))) off bytes) SUndef)
        DTYPE_Double ≡ UVALUE_Double v.
Proof.
  intros id v V.
  cbn [serialize_dvalue].
  rewrite flat_map_fold_right.

  replace (off + Z.of_nat id * 8)%Z with (off + Z.of_nat (id * 8))%Z by lia.
  rewrite flat_map_map.
  erewrite lookup_all_index_elem.

  apply deserialize_serialize_double.
  reflexivity.
  assumption.
Qed.

Lemma constList_constMemBlock
      (n : nat)
      (l d d' d'' : list binary64)
      (mb : mem_block)
  :
    constList n d ≡ (d', l) →
    constMemBlock n d ≡ (d'', mb) ->
    ∀ i, nth_error l i ≡ mem_lookup i mb.
Proof.
  intros CL CMB i.
  unfold constMemBlock in *.
  rewrite CL in *.
  invc CMB.
  now rewrite mem_block_of_list_lookup.
Qed.

Lemma alist_cons_find_some
      {K V : Type}
      {RD : RelDec eq}
      {RC : RelDec_Correct RD}
      (k k' : K)
      (v v' : V)
      (al : alist K V)
  :
    ((k, v) :: al) @ k' ≡ Some v' ->
    (k' ≡ k /\ v' ≡ v) \/ (k' ≢ k /\ al @ k' ≡ Some v').
Proof.
  intros A.
  destruct (rel_dec k k') eqn:KR.
  - left.
    rewrite rel_dec_correct in KR; subst k'.
    rewrite alist_find_cons_eq in A by reflexivity.
    now invc A.
  - right.
    rewrite <-neg_rel_dec_correct in KR.
    rewrite alist_find_cons_neq in A by congruence.
    auto.
Qed.

Lemma alist_find_in_length_1
      {K V : Type}
      {RD : RelDec eq}
      {RC : RelDec_Correct RD}
      (k k' : K)
      (v v' : V)
  :
    [(k, v)] @ k' ≡ Some v' ->
    k' ≡ k /\ v' ≡ v.
Proof.
  intros A.
  destruct (rel_dec k k') eqn:KR.
  - rewrite rel_dec_correct in KR; subst k'.
    rewrite alist_find_cons_eq in A by reflexivity.
    now invc A.
  - rewrite <-neg_rel_dec_correct in KR.
    rewrite alist_find_cons_neq in A by congruence.
    now invc A.
Qed.

Lemma fold_left_map
      {A B C : Type}
      (l : list C)
      (d : A)
      (g : C -> B)
      (f : A -> B -> A)
  :
    fold_left f (map g l) d ≡ fold_left (fun a c => f a (g c)) l d.
Proof.
  dependent induction l.
  -
    reflexivity.
  -
    cbn.
    rewrite IHl.
    reflexivity.
Qed.

Lemma maximumBy_upper_bound (l : list Z) (def : Z) (M : Z) :
  (def <= M)%Z ->
  (forall n, In n l -> n <= M)%Z ->
  (maximumBy Z.leb def l <= M)%Z.
Proof.
  intros DM MAX.
  generalize dependent def.
  induction l.
  -
    intros.
    cbn.
    assumption.
  -
    intros def DM.
    autospecialize IHl.
    {
      intros n IN.
      eapply MAX.
      now apply in_cons.
    }
    cbn.
    specialize (IHl (if def <=? a then a else def)%Z).
    autospecialize IHl.
    {
      break_if.
      -
        apply MAX.
        constructor 1.
        reflexivity.
      -
        apply Z.leb_gt in Heqb.
        assumption.
    }
    rewrite IHl.
    reflexivity.
Qed.

Lemma NM_NS_In_inv {elt:Type} (k:IM.key) (m:IM.t elt):
  IS.In k (ISP.of_list (map fst (IM.elements  m))) ->
  IM.In k m.
Proof.
  pose proof (IM.elements_3w m) as U.
  intros H.
  rewrite <- IP.of_list_3 with (s:=m).
  unfold IP.of_list, IP.to_list.
  generalize dependent (IM.elements m). intros l U H.
  induction l.
  -
    simpl in H.
    apply ISP.FM.empty_iff in H.
    tauto.
  -
    destruct a as [k' v].
    simpl in *.
    destruct (Z.eq_decidable k k') as [K|NK].
    +
      unfold IP.uncurry.
      cbn.
      apply IP.F.add_in_iff.
      auto.
    +
      apply ISP.FM.add_neq_iff in H; auto.
      unfold IP.uncurry.
      cbn.
      apply IP.F.add_in_iff.
      right.
      apply IHl.
      *
        inversion U.
        auto.
      *
        assumption.
Qed.

Lemma IM_key_in_elements_inv :
  forall k elt m,
    In k (map fst (IM.elements (elt:=elt) m)) ->
    IM.In (elt:=elt) k m.
Proof.
  intros k elt m H.
  apply NM_NS_In_inv.
  pose proof (IM.elements_3w m) as U.
  generalize dependent (IM.elements m). intros l U H.
  induction l.
  -
    cbn in U.
    tauto.
  -
    destruct a as [k' v].
    simpl in *.
    destruct (Z.eq_decidable k k') as [K|NK].
    +
      apply IS.add_1.
      auto.
    +
      (* k!=k' *)
      destruct U as [C | U];
        try congruence.
      apply IS.add_2.
      apply IHl.
      *
        assumption.
      *
        rewrite <-app_nil_l in H.
        apply SetoidList.NoDupA_split in H.
        rewrite app_nil_l in H.
        assumption.
Qed.

Lemma next_logical_key_add_logical_block
      (m : memoryV)
      (id : Z)
      (b : logical_block)
  :
    (next_logical_key m <=
     next_logical_key (add_logical_block id b m))%Z.
Proof.
  unfold add_logical_block in *.
  break_let; subst.
  unfold next_logical_key, next_logical_key_mem.
  cbn [fst snd].
  rename m0 into m; clear.

  unfold add_logical_block_mem.
  break_match; subst.
  cbn [fst snd]; clear.
  unfold logical_next_key, add.
  enough 
  (maximumBy Z.leb (-1) (map fst (IM.elements (elt:=logical_block) l)) <=
     maximumBy Z.leb (-1)
               (map fst (IM.elements (elt:=logical_block) (IM.add id b l))))%Z
    by lia.
  apply maximumBy_upper_bound.
  apply Zle_bool_imp_le; apply maximumBy_Z_def.
  intros.
  enough (T : In n (map fst (IM.elements (elt:=logical_block) (IM.add id b l)))).
  apply maximumBy_Z_correct with (def:=(-1)%Z) in T.
  apply Zle_bool_imp_le in T.
  assumption.
  eapply IM_key_in_elements.
  apply IP.F.add_in_iff.
  right.
  eapply IM_key_in_elements_inv.
  assumption.
Qed.


Lemma next_logical_key_add_to_frame_inc (m : memoryV) (b : logical_block) :
    (next_logical_key m <
     next_logical_key
       (add_to_frame (add_logical_block (next_logical_key m) b m)
                     (next_logical_key m)))%Z.
Proof.
  unfold add_to_frame.
  repeat break_match; subst.
  -
    unfold add_logical_block in *.
    break_let; invc Heqm0.
    unfold next_logical_key, next_logical_key_mem.
    cbn [fst snd].
    rename m1 into m; clear.
    unfold add_logical_block_mem.
    break_match; subst.
    cbn [fst snd]; clear.
    unfold logical_next_key, add.
    generalize (map fst (IM.elements (elt:=logical_block) l));
      intros lk; clear.
    enough 
      (maximumBy Z.leb (-1) lk <
       maximumBy Z.leb (-1)
                 (map fst
                      (IM.elements (elt:=logical_block)
                                   (IM.add (1 + maximumBy Z.leb (-1) lk) b l))))%Z
      by lia.
    assert (IM.In
              (1 + maximumBy Z.leb (-1) lk)%Z
              (IM.add (1 + maximumBy Z.leb (-1) lk)%Z b l))
      by (apply IP.F.add_in_iff; tauto).
    apply IM_key_in_elements in H.
    eapply maximumBy_Z_correct with (def:=(-1)%Z)in H.
    apply Zle_bool_imp_le in H.
    lia.
  - 
    unfold add_logical_block in *.
    break_let; invc Heqm0.
    unfold next_logical_key, next_logical_key_mem.
    cbn [fst snd].
    rename m1 into m; clear.
    unfold add_logical_block_mem.
    break_match; subst.
    cbn [fst snd]; clear.
    unfold logical_next_key, add.
    generalize (map fst (IM.elements (elt:=logical_block) l));
      intros lk; clear.
    enough 
      (maximumBy Z.leb (-1) lk <
       maximumBy Z.leb (-1)
                 (map fst
                      (IM.elements (elt:=logical_block)
                                   (IM.add (1 + maximumBy Z.leb (-1) lk) b l))))%Z
      by lia.
    assert (IM.In
              (1 + maximumBy Z.leb (-1) lk)%Z
              (IM.add (1 + maximumBy Z.leb (-1) lk)%Z b l))
      by (apply IP.F.add_in_iff; tauto).
    apply IM_key_in_elements in H.
    eapply maximumBy_Z_correct with (def:=(-1)%Z)in H.
    apply Zle_bool_imp_le in H.
    lia.
Qed.

Lemma allocate_next_logical_key_inc (m m' : memoryV) (t : dtyp) (a : addr) :
  allocate m t ≡ inr (m', a) ->
  (next_logical_key m < next_logical_key m')%Z.
Proof.
  intros A.
  apply allocate_inv in A.
  destruct A as [NV [A K]].
  subst.
  apply next_logical_key_add_to_frame_inc.
Qed.


Lemma allocate_next_logical_key (m m' : memoryV) (t : dtyp) (a : addr) :
    allocate m t ≡ inr (m', a) ->
    fst a ≡ next_logical_key m.
Proof.
  intros.
  apply allocate_inv in H.
  destruct H as [_ [_ K]].
  now rewrite K.
Qed.

Lemma initOneIRGlobal_non_void
      (data data' : list binary64)
      (s s' : IRState)
      (g : string * FHCOL.DSHType) 
      (tg : global typ)
  :
    initOneIRGlobal data g s ≡ inr (s', (data', TLE_Global tg)) ->
    g_typ tg ≢ TYPE_Void.
Proof.
  intros.
  unfold initOneIRGlobal in H.
  repeat break_match; invc H.
  all: discriminate.
Qed.

Definition genv_ptr_uniq (g : global_env) :=
  ∀ (id id' : raw_id) (ptr ptr' : addr),
    in_global_addr g id ptr →
    in_global_addr g id' ptr' →
    fst ptr ≡ fst ptr' ->
    id ≡ id'.

Definition genv_mem_bounded (g : global_env) (m : memoryV) :=
  forall id a,
    g @ id ≡ Some (DVALUE_Addr a) ->
    (fst a < next_logical_key m)%Z.

Definition genv_mem_wf (g : global_env) (m : memoryV) :=
  genv_ptr_uniq g /\ genv_mem_bounded g m.

Lemma genv_mem_bounded_allocate
      (g : global_env)
      (m m' : memoryV)
      (t : dtyp)
      (a : addr)
      (id : raw_id)
  :
    genv_mem_bounded g m ->
    allocate m t ≡ inr (m', a) ->
    genv_mem_bounded (alist_add id (DVALUE_Addr a) g) m'.
Proof.
  intros * GMB A.
  unfold genv_mem_bounded in *.
  copy_apply allocate_next_logical_key_inc A.
  apply allocate_next_logical_key in A.
  intros id' a' AA.
  apply alist_add_find_some in AA.
  destruct AA as [[ID AA] | [ID AA]].
  -
    invc AA.
    lia.
  -
    enough (fst a' < next_logical_key m)%Z by lia.
    eapply GMB.
    eassumption.
Qed.

Lemma genv_mem_wf_allocate
      (g : global_env)
      (m m' : memoryV)
      (t : dtyp)
      (a : addr)
      (id : raw_id)
  :
    genv_mem_wf g m ->
    allocate m t ≡ inr (m', a) ->
    genv_mem_wf (alist_add id (DVALUE_Addr a) g) m'.
Proof.
  intros [GUNIQ GMB] A.
  split.
  -
    unfold genv_ptr_uniq.
    unfold in_global_addr.
    intros id1 id2 ptr1 ptr2 A1 A2 PTREQ.
    apply alist_cons_find_some in A1;
      apply alist_cons_find_some in A2.
    destruct A1 as [[ID1 PTR1] | [A1 PTR1]],
             A2 as [[ID2 PTR2] | [A2 PTR2]].
    *
      congruence.
    *
      exfalso.
      subst.
      rewrite remove_neq_alist in PTR2;
        try typeclasses eauto;
        try congruence.
      invc PTR1.
      eapply GMB in PTR2.
      copy_apply allocate_next_logical_key_inc A.
      apply allocate_next_logical_key in A.
      lia.
    *
      exfalso.
      subst.
      rewrite remove_neq_alist in PTR1;
        try typeclasses eauto;
        try congruence.
      invc PTR2.
      eapply GMB in PTR1.
      copy_apply allocate_next_logical_key_inc A.
      apply allocate_next_logical_key in A.
      lia.
    *
      rewrite remove_neq_alist in PTR1, PTR2;
        try typeclasses eauto;
        try congruence.
      eapply GUNIQ; eassumption.
  -
    eapply genv_mem_bounded_allocate.
    eassumption.
    eassumption.
Qed.

Lemma genv_mem_wf_add_logical_block
      (m : memoryV)
      (g : global_env)
      (id : Z)
      (b : logical_block)
  :
    genv_mem_wf g m →
    genv_mem_wf g (add_logical_block id b m).
Proof.
  intros.
  unfold genv_mem_wf in *.
  intuition.
  clear - H1; rename H1 into GMB.
  unfold genv_mem_bounded in *.
  intros id' a A.
  apply GMB in A.
  enough (next_logical_key m <=
          next_logical_key (add_logical_block id b m))%Z
    by lia.
  apply next_logical_key_add_logical_block.
Qed.

Lemma dtyp_fits_add_logical_block_key_neq
      (m : memoryV)
      (a : Z * Z)
      (τ : dtyp)
      (b : logical_block)
  :
    dtyp_fits m a τ ->
    forall ptr, ptr ≢ fst a ->
    dtyp_fits (add_logical_block ptr b m) a τ.
Proof.
  intros F ptr NEQ.
  unfold dtyp_fits in *.
  rewrite get_logical_block_of_add_logical_block_neq
    by assumption.
  eassumption.
Qed.

Lemma Int64_to_nat_modulus (i : Int64.int) (n : nat) :
  n < MInt64asNT.to_nat i →
  (Z.of_nat n < Int64.modulus)%Z.
Proof.
  intros N.
  destruct i.
  destruct intval.
  all: cbn in N.
  all: lia.
Qed.

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
      (interp_mcfg3 (build_global_environment (convert_types (mcfg_of_tle pll)))
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
  setoid_rewrite interp3_bind.

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
                (ID_Global (Anon 1%Z),
                 TYPE_Pointer (TYPE_Array (Z.to_N (Int64.intval o)) TYPE_Double));
                (ID_Global (Anon 0%Z),
                 TYPE_Pointer (TYPE_Array (Z.to_N (Int64.intval i)) TYPE_Double))]
      as v.
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
        unfold addVar in *; cbn in Heqs3.
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
                (ID_Global (Anon 1%Z),
                 TYPE_Pointer (TYPE_Array (Z.to_N (Int64.intval o)) TYPE_Double));
                (ID_Global (Anon 0%Z),
                 TYPE_Pointer (TYPE_Array (Z.to_N (Int64.intval i)) TYPE_Double))]
      as v.
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
        unfold addVar in *; cbn in Heqs3.
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
                (ID_Global (Anon 1%Z),
                 TYPE_Pointer (TYPE_Array (Z.to_N (Int64.intval o)) TYPE_Double));
                (ID_Global (Anon 0%Z),
                 TYPE_Pointer (TYPE_Array (Z.to_N (Int64.intval i)) TYPE_Double))]
      as v.
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
        unfold addVar in *; cbn in Heqs3.
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

  apply eutt_clo_bind
    with (UU := fun _ '(memV,((l,sl),(g,_))) =>
                  fun_declarations_invariant name (memV,(l,g)) /\
                  genv_mem_wf g memV
                  ).
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

    rewrite interp3_bind.

    pose_interp3_alloca m' a' A AE.
    1:{
      unfold non_void.
      intros C. inversion C.
    }
    rewrite AE.
    cbn. repeat setoid_rewrite Eq.bind_ret_l.
    rewrite interp3_bind.
    rewrite interp3_GW.
    cbn; rewrite !ITree.Eq.Eq.bind_ret_l.
    autorewrite with itree.
    cbn.
    unfold alist_add.
    cbn.

    rewrite interp3_bind.

    pose_interp3_alloca m'' a'' A' AE'.
    1:{
      unfold non_void.
      intros C. inversion C.
    }
    rewrite AE'.
    cbn; rewrite !ITree.Eq.Eq.bind_ret_l.
    rewrite interp3_bind.
    rewrite interp3_GW.
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

    rewrite interp3_ret.
    apply eutt_Ret.
    subst R.
    unfold fun_declarations_invariant_mcfg, fun_declarations_invariant.
    unfold global_named_ptr_exists.
    split.
    -
      split.
      +
        exists a''.
        reflexivity.
      +
        exists a'.
        rewrite alist_find_cons_neq.
        rewrite alist_find_cons_eq.
        reflexivity.
        reflexivity.
        crush.
    -
      split.
      +
        clear - A A'.
        copy_apply allocate_next_logical_key_inc A; rename H into AK'.
        copy_apply allocate_next_logical_key_inc A'; rename H into AK''.
        apply allocate_next_logical_key in A.
        apply allocate_next_logical_key in A'.
        unfold genv_ptr_uniq.
        unfold in_global_addr.
        intros.
        apply alist_cons_find_some in H;
          apply alist_cons_find_some in H0.
        destruct H as [[MAIN PTR] | [NMAIN L]],
                 H0 as [[MAIN' PTR'] | [NMAIN' L']].
        *
          congruence.
        *
          exfalso.
          apply alist_find_in_length_1 in L'.
          destruct L' as [NAME' PTR'].
          invc PTR; invc PTR'.
          lia.
        *
          exfalso.
          apply alist_find_in_length_1 in L.
          destruct L as [NAME PTR].
          invc PTR; invc PTR'.
          lia.
        *
          apply alist_find_in_length_1 in L.
          apply alist_find_in_length_1 in L'.
          destruct L as [NAME PTR].
          destruct L' as [NAME' PTR'].
          congruence.
      +
        clear - A A'.
        unfold genv_mem_bounded.
        intros.
        unfold allocate in *.
        invc A.
        invc A'.
        cbn in *.
        repeat break_if; try inv H; cbn; lia.
  }

  intros.
  clear u1.

  eutt_hide_rel REL.
  
  fold_map_monad_.
  repeat unfold tfmap, TFunctor_list'.

  (* splitting the lists in (1) and (3) *)
  (* just [rewrite map_app] doesn't work for some reason *)
  replace (map (TFunctor_global typ dtyp (typ_to_dtyp [ ]))
               (flat_map (globals_of typ) gdecls ++ flat_map (globals_of typ) t))
    with (map (TFunctor_global typ dtyp (typ_to_dtyp [ ])) (flat_map (globals_of typ) gdecls) ++
              map (TFunctor_global typ dtyp (typ_to_dtyp [ ])) (flat_map (globals_of typ) t))
    by (rewrite map_app; reflexivity).

  (* splitting (1) and (3) into binds *)
  repeat break_match_goal.
  setoid_rewrite map_monad_app_.

  fold_initialization.
  simpl.

  remember (map (TFunctor_global typ dtyp (typ_to_dtyp [ ]))
                (flat_map (globals_of typ) t))
    as XY.
  remember (map (TFunctor_global typ dtyp (typ_to_dtyp [ ]))
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
  rewrite interp3_bind.

  subst LHS REL.
  destruct p0 as [le0 stack0].
  destruct x as [x_id x_typ].

  remember (Datatypes.length globals) as lg.

  remember
    {|
      block_count := block_count;
      local_count := local_count;
      void_count := void_count;
      Γ := Γ_globals |}
    as zx_state.
  remember e
    as zx_σ.

  pose (fun '(memH, t0) '(memV, (l, t1, (g, t2))) =>
          post_alloc_invariant_mcfg i o
            globals zx_σ zx_state (memH, t0) (memV, (l, t1, (g, t2))) /\
          fun_declarations_invariant_mcfg name (memV, (l, t1, (g, t2))) /\
          genv_mem_wf g memV
       )
    as post_alloc_invariant_mcfg'.

  (* split the goal:
     1) allocate
     2) initialize
   *)
  apply eutt_clo_bind with (UU:=post_alloc_invariant_mcfg').
  - (* allocate (globals ++ yx) *)
    assert (T : Ret (memory_set (memory_set mg (S lg) mo) lg mi, ())
                ≈
                ITree.bind (E:=E_mcfg)
                            (ret (mg, ()))
                            (fun mg' => ret (memory_set
                                            (memory_set (fst mg') (S lg) mo)
                                            lg mi, ())))
      by (cbn; now rewrite Eq.bind_ret_l).
    rewrite T; clear T.

    rewrite interp3_bind.
    cbn.

    pose (fun globals => (fun _ '(memV, (l, _, (g, _))) =>
                         allocated_globals memV g globals l zx_σ zx_state)
                      : Rel_mcfg_T () ())
      as allocated_globals_mcfg.
    
    pose (fun globals =>
                (fun _ '(memV, (l, _, (g, _))) =>
                   allocated_globals memV g globals l zx_σ zx_state /\
                   fun_declarations_invariant name (memV, (l, g)) /\
                   genv_mem_wf g memV
                ) : Rel_mcfg_T () ())
      as alloc_glob_decl_inv_mcfg.

    (* split the goal:
       1) allocate globals
       2) allocate yx
     *)
    apply eutt_clo_bind
      with (UU:=alloc_glob_decl_inv_mcfg globals).
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
            alloc_glob_decl_inv_mcfg pre (mg, ())
                                      (m, (le0, stack0, (g, ()))) ->
            eutt (alloc_glob_decl_inv_mcfg  (pre ++ post))
                 (Ret (mg, ()))
                    (interp_mcfg
                       (map_monad_ allocate_global
                                   (map (TFunctor_global typ dtyp (typ_to_dtyp []))
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
          split; [| tauto].
          split.
          -
            intros.
            cbn in jc.
            lia.
          -
            unfold no_llvm_ptr_aliasing.
            intros.
            rewrite nth_error_nil in *.
            discriminate.
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
        rewrite interp3_bind.
        rewrite interp3_ret.
        rewrite Eq.bind_ret_l.
        rewrite interp3_ret.
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
        rewrite interp3_bind.

        eutt_hide_left LHS.
        assert (FB : (LHS ≈ LHS ;; LHS)%monad); [| rewrite FB; clear FB; subst LHS].
        {
          subst LHS.
          clear.
          cbn.
          rewrite Eq.bind_ret_l.
          reflexivity.
        }

        apply eutt_clo_bind with (UU:=alloc_glob_decl_inv_mcfg (pre ++ [a])).
        -- (* allocate "new global" *)
          repeat rewrite interp3_bind.
          (* Alloca ng *)
          pose_interp3_alloca m'' a'' A' AE'.
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
          rewrite interp3_GW.

          apply eutt_Ret.
          unfold alloc_glob_decl_inv_mcfg.
          split.

          ++
            unfold allocated_globals.
            split.
            2:{
              pose IPRE as E_PRE_LEN; apply init_with_data_len in E_PRE_LEN.
              rename p1 into ne'.
              subst.

              replace (firstn (Datatypes.length (pre ++ [a])) (e_pre ++ ne' :: e_post'))
                with (e_pre ++ [ne'])
                in *.
              2:{
                rewrite list_cons_app with (l4:=e_post').
                rewrite app_assoc.
                rewrite firstn_app.
                replace (length (pre ++ [a]) - length (e_pre ++ [ne']))
                  with 0 in *
                  by (rewrite !app_length; cbn; lia).
                rewrite firstn_O, app_nil_r.
                rewrite firstn_all2 by (rewrite !app_length; cbn; lia).
                reflexivity.
              }

              copy_apply genIR_Γ IR.
              dedup_states.
              cbn [Γ append_to_Γ] in *.
              apply list_app_eqlen_eq_r in H.
              2: {
                cbn.
                subst.
                clear - LX.
                unfold initXYplaceholders in LX.
                cbn in LX.
                repeat break_match; inv LX.
                reflexivity.
              }
              destruct H as [ΓG XY].
              subst Γ_globals.
              invc XY.

              unfold no_llvm_ptr_aliasing.
              cbn.
              intros.

              copy_apply ListUtil.nth_some H;
                rename H7 into N1L; rewrite app_length in N1L; cbn in N1L.
              copy_apply ListUtil.nth_some H0;
                rename H7 into N2L; rewrite app_length in N2L; cbn in N2L.

              rewrite list_cons_app in H1, H2.
              rewrite app_assoc in H1, H2.
              rewrite map_app in H1, H2.
              (* rewrite <-!app_assoc in H1, H2. *)
              rewrite app_nth_error1 in H1, H2
                by (rewrite map_app, app_length, !map_length; cbn; lia).

              apply nth_map_inv in H1; apply nth_map_inv in H2.
              destruct H1 as [(e1_nm, e1_t) [E1 E1']],
                       H2 as [(e2_nm, e2_t) [E2 E2']].
              cbn in E1', E2'; inv E1'; invc E2'.
              cbn in H5, H6.
              destruct (Nat.eq_dec n1 (length pre)) as [N1|N1],
                       (Nat.eq_dec n2 (length pre)) as [N2|N2].
              +++ (* A, A *)
                exfalso; subst n1 n2.
                replace (length pre) with (0 + length pre) in E1, E2 by lia.
                rewrite ListNth.nth_error_length in E1, E2.
                cbn in E1, E2.
                invc E1; invc E2.
                now contradict H4.
              +++ (* A, I *)
                subst n1.
                assert (n2 < length pre) by lia; clear N1L N2L N2.
                replace (length pre) with (0 + length pre) in E1, H by lia.
                rewrite E_PRE_LEN in H.
                rewrite ListNth.nth_error_length in E1, H.
                cbn in E1, H.
                destruct a as (a_nm, a_t),
                         ne' as (ne_nm, ne_t).
                inversion H; subst v1 b0; clear H.
                inversion E1; subst e1_nm e1_t; clear E1.
                
                rename n2 into n.
                rewrite app_nth_error1 in * by lia.

                intros P.
                do 2 f_equal.
                destruct ptrv1 as (x, y1), ptrv2 as (x', y2);
                  cbn in P; subst x'.

                move Heqs2 at bottom; rename Heqs2 into A.
                move Heqs0 at bottom; rename Heqs0 into TG2.
                remember 
                  {|
                    block_count := Compiler.block_count s0;
                    local_count := Compiler.local_count s0;
                    void_count := Compiler.void_count s0;
                    Γ := (ID_Local (Name "Y"),
                          TYPE_Pointer (TYPE_Array (Z.to_N (Int64.intval o)) TYPE_Double))
                           :: (ID_Local (Name "X"),
                              TYPE_Pointer (TYPE_Array (Z.to_N (Int64.intval i)) TYPE_Double))
                           :: Γ s0 |}
                  as s_yx.

                copy_apply initOneIRGlobal_ident TG2.
                rewrite H in *.

                rewrite alist_find_add_eq in H5.
                destruct a'' as (ax, ay).
                inversion H5; subst x y1; clear H5.

                assert (NM_NEQ : a_nm ≢ e2_nm) by congruence; clear H4.
                rewrite alist_find_neq in H6 by congruence.

                move INV at bottom.
                unfold alloc_glob_decl_inv_mcfg, allocated_globals_mcfg,
                  allocated_globals in INV.
                destruct INV as [[APRE _] _].

                specialize (APRE n H1).
                eapply nth_error_ith in E2.
                rewrite E2 in APRE.
                destruct APRE as [(ax', y2') [AA IGA]].
                apply dtyp_fits_allocated in AA.

                unfold in_global_addr in IGA.
                cbn [fst] in *.
                rewrite IGA in H6.
                inversion H6; subst ax' y2'; clear H6.
                clear - A' AA.
                eapply freshly_allocated_different_blocks in A'; [| eassumption].
                contradiction.
              +++ (* I, A *)
                subst n2.
                assert (n1 < length pre) by lia; clear N1L N2L N1.
                replace (length pre) with (0 + length pre) in E2, H0 by lia.
                rewrite E_PRE_LEN in H0.
                rewrite ListNth.nth_error_length in E2, H0.
                cbn in E2, H0.
                destruct a as (a_nm, a_t),
                         ne' as (ne_nm, ne_t).
                inversion H0; subst v2 b'; clear H0.
                inversion E2; subst e2_nm e2_t; clear E2.
                
                rename n1 into n.
                rewrite app_nth_error1 in * by lia.

                intros P.
                do 2 f_equal.
                destruct ptrv1 as (x, y1), ptrv2 as (x', y2);
                  cbn in P; subst x'.

                move Heqs2 at bottom; rename Heqs2 into A.
                move Heqs0 at bottom; rename Heqs0 into TG2.
                remember 
                  {|
                    block_count := Compiler.block_count s0;
                    local_count := Compiler.local_count s0;
                    void_count := Compiler.void_count s0;
                    Γ := (ID_Local (Name "Y"),
                          TYPE_Pointer (TYPE_Array (Z.to_N (Int64.intval o)) TYPE_Double))
                           :: (ID_Local (Name "X"),
                              TYPE_Pointer (TYPE_Array (Z.to_N (Int64.intval i)) TYPE_Double))
                           :: Γ s0 |}
                  as s_yx.

                copy_apply initOneIRGlobal_ident TG2.
                rewrite H0 in *.

                rewrite alist_find_add_eq in H6.
                destruct a'' as (ax, ay).
                inversion H6; subst x y2; clear H6.

                assert (NM_NEQ : a_nm ≢ e1_nm) by congruence; clear H4.
                rewrite alist_find_neq in H5 by congruence.

                move INV at bottom.
                unfold alloc_glob_decl_inv_mcfg, allocated_globals_mcfg,
                  allocated_globals in INV.
                destruct INV as [[APRE _] _].

                specialize (APRE n H1).
                eapply nth_error_ith in E1.
                rewrite E1 in APRE.
                destruct APRE as [(ax', y1') [AA IGA]].
                apply dtyp_fits_allocated in AA.

                unfold in_global_addr in IGA.
                cbn [fst] in *.
                rewrite IGA in H5.
                inversion H5; subst ax' y1'; clear H5.
                clear - A' AA.
                eapply freshly_allocated_different_blocks in A'; [| eassumption].
                contradiction.
              +++ (* I, I *)
                assert (n1 < length pre) by lia.
                assert (n2 < length pre) by lia.
                clear N1L N2L N1 N2.
                rewrite app_nth_error1 in * by lia.

                rewrite alist_find_neq in H5, H6.
                2: {
                  move LG at bottom.
                  apply initIRGlobals_names_unique in LG.
                  rewrite list_cons_app, app_assoc in LG.
                  apply list_uniq_app in LG.
                  destruct LG as [AUQ _].
                  unfold list_uniq in AUQ.

                  destruct a as (a_nm, a_t).

                  move Heqs0 at bottom.
                  eapply initOneIRGlobal_ident in Heqs0.
                  rewrite Heqs0 in *; clear Heqs0.
                  intros C.
                  inversion C; subst e2_nm; clear C.

                  specialize AUQ with (x:=length pre) (a:=(a_nm, a_t)).
                  specialize AUQ with (y:=n2) (b:=(a_nm, e2_t)).
                  full_autospecialize AUQ.
                  replace (length pre) with (0 + length pre) by lia.
                  now rewrite ListNth.nth_error_length.
                  now rewrite app_nth_error1 by lia.
                  reflexivity.
                  now rewrite ListUtil.nth_beyond in E2 by lia.
                }
                2: {
                  move LG at bottom.
                  apply initIRGlobals_names_unique in LG.
                  rewrite list_cons_app, app_assoc in LG.
                  apply list_uniq_app in LG.
                  destruct LG as [AUQ _].
                  unfold list_uniq in AUQ.

                  destruct a as (a_nm, a_t).

                  move Heqs0 at bottom.
                  eapply initOneIRGlobal_ident in Heqs0.
                  rewrite Heqs0 in *; clear Heqs0.
                  intros C.
                  inversion C; subst e1_nm; clear C.

                  specialize AUQ with (x:=length pre) (a:=(a_nm, a_t)).
                  specialize AUQ with (y:=n1) (b:=(a_nm, e1_t)).
                  full_autospecialize AUQ.
                  replace (length pre) with (0 + length pre) by lia.
                  now rewrite ListNth.nth_error_length.
                  now rewrite app_nth_error1 by lia.
                  reflexivity.
                  now rewrite ListUtil.nth_beyond in E1 by lia.
                }

                move INV at bottom.
                unfold allocated_globals_mcfg, allocated_globals in INV.
                destruct INV as [[_ NA] _].

                replace (firstn (Datatypes.length pre) (e_pre ++ ne' :: e_post'))
                  with (e_pre)
                  in *.
                2:{
                  rewrite list_cons_app with (l4:=e_post').
                  rewrite firstn_app.
                  replace (length pre - length e_pre)
                    with 0 in *
                    by lia.
                  rewrite firstn_O, app_nil_r.
                  rewrite firstn_all2 by lia.
                  reflexivity.
                }

                eapply NA.
                - eapply H.
                - eapply H0.
                -
                  cbn.
                  rewrite map_app.
                  rewrite app_nth_error1
                    by (rewrite map_length; lia).
                  apply map_nth_error with (f:=IR_of_global) in E1.
                  cbn in E1; eassumption.
                -
                  cbn.
                  rewrite map_app.
                  rewrite app_nth_error1
                    by (rewrite map_length; lia).
                  apply map_nth_error with (f:=IR_of_global) in E2.
                  cbn in E2; eassumption.
                - assumption.
                - cbn; assumption.
                - cbn; assumption.
            }

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
                Unshelve.
                rewrite app_length; cbn; lia.
                cbn; lia.
              }
              
              exists a''.
              split.
              -
                destruct a as (a_nm, a_t).
                simpl in *.
                repeat break_match_hyp; invc Heqs0.
                all: simpl in *.
                all: unfold dtyp_fits.
                all: copy_apply allocate_allocated A'.
                all: apply allocated_get_logical_block in H.
                all: destruct H as [(sz, bytes, cid) B].
                all: do 3 eexists; split; [eassumption |].
                all: typ_to_dtyp_simplify.
                all: unfold allocate in A'; invc A'.
                all: cbn.
                all: rewrite get_logical_block_add_to_frame in B.
                all: rewrite get_logical_block_of_add_logical_block in B.
                all: unfold make_empty_logical_block in *.
                all: invc B.
                all: reflexivity.
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

              assert (UGH : Name (fst (ListUtil.ith (l:=pre) (i:=j) jc')) ≢ g_ident tg2).
              {
                clear - LG Heqs0.
                destruct a as (a_nm, a_t).
                apply initIRGlobals_names_unique in LG.
                apply initOneIRGlobal_ident in Heqs0.
                rewrite Heqs0 in *; clear Heqs0 tg2.
                intros C.
                unfold list_uniq in LG.
                remember (ListUtil.ith (l:=pre) (i:=j) jc') as pj.
                symmetry in Heqpj; apply nth_error_ith in Heqpj.
                invc C.
                specialize (LG (length pre) j (fst pj, a_t) pj).
                full_autospecialize LG.
                {
                  replace (length pre) with (0 + length pre) by reflexivity.
                  rewrite ListNth.nth_error_length.
                  reflexivity.
                }
                {
                  now erewrite ListNth.nth_error_weaken.
                }
                {
                  reflexivity.
                }
                lia.
              }

              unfold alloc_glob_decl_inv_mcfg, allocated_globals_mcfg,
                allocated_globals in *.
              clear - INV A' UGH.
              destruct INV as [[INV _] _].
              specialize (INV j jc').
              generalize dependent
                         (typ_to_dtyp [] (getIRType
                                            (snd (ListUtil.ith (l:=pre) (i:=j) jc')))).
              intros dt ?.
              destruct INV as [ptr [F IG]].
              exists ptr.
              split.
              -
                eapply dtyp_fits_after_allocated; eassumption.
              -
                cbn.
                unfold in_global_addr in *.
                now rewrite alist_find_neq.
            }
          ++
            cbn in *.
            unfold fun_declarations_invariant, global_named_ptr_exists in *.
            split.
            2: {
              unfold genv_mem_wf.
              split.
              -
                clear - A' DI.
                destruct DI as [_ [GUNIQ GMB]].
                unfold genv_ptr_uniq, in_global_addr.
                intros * L L' PTREQ.
                apply alist_add_find_some in L;
                  apply alist_add_find_some in L'.
                destruct L as [[ID PTR] | [ID PTR]],
                         L' as [[ID' PTR'] | [ID' PTR']].
                +
                  congruence.
                +
                  exfalso; subst.
                  invc PTR.
                  apply GMB in PTR'.
                  copy_apply allocate_next_logical_key_inc A'.
                  apply allocate_next_logical_key in A'.
                  lia.
                +
                  exfalso; subst.
                  invc PTR'.
                  apply GMB in PTR.
                  copy_apply allocate_next_logical_key_inc A'.
                  apply allocate_next_logical_key in A'.
                  lia.
                +
                  eapply GUNIQ;
                    eassumption.
              -
                destruct a.
                erewrite initOneIRGlobal_ident by eassumption.
                clear - A' DI Heqs0.
                destruct DI as [_ [_ GMB]].
                copy_apply allocate_next_logical_key A';
                  rename H into AK.
                apply allocate_next_logical_key_inc in A'.
                unfold genv_mem_bounded in *.
                intros.
                apply alist_add_find_some in H.
                destruct H as [[ID K] | [ID K]].
                +
                  invc K.
                  invc AK.
                  cbn [fst] in *.
                  lia.
                +
                  apply GMB in K.
                  lia.
            }
            destruct DI as [[[mf__m MFM] [mf__n MFN]] _].
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
        -- (* allocate post *)
          intros.
          cbn in *.
          move IHpost at bottom.

          rewrite <-ListUtil.list_app_first_last.
          destruct u2 as (m' & le' & g'' & ?).
          repeat break_let.
          destruct le' as [le' stack'].

          copy_apply global_uniq_chk_preserves_st Heqs.
          subst i0.

          move LG at bottom.
          rewrite <-ListUtil.list_app_first_last in LG.
          apply initIRGlobals_inr in LG.
          apply initIRGlobals_rev_app_inv in LG.
          destruct LG as (l'' & s'' & g1'' & g2'' & PRE'' & POST'' & G'').

          eapply IHpost.
          ++
            clear - H.
            unfold alloc_glob_decl_inv_mcfg in H.
            tauto.
          ++
            rewrite ListUtil.list_app_first_last. reflexivity.
          ++
            rewrite ListUtil.list_app_first_last. reflexivity.
          ++
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
            tauto.
    + (* allocate yx *)
      intros.
      unfold initXYplaceholders, addVars in LX.
      cbn in LX.
      repeat break_let.
      invc LX.
      cbn.
    
      repeat rewrite interp3_bind. 
      
      (* Alloca Y *)
      pose_interp3_alloca m'' a'' A' AE';
        [rewrite typ_to_dtyp_equation; congruence |].
      rewrite AE'.
      
      (* GlobalWrite Y *)
      cbn; rewrite !ITree.Eq.Eq.bind_ret_l.
      rewrite interp3_GW.
      cbn; rewrite !ITree.Eq.Eq.bind_ret_l.
      
      repeat rewrite interp3_bind.
      
      (* Alloca X *)
      pose_interp3_alloca m''' a''' A'' AE'';
        [rewrite typ_to_dtyp_equation; congruence |].
      rewrite AE''.
      
      (* GlobalWrite X *)
      cbn; rewrite !ITree.Eq.Eq.bind_ret_l.
      rewrite interp3_GW.
      cbn; rewrite !ITree.Eq.Eq.bind_ret_l.
      
      repeat rewrite interp3_ret, !ITree.Eq.Eq.bind_ret_l.
      cbn.
      rewrite interp3_ret.

      apply eutt_Ret.
      unfold post_alloc_invariant_mcfg', post_alloc_invariant_mcfg in *.
      break_let.
      split.
      2: {
        destruct H0 as [_ DI].
        inversion_clear DI as [[M F] G0M0WF].
        split.
        constructor; cbn.
        - now rewrite !alist_find_neq by discriminate.
        - now rewrite !alist_find_neq by discriminate.
        -
          eapply genv_mem_wf_allocate.
          eapply genv_mem_wf_allocate.
          all: eassumption.
      }
      split.
      *
        unfold allocated_xy.
        exists a''', a''.
        repeat split.
        --
          unfold dtyp_fits.
          clear - A''.
          apply allocate_inv in A''.
          destruct A'' as [NV [MA A]].
          subst.
          do 3 eexists.
          rewrite get_logical_block_add_to_frame.
          cbn [fst].
          rewrite get_logical_block_of_add_logical_block.
          unfold make_empty_logical_block.
          split; reflexivity.
        --
          unfold dtyp_fits.
          clear - A' A''.
          apply allocate_inv in A'.
          apply allocate_inv in A''.
          destruct A' as [NV' [MA' A']].
          destruct A'' as [NV'' [MA'' A'']].
          subst.
          rewrite get_logical_block_add_to_frame.
          cbn [fst].
          rewrite get_logical_block_of_add_logical_block_neq.
          2: {
            generalize
              (make_empty_logical_block
                 (typ_to_dtyp [] (TYPE_Array (Z.to_N (Int64.intval o))
                                             TYPE_Double)));
              intros l.
            clear.
            enough (next_logical_key m0 <
                next_logical_key
                  (add_to_frame (add_logical_block (next_logical_key m0) l m0)
                                (next_logical_key m0)))%Z
              by lia.
            apply next_logical_key_add_to_frame_inc.
          }
          rewrite get_logical_block_add_to_frame.
          rewrite get_logical_block_of_add_logical_block.
          unfold make_empty_logical_block.
          do 3 eexists.
          split; reflexivity.
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
        --
          clear - A' A''.
          eapply freshly_allocated_different_blocks.
          eassumption.
          eapply allocate_allocated.
          eassumption.
      *
        unfold allocated_globals_mcfg, allocated_globals in *.
        split.
        2: {
          destruct H0 as [[_ L] _].
          unfold no_llvm_ptr_aliasing in *; cbn in *.
          intros.
          eapply L.
          - eapply H0.
          - eapply H1.
          - eassumption.
          - eassumption.
          - assumption.
          - 
            move IR at bottom.
            dedup_states.
            apply genIR_Γ in IR.
            cbn in IR.
            apply list_app_eqlen_eq_r in IR; [| reflexivity].
            destruct IR as [ΓG XY]; invc XY.
            apply nth_map_inv in H2.
            destruct H2 as [(_nm, _t) [_ ID1]].
            invc ID1; cbn in *.
            rewrite <-H5.
            now rewrite !alist_find_neq by discriminate.
          - 
            move IR at bottom.
            dedup_states.
            apply genIR_Γ in IR.
            cbn in IR.
            apply list_app_eqlen_eq_r in IR; [| reflexivity].
            destruct IR as [ΓG XY]; invc XY.
            apply nth_map_inv in H3.
            destruct H3 as [(_nm, _t) [_ ID2]].
            invc ID2; cbn in *.
            rewrite <-H6.
            now rewrite !alist_find_neq by discriminate.
        }

        intros.
        destruct H0 as [[H0 _] _].
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
        2: assumption.

        eapply dtyp_fits_after_allocated.
        2: eapply dtyp_fits_after_allocated.
        all: eassumption.
  - (* initialize (globals ++ yx) *)
    intros.

    assert (T : Ret (memory_set (memory_set mg (S lg) mo) lg mi, ())
                ≈
                ITree.bind (E:=E_mcfg)
                            (ret (mg, ()))
                            (fun mg' => ret (memory_set
                                            (memory_set (fst mg') (S lg) mo)
                                            lg mi, ())))
      by (cbn; now rewrite Eq.bind_ret_l).
    rewrite T; clear T.

    destruct_unit.
    pose proof H0 as X.
    unfold post_alloc_invariant_mcfg' in H0.
    destruct u0 as (m', ((l', st'), (g', TU))); destruct_unit.
    cbn in H0.
    destruct u1 as (? & ()).
    subst p p1 u2.
    (* clear u1. *)
    rename H0 into POST_ALLOC.
    
    rewrite translate_bind, interp3_bind.
    subst.

    pose (fun globals : list (string * DSHType) =>
            (fun h '(memV, (l, t1, (g, t2))) =>
               post_init_invariant
                 name
                 (firstn (length globals) (e ++ [(DSHPtrVal (S (Datatypes.length globals)) o, true);
                        (DSHPtrVal (Datatypes.length globals) i, true)]))
                 {|
                   block_count := block_count;
                   local_count := local_count;
                   void_count := void_count;
                   Γ := firstn (length globals) Γ_globals |} mg (memV, (l, g))
               /\ post_alloc_invariant_mcfg' (mg, ()) (memV, (l, t1, (g, t2)))
               /\ h ≡ (mg, ())
            )
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
                       (translate exp_to_L0
                          (map_monad_ initialize_global
                                      (map (TFunctor_global typ dtyp (typ_to_dtyp []))
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
          split; [| now split].
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
              unshelve econstructor.
              exact mem_empty.
              rewrite nth_error_nil in H0.
              inversion H0.
            + solve_gamma_bound.
          -
            intuition.
            Unshelve.
            exact (ID_Local (Name "shelf_go_away")).
          -
            (* TODO: prove [anon_declarations_invariant] *)
            admit.
        }
        inv PRE.
        replace ([] ++ gdecls2)
          with gdecls2
          by apply app_nil_l.
        apply H0.
      }

      clear POST_ALLOC.
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
        rewrite interp3_ret.
        apply eutt_Ret.
        rewrite app_nil_r.
        apply PINV.
      *
        unfold post_init_invariant' in PINV.
        destruct PINV as [PINV [NPALLOC _]].
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

        pose proof LG as GUNIQ.
        apply initIRGlobals_names_unique in GUNIQ.

        rewrite translate_bind.
        rewrite interp3_bind.

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

        pose IPRE as E_PRE_LEN; apply init_with_data_len in E_PRE_LEN.
        rename p1 into ne'.
        replace
          (firstn (Datatypes.length pre)
                  ((e_pre ++ ne' :: e_post')
                     ++ [(DSHPtrVal (S (Datatypes.length pre)) o, true);
                         (DSHPtrVal (Datatypes.length pre) i, true)]))
          with e_pre in *.
        2:{
          rewrite list_cons_app.
          rewrite <-!app_assoc.
          rewrite firstn_app.
          replace (length pre - length e_pre) with 0 by lia.
          rewrite firstn_all2 by lia.
          rewrite firstn_O, app_nil_r.
          reflexivity.
        }

        replace (firstn (Datatypes.length pre)
                        (map IR_of_global (pre ++ a :: post)))
          with (map IR_of_global pre) in *.
        2:{
          rewrite map_app.
          rewrite firstn_app.
          replace (length pre - length (map IR_of_global pre))
            with 0
            by (rewrite map_length; lia).
          rewrite firstn_O, firstn_all2, app_nil_r.
          reflexivity.
          rewrite map_length; lia.
        }

        (* ZX TODO: might want to change the relation here *)
        apply eutt_clo_bind with (UU:=post_init_invariant' (pre ++ [a])).
        -- (* initialize the "new" global [a] *)
          cbn.
          autorewrite with itree.

          rewrite exp_to_L0_Global, subevent_subevent.
          rewrite interp3_bind.

          inversion_clear GINV as ((AXY & AG) & DI).
          destruct a as (a_nm, a_t).

          pose proof AG as AG'.

          assert (T : exists v, Maps.lookup (g_ident tg2) g' ≡ Some v);
            [| destruct T as [av AV]].
          {
            unfold allocated_globals in AG.
            destruct AG as [AG _].
            simpl in *.
            unfold in_global_addr in AG.

            specialize (AG (length pre)).
            autospecialize AG;
              [subst; rewrite ListUtil.length_app; cbn; lia |].
            destruct AG as [a_ptr [AA AIG]].
            unshelve erewrite ListUtil.ith_eq with (j:=length pre + 0)
              in AIG; [rewrite !app_length; cbn; lia | | lia].
            unshelve erewrite ith_eq_app_r in AIG; [cbn; lia |].
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
          rewrite (interp3_GR) by apply AV.

          autorewrite with itree.

          rename Heqs0 into IA.
          move IA at bottom.
          simpl in IA.
          repeat break_match_hyp;
            inv IA; cbn.
          ++
            rewrite typ_to_dtyp_I.
            rewrite interp3_bind.
            rewrite denote_exp_i64_mcfg.
            autorewrite with itree.
            cbn.
            autorewrite with itree.

            rewrite exp_to_L0_Memory.
            rewrite subevent_subevent.

            cbn in AV.
            unfold allocated_globals in AG.
            destruct AG as [AG _].
            specialize (AG (length pre)).
            autospecialize AG;
              [rewrite ListUtil.length_app; cbn; lia |].
            destruct AG as [a_ptr [AL IG]].
            apply dtyp_fits_allocated in AL.
            unshelve erewrite ListUtil.ith_eq with (j:=length pre + 0)
              in IG; [rewrite !app_length; cbn; lia | | lia].
            unshelve erewrite ith_eq_app_r in IG; [cbn; lia |].
            cbn in IG.
            unfold write.
            unfold in_global_addr in IG.
            replace av with (DVALUE_Addr a_ptr) in * by congruence; clear IG.
            destruct a_ptr as (a_ptr, a_off).
            copy_apply allocated_get_logical_block AL;
              rename H0 into AMB.
            destruct AMB as [[a_sz a_bytes a_id] AMB].
            rewrite interp_mcfg_store
              by (unfold write; rewrite AMB; reflexivity).
            apply eutt_Ret.
            constructor.
            2: {
              destruct NPALLOC as [[XY GLOB] DECL].
              split; [| reflexivity].
              split; [split |].
              -
                unfold allocated_xy in *.
                destruct XY as (p1 & p2 & A1 & A2 & G1 & G2).
                exists p1; exists p2.
                intuition.
                +
                  eapply dtyp_fits_add_logical_block_key_neq;
                    [eassumption |].
                  clear - AV G1 H4.
                  destruct H4 as [GUNIQ _].
                  replace a_ptr with (fst (a_ptr, a_off)) by reflexivity.
                  intros C.
                  eapply GUNIQ in C.
                  2,3: eassumption.
                  inv C.
                +
                  eapply dtyp_fits_add_logical_block_key_neq;
                    [eassumption |].
                  clear - AV H H4.
                  destruct H4 as [GUNIQ _].
                  replace a_ptr with (fst (a_ptr, a_off)) by reflexivity.
                  intros C.
                  eapply GUNIQ in C.
                  2,3: eassumption.
                  inv C.
              -
                clear - GLOB GUNIQ AL AV AMB.
                match goal with
                | [_ : _ |- context [add_all_index ?a ?b ?c]] =>
                  generalize dependent (add_all_index a b c)
                end.
                intros a_bytes'.

                intros.
                unfold allocated_globals in *.
                split; [| intuition].
                intros.
                destruct GLOB as [GLOB _].
                specialize (GLOB j jc).
                destruct GLOB as [ptr [DF IG]].
                exists ptr.
                unfold in_global_addr in *.
                intuition.
                unfold dtyp_fits.
                destruct (Z.eq_dec a_ptr (fst ptr)).
                +
                  rewrite e, get_logical_block_of_add_logical_block.
                  do 3 eexists.
                  split; [reflexivity |].
                  unfold dtyp_fits in DF.
                  destruct DF as (sz' & bytes' & cid' & AMB' & F').
                  cbn in AMB.
                  rewrite e in AMB.
                  rewrite AMB' in AMB; invc AMB.
                  assumption.
                +
                  rewrite get_logical_block_of_add_logical_block_neq
                    by assumption.
                  unfold dtyp_fits in DF.
                  assumption.
              -
                split; [tauto |].
                destruct DI as [_ WF].
                clear - WF.
                apply genv_mem_wf_add_logical_block.
                assumption.
            }
            constructor.
            **
              replace
                (firstn (Datatypes.length (pre ++ [(a_nm, DSHnat)]))
                   ((e_pre ++ ne' :: e_post') ++
                    [(DSHPtrVal (S (Datatypes.length (pre ++ [(a_nm, DSHnat)]))) o, true);
                    (DSHPtrVal (Datatypes.length (pre ++ [(a_nm, DSHnat)])) i , true)]))
                with
                  (e_pre ++ [ne']).
              2:{
                rewrite !app_length; cbn.
                rewrite list_cons_app with (l4:=e_post').
                rewrite <-!app_assoc, ->app_assoc.
                rewrite firstn_app.
                replace (length pre + 1 - length (e_pre ++ [ne']))
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
                  simpl in Heqs2.
                  repeat break_match_hyp; try inl_inr.
                  invc Heqs2.
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

                  simpl_data.
                  enough (l1' ≡ hdata_pre)
                    by now replace i0 with i1 by congruence.
                  rewrite rotateN_add in IPRE.
                  eapply initFSHGlobals_initIRGlobals_rev_data.
                  eapply PRE.
                  eapply IPRE.
                +++
                  assert (n < length e_pre).
                  {
                    apply nth_error_in in H0.
                    rewrite app_length in H0.
                    cbn in H0.
                    lia.
                  }
                  clear n0.

                  rewrite app_nth_error1 in H0 by assumption.
                  rewrite map_app in H1.
                  rewrite app_nth_error1 in H1 by (rewrite map_length; lia).
                  destruct x as [id | id].
                  2:{
                    apply nth_map_inv in H1.
                    destruct H1 as ((?, ?) & ? & ?).
                    discriminate.
                  }

                  inversion PINV as [[I _ _ _ _ _ _] _].
                  cbn in I.
                  specialize (I _ _ _ _ _ H0 H1).
                  generalize dependent
                             (LBlock a_sz
                               (add_all_index
                                  (serialize_dvalue
                                     (DVALUE_I64 (DynamicValues.Int64.repr
                                                    (DynamicValues.Int64.unsigned i0))))
                                  a_off a_bytes) a_id).
                  intros lb.

                  assert (forall vptr, g' @ id ≡ Some (DVALUE_Addr vptr) ->
                                  a_ptr ≢ fst vptr).
                  {
                    intros.
                    replace a_ptr with (fst (a_ptr, a_off)) by reflexivity.
                    move AG' at bottom.
                    destruct AG' as [_ NLPA].
                    rewrite firstn_all2 in NLPA by lia.
                    unfold no_llvm_ptr_aliasing in NLPA.
                    destruct ne'.
                    eapply NLPA with (n1:=length pre) (id1:=ID_Global (Name a_nm)).
                    -
                      rewrite nth_error_app2 by lia.
                      rewrite E_PRE_LEN, Nat.sub_diag.
                      reflexivity.
                    -
                      eapply ListNth.nth_error_weaken.
                      eapply H0.
                    -
                      cbn.
                      rewrite map_app.
                      rewrite nth_error_app2
                        by now rewrite map_length.
                      rewrite map_length, Nat.sub_diag.
                      rewrite map_cons.
                      cbn.
                      reflexivity.
                    -
                      cbn.
                      rewrite map_app.
                      eapply ListNth.nth_error_weaken.
                      eapply H1.
                    -
                      clear - H1 H2 GUNIQ E_PRE_LEN.
                      intros C; invc C.
                      unfold list_uniq in GUNIQ.
                      apply nth_map_inv in H1.
                      destruct H1 as ((a_nm', τ') & A & A').
                      invc A'.
                      specialize (GUNIQ n (length pre) (a_nm, τ') (a_nm, DSHnat)).
                      full_autospecialize GUNIQ; try reflexivity.
                      now apply ListNth.nth_error_weaken.
                      rewrite nth_error_app2 by reflexivity.
                      rewrite Nat.sub_diag.
                      reflexivity.
                      lia.
                    -
                      unfold in_local_or_global_addr.
                      assumption.
                    -
                      unfold in_local_or_global_addr.
                      assumption.
                  }

                  break_match.
                  {
                    unfold in_local_or_global_scalar in *.
                    destruct I as (vptr & τ' & I).
                    exists vptr; exists τ'.
                    destruct I as (TTT & G'ID & R').
                    split; [assumption | split; [assumption |]].
                    unfold read in *.

                    rewrite get_logical_block_of_add_logical_block_neq by now apply H3.
                    now repeat break_match_goal.
                  }
                  {
                    unfold in_local_or_global_scalar in *.
                    destruct I as (vptr & τ' & I).
                    exists vptr; exists τ'.
                    destruct I as (TTT & G'ID & R').
                    split; [assumption | split; [assumption |]].
                    unfold read in *.

                    rewrite get_logical_block_of_add_logical_block_neq by now apply H3.
                    now repeat break_match_goal.
                  }
                  {
                    unfold in_local_or_global_scalar in *.
                    destruct I as (vptr & τ' & I).
                    exists vptr; exists τ'.
                    destruct I as (TTT & DTF & ILG & IDK).
                    split; [assumption | split; [| split; [assumption |]]].
                    -
                      unfold dtyp_fits in *.
                      rewrite get_logical_block_of_add_logical_block_neq by now apply H3.
                      apply DTF.
                    -
                      unfold get_array_cell in *.
                      break_let.
                      rewrite get_logical_block_of_add_logical_block_neq.
                      apply IDK.
                      replace z with (fst vptr) by now subst.
                      apply H3.
                      now subst.
                  }
              ---
                unfold WF_IRState.
                cbn.
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
                eapply initFSHGlobals_no_id_aliasing.
                1:{
                  clear - GUNIQ.
                  rewrite list_cons_app in GUNIQ.
                  rewrite app_assoc in GUNIQ.
                  apply list_uniq_app in GUNIQ.
                  intuition.
                }
                eapply initFSHGlobals_app.
                eassumption.
                unfold initFSHGlobals.
                unfold init_with_data.
                rewrite Heqs2.
                reflexivity.
              ---
                eapply initFSHGlobals_no_dshptr_aliasing.
                eapply initFSHGlobals_app with (post:=[(a_nm, DSHnat)]).
                eassumption.
                unfold initFSHGlobals.
                unfold init_with_data.
                rewrite Heqs2.
                reflexivity.
              ---
                move AG' at bottom.
                unfold allocated_globals in AG'.
                destruct AG' as [_ NAL].
                rewrite firstn_all2 in NAL by lia.
                rewrite list_cons_app in NAL.
                rewrite app_assoc in NAL.
                unfold no_llvm_ptr_aliasing_cfg, no_llvm_ptr_aliasing.
                cbn; intros.
                eapply NAL; cbn.
                +++ eapply ListNth.nth_error_weaken; eapply H0.
                +++ eapply ListNth.nth_error_weaken; eapply H1.
                +++
                  rewrite list_cons_app.
                  rewrite !map_app.
                  rewrite app_assoc.
                  eapply ListNth.nth_error_weaken.
                  rewrite <-map_app.
                  eassumption.
                +++
                  rewrite list_cons_app.
                  rewrite !map_app.
                  rewrite app_assoc.
                  eapply ListNth.nth_error_weaken.
                  rewrite <-map_app.
                  eassumption.
                +++ eassumption.
                +++ eassumption.
                +++ eassumption.
              ---
                unfold id_allocated.
                intros.
                destruct (Nat.eq_dec (length e_pre) n).
                +++
                  subst n.
                  replace (length e_pre) with (0 + length e_pre) in H0 by lia.
                  rewrite ListNth.nth_error_length in H0.
                  cbn in H0.
                  invc H0.
                  apply initFSHGlobals_no_overwrite in Heqs3.
                  rewrite Heqs3.
                  clear - Heqs2.
                  apply mem_block_exists_union.
                  apply initOneFSHGlobal_mem_block_exists in Heqs2.
                  intuition.
                +++
                  rewrite app_nth_error1 in H0
                    by (apply nth_error_in in H0;
                        rewrite app_length in H0;
                        cbn in H0; lia).
                  destruct PINV as [[_ _ _ _ _ A] _].
                  eapply A.
                  eassumption.
              ---
                unfold gamma_bound.
                cbn.
                intros * NTH_L.
                apply nth_map_inv in NTH_L.
                destruct NTH_L as [(a_nm', a_t') [_ C]].
                inv C.
            **
              constructor.
              all: cbn; clear - DI.
              all: unfold fun_declarations_invariant in DI.
              all: intuition.
            **
              (* TODO: prove [anon_declarations_invariant] *)
              admit.
          ++ (* ZX TODO: see how these bullets can be done all in one *)
            rewrite typ_to_dtyp_D.
            rewrite interp3_bind.
            rewrite denote_exp_double_mcfg.
            autorewrite with itree.
            cbn.
            autorewrite with itree.

            rewrite exp_to_L0_Memory.
            rewrite subevent_subevent.

            cbn in AV.
            unfold allocated_globals in AG.
            destruct AG as [AG _].
            specialize (AG (length pre)).
            autospecialize AG;
              [rewrite ListUtil.length_app; cbn; lia |].
            destruct AG as [a_ptr [AL IG]].
            apply dtyp_fits_allocated in AL.
            unshelve erewrite ListUtil.ith_eq with (j:=length pre + 0)
              in IG; [rewrite !app_length; cbn; lia | | lia].
            unshelve erewrite ith_eq_app_r in IG; [cbn; lia |].
            cbn in IG.
            unfold write.
            unfold in_global_addr in IG.
            replace av with (DVALUE_Addr a_ptr) in * by congruence; clear IG.
            destruct a_ptr as (a_ptr, a_off).
            copy_apply allocated_get_logical_block AL;
              rename H0 into AMB.
            destruct AMB as [[a_sz a_bytes a_id] AMB].
            rewrite interp_mcfg_store
              by (unfold write; rewrite AMB; reflexivity).
            apply eutt_Ret.
            constructor.
            2: {
              destruct NPALLOC as [[XY GLOB] DECL].
              split; [| reflexivity].
              split; [split |].
              -
                unfold allocated_xy in *.
                destruct XY as (p1 & p2 & A1 & A2 & G1 & G2).
                exists p1; exists p2.
                intuition.
                +
                  eapply dtyp_fits_add_logical_block_key_neq;
                    [eassumption |].
                  clear - AV G1 H4.
                  destruct H4 as [GUNIQ _].
                  replace a_ptr with (fst (a_ptr, a_off)) by reflexivity.
                  intros C.
                  eapply GUNIQ in C.
                  2,3: eassumption.
                  inv C.
                +
                  eapply dtyp_fits_add_logical_block_key_neq;
                    [eassumption |].
                  clear - AV H H4.
                  destruct H4 as [GUNIQ _].
                  replace a_ptr with (fst (a_ptr, a_off)) by reflexivity.
                  intros C.
                  eapply GUNIQ in C.
                  2,3: eassumption.
                  inv C.
              -
                clear - GLOB GUNIQ AL AV AMB.
                match goal with
                | [_ : _ |- context [add_all_index ?a ?b ?c]] =>
                  generalize dependent (add_all_index a b c)
                end.
                intros a_bytes'.

                intros.
                unfold allocated_globals in *.
                split; [| intuition].
                intros.
                destruct GLOB as [GLOB _].
                specialize (GLOB j jc).
                destruct GLOB as [ptr [DF IG]].
                exists ptr.
                unfold in_global_addr in *.
                intuition.
                unfold dtyp_fits.
                destruct (Z.eq_dec a_ptr (fst ptr)).
                +
                  rewrite e, get_logical_block_of_add_logical_block.
                  do 3 eexists.
                  split; [reflexivity |].
                  unfold dtyp_fits in DF.
                  destruct DF as (sz' & bytes' & cid' & AMB' & F').
                  cbn in AMB.
                  rewrite e in AMB.
                  rewrite AMB' in AMB; invc AMB.
                  assumption.
                +
                  rewrite get_logical_block_of_add_logical_block_neq
                    by assumption.
                  unfold dtyp_fits in DF.
                  assumption.
              -
                split; [tauto |].
                destruct DI as [_ WF].
                clear - WF.
                apply genv_mem_wf_add_logical_block.
                assumption.
            }
            constructor.
            **
              replace
                (firstn (Datatypes.length (pre ++ [(a_nm, DSHCType)]))
                   ((e_pre ++ ne' :: e_post') ++
                    [(DSHPtrVal (S (Datatypes.length (pre ++ [(a_nm, DSHCType)]))) o, true);
                    (DSHPtrVal (Datatypes.length (pre ++ [(a_nm, DSHCType)])) i , true)]))
                with
                  (e_pre ++ [ne']).
              2:{
                rewrite !app_length; cbn.
                rewrite list_cons_app with (l4:=e_post').
                rewrite <-!app_assoc, ->app_assoc.
                rewrite firstn_app.
                replace (length pre + 1 - length (e_pre ++ [ne']))
                  with 0
                  by (rewrite app_length; cbn; lia).
                rewrite firstn_O, firstn_all2, app_nil_r.
                reflexivity.
                rewrite app_length; cbn; lia.
              }

              replace (firstn (Datatypes.length (pre ++ [(a_nm, DSHCType)]))
                              (map IR_of_global (pre ++ (a_nm, DSHCType) :: post)))
                with (map IR_of_global (pre ++ [(a_nm, DSHCType)]))
              in *.
              2:{
                rewrite list_cons_app with (l4:=post).
                rewrite app_assoc, !map_app, firstn_app.
                replace
                  (length (pre ++ [(a_nm, DSHCType)]) -
                   length (map IR_of_global pre ++ map IR_of_global [(a_nm, DSHCType)]))
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
                  invc Heqs2.
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
                    by (rewrite typ_to_dtyp_D; constructor).
                  cbn.
                  do 3 f_equal.

                  simpl_data.
                  autounfold with unfold_FCT in *.
                  enough (l1' ≡ hdata_pre) by congruence.
                  rewrite rotateN_add in IPRE.
                  eapply initFSHGlobals_initIRGlobals_rev_data.
                  eapply PRE.
                  eapply IPRE.
                +++
                  assert (n < length e_pre).
                  {
                    apply nth_error_in in H0.
                    rewrite app_length in H0.
                    cbn in H0.
                    lia.
                  }
                  clear n0.

                  rewrite app_nth_error1 in H0 by assumption.
                  rewrite map_app in H1.
                  rewrite app_nth_error1 in H1 by (rewrite map_length; lia).
                  destruct x as [id | id].
                  2:{
                    apply nth_map_inv in H1.
                    destruct H1 as ((?, ?) & ? & ?).
                    discriminate.
                  }

                  inversion PINV as [[I _ _ _ _ _ _] _].
                  cbn in I.
                  specialize (I _ _ _ _ _ H0 H1).
                  generalize dependent
                             (LBlock a_sz
                               (add_all_index (serialize_dvalue (DVALUE_Double b0)) a_off a_bytes) a_id).
                  intros lb.

                  assert (forall vptr, g' @ id ≡ Some (DVALUE_Addr vptr) ->
                                  a_ptr ≢ fst vptr).
                  {
                    intros.
                    replace a_ptr with (fst (a_ptr, a_off)) by reflexivity.
                    move AG' at bottom.
                    destruct AG' as [_ NLPA].
                    rewrite firstn_all2 in NLPA by lia.
                    unfold no_llvm_ptr_aliasing in NLPA.
                    destruct ne'.
                    eapply NLPA with (n1:=length pre) (id1:=ID_Global (Name a_nm)).
                    -
                      rewrite nth_error_app2 by lia.
                      rewrite E_PRE_LEN, Nat.sub_diag.
                      reflexivity.
                    -
                      eapply ListNth.nth_error_weaken.
                      eapply H0.
                    -
                      cbn.
                      rewrite map_app.
                      rewrite nth_error_app2
                        by now rewrite map_length.
                      rewrite map_length, Nat.sub_diag.
                      rewrite map_cons.
                      cbn.
                      reflexivity.
                    -
                      cbn.
                      rewrite map_app.
                      eapply ListNth.nth_error_weaken.
                      eapply H1.
                    -
                      clear - H1 H2 GUNIQ E_PRE_LEN.
                      intros C; invc C.
                      unfold list_uniq in GUNIQ.
                      apply nth_map_inv in H1.
                      destruct H1 as ((a_nm', τ') & A & A').
                      invc A'.
                      specialize (GUNIQ n (length pre) (a_nm, τ') (a_nm, DSHCType)).
                      full_autospecialize GUNIQ; try reflexivity.
                      now apply ListNth.nth_error_weaken.
                      rewrite nth_error_app2 by reflexivity.
                      rewrite Nat.sub_diag.
                      reflexivity.
                      lia.
                    -
                      unfold in_local_or_global_addr.
                      assumption.
                    -
                      unfold in_local_or_global_addr.
                      assumption.
                  }

                  break_match.
                  {
                    unfold in_local_or_global_scalar in *.
                    destruct I as (vptr & τ' & I).
                    exists vptr; exists τ'.
                    destruct I as (TTT & G'ID & R').
                    split; [assumption | split; [assumption |]].
                    unfold read in *.

                    rewrite get_logical_block_of_add_logical_block_neq by now apply H3.
                    now repeat break_match_goal.
                  }
                  {
                    unfold in_local_or_global_scalar in *.
                    destruct I as (vptr & τ' & I).
                    exists vptr; exists τ'.
                    destruct I as (TTT & G'ID & R').
                    split; [assumption | split; [assumption |]].
                    unfold read in *.

                    rewrite get_logical_block_of_add_logical_block_neq by now apply H3.
                    now repeat break_match_goal.
                  }
                  {
                    unfold in_local_or_global_scalar in *.
                    destruct I as (vptr & τ' & I).
                    exists vptr; exists τ'.
                    destruct I as (TTT & DTF & ILG & IDK).
                    split; [assumption | split; [| split; [assumption |]]].
                    -
                      unfold dtyp_fits in *.
                      rewrite get_logical_block_of_add_logical_block_neq by now apply H3.
                      apply DTF.
                    -
                      unfold get_array_cell in *.
                      break_let.
                      rewrite get_logical_block_of_add_logical_block_neq.
                      apply IDK.
                      replace z with (fst vptr) by now subst.
                      apply H3.
                      now subst.
                  }
              ---
                unfold WF_IRState.
                cbn.
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
                eapply initFSHGlobals_no_id_aliasing.
                1:{
                  clear - GUNIQ.
                  rewrite list_cons_app in GUNIQ.
                  rewrite app_assoc in GUNIQ.
                  apply list_uniq_app in GUNIQ.
                  intuition.
                }
                eapply initFSHGlobals_app.
                eassumption.
                unfold initFSHGlobals.
                unfold init_with_data.
                rewrite Heqs2.
                reflexivity.
              ---
                eapply initFSHGlobals_no_dshptr_aliasing.
                eapply initFSHGlobals_app with (post:=[(a_nm, DSHCType)]).
                eassumption.
                unfold initFSHGlobals.
                unfold init_with_data.
                rewrite Heqs2.
                reflexivity.
              ---
                move AG' at bottom.
                unfold allocated_globals in AG'.
                destruct AG' as [_ NAL].
                rewrite firstn_all2 in NAL by lia.
                rewrite list_cons_app in NAL.
                rewrite app_assoc in NAL.
                unfold no_llvm_ptr_aliasing_cfg, no_llvm_ptr_aliasing.
                cbn; intros.
                eapply NAL; cbn.
                +++ eapply ListNth.nth_error_weaken; eapply H0.
                +++ eapply ListNth.nth_error_weaken; eapply H1.
                +++
                  rewrite list_cons_app.
                  rewrite !map_app.
                  rewrite app_assoc.
                  eapply ListNth.nth_error_weaken.
                  rewrite <-map_app.
                  eassumption.
                +++
                  rewrite list_cons_app.
                  rewrite !map_app.
                  rewrite app_assoc.
                  eapply ListNth.nth_error_weaken.
                  rewrite <-map_app.
                  eassumption.
                +++ eassumption.
                +++ eassumption.
                +++ eassumption.
              ---
                unfold id_allocated.
                intros.
                destruct (Nat.eq_dec (length e_pre) n).
                +++
                  subst n.
                  replace (length e_pre) with (0 + length e_pre) in H0 by lia.
                  rewrite ListNth.nth_error_length in H0.
                  cbn in H0.
                  invc H0.
                  apply initFSHGlobals_no_overwrite in Heqs3.
                  rewrite Heqs3.
                  clear - Heqs2.
                  apply mem_block_exists_union.
                  apply initOneFSHGlobal_mem_block_exists in Heqs2.
                  intuition.
                +++
                  rewrite app_nth_error1 in H0
                    by (apply nth_error_in in H0;
                        rewrite app_length in H0;
                        cbn in H0; lia).
                  destruct PINV as [[_ _ _ _ _ A] _].
                  eapply A.
                  eassumption.
              ---
                unfold gamma_bound.
                cbn.
                intros * NTH_L.
                apply nth_map_inv in NTH_L.
                destruct NTH_L as [(a_nm', a_t') [_ C]].
                inv C.
            **
              constructor.
              all: cbn; clear - DI.
              all: unfold fun_declarations_invariant in DI.
              all: intuition.
            **
              (* TODO: prove [anon_declarations_invariant] *)
              admit.
          ++
            rewrite typ_to_dtyp_D_array.

            unfold constArray in Heqp.
            break_let.
            invc Heqp.
            unfold genFloatV.
            unfold tfmap, TFunctor_list.
            rewrite map_map.
            cbn.
            rewrite typ_to_dtyp_D.

            destruct n as (n_val, n_ran).
            assert (T : exists n, n_val ≡ Z.of_nat n)
              by (apply Z_of_nat_complete; lia);
              destruct T as [n N]; subst n_val.
            cbn in AV.
            remember {|
                DynamicValues.Int64.intval := Z.of_nat n;
                DynamicValues.Int64.intrange := n_ran |}
              as int_n.

            rename l6 into pdata.
            unfold denote_exp; fold denote_exp.
            rewrite map_monad_map.
            cbn.
            autorewrite with itree.
            rewrite interp3_bind.

            rewrite map_monad_ret_map with (g0:=UVALUE_Double) by reflexivity.
            rewrite translate_ret, interp3_ret.
            autorewrite with itree.
            rewrite interp3_bind.
            unfold concretize_or_pick.
            replace (is_concrete (UVALUE_Array (map UVALUE_Double pdata)))
              with true.
            2: {
              clear; cbn.
              symmetry; apply forallb_forall.
              intros.
              apply ListUtil.in_map_elim in H.
              destruct H as [d [_ D]].
              now subst.
            }
            cbn.
            rewrite map_monad_map.
            rewrite map_monad_inr_map with (g0:=DVALUE_Double)
              by reflexivity.
            cbn.
            rewrite translate_ret, interp3_ret.
            autorewrite with itree.

            rewrite exp_to_L0_Memory, subevent_subevent.

            unfold allocated_globals in AG.
            destruct AG as [AG _].
            specialize (AG (length pre)).
            autospecialize AG;
              [subst; rewrite ListUtil.length_app; cbn; lia |].
            destruct AG as [a_ptr [AA AIG]].
            apply dtyp_fits_allocated in AA.
            unshelve erewrite ListUtil.ith_eq with (j:=length pre + 0)
              in AIG; [rewrite !app_length; cbn; lia | | lia].
            unshelve erewrite ith_eq_app_r in AIG; [cbn; lia |].
            cbn in AIG.
            unfold in_global_addr in AIG.
            replace av with (DVALUE_Addr a_ptr) in * by congruence; clear AV.
            destruct a_ptr as (a_ptr, a_off).

            copy_apply allocated_get_logical_block AA;
              rename H0 into AM'B.
            destruct AM'B as [[a_sz a_bytes a_id] AM'B].
            rewrite interp_mcfg_store
              by (unfold write; rewrite AM'B; reflexivity).

            apply eutt_Ret.
            constructor.
            2: {
              destruct NPALLOC as [[XY GLOB] DECL].
              split; [| reflexivity].
              split; [split |].
              -
                unfold allocated_xy in *.
                destruct XY as (p1 & p2 & A1 & A2 & G1 & G2).
                exists p1; exists p2.
                intuition.
                +
                  eapply dtyp_fits_add_logical_block_key_neq;
                    [eassumption |].
                  clear - AIG G1 H4.
                  destruct H4 as [GUNIQ _].
                  replace a_ptr with (fst (a_ptr, a_off)) by reflexivity.
                  intros C.
                  eapply GUNIQ in C.
                  2,3: eassumption.
                  inv C.
                +
                  eapply dtyp_fits_add_logical_block_key_neq;
                    [eassumption |].
                  clear - AIG H H4.
                  destruct H4 as [GUNIQ _].
                  replace a_ptr with (fst (a_ptr, a_off)) by reflexivity.
                  intros C.
                  eapply GUNIQ in C.
                  2,3: eassumption.
                  inv C.
              -
                match goal with
                | [_ : _ |- context [add_all_index ?a ?b ?c]] =>
                  generalize dependent (add_all_index a b c)
                end.
                intros a_bytes'.

                intros.
                unfold allocated_globals in *.
                split; [| intuition].
                intros.
                destruct GLOB as [GLOB _].
                specialize (GLOB j jc).
                destruct GLOB as [ptr [DF IG]].
                exists ptr.
                unfold in_global_addr in *.
                intuition.
                unfold dtyp_fits.
                destruct (Z.eq_dec a_ptr (fst ptr)).
                +
                  rewrite e, get_logical_block_of_add_logical_block.
                  do 3 eexists.
                  split; [reflexivity |].
                  unfold dtyp_fits in DF.
                  destruct DF as (sz' & bytes' & cid' & AMB' & F').
                  cbn in AM'B.
                  rewrite e in AM'B.
                  rewrite AMB' in AM'B; invc AM'B.
                  assumption.
                +
                  rewrite get_logical_block_of_add_logical_block_neq
                    by assumption.
                  unfold dtyp_fits in DF.
                  assumption.
              -
                split; [tauto |].
                destruct DI as [_ WF].
                clear - WF.
                apply genv_mem_wf_add_logical_block.
                assumption.
            }
            constructor.
            **
              replace
                (firstn (Datatypes.length (pre ++ [(a_nm, FHCOL.DSHPtr int_n)]))
                   ((e_pre ++ ne' :: e_post') ++
                    [(DSHPtrVal (S (Datatypes.length (pre ++ [(a_nm, FHCOL.DSHPtr int_n)]))) o, true);
                    (DSHPtrVal (Datatypes.length (pre ++ [(a_nm, FHCOL.DSHPtr int_n)])) i , true)]))
                with
                  (e_pre ++ [ne']).
              2:{
                rewrite !app_length; cbn.
                rewrite list_cons_app with (l4:=e_post').
                rewrite <-!app_assoc, ->app_assoc.
                rewrite firstn_app.
                replace (length pre + 1 - length (e_pre ++ [ne']))
                  with 0
                  by (rewrite app_length; cbn; lia).
                rewrite firstn_O, firstn_all2, app_nil_r.
                reflexivity.
                rewrite app_length; cbn; lia.
              }

              replace (firstn (Datatypes.length (pre ++ [(a_nm, FHCOL.DSHPtr int_n)]))
                              (map IR_of_global (pre ++ (a_nm, FHCOL.DSHPtr int_n) :: post)))
                with (map IR_of_global (pre ++ [(a_nm, FHCOL.DSHPtr int_n)]))
              in *.
              2:{
                rewrite list_cons_app with (l4:=post).
                rewrite app_assoc, !map_app, firstn_app.
                replace
                  (length (pre ++ [(a_nm, FHCOL.DSHPtr int_n)]) -
                   length (map IR_of_global pre ++ map IR_of_global [(a_nm, FHCOL.DSHPtr int_n)]))
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
                rename n into n', n0 into n.
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
                  invc Heqs2.
                  unfold in_local_or_global_scalar.

                  apply nth_map_inv in H1.
                  destruct H1 as [a' [A' AX']].
                  rewrite nth_error_app2 in A' by lia.
                  replace (length e_pre - length pre)
                    with 0 in * by lia.
                  cbn in A'.
                  inversion A'; clear A'; subst a'.
                  cbn in AX'.
                  invc AX'.

                  exists (a_ptr, a_off).
                  eexists; split;
                    [reflexivity | split; [| split; [assumption | intros _]]].
                  {
                    (* clear - AG'. *)
                    destruct AG' as [AG _].
                    remember
                      (FHCOL.DSHPtr
                         {| DynamicValues.Int64.intval := Z.of_nat n';
                            DynamicValues.Int64.intrange := n_ran |}) as a_t.
                    specialize (AG (length pre)).
                    autospecialize AG; [rewrite app_length; cbn; lia |].
                    destruct AG as [a' [A_FITS A'IG]].
                    replace (ListUtil.ith (l:=pre ++ (a_nm, a_t) :: post)
                                          (i:=Datatypes.length pre) T0)
                      with (a_nm, a_t)
                      in *.
                    2: {
                      clear.
                      unshelve erewrite ListUtil.ith_eq
                        with (j:=length pre + 0) by lia.
                      rewrite !app_length; cbn; lia.
                      unshelve erewrite ith_eq_app_r.
                      cbn; lia.
                      reflexivity.
                    }
                    cbn in A_FITS, A'IG.
                    unfold in_global_addr in *.
                    replace a' with (a_ptr, a_off) in * by congruence; clear A'IG.
                    
                    (* rewrite typ_to_dtyp_D_array. *)
                    unfold dtyp_fits in *.
                    rewrite get_logical_block_of_add_logical_block.
                    do 3 eexists; split; [reflexivity |].
                    cbn.

                    clear - AM'B A_FITS Heqa_t.
                    destruct A_FITS as (sz' & bytes' & cid' & B' & F).
                    rewrite B' in AM'B.
                    invc AM'B.
                    cbn in *.
                    typ_to_dtyp_simplify.
                    assumption.
                  }
                  {
                    unfold get_array_cell.
                    rewrite get_logical_block_of_add_logical_block.
                    exists m1.
                    split.
                    -
                      clear - Heqs3.
                      eapply initFSHGlobals_no_overwrite_eq
                        with (k:=memory_next_key m_pre)
                        in Heqs3.
                      eassumption.
                      now rewrite memory_lookup_memory_set_eq.
                    -
                      intros i0 id_v.
                      generalize dependent (MInt64asNT.to_nat i0);
                        intros id IDM0.
                      unfold get_array_cell_mem_block; cbn; f_equal.
                      unfold read_in_mem_block.
                      cbn [sizeof_dtyp].
                      replace
                        (fold_right (λ (dv : dvalue) (acc : list SByte),
                                     serialize_dvalue dv ++ acc)
                                    [] (map DVALUE_Double pdata))
                        with (serialize_dvalue (DVALUE_Vector (map DVALUE_Double pdata)))
                        by reflexivity.
                      simpl_data.
                      replace hdata_pre with l1' in *.
                      2: {
                        rewrite rotateN_add in IPRE.
                        eapply initFSHGlobals_initIRGlobals_rev_data.
                        eapply PRE.
                        eapply IPRE.
                      }
                      clear - IDM0 Heqp Heqp0.
                      replace
                        (MInt64asNT.to_nat
                           {|
                             DynamicValues.Int64.intval := Z.of_nat n';
                             DynamicValues.Int64.intrange := n_ran |})
                        with n'
                        in *
                        by (unfold MInt64asNT.to_nat; cbn; auto using Nat2Z.id).

                      rewrite int64_unsigned_repr_eq.
                      2: {
                        enough (id < n') by lia.
                        eauto using constMemBlock_bound.
                      }
                      erewrite deserialize_vector.
                      reflexivity.
                      rewrite <-IDM0.
                      eapply constList_constMemBlock; eassumption.
                  }
                +++
                  assert (n < length e_pre).
                  {
                    apply nth_error_in in H0.
                    rewrite app_length in H0.
                    cbn in H0.
                    lia.
                  }
                  clear n0.

                  rewrite app_nth_error1 in H0 by assumption.
                  rewrite map_app in H1.
                  rewrite app_nth_error1 in H1 by (rewrite map_length; lia).
                  destruct x as [id | id].
                  2:{
                    apply nth_map_inv in H1.
                    destruct H1 as ((?, ?) & ? & ?).
                    discriminate.
                  }

                  inversion PINV as [[I _ _ _ _ _ _] _].
                  cbn in I.
                  specialize (I _ _ _ _ _ H0 H1).
                  generalize dependent
                             (LBlock a_sz
              (add_all_index (serialize_dvalue (DVALUE_Array (map DVALUE_Double pdata)))
                 a_off a_bytes) a_id).
                  intros lb.

                  assert (forall vptr, g' @ id ≡ Some (DVALUE_Addr vptr) ->
                                  a_ptr ≢ fst vptr).
                  {
                    intros.
                    replace a_ptr with (fst (a_ptr, a_off)) by reflexivity.
                    move AG' at bottom.
                    destruct AG' as [_ NLPA].
                    rewrite firstn_all2 in NLPA by lia.
                    unfold no_llvm_ptr_aliasing in NLPA.
                    destruct ne'.
                    eapply NLPA with (n1:=length pre) (id1:=ID_Global (Name a_nm)).
                    -
                      rewrite nth_error_app2 by lia.
                      rewrite E_PRE_LEN, Nat.sub_diag.
                      reflexivity.
                    -
                      eapply ListNth.nth_error_weaken.
                      eapply H0.
                    -
                      cbn.
                      rewrite map_app.
                      rewrite nth_error_app2
                        by now rewrite map_length.
                      rewrite map_length, Nat.sub_diag.
                      rewrite map_cons.
                      cbn.
                      reflexivity.
                    -
                      cbn.
                      rewrite map_app.
                      eapply ListNth.nth_error_weaken.
                      eapply H1.
                    -
                      clear - H1 H2 GUNIQ E_PRE_LEN.
                      intros C; invc C.
                      unfold list_uniq in GUNIQ.
                      apply nth_map_inv in H1.
                      destruct H1 as ((a_nm', τ') & A & A').
                      invc A'.
                      specialize (GUNIQ n (length pre) (a_nm, τ') (a_nm, DSHPtr int_n)).
                      full_autospecialize GUNIQ; try reflexivity.
                      now apply ListNth.nth_error_weaken.
                      rewrite nth_error_app2 by reflexivity.
                      rewrite Nat.sub_diag.
                      reflexivity.
                      lia.
                    -
                      unfold in_local_or_global_addr.
                      assumption.
                    -
                      unfold in_local_or_global_addr.
                      assumption.
                  }

                  break_match.
                  {
                    unfold in_local_or_global_scalar in *.
                    destruct I as (vptr & τ' & I).
                    exists vptr; exists τ'.
                    destruct I as (TTT & G'ID & R').
                    split; [assumption | split; [assumption |]].
                    unfold read in *.

                    rewrite get_logical_block_of_add_logical_block_neq by now apply H3.
                    now repeat break_match_goal.
                  }
                  {
                    unfold in_local_or_global_scalar in *.
                    destruct I as (vptr & τ' & I).
                    exists vptr; exists τ'.
                    destruct I as (TTT & G'ID & R').
                    split; [assumption | split; [assumption |]].
                    unfold read in *.

                    rewrite get_logical_block_of_add_logical_block_neq by now apply H3.
                    now repeat break_match_goal.
                  }
                  {
                    unfold in_local_or_global_scalar in *.
                    destruct I as (vptr & τ' & I).
                    exists vptr; exists τ'.
                    destruct I as (TTT & DTF & ILG & IDK).
                    split; [assumption | split; [| split; [assumption |]]].
                    -
                      unfold dtyp_fits in *.
                      rewrite get_logical_block_of_add_logical_block_neq by now apply H3.
                      apply DTF.
                    -
                      unfold get_array_cell in *.
                      break_let.
                      rewrite get_logical_block_of_add_logical_block_neq.
                      apply IDK.
                      replace z with (fst vptr) by now subst.
                      apply H3.
                      now subst.
                  }
              ---
                unfold WF_IRState.
                cbn.
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
                eapply initFSHGlobals_no_id_aliasing.
                1:{
                  clear - GUNIQ.
                  rewrite list_cons_app in GUNIQ.
                  rewrite app_assoc in GUNIQ.
                  apply list_uniq_app in GUNIQ.
                  intuition.
                }
                eapply initFSHGlobals_app.
                eassumption.
                unfold initFSHGlobals.
                unfold init_with_data.
                rewrite Heqs2.
                reflexivity.
              ---
                eapply initFSHGlobals_no_dshptr_aliasing.
                eapply initFSHGlobals_app with (post:=[(a_nm, FHCOL.DSHPtr int_n)]).
                eassumption.
                unfold initFSHGlobals.
                unfold init_with_data.
                rewrite Heqs2.
                reflexivity.
              ---
                move AG' at bottom.
                unfold allocated_globals in AG'.
                destruct AG' as [_ NAL].
                rewrite firstn_all2 in NAL by lia.
                rewrite list_cons_app in NAL.
                rewrite app_assoc in NAL.
                unfold no_llvm_ptr_aliasing_cfg, no_llvm_ptr_aliasing.
                cbn; intros.
                eapply NAL; cbn.

                +++ eapply ListNth.nth_error_weaken; eapply H0.
                +++ eapply ListNth.nth_error_weaken; eapply H1.
                +++
                  rewrite list_cons_app.
                  rewrite !map_app.
                  rewrite app_assoc.
                  eapply ListNth.nth_error_weaken.
                  rewrite <-map_app.
                  eassumption.
                +++
                  rewrite list_cons_app.
                  rewrite !map_app.
                  rewrite app_assoc.
                  eapply ListNth.nth_error_weaken.
                  rewrite <-map_app.
                  eassumption.
                +++ eassumption.
                +++ eassumption.
                +++ eassumption.
              ---
                unfold id_allocated.
                intros.
                rename n into n', n0 into n.
                destruct (Nat.eq_dec (length e_pre) n).
                +++
                  subst n.
                  replace (length e_pre) with (0 + length e_pre) in H0 by lia.
                  rewrite ListNth.nth_error_length in H0.
                  cbn in H0.
                  invc H0.
                  apply initFSHGlobals_no_overwrite in Heqs3.
                  rewrite Heqs3.
                  clear - Heqs2.
                  apply mem_block_exists_union.
                  apply initOneFSHGlobal_mem_block_exists in Heqs2.
                  intuition.
                +++
                  rewrite app_nth_error1 in H0
                    by (apply nth_error_in in H0;
                        rewrite app_length in H0;
                        cbn in H0; lia).
                  destruct PINV as [[_ _ _ _ _ A] _].
                  eapply A.
                  eassumption.
              ---
                unfold gamma_bound.
                cbn.
                intros * NTH_L.
                apply nth_map_inv in NTH_L.
                destruct NTH_L as [(a_nm', a_t') [_ C]].
                inv C.
            **
              constructor.
              all: cbn; clear - DI.
              all: unfold fun_declarations_invariant in DI.
              all: intuition.
            **
              (* TODO: prove [anon_declarations_invariant] *)
              admit.
        -- (* initialize [post] *)
          intros.
          cbn in *.
          move IHpost at bottom.

          rewrite <-ListUtil.list_app_first_last.
          destruct u2 as (m'' & (le'', stack'') & g''' & ?).
          repeat break_let.

          dedup_states.

          move LG at bottom.
          rewrite <-ListUtil.list_app_first_last in LG.
          apply initIRGlobals_inr in LG.
          apply initIRGlobals_rev_app_inv in LG.
          destruct LG as (l'' & s'' & g1'' & g2'' & PRE'' & POST'' & G'').

          eapply IHpost; clear IHpost.
          ++
            clear - H0 PINV.
            unfold post_init_invariant' in H0.
            intuition.
          ++
            now rewrite <-app_assoc.
          ++
            instantiate (1:=gdecls1 ++ [TLE_Global tg2]).
            now rewrite <-app_assoc.
          ++
            move PRE at bottom; move Heqs0 at bottom.

            move LX at bottom.
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
            clear - H0 PINV.
            unfold post_init_invariant' in H0.
            replace u1 with (mg, ()) in *.
            assumption.
            now repeat destruct H0.
    + (* initialize yx *)
      unfold post_init_invariant'.

      replace
        (firstn (Datatypes.length globals)
                (e ++
                   [(DSHPtrVal (S (Datatypes.length globals)) o, true);
                    (DSHPtrVal (Datatypes.length globals) i, true)]))
        with e
        in *.
      2: {
        clear - LGE.
        rewrite firstn_app.
        rewrite !LGE, Nat.sub_diag.
        now rewrite firstn_all, app_nil_r.
      }

      replace (firstn (Datatypes.length globals) Γ_globals)
        with Γ_globals
        in *.
      2: {
        dedup_states.
        clear - IR LX.
        pose proof genIR_Γ _ _ _ IR; clear IR.
        cbn in H.

        unfold initXYplaceholders, addVars in LX.
        cbn in LX.
        repeat break_let.
        invc LX.
        cbn.

        apply list_app_eqlen_eq_r in H; [| reflexivity].
        destruct H as [GG _].
        erewrite <-map_length.
        rewrite GG.
        now rewrite firstn_all.
      }

      remember {|
        block_count := block_count;
        local_count := local_count;
        void_count := void_count;
        Γ := Γ_globals |}
        as si.
      remember {|
             block_count := block_count;
             local_count := local_count;
             void_count := void_count;
             Γ := Γ_globals ++ [fake_x; fake_y] |}
        as siyx.


      
      intros.
      move LX at bottom.
      unfold initXYplaceholders, addVars in LX.
      cbn in LX.
      repeat break_let.
      invc LX.
      cbn.

      destruct H0 as [PI [[[AXY AG] DI] U1]].
      subst u1.
      unfold allocated_xy in AXY.
      destruct AXY as (x_ptr & y_ptr & AX & AY & GX & GY & XneqY).

      autorewrite with itree.
      repeat rewrite interp3_bind. 
      rewrite exp_to_L0_Global.
      rewrite subevent_subevent.
      (* the important step 1.1 *)
      rewrite interp3_GR by apply GY.

      autorewrite with itree.
      repeat rewrite interp3_bind. 



      unfold denote_exp; fold denote_exp.
      unfold tfmap, TFunctor_list.
      rewrite !map_monad_map.
      cbn.
      autorewrite with itree.
      rewrite interp3_bind.

      unfold constArray in *.
      repeat break_match_hyp.
      invc Heqp; invc Heqp0.
      rewrite !map_monad_map.
      cbn [fst snd] in *.

      setoid_rewrite map_monad_ret_map with (g1 := UVALUE_Double).
      2: {
        typ_to_dtyp_simplify.
        reflexivity.
      }
      repeat rewrite translate_ret, interp3_ret, !ITree.Eq.Eq.bind_ret_l.

      unfold concretize_or_pick.
      replace (is_concrete (UVALUE_Array (map UVALUE_Double l11)))
        with true.
      2: {
        clear; cbn.
        symmetry; apply forallb_forall.
        intros.
        apply ListUtil.in_map_elim in H.
        destruct H as [d [_ D]].
        now subst.
      }
      cbn.
      rewrite map_monad_map.
      rewrite map_monad_inr_map with (g1:=DVALUE_Double)
        by reflexivity.
      cbn.
      autorewrite with itree.

      
      repeat rewrite interp3_bind. 
      rewrite exp_to_L0_Memory.
      rewrite subevent_subevent.

      copy_apply dtyp_fits_allocated AY;
        rename H0 into AY'.
      copy_apply allocated_get_logical_block AY'.
      destruct H0 as [[y_sz y_bytes y_id] YM0B].
      destruct y_ptr as [y_ptr y_off].
      (* the important step 1.2 *)
      rewrite interp_mcfg_store.
      2: {
        unfold write.
        rewrite YM0B.
        reflexivity.
      }

      autorewrite with itree.
      repeat rewrite interp3_bind. 
      rewrite exp_to_L0_Global.
      rewrite subevent_subevent.
      (* the important step 2.1 *)
      rewrite interp3_GR by apply GX.

      autorewrite with itree.
      repeat rewrite interp3_bind. 

      unfold denote_exp; fold denote_exp.

      setoid_rewrite map_monad_ret_map with (g1 := UVALUE_Double).
      2: {
        typ_to_dtyp_simplify.
        reflexivity.
      }
      repeat rewrite translate_ret, interp3_ret, !ITree.Eq.Eq.bind_ret_l.

      (* TODO: this is a simple lemma, see multiple uses above *)
      replace (is_concrete (UVALUE_Array (map UVALUE_Double l8)))
        with true.
      2: {
        clear; cbn.
        symmetry; apply forallb_forall.
        intros.
        apply ListUtil.in_map_elim in H.
        destruct H as [d [_ D]].
        now subst.
      }
      cbn.
      rewrite map_monad_map.
      rewrite map_monad_inr_map with (g1:=DVALUE_Double)
        by reflexivity.
      cbn.
      autorewrite with itree.

      repeat rewrite interp3_bind. 
      rewrite exp_to_L0_Memory.
      rewrite subevent_subevent.

      copy_apply dtyp_fits_allocated AX;
        rename H0 into AX'.
      copy_apply allocated_get_logical_block AX'.
      rename x_id into x_id'.
      destruct H0 as [[x_sz x_bytes x_id] XM0B].
      destruct x_ptr as [x_ptr x_off].
      (* the important step 2.2 *)
      rewrite interp_mcfg_store.
      2: {
        unfold write.
        rewrite get_logical_block_of_add_logical_block_neq
          by (cbn [fst snd] in *; congruence).
        rewrite XM0B.
        reflexivity.
      }
      
      autorewrite with itree.
      rewrite interp3_ret.
      apply eutt_Ret.

      destruct PI as [[MEM_INV
                       WF
                       NO_ID_ALIAS
                       NO_DS_ALIAS
                       NO_LL_ALIAS
                       ID_ALLOC
                       GAMMA_BOUND] DECL_INV].
      dedup_states.
      simpl_data.
      cbn in *.

      (* prepare some general hyps *)
      pose proof genIR_Γ _ _ _ IR.
      cbn in H0.
      apply list_app_eqlen_eq_r in H0; [| reflexivity].
      destruct H0 as [GG XYXY].
      invc XYXY.
      cbn in *.
      (* pointers in e are below x, y *)
      pose proof initFSHGlobals_addr_bound _ _ _ G as EB.
      cbn in EB.

      assert (IEL : length (map IR_of_global globals) ≡ length e)
        by (now rewrite map_length).


      assert (XUNIQ :
                ∀ n id τ' ptr,
                  nth_error (map IR_of_global globals) n
                  ≡ Some (ID_Global id, τ') →
                  g0 @ id ≡ Some (DVALUE_Addr ptr) ->
                  x_ptr ≢ fst ptr).
      {
        clear - DI GX.
        destruct DI as [_ [GUNIQ _]].
        intros * N PTR; intros C.
        replace x_ptr with (fst (x_ptr, x_off)) in C by reflexivity.
        eapply GUNIQ in C.
        2,3: eassumption.
        subst id.
        clear - N.
        apply nth_map_inv in N.
        destruct N as [(a_nm, a_t) [_ C]].
        inv C.
      }
      assert (YUNIQ :
                ∀ n id τ' ptr,
                  nth_error (map IR_of_global globals) n
                  ≡ Some (ID_Global id, τ') →
                  g0 @ id ≡ Some (DVALUE_Addr ptr) ->
                  y_ptr ≢ fst ptr).
      {
        clear - DI GY.
        destruct DI as [_ [GUNIQ _]].
        intros * N PTR; intros C.
        replace y_ptr with (fst (y_ptr, y_off)) in C by reflexivity.
        eapply GUNIQ in C.
        2,3: eassumption.
        subst id.
        clear - N.
        apply nth_map_inv in N.
        destruct N as [(a_nm, a_t) [_ C]].
        inv C.
      }
      

      constructor.
      *
        constructor.
        --
          unfold memory_invariant.
          cbn.
          intros n * NE NG.
          apply nth_error_in_app in NE.
          destruct NE as [[L EL] | [R ER]].
          ++
            rewrite nth_error_app1
              in NG
              by (rewrite map_length; lia).
            move MEM_INV at bottom.
            specialize (MEM_INV n v b0 τ x EL NG).
            break_match.
            **
              unfold in_local_or_global_scalar in *.
              break_match; [| assumption].
              destruct MEM_INV as (ptr & τ' & T' & G0ID & READ).
              exists ptr, τ'.
              split; [assumption |].
              split; [assumption |].
              unfold read in *.
              rewrite get_logical_block_of_add_logical_block_neq.
              rewrite get_logical_block_of_add_logical_block_neq.
              assumption.
              eapply YUNIQ; eassumption.
              eapply XUNIQ; eassumption.
            **
              unfold in_local_or_global_scalar in *.
              break_match; [| assumption].
              destruct MEM_INV as (ptr & τ' & T' & G0ID & READ).
              exists ptr, τ'.
              split; [assumption |].
              split; [assumption |].
              unfold read in *.
              rewrite get_logical_block_of_add_logical_block_neq.
              rewrite get_logical_block_of_add_logical_block_neq.
              assumption.
              eapply YUNIQ; eassumption.
              eapply XUNIQ; eassumption.
            **
              destruct MEM_INV as (ptr & τ' & T' & TF & IPTR & I).
              exists ptr, τ'.
              split; [assumption |].
              split.
              ---
                eapply dtyp_fits_add_logical_block_key_neq.
                2: {
                  clear - XUNIQ NG IPTR.
                  copy_apply nth_map_inv NG.
                  destruct H as [(a_nm, a_t) [_ A]].
                  invc A; cbn in *.
                  eapply XUNIQ.
                  eassumption.
                  eassumption.
                }
                eapply dtyp_fits_add_logical_block_key_neq.
                2: {
                  clear - YUNIQ NG IPTR.
                  copy_apply nth_map_inv NG.
                  destruct H as [(a_nm, a_t) [_ A]].
                  invc A; cbn in *.
                  eapply YUNIQ.
                  eassumption.
                  eassumption.
                }
                assumption.
              ---
                split; [assumption |].
                intros B.
                specialize (I B).
                destruct I as (a_mg & A_MG & I).
                exists a_mg.
                split.
                +++
                  clear - EB EL A_MG.
                  apply EB in EL.
                  enough
                    (memory_lookup
                       (memory_set
                          (memory_set mg (S (length globals)) mo)
                          (length globals) mi) a ≡ Some a_mg)
                    by assumption.
                  rewrite !memory_lookup_memory_set_neq by lia.
                  assumption.
                +++
                  intros i' v' V'.
                  specialize (I i' v' V').
                  unfold get_array_cell in *.
                  break_let.
                  replace z with (fst (z, z0)) by reflexivity.
                  erewrite get_logical_block_of_add_logical_block_neq.
                  2: {
                    clear - XUNIQ NG IPTR.
                    copy_apply nth_map_inv NG.
                    destruct H as [(a_nm, a_t) [_ A]].
                    invc A.
                    eapply XUNIQ.
                    eassumption.
                    eassumption.
                  }
                  erewrite get_logical_block_of_add_logical_block_neq.
                  2: {
                    clear - YUNIQ NG IPTR.
                    copy_apply nth_map_inv NG.
                    destruct H as [(a_nm, a_t) [_ A]].
                    invc A.
                    eapply YUNIQ.
                    eassumption.
                    eassumption.
                  }
                  assumption.
          ++
            rewrite nth_error_app2
              in NG
              by (rewrite map_length; lia).
            apply nth_error_in_list_of_two in ER.
            rewrite IEL in NG.
            destruct ER as [[N V] | [N V]];
              rewrite N in NG; cbn in NG.
            **
              invc V; invc NG.
              exists (y_ptr, y_off).
              exists (TYPE_Array (Z.to_N (Int64.intval o)) TYPE_Double).
              split; [reflexivity |].
              split.
              ---
                unfold dtyp_fits.
                rewrite get_logical_block_of_add_logical_block_neq
                  by (cbn; assumption).
                rewrite get_logical_block_of_add_logical_block.
                do 3 eexists.
                split.
                reflexivity.

                destruct AY as (ysz & ybt & ybid & YB & YSZ).
                cbn [fst] in *.
                rewrite YM0B in YB.
                invc YB.
                assumption.
              ---
                split; [cbn; assumption |].
                intros _.
                exists mo.
                split.
                +++
                  enough
                    (memory_lookup
                       (memory_set
                          (memory_set mg (S (length globals)) mo)
                          (length globals) mi) (S (length globals)) ≡ Some mo)
                    by assumption.
                  rewrite memory_lookup_memory_set_neq by lia.
                  rewrite memory_lookup_memory_set_eq.
                  reflexivity.
                +++
                  intros i' v' V'.
                  rename l11 into pdata.
                  unfold get_array_cell.
                  erewrite get_logical_block_of_add_logical_block_neq by assumption.
                  erewrite get_logical_block_of_add_logical_block.

                  generalize dependent (MInt64asNT.to_nat i').
                  intros n' V'.
                  unfold get_array_cell_mem_block; cbn; f_equal.
                  unfold read_in_mem_block.
                  cbn [sizeof_dtyp].
                  replace
                    (fold_right (λ (dv : dvalue) (acc : list SByte),
                                 serialize_dvalue dv ++ acc)
                                [] (map DVALUE_Double pdata))
                    with (serialize_dvalue (DVALUE_Vector (map DVALUE_Double pdata)))
                    by reflexivity.
                  clear - Co V' Heqp2.
                  rewrite int64_unsigned_repr_eq.
                  2: {
                    assert (n' < (MInt64asNT.to_nat o))
                      by eauto using constMemBlock_bound.
                    split; [lia |].
                    eauto using Int64_to_nat_modulus.
                  }
                  erewrite deserialize_vector.
                  reflexivity.
                  rewrite <-V'.
                  eapply constList_constMemBlock; eassumption.
            **
              invc V; invc NG.
              exists (x_ptr, x_off).
              exists (TYPE_Array (Z.to_N (Int64.intval i)) TYPE_Double).
              split; [reflexivity |]. (* array vs array pointer *)
              split.
              ---
                unfold dtyp_fits.
                rewrite get_logical_block_of_add_logical_block.
                do 3 eexists.
                split.
                reflexivity.

                destruct AX as (xsz & xbt & xbid & XB & XSZ).
                cbn [fst] in *.
                rewrite XM0B in XB.
                invc XB.
                assumption.
              ---
                split; [cbn; assumption |].
                intros _.
                exists mi.
                split.
                +++
                  enough
                    (memory_lookup
                       (memory_set
                          (memory_set mg (S (length globals)) mo)
                          (length globals) mi) (length globals) ≡ Some mi)
                    by assumption.
                  rewrite memory_lookup_memory_set_eq.
                  reflexivity.
                +++
                  intros i' v' V'.
                  rename l8 into pdata.
                  unfold get_array_cell.
                  erewrite get_logical_block_of_add_logical_block.

                  generalize dependent (MInt64asNT.to_nat i').
                  intros n' V'.
                  unfold get_array_cell_mem_block; cbn; f_equal.
                  unfold read_in_mem_block.
                  cbn [sizeof_dtyp].
                  replace
                    (fold_right (λ (dv : dvalue) (acc : list SByte),
                                 serialize_dvalue dv ++ acc)
                                [] (map DVALUE_Double pdata))
                    with (serialize_dvalue (DVALUE_Vector (map DVALUE_Double pdata)))
                    by reflexivity.
                  clear - Ci V' Heqp1.
                  rewrite int64_unsigned_repr_eq.
                  2: {
                    assert (n' < (MInt64asNT.to_nat i))
                      by eauto using constMemBlock_bound.
                    split; [lia |].
                    eauto using Int64_to_nat_modulus.
                  }
                  erewrite deserialize_vector.
                  reflexivity.
                  rewrite <-V'.
                  eapply constList_constMemBlock; eassumption.
        -- (* WF IRSTATE *)
          clear - IEL LGE EB WF.
          unfold WF_IRState, evalContext_typechecks.
          cbn.
          intros ? n * N.
          apply nth_error_in_app in N.
          destruct N as [[L EL] | [R ER]].
          ++
            rewrite nth_error_app1
              by (rewrite map_length; lia).
            eapply WF.
            eassumption.
          ++
            rewrite nth_error_app2
              by (rewrite map_length; lia).
            apply nth_error_in_list_of_two in ER.
            destruct ER as [[N ER] | [N ER]]; invc ER.
            **
              replace (n - length (map IR_of_global globals))
                with 0
                by (rewrite map_length; lia).
              cbn.
              eexists.
              repeat f_equal.
              cbn.
              reflexivity.
            **
              replace (n - length (map IR_of_global globals))
                with 1
                by (rewrite map_length; lia).
              cbn.
              eexists.
              repeat f_equal.
              cbn.
              reflexivity.
        -- (* NO ID ALIASING *)
          clear - LGE IEL EB NO_ID_ALIAS.
          unfold no_id_aliasing in *.
          cbn in *.
          intros n1 n2 * N1 N2.
          apply nth_error_in_app in N1.
          apply nth_error_in_app in N2.
          destruct N1 as [[L1 EL1] | [R1 ER1]],
                   N2 as [[L2 EL2] | [R2 ER2]].
          ++
            rewrite !nth_error_app1
              by (rewrite map_length; lia).
            eapply NO_ID_ALIAS;
              eassumption.
          ++
            rewrite nth_error_app1
              by (rewrite map_length; lia).
            rewrite nth_error_app2
              by (rewrite map_length; lia).
            intros C1 C2; exfalso; clear - C1 C2.
            apply nth_error_in_list_of_two in C2.
            apply nth_map_inv in C1.
            destruct C1 as [(n, t) [N1 A1]].
            invc A1.
            destruct C2 as [[_ C] | [_ C]];
              invc C.
          ++
            rewrite nth_error_app2
              by (rewrite map_length; lia).
            rewrite nth_error_app1
              by (rewrite map_length; lia).
            intros C1 C2; exfalso; clear - C1 C2.
            apply nth_error_in_list_of_two in C1.
            apply nth_map_inv in C2.
            destruct C2 as [(n, t) [N2 A2]].
            invc A2.
            destruct C1 as [[_ C] | [_ C]];
              invc C.
          ++
            rewrite !nth_error_app2
              by (rewrite map_length; lia).
            intros N1 N2.
            apply nth_error_in_list_of_two in N1.
            apply nth_error_in_list_of_two in N2.
            destruct N1 as [[N1 I1] | [N1 I1]]; invc I1;
            destruct N2 as [[N2 I2] | [N2 I2]]; invc I2.
            all: lia.
        -- (* NO DSH PTR ALIASING *)
          clear - EB NO_DS_ALIAS.
          unfold no_dshptr_aliasing in *.
          intros n1 n2 * N1 N2.
          apply nth_error_in_app in N1.
          apply nth_error_in_app in N2.
          destruct N1 as [[L1 EL1] | [R1 ER1]],
                   N2 as [[L2 EL2] | [R2 ER2]].
          ++
            eapply NO_DS_ALIAS; eassumption.
          ++
            apply EB in EL1.
            apply nth_error_in_list_of_two in ER2.
            destruct ER2 as [[N2 ER2] | [N2 ER2]]; invc ER2.
            all: lia.
          ++
            apply EB in EL2.
            apply nth_error_in_list_of_two in ER1.
            destruct ER1 as [[N1 ER1] | [N1 ER1]]; invc ER1.
            all: lia.
          ++
            apply nth_error_in_list_of_two in ER1.
            apply nth_error_in_list_of_two in ER2.
            destruct ER1 as [[N1 ER1] | [N1 ER1]]; invc ER1;
              destruct ER2 as [[N2 ER2] | [N2 ER2]]; invc ER2.
            all: lia.
        -- (* NO LLVM PTR ALIASING *)
          unfold no_llvm_ptr_aliasing_cfg, no_llvm_ptr_aliasing.
          cbn.
          intros ? ? ? ? n1 n2 * N1 N2.
          apply nth_error_in_app in N1.
          apply nth_error_in_app in N2.
          destruct N1 as [[L1 EL1] | [R1 ER1]],
                   N2 as [[L2 EL2] | [R2 ER2]].
          ++
            rewrite !nth_error_app1
              by (rewrite map_length; lia).
            eapply NO_LL_ALIAS;
              eassumption.
          ++ (* copy 1 *)
            rewrite nth_error_app1
              by (rewrite map_length; lia).
            rewrite nth_error_app2
              by (rewrite map_length; lia).
            apply nth_error_in_list_of_two in ER2.
            destruct ER2 as [[N2 ER2] | [N2 ER2]]; invc ER2.
            ** (* copy 1.1 *)
              replace (n2 - length (map IR_of_global globals))
                with 0
                in * 
                by lia.
              cbn.
              intros I1 I2 _ G1 G0.
              invc I2.
              move GY after G0; move GX after G0.
              unfold in_local_or_global_addr, in_global_addr in *.
              replace ptrv2 with (y_ptr, y_off) in * by congruence.
              apply nth_map_inv in I1.
              destruct I1 as [(n, t) [N1 ON1]].
              invc ON1.
              clear - G0 G1 DI.
              intros C; symmetry in C.
              destruct DI as [_ [GUNIQ _]].
              eapply GUNIQ in C.
              2,3: eassumption.
              invc C.
            ** (* copy 1.2 *)
              replace (n2 - length (map IR_of_global globals))
                with 1
                in * 
                by lia.
              cbn.
              intros I1 I2 _ G1 G0.
              invc I2.
              move GY after G0; move GX after G0.
              unfold in_local_or_global_addr, in_global_addr in *.
              replace ptrv2 with (x_ptr, x_off) in * by congruence.
              apply nth_map_inv in I1.
              destruct I1 as [(n, t) [N1 ON1]].
              invc ON1.
              clear - G0 G1 DI.
              intros C; symmetry in C.
              destruct DI as [_ [GUNIQ _]].
              eapply GUNIQ in C.
              2,3: eassumption.
              invc C.
          ++ (* copy 2 *)
            rewrite nth_error_app2
              by (rewrite map_length; lia).
            rewrite nth_error_app1
              by (rewrite map_length; lia).
            apply nth_error_in_list_of_two in ER1.
            destruct ER1 as [[N1 ER1] | [N1 ER1]]; invc ER1.
            ** (* copy 2.1 *)
              replace (n1 - length (map IR_of_global globals))
                with 0
                in * 
                by lia.
              cbn.
              intros I1 I2 _ G1 G0.
              invc I1.
              move GY after G0; move GX after G0.
              unfold in_local_or_global_addr, in_global_addr in *.
              replace ptrv1 with (y_ptr, y_off) in * by congruence.
              apply nth_map_inv in I2.
              destruct I2 as [(n, t) [N2 ON2]].
              invc ON2.
              clear - G0 G1 DI.
              intros C; symmetry in C.
              destruct DI as [_ [GUNIQ _]].
              eapply GUNIQ in C.
              2,3: eassumption.
              invc C.
            ** (* copy 2.2 *)
              replace (n1 - length (map IR_of_global globals))
                with 1
                in * 
                by lia.
              cbn.
              intros I1 I2 _ G1 G0.
              invc I1.
              move GY after G0; move GX after G0.
              unfold in_local_or_global_addr, in_global_addr in *.
              replace ptrv1 with (x_ptr, x_off) in * by congruence.
              apply nth_map_inv in I2.
              destruct I2 as [(n, t) [N2 ON2]].
              invc ON2.
              clear - G0 G1 DI.
              intros C; symmetry in C.
              destruct DI as [_ [GUNIQ _]].
              eapply GUNIQ in C.
              2,3: eassumption.
              invc C.
          ++
            rewrite !nth_error_app2
              by (rewrite map_length; lia).
            intros N1 N2.
            apply nth_error_in_list_of_two in N1.
            apply nth_error_in_list_of_two in N2.
            destruct N1 as [[N1 I1] | [N1 I1]]; invc I1;
            destruct N2 as [[N2 I2] | [N2 I2]]; invc I2.
            all: try congruence.
            all: intros _.
            **
              intros G1 G0.
              move GY after G0; move GX after G0.
              unfold in_local_or_global_addr, in_global_addr in *.
              replace ptrv2 with (x_ptr, x_off) in * by congruence.
              replace ptrv1 with (y_ptr, y_off) in * by congruence.
              cbn.
              intros C.
              congruence.
            **
              intros G1 G0.
              move GY after G0; move GX after G0.
              unfold in_local_or_global_addr, in_global_addr in *.
              replace ptrv1 with (x_ptr, x_off) in * by congruence.
              replace ptrv2 with (y_ptr, y_off) in * by congruence.
              cbn.
              intros C.
              congruence.
        -- (* ID ALLOCATED *)
          unfold id_allocated.
          intros n * N.
          apply nth_error_in_app in N.
          destruct N as [[L EL] | [R ER]].
          ++
            do 2 apply mem_block_exists_memory_set.
            eapply ID_ALLOC.
            eassumption.
          ++
            apply nth_error_in_list_of_two in ER.
            destruct ER as [[N ER] | [N ER]]; invc ER.
            **
              apply mem_block_exists_memory_set.
              apply mem_block_exists_memory_set_eq.
              reflexivity.
            **
              apply mem_block_exists_memory_set_eq.
              reflexivity.
        --
          clear - GAMMA_BOUND.
          unfold gamma_bound in *.
          unfold LidBound.lid_bound, VariableBinding.state_bound in *.
          cbn in *.
          intros * N.
          apply nth_error_in_app in N.
          destruct N as [[N NTH] | [N NTH]].
          ++
            eapply GAMMA_BOUND.
            eassumption.
          ++
            exfalso.
            apply nth_error_in_list_of_two in NTH.
            destruct NTH as [[_ C] | [_ C]];
              inv C.
      *
        apply DECL_INV.
Admitted.

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

(*
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

Lemma initOneIRGlobal_no_type_defs :
  forall l a σ σ' l' t,
    initOneIRGlobal l a σ ≡ inr (σ', (l', t)) ->
    type_defs_of typ t ≡ [].
Proof.
  unfold initOneIRGlobal; cbn; intros; simp; cbn in *; auto.
Qed.

Lemma init_with_data_initOneIRGlobal_no_type_defs:
  forall g l x σ σ' b t,
    init_with_data initOneIRGlobal x l g σ ≡ inr (σ', (b, t)) ->
    m_type_defs (mcfg_of_modul (modul_of_toplevel_entities t)) ≡ [].
Proof.
  induction g as [| ? g IH]; intros; cbn in *; [simp; cbn; auto |].
  simp.
  copy_apply IH Heqs2.
  rewrite list_cons_app.
  cbn.
  erewrite IH, initOneIRGlobal_no_type_defs; eauto.
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
  copy_apply IH Heqs2.
  rewrite list_cons_app.
  rewrite mcfg_of_tle_app.
  rewrite m_definitions_app.
  erewrite initOneIRGlobal_no_definitions; eauto.
  cbn.
  erewrite initOneIRGlobal_no_type_defs; eauto.
  erewrite init_with_data_initOneIRGlobal_no_type_defs; eauto.
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
Hint Rewrite interp3_bind : local.
Hint Rewrite interp3_ret : local.

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
(*     rewrite interp3_bind. *)
(*     autorewrite with local. *)

(*     apply eutt_clo_bind. *)


(*     simpl mcfg_of_tle. *)
(*     simpl m_definitions. *)
(*     simpl. *)
(*     Set Printing . *)
(*     rewrite interp3_bind. *)
    
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
    (*     rewrite interp3_bind, translate_bind. *)
    (*     match goal with *)
    (*     | ?t ≈ _ => assert (t ≈ ITree.bind (lift_sem_to_mcfg (fun p =>  *)


    (* setoid_rewrite bind_bind. *)
    (*   unfold translate_E_vellvm_mcfg. *)
    (* setoid_rewrite (interp3_bind defined_intrinsics . *)

    (* unfold lift_sem_to_mcfg. *)
    (* break_match_goal. *)
    (* { *)
    (*   unfold semantics_llvm_mcfg, model_to_L3, denote_vellvm_init, denote_vellvm. *)
    (*   simpl bind. *)
    (*   unfold translate_E_vellvm_mcfg. *)
    (*   rewrite interp3_bind, translate_bind. *)

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
    (* } *)



    (*         unfold global_YX,constArray in EQ1. *)
Abort.

*)
