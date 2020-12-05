Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.
Require Import Helix.LLVMGen.Correctness_MExpr.
Require Import Helix.LLVMGen.IdLemmas.
Require Import Helix.LLVMGen.StateCounters.
Require Import Helix.LLVMGen.VariableBinding.
Require Import Helix.LLVMGen.BidBound.
Require Import Helix.LLVMGen.LidBound.
Require Import Helix.LLVMGen.StateCounters.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Global Opaque resolve_PVar.
Opaque incBlockNamed.
Opaque incVoid.
Opaque incLocal.

Axiom int_eq_inv: forall a b, Int64.intval a ≡ Int64.intval b -> a ≡ b.

Arguments add_comment /.
Arguments add_comments /.
Lemma wf_ocfg_bid_singleton : forall {T} (b : _ T), wf_ocfg_bid [b].
Proof.
  intros.
  red.
  eapply Coqlib.list_norepet_cons; eauto.
  eapply Coqlib.list_norepet_nil.
Qed.

Lemma wf_ocfg_bid_cons' : forall {T} (b : _ T) bks,
    ¬ In (blk_id b) (map blk_id bks) ->
    wf_ocfg_bid bks ->
    wf_ocfg_bid (b :: bks).
Proof.
  intros.
  eapply Coqlib.list_norepet_cons; eauto.
Qed.

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

(* This establishes that the generated code does not contain any two blocks with the same id.
   The proof is extremely messy, and still has some admits, but conceptually is shouldn't be hard.
 *)
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
                                             Γ := (ID_Local (Name ("Loop_i" @@ string_of_nat (local_count i))), TYPE_I 64) :: Γ i |}); reflexivity.
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
      - unfold inputs in H.

        rewrite blk_id_map_convert_typ in H.

        eapply Forall_forall in H0; eauto.
        eapply bid_bound_between_bound_earlier in H0.

        eapply bid_bound_name in H0; [lia | solve_prefix].
      - cbn in H0. destruct H0; inversion H0.
    }

    (* TODO: Automate this... *)
    eapply wf_ocfg_bid_cons'.
    { cbn.
      intuition.

      rewrite map_app in H0.
      eapply in_app_or in H0.
      destruct H0.
      - unfold inputs in H.

        rewrite blk_id_map_convert_typ in H.

        eapply Forall_forall in H0; eauto.
        eapply bid_bound_between_bound_earlier in H0.

        eapply bid_bound_name in H0; [lia | solve_prefix].
      - cbn in H0. destruct H0; inversion H0.
    }

    unfold wf_ocfg_bid.
    rewrite map_app. cbn.
    apply Coqlib.list_norepet_append; eauto.

    { constructor.
      intros CONTRA; inv CONTRA.
      constructor.
    }

    unfold Coqlib.list_disjoint.
    intros x y H0 H1.

    cbn in H1. destruct H1; inv H1.
    
    unfold inputs in H.
    rewrite blk_id_map_convert_typ in H.

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
                            TYPE_Pointer (TYPE_Array (Int64.intval size) TYPE_Double)) :: Γ1 |}
                    (Name (x @@ string_of_nat bid))).
    {
      do 2 red.
      exists x.
      exists {|
          block_count := bid;
          local_count := S lid1;
          void_count := void1;
          Γ := (ID_Local (Name ("a" @@ string_of_nat lid1)),
                TYPE_Pointer (TYPE_Array (Int64.intval size) TYPE_Double)) :: Γ1 |}.
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
    unfold inputs in GEN.
    rewrite blk_id_map_convert_typ in GEN.

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
    unfold inputs in *.
    rewrite blk_id_map_convert_typ in *.

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
Opaque incBlockNamed.

Section GenIR.

  (* The result is a branch *)
  Definition branches (to : block_id) (mh : memoryH * ()) (c : config_cfg_T (block_id * block_id + uvalue)) : Prop :=
    match c with
    | (m,(l,(g,res))) => exists from, res ≡ inl (from, to)
    end.

  Hint Resolve state_invariant_incBlockNamed : state_invariant.
  Hint Resolve state_invariant_incLocal : state_invariant.
  Hint Resolve state_invariant_incVoid : state_invariant.

  Tactic Notation "state_inv_auto" := eauto with state_invariant.

  Lemma genIR_Context:
    ∀ (op : DSHOperator) (s1 s2 : IRState) (nextblock b : block_id) (bk_op : list (LLVMAst.block typ)),
      genIR op nextblock s1 ≡ inr (s2, (b, bk_op)) →
      Γ s1 ≡ Γ s2.
  Proof.
    induction op;
      intros s1 s2 nextblock b bk_op H;
      cbn in H; simp;
        repeat
          (match goal with
           | H : ErrorWithState.err2errS (MInt64asNT.from_nat ?n) ?s1 ≡ inr (?s2, _) |- _ =>
             destruct (MInt64asNT.from_nat n); inversion H; subst
           | H: _ :: Γ ?s1 ≡ Γ ?s2,
                R: Γ ?s2 ≡ _ |- _ =>
             rewrite <- H in R; inversion R; subst
           | H: _ :: _ :: Γ ?s1 ≡ Γ ?s2,
                R: Γ ?s2 ≡ _ |- _ =>
             rewrite <- H in R; inversion R; subst
           | H: _ :: _ :: _ :: Γ ?s1 ≡ Γ ?s2,
                R: Γ ?s2 ≡ _ |- _ =>
             rewrite <- H in R; inversion R; subst
           | H: inl _ ≡ inr _ |- _ =>
             inversion H
           | H: inr (?i1, Γ ?s1) ≡ inr (?i2, Γ ?s2) |- _ =>
             inversion H; clear H
           | RES : resolve_PVar ?p ?s1 ≡ inr (?s2, ?x) |- _ =>
             rewrite <- (@resolve_PVar_state p s1 s2 x RES) in *
           | H: incBlockNamed _ _ ≡ inr _ |- _ =>
             apply incBlockNamed_Γ in H
           | H: incLocal _ ≡ inr _ |- _ =>
             apply incLocal_Γ in H
           | H: incVoid _ ≡ inr _ |- _ =>
             apply incVoid_Γ in H
           | GEN: genNExpr _ _ ≡ inr _ |- _ =>
             apply genNExpr_context in GEN; cbn in GEN; inversion GEN; subst
           | GEN: genMExpr _ _ ≡ inr _ |- _ =>
             apply genMExpr_context in GEN; cbn in GEN; inversion GEN; subst
           | GEN: genAExpr _ _ ≡ inr _ |- _ =>
             apply genAExpr_context in GEN; cbn in GEN; inversion GEN; subst
           | GEN : genIR ?op ?b ?s1 ≡ inr _ |- _ =>
             apply IHop in GEN; cbn in GEN; eauto
           end; cbn in *; subst);
        subst_contexts;
        auto.
    - inversion Heqs; subst.
      apply incBlockNamed_Γ in Heqs1.
      subst_contexts.
      rewrite <- Heqs0 in Heql1.
      inversion Heql1.
      reflexivity.
    - eapply IHop1 in Heqs2; eauto.
      eapply IHop2 in Heqs0; eauto.
      subst_contexts.
      reflexivity.
  Qed.

  Hint Resolve genIR_Context  : helix_context.

  (* TODO: Move *)
  Lemma add_comment_eutt :
    forall comments bks ids,
      denote_ocfg (convert_typ [] (add_comment bks comments)) ids ≈ denote_ocfg (convert_typ [] bks) ids.
  Proof.
    intros comments bks ids.
    induction bks.
    - cbn. reflexivity.
    - cbn.
      destruct ids as (bid_from, bid_src); cbn.
      match goal with
      | |- context[denote_ocfg ?bks (_, ?bid_src)] =>
        destruct (find_block bks bid_src) eqn:FIND
      end.
  Admitted.

  (* TODO: Move *)
  (* Could probably have something more general... *)
  Lemma add_comments_eutt :
    forall bk comments bids,
      denote_ocfg
        [fmap (typ_to_dtyp [ ]) (add_comments bk comments)] bids ≈ denote_ocfg [fmap (typ_to_dtyp [ ]) bk] bids.
  Proof.
    intros bk comments bids.
  Admitted.

  (* TODO: Move *)
  Lemma convert_typ_block_app : forall (a b : list (LLVMAst.block typ)) env, (convert_typ env (a ++ b) ≡ convert_typ env a ++ convert_typ env b)%list.
  Proof.
    induction a as [| [] a IH]; cbn; intros; auto.
    rewrite IH; reflexivity.
  Qed.

  Lemma assert_NT_lt_success :
    forall {s1 s2 x y v},
      assert_NT_lt s1 x y ≡ inr v ->
      assert_NT_lt s2 x y ≡ inr v.
  Proof.
    intros s1 s2 x y v H.
    unfold assert_NT_lt in *.
    destruct ((MInt64asNT.to_nat x <? MInt64asNT.to_nat y)%nat); inversion H.
    cbn in *. subst.
    auto.
  Qed.

  Infix "⊍" := Coqlib.list_disjoint (at level 60).
  (* TODO: move, add a file for disjoint list stuff? *)
  Lemma Forall_disjoint :
    forall {A} (l1 l2 : list A) (P1 P2 : A -> Prop),
      Forall P1 l1 ->
      Forall P2 l2 ->
      (forall x, P1 x -> ~(P2 x)) ->
      l1 ⊍ l2.
  Proof.
    induction l1;
      intros l2 P1 P2 L1 L2 P1NP2.
    - intros ? ? CONTRA. inversion CONTRA.
    - apply Coqlib.list_disjoint_cons_l.
      + eapply IHl1; eauto using Forall_inv_tail.
      + apply Forall_inv in L1.
        apply P1NP2 in L1.
        intros IN.
        eapply Forall_forall in L2; eauto.
  Qed.

  (* Import ProofMode. *)
  Notation "'gep' τ e" := (OP_GetElementPtr τ e) (at level 10, only printing).
  Notation "'double'" := (DTYPE_Double) (at level 10, only printing).
  Notation "'arr'" := (DTYPE_Array) (at level 10, only printing).
  Notation "'to_nat'" := (MInt64asNT.to_nat) (only printing).

 
  (* Lemma state_invariant_sub_alist: *)
  (*   forall σ s mH mV l1 l2 g, *)
  (*     l1 ⊑ l2 -> *)
  (*     state_invariant σ s mH (mV,(l1,g)) -> *)
  (*     state_invariant σ s mH (mV,(l2,g)).  *)
  (* Proof. *)
  (*   intros * SUB INV; inv INV. *)
  (*   split; auto. *)
  (*   cbn; intros * LUH LUV. *)
  (*   eapply mem_is_inv in LUH; eapply LUH in LUV; clear mem_is_inv LUH. *)
  (*   destruct v, x; cbn in *; auto. *)
  (*   - apply SUB in LUV; auto. *)
  (*   - apply SUB in LUV; auto. *)
  (*   - destruct LUV as (? & SUC & MLU & ? & ? & LU & ?); *)
  (*       do 2 eexists; repeat split; eauto. *)
  (*     apply SUB in LU; auto. *)
  (*   - cbn in *. *)
  (* Qed. *)

  Import AlistNotations.
  Definition freshness (s1 s2 : IRState) (l1 : local_env) : local_env -> Prop :=
    fun l2 =>
      l1 ⊑ l2 /\
      forall id v,
        alist_In id l2 v ->
        ~ alist_In id l1 v ->
        lid_bound_between s1 s2 id.

  Lemma freshness_ext : forall s1 s2 l1 l2,
      freshness s1 s2 l1 l2 ->
      l1 ⊑ l2.
  Proof.
    intros * FRESH; apply FRESH.
  Qed.

  Lemma state_invariant_Γ :
    forall σ s1 s2 memH stV,
      state_invariant σ s1 memH stV ->
      Γ s2 ≡ Γ s1 ->
      state_invariant σ s2 memH stV.
  Proof.
    intros * INV EQ; inv INV.
    split; cbn; eauto.
    - red; rewrite EQ; apply mem_is_inv.
    - red. rewrite EQ; apply IRState_is_WF.
    - eapply no_id_aliasing_gamma; eauto.
    - destruct stV as (? & ? & ?); cbn in *; eapply no_llvm_ptr_aliasing_gamma; eauto.
  Qed.

  Lemma state_invariant_escape_scope : forall σ v x s1 s2 stH stV,
      Γ s1 ≡ x :: Γ s2 ->
      state_invariant (v::σ) s1 stH stV ->
      state_invariant σ s2 stH stV.
  Proof.
    intros * EQ [MEM WF ALIAS1 ALIAS2 ALIAS3].
    destruct stV as (? & ? & ?).
    split.
    - red; intros * LU1 LU2.
      red in MEM.
      specialize (MEM (S n)).
      rewrite EQ, 2nth_error_Sn in MEM.
      specialize (MEM _ _ _ LU1 LU2).
      destruct v0; cbn; auto.
    - repeat intro.
      do 2 red in WF.
      edestruct WF with (n := S n) as (?id & LU).
      rewrite nth_error_Sn;eauto.
      exists id.
      rewrite EQ in LU.
      rewrite nth_error_Sn in LU;eauto.

    - red; intros * LU1 LU2.
      specialize (ALIAS1 (S n) (S n')).
      rewrite EQ, 2nth_error_Sn in ALIAS1.
      eapply ALIAS1 in LU1; eauto.
      destruct LU1 as (SN & N).
      inv SN.
      auto.
    - red; intros * LU1 LU2.
      specialize (ALIAS2 (S n) (S n')).
      rewrite 2nth_error_Sn in ALIAS2.
      eapply ALIAS2 in LU1; eauto.

    - do 2 red. intros * LU1 LU2 LU3 LU4 INEQ.
      do 2 red in ALIAS3.
      specialize (ALIAS3 id1 ptrv1 id2 ptrv2 (S n1) (S n2)).
      rewrite !EQ, !nth_error_Sn in ALIAS3.
      eapply ALIAS3 in LU1; eauto.
  Admitted.


  Lemma state_invariant_enter_scope_DSHnat : forall σ v x τ s1 s2 stH mV l g,
      τ ≡ getWFType x DSHnat ->
      Γ s1 ≡ (x,τ) :: Γ s2 ->
      ~ In x (map fst (Γ s2)) ->
      in_local_or_global_scalar l g mV x (dvalue_of_int v) τ ->
      state_invariant σ s2 stH (mV,(l,g)) ->
      state_invariant (DSHnatVal v::σ) s1 stH (mV,(l,g)).
  Proof.
    intros * -> EQ fresh IN [MEM WF ALIAS1 ALIAS2 ALIAS3].
    split.
    - red; intros * LU1 LU2.
      destruct n as [| n].
      + rewrite EQ in LU2; cbn in *.
        inv LU1; inv LU2; auto.
      + rewrite nth_error_Sn in LU1.
        rewrite EQ, nth_error_Sn in LU2.
        eapply MEM in LU2; eauto.
    -  do 2 red.
       intros ? [| n] LU.
       + cbn in LU.
         inv LU.
         rewrite EQ; cbn; eauto.
       + rewrite nth_error_Sn in LU.
         rewrite EQ,nth_error_Sn.
         apply WF in LU; auto.

    - red; intros * LU1 LU2.
      destruct n as [| n], n' as [| n']; auto.
      + rewrite EQ in LU2; cbn in *.
        rewrite EQ in LU1; cbn in *.
        inv LU1; inv LU2; auto. split; auto. eexists; auto.
      + exfalso.
        rewrite EQ, nth_error_Sn in LU2.
        rewrite EQ in LU1.
        cbn in *.
        inv LU1.
        apply fresh.
        apply nth_error_In in LU2.
        replace id with (fst (id,τ')) by reflexivity.
        apply in_map; auto.

      + exfalso.
        rewrite EQ, nth_error_Sn in LU1.
        rewrite EQ in LU2.
        cbn in *.
        inv LU2.
        apply fresh.
        apply nth_error_In in LU1.
        replace id with (fst (id,τ)) by reflexivity.
        apply in_map; auto.

      + rewrite EQ, nth_error_Sn in LU1.
        rewrite EQ, nth_error_Sn in LU2.
        eapply ALIAS1 in LU1; apply LU1 in LU2; eauto.
        destruct LU2; split; auto.

    - red; intros * LU1 LU2.
      destruct n as [| n], n' as [| n']; auto.
      + inv LU1.

      + inv LU2.


      + rewrite nth_error_Sn in LU1.
        rewrite nth_error_Sn in LU2.
        eapply ALIAS2 in LU1; apply LU1 in LU2; eauto.

    - do 2 red. intros * LU1 LU2 LU3 LU4 INEQ.
      destruct n1 as [| n1], n2 as [| n2]; auto.
      + cbn in LU1. inv LU1; inv LU2.
        intros H H0.
        admit. (* Probably need to make about locals only *)
      + cbn in *; inv LU1.
        admit.
      + cbn in *; inv LU2.
        admit.
  Admitted.

  Lemma state_invariant_enter_scope_DSHCType : forall σ v x τ s1 s2 stH mV l g,
      τ ≡ getWFType x DSHCType ->
      Γ s1 ≡ (x,τ) :: Γ s2 ->
      ~ In x (map fst (Γ s2)) ->
      in_local_or_global_scalar l g mV x (dvalue_of_bin v) τ ->
      state_invariant σ s2 stH (mV,(l,g)) ->
      state_invariant (DSHCTypeVal v::σ) s1 stH (mV,(l,g)).
  Proof.
    intros * -> EQ fresh IN [MEM WF ALIAS1 ALIAS2 ALIAS3].
    split.
    - red; intros * LU1 LU2.
      destruct n as [| n].
      + rewrite EQ in LU2; cbn in *.
        inv LU1; inv LU2; auto.
      + rewrite nth_error_Sn in LU1.
        rewrite EQ, nth_error_Sn in LU2.
        eapply MEM in LU2; eauto.
    -  do 2 red.
       intros ? [| n] LU.
       + cbn in LU.
         inv LU.
         rewrite EQ; cbn; eauto.
       + rewrite nth_error_Sn in LU.
         rewrite EQ,nth_error_Sn.
         apply WF in LU; auto.

    - red; intros * LU1 LU2.
      destruct n as [| n], n' as [| n']; auto.
      + rewrite EQ in LU2; cbn in *.
        rewrite EQ in LU1; cbn in *.
        inv LU1; inv LU2; auto. split; auto. eexists; auto.
      + exfalso.
        rewrite EQ, nth_error_Sn in LU2.
        rewrite EQ in LU1.
        cbn in *.
        inv LU1.
        apply fresh.
        apply nth_error_In in LU2.
        replace id with (fst (id,τ')) by reflexivity.
        apply in_map; auto.

      + exfalso.
        rewrite EQ, nth_error_Sn in LU1.
        rewrite EQ in LU2.
        cbn in *.
        inv LU2.
        apply fresh.
        apply nth_error_In in LU1.
        replace id with (fst (id,τ)) by reflexivity.
        apply in_map; auto.

      + rewrite EQ, nth_error_Sn in LU1.
        rewrite EQ, nth_error_Sn in LU2.
        eapply ALIAS1 in LU1; apply LU1 in LU2; eauto.
        destruct LU2; split; auto.

    - red; intros * LU1 LU2.
      destruct n as [| n], n' as [| n']; auto.
      + inv LU1.

      + inv LU2.


      + rewrite nth_error_Sn in LU1.
        rewrite nth_error_Sn in LU2.
        eapply ALIAS2 in LU1; apply LU1 in LU2; eauto.

    - do 2 red. intros * LU1 LU2 LU3 LU4 INEQ.
      destruct n1 as [| n1], n2 as [| n2]; auto.
      + cbn in *.
        inv LU1; inv LU2.
        admit.
      + cbn in *; inv LU1.
        admit.
      + cbn in *; inv LU2.
        admit.
  Admitted.

  Lemma state_invariant_enter_scope_DSHPtr :
    forall σ ptrh sizeh ptrv x τ s1 s2 stH mV mV_a l g,
      τ ≡ getWFType (ID_Local x) (DSHPtr sizeh) ->
      Γ s1 ≡ (ID_Local x,τ) :: Γ s2 ->

      (* Freshness *)
      ~ In (ID_Local x) (map fst (Γ s2)) ->          (* The new ident is fresh *)
      (forall sz, ~ In (DSHPtrVal ptrh sz) σ) -> (* The new Helix address is fresh *)
      no_llvm_ptr_aliasing_cfg σ s2 (mV, (l, g)) ->

      state_invariant σ s2 stH (mV,(l,g)) ->

      (* We know that a certain ptr has been allocated *)
      allocate mV (DTYPE_Array (Int64.intval sizeh) DTYPE_Double) ≡
               inr (mV_a, ptrv) ->

      state_invariant (DSHPtrVal ptrh sizeh :: σ) s1
                      (memory_set stH ptrh mem_empty)
                      (mV_a, (alist_add x (UVALUE_Addr ptrv) l,g)).
  Proof.
    Opaque add_logical_block. Opaque next_logical_key.
    intros * -> EQ fresh1 fresh2 fresh3 [MEM WF ALIAS1 ALIAS2 ALIAS3] alloc.
    split.
    - red; intros * LU1 LU2.
      destruct n as [| n].
      + rewrite EQ in LU2; cbn in *.
        inv LU1; inv LU2; eauto.
        exists mem_empty. eexists ptrv. eexists.
        split; auto.
        apply memory_lookup_memory_set_eq.

        split. reflexivity.
        split. red.
        inv alloc.
        rewrite get_logical_block_of_add_to_frame. cbn.
        rewrite get_logical_block_of_add_logical_block.

        auto. eexists. eexists. eexists. split; auto.
        reflexivity. cbn. rewrite typ_to_dtyp_D_array. cbn. lia.
        split; auto. inv alloc.
        red.
        rewrite alist_add_find_eq. reflexivity.
        inv alloc.
        intros. inversion H.

      + rewrite nth_error_Sn in LU1.
        rewrite EQ, nth_error_Sn in LU2.
        eapply MEM in LU2; eauto.

        admit.
    - do 2 red.
      intros ? [| n] LU.
      + cbn in LU.
        inv LU.
        rewrite EQ; cbn; eauto.
        exists (ID_Local x). cbn. reflexivity.
      + rewrite nth_error_Sn in LU.
        rewrite EQ,nth_error_Sn.
        apply WF in LU; auto.

    - red; intros * LU1 LU2.
      destruct n as [| n], n' as [| n']; auto.
      + rewrite EQ in LU2; cbn in *.
        rewrite EQ in LU1; cbn in *.
        inv LU1; inv LU2; auto. split; auto. eexists; auto.

      + exfalso.
        rewrite EQ, nth_error_Sn in LU2.
        rewrite EQ in LU1.
        cbn in *.
        inv LU1.
        apply fresh1.
        apply nth_error_In in LU2.
        replace (ID_Local x) with (fst (ID_Local x,τ')) by reflexivity.
        apply in_map; auto.

      + exfalso.
        rewrite EQ, nth_error_Sn in LU1.
        rewrite EQ in LU2.
        cbn in *.
        inv LU2.
        apply fresh1.
        apply nth_error_In in LU1.
        replace (ID_Local x) with (fst (ID_Local x,τ)) by reflexivity.
        apply in_map; auto.

      + rewrite EQ in LU2; cbn in *.
        rewrite EQ in LU1; cbn in *.
        inv LU1; inv LU2; auto.
        split.
        assert (n ≡ n'). {
          eapply ALIAS1; eauto.
        } subst; auto.
        admit.

    - red; intros * LU1 LU2.
      destruct n as [| n], n' as [| n']; auto.
      + cbn in *. inv LU1. exfalso.
        eapply fresh2.
        apply nth_error_In in LU2. eauto.
      + cbn in *. inv LU2. exfalso.
        eapply fresh2.
        apply nth_error_In in LU1. eauto.
      + cbn in *.
        assert (n ≡ n'). {
          eapply ALIAS2; eauto.
        }
        subst; auto.

    - do 2 red. intros * LU1 LU2 LU3 LU4 INEQ IN1 IN2.
      destruct n1 as [| n1], n2 as [| n2]; auto.
      + rewrite EQ in LU3.
        rewrite EQ in LU4.
        cbn in *.
        inv LU1; inv LU2; inv LU3; inv LU4.
        eauto.
      + rewrite EQ in LU3,LU4.
        cbn in *.
        inv LU1; inv LU3.
        (* eapply fresh3 in IN1; eauto. *)
        (* red in IN1, IN. *)
        (* destruct id1; cbn; eauto. *)
        (* rewrite IN1 in IN; inv IN; auto. *)
        (* rewrite IN1 in IN; inv IN; auto. *)
        admit.
      + rewrite EQ in LU3,LU4.
        cbn in *.
        inv LU2; inv LU4.
        (* eapply fresh3 in IN1; eauto. *)
        (* red in IN2, IN. *)
        (* destruct id2; cbn; eauto. *)
        (* rewrite IN2 in IN; inv IN; auto. *)
        (* rewrite IN2 in IN; inv IN; auto. *)
        admit.
      + rewrite EQ in LU3,LU4.
        cbn in *.
        eapply ALIAS3.
        apply LU1.
        all:eauto.
  Admitted.

  Ltac remove_neq_locals :=
    match goal with
    | |- Maps.add ?x ?v ?l1 @ ?id ≡ ?l2 @ ?id =>
      assert (x ≢ id) by
          (eapply lid_bound_earlier; eauto;
           [eapply incLocal_lid_bound; eauto | solve_local_count]);
      setoid_rewrite maps_add_neq; eauto
    end.

  Definition genIR_post (σ : evalContext) (s1 s2 : IRState) (to : block_id) (li : local_env)
    : Rel_cfg_T unit ((block_id * block_id) + uvalue) :=
    lift_Rel_cfg (state_invariant σ s2) ⩕
                 branches to ⩕
                 (fun sthf stvf => local_scope_modif s1 s2 li (fst (snd stvf))).

 
  Opaque alist_add.
  Lemma compile_FSHCOL_correct :
    forall (** Compiler bits *) (s1 s2: IRState)
      (** Helix bits    *) (op: DSHOperator) (σ : evalContext) (memH : memoryH)
      (** Vellvm bits   *) (nextblock bid_in bid_from : block_id) (bks : list (LLVMAst.block typ))
      (* (env : list (ident * typ)) *)  (g : global_env) ((* ρi  *)ρ : local_env) (memV : memoryV),
      genIR op nextblock s1 ≡ inr (s2,(bid_in,bks)) ->
      bid_bound s1 nextblock ->
      state_invariant σ s1 memH (memV, (ρ, g)) ->
      Gamma_safe σ s1 s2 ->
      no_failure (E := E_cfg) (interp_helix (denoteDSHOperator σ op) memH) -> (* Evaluation succeeds *)
      eutt (succ_cfg (genIR_post σ s1 s2 nextblock ρ))
           (interp_helix (denoteDSHOperator σ op) memH)
           (interp_cfg (D.denote_ocfg (convert_typ [] bks) (bid_from,bid_in))
                       g ρ memV).
  Proof.
    intros s1 s2 op; revert s1 s2; induction op; intros * GEN NEXT PRE GAM NOFAIL.
    - (* DSHNOp *)
      (* begin comment
      cbn* in *.
      simp.
      cbn*.
      hvred.
      vjmp.
      (* TODO :( *)
      unfold fmap, Fmap_block; cbn.
      vred.
      vred.
      vred.
      vred.

      rewrite denote_ocfg_unfold_not_in; cycle 1.
      {
        (* TODO: auto and part of vjmp_out *)
        rewrite find_block_ineq; [apply find_block_nil | cbn].

        assert (nextblock ≢ bid_in).
        {
          (* TODO: pull this out into automation *)
          eapply bid_bound_fresh; eauto.
          eapply bid_bound_bound_between; eauto.

          match goal with
          | H: incBlockNamed ?msg ?s1 ≡ inr (_, ?bid) |-
            bid_bound ?s2 bid_in =>
            idtac H
          end.
          eapply bid_bound_incBlockNamed; eauto; reflexivity.
          solve_not_bid_bound.
          block_count_replace. lia.
          reflexivity.
        }
        auto.
      }
      vred.

      apply eutt_Ret.
      split; [| split]; cbn in *; eauto.
      eapply state_invariant_incVoid; eauto.
      eapply state_invariant_incBlockNamed; eauto.

      end comment *)
      admit.

    -

    - admit.
    - admit.
    - admit.
    - admit.

    - (* DSHLoop *)

      (*
      (* Require Import Correctness_While. *)
      (* Import ProofMode. *)
      Opaque add_comment.
      Opaque dropVars.
      Opaque newLocalVar.
      Opaque genWhileLoop.
      (* rewrite DSHLoop_interpreted_as_tfor. *)
      cbn* in *; simp; cbn in *.
      rewrite add_comment_eutt.
      clean_goal.
      rename i into s1, i0 into s2, i1 into s3, i2 into s4, i3 into s5, s2 into s6.

      local_scope_modif s3 s4 li l

      pose proof
           @genWhileLoop_tfor_correct "Loop_loop" (Name ("Loop_i" @@ string_of_nat (local_count i0))) b b0 l nextblock bid_in
           {| block_count := block_count i3; local_count := local_count i3; void_count := void_count i3; Γ := l1 |} s2 l0 as GENC.
      forward GENC; [clear GENC |].
      {
        rename l into bodyV, b0 into entry_body.


        (* Lemma genIR_entry_entry_in_bids : *)


        (* Checking that we properly enter the body *)
        admit.
      }
      forward GENC; [clear GENC |].
      {
        (* wf_ocfg_bid of the graph generated by genWhileLopo *)
        admit.
      }
      forward GENC; [clear GENC |].
      {
        (* Freshness of nextblock *)
        admit.
      }
      specialize (GENC n Heqs5 (option (memoryH * unit)%type)).

      match goal with
        |- eutt _ (tfor ?bod _ _ _) _ => specialize (GENC bod)
      end.
      forward GENC; [clear GENC |].
      {
        rename n into foo.
        clear -Heqs.
        unfold MInt64asNT.from_nat in Heqs.
        unfold MInt64asNT.from_Z in Heqs.
        simp.
        apply l0.
      }

      (* Invariant at each iteration *)
      specialize (GENC (fun k mH stV =>
                          match mH with
                          | None => False
                          | Some (mH,tt) => state_invariant σ s2 (* b *) mH stV
                          end)).
      (* Precondition *)
      specialize (GENC (fun mH stV =>
                          match mH with
                          | None => False
                          | Some (mH,tt) => state_invariant σ s2 mH stV
                          end)).
      (* Postcondition *)
      specialize (GENC (fun mH stV =>
                          match mH with
                          | None => False
                          | Some (mH,tt) => state_invariant σ s2 mH stV
                          end)).

      {
        clear GENC.
        cbn.
        intros x (? & ? & ? & ?).
        intros (H1 & H2).
        destruct x as [[mH []] | ?]; [| intuition].
        split; cbn; auto.
        destruct H1; eauto.
      }

      (* { *)
      (*   clear GENC. *)
      (*   cbn. *)
      (*   intros x (? & ? & ? & ?). *)
      (*   intros [H1 H2]. *)
      (*   destruct x as [[mH []] | ?]; [| intuition]. *)
      (*   split; cbn; auto. *)
      (*   destruct H1; eauto. *)
      (*   admit. (* TODO: might have broken when adjusting meminv *) *)
      (*   admit. (* TODO: might have broken when adjusting meminv *) *)
      (* } *)

      (* { *)
      (*   (* Body correct *) *)
      (*   clear GENC. *)
      (*   intros * HPRE. *)
      (*   destruct a as [[mH[]] |]; cbn in HPRE; [| destruct HPRE as [abs _]; inv abs]. *)
      (*   break_match_goal. *)
      (*   - (* TODO: invariant that ~ k < n *) *)
      (*     exfalso. admit. *)
      (*   - hvred. *)
      (*     eapply eutt_mon. *)
      (*     2:eapply IHop. *)
      (*     2:eassumption. *)
      (*     { *)
      (*       intros [[?mH []] |] (? & ? & ? & ?) PRE'; cbn in PRE'; [| inv PRE']. *)
      (*       destruct PRE' as [SINV [? ->]] ; cbn in *. *)
      (*       split; [|split]; eauto. *)
      (*       (* TODO: add local_scope_modif to the postcondition of genIR *) *)
      (*       destruct HPRE as [SINVPRE LUPRE]. *)
      (*       match type of Heqs2 with *)
      (*       | genIR _ _ ?s1 ≡ inr (?s2, _) => *)
      (*         assert (local_scope_modif s1 s2 l2 a) *)
      (*       end. *)
      (*       admit. *)

      (*       { clear NOFAIL IHop. *)
      (*         rewrite <- LUPRE. *)
      (*         eapply local_scope_modif_out with (s1 := i0).  *)
      (*         3:eauto. *)
      (*         destruct i0; cbn; red; cbn; lia. *)
      (*         do 3 eexists; cbn; repeat split; eauto.  *)
      (*       }  *)
      (*       clean_goal. *)
      (*       rename i into s1, i0 into s2, s2 into s4, i3 into s3. *)
      (*       assert (l1 ≡ Γ s4) by admit. (* genWhileLoop_Γ *) *)
      (*       apply genIR_Context in Heqs2. *)
      (*       apply incBlockNamed_Γ in Heqs1. *)
      (*       cbn in *. *)
      (*       clear - Heqs2 Heql2 H SINV. *)
      (*       subst. *)
      (*       rewrite Heql2 in Heqs2. *)
      (*       inv Heqs2. *)
      (*       eapply state_invariant_escape_scope; eauto. *)
      (*     } *)
      (*     { *)
      (*       clear - Heqs1. *)
      (*       admit. *)
      (*     } *)
      (*     (* eapply state_invariant_enter_scope_DSHnat. *) *)
      (*     admit. *)
      (*     (* TODO: state_invariant stable by extension of both gamma and σ simultaneously *) *)
      (*     admit. *)
      (*     admit. *)
      (* } *)

      (* { *)
      (*   (* Rephrase this : really the invariant should be stable by modifications in [s1;s2] *) *)
      (*   admit. *)
      (* } *)
      (* { *)
      (*   intros ?; auto. *)
      (* } *)
      (* { *)
      (*   intros ?; auto. *)
      (* } *)
      (* { *)
      (*   admit. *)
      (* } *)
      *)
      admit.
    - (* DSHAlloc *)
  (*     cbn* in *. *)
  (*     simp. *)
  (*     cbn. *)
  (*     clean_goal. *)
  (*     rewrite add_comment_eutt. *)
  (*     hvred. *)

  (*     Set Nested Proofs Allowed. *)
  (* Lemma interp_Mem_MemAlloc : *)
  (*   forall size mem, *)
  (*     interp_Mem (trigger (MemAlloc size)) mem ≈ *)
  (*                Ret (mem, memory_next_key mem). *)
  (* Proof. *)
  (*   intros size mem. *)
  (*   setoid_rewrite interp_Mem_vis_eqit; cbn. *)
  (*   rewrite bind_ret_l. *)
  (*   rewrite interp_Mem_ret. *)
  (*   apply tau_eutt. *)
  (* Qed. *)

  (* Lemma interp_helix_MemAlloc : *)
  (*   forall {E} size mem, *)
  (*     interp_helix (E := E) (trigger (MemAlloc size)) mem ≈ *)
  (*     Ret (Some (mem, memory_next_key mem)). *)
  (* Proof. *)
  (*   intros. *)
  (*   Transparent interp_helix. *)
  (*   unfold interp_helix. *)
  (*   Opaque interp_helix. *)
  (*   setoid_rewrite interp_Mem_vis_eqit. *)
  (*   cbn. rewrite Eq.bind_ret_l, tau_eutt. *)
  (*   cbn; rewrite interp_Mem_ret, interp_fail_Ret, translate_ret. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Import ProofMode. *)

  (* rewrite interp_helix_MemAlloc. *)
  (* hred. *)
  (* rewrite interp_helix_MemSet. *)
  (* hred. *)
  (* unfold add_comments; cbn. *)
  (* unfold fmap, Fmap_block; cbn. *)
  (* vjmp. *)
  (* rewrite find_block_eq; reflexivity. *)
  (* cbn. *)
  (* vred. *)
  (* vred. *)
  (* vred. *)
  (* edestruct denote_instr_alloca_exists as (mV' & addr & Alloc & EQAlloc); *)
  (*   [| rewrite EQAlloc; clear EQAlloc]. *)
  (* red; easy. *)
  (* vred. *)
  (* vred. *)
  (* admit. *)
  (* (* (* no_repeat assumption  *) *) *)
  (* (* rename b into target. *) *)
  (* (* vjmp. *) *)
  (* (* { *) *)
  (* (*   rewrite find_block_ineq. *) *)

  (* (*   apply find_block_tail_wf. *) *)
  (* (*   admit. *) *)


  (*   - admit. *)
  (*   - (* DSHSeq *) *)
  (*     Opaque add_comment. *)
  (*     cbn. *)

  (*     pose proof GEN as GEN_DESTRUCT. *)
  (*     cbn* in GEN_DESTRUCT; simp. *)

  (*     rename i into s_op1, l0 into bk_op1, l into bk_op2. *)
  (*     rename b into op2_entry, bid_in into op1_entry. *)
  (*     rename Heqs0 into GEN_OP2, Heqs2 into GEN_OP1. *)
  (*     rewrite add_comment_eutt. *)
  (*     cbn. *)
  (*     clean_goal. *)

  (*     rewrite convert_typ_block_app. *)
  (*     rewrite denote_ocfg_app; eauto. *)
  (*     2: { *)
  (*       unfold no_reentrance. *)
  (*       pose proof GEN_OP1 as GEN_OP1'. *)

  (*       apply (inputs_not_earlier_bound _ _ _ NEXT) in GEN_OP1'. *)
  (*       apply inputs_bound_between in GEN_OP1. *)
  (*       apply outputs_bound_between in GEN_OP2. *)

  (*       pose proof (Forall_and GEN_OP1 GEN_OP1') as INPUTS. *)
  (*       cbn in INPUTS. *)

  (*       eapply (Forall_disjoint GEN_OP2 INPUTS). *)
  (*       intros x OUT_PRED [IN_BOUND IN_NEXT]. *)
  (*       destruct OUT_PRED as [OUT_PRED | OUT_PRED]; auto. *)
  (*       eapply (state_bound_between_separate incBlockNamed_count_gen_injective OUT_PRED IN_BOUND). *)
  (*       lia. auto. *)
  (*       block_count_replace. *)
  (*       lia. *)
  (*     } *)
  (*     hvred. *)

  (*     (* Helix generates code for op2 *first*, so op2 gets earlier *)
  (*       variables from the irstate. Helix needs to do this because it *)
  (*       passes the block id for the next block that an operator should *)
  (*       jump to when it's done executing... So it generates code for *)
  (*       op2, which goes to the next block of the entire sequence, and *)
  (*       then passes the entry point for op2 as the "nextblock" for *)
  (*       op1. *)
  (*     *) *)
  (*     cbn in *. *)
  (*     pose proof PRE as SINV. *)
  (*     simp. *)

  (*     rename Heqs0 into GEN_OP2, Heqs1 into GEN_OP1. *)

  (*     eapply eutt_clo_bind_returns. *)
  (*     { *)
  (*       eapply IHop1 with (s1:=s_op1) (s2:=s2); eauto. *)
  (*       - eapply bid_bound_genIR_entry; eauto. *)
  (*       - apply genIR_Context in GEN_OP2. *)
  (*         eapply state_invariant_Γ; eauto. *)
  (*       - eapply Gamma_safe_shrink; eauto. *)
  (*         eauto using genIR_Context. *)
  (*         solve_local_count. *)
  (*         solve_local_count. *)
  (*     } *)

  (*     clear IHop1. *)
  (*     introR; destruct_unit. *)
  (*     intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET. *)
  (*     cbn in PRE0; destruct PRE0 as [INV2 [from2 BRANCH2]]; cbn in *; inv_eqs. *)
  (*     subst. *)

  (*     eapply eqit_mon; auto. *)
  (*     2: { *)
  (*       eapply IHop2; try exact GEN_OP2; eauto. *)
  (*       - eapply state_invariant_Γ; eauto. *)
  (*         apply genIR_Context in GEN_OP1; apply genIR_Context in GEN_OP2; rewrite GEN_OP2; auto. *)
  (*       - eapply Gamma_safe_shrink; eauto. *)
  (*         eauto using genIR_Context. *)
  (*         solve_local_count. *)
  (*         solve_local_count. *)
  (*     }           *)
  (*     clear IHop2. *)

  (*     intros [[memH1 ?]|] (memV1 & l1 & g1 & res1) PR; [| inv PR]. *)
  (*     destruct PR as [? [? BR]]. *)
  (*     cbn in *. *)

  (*     destruct res1 as [[from1 next] | v]; simp. *)

  (*     split; cbn; eauto. *)
  (*     eapply state_invariant_Γ; eauto. *)
  (*     apply genIR_Context in GEN_OP1; auto. *)

(*
    -
      Opaque genWhileLoop.
      cbn* in *.
      simp.
      unfold denotePExpr in *; cbn* in *.
      simp; try now (exfalso; clear -NOFAIL; try apply no_failure_Ret in NOFAIL; try_abs).
      apply no_failure_Ret in NOFAIL; simp; cbn in *; try_abs.
      hide_strings'.
      inv_resolve_PVar Heqs0.
      inv_resolve_PVar Heqs1.
      cbn* in *.
      simp.
      eutt_hide_right.
      repeat apply no_failure_Ret in NOFAIL.
      repeat (edestruct @no_failure_helix_LU as (? & NOFAIL' & ?); eauto; []; clear NOFAIL; rename NOFAIL' into NOFAIL; cbn in NOFAIL; eauto).
      rauto:L.
      all:eauto.
      Ltac rewrite_nth_error :=
        match goal with
        | h: nth_error _ _ ≡ _ |- _ => rewrite h
        end.
      Ltac rewrite_memory_lookup :=
        match goal with
        | h: memory_lookup _ _ ≡ _ |- _ => rewrite h
        end.
      subst; eutt_hide_left.
      Transparent genWhileLoop.
      cbn in *.
      simp.
      cbn in *.
      unfold add_comments; cbn.
      repeat rewrite fmap_list_app.
      cbn.
      match goal with
        |- context[denote_ocfg ?x] =>
        remember x as bks
      end.
(*
      erewrite denote_ocfg_unfold.
      2:{
        subst; cbn.
        clear.
        destruct (Eqv.eqv_dec_p bid_in bid_in) as [foo | foo].
        reflexivity.
        exfalso; apply foo; reflexivity.
      }
      Opaque find_block.
      cbn.
      norm_v.
      unfold IntType; rewrite typ_to_dtyp_I.
      cbn.
      focus_single_step_v; norm_v.
      cbn; norm_v.
      subst.
      norm_v.
      focus_single_step_v; norm_v.
      rewrite interp_cfg_to_L3_LW.
      cbn; norm_v.
      unfold endo.
      subst.
      repeat (norm_v; []).
      focus_single_step_v.
      (* onAllHyps move_up_types. *)
      unfold endo.
      focus_single_step_v.
      norm_v.
      2: apply lookup_alist_add_eq.
      cbn; norm_v.
      subst; cbn; norm_v.
      focus_single_step_v.
      (* Case analysis on whether we ever enter the loop or not *)
      unfold eval_int_icmp.
      cbn.
      break_match_goal.
      -- (* We enter the loop *)
        cbn; norm_v.
        subst; cbn; norm_v.
        rewrite find_block_ineq, find_block_eq.
        2: reflexivity.
        2:cbn; admit.
        norm_v.
        (* loopblock  *)
        rewrite denote_ocfg_unfold.
        2:{
          cbn.
          match goal with
            |- context[if ?p then true else false] =>
            destruct p as [EQ | INEQ]
          end.
          admit.
          match goal with
            |- context[if ?p then true else false] =>
            destruct p as [?EQ | ?INEQ]
          end.
          reflexivity.
          admit.
        }
*)
      (* Need to denote phis, I cannot denote the block directly :( *)
        admit.
      (* -- *)
      (*   (* from == to, we go from the entry block to the next one directly *) *)
      (*   cbn. *)
      (*   norm_v. *)
      (*   subst; cbn; norm_v. *)
      (*   repeat rewrite find_block_ineq. *)
      (*   2,3,4,5: cbn; admit. *)
      (*   cbn. *)
      (*   rewrite find_block_nil. *)
      (*   cbn; norm_v. *)
      (*   assert (n ≡ 0) by admit. *)
      (*   subst. *)
      (*   cbn; norm_h. *)
      (*   rewrite interp_Mem_MemSet. *)
      (*   norm_h. *)
      (*   apply eutt_Ret. *)
      (*   split; eauto. *)
      (*   { *)
      (*     admit. *)
      (*   } *)
      (*   { *)
      (*     admit. *)
      (*   } *)
    - (* DSHBinOp *)
      cbn* in *.
      simp.
      inv_resolve_PVar Heqs1.
      inv_resolve_PVar Heqs2.
      (* On the Helix side, the computation consists in:
         1. xi <- denotePExpr x
         2. yi <- denotePExpr y
         3. lookup xi in memory
         4. lookup yi in memory
         5. denoteDSHBinop on the values read
         6. write the result in memory at yi
       *)
      eutt_hide_right.
      rauto:L.
      subst; eutt_hide_left.
      unfold add_comments.
      cbn.
      match goal with
        |- context[denote_ocfg ?x] =>
        remember x as bks
      end.
      (* Lemma about while loop instead *)
      (* erewrite denote_ocfg_unfold. *)
      (* 2:{ *)
      (*   subst; cbn. *)
      (*   destruct (Eqv.eqv_dec_p bid_in bid_in).  *)
      (*   reflexivity. *)
      (*   exfalso. *)
      (*   apply n0. *)
      (*   reflexivity. *)
      (* } *)
      (* cbn. *)
      (* norm_v. *)
      (* unfold IntType; rewrite typ_to_dtyp_I. *)
      (* cbn. *)
      (* setoid_rewrite bind_ret_l. *)
      (* setoid_rewrite bind_ret_l. *)
      (* cbn. *)
      (* norm_v. *)
      (* rewrite interp_cfg_to_L3_LW. *)
      (* cbn*; norm_v. *)
      (* cbn*; norm_v. *)
      (* 2:{ *)
      (*   cbn. *)
      (*   unfold endo. *)
      (*   rewrite rel_dec_eq_true; eauto; typeclasses eauto. *)
      (* } *)
      (* cbn. *)
      (* unfold endo. *)
      (* unfold eval_int_icmp. *)
      (* cbn. *)
      (* focus_single_step_v. *)
      (* unfold Int64_eq_or_cerr, Z_eq_or_cerr, ErrorWithState.err2errS, Z_eq_or_err, memory_lookup_err in *. *)
      (* cbn* in *. *)
      (* simp. *)
      (* inv_resolve_PVar Heqs0. *)
      (* inv_resolve_PVar Heqs1. *)
      (* onAllHyps move_up_types.  *)
  (*     repeat match goal with *)
  (*            | h : Int64.intval _ ≡ Int64.intval _ |- _ => apply int_eq_inv in h; subst *)
  (*            end. *)
  (*     eutt_hide_left. *)
  (*     focus_single_step_v. *)
  (*     unfold MInt64asNT.from_nat in *. *)
  (*     rename n into index1. *)
  (*     break_if. *)
  (*     { *)
  (*       cbn. *)
  (*       norm_v. *)
  (*       subst. *)
  (*       cbn. *)
  (*       norm_v. *)
      admit.
    - (* DSHMemMap2 *) admit.
    - (* DSHPower *) admit.
    - (* DSHLoop *)
      Opaque genWhileLoop.
      Require Import Correctness_While.
      rewrite DSHLoop_interpreted_as_tfor.
      cbn* in *; simp.
      rewrite add_comment_eutt.
      (*
        sub_alist
       parameterized by some l_i
       start from l_i \subseteqeq_[s1;s2] l1
       end in l2 such that l2 | dom(l_i) ~~ l_i
        I l --> l ⊑ l' --> I l'
        forall l ⊑_[s1;s2] l',
        eutt op c
        gencode op s1 = (s2,c)
        pre: dom(l_i) ∩ [s1;s2] = nil
        {c}
        post: dom(l_f) \ dom(l_i) ⊆ [s1;s2]
       *)
      assert (IN: In b0 (block_ids l)).
      {
        (* Prpoerty of genIR *)
        admit.
      }
      assert (NOREPET: blk_id_norepet l0).
      {
        (* Prpoerty of genWhileLoop *)
        admit.
      }
      assert (FRESH: fresh_in_cfg l0 nextblock).
      {
        (* Property of? *)
        admit.
      }
      assert (NOTOVER: Z.of_nat n < Integers.Int64.modulus).
      {
        (* Property of no_failure of the source semantics, annoying to work with *)
        admit.
      }
      (* let (I := fun _ mH => *)
 (* nat → config_helix_OT () → memoryV * (alist raw_id uvalue * global_env) → Prop *)
      eapply eutt_mon; cycle 1.
      eapply (genWhileLoop_tfor_correct IN NOREPET FRESH _ Heqs4 _ NOTOVER).
      Unshelve.
      15:{
        refine (fun _ mh '(mv,(l,g)) =>
                  match mh with
                  | None => False
                  | Some mh => state_invariant σ s1 b mh _
                  end
               ).
        (*
          DSHLoop 2 ()
         *)
      admit.
      4: eassumption.

    - (* DSHAlloc *) admit.
    - (* DSHMemInit *) admit.
    - (* DSHSeq *)
      cbn.
      pose proof GEN as GEN_DESTRUCT.
      cbn in GEN_DESTRUCT; simp.
      rename i into s_op1.
      rename l0 into bk_op1.
      rename l into bk_op2.
      rename b into op2_entry.
      rename bid_in into op1_entry.
      rename Heqs0 into GEN_OP2.
      rename Heqs2 into GEN_OP1.
      rewrite add_comment_eutt.
      cbn.
      rewrite convert_typ_block_app.
      rewrite denote_ocfg_app; eauto.
      2: {
        unfold no_reentrance.
        pose proof GEN_OP1 as GEN_OP1'.
        apply (inputs_not_earlier_bound _ _ _ NEXT) in GEN_OP1'.
        apply inputs_bound_between in GEN_OP1.
        apply outputs_bound_between in GEN_OP2.
        pose proof (Forall_and GEN_OP1 GEN_OP1') as INPUTS.
        cbn in INPUTS.
        eapply (Forall_disjoint GEN_OP2 INPUTS).
        intros x OUT_PRED [IN_BOUND IN_NEXT].
        destruct OUT_PRED as [OUT_PRED | OUT_PRED]; auto.
        eapply (state_bound_between_separate incBlockNamed_count_gen_injective OUT_PRED IN_BOUND).
        lia. auto.
        block_count_replace.
        lia.
      }
      rauto.
      (* Helix generates code for op2 *first*, so op2 gets earlier
        variables from the irstate. Helix needs to do this because it
        passes the block id for the next block that an operator should
        jump to when it's done executing... So it generates code for
        op2, which goes to the next block of the entire sequence, and
        then passes the entry point for op2 as the "nextblock" for
        op1.
      *)
      cbn in NOFAIL.
      pose proof BISIM as BISIM2.
      destruct BISIM as [[SINV (?from & EQ)] FRESH]; cbn in *; inv EQ.
      simp.
      rename Heqs0 into GEN_OP2.
      rename Heqs1 into GEN_OP1.
      eapply eutt_clo_bind_returns.
      {
        eapply IHop1 with (s1:=s_op1) (s2:=s2).
        - eapply bid_bound_genIR_entry; eauto.
        - split.
          + cbn.
            split.
            * cbn.
              apply genIR_Context in GEN_OP2.
              split.
              -- unfold memory_invariant.
                 rewrite <- GEN_OP2.
                 apply SINV.
              -- unfold WF_IRState.
                 rewrite <- GEN_OP2.
                 apply SINV.
              -- eapply no_id_aliasing_gamma; eauto.
                 eapply st_no_id_aliasing; eauto.
              -- eapply st_no_dshptr_aliasing; eauto.
              -- cbn in *.
                 eapply no_llvm_ptr_aliasing_gamma; eauto.
                 eapply st_no_llvm_ptr_aliasing in SINV. cbn in SINV.
                 eauto.
            * cbn. exists from.
              reflexivity.
          + cbn.
            solve_fresh.
        - eapply no_failure_helix_bind_prefix; eauto.
        - auto.
      }
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      cbn in PRE; destruct PRE as [[INV2 [from2 BRANCH2]] FRESH2]; cbn in *; inv_eqs.
      subst...
      eapply eqit_mon; auto.
      2: {
        eapply IHop2; eauto.
        destruct BISIM2 as [[SINV2 BRANCHES2] FRESHNESS2].
        cbn in SINV2, BRANCHES2, FRESHNESS2.
        split.
        - cbn.
          destruct SINV2.
          destruct INV2.
          split; cbn; auto.
          + split.
            * apply genIR_Context in GEN_OP2.
              apply genIR_Context in GEN_OP1.
              unfold memory_invariant.
              subst_contexts.
              cbn.
              apply mem_is_inv0.
            * apply SINV.
            * eapply st_no_id_aliasing; eauto.
            * eapply st_no_dshptr_aliasing; eauto.
            * (* TODO: turn this into a lemma *)
              cbn in st_no_llvm_ptr_aliasing0. cbn.
              unfold no_llvm_ptr_aliasing.
              assert (Γ s1 ≡ Γ s_op1) by (eapply genIR_Context; eauto).
              assert (Γ s_op1 ≡ Γ s2) by (eapply genIR_Context; eauto).
              assert (Γ s1 ≡ Γ s2) by congruence.
              rewrite H1.
              apply st_no_llvm_ptr_aliasing0.
          + exists from2. reflexivity.
        - cbn.
          (* TODO: make solve_fresh do this *)
          (* Nothing in ρ is bound between s1 and s2 *)
          unfold freshness_pre in FRESHNESS2.
          (* Everything new in l is bound between s_op1 and s2... *)
          unfold freshness_post in FRESH2.
          (* This is consistent so far... *)
          unfold freshness_pre.
          intros id v H.
          destruct (alist_In_dec id ρ v) as [AIN | ANIN].
          + pose proof (FRESHNESS2 _ _ AIN) as NBOUND.
            intros CONTRA.
            apply NBOUND.
            eapply state_bound_between_shrink; eauto.
            solve_local_count.
          + pose proof (FRESH2 _ _ H ANIN) as BOUND2.
            intros BOUND1.
            eapply (state_bound_between_id_separate incLocalNamed_count_gen_injective BOUND1 BOUND2).
            auto.
      }
      intros [[memH1 ?]|] (memV1 & l1 & g1 & res1) PR.
      2: {
        inversion PR.
      }
      destruct res1 as [[from1 next] | v].
      2: {
        destruct PR as [[? [? BR]] ?].
        inversion BR.
      }
      cbn in PR. destruct PR as [[SINV1 BRANCHES1] FRESH1].
      cbn.
      split; auto.
      cbn. cbn in SINV1.
      destruct SINV1 as [MINV1 WF1].
      destruct INV2 as [MINV2 WF2].
      split.
      split.
      + cbn.
        apply genIR_Context in GEN_OP1.
        rewrite <- GEN_OP1.
        apply MINV1.
      + auto.
      + eapply no_id_aliasing_gamma; eauto.
        eapply genIR_Context; eauto.
      + eauto.
      + eapply no_llvm_ptr_aliasing_gamma; eauto.
        eapply genIR_Context; eauto.
      + cbn. cbn in BRANCHES1.
        destruct BRANCHES1 as [from1' BRANCHES1].
        exists from1. inversion BRANCHES1.
        reflexivity.
      + cbn in *.
        unfold freshness_post in *.
        intros id v AIN ANIN.
        destruct (alist_In_dec id l v) as [AINL | ANINL].
        * pose proof (FRESH2 _ _ AINL ANIN).
          eapply state_bound_between_shrink; eauto.
          apply genIR_local_count in GEN_OP2; lia.
        * pose proof (FRESH1 _ _ AIN ANINL).
          eapply state_bound_between_shrink; eauto.
          apply genIR_local_count in GEN_OP1; lia. *)
  Admitted.
  End GenIR.
