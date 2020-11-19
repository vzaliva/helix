Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.
Require Import Helix.LLVMGen.Correctness_MExpr.
Require Import Helix.LLVMGen.IdLemmas.
Require Import Helix.LLVMGen.StateCounters.
Require Import Helix.LLVMGen.VariableBinding.
Require Import Helix.LLVMGen.BidBound.
Require Import Helix.LLVMGen.LidBound.
Require Import Helix.LLVMGen.Freshness.

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
Lemma wf_cfg_singleton : forall {T} (b : _ T), wf_cfg [b].
Proof.
  intros.
  red.
  eapply Coqlib.list_norepet_cons; eauto.
  eapply Coqlib.list_norepet_nil. 
Qed.

Lemma wf_cfg_cons' : forall {T} (b : _ T) bks,
    ¬ In (blk_id b) (map blk_id bks) ->
    wf_cfg bks ->
    wf_cfg (b :: bks).
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
Lemma generates_wf_cfgs :
  ∀ (op : DSHOperator) (s1 s2 : IRState) (nextblock b : block_id) (bk_op : list (LLVMAst.block typ)),
    bid_bound s1 nextblock ->
    genIR op nextblock s1 ≡ inr (s2, (b, bk_op)) →
    wf_cfg bk_op. 
Proof.
  induction op; intros * NEXT GEN.
  - cbn* in *; simp; cbn.
    eapply wf_cfg_singleton.
  - cbn* in *; simp; cbn in *.
    eapply wf_cfg_singleton.
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
    eapply wf_cfg_cons'.
    { cbn.
      intuition;
        match goal with
        | h: Name _ ≡ Name _ |- _ => apply Name_inj in h; inv h
        end. 
    }
    eapply wf_cfg_cons'.
    { cbn.
      intuition;
        match goal with
        | h: Name _ ≡ Name _ |- _ => apply Name_inj in h; inv h
        end. 
    }
    eapply wf_cfg_cons'.
    { cbn.
      intuition;
        match goal with
        | h: Name _ ≡ Name _ |- _ => apply Name_inj in h; inv h
        end. 
    }
    eapply wf_cfg_singleton.
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
    eapply wf_cfg_cons'.
    { cbn.
      intuition;
        match goal with
        | h: Name _ ≡ Name _ |- _ => apply Name_inj in h; inv h
        end. 
    }
    eapply wf_cfg_cons'.
    { cbn.
      intuition;
        match goal with
        | h: Name _ ≡ Name _ |- _ => apply Name_inj in h; inv h
        end. 
    }
    eapply wf_cfg_cons'.
    { cbn.
      intuition;
        match goal with
        | h: Name _ ≡ Name _ |- _ => apply Name_inj in h; inv h
        end. 
    }
    eapply wf_cfg_singleton.

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
    eapply wf_cfg_cons'.
    { cbn.
      intuition;
        match goal with
        | h: Name _ ≡ Name _ |- _ => apply Name_inj in h; inv h
        end. 
    }
    eapply wf_cfg_cons'.
    { cbn.
      intuition;
        match goal with
        | h: Name _ ≡ Name _ |- _ => apply Name_inj in h; inv h
        end. 
    }
    eapply wf_cfg_cons'.
    { cbn.
      intuition;
        match goal with
        | h: Name _ ≡ Name _ |- _ => apply Name_inj in h; inv h
        end. 
    }
    eapply wf_cfg_singleton.

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
    eapply wf_cfg_cons'.
    { cbn.
      intuition;
        match goal with
        | h: Name _ ≡ Name _ |- _ => apply Name_inj in h; inv h
        end. 
    }
    eapply wf_cfg_cons'.
    { cbn.
      intuition;
        match goal with
        | h: Name _ ≡ Name _ |- _ => apply Name_inj in h; inv h
        end. 
    }
    eapply wf_cfg_cons'.
    { cbn.
      intuition;
        match goal with
        | h: Name _ ≡ Name _ |- _ => apply Name_inj in h; inv h
        end. 
    }
    eapply wf_cfg_singleton.

  - cbn* in *.
    simp.
    clean_goal.
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
    eapply wf_cfg_cons'.
    { cbn.
      intuition.
      match goal with
      | h: Name _ ≡ Name _ |- _ =>
        apply Name_inj in h; 
          first [now inv h | apply valid_prefix_string_of_nat_forward in h as [abs _]; intuition] 
      end.
      admit.
    }
    admit.

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
    apply wf_cfg_cons'; auto; clear WF.
    cbn.
    cbn in *; intros abs; apply ListUtil.in_map_elim in abs as (? & ? & ?).
    Transparent incVoid. cbn in Heqs2; inv Heqs2. Opaque incVoid.
    cbn in *.
    clear BOUND H Heql0.
    clean_goal.
    (* A bit lost *)
    admit.
    (* eapply inputs_not_earlier_bound in GEN. *)
    (* unfold inputs,fmap,Fmap_list in GEN. *)
    (* rewrite blk_id_map_convert_typ in GEN. *)
    (* edestruct Forall_forall as [IMP _]. *)
    (* specialize (IMP GEN (blk_id x0)). *)
    (* cbn in *. *)
    (* eapply IMP. *)
    (* 2: symmetry; exact H2. *)
    (* apply in_map; auto. *)
    (* clear BOUND. *)
Admitted. 
   
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

  (* TODO: move this? *)
  Lemma incLocal_id_neq :
    forall s1 s2 s3 s4 id1 id2,
      incLocal s1 ≡ inr (s2, id1) ->
      incLocal s3 ≡ inr (s4, id2) ->
      local_count s1 ≢ local_count s3 ->
      id1 ≢ id2.
  Proof.
    intros s1 s2 s3 s4 id1 id2 GEN1 GEN2 COUNT.
    eapply incLocalNamed_count_gen_injective.
    symmetry. rewrite incLocal_unfold in *. eapply GEN1.
    symmetry. rewrite incLocal_unfold in *. eapply GEN2.
    solve_local_count_tac.
    solve_prefix.
    solve_prefix.
  Qed.

  Lemma incLocal_id_neq_flipped :
    forall s1 s2 s3 s4 id1 id2,
      incLocal s1 ≡ inr (s2, id1) ->
      incLocal s3 ≡ inr (s4, id2) ->
      local_count s1 ≢ local_count s3 ->
      id2 ≢ id1.
  Proof.
    intros s1 s2 s3 s4 id1 id2 GEN1 GEN2 COUNT.
    intros EQ. symmetry in EQ. revert EQ.
    eapply incLocal_id_neq; eauto.
  Qed.

  Lemma in_gamma_not_in_neq :
    forall σ s id r,
      in_Gamma σ s id ->
      ~ in_Gamma σ s r ->
      id ≢ r.
  Proof.
    intros σ s id r GAM NGAM.
    destruct (Eqv.eqv_dec_p r id) as [EQ | NEQ].
    - do 2 red in EQ.
      subst.
      contradiction.
    - unfold Eqv.eqv, eqv_raw_id in NEQ.
      eauto.
  Qed.

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
      apply incBlockNamed_Γ in Heqs3.
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
      denote_bks (convert_typ [] (add_comment bks comments)) ids ≈ denote_bks (convert_typ [] bks) ids.
  Proof.
    intros comments bks ids.
    induction bks.
    - cbn. reflexivity.
    - cbn.
      destruct ids as (bid_from, bid_src); cbn.
      match goal with
      | |- context[denote_bks ?bks (_, ?bid_src)] =>
        destruct (find_block dtyp bks bid_src) eqn:FIND
      end.
  Admitted.

  (* TODO: Move *)
  (* Could probably have something more general... *)
  Lemma add_comments_eutt :
    forall bk comments bids,
      denote_bks
        [fmap (typ_to_dtyp [ ]) (add_comments bk comments)] bids ≈ denote_bks [fmap (typ_to_dtyp [ ]) bk] bids.
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

  Lemma no_failure_helix_LU : forall {E X} s a (k : _ -> itree _ X) m,
      no_failure (E := E) (interp_helix (ITree.bind (trigger (MemLU s a)) k) m) ->
      exists v,
        no_failure (E := E) (interp_helix (k v) m) /\ memory_lookup m a ≡ Some v.
  Proof.
    intros * NOFAIL.
    rewrite interp_helix_bind in NOFAIL.
    Transparent interp_helix interp_Mem.
    unfold interp_helix in NOFAIL.
    unfold interp_Mem in NOFAIL.
    rewrite interp_state_trigger in NOFAIL.
    cbn* in *.
    simp.
    - unfold throw in *.
      rewrite interp_fail_vis in NOFAIL.
      cbn in *.
      rewrite bind_ret_l, translate_ret, bind_ret_l in NOFAIL.
      apply eutt_Ret in NOFAIL; contradiction NOFAIL; auto.
    - rewrite interp_fail_ret in NOFAIL.
      cbn in *; rewrite translate_ret, bind_ret_l in NOFAIL.
      eexists; split; eauto.
  Qed.
  Opaque interp_helix interp_Mem.

  (* Import ProofMode. *)
  Notation "'gep' τ e" := (OP_GetElementPtr τ e) (at level 10, only printing).
  Notation "'double'" := (DTYPE_Double) (at level 10, only printing).
  Notation "'arr'" := (DTYPE_Array) (at level 10, only printing).
  Notation "'to_nat'" := (MInt64asNT.to_nat) (only printing).

  Variant hidden_cont  (T: Type) : Type := boxh_cont (t: T).
  Variant visible_cont (T: Type) : Type := boxv_cont (t: T).
  Ltac hide_cont :=
    match goal with
    | h : visible_cont _ |- _ =>
      let EQ := fresh "HK" in
      destruct h as [EQ];
      apply boxh_cont in EQ
    | |- context[ITree.bind _ ?k] =>
      remember k as K eqn:VK;
      apply boxh_cont in VK
    end.
  Ltac show_cont :=
    match goal with
    | h: hidden_cont _ |- _ =>
      let EQ := fresh "VK" in
      destruct h as [EQ];
      apply boxv_cont in EQ
    end.
  Notation "'hidden' K" := (hidden_cont (K ≡ _)) (only printing, at level 10).
  Ltac subst_cont :=
    match goal with
    | h: hidden_cont _ |- _ =>
      destruct h; subst
    | h: visible_cont _ |- _ =>
      destruct h; subst
    end.

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

  (* TODO: Move? *)
  Opaque mem_lookup.
  Opaque mem_add.
  Opaque memory_lookup.
  Opaque memory_set.

  (* TODO: Move? *)
  Lemma mem_lookup_mem_add_neq :
    forall x y v bk,
      x ≢ y ->
      mem_lookup x (mem_add y v bk) ≡ mem_lookup x bk.
  Proof.
    intros x y v bk H.
    Transparent mem_lookup mem_add.
    cbn.
    Opaque mem_lookup mem_add.
    rewrite Memory.NM.Raw.Proofs.add_find.
    assert (match OrderedTypeEx.Nat_as_OT.compare x y with
            | OrderedType.EQ _ => Some v
            | _ => Memory.NM.Raw.find x (Memory.NM.this bk)
            end ≡ Memory.NM.Raw.find x (Memory.NM.this bk)) by admit.
    setoid_rewrite H0.
    reflexivity.
    admit.
  Admitted.

  Lemma mem_lookup_mem_add_eq :
    forall x v bk,
      mem_lookup x (mem_add x v bk) ≡ Some v.
  Proof.
    intros x v bk.
    Transparent mem_lookup mem_add.
    cbn.
    Opaque mem_lookup mem_add.
    rewrite Memory.NM.Raw.Proofs.add_find.
    admit.
    admit.
  Admitted.


  Lemma memory_lookup_memory_set_eq :
    forall x bk m,
      memory_lookup (memory_set m x bk) x ≡ Some bk.
  Proof.
    intros x bk m.
    Transparent memory_lookup memory_set.
    unfold memory_lookup, memory_set.
    Opaque memory_lookup memory_set.
    setoid_rewrite Memory.NM.Raw.Proofs.add_find.
    admit.
    admit.
  Admitted.

  (* TODO: Move? *)
  Lemma memory_lookup_memory_set_neq :
    forall m x y bk,
      x ≢ y ->
      memory_lookup (memory_set m x bk) y ≡ memory_lookup m y.
  Proof.
    intros m x y bk H.
    admit.
  Admitted.

  (* TODO: Move this and use it in aexpr proof as well *)
  Lemma repr_of_nat_to_nat :
    forall x,
      repr (Z.of_nat (MInt64asNT.to_nat x)) ≡ x.
  Proof.
    intros x.
    cbn.
    unfold MInt64asNT.to_nat.
    cbn.
    rewrite Znat.Z2Nat.id, repr_intval; auto.
    destruct (Int64.intrange x); lia.
  Qed.

  (* TODO: move this and prove this *)
  Lemma from_Z_intval :
    forall sz i,
      MInt64asNT.from_Z sz ≡ inr i ->
      sz ≡ Int64.intval i.
  Proof.
    intros sz i H.
  Admitted.

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
      admit.

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

  (* TODO: move this? *)
  Lemma maps_add_neq :
    forall {K} {V} {eqk : K -> K -> Prop} {RD : RelDec eqk} `{RelDec_Correct _ eqk} `{Symmetric _ eqk} `{Transitive _ eqk} (x id : K) (v : V) m,
      ~ eqk id x ->
      Maps.add x v m @ id ≡ m @ id.
  Proof.
    intros K V eqk RD RDC SYM TRANS H x id v m H0.
    cbn. unfold alist_add. 
    rewrite rel_dec_neq_false; eauto.
    eapply remove_neq_alist; eauto.
  Qed.

  Ltac remove_neq_locals :=
    match goal with
    | |- Maps.add ?x ?v ?l1 @ ?id ≡ ?l2 @ ?id =>
      assert (x ≢ id) by
          (eapply lid_bound_earlier; eauto;
           [eapply incLocal_lid_bound; eauto | solve_local_count]);
      setoid_rewrite maps_add_neq; eauto
    end.

  Lemma local_scope_preserved_bound_earlier :
    forall s1 s2 s3 x v l l',
      lid_bound s1 x ->
      s1 <<= s2 ->
      local_scope_preserved s2 s3 l l' ->
      local_scope_preserved s2 s3 l (Maps.add x v l').
  Proof.
    intros s1 s2 s3 x v l l' BOUND LT PRES.
    unfold local_scope_preserved.
    intros id BETWEEN.

    epose proof (lid_bound_earlier _ _ _ _ _ BOUND BETWEEN LT) as NEQ.
    unfold local_scope_preserved in PRES.
    setoid_rewrite maps_add_neq; eauto.
  Qed.

  Ltac solve_lid_bound :=
    eapply incLocal_lid_bound; eauto.

  Ltac solve_local_scope_preserved :=
    first [ apply local_scope_preserved_refl
          | eapply local_scope_preserved_bound_earlier;
            [solve_lid_bound | solve_local_count | solve_local_scope_preserved]
          ].

  Definition genIR_post (σ : evalContext) (s1 s2 : IRState) (to : block_id) (li : local_env)
    : Rel_cfg_T unit ((block_id * block_id) + uvalue) :=
    lift_Rel_cfg (state_invariant σ s2) ⩕
                 branches to ⩕
                 (fun sthf stvf => local_scope_modif s1 s2 li (fst (snd stvf))).

  (* TODO: move to vellvm *)
  Lemma handle_gep_addr_array_same_block :
    forall ptr ptr_elem ix sz τ,
      handle_gep_addr (DTYPE_Array sz τ) ptr
                      [DVALUE_I64 (repr 0); DVALUE_I64 ix] ≡ inr ptr_elem ->
      fst ptr ≡ fst ptr_elem.
  Proof.
    intros [ptrb ptro] [ptr_elemb ptr_elemo] ix sz τ GEP.
    cbn in GEP.
    inversion GEP; subst.
    reflexivity.
  Qed.

  (* TODO: move to vellvm *)
  Lemma handle_gep_addr_array_offset :
    forall ptr ptr_elem ix sz τ,
      handle_gep_addr (DTYPE_Array sz τ) ptr
                      [DVALUE_I64 (repr 0); DVALUE_I64 ix] ≡ inr ptr_elem ->
      snd ptr + DynamicValues.Int64.unsigned ix * sizeof_dtyp τ ≡ snd ptr_elem.
  Proof.
    intros [ptrb ptro] [ptr_elemb ptr_elemo] ix sz τ GEP.
    cbn in GEP.
    inversion GEP; subst.
    cbn.
    admit. (* Should hold *)
  Admitted.

  (* TODO: move to vellvm *)
  Lemma dtyp_fits_array_elem :
    forall m ptr ptr_elem ix sz τ,
      dtyp_fits m ptr (DTYPE_Array sz τ) ->
      handle_gep_addr (DTYPE_Array sz τ) ptr
                      [DVALUE_I64 (repr 0); DVALUE_I64 ix] ≡ inr ptr_elem ->
      Int64.intval ix < sz ->
      dtyp_fits m ptr_elem τ.
  Proof.
    intros m ptr ptr_elem ix sz τ FITS GEP SZ.
    cbn in GEP.
    unfold dtyp_fits in *.
    destruct FITS as (sz' & bytes & cid & BLOCK & BOUND).
    exists sz'. exists bytes. exists cid.
    split.
    erewrite <- handle_gep_addr_array_same_block; eauto.
    erewrite <- handle_gep_addr_array_offset; eauto.
    admit. (* Should hold *)
  Admitted.

  Opaque alist_add.

  (* TODO: move these *)
  Lemma in_local_or_global_scalar_not_in_gamma :
    forall r v ρ g m id v_id τ σ s,
      in_Gamma σ s id ->
      ~ in_Gamma σ s r ->
      in_local_or_global_scalar ρ g m (ID_Local id) v_id τ ->
      in_local_or_global_scalar (alist_add r v ρ) g m (ID_Local id) v_id τ.
  Proof.
    intros r v ρ g m id v_id τ σ s GAM NGAM INLG.
    destruct (Eqv.eqv_dec_p r id) as [EQ | NEQ].
    - do 2 red in EQ.
      subst.
      contradiction.
    - unfold Eqv.eqv, eqv_raw_id in NEQ.
      cbn in *.
      erewrite alist_find_neq; eauto.
  Qed.

  Ltac solve_in_gamma :=
    match goal with
    | GAM : nth_error (Γ ?s) ?n ≡ Some (ID_Local ?id, _),
            SIG : nth_error ?σ ?n ≡ Some _ |-
      in_Gamma _ _ ?id
      => econstructor; [eapply SIG | eapply GAM | eauto]
    end.

  Ltac solve_not_in_gamma :=
    first [
        match goal with
        | GAM : Gamma_safe ?σ ?si ?sf |- 
          ~ in_Gamma ?σ ?si ?id =>
          eapply GAM; solve_lid_bound_between
        end
      | solve [eapply not_in_Gamma_Gamma_eq; [eassumption | solve_not_in_gamma]]
      ].

  Ltac solve_id_neq :=
    first [ solve [eapply incLocal_id_neq; eauto; solve_local_count]
          | solve [eapply in_gamma_not_in_neq; [solve_in_gamma | solve_not_in_gamma]]
          ].

  Ltac solve_local_lookup :=
    first
      [ now eauto
      | solve [erewrite alist_add_find_eq; eauto]
      | solve [erewrite alist_find_neq; [solve_local_lookup|solve_id_neq]]
      ].

  Ltac solve_in_local_or_global_scalar :=
    first
      [ now eauto
      | solve [eapply in_local_or_global_scalar_not_in_gamma; [solve_in_gamma | solve_not_in_gamma | solve_in_local_or_global_scalar]]
      ].

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
           (interp_cfg (D.denote_bks (convert_typ [] bks) (bid_from,bid_in))
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

      rewrite denote_bks_unfold_not_in; cycle 1.
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

    - (* ** DSHAssign (x_p, src_e) (y_p, dst_e):
         Helix side:
         1. x_i <- evalPExpr σ x_p ;;
         2. y_i <- evalPExpr σ y_p ;;
         3. x <- memory_lookup_err "Error looking up 'x' in DSHAssign" mem x_i ;;
         4. y <- memory_lookup_err "Error looking up 'y' in DSHAssign" mem y_i ;;
         5. src <- evalNExpr σ src_e ;;
         6. dst <- evalNExpr σ dst_e ;;
         7. v <- mem_lookup_err "Error looking up 'v' in DSHAssign" (to_nat src) x ;;
         8. ret (memory_set mem y_i (mem_add (to_nat dst) v y))

         Vellm side:
         src_nexpcode ++
         dst_nexpcode ++
         px <- gep "src_p"[src_nexpr] ;;
         v  <- load px ;;
         py <- gep "dst_p"[dst_nexpr] ;;
         store v py
       *)

      cbn* in *; simp.
      hide_cfg.
      inv_resolve_PVar Heqs0.
      inv_resolve_PVar Heqs1.
      unfold denotePExpr in *; cbn* in *.
      simp. Time all:try_abs.
      all: apply no_failure_Ret in NOFAIL; try_abs.
      clean_goal.
      repeat apply no_failure_Ret in NOFAIL.
      edestruct @no_failure_helix_LU as (? & NOFAIL' & ?); eauto; []; clear NOFAIL; rename NOFAIL' into NOFAIL; cbn in NOFAIL; eauto.
      edestruct @no_failure_helix_LU as (? & NOFAIL' & ?); eauto; []; clear NOFAIL; rename NOFAIL' into NOFAIL; cbn in NOFAIL; eauto.
      rename s1 into si, s2 into sf,
      i5 into s1, i6 into s2,
      i8 into s3, i10 into s4,
      i11 into s5, i12 into s6,
      i13 into s7.
      rename n1 into x_p, n2 into y_p.
      rename a into x_i, a0 into y_i.
      rename x0 into y.
      clean_goal.

      hred.
      hstep; [eauto |].
      hred; hstep; [eauto |].
      hred.

      subst; eutt_hide_left.
      vjmp.
      unfold fmap, Fmap_block; cbn.
      vred.
      vred.
      vred.

      (* Step 5. *)
      subst. eapply eutt_clo_bind_returns; [eapply genNExpr_correct |..]; eauto.
      solve_state_invariant.
      solve_gamma_safe.

      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (PRE1 & [EXP1 EXT1 SCOPE1 VAR1 GAM1 MONO1]).
      cbn in *; inv_eqs.
      hvred.

      (* Step 6. *)
      eapply eutt_clo_bind_returns; [eapply genNExpr_correct |..]; eauto.
      solve_gamma_safe.

      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE0 as (PRE2 & [EXP2 EXT2 SCOPE2 VAR2 GAM2 MONO2]).
      cbn in *; inv_eqs.
      
      hvred.
      break_inner_match_hyp; break_inner_match_hyp; try_abs.
      2: apply no_failure_Ret in NOFAIL; try_abs.
      destruct_unit.

      rename vH into src, vH0 into dst, b into v.
      clean_goal.
      (* Step 7. *)
      hvred.
      hstep.
      unfold assert_NT_lt,assert_true_to_err in *; simp.
      hide_cont.
      clear NOFAIL.
      rename i1 into vsz.
      rename i0 into vx_p, i3 into vy_p.
      rename e into esrc.
      clean_goal.

      (* Question 1: is [vx_p] global, local, or can be either? *)
      (* We access in memory vx_p[e] *)
      edestruct memory_invariant_Ptr as (membk & ptr & LU & FITS & INLG & GETCELL); [| eauto | eauto |]; eauto.
      clear FITS.

      rewrite LU in H; symmetry in H; inv H.
      specialize (GETCELL _ _ Heqo1).
      clean_goal.
      (* I find some pointer either in the local or global environment *)
      destruct vx_p as [vx_p | vx_p]; cbn in INLG.
      { (* vx_p is in global environment *)
        edestruct denote_instr_gep_array as (ptr' & READ & EQ); cycle -1; [rewrite EQ; clear EQ | ..]; cycle 1.
        3: apply GETCELL.
        { vstep; solve_lu; reflexivity. }
        {
          destruct MONO2 as [| <-]. 
          - rewrite EXP1; auto.
            rewrite repr_of_nat_to_nat.
            cbn; reflexivity.
            eapply local_scope_preserve_modif; eauto.
            clear EXP1 EXP2 VAR1 VAR2.
            clean_goal.
            eapply Gamma_preserved_Gamma_eq; [exact GAM1 |].
            eapply Gamma_preserved_if_safe; [| exact SCOPE2].
            solve_gamma_safe.
          - rewrite EXP1.
            rewrite repr_of_nat_to_nat.
            reflexivity.
            eauto using local_scope_preserved_refl.
            eauto using Gamma_preserved_refl.
        }

        clear EXP1.
        clean_goal.
        
        subst_cont; vred.
        vred.
        (* load *)
        vstep.
        { vstep; solve_lu. }
        vred.
        hide_cont.

        destruct vy_p as [vy_p | vy_p].
        { (* vy_p in global *)
          assert (Γ si ≡ Γ sf) as CONT by solve_gamma.
          rewrite CONT in LUn0, LUn.
          edestruct memory_invariant_Ptr as (ymembk & yptr & yLU & yFITS & yINLG & yGETCELL); [| eapply Heqo0 | eapply LUn0 |]; [solve_state_invariant |].

          clean_goal.
          rewrite yLU in H0; symmetry in H0; inv H0.

          edestruct denote_instr_gep_array_no_read as (yptr' & yGEP & yEQ); cycle -1; [rewrite yEQ; clear yEQ | ..]; cycle 1.
          { vstep; solve_lu.
            cbn; reflexivity.
          }
          { rewrite EXP2.
            - rewrite repr_of_nat_to_nat.
              cbn; reflexivity.
            - clear EXP2.
              clean_goal.
              solve_local_scope_preserved.
            - destruct PRE2.
              (* TODO: can we automate this better? *)
              assert (Γ si ≡ Γ s7) as GAMsisf by solve_gamma.
              eapply Gamma_preserved_Gamma_eq. eapply GAMsisf.
              eapply Gamma_preserved_if_safe with (s2:=sf); eauto.
              solve_local_scope_modif.
          }

          { rewrite typ_to_dtyp_D_array in yFITS.
            assert (sz0 ≡ Int64.intval i4) by
                (apply from_Z_intval; eauto).
            subst.
            eauto.
          }

          vstep.
          subst_cont.
          vred.

          epose proof (write_succeeds _ _) as [m2 WRITE_SUCCEEDS].

          (* Store *)
          erewrite denote_instr_store; eauto.
          2: {
            vstep.
            - cbn.
              solve_local_lookup.
            - cbn.
              apply eqit_Ret.
              cbn.
              reflexivity.
          }

          2: {
            vstep.
            - cbn.
              solve_local_lookup.
            - cbn.
              apply eqit_Ret.
              cbn.
              reflexivity.
          }

          2: {
            cbn. reflexivity.
          }

          { vstep.
            rewrite denote_term_br_1.
            vstep.
            rewrite denote_bks_unfold_not_in.
            2: {
              (* TODO: Add a subst_cfg *)
              destruct VG; subst.
              cbn.

              unfold find_block.
              cbn.
              assert (bid_in ≢ nextblock).
              { (* Should hold from NEXT and Heqs *)
                eapply incBlockNamed_bound_between in Heqs.
                intros CONTRA; symmetry in CONTRA; revert CONTRA.
                eapply bid_bound_fresh; eauto.
                solve_prefix.
              }
              assert ((if Eqv.eqv_dec_p bid_in nextblock then true else false) ≡ false) as BID_NEQ.
              {
                unfold Eqv.eqv_dec_p.
                break_match_goal; [contradiction | reflexivity].
              }
              rewrite BID_NEQ.
              reflexivity.
            }
            
            vstep.

            apply eutt_Ret.
            cbn.
            split; [| split]; cbn.
            - (* State invariant *)
              cbn.
              split; eauto.
              destruct PRE2.
              unfold memory_invariant.
              intros n1 v0 τ x0 H4 H5.
              cbn in mem_is_inv.
              pose proof (mem_is_inv n1 v0 τ x0 H4 H5).

              (* TODO: can probably turn this into a lemma *)
              (* All depends on whether x0 == r, r1, or r0 *)
              destruct x0.
              { (* x0 is a global *)
                destruct v0.
                cbn. cbn in H4.
                { cbn in H. destruct H as (ptr_l & τ' & TYPE & INLG' & READ').
                  do 2 eexists.
                  repeat split; eauto.

                  destruct (Z.eq_dec (fst ptr_l) (fst yptr)) as [EQ | NEQ].
                  - destruct (Eqv.eqv_dec_p id vy_p) as [EQid | NEQid].
                    + do 2 red in EQid.
                      subst. cbn in yINLG.
                      assert (n1 ≡ y_p).
                      eapply st_no_id_aliasing; eauto.
                      subst.
                      rewrite Heqo0 in H4.
                      discriminate H4.
                    + unfold Eqv.eqv, eqv_raw_id in NEQid.
                      assert (fst ptr_l ≢ fst yptr).
                      { assert (ID_Global id ≢ ID_Global vy_p).
                        injection. apply NEQid.

                        eapply st_no_llvm_ptr_aliasing.
                        eapply H4.
                        eapply Heqo0.
                        3: eapply  H.
                        all: eauto.
                      }
                      contradiction.
                  - epose proof (IRState_is_WF _ _ H4) as [idT NT].
                    rewrite H5 in NT. cbn in NT. inv NT.
                    inv H1.

                    erewrite write_untouched; eauto.
                    constructor.
                    eapply sizeof_dvalue_pos.
                    cbn.
                    rewrite typ_to_dtyp_I.
                    constructor.

                    pose proof (handle_gep_addr_array_same_block _ _ _ _ yGEP) as YPTRBLOCK.
                    rewrite YPTRBLOCK in NEQ.
                    do 2 red. auto.
                }

                { cbn in H. destruct H as (ptr_l & τ' & TYPE & INLG' & READ').
                  do 2 eexists.
                  repeat split; eauto.

                  destruct (Z.eq_dec (fst ptr_l) (fst yptr)) as [EQ | NEQ].
                  - destruct (Eqv.eqv_dec_p id vy_p) as [EQid | NEQid].
                    + do 2 red in EQid.
                      subst. cbn in yINLG.
                      assert (n1 ≡ y_p).
                      eapply st_no_id_aliasing; eauto.
                      subst.
                      rewrite Heqo0 in H4.
                      discriminate H4.
                    + unfold Eqv.eqv, eqv_raw_id in NEQid.
                      assert (fst ptr_l ≢ fst yptr).
                      { assert (ID_Global id ≢ ID_Global vy_p).
                        injection. apply NEQid.

                        eapply st_no_llvm_ptr_aliasing.
                        eapply H4.
                        eapply Heqo0.
                        3: eapply  H.
                        all: eauto.
                      }
                      contradiction.
                  - epose proof (IRState_is_WF _ _ H4) as [idT NT].
                    rewrite H5 in NT. cbn in NT. inv NT.
                    inv H1.

                    erewrite write_untouched; eauto.
                    constructor.
                    eapply sizeof_dvalue_pos.
                    cbn.
                    rewrite typ_to_dtyp_D.
                    constructor.

                    pose proof (handle_gep_addr_array_same_block _ _ _ _ yGEP) as YPTRBLOCK.
                    rewrite YPTRBLOCK in NEQ.
                    do 2 red. auto.
                }
                destruct H as (bk_h & ptr_l & τ' & MINV).
                destruct MINV as (MLUP & MTYP & FITS & INLG' & GET).
                destruct (NPeano.Nat.eq_dec a y_i) as [ALIAS | NALIAS].
                - (* DSHPtrVals alias *)
                  subst.
                  rewrite yLU in MLUP.
                  inv MLUP.

                  epose proof (st_no_dshptr_aliasing _ _ _ _ _ Heqo0 H4); subst.
                  pose proof H5 as IDS.
                  rewrite LUn0 in IDS.
                  inv IDS.

                  (* Since y_i = a, we know this matches the block that was written to *)
                  exists (mem_add (MInt64asNT.to_nat dst) v bk_h).

                  (* *)
                  exists yptr. exists (TYPE_Array sz0 TYPE_Double).

                  split.
                  { rewrite memory_lookup_memory_set_eq. reflexivity. }
                  split; auto.
                  split.
                  eapply dtyp_fits_after_write; eauto.
                  split.
                  { cbn.
                    rewrite Heqo0 in H4.
                    rewrite LUn0 in H5.
                    inversion H5; subst; auto.
                  }
                  { (* Need to show that every lookup matches *)
                    intros i v0 H3.

                    (* TODO: do I even need this...? *)
                    assert (~(no_overlap_dtyp yptr' DTYPE_Double yptr (DTYPE_Array sz0 DTYPE_Double))) as OVER.
                    { erewrite <- from_Z_intval in yGEP; eauto.
                      eapply gep_array_ptr_overlap_dtyp; cbn; eauto.
                      rewrite repr_of_nat_to_nat.
                      admit.
                      lia.
                    }

                    (* Because I know that there is overlap, I know that fst yptr' = fst yptr  *)
        (*              *)

                    pose proof (dtyp_fits_allocated yFITS) as yALLOC.
                    epose proof (write_array_lemma _ _ _ _ _ _ yALLOC yGEP) as WRITE_ARRAY.
                    erewrite WRITE_ARRAY in WRITE_SUCCEEDS.

                    destruct (Nat.eq_dec i (MInt64asNT.to_nat dst)) as [EQdst | NEQdst].
                    {
                    (* In the case where i = DST *)

        (*                I know v0 = v (which is the value from the source (GETCELL) *)

        (*                I should be able to show that yptr' is GEP of yptr in this case... *)

        (*                May be able to use write array lemmas...? *)
        (*              *)

                      subst.
                      rewrite mem_lookup_mem_add_eq in H3; inv H3.

                      change (UVALUE_Double v0) with (dvalue_to_uvalue (DVALUE_Double v0)).
                      eapply write_array_cell_get_array_cell; eauto.
                      constructor.
                    }
                    {
                    (* In the case where i <> dst *)

        (*                I should be able to use yGETCELL along with H4 (getting rid of mem_add) *)
        (*              *)
                      rewrite mem_lookup_mem_add_neq in H3; auto.
                      erewrite write_array_cell_untouched; eauto.
                      constructor.
                    }
                  }
                - (* DSHPtrVals do not alias *)

                  (* This must be the case because if y_i <> a, then *)
        (*           we're looking at a different helix block. *)
                  exists bk_h.

                  cbn.
                  (* Need the pointer that matches up with @id *)
                  exists ptr_l. exists τ'.

                  rewrite memory_lookup_memory_set_neq; auto.
                  repeat split; auto.

                  eapply dtyp_fits_after_write; eauto.

                  assert (fst (ptr_l) ≢ fst yptr) as DIFF_BLOCKS.
                  { (* yINLG and INLG' *)
                    eapply st_no_llvm_ptr_aliasing.
                    6: eapply INLG'.
                    6: (* This is local now... *) { eapply in_local_or_global_addr_same_global. eapply yINLG. }
                    3: eapply H5.
                    3: eapply LUn0.
                    all: eauto.
                    intros CONTRA; inv CONTRA.
                    (* H5 and LUN5, means that n1 = y_p, which means a = y_i *)
                    assert (a ≡ y_i).
                    { assert (n1 ≡ y_p).
                      eapply st_no_id_aliasing; eauto.
                      subst.
                      rewrite Heqo0 in H4.
                      inv H4.
                      contradiction.
                    }
                    contradiction.
                  }

                  pose proof (dtyp_fits_allocated yFITS) as yALLOC.
                  epose proof (write_array_lemma _ _ _ _ _ _ yALLOC yGEP) as WRITE_ARRAY.
                  rewrite WRITE_ARRAY in WRITE_SUCCEEDS.

                  intros i v0 H3.
                  erewrite write_array_cell_untouched_ptr_block; eauto.
                  constructor.
              }

              { (* x0 is a local *)
                destruct v0. (* Probably need to use WF_IRState to make sure we only consider valid types *)
                solve_in_local_or_global_scalar.
                solve_in_local_or_global_scalar.

                destruct H as (bk_h & ptr_l & τ' & MINV). (* Do I need this? *)
                destruct (NPeano.Nat.eq_dec a y_i) as [ALIAS | NALIAS].
                - (* PTR aliases, local case should be bogus... *)
                  subst.

                  epose proof (st_no_dshptr_aliasing _ _ _ _ _ Heqo0 H4); subst.
                  rewrite LUn0 in H5.
                  inversion H5.
                - (* This is the branch where a and y_i don't *)
        (*              alias. These are the DSHPtrVal pointers... *)

        (*              DSHPtrVal a size1 corresponds to %id, which must be a local id. *)

        (*              I need to show the memory invariant holds. *)

        (*              - y_i points to ymembk *)
        (*              - a points to bk_h *)

        (*              no_pointer_aliasing is a given. *)

        (*              We should say that there exists bk_h and ptr_l. *)

        (*              The memory_lookup case should hold because we *)
        (*              don't care about the memory_set operation because *)
        (*              a <> y_i *)

        (*              mem_lookup_succeeds is as before. *)

        (*              dtyp_fits should hold because the write shouldn't *)
        (*              change the block for ptr_l at all (no aliasing). *)
                     
        (*              I need in_local_or_global_addr to hold, meaning I can find *)

        (*              l1 @ id = Some ptr_l *)

        (*              If id is in l0 then this follows from freshness and the old MINV. *)

        (*              Otherwise, there's actually a contradiction with *)
        (*              MINV's in_local_or_global_addr... Because id *)
        (*              would not be in l0. *)
        (*            *)

                  destruct MINV as (MLUP & MSUC & FITS & INLG' & GET).
                  subst.
                  cbn.
                  exists bk_h. exists ptr_l. exists τ'.
                  
                  rewrite memory_lookup_memory_set_neq; auto.
                  repeat (split; auto).
                  + admit. (* should hold might not need *)
                  + solve_local_lookup.
                  + intros i v0 H6.
                    pose proof (GET i v0 H6).
                    (* untouched part of memory, so this should hold *)
                    admit. (* TODO: do this one *)
              }

              + destruct PRE2. eapply st_no_id_aliasing; eauto.
              + eapply st_no_dshptr_aliasing; eauto.
              + (* TODO: turn this into a tactic? *)
                do 3 (eapply no_llvm_ptr_aliasing_not_in_gamma; [ | eauto | solve_not_in_gamma]).
                eapply state_invariant_no_llvm_ptr_aliasing; eauto.
              + admit.
            - exists bid_in. reflexivity.

            - (* The only local variables modified are in [si;sf] *)
              assert (local_scope_modif s6 sf ρ l0); solve_local_scope_modif.
          }
        }

        { (* vy_p in local *)
          assert (Γ si ≡ Γ sf) as CONT by solve_gamma.
          rewrite CONT in LUn0, LUn.
          edestruct memory_invariant_Ptr as (ymembk & yptr & yLU & yFITS & yINLG & yGETCELL); [| eapply Heqo0 | eapply LUn0 |]; [solve_state_invariant|].

          clean_goal.
          rewrite yLU in H0; symmetry in H0; inv H0.
          cbn in yINLG.

          edestruct denote_instr_gep_array_no_read as (yptr' & yGEP & yEQ); cycle -1; [rewrite yEQ; clear yEQ | ..]; cycle 1.
          { vstep.
            do 3 (setoid_rewrite lookup_alist_add_ineq; [eauto | solve_id_neq ]).
            reflexivity.
          }
          { rewrite EXP2.
            - rewrite repr_of_nat_to_nat.
              cbn; reflexivity.
            - clear EXP2.
              clean_goal.
              solve_local_scope_preserved.
            - admit.
          }

          { rewrite typ_to_dtyp_D_array in yFITS.
            assert (sz0 ≡ Int64.intval i4) by
                (apply from_Z_intval; eauto).
            subst.
            eauto.
          }

          vstep.
          subst_cont.
          vred.

          epose proof (write_succeeds _ _) as [m2 WRITE_SUCCEEDS].

          (* Store *)
          erewrite denote_instr_store; eauto.
          2: {
            vstep.
            - cbn.
              solve_local_lookup.
            - cbn.
              apply eqit_Ret.
              cbn.
              reflexivity.
          }

          2: {
            vstep.
            - cbn.
              solve_local_lookup.
            - cbn.
              apply eqit_Ret.
              cbn.
              reflexivity.
          }

          2: {
            cbn. reflexivity.
          }

          1: {
            vstep.
            rewrite denote_term_br_1.
            vstep.
            rewrite denote_bks_unfold_not_in.
            2: {
              (* TODO: Add a subst_cfg *)
              destruct VG; subst.
              cbn.

              unfold find_block.
              cbn.
              assert (bid_in ≢ nextblock).
              { (* Should hold from NEXT and Heqs *)
                eapply incBlockNamed_bound_between in Heqs.
                intros CONTRA; symmetry in CONTRA; revert CONTRA.
                eapply bid_bound_fresh; eauto.
                solve_prefix.
              }
              assert ((if Eqv.eqv_dec_p bid_in nextblock then true else false) ≡ false).
              {
                unfold Eqv.eqv_dec_p.
                break_match_goal; [contradiction | reflexivity].
              }
              rewrite H0.
              reflexivity.
            }
            
            vstep.

            apply eutt_Ret; split; [| split]; cbn.
            - admit. (* TODO: state_invariant *)
            - exists bid_in. reflexivity.
            - assert (local_scope_modif s6 sf ρ l0); solve_local_scope_modif.
          }
        }
      }

      { (* vx_p is in local *)
        admit.
      }

    - admit.
    - admit.
    - admit.
    - admit.

    - (* DSHLoop *)

      (* Require Import Correctness_While. *)
      (* (* Import ProofMode. *) *)
      (* Opaque add_comment. *)
      (* Opaque genWhileLoop. *)
      (* rewrite DSHLoop_interpreted_as_tfor. *)
      (* cbn* in *; simp; cbn in *. *)
      (* rewrite add_comment_eutt. *)
      (* clean_goal. *)

      (* pose proof *)
      (*      @genWhileLoop_tfor_correct "Loop_loop" (Name ("Loop_i" @@ string_of_nat (local_count i0))) b b0 l nextblock bid_in *)
      (*      {| block_count := block_count i3; local_count := local_count i3; void_count := void_count i3; Γ := l1 |} s2 l0 as GENC. *)
      (* forward GENC; [clear GENC |]. *)
      (* { *)
      (*   rename l into bodyV, b0 into entry_body. *)
      (*   (* Checking that we properly enter the body *) *)
      (*   admit. *)
      (* } *)
      (* forward GENC; [clear GENC |]. *)
      (* { *)
      (*   (* wf_cfg of the graph generated by genWhileLopo *) *)
      (*   admit. *)
      (* } *)
      (* forward GENC; [clear GENC |]. *)
      (* { *)
      (*   (* Freshness of nextblock *) *)
      (*   admit. *)
      (* } *)
      (* specialize (GENC n Heqs5 (option (memoryH * unit)%type)). *)

      (* match goal with *)
      (*   |- eutt _ (tfor ?bod _ _ _) _ => specialize (GENC bod) *)
      (* end. *)
      (* forward GENC; [clear GENC |]. *)
      (* { *)
      (*   rename n into foo. *)
      (*   clear -Heqs. *)
      (*   unfold MInt64asNT.from_nat in Heqs. *)
      (*   unfold MInt64asNT.from_Z in Heqs. *)
      (*   simp. *)
      (*   apply l0. *)
      (* } *)

      (* (* Invariant at each iteration *) *)
      (* specialize (GENC (fun k mH stV =>  *)
      (*                     match mH with *)
      (*                     | None => False *)
      (*                     | Some (mH,tt) => state_invariant σ s2 (* b *) mH stV *)
      (*                     end)). *)
      (* (* Precondition *) *)
      (* specialize (GENC (fun mH stV => *)
      (*                     match mH with *)
      (*                     | None => False *)
      (*                     | Some (mH,tt) => state_invariant σ s2 mH stV *)
      (*                     end)). *)
      (* (* Postcondition *) *)
      (* specialize (GENC (fun mH stV => *)
      (*                     match mH with *)
      (*                     | None => False *)
      (*                     | Some (mH,tt) => state_invariant σ s2 mH stV *)
      (*                     end)). *)
      
      (* Import ProofMode. *)

      (* eapply eutt_mon. *)
      (* 2: eapply GENC. *)

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
  (*     rewrite denote_bks_app; eauto. *)
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
        |- context[denote_bks ?x] =>
        remember x as bks
      end.
(*
      erewrite denote_bks_unfold.
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
        rewrite denote_bks_unfold.
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
        |- context[denote_bks ?x] =>
        remember x as bks
      end.
      (* Lemma about while loop instead *)
      (* erewrite denote_bks_unfold. *)
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
      rewrite denote_bks_app; eauto.
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
