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

  Definition GenIR_Rel σ (sinvs : IRState) to : Rel_cfg_T unit ((block_id * block_id) + uvalue) :=
    lift_Rel_cfg (state_invariant σ sinvs) ⩕ branches to. 

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

  (* TODO: move this? *)
  Ltac solve_local_lookup :=
    repeat
      (match goal with
       | |- context [ if ?x ?[ Logic.eq ] ?x then _ else _ ]
         => rewrite  eq_dec_eq
       | GEN1 : incLocal ?s1 ≡ inr (?s2, ?x),
                GEN2 : incLocal ?s3 ≡ inr (?s4, ?y)
         |- context [ if ?x ?[ Logic.eq ] ?y then _ else _ ]
         =>
         let H := fresh "NEQ"
         in assert (local_count s1 ≢ local_count s3) as H by solve_local_count;
            rewrite (eq_dec_neq (incLocal_id_neq GEN1 GEN2 H))
       | GEN1 : incLocal ?s1 ≡ inr (?s2, ?x),
                GEN2 : incLocal ?s3 ≡ inr (?s4, ?y)
         |- context [ if negb (?x ?[ Logic.eq ] ?y) then _ else _ ]
         => let H := fresh "NEQ"
           in assert (local_count s1 ≢ local_count s3) as H by solve_local_count;
              rewrite (eq_dec_neq (incLocal_id_neq GEN1 GEN2 H))
       end; cbn; auto).

  Lemma compile_FSHCOL_correct :
    forall (** Compiler bits *) (s1 s2: IRState)
      (** Helix bits    *) (op: DSHOperator) (σ : evalContext) (memH : memoryH) 
      (** Vellvm bits   *) (nextblock bid_in bid_from : block_id) (bks : list (LLVMAst.block typ))
      (* (env : list (ident * typ)) *)  (g : global_env) ((* ρi  *)ρ : local_env) (memV : memoryV),
      bid_bound s1 nextblock ->
      (GenIR_Rel σ s1 bid_in) (memH,tt) (memV, (ρ, (g, (inl (bid_from, bid_in))))) ->
      Gamma_safe σ s1 s2 ->
      no_failure (E := E_cfg) (interp_helix (denoteDSHOperator σ op) memH) -> (* Evaluation succeeds *)
      genIR op nextblock s1 ≡ inr (s2,(bid_in,bks)) ->
      eutt (succ_cfg (GenIR_Rel σ s2 nextblock))
           (interp_helix (denoteDSHOperator σ op) memH)
           (interp_cfg (D.denote_bks (convert_typ [] bks) (bid_from,bid_in))
                       g ρ memV).
  Proof.
    intros s1 s2 op; revert s1 s2; induction op; intros * NEXT PRE GAM NOFAIL GEN.
    - (* DSHNOp *)
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

      apply eutt_Ret; auto.
      destruct PRE as [STATE [from BRANCH]].
      cbn in *; split; cbn; eauto.
      eapply state_invariant_incVoid; eauto.
      eapply state_invariant_incBlockNamed; eauto.

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
      destruct PRE as [BISIM1 [_bid EQ]]; inv EQ.
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
      eapply Gamma_safe_shrink; eauto.
      repeat match goal with
               | h : incLocal _ ≡ _ |- _ => eapply incLocal_Γ in h
               | h : incVoid _ ≡ _ |- _ => eapply incVoid_Γ in h
               | h : incBlockNamed _ _ ≡ _ |- _ => eapply incBlockNamed_Γ in h
             end.
      rewrite Heqs7, Heqs6, Heqs5, Heqs4, Heqs3; auto. 
      solve_local_count.
      solve_local_count.

      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE as (PRE1 & [EXP1 EXT1 SCOPE1 VAR1 GAM1 MONO1]).
      cbn in *; inv_eqs.
      hvred.

      (* Step 6. *)
      destruct  PRE1.
      eapply eutt_clo_bind_returns; [eapply genNExpr_correct |..]; eauto.
      eapply Gamma_safe_shrink; eauto.
      repeat match goal with
             | h : incLocal _ ≡ _ |- _ => eapply incLocal_Γ in h
             | h : incVoid _ ≡ _ |- _ => eapply incVoid_Γ in h
             | h : incBlockNamed _ _ ≡ _ |- _ => eapply incBlockNamed_Γ in h
             end.
      rewrite <- Heqs, <- Heqs3, <- Heqs4, <- Heqs5, <- Heqs6, <- Heqs7; auto. 
      solve_local_count.
      solve_local_count.

      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      destruct PRE as (PRE2 & [EXP2 EXT2 SCOPE2 VAR2 GAM2 MONO2]).
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
      edestruct memory_invariant_Ptr as (membk & ptr & LU & MEM_SUC & FITS & INLG & GETCELL); [| eauto | eauto |]; eauto.
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
            eapply Gamma_safe_shrink; eauto.
            repeat match goal with
                   | h : incLocal _ ≡ _ |- _ => eapply incLocal_Γ in h
                   | h : incVoid _ ≡ _ |- _ => eapply incVoid_Γ in h
                   | h : incBlockNamed _ _ ≡ _ |- _ => eapply incBlockNamed_Γ in h
                   end.
            rewrite <- Heqs, <- Heqs3, <- Heqs4, <- Heqs5, <- Heqs6, <- Heqs7; auto. 
            solve_local_count.
            solve_local_count.
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
          edestruct memory_invariant_Ptr as (ymembk & yptr & yLU & yMEM_SUC & yFITS & yINLG & yGETCELL); [| eapply Heqo0 | eapply LUn0 |]; [solve_state_invariant |].

          clean_goal.
          rewrite yLU in H0; symmetry in H0; inv H0.
          cbn in yINLG.

          (* TODO: clean this up *)
          unfold mem_lookup_succeeds in yMEM_SUC.
          edestruct (yMEM_SUC (MInt64asNT.to_nat dst)).
          apply Nat.ltb_lt in Heqb. lia.

          edestruct denote_instr_gep_array' as (yptr' & yREAD & yGEP & yEQ); cycle -1; [rewrite yEQ; clear yEQ | ..]; cycle 1.
          { vstep; solve_lu.
            cbn; reflexivity.
          }
          { rewrite EXP2.
            - rewrite repr_of_nat_to_nat.
              cbn; reflexivity.
            - clear EXP2.
              clean_goal.

              (* TODO: make lemma *)
              unfold local_scope_preserved.
              intros id H0.
              destruct PRE2.
              cbn in H4.

              (* id is bound between s7 and sf

                 Heqs9

                 r1 is bound in s6
                 r is bound in s4
               *)

              
              admit. (* Need additional lemmas about [local_scope_preserved] *)
            - destruct PRE2.
              Set Nested Proofs Allowed.
              Lemma Gamma_preserved_extended_fresh :
                forall σ s l l' id v memH memV g,
                  Gamma_preserved σ s l l' ->
                  memory_invariant σ s memH (memV, (l', g)) ->
                  alist_fresh id l' ->
                  Gamma_preserved σ s l (Maps.add id v l').
              Proof.
                intros σ s l l' id v memH memV g GAMMA MINV FRESH.
                unfold Gamma_preserved in *.
                intros id0 IN.
                assert ({id ≡ id0} + {id ≢ id0}) as [EQ | NEQ] by admit. (* Should be fine... *)
                - subst.
                  destruct IN.
                  exfalso.
                  unfold alist_fresh in FRESH.
                  unfold memory_invariant in MINV.
                  destruct v0.
                  + epose proof (memory_invariant_LLU _ MINV H0 H).
                    cbn in H2.
                    rewrite FRESH in H2. discriminate H2.
                  + epose proof (memory_invariant_LLU_AExpr _ MINV H0 H).
                    cbn in H2.
                    rewrite FRESH in H2. discriminate H2.
                  + epose proof (memory_invariant_LLU_Ptr _ MINV H0 H).
                    cbn in H2.
                    destruct H2 as (bk & ptr & MLUP & MSUC & FITS & LUP & ?).
                    rewrite FRESH in LUP. discriminate LUP.
                - cbn. break_match_goal.
                  admit. (* I'm just lazy *)
                  rewrite remove_neq_alist; eauto.
                  (* These should hold *)
                  admit. 
                  admit.
              Admitted.

              eapply Gamma_preserved_extended_fresh.
              eapply Gamma_preserved_extended_fresh.
              eapply Gamma_preserved_refl.

              admit.
              admit.
              admit.
              admit.
          }

          eapply yGETCELL; eauto.

          vstep.
          subst_cont.
          vred.

          epose proof (@read_write_succeeds memV yptr' _ _ (DVALUE_Double v) yREAD) as (memV2 & WRITE_SUCCEEDS).
          constructor.

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
              assert (bid_in ≢ nextblock) by admit. (* Should hold from NEXT and Heqs *)
              assert ((if Eqv.eqv_dec_p bid_in nextblock then true else false) ≡ false) as BID_NEQ by admit.
              rewrite BID_NEQ.
              reflexivity.
            }
            
            vstep.

            assert (Γ sf ≡ Γ si) as CONT by admit. (* This should hold *)
            
            apply eutt_Ret.
            cbn.
            split; cbn.
            - (* State invariant *)
              cbn.
              split; eauto.
              destruct PRE2 as [SINV ?].
              destruct SINV.
              unfold memory_invariant.
              intros n1 v0 τ x0 H4 H5.
              cbn in mem_is_inv.
              pose proof (mem_is_inv n1 v0 τ x0 H4 H5).

              (* TODO: can probably turn this into a lemma *)
              (* All depends on whether x0 == r, r1, or r0 *)
              destruct x0.
              { (* x0 is a global *)
                destruct v0.
                cbn. cbn in H3. 
                admit.
                admit.
                destruct H3 as (bk_h & ptr_l & MINV).
                destruct MINV as (MLUP & MSUC & FITS & INLG' & GET).
                destruct (NPeano.Nat.eq_dec a y_i) as [ALIAS | NALIAS].
                - (* DSHPtrVals alias *)
                  subst.
                  rewrite yLU in MLUP.
                  inv MLUP.

                  epose proof (st_no_dshptr_aliasing _ _ _ _ _ Heqo0 H4); subst.

                  (* Since y_i = a, we know this matches the block that was written to *)
                  exists (mem_add (MInt64asNT.to_nat dst) v bk_h).

                  (* *)
                  exists yptr.


                  split.
                  { rewrite memory_lookup_memory_set_eq. reflexivity. }
                  split.
                  { unfold mem_lookup_succeeds.
                    intros i BOUNDS.
                    destruct (NPeano.Nat.eq_dec i (MInt64asNT.to_nat dst)) as [EQDST | NEQDST].
                    - subst. rewrite mem_lookup_mem_add_eq.
                      exists v. reflexivity.
                    - assert (size0 ≡ size1) by (eapply ptr_alias_size_eq; eauto); subst.
                      rewrite mem_lookup_mem_add_neq; eauto.
                  }
                  split.
                  admit. (* Might not need this, but should hold *)
                  split.
                  { cbn.
                    rewrite Heqo0 in H4.
                    rewrite <- CONT in LUn0. rewrite LUn0 in H5.
                    inversion H5; subst; auto.
                  }
                  { (* Need to show that every lookup matches *)
                    intros i v0 H3.

                    (* TODO: do I even need this...? *)
                    assert (~(no_overlap_dtyp yptr' DTYPE_Double yptr (DTYPE_Array sz0 DTYPE_Double))) as OVER.
                    { erewrite <- from_Z_intval in yGEP; eauto.
                      eapply gep_array_ptr_overlap_dtyp; cbn; eauto.
                      admit.
                      lia.
                    }

                    (* Because I know that there is overlap, I know that fst yptr' = fst yptr 
                     *)

                    pose proof (dtyp_fits_allocated yFITS) as yALLOC.
                    epose proof (write_array_lemma _ _ _ _ _ _ yALLOC yGEP) as WRITE_ARRAY.
                    rewrite WRITE_ARRAY in WRITE_SUCCEEDS.

                    destruct (Nat.eq_dec i (MInt64asNT.to_nat dst)) as [EQdst | NEQdst].
                    {
                    (* In the case where i = dst

                       I know v0 = v (which is the value from the source (GETCELL)

                       I should be able to show that yptr' is GEP of yptr in this case...

                       May be able to use write array lemmas...?
                     *)

                      subst.
                      rewrite mem_lookup_mem_add_eq in H3; inv H3.

                      change (UVALUE_Double v0) with (dvalue_to_uvalue (DVALUE_Double v0)).
                      eapply write_array_cell_get_array_cell; eauto.
                      constructor.
                    }
                    {
                    (* In the case where i <> dst

                       I should be able to use yGETCELL along with H4 (getting rid of mem_add)
                     *)
                      rewrite mem_lookup_mem_add_neq in H3; auto.
                      erewrite write_array_cell_untouched; eauto.
                      constructor.
                    }
                  }
                - (* DSHPtrVals do not alias *)

                  (* This must be the case because if y_i <> a, then
                  we're looking at a different helix block. *)
                  exists bk_h.

                  cbn.
                  cbn in INLG'.
                  (* Need the pointer that matches up with @id *)
                  exists ptr_l.

                  rewrite memory_lookup_memory_set_neq; auto.
                  repeat split; auto.

                  eapply dtyp_fits_after_write; eauto.

                  (* What if... fst (ptr_l) = fst yptr' and vice versa?

                     I think if they don't equal then they don't overlap...
                   *)

                  (* Can ptr_l = yptr'? *)

                  (* TODO: This should hold from extra memory invariant aliasing stuff. *)
                  assert (fst (ptr_l) ≢ fst yptr) as DIFF_BLOCKS. admit.

                  pose proof (dtyp_fits_allocated yFITS) as yALLOC.
                  epose proof (write_array_lemma _ _ _ _ _ _ yALLOC yGEP) as WRITE_ARRAY.
                  rewrite WRITE_ARRAY in WRITE_SUCCEEDS.

                  intros i v0 H3.
                  erewrite write_array_cell_untouched_ptr_block; eauto.
                  constructor.
              }

              { (* x0 is a local *)
                destruct v0. (* Probably need to use WF_IRState to make sure we only consider valid types *)
                admit.
                admit.
                destruct H3 as (bk_h & ptr_l & MINV). (* Do I need this? *)
                destruct (NPeano.Nat.eq_dec a y_i) as [ALIAS | NALIAS].
                - (* PTR aliases, local case should be bogus... *)
                  subst.

                  epose proof (st_no_dshptr_aliasing _ _ _ _ _ Heqo0 H4); subst.
                  rewrite <- CONT in LUn0. rewrite LUn0 in H5.
                  inversion H5.
                - (* This is the branch where a and y_i don't
                     alias. These are the DSHPtrVal pointers...

                     DSHPtrVal a size1 corresponds to %id, which must be a local id.

                     I need to show the memory invariant holds.

                     - y_i points to ymembk
                     - a points to bk_h

                     no_pointer_aliasing is a given.

                     We should say that there exists bk_h and ptr_l.

                     The memory_lookup case should hold because we
                     don't care about the memory_set operation because
                     a <> y_i

                     mem_lookup_succeeds is as before.

                     dtyp_fits should hold because the write shouldn't
                     change the block for ptr_l at all (no aliasing).
                     
                     I need in_local_or_global_addr to hold, meaning I can find

                     l1 @ id = Some ptr_l

                     If id is in l0 then this follows from freshness and the old MINV.

                     Otherwise, there's actually a contradiction with
                     MINV's in_local_or_global_addr... Because id
                     would not be in l0.
                   *)

                  destruct MINV as (MLUP & MSUC & FITS & INLG' & GET).
                  pose proof alist_In_dec id l0.
                  edestruct H3 as [INl0 | NINl0].
                  + subst.
                    cbn.                  
                    exists bk_h. exists ptr'.
                    
                    rewrite memory_lookup_memory_set_neq; auto.
                    repeat (split; auto).
                    * admit. (* should hold might not need *)
                    * (* This should all hold from the fact that id is
                       in l0 and everything is fresh... *)

                      (* This is hideous *)
                      (* automate. Make the add function opaque... *)
                      assert (id ?[ Logic.eq ] r0 ≡ false) as IDR0 by admit.
                      rewrite IDR0.
                      assert (negb (r0 ?[ Logic.eq ] r1) ≡ true) as R0R1 by admit.
                      rewrite R0R1.
                      cbn.
                      assert (id ?[ Logic.eq ] r1 ≡ false) as IDR1 by admit.
                      rewrite IDR1.
                      cbn.
                      assert (negb (r1 ?[ Logic.eq ] r) ≡ true) as R1R by admit.
                      rewrite R1R.
                      cbn.
                      assert (negb (r0 ?[ Logic.eq ] r) ≡ true) as R0R by admit.
                      rewrite R0R.
                      cbn.
                      assert (id ?[ Logic.eq ] r ≡ true) as IDR by admit.
                      rewrite IDR.
                      reflexivity.
                    * intros i v0 H6.
                      pose proof (GET i v0 H6).
                      (* untouched part of memory, so this should hold *)
                      admit. (* TODO: do this one *)
                  + cbn in INLG'.
                    exfalso.
                    apply NINl0. eauto.
              }

              + eapply WF_IRState_Γ;
                  eauto; symmetry; eapply incLocal_Γ; eauto.
              + destruct PRE2. eapply st_no_id_aliasing; eauto.
              + eapply st_no_dshptr_aliasing; eauto.
              + cbn.
                destruct PRE2 as [INV2 ?].
                eapply no_llvm_ptr_aliasing_not_in_gamma.
                eapply no_llvm_ptr_aliasing_not_in_gamma.
                eapply no_llvm_ptr_aliasing_not_in_gamma.
                eapply st_no_llvm_ptr_aliasing in INV2. cbn in INV2. eauto.

                (* TODO: these admits scare me *)
                eapply WF_IRState_Γ;
                  eauto; symmetry; eapply incLocal_Γ; eauto.
                admit.
                eapply WF_IRState_Γ;
                  eauto; symmetry; eapply incLocal_Γ; eauto.
                admit.
                eapply WF_IRState_Γ;
                  eauto; symmetry; eapply incLocal_Γ; eauto.
                admit.
            - exists bid_in. reflexivity.
          }
        }

        { (* vy_p in local *)
          edestruct memory_invariant_Ptr as (ymembk & yptr & yLU & yMEMSUC & yFITS & yINLG & yGETCELL); [| eapply Heqo0 | eapply LUn0 |]; [solve_state_invariant |].

          clean_goal.
          rewrite yLU in H0; symmetry in H0; inv H0.
          cbn in yINLG.

          edestruct denote_instr_gep_array as (yptr' & yREAD & yEQ); cycle -1; [rewrite yEQ; clear yEQ | ..]; cycle 1.
          { vstep; solve_lu.
            admit. (* ugh *)
          }
          { rewrite EXP2.
            - rewrite repr_of_nat_to_nat.
              cbn; reflexivity.
            - clear EXP2.
              clean_goal.
              admit. (* Need additional lemmas about [local_scope_preserved] *)
            - admit.
          }

          eapply yGETCELL.
          admit. (* Should be true because dst < size *)

          vstep.
          subst_cont.
          vred.

          epose proof (@read_write_succeeds memV yptr' _ _ (DVALUE_Double v) yREAD) as (memV2 & WRITE_SUCCEEDS).
          constructor.

          (* Store *)
          erewrite denote_instr_store; eauto.
          2: {
            vstep.
            - cbn.

              (* TODO: automate? *)
              assert (r1 ≢ r0) as NEQ by admit.
              assert (r0 ≢ r1) as NEQ' by auto.
              apply eq_dec_neq in NEQ.
              apply eq_dec_neq in NEQ'.
              rewrite NEQ, NEQ'.
              cbn.

              assert (r1 ≡ r1) as EQ by auto.
              eapply rel_dec_eq_true in EQ.

              rewrite EQ.
              reflexivity.
              apply RelDec_Correct_eq_typ.
            - cbn.
              apply eqit_Ret.
              cbn.
              reflexivity.
          }

          2: {
            vstep.
            - cbn.

              (* TODO: automate? *)
              assert (r0 ≡ r0) as EQ by auto.
              eapply rel_dec_eq_true in EQ.

              rewrite EQ.
              reflexivity.
              apply RelDec_Correct_eq_typ.
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
              assert (bid_in ≢ nextblock) by admit.
              assert ((if Eqv.eqv_dec_p bid_in nextblock then true else false) ≡ false) by admit.
              rewrite H0.
              reflexivity.
            }
            
            vstep.

            apply eutt_Ret.
            cbn.
            split; cbn.
            - admit. (* TODO: state_invariant *)
            - exists bid_in. reflexivity.
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
    - admit.
    - (* DSHAlloc *)
      cbn* in *.
      simp.
      cbn.
      clean_goal.
      hvred.

      Set Nested Proofs Allowed.
  Lemma interp_Mem_MemAlloc :
    forall size mem,
      interp_Mem (trigger (MemAlloc size)) mem ≈
                 Ret (mem, memory_next_key mem).
  Proof.
    intros size mem.
    setoid_rewrite interp_Mem_vis_eqit; cbn.
    rewrite bind_ret_l.
    rewrite interp_Mem_ret.
    apply tau_eutt.
  Qed.

  Lemma interp_helix_MemAlloc :
    forall {E} size mem,
      interp_helix (E := E) (trigger (MemAlloc size)) mem ≈
      Ret (Some (mem, memory_next_key mem)).
  Proof.
    intros.
    Transparent interp_helix.
    unfold interp_helix.
    Opaque interp_helix.
    setoid_rewrite interp_Mem_vis_eqit.
    cbn. rewrite Eq.bind_ret_l, tau_eutt.
    cbn; rewrite interp_Mem_ret, interp_fail_Ret, translate_ret.
    reflexivity.
  Qed.

  Import ProofMode.

  rewrite interp_helix_MemAlloc.
  hred.
  rewrite interp_helix_MemSet.
  hred.
  unfold add_comments; cbn.
  unfold fmap, Fmap_block; cbn.
  vjmp.
  rewrite find_block_eq; reflexivity.
  cbn.
  vred.
  vred.
  vred.
  edestruct denote_instr_alloca_exists as (mV' & addr & Alloc & EQAlloc);
    [| rewrite EQAlloc; clear EQAlloc].
  red; easy.
  vred.
  vred.
  admit.
  (* (* no_repeat assumption  *) *)
  (* rename b into target. *)
  (* vjmp. *)
  (* { *)
  (*   rewrite find_block_ineq. *)

  (*   apply find_block_tail_wf. *)
  (*   admit. *)
    

    - admit.
    - (* DSHSeq *)
      Opaque add_comment.
      cbn.

      pose proof GEN as GEN_DESTRUCT.
      cbn* in GEN_DESTRUCT; simp.

      rename i into s_op1, l0 into bk_op1, l into bk_op2.
      rename b into op2_entry, bid_in into op1_entry.
      rename Heqs0 into GEN_OP2, Heqs2 into GEN_OP1.
      rewrite add_comment_eutt.
      cbn.
      clean_goal.
        
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
      hvred.

      (* Helix generates code for op2 *first*, so op2 gets earlier
        variables from the irstate. Helix needs to do this because it
        passes the block id for the next block that an operator should
        jump to when it's done executing... So it generates code for
        op2, which goes to the next block of the entire sequence, and
        then passes the entry point for op2 as the "nextblock" for
        op1.
      *)
      cbn in NOFAIL.
      pose proof PRE as BISIM.
      destruct BISIM as [SINV (?from & EQ)]; cbn in *; inv EQ.
      simp.

      rename Heqs0 into GEN_OP2, Heqs1 into GEN_OP1.

      eapply eutt_clo_bind_returns.
      {
        eapply IHop1 with (s1:=s_op1) (s2:=s2).
        - eapply bid_bound_genIR_entry; eauto.
        - split.
          + cbn.
            apply genIR_Context in GEN_OP2.
            eapply state_invariant_Γ; eauto.
          + cbn; exists from; reflexivity.
        - eapply Gamma_safe_shrink; eauto.
          eauto using genIR_Context.
          solve_local_count.
          solve_local_count.
        - eapply no_failure_helix_bind_prefix; eauto.
        - auto.
      }

      clear IHop1.
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      cbn in PRE0; destruct PRE0 as [INV2 [from2 BRANCH2]]; cbn in *; inv_eqs.
      subst.

      eapply eqit_mon; auto.
      2: {
        eapply IHop2; try exact GEN_OP2; eauto.
        - split; cbn.
          eapply state_invariant_Γ; eauto.
          apply genIR_Context in GEN_OP1; apply genIR_Context in GEN_OP2; rewrite GEN_OP2; auto.
          exists from2; reflexivity.
        - eapply Gamma_safe_shrink; eauto.
          eauto using genIR_Context.
          solve_local_count.
          solve_local_count.
      }          
      clear IHop2.

      intros [[memH1 ?]|] (memV1 & l1 & g1 & res1) PR; [| inv PR].
      destruct PR as [? [? BR]].
      cbn in *.

      destruct res1 as [[from1 next] | v]; simp.

      split; cbn; eauto.
      eapply state_invariant_Γ; eauto.
      apply genIR_Context in GEN_OP1; auto.

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
