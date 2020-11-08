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

  (* TODO: Move this, and remove Transparent / Opaque *)
  Lemma incLocal_unfold :
    forall s,
      incLocal s ≡ inr
               ({|
                   block_count := block_count s;
                   local_count := S (local_count s);
                   void_count := void_count s;
                   Γ := Γ s
                 |}
                , Name ("l" @@ string_of_nat (local_count s))).
  Proof.
    intros s.
    Transparent incLocal.
    cbn.
    reflexivity.
    Opaque incLocal.
  Qed.

  (* TODO: Move this, and remove Transparent / Opaque *)
  Lemma incVoid_unfold :
    forall s,
      incVoid s ≡ inr
               ({|
                   block_count := block_count s;
                   local_count := local_count s;
                   void_count := S (void_count s);
                   Γ := Γ s
                 |}
                , Z.of_nat (void_count s)).
  Proof.
    intros s.
    Transparent incVoid.
    cbn.
    reflexivity.
    Opaque incVoid.
  Qed.

  Lemma genNExpr_context :
    forall nexp s1 s2 e c,
      genNExpr nexp s1 ≡ inr (s2, (e,c)) ->
      Γ s1 ≡ Γ s2.
  Proof.
    induction nexp;
      intros s1 s2 e c GEN;
      cbn in GEN; simp;
        repeat
          match goal with
          | H: ErrorWithState.option2errS _ (nth_error (Γ ?s1) ?n) ?s1 ≡ inr (?s2, _) |- _ =>
            destruct (nth_error (Γ s1) n); inversion H; subst
          | H: incLocal ?s1 ≡ inr (?s2, _) |- _ =>
            rewrite incLocal_unfold in H; cbn in H; inversion H; cbn; auto
          | IH: ∀ (s1 s2 : IRState) (e : exp typ) (c : code typ), genNExpr ?nexp s1 ≡ inr (s2, (e, c)) → Γ s1 ≡ Γ s2,
      GEN: genNExpr ?nexp _ ≡ inr _ |- _ =>
    rewrite (IH _ _ _ _ GEN)
    end; auto.
  Qed.

  Lemma genMExpr_context :
    forall mexp s1 s2 e c,
      genMExpr mexp s1 ≡ inr (s2, (e,c)) ->
      Γ s1 ≡ Γ s2.
  Proof.
    induction mexp;
      intros s1 s2 e c GEN;
      cbn in GEN; simp;
        repeat
          match goal with
          | H: ErrorWithState.option2errS _ (nth_error (Γ ?s1) ?n) ?s1 ≡ inr (?s2, _) |- _ =>
            destruct (nth_error (Γ s1) n); inversion H; subst
          | H: incLocal ?s1 ≡ inr (?s2, _) |- _ =>
            rewrite incLocal_unfold in H; cbn in H; inversion H; cbn; auto
          | IH: ∀ (s1 s2 : IRState) (e : exp typ) (c : code typ), genMExpr ?nexp s1 ≡ inr (s2, (e, c)) → Γ s1 ≡ Γ s2,
      GEN: genMExpr ?nexp _ ≡ inr _ |- _ =>
    rewrite (IH _ _ _ _ GEN)
    end; auto.
  Qed.

  Hint Resolve genNExpr_context : helix_context.
  Hint Resolve genMExpr_context : helix_context.
  Hint Resolve incVoid_Γ        : helix_context.
  Hint Resolve incLocal_Γ       : helix_context.
  Hint Resolve incBlockNamed_Γ  : helix_context.

  Lemma genAExpr_context :
    forall aexp s1 s2 e c,
      genAExpr aexp s1 ≡ inr (s2, (e,c)) ->
      Γ s1 ≡ Γ s2.
  Proof.
    induction aexp;
      intros s1 s2 e c GEN;
      cbn in GEN; simp;
        repeat
          match goal with
          | H: ErrorWithState.option2errS _ (nth_error (Γ ?s1) ?n) ?s1 ≡ inr (?s2, _) |- _ =>
            destruct (nth_error (Γ s1) n); inversion H; subst
          | H: incLocal ?s1 ≡ inr (?s2, _) |- _ =>
            rewrite incLocal_unfold in H; cbn in H; inversion H; cbn; auto
          | H: incVoid ?s1 ≡ inr (?s2, _) |- _ =>
            rewrite incVoid_unfold in H; cbn in H; inversion H; cbn; auto
          | IH: ∀ (s1 s2 : IRState) (e : exp typ) (c : code typ), genAExpr ?aexp s1 ≡ inr (s2, (e, c)) → Γ s1 ≡ Γ s2,
      GEN: genAExpr ?aexp _ ≡ inr _ |- _ =>
    rewrite (IH _ _ _ _ GEN)
  | GEN: genNExpr _ _ ≡ inr _ |- _ =>
    rewrite (genNExpr_context _ _ GEN)
  | GEN: genMExpr _ _ ≡ inr _ |- _ =>
    rewrite (genMExpr_context _ _ GEN)
    end; subst; auto.
  Qed.
  
  Ltac subst_contexts :=
    repeat match goal with
           | H : Γ ?s1 ≡ Γ ?s2 |- _ =>
             rewrite H in *; clear H
           end.

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

  Import ProofMode.
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

  Lemma state_invariant_sub_alist:
    forall σ s mH mV l1 l2 g,
      l1 ⊑ l2 ->
      state_invariant σ s mH (mV,(l1,g)) ->
      state_invariant σ s mH (mV,(l2,g)). 
  Proof.
    intros * SUB INV; inv INV.
    split; auto.
    cbn; intros * LUH LUV.
    eapply MINV in LUH; eapply LUH in LUV; clear MINV LUH.
    destruct v, x; cbn in *; auto.
    - apply SUB in LUV; auto.
    - apply SUB in LUV; auto.
    - destruct LUV as (? & ? & ? & LU & ?); do 2 eexists; repeat split; eauto.
      apply SUB in LU; auto.
  Qed.

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
    split; cbn.
    - rewrite EQ; apply MINV.
    - red. rewrite EQ; apply WF.
  Qed.
  
  Lemma compile_FSHCOL_correct :
    forall (** Compiler bits *) (s1 s2: IRState)
      (** Helix bits    *) (op: DSHOperator) (σ : evalContext) (memH : memoryH) 
      (** Vellvm bits   *) (nextblock bid_in bid_from : block_id) (bks : list (LLVMAst.block typ))
      (* (env : list (ident * typ)) *)  (g : global_env) ((* ρi  *)ρ : local_env) (memV : memoryV),
      bid_bound s1 nextblock ->
      (GenIR_Rel σ s1 bid_in (* ⩕ lift_Rel_cfg (fresh_pre s1 s2) *)) (memH,tt) (memV, (ρ, (g, (inl (bid_from, bid_in))))) ->
      Gamma_safe σ s1 s2 ->
      no_failure (E := E_cfg) (interp_helix (denoteDSHOperator σ op) memH) -> (* Evaluation succeeds *)
      genIR op nextblock s1 ≡ inr (s2,(bid_in,bks)) ->
      eutt (succ_cfg (GenIR_Rel σ s2 nextblock (* ⩕ lift_Rel_cfg (fresh_post s1 s2 ρ) *)))
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
          eapply bid_bound_incBlockNamed; eauto;
            solve_not_ends_with.
          solve_not_bid_bound.
          block_count_replace. lia.
          solve_not_ends_with.
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
      edestruct memory_invariant_Ptr as (membk & ptr & LU & INLG & GETCELL); [| eauto | eauto |]; eauto.

      rewrite LU in H; symmetry in H; inv H.
      specialize (GETCELL _ _ Heqo1).
      clean_goal.
      (* I find some pointer either in the local or global environment *)
      destruct vx_p as [vx_p | vx_p]; cbn in INLG.
      {
        edestruct denote_instr_gep_array as (ptr' & READ & EQ); cycle -1; [rewrite EQ; clear EQ | ..]; cycle 1.
        3: apply GETCELL.
        { vstep; solve_lu; reflexivity. }
        {
          destruct MONO2 as [| <-]. 
          - rewrite EXP1; auto.
            replace (repr (Z.of_nat (MInt64asNT.to_nat src))) with src by admit.
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
            replace (repr (Z.of_nat (MInt64asNT.to_nat src))) with src by admit.
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
        {
          edestruct memory_invariant_Ptr as (ymembk & yptr & yLU & yINLG & yGETCELL); [| eapply Heqo0 | eapply LUn0 |]; [solve_state_invariant |].
          assert (allocated yptr memV) as ALLOC by admit.
          assert (allocated yptr memV) as ALLOC' by admit.
          epose proof (write_array_exists _ _ _ _ _ _ ALLOC).
          destruct H as (addr & HANDLE & WRITE).

          clean_goal.
          rewrite yLU in H0; symmetry in H0; inv H0.
          cbn in yINLG.
          (* How do we know that ymembk is allocated? *)
        (*      yGETCELL does not contain any information here. *)
        (*    *)
          (* Oooh we don't, we're using [gep] but not for reading a cell here? *)
        (*      Not true though, the cell must be allocated, we are about to write in it. *)
        (*      We need another lemma about [OP_GetElementPtr] then. *)
        (*    *)
          edestruct denote_instr_gep_array as (yptr' & yREAD & yEQ); cycle -1; [rewrite yEQ; clear yEQ | ..]; cycle 1.
          { vstep; solve_lu.
            cbn; reflexivity.
          }
          { rewrite EXP2.
            - replace (repr (Z.of_nat (MInt64asNT.to_nat dst))) with dst by admit.
              reflexivity.
            - clear EXP2.
              clean_goal.
              admit. (* Need additional lemmas about [local_scope_preserved] *)
            - admit.
          }
          eapply yGETCELL.
          admit.

          vstep.
          subst_cont.
          vred.

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

          1: {
            vstep.
            rewrite denote_term_br_1.
            vstep.
            admit.
          }
          admit.
          admit.
          
        }
        admit.
      }
      admit.

    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - 
      cbn.

      pose proof GEN as GEN_DESTRUCT.
      cbn in GEN_DESTRUCT; simp.

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
          apply genIR_local_count in GEN_OP1; lia.
*)
  Admitted.
  End GenIR.
 
