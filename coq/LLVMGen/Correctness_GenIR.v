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


  Lemma compile_FSHCOL_correct :
    forall (** Compiler bits *) (s1 s2: IRState)
      (** Helix bits    *) (op: DSHOperator) (σ : evalContext) (memH : memoryH) 
      (** Vellvm bits   *) (nextblock bid_in bid_from : block_id) (bks : list (LLVMAst.block typ))
      (* (env : list (ident * typ)) *)  (g : global_env) (ρ : local_env) (memV : memoryV),
      bid_bound s1 nextblock ->
      (GenIR_Rel σ s1 bid_in ⩕ lift_Rel_cfg (fresh_pre s1 s2)) (memH,tt) (memV, (ρ, (g, (inl (bid_from, bid_in))))) ->
      no_failure (E := E_cfg) (interp_helix (denoteDSHOperator σ op) memH) -> (* Evaluation succeeds *)
      genIR op nextblock s1 ≡ inr (s2,(bid_in,bks)) ->
      eutt (succ_cfg (GenIR_Rel σ s2 nextblock ⩕ lift_Rel_cfg (fresh_post s1 s2 ρ)))
           (interp_helix (denoteDSHOperator σ op) memH)
           (interp_cfg (D.denote_bks (convert_typ [] bks) (bid_from,bid_in))
                       g ρ memV).
  Proof.
    intros s1 s2 op; revert s1 s2; induction op; intros * NEXT BISIM NOFAIL GEN.
    - cbn* in *.
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
      destruct BISIM as [[STATE [from BRANCH]] FRESH].
      cbn in STATE, BRANCH.
      split; cbn; eauto.
      2: solve_fresh.

      cbn in FRESH.
      split; [solve_state_invariant|].
      cbn. exists bid_in.
      reflexivity.
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
      destruct BISIM as [[BISIM1 [_bid EQ]] FRESH]; inv EQ.
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
      subst; eapply eutt_clo_bind_returns; [eapply genNExpr_correct_ind |..]; eauto.
      { split.
        - solve_state_invariant.
        - eapply freshness_pre_shrink; eauto; solve_local_count. (* TODO: make this part of solve_fresh *)
      }
      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      cbn in PRE; destruct PRE as ((INV1 & FRESH1) & EXP1 & ?); cbn in *; inv_eqs.
      hvred.

      (* Step 6. *)
      eapply eutt_clo_bind_returns; [eapply genNExpr_correct_ind |..]; eauto.
      { split.
        - solve_state_invariant.
        - solve_fresh.
      }

      introR; destruct_unit.
      intros RET _; eapply no_failure_helix_bind_continuation in NOFAIL; [| eassumption]; clear RET.
      cbn in PRE; destruct PRE as ((INV2 & FRESH2) & EXP2 & ?); cbn in *; inv_eqs.
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
      edestruct memory_invariant_Ptr as (NOALIAS & membk & ptr & LU & MEM_SUC & FITS & INLG & GETCELL); [| eauto | eauto |]; eauto.
      clear FITS.

      rewrite LU in H; symmetry in H; inv H.
      specialize (GETCELL _ _ Heqo1).
      clean_goal.
      (* I find some pointer either in the local or global environment *)
      destruct vx_p as [vx_p | vx_p]; cbn in INLG.
      { (* vx_p is in local environment *)
        edestruct denote_instr_gep_array as (ptr' & READ & EQ); cycle -1; [rewrite EQ; clear EQ | ..]; cycle 1.
        3: apply GETCELL.
        { vstep; solve_lu; reflexivity. }
        { rewrite EXP1; auto.
          rewrite repr_of_nat_to_nat.
          reflexivity.
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
          edestruct memory_invariant_Ptr as (yNOALIAS & ymembk & yptr & yLU & yMEM_SUC & yFITS & yINLG & yGETCELL); [| eapply Heqo0 | eapply LUn0 |]; [solve_state_invariant |].

          clean_goal.
          rewrite yLU in H0; symmetry in H0; inv H0.
          cbn in yINLG.

          (* TODO: clean this up *)
          unfold mem_lookup_succeeds in yMEM_SUC.
          edestruct (yMEM_SUC (MInt64asNT.to_nat dst)).
          apply Nat.ltb_lt in Heqb. lia.

          edestruct denote_instr_gep_array as (yptr' & yREAD & yEQ); cycle -1; [rewrite yEQ; clear yEQ | ..]; cycle 1.
          { vstep; solve_lu.
            cbn; reflexivity.
          }
          { rewrite EXP2.
            2:{ cbn. etransitivity. apply sub_alist_add.
                2: apply sub_alist_add.
                admit. admit. (* These should hold *)
            }

            rewrite repr_of_nat_to_nat.
            reflexivity.
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

              Set Nested Proofs Allowed.

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
                solve_not_ends_with.
                solve_not_ends_with.
              Qed.

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
              assert (bid_in ≢ nextblock) by admit.
              assert ((if Eqv.eqv_dec_p bid_in nextblock then true else false) ≡ false) as BID_NEQ by admit.
              rewrite BID_NEQ.
              reflexivity.
            }
            
            vstep.

            assert (Γ sf ≡ Γ si) as CONT by admit. (* This should hold *)
            
            apply eutt_Ret.
            cbn.
            split; cbn.
            split; cbn; eauto.
            - (* State invariant *)
              cbn.
              split; eauto.
              destruct INV2.
              unfold memory_invariant.
              intros n1 v0 τ x0 H0 H3.
              cbn in mem_is_inv.
              pose proof (mem_is_inv n1 v0 τ x0 H0 H3).

              (* TODO: can probably turn this into a lemma *)
              (* All depends on whether x0 == r, r1, or r0 *)
              destruct x0.
              { (* x0 is a global *)
                destruct v0.
                admit.
                admit.
                destruct H4 as (yNOALIAS' & bk_h & ptr_l & MINV).
                split; eauto.
                destruct (NPeano.Nat.eq_dec a y_i) as [ALIAS | NALIAS].
                - (* PTR aliases *)
                  subst.
                  pose proof (ptr_alias_eq _ yNOALIAS H0); subst.
                  exists (mem_add (MInt64asNT.to_nat dst) v ymembk). exists yptr.
                  split.
                  { rewrite memory_lookup_memory_set_eq. reflexivity. }
                  split.
                  { unfold mem_lookup_succeeds.
                    intros i H4.
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
                    rewrite Heqo0 in H0.
                    rewrite <- CONT in LUn0. rewrite LUn0 in H3.
                    inversion H3; subst; auto.
                  }
                  { intros i v0 H4.

                    (* Probably want this to be a lemma *)
                    apply write_correct in WRITE_SUCCEEDS.
                    destruct WRITE_SUCCEEDS.


                    (* Not sure about this... Will look at this tomorrow *)
                    Set Nested Proofs Allowed.
                    Lemma blah :
                      forall m1 m2 ptr ptr' i τ v uv,
                        write m1 ptr v ≡ inr m2 ->
                        ptr ≢ ptr' ->
                        get_array_cell m1 ptr' i τ ≡ inr uv ->
                        get_array_cell m2 ptr' i τ ≡ inr uv.
                    Proof.
                      intros m1 m2 ptr ptr' i τ v dv WRITE NEQ GET.
                      apply write_correct in WRITE.
                      destruct WRITE.
                      assert (dvalue_has_dtyp v τ) by admit. (* this is fantasy *)
                      specialize (is_written0 τ H).
                      destruct is_written0.

                      pose proof (get_array_succeeds_allocated _ _ _ _ GET) as ALLOC.
                      epose proof (read_array _ _ _ _ _ ALLOC).
                      edestruct read_array_exists.
                      admit.

                      destruct H1.

                      rewrite <- H2 in GET.

                      erewrite <- read_array.

                      rewrite old_lu0; eauto.

                      eapply sizeof_dvalue_pos; eauto.

                      admit.
                    Qed.

                    (* Should we show that yptr <> yptr' ?

                       Actually, ideally they don't even have the same block...
                     *)
                    unfold get_array_cell.
                    destruct (NPeano.Nat.eq_dec i (MInt64asNT.to_nat dst)) as [EQDST | NEQDST].
                    - subst.
                    destruct 
                    
                    eapply read_array.

                    admit.
                  }
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
                  edestruct H4 as [INl0 | NINl0].
                  admit.
                  admit.
                  (* + subst. *)
                  (*   cbn.                   *)
                  (*   exists bk_h. exists ptr'. *)

                  (*   rewrite memory_lookup_memory_set_neq; auto. *)
                  (*   repeat (split; auto). *)
                  (*   * admit. (* should hold might not need *) *)
                  (*   * (* This should all hold from the fact that id is *)
                  (*      in l0 and everything is fresh... *) *)

                  (*     (* This is hideous *) *)
                  (*     assert (id ?[ Logic.eq ] r0 ≡ false) as IDR0 by admit. *)
                  (*     rewrite IDR0. *)
                  (*     assert (negb (r0 ?[ Logic.eq ] r1) ≡ true) as R0R1 by admit. *)
                  (*     rewrite R0R1. *)
                  (*     cbn. *)
                  (*     assert (id ?[ Logic.eq ] r1 ≡ false) as IDR1 by admit. *)
                  (*     rewrite IDR1. *)
                  (*     cbn. *)
                  (*     assert (negb (r1 ?[ Logic.eq ] r) ≡ true) as R1R by admit. *)
                  (*     rewrite R1R. *)
                  (*     cbn. *)
                  (*     assert (negb (r0 ?[ Logic.eq ] r) ≡ true) as R0R by admit. *)
                  (*     rewrite R0R. *)
                  (*     cbn. *)
                  (*     assert (id ?[ Logic.eq ] r ≡ true) as IDR by admit. *)
                  (*     rewrite IDR. *)
                  (*     reflexivity. *)
                  (*   * intros i v0 H5. *)
                  (*     pose proof (GET i v0 H5). *)
                  (*     (* untouched part of memory, so this should hold *) *)
                  (*     admit. *)
                  (* + cbn in INLG'. *)
                  (*   exfalso. *)
                  (*   apply NINl0. eauto. *)
              }


                (* I should know that r, r1, and r0 are all used as local variables...

                   So if x0 is a global, it can't equal any of these...
                 *)
                (* assert ({id ≡ r0} + {id ≢ r0}) as [IDR0 | NIDR0] by apply rel_dec_p. *)
                (* - subst. cbn. *)
                (*   destruct v0. *)
                (*   cbn in H4. *)

                (* assert ({id ≡ r} + {id ≢ r}) as [IDR | NIDR] by apply rel_dec_p. *)
                (* - subst. cbn. *)
                (*   destruct v0; cbn; auto. *)
                (*   + unfold in_local_or_global_scalar in H4. *)
                (*     destruct H4. destruct H4. *)
                (*     exists x0. exists x1. *)
                (*     cbn in H4. *)
                (*     destruct H4, H5. *)
                (*     repeat (split; auto). *)

                (*     destruct x0. *)
                (*     cbn. *)

                (*     (* This means that this pointer (z, z0) has to be separate from yptr'... *) *)

              { (* x0 is a local *)
                destruct v0. (* Probably need to use WF_IRState to make sure we only consider valid types *)
                admit.
                admit.
                destruct H4 as (yNOALIAS' & bk_h & ptr_l & MINV). (* Do I need this? *)
                destruct (NPeano.Nat.eq_dec a y_i) as [ALIAS | NALIAS].
                - (* PTR aliases, local case should be bogus... *)
                  subst.
                  pose proof (ptr_alias_eq _ yNOALIAS H0); subst.
                  rewrite <- CONT in LUn0. rewrite LUn0 in H3.
                  inversion H3.
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

                  split; eauto.
                  destruct MINV as (MLUP & MSUC & FITS & INLG' & GET).
                  pose proof alist_In_dec id l0.
                  edestruct H4 as [INl0 | NINl0].
                  + subst.
                    cbn.                  
                    exists bk_h. exists ptr'.
                    
                    rewrite memory_lookup_memory_set_neq; auto.
                    repeat (split; auto).
                    * admit. (* should hold might not need *)
                    * (* This should all hold from the fact that id is
                       in l0 and everything is fresh... *)

                      (* This is hideous *)
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
                    * intros i v0 H5.
                      pose proof (GET i v0 H5).
                      (* untouched part of memory, so this should hold *)
                      admit. (* TODO: do this one *)
                  + cbn in INLG'.
                    exfalso.
                    apply NINl0. eauto.
              }
            - (* freshness_post *)
              cbn.
              admit.
          }
        }

        { (* vy_p in local *)
          edestruct memory_invariant_Ptr as (ymembk & yptr & yLU & yFITS & yINLG & yGETCELL); [| eapply Heqo0 | eapply LUn0 |]; [solve_state_invariant |].

          clean_goal.
          rewrite yLU in H0; symmetry in H0; inv H0.
          cbn in yINLG.

          edestruct denote_instr_gep_array as (yptr' & yREAD & yEQ); cycle -1; [rewrite yEQ; clear yEQ | ..]; cycle 1.
          { vstep; solve_lu.
            admit. (* ugh *)
          }
          { rewrite EXP2.
            2:{ cbn. etransitivity. apply sub_alist_add.
                2: apply sub_alist_add.
                admit. admit. (* These should hold *)
            }
            replace (repr (Z.of_nat (MInt64asNT.to_nat dst))) with dst by admit.
            cbn; reflexivity.
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
            split; cbn; eauto.
            - cbn.
              admit.
            - cbn.
              admit.
          }
        }
        Unshelve.
        all:admit.
      }

      (* vx_p is in global environment, should be largely the same. *)
      admit.
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
    - (* DSHLoop *) admit.
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
  Admitted.
  End GenIR.
 
