Require Export Helix.DSigmaHCOL.DSigmaHCOLITree.
Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Paco.paco.
Import MInt64asNT.

Section Eval_Denote_Equiv.

  Hint Rewrite interp_Mem_bind : itree.
  Hint Rewrite interp_Mem_ret : itree.
  Hint Rewrite @interp_Mem_MemLU : itree.

  Ltac go := unfold denotePExpr, evalIUnCType, denoteIUnCType; autorewrite with itree.

  Ltac inv_sum :=
    match goal with
    | h: inl _ = inl _ |-  _ => inv h
    | h: inr _ = inr _ |-  _ => inv h
    | h: inl _ = inr _ |-  _ => inv h
    | h: inr _ = inl _ |-  _ => inv h
    | h: inl _ ≡ inl _ |-  _ => inv h
    | h: inr _ ≡ inr _ |-  _ => inv h
    | h: inl _ ≡ inr _ |-  _ => inv h
    | h: inr _ ≡ inl _ |-  _ => inv h
     end.

  Ltac inv_option :=
    match goal with
    | h: Some _ = Some _ |-  _ => inv h
    | h: None   = Some _ |-  _ => inv h
    | h: Some _ = None   |-  _ => inv h
    | h: None   = None   |-  _ => inv h
    | h: Some _ ≡ Some _ |-  _ => inv h
    | h: None   ≡ Some _ |-  _ => inv h
    | h: Some _ ≡ None   |-  _ => inv h
    | h: None   ≡ None   |-  _ => inv h
     end.

  Ltac simp' := repeat (inv_sum || inv_option || break_and || break_match_hyp).

  Lemma interp_Mem_MemLU :
    forall str mem m x,
      memory_lookup_err str mem x = inr m ->
      eutt equiv (interp_Mem (trigger (MemLU str x)) mem) (interp_Mem (Ret m) mem).
  Proof.
    intros str mem m x H.
    unfold trigger.
    setoid_rewrite interp_Mem_vis_eqit.
    cbn.
    break_match_goal; simp'.
    cbn; go.
    rewrite tau_eutt.
    cbn.
    apply eutt_Ret.
    now split.
  Qed.

  Lemma Denote_Eval_Equiv_MExpr: forall mem σ e bk size,
      evalMExpr mem σ e = inr (bk,size) ->
      eutt equiv
           (interp_Mem (denoteMExpr σ e) mem)
           (Ret (mem, (bk,size))).
  Proof.
    intros mem σ [] * EVAL.
    - cbn* in *; simp'.
      inv H1; cbn in *.
      go.
      rewrite Heqs.
      cbn.
      go.
      2: eapply memory_lookup_err_inr_Some_eq; eauto.
      apply eutt_Ret.
      split; cbn. reflexivity.
      now split; cbn.
    - cbn in EVAL.
      simp'.
      cbn; go.
      now apply eutt_Ret.
  Qed.

  Ltac ret_bind_l_right v :=
    match goal with
      |- eutt _ _ ?t =>
        rewrite <- (bind_ret_l v (fun _ => t))
    end.

  Definition eq_relation_het {A B} (R S : A -> B -> Prop) :=
    R <2= S /\ S <2= R.

  Lemma eqrel_simpl {A B} (R S : A -> B -> Prop) :
    eq_relation_het R S <->
      (forall a b, R a b <-> S a b).
  Proof.
    unfold eq_relation_het.
    split; intros; intuition.
    all: now apply H.
  Qed.

  Instance eutt_EQ_REL_Proper_het {E} {A B} :
    Proper (eq_relation_het ==> @eutt E A A eq ==> @eutt E B B eq ==> iff) (@eutt E A B).
  Proof.
    repeat red.
    intros; split; intros.
    -  rewrite <- H0. rewrite <- H1.
       clear H0 H1.
       destruct H.
       eapply eqit_mon; eauto.
    - rewrite H0, H1.
      destruct H.
      eapply eqit_mon; eauto.
  Qed.

  Instance eutt_EQUIV_REL_Proper_het {E} {A B} `{@Equivalence A ea} `{@Equivalence B eb} :
    Proper (eq_relation_het ==> @eutt E A A ea ==> @eutt E B B eb ==> iff) (@eutt E A B).
  Proof.
    repeat red.
    intros; split; intros.
    -
      rewrite <-H1.
      eapply eqit_mon.
      4: give_up.
      (*

      rewrite <- H0. rewrite <- H1.
      clear H0 H1.
      destruct H.
      eapply eqit_mon; eauto.
    -
      rewrite H0, H1.
      destruct H.
      eapply eqit_mon; eauto.
  Qed. *) Abort.

  Instance eutt_equiv_Proper {E} `{@Equivalence A ea} :
    Proper ((@eutt E A A ea) ==> (@eutt E A A ea) ==> (iff)) (@eutt E A A ea).
  Proof.
    intros x1 x2 EX y1 y2 EY.
    split; intros.
    now rewrite <-EX, <-EY.
    now rewrite EX, EY.
  Qed.

  (* TODO: rename or replace with existing *)
  Definition pointwise_impl {A B : Type} (RA : relation A) (RB : relation B)
    : relation (A -> B) :=
    fun f1 f2 => forall a1 a2, RA a1 a2 -> RB (f1 a1) (f2 a2).

  Instance pointwise_impl_Symmetric
    {A B : Type}
    `{Symmetric A RA}
    `{Symmetric B RB}
    :
    Symmetric (pointwise_impl RA RB).
  Proof.
    repeat red.
    intros.
    intuition.
  Qed.

  Instance pointwise_impl_Transitive
    {A B : Type}
    `{Reflexive A RA}
    `{Transitive B RB}
    :
    Transitive (pointwise_impl RA RB).
  Proof.
    repeat red.
    intros.
    etransitivity.
    eapply H1.
    reflexivity.
    now apply H2.
  Qed.

  Add Parametric Relation
    (A B : Type)
    (EA : relation A)
    (EB : relation B)
    (RA : @Reflexive A EA)
    (SA : @Symmetric A EA)
    (SB : @Symmetric B EB)
    (TB : @Transitive B EB)
    :
    (A -> B) (@pointwise_impl A B EA EB)
      symmetry proved by (@pointwise_impl_Symmetric A B EA SA EB SB)
      transitivity proved by (@pointwise_impl_Transitive A B EA RA EB TB)
      as pointwise_impl_Param.

  Instance ITree_bind_equiv_Proper {E} `{ea : relation A} `{eb : relation B} :
    Proper (@eutt E A A ea ==>
              pointwise_impl ea (@eutt E B B eb) ==>
              @eutt E B B eb)
      ITree.bind.
  Proof.
    intros x1 x2 X f1 f2 F.
    eapply eutt_clo_bind; eassumption.
  Qed.

  Definition pointwise_impl' {A B : Type} (RA : relation A) (RB : relation B)
    : relation (A -> B) :=
    fun f1 f2 => f1 ≡ f2 /\ Proper (RA ==> RB) f1.

  Lemma pointwise_impl_eq :
    forall {A B : Type} (RA : relation A) (RB : relation B) f1 f2,
      pointwise_impl' RA RB f1 f2 -> pointwise_impl RA RB f1 f2.
  Proof.
    unfold pointwise_impl', pointwise_impl.
    intros.
    destruct H; subst f2.
    eapply H1.
    assumption.
  Qed.

  Lemma pointwise_impl'_simp :
    forall {A B : Type} (RA : relation A) (RB : relation B) f,
      Proper (RA ==> RB) f ->
      pointwise_impl' RA RB f f.
  Proof.
    red.
    tauto.
  Qed.

  (* TODO : MOVE THIS TO ITREE *)
  Instance eutt_interp_state_eq {E F: Type -> Type} {S : Type} {R}
    (h : E ~> Monads.stateT S (itree F)) :
    Proper (eutt Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp_state E (itree F) S _ _ _ h R).
  Proof.
    repeat intro. subst. revert_until R.
    einit. ecofix CIH. intros.

    rewrite !unfold_interp_state. punfold H0. red in H0.
    induction H0; intros; subst; simpl; pclearbot.
    - eret.
    - etau.
    - ebind. econstructor; [reflexivity|].
      intros; subst.
      etau. ebase.
    - rewrite tau_euttge, unfold_interp_state; eauto.
    - rewrite tau_euttge, unfold_interp_state; eauto.
  Qed.

  Instance NTypeEquiv_Equivalence : Equivalence NTypeEquiv.
  Proof.
    (* REASON: [Fail typeclasses eauto.] *)
    apply NTypeSetoid.
  Qed.

  Definition decide_MemEventT_equiv {T : Type} (e : MemEvent T) : Equiv T :=
    match e with
    | MemLU _ _ => NM_Equiv
    | _ => equiv
    end.

  Instance decide_MemEventT_equiv_Equivalence `{e : MemEvent T} :
    Equivalence (decide_MemEventT_equiv e).
  Proof.
    destruct e; cbn.
    all: typeclasses eauto.
  Qed.

  Instance Mem_handler_Proper {T : Type} :
    forall e,
    Proper (equiv ==>
              eutt (@products.prod_equiv
                      memoryH equiv
                      T (decide_MemEventT_equiv e)))
      (Mem_handler T e).
  Proof.
    intros e m1 m2 M.
    unfold decide_MemEventT_equiv.
    destruct e; cbn.
    -
      pose proof (M id) as MID.
      unfold memory_lookup_err, memory_lookup, trywith.
      repeat break_match;
        try some_none; repeat some_inv;
        try inl_inr; repeat inl_inr_inv.
      +
        subst s s0; clear.
        cbn.
        admit.
      +
        subst m3 m4; clear - M MID.
        cbn.
        erewrite <-eutt_Ret.
        constructor.
        assumption.
        cbn.
        admit.
    -
      erewrite <-eutt_Ret.
      constructor.
      now rewrite M.
      cbn.
      reflexivity.
    -
      erewrite <-eutt_Ret.
      constructor.
      assumption.
      cbn.
      match goal with
      | |- ?x = ?y => enough (T : x ≡ y) by now rewrite T
      end.
      eapply memory_next_key_struct.
      intros.
      now rewrite M.
    -
      erewrite <-eutt_Ret.
      constructor.
      now rewrite M.
      reflexivity.
  Qed.
  
  (* See [interp_Mem_proper] *)
  Instance interp_Mem_equiv_proper {A} {e : Equiv A} {EQ : @Equivalence A e} :
    Proper ((eutt e) ==> equiv ==> (eutt equiv)) (@interp_Mem A).
  Proof.
    intros x1 x2 X m1 m2 M.
    unfold interp_Mem.
  Admitted.

  Lemma Denote_Eval_Equiv_NExpr: forall mem σ e v,
        evalNExpr σ e = inr v ->
        eutt equiv
             (interp_Mem (denoteNExpr σ e) mem)
             (Ret (mem, v)).
  Proof.
    induction e; cbn; intros * HEval; cbn* in *; simp; go;
      try inv_option; try inv_sum.
    all: try rewrite <-eutt_Ret.
    constructor; now cbn.
    constructor; now cbn.
    -
      admit.
    -
      admit.
    -
      specialize (IHe1 i).
      specialize (IHe2 i0).
      autospecialize IHe1; [reflexivity |].
      autospecialize IHe2; [reflexivity |].

      setoid_rewrite IHe1.
      eapply eutt_equiv_Proper.
      2: reflexivity.
      eapply ITree_bind_equiv_Proper.
      eassumption.
      {
        eapply pointwise_impl_eq.
        eapply pointwise_impl'_simp.
        clear.
        intros (m1, v1) (m2, v2) [M V].
        cbn in M, V.
        go.
        eapply ITree_bind_equiv_Proper.
        rewrite M.
        reflexivity.
        unfold pointwise_impl.
        intros (m1', v1') (m2', v2') [M' V'].
        cbn in M', V'.
        rewrite !interp_Mem_ret.
        apply eutt_Ret.
        constructor.
        now rewrite M'.
        now rewrite V, V'.
      }

      rewrite bind_ret_l.
      rewrite interp_Mem_bind.

      eapply eutt_equiv_Proper.
      2: reflexivity.
      eapply ITree_bind_equiv_Proper.
      eassumption.
      {
        eapply pointwise_impl_eq.
        eapply pointwise_impl'_simp.
        clear.
        intros (m1, v1) (m2, v2) [M V].
        cbn in M, V.
        go.
        apply eutt_Ret.
        constructor.
        now rewrite M.
        now rewrite V.
      }

      rewrite bind_ret_l.
      rewrite interp_Mem_ret.
      apply eutt_Ret.
      constructor.
      reflexivity.
      assumption.
  *) Admitted.

    Lemma Denote_Eval_Equiv_AExpr: forall mem σ e v,
        evalAExpr mem σ e = inr v ->
        eutt equiv
             (interp_Mem (denoteAExpr σ e) mem)
             (Ret (mem, v)).
    Proof. (*
      induction e; cbn; intros * HEval; cbn* in *; simp; go;
        try (reflexivity ||
             (rewrite IHe1; [| reflexivity]; go; rewrite IHe2; [| reflexivity]; go; reflexivity) ||
             (rewrite IHe; [| reflexivity]; go; reflexivity)).
      rewrite Denote_Eval_Equiv_NExpr; eauto; go;
             rewrite Denote_Eval_Equiv_MExpr; eauto; go;
             repeat match_rewrite; go; reflexivity.
    Qed. *) Admitted.

    Lemma Denote_Eval_Equiv_IMap: forall mem n f σ m1 m2 id,
        evalDSHIMap mem n f σ m1 m2 = inr id ->
        eutt equiv
             (interp_Mem (denoteDSHIMap n f σ m1 m2) mem)
             (Ret (mem, id)).
    Proof.
      induction n; intros; cbn* in *; simp; go; try reflexivity.
      all: try inv_sum.
      apply eutt_Ret.
      now constructor.

      eapply eutt_equiv_Proper.
      eapply ITree_bind_equiv_Proper.
      2: {
        match goal with
        | |- pointwise_impl _ _ ?f _ => instantiate (1:=f)
        end.
        instantiate (1:=equiv).
        apply pointwise_impl_eq.
        eapply pointwise_impl'_simp.
        clear.
        intros (mem1, v1) (mem2, v2) [M V].
        cbn in M, V.
        eapply interp_Mem_equiv_proper.
        2: assumption.
        cbv in V; subst.
        reflexivity.
      }
      rewrite Denote_Eval_Equiv_AExpr.
      reflexivity.
      unfold evalIUnCType in Heqs1.
      rewrite Heqs1.
      reflexivity.
      reflexivity.
      rewrite bind_ret_l.
      eapply IHn.
      assumption.
    Qed.

    Lemma Denote_Eval_Equiv_BinCType: forall mem σ f i a b v,
        evalIBinCType mem σ f i a b = inr v ->
        eutt equiv
             (interp_Mem (denoteIBinCType σ f i a b) mem)
             (Ret (mem, v)).
    Proof.
      unfold evalIBinCType, denoteIBinCType; intros.
      eapply Denote_Eval_Equiv_AExpr; eauto.
    Qed.

    Lemma Denote_Eval_Equiv_BinOp: forall mem n off σ f x y blk,
        evalDSHBinOp mem n off f σ x y = inr blk ->
        eutt equiv
             (interp_Mem (denoteDSHBinOp n off f σ x y) mem)
             (Ret (mem, blk)).
    Proof.
      induction n as [| n IH]; intros; cbn* in *; simp; go; try reflexivity.
      all: try inl_inr; repeat inl_inr_inv.
      apply eutt_Ret.
      now constructor.

      eapply eutt_equiv_Proper.
      eapply ITree_bind_equiv_Proper.
      2: {
        match goal with
        | |- pointwise_impl _ _ ?f _ => instantiate (1:=f)
        end.
        instantiate (1:=equiv).
        apply pointwise_impl_eq.
        eapply pointwise_impl'_simp.
        clear.
        intros (mem1, v1) (mem2, v2) [M V].
        cbn in M, V.
        eapply interp_Mem_equiv_proper.
        2: assumption.
        cbv in V; subst.
        reflexivity.
      }
      rewrite Denote_Eval_Equiv_BinCType.
      reflexivity.
      rewrite Heqs2; reflexivity.
      reflexivity.
      rewrite bind_ret_l.
      eapply IH.
      assumption.
    Qed.

    Import MonadNotation.
    Local Open Scope monad_scope.

    Definition denote_Loop_for_i_to_N σ body (i N: nat) :=
      iter (fun (p: nat) =>
              if EqNat.beq_nat p N
              then ret (inr tt)
              else
                vp <- lift_Serr (from_nat p) ;;
                denoteDSHOperator ((DSHnatVal vp , false):: σ) body;;
                Ret (inl (S p))
           ) i.

    Lemma denote_Loop_for_0_to_N:
      forall σ body N, eutt equiv (denote_Loop_for_i_to_N σ body 0 N) (denoteDSHOperator σ (DSHLoop N body)).
    Proof.
      unfold denote_Loop_for_i_to_N; reflexivity.
    Qed.

    (* loop over [i .. N)
       Some boundary cases:
       - i<N => either [Some _] or [None] if runs out of fuel
       - i>N => same as [eval_Loop_for_0_to_N]
       - N=0 =>
         - fuel=0 => [None]
         - fuel>0 => [Some (ret mem)] no-op
       - i=N =>
         - fuel=0 => [None]
         - fuel>0 => [Some (ret mem)] no-op

      NOTE: Struct [{struct N}] works instead of [{struct fuel}] here as well.
     *)
    Fixpoint eval_Loop_for_i_to_N σ body (i N: nat) mem fuel {struct fuel} :=
      match fuel with
      | O => None
      | S fuel =>
        match N with
        | O => Some (ret mem)
        | S N =>
          if EqNat.beq_nat i (S N) then
            Some (ret mem)
          else
            match eval_Loop_for_i_to_N σ body i N mem fuel with
            | Some (inr mem) =>
              match from_nat N with
              | inl msg => Some (inl msg)
              | inr vN =>
                evalDSHOperator ((DSHnatVal vN , false) :: σ) body mem fuel
              end
            | Some (inl msg) => Some (inl msg)
            | None => None
            end
        end
      end.

    Lemma eval_Loop_for_N_to_N: forall fuel σ op N mem,
        eval_Loop_for_i_to_N σ op N N mem (S fuel) ≡ Some (ret mem).
    Proof.
      intros fuel σ op [| N] mem; [reflexivity |].
      simpl; rewrite Nat.eqb_refl; reflexivity.
    Qed.

    (*
    Lemma eval_Loop_for_i_to_N_invert: forall σ i ii N op fuel mem_i mem_f,
        i < N ->
        from_nat i ≡ inr ii ->
        eval_Loop_for_i_to_N σ op i N mem_i fuel ≡ Some (inr mem_f) ->
        exists mem_aux,
          evalDSHOperator ((DSHnatVal ii , false) :: σ) op mem_i fuel ≡ Some (inr mem_aux) /\
          eval_Loop_for_i_to_N σ op (S i) N mem_aux fuel ≡ Some (inr mem_f).
    Proof.
      (* This proof is surprisingly painful to go through *)
      intros.
      (* Induction on the number of steps remaining *)
      remember (N - i) as k.
      revert σ fuel i ii N Heqk mem_i mem_f H0 H1 H.
      induction k as [| k IH];
        intros σ fuel i ii N EQ mem_i mem_f Hn Heval ineq;[lia|].

      (* N > 0 for us to be able to take a step *)
      destruct N as [| N]; [lia |].
      (* We got some fuel since the computation succeeded *)
      destruct fuel as [| fuel]; [inv Heval |].
      (* We can now reduce *)
      simpl in Heval.

      (* We know there's still a step to be taken *)
      destruct (i =? S N)%nat eqn:EQ'; [apply beq_nat_true in EQ'; lia | apply beq_nat_false in EQ'].
      (* And that the recursive call succeeded since the computation did *)
      destruct (eval_Loop_for_i_to_N σ op i N mem_i fuel) eqn: HEval'; [| inv Heval].
      destruct s; inv Heval.

      (* Now there are two cases:
         either a single step was remaining and we should be able to conclude directly;
         or more were remaining, and we should be able to conclude by induction
       *)

      destruct (i =? N)%nat eqn: EQ''; [apply beq_nat_true in EQ''; subst; clear IH |].
      - clear EQ' EQ ineq.
        rewrite Hn in H0.
        destruct fuel as [| fuel]; [inv HEval' |].
        rewrite eval_Loop_for_N_to_N in HEval'.
        setoid_rewrite eval_Loop_for_N_to_N.
        inv HEval'.
        exists mem_f.
        split; [apply evalDSHOperator_fuel_monotone; auto | auto ].
        rewrite Hn.
        auto.
      - destruct (from_nat N) eqn:NN.
        +
          eapply IH in HEval';[|lia|eauto|apply beq_nat_false in EQ''; lia].
          destruct HEval' as (mem_aux & STEP & TAIL).
          exists mem_aux; split; [apply evalDSHOperator_fuel_monotone; auto |].
          cbn; rewrite EQ'', TAIL.
          rewrite NN.
          reflexivity.
        +
          eapply IH in HEval';[|lia|eauto|apply beq_nat_false in EQ''; lia].
          destruct HEval' as (mem_aux & STEP & TAIL).
          exists mem_aux; split; [apply evalDSHOperator_fuel_monotone; auto |].
          cbn; rewrite EQ'', TAIL.
          rewrite NN.
          reflexivity.
    Qed.
     *)

    Lemma eval_Loop_for_i_to_N_invert: forall σ i ii N op fuel mem_i mem_f,
        i < N ->
        from_nat i ≡ inr ii ->
        eval_Loop_for_i_to_N σ op i N mem_i fuel = Some (inr mem_f) ->
        exists mem_aux,
          evalDSHOperator ((DSHnatVal ii , false) :: σ) op mem_i fuel = Some (inr mem_aux) /\
          eval_Loop_for_i_to_N σ op (S i) N mem_aux fuel = Some (inr mem_f).
    Proof.
      (* This proof is surprisingly painful to go through *)
      intros.
      (* Induction on the number of steps remaining *)
      remember (N - i) as k.
      revert σ fuel i ii N Heqk mem_i mem_f H0 H1 H.
      induction k as [| k IH];
        intros σ fuel i ii N EQ mem_i mem_f Hn Heval ineq;[lia|].

      (* N > 0 for us to be able to take a step *)
      destruct N as [| N]; [lia |].
      (* We got some fuel since the computation succeeded *)
      destruct fuel as [| fuel]; [inv Heval |].
      (* We can now reduce *)
      simpl in Heval.

      (* We know there's still a step to be taken *)
      destruct (i =? S N)%nat eqn:EQ'; [apply beq_nat_true in EQ'; lia | apply beq_nat_false in EQ'].
      (* And that the recursive call succeeded since the computation did *)
      destruct (eval_Loop_for_i_to_N σ op i N mem_i fuel) eqn: HEval'; [| inv Heval].
      destruct s; inv Heval.
      1: solve [inv H1].

      (* Now there are two cases:
         either a single step was remaining and we should be able to conclude directly;
         or more were remaining, and we should be able to conclude by induction
       *)

      destruct (i =? N)%nat eqn: EQ''; [apply beq_nat_true in EQ''; subst; clear IH |].
      - clear EQ' EQ ineq.
        rewrite Hn in H.
        destruct fuel as [| fuel]; [inv HEval' |].
        rewrite eval_Loop_for_N_to_N in HEval'.
        setoid_rewrite eval_Loop_for_N_to_N.
        inv HEval'.
        exists mem_f.
        split; [| reflexivity].
        apply evalDSHOperator_fuel_monotone_equiv.
        rewrite <-H.
        inv H1.
        now rewrite H3.
      - destruct (from_nat N) eqn:NN.
        +
          invc H.
          invc H1.
        +
          apply Option_equiv_eq in HEval'.
          eapply IH in HEval';[|lia|eauto|apply beq_nat_false in EQ''; lia].
          destruct HEval' as (mem_aux & STEP & TAIL).
          exists mem_aux; split; [apply evalDSHOperator_fuel_monotone_equiv; auto |].
          cbn.
          rewrite EQ'', NN.
          repeat break_match_goal; invc TAIL; invc H3.
          rewrite H4.
          rewrite <-H.
          invc H1.
          now rewrite H3.
    Qed.

    Lemma eval_Loop_for_i_to_N_i_gt_N σ op i N fuel mem:
      i > N ->
      eval_Loop_for_i_to_N σ op i N mem fuel ≡ eval_Loop_for_i_to_N σ op 0 N mem fuel.
    Proof.
      revert fuel.
      induction N; intros.
      +
        destruct fuel;reflexivity.
      +
        destruct fuel; [ reflexivity|].
        cbn.
        break_if; [apply beq_nat_true in Heqb; lia| ].
        apply beq_nat_false in Heqb.
        rewrite IHN.
        reflexivity.
        lia.
    Qed.

    Lemma eval_Loop_for_0_to_N:
      forall σ body N mem mem' fuel,
        evalDSHOperator σ (DSHLoop N body) mem fuel = Some (inr mem') ->
        eval_Loop_for_i_to_N σ body 0 N mem fuel = Some (inr mem').
    Proof.
      induction N as [| N IH]; intros.
      - destruct fuel; auto.
      - destruct fuel as [| fuel ]; [auto |].
        cbn in *.
        repeat break_match_hyp;
          try some_none; repeat some_inv;
          try inl_inr; repeat inl_inr_inv.
        apply Option_equiv_eq in Heqo.
        apply IH in Heqo.
        repeat break_match;
          try some_none; repeat some_inv;
          try inl_inr; repeat inl_inr_inv.
        now rewrite Heqo.
    Qed.

    Lemma eval_Loop_for_i_to_N_fuel_monotone:
      forall res σ op i N fuel mem,
        eval_Loop_for_i_to_N σ op i N mem fuel = Some res ->
        eval_Loop_for_i_to_N σ op i N mem (S fuel) = Some res.
    Proof.
      intros res σ op i N fuel mem H.
      revert H.
      revert res σ i fuel.
      induction N; intros.
      -
        destruct fuel; cbn in *; [some_none| apply H].
      -
        cbn.
        destruct fuel; [cbn in H; some_none|].
        break_if.
        +
          apply beq_nat_true in Heqb.
          subst.
          cbn in H.
          rewrite Nat.eqb_refl in H.
          apply H.
        +
          repeat break_match_goal; subst; cbn in H; rewrite Heqb in H.
          *
            rewrite <- Heqo.
            repeat break_match_hyp; subst;
              apply Option_equiv_eq in Heqo0.
            --
              rewrite <- H.
              apply IHN.
              apply Heqo0.
            --
              apply IHN in Heqo0.
              rewrite Heqo in Heqo0.
              inv Heqo0.
              inv H2.
            --
              apply IHN in Heqo0.
              rewrite Heqo in Heqo0.
              inv Heqo0.
              inv H2.
            --
              some_none.
          *
            repeat break_match_hyp; subst;
              apply Option_equiv_eq in Heqo0.
            --
              apply IHN in Heqo0.
              rewrite Heqo in Heqo0.
              inv Heqo0.
              inv H2.
            --
              apply IHN in Heqo0.
              rewrite Heqo in Heqo0.
              inv Heqo.
              inv Heqs1.
              apply H.
            --
              inv Heqs1.
            --
              some_none.
          *
            repeat break_match_hyp; subst;
              apply Option_equiv_eq in Heqo0.
            --
              apply IHN in Heqo0.
              rewrite Heqo in Heqo0.
              inv Heqo0.
              inv H2.
            --
              inv Heqs1.
            --
              apply IHN in Heqo0.
              rewrite Heqo in Heqo0.
              repeat some_inv; repeat inl_inr_inv; subst.
              rewrite Heqo0.
              destruct evalDSHOperator eqn:E in H; [| some_none].
              erewrite evalDSHOperator_fuel_monotone; eassumption.
            --
              some_none.
          *
            exfalso.
            break_match_hyp.
            --
              apply Option_equiv_eq in Heqo0.
              apply IHN in Heqo0.
              rewrite Heqo in Heqo0.
              some_none.
            --
              some_none.
    Qed.

    Lemma eval_Loop_for_i_to_N_fuel_monotone_gt:
      forall res σ op i N fuel fuel' mem,
        fuel'>fuel ->
        eval_Loop_for_i_to_N σ op i N mem fuel = Some res ->
        eval_Loop_for_i_to_N σ op i N mem fuel' = Some res.
    Proof.
      intros H.
      intros σ op i N fuel fuel' mem H0 H1.
      remember (fuel'-fuel) as d.
      assert(F: fuel' ≡ fuel + d) by lia.
      subst fuel'.
      clear H0 Heqd.
      induction d.
      -
        replace (fuel + 0) with fuel by lia.
        auto.
      -
        replace (fuel + S d) with (S (fuel + d)) by lia.
        apply eval_Loop_for_i_to_N_fuel_monotone.
        auto.
    Qed.

    (* Extend [from_nat_lt] to [le] *)
    Lemma from_nat_le:
      forall x xi y,
        from_nat x ≡ inr xi ->
        y<=x ->
        exists yi, from_nat y ≡ inr yi.
    Proof.
      intros.
      destruct (Nat.eq_dec x y).
      -
        subst.
        eexists.
        eauto.
      -
        eapply from_nat_lt; eauto.
        unfold lt, peano_naturals.nat_lt.
        lia.
    Qed.

    Lemma Loop_is_Iter_aux:
      ∀ (op : DSHOperator)
        (IHop: ∀ (σ : evalContext) (mem' : memory) (fuel : nat) (mem : memory),
            evalDSHOperator σ op mem (S fuel) = Some (inr mem')
            → eutt equiv (interp_Mem (denoteDSHOperator σ op) mem) (Ret (mem', ())))

        (i N: nat)
        (σ : evalContext) (mem : memory) (fuel : nat) (mem' : memory) {nn},
        from_nat N ≡ inr nn ->
        i <= (S N) ->
        eval_Loop_for_i_to_N σ op i (S N) mem (S fuel) = Some (inr mem')
        → eutt equiv
            (interp_state (case_ Mem_handler pure_state) (denote_Loop_for_i_to_N σ op i (S N)) mem) (Ret (mem', ())).
    Proof.
      intros op IHop i N σ mem fuel mem' nn NN ineq HEval.
      remember ((S N) - i) as k.
      revert Heqk σ mem mem' HEval.
      revert i ineq NN.
      induction k as [| k IH].
      - intros i ineq NN EQ.
        assert ((S N) ≡ i) by lia; clear EQ ineq; subst.
        intros.
        cbn in HEval.
        rewrite Nat.eqb_refl in HEval.
        inv HEval.
        unfold denote_Loop_for_i_to_N.
        (* poor man's [iter_unfold_pointed] *)
        match goal with
        | |- context[eutt equiv (interp_state ?h (iter ?k ?i) _) _] =>
            generalize (ITree.Basics.CategoryTheory.iter_unfold k);
            let EQ := fresh "EQ" in intros EQ; rewrite (EQ i); clear EQ
        end.
        cbn; go.
        rewrite Nat.eqb_refl.
        go. cbn; go.
        apply eutt_Ret.
        invc H1.
        now constructor.
      - intros i ineq NN EQ σ mem mem' HEval.
        destruct (i =? S N)%nat eqn:EQ'.
          * unfold eval_Loop_for_i_to_N in HEval; rewrite EQ' in HEval.
            inv HEval.
            unfold denote_Loop_for_i_to_N.
            (* poor man's [iter_unfold_pointed] *)
            match goal with
            | |- context[eutt equiv (interp_state ?h (iter ?k ?i) _) _] =>
                generalize (ITree.Basics.CategoryTheory.iter_unfold k);
                let EQ := fresh "EQ" in intros EQ; rewrite (EQ i); clear EQ
            end.
            cbn; go.
            rewrite EQ'.
            cbn; go.
            cbn; go.
            apply eutt_Ret.
            invc H1.
            now constructor.
          * unfold denote_Loop_for_i_to_N.
            (* poor man's [iter_unfold_pointed] *)
            match goal with
            | |- context[eutt equiv (interp_state ?h (iter ?k ?i) _) _] =>
                generalize (ITree.Basics.CategoryTheory.iter_unfold k);
                let EQ := fresh "EQ" in intros EQ; rewrite (EQ i); clear EQ
            end.
            cbn; go.
            rewrite EQ'; cbn*; go.
            apply beq_nat_false in EQ'.
            assert(exists ii : t, from_nat i ≡ inr ii) as II.
            {
              assert(i<=N) by lia.
              eapply from_nat_le;
              eauto.
            }
            destruct II as [ii II].
            rewrite II.
            cbn.
            apply eval_Loop_for_i_to_N_invert with (ii:=ii) in HEval; [|lia| apply II].
            destruct HEval as (mem_aux & Eval_body & Eval_tail).
            apply evalDSHOperator_fuel_monotone_equiv in Eval_body.
            apply IHop in Eval_body.
            go.
            (* rewrite Eval_body; cbn; go.
            cbn; go.
            apply IH in Eval_tail;try lia;auto.
    Qed. *) Admitted.

    Lemma Loop_is_Iter:
      ∀ (op : DSHOperator)
        (IHop: ∀ (σ : evalContext) (mem' : memory) (fuel : nat) (mem : memory),
            evalDSHOperator σ op mem (S fuel) = Some (inr mem')
            → eutt equiv (interp_Mem (denoteDSHOperator σ op) mem) (Ret (mem', ())))
        (N: nat) (σ : evalContext) (mem : memory) (fuel : nat) (mem' : memory),
        evalDSHOperator σ (DSHLoop N op) mem (S fuel) = Some (inr mem') ->
        eutt equiv (interp_state (case_ Mem_handler pure_state) (denoteDSHOperator σ (DSHLoop N op)) mem) (Ret (mem', ())).
    Proof.
      intros.
      destruct N.
      -
        cbn in H; inv H.
        cbn; go.
        (* poor man's [iter_unfold_pointed] *)
        match goal with
        | |- context[eutt equiv (interp_state ?h (iter ?k ?i) _) _] =>
            generalize (ITree.Basics.CategoryTheory.iter_unfold k);
            let EQ := fresh "EQ" in intros EQ; rewrite (EQ i); clear EQ
        end.
        cbn; go.
        cbn; go.
        apply eutt_Ret.
        invc H2.
        now constructor.
      -
        edestruct @evalDSHLoop_SN_in_range_equiv; eauto.
        apply eval_Loop_for_0_to_N in H.
        cbn; go.
        eapply Loop_is_Iter_aux;eauto.
        lia.
    Qed.

    Lemma Denote_Eval_Equiv_DSHMap2:
      forall n (σ: evalContext) mem f m1 m2 m3 m4,
        evalDSHMap2 mem n f σ m1 m2 m3  = inr m4 ->
        eutt equiv
             (interp_Mem (denoteDSHMap2 n f σ m1 m2 m3) mem)
             (Ret (mem, m4)).
    Proof.
      induction n as [| n IH]; intros σ mem f m1 m2 m3 m4 HEval; cbn in HEval.
      - inv_sum; cbn; go.
        apply eutt_Ret.
        now constructor.
      - cbn* in *; simp; go.
        unfold denoteBinCType; cbn.
        (* rewrite Denote_Eval_Equiv_AExpr; eauto; go.
        rewrite IH; eauto; go.
        reflexivity.
    Qed. *) Admitted.

    Lemma Denote_Eval_Equiv_DSHPower:
      forall n (σ: evalContext) mem f x y xoff yoff m,
        evalDSHPower mem σ n f x y xoff yoff = inr m ->
        eutt equiv
             (interp_Mem (denoteDSHPower σ n f x y xoff yoff) mem)
             (Ret (mem, m)).
    Proof.
      induction n as [| n IH]; intros σ mem f x y xoff yoff m HEval; cbn in HEval.
      - inv_sum; cbn; go.
        apply eutt_Ret.
        now constructor.
      - cbn* in *; simp; go.
        unfold denoteBinCType.
        (* rewrite Denote_Eval_Equiv_AExpr; eauto; go.
        rewrite IH; eauto; reflexivity.
    Qed. *) Admitted.

    Theorem Denote_Eval_Equiv:
      forall (σ: evalContext) (op: DSHOperator) (mem: memory) (fuel: nat) (mem': memory),
        evalDSHOperator σ op mem fuel = Some (inr mem') ->
        eutt equiv (interp_Mem (denoteDSHOperator σ op) mem) (Ret (mem', tt)).
    Proof.
      intros ? ? ? ? ? H; destruct fuel as [| fuel]; [inversion H |].
      revert σ mem' fuel mem H.
      induction op; intros σ mem fuel mem' HEval; cbn in HEval.
      - simp; cbn; go.
        apply eutt_Ret.
        invc HEval; invc H1.
        now constructor.
      - cbn* in *; simp; go.
        all: try some_none; repeat some_inv; try inl_inr; repeat inl_inr_inv.
        rewrite Heqs0; cbn; go.
        rewrite Heqs; cbn.
        go.
        3: cbn*; rewrite Heqo1; reflexivity.
        2: cbn*; rewrite Heqo0; reflexivity.
        rewrite Denote_Eval_Equiv_NExpr; eauto; go.
        rewrite Denote_Eval_Equiv_NExpr; eauto; go.
        repeat match_rewrite; go.
        rewrite interp_Mem_MemSet.
        apply eutt_Ret.
        now constructor.
      - cbn* in *; simp; go.
        all: try some_none; repeat some_inv; try inl_inr; repeat inl_inr_inv.
        cbn*; repeat match_rewrite; go.
        rewrite Heqs2. repeat match_rewrite; go.
        unfold assert_NT_le, assert_true_to_err in Heqs3.
        unfold assert_nat_le. unfold assert_true_to_err.
        break_if.
        go.
        3: cbn*; match_rewrite; eauto.
        2: cbn*; match_rewrite; eauto.
        rewrite  Denote_Eval_Equiv_IMap; eauto; go.
        rewrite interp_Mem_MemSet; reflexivity.
        exfalso.
        apply leb_complete_conv in Heqb.
        unfold to_nat in Heqb. break_if. 2 : inv Heqs3.
        eapply leb_complete in Heqb0.
        unfold to_nat in Heqb0. revert Heqb.
        apply le_not_lt. clear -Heqs Heqb0.
        unfold from_nat in Heqs.
        apply from_Z_intval in Heqs.
        rewrite <- Heqs in Heqb0.
        lia.
      - cbn* in *; simp; go.
        cbn*; repeat match_rewrite; go.
        rewrite Heqs2.
        repeat match_rewrite; go.
        2,3: cbn*; match_rewrite; eauto.
        rewrite  Denote_Eval_Equiv_BinOp; eauto; go.
        go.
        rewrite interp_Mem_MemSet; reflexivity.
      - cbn* in *; simp; go.
        cbn*; repeat match_rewrite; go.
        2,3,4: cbn*; match_rewrite; eauto.
        rewrite Denote_Eval_Equiv_DSHMap2; eauto; go.
        rewrite interp_Mem_MemSet; reflexivity.
      - cbn* in *; simp; go.
        cbn*; repeat match_rewrite; go.
        rewrite Heqs1.
        repeat match_rewrite; go.
        rewrite Denote_Eval_Equiv_NExpr; eauto; go.
        rewrite Denote_Eval_Equiv_NExpr; eauto; go.
        rewrite Denote_Eval_Equiv_NExpr; eauto; go.

        rewrite Heqs7. rewrite interp_Mem_ret. rewrite bind_ret_l.
        rewrite interp_Mem_bind.
        rewrite Denote_Eval_Equiv_DSHPower; eauto; go.
        2,3: cbn*; match_rewrite; eauto.
        rewrite interp_Mem_MemSet; reflexivity.
      - eapply Loop_is_Iter; eauto.
      - cbn; simp; go.
        Transparent interp_Mem.
        unfold interp_Mem.
        rewrite interp_state_trigger; cbn.
        Opaque interp_Mem.
        go.
        rewrite interp_Mem_MemSet; go.
        destruct fuel as [| fuel]; [inv Heqo |].
        rewrite IHop; eauto; go.
        Transparent interp_Mem.
        unfold interp_Mem.
        rewrite interp_state_trigger; cbn.
        reflexivity.
        Opaque interp_Mem.
      - cbn* in *; simp.
        unfold denotePExpr; cbn*; match_rewrite; go.
        2:cbn*; match_rewrite; eauto.
        rewrite interp_Mem_MemSet; reflexivity.
      - cbn; simp; go.
        rewrite IHop1; eauto using evalDSHOperator_fuel_monotone.
        go; rewrite IHop2; eauto using evalDSHOperator_fuel_monotone.
        reflexivity.
    Qed.

  End Eval_Denote_Equiv.
