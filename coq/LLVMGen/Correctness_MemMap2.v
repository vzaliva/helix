Require Import Helix.MSigmaHCOL.MemSetoid.
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
Require Import Helix.LLVMGen.Context.
Require Import Helix.LLVMGen.Correctness_While.
Require Import Helix.LLVMGen.Correctness_AExpr.
Require Import Helix.LLVMGen.Pure.

Require Import Paco.paco.
From ITree Require Import ITree Eq.Eq HeterogeneousRelations.

Set Implicit Arguments.
Set Strict Implicit.

Opaque dropVars.
Opaque newLocalVar.
Opaque resolve_PVar.
Opaque incBlockNamed.
Opaque incVoid.
Opaque incLocal.
Opaque genWhileLoop.

Import Memory.NM.
Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope nat_scope.

Ltac interp_MF_ret := setoid_rewrite interp_Mem_ret; setoid_rewrite interp_fail_ret; cbn.
Ltac interp_MF_bind := setoid_rewrite interp_Mem_bind; setoid_rewrite interp_fail_bind; cbn.

Ltac final := apply eqit_Ret; eauto.
Ltac step :=
  first [progress vred_E3 | vred_I3];
  rewrite 1?interp_Mem_ret, 1?interp_fail_ret, 1?bind_ret_l;
  rewrite 1?interp_Mem_bind, 1?interp_fail_bind, 1?bind_bind;
  rewrite 1?interp_fail_throw, 1?bind_ret_l; cbn.

Definition mem_eq :=
      (fun (x y : option (memoryH * mem_block)) => match x, y with
                  | Some (mH, m), Some (mH', m') => mH ≡ mH' /\ m = m'
                  | None, None => True
                  | _, _ => False end).

Instance mem_eq_Equivalence : Equivalence mem_eq.
Proof.
  split.
  - red. intros [ []| ]. red.
    split; eauto. apply NM_Equiv_Reflexive.
    red. auto.
  - red. intros [ []| ] [ []| ]; red; cbn; intros []; auto.
    split; auto. apply NM_Equiv_Symmetric. auto.
  - red. intros [ []| ] [ []| ] [ []| ]; red; cbn; intros []; auto.
    intros []. split. rewrite H. auto.
    eapply NM_Equiv_Transitive; eauto.
Qed.

Lemma Returns_fail_throw :
  forall T m x s, not (Returns (Some x) (interp_fail handle_failure (interp_Mem (T := T) (throw s) m))).
Proof.
  intros. intro abs.
  setoid_rewrite interp_Mem_vis_eqit in abs.
  unfold pure_state in *; cbn in *.
  rewrite interp_fail_bind in abs.
  rewrite interp_fail_vis in abs.
  cbn in *.
  rewrite Eq.bind_bind, !bind_ret_l in abs.
  apply Returns_Ret in abs.
  inversion abs.
Qed.

Lemma commut_gen :
  forall {A : Type}
    (QQ : A -> A -> Prop) `{Equivalence A QQ}
    (t1 t2 : A -> itree void1 A) (m : A)
    (ti1 ti2 : itree void1 A),
    ti1 ≈ t1 m ->
    ti2 ≈ t2 m ->
    (eutt (fun m1' m2' => eutt QQ (t1 m1') (t2 m2')) (t2 m) (t1 m)) ->
    (eutt (fun m1' m2' => eutt QQ (t2 m1') (t1 m2')) (t1 m) (t2 m)) ->
    eutt QQ (a <- ti1 ;; t2 a) (a <- ti2  ;; t1 a).
Proof.
  intros. rewrite H0, H1. eapply eutt_clo_bind; eauto.
Qed.

Section DSHMemMap2_is_tfor.

  (* Iterative body of [MemMap2] *)
  Definition DSHMemMap2_body
             (σ : evalContext)
             (f : AExpr)
             (offset : nat)
             (init0 init1 acc : mem_block) :
             itree Event mem_block :=
    v0 <- lift_Derr (mem_lookup_err ("Error reading 1st arg memory in denoteDSHMap2 @" @@ Misc.string_of_nat offset @@ " in " @@ string_of_mem_block_keys init0) offset init0) ;;
    v1 <- lift_Derr (mem_lookup_err ("Error reading 2nd arg memory in denoteDSHMap2 @" @@ Misc.string_of_nat offset @@ " in " @@ string_of_mem_block_keys init1) offset init1) ;;
    v' <- denoteBinCType σ f v0 v1 ;;
    ret (mem_add offset v' acc).

  (* [tfor] formulation of [DSHMemMap2].
     "Reverse/downward" indexing ([n - 1 .. 0]). *)
  Definition DSHMemMap2_tfor_down
             (σ : evalContext)
             (f : AExpr)
             (i n e: nat)
             (init0 init1 acc : mem_block):
    itree Event mem_block :=
    (* MemMap2 has "reverse indexing" on its body *)
    tfor (fun i acc => DSHMemMap2_body σ f (e - 1 - i) init0 init1 acc) i n acc.

  (* "Right"-side-up indexing variant ([0 .. n - 1]). *)
  Definition DSHMemMap2_tfor_up
             (σ : evalContext)
             (f : AExpr)
             (i n : nat)
             (init0 init1 acc : mem_block):
    itree Event mem_block :=
    tfor (fun i acc => DSHMemMap2_body σ f i init0 init1 acc) i n acc.
    
  (* [denoteDSHMap2] is equivalent to [tfor] with "reverse indexing" on an
     [MemMap2] body. *)
  Lemma denoteDSHMap2_as_tfor:
    forall (σ : evalContext) n f x0 x1 y,
      denoteDSHMap2 n f σ x0 x1 y ≈ DSHMemMap2_tfor_down σ f 0 n n x0 x1 y.
  Proof.
    intros.
    unfold DSHMemMap2_tfor_down. revert y.
    induction n.
    - cbn. intros.
      setoid_rewrite tfor_0.
      reflexivity.
    - intros.
      rewrite tfor_unroll; [| lia].
      assert (S n - 1 - 0 ≡ n) by lia. rewrite H. cbn.
      repeat setoid_rewrite bind_bind.
      cbn.
      eapply eutt_clo_bind; [reflexivity |].
      intros u1 u2 H'.
      eapply eutt_clo_bind; [reflexivity|].
      intros u0 u3 H''. subst.
      eapply eutt_clo_bind; [reflexivity|].
      intros; subst. rewrite bind_ret_l.
      rewrite IHn.

      setoid_rewrite tfor_ss_dep. 3 : lia.
      reflexivity. intros.
      cbn. assert (n - 0 - S i ≡ n - 1 - i) by lia. rewrite H0. reflexivity.
  Qed.

  Lemma swap_body_interp:
    forall (n n' : nat) (σ : evalContext) (f : AExpr) (x0 x1 : mem_block) mH init,
    eutt (E := E_cfg) mem_eq
            (interp_helix (a <- DSHMemMap2_body σ f n x0 x1 init ;; DSHMemMap2_body σ f n' x0 x1 a) mH)
            (interp_helix (a <- DSHMemMap2_body σ f n' x0 x1 init ;; DSHMemMap2_body σ f n x0 x1 a) mH).
  Proof.
    intros *.

    eapply eutt_translate_gen.
    Transparent DSHMemMap2_body.
    cbn.
    do 2 rewrite interp_Mem_bind.
    do 2 rewrite interp_fail_bind.

    eapply eutt_Proper_mono; cycle 1.
    eenough (HH : _).
    eapply commut_gen with (m := Some (mH, init))
                              (QQ := fun x y => match x, y with
                                             | Some (mH, x), Some (mH', y) => mH ≡ mH' /\ NM_Equiv x y
                                             | None, None => True
                                             | _, _ => False
                                             end) ; unfold Monad.eq1, ITreeMonad.Eq1_ITree.
    4: revert n n'; eapply HH.
    4: eapply HH.
    4: clear n n'; intros n n'.
    {
      split; repeat intro.
      destruct x as [ [] |] eqn: H.
      split; eauto. reflexivity. eauto.
      destruct x as [ [] |] eqn: H'.
      destruct y as [ [] |] eqn: H''.
      destruct H; eauto. subst. split; eauto.
      symmetry. auto.
      inv H.
      destruct y. inv H. auto.

      destruct x as [ [] |] eqn: H'; destruct y as [ [] |] eqn: H'';
        destruct z as [ [] |] eqn: H'''; try inv H; auto.
      destruct H0. subst. split; auto.
      etransitivity; eauto.
    }

    { reflexivity. }
    { reflexivity. }

    {
      Import ProofMode. cbn.
      hred. vred. vred.
      do 2 step.
      unshelve eapply eutt_clo_bind_returns.

      exact (fun l r =>
                       ((exists s, mem_lookup_err
                       ("Error reading 1st arg memory in denoteDSHMap2 @" @@
                        Misc.string_of_nat n' @@ " in " @@ string_of_mem_block_keys x0) n'
                       x0 ≡ inl s /\ l ≡ None) \/
                       (exists b, mem_lookup_err
                       ("Error reading 1st arg memory in denoteDSHMap2 @" @@
                        Misc.string_of_nat n' @@ " in " @@ string_of_mem_block_keys x0) n'
                       x0 ≡ inr b /\ l ≡ Some (mH, b))) /\
                       ((exists s, mem_lookup_err
                       ("Error reading 1st arg memory in denoteDSHMap2 @" @@
                        Misc.string_of_nat n @@ " in " @@ string_of_mem_block_keys x0) n
                       x0 ≡ inl s /\ r ≡ None) \/
                        (exists b, mem_lookup_err
                        ("Error reading 1st arg memory in denoteDSHMap2 @" @@
                         Misc.string_of_nat n @@ " in " @@ string_of_mem_block_keys x0) n
                        x0 ≡ inr b /\ r ≡ Some (mH, b)))).

      unfold lift_Derr.
      break_match. break_match.
      { setoid_rewrite interp_Mem_vis_eqit.
        unfold pure_state in *; cbn in *.
        rewrite !interp_fail_bind.
        rewrite !interp_fail_vis.
        cbn in *. step. final.
        split; eauto. }
      { setoid_rewrite interp_Mem_vis_eqit.
        unfold pure_state in *; cbn in *.
        rewrite !interp_fail_bind.
        rewrite !interp_fail_vis.
        cbn in *. step. final.
        split; eauto. }
      { step. step. break_match; step; final; split; eauto. }

      (* EUTT_CLO_BIND continuation *)
      intros. cbn in H.
      destruct H as [[[? []] | [? []]] [[? []] | [? []]]]; subst; cbn.
      { do 2 final. }
      { rewrite H, H3.
        unfold lift_Derr; cbn.
        break_match.
        { repeat step; repeat final. }
        unfold denoteBinCType.
        repeat step.
        edestruct genAExpr_correct_helix_pure_classic
          with (aexp := f) as [HA | (? & HA)];
          setoid_rewrite HA.
        + step; repeat final.
        + repeat step; final.
          break_match; repeat step; final.
      }
      { rewrite H, H3.
        unfold lift_Derr; cbn.
        break_match.
        - break_match.
          { repeat step; repeat final. }
          unfold denoteBinCType.
          repeat step.
          edestruct genAExpr_correct_helix_pure_classic
            with (aexp := f) as [HA | (? & HA)];
            setoid_rewrite HA.
          + step; repeat final.
          + repeat step; final.
            repeat step; final.
        - break_match.
          { repeat step; repeat final. }
          unfold denoteBinCType.
          repeat step.
          edestruct genAExpr_correct_helix_pure_classic
            with (aexp := f) as [HA | (? & HA)];
            setoid_rewrite HA.
          + step; repeat final.
          + repeat step; final.
            repeat step; final.
      }

      do 2 step.
      unshelve eapply eutt_clo_bind_returns.

      exact (fun l r =>
                       ((exists s, mem_lookup_err
                       ("Error reading 2nd arg memory in denoteDSHMap2 @" @@
                        Misc.string_of_nat n' @@ " in " @@ string_of_mem_block_keys x1) n'
                        x1 ≡ inl s /\ l ≡ None) \/
                       (exists b, mem_lookup_err
                       ("Error reading 2nd arg memory in denoteDSHMap2 @" @@
                        Misc.string_of_nat n' @@ " in " @@ string_of_mem_block_keys x1) n'
                        x1 ≡ inr b /\ l ≡ Some (mH, b))) /\
                       ((exists s, mem_lookup_err
                       ("Error reading 2nd arg memory in denoteDSHMap2 @" @@
                        Misc.string_of_nat n @@ " in " @@ string_of_mem_block_keys x1) n
                        x1 ≡ inl s /\ r ≡ None) \/
                        (exists b, mem_lookup_err
                        ("Error reading 2nd arg memory in denoteDSHMap2 @" @@
                         Misc.string_of_nat n @@ " in " @@ string_of_mem_block_keys x1) n
                         x1 ≡ inr b /\ r ≡ Some (mH, b)))).

      unfold lift_Derr.
      break_match. break_match.
      { setoid_rewrite interp_Mem_vis_eqit.
        unfold pure_state in *; cbn in *.
        rewrite !interp_fail_bind.
        rewrite !interp_fail_vis.
        cbn in *. step. final.
        split; eauto. }
      { setoid_rewrite interp_Mem_vis_eqit.
        unfold pure_state in *; cbn in *.
        rewrite !interp_fail_bind.
        rewrite !interp_fail_vis.
        cbn in *. step. final.
        split; eauto. }
      { step. step. break_match; step; final; split; eauto. }

      (* EUTT_CLO_BIND continuation *)
      intros. cbn in H2.
      destruct H2 as [[[? []] | [? []]] [[? []] | [? []]]]; subst; cbn.
      { do 2 final. }
      { rewrite H, H3, H2, H7.
        unfold denoteBinCType.
        repeat step.
        edestruct genAExpr_correct_helix_pure_classic
          with (aexp := f) as [HA | (? & HA)];
          setoid_rewrite HA.
        + step; repeat final.
        + repeat step; final.
          repeat step; final. }
      { rewrite H, H3, H2, H7.
        unfold denoteBinCType.
        repeat step.
        edestruct genAExpr_correct_helix_pure_classic
          with (aexp := f) as [HA | (? & HA)];
          setoid_rewrite HA.
        + step; repeat final.
        + repeat step; final.
          repeat step; final. }

      rewrite H, H3, H2, H7; cbn.

      unfold denoteBinCType.
      repeat step.

      all: edestruct genAExpr_correct_helix_pure_classic
        with (aexp := f) as [HA | (? & HA)];
        setoid_rewrite HA.

      all: edestruct genAExpr_correct_helix_pure_classic
        with (aexp := f) as [HA' | (? & HA')];
        setoid_rewrite HA'.

      { step; repeat final. }
      { repeat step; final.
        repeat step.
        setoid_rewrite HA; step; final. }
      { repeat step; final.
        repeat step.
        setoid_rewrite HA'; step; final. }

      repeat step; final.
      repeat step.
      setoid_rewrite HA.
      setoid_rewrite HA'.
      repeat step; final.

      split; auto.

      pose proof @mem_lookup_mem_add_eq as EQ.
      pose proof @mem_lookup_mem_add_neq as NEQ.
      unfold mem_add, mem_lookup in EQ, NEQ.

      intro.

      destruct (Nat.eq_dec n' n); [subst |].
      - rewrite H in H3; inv H3.        
        rewrite H2 in H7; inv H7.
        rewrite HA in HA'.
        apply eqit_inv in HA'.
        cbn in HA'; inv HA'.
        destruct (Nat.eq_dec k n); [subst |].
        + rewrite EQ; constructor; reflexivity.
        + rewrite NEQ by auto.
          do 2 f_equiv; intro.
          destruct (find k0 init); constructor.
          reflexivity.
      - destruct (Nat.eq_dec k n); destruct (Nat.eq_dec k n'); subst.
        + rewrite EQ, NEQ, EQ by auto.
          constructor; reflexivity.
        + rewrite EQ, NEQ, EQ by auto.
          constructor; reflexivity.
        + rewrite NEQ, EQ, EQ by auto.
          constructor; reflexivity.
        + rewrite 4 NEQ by auto.
          do 2 f_equiv.
          intro.
          destruct (find k0 init); constructor.
          reflexivity.
    }
    {
      intros [[]|] [[]| ] *.
      intros. 2,3 : intros; contradiction.
      2 : red; cbn; reflexivity.
      destruct H; subst.
      red; auto.
    }
  Qed.

  Lemma eq_rev_interp :
    forall σ f n x0 x1 y memH,
      eutt mem_eq
        (interp_helix (E := E_cfg) (DSHMemMap2_tfor_up   σ f 0 n   x0 x1 y) memH)
        (interp_helix (E := E_cfg) (DSHMemMap2_tfor_down σ f 0 n n x0 x1 y) memH).
    Proof.
      unfold DSHMemMap2_tfor_up, DSHMemMap2_tfor_down.
      intros.
      revert σ f x0 x1 y memH.
      Opaque DSHMemMap2_body.
      induction n. intros. cbn.
      - rewrite! tfor_0. reflexivity.
      - intros. setoid_rewrite tfor_unroll at 2.
        cbn. 2 : lia.
        assert (EQ : n - 0 - 0 ≡ n) by lia; rewrite EQ; clear EQ.
        assert (EQ : n - 0 ≡ n) by lia; rewrite EQ; clear EQ.
        etransitivity; cycle 1.
        rewrite interp_helix_bind.
        eapply eutt_clo_bind. reflexivity.
        intros [[]|] [[]|] EQ; inv EQ.
        {
          setoid_rewrite tfor_ss_dep at 2. 3 : lia.
          2 : {
            intros. Unshelve.
            3 : { exact (fun i y => DSHMemMap2_body σ f (n - 1 - i) x0 x1 y). }
            cbn.
            assert (EQ : n - S i ≡ n - 1 - i) by lia; rewrite EQ; clear EQ.
            reflexivity.
            shelve.
          }
          rewrite <- IHn.
          Unshelve.
          2 : exact (fun a =>
              match a with
              | Some (m1, m2) =>
                interp_helix (tfor (λ (i : nat) (acc : mem_block), DSHMemMap2_body σ f i x0 x1 acc) 0 n m2) m1
              | None => Ret None
              end).
          cbn. reflexivity.
        }
        { cbn. reflexivity. }
        cbn.

        setoid_rewrite tfor_split with (j := n) at 1. 2, 3 : lia.
        clear IHn.
        etransitivity.
        {
          rewrite interp_helix_bind. eapply eutt_clo_bind. reflexivity.
          intros [[]|] [[]|] EQ; inv EQ.
          setoid_rewrite tfor_unroll at 1. setoid_rewrite tfor_0 at 1. setoid_rewrite bind_ret_r at 1.
          2 : lia. Unshelve.
          3 : exact (fun a =>
              match a with
              | Some (m1, m2) => interp_helix (DSHMemMap2_body σ f n x0 x1 m2) m1
              | None => Ret None
              end).
          cbn. reflexivity.
          cbn. reflexivity.
        }
        cbn.

        remember n.
        remember (λ y : mem_block, DSHMemMap2_body σ f n0 x0 x1 y).
        rewrite Heqn0. clear Heqn0. subst.
        revert x0 x1 y n0.
        induction n.
        + intros.
          setoid_rewrite tfor_0.
          rewrite interp_helix_ret. cbn. rewrite bind_ret_l.
          etransitivity; cycle 1.
          eapply eutt_clo_bind.
          reflexivity.
          {
            intros [[]|] [[]|] EQ; inv EQ.
            Unshelve.
            setoid_rewrite tfor_0 at 2. rewrite interp_helix_ret. cbn.
            3 : exact (fun a => Ret a).
            cbn. reflexivity. cbn. reflexivity.
          }
          cbn. rewrite bind_ret_r. reflexivity.
        + intros.
          (* 1 *)
          setoid_rewrite tfor_split with (j := n) at 1. 2, 3 : lia.
          etransitivity.
          {
            rewrite interp_helix_bind.
            eapply eutt_clo_bind. eapply eutt_clo_bind.
            reflexivity.
            intros [[]|] [[]|] EQ; inv EQ.
            setoid_rewrite tfor_unroll at 1. setoid_rewrite tfor_0 at 1.
            setoid_rewrite bind_ret_r at 1.
            2 : lia.
            Unshelve.
            7 : exact (fun a =>
                match a with
                | Some (m1, m2) => interp_helix (DSHMemMap2_body σ f n x0 x1 m2) m1
                | None => Ret None
                end).
            cbn. reflexivity. cbn. reflexivity.
            intros [[]|] [[]|] EQ; inv EQ.
            3 : exact (fun a =>
                match a with
                | Some (m1, m2) => interp_helix (DSHMemMap2_body σ f n0 x0 x1 m2) m1
                | None => Ret None
                end).
            1, 2 : cbn ; reflexivity.
          }

          etransitivity; cycle 1.
          {
            eapply eutt_clo_bind.
            reflexivity.
            intros [[]|] [[]|] EQ; inv EQ.
            setoid_rewrite tfor_split with (j := n) at 2.
            rewrite interp_helix_bind. 2, 3 : lia.
            Unshelve.
            3 : exact (fun a =>
                match a with
                | Some (m1, m2) =>
                    '(m3, m4) <- interp_helix (tfor (λ (i : nat) (acc : mem_block), DSHMemMap2_body σ f i x0 x1 acc) 0 n m2 ) m1 ;;
                      interp_helix (DSHMemMap2_body σ f n x0 x1 m4) m3
                | None => Ret None
                end).
            cbn.
            eapply eutt_clo_bind. reflexivity.

            intros [[]|] [[]|] EQ; inv EQ.
            setoid_rewrite tfor_unroll. setoid_rewrite tfor_0. setoid_rewrite bind_ret_r.
            reflexivity. lia. reflexivity.
            cbn. reflexivity.
          }
          cbn.
          etransitivity; cycle 1.
          eapply eutt_clo_bind. reflexivity.
          {
            intros [[]|] [[]|] EQ; inv EQ.
            rewrite <- interp_helix_bind.

            Unshelve.
            3 : {
              exact
                (fun a =>
                  match a with
                  | Some (m1, m2) =>
                    (interp_helix (ITree.subst (DSHMemMap2_body σ f n x0 x1)
                            (tfor (fun (i : nat) (acc : mem_block) => DSHMemMap2_body σ f i x0 x1 acc) O n m2)) m1)
                  | None => Ret None
                  end).
            }
            reflexivity.
            cbn. reflexivity.
          }

          rewrite <- interp_helix_bind.
          rewrite <- interp_helix_bind.
          rewrite <- interp_helix_bind.
          setoid_rewrite <- bind_bind.
          setoid_rewrite interp_helix_bind at 2.
          setoid_rewrite interp_helix_bind at 2.
          etransitivity; cycle 1.
          {
            eapply eutt_clo_bind. apply IHn.
            intros [[]|] [[]|] EQ; inv EQ.
            Unshelve.
            3 :  exact (fun r => match r with
                              | Some (m1, m0) => interp_helix (DSHMemMap2_body σ f n x0 x1 m0) m1
                              | None => Ret None
                              end).
            cbn.
            Transparent DSHMemMap2_body.
            unfold DSHMemMap2_body. cbn.
            rewrite! interp_helix_bind.
            eapply eutt_clo_bind.  reflexivity.
            intros [[]|] [[]|] EQ'; inv EQ'; try reflexivity. cbn in *.
            rewrite! interp_helix_bind.
            eapply eutt_clo_bind.  reflexivity.

            intros [[]|] [[]|] EQ'; inv EQ'; try reflexivity. cbn in *.
            rewrite! interp_helix_bind.
            eapply eutt_clo_bind.  reflexivity.

            intros [[]|] [[]|] EQ'; inv EQ'; try reflexivity. cbn in *.
            rewrite! interp_helix_ret.
            cbn. apply eqit_Ret. cbn. split; auto.
            apply mem_add_proper. auto. auto. auto.

            cbn. reflexivity.
          }

          rewrite !bind_bind.
          clear IHn.
          setoid_rewrite interp_helix_bind.
          eapply eutt_clo_bind. reflexivity.

          intros [[]|] [[]|] EQ; inv EQ.
          rewrite <- interp_helix_bind.
          2 : { rewrite bind_ret_l. reflexivity. }

          eapply swap_body_interp.
    Qed.

  Lemma DSHMemMap2_eq_ret :
    forall σ f n x0 x1 y memH,
      no_failure (E := E_cfg) (interp_helix (DSHMemMap2_body σ f n x0 x1 y) memH) ->
      exists b, interp_helix (E := E_cfg) (DSHMemMap2_body σ f n x0 x1 y) memH ≈ interp_helix (Ret b) memH.
  Proof.
    intros.
    Transparent DSHMemMap2_body. cbn* in *; simp; try_abs.

    pose proof @genAExpr_correct_helix_pure.
    edestruct H0. rewrite! bind_ret_l in H.
    apply no_failure_helix_bind_prefix in H. eauto.
    eexists.
    eapply eutt_translate_gen.
    unfold denoteIUnCType.
    rename H1 into N_DENOTE.
    hred.
    rewrite interp_Mem_bind.
    rewrite interp_fail_bind.
    setoid_rewrite N_DENOTE.
    hred. reflexivity.
  Qed.

  Transparent DSHMemMap2_body.


  Lemma DSHMemMap2_interpreted_as_tfor:
    forall σ (n : nat) (m : memoryH) f
      (init1 init2 acc : mem_block),
      eutt (mem_eq)
           (interp_helix (E := E_cfg) (denoteDSHMap2 n f σ init1 init2 acc) m)
            (tfor (fun k x' =>
                    match x' with
                    | None => Ret None
                    | Some (m', acc) => interp_helix (DSHMemMap2_body σ f k init1 init2 acc) m'
                    end)
              0 n (Some (m, acc))).
  Proof.
    intros.
    rewrite denoteDSHMap2_as_tfor.
    rewrite <- eq_rev_interp.
    unfold DSHMemMap2_tfor_up.
    rewrite interp_helix_tfor; [|lia].
    cbn.
    eapply eutt_Proper_mono; cycle 1.
    apply eutt_tfor.
    intros [[m' acc']|] i; [| reflexivity].
    cbn.
    repeat rewrite interp_helix_bind.
    rewrite bind_bind.
    apply eutt_eq_bind; intros [[?m ?] |]; [| rewrite bind_ret_l; reflexivity].
    bind_ret_r2.
    apply eutt_eq_bind.
    intros [|]; reflexivity. repeat intro. subst. reflexivity.
  Qed.

End DSHMemMap2_is_tfor.

(* The result is a branch *)
Definition branches (to : block_id) (mh : memoryH * ()) (c : config_cfg_T (block_id * block_id + uvalue)) : Prop :=
  match c with
  | (m,(l,(g,res))) => exists from, res ≡ inl (from, to)
  end.

Definition genIR_post (σ : evalContext) (s1 s2 : IRState) (to : block_id) (li : local_env)
  : Rel_cfg_T unit ((block_id * block_id) + uvalue) :=
  lift_Rel_cfg (state_invariant σ s2) ⩕
               branches to ⩕
               (fun sthf stvf => local_scope_modif s1 s2 li (fst (snd stvf))).

Import AlistNotations.

Definition memory_invariant_partial_write' (configV : config_cfg) (index loopsize : nat) (ptr_llvm : addr)
            (bk_helix : mem_block) (x : ident) sz : Prop :=
    let '(mem_llvm, (ρ, g)) := configV in
    dtyp_fits mem_llvm ptr_llvm (typ_to_dtyp [] (TYPE_Array sz TYPE_Double)) /\
    in_local_or_global_addr ρ g x ptr_llvm /\
            (∀ (i : Int64.int) (v0 : binary64),
                (MInt64asNT.to_nat i) < index \/ (MInt64asNT.to_nat i) >= loopsize ->
                  (mem_lookup (MInt64asNT.to_nat i) bk_helix ≡ Some v0
                    → get_array_cell mem_llvm ptr_llvm (MInt64asNT.to_nat i) DTYPE_Double ≡ inr (UVALUE_Double v0))).

Lemma DSHMemMap2_correct:
  ∀ (n : nat) (x0_p x1_p y_p : PExpr) (f : AExpr) (s1 s2 : IRState) (σ : evalContext) (memH : memoryH)
    (nextblock bid_in bid_from : block_id) (bks : list (LLVMAst.block typ)) (g : global_env)
    (ρ : local_env) (memV : memoryV),
    genIR (DSHMemMap2 n x0_p x1_p y_p f) nextblock s1 ≡ inr (s2, (bid_in, bks))
    → bid_bound s1 nextblock
    → state_invariant σ s1 memH (memV, (ρ, g))
    → Gamma_safe σ s1 s2
    (* We need an explicit predicate stating that the source program will not fail. *)
    → no_failure (E := E_cfg) (interp_helix (denoteDSHOperator σ (DSHMemMap2 n x0_p x1_p y_p f)) memH)
    → eutt (succ_cfg (genIR_post σ s1 s2 nextblock ρ))
           (interp_helix (denoteDSHOperator σ (DSHMemMap2 n x0_p x1_p y_p f)) memH)
            (interp_cfg (denote_ocfg (convert_typ [] bks) (bid_from, bid_in)) g ρ memV).
Proof.
  intros n x0_p x1_p y_p f s1 s2 σ memH nextblock bid_in bid_from bks g ρ memV GEN NEXT PRE GAM NOFAIL.
  Opaque genAExpr.
  Opaque IntType.
  Opaque incLocalNamed.
  Opaque newLocalVar.
  Opaque addVars.
  Opaque swapVars.

  pose proof generates_wf_ocfg_bids _ NEXT GEN as WFOCFG.
  pose proof inputs_bound_between _ _ _ GEN as INPUTS_BETWEEN.
  pose proof genIR_Γ _ _ _ GEN as GENIR_Γ.
  pose proof genIR_local_count _ _ _ GEN as GENIR_local.

  (* Clean up PVars *)
  cbn* in *; simp; cbn* in *.
  hide_cfg.
  inv_resolve_PVar Heqs1.
  inv_resolve_PVar Heqs2.
  inv_resolve_PVar Heqs3.
  unfold denotePExpr in *; cbn* in *.

  (* Clean up w/ renaming *)
  rename i14 into storeid.
  rename r0 into p0x.
  rename r1 into p1x.
  rename r2 into py.
  rename r3 into v0.
  rename r4 into v1.
  destruct_unit.
  rename e into fexpr.
  rename c into fexpcode.

  rename i1 into x0.
  rename i4 into x1.
  rename r into loopvarid.
  rename i7 into y.
  rename i2 into xp0_typ_.
  rename i5 into xp1_typ_.
  rename i8 into yp_typ_.

  destruct_unit.
  simp; try_abs.

  clean_goal.

  (* Clean up [no_failure] *)
  repeat apply no_failure_Ret in NOFAIL.

  destruct (assert_nat_le "DSHMemMap2 'n' larger than 'y_size'" n (MInt64asNT.to_nat i2)) eqn:BOUNDS; try_abs.

  repeat apply no_failure_Ret in NOFAIL.

  do 3 (edestruct @no_failure_helix_LU
          as (? & NOFAIL' & ?); eauto;
          clear NOFAIL; rename NOFAIL' into NOFAIL;
          cbn in NOFAIL; eauto).

  clean_goal. destruct_unit.

  hred.

  (* repeat apply no_failure_Ret in NOFAIL. *)
  rewrite BOUNDS.

  unfold assert_nat_le, assert_true_to_err in BOUNDS.
  destruct (n <=? MInt64asNT.to_nat i2) eqn:E; try discriminate.
  clear BOUNDS; rename E into BOUNDS.
  apply leb_complete in BOUNDS.

  do 3 (hred; hstep; [eauto |]).
  hred.

  (* Rename states in order *)
  rename i   into  s0.
  rename i9  into  s1.
  rename s2  into s2t.
  rename i10 into  s2.
  rename i12 into  s3.
  rename i13 into  s4.
  rename i15 into  s5.
  rename i16 into  s6.
  rename i17 into  s7.
  rename i18 into  s8.
  rename i19 into  s9.
  rename i20 into s10.
  rename i21 into s11.
  rename i11 into s12.
  rename s2t into s13.

  rename l0 into bks.

  rename n3 into x0_h_ptr.
  rename n4 into x1_h_ptr.
  rename n5 into  y_h_ptr.

  rename n0 into n_x0.
  rename n1 into n_x1.
  rename n2 into n_y.

  rename Heqo1 into nth_σ_x0.
  rename Heqo0 into nth_σ_x1.
  rename Heqo  into nth_σ_y.

  rename LUn  into nth_Γ_x0.
  rename LUn0 into nth_Γ_x1.
  rename LUn1 into nth_Γ_y.

  rename sz  into sz_x0.
  rename sz0 into sz_x1.
  rename sz1 into sz_y.

  pose proof state_invariant_memory_invariant PRE as MINV_X0_OFF.
  pose proof state_invariant_memory_invariant PRE as MINV_X1_OFF.
  pose proof state_invariant_memory_invariant PRE as MINV_Y_OFF.
  unfold memory_invariant in MINV_X0_OFF, MINV_X1_OFF, MINV_Y_OFF.

  replace (Γ s1) with (Γ s0)
    in nth_Γ_x0, nth_Γ_x1, nth_Γ_y
    by solve_gamma.

  specialize (MINV_X0_OFF _ _ _ _ _ nth_σ_x0 nth_Γ_x0).
  specialize (MINV_X1_OFF _ _ _ _ _ nth_σ_x1 nth_Γ_x1).
  specialize (MINV_Y_OFF  _ _ _ _ _ nth_σ_y  nth_Γ_y).
  cbn in MINV_X0_OFF, MINV_X1_OFF, MINV_Y_OFF.

  destruct MINV_X0_OFF as
    (ptrll_x0_off & τ_x0_off & TEQ_x0_off & FITS_x0_off & INLG_x0_off &
     bkh_x0_off & MLUP_x0_off & GETARRAYCELL_x0_off); eauto.

  destruct MINV_X1_OFF as
    (ptrll_x1_off & τ_x1_off & TEQ_x1_off & FITS_x1_off & INLG_x1_off &
     bkh_x1_off & MLUP_x1_off & GETARRAYCELL_x1_off); eauto.

  destruct MINV_Y_OFF as
    (ptrll_y_off & τ_y_off & TEQ_y_off & FITS_y_off & INLG_y_off &
     bkh_y_off & MLUP_y_off & GETARRAYCELL_y_off); eauto.

  rewrite MLUP_x0_off in H;  symmetry in H;  inv H.
  rewrite MLUP_x1_off in H0; symmetry in H0; inv H0.
  rewrite MLUP_y_off  in H1; symmetry in H1; inv H1.

  inv TEQ_x0_off; inv TEQ_x1_off; inv TEQ_y_off.

  (* We know that the Helix denotation can be expressed via the [tfor] operator *)
  assert (NOFAIL_cont := NOFAIL).
  apply no_failure_helix_bind_prefix in NOFAIL.

  (* get no-failure in "reverse" direction before getting it in the right direction. *)
  assert (NOFAIL_rev := NOFAIL).

  eapply eutt_Proper_mono; cycle 1.
  eapply eqit_trans.
  {
    eapply eutt_clo_bind_returns.
    apply DSHMemMap2_interpreted_as_tfor.
    intros [ [] |] [ []| ] EQ R1 R2; inv EQ.
    rewrite interp_helix_MemSet.
    Unshelve.
    6 : exact (fun x => match x with
                     | Some (m1, m2) => Ret (Some (memory_set m1 y_h_ptr m2))
                     | None => Ret None
                     end
              ).
    cbn. apply eqit_Ret.
    3 : { intros [] []. destruct p. exact (m0 = m).
          exact False. exact False. exact True. }
    cbn. eapply memory_set_proper. red. reflexivity. reflexivity. auto.
    cbn. apply eqit_Ret. auto.
    intros.
    destruct X.
    exact (genIR_post σ s0 s13 nextblock ρ (m, ()) X0).
    exact False.
  }
  2 : {
    repeat intro. inv H. destruct x. destruct r2. destruct p.
    3 : { destruct r2. inv REL1. inv REL2. }
    destruct u. unfold genIR_post in *. destruct REL2. destruct H0. split; auto.
    unfold lift_Rel_cfg in *. destruct y0. destruct p. destruct p.
    destruct H. split; auto.
    red. intros. red in mem_is_inv.
    destruct v; specialize (mem_is_inv _ _ _ _ _ H H2); cbn in *; eauto.
    edestruct mem_is_inv as (? & ? & ? & ? & ? & ?).
    exists x2, x3. split; auto. split; auto. split; auto. intros.
    specialize (H6 H7).
    destruct H6 as (? & ? & ?).
    exists x4. split. pose proof @memory_lookup_proper.
    do 3 red in H9. specialize (H9 _ _ REL1).
    specialize (H9 a a eq_refl).
    pose proof Extensionality_t.
    unfold Same_t in H10. red in REL1. red in REL1. specialize (H10 mem_block _ m0 m REL1). rewrite H10.
    eauto.

    intros. auto.
    red. intros. eapply mem_block_exists_proper. reflexivity. eauto.
    red in st_id_allocated. eapply st_id_allocated. eauto.
    split; auto. inv REL1.
  }

  assert (PROPER: forall E, Proper (eutt (E := E) mem_eq ==> impl) no_failure). {
    repeat intro. eapply eutt_Proper_mono in H.
    eapply no_failure_eutt; eauto. symmetry. apply H.
    repeat intro.
    pose proof Extensionality_t.
    unfold Same_t in H2. unfold mem_eq in H1. destruct x2, y1. destruct p, p0.
    destruct H1.
    subst.
    assert (m0 ≡ m2). do 3 red in H3.
    specialize (H2 _ _ _ _ H3). auto. subst. reflexivity.
    destruct p. inv H1. inv H1. reflexivity.
  }

  rewrite DSHMemMap2_interpreted_as_tfor in NOFAIL.

  cbn* in *; simp; cbn in *.
  clean_goal.

  match goal with
  | [H : genWhileLoop ?prefix _ _ ?loopvar ?loopcontblock ?body_entry ?body_blocks _ ?nextblock ?s1' ≡ inr (?s2', (?entry_id, ?bks)) |- _]
    => epose proof @genWhileLoop_tfor_correct prefix loopvar loopcontblock body_entry body_blocks nextblock bid_in s1' s2' s1 s12 bks as GENC
  end.

  Transparent genMemMap2Body.
  forward GENC; [clear GENC |].
  cbn. left; reflexivity.

  forward GENC; [clear GENC |].
  eauto.

  forward GENC; [clear GENC |].
  { eauto using wf_ocfg_bid_add_comment. }

  forward GENC; [clear GENC |].
  {
    eapply lid_bound_between_shrink;
      [eapply lid_bound_between_incLocalNamed | | ];
      eauto; try reflexivity.
    get_local_count_hyps.
    Transparent addVars.
    inv Heqs14.
    cbn in Heqs15.
    solve_local_count.
    Opaque addVars.
  }

  forward GENC; [clear GENC |]. {
    rewrite Forall_forall in INPUTS_BETWEEN. intros IN. subst.
    inv VG.
    rewrite inputs_convert_typ, add_comment_inputs in INPUTS_BETWEEN.
    apply INPUTS_BETWEEN in IN; clear INPUTS_BETWEEN.
    eapply not_bid_bound_between; eauto.
  }

  rename Heqs7 into WHILE.

  specialize (GENC n WHILE).

  match goal with
    |- context [tfor ?bod _ _ _] => specialize (GENC _ bod)
  end.

  assert (OVERFLOW: (Z.of_nat n < Integers.Int64.modulus)%Z). {
    clear -Heqs6.
    unfold MInt64asNT.from_nat in Heqs6.
    unfold MInt64asNT.from_Z in Heqs6.
    simp.
    apply l0.
  }

  forward GENC; [clear GENC |]; eauto.

  inv VG.
  rewrite add_comment_eutt.

  rename memV into mV_init.

  (* Invariant at each iteration *)
  set (I := (fun (k : nat) (mH : option (memoryH * mem_block)) (stV : memoryV * (local_env * global_env)) =>
               match mH with
               | None => False
               | Some (mH, b) =>
                 let '(mV, (ρ, g')) := stV in
                 (* 1. Relaxed state invariant *)
                 state_invariant σ s13 mH stV /\
                 (* 2. Preserved state invariant *)
                 memory_invariant_partial_write' stV k n ptrll_y_off b y sz_y /\
                 mH ≡ memH /\ g ≡ g' /\
                 allocated ptrll_y_off mV
               end)).

  (* Precondition and postcondition *)
  set (P := (fun (mH : option (memoryH * mem_block)) (stV : memoryV * (local_env * global_env)) =>
               match mH with
               | None => False
               | Some (mH,b) => state_invariant σ s13 mH stV /\
                 let '(mV, (p, g')) := stV in
                 mH ≡ memH /\ g ≡ g' /\ mV ≡ mV_init /\ ρ ≡ p /\ b ≡ bkh_y_off
               end)).

  set (Q := (fun (mH : option (memoryH * mem_block)) (stV : memoryV * (local_env * global_env)) =>
               match mH with
               | None => False
               | Some (mH,mb) => state_invariant σ s13 (memory_set mH y_h_ptr mb) stV /\
                 let '(mV, (p, g')) := stV in
                 mH ≡ memH /\ g ≡ g'
               end)).

  specialize (GENC I P Q (Some (memH, bkh_y_off))).

  assert (EE : (ID_Local v1, TYPE_Double) ::
               (ID_Local v0, TYPE_Double) :: Γ s12 ≡ Γ s11).
  { Transparent addVars dropVars.
    inv Heqs14.
    apply genAExpr_Γ in Heqs15.
    cbn in Heqs15.
    unfold dropVars in Heqs16.
    inv Heqs16.
    rewrite <- Heqs15 in H0.
    cbn in H0.
    inv H0.
    rewrite <- Heqs15.
    reflexivity.
    Opaque addVars dropVars.
  }

  assert (INV_STABLE :
    forall (k : nat) (a : option (prod memory mem_block))
           (l : alist raw_id uvalue) (mV : memory_stack)
           (g0 : global_env) (id : local_id) (v0 : uvalue),
           (lid_bound_between s12 s13 id) \/ (lid_bound_between s1 s12 id) ->
           I k a (mV, (l, g0)) ->
           I k a (mV, (alist_add id v0 l, g0))).
  {
    intros.
    unfold I in *.
    destruct a eqn:AEQ; eauto.
    destruct p eqn:AEP.
    destruct H0 as (? & ? & <- & <- & ?).
    subst.
    split; [|split;[|split]];eauto.

    - eapply state_invariant_same_Γ with (s1 := s13); eauto.
      eapply not_in_Gamma_Gamma_eq; eauto.
      eapply GAM.
      eapply lid_bound_between_shrink_down.
      2 : {
        destruct H; eapply lid_bound_between_shrink. eauto. 3 :  eauto.
        2 : solve_local_count. 3 : solve_local_count. 2 : reflexivity.
        Transparent addVars.
        inv Heqs14.
        cbn in Heqs15.
        solve_local_count.
      }

      solve_local_count.

    - unfold memory_invariant_partial_write' in *.

      destruct H1 as (? & ? & ?).
      intuition.
      + unfold alist_add; cbn. cbn.
        destruct y; auto. cbn in *.
         break_match_goal.
        * rewrite rel_dec_correct in Heqb1; subst.
          assert (Gamma_safe σ s0 s13) by solve_gamma_safe.

          Transparent addVars.
          inv Heqs14.

          assert (NIN: not (in_Gamma σ s0 id)). apply H.
          eapply lid_bound_between_shrink.
          eauto.
          solve_local_count.
          solve_local_count.
          exfalso; eapply NIN.
          econstructor; [apply nth_σ_y | eauto | eauto].
        * apply neg_rel_dec_correct in Heqb1.
          rewrite remove_neq_alist; eauto.
          all: typeclasses eauto.

      + unfold alist_add; cbn. cbn.
        destruct y; auto. cbn in *.
        break_match_goal.
        * rewrite rel_dec_correct in Heqb1; subst.
          assert (Gamma_safe σ s0 s12) by solve_gamma_safe.

          Transparent addVars.
          inv Heqs14.

          assert (NIN: not (in_Gamma σ s0 id)). apply H.
          eapply lid_bound_between_shrink.
          eauto.
          solve_local_count.
          solve_local_count.
          exfalso; eapply NIN.
          econstructor; [apply nth_σ_y | eauto | eauto].
        * apply neg_rel_dec_correct in Heqb1.
          rewrite remove_neq_alist; eauto.
          all: typeclasses eauto.
  }

  (* Loop body match *)
  forward GENC; [clear GENC |].
  {
    intros ? ? ? [[? ?]|] * (INV & LOOPVAR & BOUNDk & RET); [| inv INV].
    assert (INV' := INV).

    subst P Q.

    assert (EQk: MInt64asNT.from_nat k ≡ inr (Int64.repr (Z.of_nat k))).
    { destruct (MInt64asNT.from_nat k) eqn:EQN.
     - exfalso.
       unfold MInt64asNT.from_nat in *.
       unfold MInt64asNT.from_Z in *.
       simp; lia.
     - unfold MInt64asNT.from_nat in *.
       apply from_Z_intval in EQN.
       rewrite EQN, repr_intval.
       reflexivity.
    }

    (* [HELIX] Clean-up (match breaks using no failure) *)
    eapply no_failure_tfor in NOFAIL.
    3: eauto. 2: lia.
    cbn in NOFAIL.
    rewrite interp_helix_bind in NOFAIL.

    destruct (mem_lookup k bkh_x0_off) eqn:Ex0; revgoals.
    { apply no_failure_bind_prefix in NOFAIL.
      apply failure_helix_throw in NOFAIL.
      contradiction. }

    destruct (mem_lookup k bkh_x1_off) eqn:Ex1; revgoals.
    { rewrite interp_helix_Ret, bind_ret_l in NOFAIL.
      apply failure_helix_throw' in NOFAIL.
      contradiction. }

    repeat step.

    replace (match x0 with
             | ID_Global rid => ID_Global rid
             | ID_Local  lid => ID_Local  lid
             end) with x0 by (destruct x0; auto).
    
    replace (match x1 with
             | ID_Global rid => ID_Global rid
             | ID_Local  lid => ID_Local  lid
             end) with x1 by (destruct x1; auto).

    (* [HELIX] "denoteBinCType" exposed *)
    unfold denoteBinCType.

    (* [Vellvm] step until "fmap" is exposed, so we can match with AExpr denotation *)
    rewrite denote_ocfg_unfold_in.
    2: { apply find_block_eq; auto. }

    Transparent IntType. 
    cbn; vred.

    rewrite denote_no_phis.
    vred; cbn.

    rewrite denote_code_cons.

    (* Get mem information from PRE condition here (global and local state has changed). *)
    (* Needed for the following GEP and Load instructions *)
    destruct INV as (INV_r & INV_p & -> & -> & ?).

    rewrite -> GENIR_Γ in nth_Γ_x0, nth_Γ_x1.

    (* Memory invariant for x *)
    pose proof state_invariant_memory_invariant INV_r as MINV_X0_OFF.
    pose proof state_invariant_memory_invariant INV_r as MINV_X1_OFF.

    specialize (MINV_X0_OFF _ _ _ _ _ nth_σ_x0 nth_Γ_x0).
    specialize (MINV_X1_OFF _ _ _ _ _ nth_σ_x1 nth_Γ_x1).

    cbn in MINV_X0_OFF, MINV_X1_OFF.

    destruct MINV_X0_OFF as
      (ptrll_x0_off_l & τ_x0_off & TEQ_x0_off & FITS_x0_off_l & INLG_x0_off_l &
       bkh_x0_off_l & MLUP_x0_off_l & GETARRAYCELL_x0_off_l); eauto.

    destruct MINV_X1_OFF as
      (ptrll_x1_off_l & τ_x1_off & TEQ_x1_off & FITS_x1_off_l & INLG_x1_off_l &
       bkh_x1_off_l & MLUP_x1_off_l & GETARRAYCELL_x1_off_l); eauto.

    rewrite MLUP_x0_off in MLUP_x0_off_l; inv MLUP_x0_off_l.
    rewrite MLUP_x1_off in MLUP_x1_off_l; inv MLUP_x1_off_l.

    inv TEQ_x0_off; inv TEQ_x1_off.

    rewrite <- GENIR_Γ in nth_Γ_x0, nth_Γ_x1.

    Transparent incLocal.

    Ltac derive_NEQ :=
      unfold incLocal in *;
      match goal with
      | |- ?id1 ≢ ?id2 =>
        match goal with
        | [ H1 : incLocalNamed _ _ ≡ inr (_, id1),
            H2 : incLocalNamed _ _ ≡ inr (_, id2) |- _ ] => 
          intro; subst;
          eapply lid_bound_between_incLocalNamed in H1; eauto;
          eapply lid_bound_between_incLocalNamed in H2; eauto;
          (now eapply state_bound_between_id_separate;
                [ eapply incLocalNamed_count_gen_injective
                | apply H1 | apply H2 | solve_local_count ]) ||
          (now eapply state_bound_between_id_separate;
                [ eapply incLocalNamed_count_gen_injective
                | apply H2 | apply H1 | solve_local_count ])
        end
      end.

    assert (UNIQ_v0  : loopvarid ≢ v0)  by derive_NEQ.
    assert (UNIQ_v1  : loopvarid ≢ v1)  by derive_NEQ.
    assert (UNIQ_p0x : loopvarid ≢ p0x) by derive_NEQ.
    assert (UNIQ_p1x : loopvarid ≢ p1x) by derive_NEQ.
    assert (UNIQ_py  : loopvarid ≢ py)  by derive_NEQ.

    assert (NEQ_v0_v1  : v0 ≢ v1)  by derive_NEQ.
    assert (NEQ_v0_p1x : v0 ≢ p1x) by derive_NEQ.

    (* pose proof INV_p as MINV_YOFF.
    unfold memory_invariant_partial_write' in MINV_YOFF.
    destruct MINV_YOFF as (FITS_yoff_l & INLG_YOFF & MINV_YOFF). *)

    (* [Vellvm] GEP Instruction for [x0] *)
    match goal with
    | [|- context[OP_GetElementPtr (DTYPE_Array ?size' ?τ') (_, ?ptr') _]] =>
      edestruct denote_instr_gep_array' with
        (l := li) (g := g0) (m := mV) (i := p0x)
        (size := size') (a := ptrll_x0_off_l) (ptr := ptr') as (? & ? & ? & ?)
    end.

    { destruct x0.
      - rewrite denote_exp_GR; [| eauto]; reflexivity.
      - rewrite denote_exp_LR; [| eauto]; reflexivity. }

    { rewrite denote_exp_LR; [reflexivity | eauto]. }

    { rewrite <- to_nat_repr_nat with (k := k); auto.
      eapply GETARRAYCELL_x0_off_l.
      rewrite -> to_nat_repr_nat; eauto. }

    rename x into src_x0_addr.
    rename H0 into READ_x0.
    rename H1 into HSRC_GEP_x0.
    rename H2 into x0_HGEP.

    vred.
    rewrite x0_HGEP; clear x0_HGEP.
    vred.

    (* [Vellvm] : Load *)
    vred.
    rewrite denote_instr_load; eauto.
    2: apply denote_exp_LR, alist_find_add_eq.

    vred; cbn.
    rewrite denote_code_cons.

    set (li' := (alist_add v0 (UVALUE_Double b1)
                  (alist_add p0x (UVALUE_Addr src_x0_addr)
                    li))).

    (* [Vellvm] GEP Instruction for [x1] *)
    match goal with
    | [|- context[OP_GetElementPtr (DTYPE_Array ?size' ?τ') (_, ?ptr') _]] =>
      edestruct denote_instr_gep_array' with
        (l := li') (g := g0) (m := mV) (i := p1x)
        (size := size') (a := ptrll_x1_off_l) (ptr := ptr') as (? & ? & ? & ?)
    end.

    {
      destruct x1.
      { rewrite denote_exp_GR; [| eauto]; reflexivity. }
      rewrite denote_exp_LR; [reflexivity |].
      unfold li'; cbn.
      apply lid_bound_between_incLocal in Heqs9  as Heqs9'.
      apply lid_bound_between_incLocal in Heqs12 as Heqs12'.
      Transparent addVars.
      unfold addVars in Heqs14; inv Heqs14.
      rewrite 2 alist_find_neq; eauto.
      all: intro C; symmetry in C; subst.
      all: eapply GAM; [| eapply mk_in_Gamma with (n := n_x1); eauto].
      all: eapply lid_bound_between_shrink; eauto.
      all: solve_local_count.
    }

    { rewrite denote_exp_LR; [reflexivity |].
      unfold li'; cbn.
      rewrite 2 alist_find_neq; eauto. }

    { rewrite <- to_nat_repr_nat with (k := k); auto.
      eapply GETARRAYCELL_x1_off_l.
      rewrite -> to_nat_repr_nat; eauto. }

    rename x into src_x1_addr.
    rename H0 into READ_x1.
    rename H1 into HSRC_GEP_x1.
    rename H2 into x1_HGEP.

    vred.
    rewrite x1_HGEP; clear x1_HGEP.
    vred.

    (* [Vellvm] : Load *)
    vred.
    rewrite denote_instr_load; eauto.
    2: apply denote_exp_LR, alist_find_add_eq.

    (* [Vellvm] : Clean up *)
    vred.
    rewrite map_app.
    typ_to_dtyp_simplify.
    rewrite denote_code_app.
    vred.

    (*
      Transparent addVars. unfold addVars in Heqs12. inv Heqs12.

      assert (s2_ext : Γ s5 ≡ (ID_Local loopvarid, IntType) :: Γ s1). {
        assert (H5 :Γ s2 ≡ Γ s5) by solve_gamma.
        rewrite <- H5.
        apply newLocalVar_Γ in Heqs4. eauto.
      }

      assert (neg0 : ~ in_Gamma σ s0 v) by solve_not_in_gamma.
      eapply not_in_gamma_protect in neg0.

      assert (neg1 : ¬ in_Gamma ((DSHnatVal (Int64.repr (Z.of_nat k)), false) :: (protect σ n1)) s5 v). {
          eapply not_in_gamma_cons.
          assert (Heqs4' := Heqs4).
          eauto.
          eapply not_in_Gamma_Gamma_eq. 2 : eauto. solve_gamma.
          auto.
      }
    *)

    rewrite interp_helix_bind.

    Ltac derive_not_in_Gamma s0 :=
      match goal with
      | SINV : state_invariant _ s0 _ _ |- ¬ in_Gamma _ ?s ?v =>
        let C := fresh "C" in intro C; inv C;
        eapply not_lid_bound_incLocal with (id := v); eauto;
        apply lid_bound_before with (s1 := s0); [| solve_local_count];
        apply st_gamma_bound in SINV;
        eapply SINV;
        replace (Γ s0) with (Γ s) by solve_gamma;
        eassumption
      end.

    set (s9_10 := {| block_count := block_count s9
      ; local_count := local_count s9
      ; void_count  := void_count s9
      ; Γ := (ID_Local v0, TYPE_Double) :: Γ s9
     |}).

    set (s11' := {| block_count := block_count s11
      ; local_count := local_count s11
      ; void_count  := void_count s11
      ; Γ := (ID_Local v0, TYPE_Double) :: Γ s9
     |}).

    eapply eutt_clo_bind_returns.
    {
      eapply genAExpr_correct.
      - eassumption.
      - unfold Maps.add, Map_alist, li'.
        eapply state_invariant_enter_scope_DSHCType' with (s1 := s9_10); eauto.
        { inv Heqs14; reflexivity. }
        { repeat eexists; break_and_goal; revgoals.
          - symmetry; eassumption.
          - inv Heqs14; solve_local_count.
          - reflexivity. }
        { intro C; inv C.
          eapply not_lid_bound_incLocal with (id := v1); eauto.
          apply lid_bound_before with (s1 := s0); [| solve_local_count].
          apply st_gamma_bound in PRE.
          destruct n0; cbn in H1.
          - inv H1; contradiction.
          - eapply PRE.
            replace (Γ s0) with (Γ s9) by solve_gamma.
            apply H1. }
        { inv Heqs14; constructor. }
        { apply alist_find_add_eq. }

        eapply state_invariant_enter_scope_DSHCType' with (s1 := s9); eauto.
        { reflexivity. }
        { repeat eexists; break_and_goal; revgoals.
          - symmetry; eassumption.
          - inv Heqs14; solve_local_count.
          - reflexivity. }
        { derive_not_in_Gamma s0. }
        { rewrite 2 alist_find_neq by assumption.
          apply alist_find_add_eq. }
        clear s9_10.

        do 4 (eapply state_invariant_same_Γ;
               [ reflexivity
               | constructor
               | derive_not_in_Gamma s0
               | ]).

        apply state_invariant_protect.

        eapply state_invariant_Γ' with (s1 := s13).
        3: apply gamma_bound_mono with (s1 := s0).
        2, 5: solve_gamma.
        3: solve_local_count.
        2: eapply st_gamma_bound, PRE.
        assumption.

      - eapply Gamma_safe_Context_extend with (s1 := s9_10) (s2 := s11').
        4: replace (Γ s10) with (Γ s11) by solve_gamma.
        4, 5: rewrite <- EE; f_equal.
        4, 5: replace (Γ s12) with (Γ s13) by solve_gamma.
        4, 5: rewrite <- GENIR_Γ.
        4, 5: replace (Γ s0) with (Γ s9) by solve_gamma.
        4, 5: reflexivity.
        eapply Gamma_safe_Context_extend with (s1 := s0) (s2 := s13).
        4, 5: unfold s9_10, s11'; cbn; f_equal.
        4, 5: solve_gamma.
        5: inv Heqs14.
        2, 3, 5, 6: solve_local_count.
        apply Gamma_safe_protect; assumption.
        1: apply incLocal_lid_bound in Heqs12.
        2: apply incLocal_lid_bound in Heqs13.
        2: inv Heqs14.
        all: intros.
        all: eapply lid_bound_earlier; eauto.
        solve_local_count.
      - unfold denoteBinCType in NOFAIL.
        eapply no_failure_bind_cont with (u := (memH, b1)) in NOFAIL.
        eapply no_failure_helix_bind_continuation in NOFAIL; eauto.
        all: constructor; rewrite interp_helix_Ret; reflexivity.
    }

    (* unfold UU; clear UU. *)
    unfold li'; clear li'.

    intros [ [mH' t_Aexpr] | ] [mV' [li' [g0' []]]].
    intros (PRE_INV & AEXP) RET1 RET2.
    2 : { intros; cbn in *; contradiction. }

    cbn.
    typ_to_dtyp_simplify.
    rewrite denote_code_cons.

    assert (LOOPVAR': li' @ loopvarid ≡ Some (uvalue_of_nat k)).
    {
      erewrite local_scope_modif_out; eauto.
      2: eapply lid_bound_between_incLocalNamed; eauto.
      2: reflexivity.
      1: solve_local_count.
      eapply local_scope_modif_trans.
      4: destruct AEXP; cbn in extends; eassumption.
      1, 2: inv Heqs14; solve_local_count.
      apply lid_bound_between_incLocal in
        Heqs9  as Heqs9' , Heqs10 as Heqs10',
        Heqs12 as Heqs12', Heqs13 as Heqs13'.
      apply lid_bound_between_shrink
        with (s1 := s2) (s4 := s10)
        in Heqs9', Heqs10', Heqs12', Heqs13'.
      repeat (eapply local_scope_modif_add'; auto).
      all: inv Heqs14; solve_local_count.
    }

    cbn in PRE_INV.

    destruct AEXP.
    cbn in is_almost_pure.
    destruct is_almost_pure as (H1 & H2 & H3).
    symmetry in H1, H2, H3; subst.

    destruct INV_p as (FITS_y_off_l & INLG_y_off_l & GETARRAYCELL_y_off_l).

    assert (INLG_y_off' : in_local_or_global_addr li' g0 y ptrll_y_off).
    {
      destruct y; cbn in *; auto.
      rewrite <- INLG_y_off_l; symmetry.
      eapply local_scope_modif_shrink
        with (s1 := s1) (s4 := s12)
        in extends.
      eapply local_scope_modif_sub'_l in extends.
      eapply local_scope_modif_sub'_l in extends.
      eapply local_scope_modif_sub'_l in extends.
      eapply local_scope_modif_sub'_l in extends.
      eapply local_scope_modif_external; [eassumption |].
      { intro; eapply GAM.
        eapply lid_bound_between_shrink; eauto.
        1, 2: solve_local_count.
        econstructor; eauto. }
      Transparent addVars.
      5, 6: inv Heqs14; solve_local_count.
      all: eapply lid_bound_between_shrink;
        [ eapply lid_bound_between_incLocal; eassumption
        | inv Heqs14; solve_local_count
        | inv Heqs14; solve_local_count ].
      Opaque addVars.
    }

    (* [Vellvm] GEP without read on y *)
    set (y_size := Z.to_N (Int64.intval yp_typ_)).
    match goal with
    | [|- context[OP_GetElementPtr (DTYPE_Array y_size _) (_, ?ptr')]] =>
        edestruct denote_instr_gep_array_no_read with
          (l := li') (g := g0) (m := mV) (i := py) (τ := DTYPE_Double)
          (size := y_size) (a := ptrll_y_off) (ptr := ptr')
          as (y_GEP_addr & y_HGEP & EQ_y_HG)
    end.

    { destruct y.
      - rewrite denote_exp_GR; eauto.
        reflexivity.
      - rewrite denote_exp_LR; eauto.
        reflexivity. }

    { erewrite denote_exp_LR with (id := loopvarid).
      reflexivity.
      eassumption. }

    { subst y_size.
      erewrite <- from_N_intval; eauto.
      typ_to_dtyp_simplify.
      assumption. }

    rename y_GEP_addr into dst_addr.
    rename y_HGEP into HDST_GEP.

    vred.
    rewrite EQ_y_HG; clear EQ_y_HG.
    vred.

    rewrite denote_code_singleton.

    cbn in PRE_INV.
    (* [HELIX] easy clean-up. *)
    hred.
    vred.

    Opaque addVars dropVars.
    cbn in *.

    assert (Y_SIZE : sz_y ≡ Z.to_N (Int64.intval i2)). {
      apply nth_error_protect_eq' in nth_σ_y.
      rewrite GENIR_Γ in nth_Γ_y.
      replace (Γ s13) with (Γ s12) in nth_Γ_y by solve_gamma.
      epose proof (vellvm_helix_ptr_size _ nth_Γ_y nth_σ_y).
      eapply state_invariant_cons2 in PRE_INV.
      3 : eauto. 2 : solve_local_count.
      specialize (H0 PRE_INV). eauto.
    }

    (* Store  *)
    edestruct write_succeeds with
      (m1 := mV)
      (v := DVALUE_Double t_Aexpr)
      (a := dst_addr).
    apply DVALUE_Double_typ.
    {
      typ_to_dtyp_simplify.
      pose proof (from_N_intval _ EQsz1) as EQ.
      rewrite Y_SIZE in EQ.
      eapply dtyp_fits_array_elem.
      subst y_size. 2 : eauto.
      rewrite <- EQ. rewrite <- Y_SIZE. eauto.
      subst y_size. rewrite <- EQ.
      eapply to_nat_repr_nat in EQk.
      rewrite Znat.Z2N.id; [|apply Int64_intval_pos].

      pose proof Znat.inj_le _ _ BOUNDS as LE.
      unfold MInt64asNT.to_nat in LE.

      rewrite Znat.Z2Nat.id in LE; [|apply Int64_intval_pos].
      rewrite !Int64.unsigned_repr_eq.
      rewrite Zdiv.Zmod_small; try lia.
    }

    rewrite denote_instr_store.
    2 : {
      eapply exp_correct.
      { eapply local_scope_preserved_add_bound_earlier.
        eapply local_scope_preserved_refl.
        eapply lid_bound_between_incLocal.
        eassumption.
        Transparent addVars.
        inv Heqs14; solve_local_count.
        Opaque addVars. }
      eapply Gamma_preserved_add_not_in_Gamma.
      solve_gamma_preserved.
      eapply not_in_gamma_cons with (s1 := s9_10).
      rewrite <- Gamma_cst.
      rewrite <- EE.
      unfold s9_10; cbn.
      do 2 f_equal.
      solve_gamma.
      2: solve_id_neq.
      eapply not_in_gamma_cons.
      unfold s9_10; cbn.
      reflexivity.
      eapply not_in_Gamma_Gamma_eq with (s1 := s0).
      2 : eapply not_in_gamma_protect.
      2: derive_not_in_Gamma s0.
      solve_gamma.
      solve_id_neq.
    }
    3 : { cbn. reflexivity. }
    2: {
      eapply denote_exp_LR.
      cbn.
      solve_alist_in. }
    2 : eauto.

    vred.
    rewrite denote_term_br_1.
    vred.

    cbn.
    rename b into loopcont.
    rewrite denote_ocfg_unfold_not_in.
    vred.
    2: {
      cbn.
      assert (b0 ≢ loopcont) as NEQ by solve_id_neq.
      rewrite find_block_ineq; eauto.
    }
    rename x into mV_yoff.
    rename H0 into WRITE_MEM.

    (* Re-establish INV in post condition *)

    apply eqit_Ret; break_and_goal.
    2: eexists; eauto.
    - erewrite local_scope_modif_out.
      eauto.
      2: eapply lid_bound_between_incLocalNamed; eauto.
      2: reflexivity.
      solve_local_count.
      apply local_scope_modif_add.
      eapply lid_bound_between_shrink_down; revgoals.
      apply lid_bound_between_incLocal.
      eassumption.
      solve_local_count.
    - (* Re-establish loop invariant *)
      eapply INV_STABLE. right.
      eapply lid_bound_between_shrink.
      eapply lid_bound_between_incLocal.
      eassumption.
      solve_local_count.
      Transparent addVars.
      inv Heqs14; solve_local_count.
      Opaque addVars.

      repeat red; break_and_goal; eauto.
      3: solve_allocated.

      split; destruct INV_r; auto.
      3: red; break_and_goal.
      3: eapply dtyp_fits_after_write; eauto.
      3: assumption.

      (* Establish the relaxed state invariant with changed states and extended local environment *)
      {
        repeat intro.
        destruct (Nat.eq_dec n0 n_y); [subst |].
        {
          rewrite nth_σ_y in H0; inv H0.
          rewrite GENIR_Γ in nth_Γ_y.
          rewrite nth_Γ_y in H1; inv H1.
          eexists ptrll_y_off, _; break_and_goal; eauto.
          1: eapply dtyp_fits_after_write; eauto.
          intros _.
          exists bkh_y_off; split; eauto.
          intros.
          destruct (Nat.eq_dec (MInt64asNT.to_nat i) k).
          - rewrite e in *; clear e.
            change (UVALUE_Double v) with (dvalue_to_uvalue (DVALUE_Double v)).
            eapply write_array_cell_get_array_cell.
            2, 3: constructor.
            erewrite <- write_array_lemma; eauto.
            admit.
          - erewrite write_untouched_ptr_block_get_array_cell.
            3: eapply WRITE_MEM.
            2: eauto.
            1: eapply GETARRAYCELL_y_off_l.
            all: admit.
        }
        {
          apply nth_error_protect_ineq with (n' := n_y) in H0; auto.
          do 2 erewrite <- nth_error_Sn in H0.
          do 2 erewrite <- nth_error_Sn in H1.
          apply state_invariant_memory_invariant in PRE_INV as MEM_INV.
          replace (Γ s13) with (Γ s12) in H1 by solve_gamma.
          rewrite -> EE in H1.
          specialize (MEM_INV _ _ _ _ _ H0 H1).
          destruct v; eauto.
          - destruct x; auto.
            cbn; cbn in MEM_INV.
            destruct MEM_INV as (? & ? & ? & ? & ?).
            eexists _, _; break_and_goal; eauto.
            erewrite write_untouched; eauto.
            all: constructor.
            erewrite <- handle_gep_addr_array_same_block; eauto.
            clear st_no_id_aliasing st_no_dshptr_aliasing st_no_llvm_ptr_aliasing.
            apply st_no_llvm_ptr_aliasing in PRE_INV as NO_LLVM_ALIASING.
            eapply NO_LLVM_ALIASING with (n1 := S (S n_y)) (n2 := S (S n0)); eauto.
            + cbn; eapply nth_error_protect_eq'; eauto.
            + rewrite <- EE; cbn.
              replace (Γ s12) with (Γ s0) by solve_gamma.
              eassumption.
            + intro C; rewrite C in *.
              rewrite <- EE in H1; cbn in H1.
              replace (Γ s12) with (Γ s0) in H1 by solve_gamma.
              apply st_no_id_aliasing in PRE_INV as NO_ID_ALIASING.
              eapply n1.
              do 2 apply Nat.succ_inj.
              cbn in H0.
              rewrite nth_error_protect_neq in H0 by auto.
              eapply NO_ID_ALIASING; cbn.
              1: eapply nth_error_protect_eq'.
              2: eapply nth_error_protect_ineq.
              4, 5: rewrite <- EE; cbn.
              4, 5: replace (Γ s12) with (Γ s0) by solve_gamma.
              all: eauto.
          - destruct x; auto.
            cbn; cbn in MEM_INV.
            destruct MEM_INV as (? & ? & ? & ? & ?).
            eexists _, _; break_and_goal; eauto.
            erewrite write_untouched; eauto.
            all: constructor.
            erewrite <- handle_gep_addr_array_same_block; eauto.
            clear st_no_id_aliasing st_no_dshptr_aliasing st_no_llvm_ptr_aliasing.
            apply st_no_llvm_ptr_aliasing in PRE_INV as NO_LLVM_ALIASING.
            eapply NO_LLVM_ALIASING with (n1 := S (S n_y)) (n2 := S (S n0)); eauto.
            + cbn; eapply nth_error_protect_eq'; eauto.
            + rewrite <- EE; cbn.
              replace (Γ s12) with (Γ s0) by solve_gamma.
              eassumption.
            + intro C; rewrite C in *.
              rewrite <- EE in H1; cbn in H1.
              replace (Γ s12) with (Γ s0) in H1 by solve_gamma.
              apply st_no_id_aliasing in PRE_INV as NO_ID_ALIASING.
              eapply n1.
              do 2 apply Nat.succ_inj.
              cbn in H0.
              rewrite nth_error_protect_neq in H0 by auto.
              eapply NO_ID_ALIASING; cbn.
              1: eapply nth_error_protect_eq'.
              2: eapply nth_error_protect_ineq.
              4, 5: rewrite <- EE; cbn.
              4, 5: replace (Γ s12) with (Γ s0) by solve_gamma.
              all: eauto.
          - destruct MEM_INV as (? & ? & ? & ? & ? & ?).
            eexists _, _; break_and_goal; eauto.
            1: eapply dtyp_fits_after_write; eauto.
            intro; subst.
            destruct H5 as (? & ? & ?); auto.
            eexists; split; eauto.
            intros.
            erewrite write_untouched_ptr_block_get_array_cell; eauto.
            enough (fst dst_addr ≢ fst x2) by
                   (intro C; symmetry in C; contradiction).
            erewrite <- handle_gep_addr_array_same_block; eauto.
            clear st_no_id_aliasing st_no_dshptr_aliasing st_no_llvm_ptr_aliasing.
            apply st_no_llvm_ptr_aliasing in PRE_INV as NO_LLVM_ALIASING.
            eapply NO_LLVM_ALIASING with (n1 := S (S n_y)) (n2 := S (S n0)); eauto.
            + cbn; eapply nth_error_protect_eq'; eauto.
            + rewrite <- EE; cbn.
              replace (Γ s12) with (Γ s0) by solve_gamma.
              eassumption.
            + intro C; rewrite C in *.
              rewrite <- EE in H1; cbn in H1.
              replace (Γ s12) with (Γ s0) in H1 by solve_gamma.
              apply st_no_id_aliasing in PRE_INV as NO_ID_ALIASING.
              eapply n1.
              do 2 apply Nat.succ_inj.
              cbn in H0.
              rewrite nth_error_protect_neq in H0 by auto.
              eapply NO_ID_ALIASING; cbn.
              1: eapply nth_error_protect_eq'.
              2: eapply nth_error_protect_ineq.
              4, 5: rewrite <- EE; cbn.
              4, 5: replace (Γ s12) with (Γ s0) by solve_gamma.
              all: eauto.
        }
      }
      (* {
        (* TODO: The write state invariant doesn't take account to when pointers are different.
        Need to specify a range that is not being written to and state that the dst_addr is contained in it*)

        eapply state_invariant_cons2 with (s := s9). solve_local_count.
        eapply EE.
        destruct PRE_INV'.
        split; eauto.
        (* TRICKY MEMORY INVARIANT RE-STATING -.- *)
        cbn.
        cbn in mem_is_inv. clear INV' INV_r.
        (* partial memory write invariant *)
        destruct INV_p as (FITS_p & INLG_p & MLU_f).
        (* "Clean your room" *)
        clear RET1 RET2 Mono_IRState extends exp_in_scope exp_correct.
        clear NOFAIL' FITS_xoff_l INLG_xoff_l MLUP_xoff_l GETARRAYCELL_xoff_l UNIQ0 UNIQ1 UNIQ2.
        clear EQ_y_HG.
        clean_goal.
        rename WRITE_MEM into ptrll_INLG.
        rename H1 into WRITE_dst.

        pose proof LUn0. pose proof Heqo0.
        intros * CLU CEq.
        rewrite <- EE in CEq.
        destruct (Nat.eq_dec n2 (S (S n1))) eqn : IS_IT_THE_WRITTEN_ADDRESS ; subst.
        (* Yes, it is the address being written to (ptrll_yoff). *)
        {
          intros. specialize (mem_is_inv (S (S n1))). cbn in mem_is_inv.
          rewrite <- EE in mem_is_inv. specialize (mem_is_inv _ _ _ _ H1 H0).
          cbn in CLU, CEq. rewrite H0 in CEq.
          rewrite H1 in CLU. inv CEq. inv CLU.
          edestruct mem_is_inv as (? & ? & ? & ? & ? & ?); clear mem_is_inv.
          inv H2. clear H5.
          exists x1. eexists. split; eauto. split.
          eapply dtyp_fits_after_write; eauto.
          split; eauto. intros. inv H2.
        }

        (* No, but perhaps it is still covered by the partial write invariant. *)
        {
          intros. rewrite EE in CEq.
          assert (x0 ≢ y). {
            intro. subst. apply n3.
            eapply st_no_id_aliasing; eauto.
            rewrite <- EE. eauto.
          }

          specialize (mem_is_inv n2). cbn in mem_is_inv.
          specialize (mem_is_inv _ _ _ _ CLU CEq).
          destruct v0; eauto.
          {
            (* [Case] v0 is a natVal *)
            (* WTS: in_local_or_global_scalar li' g0 mV_yoff @id (dvalue_of_int n4) τ *)
            destruct x0; eauto.
            red in mem_is_inv.
            edestruct mem_is_inv as (? & ? & ? & ? & ?); clear mem_is_inv.
            cbn. inv H3. eexists x0. eexists. split; eauto. split; eauto.
            (* Is it covered by the partial write on mV? *)

            assert (no_overlap_dtyp dst_addr DTYPE_Double x0 (typ_to_dtyp [] x1)) as NOALIAS'.
            {
              unfold no_overlap_dtyp.
              unfold no_overlap.
              left.

              rewrite <- (handle_gep_addr_array_same_block _ _ _ _ HDST_GEP).

              intros BLOCKS; symmetry in BLOCKS; revert BLOCKS.

              do 2 red in st_no_llvm_ptr_aliasing.
              rewrite <- EE in CEq. 
              specialize (st_no_llvm_ptr_aliasing (ID_Global id) x0 y ptrll_yoff n2 (S (S n1))).
              cbn in st_no_llvm_ptr_aliasing.
              eapply st_no_llvm_ptr_aliasing. eauto. eauto. rewrite <- EE. eauto. rewrite <- EE. eauto. eauto. eauto.
              eauto.
            }
            (* No *)
            cbn in H4.
            erewrite write_untouched; eauto. constructor.
          }
          {
            (* [Case] v0 is a CTypeVal *)
            red in mem_is_inv.
            destruct x0; eauto.

            edestruct mem_is_inv as (? & ? & ? & ? & ?); clear mem_is_inv.

            cbn. inv H3. eexists x0. eexists. split; eauto. split; eauto.
            (* Is it covered by the partial write on mV? *)

            assert (no_overlap_dtyp dst_addr DTYPE_Double x0 (typ_to_dtyp [] x1)) as NOALIAS'.
            {
              unfold no_overlap_dtyp.
              unfold no_overlap.
              left.

              rewrite <- (handle_gep_addr_array_same_block _ _ _ _ HDST_GEP).

              intros BLOCKS; symmetry in BLOCKS; revert BLOCKS.

              do 2 red in st_no_llvm_ptr_aliasing.
              rewrite <- EE in CEq. 
              specialize (st_no_llvm_ptr_aliasing (ID_Global id) x0 y ptrll_yoff n2 (S (S n1))).
              cbn in st_no_llvm_ptr_aliasing.
              eapply st_no_llvm_ptr_aliasing. eauto. eauto. rewrite <- EE. eauto. rewrite <- EE. eauto. eauto. eauto.
              eauto.
            }
            (* No *)
            cbn in H4.
            erewrite write_untouched; eauto. constructor.
          }
          {
            (* It's a pointer! Pointer ! *)
            clean_goal. subst I. clear INV_STABLE. clear WHILE Heqs6 Heqs14 Heqs13.
            clear E.
            clean_goal.
            clear EQ_y_HG'.
            revert MINV_YOFF; intros.

            edestruct mem_is_inv as (? & ? & ? & ? & ? & ?); clear mem_is_inv.

            eexists. eexists. split; eauto.

            split. eapply dtyp_fits_after_write; eauto.

            split; eauto. intros.
            specialize (H6 H7).
            destruct H6 as (? & ? & ? ).
            eexists. split; eauto.
            intros.
            inv H3.
            erewrite write_untouched_ptr_block_get_array_cell.
            2 : eauto.
            2 : eauto.
            eauto.

            assert (fst x1 ≢ fst ptrll_yoff). {
              do 2 red in st_no_llvm_ptr_aliasing.
              rewrite <- EE in CEq. 
              specialize (st_no_llvm_ptr_aliasing x0 x1 y ptrll_yoff n2 (S (S n1))).
              cbn in st_no_llvm_ptr_aliasing.
              eapply st_no_llvm_ptr_aliasing. eauto. eauto. rewrite <- EE. eauto. rewrite <- EE. eauto. eauto. eauto.
              eauto.
            }

            assert (fst ptrll_yoff ≡ fst dst_addr). {
              revert HDST_GEP; intros.
              unfold handle_gep_addr in HDST_GEP.
              destruct ptrll_yoff. cbn in HDST_GEP. inv HDST_GEP. cbn. auto.
            }
            rewrite <- H7. auto.
          }
        }
      } *)

      {
        eapply state_invariant_cons2 with (s' := s12) in PRE_INV.
        3: rewrite <- EE.
        3: reflexivity.
        2: solve_local_count.
        eapply no_llvm_ptr_aliasing_gamma with (s1 := s12).
        2: solve_gamma.
        eapply no_llvm_ptr_aliasing_protect.
        destruct PRE_INV; cbn in *.
        eassumption.
      }

      (* Partial memory up to (S k) *)
      {
        (* intros. *)
        intros i v Bounds_sz MLU_k.
        (* rename MINV_Y_OFF into MINV_partial.
        revert MINV_partial; intros. *)

        destruct (@dec_eq_nat (MInt64asNT.to_nat i) k).
        {
          rewrite H0 in *; clear i H0.
          (* This is the index that _was_ written to. *)
          rewrite mem_lookup_mem_add_eq in MLU_k; inv MLU_k.
          erewrite <- read_array.
          change (UVALUE_Double v) with (dvalue_to_uvalue (DVALUE_Double v)).
          eapply write_read.
          - constructor.
          - eassumption.
          - constructor.
          - solve_allocated.
          - eassumption.
        }
        {
          erewrite write_array_cell_untouched.
          eapply GETARRAYCELL_y_off_l.
          - lia.
          - erewrite <- mem_lookup_mem_add_neq; eauto.
          - erewrite <- write_array_lemma; eauto.
          - constructor.
          - intro.
            rewrite repr_of_nat_to_nat in H1.
            rewrite Integers.Int64.unsigned_repr_eq in H1.
            rewrite Z.mod_small in H1 by lia.
            apply f_equal with (f := Z.to_nat) in H1.
            rewrite Znat.Nat2Z.id in H1.
            eapply H0; subst.
            reflexivity.
        }
      }
    (* local_scope_modif s1 s12 li (li' [py : UVALUE_Addr y_GEP_addr]) *)
    - eapply local_scope_modif_add'.
      eapply lid_bound_between_shrink.
      eapply lid_bound_between_incLocal.
      eassumption.
      solve_local_count.
      Transparent addVars.
      inv Heqs14; solve_local_count.
      eapply local_scope_modif_shrink
        with (s1 := s1) (s4 := s12)
        in extends.
      2, 3: inv Heqs14; solve_local_count.
      eapply local_scope_modif_sub'_l in extends.
      eapply local_scope_modif_sub'_l in extends.
      eapply local_scope_modif_sub'_l in extends.
      eapply local_scope_modif_sub'_l in extends.
      eassumption.
      all: eapply lid_bound_between_shrink;
        [ eapply lid_bound_between_incLocal; eassumption
        | inv Heqs14; solve_local_count
        | inv Heqs14; solve_local_count ].
      Opaque addVars.
  }

  (* I stable under local env extension *)
  forward GENC; [clear GENC |]; eauto.

  forward GENC; [clear GENC |].
  { get_local_count_hyps.
    Transparent addVars.
    unfold addVars in Heqs14. inv Heqs14.
    cbn in Heqs15. lia. } 

  forward GENC; [clear GENC |].
  { reflexivity. }

  (* P -> I 0 *)
  forward GENC; [clear GENC |].
  {
    subst I P; red; intros; auto. destruct a; eauto.
    destruct p; eauto. destruct b1; eauto. destruct p; eauto.
    intuition. subst.
    destruct H0.
    cbn.
    unfold memory_invariant in mem_is_inv.
    (* erewrite <- nth_error_protect_neq in Heqo. *)
    rewrite GENIR_Γ in nth_Γ_y.
    specialize (mem_is_inv _ _ _ _ _ nth_σ_y nth_Γ_y).
    cbn in mem_is_inv.
    edestruct mem_is_inv as (?  & ? & ? & ? & ? & ?). inv H.
    split; eauto. subst. solve_allocated.
  }

  (* I n -> Q *)
  forward GENC; [clear GENC |].
  {
    subst I P Q; red; intros; auto. destruct a; auto.
    destruct p; eauto. destruct b1; eauto. destruct p; eauto.
    destruct H as (? & ? & ? & ? & ?). subst.
    destruct H.
    break_and_goal; eauto.
    destruct H0 as (? & ? & ?).
    split; eauto; revgoals.

    (* id's are still well-allocated. *)
    {
      red in st_id_allocated. red. intros.
      destruct (@dec_eq_nat n0 n_y). subst.
      rewrite nth_σ_y in H2. inv H2.
      apply mem_block_exists_memory_set_eq. reflexivity.
      apply mem_block_exists_memory_set. eapply st_id_allocated.
      eauto.
    }

    repeat intro.
    specialize (mem_is_inv _ _ _ _ _ H2 H4).
    destruct v; auto.
    destruct mem_is_inv as (? & ? & ? & ? & ? & ?).
    destruct (Nat.eq_dec n0 n_y); [subst |].
    - rewrite nth_σ_y in H2; inv H2.
      rewrite GENIR_Γ in nth_Γ_y.
      rewrite nth_Γ_y in H4; inv H4.
      eexists ptrll_y_off, _; break_and_goal; eauto.
      intros _.
      rewrite memory_lookup_memory_set_eq.
      eexists; split; eauto.
      intros.
      eapply H1; auto; lia.
    - eexists _, _; break_and_goal; eauto.
    intro; subst.
    conclude H8 auto.
    destruct H8 as (? & ? & ?).
    eexists; split; eauto.
    rewrite memory_lookup_memory_set_neq; auto.
    intro C; symmetry in C; subst.
    eapply st_no_llvm_ptr_aliasing; eauto.
  }

  setoid_rewrite <- bind_ret_r at 6.

  vstep.
  eapply eutt_clo_bind_returns.

  (* PRECONDITION *)

  eapply GENC.
  {
    subst P I. clear GENC.
    cbn. split; [|split]; eauto.
    eapply state_invariant_Γ. eauto.
    solve_gamma. solve_local_count.
  }

  intros [[]|]; intros (? & ? & ? & []) (? & ? & ?) RET1 RET2; subst P I; try_abs;
  cbn in H0; try destruct H0 as (? & <- & <- & ?); try contradiction.
  2 : { destruct H; inv H. } (* absurd *)

  vred.
  apply eqit_Ret.

  (* genIR *)
  {
    split; [| split]; cbn; eauto.
    - destruct H0 as (? & ? & ?); subst.
      destruct H0.
      split; eauto.
    - destruct H; eauto.
    - solve_local_scope_modif.
  }
Admitted.
