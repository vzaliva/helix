Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.

Set Nested Proofs Allowed.


Set Implicit Arguments.
Set Strict Implicit.

Import MDSHCOLOnFloat64.
Import D.

Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope nat_scope.

Section TFor.
  (* Experimenting with a pure vellvm specification of genWhileLoop via a [tfor] itree combinator *)
  Import ITreeNotations.

  Definition tfor {E X} (body : nat -> X -> itree E X) from to : X -> itree E X :=
    fun x => iter (fun '(p,x) =>
                  if EqNat.beq_nat p to
                  then Ret (inr x)
                  else
                    y <- (body p x);; (Ret (inl (S p,y)))
               ) (from,x).


  Lemma tfor_0: forall {E A} k (body : nat -> A -> itree E A) a0,
      tfor body k k a0 ≈ Ret a0.
  Proof.
    intros; unfold tfor; cbn.
    unfold iter, CategoryKleisli.Iter_Kleisli, Basics.iter, MonadIter_itree.
    rewrite unfold_iter, Nat.eqb_refl, bind_ret_l.
    reflexivity.
  Qed.

  Lemma tfor_unroll: forall {E A} i j (body : nat -> A -> itree E A) a0,
      i < j ->
      tfor body i j a0 ≈
      a <- body i a0;; tfor body (S i) j a.
  Proof.
    intros; unfold tfor; cbn.
    unfold iter, CategoryKleisli.Iter_Kleisli, Basics.iter, MonadIter_itree.
    rewrite unfold_iter at 1.
    pose proof Nat.eqb_neq i j as [_ EQ].
    rewrite EQ; try lia.
    rewrite bind_bind.
    apply eutt_eq_bind; intros ?; rewrite bind_ret_l, tau_eutt.
    reflexivity.
  Qed.

  Lemma tfor_split: forall {E A} (body : nat -> A -> itree E A) i j k a0,
      i <= j ->
      j <= k ->
      tfor body i k a0 ≈
      a <- tfor body i j a0;; tfor body j k a. 
  Proof.
    intros * LE1 LE2.
    remember (j - i) as p; revert a0 i LE1 Heqp.
    induction p as [| p IH]; intros ? ? LE1 EQ.
    - replace i with j by lia.
      rewrite tfor_0, bind_ret_l.
      reflexivity.
    - rewrite tfor_unroll; [| lia].
      rewrite tfor_unroll; [| lia].
      rewrite bind_bind.
      apply eutt_eq_bind; intros ?.
      eapply IH; lia.
  Qed.

  Lemma eutt_tfor: forall {E A} (body body' : nat -> A -> itree E A) i j a0,
      (forall k i, body i k ≈ body' i k) ->
      (tfor body i j a0) ≈ (tfor body' i j a0).
  Proof.
    intros.
    unfold tfor, iter, CategoryKleisli.Iter_Kleisli, Basics.iter, MonadIter_itree.
    eapply KTreeFacts.eutt_iter.
    intros [].
    break_match_goal.
    reflexivity.
    cbn.
    rewrite H.
    reflexivity.
  Qed.

End TFor.

Section DSHLoop_is_tfor.

  Transparent interp_Mem.

  (* MOVE prelude *)
  Global Instance interp_Mem_proper {X} : Proper (eutt Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp_Mem X).
  Proof.
    intros ? ? EQ ? ? <-. 
    unfold interp_Mem.
    rewrite EQ.
    reflexivity.
  Qed.  
  Global Instance interp_helix_proper {E X} : Proper (eutt Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp_helix X E).
  Proof.
    intros ? ? EQ ? ? <-. 
    unfold interp_helix.
    rewrite EQ.
    reflexivity.
  Qed.

  (* MOVE itree *)
  Lemma interp_fail_iter : 
    forall {A R : Type} (E F : Type -> Type) (a0 : A) (h : E ~> failT (itree F)) f,
      interp_fail (E := E) (T := R) h (ITree.iter f a0) ≈
                  @Basics.iter _ failT_iter _ _ (fun a => interp_fail h (f a)) a0.
  Proof.
    unfold Basics.iter, failT_iter, Basics.iter, MonadIter_itree in *; cbn.
    einit. ecofix CIH; intros *.
    rewrite 2 unfold_iter; cbn.
    rewrite !bind_bind.
    rewrite interp_fail_bind.
    ebind; econstructor; eauto.
    reflexivity.
    intros [[a1|r1]|] [[a2|r2]|] EQ; inv EQ.
    - rewrite bind_ret_l.
      rewrite interp_fail_tau.
      estep.
    - rewrite bind_ret_l, interp_fail_ret.
      eret.
    - rewrite bind_ret_l.
      eret.
  Qed.

  (* MOVE itree *)
  Lemma interp_state_iter : 
    forall {A R S : Type} (E F : Type -> Type) (s0 : S) (a0 : A) (h : E ~> Monads.stateT S (itree F)) f,
      interp_state (E := E) (T := R) h (iter f a0) s0 ≈ 
                   @Basics.iter _ MonadIter_stateT0 _ _ (fun a s => interp_state h (f a) s) a0 s0.
  Proof.
    unfold iter, CategoryKleisli.Iter_Kleisli, Basics.iter, MonadIter_stateT0, Basics.iter, MonadIter_itree in *; cbn.
    einit. ecofix CIH; intros.
    rewrite 2 unfold_iter; cbn.
    rewrite !bind_bind.
    setoid_rewrite bind_ret_l.
    rewrite interp_state_bind.
    ebind; econstructor; eauto.
    - reflexivity.
    - intros [s' []] _ []; cbn.
      + rewrite interp_state_tau.
        estep.
      + rewrite interp_state_ret; apply reflexivity.
  Qed.

  (* MOVE itree *)
  Lemma translate_iter : 
    forall {A R : Type} (E F : Type -> Type) (a0 : A) (h : E ~> F) f,
      translate (E := E) (F := F) (T := R) h (ITree.iter f a0) ≈
                ITree.iter (fun a => translate h (f a)) a0.
  Proof.
    intros; revert a0.
    einit; ecofix CIH; intros.
    rewrite 2 unfold_iter; cbn.
    rewrite translate_bind.
    ebind; econstructor; eauto.
    - reflexivity.
    - intros [|] [] EQ; inv EQ.
      + rewrite translate_tau; estep. 
      + rewrite translate_ret; apply reflexivity.
  Qed.

  Transparent interp_Mem.
  Lemma interp_helix_iter :
    forall {X : Type} (E : Type -> Type) (m0 : memoryH) A (a0 : A) f,
      @interp_helix X E (iter f a0) m0 ≈
                    iter
                    (fun '(m,a) => 
                       ITree.bind (interp_helix (f a) m)
                                  (fun x => match x with
                                         | None => Ret (inr None)
                                         | Some (m',x) => match x with
                                                         | inl x => Ret (inl (m',x))
                                                         | inr a => Ret (inr (Some (m',a)))
                                                         end
                                         end)
                    )
                    (m0,a0).
  Proof.
    unfold interp_helix, interp_Mem.
    intros.
    rewrite interp_state_iter.
    unfold Basics.iter, MonadIter_stateT0, Basics.iter, MonadIter_itree.
    rewrite interp_fail_iter.
    unfold iter, CategoryKleisli.Iter_Kleisli.
    unfold Basics.iter, failT_iter, MonadIter_stateT0, Basics.iter, MonadIter_itree.
    cbn.
    rewrite translate_iter.
    apply KTreeFacts.eutt_iter.
    intros [m a].
    rewrite translate_bind.
    cbn.
    rewrite interp_fail_bind.
    rewrite translate_bind.
    rewrite !bind_bind.
    eapply eutt_eq_bind.
    intros [[s []] |]; cbn; rewrite ?interp_fail_Ret, ?translate_ret, ?bind_ret_l, ?translate_ret; reflexivity.
  Qed.

  Lemma __interp_helix_tfor: 
    forall {E : Type -> Type} (X : Type) (body : nat -> X -> _) k n, 
      k <= n ->
        tfor (E := E) (fun k x =>
                match x with
                | None => Ret None
                | Some (m',y) =>
                  ITree.bind (interp_helix (body k y) m')
                             (fun x => match x with
                                    | None => Ret None
                                    | Some y => Ret (Some y)
                                    end)
                end) k n None ≈ Ret None.
  Proof.
    intros.
    remember (n - k) as rem.
    revert k Heqrem H.
    induction rem as [| rem IH].
    - intros ? ? ?; assert (k ≡ n) by lia; subst.
      unfold tfor.
      cbn.
      unfold iter, CategoryKleisli.Iter_Kleisli, Basics.iter, MonadIter_itree.
      rewrite unfold_iter.
      rewrite Nat.eqb_refl, bind_ret_l.
      reflexivity.
    - intros.
      unfold tfor.
      unfold iter, CategoryKleisli.Iter_Kleisli, Basics.iter, MonadIter_itree.
      cbn.
      rewrite unfold_iter.
      assert (k =? n ≡ false) by (apply Nat.eqb_neq; lia).
      rewrite H0; rewrite !bind_ret_l, tau_eutt.
      rewrite <- (IH (S k)); try lia.
      reflexivity.
  Qed.

  Lemma interp_helix_tfor {E : Type -> Type} : 
    forall (X : Type) body k n m (x : X),
      k <= n ->
      interp_helix (E := E) (tfor body k n x) m
                   ≈
                   tfor (fun k x =>
                           match x with
                           | None => Ret None
                           | Some (m',y) =>
                             ITree.bind (interp_helix (body k y) m')
                                        (fun x => match x with
                                               | None => Ret None
                                               | Some y => Ret (Some y)
                                               end)
                           end) k n (Some (m,x)).
  Proof.
    intros * LE.
    remember (n - k) as rem.
    revert m x k Heqrem LE.
    induction rem as [| rem IH].
    - intros.
      assert (k ≡ n) by lia.
      unfold tfor.
      cbn.
      unfold iter, CategoryKleisli.Iter_Kleisli, Basics.iter, MonadIter_itree.
      rewrite unfold_iter.
      rewrite H, Nat.eqb_refl, bind_ret_l, interp_helix_Ret.
      rewrite unfold_iter.
      rewrite Nat.eqb_refl, bind_ret_l.
      reflexivity.
    - intros * EQ INEQ.
      unfold tfor.
      unfold iter, CategoryKleisli.Iter_Kleisli, Basics.iter, MonadIter_itree.
      rewrite 2 unfold_iter.
      assert (k =? n ≡ false) by (apply Nat.eqb_neq; lia).
      cbn; rewrite !H.
      rewrite !bind_bind.
      rewrite interp_helix_bind.
      apply eutt_eq_bind; intros [[]|].
      + cbn; rewrite ?bind_ret_l.
        rewrite 2tau_eutt.
        specialize (IH m0 x0 (S k)).
        unfold tfor in IH.
        unfold iter, CategoryKleisli.Iter_Kleisli, Basics.iter, MonadIter_itree in IH.
        cbn in *. rewrite IH;try lia.
        reflexivity.
      + rewrite !bind_ret_l.
        rewrite tau_eutt.
        rewrite <- __interp_helix_tfor.
        unfold tfor.
        unfold iter, CategoryKleisli.Iter_Kleisli, Basics.iter, MonadIter_itree.
        cbn.
        reflexivity.
        lia.
  Qed.

  (* The denotation of the [DSHLoop] combinator can be rewritten in terms of the [do_n] combinator.
     So if we specify [genWhileLoop] in terms of this same combinator, then we might be good to go
     with a generic spec that of [GenWhileLoop] that does not depend on Helix.
   *)
  Lemma DSHLoop_as_tfor: forall σ n op,
      denoteDSHOperator σ (DSHLoop n op)
                        ≈
      tfor (fun p _ => vp <- lift_Serr (MInt64asNT.from_nat p) ;;
                    denoteDSHOperator (DSHnatVal vp :: σ) op) 0 n tt.
  Proof.
    intros.
    unfold tfor.
    cbn.
    eapply (eutt_iter'' (fun a '(b,_) => a ≡ b) (fun a '(b,_) => a ≡ b)); auto.
    intros ? [? []] <-.
    cbn.
    break_match_goal.
    apply eutt_Ret; auto.
    rewrite bind_bind.
    eapply eutt_eq_bind; intros ?.
    eapply eutt_eq_bind; intros ?.
    apply eutt_Ret; auto.
  Qed.

  (* The denotation of the [DSHLoop] combinator can be rewritten in terms of the [do_n] combinator.
     So if we specify [genWhileLoop] in terms of this same combinator, then we might be good to go
     with a generic spec that of [GenWhileLoop] that does not depend on Helix.
   *)
  Lemma DSHLoop_interpreted_as_tfor:
    forall E σ n op m,
      interp_helix (E := E) (denoteDSHOperator σ (DSHLoop n op)) m
      ≈
      tfor (fun k x => match x with
                    | None => Ret None
                    | Some (m',_) => interp_helix (vp <- lift_Serr (MInt64asNT.from_nat k) ;;
                                                  denoteDSHOperator (DSHnatVal vp :: σ) op) m'
                    end)
      0 n (Some (m, ())).
  Proof.
    intros.
    rewrite DSHLoop_as_tfor.
    rewrite interp_helix_tfor; [|lia].
    cbn.
    apply eutt_tfor.
    intros [[m' _]|] i; [| reflexivity].
    rewrite interp_helix_bind.
    rewrite bind_bind.
    apply eutt_eq_bind; intros [[?m ?] |]; [| rewrite bind_ret_l; reflexivity].
    bind_ret_r2.
    apply eutt_eq_bind.
    intros [|]; reflexivity.
  Qed.
    
End DSHLoop_is_tfor.

(* TODO: Move to Prelude *)
Definition uvalue_of_nat k := UVALUE_I64 (Int64.repr (Z.of_nat k)).

Fixpoint build_vec_gen_aux {E} (from remains: nat)
         (body : nat -> mem_block -> itree E mem_block) : mem_block -> itree E mem_block :=
  fun vec =>
    match remains with
    | 0 => ret vec
    | S remains' =>
      vec' <- body from vec;;
      build_vec_gen_aux (S from) remains' body vec'
    end.

Definition build_vec_gen {E} (from to: nat) :=
  @build_vec_gen_aux E from (to - from).

Definition build_vec {E} := @build_vec_gen E 0.

From Paco Require Import paco.
From ITree Require Import Basics.HeterogeneousRelations.

(* IY: TODO: move to ITrees*)
Lemma eutt_Proper_mono : forall {A B E},
        Proper ((@subrelationH A B) ==> (@subrelationH _ _)) (eutt (E := E)).
Proof.
  intros A B. do 3 red.
    intros E x y. pcofix CIH. pstep. red.
    intros sub a b H.
    do 2 red in H. punfold H. red in H.
    remember (observe a) as a'.
    remember (observe b) as b'.
    generalize dependent a. generalize dependent b.
    induction H; intros; eauto.
    + constructor. red in REL. destruct REL.
      right. apply CIH. assumption. assumption.
      destruct H.
    + constructor. red in REL. intros.
      specialize (REL v). unfold id.
      destruct REL. right. apply CIH. assumption. assumption.
      destruct H.
Qed.


(* TODO: Move to Vellvm Denotation_Theory.v? *)

Definition block_ids {T : Set} (b : list ((LLVMAst.block T))) :=
  map (@blk_id T) b.

Definition disjoint_bid_blocks {T : Set} (b b' : list ((LLVMAst.block T))) :=
  block_ids b ⊍ block_ids b'.

Lemma disjoint_bid_blocks_not_in_r {T : Set} (b b' : list (LLVMAst.block T)) :
  disjoint_bid_blocks b b' ->
  forall x, In x (block_ids b) -> ~ In x (block_ids b').
Proof.
  intros; eauto using Coqlib.list_disjoint_notin, Coqlib.list_disjoint_sym.
Qed.

Lemma disjoint_bid_blocks_not_in_l {T : Set} (b b' : list (LLVMAst.block T)) :
  disjoint_bid_blocks b b' ->
  forall x, In x (block_ids b') -> ~ In x (block_ids b).
Proof.
  intros; eauto using Coqlib.list_disjoint_notin, Coqlib.list_disjoint_sym.
Qed.

Lemma fold_left_acc_app : forall {a t} (l : list t) (f : t -> list a) acc,
    (fold_left (fun acc bk => acc ++ f bk) l acc ≡
    acc ++ fold_left (fun acc bk => acc ++ f bk) l [])%list.
Proof.
  intros. induction l using List.list_rev_ind; intros; cbn.
  - rewrite app_nil_r. reflexivity.
  - rewrite 2 fold_left_app, IHl.
    cbn.
    rewrite app_assoc.
    reflexivity.
Qed.

Definition imp_rel {A B : Type} (R S: A -> B -> Prop): Prop :=
  forall a b, R a b -> S a b.

Definition stable_exp_local (R: Rel_cfg) : Prop :=
    forall memH memV ρ1 ρ2 g,
      R memH (memV, (ρ1, g)) ->
      ρ1 ⊑ ρ2 ->
      R memH (memV, (ρ2, g)).

(* TODO: Show symmetric case *)
Lemma no_repet_app_not_in_l :
  forall (T : Set) id (bs bs' : list (LLVMAst.block T)), In id (block_ids bs) ->
    blk_id_norepet (bs' ++ bs) ->
    not (In id (block_ids bs')).
Proof.
  intros. destruct bs.
  inversion H.
  inv H.
  apply no_repeat_cons_not_in.
  unfold blk_id_norepet in *.
  rewrite map_app in H0.
  rewrite map_cons. rewrite map_cons in H0.
  rewrite list_cons_app in H0.
  rewrite app_assoc in H0.
  apply Coqlib.list_norepet_append_left in H0.
  rewrite list_cons_app.
  rewrite Coqlib.list_norepet_app in *.
  intuition. apply Coqlib.list_disjoint_sym. auto.
  unfold blk_id_norepet in H0.
  rewrite map_app in H0. rewrite map_cons in H0. rewrite list_cons_app in H0.
  apply Coqlib.list_norepet_append_commut in H0. rewrite <- app_assoc in H0.
  apply Coqlib.list_norepet_append_right in H0.
  rewrite Coqlib.list_norepet_app in H0.
  destruct H0 as (? & ? & ?).
  red in H2. intro. eapply H2; eauto.
Qed.


(* TODO: Show symmetric case *)
Lemma no_repet_app_not_in_r :
  forall (T : Set) id (bs bs' : list (LLVMAst.block T)), In id (block_ids bs) ->
    blk_id_norepet (bs' ++ bs) ->
    not (In id (block_ids bs')).
Proof.
  intros. destruct bs.
  inversion H.
  inv H.
  apply no_repeat_cons_not_in.
  unfold blk_id_norepet in *.
  rewrite map_app in H0.
  rewrite map_cons. rewrite map_cons in H0.
  rewrite list_cons_app in H0.
  rewrite app_assoc in H0.
  apply Coqlib.list_norepet_append_left in H0.
  rewrite list_cons_app.
  rewrite Coqlib.list_norepet_app in *.
  intuition. apply Coqlib.list_disjoint_sym. auto.
  unfold blk_id_norepet in H0.
  rewrite map_app in H0. rewrite map_cons in H0. rewrite list_cons_app in H0.
  apply Coqlib.list_norepet_append_commut in H0. rewrite <- app_assoc in H0.
  apply Coqlib.list_norepet_append_right in H0.
  rewrite Coqlib.list_norepet_app in H0.
  destruct H0 as (? & ? & ?).
  red in H2. intro. eapply H2; eauto.
Qed.

(* Useful lemmas about rcompose. TODO: Move? *)
Lemma rcompose_eq_r :
  forall A B (R: relationH A B), eq_rel (R) (rcompose R (@Logic.eq B)).
Proof.
  repeat intro. red. split; repeat intro; auto. econstructor.
  apply H. reflexivity.
  inversion H. subst. auto.
Qed.

Lemma rcompose_eq_l :
  forall A B (R: relationH A B), eq_rel (R) (rcompose (@Logic.eq A) R).
Proof.
  repeat intro. red. split; repeat intro; auto. econstructor.
  reflexivity. apply H.
  inversion H. subst. auto.
Qed.

From Vellvm Require Import Numeric.Integers.
Lemma denote_bks_prefix :
  forall (prefix bks' postfix bks : list (LLVMAst.block dtyp)) (from to: block_id),
    bks ≡ (prefix ++ bks' ++ postfix) ->
    blk_id_norepet bks ->
    denote_bks bks (from, to) ≈
               ITree.bind (denote_bks bks' (from, to))
               (fun x => match x with
                      | inl x => denote_bks bks x
                      | inr x => ret (inr x)
                      end
               ).
Proof.
  intros * ->; revert from to.
  einit.
  ecofix CIH.
  clear CIH0.
  intros * WF.
  Transparent denote_bks.
  destruct (find_block dtyp bks' to) as [bk |] eqn:EQ.
  - unfold denote_bks at 1 3.
    rewrite 2 KTreeFacts.unfold_iter_ktree.
    cbn; rewrite !bind_bind.
    assert (find_block dtyp (prefix ++ bks' ++ postfix) to ≡ Some bk).
    {
      erewrite find_block_app_r_wf; eauto.
      erewrite find_block_app_l_wf; eauto.
      eapply no_repeat_app_r; eauto.
    }
    do 2 match_rewrite.
    rewrite !bind_bind.
    eapply euttG_bind; econstructor; [reflexivity | intros [] ? <-].
    + rewrite !bind_ret_l; cbn.
      rewrite bind_tau; etau.
    + rewrite !bind_ret_l.
      reflexivity.
  - edrop.
    rewrite (denote_bks_unfold_not_in bks'); auto.
    rewrite bind_ret_l.
    reflexivity.
Qed.

(* Another Useful Vellvm utility. Obviously true, but the proof might need some tricks.. *)
(* Lemma string_of_nat_length_lt : *)
(*   (forall n m, n < m -> length (string_of_nat n) <= length (string_of_nat m))%nat. *)
(* Proof. *)
(*   induction n using (well_founded_induction lt_wf). *)
(*   intros. unfold string_of_nat. *)
(* Admitted. *)

Lemma incLocal_fresh:
    forall i i' i'' r r' , incLocal i ≡ inr (i', r) ->
                                          incLocal  i' ≡ inr (i'', r') -> r ≢ r'.
Proof.
  intros. cbn in H, H0. Transparent incLocal. unfold incLocal in *.
  intro. cbn in *. inversion H. inversion H0. subst. cbn in H6. clear -H6.
  cbn in H6. apply Name_inj in H6.
  apply append_simplify_l in H6.
  apply string_of_nat_inj in H6. auto.
  apply Nat.neq_succ_diag_l.
Qed.

Require Import String. Open Scope string_scope.

Lemma __fresh:
    forall prefix i i' i'' r r' , incLocal i ≡ inr (i', r) ->
                        incLocalNamed (prefix @@ "_next_i") i' ≡ inr (i'', r') -> r ≢ r'.
Proof.
  intros * H1 H2. cbn.
  unfold incLocal, incLocalNamed in *.
  cbn in *; inv H1; inv H2.
  intros abs; apply Name_inj in abs.
  pose proof @string_of_nat_inj. specialize (H (local_count i) (S (local_count i))).
  assert (local_count i ≢ S (local_count i)) by lia.
  specialize (H H0).
  clear H0.
  (* apply String.string_dec_sound in abs. *)
  pose proof string_dec.
  match goal with
  | [ H : ?l ≡ ?r |- _] => remember l; remember r
  end.
  specialize (H0 s s0).

  pose proof (string_dec "l" prefix). destruct H1. subst.
  destruct H0. 2 : { contradiction. }
  rewrite <- append_assoc in e. apply append_simplify_l in e.
  (* Yeeah not gonna bother with this. It's true though.
     We probably just prove the lemma for the exact string "s" we need.
   *)
Admitted.

Opaque incLocalNamed.
Opaque incLocal.

(* TODO: Figure out how to avoid this *)
Arguments fmap _ _ /.
Arguments Fmap_block _ _ _ _/.

Lemma lt_antisym: forall x, Int64.lt x x ≡ false.
Proof.
  intros.
  pose proof Int64.not_lt x x.
  rewrite Int64.eq_true, Bool.orb_comm in H.
  cbn in H.
  rewrite Bool.negb_true_iff in H; auto.
Qed.

Lemma ltu_antisym: forall x, Int64.ltu x x ≡ false.
Proof.
  intros.
  pose proof Int64.not_ltu x x.
  rewrite Int64.eq_true, Bool.orb_comm in H.
  cbn in H.
  rewrite Bool.negb_true_iff in H; auto.
Qed.

Import Int64 Int64asNT.Int64 DynamicValues.Int64.
Lemma __arith: forall j, j> 0 ->
                    (Z.of_nat j < half_modulus)%Z ->
                    add (repr (Z.of_nat (j - 1))) (repr 1) ≡
                        repr (Z.of_nat j).
Proof.
  intros .
  unfold Int64.add.
  rewrite !Int64.unsigned_repr_eq.
  cbn.
  f_equal.
  rewrite Zdiv.Zmod_small; try lia.
  unfold half_modulus in *.
  split; try lia.
  transitivity (Z.of_nat j); try lia.
  eapply Z.lt_le_trans; eauto.
  transitivity (modulus / 1)%Z.
  eapply Z.div_le_compat_l; try lia.
  unfold modulus.
  pose proof Coqlib.two_power_nat_pos wordsize; lia.
  rewrite Z.div_1_r.
  reflexivity.
Qed.

Lemma __arithu: forall j, j> 0 ->
                    (Z.of_nat j < modulus)%Z ->
                    add (repr (Z.of_nat (j - 1))) (repr 1) ≡
                        repr (Z.of_nat j).
Proof.
  intros .
  unfold Int64.add.
  rewrite !Int64.unsigned_repr_eq.
  cbn.
  f_equal.
  rewrite Zdiv.Zmod_small; try lia.
Qed.

Lemma lt_nat_to_Int64: forall j n,
    0 <= j ->
    j < n ->
    (Z.of_nat n < half_modulus)%Z ->
    lt (repr (Z.of_nat j)) (repr (Z.of_nat n)) ≡ true.
Proof.
  intros.
  unfold lt.
  rewrite !signed_repr.
  2,3:unfold min_signed, max_signed; try lia.
  break_match_goal; auto.
  lia.
Qed.

Lemma ltu_nat_to_Int64: forall j n,
    0 <= j ->
    j < n ->
    (Z.of_nat n < modulus)%Z ->
    ltu (repr (Z.of_nat j)) (repr (Z.of_nat n)) ≡ true.
Proof.
  intros.
  unfold ltu.
  rewrite !unsigned_repr.
  2,3:unfold max_unsigned; try lia.
  break_match_goal; auto.
  lia.
Qed.

Lemma lt_Z_to_Int64: forall j n,
    (0 <= j)%Z ->
    (n < half_modulus)%Z ->
    (j < n)%Z ->
    lt (repr j) (repr n) ≡ true.
Proof.
  intros.
  unfold lt.
  rewrite !signed_repr. break_match_goal; auto.
  1,2:unfold min_signed, max_signed; lia.
Qed.

Lemma ltu_Z_to_Int64: forall j n,
    (0 <= j)%Z ->
    (n < modulus)%Z ->
    (j < n)%Z ->
    ltu (repr j) (repr n) ≡ true.
Proof.
  intros.
  unfold ltu.
  rewrite !unsigned_repr. break_match_goal; auto.
  1,2:unfold max_unsigned; lia.
Qed.

Lemma alist_find_eq:
  ∀ (K V : Type) (RR : RelDec Logic.eq),
    RelDec_Correct RR → ∀ (m : alist K V) (k : K) (v : V), alist_add k v m @ k ≡ Some v.
Proof.
  intros.
  cbn.
  rewrite rel_dec_eq_true; auto.
Qed.



(** Inductive lemma to reason about while loops.
    The code generated is of the shape:
         block_entry ---> nextblock
             |
    ---->loopblock
    |        |
    |    body_entry
    |        |
    |      (body)
    |        |
     ----loopcontblock --> nextblock

 The toplevel lemma [genWhileLoop] will specify a full execution of the loop, starting from [block_entry].
 But to be inductive, this lemma talks only about the looping part:
 - we start from [loopcontblock]
 - we assume that [j] iterations have already been executed
 We therefore assume (I j) initially, and always end with (I n). 
 We proceed by induction on the number of iterations remaining, i.e. (n - j).

 Since in order to reach [loopcontblock], we need to have performed at least one iteration, we have the
 following numerical bounds:
 - j > 0
 - j <= n
 - Z.of_nat n < Int64.modulus (or the index would overflow)
 *)
Lemma genWhileLoop_tfor_ind: 
  forall (prefix : string)
    (loopvar : raw_id)            (* lvar storing the loop index *)
    (loopcontblock : block_id)    (* reentry point from the body back to the loop *)
    (body_entry : block_id)       (* entry point of the body *)
    (body_blocks : list (LLVMAst.block typ)) (* (llvm) body to be iterated *)
    (nextblock : block_id)        (* exit point of the overall loop *)
    (entry_id : block_id)         (* entry point of the overall loop *)
    (s1 s2 : IRState)
    (bks : list (LLVMAst.block typ)) ,

    In body_entry (block_ids body_blocks) ->

    (* All labels generated are distinct *)
    blk_id_norepet bks ->

    fresh_in_cfg bks nextblock -> 

    forall (n : nat)                     (* Number of iterations *)

      (* Generation of the LLVM code wrapping the loop around bodyV *)
      (HGEN: genWhileLoop prefix (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n))
                          loopvar loopcontblock body_entry body_blocks [] nextblock s1
                          ≡ inr (s2,(entry_id, bks))) 

      (* Computation on the other side, operating over some type of accumulator [A], *)
      (* i.e. the counterpart to bodyV (body_blocks) *)
      (A : Type)
      (bodyF: nat -> A -> itree _ A)


      (j : nat)                       (* Next iteration to be performed *)
      (UPPER_BOUND : 0 < j <= n)
      (NO_OVERFLOW : (Z.of_nat n < Int64.modulus)%Z)

      (* Main relations preserved by iteration *)
      (I : nat (* -> A *) -> A -> _),

      (* We assume that we know how to relate the iterations of the bodies *)
      (forall g l mV a k _label _label',
          (conj_rel (I k)
                    (fun _ '(_, (l, _)) => l @ loopvar ≡ Some (uvalue_of_nat k))
                    a (mV,(l,g))) ->
          eutt
            ( (fun a' '(memV, (l, (g, x))) =>
                 l @ loopvar ≡ Some (uvalue_of_nat k) /\
                 x ≡ inl (_label', loopcontblock) /\
                 I (S k) (* a *) a' (memV, (l, g))))
            (bodyF k a)
            (interp_cfg (denote_bks (convert_typ [] body_blocks) (_label, body_entry)) g l mV)
      ) ->

      (* Invariant is stable under the administrative bookkeeping that the loop performs *)
      (forall a sa b sb c sc d sd e se msg msg' msg'',
          incBlockNamed msg s1 ≡ inr (sa, a) ->
          incBlockNamed msg' sa ≡ inr (sb, b) ->
          incLocal sb ≡ inr (sc,c) ->
          incLocal sc ≡ inr (sd,d) ->
          incLocalNamed msg'' sd ≡ inr (se, e) ->
          forall k a l mV g id v,
            id ≡ c \/ id ≡ d \/ id ≡ e \/ id ≡ loopvar ->
            I k a (mV, (l, g)) ->
            I k a (mV, ((alist_add id v l), g))) ->

    (* Main result. Need to know initially that P holds *)
    forall g l mV a _label,
      (conj_rel
         (I j)
         (fun _ '(_, (l, _)) => l @ loopvar ≡ Some (uvalue_of_nat (j - 1)))
         a (mV,(l,g))
      ) ->
      eutt (fun a '(memV, (l, (g,x))) =>
              x ≡ inl (loopcontblock, nextblock) /\
              I n a (memV,(l,g))
           )
           (tfor bodyF j n a) 
           (interp_cfg (denote_bks (convert_typ [] bks)
                                                (_label, loopcontblock)) g l mV).
Proof.
  intros * IN UNIQUE_IDENTS NEXTBLOCK_ID * GEN A LVAR_FRESH *.
  unfold genWhileLoop in GEN. cbn* in GEN. simp.
  intros BOUND OVER * FBODY STABLE.
  
  remember (n - j) as k eqn:K_EQ.
  revert j K_EQ BOUND.
  induction k as [| k IH]; intros j EQidx.

  - (* Base case: we enter through [loopcontblock] and jump out immediately to [nextblock] *)
    intros  BOUND * (INV & LOOPVAR).
    (* Import ProofMode. *)
    (* This ugly preliminary is due to the conversion of types, as most ugly things on Earth are. *)
    apply no_repeat_convert_typ with (env := []) in UNIQUE_IDENTS; cbn in UNIQUE_IDENTS; rewrite ?convert_typ_block_app in UNIQUE_IDENTS.
    apply fresh_in_convert_typ with (env := []) in NEXTBLOCK_ID; cbn in NEXTBLOCK_ID; rewrite ?convert_typ_block_app in NEXTBLOCK_ID.
    cbn; rewrite ?convert_typ_block_app.
    hide_cfg.
    (* We jump into [loopcontblock]
       We denote the content of the block.
     *)
    vjmp.

    cbn.
    assert (n ≡ j) by lia; subst.
    (* replace (j - S j) with 0 by lia. *)

    vred.
    vred.
    vred.
    vstep. 
    {
      vstep.
      vstep; solve_lu; reflexivity.
      vstep; reflexivity.
      all: reflexivity.
    }
    vred.
    vstep.
    {
      cbn.
      vstep.
      vstep; solve_lu; reflexivity.
      vstep; reflexivity.
      all:reflexivity.
    }      

    (* We now branch to [nextblock] *)
    vbranch_r.
    { vstep.
      solve_lu.
      apply eutt_Ret; repeat f_equal.
      cbn.
      clear - BOUND OVER.
      destruct BOUND as [? _].
      rewrite __arithu; try lia.
      unfold eval_int_icmp.
      rewrite ltu_antisym.
      reflexivity.
    }

    vjmp_out.
    cbn.
    replace (j - j) with 0 by lia.
    cbn; vred.

    rewrite tfor_0.
    (* We have only touched local variables that the invariant does not care about, we can reestablish it *)
    apply eutt_Ret.
    split.
    + reflexivity.
    + eapply STABLE; eauto.

  - (* Inductive case *)
    cbn in *. intros [LT LE] * (INV & LOOPVAR).
    (* This ugly preliminary is due to the conversion of types, as most ugly things on Earth are. *)
    apply no_repeat_convert_typ with (env := []) in UNIQUE_IDENTS; cbn in UNIQUE_IDENTS; rewrite ?convert_typ_block_app in UNIQUE_IDENTS.
    apply fresh_in_convert_typ with (env := []) in NEXTBLOCK_ID; cbn in NEXTBLOCK_ID; rewrite ?convert_typ_block_app in NEXTBLOCK_ID.
    cbn; rewrite ?convert_typ_block_app.
    cbn in IH; rewrite ?convert_typ_block_app in IH.
    hide_cfg.

    (* RHS : Reducing RHS to apply Body Hypothesis *)
    (* Step 1 : First, process [loopcontblock] and check that k<n, and hence that we do not exit *)
    vjmp.
    cbn.
    vred.
    vred.
    vred.
    vstep.
    {
      vstep.
      vstep; solve_lu.
      vstep; solve_lu.
      all: reflexivity.
    }
    vred.
    vstep.
    {
      cbn; vstep.
      vstep; solve_lu.
      vstep; solve_lu.
      all: reflexivity.
    }
    vred.

    (* Step 2 : Jump to b0, i.e. loopblock (since we have checked k < n). *)
    vbranch_l. 
    { cbn; vstep;  try solve_lu.
      rewrite __arithu; try lia.
      apply eutt_Ret.
      repeat f_equal.
      clear - EQidx LT LE OVER.
      unfold eval_int_icmp; rewrite ltu_nat_to_Int64; try lia.
      reflexivity.
    }

    vjmp.
    (* We update [loopvar] via the phi-node *)
    cbn; vred.

    focus_single_step_v.

    (* BEGIN TODO: infrastructure to deal with non-empty phis *)
    unfold denote_phis.
    cbn.
    rewrite denote_phi_tl; cycle 1.
    {
      inv VG. inversion UNIQUE_IDENTS.
      subst. intro. subst. apply H1. right.
      rewrite map_app.
      apply in_or_app. right. constructor. reflexivity.
    }

    rewrite denote_phi_hd.
    cbn.
    (* TOFIX: broken automation, a wild translate sneaked in where it shouldn't *)
    rewrite translate_bind.
    rewrite ?interp_cfg_to_L3_ret, ?bind_ret_l;
      rewrite ?interp_cfg_to_L3_bind, ?bind_bind.

    vstep.
    {
      setoid_rewrite lookup_alist_add_ineq.
      setoid_rewrite lookup_alist_add_eq. reflexivity. subst.
      intros ?; eapply __fresh; eauto.
    }
    (* TOFIX: broken automation, a wild translate sneaked in where it shouldn't *)
    rewrite translate_ret.
    repeat vred.
    cbn.
    repeat vred.
    (* TOFIX: we leak a [LocalWrite] event *)
    rewrite interp_cfg_to_L3_LW.
    repeat vred.
    subst.
    cbn.
    (* END TODO: infrastructure to deal with non-empty phis *)

    vred.
    (* Step 3 : we jump into the body *)
    vred.

    (* In order to use our body hypothesis, we need to restrict the ambient cfg to only the body *)
    inv VG.
    rewrite denote_bks_prefix; cycle 1; auto.
    {
      match goal with
        |- ?x::?y::?z ≡ _ => replace (x::y::z) with ([x;y]++z)%list by reflexivity
      end; f_equal.
    }
    hide_cfg.
    (* rewrite <- EQidx. *)

    cbn; vred.
    destruct j as [| j]; [lia |].
    rewrite tfor_unroll; [| lia].

    eapply eutt_clo_bind.
    (* We can now use the body hypothesis *)
    eapply FBODY.
    {
      (* A bit of arithmetic is needed to prove that we have the right precondition *)
      split.
      + repeat (eapply STABLE; eauto).

      + rewrite alist_find_eq.
        reflexivity.
        typeclasses eauto.
    }

    (* Step 4 : Back to starting from loopcontblock and have reestablished everything at the next index:
        conclude by IH *)
    intros ? (? & ? & ? & ?) (LOOPVAR' & HS & IH').
    subst.
    eapply IH; try lia.
    split; auto.
    Unshelve.
    all: try auto.
Qed.

Lemma genWhileLoop_tfor_correct:
  forall (prefix : string)
    (loopvar : raw_id)            (* lvar storing the loop index *)
    (loopcontblock : block_id)    (* reentry point from the body back to the loop *)
    (body_entry : block_id)       (* entry point of the body *)
    (body_blocks : list (LLVMAst.block typ)) (* (llvm) body to be iterated *)
    (nextblock : block_id)        (* exit point of the overall loop *)
    (entry_id : block_id)         (* entry point of the overall loop *)
    (s1 s2 : IRState) 
    (bks : list (LLVMAst.block typ)) ,

    In body_entry (block_ids body_blocks) ->

    (* All labels generated are distinct *)
    blk_id_norepet bks ->

    fresh_in_cfg bks nextblock ->

    forall (n : nat)                     (* Number of iterations *)
      
      (* Generation of the LLVM code wrapping the loop around bodyV *)
      (HGEN: genWhileLoop prefix (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n))
                          loopvar loopcontblock body_entry body_blocks [] nextblock s1
                          ≡ inr (s2,(entry_id, bks))) 

      (* Computation on the Helix side performed at each cell of the vector, *)
      (*    the counterpart to bodyV (body_blocks) *)
      A
      (bodyF: nat -> A -> itree _ A)

      (NO_OVERFLOW : (Z.of_nat n < Int64.modulus)%Z)

      (* Main relations preserved by iteration *)
      (I : nat -> _) P Q,

      (* We assume that we know how to relate the iterations of the bodies *)
      (forall g l mV a k _label _label',
          (conj_rel (I k)
                    (fun _ '(_, (l, _)) => l @ loopvar ≡ Some (uvalue_of_nat k))
                    a (mV,(l,g))) ->
          eutt
            ( (fun a' '(memV, (l, (g, x))) =>
                 l @ loopvar ≡ Some (uvalue_of_nat k) /\
                 x ≡ inl (_label', loopcontblock) /\
                 I (S k) (* a *) a' (memV, (l, g))))
            (bodyF k a)
            (interp_cfg (denote_bks (convert_typ [] body_blocks) (_label, body_entry)) g l mV)
      ) ->


    (* Invariant is stable under the administrative bookkeeping that the loop performs *)
    (forall a sa b sb c sc d sd e se msg msg' msg'',
          incBlockNamed msg s1 ≡ inr (sa, a) ->
          incBlockNamed msg' sa ≡ inr (sb, b) ->
          incLocal sb ≡ inr (sc,c) ->
          incLocal sc ≡ inr (sd,d) ->
          incLocalNamed msg'' sd ≡ inr (se, e) ->
          forall k a l mV g id v,
            id ≡ c \/ id ≡ d \/ id ≡ e \/ id ≡ loopvar ->
            I k a (mV, (l, g)) ->
            I k a (mV, ((alist_add id v l), g))) ->

    (* R must be stable by extension of the local env *)
      (* (forall mH mV g l l', *)
      (*     l ⊑ l' -> *)
      (*                       R mH (mV, (l, g)) -> *)
      (*                       R mH (mV, (l', g))) -> *)

    (* We bake in the weakening on the extremities to ease the use of the lemma *)
    imp_rel P (I 0) ->
    imp_rel (I n) Q ->

    (* (forall g l mV a ymem, *)
    (*     (R a (mV, (l, g)) -> I 0 mem_empty mH (mV, (l, g)) /\ l @ loopvar ≡ Some (uvalue_of_nat 0)) /\ *)
    (*     (I n ymem mH (mV, (l, g)) -> R mH (mV, (l, g)))) -> *)

    (* Main result. Need to know initially that R holds *)
    forall g l mV a _label,
      P a (mV,(l,g)) ->
      eutt (fun a '(memV, (l, (g,x))) =>
              (* Consider generalizing? *)
              (x ≡ inl (loopcontblock, nextblock) \/
               x ≡ inl (entry_id, nextblock)) /\
              Q a (memV,(l,g)))
           (tfor bodyF 0 n a) 
           (interp_cfg (denote_bks (convert_typ [] bks) (_label ,entry_id)) g l mV).
Proof. 

  intros * IN UNIQUE EXIT * GEN * BOUND * IND STABLE pre post IMPSTATE IND_INV * PRE.
  pose proof @genWhileLoop_tfor_ind as GEN_IND.
  specialize (GEN_IND prefix loopvar loopcontblock body_entry body_blocks nextblock entry_id s1 s2 bks).
  specialize (GEN_IND IN UNIQUE EXIT n GEN).
  unfold genWhileLoop in GEN. cbn* in GEN. simp.
  destruct n as [| n].
  - (* 0th index *)
    cbn.

    apply fresh_in_convert_typ with (env := []) in EXIT; cbn in EXIT; rewrite ?convert_typ_block_app in EXIT.
    cbn; rewrite ?convert_typ_block_app.
    cbn in GEN_IND; rewrite ?convert_typ_block_app in GEN_IND.

    hide_cfg.
    vjmp.

    vred. vred. vred. vstep.
    {
      cbn.
      vstep.
      vstep; solve_lu; reflexivity.
      vstep; reflexivity.
      all:reflexivity.
    }

    (* We now branch to [nextblock] *)
    vbranch_r.
    { vstep.
      solve_lu.
      apply eutt_Ret; repeat f_equal.
    }

    vjmp_out.
    vred.
    cbn.
    rewrite tfor_0.

    (* We have only touched local variables that the invariant does not care about, we can reestablish it *)
    apply eutt_Ret. cbn. split. right. reflexivity.
    eapply post; eapply STABLE; eauto.

  - cbn in *.

    (* Clean up convert_typ junk *)
    apply fresh_in_convert_typ with (env := []) in EXIT; cbn in EXIT; rewrite ?convert_typ_block_app in EXIT.
    apply no_repeat_convert_typ with (env := []) in UNIQUE; cbn in UNIQUE; rewrite ?convert_typ_block_app in UNIQUE.
    cbn; rewrite ?convert_typ_block_app.
    cbn in GEN_IND; rewrite ?convert_typ_block_app in GEN_IND.

    hide_cfg.

    vjmp.
    cbn.
    vred. vred. vred.
    vstep.
    {
      vstep. vstep; solve_lu.
      vstep; solve_lu.
      all :reflexivity.
    }
    vstep. 

    (* Step 1 : Jump to b0, i.e. loopblock (since we have checked k < n). *)
    vbranch_l.
    {
      cbn; vstep.
      match goal with
        |- Maps.lookup ?k (alist_add ?k ?a ?b) ≡ _ =>
        rewrite (lookup_alist_add_eq _ _ b)
      end; reflexivity.
      unfold eval_int_icmp. cbn.
      rewrite ltu_Z_to_Int64; try lia.
      reflexivity.
    }
    vjmp. vred.
    (* We update [loopvar] via the phi-node *)
    cbn; vred.

    focus_single_step_v.

    (* BEGIN TODO: infrastructure to deal with non-empty phis *)
    unfold denote_phis.
    cbn.
    rewrite denote_phi_hd.
    cbn.

    (* TOFIX: broken automation, a wild translate sneaked in where it shouldn't *)
    rewrite translate_bind.
    rewrite ?interp_cfg_to_L3_ret, ?bind_ret_l;
      rewrite ?interp_cfg_to_L3_bind, ?bind_bind.

    vstep. tred. repeat vred.
    unfold map_monad. cbn. vred. 
    rewrite interp_cfg_to_L3_LW. vred. vred. vred. vred.

    subst.
    vred.
    vred.
    inv VG.

    rewrite denote_bks_prefix; cycle 1; auto.
    {
      match goal with
        |- ?x::?y::?z ≡ _ => replace (x::y::z) with ([x;y]++z)%list by reflexivity
      end; f_equal.
    }
    hide_cfg.
    vred.

    rewrite tfor_unroll; [| lia].
    eapply eutt_clo_bind.

    + (* Base case : first iteration of loop. *)
      eapply IND.
      split.
      eapply STABLE; eauto.
      unfold Maps.add, Map_alist.
      apply alist_find_eq. typeclasses eauto.
    + intros ? (? & ? & ? & ?) (LU & -> & ?).
      eapply eutt_Proper_mono.
      2: apply GEN_IND.
      { clear - post; intros ? (? & ? & ? & ?) [-> ?]; split; eauto. }
      lia.
      lia.
      eauto. 
      eapply STABLE; eauto.
      split; eauto.
      Unshelve. eauto. 
Qed.

(* TODO: incLocalNamed should be opaque, and the stability hyp revisited *)

(** Inductive lemma to reason about while loops.
    The code generated is of the shape:
         block_entry ---> nextblock
             |
    ---->loopblock
    |        |
    |    body_entry
    |        |
    |      (body)
    |        |
     ----loopcontblock --> nextblock

 The toplevel lemma [genWhileLoop] will specify a full execution of the loop, starting from [block_entry].
 But to be inductive, this lemma talks only about the looping part:
 - we start from [loopcontblock]
 - we assume that [j] iterations have already been executed
 We therefore assume (I j) initially, and always end with (I n). 
 We proceed by induction on the number of iterations remaining, i.e. (n - j).

 Since in order to reach [loopcontblock], we need to have performed at least one iteration, we have the
 following numerical bounds:
 - j > 0
 - j <= n
 - Z.of_nat n < Int64.modulus (or the index would overflow)
 *)
Lemma genWhileLoop_ind:
  forall (prefix : string)
    (loopvar : raw_id)            (* lvar storing the loop index *)
    (loopcontblock : block_id)    (* reentry point from the body back to the loop *)
    (body_entry : block_id)       (* entry point of the body *)
    (body_blocks : list (LLVMAst.block typ)) (* (llvm) body to be iterated *)
    (nextblock : block_id)        (* exit point of the overall loop *)
    (entry_id : block_id)         (* entry point of the overall loop *)
    (s1 s2 : IRState)
    (bks : list (LLVMAst.block typ)) ,

    In body_entry (block_ids body_blocks) ->

    (* All labels generated are distinct *)
    blk_id_norepet bks ->

    fresh_in_cfg bks nextblock ->

    forall (n : nat)                     (* Number of iterations *)

      (* Generation of the LLVM code wrapping the loop around bodyV *)
      (HGEN: genWhileLoop prefix (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n))
                          loopvar loopcontblock body_entry body_blocks [] nextblock s1
                          ≡ inr (s2,(entry_id, bks))) 
      
      (* Computation on the Helix side performed at each cell of the vector, *)
      (*    the counterpart to bodyV (body_blocks) *)
      (bodyH: nat -> mem_block -> itree _ mem_block)
      (j : nat)                       (* Starting iteration *)
      (UPPER_BOUND : 0 < j <= n)
      (NO_OVERFLOW : (Z.of_nat n < Int64.modulus)%Z)

      (* Main relations preserved by iteration *)
      (I : nat -> mem_block -> Rel_cfg),

      (* We assume that we know how to relate the iterations of the bodies *)
      (forall g l mV mH ymem k _label _label',

          (conj_rel (I k ymem)
                    (fun _ '(_, (l, _)) => l @ loopvar ≡ Some (uvalue_of_nat k))
                    mH (mV,(l,g))) ->
          eutt
            (succ_cfg (fun '(memH,vec') '(memV, (l, (g, x))) =>
                         l @ loopvar ≡ Some (uvalue_of_nat k) /\
                         x ≡ inl (_label', loopcontblock) /\
                         I (S k) vec' memH (memV, (l, g))))
            (interp_helix (bodyH k ymem) mH)
            (interp_cfg
               (denote_bks (convert_typ [] body_blocks) (_label, body_entry)) g l mV)
      ) ->

      (* Invariant is stable under the administrative bookkeeping that the loop performs *)
      (forall a sa b sb c sc d sd e se msg msg' msg'',
          incBlockNamed msg s1 ≡ inr (sa, a) ->
          incBlockNamed msg' sa ≡ inr (sb, b) ->
          incLocal sb ≡ inr (sc,c) ->
          incLocal sc ≡ inr (sd,d) ->
          incLocalNamed msg'' sd ≡ inr (se, e) ->
          forall k ymem mH l mV g id v,
            id ≡ c \/ id ≡ d \/ id ≡ e \/ id ≡ loopvar ->
                            I k ymem mH (mV, (l, g)) ->
                            I k ymem mH (mV, ((alist_add id v l), g))) ->

    (* Main result. Need to know initially that P holds *)
    forall g l mV mH ymem _label,
      (conj_rel
         (I j ymem)
         (fun _ '(_, (l, _)) => l @ loopvar ≡ Some (uvalue_of_nat (j - 1)))
         mH (mV,(l,g))
      ) ->
      eutt (succ_cfg (fun '(memH,vec') '(memV, (l, (g,x))) =>
              x ≡ inl (loopcontblock, nextblock) /\
              I n vec' memH (memV,(l,g))
           ))
           (interp_helix (build_vec_gen j n bodyH ymem) mH)
           (interp_cfg (denote_bks (convert_typ [] bks)
                                                (_label, loopcontblock)) g l mV).
Proof.
  intros * IN UNIQUE_IDENTS NEXTBLOCK_ID * GEN LVAR_FRESH *.
  unfold genWhileLoop in GEN. cbn* in GEN. simp.
  intros BOUND OVER * HBODY STABLE.
  unfold build_vec_gen.
  
  remember (n - j) as k eqn:K_EQ.
  revert j K_EQ BOUND.
  induction k as [| k IH]; intros j EQidx.

  - (* Base case: we enter through [loopcontblock] and jump out immediately to [nextblock] *)
    intros  BOUND * (INV & LOOPVAR).
    (* Import ProofMode. *)
    (* This ugly preliminary is due to the conversion of types, as most ugly things on Earth are. *)
    apply no_repeat_convert_typ with (env := []) in UNIQUE_IDENTS; cbn in UNIQUE_IDENTS; rewrite ?convert_typ_block_app in UNIQUE_IDENTS.
    apply fresh_in_convert_typ with (env := []) in NEXTBLOCK_ID; cbn in NEXTBLOCK_ID; rewrite ?convert_typ_block_app in NEXTBLOCK_ID.
    cbn; rewrite ?convert_typ_block_app.
    hide_cfg.
    (* We jump into [loopcontblock]
       We denote the content of the block.
     *)
    vjmp.

    cbn.
    assert (n ≡ j) by lia; subst.
    (* replace (j - S j) with 0 by lia. *)

    vred.
    vred.
    vred.
    vstep. 
    {
      vstep.
      vstep; solve_lu; reflexivity.
      vstep; reflexivity.
      all: reflexivity.
    }
    vred.
    vstep.
    {
      cbn.
      vstep.
      vstep; solve_lu; reflexivity.
      vstep; reflexivity.
      all:reflexivity.
    }      

    (* We now branch to [nextblock] *)
    vbranch_r.
    { vstep.
      solve_lu.
      apply eutt_Ret; repeat f_equal.
      cbn.
      clear - BOUND OVER.
      destruct BOUND as [? _].
      rewrite __arithu; try lia.
      unfold eval_int_icmp.
      rewrite ltu_antisym.
      reflexivity.
    }

    vjmp_out.
    cbn.
    replace (j - j) with 0 by lia.
    cbn; hvred.

    (* We have only touched local variables that the invariant does not care about, we can reestablish it *)
    cbn.
    apply eutt_Ret.
    split.
    + reflexivity.
    + eapply STABLE; eauto.

  - (* Inductive case *)
    Opaque half_modulus.
    cbn in *. intros [LT LE] * (INV & LOOPVAR).
    (* This ugly preliminary is due to the conversion of types, as most ugly things on Earth are. *)
    apply no_repeat_convert_typ with (env := []) in UNIQUE_IDENTS; cbn in UNIQUE_IDENTS; rewrite ?convert_typ_block_app in UNIQUE_IDENTS.
    apply fresh_in_convert_typ with (env := []) in NEXTBLOCK_ID; cbn in NEXTBLOCK_ID; rewrite ?convert_typ_block_app in NEXTBLOCK_ID.
    cbn; rewrite ?convert_typ_block_app.
    cbn in IH; rewrite ?convert_typ_block_app in IH.
    hide_cfg.

    (* RHS : Reducing RHS to apply Body Hypothesis *)
    (* Step 1 : First, process [loopcontblock] and check that k<n, and hence that we do not exit *)
    vjmp.
    cbn.
    vred.
    vred.
    vred.
    vstep.
    {
      vstep.
      vstep; solve_lu.
      vstep; solve_lu.
      all: reflexivity.
    }
    vred.
    vstep.
    {
      cbn; vstep.
      vstep; solve_lu.
      vstep; solve_lu.
      all: reflexivity.
    }
    vred.

    (* Step 2 : Jump to b0, i.e. loopblock (since we have checked k < n). *)
    vbranch_l. 
    { cbn; vstep;  try solve_lu.
      rewrite __arithu; try lia.
      apply eutt_Ret.
      repeat f_equal.
      clear - EQidx LT LE OVER.
      unfold eval_int_icmp; rewrite ltu_nat_to_Int64; try lia.
      reflexivity.
    }

    vjmp.
    (* We update [loopvar] via the phi-node *)
    cbn; vred.

    focus_single_step_v.

    (* BEGIN TODO: infrastructure to deal with non-empty phis *)
    unfold denote_phis.
    cbn.
    rewrite denote_phi_tl; cycle 1.
    {
      inv VG. inversion UNIQUE_IDENTS.
      subst. intro. subst. apply H1. right.
      rewrite map_app.
      apply in_or_app. right. constructor. reflexivity.
    }

    rewrite denote_phi_hd.
    cbn.
    (* TOFIX: broken automation, a wild translate sneaked in where it shouldn't *)
    rewrite translate_bind.
    rewrite ?interp_cfg_to_L3_ret, ?bind_ret_l;
      rewrite ?interp_cfg_to_L3_bind, ?bind_bind.

    vstep.
    {
      setoid_rewrite lookup_alist_add_ineq.
      setoid_rewrite lookup_alist_add_eq. reflexivity. subst.
      intros ?; eapply __fresh; eauto.
    }
    (* TOFIX: broken automation, a wild translate sneaked in where it shouldn't *)
    rewrite translate_ret.
    repeat vred.
    cbn.
    repeat vred.
    (* TOFIX: we leak a [LocalWrite] event *)
    rewrite interp_cfg_to_L3_LW.
    repeat vred.
    subst.
    cbn.
    (* END TODO: infrastructure to deal with non-empty phis *)

    vred.
    (* Step 3 : we jump into the body *)
    vred.

    (* In order to use our body hypothesis, we need to restrict the ambient cfg to only the body *)
    inv VG.
    rewrite denote_bks_prefix; cycle 1; auto.
    {
      match goal with
        |- ?x::?y::?z ≡ _ => replace (x::y::z) with ([x;y]++z)%list by reflexivity
      end; f_equal.
    }
    hide_cfg.
    (* rewrite <- EQidx. *)

    cbn; hvred.
    destruct j as [| j]; [lia |].
    eapply eutt_clo_bind.
    (* We can now use the body hypothesis *)
    eapply HBODY.
    {
      (* A bit of arithmetic is needed to prove that we have the right precondition *)
      split.
      + repeat (eapply STABLE; eauto).

      + rewrite alist_find_eq.
        reflexivity.
        typeclasses eauto.
    }

    (* Step 4 : Back to starting from loopcontblock and have reestablished everything at the next index:
        conclude by IH *)
    introR.
    destruct PRE as (LOOPVAR' & HS & IH').
    subst.
    eapply IH; try lia.
    split; auto.
    Unshelve.
    all: try auto.
Qed.


Lemma genWhileLoop_correct:
  forall (prefix : string)
    (loopvar : raw_id)            (* lvar storing the loop index *)
    (loopcontblock : block_id)    (* reentry point from the body back to the loop *)
    (body_entry : block_id)       (* entry point of the body *)
    (body_blocks : list (LLVMAst.block typ)) (* (llvm) body to be iterated *)
    (nextblock : block_id)        (* exit point of the overall loop *)
    (entry_id : block_id)         (* entry point of the overall loop *)
    (s1 s2 : IRState) σ
    (bks : list (LLVMAst.block typ)) ,

    In body_entry (block_ids body_blocks) ->

    (* All labels generated are distinct *)
    blk_id_norepet bks ->

    fresh_in_cfg bks nextblock ->

    forall (n : nat)                     (* Number of iterations *)

      (* Generation of the LLVM code wrapping the loop around bodyV *)
      (HGEN: genWhileLoop prefix (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n))
                          loopvar loopcontblock body_entry body_blocks [] nextblock s1
                          ≡ inr (s2,(entry_id, bks))) 

      (* Computation on the Helix side performed at each cell of the vector, *)
      (*    the counterpart to bodyV (body_blocks) *)
      (bodyH: nat -> mem_block -> itree _ mem_block)
      (NO_OVERFLOW : (Z.of_nat n < Int64.modulus)%Z)

      (* Main relations preserved by iteration *)
      (I : nat -> mem_block -> Rel_cfg)
      (R : Rel_cfg),

      (* We assume that we know how to relate the iterations of the bodies *)
      (forall g l mV mH ymem k _label _label',

          (conj_rel (I k ymem)
                    (fun _ '(_, (l, _)) => l @ loopvar ≡ Some (uvalue_of_nat k))
                    mH (mV,(l,g))) ->
          eutt
            (succ_cfg (fun '(memH,vec') '(memV, (l, (g, x))) =>
                         l @ loopvar ≡ Some (uvalue_of_nat k) /\
                         x ≡ inl (_label', loopcontblock) /\
                         I (S k) vec' memH (memV, (l, g))))
            (interp_helix (bodyH k ymem) mH)
            (interp_cfg
               (denote_bks (convert_typ [] body_blocks) (_label, body_entry)) g l mV)
      ) ->

    (* Invariant is stable under the administrative bookkeeping that the loop performs *)
    (forall a sa b sb c sc d sd e se msg msg' msg'',
        incBlockNamed msg s1 ≡ inr (sa, a) ->
        incBlockNamed msg' sa ≡ inr (sb, b) ->
        incLocal sb ≡ inr (sc,c) ->
        incLocal sc ≡ inr (sd,d) ->
        incLocalNamed msg'' sd ≡ inr (se, e) ->
        forall k ymem mH l mV g id v,
          id ≡ c \/ id ≡ d \/ id ≡ e \/ id ≡ loopvar ->
                          I k ymem mH (mV, (l, g)) ->
                          I k ymem mH (mV, ((alist_add id v l), g))) ->

    (* R must be stable by extension of the local env *)
      (forall mH mV g l l',
          l ⊑ l' ->
                            R mH (mV, (l, g)) ->
                            R mH (mV, (l', g))) ->

    (* R must entail the state invariant *)
    imp_rel R (state_invariant σ s1) ->

    (forall g l mV mH ymem,
        (R mH (mV, (l, g)) -> I 0 mem_empty mH (mV, (l, g)) /\ l @ loopvar ≡ Some (uvalue_of_nat 0)) /\
        (I n ymem mH (mV, (l, g)) -> R mH (mV, (l, g)))) ->

    (* Main result. Need to know initially that R holds *)
    forall g l mV mH _label,
      R mH (mV,(l,g)) ->
      eutt (succ_cfg
            (fun '(memH,vec') '(memV, (l, (g,x))) =>
                            (* Consider generalizing? *)
                          (x ≡ inl (loopcontblock, nextblock) \/
                          x ≡ inl (entry_id, nextblock)) /\
                          R memH (memV,(l,g))))

           (interp_helix (build_vec n bodyH mem_empty) mH)
           (interp_cfg (denote_bks (convert_typ [] bks) (_label ,entry_id)) g l mV).
Proof with rauto.

  
  intros * IN UNIQUE EXIT * GEN * BOUND * IND STABLE STABLE' IMPSTATE IND_INV * PRE.
  pose proof @genWhileLoop_ind as GEN_IND.
  specialize (GEN_IND prefix loopvar loopcontblock body_entry body_blocks nextblock entry_id s1 s2 bks).
  specialize (GEN_IND IN UNIQUE EXIT n GEN).
  unfold genWhileLoop in GEN. cbn* in GEN. simp.
  unfold build_vec.
  destruct n.
  - (* 0th index *)
    cbn.

    apply fresh_in_convert_typ with (env := []) in EXIT; cbn in EXIT; rewrite ?convert_typ_block_app in EXIT.
    cbn; rewrite ?convert_typ_block_app.
    cbn in GEN_IND; rewrite ?convert_typ_block_app in GEN_IND.

    hide_cfg.
    vjmp.

    vred. vred. vred. vstep.
    {
      cbn.
      vstep.
      vstep; solve_lu; reflexivity.
      vstep; reflexivity.
      all:reflexivity.
    }

    (* We now branch to [nextblock] *)
    vbranch_r.
    { vstep.
      solve_lu.
      apply eutt_Ret; repeat f_equal.
    }

    vjmp_out.
    hvred.
    cbn.
    hvred.

    (* We have only touched local variables that the invariant does not care about, we can reestablish it *)
    apply eutt_Ret. cbn. split. right. reflexivity.
    eapply STABLE'. apply sub_alist_add. eapply state_invariant_alist_fresh.
    eapply state_invariant_incBlockNamed. apply Heqs0.
    eapply state_invariant_incBlockNamed. apply Heqs.
    apply IMPSTATE. apply PRE. eauto. eauto.

  - Opaque build_vec_gen.
    cbn.
    cbn in *.

    (* Clean up convert_typ junk *)
    apply fresh_in_convert_typ with (env := []) in EXIT; cbn in EXIT; rewrite ?convert_typ_block_app in EXIT.
    apply no_repeat_convert_typ with (env := []) in UNIQUE; cbn in UNIQUE; rewrite ?convert_typ_block_app in UNIQUE.

    cbn; rewrite ?convert_typ_block_app.
    cbn in GEN_IND; rewrite ?convert_typ_block_app in GEN_IND.

    hide_cfg.

    Transparent build_vec_gen.
    cbn.

    hvred.

    vjmp.
    cbn.
    vred. vred. vred.
    vstep.
    {
      vstep. vstep; solve_lu.
      vstep; solve_lu.
      all :reflexivity.
    }
    vred.
    vstep. cbn.
    hvred.

    (* Step 1 : Jump to b0, i.e. loopblock (since we have checked k < n). *)
    vbranch_l.
    {
      cbn; vstep.
      match goal with
        |- Maps.lookup ?k (alist_add ?k ?a ?b) ≡ _ =>
        rewrite (lookup_alist_add_eq _ _ b)
      end; reflexivity.
      unfold eval_int_icmp. cbn.
      rewrite ltu_Z_to_Int64; try lia.
      reflexivity.
    }
    vjmp. vred.
    (* We update [loopvar] via the phi-node *)
    cbn; vred.

    focus_single_step_v.

    (* BEGIN TODO: infrastructure to deal with non-empty phis *)
    unfold denote_phis.
    cbn.
    rewrite denote_phi_hd.
    cbn.

    (* TOFIX: broken automation, a wild translate sneaked in where it shouldn't *)
    rewrite translate_bind.
    rewrite ?interp_cfg_to_L3_ret, ?bind_ret_l;
      rewrite ?interp_cfg_to_L3_bind, ?bind_bind.

    vstep. tred. repeat vred.
    unfold map_monad. cbn. vred. 
    rewrite interp_cfg_to_L3_LW. vred. vred. vred. vred.

    subst. vred.

    vred.

    inv VG.

    match goal with
    | [ |- context[?hd :: ?hd' :: _ ++ ?tl] ] => remember hd; remember hd'; remember tl
    end.
    assert (AUX:
              (b :: b1 :: (convert_typ nil body_blocks) ++ l0 ≡ [b; b1] ++ (convert_typ nil body_blocks) ++ l0)%list).
    reflexivity.
    rewrite AUX.

    rewrite (denote_bks_prefix).
    2 : reflexivity.
    2 : {
      (* Seems like a case we can add to solve_lu. *)
      clear -UNIQUE IN.
      pose proof no_repeat_app_l.
      cbn. apply UNIQUE.
    }

    hide_cfg. rewrite AUX in *. clear AUX.

    vred.
    eapply eutt_clo_bind.

    (* Base case : first iteration of loop. *)
    eapply IND. edestruct IND_INV. split. destruct H. eauto.
    2 : eauto.
    eapply STABLE; eauto.
    unfold Maps.add, Map_alist.
    apply alist_find_eq. typeclasses eauto.

    intros. destruct u1. destruct u2 as (? & ?& ? &?).
    destruct p, s. 3 : inversion H. cbn in H. destruct p. destruct H as (LOOPVAR & ID & INV).
    inversion ID; subst.

    unfold build_vec_gen in GEN_IND.
    assert (forall j, S n - S j ≡ n - j) by lia.
    assert (n ≡ n - 0) by lia. rewrite H0. rewrite <- H.
    eapply eutt_Proper_mono.
    2 : {
      eapply GEN_IND.
      - lia.
      - lia.
      - intros. eapply IND. apply H1.
      - eapply STABLE; eauto.
      - split; eauto.
    }

    repeat intro.
    repeat red. repeat red in H1. destruct x; try contradiction.
    destruct p. destruct y as (? & ? & ? & ?). destruct H1. split.
    left; auto. edestruct IND_INV. apply H4. apply H2.

    destruct H as (? & ? & ?). inversion H0.
    Unshelve. eauto. exact mem_empty. eauto.
Qed.
