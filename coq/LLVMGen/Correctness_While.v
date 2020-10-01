Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.

Set Implicit Arguments.
Set Strict Implicit.

Import MDSHCOLOnFloat64.
Import D.

Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

(* TODO: Move to Prelude *)
Definition uvalue_of_nat k := UVALUE_I64 (Int64.repr (Z.of_nat k)).

Fixpoint build_vec_gen_aux {E} (from remains : nat) (body : nat -> mem_block -> itree E mem_block) : mem_block -> itree E mem_block :=
  fun vec =>
    match remains with
    | 0 => ret vec
    | S remains' =>
      vec' <- body from vec;;
      build_vec_gen_aux (S from) remains' body vec'
    end.

Definition build_vec_gen {E} (from to : nat) :=
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

Lemma convert_typ_block_app : forall (a b : list (LLVMAst.block typ)) env, (convert_typ env (a ++ b) ≡ convert_typ env a ++ convert_typ env b)%list.
Proof.
  induction a as [| [] a IH]; cbn; intros; auto.
  rewrite IH; reflexivity.
Qed.

Notation "x < y" := (DynamicValues.Int64.lt x y).
Notation "x + y" := (DynamicValues.Int64.add x y).
Notation "'u_zero'" := (UVALUE_I1 DynamicValues.Int1.zero).
Notation "'u_one" := (UVALUE_I1 DynamicValues.Int1.one).
Notation "'d_zero'" := (DVALUE_I1 DynamicValues.Int1.zero).
Notation "'d_one'" := (DVALUE_I1 DynamicValues.Int1.one).
Notation "'(int64)' x" := (Int64.repr x) (at level 10).
Notation "'(Z)' x" := (Z.of_nat x) (at level 10).

(* TODO: Move to Vellvm Denotation_Theory.v? *)

Definition block_ids {T : Set} (b : list ((LLVMAst.block T))) :=
  fold_left (fun (acc : list block_id) (bk : LLVMAst.block T) => (acc ++ [blk_id bk])%list) b [].

(* IY: Why isn't it the below, instead? It looks like outputs etc. also have use
   fold_left instead of map (in Vellvm - Denotation_Theory.v), which feels super
   awkward. Following Vellvm conventions for now. *)
Definition block_ids' {T : Set} (b : list ((LLVMAst.block T))) :=
  map (@blk_id T).

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

(* IY: The more general statement should be In being injective over List.map,
   but it's stated like this here because we're using fold_left *)
Lemma In_inj_block_ids :
  forall T x (b : list (LLVMAst.block T)), In x b -> In (blk_id x) (block_ids b).
Proof.
  intros. revert H. revert x. induction b.
  - intros. inversion H.
  - intros. unfold block_ids. cbn.
    rewrite fold_left_acc_app. rewrite <-list_cons_app.
    cbn in H. destruct H. cbn. left. rewrite H. reflexivity.
    cbn. right. apply IHb. auto.
Qed.

Definition imp_rel {A B : Type} (R S: A -> B -> Prop): Prop :=
  forall a b, R a b -> S a b.


Definition stable_exp_local (R: Rel_cfg) : Prop :=
    forall memH memV ρ1 ρ2 g,
      R memH (memV, (ρ1, g)) ->
      ρ1 ⊑ ρ2 ->
      R memH (memV, (ρ2, g)).

Lemma disjoint_bid_neq {T : Set} (b b' : list (LLVMAst.block T)) :
  disjoint_bid_blocks b b' ->
  forall x x', In x b -> In x' b' -> blk_id x ≢ blk_id x'.
Proof.
  intros.
  do 2 red in H.
  specialize (H (blk_id x) (blk_id x')).
  apply H; apply In_inj_block_ids; auto.
Qed.

Lemma find_block_ineq :
  ∀ (T : Set) (x : block_id) (b bs : list (LLVMAst.block T)) e,
    disjoint_bid_blocks b bs ->
    find_block T bs x ≡ Some e -> find_block T (b ++ bs) x ≡ Some e.
Proof.
  intros.
  induction b.
  - intros. rewrite app_nil_l. apply H0.
  - intros.
    rewrite list_cons_app.
    rewrite <- app_assoc.
    rewrite <- list_cons_app.
    cbn.
    assert (blk_id a ≢ x).
    assert (H' := H0).
    apply find_some in H0. destruct H0.
    assert (In a (a :: b)). { red. left. reflexivity. }
    destruct (Eqv.eqv_dec_p (blk_id e) x). 2 : inversion H1.
    rewrite <- e0.
    eapply disjoint_bid_neq; eauto.
    assert (not (Eqv.eqv (blk_id a) x)). red. intros. apply H1. rewrite H2. reflexivity.
    unfold Eqv.eqv_dec_p. eapply rel_dec_neq_false in H2. 2 : typeclasses eauto.
    setoid_rewrite H2. apply IHb.
    red. red in H.
    eapply Coqlib.list_disjoint_cons_left.
    rewrite list_cons_app in H.
    clear H0 IHb H1 H2. induction b. cbn. rewrite app_nil_r in H.
    apply H. red. intros. red in H. apply H. 2 : auto.
    eapply Permutation.Permutation_in. 2: apply H0.
    clear H IHb H0 H1.
    remember (a0 :: b). clear Heql.
    induction l. cbn. auto.
    cbn. cbn in IHl. eapply Permutation.perm_trans.
    rewrite list_cons_app.
    rewrite Permutation.Permutation_app_swap. apply Permutation.Permutation_refl.
    pose proof @fold_left_acc_app .
    specialize (H _ _ l (fun x => [blk_id x])). cbn in H.
    assert (
    (fold_left (λ (acc : list block_id) (bk : LLVMAst.block T), (acc ++ [blk_id bk])%list) l [blk_id a1] ++
               [blk_id a]) ≡
     ([blk_id a1] ++ fold_left (λ (acc : list block_id) (bk : LLVMAst.block T), acc ++ [blk_id bk]) l [ ]) ++
     [blk_id a])%list. rewrite H. reflexivity. rewrite H0.
    assert (
    (fold_left (λ (acc : list block_id) (bk : LLVMAst.block T), (acc ++ [blk_id bk])%list) l
       [blk_id a; blk_id a1]) ≡
     ([blk_id a; blk_id a1] ++ fold_left (λ (acc : list block_id) (bk : LLVMAst.block T), acc ++ [blk_id bk]) l [ ])%list).
    rewrite H; reflexivity.
    rewrite H1. clear H0 H1. eapply Permutation.perm_trans.
    apply Permutation.Permutation_app_swap. cbn.
    apply Permutation.Permutation_refl.
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

(* Auxiliary integer computation lemmas *)
Lemma bounds_check_aux :
  forall (j n :nat),
    ((int64) ((Z) j) + (int64) 1 < (int64) ((Z) n)) ≡ true ->
                    (j + 1 < n)%nat.
Proof.
  Admitted.

Lemma eval_int_icmp_aux :
  forall (n k : nat),
    dvalue_to_uvalue (eval_int_icmp Slt ((int64) ((Z) (n - S k)) + (int64) 1) ((int64) ((Z) n)))
                     ≡ (UVALUE_I1 DynamicValues.Int1.one).
Proof.
Admitted.

Lemma find_block_label_in_blocks :
  forall label bks, In label (block_ids bks) ->
  exists x, find_block dtyp (convert_typ [ ] bks) label ≡ Some x.
Proof.
Admitted.

Lemma body_blocks_from_entry_eq:
  forall (prefix : string)
    (loopvar : raw_id)            (* lvar storing the loop index *)
    (loopcontblock : block_id)    (* reentry point from the body back to the loop *)
    (body_entry : block_id)       (* entry point of the body *)
    (body_blocks : list (LLVMAst.block typ)) (* (llvm) body to be iterated *)
    (nextblock : block_id)        (* exit point of the overall loop *)
    (entry_id : block_id)         (* entry point of the overall loop *)
    (s1 s2 : IRState)
    (n : nat)
    (bks : list (LLVMAst.block typ)),

    In body_entry (block_ids body_blocks) ->

    (* Generation of the LLVM code wrapping the loop around bodyV *)
    genWhileLoop prefix (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n))
                       loopvar loopcontblock body_entry body_blocks [] nextblock s1
                       ≡ inr (s2,(entry_id, bks)) ->

    (* TODO: Add hypothesis about freshness/separation btw body_blocks and bks. *)

    forall g l mV _label,
      eutt Logic.eq
      (with_err_LB (interp_cfg (denote_bks (convert_typ [ ] body_blocks) (_label, body_entry)) g l mV))
      (with_err_LB (interp_cfg (denote_bks (convert_typ [ ] bks) (_label, body_entry)) g l mV)).
Proof.
  intros. unfold genWhileLoop in H0. cbn* in H0. simp.
  rewrite list_cons_app.
  rewrite convert_typ_block_app.
  apply find_block_label_in_blocks in H. destruct H.
  rewrite denote_bks_flow_right. 2 : admit. (* TODO: Freshness. *)

  rewrite denote_bks_unfold_in.
  2 : apply H.
  cbn...
Admitted.

(* TODO: Freshness is stated in a somewhat ad-hoc way in here. Needs clean-up. *)
Lemma genWhileLoop_ind:
  forall (prefix : string)
    (loopvar : raw_id)            (* lvar storing the loop index *)
    (loopcontblock : block_id)    (* reentry point from the body back to the loop *)
    (body_entry : block_id)       (* entry point of the body *)
    (body_blocks : list (LLVMAst.block typ)) (* (llvm) body to be iterated *)
    (nextblock : block_id)        (* exit point of the overall loop *)
    (entry_id : block_id)         (* entry point of the overall loop *)
    (s1 s2 : IRState)
    (bks : list (LLVMAst.block typ))
    (n : nat)                       (* Number of iterations *)
    (j : nat)                       (* Starting iteration *)
    (BOUND : (n >= j))
    (* Main relations preserved by iteration *)
    (I : nat -> mem_block -> Rel_cfg),

    In body_entry (block_ids body_blocks) ->

    (* Uniqueness of identifiers *)
    find_block dtyp (convert_typ [ ] body_blocks) loopcontblock ≡ None ->
    find_block dtyp (convert_typ [ ] body_blocks) nextblock ≡ None ->
    entry_id ≢ loopcontblock ->
    entry_id ≢ nextblock ->
    loopcontblock ≢ nextblock ->
    (forall loop_id i i0,
        incBlockNamed (prefix @@ "_entry") s1 ≡ inr (i, entry_id) ->
        incBlockNamed (prefix @@ "_loop") i ≡ inr (i0, loop_id) ->
        loop_id ≢ loopcontblock /\ loop_id ≢ nextblock) ->

    (* Generation of the LLVM code wrapping the loop around bodyV *)
    genWhileLoop prefix (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n))
                       loopvar loopcontblock body_entry body_blocks [] nextblock s1
                       ≡ inr (s2,(entry_id, bks)) ->
    (* Computation on the Helix side performed at each cell of the vector, *)
    (*    the counterpart to bodyV (body_blocks) *)
    forall (bodyH: nat -> mem_block -> itree _ mem_block),

    (* Inductive Case *)
    (* We build weakening in the rule: the precondition implies the initial invariant
       and the final invariant implies the postcondition
     *)
    (forall g l mV mH ymem k _label,

        (conj_rel (I k ymem)
                  (fun _ '(_, (l, _)) => l @ loopvar ≡ Some (uvalue_of_nat k))
                  mH (mV,(l,g))) ->
        eutt
          (
             (fun '(memH,vec') '(memV, (l, (g, x))) =>
                l @ loopvar ≡ Some (uvalue_of_nat k) /\
                I (S k) vec' memH (memV, (l, g))
    ))
          (with_err_RB (interp_Mem (bodyH k ymem) mH))
          (with_err_LB (interp_cfg
                          (denote_bks (convert_typ [] body_blocks) (_label, body_entry)) g l mV))
    ) ->

    (* Invariant is stable under extending local state *)
    (forall k mH mV l l' g ymem, I k ymem mH (mV, (l, g)) -> l ⊑ l' -> I k ymem mH (mV, (l', g))) ->


    (* Main result. Need to know initially that P holds *)
    forall g l mV mH ymem _label,


  (forall i i0 i1 i2 r r0 b0,
      incBlockNamed (prefix @@ "_entry") s1 ≡ inr (i, entry_id) ->
      incBlockNamed (prefix @@ "_loop") i ≡ inr (i0, b0) ->
      incLocal i0 ≡ inr (i1, r) ->
      incLocal i1 ≡ inr (i2, r0) ->

      (alist_fresh r0
        (alist_add (Name ((prefix @@ "_next_i") @@ string_of_nat (local_count i2)))
          (UVALUE_I64 ((int64) ((Z) j) + (int64) 1)) l) /\
            alist_fresh (Name ((prefix @@ "_next_i") @@ string_of_nat (local_count i2))) l)) ->

      (conj_rel
         (I j ymem)
         (fun _ '(_, (l, _)) => l @ loopvar ≡ Some (uvalue_of_nat j))
         mH (mV,(l,g))
      ) ->
      eutt (fun '(memH,vec') '(memV, (l, (g,x))) =>
              (* l @ loopvar ≡ Some (uvalue_of_nat n) /\ *)
              x ≡ inl (loopcontblock, nextblock) /\
              I n vec' memH (memV,(l,g))
           )
           (with_err_RB (interp_Mem (build_vec_gen (S j) n bodyH ymem) mH))
           (with_err_LB (interp_cfg (denote_bks (convert_typ [] bks)
                                                (_label, loopcontblock)) g l mV)).

Proof with rauto.
  intros * BOUND * IN F0 F1 F2 F3 F4 F5 GEN.
  unfold genWhileLoop in GEN. cbn* in GEN. simp.
  intros * HBODY STABLE.
  remember (n - j) as k.
  assert (JEQ: j ≡ n - k) by lia.
  rewrite JEQ. clear BOUND Heqk JEQ j.

  generalize dependent k.
  generalize dependent n.
  induction k as [| k IH]; intros * FRESH PRE.
  - admit.
  (* - cbn... *)
  (*   (* LHS Helix simplification *) *)
  (*   unfold build_vec_gen, build_vec_gen_aux. *)
  (*   assert (n - S j ≡ 0) by lia. *)
  (*   rewrite H. cbn. *)
  (*   cbn... *)

  (*   (* RHS Vellvm simplification *) *)
  (*   rewrite denote_bks_unfold_in. *)
  (*   2 : { *)
  (*     rewrite find_block_ineq. rewrite find_block_ineq. *)
  (*     rewrite convert_typ_block_app. rewrite find_block_none_app. *)
  (*     Opaque find_block. *)
  (*     cbn. unfold fmap, Fmap_block. cbn. rewrite find_block_eq. *)
  (*     reflexivity. cbn. reflexivity. *)
  (*     auto. *)
  (*     cbn. eapply F5; eauto. *)
  (*     cbn. auto. *)
  (*   } *)
  (*   cbn... *)
  (*   cbn... *)
  (*   focus_single_step_v. *)
  (*   Transparent denote_code. *)
  (*   cbn... *)
  (*   focus_single_step_v. *)

  (*   setoid_rewrite denote_instr_op. *)
  (*   2 : { *)
  (*     cbn... *)
  (*     2 : { *)
  (*       destruct PRE; eauto. *)
  (*     } *)
  (*     cbn... *)
  (*     unfold uvalue_to_dvalue_binop. *)
  (*     cbn... *)
  (*     reflexivity. *)
  (*   } *)
  (*   cbn... subst. cbn... *)
  (*   rewrite denote_instr_op. *)
  (*   2 : { *)
  (*     cbn. *)
  (*     cbn... *)
  (*     2 : { *)
  (*       setoid_rewrite lookup_alist_add_eq. reflexivity. *)
  (*     } *)
  (*     cbn... *)
  (*     Arguments uvalue_to_dvalue_binop /. *)
  (*     cbn... *)
  (*     reflexivity. *)
  (*   } *)
  (*   cbn... *)
  (*   rewrite denote_term_br_r. *)
  (*   2 : { *)
  (*     (* TODO: notation for map updates *) *)
  (*     cbn... *)
  (*     2 : { *)
  (*       setoid_rewrite lookup_alist_add_eq. reflexivity. *)
  (*     } *)
  (*     match goal with *)
  (*     | [ |- ret (_, (_, (_, ?x))) ≈ Ret (_, (_, (_, ?x'))) ] => assert (x ≡ x') *)
  (*         end. *)
  (*     unfold eval_int_icmp. cbn. *)
  (*     assert ((int64) ((Z) j) + (int64) 1 < (int64) ((Z) n) ≡ false). { *)
  (*       symmetry in EQ. rewrite Nat.sub_0_le in EQ. *)
  (*       assert (j + 1 > n) by lia. *)
  (*       apply gt_asym in H0. *)
  (*       apply Bool.not_true_is_false. red. intros. apply H0. *)
  (*       assert ((j + 1 < n -> n > j + 1)%nat). intros; lia. *)
  (*       apply H2. clear H2. *)
  (*       apply bounds_check_aux. auto. *)
  (*     } *)
  (*     rewrite H0. cbn. reflexivity. *)
  (*     cbn. rewrite H0. reflexivity. *)
  (*   } *)
  (*   cbn... subst. rewrite denote_bks_unfold_not_in. *)
  (*   2 : { *)
  (*     rewrite find_block_ineq. rewrite find_block_ineq. *)
  (*     rewrite convert_typ_block_app. rewrite find_block_none_app. *)
  (*     Opaque find_block. *)
  (*     cbn. unfold fmap, Fmap_block. cbn. rewrite find_block_ineq. *)
  (*     apply find_block_nil. cbn. auto. auto. cbn. eapply F5; eauto. cbn. auto. *)
  (*   } *)
  (*   cbn... apply eutt_Ret. *)
  (*   split. *)
  (*   + reflexivity. *)
  (*   + *)
  (*     eapply HBODY. destruct PRE. *)
  (*     2 : { *)
  (*       Unshelve. *)
  (*       eapply sub_alist_add. cbn. *)
  (*       eapply FRESH; eauto. *)
  (*     } eapply HBODY. *)
  (*     2 : { *)
  (*       Unshelve. 2 : exact l. *)
  (*       eapply sub_alist_add.  eapply FRESH; eauto. *)
  (*     } *)
  (*     assert (n <= j). lia. *)
  (*     assert (n ≡ j). lia. *)
  (*     rewrite H1. auto. *)

  -
    match goal with
    | [ |- context[convert_typ _ ?l] ] => remember l as L
    end.

    (* RHS : Reducing RHS to apply Body Hypothesis *)
    (* First step : First, Check that k<n hence we do not exit, in order to jump back to bodyblock. *)
    setoid_rewrite list_cons_app in HeqL.
    subst.
    rewrite convert_typ_block_app.
    (* We ignore entry_id *)
    rewrite denote_bks_flow_right.

    match goal with
    | [ |- context[convert_typ _ ?l] ] => remember l as L
    end. setoid_rewrite list_cons_app in HeqL.
    subst. rewrite convert_typ_block_app.
    rewrite denote_bks_unfold_in. cbn.
    cbn...
    2 : {
      rewrite convert_typ_block_app.
      rewrite app_assoc.
      eapply find_block_ineq. admit.
      cbn.
      assert (loopcontblock ≡ loopcontblock) by reflexivity.
      eapply rel_dec_eq_true in H. 2 : typeclasses eauto. setoid_rewrite H.
      reflexivity.
    }

    (* Updating (loopvar <- S k) coming from loopcontblock. *)
    focus_single_step_v.
    unfold fmap, Fmap_block. cbn. cbn... 
    rewrite Heqi7. cbn...
    focus_single_step_v.
    Transparent denote_code.
    unfold denote_code. cbn. Opaque denote_code.
    cbn... focus_single_step_v.
    Transparent denote_instr. unfold denote_instr. cbn...
    Opaque denote_instr.
    2 : { destruct PRE as (INV & LOOPVAR). apply LOOPVAR. }
    cbn. cbn...
    unfold uvalue_to_dvalue_binop. cbn. cbn...
    rewrite interp_cfg_to_L3_LW. cbn...

    (* Simplifying until we get to the branching conditional statement. *)
    rewrite Heqi10. cbn...
    Transparent denote_instr. unfold denote_instr. cbn...
    Opaque denote_instr. cbn...
    unfold uvalue_to_dvalue_binop. cbn.
    2 : {
      setoid_rewrite lookup_alist_add_eq. reflexivity.
    }
    cbn. cbn...
    rewrite interp_cfg_to_L3_LW. cbn. cbn...
    clear Heqi10. rewrite Heqi9.
    Transparent denote_terminator. cbn.
    rewrite translate_trigger. rewrite lookup_E_to_exp_E_Local.
    rewrite subevent_subevent. rewrite translate_bind.
    rewrite bind_bind. rewrite translate_trigger.
    cbn... cbn.
    2 : {
      setoid_rewrite lookup_alist_add_eq. reflexivity.
    }

    (* We find that k < n, thus we go back to looping on the body *)
    cbn...
    rewrite eval_int_icmp_aux.
    Typeclasses eauto := 4.
    cbn...
    focus_single_step_v.
    Typeclasses eauto :=.
    setoid_rewrite translate_ret.
    setoid_rewrite interp_cfg_to_L3_ret.
    rewrite translate_ret. rewrite bind_ret_l.

    rewrite Heqi11. cbn.
    2 : admit. 2 : admit. (* TODO: Freshness *)
    cbn... clear Heqi11.

    (* Step 2 : Jump back to body_entry (since we have checked k < n). *)
    unfold fmap, Fmap_block. cbn. rewrite convert_typ_block_app.
    rewrite list_cons_app. rewrite denote_bks_unfold_in.
    2 : { rewrite <- list_cons_app. setoid_rewrite find_block_eq. reflexivity. cbn. reflexivity.  }
    cbn... rewrite denote_phi_tl. 2 : admit. (* TODO: Freshness *)
    focus_single_step_v.
    Transparent denote_phi. unfold denote_phi. rewrite assoc_hd. cbn.
    cbn... cbn. rewrite translate_ret. rewrite bind_ret_l.
    Opaque denote_phi.
    2 : {
      setoid_rewrite lookup_alist_add_ineq. 2 : { admit. } (* TODO: Freshness *)
      setoid_rewrite lookup_alist_add_eq. reflexivity.
    }
    cbn... rewrite Heqi12. cbn...
    (* Got the phi node from loop cont block, now! Time to jump to body_entry. *)
    (* Before that, we need to clean up some fluff. *)
    cbn... focus_single_step_v.
    rewrite interp_cfg_to_L3_LW. cbn.
    rewrite translate_ret. rewrite bind_ret_l. rewrite Heqi13.

    focus_single_step_v. cbn...
    rewrite Heqi14. clear Heqi13 Heqi14. clear i13 i14.
    cbn...
    cbn. rewrite interp_cfg_to_L3_ret. setoid_rewrite translate_ret.
    rewrite bind_ret_l. rewrite interp_cfg_to_L3_bind.
    setoid_rewrite translate_ret. setoid_rewrite interp_cfg_to_L3_ret.
    rewrite bind_ret_l.

    (* Starting to see body entry in the horizon. We need to apply the body hypothesis
       to retrieve the fact that "bks" entering from "body_entry" is the same denotation
       as "body_bks" entering from "body_entry". *)
    match goal with
    | [ |- context[denote_bks ?l]] => remember l as bks
    end.
    clear i11 i12 Heqi12 i10 i9 Heqi9. clear i7 Heqi7.

    (* Step 3 : Starting to think about applying body hypothesis *)
    (* Step 3.1 : Make right had side of equation agree with right hand side of HBODY *)
    match goal with
    | [ |- context[interp_cfg _ _ ?l _]] => remember l as LOCAL
    end.
    match goal with
    | [ |- eutt ?R _ _ ] => remember R as REL
    end.

    pose proof @rcompose_eq_r. specialize (H _ _ REL).
    rewrite H.

    (* If we enter from body_entry, having either body_blocks or bks should be the same *)
    eapply eqit_trans.
    2 : {
      Unshelve.
      2 : exact (with_err_LB (interp_cfg
                                (denote_bks (convert_typ [ ] body_blocks)
                                            (b0, body_entry)) g LOCAL mV)).
      pose proof @body_blocks_from_entry_eq.

      rewrite H0.
      2 : {
        Unshelve.
        2 : exact prefix. 8 :exact n. 2 : exact loopvar. 2 : exact loopcontblock.
        2 : exact nextblock. 2 : exact entry_id. 2 : exact s1. 2 : exact s2.
        cbn. apply IN. auto.
      }
      (* rewrite Heqs. rewrite Heqs0. rewrite Heqs1. rewrite Heqs2. rewrite Heqs3. rewrite Heqs4. *)
      (*   rewrite Heqs5. reflexivity. *)
      (* } *)
      subst.
      rewrite list_cons_app.
      cbn. unfold fmap, Fmap_block. cbn.

      rewrite list_cons_app.

      (* Ignore entry_id *)
      rewrite denote_bks_flow_right. 2 : admit. 2 : admit. (* TODO: Freshness *)
      cbn... cbn.
      unfold fmap, Fmap_block. cbn.
      cbn...
      admit.
      (* reflexivity. *)
      admit. (* *)
    }

    (* Now the RHS is the same as the body hypothesis, we should now reduce the LHS respectively. *)
    unfold build_vec_gen, build_vec_gen_aux. cbn.
    assert (n - S (n - S k) ≡ k).
    assert (n - S (n - S k) ≡ n - (1 + (n - 1 - k))) by lia.

    (* Step 3 (Actually applying BH): By body hypothesis, this will lead to my invariant being true at
       step S k, and to jumping to loopcontblock. *)

    (* Step 4 : Back to starting from loopcontblock and have reestablished everything at the next index:
       conclude by IH *)

Admitted.



Lemma genWhileLoop_correct:
  forall (msg : string)
    (lvar : raw_id)            (* lvar storing the loop index *)
    (body_entry_id : block_id) (* entry point of the body *)
    (wrap_loop_id : block_id)  (* reentry point from the body back to the loop *)
    (bodyV : list (LLVMAst.block typ)) (* (llvm) body to be iterated *)
    (exit_id : block_id)       (* exit point of the overall loop *)
    (entry_id : block_id)      (* entry point of the overall loop *)
    σ (s1 s2 : IRState)
    (bks : list (LLVMAst.block typ)) (* (llvm) code defining the whole loop *)
    (from_id: block_id)        (* point from which we enter the overall loop *)
    (n : nat)                    (* Number of iterations *)

    (* Generation of the LLVM code wrapping the loop around bodyV *)
    (GEN: genWhileLoop msg (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n))
                       lvar wrap_loop_id body_entry_id bodyV [] exit_id s1
                       ≡ inr (s2,(entry_id,bks)))

    (* Computation on the Helix side performed at each cell of the vector,
       the counterpart to bodyV *)
    (bodyH: nat -> mem_block -> itree _ mem_block) 

    (* Main relation preserved by iteration *)
    (R : Rel_cfg),

    (* Inductive proof: Assuming R, reestablish R by going through both bodies *)
    (forall g l mV mH ymem,
        (* ((R ⩕ Invk n) (mH,ymem) (mV, (l, (g, (inl body))))) -> *)
        (R mH (mV,(l,g))) ->
        eutt
          (lift_Rel_cfg R)
          (* (R ⩕ Invk (n +1) /\ lvar = n /\ retlabel = post ) *)
          (with_err_RB (interp_Mem (bodyH n ymem) mH))
          (with_err_LB (interp_cfg
                          (denote_bks (convert_typ [] bodyV) (from_id,body_entry_id)) g l mV))
    ) ->

    (* R must be stable by extension of the local env *)
    stable_exp_local R ->

    (* R must entail the state invariant *)
    imp_rel R (state_invariant σ s1) ->

    (* Main result. Need to know initially that R holds *)
    forall g l mV mH ymem,
      R mH (mV,(l,g)) ->
      eutt (lift_Rel_cfg R)
           (with_err_RB (interp_Mem (build_vec n bodyH ymem) mH))
           (with_err_LB (interp_cfg (denote_bks (convert_typ [] bks) (from_id,entry_id)) g l mV)).
Proof with rauto.
  intros * GEN * IND STABLE IMPSTATE * PRE.
  cbn* in GEN; simp. 
  destruct n as [|[|n]].
  - (* n = 0: we never enter the loop *)

    cbn...

    jump_in.

  (*   cbn... *)
  (*   cbn... *)

  (*   rewrite denote_instr_op. *)
  (*   2:{ *)
  (*     cbn... *)
  (*     cbn... *)
  (*     reflexivity. *)
  (*   } *)

  (*   cbn... *)
  (*   focus_single_step_v. *)
  (*   rewrite denote_term_br_r. *)
  (*   2:{ *)
  (*     cbn... *)
  (*     cbn... *)
  (*     reflexivity. *)
  (*     unfold local_env; rewrite lookup_alist_add_eq; reflexivity. *)
  (*   } *)

  (*   cbn... *)
  (*   subst. *)

  (*   rewrite denote_bks_unfold_not_in. *)
  (*   2: admit. *)

  (*   cbn... *)
  (*   apply eutt_Ret. *)

  (*   cbn; eapply STABLE; eauto. *)
  (*   eapply sub_alist_add. *)
  (*   eapply concrete_fresh_fresh; eauto. *)
  (*   eapply incLocal_is_fresh. *)
  (*   eapply state_invariant_incBlockNamed; eauto. *)
  (*   eapply state_invariant_incBlockNamed; eauto. *)

  (* - (* n > 0 *) *)
  (*   cbn. *)
  (*   eutt_hide_left. *)

  (*   jump_in. *)

  (*   cbn... *)
  (*   cbn... *)

  (*   focus_single_step_v. *)
  (*   rewrite denote_instr_op. *)
  (*   2:{ *)
  (*     cbn... *)
  (*     cbn... *)
  (*     reflexivity. *)
  (*   } *)

  (*   cbn... *)
  (*   subst. *)
  (*   cbn... focus_single_step_v. *)
  (*   rewrite denote_term_br_l. *)
  (*   2:{ *)
  (*     cbn... *)
  (*     cbn... *)
  (*     reflexivity. *)
  (*     unfold local_env; rewrite lookup_alist_add_eq; reflexivity. *)
  (*   } *)

  (*   cbn... *)
  (*   subst; cbn... *)

  (*   jump_in. *)
  (*   2:admit. *)

  (*   cbn... *)

  (*   find_phi. *)

  (*   cbn... *)
  (*   focus_single_step_v. *)

  (*   cbn... *)
  (*   subst... *)
  (*   cbn... *)


Admitted.
