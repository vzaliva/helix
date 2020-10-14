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

(* Lemma disjoint_bid_neq {T : Set} (b b' : list (LLVMAst.block T)) : *)
(*   disjoint_bid_blocks b b' -> *)
(*   forall x x', In x b -> In x' b' -> blk_id x ≢ blk_id x'. *)
(* Proof. *)
(*   intros. *)
(*   do 2 red in H. *)
(*   specialize (H (blk_id x) (blk_id x')). *)
(*   apply H; apply In_inj_block_ids; auto. *)
(* Qed. *)

(* Lemma find_block_ineq : *)
(*   ∀ (T : Set) (x : block_id) (b bs : list (LLVMAst.block T)) e, *)
(*     disjoint_bid_blocks b bs -> *)
(*     find_block T bs x ≡ Some e -> find_block T (b ++ bs) x ≡ Some e. *)
(* Proof. *)
(*   intros. *)
(*   induction b. *)
(*   - intros. rewrite app_nil_l. apply H0. *)
(*   - intros. *)
(*     rewrite list_cons_app. *)
(*     rewrite <- app_assoc. *)
(*     rewrite <- list_cons_app. *)
(*     cbn. *)
(*     assert (blk_id a ≢ x). *)
(*     assert (H' := H0). *)
(*     apply find_some in H0. destruct H0. *)
(*     assert (In a (a :: b)). { red. left. reflexivity. } *)
(*     destruct (Eqv.eqv_dec_p (blk_id e) x). 2 : inversion H1. *)
(*     rewrite <- e0. *)
(*     eapply disjoint_bid_neq; eauto. *)
(*     assert (not (Eqv.eqv (blk_id a) x)). red. intros. apply H1. rewrite H2. reflexivity. *)
(*     unfold Eqv.eqv_dec_p. eapply rel_dec_neq_false in H2. 2 : typeclasses eauto. *)
(*     setoid_rewrite H2. apply IHb. *)
(*     red. red in H. *)
(*     eapply Coqlib.list_disjoint_cons_left. *)
(*     rewrite list_cons_app in H. *)
(*     clear H0 IHb H1 H2. induction b. cbn. rewrite app_nil_r in H. *)
(*     apply H. red. intros. red in H. apply H. 2 : auto. *)
(*     eapply Permutation.Permutation_in. 2: apply H0. *)
(*     clear H IHb H0 H1. *)
(*     remember (a0 :: b). clear Heql. *)
(*     induction l. cbn. auto. *)
(*     cbn. cbn in IHl. eapply Permutation.perm_trans. *)
(*     rewrite list_cons_app. *)
(*     rewrite Permutation.Permutation_app_swap. apply Permutation.Permutation_refl. *)
(*     pose proof @fold_left_acc_app . *)
(*     specialize (H _ _ l (fun x => [blk_id x])). cbn in H. *)
(*     assert ( *)
(*     (fold_left (λ (acc : list block_id) (bk : LLVMAst.block T), (acc ++ [blk_id bk])%list) l [blk_id a1] ++ *)
(*                [blk_id a]) ≡ *)
(*      ([blk_id a1] ++ fold_left (λ (acc : list block_id) (bk : LLVMAst.block T), acc ++ [blk_id bk]) l [ ]) ++ *)
(*      [blk_id a])%list. rewrite H. reflexivity. rewrite H0. *)
(*     assert ( *)
(*     (fold_left (λ (acc : list block_id) (bk : LLVMAst.block T), (acc ++ [blk_id bk])%list) l *)
(*        [blk_id a; blk_id a1]) ≡ *)
(*      ([blk_id a; blk_id a1] ++ fold_left (λ (acc : list block_id) (bk : LLVMAst.block T), acc ++ [blk_id bk]) l [ ])%list). *)
(*     rewrite H; reflexivity. *)
(*     rewrite H1. clear H0 H1. eapply Permutation.perm_trans. *)
(*     apply Permutation.Permutation_app_swap. cbn. *)
(*     apply Permutation.Permutation_refl. *)
(* Qed. *)


Lemma blk_id_norepet_find_block {T} :
  forall (bks : list (LLVMAst.block T)), blk_id_norepet bks ->
  forall x b bs e, (bks ≡ b ++ bs)%list -> find_block T bs x ≡ Some e -> find_block T (b ++ bs) x ≡ Some e.
Proof.
  intros.
  induction b.
  - intros. rewrite app_nil_l. auto.
  - intros.
    rewrite list_cons_app.
    rewrite <- app_assoc.
    rewrite <- list_cons_app.
    cbn.
    assert (blk_id a ≢ x).
    assert (H' := H1).
    apply find_some in H1. destruct H1.
    assert (In a (a :: b)). { red. left. reflexivity. }
    destruct (Eqv.eqv_dec_p (blk_id e) x). 2 : inversion H3.
    rewrite <- e0.
    red in H.
Admitted.


(* list_nopet -> then we can use find_block to find anything  *)

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

(* TODO: General Vellvm lemma *)
Lemma denote_bks_prefix_ :
  forall (prefix bks postfix : list (LLVMAst.block dtyp)) (from to: block_id),
    (* In to (map blk_id bks) -> *)
    (* (* All labels are distinct *) *)
    (* Coqlib.list_norepet (map blk_id (prefix ++ bks ++ postfix)) -> *) (* TODO: Perhaps we don't need this.. *)

    not (In to (map blk_id prefix)) ->
    denote_bks (prefix ++ bks ++ postfix) (from, to) ≈
               ITree.bind (denote_bks bks (from, to))
               (fun x => match x with
                      | inl x => denote_bks (prefix ++ bks ++ postfix) x
                      | inr x => ret (inr x)
                      end
               ).
Proof.
  (* denote_bks_app denote_bks_cons *)
Admitted.

From Vellvm Require Import Numeric.Integers.
(* YZ: I think this is what we need *)
Lemma denote_bks_prefix :
  forall (prefix bks' postfix bks : list (LLVMAst.block dtyp)) (from to: block_id),
    bks ≡ (prefix ++ bks' ++ postfix) ->
    ~ In to (map blk_id prefix) ->
    denote_bks bks (from, to) ≈
               ITree.bind (denote_bks bks' (from, to))
               (fun x => match x with
                      | inl x => denote_bks bks x
                      | inr x => ret (inr x)
                      end
               ).
Proof.
Admitted.

(* Auxiliary integer computation lemmas *)

Lemma genWhileLoop_ind_arith_aux_0:
  forall n,
    dvalue_to_uvalue (eval_int_icmp Slt ((int64) ((Z) (n - 1 - 1)) + (int64) 1) ((int64) ((Z) n))) ≡ u_zero.
Admitted.

Lemma genWhileLoop_ind_arith_aux_1: forall n k,
  dvalue_to_uvalue (eval_int_icmp Slt ((int64) ((Z) (n - S k - 1)) + (int64) 1) ((int64) ((Z) n))) ≡ 'u_one.
Proof.
  intros.
  assert ((eval_int_icmp Slt ((int64) ((Z) (n - S k - 1)) + (int64) 1) ((int64) ((Z) n))) ≡ DVALUE_I1 DynamicValues.Int1.one).
  eapply RelDec_Correct_eq_typ. Unshelve. 3 : apply @dvalue_eq_dec.
  unfold eval_int_icmp. cbn.
  assert ((int64) ((Z) (n - S k - 1)) + (int64) 1 ≡ (int64) ((Z) (n - S k))). {
    Int64.bit_solve.  destruct (Int64.testbit ((int64) ((Z) (n - S k))) i) eqn: H'.
Admitted.

Lemma genWhileLoop_ind_arith_aux_2: forall n k,
UVALUE_I64 ((int64) ((Z) (n - S (S k) - 1)) + (int64) 1) ≡ uvalue_of_nat (n - S (S k)).
Admitted.

Lemma incLocalNamed_fresh:
    forall i i' i'' r r' str str', incLocalNamed str i ≡ inr (i', r) ->
                                          incLocalNamed str' i' ≡ inr (i'', r') -> r ≢ r'.
Proof.
Admitted.


(* TODO: Figure out how to avoid this *)
Arguments fmap _ _ /.
Arguments Fmap_block _ _ _ _/.

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
    (UPPER_BOUND : n > j)
    (LOW_BOUND : j > 0)
    (* Main relations preserved by iteration *)
    (I : nat -> mem_block -> Rel_cfg),

    In body_entry (block_ids body_blocks) ->

    (* All labels generated are distinct *)
    blk_id_norepet bks ->

    fresh_in_cfg bks nextblock ->

    (* Loopvar is unique*)
    (forall i s r, incLocal i ≡ inr (s, r) -> loopvar ≢ r) ->
    (forall str s r, incLocalNamed str ≡ s -> loopvar ≢ r) ->

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
    (forall g l l' mV mH ymem k _label _label',

        (conj_rel (I k ymem)
                  (fun _ '(_, (l, _)) => l @ loopvar ≡ Some (uvalue_of_nat k))
                  mH (mV,(l',g))) ->
        eutt
          (succ_cfg (fun '(memH,vec') '(memV, (l, (g, x))) =>
                l @ loopvar ≡ Some (uvalue_of_nat k) /\
                x ≡ inl (_label', loopcontblock) /\
                I (S k) vec' memH (memV, (l, g))))
          (interp_helix (bodyH (S k) ymem) mH)
          (interp_cfg
             (denote_bks (convert_typ [] body_blocks) (_label, body_entry)) g l mV)
    ) ->

    (* Invariant is stable under extending local state *)
    (forall k mH mV s s' g l ymem id v str, incLocal s ≡ inr (s', id)
                                       \/ incLocalNamed str s ≡ inr (s', id)
                                       \/ id ≡ loopvar ->
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
              I (n - 1) vec' memH (memV,(l,g))
           ))
           (interp_helix (build_vec_gen (S j) n bodyH ymem) mH)
           (interp_cfg (denote_bks (convert_typ [] bks)
                                                (_label, loopcontblock)) g l mV).

Proof.
  intros * UPPER_BOUND LOWER_BOUND * IN UNIQUE_IDENTS NEXTBLOCK_ID LOOPVAR0 LOOPVAR1 GEN.
  unfold genWhileLoop in GEN. cbn* in GEN. simp.
  intros * HBODY STABLE.
  unfold build_vec_gen.
  remember (n - S j) as k eqn:K_EQ.

  assert (JEQ' : j ≡ (n - S k)) by lia. rewrite JEQ' in *.

  assert (n - S k > 0) by lia.
  clear JEQ'.
  clear UPPER_BOUND.

  induction k as [| k IH].

  - (* Base case: we enter through [loopcontblock] and jump out immediately to [nextblock] *)
    intros * (INV & LOOPVAR).

    (* This ugly preliminary is due to the conversion of types, as most ugly things on Earth are. *)
    apply no_repeat_convert_typ with (env := []) in UNIQUE_IDENTS; cbn in UNIQUE_IDENTS; rewrite ?convert_typ_block_app in UNIQUE_IDENTS.
    apply fresh_in_convert_typ with (env := []) in NEXTBLOCK_ID; cbn in NEXTBLOCK_ID; rewrite ?convert_typ_block_app in NEXTBLOCK_ID.
    cbn; rewrite ?convert_typ_block_app.
    hide_cfg.

    (* We jump into [loopcontblock]
       We denote the content of the block.
     *)
    vjmp.

    Import ProofMode.
    cbn.
    (* TODO add to vred *)

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
      apply genWhileLoop_ind_arith_aux_0.
    } 

    vjmp_out.
    hvred.

    (* We have only touched local variables that the invariant does not care about, we can reestablish it *)
    apply eutt_Ret.
    split.
    + reflexivity.
    + eapply STABLE. left. eauto.
      eapply STABLE. right. left. reflexivity.
      apply INV.

  - (* Inductive case *)

    cbn in *. intros * (INV & LOOPVAR).
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
    { cbn; vstep; try solve_lu.
      rewrite genWhileLoop_ind_arith_aux_1.
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
      (* TODO *)
      admit.
      (* inversion UNIQUE_IDENTS. *)
      (* intro. subst. apply H3. right. *)
      (* apply in_or_app. right. constructor. reflexivity. *)
    }
    rewrite denote_phi_hd.
    cbn.
    (* TOFIX: broken automation, a wild translate sneaked in where it shouldn't *)
    rewrite translate_bind.
    rewrite ?interp_cfg_to_L3_ret, ?bind_ret_l;
      rewrite ?interp_cfg_to_L3_bind, ?bind_bind.
    
    vstep.
    {
      (* TODO automation? *)
      setoid_rewrite lookup_alist_add_ineq.
      setoid_rewrite lookup_alist_add_eq. reflexivity.
      intro. symmetry in H0. revert H0.
      Transparent incLocal.
      eapply incLocalNamed_fresh.
      eauto. reflexivity.
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
    rewrite denote_bks_prefix; cycle 1.
    {
      match goal with
        |- ?x::?y::?z ≡ _ => replace (x::y::z) with ([x;y]++z) by reflexivity
      end; f_equal.
    }
    {
      (* TODO: exploit [fresh_in_cfg] to prove that [body_entry] can't be in the prefix *)
      admit.
    }
    hide_cfg.
    hvred.
    eapply eutt_clo_bind.
    (* We can know use the body hypothesis *)
    eapply HBODY.
    {
      (* A bit of arithmetic is needed to prove that we have the right precondition *)
      red. cbn. split. 
      + subst. eapply STABLE. right. right. reflexivity.
        eapply STABLE. left. eauto.
        eapply STABLE. right. left. reflexivity. auto.
        eapply INV.
      + subst. cbn. assert (L : loopvar ≡ loopvar) by reflexivity. eapply rel_dec_eq_true in L.
        rewrite L. cbn.
        rewrite <- genWhileLoop_ind_arith_aux_2. reflexivity.
        typeclasses eauto.
    }

    (* Step 4 : Back to starting from loopcontblock and have reestablished everything at the next index:
        conclude by IH *)
    introR.
    destruct PRE as (LOOPVAR' & HS & IH').
    subst.
    replace (S (n - S (S k)) ) with ( n - S k) by lia.
    eapply IH; try lia.
    split.
    replace (n - S k) with (S (n - S (S k))) by lia; eauto.
    replace (n - S k - 1) with (n - S (S k)) by lia; auto.

    Unshelve.
    all: try auto.
    exact UVALUE_None.
    exact UVALUE_None.
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

    (* All labels generated are distinct *)
    (UNIQUE : blk_id_norepet bks)

    (EXIT_FRESH: fresh_in_cfg bks exit_id)
    (* Computation on the Helix side performed at each cell of the vector, *)
    (*        the counterpart to bodyV *)
    (bodyH: nat -> mem_block -> itree _ mem_block)

    (* Main relation preserved by iteration *)
    (R : Rel_cfg),

    (* Inductive proof: Assuming R, reestablish R by going through both bodies *)
    (forall g l mV mH ymem _label k,
        (R mH (mV,(l,g))) ->
        eutt (succ_cfg
              (fun '(memH,vec') '(memV, (l, (g,x))) =>
                            x ≡ inl (_label, wrap_loop_id) /\
                            R memH (memV,(l,g))))
          (interp_helix (bodyH k ymem) mH)
          (interp_cfg
             (denote_bks (convert_typ [] bodyV) (_label,body_entry_id)) g l mV)
    ) ->

    (* R must be stable by extension of the local env *)
    (forall mH mV s s' g l id v str,
                            incLocalNamed str s ≡ inr (s', id) ->
                            R mH (mV, (l, g)) ->
                            R mH (mV, ((alist_add id v l), g))) ->

    (* R must entail the state invariant *)
    imp_rel R (state_invariant σ s1) ->

    (* Main result. Need to know initially that R holds *)
    forall g l mV mH ymem ,
      R mH (mV,(l,g)) ->
      eutt (succ_cfg
            (fun '(memH,vec') '(memV, (l, (g,x))) =>
                          (x ≡ inl (wrap_loop_id, exit_id) \/
                          x ≡ inl (entry_id, exit_id)) /\
                          R memH (memV,(l,g))))

           (interp_helix (build_vec n bodyH ymem) mH)
           (interp_cfg (denote_bks (convert_typ [] bks) (from_id,entry_id)) g l mV).
Proof with rauto.
  intros * GEN * UNIQUE EXIT * IND STABLE IMPSTATE * PRE.
  unfold genWhileLoop in GEN. cbn* in GEN. simp.
  unfold build_vec.
  destruct n.
  - (* 0th index *)
    cbn.

    apply fresh_in_convert_typ with (env := []) in EXIT; cbn in EXIT; rewrite ?convert_typ_block_app in EXIT.
    cbn; rewrite ?convert_typ_block_app.

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
    eapply STABLE. reflexivity. eauto.

  - (* 1th index : single loop iteration *)
    destruct n.
  {
    Opaque build_vec_gen.
    cbn.
    cbn in *.
    apply fresh_in_convert_typ with (env := []) in EXIT; cbn in EXIT; rewrite ?convert_typ_block_app in EXIT.
    apply no_repeat_convert_typ with (env := []) in UNIQUE; cbn in UNIQUE; rewrite ?convert_typ_block_app in UNIQUE.

    cbn; rewrite ?convert_typ_block_app.

    hide_cfg.

    (* pose proof @genWhileLoop_ind as GEN_IND. *)
    Transparent build_vec_gen.
    (* unfold build_vec_gen in GEN_IND. *)
    (* unfold build_vec_gen. cbn in GEN_IND. *)
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

    (* Step 2 : Jump to b0, i.e. loopblock (since we have checked k < n). *)
    vbranch_l.
    {
      cbn; vstep; try solve_lu.
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

    rewrite denote_bks_prefix.

    vred.
    eapply eutt_clo_bind. apply IND.
    eapply STABLE. admit. eapply STABLE. reflexivity. auto.

    intros. destruct u1. destruct u2 as (? & ?& ? &?).
    destruct p, s.
    3 : inversion H.
    cbn in H.

    destruct p.
    destruct H as (ID & INV).
    inversion ID; subst.
    vjmp.

      Unshelve.
    repeat vred. vstep.
    {
      vstep. vstep. solve_lu. admit. (* loopvar *)
      reflexivity.
      vstep.
      reflexivity.
      apply uvalue_to_dvalue_of_dvalue_to_uvalue.
      Unshelve. reflexivity.
      3 : exact (DVALUE_I64 (repr 1)). cbn. reflexivity.
    }
    hvred.
    vstep. cbn.
    vred.

    vstep. vstep. solve_lu. reflexivity.
    vstep. reflexivity. reflexivity. reflexivity. reflexivity.


    vbranch_r.
    vstep. solve_lu. reflexivity.

    vjmp_out. vred. apply eutt_Ret.
    split. 
    + left. reflexivity.
    + eapply STABLE. admit.
      eapply STABLE. admit.
      apply INV.
    + destruct H as (? & ?). inversion H.
    + inv VG. admit.
    + admit.
      Unshelve. all : eauto.
    + eauto.
    + eauto.
    + eauto.
  }

  (* IH*)
  Admitted.
