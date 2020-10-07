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

(* Definition block_ids {T : Set} (b : list ((LLVMAst.block T))) := *)
(*   fold_left (fun (acc : list block_id) (bk : LLVMAst.block T) => (acc ++ [blk_id bk])%list) b []. *)

(* IY: Why isn't it the below, instead? It looks like outputs etc. also have use
   fold_left instead of map (in Vellvm - Denotation_Theory.v), which feels super
   awkward. Following Vellvm conventions for now. *)
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

(* (* IY: The more general statement should be In being injective over List.map, *)
(*    but it's stated like this here because we're using fold_left *) *)
(* Lemma In_inj_block_ids : *)
(*   forall T x (b : list (LLVMAst.block T)), In x b -> In (blk_id x) (block_ids b). *)
(* Proof. *)
(*   intros. revert H. revert x. induction b. *)
(*   - intros. inversion H. *)
(*   - intros. unfold block_ids. cbn. *)
(*     rewrite fold_left_acc_app. rewrite <-list_cons_app. *)
(*     cbn in H. destruct H. cbn. left. rewrite H. reflexivity. *)
(*     cbn. right. apply IHb. auto. *)
(* Qed. *)

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


(* All labels in a list of blocks are distinct *)
Definition blk_id_norepet {T} (bks : list (LLVMAst.block T)) :=
  Coqlib.list_norepet (map blk_id bks).

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
    (* TODO: Rethink about this lower bound (j > 0?) *)
    (LOW_BOUND : j > 1)
    (* Main relations preserved by iteration *)
    (I : nat -> mem_block -> Rel_cfg),

    In body_entry (block_ids body_blocks) ->

    not (In nextblock (map blk_id bks)) ->

    (* Loopvar is unique *)
    (* TODO : quantify boundedness using s1. *)
    (forall i s r, incLocal i ≡ inr (s, r) -> loopvar ≢ r) ->
    (* TODO : assumption doesn't include r *)
    (forall str s r, incLocalNamed str ≡ s -> loopvar ≢ r) ->

    (* Generation of the LLVM code wrapping the loop around bodyV *)
    genWhileLoop prefix (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n))
                       loopvar loopcontblock body_entry body_blocks [] nextblock s1
                       ≡ inr (s2,(entry_id, bks)) ->

    (* All labels generated are distinct *)
    blk_id_norepet bks ->
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
             (fun '(memH,vec') '(memV, (l, (g, x))) =>
                l @ loopvar ≡ Some (uvalue_of_nat k) /\
                x ≡ inl (_label', loopcontblock) /\
                I (S k) vec' memH (memV, (l, g)))
          (with_err_RB (interp_Mem (bodyH (S k) ymem) mH))
          (with_err_LB (interp_cfg
                          (denote_bks (convert_typ [] body_blocks) (_label, body_entry)) g l mV))
    ) ->

    (* Invariant is stable under extending local state *)
    (* TODO: clean up incLocalNamed, incLocal *)
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
      eutt (fun '(memH,vec') '(memV, (l, (g,x))) =>
              x ≡ inl (loopcontblock, nextblock) /\
              I (n - 1) vec' memH (memV,(l,g))
           )
           (with_err_RB (interp_Mem (build_vec_gen (S j) n bodyH ymem) mH))
           (with_err_LB (interp_cfg (denote_bks (convert_typ [] bks)
                                                (_label, loopcontblock)) g l mV)).

Proof with rauto.
  intros * UPPER_BOUND LOWER_BOUND * IN UNIQUE_IDENTS NEXTBLOCK_ID LOOPVAR0 LOOPVAR1 GEN.
  unfold genWhileLoop in GEN. cbn* in GEN. simp.
  intros * HBODY STABLE.
  unfold build_vec_gen.
  remember (n - S j) as k eqn:K_EQ.

  assert (JEQ' : j ≡ (n - S k)) by lia. rewrite JEQ' in *.

  assert (n - S k > 1). lia.
  clear JEQ'.
  clear UPPER_BOUND.
  red in UNIQUE_IDENTS. cbn in UNIQUE_IDENTS. rewrite map_app in UNIQUE_IDENTS.
  cbn in UNIQUE_IDENTS.
  assert (MAP_CONV: forall bs, map blk_id bs ≡ map blk_id (convert_typ [] bs)). {
    induction bs. cbn. reflexivity.
    cbn. rewrite IHbs. reflexivity.
  }
  rewrite MAP_CONV in UNIQUE_IDENTS.

  match goal with
  | [ |- context[convert_typ [] (?a::?b::_ ++?c)]] => remember a as entry_bk;
                                                       remember b as b0_bk;
                                                       remember c as loopcont_bk
  end.

  induction k as [| k IH].
  - intros * (INV & LOOPVAR).
    cbn...

    (* RHS Vellvm simplification *)
    subst.
    Arguments fmap /.
    Arguments Fmap_block /.
    cbn. intros.
    rewrite denote_bks_unfold_in.
    2 : {
      rewrite find_block_ineq. rewrite find_block_ineq.
      rewrite convert_typ_block_app. rewrite find_block_none_app.
      Opaque find_block.
      cbn. unfold fmap, Fmap_block. cbn. rewrite find_block_eq.
      reflexivity. cbn. reflexivity.
      auto.
      cbn.
      apply find_block_not_in_inputs.
      red. intros.
      eapply Coqlib.list_drop_norepet in UNIQUE_IDENTS.
      Unshelve. 4 : exact 2. cbn in UNIQUE_IDENTS.
      apply Coqlib.list_norepet_append_commut in UNIQUE_IDENTS.
      cbn in UNIQUE_IDENTS. inversion UNIQUE_IDENTS. apply H3.
      apply H0.
      red. cbn. intros.
      cbn in UNIQUE_IDENTS.
      apply (Coqlib.list_drop_norepet 1) in UNIQUE_IDENTS. cbn in UNIQUE_IDENTS.
      rewrite list_cons_app in UNIQUE_IDENTS.
      rewrite -> Coqlib.list_norepet_app in UNIQUE_IDENTS. destruct UNIQUE_IDENTS as (? & ? & ?).
      red in H3. specialize (H3 b0 loopcontblock). apply H3. constructor. reflexivity.
      apply in_or_app. right. constructor. auto. auto.
      cbn.
      rewrite list_cons_app in UNIQUE_IDENTS.
      apply Coqlib.list_norepet_append_commut in UNIQUE_IDENTS.
      rewrite Coqlib.list_norepet_app in UNIQUE_IDENTS.
      destruct UNIQUE_IDENTS as (? & ? & ?).
      apply Coqlib.list_disjoint_sym in H2.
      apply H2. constructor. reflexivity.
      cbn. right. apply in_or_app. right. constructor. auto.
    }
    cbn...
    cbn...
    focus_single_step_v.
    Transparent denote_code.
    cbn...
    focus_single_step_v.

    setoid_rewrite denote_instr_op.
    2 : {
      cbn...
      2 : {
        eauto.
      }
      cbn...
      unfold uvalue_to_dvalue_binop.
      cbn...
      reflexivity.
    }
    cbn... subst. cbn...
    rewrite denote_instr_op.
    2 : {
      cbn.
      cbn...
      2 : {
        setoid_rewrite lookup_alist_add_eq. reflexivity.
      }
      cbn...
      Arguments uvalue_to_dvalue_binop /.
      cbn...
      reflexivity.
    }
    cbn...
    rewrite denote_term_br_r.
    2 : {
      (* TODO: notation for map updates *)
      cbn...
      2 : {
        setoid_rewrite lookup_alist_add_eq. reflexivity.
      }
      match goal with
      | [ |- ret (_, (_, (_, ?x))) ≈ Ret (_, (_, (_, ?x'))) ] => assert (x ≡ x')
          end.
  apply genWhileLoop_ind_arith_aux_0.
      cbn. rewrite H0. reflexivity.
    }
    cbn...

    subst. rewrite denote_bks_unfold_not_in.
    2 : {
      rewrite find_block_ineq. rewrite find_block_ineq.
      rewrite convert_typ_block_app. rewrite find_block_none_app.
      Opaque find_block.
      cbn. unfold fmap, Fmap_block. cbn. rewrite find_block_ineq.
      apply find_block_nil. cbn.
      cbn in NEXTBLOCK_ID. intro. apply NEXTBLOCK_ID. right. right.
      rewrite map_app. cbn. apply in_or_app. right. cbn. left. auto.
      cbn in NEXTBLOCK_ID. apply find_block_not_in_inputs. intro.
      apply NEXTBLOCK_ID. right. right. rewrite map_app. cbn.
      apply in_or_app. left. unfold inputs in H0. rewrite MAP_CONV. cbn in H0. unfold Fmap_list in H0.
      auto. cbn.
      cbn in NEXTBLOCK_ID. intro. apply NEXTBLOCK_ID. right. left. auto.
      cbn. cbn in NEXTBLOCK_ID. intro. apply NEXTBLOCK_ID. left. auto.
    }
    cbn...

    apply eutt_Ret.
    split.
    + reflexivity.
    + eapply STABLE. left. eauto.
      eapply STABLE. right. left. reflexivity.
      apply INV.

  - cbn in *. intros * (INV & LOOPVAR).
    Arguments fmap /.
    Arguments Fmap_block /.
    cbn...

    (* RHS : Reducing RHS to apply Body Hypothesis *)
    (* First step : First, Check that k<n hence we do not exit, in order to jump back to bodyblock. *)
    rewrite list_cons_app.
    rewrite convert_typ_block_app.
    (* We ignore entry_id *)
    cbn. rewrite list_cons_app.
    rewrite denote_bks_unfold_in. cbn.

    (* START rewrite *)
    rewrite bind_bind. rewrite bind_bind. rewrite interp_cfg_to_L3_bind.
    rewrite translate_bind.
    (* END rewrite *)

    2 : {
      match goal with
      | [ |- find_block dtyp (_ ++ ?l) _ ≡ _ ] => remember l
      end
      .
      rewrite list_cons_app in Heql0.
      rewrite Heql0.
      rewrite app_assoc.
      rewrite app_assoc. erewrite blk_id_norepet_find_block. reflexivity.
      2 : reflexivity. cbn. cbn in UNIQUE_IDENTS.
      2 : {
        cbn. subst.
        assert (EQ: loopcontblock ≡ loopcontblock) by reflexivity.
        eapply rel_dec_eq_true in EQ. 2 : typeclasses eauto. subst.
        cbn. rewrite find_block_eq. reflexivity. reflexivity.
      }
      red. cbn.
      rewrite map_app. cbn. subst. cbn. 
      apply UNIQUE_IDENTS.
    }

    (* Updating (loopvar <- S k) coming from loopcontblock. *)
    focus_single_step_v.
    cbn.

    (* START rewrite *)
    rewrite interp_cfg_to_L3_ret. rewrite translate_ret. rewrite bind_ret_l.
    (* END rewrite *)

    rewrite Heqi7.

    (* START rewrite *)
    rewrite bind_bind. rewrite interp_cfg_to_L3_bind.
    rewrite translate_bind. cbn. rewrite interp_cfg_to_L3_ret.
    rewrite translate_ret. rewrite bind_ret_l. rewrite bind_ret_l.
    rewrite bind_bind. rewrite interp_cfg_to_L3_bind.
    rewrite translate_bind. cbn.
    (* END rewrite *)

    focus_single_step_v.
    Transparent denote_code.
    unfold denote_code. cbn. Opaque denote_code.

    (* START rewrite *)
    rewrite bind_bind. rewrite interp_cfg_to_L3_bind.
    rewrite translate_bind. rewrite bind_bind.
    (* END rewrite *)

    focus_single_step_v.
    Transparent denote_instr. unfold denote_instr.
    Opaque denote_instr.

    (* START rewrite *)
    setoid_rewrite interp_cfg_to_L3_bind. rewrite translate_bind.
    rewrite bind_bind. cbn. (* This cbn takes so long.. *)
    rewrite translate_bind. rewrite interp_cfg_to_L3_bind.
    rewrite translate_bind. rewrite bind_bind.
    rewrite translate_trigger. rewrite translate_trigger.
    rewrite lookup_E_to_exp_E_Local.
    rewrite subevent_subevent.
    rewrite exp_E_to_instr_E_Local. rewrite subevent_subevent.
    rewrite interp_cfg_to_L3_LR.
    (* END rewrite *)

    2 : { cbn... eauto. }
    cbn.

    (* START rewrite *)
    rewrite translate_ret. rewrite bind_ret_l. rewrite translate_bind.
    rewrite interp_cfg_to_L3_bind. rewrite translate_bind. rewrite bind_bind.
    cbn...
    (* END rewrite *)

    unfold uvalue_to_dvalue_binop. cbn. cbn...
    unfold uvalue_to_dvalue. cbn.
    cbn...
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
    rewrite interp_cfg_to_L3_LW. cbn.

    (* START rewrite *)
    rewrite translate_ret. rewrite bind_ret_l. rewrite interp_cfg_to_L3_bind.
    rewrite translate_bind. rewrite bind_bind. rewrite bind_ret_l.
    rewrite interp_cfg_to_L3_ret. rewrite translate_ret. rewrite bind_ret_l.
    rewrite bind_ret_l. rewrite interp_cfg_to_L3_ret. rewrite translate_ret.
    rewrite bind_ret_l.
    (* END rewrite *)
    clear Heqi10. rewrite Heqi9.
    Transparent denote_terminator. cbn.

    (* START rewrite *)
    rewrite translate_trigger. rewrite lookup_E_to_exp_E_Local.
    rewrite subevent_subevent. rewrite translate_bind.
    rewrite bind_bind. rewrite translate_trigger.
    rewrite interp_cfg_to_L3_bind.
    rewrite translate_bind.
    (* END rewrite *)
    focus_single_step_v.

    cbn...
    cbn.
    2 : {
      setoid_rewrite lookup_alist_add_eq. reflexivity.
    }

    (* We find that k < n, thus we go back to looping on the body *)
    cbn...

    (* assert (n - S (S k) ≡ n - S k - 1) by lia. setoid_rewrite H0. *)
    cbn.
    match goal with
    | [ |- context [(g, ?w)]] => remember w
    end.

    assert (u ≡ 'u_one). subst.
    apply genWhileLoop_ind_arith_aux_1.
    rewrite H0.

    rewrite Heqi11. cbn.
    cbn... clear Heqi11.


    (* Step 2 : Jump back to body_entry (since we have checked k < n). *)
    simpl. cbn...
    simpl.
    rewrite list_cons_app. cbn...

    rewrite denote_bks_unfold_in.

    2 : {
      rewrite list_cons_app.
      erewrite blk_id_norepet_find_block.
      reflexivity. 2 : reflexivity.
      red; cbn; rewrite map_app; cbn.
      subst. cbn.
      apply UNIQUE_IDENTS.
      rewrite find_block_eq. reflexivity. subst. cbn. reflexivity.
    }
    cbn...
    subst. cbn...
    (* rewrite Heqb0_bk, Heqentry_bk, Heqloopcont_bk. cbn... *)
    rewrite denote_phi_tl.
    focus_single_step_v.
    2 : {
      inversion UNIQUE_IDENTS.
      cbn in H2. intro. subst. apply H3. right.
      apply in_or_app. right. constructor. reflexivity.
    }
    Transparent denote_phi. unfold denote_phi. rewrite assoc_hd. cbn.
    cbn... cbn. rewrite translate_ret. rewrite bind_ret_l.
    Opaque denote_phi.
    2 : {
      setoid_rewrite lookup_alist_add_ineq.
      setoid_rewrite lookup_alist_add_eq. reflexivity.
      intro. symmetry in H1. revert H1.
      Transparent incLocal.
      eapply incLocalNamed_fresh.
      eauto. reflexivity.
    }
    cbn... rewrite Heqi7. cbn...

    (* Got the phi node from loop cont block, now! Time to jump to body_entry. *)
    (* Before that, we need to clean up some fluff. *)
    cbn... focus_single_step_v. cbn...
    subst.

    cbn...
    focus_single_step_v. cbn...
    subst.
    cbn...
    cbn...
    rewrite interp_cfg_to_L3_LW. cbn. setoid_rewrite translate_ret.
    rewrite bind_ret_l.
    cbn... cbn.
    rewrite interp_cfg_to_L3_ret. setoid_rewrite translate_ret.
    rewrite bind_ret_l. rewrite interp_cfg_to_L3_bind.
    setoid_rewrite translate_ret. setoid_rewrite interp_cfg_to_L3_ret.
    rewrite bind_ret_l.

    (* Starting to see body entry in the horizon. We need to apply the body hypothesis
       to retrieve the fact that "bks" entering from "body_entry" is the same denotation
       as "body_bks" entering from "body_entry". *)

    (* Step 3 : Starting to think about applying body hypothesis *)
    (* Step 3.1 : Make right had side of equation agree with right hand side of HBODY *)
    match goal with
    | [ |- context[interp_cfg _ _ ?l _]] => remember l as LOCAL
    end.

    assert (H0': (forall A (b : A) b1 l0 l1, b :: b1 :: l0 ++ l1 ≡ (b :: [b1]) ++ l0 ++ l1)%list). cbn. reflexivity.
    rewrite H0'.

    rewrite denote_bks_prefix_.
    2 : {
      assert (forall bs, map blk_id bs ≡ map blk_id (convert_typ [] bs)). {
        induction bs. cbn. reflexivity.
        cbn. rewrite IHbs. reflexivity.
      }
      subst. rewrite <-H1. unfold block_ids in IN. apply IN.
    }

    2 : {
      subst. cbn. rewrite map_app. cbn. apply UNIQUE_IDENTS.
    }
    cbn...

    assert (n - k ≡ S (S (n - S (S k)))). lia.

    rewrite <-H1.
    eapply eutt_clo_bind.

    (* Step 3 (Actually applying BH): By body hypothesis, this will lead to my invariant being true at
       step S k, and to jumping to loopcontblock. *)
    eapply HBODY.

    red. Unshelve. 6 : exact LOCAL. split.
    + subst. eapply STABLE. right. right. reflexivity.
      eapply STABLE. left. eauto.
      eapply STABLE. right. left. reflexivity. auto.
    + subst. cbn. assert (L : loopvar ≡ loopvar) by reflexivity. eapply rel_dec_eq_true in L.
      rewrite L. cbn.
      rewrite genWhileLoop_ind_arith_aux_2. reflexivity.
      typeclasses eauto.
    +

    intros *. destruct u1, u2. destruct p. destruct p.
    intros (LOOPVAR' & HS & IH').
    rewrite HS.

    (* Step 4 : Back to starting from loopcontblock and have reestablished everything at the next index:
        conclude by IH *)
    (* assert (EQ'' : S ( S (S (n - S (S k)) - 1)) ≡ n - k). lia. *)
    (* rewrite EQ''. *)
    subst. cbn in IH. rewrite convert_typ_block_app in IH. cbn in IH.
      match goal with
      | [ |- context[denote_bks (?a :: ?b :: ?c ++ ?d)]] => remember a; remember b; remember c; remember d
      end.
      match goal with
      | [ H : context[denote_bks (?a :: ?b :: ?c ++ ?d)] |- _] => remember a; remember b; remember c; remember d
      end
      .
      assert (EQB1: b2 ≡ b). {
        subst.
        rewrite 2 typ_to_dtyp_I. reflexivity.
      }
      assert (EQB2: b3 ≡ b1). {
        subst. rewrite typ_to_dtyp_I. reflexivity.
      }
      assert (EQB3 : l4 ≡ l2). {
        subst. rewrite 2 typ_to_dtyp_I. reflexivity.
      }
      rewrite <- EQB1,<- EQB2,<- EQB3.
      assert (S (n - S k) ≡ n - k). lia. rewrite <- H2.
      eapply IH. lia. lia. lia.

      assert ((S (n - S (S k)) ) ≡ n - S k). lia. rewrite <- H3. auto.

      split; auto. rewrite H3.
      Unshelve.
      all: try auto.
      assert (n - S k - 1 ≡ n - S (S k)). lia. rewrite H4. auto.
    + auto.
    + apply RawIDOrd.eq_dec.
Qed.

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

    (* Computation on the Helix side performed at each cell of the vector, *)
(*        the counterpart to bodyV *)
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
