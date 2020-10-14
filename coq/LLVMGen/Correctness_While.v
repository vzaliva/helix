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
    (bks : list (LLVMAst.block typ)) ,

    In body_entry (block_ids body_blocks) ->

    (* All labels generated are distinct *)
    blk_id_norepet bks ->

    fresh_in_cfg bks nextblock ->

    forall (n : nat)                       (* Number of iterations *),

    (* Generation of the LLVM code wrapping the loop around bodyV *)
    genWhileLoop prefix (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n))
                       loopvar loopcontblock body_entry body_blocks [] nextblock s1
                       ≡ inr (s2,(entry_id, bks)) ->

    (* Loopvar is unique*)
    (forall i s r, incLocal i ≡ inr (s, r) -> loopvar ≢ r) ->
    (forall str s r, incLocalNamed str ≡ s -> loopvar ≢ r) ->

    (* Computation on the Helix side performed at each cell of the vector, *)
    (*    the counterpart to bodyV (body_blocks) *)
    forall (bodyH: nat -> mem_block -> itree _ mem_block)
    (j : nat)                       (* Starting iteration *)
    (UPPER_BOUND : n > j)

    (* Main relations preserved by iteration *)
    (I : nat -> mem_block -> Rel_cfg),
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
  intros * IN UNIQUE_IDENTS NEXTBLOCK_ID * GEN LOOPVAR0 LOOPVAR1 * BOUND *.
  unfold genWhileLoop in GEN. cbn* in GEN. simp.
  intros * HBODY STABLE.
  unfold build_vec_gen.
  remember (n - S j) as k eqn:K_EQ.

  assert (JEQ' : j ≡ (n - S k)) by lia. rewrite JEQ' in *.

  (* assert (n - S k > 0) by lia. *)
  clear JEQ'.
  clear BOUND.

  induction k as [| k IH].

  - (* Base case: we enter through [loopcontblock] and jump out immediately to [nextblock] *)
    intros * (INV & LOOPVAR).
    Import ProofMode.
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
      intro.
      (* symmetry in H0. revert H0. *)
      (* Transparent incLocal. *)
      (* eapply incLocalNamed_fresh. *)
      (* eauto. reflexivity. *) admit.
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
        |- ?x::?y::?z ≡ _ => replace (x::y::z) with ([x;y]++z) by reflexivity
      end; f_equal.
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
  forall (prefix : string)
    (loopvar : raw_id)            (* lvar storing the loop index *)
    (loopcontblock body_entry: block_id) (* entry point of the body *)
    (body_blocks : list (LLVMAst.block typ)) (* (llvm) body to be iterated *)
    (exit_id : block_id)       (* exit point of the overall loop *)
    (entry_id : block_id)      (* entry point of the overall loop *)
    σ (s1 s2 : IRState)
    (bks : list (LLVMAst.block typ)) (* (llvm) code defining the whole loop *)
    (n : nat)                    (* Number of iterations *)

    (* Generation of the LLVM code wrapping the loop around bodyV *)
    (GEN: genWhileLoop prefix (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n))
                       loopvar loopcontblock body_entry body_blocks [] exit_id s1
                       ≡ inr (s2,(entry_id,bks)))

    (* All labels generated are distinct *)
    (UNIQUE : blk_id_norepet bks)
    (IN :In body_entry (block_ids body_blocks))
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
                            x ≡ inl (_label, loopcontblock) /\
                            R memH (memV,(l,g))))
          (interp_helix (bodyH k ymem) mH)
          (interp_cfg
             (denote_bks (convert_typ [] body_blocks) (_label,body_entry)) g l mV)
    ) ->

    (* R must be stable by extension of the local env *)
    (forall mH mV s s' g l id v str,
                            incLocalNamed str s ≡ inr (s', id) ->
                            R mH (mV, (l, g)) ->
                            R mH (mV, ((alist_add id v l), g))) ->

    (* R must entail the state invariant *)
    imp_rel R (state_invariant σ s1) ->

    (* Main result. Need to know initially that R holds *)
    forall g l mV mH ymem _label,
      R mH (mV,(l,g)) ->
      eutt (succ_cfg
            (fun '(memH,vec') '(memV, (l, (g,x))) =>
                          (x ≡ inl (loopcontblock, exit_id) \/
                          x ≡ inl (entry_id, exit_id)) /\
                          R memH (memV,(l,g))))

           (interp_helix (build_vec n bodyH ymem) mH)
           (interp_cfg (denote_bks (convert_typ [] bks) (_label ,entry_id)) g l mV).
Proof with rauto.
  intros * GEN * UNIQUE IN EXIT * IND STABLE IMPSTATE * PRE.
  pose proof @genWhileLoop_ind as GEN_IND.
  specialize (GEN_IND prefix loopvar loopcontblock body_entry body_blocks exit_id entry_id s1 s2 bks).
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
    eapply STABLE. Transparent incLocal. apply Heqs1. eauto.

  - Opaque build_vec_gen.
    cbn.
    cbn in *.
    apply fresh_in_convert_typ with (env := []) in EXIT; cbn in EXIT; rewrite ?convert_typ_block_app in EXIT.
    apply no_repeat_convert_typ with (env := []) in UNIQUE; cbn in UNIQUE; rewrite ?convert_typ_block_app in UNIQUE.

    cbn; rewrite ?convert_typ_block_app.
    cbn in GEN_IND; rewrite ?convert_typ_block_app in GEN_IND.

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
      (* assert (genWhileLoop_aux_0: dvalue_to_uvalue (eval_int_icmp Slt ((int64) 0) ((int64) (Z.pos (Pos.succ (Pos.of_succ_nat n))))) ≡ 'u_one). admit. *)
      (* rewrite <- genWhileLoop_aux_0. cbn. reflexivity. *) admit.
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
    eapply STABLE. admit. eapply STABLE. eauto. eauto.

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
    (* hvred. *)
    vstep. cbn.
    vred.

    vstep. vstep. vstep. solve_lu. reflexivity.
    vstep. reflexivity. reflexivity. reflexivity. reflexivity.


    vbranch_l.
    vstep. solve_lu. admit.

    (* reflexivity. *)

    vjmp. vred.

    (* BEGIN TODO: infrastructure to deal with non-empty phis *)
    unfold denote_phis.
    repeat vred.

    unfold map_monad. cbn. vred. 
    (* rewrite interp_cfg_to_L3_LW. vred. vred. vred. vred. *)
    rewrite denote_phi_tl.

    vred. rewrite denote_phi_hd.

    cbn.

    (* TOFIX: broken automation, a wild translate sneaked in where it shouldn't *)
    rewrite translate_bind.
    rewrite ?interp_cfg_to_L3_ret, ?bind_ret_l;
      rewrite ?interp_cfg_to_L3_bind, ?bind_bind.

    vstep. solve_lu. tred. repeat vred.

    rewrite interp_cfg_to_L3_LW. repeat vred.
    (* TODO : What is the appropriate relation "R" here?*)
   assert (REL: forall _label R,
    eutt R (interp_cfg_to_L3 defined_intrinsics (denote_bks G (b0, body_entry)) g0 l0 m)
         (interp_cfg_to_L3 defined_intrinsics (denote_bks G (_label, loopcontblock)) g0 l0 m)). {
     admit.
   }

   (* TODO : use REL and eqit_trans to apply GEN_IND. *)
    (* eapply IND.  *)
    (* TODO : state a lemma about the relationship between body_entry and... etc.*)
    assert (loopcontblock ≡ body_entry). admit. rewrite <- H.


   (* After getting that into shape, applying the GEN_IND should be fairly straightforward. *)
    (* rewrite <- H0. *)
    (* Trying to see how genWhileLoop_ind would be applied. *)
    unfold build_vec_gen in GEN_IND.
    assert (forall j, S n - S j ≡ n - j) by lia.
    assert (n ≡ n - 0) by lia. rewrite H1. rewrite <- H0.

    eapply eutt_Proper_mono. admit.
    (* Unset Printing Notations.  *)
    (* assert (n - 0 ≡ n) by lia. rewrite H1 in GEN_IND. *)
    (* rewrite H. rewrite <- H0. *)

    eapply GEN_IND.
    admit. admit. lia.
    intros.
    cbn. eapply eutt_Proper_mono. admit. apply IND.
    destruct H1. destruct H2. admit.
    intros. eapply STABLE. destruct H2. apply e. destruct o. rewrite <- H2. admit.
    inversion H2. admit.
    apply H3.
    split. admit. solve_lu. admit.
    inversion H. inversion H0.
    admit. admit. all: eauto. exact 'u_one.

Admitted.
 

