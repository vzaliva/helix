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
  @build_vec_gen_aux E from (1 + to - from).

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

(* Notation "x < y" := (DynamicValues.Int64.lt x y). *)
(* Notation "x + y" := (DynamicValues.Int64.add x y). *)
(* Notation "'u_zero'" := (UVALUE_I1 DynamicValues.Int1.zero). *)
(* Notation "'u_one" := (UVALUE_I1 DynamicValues.Int1.one). *)
(* Notation "'d_zero'" := (DVALUE_I1 DynamicValues.Int1.zero). *)
(* Notation "'d_one'" := (DVALUE_I1 DynamicValues.Int1.one). *)
(* Notation "'(int64)' x" := (Int64.repr x) (at level 10). *)
(* Notation "'(Z)' x" := (Z.of_nat x) (at level 10). *)

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

Lemma __fresh:
    forall s i i' i'' r r' , incLocal i ≡ inr (i', r) ->
                      incLocalNamed s i' ≡ inr (i'', r') -> r ≢ r'.
Proof.
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

Lemma lt_nat_to_Int64: forall j n,
    0 <= j ->
    j < n ->
    (Z.of_nat n < half_modulus)%Z ->
    (Z.of_nat j < half_modulus)%Z ->
    lt (repr (Z.of_nat j)) (repr (Z.of_nat n)) ≡ true.
Proof.
  intros.
  unfold lt.
  rewrite !signed_repr.
  2,3:unfold min_signed, max_signed; lia.
  break_match_goal; auto.
  lia.
Qed.

Lemma alist_find_eq:
  ∀ (K V : Type) (RR : RelDec Logic.eq),
    RelDec_Correct RR → ∀ (m : alist K V) (k : K) (v : V), alist_add k v m @ k ≡ Some v.
Proof.
  intros.
  cbn.
  rewrite rel_dec_eq_true; auto.
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
      (NO_OVERFLOW : (Z.of_nat n < Int64.half_modulus)%Z)

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
            (interp_helix (bodyH (S k) ymem) mH)
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
          forall k ymem mH l l' mV g,
            (forall id, id <> c -> id <> d -> id <> e -> id <> loopvar -> l @ id ≡ l' @ id) ->
            I k ymem mH (mV, (l, g)) ->
            I k ymem mH (mV, (l', g))) ->
      
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
           (interp_helix (build_vec_gen (S j) n bodyH ymem) mH)
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
    replace (j - S j) with 0 by lia.

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
      rewrite __arith; try lia.
      unfold eval_int_icmp.
      rewrite lt_antisym.
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
    + eapply STABLE; cycle -1; [apply INV |..]; eauto.
      intros; rewrite 2 alist_find_neq; eauto. 

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
    { cbn; vstep; try solve_lu.
      rewrite __arith; try lia.
      apply eutt_Ret.
      repeat f_equal.
      clear - EQidx LT LE OVER.
      unfold eval_int_icmp; rewrite lt_nat_to_Int64; try lia.
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
        |- ?x::?y::?z ≡ _ => replace (x::y::z) with ([x;y]++z) by reflexivity
      end; f_equal.
    }
    hide_cfg.
    rewrite <- EQidx.

    cbn; hvred.
    eapply eutt_clo_bind.
    (* We can now use the body hypothesis *)
    eapply HBODY.
    {
      (* A bit of arithmetic is needed to prove that we have the right precondition *)
      split.
      + eapply STABLE; cycle -1; [apply INV |..]; eauto. 
        intros; rewrite 3 alist_find_neq; eauto. 
       
      + rewrite alist_find_eq.
        reflexivity.
        typeclasses eauto.
    }

    (* Step 4 : Back to starting from loopcontblock and have reestablished everything at the next index:
        conclude by IH *)
    introR.
    destruct PRE as (LOOPVAR' & HS & IH').
    subst.
    replace k with (n - (S j)) by lia.
    eapply IH; try lia.
    split; auto.
    replace (S j - 1) with j by lia; auto.
    Unshelve.
    all: try auto.
Qed.

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

    (* Loopvar is unique. TODO: Fix, something is off here. *)
    (LVAR_FRESH' : forall str s s' id, incLocalNamed str s ≡ inr(s', id) -> loopvar ≢ id)

    (* Computation on the Helix side performed at each cell of the vector, *)
    (*        the counterpart to bodyV *)
    (bodyH: nat -> mem_block -> itree _ mem_block)

    (* Main relation preserved by iteration *)
    (R : Rel_cfg)

    (* Main relations preserved by iteration *)
    (I : nat -> mem_block -> Rel_cfg)

    (BASE : forall g l l' mV mH ymem _label _label',
        (conj_rel (I 0 ymem)
                  (fun _ '(_, (l, _)) => l @ loopvar ≡ Some (uvalue_of_nat 0))
                  mH (mV,(l',g))) ->
        eutt
          (succ_cfg (fun '(memH,vec') '(memV, (l, (g, x))) =>
                l @ loopvar ≡ Some (uvalue_of_nat 0) /\
                x ≡ inl (_label', loopcontblock) /\
                I 0 vec' memH (memV, (l, g))))
          (interp_helix (bodyH 0 ymem) mH)
          (interp_cfg
             (denote_bks (convert_typ [] body_blocks) (_label, body_entry)) g l mV)),

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

    (* R must be stable by extension of the local env *)
    (forall mH mV s s' g l id v str,
                            incLocalNamed str s ≡ inr (s', id) ->
                            R mH (mV, (l, g)) ->
                            R mH (mV, ((alist_add id v l), g))) ->

    (* TODO : use [sub_alist] ⊑ and match on loopvar *)
    (* Invariant is stable under extending local state *)
    (forall k mH mV s s' g l ymem id v str, incLocal s ≡ inr (s', id)
                                       \/ incLocalNamed str s ≡ inr (s', id)
                                       \/ id ≡ loopvar ->
                            I k ymem mH (mV, (l, g)) ->
                            I k ymem mH (mV, ((alist_add id v l), g))) ->

    (* R must entail the state invariant *)
    imp_rel R (state_invariant σ s1) ->

    (forall g l mV mH ymem,
        (R mH (mV, (l, g)) -> I 0 ymem mH (mV, (l, g)) /\ l @ loopvar ≡ Some (uvalue_of_nat 0)) /\
        (I (n - 1) ymem mH (mV, (l, g)) -> R mH (mV, (l, g)))) ->

    (* Main result. Need to know initially that R holds *)
    forall g l mV mH ymem _label,
      R mH (mV,(l,g)) ->
      eutt (succ_cfg
            (fun '(memH,vec') '(memV, (l, (g,x))) =>
                            (* Consider generalizing? *)
                          (x ≡ inl (loopcontblock, exit_id) \/
                          x ≡ inl (entry_id, exit_id)) /\
                          R memH (memV,(l,g))))

           (interp_helix (build_vec n bodyH ymem) mH)
           (interp_cfg (denote_bks (convert_typ [] bks) (_label ,entry_id)) g l mV).
Proof with rauto.
  (*
  intros * GEN * UNIQUE IN EXIT LVAR_FRESH * BASE IND STABLE STABLE' IMPSTATE IND_INV * PRE.
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
    eapply STABLE. Transparent incLocal. reflexivity. eauto.

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
      cbn; vstep; try solve_lu.
      erewrite <- arith_aux0. reflexivity. 
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
              b :: b1 :: (convert_typ nil body_blocks) ++ l0 ≡ [b; b1] ++ (convert_typ nil body_blocks) ++ l0).
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
    eapply BASE. edestruct IND_INV. apply H. eauto.

    intros. destruct u1. destruct u2 as (? & ?& ? &?).
    destruct p, s. 3 : inversion H. cbn in H. destruct p. destruct H as (LOOPVAR & ID & INV).
    inversion ID; subst.

    unfold build_vec_gen in GEN_IND.
    assert (forall j, S n - S j ≡ n - j) by lia.
    assert (n ≡ n - 0) by lia. rewrite H0. rewrite <- H.
    eapply eutt_Proper_mono.
    2 : {
      eapply GEN_IND.
      - eauto.
      - lia.
      - intros. eapply IND. apply H1.
      - intros. eapply STABLE'. apply H1. apply H2.
      - split; eauto.
    }

    repeat intro.
    repeat red. repeat red in H1. destruct x; try contradiction.
    destruct p. destruct y as (? & ? & ? & ?). destruct H1. split.
    left; auto. edestruct IND_INV. apply H4. apply H2.

    destruct H as (? & ? & ?). inversion H0.
    Unshelve. eauto.

Qed.
*)
Admitted.
