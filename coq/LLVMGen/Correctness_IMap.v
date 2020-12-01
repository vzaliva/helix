Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.
Require Import Helix.LLVMGen.Correctness_MExpr.
Require Import Helix.LLVMGen.Correctness_AExpr.
Require Import Helix.LLVMGen.Correctness_While.
Require Import Helix.LLVMGen.IdLemmas.
Require Import Helix.LLVMGen.StateCounters.
Require Import Helix.LLVMGen.VariableBinding.
Require Import Helix.LLVMGen.BidBound.


Require Import Helix.LLVMGen.Correctness_GenIR.
Set Nested Proofs Allowed.

Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

Set Implicit Arguments.
Set Strict Implicit.

Global Opaque resolve_PVar.

Import ProofMode.


(* IY: Defining this as a Definition here, because we want the opacity in the
    later parts of this proof. *)
Definition IMAP_BODYH σ x f :=
  let FN :=
  (λ (x : mem_block) (σ : evalContext) (n' : nat) (mem_bl : Memory.NM.t binary64),
        ` H : binary64 <- lift_Derr (mem_lookup_err "Error reading memory denoteDSHIMap" n' x);;
        ` H0 : MInt64asNT.t <- lift_Serr (MInt64asNT.from_nat n');;
        ` H1 : binary64 <- denoteIUnCType σ f H0 H;; Ret (mem_add n' H1 mem_bl)) in
  (fun n mem_bl=> FN x σ n%nat mem_bl).
Opaque IMAP_BODYH.


Lemma denoteDSHIMap_eq_build_vec:
  ∀ (n : nat) (f : AExpr) (σ : evalContext) (memH : memoryH) (x x0 : mem_block),
  @eqit (CallE +' PickE +' UBE +' DebugE +' FailureE) (option (memoryH * mem_block))
    (option (memoryH * mem_block)) (@Logic.eq (option (memoryH * mem_block))) true true
    (interp_helix (denoteDSHIMap n f σ x x0) memH)
    (interp_helix (build_vec n (λ (m : nat) (mem_bl : Memory.NM.t binary64),
                                IMAP_BODYH σ x f (n - m - 1) mem_bl) x0) memH).
Proof.
  intros n f σ memH x x0.

  unfold denoteDSHIMap, build_vec, build_vec_gen, build_vec_gen_aux.
  assert (H1 : (n ≡ n - 0)%nat) by lia. rewrite <- H1. clear H1.
  subst.

  revert memH x x0 σ.

  induction n.
  - cbn. reflexivity.
  - setoid_rewrite <- bind_bind. setoid_rewrite <- bind_bind.

    cbn. intros *.

    rewrite interp_helix_bind.
    setoid_rewrite  interp_helix_bind at 2.

    eapply eutt_clo_bind.
    Unshelve.
    3 : {
      intros.

      refine (
          match X, X0 with
          | Some (x_memH, x_memb), Some (x0_memH, x0_memb) =>
              x_memH ≡ x0_memH /\ mem_add n x_memb x0 ≡ x0_memb
          | None, None => True
          | _, _ => False
          end
        ).
    }
    cbn.

    {
      Transparent IMAP_BODYH.
      subst. cbn.
      rewrite 2 interp_helix_bind.
      rewrite Nat.sub_0_r.
      eapply eutt_clo_bind.
      reflexivity.
      intros [ [memH0 bin0] | ]  [ [memH0' bin0'] | ] EQ0 ; inversion EQ0; subst.
      rewrite 2 interp_helix_bind.
      eapply eutt_clo_bind.
      reflexivity.

      intros [ [memH1 binH1] | ] [ [memH1' bin1'] | ] EQ1; inversion EQ1; subst.
      rewrite interp_helix_bind.
      rewrite <- bind_ret_r at 1.
      eapply eutt_clo_bind. reflexivity.

      intros [ [memH2 bin2] | ] [ [memH2' bin2'] | ] EQ2; inversion EQ2; subst.
      rewrite interp_helix_ret. cbn.
      apply eutt_Ret. split; cbn; try rewrite <- H; try reflexivity.
      apply eutt_Ret; try inversion H. auto.
      apply eutt_Ret. auto.
      apply eutt_Ret. auto.
    }

    (* Bind continuation case of DSHIMap and build_vec equality *)
    {
      intros [ [memH0 memBl0] | ] [ [memH0' memBl0'] | ] EQ0 ; inversion EQ0.

      rewrite IHn.
      Opaque IMAP_BODYH.
      cbn.

      subst. remember (mem_add n memBl0 x0).
      clear Heqt.
      clear.

      (* Finnicky nat handling for the induction to work. *)
      remember 0%nat in * at 1.
      rewrite <- Heqn0 at 1.
      assert ( H: (n ≡ n + n0)%nat) by lia.
      rewrite H. rewrite <- H at 1. rewrite <- H at 1.
      clear Heqn0 H.

      revert n0 memH0' t.

      induction n; [reflexivity | ].
      intros; rewrite 2 interp_helix_bind.

      eapply eutt_clo_bind_returns. reflexivity.
      intros [ [memH memBl] | ] [ [memH' memBl'] | ] A RetH RetH'; inversion A ; [ | reflexivity ].
      subst.

      assert (EQV': (S n + n0)%nat ≡ (n + (S n0))%nat) by lia.
      rewrite EQV'. apply IHn.
      reflexivity.
    }
Qed.



(* TODO: Move to Vellvm/ITree *)

Lemma no_failure_has_post_some :
  forall E X (t : itree E (option X)), no_failure t -> has_post t (fun x => exists x', x ≡ Some x').
Proof.
  intros.
  eapply has_post_eutt. reflexivity. 2 : apply H.
  red. intros. split; intro. destruct H0. intro. subst. inversion H1.
  red in H0. destruct a. exists x. reflexivity.
  exfalso. apply H0. reflexivity.
Qed.

Lemma no_failure_bind :
  forall E X Y (t : itree E (option X)) (k : option X -> itree E (option Y)),
    (forall u, no_failure (k (Some u))) ->
    no_failure t -> no_failure (ITree.bind t k).
Proof.
  intros. apply no_failure_has_post_some in H0.
  eapply eutt_post_bind. apply H0.
  intros. destruct H1. subst. apply H.
Qed.

(* TODO: Use above lemmas to prove this. *)
Lemma no_failure_index :
  ∀ (n : nat) (f : AExpr) (σ : evalContext) (x : mem_block) (memH : memoryH) (ymem : mem_block)
    (NOFAIL : @no_failure E_cfg (memory * mem_block) (interp_helix (denoteDSHIMap (S n) f σ x ymem) memH)),
    @no_failure E_cfg (memory * mem_block) (interp_helix (IMAP_BODYH σ x f n ymem) memH).
Proof.
  intros.
  revert n f σ x memH ymem NOFAIL.
  intros.
  cbn* in *.
  setoid_rewrite <- bind_bind in NOFAIL.
  setoid_rewrite <- bind_bind in NOFAIL.
  eapply no_failure_helix_bind_prefix in NOFAIL.
  unfold no_failure.
  rewrite has_post_post_strong.
  red. Transparent IMAP_BODYH. cbn. Opaque IMAP_BODYH.
  vstep. rewrite interp_helix_bind. cbn.

  eapply eutt_clo_bind_returns.
  - cbn.
    eapply no_failure_helix_bind_prefix in NOFAIL.
    red in NOFAIL. rewrite has_post_post_strong in NOFAIL.
    red in NOFAIL.
    eapply NOFAIL.
  - intros [ [memH' bin']| ] [ [memH'' bin'' ]|] (EQ & S) R1 R2; inversion EQ; subst.
    2 : apply eqit_Ret; eauto.
    inversion EQ; subst.
    eapply no_failure_helix_bind_continuation in NOFAIL; eauto.

    rewrite interp_helix_bind.
    eapply eutt_clo_bind_returns.
    eapply no_failure_helix_bind_prefix in NOFAIL.
    red in NOFAIL. rewrite has_post_post_strong in NOFAIL.
    red in NOFAIL.
    apply NOFAIL.

    cbn* in *.

    intros [ [memH1' bin1']| ] [ [memH1'' bin1'' ]|] (EQ1 & S1) R11 R12; inversion EQ1; subst.
    2 : apply eqit_Ret; eauto.
    eapply no_failure_helix_bind_continuation in NOFAIL; eauto.

    rewrite interp_helix_bind.
    eapply eutt_clo_bind_returns.
    red in NOFAIL. rewrite has_post_post_strong in NOFAIL.
    red in NOFAIL. apply NOFAIL.

    intros [ [memH2' bin2']| ] [ [memH2'' bin2'' ]|] (EQ2 & S2) R21 R22; inversion EQ2; subst.
    2 : apply eqit_Ret; eauto.
    inversion EQ2; subst.
    rewrite interp_helix_ret.
    apply eqit_Ret. split; eauto. intro. inversion H.
Qed.

Require Import Paco.paco.


(* Not necessarily true. (counterexample : diverging itrees) *)
(* Lemma has_post_some_returns : *)
(*   forall E X (t : itree E (option X)), has_post t (fun x => exists x', x ≡ Some x') -> exists x', Returns (Some x') t. *)
(* Proof. *)
(* Admitted. *)

Lemma no_failure_map_succ:
  forall n f σ x ymem memH
    s1 s2 e c l g memV
  (GEN: genAExpr f s1 ≡ inr (s2, (e, c)))
  (STATE: forall b t, state_invariant (DSHCTypeVal b :: DSHnatVal t :: σ) s1 memH (memV, (l, g))),
  @no_failure E_cfg (memoryH * mem_block) (interp_helix (denoteDSHIMap (S n) f σ x ymem) memH) ->
  forall ymem',
    @Returns E_cfg _ (Some (memH, ymem'))
             (interp_helix (IMAP_BODYH σ x f n ymem) memH) ->
    @no_failure E_cfg (memoryH * mem_block) (interp_helix (denoteDSHIMap n f σ x ymem') memH).
Proof.
  intros.

  Transparent IMAP_BODYH.
  rename H0 into RET_H.
  unfold IMAP_BODYH in RET_H.
  Opaque IMAP_BODYH.

  cbn* in *.
  unfold denoteDSHIMap in *.
  assert (NOFAIL := H).
  eapply no_failure_helix_bind_prefix in H.
  unfold lift_Derr, mem_lookup_err.

  setoid_rewrite interp_helix_bind in RET_H.
  eapply Returns_bind_inversion in RET_H  as ([[ mh' b' ]| ] & RET_PRE & RET_H).
  2 : {
    apply Returns_Ret in RET_H. inversion RET_H.
  }

  Ltac try_throw_abs :=
      repeat match goal with
      | [ H: Returns (Some _) (interp_helix (ITree.bind (throw _) _ ) _) |- _ ] => abs_by Returns_helix_throw'
      | [ H: no_failure (interp_helix (ITree.bind (throw _ ) _ ) _) |- _ ] => abs_by failure_helix_throw'
      | [ H: Returns (Some _) (interp_helix (throw _) _) |- _ ] => abs_by Returns_helix_throw
      | [ H: no_failure (interp_helix (throw _ ) _ ) |- _ ] => abs_by failure_helix_throw
          end.

  simp; try_throw_abs.
  eapply no_failure_helix_bind_continuation in NOFAIL.
  (* abs_by failure_helix_throw'. *)
  2 : {rewrite interp_helix_ret. cbn. constructor. reflexivity. }

  eapply no_failure_helix_bind_continuation in NOFAIL.
  2 : { constructor. rewrite interp_helix_ret. cbn. reflexivity. }

  setoid_rewrite interp_helix_bind in RET_H.
  setoid_rewrite interp_helix_ret in RET_H.
  setoid_rewrite bind_ret_l in RET_H. setoid_rewrite interp_helix_bind in RET_H.
  eapply Returns_bind_inversion in RET_H  as ([[ mh'' b'' ]| ] & RET_PRE' & RET_H').
  2 : {
    apply Returns_Ret in RET_H'. inversion RET_H'.
  }

  setoid_rewrite interp_helix_ret in RET_H'. eapply Returns_Ret in RET_H'. inversion RET_H'; subst.

  eapply no_failure_helix_bind_continuation in NOFAIL.
  setoid_rewrite interp_helix_ret in RET_PRE.
  eapply Returns_Ret in RET_PRE. inversion RET_PRE; subst.

  2 : {
    rewrite interp_helix_ret in RET_PRE. apply Returns_Ret in RET_PRE. inversion RET_PRE; subst.
    apply RET_PRE'.
  }
  apply NOFAIL.
Qed.

(* Lemma no_failure_index_dec : *)
(*   forall (n: nat) f σ x memH ymem *)
(*     (NOFAIL : @no_failure E_cfg (memoryH * mem_block) (interp_helix (denoteDSHIMap (S n) f σ x ymem) memH)), *)
(*     forall s1 s2 e c memV l g *)
(*     (STATE : ∀ (b : binary64) (t : Int64.int), state_invariant (DSHCTypeVal b :: DSHnatVal t :: σ) s1 memH (memV, (l, g))) *)
(*     (GEN: genAExpr f s1 ≡ inr (s2, (e, c))), *)
(*     forall (i : nat) (BOUND : (n > i)%nat), *)
(*       exists ymem', *)
(*         (* TODO: Same as above. *) *)
(*     @no_failure E_cfg (memoryH * mem_block) (interp_helix (IMAP_BODYH σ x f (n - i) ymem') memH). *)
(* Proof. *)
(*   intros. *)
(*   revert n ymem NOFAIL BOUND. *)
(*   induction i. *)
(*   - cbn. intros. *)
(*     rewrite Nat.sub_0_r. *)
(*     exists ymem. *)
(*     apply no_failure_index. apply NOFAIL. *)
(*   - cbn. intros. *)
(*     assert (n - S i ≡ (n - 1) - i)%nat by lia. *)
(*     rewrite H. *)
(*     edestruct no_failure_map_succ as (? & ?). *)
(*     apply GEN. intros; apply STATE. apply NOFAIL. *)
(*     edestruct IHi as (? & ?). *)
(*     3 : { exists x1. apply H1. } 2 : lia. *)
(*     assert (S (n - 1) ≡ n) by lia. rewrite H1. apply H0. *)
(* Qed. *)

Opaque incBlockNamed.
Opaque incVoid.
Opaque incLocal.

(* DSHIMap case for [compile_FSHCOL_correct]. *)
Lemma compile_DSHIMap_correct:
  ∀ (n : nat)
    (x_p y_p : PExpr)
    (f : AExpr)
    (s1 s2 : IRState)
    (σ : evalContext)
    (memH : memoryH)
    (nextblock bid_in bid_from : block_id)
    (bks : list (LLVMAst.block typ))
    (g : global_env)
    (ρ : local_env)
    (memV : memoryV)
    (NEXT : bid_bound s1 nextblock)
    (STATE : state_invariant σ s1 memH (memV, (ρ, g)))
    (GAM: Gamma_safe σ s1 s2)
    (NOFAIL : @no_failure E_cfg (memoryH * ())
                          (interp_helix (denoteDSHOperator σ (DSHIMap n x_p y_p f)) memH))
    (GEN : genIR (DSHIMap n x_p y_p f) nextblock s1 ≡ inr (s2, (bid_in, bks)))

    (* Added constraints related to bounds-checking / freshness*)
    (OVERFLOW : Z.of_nat n < Integers.Int64.modulus),

    eutt (succ_cfg (genIR_post σ s1 s2 nextblock ρ))
         (interp_helix (denoteDSHOperator σ (DSHIMap n x_p y_p f)) memH)
         (interp_cfg (denote_bks (convert_typ [] bks) (bid_from, bid_in)) g ρ memV).
Proof.
  intros.

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

  (* Duplicate work as genMExpr_correct, needed for GEP later. *)
  edestruct memory_invariant_Ptr as (bkH & ptrV & Mem_LU & LUV & EQ); eauto.
  hvred. hstep. solve_lu.
  hvred.
  edestruct (@memory_invariant_Ptr _ σ _ _ _ _ _ _ _ _ _ STATE Heqo0 LUn0)
    as (bkH' & ptrV' & Mem_LU' & LUV' & EQ'); eauto.
  hvred. hstep. solve_lu.

  eutt_hide_right.
  repeat apply no_failure_Ret in NOFAIL.
  repeat (edestruct @no_failure_helix_LU as (? & NOFAIL' & ?); eauto; [];
          clear NOFAIL; rename NOFAIL' into NOFAIL; cbn in NOFAIL; eauto).


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
  cbn in *.
  (* rewrite add_comment_eutt. *)
  subst.

  (* Gather information from AExpr correctness *)
  (* denoting [f] *)
  (* pose proof @genAExpr_correct as AEXPR_INV. *)
  (* specialize (AEXPR_INV _ _ _ σ memH _ _ g ρ memV Heqs10). *)

  match goal with
  | [ H : context [genWhileLoop msg _ _ _ _ _ ?body _ _ ?s] |-_] => remember body as body_blocks;
                                                                    remember s as s1'
  end.

  remember (fun x σ n' mem_bl =>
      ` H : binary64 <- lift_Derr (mem_lookup_err "Error reading memory denoteDSHIMap" n' x);;
      ` H0 : MInt64asNT.t <- lift_Serr (MInt64asNT.from_nat n');;
      ` H1 : binary64 <- denoteIUnCType σ f H0 H;; Ret (mem_add n' H1 mem_bl)) as FN.

(* Needs to be revisited with respect to all the changes to the invariants. Let's first sovle completely the Loop operator
  

  pose proof @genWhileLoop_correct as GEN_W.
  assert (IN: In b0 (block_ids body_blocks)). {
    subst. unfold block_ids. rewrite map_cons. cbn. left. reflexivity.
  }

  assert (UNIQUE: blk_id_norepet l0). {
    (* Well-formedness condition needed as assumption in this lemma. *)
    admit.
  }

  assert (FRESH: fresh_in_cfg l0 nextblock). {
    (* Ditto (UNIQUE). Maybe we can get this from no_failure..? *)
    admit.
  }
  specialize (GEN_W _ _ _ _ _ _ _ _ s2 _ IN UNIQUE FRESH n Heqs4).

  (* Defining BODY_H *)
  clear HeqFN.

  remember (fun m mem_bl => IMAP_BODYH σ bkH f (n - m - 1)%nat mem_bl) as BODY.

  (* GEN_W gets a BODY *)
  specialize (GEN_W BODY OVERFLOW).

  (* Defining Indexed Invariant (I : nat -> mem_block -> Rel_cfg) and stable
      state invariant (R : Rel_cfg)*)
  (* TODO: Tweak to change with "mem_bl" and "m"*)
  (* Do we want state_invariant here, or Gen_IR *)
  (* Can retrieve*)
  (* State/GenIR Invariant *)
  remember (fun (m : nat) (mem_bl : mem_block) memH '(memV_, (l_, g_)) =>
              state_invariant σ s1 memH (memV_, (l_, g_))) as INV.

  (* Indexed Invariant *)
  remember (fun memH '(memV_, (l_, g_)) => forall mem_bl,
    state_invariant σ s2 (memory_set memH a0 mem_bl) (memV_, (l_, g_))) as R.

  (* GEN_W also gets an INV and R *)
  specialize (GEN_W INV R).

  match goal with
  | [ |- eutt _ _ ?RHS] => remember RHS
  end .

  assert (i ≈ ITree.bind' (fun x => Ret x) i). rewrite bind_ret_r. reflexivity.

  rewrite H1. clear H1.

  eapply eutt_clo_bind_returns.
  rewrite Heqi.

  eapply eutt_Proper_R. 2, 3: reflexivity.
  eapply rcompose_eq_l.

  eapply eqit_trans.

  (* Apply genWhileLoop_correct top lemma *)
  2 : eapply GEN_W; clear GEN_W.

  (* denoteDSHIMap is equivalent to some IMap expression. *)
  rewrite HeqBODY.
  apply denoteDSHIMap_eq_build_vec.

  (* Equate the rest of the continuation with each other (Trivial Ret continuations) *)
  7 : {
    intros.
    destruct u1. destruct p1.
    rewrite interp_helix_MemSet. apply eutt_Ret.
    cbn. cbn in H1. destruct u2. destruct p1. destruct p1.
    destruct H1.

    clear GEN_W.
    2 : destruct H1.
    red. Unshelve.

    subst.
    split. red. apply H4. red. destruct H1. exists b; auto. exists bid_in; auto.
  }

  (* Integer bound
      TODO: Is it necessary to assume this bound as part of this lemma? *)
  2: auto.

  (* Prove body hypothesis (body blocks is equal to one iteration of IMAP_BODYH) *)
  (* TODO : Add assumption in genWhile_correct that BODYH holds true only when n > 0. *)
  {
    intros.
    assert (n > 0)%nat. admit.
    Transparent IMAP_BODYH. unfold IMAP_BODYH.
    subst.

    eapply no_failure_helix_bind_prefix in NOFAIL.

    rename H1 into INV.

    match goal with
    | [ |- eutt ?R _ _ ] => remember R as POST
    end.

    destruct INV as (STATE_INV & LOOPVAR).
    (* destruct STATE_INV. *)
    (* pose proof no_failure_index_dec as NF. *)
    (* destruct n; [inversion H2 |]. *)
    (* (* specialize (NF _ _ _ _ _ _ NOFAIL). *) *)
 
    (* cbn* in *. *)
    (* vjmp. hvred. *)

    (* unfold denote_phis. *)
    (* cbn. *)
    (* hvred. vred. *)

    (* rename Heqs4 into GEN. *)
    (* rename i1 into ptr. *)

    (* [vstep] does not handle gep currently *)

    cbn.

    (* apply  *)

    (* Get information about pointer access through mem_lookup not failing *)

  (*   eapply no_failure_helix_bind_prefix in NOFAIL. *)

  (*   unfold denoteDSHIMap in NOFAIL. *)
  (*   cbn* in *; inv_eqs. *)
  (*   hvred. *)
  (*   simp. *)

  (*   (* What to do when n is 0? Should we assume that [no_failure BODY], instead? *) *)
  (*   (* TODO Lemma: no_failure on fixpoint should imply that each iteration of *)
  (*      the loop (or for any indexing i < n) should not fail. *) *)

  (*   cbn in NOFAIL. *)
  (*   eapply no_failure_helix_bind_prefix in NOFAIL. *)
  (*   cbn* in *; inv_eqs. *)
  (*   (* Clean up *) *)
  (*   clear UNIQUE FRESH IN. *)
  (*   simp. (* Something is wrong here: NOFAIL *) *)
  (*   (* unfold throw in NOFAIL. *) *)

  (*   (* inversion NOFAIL. *) *)
  (*   red in NOFAIL.  *)
  (*   simp. try_abs. *)
  (*   hvred. *)
  (*   cbn* in *; simp. *)


  (*   (* TODO *) *)


  (*   hvred. *)
  (*   vstep. *)
  (*   hvred. *)
  (*   symmetry. *)

  (*   (* TODO: GEP *) *)
  (*   { *)
  (*     edestruct denote_instr_gep_array as (? & READ & EQ_); eauto. *)
  (*     2 : { *)
  (*       eapply LU_ARRAY; eauto. *)
  (*       apply Memory.NM.find_1. apply H1. apply m.  *)
  (*       apply find_some in mem_lookup_H. *)
  (*       unfold Memory.NM.In in IN_MAP. *)
  (*         in mem_lookup_H. *)
  (*       cbn i *)
  (*       apply *)
  (*       Unshelve. *)

  (*       apply H0. *)

  (*     3 : apply LOOKUP_H; eauto. *)

  (*     4 : { *)
  (*       rewrite EQ.  *)
  (*       cbn in EQ. rewrite <- EQ. setoid_rewrite EQ.  *)
  (*       rewrite EQ.  *)
  (*       vred. tep.  *)
  (*     } *)

  (*     shelve. *)
  (*   } *)

  (*   hvred. vstep. *)
  (*   { *)

  (*   } *)

  (*   (* Looking up memory : PROBLEM AREA !! *) *)
  (*   (* edestruct denote_instr_gep_array as (? & READ & EQ)shelve. *) *)
  (*   (* TODO: Indexed Invariant should reference mem *) *)

  (*   (* hvred. *) *)
  (*   (* eapply eutt_clo_bind_returns. *) *)
  (*   vstep. *)
  (*   (* edestruct denote_instr_gep_array as (? & READ & EQ); shelve. *) *)
  (*   shelve. shelve. *)

  (*   (* intros. destruct u1, u2. destruct p1, p2. destruct p1. *) *)
  (*   (* hvred. *) *)

  (*   (* shelve. shelve. *) *)
  (* } *)

  (* { *)
  (*   intros. subst. shelve. *)
  (*   (* destruct H6 as [ | [| [|] ]] ; subst; admit. *) *)
  (* } *)

  (* (* Imp_rel state invariant *) *)
  (* 2 : { *)
  (*   subst. repeat intro. destruct b1. destruct p1. admit. *)
  (* } *)

  (* (* Stability condition *) *)
  (* { *)
  (*   intros. subst. intros. *)
  (*   red in H1. *)
  (*   pose proof @memory_invariant_ext_local. *)
  (*   red in H3. *)
  (*   admit. *)
  (* } *)

  (* { *)
  (*   (* subst. intros. split. intros. split; eauto. red in STATE. *) *)
  (*   shelve. *)
  (* } *)

  (* { *)
  (*   subst. red in STATE. intros. *)
  (*   (* TODO: The mem_block should be instantiated concretely. *) *)
  (*   intros. shelve. *)
    (* } *)

    *)
Admitted.

