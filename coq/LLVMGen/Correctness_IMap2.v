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

From Vellvm Require Import Utils.Commutation.

Require Import Paco.paco.
From ITree Require Import HeterogeneousRelations.

Import ProofMode.

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

Section DSHIMap_is_tfor.

  (* Iterative body of [IMap] *)
  Definition DSHIMap_body
             (σ : evalContext)
             (f : AExpr)
             (offset : nat)
             (init acc : mem_block) : itree Event mem_block :=
    v <-
       lift_Derr (mem_lookup_err "Error reading memory denoteDSHIMap" offset init);;
    vn <- lift_Serr (MInt64asNT.from_nat offset);;
    v'<- denoteIUnCType σ f vn v;;
    ret (mem_add offset v' acc).


  (* | DSHIMap n x_p y_p f => *)
  (*   '(x,i) <- resolve_PVar x_p ;; *)
  (*   '(y,o) <- resolve_PVar y_p ;; *)
  (*   loopcontblock <- incBlockNamed "IMap_lcont" ;; *)
  (*   loopvar <- incLocalNamed "IMap_i" ;; *)
  (*   '(body_entry, body_blocks) <- genIMapBody i o x y f loopvar loopcontblock ;; *)
  (*   add_comment *)
  (*     (genWhileLoop "IMap" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n)) loopvar loopcontblock body_entry body_blocks [] nextblock) *)

  (* [tfor] formulation of [DSHIMap].
     "Reverse/downward" indexing ([n - 1 .. 0]). *)
  Definition DSHIMap_tfor_down
             (σ : evalContext)
             (f : AExpr)
             (i n e: nat)
             (init acc : mem_block):
    itree Event mem_block :=
    (* IMap has "reverse indexing" on its body *)
    tfor (fun i acc => DSHIMap_body σ f (e - 1 - i) init acc) i n acc.

  (* "Right"-side-up indexing variant ([0 .. n - 1]). *)
  Definition DSHIMap_tfor_up
             (σ : evalContext)
             (f : AExpr)
             (i n : nat)
             (init acc : mem_block):
    itree Event mem_block :=
    tfor (fun i acc => DSHIMap_body σ f i init acc) i n acc.

  (* [denoteDSHIMap] is equivalent to [tfor] with "reverse indexing" on an
     [IMap] body. *)
  Lemma denoteDSHIMap_as_tfor:
    forall (σ : evalContext) n f x y,
      denoteDSHIMap n f σ x y ≈ DSHIMap_tfor_down σ f 0 n n x y.
  Proof.
    intros.
    unfold DSHIMap_tfor_down. revert y.
    induction n.
    - cbn. intros.
      setoid_rewrite tfor_0.
      reflexivity.
    - intros.
      rewrite tfor_unroll; [| lia].
      assert (S n - 1 - 0 ≡ n) by lia. rewrite H. cbn.
      repeat setoid_rewrite bind_bind.
      cbn.
      eapply eutt_clo_bind; [reflexivity|].
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

  (* Lemma denoteDSHIMap_as_tfor: *)
  (*   forall (σ : evalContext) n x y f, *)
  (*     denoteDSHOperator σ (DSHIMap n x y f) ≈ DSHIMap_tfor_down σ f 0 n n x y. *)

  Lemma eq_rev :
    forall σ f n x y,
      DSHIMap_tfor_up σ f 0 n x y ≈ DSHIMap_tfor_down σ f 0 n n x y.
  Admitted.

  Lemma DSHIMap_interpreted_as_tfor:
    forall E σ (n : nat) (m : memoryH) f
      (init acc : mem_block),
      interp_helix (E := E) (denoteDSHIMap n f σ init acc) m ≈
      tfor (fun k x' =>
              match x' with
              | None => Ret None
              | Some (m', acc) => interp_helix (DSHIMap_body σ f k init acc) m'
              end)
        0 n (Some (m, acc)).
  Proof.
    intros.
    rewrite denoteDSHIMap_as_tfor.
    rewrite <- eq_rev.
    unfold DSHIMap_tfor_up.
    rewrite interp_helix_tfor; [|lia].
    cbn.
    apply eutt_tfor.
    intros [[m' acc']|] i; [| reflexivity].
    cbn.
    repeat rewrite interp_helix_bind.
    rewrite bind_bind.
    apply eutt_eq_bind; intros [[?m ?] |]; [| rewrite bind_ret_l; reflexivity].
    bind_ret_r2.
    apply eutt_eq_bind.
    intros [|]; reflexivity.
  Qed.


End DSHIMap_is_tfor.

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

Lemma DSHIMap_correct:
  ∀ (n : nat) (x_p y_p : PExpr) (f : AExpr) (s1 s2 : IRState) (σ : evalContext) (memH : memoryH) 
    (nextblock bid_in bid_from : block_id) (bks : list (LLVMAst.block typ)) (g : global_env) 
    (ρ : local_env) (memV : memoryV),
    genIR (DSHIMap n x_p y_p f) nextblock s1 ≡ inr (s2, (bid_in, bks))
    → bid_bound s1 nextblock
    → state_invariant σ s1 memH (memV, (ρ, g))
    → Gamma_safe σ s1 s2
    → no_failure (E := E_cfg) (interp_helix (denoteDSHOperator σ (DSHIMap n x_p y_p f)) memH)
    → eutt (succ_cfg (genIR_post σ s1 s2 nextblock ρ))
           (interp_helix (denoteDSHOperator σ (DSHIMap n x_p y_p f)) memH)
            (interp_cfg (denote_ocfg (convert_typ [] bks) (bid_from, bid_in)) g ρ memV).
Proof.
  intros n x_p y_p f s1 s2 σ memH nextblock bid_in bid_from bks g ρ memV GEN NEXT PRE GAM NOFAIL.
  Opaque genIMapBody.
  Opaque genAExpr.
  Opaque IntType.
  Opaque incLocalNamed.
  Opaque newLocalVar.

  pose proof generates_wf_ocfg_bids _ NEXT GEN as WFOCFG.
  pose proof inputs_bound_between _ _ _ GEN as INPUTS_BETWEEN.
  pose proof genIR_Γ _ _ _ GEN as GENIR_Γ.
  pose proof genIR_local_count _ _ _ GEN as GENIR_local.

  (* Clean up PVars *)
  cbn* in *; simp; cbn* in *.
  hide_cfg.
  inv_resolve_PVar Heqs1.
  inv_resolve_PVar Heqs2.
  unfold denotePExpr in *; cbn* in *.

  simp; try_abs.

  clean_goal.

  repeat apply no_failure_Ret in NOFAIL.
  edestruct @no_failure_helix_LU as (? & NOFAIL' & ?); eauto; []; clear NOFAIL; rename NOFAIL' into NOFAIL; cbn in NOFAIL; eauto.
  edestruct @no_failure_helix_LU as (? & NOFAIL' & ?); eauto; []; clear NOFAIL; rename NOFAIL' into NOFAIL; cbn in NOFAIL; eauto.
  clean_goal.

  hred.
  hstep; [eauto |].
  hred; hstep; [eauto |].
  hred.

  (* We know that the Helix denotation can be expressed via the [tfor] operator *)
  assert (NOFAIL_cont := NOFAIL).
  apply no_failure_helix_bind_prefix in NOFAIL.

  rewrite DSHIMap_interpreted_as_tfor.
  rewrite DSHIMap_interpreted_as_tfor in NOFAIL.

  match goal with
  | [H : genWhileLoop ?prefix' _ _ ?loopvar' ?loopcontblock' ?body_entry' ?body_blocks' _ ?nextblock' ?s1' ≡ inr (?s2', (?entry_id', ?bks')) |- _] =>
    remember prefix' as prefix
      ; rename loopvar' into loopvar
      ; rename loopcontblock' into loopcontblock
      ; rename body_entry' into body_entry
      ; rename body_blocks' into body_blocks
      ; rename nextblock' into nextblock_
      ; rename s1' into s1_
      ; rename s2' into s2_
      ; rename entry_id' into entry_id
      ; rename bks' into bks
  end.

  cbn* in *; simp; cbn in *.

  Transparent genIMapBody.
  pose proof @genWhileLoop_tfor_correct prefix loopvar loopcontblock body_entry body_blocks nextblock_ entry_id s1_ s2_ i s1_ bks as GENC.
  forward GENC; [clear GENC |].
  {

    clear -Heqs5.
    rename Heqs5 into GEN.
    Set Nested Proofs Allowed.

    Lemma genWhileLoop_entry_in_scope_IMap:
      ∀ (f : AExpr) (i0 : ident) (i1 : Int64.int) (i3 : ident) (i4 : Int64.int) (i6 : IRState) (loopcontblock : block_id) (loopvar : raw_id) 
        (body_entry : block_id) (body_blocks : list (LLVMAst.block typ)) (s1_ : IRState),
        genIMapBody i1 i4 i0 i3 f loopvar loopcontblock i6 ≡ inr (s1_, (body_entry, body_blocks)) → List.In body_entry (inputs body_blocks).
    Proof.
      induction f; intros *; try (cbn; intros GEN; clear -GEN; simp; cbn; auto; fail).
    Qed.

    eapply genWhileLoop_entry_in_scope_IMap; eauto.
  }

  forward GENC; [clear GENC |].
  eauto. subst.
  reflexivity.

  forward GENC; [clear GENC |].
  {
    eauto using wf_ocfg_bid_add_comment.
  }

  forward GENC; [clear GENC |].
  {
    eapply lid_bound_between_shrink; [eapply lid_bound_between_newLocalVar | | ]; eauto; try reflexivity; solve_local_count.
    subst.

    destruct u.
    eapply dropVars_local_count in Heqs7. rewrite Heqs7.
    eapply genIMapBody_local_count in Heqs5. apply Heqs5.
    (* TODO: solve_local_count doesn't work for dropVars properly? *)
  }

  forward GENC; [clear GENC |].
  {
    rewrite Forall_forall in INPUTS_BETWEEN. intros IN. subst.
    inv VG.
    rewrite inputs_convert_typ, add_comment_inputs in INPUTS_BETWEEN.
    apply INPUTS_BETWEEN in IN; clear INPUTS_BETWEEN.
    eapply not_bid_bound_between; eauto.
  }

  rename Heqs8 into WHILE.

  specialize (GENC n WHILE).
  match goal with
    |- context[tfor ?bod _ _ _] => specialize (GENC _ bod)
  end.

  forward GENC; [clear GENC |].
  {
    clear -Heqs.
    unfold MInt64asNT.from_nat in Heqs.
    unfold MInt64asNT.from_Z in Heqs.
    simp.
    apply l0.
  }

  (* Invariant at each iteration *)
  set (I := (fun (k : nat) (mH : option (memoryH * mem_block)) (stV : memoryV * (local_env * global_env)) =>
               match mH with
               | None => False
               | Some (mH, b) => state_invariant σ s2_ mH stV
               end)).
  (* Precondition and postcondition *)
  set (P := (fun (mH : option (memoryH * mem_block)) (stV : memoryV * (local_env * global_env)) =>
               match mH with
               | None => False
               | Some (mH,b) => state_invariant σ s2_ mH stV
               end)).

  specialize (GENC I P P (Some (memH, x0))).


  forward GENC; [clear GENC |].
  {
    subst I P; intros ? ? ? [[? []]|] * (INV & LOOPVAR & BOUNDk & RET); [| inv INV].

    assert (EQk: MInt64asNT.from_nat k ≡ inr (Int64.repr (Z.of_nat k))).
    {clear - BOUNDk Heqs.
     destruct (MInt64asNT.from_nat k) eqn:EQ.
     - exfalso.
       unfold MInt64asNT.from_nat in *.
       unfold MInt64asNT.from_Z in *.
       simp; lia.
     - unfold MInt64asNT.from_nat in *.
       apply from_Z_intval in EQ.
       rewrite EQ, repr_intval.
       reflexivity.
    }

    rewrite EQk in *.
    setoid_rewrite bind_ret_l.

    eapply no_failure_tfor in NOFAIL. 3 : eauto. 2 : lia. cbn in NOFAIL.
    rewrite interp_helix_bind in NOFAIL. rewrite EQk in NOFAIL.
    assert (NOFAIL' := NOFAIL).
    apply no_failure_bind_prefix in NOFAIL.

    simp; try_abs. clear NOFAIL.
    hvred.
    eapply no_failure_bind_cont in NOFAIL'; cycle 1.
    rewrite interp_helix_ret. constructor. cbn. reflexivity.
    cbn in NOFAIL'.

    Require Import Helix.LLVMGen.Correctness_AExpr.
    pose proof @genAExpr_correct.
    unfold denoteIUnCType.
    clear RET.

    Transparent genIMapBody. cbn in Heqs5. simp.
    rename Heqs10 into AEXP.

    match goal with
    | [ |- context[denoteAExpr ?σ f]] => remember σ as aσ
    end.


    destruct u, u1.
    eapply H1 in AEXP; clear H1; cycle 1.
    - eapply state_invariant_enter_scope_DSHCType; cycle 1.
      {
        cbn.

        clear WFOCFG INPUTS_BETWEEN NOFAIL'.
        clear NOFAIL_cont H H0 NEXT LOOPVAR EQk BOUNDk Heqo1.
        clear Heqs LUn EQsz LUn0 EQsz0 Heqo0 Heqo.

        solve_gamma.
      }

      3 : eapply state_invariant_enter_scope_DSHnat; eauto.
      3 : {
        intros abs. eapply in_Gamma_Gamma_eq in abs; [| eapply incBlockNamed_Γ ; eauto].
        eapply GAM; eauto.

        eapply lid_bound_between_newLocalVar in Heqs4.
        2:reflexivity.
        eapply lid_bound_between_shrink; eauto.
        solve_local_count.
        apply dropVars_local_count in Heqs7.

        apply genWhile_local_count in WHILE.
        clear WFOCFG INPUTS_BETWEEN NOFAIL_cont NOFAIL'.
        apply genAExpr_local_count in AEXP.
        cbn in AEXP.
        solve_local_count.
      }
      3 : {
        clear WFOCFG INPUTS_BETWEEN NOFAIL'.
        clear NOFAIL_cont H H0 NEXT LOOPVAR EQk BOUNDk Heqo1.
        clear Heqs LUn EQsz LUn0 EQsz0 Heqo0 Heqo.

        eapply state_invariant_Γ in GENIR_Γ; eauto.
        solve_state_invariant.
      }
      3 : { reflexivity. }
      solve_gamma.
      solve_gamma.
    - admit.
    - admit.
    - admit.
    - admit.
  }

  forward GENC; [clear GENC |].
  {
    subst I P; cbn.
    intros _ * BOUND INV; simp; auto.
    (* TODO 1 *)
    admit.
  }

  forward GENC; [clear GENC |].
  {
    admit.
  }

  forward GENC; [clear GENC |].
  {
    reflexivity.
  }

  forward GENC; [clear GENC |].
  {
    subst P I; red; intros; auto. 
  }

  forward GENC; [clear GENC |].
  {
    subst I P; red; intros; auto. 
  }

  specialize (GENC g ρ memV bid_from).
  eapply eutt_mon.
  {
    clear GENC NOFAIL INPUTS_BETWEEN WFOCFG;subst P I.
    intros [[? []] | ] (? & ? & ? & ?) *; cbn.
    split; [| split]; cbn; eauto; admit.
    - (* Need to enter scope,then escape it to link with s2 *)
      (* eapply state_invariant_Γ; eauto; admit. *)
      admit.
  }
  { subst P; cbn.
    clear -PRE.
    solve_state_invariant.
    admit.
  }
Admitted.

Section Swap.

  Definition pair_rel {A B} (RA : A -> A -> Prop) (RB : B -> B -> Prop) :=
    (fun '(a, b) '(a', b') => RA a a' /\ RB b b').

  (* < Desired Lemma > *)
  Lemma mem_block_equiv_is_order_independent :
    ∀ (n : nat) (init_vec : memoryH) x y σ f,
      eutt (E := void1) (Coqlib.option_rel (pair_rel (@eq memoryH) (@equiv mem_block _)))
        (interp_helix (DSHIMap_tfor_up σ f 0 n x y) init_vec)
        (interp_helix (DSHIMap_tfor_down σ f 0 n n x y) init_vec).
  Proof.
    intros *.
    unfold DSHIMap_tfor_up, DSHIMap_tfor_down.
  Admitted.

  Instance option_pair_rel_Equiv {A B} {R : A -> A -> Prop} {S : B -> B -> Prop}
           {EQR: Equivalence R} {EQS: Equivalence S}
    : Equivalence (Coqlib.option_rel (pair_rel R S)).
  Proof.
    split.
    - red; intros [ [] | ]; constructor; unfold pair_rel; split; reflexivity.
    - red; intros [ [] | ] [ [] | ] H; inv H ; constructor; unfold pair_rel in *.
      destruct H2 as []. split; symmetry; auto.
    - red; intros [ [] | ] [ [] | ] [ [] | ] H H'; inv H; inv H'; constructor;
        unfold pair_rel in *.
      destruct H2 as []; destruct H1 as []; split; etransitivity; eauto.
  Qed.

  Notation "⤉ ( R , S ) " := (Coqlib.option_rel (pair_rel R S)) (at level 10).

  Definition equiv_mem_block_frag (i n : nat) (m m' : mem_block) :=
    forall k, i <= k -> k < n -> find k m = find k m'.

  Definition equiv_mem_block (n : nat) (m m' : mem_block) :=
    equiv_mem_block_frag 0 n m m'.

  Instance option_pair_Equivalence: (Equivalence (⤉ (@eq memoryH, @equiv mem_block _))).
  Proof.
    intros. apply (@option_pair_rel_Equiv memoryH mem_block eq equiv _ mem_block_Equiv_Equivalence).
  Qed.

  Lemma imap_body_post:
    forall E m1 m2 init σ f i,
      no_failure (interp_helix (E := E) (DSHIMap_body σ f i init m2) m1) ->
    forall m0 b t0 b1,
      MInt64asNT.from_nat i ≡ inr t0 ->
      mem_lookup_err "Error reading memory denoteDSHIMap" i init ≡ inr b ->
      Returns (E := E) (Some (m0, b1)) (interp_helix (denoteIUnCType σ f t0 b) m1) ->
      Returns (Some (m0, mem_add i b1 m2)) (interp_helix (E := E) (DSHIMap_body σ f i init m2) m1).
  Proof.
    intros. cbn in *.
    assert (H' := H).
    apply no_failure_helix_bind_prefix in H.
    rewrite interp_helix_bind.
    unfold lift_Derr in H.

    destruct (mem_lookup_err "Error reading memory denoteDSHIMap" i init) eqn: MEM.

    try_abs.
    cbn. rewrite interp_helix_ret. cbn. rewrite bind_ret_l.


    eapply no_failure_helix_bind_continuation in H'.
    2 : {
      cbn. rewrite interp_helix_ret. constructor. cbn. reflexivity.
    }

    clear H.
    assert (H := H').
    eapply no_failure_helix_bind_prefix in H'.
    unfold lift_Serr in H'. destruct (MInt64asNT.from_nat i) eqn: HM. cbn in *.
    try_abs. cbn.
    rewrite interp_helix_bind; cbn. rewrite interp_helix_ret. cbn.
    rewrite bind_ret_l.
    rewrite interp_helix_bind.

    eapply no_failure_helix_bind_continuation in H.
    2 : {
      cbn. rewrite interp_helix_ret. constructor. cbn. reflexivity.
    }


    inv H0. inv H1.
    eapply no_failure_helix_bind_prefix in H.
    red in H.
    eapply Returns_bind. apply H2. cbn. rewrite interp_helix_ret. cbn. constructor. reflexivity.
  Qed.

  (* < Generalized Lemma > Equivalent to Desired lemma when i = 0 *)
  Lemma swap_ind:
    ∀ n i : nat,
      (∀ (memH : memoryH) (σ : evalContext) (f : AExpr) (init : mem_block),
          eutt (E := void1) (⤉ (eq, equiv))
            (interp_helix (vec <- tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f i0 init acc) 0 i init;;
              tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f (n - 1 - i0) init acc) 0 (n - i) vec) memH)
            (interp_helix (vec <- tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f (S i - 1 - i0) init acc) 0 i init;;
              tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f i0 init acc) (S i) n vec) memH))
      → ∀ (memH : memoryH) (σ : evalContext) (f : AExpr) (init : mem_block),
        0 < S i
        → S i < n
        -> no_failure (E := void1) (interp_helix (vec <- tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f i0 init acc) 0 (S i) init;;
                                tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f (n - 1 - i0) init acc) 0 (n - S i) vec) memH)
        → eutt (E := void1) (⤉ (eq, equiv_mem_block n))
          (interp_helix (vec <- tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f i0 init acc) 0 (S i) init;;
          tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f (n - 1 - i0) init acc) 0 (n - S i) vec) memH)
          (interp_helix (vec <- tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f (S (S i) - 1 - i0) init acc) 0 (S i) init;;
            tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f i0 init acc) (S (S i)) n vec) memH).
  Proof.
    intros n i IHi memH σ f init LO HI NOFAIL.
    Opaque DSHIMap_body.
    assert (EQ: S (S i) - 1 ≡ S i) by lia; rewrite EQ; clear EQ.

      setoid_rewrite tfor_split with (j := i) at 1; try lia.

      assert (
        SWAP_LHS:
          eutt (E := void1) (⤉ (eq, equiv_mem_block n))

            (interp_helix (vec <- (tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f i0 init acc) 0 i init) ;;
                           vec <- (tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f i0 init acc) i (S i) vec) ;;
                            tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f (n - 1 - i0) init acc) 0 (n - S i) vec) memH)

            (interp_helix (vec <- (tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f i0 init acc) 0 i init) ;;
                           (tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f (n - 1 - i0) init acc) 0 (n - i) vec)) memH)). {
        intros; setoid_rewrite interp_helix_bind.
        eapply eutt_clo_bind. reflexivity.

        intros [[] |] [[]|] EQ; inv EQ.
        2 : { apply eqit_Ret; constructor. }
        setoid_rewrite tfor_split with (j := n - S i) at 2; try lia.
        cbn.

        assert (
           H: tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f (n - 1 - i0) init acc) (n - S i) (n - i) m2 ≈
                 tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f i0 init acc) i (S i) m2). {
          rewrite tfor_unroll. 2 : lia.
          assert (EQ : S (n - S i) ≡ n - i) by lia; rewrite EQ; clear EQ.
          assert (EQ : n - 1 - (n - S i) ≡ i) by lia; rewrite EQ; clear EQ.
          setoid_rewrite tfor_0. rewrite bind_ret_r. rewrite tfor_unroll; try lia.
          setoid_rewrite tfor_0. rewrite bind_ret_r.
          reflexivity.
        }

        setoid_rewrite <- H; clear H.

        rewrite interp_helix_bind.

        assert (forall m m2, eutt (E := void1) eq
              (interp_helix (tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f (n - 1 - i0) init acc) (n - S i) (n - i) m2) m)
              (interp_helix (DSHIMap_body σ f i init m2) m)). {
          intros.
          rewrite tfor_unroll.
          assert (EQ : n - 1 - (n - S i) ≡ i) by lia; rewrite EQ; clear EQ.
          assert (EQ : S (n - S i) ≡ n - i) by lia; rewrite EQ; clear EQ.
          setoid_rewrite tfor_0. rewrite bind_ret_r. reflexivity. lia.
        }

        setoid_rewrite H.
        match goal with
        | [ |- _ ?R ] => remember R as RHS
        end.
        assert (RHS ≈
          interp_helix (vec <- tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f (n - 1 - i0) init acc) 0 (n - S i) m2;;
                        (DSHIMap_body σ f i init vec)) m1). {
          subst. setoid_rewrite interp_helix_bind.
          eapply eutt_clo_bind. reflexivity.

          intros [[] |] [[] |] EQ; inv EQ. 2 : reflexivity.
          apply H.
        }
        rewrite H0. clear H0 HeqRHS H RHS.

        setoid_rewrite interp_helix_bind.
        eapply eqit_mon; auto.

        Unshelve.
        3 : exact (⤉ (eq, (fun x y => equiv_mem_block_frag i (S i) x y /\ equiv_mem_block_frag (S i) n x y))).
        {
          intros [[] |] [[] |] EQ; inv EQ. inv H1.
          2 : constructor.
          constructor. cbn. split; auto.
          destruct H0.
          Set Nested Proofs Allowed.

          Lemma equiv_mem_block_split:
            forall i j k m m',
              i <= j -> S j <= k ->
              equiv_mem_block_frag i (S j) m m' /\ equiv_mem_block_frag (S j) k m m' ->
              equiv_mem_block k m m'.
          Proof.
            unfold equiv_mem_block, equiv_mem_block_frag; intros * B B' []. intros.

            destruct (k0 <=? S j) eqn: EQ.
            apply H. rewrite Nat.leb_le in EQ.
          Admitted.
          admit.
        }


        (* match goal with *)
        (* | [ |- eutt _ (ITree.bind ?pre ?post) (ITree.bind ?pre' ?post') ] => *)
        (*     remember pre as PRE ; remember post as POST; *)
        (*     remember pre' as PRE' ; remember post' as POST' *)
        (* end. *)

        (* eapply commut_gen'.  *)
        (*     (Q1 := fun x => Returns x PRE) *)
        (*     (Q2 := fun x => Returns x PRE'). *)
        (* - admit. *)
        (* - admit. *)
        (* - rewrite has_post_post_strong. eapply eutt_Returns_. eauto. *)
        (* - rewrite has_post_post_strong. eapply eutt_Returns_. eauto. *)
        (* - intros. rewrite has_post_post_strong. eapply eutt_Returns_. *)
        (*   intros [[] |] EQ. subst. *)
        (*   destruct a as [[] |]. *)

        (*   intros. *)
        (* - admit. *)
        (* - admit. *)

      (* setoid_rewrite bind_bind. *)
      (* rewrite SWAP_LHS; clear SWAP_LHS. *)
      (* rewrite IHi; try lia. clear IHi. *)

      (* assert (EQ : S i - 1 ≡ i) by lia; rewrite EQ; clear EQ. *)
      (* setoid_rewrite tfor_unroll at 2. *)

      (* assert (EQ : S i - 0 ≡ S i) by lia; rewrite EQ; clear EQ. *)

      (* assert ( *)
      (*   SWAP_LHS: *)
      (*     eutt (E := void1) eq *)
      (*          (interp_helix *)
      (*             (vec <- DSHIMap_body σ f (S i) init init;; *)
      (*               tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f (S i - i0) init acc) 1 (S i) vec ) memH) *)
      (*          (interp_helix *)
      (*               (vec <- tfor (λ (i0 : nat) (acc : mem_block), DSHIMap_body σ f (S i - i0) init acc) 1 (S i) init ;; *)
      (*                DSHIMap_body σ f (S i) init vec) memH)). { *)
      (*   setoid_rewrite interp_helix_bind. *)
      (*   eapply commut_gen; admit. *)
      (* } *)
      (* all : try lia. *)

      (* setoid_rewrite interp_helix_bind at 2. *)
      (* rewrite SWAP_LHS; clear SWAP_LHS. *)
      (* rewrite <- interp_helix_bind. *)
      (* rewrite tfor_ss_dep. *)
      (* all : try lia. *)
      (* 2 : { Unshelve. 4 : exact (fun n mem_bl => DSHIMap_body σ f (i - n) init mem_bl). intros; reflexivity. shelve. shelve. } *)
      (* setoid_rewrite bind_bind. *)
      (* setoid_rewrite interp_helix_bind. *)
      (* eapply eutt_clo_bind. reflexivity. *)

      (* intros [[] |] [[] |] EQ; inv EQ. 2 : reflexivity. *)
      (* rewrite tfor_split with (j := (S (S i))); try lia. *)
      (* rewrite tfor_unroll. setoid_rewrite tfor_0. *)
      (* rewrite bind_ret_r. reflexivity. lia. *)
      (* Unshelve. *)

  Admitted.
End Swap.
