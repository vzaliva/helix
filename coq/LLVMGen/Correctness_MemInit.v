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
Require Import Helix.LLVMGen.StateCounters.

From Helix Require Import MSigmaHCOL.MemSetoid.

Set Implicit Arguments.
Set Strict Implicit.

Opaque dropVars.
Opaque newLocalVar.
Opaque resolve_PVar.
Opaque incBlockNamed.
Opaque incVoid.
Opaque incLocal.
Opaque genWhileLoop.

Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope nat_scope.

(* The result is a branch *)
Definition branches {T : Type} (to : block_id) (mh : memoryH * T) (c : config_cfg_T (block_id * block_id + uvalue)) : Prop :=
  match c with
  | (m,(l,(g,res))) => exists from, res ≡ inl (from, to)
  end.

Definition genIR_post {T} (σ : evalContext) (s1 s2 : IRState) (to : block_id) (li : local_env)
  : Rel_cfg_T T ((block_id * block_id) + uvalue) :=
  lift_Rel_cfg (state_invariant σ s2) ⩕
               branches to ⩕
               (fun sthf stvf => local_scope_modif s1 s2 li (fst (snd stvf))).

(* One step unrolling of the combinator *)
Lemma tfor_unroll_right: forall {E A} i j (body : nat -> A -> itree E A) a0,
    i <= j ->
    tfor body i (S j) a0 ≈
         a <- tfor body i j a0;; body j a.
Proof.
  intros * ineq.
  rewrite tfor_split; eauto.
  apply eutt_eq_bind; intros.
  rewrite tfor_unroll; [| lia].
  bind_ret_r2.
  apply eutt_eq_bind; intros.
  rewrite tfor_0; reflexivity.
Qed.

Lemma mem_union_tfor :
  forall i value x,
    eutt equiv (Ret (mem_union (mem_const_block i value) x))
        (tfor (E := Event) (fun k x => Ret (mem_add k value x)) 0 i x).
Proof.
  intros i value.
  induction i as [| i IH].
  - intros; cbn.
    rewrite tfor_0. apply eqit_Ret.
    apply mem_union_mem_empty.
  - intros; cbn.
    rewrite tfor_unroll_right; [| lia].
    unfold equiv.
    etransitivity; cycle 1.
    { eapply eutt_clo_bind. eapply IH.
      intros. apply eqit_Ret.
      eapply mem_add_proper.
      1, 2 : reflexivity. exact H. }
    rewrite bind_ret_l. apply eqit_Ret.
    apply mem_union_mem_add_commut.
Qed.

Lemma mem_union_tfor_interp i value x memH:
  eutt equiv
       (interp_helix (E := E_cfg) (Ret (mem_union (mem_const_block i value) x)) memH)
        (interp_helix (tfor (E := Event) (fun k x => Ret (mem_add k value x)) 0 i x) memH).
Proof.
  rewrite interp_helix_ret. revert x memH.
  induction i as [| i IH].
  - intros; cbn.
    rewrite tfor_0. rewrite interp_helix_ret.
    apply eqit_Ret. f_equiv.
    constructor; cbn; [ | apply mem_union_mem_empty].
    apply NM_Equiv_Reflexive.
  - intros; cbn.
    rewrite tfor_unroll_right; [| lia].
    unfold equiv.
    etransitivity; cycle 1.
    { setoid_rewrite interp_helix_bind. eapply eutt_clo_bind. eapply IH.
      intros. destruct u1, u2; inv H.
      - destruct p, p0. setoid_rewrite interp_helix_ret. inv H2; cbn in *.
        Unshelve.
        2 : { intros. destruct x0. destruct p.
              exact (Ret (Some (m, mem_add i value m0))).
              exact (Ret None). }
        apply eqit_Ret. do 2 constructor; eauto. cbn.
        eapply mem_add_proper; eauto.
     - apply eqit_Ret. reflexivity. }
    cbn. setoid_rewrite bind_ret_l. apply eqit_Ret.
    do 2 constructor; [ apply NM_Equiv_Reflexive | apply mem_union_mem_add_commut].
Qed.

Opaque dropVars.
Opaque newLocalVar.
Opaque resolve_PVar.
Opaque incLocalNamed.
Opaque incBlockNamed.
Opaque incVoid.
Opaque incLocal.
Opaque genWhileLoop.

Definition memory_invariant_partial_write' (configV : config_cfg) (index loopsize : nat) (ptr_llvm : addr)
            (bk_helix : mem_block) (x : ident) sz : Prop :=
    let '(mem_llvm, (ρ, g)) := configV in
    dtyp_fits mem_llvm ptr_llvm (typ_to_dtyp [] (TYPE_Array sz TYPE_Double)) /\
    in_local_or_global_addr ρ g x ptr_llvm /\
            (∀ (i : Int64.int) (v0 : binary64),
                (MInt64asNT.to_nat i) < index \/ (MInt64asNT.to_nat i) >= loopsize ->
                  (mem_lookup (MInt64asNT.to_nat i) bk_helix ≡ Some v0
                    → get_array_cell mem_llvm ptr_llvm (MInt64asNT.to_nat i) DTYPE_Double ≡ inr (UVALUE_Double v0))).

Instance state_invariant_memory_equiv_Proper σ s a :
  Proper (equiv ==> flip impl) (fun m => state_invariant σ s m a).
Admitted.

(* TODO: Move to [Correctness_Invariants] *)
Lemma state_invariant_cons :
  forall a x s' s σ mH mV l g,
    s <<= s' ->
    x :: Γ s' ≡ Γ s ->
    state_invariant (a :: σ) s mH (mV, (l, g)) ->
    state_invariant σ s' mH (mV, (l, g)).
Proof.
  intros * LT GAM INV.
  destruct INV.
  unfold memory_invariant, WF_IRState, no_id_aliasing, no_dshptr_aliasing, no_llvm_ptr_aliasing, id_allocated in *.
  rewrite <- GAM in *.
  cbn in *.
  split; eauto; red; repeat intro.
  - intros. specialize (mem_is_inv (S n)).
    cbn in *.
    specialize (mem_is_inv _ _ _ _ H H0). destruct v; eauto.
  - red in IRState_is_WF. specialize (IRState_is_WF v (S n)).
    cbn in *. eauto.
  - assert ((S n2) ≡ (S n1) -> n2 ≡ n1) by lia. apply H3.
    eapply st_no_id_aliasing; eauto.
  - assert ((S n') ≡ (S n) -> n' ≡ n) by lia. apply H1.
    eapply st_no_dshptr_aliasing; eauto.
  - red in st_no_llvm_ptr_aliasing.
    specialize (st_no_llvm_ptr_aliasing id1 ptrv1 id2 ptrv2 (S n1) (S n2)).
    cbn in *. rewrite <- GAM in *. revert H6. eapply st_no_llvm_ptr_aliasing;eauto.
  - specialize (st_id_allocated (S n)). cbn in *. eauto.
  - unfold gamma_bound in st_gamma_bound.
    eapply state_bound_mono.
    eapply st_gamma_bound.
    2: solve_local_count.
    rewrite <- GAM.
    rewrite nth_error_Sn.
    eauto.
Qed.

Lemma MemInit_Correct:
  ∀ (y_p : PExpr) (value : binary64) (s1 s2 : IRState) (σ : evalContext) 
    (memH : memoryH) (nextblock bid_in bid_from : block_id) (bks : list (LLVMAst.block typ)) 
    (g : global_env) (ρ : local_env) (memV : memoryV),
    genIR (DSHMemInit y_p value) nextblock s1 ≡ inr (s2, (bid_in, bks))
    → bid_bound s1 nextblock
    → state_invariant σ s1 memH (memV, (ρ, g))
    → Gamma_safe σ s1 s2
    → no_failure (E := E_cfg) (interp_helix (denoteDSHOperator σ (DSHMemInit y_p value)) memH)
    → eutt (succ_cfg (genIR_post σ s1 s2 nextblock ρ))
           (interp_helix (denoteDSHOperator σ (DSHMemInit y_p value)) memH)
           (interp_cfg (denote_ocfg (convert_typ [] bks) (bid_from, bid_in)) g ρ memV).
Proof.
  intros y_p value s1 s2 σ memH nextblock bid_in bid_from bks g ρ memV GEN NEXT PRE GAM NOFAIL.

  pose proof generates_wf_ocfg_bids _ NEXT GEN as WFOCFG.
  pose proof inputs_bound_between _ _ _ GEN as INPUTS_BETWEEN.
  pose proof genIR_Γ _ _ _ GEN as GENIR_Γ.
  pose proof genIR_local_count _ _ _ GEN as GENIR_local.

  (* Clean up PVars *)
  cbn* in *; simp; cbn* in *.
  inv_resolve_PVar Heqs0.
  unfold denotePExpr in *; cbn* in *.

  (* Renaming *)
  rename i1 into size, r into pt, b into init_block_id, b0 into loopcontblock,
    r0 into loopvar, i7 into storeid.

  simp; try_abs.

  (* Clean up [no_failure] *)
  apply no_failure_Ret in NOFAIL.
  edestruct @no_failure_helix_LU as (? & NOFAIL' & ?); eauto; []; clear NOFAIL; rename NOFAIL' into NOFAIL; cbn in NOFAIL; eauto.
  hred.
  hstep; eauto.
  hred.

  rename x into mem_bkH.

  (* The computation is now reduced to a single writing event, but of a vector built atomically.
     On the Vellvm side, each cell of this vector must be written 1 by 1: we hence rephrase this in terms of a [tfor].
   *)
  match goal with
  |- context[interp_helix ?t _] => 
  cut (x <- Ret (mem_union (mem_const_block (MInt64asNT.to_nat i) value) mem_bkH);; trigger (MemSet n0 x) ≈ t); [| cbn; rewrite bind_ret_l; reflexivity];
  intros EQ; rewrite <- EQ; clear EQ
  end.
  cbn; rewrite interp_helix_bind.

  clean_goal.

  (* STEP 2:
    We now change the VIR semantics: not much to do. *)
  rewrite add_comment_eutt.
  bind_ret_r2.

  (* STEP 3:
    Memory invariant *)
  pose proof state_invariant_memory_invariant PRE as MINV_XOFF.
  unfold memory_invariant in MINV_XOFF.
  specialize (MINV_XOFF _ _ _ _ _ Heqo LUn). cbn in MINV_XOFF.
  destruct MINV_XOFF as (ptrll_xoff & τ_xoff & TEQ_xoff & FITS_xoff & INLG_xoff & bkh_xoff & MLUP_xoff & GETARRAYCELL_xoff); eauto.

  (* Duplicating, as we need to do the same inside the loop body *)
  assert (H' := H).
  rewrite MLUP_xoff in H; symmetry in H; inv H.

  inv TEQ_xoff. cbn.

 (* We need to settle on the relation that holds at the end of the loops.
     It is not quite [state_invariant]: on the helix side, the memory has not been touched,
     we performed a pure computation.
     On the Vellvm side, we are done, everything is written in memory. *)
  eapply eutt_clo_bind with (UU := succ_cfg (genIR_post σ s1 s2 nextblock ρ)).
  {
    match type of Heqs1 with
      | genWhileLoop ?a _ _ ?b ?c ?d ?e _ ?f _ ≡ inr (_,(?g,?h)) =>
        set (prefix := a); set (body_blocks := e);
          rename d into body_entry, f into nextblock, g into entry_id, h into bks
    end.

    clean_goal.

    rename s1 into s0, i6 into s1, i4 into sb1, i5 into sb2.
    pose proof
         @genWhileLoop_tfor_correct prefix loopvar loopcontblock body_entry body_blocks
         nextblock entry_id s1 s2 sb1 sb2 bks as LOOP.
    forward LOOP.
    { subst body_blocks; cbn; auto. }

    forward LOOP.
    { subst prefix; reflexivity. }

    forward LOOP.
    { eauto using wf_ocfg_bid_add_comment. }

    forward LOOP; [clear LOOP |].
    { solve_lid_bound_between. }

    assert (EQ: Z.of_nat (BinNat.N.to_nat sz) ≡ Int64.intval size). {
      clear -EQsz.
      rewrite Znat.N_nat_Z.
      unfold MInt64asNT.from_N in EQsz.
      apply from_Z_intval in EQsz; auto.
    }

    forward LOOP; [clear LOOP |].
    { clear -INPUTS_BETWEEN NEXT.
      intros IN; rewrite inputs_convert_typ, add_comment_inputs in INPUTS_BETWEEN.
      rewrite Forall_forall in INPUTS_BETWEEN; apply INPUTS_BETWEEN in IN; clear INPUTS_BETWEEN.
      eapply not_bid_bound_between; eauto. }

    specialize (LOOP (BinNat.N.to_nat sz)).
    rename Heqs1 into WHILE.

   forward LOOP; [clear LOOP |].
   { subst body_blocks prefix.
     rewrite EQ.
      exact WHILE. }

    eapply eutt_Proper_mono; cycle 1.
    eapply eqit_trans.
    { eapply mem_union_tfor_interp. }
    { rewrite interp_helix_tfor; [| lia].
      match goal with
        |- context[tfor ?bod] =>
        specialize (LOOP _ bod)
      end.

    forward LOOP; [clear LOOP |].
    { rewrite EQ.
      edestruct Int64.intrange; eauto. }

    rename i0 into y.

    set (I := (fun (k : nat) (mH : option (memoryH * mem_block)) (stV : memoryV * (local_env * global_env)) =>
                match mH with
                | None => False
                | Some (mH,bkH) =>
                let '(mV, (ρ, g')) := stV in
                (* 1. Relaxed state invariant *)
                state_invariant (protect σ n) s0 mH stV /\
                (* 2. Preserved state invariant *)
                memory_invariant_partial_write' stV k n ptrll_xoff bkH y sz /\
                mH ≡ memH /\ g ≡ g' /\
                allocated ptrll_xoff mV
                end)).

    set (P := fun o stV =>
                match o with
                | None => False
                | Some (mH,bkH) => bkH ≡ bkh_xoff /\ state_invariant (protect σ n) s0 mH stV /\
                      let '(mV, (p, g')) := stV in
                          mH ≡ memH /\ g ≡ g' /\ mV ≡ memV /\ ρ ≡ p
                end).

    set (Q := fun o stV =>
                match o with
                | None => False
                | Some (mH,bkH) =>
                    state_invariant σ s2 (memory_set mH n0 bkH) stV /\
                      let '(mV, (p, g')) := stV in
                      mH ≡ memH /\ g ≡ g'
                end).

    specialize (LOOP I P Q (Some (memH,bkh_xoff))).

    forward LOOP.
    {
      (* Relating bodies *) clear LOOP.
      intros ? ? ? [[? ?]|] * (INV & LOOPVAR & BOUNDk & RET); [| inv INV].
      hred.

      rewrite denote_ocfg_unfold_in.
      2: apply find_block_eq; auto.

      cbn; vred. Transparent IntType. cbn.

      rewrite denote_no_phis.
      vred; cbn.

      rewrite denote_code_cons.
      (* Get mem information from PRE condition here (global and local state has changed). *)
      (* Needed for the following GEP and Load instructions *)
      destruct INV as (INV_r & INV_p & -> & -> & ?).
      apply nth_error_protect_eq' in Heqo; auto.

      unfold memory_invariant_partial_write' in INV_p.
      destruct INV_p as (FITS_yoff_l & INLG_YOFF & MINV_YOFF).

      (* [Vellvm] GEP Instruction for [x] *)
      match goal with
      | [|- context[OP_GetElementPtr (DTYPE_Array ?size' ?τ') (_, ?ptr') _]] =>
        edestruct denote_instr_gep_array_no_read with
            (l := li) (g := g0) (m := mV) (i := pt)
            (size := size') (a := ptrll_xoff) (ptr := ptr') as (GEP_addr & Hread & EQ_HG)
      end.
      { destruct y; rename id into YID.
        - (* y is ID_Global *)
          rewrite denote_exp_GR; [ | eauto ].
          cbn. subst. reflexivity.
        - (* y is ID_Local *)
          rewrite denote_exp_LR; [ | eauto ].
          cbn. subst. reflexivity. }
      { rewrite denote_exp_LR. reflexivity. eauto. }
      { typ_to_dtyp_simplify.
        erewrite <- from_N_intval; eauto. }

      (* [Vellvm] Reduce GEP *)
      vred.
      setoid_rewrite EQ_HG; clear EQ_HG.
      vred. vred.

      (* [Vellvm] STORE instruction : initialize with default value for [GEP_Addr] *)
      edestruct write_succeeds with (m1 := mV) (a := GEP_addr); [eapply DVALUE_Double_typ |..].
      { typ_to_dtyp_simplify.

        eapply dtyp_fits_array_elem; [ | eauto | ].
        { erewrite <- from_N_intval; eauto. }
        { rewrite Int64.unsigned_repr; try lia.
          split; [lia |].
          clear - BOUNDk EQ.
          apply f_equal with (f:=Z.to_nat) in EQ.
          rewrite Znat.Nat2Z.id in EQ.
          rewrite EQ in BOUNDk; clear - BOUNDk.
          pose proof Int64.intrange size as [LO HI].
          apply Znat.Z2Nat.inj_lt in HI; try lia.
          unfold Int64.max_unsigned.
          lia.
        } }
        
      vred.
      rewrite denote_instr_store; eauto; cycle 1.
      { rewrite denote_exp_double; reflexivity. }
      { eapply denote_exp_LR.
        solve_alist_in. }
      { constructor. }

      vred.
      rewrite denote_term_br_1.
      vred.

      cbn.
      (* Not in body any more *)
      rewrite denote_ocfg_unfold_not_in.
      vred.
      2: { rewrite find_block_ineq; eauto. cbn. solve_id_neq. }

      (* Re-establish INV in post condition *)
      apply eqit_Ret.
      split; [|split; [|split]]; eauto.
      solve_alist_in.

      unfold I.
      split; [|split; [|split; [|split]]]; eauto.

      (* Establish the relaxed state invariant with changed states and extended
        local environment *)
      { revert INV_r; intros INV_r.
        rename H0 into H_write.
        eapply state_invariant_same_Γ with (s1 := s0);
          [ eauto | solve_local_count | solve_not_in_gamma | ].

        (* The state invariant is preserved by a single write on [H_write] and
         adding the [GEP_addr] into the local list. *)
        destruct INV_r.
        constructor; eauto.
        repeat intro.

        specialize (mem_is_inv _ _ _ _ _ H0 H1).

        (* Is it written to? *)
        destruct (Nat.eq_dec n1 n) eqn : IS_IT_THE_WRITTEN_ADDRESS ; subst.
        { (* Yes *)
          rewrite Heqo in H0; inv H0.
          rewrite LUn in H1; inv H1.
          edestruct mem_is_inv as (? & ? & ? & ? & ? & ?); clear mem_is_inv.

          eexists _,_. repeat (split; eauto).
          eapply dtyp_fits_after_write; eauto.
          intros ABS; inv ABS. }
        { (* No *)
          revert LUn Heqo. intros.
          rename
            H0 into Heqo',
            H1 into LUn'.
          assert (x0 ≢ y). {
            intro. subst. apply n2.
            eapply st_no_id_aliasing; eauto.
          }

          destruct v.
          { (* natVal *)
            destruct x0; eauto.
            cbn; destruct mem_is_inv as (?&?&?&?&?).
            eexists x0, x1; split; [ eauto | split; [ eauto | ]].
            assert (no_overlap_dtyp GEP_addr DTYPE_Double x0 (typ_to_dtyp [] x1)) as NOALIAS. {
              (* The dtyp does not overlap! *)
              unfold no_overlap_dtyp, no_overlap.
              left. rewrite <- (handle_gep_addr_array_same_block _ _ _ _ Hread).

              intros BLOCKS; symmetry in BLOCKS; revert BLOCKS.

              do 2 red in st_no_llvm_ptr_aliasing.
              eapply st_no_llvm_ptr_aliasing. 5 : exact H0. 5,6: eauto. 3: eauto.
              all : eauto. }
            erewrite write_untouched; eauto. constructor. }
          { (* CTypeVal *)
            destruct x0; eauto.
            cbn; destruct mem_is_inv as (?&?&?&?&?).
            eexists x0, x1; split; [ eauto | split; [ eauto | ]].
            assert (no_overlap_dtyp GEP_addr DTYPE_Double x0 (typ_to_dtyp [] x1)) as NOALIAS. {
              (* The dtyp does not overlap! *)
              unfold no_overlap_dtyp, no_overlap.
              left. rewrite <- (handle_gep_addr_array_same_block _ _ _ _ Hread).

              intros BLOCKS; symmetry in BLOCKS; revert BLOCKS.

              do 2 red in st_no_llvm_ptr_aliasing.
              eapply st_no_llvm_ptr_aliasing. 5 : exact H0. 5,6: eauto. 3: eauto.
              all : eauto. }
            erewrite write_untouched; eauto. constructor. }
          { (* PtrVal *)
            clean_goal.
            edestruct mem_is_inv as (? & ? & ? & ? & ? & ?); clear mem_is_inv.
            eexists _,_; repeat (split; eauto).
            eapply dtyp_fits_after_write; eauto.

            (* no write on pointer *)
            intros. specialize (H4 H5).

            destruct H4 as (?&?&?). eexists. split; eauto.
            intros. specialize (H6 _ _ H7).
            erewrite write_untouched_ptr_block_get_array_cell.
            2: eauto. 2 : eauto.

            eauto.

            assert (fst ptrll_xoff ≡ fst GEP_addr). {
              revert Hread; intros.
              unfold handle_gep_addr in Hread.
              destruct ptrll_xoff. cbn in Hread. inv Hread. cbn. auto.
            }

            rewrite <- H8; eauto.
          }
        }
      }

      (* Partial memory up to (S k) *)
      { unfold memory_invariant_partial_write'.
        split; [ | split  ].
        { eapply dtyp_fits_after_write; eauto. }
        { destruct y.
          - eapply in_local_or_global_addr_same_global; eauto.
          - cbn; intros; eauto. solve_alist_in. }
        { intros * Bounds_sz MLU_i0.
          revert MINV_YOFF; intros.

          (* Written index? *)
          destruct (Nat.eq_dec (MInt64asNT.to_nat i0) k) eqn: IS_IT_THE_WRITTEN_ADDRESS.
          { (*Yes*)
            subst.
            rewrite mem_lookup_mem_add_eq in MLU_i0. inv MLU_i0.
            erewrite <- read_array.
            pose proof @write_read as WR.
            assert (is_supported DTYPE_Double). constructor.
            specialize (WR _ _ DTYPE_Double  _ _ H1 H0).
            cbn in WR. eapply WR. constructor. solve_allocated.
            eauto. }
          { (*No*)
            (* This wasn't written to, and is covered by the partial memory
              invariant up to this point. *)
              specialize (MINV_YOFF i0 v0).
              erewrite write_array_cell_untouched.
              + eapply MINV_YOFF; [eauto|].
                destruct Bounds_sz.
                rewrite mem_lookup_mem_add_neq in MLU_i0; try lia; eauto.
                eauto.
                rewrite mem_lookup_mem_add_neq in MLU_i0; try lia; eauto.
              + erewrite <- write_array_lemma. eauto. solve_allocated. eauto.
              + constructor.
              + repeat rewrite Int64.unsigned_repr; try lia.
                *
                  clear.
                  unfold MInt64asNT.to_nat, Int64.max_unsigned.
                  pose proof Int64.intrange i0 as [LO HI].
                  rewrite Znat.Z2Nat.id; lia.
                *
                  split; [lia |].
                  clear - BOUNDk EQ.
                  apply f_equal with (f:=Z.to_nat) in EQ.
                  rewrite Znat.Nat2Z.id in EQ.
                  rewrite EQ in BOUNDk; clear - BOUNDk.
                  pose proof Int64.intrange size as [LO HI].
                  apply Znat.Z2Nat.inj_lt in HI; try lia.
                  unfold Int64.max_unsigned.
                  lia.
          }
          } }

      { solve_allocated. }

      { (* local_scope_modif *)
        (* not true *)
        admit. }
    }

    forward LOOP; [clear LOOP|]; eauto.
    {
      subst I.
      intros * Hl INV; eauto. cbn in *.
      destruct a; eauto.
      destruct p.
      destruct INV as (?&?&?&?&?).
      destruct H0 as (?&?&?).

      split; eauto.
      2 : repeat (split; eauto).
      - eapply state_invariant_same_Γ; eauto.

        destruct Hl.
        + eapply not_in_gamma_protect. eapply GAM.
          eapply lid_bound_between_shrink; eauto.
          solve_local_count.
        + eapply not_in_gamma_protect. eapply GAM.
          eapply lid_bound_between_shrink; eauto;
          solve_local_count.
      - destruct y.
        + eapply in_local_or_global_addr_same_global; eauto.
        + cbn; intros. repeat red in H4.
          setoid_rewrite alist_find_neq; eauto.
          admit. (* not in alist *)
    }

    forward LOOP; [solve_local_count|].
    forward LOOP; [solve_local_count|].

    forward LOOP; [clear LOOP |].
    {
      subst I P; red; intros; auto. destruct a; eauto.
      destruct p; eauto. destruct b; eauto. destruct p; eauto.
      intuition. subst.
      destruct H.
      cbn.
      unfold memory_invariant in mem_is_inv.
      apply nth_error_protect_eq' in Heqo.
      specialize (mem_is_inv _ _ _ _ _ Heqo LUn).
      cbn in mem_is_inv.
      edestruct mem_is_inv as (?  & ? & ? & ? & ? & ?). inv H.
      split; eauto. eauto. subst. solve_allocated.
    }

    forward LOOP; [clear LOOP |].
    {
      (* (I i -> Q) *)
      subst Q I.
      red; intros.
      break_match_goal; auto.
      destruct p. destruct b, p.
      destruct H as (?&?&?&?&?). split; eauto.
      destruct H0 as (?&?&?).
      destruct H.

      split; eauto; cycle 1.
      eapply WF_IRState_protect, WF_IRState_Γ; eauto.
      eapply no_id_aliasing_protect, no_id_aliasing_gamma; eauto.
      eapply no_dshptr_aliasing_protect; eauto.
      eapply no_llvm_ptr_aliasing_protect, no_llvm_ptr_aliasing_gamma; eauto.

      (* id's are still well-allocated. *)
      {
        red in st_id_allocated. red. intros.
        destruct (@dec_eq_nat n1 n). subst.
        rewrite Heqo in H. inv H.
        apply mem_block_exists_memory_set_eq. reflexivity.
        apply mem_block_exists_memory_set. eapply st_id_allocated.
        eapply nth_error_protect_ineq in H. 2 : eauto.
        eauto.
      }

      eapply gamma_bound_mono; eauto.

      cbn in *. intros.
      rename H0 into FITS, H4 into INLG, H5 into MLU.
      (* Two possible cases : either the index isn't with the pointer location,
        which is where we can use the normal memory invariant [mem_is_inv].
        Ohterwise, we can show that the [partial memory write] is complete
        and use [MLU] to restate the memory lookup. *)
      destruct (Nat.eq_dec n1 n); cycle 1.
      {
        (* Case 1 : The address in question was not written to : use normal memory
          invariant. *)
        subst. eapply nth_error_protect_ineq in H7; eauto.
        specialize (mem_is_inv _ _ _ _ _ Heqo LUn). destruct v0; eauto.
        destruct mem_is_inv as (ptrll & τ' & TEQ & FITS' & INLG' & MLUP).
        inv TEQ. eexists. eexists.
        split; eauto. split; eauto. split; eauto.
        intros.
        specialize (MLUP H0).
        destruct MLUP as (bkh & MLU_ & MLU__).
        exists bkh.
        assert (a0 ≢ y_h_ptr). {
          intro. apply n3.
          red in st_no_dshptr_aliasing.
          pose proof Heqo0.
          eapply nth_error_protect_eq' in H4.
          eapply st_no_dshptr_aliasing; eauto. subst. eauto.
        }
        split.
        pose proof memory_lookup_memory_set_neq.
        cbn in H4. erewrite H4. eauto.
        eauto.
        intros.
        eauto.
      }
      {
        (* Case 2 : The address in question is definitely written to, and the
        complete partial memory invariant ensures that we have the right cells. *)
        subst.
        rewrite <- GENIR_Γ in H1.
        rewrite LUn0 in H1.
        inv H1. rewrite Heqo0 in H. inv H.

        clear mem_is_inv.
        eexists. eexists. split; eauto. split; eauto.
        split; eauto. intros. eexists.
        split.
        pose proof memory_lookup_memory_set_eq. cbn in H0.
        eapply H0.
        intros. eapply MLU. 2 : eauto.

        revert BOUNDS; intro.
        lia.
    }

    assert (BinNat.N.to_nat sz ≡ MInt64asNT.to_nat i). admit.
    rewrite H in LOOP.

    eapply LOOP.
    {
      subst P I. clear LOOP.
      cbn. split; [|split]; eauto.
      apply state_invariant_protect.
      eapply state_invariant_Γ. eauto.
      solve_gamma. solve_local_count. }
    }

    red. intros [[? ?] | ] (? & ? & ? & ?); [| cbn in *; intuition].
    2 : { destruct H. inv REL1. inv REL2. inv H0. auto. }
    intros [? ? ?]; eauto. inv REL1.
    destruct REL2 as (?&?&?).
    repeat red.
    split; [| split]; cbn; eauto.
    - destruct b; eauto. destruct H1 as (? & ? & ? & ?); subst.
      cbn in *. inv H0. cbn in *. (*Properness lemma*)
      eapply state_invariant_memory_equiv_Proper; eauto.
    - destruct H; eauto.
    - solve_local_scope_modif.
  }

  intros. destruct u1; cycle 1.
  { apply eutt_Ret; eauto. }
  destruct p.
  setoid_rewrite interp_helix_MemSet.
  destruct H as (H1 & H2 & H3).

  apply eutt_Ret.
  split; [| split]; cbn; auto.

  destruct u2, p, p. destruct H1.

  split; eauto.

  (* Need to transport information about what has been written on the Vellvm side during the loop *)
  - Opaque memory_set.
    cbn; intros * LU1 LU2.
    eapply mem_is_inv in LU2; eauto.
    destruct v; auto.
    destruct LU2 as (? & ? & ? & ? & ? & ?).
    destruct (n0 =? a) eqn:EQ.
    * apply beq_nat_true in EQ; subst.
      do 2 eexists.
      split; [reflexivity |].
      do 2 (split; eauto).  intros.
      specialize (H4 H). destruct H4 as (?&?&?). exists x2; eauto.
      rewrite memory_lookup_memory_set_eq; eexists. f_equiv.

      rename m0 into MEM_, x2 into MEM__. red in H2.
      admit.
      intros; eapply H5; eauto.
    * rewrite memory_lookup_memory_set_neq; [| apply NPeano.Nat.eqb_neq in EQ; auto].
      do 2 eexists ; eauto.
  - eapply id_allocated_memory_set; eauto.
Admitted.
