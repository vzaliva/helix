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


  Lemma DSHIMap_as_tfor : forall σ n x y f,
      denoteDSHOperator σ (DSHIMap n x y f) ≈
      '(x_i, _) <- denotePExpr σ x;;
      '(y_i, y_size) <- denotePExpr σ y;;
        _ <- lift_Serr (assert_nat_neq "DSHIMap 'x' must not be equal 'y'" x_i y_i);;
       x2 <- trigger (MemLU "Error looking up 'x' in DSHIMap" x_i);;
       y0 <- trigger (MemLU "Error looking up 'y' in DSHIMap" y_i);;
       v <- lift_Derr (assert_nat_lt "DSHIMap 'n' index out of bounds" n (MInt64asNT.to_nat y_size));;
       y' <- DSHIMap_tfor_up (protect_p σ y) f 0 n x2 y0 ;;
        trigger (MemSet y_i y').
  Proof.
    intros.
    unfold denoteDSHOperator.
    cbn.
    repeat (eapply eutt_clo_bind; [reflexivity|intros; try break_match_goal; subst]).
    setoid_rewrite denoteDSHIMap_as_tfor.

    rewrite eq_rev.
    reflexivity.
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

Import AlistNotations.

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
  unfold denotePExpr in *; cbn* in *.

  (* Clean up w/ renaming *)
  rename i12 into storeid.
  rename r0 into px.
  rename r1 into py.
  rename r2 into v.
  destruct_unit.
  rename e into fexpr.
  rename c into fexpcode.

  rename i1 into x.
  rename r into loopvarid.
  rename i4 into y.
  rename i2 into xp_typ_.
  rename i5 into yp_typ_.


  destruct_unit.
  simp; try_abs.

  clean_goal. destruct_unit.

  (* Clean up [no_failure] *)
  repeat apply no_failure_Ret in NOFAIL.
  destruct (assert_nat_neq "DSHIMap 'x' must not be equal 'y'" n3 n2) eqn : XNEQY; try_abs.

  repeat apply no_failure_Ret in NOFAIL.
  edestruct @no_failure_helix_LU as (? & NOFAIL' & ?); eauto; []; clear NOFAIL; rename NOFAIL' into NOFAIL; cbn in NOFAIL; eauto.
  edestruct @no_failure_helix_LU as (? & NOFAIL' & ?); eauto; []; clear NOFAIL; rename NOFAIL' into NOFAIL; cbn in NOFAIL; eauto.


  clean_goal.

  hred.
  destruct (assert_nat_lt "DSHIMap 'n' index out of bounds" n (MInt64asNT.to_nat i0)) eqn : BOUNDS; try_abs.

  repeat apply no_failure_Ret in NOFAIL.
  rewrite XNEQY.

  hred.
  hstep; [eauto |].
  hred; hstep; [eauto |].
  hred.

  hred.

  hred.

  (* Rename states in order *)
  rename i into s0.
  rename i6 into s1.
  rename s2 into s12.
  rename i7 into s2.
  rename i10 into s3.
  rename i11 into s4.
  rename i13 into s5.
  rename i14 into s6.
  rename i15 into s7.
  rename i16 into s8.
  rename i17 into s9.
  rename i8 into s10.
  rename i9 into s11.

  rename l0 into bks.

  rename n3 into x_h_ptr.
  rename n2 into y_h_ptr.


  (* [Hyp] Get memory/ptr information for xtyp, ytyp, xptyp, yptyp. *)
  (* Duplicate work as genMExpr_correct, needed for GEP later. *)

  (* Memory invariant *)
  pose proof state_invariant_memory_invariant PRE as MINV_YOFF.
  pose proof state_invariant_memory_invariant PRE as MINV_XOFF.
  unfold memory_invariant in MINV_YOFF.
  unfold memory_invariant in MINV_XOFF.
  specialize (MINV_YOFF _ _ _ _ _ Heqo0 LUn0).
  specialize (MINV_XOFF _ _ _ _  _ Heqo LUn).
  cbn in MINV_YOFF, MINV_XOFF.


  destruct MINV_YOFF as (ptrll_yoff & τ_yoff & TEQ_yoff & FITS_yoff & INLG_yoff & bkh_yoff & MLUP_yoff & GETARRAYCELL_yoff); eauto.
  destruct MINV_XOFF as (ptrll_xoff & τ_xoff & TEQ_xoff & FITS_xoff & INLG_xoff & bkh_xoff & MLUP_xoff & GETARRAYCELL_xoff); eauto.
  (* Duplicating, as we need to do the same inside the loop body *)
  assert (H' := H). assert (H0' := H0).
  assert (H0'' := H0). (* Another for py !*)
  rewrite MLUP_xoff in H; symmetry in H; inv H.
  rewrite MLUP_yoff in H0; symmetry in H0; inv H0.

  inv TEQ_yoff. inv TEQ_xoff. cbn.

  (* We know that the Helix denotation can be expressed via the [tfor] operator *)
  assert (NOFAIL_cont := NOFAIL).
  apply no_failure_helix_bind_prefix in NOFAIL.

  rewrite DSHIMap_interpreted_as_tfor.
  rewrite DSHIMap_interpreted_as_tfor in NOFAIL.

  cbn* in *; simp; cbn in *.
  clean_goal.

  Set Nested Proofs Allowed.

  Lemma typ_to_dtyp_P :
      forall t s,
        typ_to_dtyp s (TYPE_Pointer t) ≡ DTYPE_Pointer.
  Proof.
    intros t s.
    apply typ_to_dtyp_equation.
  Qed.

  (* TODO: Move*)
  Lemma denote_exp_ID :forall defs g l m id τ ptr,
      in_local_or_global_addr l g id ptr ->
      interp_cfg_to_L3 defs (translate exp_E_to_instr_E (denote_exp (Some τ) (EXP_Ident id))) g l m
      ≈
      Ret (m,(l,(g,UVALUE_Addr ptr))).
  Proof.
    intros. destruct id eqn: Hh; [ rewrite denote_exp_GR | rewrite denote_exp_LR ] ; eauto; try reflexivity.
  Qed.

  Ltac typ_to_dtyp_simplify :=
    repeat
      (try rewrite typ_to_dtyp_I in *;
       try rewrite typ_to_dtyp_D in *;
       try rewrite typ_to_dtyp_D_array in *;
       try rewrite typ_to_dtyp_P in *).

  (* TODO : "s1" and "s2" might need to be changed *)
  match goal with
  | [H : genWhileLoop ?prefix _ _ ?loopvar ?loopcontblock ?body_entry ?body_blocks _ ?nextblock ?s1' ≡ inr (?s2', (?entry_id, ?bks)) |- _]
    => epose proof @genWhileLoop_tfor_correct prefix loopvar loopcontblock body_entry body_blocks nextblock bid_in s1' s2' s1 s11 bks as GENC
  end.

  Transparent genIMapBody.
  forward GENC; [clear GENC |].
  cbn. left; reflexivity.

  forward GENC; [clear GENC |].
  eauto.

  forward GENC; [clear GENC |].
  {
    eauto using wf_ocfg_bid_add_comment.
  }

  forward GENC; [clear GENC |].
  {
    eapply lid_bound_between_shrink; [eapply lid_bound_between_newLocalVar | | ]; eauto; try reflexivity; solve_local_count.
    get_local_count_hyps.
    Transparent addVars.
    inv Heqs12.
    cbn in Heqs13.
    solve_local_count.
    Opaque addVars.
  }

  forward GENC; [clear GENC |].  {
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

  forward GENC; [clear GENC |].
  {
    clear -Heqs5.
    unfold MInt64asNT.from_nat in Heqs5.
    unfold MInt64asNT.from_Z in Heqs5.
    simp.
    apply l0.
  }

  inv VG.
  rewrite add_comment_eutt.

  rename memV into mV_init.
  rename sz0 into y_sz.
  rename sz into x_sz.

  destruct u. unfold assert_nat_neq in XNEQY.
  unfold assert_false_to_err in XNEQY. break_match_hyp; try inv XNEQY.
  apply beq_nat_false in Heqb1.
  unfold assert_nat_lt, assert_true_to_err in BOUNDS.
  break_match_hyp; inv BOUNDS.
  rename Heqb1 into XNEQY.
  rename Heqb0 into BOUNDS.
  apply Nat.ltb_lt in BOUNDS.


  (* Definition memory_invariant_partial_write' (configV : config_cfg) (index : nat) (ptr_llvm : addr) *)
  (*            (bk_helix : mem_block) (x : ident) sz : Prop := *)
  (*     let '(mem_llvm, (ρ, g)) := configV in *)
  (*         dtyp_fits mem_llvm ptr_llvm (typ_to_dtyp [] (TYPE_Array sz TYPE_Double)) *)
  (*             ∧ in_local_or_global_addr ρ g x ptr_llvm *)
  (*             ∧ (∀ (i : Int64.int) (v0 : binary64), *)
  (*                 ((MInt64asNT.to_nat i) < N.to_nat sz -> (MInt64asNT.to_nat i) < index) -> *)
  (*                 mem_lookup (MInt64asNT.to_nat i) bk_helix ≡ Some v0 *)
  (*                 → get_array_cell mem_llvm ptr_llvm (MInt64asNT.to_nat i) DTYPE_Double ≡ inr (UVALUE_Double v0)). *)



  Definition memory_invariant_partial_write' (configV : config_cfg) (index : nat) (ptr_llvm : addr)
             (bk_helix : mem_block) (x : ident) sz : Prop :=
      let '(mem_llvm, (ρ, g)) := configV in
      dtyp_fits mem_llvm ptr_llvm (typ_to_dtyp [] (TYPE_Array sz TYPE_Double)) /\
      in_local_or_global_addr ρ g x ptr_llvm /\
          forall k dst_addr, k <= index ->
            handle_gep_addr (DTYPE_Array sz DTYPE_Double) ptr_llvm
                        [DVALUE_I64 (DynamicValues.Int64.repr 0); DVALUE_I64 (DynamicValues.Int64.repr (Z.of_nat k))] ≡ inr dst_addr ->
              in_local_or_global_addr ρ g x dst_addr /\
              (∀ (i : Int64.int) (v0 : binary64),
                  ((MInt64asNT.to_nat i) < BinNat.N.to_nat sz -> (MInt64asNT.to_nat i) < index) ->
                  mem_lookup (MInt64asNT.to_nat i) bk_helix ≡ Some v0
                  → get_array_cell mem_llvm dst_addr (MInt64asNT.to_nat i) DTYPE_Double ≡ inr (UVALUE_Double v0)).

  (* TODO : Add something like ext_memory but which talks about a range of pointers being extended. *)
  (* Invariant at each iteration *)
  set (I := (fun (k : nat) (mH : option (memoryH * mem_block)) (stV : memoryV * (local_env * global_env)) =>
               match mH with
               | None => False
               | Some (mH, b) =>
                 let '(mV, (ρ, g')) := stV in
                 (* 1. Relaxed state invariant *)
                 state_invariant (protect σ n1) s12 mH stV /\
                 (* 2. Preserved state invariant *)
                 memory_invariant_partial_write' stV k ptrll_yoff b y y_sz /\
                 mH ≡ memH /\ g ≡ g' /\
                 allocated ptrll_yoff mV /\
                  forall i, i <= k ->
                  exists dst_addr, handle_gep_addr (DTYPE_Array y_sz DTYPE_Double) ptrll_yoff
                    [DVALUE_I64 (DynamicValues.Int64.repr 0); DVALUE_I64 (DynamicValues.Int64.repr (Z.of_nat i))] ≡ inr dst_addr /\
                    exists v, mem_lookup i b ≡ Some v /\
                        ext_memory mV_init dst_addr DTYPE_Double (UVALUE_Double v) mV
                 (* exists v, ext_memory mV_init ptrll_yoff DTYPE_Double (UVALUE_Double v) mV /\ *)
               end)).

  (* Precondition and postcondition *)
  set (P := (fun (mH : option (memoryH * mem_block)) (stV : memoryV * (local_env * global_env)) =>
               match mH with
               | None => False
               | Some (mH,b) => state_invariant (protect σ n1) s12 mH stV /\
                 let '(mV, (p, g')) := stV in
                 mH ≡ memH /\ g ≡ g' /\ mV ≡ mV_init /\ ρ ≡ p /\ b ≡ bkh_yoff
                  (* exists v, ext_memory mV_init ptrll_yoff DTYPE_Double (UVALUE_Double v) mV *)
               end)).

  set (Q := (fun (mH : option (memoryH * mem_block)) (stV : memoryV * (local_env * global_env)) =>
               match mH with
               | None => False
               | Some (mH,b) => state_invariant (protect σ n1) s12 mH stV /\
                 let '(mV, (p, g')) := stV in
                 mH ≡ memH /\ g ≡ g'
                  (* exists v, ext_memory mV_init ptrll_yoff DTYPE_Double (UVALUE_Double v) mV *)
               end)).

  specialize (GENC I P Q (Some (memH, bkh_yoff))).

  assert (EE : (ID_Local v, TYPE_Double) :: (ID_Local loopvarid, IntType) ::  Γ s12 ≡ Γ s9). {
    get_gammas; eauto.

    Transparent addVars. unfold addVars in Heqs12. inv Heqs12.
    Opaque addVars. cbn in Heqs13.
    congruence.
  }

  Lemma st_no_dshptr_aliasing_neq :
    forall σ,
      no_dshptr_aliasing σ ->
        ∀ (n n' ptr1 ptr2 : nat) (sz sz' : Int64.int) (b b' : bool),
          nth_error σ n ≡ Some (DSHPtrVal ptr1 sz, b)
          → nth_error σ n' ≡ Some (DSHPtrVal ptr2 sz', b') →
          ptr1 ≢ ptr2 ->
          n' ≢ n.
  Proof.
    intros σ H n n' ptr1 ptr2 sz sz' b b' H0 H1 H2.
    unfold no_dshptr_aliasing in *.
    intros N.
    subst.
    rewrite H0 in H1.
    inv H1.
    contradiction.
  Qed.
  assert (INEQ : n0 ≢ n1). {
    destruct PRE.
    eapply st_no_dshptr_aliasing_neq; eauto.
  }

  assert (INV_STABLE : forall (k : nat) (a : option (prod memory mem_block)) (l : alist raw_id uvalue) (mV : memory_stack) (g0 : global_env) 
    (id : local_id) (v0 : uvalue) (_ : Logic.or (lid_bound_between s11 s12 id) (lid_bound_between s1 s11 id)) (_ : I k a (pair mV (pair l g0))),
             I k a (pair mV (pair (alist_add id v0 l) g0))).
  {
    intros.
    unfold I in *.
    destruct a eqn : AEQ ; eauto.
    destruct p eqn: AEP.
    destruct H0 as (? & ? & <- & <- & ?). subst.
    split; [|split;[|split]];eauto.

    - eapply state_invariant_same_Γ with (s1 := s12); eauto.
      eapply not_in_Gamma_Gamma_eq; eauto.
      eapply not_in_gamma_protect.
      eapply GAM.
      eapply lid_bound_between_shrink_down.
      2 : {
        destruct H; eapply lid_bound_between_shrink. eauto. 3 :  eauto.
        2 : solve_local_count. 3 : solve_local_count. 2 : reflexivity.
        Transparent addVars.
        inv Heqs12.
        cbn in Heqs13.
        solve_local_count.
      }

      solve_local_count.

    - unfold memory_invariant_partial_write in *. admit.

      (* destruct H1 as (? & ? & ?). *)
      (* intuition. *)
      (* + unfold alist_add; cbn. cbn. *)
      (*   destruct y; auto. cbn in *. *)
      (*    break_match_goal. *)
      (*   * rewrite rel_dec_correct in Heqb1; subst. *)
      (*     assert (Gamma_safe σ s0 s12). solve_gamma_safe. *)

      (*     Transparent addVars. *)
      (*     inv Heqs12. *)
      (*     cbn in Heqs13. *)

      (*     assert (NIN: not (in_Gamma σ s0 id)). apply H. *)
      (*     eapply lid_bound_between_shrink. eauto. *)
      (*     Transparent newLocalVar. *)
      (*     cbn in *. *)
      (*     inv Heqs4. *)
      (*     solve_local_count. solve_local_count. *)
      (*     exfalso; eapply NIN. *)
      (*     econstructor. apply Heqo0. eauto. *)
      (*     eauto. *)
      (*   * apply neg_rel_dec_correct in Heqb1. *)
      (*     rewrite remove_neq_alist; eauto. *)
      (*     all: typeclasses eauto. *)

      (* + *)
      (* + unfold alist_add; cbn. cbn. *)
      (*   destruct y; auto. cbn in *. *)
      (*     break_match_goal. *)
      (*   * rewrite rel_dec_correct in Heqb1; subst. *)
      (*     assert (Gamma_safe σ s0 s12). solve_gamma_safe. *)

      (*     Transparent addVars. *)
      (*     inv Heqs12. *)
      (*     cbn in Heqs13. *)

      (*     assert (NIN: not (in_Gamma σ s0 id)). apply H. *)
      (*     eapply lid_bound_between_shrink. eauto. solve_local_count. solve_local_count. *)
      (*     exfalso; eapply NIN. *)
      (*     econstructor. apply Heqo0. eauto. *)
      (*     eauto. *)
      (*   * apply neg_rel_dec_correct in Heqb1. *)
      (*     rewrite remove_neq_alist; eauto. *)
      (*     all: typeclasses eauto. *)
  }

  (* Loop body match *)
  forward GENC; [clear GENC |].
  {
    intros ? ? ? [[? ?]|] * (INV & LOOPVAR & BOUNDk & RET); [| inv INV].
    assert (INV' := INV).

    subst P Q ;

    (* [HELIX] Clean-up (match breaks using no failure) *)
    assert (EQk: MInt64asNT.from_nat k ≡ inr (Int64.repr (Z.of_nat k))).
    {
     destruct (MInt64asNT.from_nat k) eqn:EQN.
     - exfalso.
       unfold MInt64asNT.from_nat in *.
       unfold MInt64asNT.from_Z in *.
       simp; lia.
     - unfold MInt64asNT.from_nat in *.
       apply from_Z_intval in EQN.
       rewrite EQN, repr_intval.
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
    cbn in NOFAIL'. rewrite bind_ret_l in NOFAIL'. rewrite interp_helix_bind in NOFAIL'.
    clear RET. clear WFOCFG. clear INPUTS_BETWEEN.

    (* [HELIX] "denoteIUnCType" exposed *)
    unfold denoteIUnCType.

    Transparent genIMapBody. cbn in Heqs5. simp; try_abs.

    (* [Vellvm] step until "fmap" is exposed, so we can match with AExpr denotation *)
    rewrite denote_ocfg_unfold_in.
    2: {
      apply find_block_eq; auto.
    }

    cbn; vred. Transparent IntType. cbn.

    rewrite denote_no_phis.
    vred; cbn.

    rewrite denote_code_cons.

    (* Get mem information from PRE condition here (global and local state has changed). *)
    (* Needed for the following GEP and Load instructions *)
    destruct INV as (INV_r & INV_p & -> & -> & ?).

    assert (Heqo' := Heqo).
    assert (Heqo0' := Heqo0).

    (* Read info as if we're reading from a protected σ *)
    erewrite <- nth_error_protect_neq with (n2 := n1) in Heqo; auto.

    apply nth_error_protect_eq' in Heqo0.

    rewrite GENIR_Γ in LUn0, LUn.

    (* Memory invariant for x *)
    pose proof state_invariant_memory_invariant INV_r as MINV_XOFF.
    unfold memory_invariant in MINV_XOFF.
    specialize (MINV_XOFF _ _ _ _ _ Heqo LUn).
    cbn in MINV_XOFF.

    destruct MINV_XOFF as (ptrll_xoff_l & τ_xoff & TEQ_xoff & FITS_xoff_l & INLG_xoff_l & bkh_xoff_l & MLUP_xoff_l & GETARRAYCELL_xoff_l); eauto.

    rewrite MLUP_xoff_l in H'; symmetry in H'; inv H'.
    inv TEQ_xoff.

    assert (UNIQ0 : v ≢ loopvarid). {
      intros CONTRA; subst.
      eapply lid_bound_between_newLocalVar in Heqs4.
      eapply lid_bound_between_incLocal in Heqs11.
      eapply state_bound_between_id_separate.
      2 : eapply Heqs4.
      2 : eapply Heqs11.
      eapply incLocalNamed_count_gen_injective.
      solve_local_count. reflexivity.
    }


    assert (UNIQ1 : loopvarid ≢ px). {
      intros CONTRA; subst.

      eapply lid_bound_between_newLocalVar in Heqs4.
      eapply lid_bound_between_incLocal in Heqs9.
      eapply state_bound_between_id_separate.
      2 : eapply Heqs4.
      2 : eapply Heqs9.
      eapply incLocalNamed_count_gen_injective.
      solve_local_count. reflexivity.
    }

    assert (UNIQ2 : loopvarid ≢ py). {
      intros CONTRA; subst.

      eapply lid_bound_between_newLocalVar in Heqs4.
      eapply lid_bound_between_incLocal in Heqs10.
      eapply state_bound_between_id_separate.
      2 : eapply Heqs4.
      2 : eapply Heqs10.
      eapply incLocalNamed_count_gen_injective.
      solve_local_count. reflexivity.
    }


    pose proof INV_p as MINV_YOFF.
    unfold memory_invariant_partial_write' in MINV_YOFF.
    destruct MINV_YOFF as (FITS_yoff_l & INLG_YOFF & MINV_YOFF).

    (* [Vellvm] GEP Instruction for [x] *)
    match goal with
    | [|- context[OP_GetElementPtr (DTYPE_Array ?size' ?τ') (_, ?ptr') _]] =>
    edestruct denote_instr_gep_array' with
        (ρ := li) (g := g0) (m := mV) (i := px)
        (size := size') (a := ptrll_xoff_l) (ptr := ptr') as (? & ? & ? & ?)
    end.

    destruct x;
    rename id into XID.
    rewrite denote_exp_GR. 2 : eauto.
    cbn. subst. reflexivity.
    2 : {
      rewrite denote_exp_LR. 2 : eauto.
      cbn.
      unfold uvalue_of_nat. reflexivity.
    }

    { rewrite denote_exp_LR. reflexivity. eauto. }
    {
      assert (GET := GETARRAYCELL_xoff).
        Lemma to_nat_repr_nat :
          forall k, MInt64asNT.from_nat k ≡ inr (Int64.repr (Z.of_nat k)) ->
              MInt64asNT.to_nat (Int64.repr (Z.of_nat k)) ≡ k.
        Proof.
          intros.
          unfold MInt64asNT.to_nat.
          unfold MInt64asNT.from_nat in H.
          apply from_Z_intval in H.
          rewrite <- H.
          apply Znat.Nat2Z.id.
        Qed.

        specialize (GET (Int64.repr (Z.of_nat k))).
        pose proof EQk.
        apply to_nat_repr_nat in EQk. rewrite <- EQk.
        eapply GETARRAYCELL_xoff_l.
        rewrite to_nat_repr_nat. eauto. auto.
    }
    Unshelve. 2 : eauto.


    rename x0 into src_addr.
    rename H0 into READ_x.
    rename H1 into HSRC_GEP.
    rename H2 into x_HGEP.

    vred.
    setoid_rewrite x_HGEP; clear x_HGEP.
    vred.


    (* [Vellvm] : Load *)
    vred.
    rewrite denote_instr_load.
    2 : {
      apply denote_exp_LR.
      cbn. apply alist_find_add_eq.
    }
    2: eauto.

    (* [Vellvm] : Clean up *)
    vred.
    rewrite map_app.
    cbn.
    typ_to_dtyp_simplify.
    rewrite denote_code_app.
    vred.
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

    (* [Vellvm] GEP without read on y *)
    set (y_size := Z.to_N (Int64.intval yp_typ_)).
    match goal with
    | [|- context[OP_GetElementPtr (DTYPE_Array y_size _) (_, ?ptr')]] =>
        edestruct denote_instr_gep_array_no_read with
          (ρ := li) (g := g0) (m := mV) (i := py) (τ := DTYPE_Double)
            (size := y_size) (a := ptrll_yoff) (ptr := ptr') as (y_GEP_addr & y_HGEP & EQ_y_HG)
    end.

    {
      destruct y.
      rewrite denote_exp_GR. 2 : eauto.
      cbn. subst. reflexivity.
      rewrite denote_exp_LR. reflexivity.
      cbn.
      eauto.
    }

    {
      erewrite denote_exp_LR with (id := loopvarid).
      reflexivity.
      cbn.
      eauto.
    }

    {
      typ_to_dtyp_simplify.
      subst y_size.
      erewrite <- from_N_intval; eauto.
    }

    rename y_GEP_addr into dst_addr.
    rename y_HGEP into HDST_GEP.

    assert (allocated ptrll_xoff_l mV) as PTRLL_XOFF_ALLOCATED_mV_yoff by solve_allocated.
    assert (allocated ptrll_yoff mV) as SRC_ALLOCATED_mV by solve_allocated.

    assert (no_overlap_dtyp dst_addr DTYPE_Double src_addr DTYPE_Double) as NOALIAS.
    {
      unfold no_overlap_dtyp.
      unfold no_overlap.
      left.

      rewrite <- (handle_gep_addr_array_same_block _ _ _ _ HDST_GEP).
      rewrite <- (handle_gep_addr_array_same_block _ _ _ _ HSRC_GEP).
      intros BLOCKS; symmetry in BLOCKS; revert BLOCKS.
      destruct INV_r.

      do 2 red in st_no_llvm_ptr_aliasing.
      pose proof st_no_llvm_ptr_aliasing.
      specialize (H0 x ptrll_xoff_l y ptrll_yoff n0 n1). cbn in H.
      eapply H0; eauto.

      - intros CONTRA.
        rewrite CONTRA in LUn.
        pose proof st_no_id_aliasing as HST.
        red in HST.
        epose proof (HST _ _ _ _ _ _ _ Heqo Heqo0 LUn LUn0).
        subst.

        rewrite Heqo0 in Heqo.
        inv Heqo.
    }

    assert (E : Γ s5 ≡ Γ s7) by solve_gamma.
    rewrite E in *.


    (* [BOTH] Finally eached AExpr / FMap. Step both of them. *)
    eapply eutt_clo_bind_returns.
    {
      eapply genAExpr_correct.
      eassumption.
      - (* From our . [state_invariant_relaxed] and [memory_invariant_partial_write],
          we should be able to retrieve the normal state invariant. *)
        eapply state_invariant_enter_scope_DSHCType' with (s1 := s5); eauto.
        + rewrite E. reflexivity.
        + eapply lid_bound_before.
          solve_lid_bound. eauto.
        + solve_local_count.
        + solve_alist_in.
        + (* use LOOPVAR *)
          eapply state_invariant_Γ with (s1 := s2).
          2 : solve_gamma.

          eapply state_invariant_enter_scope_DSHnat with (x := loopvarid); eauto.
          * apply not_in_Gamma_Gamma_eq with (s1 := s0). solve_gamma.
            eapply Gamma_safe_protect in GAM.
            eapply GAM. eapply lid_bound_between_shrink with (s2 := s1) (s3 := s2); try solve_local_count.
            clear -Heqs4. Transparent newLocalVar.
            eapply lid_bound_between_newLocalVar; eauto. reflexivity.
          * rewrite alist_find_neq; auto. rewrite alist_find_neq; auto.
          * eapply state_invariant_Γ with (s1 := s0). 2 : solve_gamma. 2 : solve_local_count.
            eapply state_invariant_same_Γ; eauto using lid_bound_between_incLocal.
            eapply state_invariant_same_Γ; eauto using lid_bound_between_incLocal.
            solve_not_in_gamma.
            eapply state_invariant_Γ'.
            eauto. solve_gamma.
            destruct PRE.
            eauto.
          * solve_local_count.
      - eapply Gamma_safe_Context_extend with (s1 := s2) (s2 := s10).
        4 : { cbn. assert (GAM_E: Γ s2 ≡ Γ s7) by solve_gamma. rewrite GAM_E. reflexivity. }
        2 : solve_local_count.
        2 : solve_local_count.
        2 : {
          apply genAExpr_Γ in Heqs13. cbn in Heqs13.
          eapply dropVars_Γ in Heqs14. 2 : eauto. rewrite Heqs14. auto.
        }
        2 : { intros. cbn in *. solve_id_neq. }

        assert (Heqs4' := Heqs4).
        eapply Gamma_safe_Context_extend with (s1 := s0) (s2 := s12).
        apply Gamma_safe_protect.
        auto.
        solve_local_count. solve_local_count.
        apply incBlockNamed_Γ in Heqs3.
        apply newLocalVar_Γ in Heqs4.
        rewrite Heqs4. rewrite Heqs3. reflexivity.
        eapply dropVars_Γ in Heqs6.

        2 : {
          apply genAExpr_Γ in Heqs13. cbn in Heqs13. rewrite s2_ext in Heqs13.
          eapply dropVars_Γ in Heqs14 ; eauto.
        }
        assert (GAM_E : Γ s11 ≡ Γ s12) by solve_gamma. rewrite <- GAM_E.

        apply genAExpr_Γ in Heqs13. cbn in Heqs13. rewrite s2_ext in Heqs13.
        eapply dropVars_Γ in Heqs14 ; eauto.
        rewrite <- Heqs13.
        assert (H1: Γ s1 ≡ Γ s11) by solve_gamma.
        rewrite H1. clear H1. reflexivity.

        intros. eapply state_bound_between_separate.
        eapply incLocalNamed_count_gen_injective.
        2 : eauto.
        2 : reflexivity. Unshelve. 3 : exact s1.
        eapply lid_bound_between_newLocalVar. 2 : eauto. cbn. reflexivity.
        all : eauto.
        eauto. exact [].

      - clear -NOFAIL'. unfold denoteIUnCType in NOFAIL'.
        apply no_failure_bind_prefix in NOFAIL'. eauto.
    }

    (* "Final" simultaneous step inside the loop body *)
    intros [ [mH' t_Aexpr] | ] [mV' [li' [g0' []]]].
    intros (PRE_INV & AEXP) RET1 RET2.
    2 : { intros. cbn in *. contradiction. }

    cbn in PRE_INV.
    assert (PRE_INV' := PRE_INV).
    (* [HELIX] easy clean-up. *)
    hred.
    vred.

    destruct AEXP. destruct is_almost_pure as (-> & -> & ->).
    rename mV' into mV.
    rename mH' into memH.
    rename g0' into g0.
    Opaque newLocalVar.
    cbn in *.

    (* [Vellvm] GEP and Store the result so we can re-establish loop invariant. *)

    (* 1. GEP *)
    match goal with
    | [|- context[OP_GetElementPtr (DTYPE_Array y_size _) (_, ?ptr')]] =>
      pose proof (denote_instr_gep_array_no_read_addr py y_size DTYPE_Double defined_intrinsics
                                                      (EXP_Ident (ID_Local loopvarid)) k ptr' ptrll_yoff g0 li' mV dst_addr)
           as EQ_y_HG'
    end.


    assert (in_local_or_global_addr li' g0 y ptrll_yoff). {
      destruct y. cbn in *. eauto.
      cbn.
      cbn in INLG_yoff.
      destruct PRE_INV.
      clear IRState_is_WF.
      clear st_id_allocated st_no_id_aliasing.
      cbn in mem_is_inv. rewrite <- EE in mem_is_inv.
      specialize (mem_is_inv (S (S n1))). cbn in mem_is_inv.
      specialize (mem_is_inv _ _ _ _ Heqo0 LUn0). cbn in mem_is_inv.
      edestruct mem_is_inv as (? & ? & ? & ? & ?); clear mem_is_inv.
      inv H0. destruct H2. clear H2.
      rename st_no_dshptr_aliasing into DSH.
      rename st_no_llvm_ptr_aliasing into LLVM.
      red in DSH, LLVM. red in LLVM.
      red in st_gamma_bound.
      rewrite <- EE in st_gamma_bound.
      rewrite <- GENIR_Γ in LUn0.
      rewrite <- GENIR_Γ in st_gamma_bound.

      destruct PRE.
      specialize (st_gamma_bound0 n1 id). cbn in st_gamma_bound.
      specialize (st_gamma_bound0 _ LUn0).
      erewrite <- local_scope_modif_bound_before. 2 : eauto. 3 : eauto.
      2 : solve_local_count.
      erewrite alist_find_neq.
      erewrite alist_find_neq.
      eauto.
      eapply in_gamma_not_in_neq.
      solve_in_gamma. solve_not_in_gamma.
      eapply in_gamma_not_in_neq.
      solve_in_gamma. solve_not_in_gamma.
    }

    forward EQ_y_HG'; [clear EQ_y_HG' | ].
    {
      destruct y.
      rewrite denote_exp_GR. 2 : eauto.
      cbn. subst. reflexivity.
      rewrite denote_exp_LR. reflexivity.
      cbn. eauto.
    }

    forward EQ_y_HG'; [clear EQ_y_HG' | ].
    {
      erewrite denote_exp_LR with (id := loopvarid).
      reflexivity.
      cbn.
      Unshelve.

      erewrite local_scope_modif_out.
      4 : eauto.
      rewrite alist_find_neq.
      rewrite alist_find_neq. cbn. setoid_rewrite LOOPVAR.
      Unshelve.
      unfold uvalue_of_nat. reflexivity. eauto. eauto.
      3 : exact s1. solve_local_count.
      eapply lid_bound_between_shrink with (s2 := s1) (s3 := s2).
      Transparent newLocalVar.
      eapply lid_bound_between_newLocalVar; eauto. reflexivity.
      solve_local_count.
      solve_local_count.
    }

    forward EQ_y_HG'; [clear EQ_y_HG' | ].
    {
      typ_to_dtyp_simplify.
      subst y_size.
      erewrite <- from_N_intval; eauto.
    }

    forward EQ_y_HG'; [clear EQ_y_HG' | ].
    auto.

    vred.
    rewrite EQ_y_HG'.
    vred.

    (* 2. Store  *)
    edestruct write_succeeds with (m1 := mV) (v := DVALUE_Double t_Aexpr) (a := dst_addr).
    apply DVALUE_Double_typ.
    {
      typ_to_dtyp_simplify.
      epose proof (vellvm_helix_ptr_size _ LUn0 Heqo0).
      eapply state_invariant_cons2 in PRE_INV'. 3 : eauto. 2 : solve_local_count.
      specialize (H1 PRE_INV').

      pose proof (from_N_intval _ EQsz0) as EQ.
      rewrite H1 in EQ.
      eapply dtyp_fits_array_elem.
      subst y_size. 2 : eauto.
      rewrite <- EQ. rewrite <- H1. eauto.
      subst y_size. rewrite <- EQ.
      clear -BOUNDS BOUNDk EQk.

      rewrite Znat.Z2N.id; [|apply Int64_intval_pos].
      apply to_nat_repr_nat in EQk.

      pose proof Znat.inj_lt _ _ BOUNDS as LT.
      unfold MInt64asNT.to_nat in LT.

      rewrite Znat.Z2Nat.id in LT; [|apply Int64_intval_pos].
      etransitivity. 2 : eauto.
      clear -BOUNDk.
      rewrite <- intval_to_from_nat_id.
      eapply Znat.inj_lt.

      unfold DynamicValues.Int64.intval. unfold Z.of_nat.
      destruct k eqn: Hk; subst. apply BOUNDk.
      destruct (DynamicValues.Int64.repr (Z.pos (Pos.of_succ_nat n0))) eqn: Ha.
      Transparent DynamicValues.Int64.repr.
      admit. (* arithmetic *)
    }


    vred.
    rewrite denote_instr_store.
    2 : {
      eapply exp_correct.
      solve_local_scope_preserved.
      cbn.
      eapply Gamma_preserved_add_not_in_Gamma.
      solve_gamma_preserved.
      eapply not_in_gamma_cons. cbn. reflexivity.
      2 : solve_id_neq.

      eapply not_in_gamma_cons. eauto.
      eapply not_in_Gamma_Gamma_eq.
      2 : {
        assert (neg2 : ~ in_Gamma σ s0 py) by solve_not_in_gamma.
        apply not_in_gamma_protect; eauto.
      } solve_gamma. eauto.
    }
    3 : { cbn. reflexivity. }
    2: {
      eapply denote_exp_LR.

      cbn.
      solve_alist_in.
    }
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
    rename x0 into mV_yoff.
    rename H0 into WRITE_MEM.

  (* Re-establish INV in post condition *)

  apply eqit_Ret.
  split; [|split; [|split]].
  - clear Mono_IRState.

    erewrite local_scope_modif_out.
    eauto.
    3 : eauto.
    3 : {
      eapply local_scope_modif_add'.
      2 : {
        eapply local_scope_modif_sub'_l.
        2 : eapply local_scope_modif_sub'_l.
        3 : {
          eapply local_scope_modif_shrink.
          eauto. Unshelve.
          5 : exact s10. 4 : exact s4.
          solve_local_count. solve_local_count.
          exact s1.
        }
        solve_lid_bound_between. solve_lid_bound_between.
      }
      solve_lid_bound_between.
    }
    solve_local_count.
    {
      eapply lid_bound_between_shrink with (s2 := s1) (s3 := s2).
      Transparent newLocalVar.
      eapply lid_bound_between_newLocalVar; eauto. reflexivity.
      solve_local_count.
      solve_local_count.
    }
  - exists b0. reflexivity.

  - eapply INV_STABLE. right. solve_lid_bound_between.

    split; [| split ;[split ;[|split]| split;[|split]]]; eauto.

    (* Establish the relaxed state invariant with changed states and extended local environment *)
    {
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
          pose proof MINV_YOFF as PARTIAL_WRITE.
          specialize (PARTIAL_WRITE k dst_addr). forward PARTIAL_WRITE.
          lia.
          forward PARTIAL_WRITE.
          pose proof HDST_GEP.
          pose proof (from_N_intval _ EQsz0) as EQ.
          rewrite EQ. subst y_size. eauto.
          edestruct mem_is_inv as (? & ? & ? & ? & ? & ?); clear mem_is_inv.


          eexists. eexists. split; eauto.

          split. eapply dtyp_fits_after_write; eauto.

          split; eauto. destruct PARTIAL_WRITE.
          destruct (Nat.eq_dec y_h_ptr a).
          {

            intros.

            pose proof H as MEM.
            edestruct MEM as (MEM_ALLOC & M').

            eexists. subst. split; eauto.
            intros.
            destruct (@peano_naturals.nat_le_dec (MInt64asNT.to_nat i) k). {
              specialize (M' _ l). edestruct M' as (? & ? & ? & ?).
              erewrite <- read_array; eauto.
              2 : solve_allocated.
              2 : eauto.
              pose proof HDST_GEP.

              destruct H. 2 : eauto.
              (* The address has been written to already. *)
              admit. admit.

            }
            admit.
          }

            clear H3 H4 H5.
            intros. eexists.

          split.

          intros. admit.
          admit.
        }
      }
    }

    {
      eapply dtyp_fits_after_write; eauto.
      destruct INV_p; auto.
    }

    {
      intros.

      eapply read_array_exists with (i := MInt64asNT.to_nat i) in H .
      destruct H as (? & ? & ?).  eauto.
      (* TODO : write_array_cell_get_array_cell but with a write and gep. *)
    (* Lemma write_get_array_cell : *)
    (*   forall (m m' : memory_stack) (t : dtyp) (val : dvalue) (a : addr) (i : nat), *)
    (*     write a i t val = inr m' -> *)

    (*     handle_gep_addr (DTYPE_Array ?size ?τ) ptrll_yoff *)
    (*           [DVALUE_I64 (repr 0); DVALUE_I64 (repr (Z.of_nat (MInt64asNT.to_nat i)))] ≡ inr x0 -> *)
    (*     dvalue_has_dtyp val t -> *)
    (*     get_array_cell m' a i t = inr (dvalue_to_uvalue val). *)
    (* Proof. *)
    (*   intros m m' t val a i WRITE TYP. *)
    (*   destruct a; cbn in *. *)
    (*   break_match_hyp; inv WRITE. *)
    (*   destruct l. *)
    (*   inversion H0; subst. *)
    (*   rewrite get_logical_block_of_add_logical_block. *)
    (*   rewrite read_in_mem_block_write_to_mem_block; eauto. *)
    (* Qed. *)
      (* pose proof write_array_cell_get_array_cell. *)
      (* specialize  *)
      (* write_preserves_allocated *)
      (* eapply get_array_cell_write_no_overlap; eauto. *)
      (* constructor. *)
      admit.
    }

    solve_allocated.

    (* local_scope_modif s1 s11 li (li' [py : UVALUE_Addr y_GEP_addr]) *)
  - admit.
}


(* I stable under local env extension *)
forward GENC; [clear GENC |]; eauto.

forward GENC; [clear GENC |].
{
  get_local_count_hyps.
  unfold addVars in Heqs12. inv Heqs12.
  cbn in Heqs13. lia.
}

forward GENC; [clear GENC |].
{
  reflexivity.
}

(* P -> I 0 *)
forward GENC; [clear GENC |].
{
  subst I P; red; intros; auto. destruct a; eauto.
  destruct p; eauto. destruct b1; eauto. destruct p; eauto.
  intuition. subst.
  destruct H0.
  cbn.
  unfold memory_invariant in mem_is_inv.
  erewrite <- nth_error_protect_neq in Heqo.
  rewrite GENIR_Γ in LUn.
  specialize (mem_is_inv _ _ _ _ _ Heqo LUn).
  cbn in mem_is_inv.
  edestruct mem_is_inv as (?  & ? & ? & ? & ? & ?). inv H.
  split; eauto. eauto. subst. solve_allocated.
}

(* I n -> Q *)
forward GENC; [clear GENC |].
{
  subst I P Q; red; intros; auto. destruct a; auto.
  destruct p; eauto. destruct b1; eauto. destruct p; eauto.
  destruct H as (? & ? & ? & ?). subst. split; eauto.
  split; eauto. destruct H2. auto.
}

setoid_rewrite <- bind_ret_r at 6.

vstep.
eapply eutt_clo_bind.

(* PRECONDITION *)

eapply GENC.
{
  subst P I. clear GENC.
  cbn. split; [|split]; eauto.
  apply state_invariant_protect.
  eapply state_invariant_Γ. eauto.
  solve_gamma. solve_local_count.
}

intros [[]|]; intros (? & ? & ? & []) (? & ? & ?); subst P I; try_abs;
cbn in H0; try destruct H0 as (? & <- & <- & ?).
  rewrite interp_helix_MemSet.
2 : { destruct H; inv H. } (* absurd *)


vred.
apply eqit_Ret.


(* genIR *)
{
  split; [| split]; cbn; eauto.
  - (* Need to enter scope,then escape it to link with appropriate state *)
    destruct H0 as (? & ? & ?); subst.

    (* Need to enter scope,then escape it to link with s2 *)
    (* TODO : Need "RANGE, cell writing up to [n]th cell" version of this lemma *)
    eapply state_invariant_write_double_result; eauto.
    rewrite <- GENIR_Γ; eauto.

    {
      destruct y. cbn in *. eauto.
      cbn.
      cbn in INLG_yoff.
      destruct H0.
      clear IRState_is_WF.
      clear st_id_allocated st_no_id_aliasing.
      cbn in mem_is_inv.
      specialize (mem_is_inv n1). cbn in mem_is_inv.
      rewrite <- GENIR_Γ in mem_is_inv. cbn in *.
      eapply nth_error_protect_eq' in Heqo0.
      specialize (mem_is_inv _ _ _ _ Heqo0 LUn0). cbn in mem_is_inv.
      edestruct mem_is_inv as (? & ? & ? & ? & ?); clear mem_is_inv.
      inv H0. destruct H3. clear H3.
      rename st_no_dshptr_aliasing into DSH.
      rename st_no_llvm_ptr_aliasing into LLVM.
      red in DSH, LLVM. red in LLVM.
      red in st_gamma_bound.
      rewrite <- GENIR_Γ in st_gamma_bound.

      clear st_gamma_bound.
      destruct PRE.
      specialize (st_gamma_bound n1 id). cbn in st_gamma_bound.
      specialize (st_gamma_bound _ LUn0).
      erewrite <- local_scope_modif_bound_before. 2 : eauto.
      eauto. 2 : eauto. solve_local_count.
    }

    {
      admit.
    }

    {
      admit.
    }

    {
      admit.
    }

    {
      admit.
    }
  - destruct H; eauto.
  - solve_local_scope_modif.
}

contradiction. contradiction.
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
  forall k, (i <= k -> k < n -> find k m = find k m').

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
