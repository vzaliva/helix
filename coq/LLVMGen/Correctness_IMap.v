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


  Lemma DSHIMap_as_tfor : forall σ n x y f,
      denoteDSHOperator σ (DSHIMap n x y f) ≈
      '(x_i, _) <- denotePExpr σ x;;
      '(y_i, _) <- denotePExpr σ y;;
       x2 <- trigger (MemLU "Error looking up 'x' in DSHIMap" x_i);;
       y0 <- trigger (MemLU "Error looking up 'y' in DSHIMap" y_i);;
       y' <- DSHIMap_tfor_up σ f 0 n x2 y0 ;;
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

(* Yet another tweak at DSHCType *)
Lemma state_invariant_enter_scope_DSHCType : 
  forall σ v x s1 s2 stH mV l g,
    Γ s2 ≡ (ID_Local x, TYPE_Double) :: Γ s1 ->
    ~ in_Gamma σ s1 x ->
    l @ x ≡ Some (UVALUE_Double v) ->
    state_invariant σ s1 stH (mV,(l,g)) ->
    state_invariant (DSHCTypeVal v::σ) s2 stH (mV,(l,g)).
Proof.
  intros * EQ GAM LU [MEM WF ALIAS1 ALIAS2 ALIAS3]; inv EQ; cbn in *.
  split.
  - red; intros * LU1 LU2.
    destruct n as [| n].
    + cbn in *; inv LU1; inv LU2; auto. rewrite H0 in H1. inv H1. eauto.
    + rewrite nth_error_Sn in LU1.
      cbn in *. rewrite H0 in *.
      eapply MEM in LU2; eauto.
  -  do 2 red.
    cbn.
    intros ? [| n] LU'.
    + cbn in LU'.
      inv LU'.
      cbn.

      rewrite H0.
      exists (ID_Local x); reflexivity.
    + rewrite nth_error_Sn in LU'.
      apply WF in LU'; auto.
      rewrite H0. cbn. auto.

  - red; intros * LU1 LU2 LU3 LU4.
    destruct n1 as [| n1], n2 as [| n2]; auto.
    + exfalso. cbn in *.
      apply GAM.
      inv LU3; eapply mk_in_Gamma; eauto.
      rewrite H0 in *. inv H1. eauto.
    + exfalso.
      apply GAM; inv LU4; eapply mk_in_Gamma; eauto.
      rewrite H0 in H1. inv H1. cbn in *. rewrite H0 in *. eauto.
    + rewrite H0 in *; inv LU3; inv LU4; eapply ALIAS1 in LU1; apply LU1 in LU2; eauto.

  - red; intros * LU1 LU2.
    destruct n as [| n], n' as [| n']; auto.
    + inv LU1.
    + inv LU2.
    + rewrite nth_error_Sn in LU1.
      rewrite nth_error_Sn in LU2.
      eapply ALIAS2 in LU1; apply LU1 in LU2; eauto.

  - do 2 red. intros * LU1 LU2 LU3 LU4 INEQ IN1 IN2.
    cbn in *.
    destruct n1 as [| n1], n2 as [| n2]; auto.
    + cbn in *. rewrite H0 in *; inv LU1; inv LU2; inv LU3; inv LU4; auto.
    + rewrite H0 in *; cbn in *; inv LU1; inv LU3; eauto.
      cbn in *.
      Transparent addVars. cbn* in *. rewrite LU in IN1. inv IN1.
    + rewrite H0 in *; cbn in *; inv LU2; inv LU4.
      cbn in *; rewrite LU in IN2; inv IN2.
    + rewrite H0 in *; cbn in *.
      eapply ALIAS3; [exact LU1 | exact LU2 |..]; eauto.
  - intros [| n] * LUn; [inv LUn |].
    eapply st_id_allocated; eauto.
Qed.

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

  edestruct @no_failure_helix_LU as (? & NOFAIL' & ?); eauto; []; clear NOFAIL; rename NOFAIL' into NOFAIL; cbn in NOFAIL; eauto.
  edestruct @no_failure_helix_LU as (? & NOFAIL' & ?); eauto; []; clear NOFAIL; rename NOFAIL' into NOFAIL; cbn in NOFAIL; eauto.
  clean_goal.

  hred.
  hstep; [eauto |].
  hred; hstep; [eauto |].
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

  (* [Hyp] Get memory/ptr information for xtyp, ytyp, xptyp, yptyp. *)
  (* Duplicate work as genMExpr_correct, needed for GEP later. *)

  (* Memory invariant *)
  pose proof state_invariant_memory_invariant PRE as MINV_YOFF.
  pose proof state_invariant_memory_invariant PRE as MINV_XOFF.
  unfold memory_invariant in MINV_YOFF.
  unfold memory_invariant in MINV_XOFF.
  specialize (MINV_YOFF _ _ _ _ Heqo0 LUn0).
  specialize (MINV_XOFF _ _ _ _ Heqo LUn).
  cbn in MINV_YOFF, MINV_XOFF.

  destruct MINV_YOFF as (bkh_yoff & ptrll_yoff & τ_yoff & MLUP_yoff & TEQ_yoff & FITS_yoff & INLG_yoff & GETARRAYCELL_yoff).
  destruct MINV_XOFF as (bkh_xoff & ptrll_xoff & τ_xoff & MLUP_xoff & TEQ_xoff & FITS_xoff & INLG_xoff & GETARRAYCELL_xoff).
  (* Duplicating, as we need to do the same inside the loop body *)
  assert (H' := H). assert (H0' := H0).
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
    admit.
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

  (* Invariant at each iteration *)
  set (I := (fun (k : nat) (mH : option (memoryH * mem_block)) (stV : memoryV * (local_env * global_env)) =>
               match mH with
               | None => False
               | Some (mH, b) =>
                 let '(mV, (p, g)) := stV in
                 state_invariant σ s12 mH stV /\
                 mH ≡ memH /\
                  exists v, ext_memory mV_init ptrll_yoff DTYPE_Double (UVALUE_Double v) mV
               end)).
  (* Precondition and postcondition *)
  set (P := (fun (mH : option (memoryH * mem_block)) (stV : memoryV * (local_env * global_env)) =>
               match mH with
               | None => False
               | Some (mH,b) => state_invariant σ s12 mH stV
               end)).

  specialize (GENC I P P (Some (memH, bkh_yoff))).

  (* Loop body match *)
  forward GENC; [clear GENC |].
  {
    subst I P; intros ? ? ? [[? []]|] * (INV & LOOPVAR & BOUNDk & RET); [| inv INV].

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
    rename n3 into x_addr.
    rename n2 into x0_addr.

    (* Get mem information from PRE condition here (global and local state has changed). *)
    (* Needed for the following GEP and Load instructions *)
    destruct INV as (INV & -> & (py_val & EXT_MEM)).

    destruct EXT_MEM.
    pose proof state_invariant_memory_invariant INV as MINV_YOFF.
    pose proof state_invariant_memory_invariant INV as MINV_XOFF.
    unfold memory_invariant in MINV_YOFF.
    unfold memory_invariant in MINV_XOFF.
    rewrite GENIR_Γ in LUn0, LUn.
    specialize (MINV_YOFF _ _ _ _ Heqo0 LUn0).
    specialize (MINV_XOFF _ _ _ _ Heqo LUn).
    cbn in MINV_YOFF , MINV_XOFF.

    destruct MINV_YOFF as (bkh_yoff_l & ptrll_yoff_l & τ_yoff_l & MLUP_yoff_l &
                           TEQ_yoff_l & FITS_yoff_l & INLG_yoff_l & GETARRAYCELL_yoff_l).
    destruct MINV_XOFF as (bkh_xoff_l & ptrll_xoff_l & τ_xoff_l & MLUP_xoff_l & TEQ_xoff_l & FITS_xoff_l
                           & INLG_xoff_l & GETARRAYCELL_xoff_l).

    rewrite MLUP_xoff_l in H'; symmetry in H'; inv H'.
    rewrite MLUP_yoff_l in H0'; symmetry in H0'; inv H0'.

    inv TEQ_yoff_l.
    inv TEQ_xoff_l. cbn.

    (* [Vellvm] GEP Instruction *)
    match goal with
    | [|- context[OP_GetElementPtr (DTYPE_Array ?size' ?τ') (_, ?ptr') _]] =>
    edestruct denote_instr_gep_array with
        (ρ := li) (g := g0) (m := mV) (i := px)
        (size := size') (a := ptrll_xoff_l) (ptr := ptr') as (? & ? & ?)
    end.

    destruct x;
    rename id into XID.
    rewrite denote_exp_GR. 2 : eauto.
    cbn. reflexivity.
    2 : {
      rewrite denote_exp_LR. 2 : eauto.
      cbn.
      unfold uvalue_of_nat. reflexivity.
    }

    unfold denote_exp; cbn.
    rewrite translate_trigger, lookup_E_to_exp_E_Local, subevent_subevent,
      translate_trigger, exp_E_to_instr_E_Local, subevent_subevent.

    setoid_rewrite interp_cfg_to_L3_LR; cycle -1.
    2 : reflexivity.
    2 : {
      typ_to_dtyp_simplify; eauto.
      assert (GET := GETARRAYCELL_xoff_l).
      assert (KNat : MInt64asNT.to_nat (Int64.repr (Z.of_nat k )) ≡ k). admit.
      specialize (GET (Int64.repr (Z.of_nat k))).
      rewrite KNat in GET. eapply GET. eauto.
    }
    eauto.

    vred.
    setoid_rewrite H0; clear H0.
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

    Require Import Helix.LLVMGen.Correctness_AExpr.

    Transparent addVars. unfold addVars in Heqs12. inv Heqs12.


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


    Lemma not_in_gamma_cons :
      forall σ s1 s2 id id' τ v,
        Γ s2 ≡ (ID_Local id', τ) :: Γ s1 ->
        ~ in_Gamma σ s1 id ->
        id ≢ id' ->
        ~ in_Gamma (v :: σ) s2 id.
    Proof.
      intros σ s1 s2 id id' τ v GAM NIN NEQ.
      intros CONTRA.
      inv CONTRA.
      apply NIN.
      rewrite GAM in *.
      destruct n.
      - cbn in *; inv H; inv H0.
        contradiction.
      - esplit; eauto.
        eapply evalContext_typechecks_extend; eauto.
    Qed.

    assert (s2_ext : Γ s7 ≡ (ID_Local loopvarid, IntType) :: Γ s1). {
      assert (H1 :Γ s2 ≡ Γ s7) by solve_gamma.
      rewrite <- H1.
      apply newLocalVar_Γ in Heqs4. eauto.
    }

    assert (neg0 : ~ in_Gamma σ s0 v) by solve_not_in_gamma.

    assert (neg1 : ¬ in_Gamma (DSHnatVal (Int64.repr (Z.of_nat k)) :: σ) s7 v). {
        eapply not_in_gamma_cons.
        assert (Heqs4' := Heqs4).
        eauto.
        eapply not_in_Gamma_Gamma_eq. 2 : eauto. solve_gamma.
        auto.
    }

    (* [BOTH] Finally eached AExpr / FMap. Step both of them. *)
    eapply eutt_clo_bind_returns.
    {
      eapply genAExpr_correct.
      eassumption.
      - eapply state_invariant_enter_scope_DSHCType with (s1 := s7); eauto.
        + reflexivity.
        + solve_alist_in.
        + (* use LOOPVAR *)
          eapply state_invariant_Γ with (s1 := s2).
          2 : solve_gamma.

          eapply state_invariant_enter_scope_DSHnat with (x := loopvarid); eauto.
          * apply not_in_Gamma_Gamma_eq with (s1 := s0). solve_gamma.
            eapply GAM. eapply lid_bound_between_shrink with (s2 := s1) (s3 := s2); try solve_local_count.
            clear -Heqs4. Transparent newLocalVar.
            eapply lid_bound_between_newLocalVar; eauto. reflexivity.
          * rewrite alist_find_neq; auto. rewrite alist_find_neq; auto.
          * eapply state_invariant_Γ with (s1 := s12). 2 : eauto.
            eapply state_invariant_same_Γ; eauto using lid_bound_between_incLocal.
            eapply state_invariant_same_Γ; eauto using lid_bound_between_incLocal.
            solve_not_in_gamma.
            eapply state_invariant_Γ. eauto. eauto. solve_gamma.
      - (* eapply Gamma_safe_Context_extend. *)
        (* eapply Gamma_safe_Context_extend. *)
        (* eauto. *)
        admit.
      - clear -NOFAIL'. unfold denoteIUnCType in NOFAIL'.
        apply no_failure_bind_prefix in NOFAIL'. eauto.
    }

    (* "Final" simultaneous step inside the loop body *)
    intros [ [mH' bin] | ] [mV' [li' [g0' []]]].
    intros (PRE_INV & AEXP) RET1 RET2.

    (* [HELIX] easy clean-up. *)
    hred.

    (* [Vellvm] GEP and Store the result so we can re-establish loop invariant. *)

    (* 1. GEP *)
    set (y_size := Z.to_N (Int64.intval yp_typ_)).
    match goal with
    | [|- context[OP_GetElementPtr (DTYPE_Array y_size _) (_, ?ptr')]] =>
        edestruct denote_instr_gep_array with
          (ρ := li') (g := g0') (m := mV') (i := py) (τ := DTYPE_Double)
            (size := y_size) (a := ptrll_yoff_l) (ptr := ptr') as (? & ? & ?)
    end.

    admit. admit. admit.

    (* rewrite & step *)
    vred.
    rewrite H1; clear H1.
    vred.

    2 : try_abs.

    (* 2. Store  *)
    vred.
    rewrite denote_instr_store.
    2 : admit.
    2 : admit. 2 : admit. 2 : admit.
    vred.
    rewrite denote_term_br_1.
    vred.

    cbn.
    rename b into loopcont.
    rewrite denote_ocfg_unfold_not_in.
    vred.
    2 : admit.

    (* Re-establish INV in post condition *)
    apply eqit_Ret.
    split; [|split; [|split]]; eauto.
    admit.
  }


  forward GENC; [clear GENC |].
              {
                admit.
    (* apply newLocalVar_local_count in Heqs2. *)
    (* apply dropVars_local_count in Heqs5. *)
  }

  forward GENC; [clear GENC |]. admit.

  forward GENC; [clear GENC |].
  {
    admit.
  }


  forward GENC; [clear GENC |].
  {
    subst I P; red; intros; auto. admit.
  }

  forward GENC; [clear GENC |].
  {
    subst I P; red; intros; auto. admit.
  }

  (* eapply eutt_mon; [| apply GENC]. *)

  (* specialize (GENC g ρ memV bid_from). *)
  admit.
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
