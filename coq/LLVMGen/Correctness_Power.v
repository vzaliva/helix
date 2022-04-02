Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.
Require Import Helix.LLVMGen.Correctness_MExpr.
Require Import Helix.LLVMGen.Correctness_AExpr.
Require Import Helix.LLVMGen.IdLemmas.
Require Import Helix.LLVMGen.StateCounters.
Require Import Helix.LLVMGen.VariableBinding.
Require Import Helix.LLVMGen.BidBound.
Require Import Helix.LLVMGen.LidBound.
Require Import Helix.LLVMGen.StateCounters.
Require Import Helix.LLVMGen.Context.
Require Import Helix.LLVMGen.Correctness_While.

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

Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope nat_scope.

Section DSHPower_is_tfor.

  Definition DSHPower_tfor_body (σ : evalContext) (f : AExpr) (x y : mem_block) (xoffset yoffset : nat) (acc : mem_block) :=
    xv <- lift_Derr (mem_lookup_err "Error reading 'xv' memory in denoteDSHBinOp" xoffset x) ;;
    yv <- lift_Derr (mem_lookup_err "Error reading 'yv' memory in denoteDSHBinOp" yoffset acc) ;;
    v' <- denoteBinCType σ f yv xv ;;
    ret (mem_add yoffset v' acc).

  Definition DSHPower_tfor
             (σ: evalContext)
             (n: nat)
             (f: AExpr)
             (x y: mem_block)
             (xoffset yoffset: nat) :
    itree Event mem_block
    :=
      tfor (fun i acc =>
              DSHPower_tfor_body σ f x y xoffset yoffset acc
           ) 0 n y.

  Definition DSHPower_interpreted_tfor
             {E}
             (σ: evalContext)
             (n: nat)
             (f: AExpr)
             (x y: mem_block)
             (xoffset yoffset: nat) m
    : itree E (option (memoryH * mem_block))
    :=
      tfor (fun i acc =>
              match acc with
              | None => Ret None
              | Some (m',acc) =>
                interp_helix (DSHPower_tfor_body σ f x y xoffset yoffset acc) m'
              end
           ) 0 n (Some (m, y)).

  Lemma denoteDSHPower_as_tfor :
    forall (σ: evalContext)
      (n: nat)
      (f: AExpr)
      (x y: mem_block)
      (xoffset yoffset: nat),
      denoteDSHPower σ n f x y xoffset yoffset
                     ≈
                     DSHPower_tfor σ n f x y xoffset yoffset.
  Proof.
    intros σ n; revert σ.
    induction n; unfold DSHPower_tfor; intros σ f x y xoffset yoffset.
    - cbn.
      rewrite tfor_0.
      reflexivity.
    - cbn.
      rewrite tfor_unroll_down; [|lia|].
      + cbn.
        unfold mem_lookup_err.
        repeat setoid_rewrite bind_bind.
        eapply eutt_clo_bind; [reflexivity|].
        intros u1 u2 H; subst.
        eapply eutt_clo_bind; [reflexivity|].
        intros u0 u3 H0; subst.
        eapply eutt_clo_bind; [reflexivity|].
        intros u1 u0 H.
        rewrite bind_ret_l.
        unfold DSHPower_tfor in IHn.
        subst.
        apply IHn.
      + intros x0 i j.
        reflexivity.
  Qed.

  Lemma DSHPower_as_tfor : forall σ ne x_p xoffset y_p yoffset f initial,
      denoteDSHOperator σ (DSHPower ne (x_p,xoffset) (y_p,yoffset) f initial)
                        ≈
          '(x_i,x_size) <- denotePExpr σ x_p ;;
          '(y_i,y_size) <- denotePExpr σ y_p ;;
          lift_Serr (assert_nat_neq "DSHPower 'x' must not be equal 'y'" x_i y_i);;
          x <- trigger (MemLU "Error looking up 'x' in DSHPower" x_i) ;;
          y <- trigger (MemLU "Error looking up 'y' in DSHPower" y_i) ;;
          n <- denoteNExpr σ ne ;; (* [n] denoteuated once at the beginning *)
          xoff <- denoteNExpr σ xoffset ;;
          yoff <- denoteNExpr σ yoffset ;;
          lift_Derr (assert_NT_lt "DSHPower 'y' offset out of bounds" yoff y_size) ;;
          let y' := mem_add (MInt64asNT.to_nat yoff) initial y in
          y'' <- DSHPower_tfor (protect_p σ y_p) (MInt64asNT.to_nat n) f x y' (MInt64asNT.to_nat xoff) (MInt64asNT.to_nat yoff) ;;
          trigger (MemSet y_i y'').
  Proof.
    intros σ ne x_p xoffset y_p yoffset f initial.
    unfold denoteDSHOperator.
    cbn.
    repeat (eapply eutt_clo_bind_returns; [reflexivity|intros; try break_match_goal; subst]).
    rewrite denoteDSHPower_as_tfor.
    reflexivity.
  Qed.

  Lemma DSHPower_intepreted_as_tfor : forall σ ne x_p xoffset y_p yoffset f initial E m,
      interp_helix (E := E) (denoteDSHOperator σ (DSHPower ne (x_p,xoffset) (y_p,yoffset) f initial)) m
                        ≈
      interp_helix (E := E)
      ('(x_i,x_size) <- denotePExpr σ x_p ;;
       '(y_i,y_size) <- denotePExpr σ y_p ;;
        _ <- lift_Serr (assert_nat_neq "DSHPower 'x' must not be equal 'y'" x_i y_i);;
       x <- trigger (MemLU "Error looking up 'x' in DSHPower" x_i) ;;
       y <- trigger (MemLU "Error looking up 'y' in DSHPower" y_i) ;;
       n <- denoteNExpr σ ne ;; (* [n] denoteuated once at the beginning *)
       xoff <- denoteNExpr σ xoffset ;;
       yoff <- denoteNExpr σ yoffset ;;
       lift_Derr (assert_NT_lt "DSHPower 'y' offset out of bounds" yoff y_size) ;;
       let y' := mem_add (MInt64asNT.to_nat yoff) initial y in
       y'' <- DSHPower_tfor (protect_p σ y_p) (MInt64asNT.to_nat n) f x y' (MInt64asNT.to_nat xoff) (MInt64asNT.to_nat yoff) ;;
       trigger (MemSet y_i y'')) m.
  Proof.
    intros σ ne x_p xoffset y_p yoffset f initial E m.

    rewrite DSHPower_as_tfor.
    reflexivity.
  Qed.

  Definition DSHPower_code (px py xv yv : raw_id) (xtyp xptyp : typ) (x : ident) (src_nexpr : exp typ) (fexpr : exp typ) (fexpcode : code typ) (storeid1 : int) :=
    ([
      (IId px,  INSTR_Op (OP_GetElementPtr
                            xtyp (xptyp, (EXP_Ident x))
                            [(IntType, EXP_Integer 0%Z);
                            (IntType, src_nexpr)]

      ));
    (IId xv, INSTR_Load false TYPE_Double
                        (TYPE_Pointer TYPE_Double,
                         (EXP_Ident (ID_Local px)))
                        (ret 8%Z));
    (IId yv, INSTR_Load false TYPE_Double
                        (TYPE_Pointer TYPE_Double,
                         (EXP_Ident (ID_Local py)))
                        (ret 8%Z))
    ]
      ++ fexpcode ++
      [
        (IVoid storeid1, INSTR_Store false
                                     (TYPE_Double, fexpr)
                                     (TYPE_Pointer TYPE_Double,
                                      (EXP_Ident (ID_Local py)))
                                     (ret 8%Z))
      ])%list.

  Definition DSHPower_block body_block_id loopcontblock (px py xv yv : raw_id) (xtyp xptyp : typ) (x : ident) (src_nexpr : exp typ) (fexpr : exp typ) (fexpcode : code typ) (storeid1 : int) : LLVMAst.block typ :=
    {|
    blk_id    := body_block_id ;
    blk_phis  := [];
    blk_code  := DSHPower_code px py xv yv xtyp xptyp x src_nexpr fexpr fexpcode storeid1;
    blk_term  := TERM_Br_1 loopcontblock;
    blk_comments := None
    |}.

End DSHPower_is_tfor.

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


(* TODO: probably want to move this ltac *)
Ltac get_mem_eqs :=
  cbn in *;
  repeat match goal with
         | H: (lift_Rel_cfg (state_invariant ?σ1 ?s3) ⩕ genNExpr_post ?e ?σ2 ?s1 ?s2 ?mh (mk_config_cfg ?mv ?l ?g)) (?mh', ?t) (?mv', (?l', (?g', ()))) |- _
           => apply genNExpr_memoryV in H
         end.

Ltac solve_mem_eq :=
  get_mem_eqs; subst;
  reflexivity.

Ltac solve_dtyp_fits_mem_eq :=
  match goal with
  | H: dtyp_fits ?m1 ?ptr ?τ
    |- dtyp_fits ?m2 ?ptr ?τ
    => let MEM := fresh "MEM" in assert (m2 ≡ m1) as MEM by solve_mem_eq; rewrite MEM; assumption
  end.

(* TODO: expand this. Just trying to figure out this case first *)
Ltac solve_dtyp_fits :=
  first [ solve_dtyp_fits_mem_eq
        | eapply dtyp_fits_array_elem; [eauto|eassumption|eauto]
        ].


Lemma DSHPower_correct:
  ∀ (n : NExpr) (src dst : MemRef) (f : AExpr) (initial : binary64) (s1 s2 : IRState) (σ : evalContext) (memH : memoryH) (nextblock bid_in bid_from : block_id) (bks : list (LLVMAst.block typ)) (g : global_env)
    (l : local_env) (memV : memoryV),
    genIR (DSHPower n src dst f initial) nextblock s1 ≡ inr (s2, (bid_in, bks))
    → bid_bound s1 nextblock
    → state_invariant σ s1 memH (memV, (l, g))
    → Gamma_safe σ s1 s2
    → no_failure (E := E_cfg) (interp_helix (denoteDSHOperator σ (DSHPower n src dst f initial)) memH)
    → eutt (succ_cfg (genIR_post σ s1 s2 nextblock l)) (interp_helix (denoteDSHOperator σ (DSHPower n src dst f initial)) memH) (interp_cfg (denote_ocfg (convert_typ [] bks) (bid_from, bid_in)) g l memV).
Proof.
  intros n src dst f initial s1 s2 σ memH nextblock bid_in bid_from bks g l memV GEN NEXT PRE GAM NOFAIL.

  pose proof generates_wf_ocfg_bids _ NEXT GEN as WFOCFG.
  pose proof inputs_bound_between _ _ _ GEN as INPUTS_BETWEEN.
  pose proof genWhileLoop_entry_in_scope _ _ _ GEN as ENTRY_IN.

  cbn in * |-; simp.
  rewrite DSHPower_as_tfor; cbn.
  inv_resolve_PVar Heqs0.
  inv_resolve_PVar Heqs1.
  unfold denotePExpr in *.
  cbn* in *.
  destruct u.
  simp; try_abs.

  assert (incLocalNamed "Power_i" i21
                        ≡ inr
                        ({|
                            block_count := block_count i21;
                            local_count := S (local_count i21);
                            void_count := void_count i21;
                            Γ := Γ i21 |}, Name ("Power_i" @@ string_of_nat (local_count i21)))) as LC_Gen by reflexivity.

  repeat apply no_failure_Ret in NOFAIL.
  break_match_hyp; try_abs.
  repeat apply no_failure_Ret in NOFAIL.
  rename Heqs0 into NO_ALIAS_XY.

  do 2 (apply no_failure_helix_LU in NOFAIL; destruct NOFAIL as (? & NOFAIL & ?); cbn in NOFAIL).

  (* Symbolically reducing the concrete prefix on the Helix side *)
  hred.
  rewrite NO_ALIAS_XY.
  hred.
  hstep; [eassumption |].
  hred; hstep; [eassumption |].
  hred.

  rename l0 into loop_blocks.

  assert (wf_ocfg_bid loop_blocks) as WF_loop_blocks.
  { eapply wf_ocfg_bid_add_comment; eauto.
  }
  assert (free_in_cfg loop_blocks nextblock) as FREE_loop_blocks_nextblock.
  {
    rewrite Forall_forall in INPUTS_BETWEEN. intros IN. subst.
    rewrite inputs_convert_typ, add_comment_inputs in INPUTS_BETWEEN.
    apply INPUTS_BETWEEN in IN; clear INPUTS_BETWEEN.
    eapply not_bid_bound_between; eauto.
  }

  assert (~ (b ≡ bid_in \/ False)) as BBID_IN. (* easier than writing out all the body blocks *)
  { (* entry_id (bid_in), is not in the outputs of body_blocks *)
    intros [CONTRA | []].
    subst.

    Set Nested Proofs Allowed.
    eapply genWhileLoop_entry_block in Heqs2.
    inv Heqs2.
    Transparent incBlockNamed.
    inv Heqs.
    Opaque incBlockNamed.
  }

  (* body_etry (* b0 *) is in inputs body_blocks *)
  assert (b0 ≡ b0 ∨ False) as B0B0 by auto.
  epose proof @genWhileLoop_init' _ _ _ _ _ _ _ _ _ _ _ _ _ bid_from Heqs2 WF_loop_blocks BBID_IN FREE_loop_blocks_nextblock B0B0 as INIT.
  cbn in INIT.
  destruct INIT as (body_bks' & GEN' & INIT & WF_BODY_BKS' & FREE_BODY_BKS'_NEXTBLOCK).
  clear Heqs2.

  (* TODO: use matches to get sb1 / sb2 *)
  match goal with
  | H: genWhileLoop ?prefix ?x ?y ?loopvar ?loopcontblock ?body_entry ?body_blocks [] ?nextblock ?s1 ≡ inr (?s2, (?bid_in, ?bks)) |- _
    => epose proof @genWhileLoop_tfor_correct_nexpr prefix loopvar loopcontblock body_entry body_blocks nextblock bid_in σ {|
           block_count := block_count i21;
           local_count := S (local_count i21);
           void_count := void_count i21;
           Γ := Γ i21 |} s2 i16 {|
           block_count := block_count i21;
           local_count := S (local_count i21);
           void_count := void_count i21;
           Γ := Γ i21 |} bks as LOOPTFOR
  end.

  (* s1 s2 sb1 sb2

     sb1 << sb2
     local_count sb2 ≡ local_count s1

     What's modified in l_loop and l_AExpr?

   *)

  assert (In b0
               (inputs
                  [{| blk_id := b0;
                      blk_phis := [];
                      blk_code :=
                        (IId r2, INSTR_Load false TYPE_Double (TYPE_Pointer TYPE_Double, (EXP_Ident (ID_Local r))) (Some 8%Z))
                          :: c2 ++
                          [(IVoid i15,
                            INSTR_Store false (TYPE_Double, e2)
                                        (TYPE_Pointer TYPE_Double, (EXP_Ident (ID_Local r))) (Some 8%Z)) : (instr_id * instr typ)];
                      blk_term := TERM_Br_1 b;
                      blk_comments := None
                   |}])) as Inb0 by auto.

  assert (is_correct_prefix "Power") as PREF_POWER by solve_prefix.

  assert (lid_bound_between i16 {|
           block_count := block_count i21;
           local_count := S (local_count i21);
           void_count := void_count i21;
           Γ := Γ i21 |}
                            ("Power_i" @@ string_of_nat (local_count i21))) as LID_BOUND_BETWEEN_POWER_I by solve_lid_bound_between.

  specialize (LOOPTFOR Inb0 PREF_POWER WF_BODY_BKS' LID_BOUND_BETWEEN_POWER_I).
  specialize (LOOPTFOR FREE_BODY_BKS'_NEXTBLOCK).

  clear LID_BOUND_BETWEEN_POWER_I.
  assert (lid_bound_between i21 {|
           block_count := block_count i21;
           local_count := S (local_count i21);
           void_count := void_count i21;
           Γ := Γ i21 |}
                            ("Power_i" @@ string_of_nat (local_count i21))) as LID_BOUND_BETWEEN_POWER_I by solve_lid_bound_between.


  (* Need to know how many times we loop, this is determined by the
  result of evaluating the expression e1 *)
  pose proof Heqs7 as LOOP_END.

  (* Clean up LLVM side a bit *)
  setoid_rewrite add_comment_eutt.

  (* Substitute blocks *)
  rewrite INIT.

  rename r0 into src_ptr_id.
  rename r1 into src_val_id.
  rename r into dst_ptr_id.
  rename r2 into dst_val_id.

  rename e0 into xoff_exp.
  rename e1 into yoff_exp.
  rename e into loop_end_exp.
  rename c0 into xoff_code.
  rename c1 into yoff_code.
  rename c into loop_end_code.

  rename n0 into xoff_nexpr.
  rename n1 into yoff_nexpr.
  rename n into loop_end_nexpr.

  rename n4 into dst_addr_h.
  rename i into dst_size_h.
  rename n5 into src_addr_h.
  rename i2 into src_size_h.

  assert (Γ s1 ≡ Γ s2) as Γ_S1S2.
  { get_gammas.
    apply dropVars_Γ' in Heqs15.
    rewrite <- Heqs14 in Heqs15.
    solve_gamma.
  }

  (* Need to reorder the nexprs to line things up.

     In helix we evaluate:

     1) loop_end
     2) xoff
     3) yoff

     In LLVM the loop_end is calculated last:

     1) xoff
     2) yoff
     3) loop_end

     I should be able to commute loop_end_code in order to match it up
     with denoteNExpr σ loop_end_nexpr.
   *)

  repeat rewrite convert_typ_code_app.
  repeat setoid_rewrite denote_code_app.

  vstep.
  vred.

  (* loop_end *)
  eapply eutt_clo_bind_returns.
  { eapply genNExpr_correct; [eauto|solve_state_invariant|solve_gamma_safe|eauto].
  }

  intros [[m_loopend t_loopend] |] [mV_loopend [l_loopend [g_loopend []]]] PostLoopEnd RetLoopNExp RetLoopCode; [|inversion PostLoopEnd].
  destruct PostLoopEnd as [PostLoopEndSINV PostLoopEndNExpr]. cbn in PostLoopEndSINV.
  pose proof (Correctness_NExpr.is_almost_pure PostLoopEndNExpr) as [MHPURE [MVPURE GPURE]]; subst.
  vred; hred; vred.

  pose proof NOFAIL as NOFAIL_loopend.
  eapply no_failure_helix_bind_prefix in NOFAIL_loopend.
  eapply no_failure_helix_bind_continuation in NOFAIL; [eauto|eassumption].

  pose proof NOFAIL as NOFAIL_xoff.
  eapply no_failure_helix_bind_prefix in NOFAIL_xoff.

  (* xoff *)
   eapply eutt_clo_bind_returns.
  { eapply genNExpr_correct; [eauto|solve_state_invariant|solve_gamma_safe|eauto].
  }

  intros [[m_xoff xoff_res] |] [mV_xoff [l_xoff [g_xoff []]]] PostXoff RetXoffNExp RetXoffCode; [|inversion PostXoff].
  destruct PostXoff as [PostXoffSINV PostXoffNExpr]. cbn in PostXoffSINV.
  pose proof (Correctness_NExpr.is_almost_pure PostXoffNExpr) as [MHPURE [MVPURE GPURE]]; subst.
  vred; hred; vred.

  eapply no_failure_helix_bind_continuation in NOFAIL; [eauto|eassumption].
  pose proof NOFAIL as NOFAIL_yoff.
  eapply no_failure_helix_bind_prefix in NOFAIL_yoff.

  (* yoff *)
  eapply eutt_clo_bind_returns.
  { eapply genNExpr_correct; [eauto|solve_state_invariant|solve_gamma_safe|eauto].
  }

  intros [[m_yoff yoff_res] |] [mV_yoff [l_yoff [g_yoff []]]] PostYoff RetYoffNExp RetYoffCode; [|inversion PostYoff].
  destruct PostYoff as [PostYoffSINV PostYoffNExpr]. cbn in PostYoffSINV.
  pose proof (Correctness_NExpr.is_almost_pure PostYoffNExpr) as [MHPURE [MVPURE GPURE]]; subst.

  Ltac nexpr_modifs :=
    repeat
      match goal with
      | POST : genNExpr_post _ _ _ _ _ _ _ _ |- _
        => eapply Correctness_NExpr.extends in POST; cbn in POST
      end.

  assert (local_scope_modif i5 i7 l l_xoff /\ local_scope_modif i5 i8 l l_yoff) as [LSM_xoff LSM_yoff].
  {
    nexpr_modifs.
    epose proof local_scope_modif_trans'' PostLoopEndNExpr PostXoffNExpr as LSM_xoff.
    repeat (forward LSM_xoff; solve_local_count).
    epose proof local_scope_modif_trans'' LSM_xoff PostYoffNExpr as LSM_yoff.
    repeat (forward LSM_yoff; solve_local_count).
    auto.
  }

  assert (WF_IRState σ i5) as WFi5.
  { eapply WF_IRState_Γ; eauto.
    solve_gamma.
  }

  assert (gamma_bound i5) as GBi5.
  { eapply gamma_bound_mono.
    { eapply st_gamma_bound in PRE. apply PRE. }
    solve_local_count.
    solve_gamma.
  }


  hred.

  eapply no_failure_helix_bind_continuation in NOFAIL; [eauto|eassumption].
  pose proof NOFAIL as NOFAIL_Assert.
  eapply no_failure_helix_bind_prefix in NOFAIL_Assert.

  (* TODO: I feel like I should be able to automate all of this no failure stuff. *)
  break_match_goal.
  { exfalso; eapply failure_helix_throw; eassumption. }
  rewrite bind_ret_l in NOFAIL.

  hred.

  match goal with
  | H: assert_NT_lt _ _ _ ≡ inr _ |- _
    =>
    unfold assert_NT_lt, assert_true_to_err in H;
      break_if; inv H
  end.

  match goal with
  | H: (_ <? _) ≡ true |- _
    => rename H into LT_yoff
  end.

  (* Need to figure out the corresponding pointer for id (i3).

     Need to get this from the memory_invariant *)

  pose proof state_invariant_memory_invariant PRE as MINV_YOFF.
  pose proof state_invariant_memory_invariant PRE as MINV_XOFF.
  unfold memory_invariant in MINV_YOFF.
  unfold memory_invariant in MINV_XOFF.
  specialize (MINV_YOFF n3 _ _ _ _ Heqo LUn0).
  specialize (MINV_XOFF n2 _ _ _ _ Heqo0 LUn).
  cbn in MINV_YOFF, MINV_XOFF.

  destruct MINV_YOFF as (ptrll_yoff & τ_yoff & TEQ_yoff & FITS_yoff & INLG_yoff & MLUP_yoff).
  specialize (MLUP_yoff eq_refl) as (bkh_yoff & MLUP_yoff & GETARRAYCELL_yoff).

  destruct MINV_XOFF as (ptrll_xoff & τ_xoff & TEQ_xoff & FITS_xoff & INLG_xoff & MLUP_xoff).
  specialize (MLUP_xoff eq_refl) as (bkh_xoff & MLUP_xoff & GETARRAYCELL_xoff).

  rewrite MLUP_xoff in H; symmetry in H; inv H.
  rewrite MLUP_yoff in H0; symmetry in H0; inv H0.

  inv TEQ_yoff. inv TEQ_xoff. cbn. vred.

  edestruct denote_instr_gep_array_no_read with (m:=mV_yoff) (g:=g_yoff) (l:=l_yoff) (size:=(Z.to_N (Int64.intval i1))) (τ:=DTYPE_Double) (i:=src_ptr_id) (ptr := @EXP_Ident dtyp i0) (a:= ptrll_xoff) (e_ix:=convert_typ [] xoff_exp) (ix:=(MInt64asNT.to_nat xoff_res)).

  { destruct i0.
    { rewrite denote_exp_GR.
      change (UVALUE_Addr ptrll_xoff) with (dvalue_to_uvalue (DVALUE_Addr ptrll_xoff)).
      reflexivity.
      auto.
    }
    { assert (lid_bound s1 id) as LID_BOUND0 by (eapply st_gamma_bound; solve_lid_bound).
      rewrite denote_exp_LR.
      change (UVALUE_Addr ptrll_yoff) with (dvalue_to_uvalue (DVALUE_Addr ptrll_yoff)).
      reflexivity.
      cbn.

      nexpr_modifs.
      Ltac solve_alist_in_yoff upper :=
        erewrite <- local_scope_modif_bound_before with (s2:=upper); eauto;
        repeat (eapply local_scope_modif_add'; [solve_lid_bound_between|]);
        match goal with
        | LSM1 : local_scope_modif ?s1 ?s2 _ ?l2,
          LSM2 : local_scope_modif ?s12 ?s22 ?l1 _
          |- local_scope_modif _ _ ?l1 ?l2
          => eapply (@local_scope_modif_shrink _ s12 s2); [solve_local_scope_modif| |]; solve_local_count
        end.


      solve_alist_in_yoff s2.
    }
  }

  { apply Correctness_NExpr.exp_correct in PostXoffNExpr.
    cbn in PostXoffNExpr.
    rewrite repr_of_nat_to_nat.
    destruct PostYoffNExpr.

    eapply PostXoffNExpr; [solve_local_scope_preserved | solve_gamma_preserved].
  }

  { typ_to_dtyp_simplify.
    erewrite <- from_N_intval; eauto.
  }

  rename x into src_addr.
  destruct H as [HSRC_GEP HSRC_GEP_EUTT].
  cbn.

  replace (match i0 with | ID_Global rid => ID_Global rid | ID_Local lid => ID_Local lid end) with (i0) by (destruct i0; auto).

  rewrite HSRC_GEP_EUTT.

  vred; hred; vred.

  edestruct denote_instr_gep_array_no_read with
    (m:=mV_yoff)
    (g:=g_yoff)
    (l:=(alist_add src_ptr_id (UVALUE_Addr src_addr) l_yoff))
    (size:=(Z.to_N (Int64.intval i4)))
    (τ:=DTYPE_Double)
    (i:=dst_ptr_id)
    (ptr := @EXP_Ident dtyp i3)
    (a:= ptrll_yoff)
    (e_ix:= tfmap (typ_to_dtyp []) yoff_exp)
    (ix:=(MInt64asNT.to_nat yoff_res)).
  { destruct i3 as [id | id].
    { rewrite denote_exp_GR.
      change (UVALUE_Addr ptrll_yoff) with (dvalue_to_uvalue (DVALUE_Addr ptrll_yoff)).
      reflexivity.
      auto.
    }
    { assert (lid_bound s1 id) as LID_BOUND0 by (eapply st_gamma_bound; solve_lid_bound).
      rewrite denote_exp_LR.
      change (UVALUE_Addr ptrll_yoff) with (dvalue_to_uvalue (DVALUE_Addr ptrll_yoff)).
      reflexivity.
      cbn.

      nexpr_modifs.
      solve_alist_in_yoff s2.
    }
  }

  { apply Correctness_NExpr.exp_correct in PostYoffNExpr.
    cbn in PostYoffNExpr.
    rewrite repr_of_nat_to_nat.

    eapply PostYoffNExpr; [solve_local_scope_preserved | solve_gamma_preserved].
  }


  { typ_to_dtyp_simplify.
    erewrite <- from_N_intval; eauto.
  }

  rename x into dst_addr.
  destruct H as [HDST_GEP HDST_GEP_EUTT].
  cbn.

  replace (match i3 with | ID_Global rid => ID_Global rid | ID_Local lid => ID_Local lid end) with (i3) by (destruct i3; auto).

  rewrite HDST_GEP_EUTT.

  vred; hred; vred.

  (* Store for the initial value *)
  edestruct denote_instr_store_exists with (a := dst_addr) (m:=mV_yoff).

  { cbn.
    apply denote_exp_double.
  }

  { apply denote_exp_LR.
    apply alist_find_add_eq.
  }

  { reflexivity.
  }

  { constructor.
  }

  { typ_to_dtyp_simplify.
    epose proof (vellvm_helix_ptr_size _ LUn0 Heqo PRE); subst.

    pose proof (from_N_intval _ EQsz0) as EQ.
    apply Znat.Z2N.inj in EQ; [|apply Int64_intval_pos|apply Int64_intval_pos].

    rewrite <- EQ in *.
    eapply dtyp_fits_array_elem; [eapply FITS_yoff|..]; eauto.

    rewrite Znat.Z2N.id; [|apply Int64_intval_pos].
    apply NPeano.Nat.ltb_lt in LT_yoff.
    pose proof Znat.inj_lt _ _ LT_yoff as LT.
    unfold MInt64asNT.to_nat in LT.
    rewrite Znat.Z2Nat.id in LT; [|apply Int64_intval_pos].
    rewrite Znat.Z2Nat.id in LT; [|apply Int64_intval_pos].

    rewrite repr_of_nat_to_nat.
    apply LT.
  }

  rename x into mV_init.
  destruct H as [WRITE_INIT STORE_INIT].
  cbn in STORE_INIT.
  cbn.
  rewrite STORE_INIT.

  vred.

  cbn in PostLoopEndNExpr.
  pose proof Correctness_NExpr.exp_correct PostLoopEndNExpr as PostLoopEndNExprCorrect.
  cbn in PostLoopEndNExprCorrect.

  epose proof (denote_exp_i64 t_loopend) as T_LOOPEND_EUTT.
  assert (eutt Logic.eq (interp_cfg (translate exp_to_instr (denote_exp (Some (DTYPE_I (Npos 64))) (EXP_Integer (Integers.Int64.intval t_loopend)))) g_yoff l_loopend mV_yoff)
               (interp_cfg
                  (translate exp_to_instr
                             (denote_exp (Some (DTYPE_I (Npos 64)))
                                         (convert_typ [] loop_end_exp))) g_yoff l_loopend mV_yoff)) as EUTT_INT.
  rewrite T_LOOPEND_EUTT.
  rewrite PostLoopEndNExprCorrect.
  reflexivity.

  solve_local_scope_preserved.
  solve_gamma_preserved.

  specialize (LOOPTFOR loop_end_nexpr i5 i6 m_yoff m_yoff loop_end_exp loop_end_code WFi5 GBi5 Heqs3).
  repeat (forward LOOPTFOR; [solve_local_count|]).
  specialize (LOOPTFOR t_loopend RetLoopNExp).

  forward LOOPTFOR. eauto.

  (* TODO: may be able to separate this out into the DSHPower_body_eutt lemma *)
  unfold DSHPower_tfor.
  rewrite interp_helix_tfor; [|lia].
  match goal with
    |- eutt _ (ITree.bind (tfor ?bod _ _ _) _) _ => specialize (LOOPTFOR _ bod)
  end.

  (* Will need to set up loop invariants and such, just like loop case *)
  (* Invariant at each iteration *)

  set (I := (fun (k : nat) (mH : option (memoryH * mem_block)) (stV : memoryV * (local_env * global_env)) =>
               match mH with
               | None => False
               | Some (mH,mb) =>
                 match stV with
                 | (mV, (l, g)) =>
                   state_invariant (protect σ n3) s2 mH stV /\
                   alist_find dst_ptr_id l ≡ Some (UVALUE_Addr dst_addr) /\
                   alist_find src_ptr_id l ≡ Some (UVALUE_Addr src_addr) /\
                   local_scope_modif i16 s2 (alist_add dst_ptr_id (UVALUE_Addr dst_addr) (alist_add src_ptr_id (UVALUE_Addr src_addr) l_yoff)) l /\
                   g ≡ g_yoff /\
                   allocated ptrll_yoff mV /\
                   (* Not sure if this is the right block *)
                   Returns (Some (mH, mb))
                           (@interp_helix _ E_cfg (tfor
                                                     (λ (_ : nat) (acc : mem_block),
                                                      DSHPower_tfor_body (protect σ n3) f bkh_xoff
                                                                         (mem_add (MInt64asNT.to_nat yoff_res) initial bkh_yoff)
                                                                         (MInt64asNT.to_nat xoff_res) (MInt64asNT.to_nat yoff_res) acc) 0 k
                                                     (mem_add (MInt64asNT.to_nat yoff_res) initial bkh_yoff)) m_yoff) /\
                   (forall y, y ≢ (MInt64asNT.to_nat yoff_res) -> mem_lookup y mb ≡ mem_lookup y bkh_yoff) /\
                   exists v, mem_lookup (MInt64asNT.to_nat yoff_res) mb ≡ Some v /\
                        ext_memory mV_init dst_addr DTYPE_Double (UVALUE_Double v) mV
                 end
               end)).

  (* Precondition *)
  set (P := (fun (mH : option (memoryH * mem_block)) (stV : memoryV * (local_env * global_env)) =>
               match mH with
               | None => False
               | Some (mH,mb) =>
                 match stV with
                 | (mV, (l, g)) =>
                   state_invariant (protect σ n3) s2 mH stV /\
                   alist_find dst_ptr_id l ≡ Some (UVALUE_Addr dst_addr) /\
                   alist_find src_ptr_id l ≡ Some (UVALUE_Addr src_addr) /\
                   local_scope_modif i16 s2 (alist_add dst_ptr_id (UVALUE_Addr dst_addr) (alist_add src_ptr_id (UVALUE_Addr src_addr) l_yoff)) l /\
                   g ≡ g_yoff /\
                   mH ≡ m_yoff /\
                   mb ≡ mem_add (MInt64asNT.to_nat yoff_res) initial bkh_yoff /\
                   mV ≡ mV_init
                 end
               end)).

  (* Postcondition *)
  set (Q := (fun (mH : option (memoryH * mem_block)) (stV : memoryV * (local_env * global_env)) =>
               match mH with
               | None => False
               | Some (mH,mb) => state_invariant σ s2 (memory_set mH dst_addr_h mb) stV
               end)).

  specialize (LOOPTFOR I P Q (Some (m_yoff, mem_add (MInt64asNT.to_nat yoff_res) initial bkh_yoff))).

  (* Relating iterations of the bodies *)
  forward LOOPTFOR.
  { intros g_loop l_loop mV_loop [[mH_loop mb_loop] |] k _label [HI [POWERI [LOOPEND_EXPID [BOUND RETURNS]]]]; [|inv HI].
    cbn in HI.
    destruct HI as [LINV_SINV [LINV_DST_PTR_ID [LINV_SRC_PTR_ID [LINV_LSM [LINV_GLOBALS [LINV_ALLOC [LINV_RET [LINV_HELIX_MB_OLD [v [LINV_HELIX_MB_NEW LINV_MEXT]]]]]]]]]].
    pose proof LINV_MEXT as [LINV_MEXT_NEW LINV_MEXT_OLD].
    unfold DSHPower_tfor_body.

    unfold mem_lookup_err.
    unfold trywith.

    rewrite denoteDSHPower_as_tfor in NOFAIL.
    unfold DSHPower_tfor in NOFAIL.

    eapply no_failure_helix_bind_prefix in NOFAIL.
    rewrite interp_helix_tfor in NOFAIL; [|lia].
    eapply no_failure_tfor with (k0:=k) in NOFAIL; [|lia|eauto].
    cbn in NOFAIL.

    break_match_goal.
    2: { unfold mem_lookup_err in *.
         rewrite Heqo1 in NOFAIL.
         cbn in NOFAIL.
         eapply no_failure_bind_prefix in NOFAIL.
         eapply no_failure_helix_bind_prefix in NOFAIL.
         eapply failure_helix_throw in NOFAIL.
         inv NOFAIL.
    }
    rename Heqo1 into MEMLUP_xoff.

    unfold mem_lookup_err in NOFAIL.
    rewrite MEMLUP_xoff in NOFAIL.


    rewrite LINV_HELIX_MB_NEW in NOFAIL.
    cbn in NOFAIL.
    repeat rewrite bind_ret_l in NOFAIL.
    rewrite LINV_HELIX_MB_NEW.
    cbn.
    repeat rewrite bind_ret_l.

    rewrite denote_ocfg_unfold_in.
    2: {
      apply find_block_eq; auto.
    }

    cbn; vred.

    rewrite denote_no_phis.
    vred; cbn.

    rewrite denote_code_cons.
    vred.

    pose proof (write_correct WRITE_INIT) as [WRITE_ALLOCATED WRITE_WRITTEN].
    specialize (WRITE_WRITTEN DTYPE_Double).
    forward WRITE_WRITTEN; [constructor|].
    destruct WRITE_WRITTEN as [MEXT_INIT_NEW MEXT_INIT_OLD].

    assert (allocated ptrll_xoff mV_yoff) as PTRLL_XOFF_ALLOCATED_mV_yoff by solve_allocated.
    assert (allocated src_addr mV_yoff) as SRC_ALLOCATED_mV_yoff by solve_allocated.

    assert (no_overlap_dtyp dst_addr DTYPE_Double src_addr DTYPE_Double) as NOALIAS.
    { pose proof NO_ALIAS_XY.
      clear NO_ALIAS_XY.
      rename H into NO_ALIAS_XY.
      unfold assert_nat_neq in NO_ALIAS_XY.

      destruct (src_addr_h =? dst_addr_h) eqn:EQ.
      - (* FIXME : repair *)
        admit.
      - apply beq_nat_false in EQ.
        destruct PRE.

        (* TODO: should this be a lemma? *)
        assert (i0 ≢ i3) as ID_NEQ.
        { intros CONTRA.
          rewrite CONTRA in LUn.
          epose proof (st_no_id_aliasing _ _ _ _ _ _ _ Heqo0 Heqo LUn LUn0).
          subst.

          rewrite Heqo0 in Heqo.
          inv Heqo.
          contradiction.
        }

        unfold no_overlap_dtyp.
        unfold no_overlap.
        left.

        rewrite <- (handle_gep_addr_array_same_block _ _ _ _ HDST_GEP).
        rewrite <- (handle_gep_addr_array_same_block _ _ _ _ HSRC_GEP).
        intros BLOCKS; symmetry in BLOCKS; revert BLOCKS.

        cbn in st_no_llvm_ptr_aliasing.
        eapply st_no_llvm_ptr_aliasing.
        5: eauto.
        3-4: eauto.
        all: eauto.
    }

    econstructor.

    (* Load src *)
    rewrite denote_instr_load.
    2: {
      apply denote_exp_LR.

      cbn.
      eauto.
    }
    2: {
      erewrite LINV_MEXT_OLD; eauto; [|solve_allocated | ].
      erewrite MEXT_INIT_OLD; eauto.

      solve_read. solve_allocated.
      admit. admit. (*[no_overlap_dtyp] obligations *)
    }

    vred.
    rewrite map_app.
    cbn.
    typ_to_dtyp_simplify.
    rewrite denote_code_cons.
    vred; hred.

    (* Load dst *)
    rewrite denote_instr_load; [|apply denote_exp_LR; cbn; solve_alist_in|solve_read].

    cbn.
    vred.

    rewrite denote_code_app.
    vred.
    rewrite bind_bind.

    (* FIXME : proof repaired up until this point *)
  (*   change (map (λ '(id1, i), (Endo_instr_id id1, Fmap_instr typ dtyp (typ_to_dtyp []) i)) c2) with (convert_typ [] c2). *)

  (*   eapply eutt_clo_bind_returns. *)
  (*   { *)
  (*     eapply genAExpr_correct. *)
  (*     eauto. *)
  (*     { eapply state_invariant_enter_scope_DSHCType' with (s1:={| block_count := block_count i19; local_count := local_count i19; void_count := void_count i19; Γ := (ID_Local dst_val_id, TYPE_Double) :: Γ i19 |}); cbn; eauto. *)

  (*       eapply lid_bound_before; [solve_lid_bound | solve_local_count]. *)
  (*       2: solve_alist_in. *)

  (*       { pose proof GAM. *)
  (*         unfold Gamma_safe in H. *)
  (*         assert (~ in_Gamma σ s1 src_val_id) by solve_not_in_gamma. *)
  (*         assert (Γ s1 ≡ Γ i19) by solve_gamma. *)

  (*         eapply not_in_gamma_cons; [cbn; eauto; try solve_gamma | solve_not_in_gamma |]. *)

  (*         (* TODO: add this to solve_not_in_gamma? *) *)
  (*         intros CONTRA; subst. *)

  (*         match goal with *)
  (*         | H1: incLocal _ ≡ inr (_, dst_val_id), *)
  (*               H2: incLocal _ ≡ inr (_, dst_val_id) |- _ *)
  (*           => eapply lid_bound_between_incLocal in H1; *)
  (*               eapply lid_bound_between_incLocal in H2; *)
  (*               eapply state_bound_between_id_separate;[|eapply H1|eapply H2|solve_local_count]; *)
  (*                 eapply incLocalNamed_count_gen_injective *)
  (*         end. *)
  (*       } *)

  (*       eapply state_invariant_enter_scope_DSHCType'; cbn. *)
  (*       eauto. *)
  (*       eauto. *)
  (*       3: solve_local_count. *)

  (*       eapply lid_bound_before; [solve_lid_bound | solve_local_count]. *)
  (*       eapply not_in_Gamma_Gamma_eq with (s1 := s1); [solve_gamma|solve_not_in_gamma]. *)

  (*       { solve_alist_in. *)
  (*       } *)

  (*       eapply state_invariant_same_Γ' with (s1:=s2); eauto. *)
  (*       solve_gamma. *)
  (*       { get_gamma_bounds. *)
  (*         assert (Γ i8 ≡ Γ i19) by solve_gamma. *)
  (*         eapply gamma_bound_mono. *)
  (*         apply PostYoffSINV. *)
  (*         solve_local_count. *)
  (*         eauto. *)
  (*       } *)

  (*       { eapply not_in_Gamma_Gamma_eq; eauto. *)
  (*         eapply not_in_gamma_protect. *)
  (*         eapply GAM. *)
  (*         solve_lid_bound_between. *)
  (*       } *)

  (*       eapply state_invariant_same_Γ with (s1:=s2); eauto. *)
  (*       { eapply not_in_Gamma_Gamma_eq; eauto. *)
  (*         eapply not_in_gamma_protect. *)
  (*         eapply GAM. *)
  (*         solve_lid_bound_between. *)
  (*       } *)

  (*     } *)

  (*     { eapply Gamma_safe_Context_extend. *)
  (*       eapply Gamma_safe_Context_extend. *)
  (*       9: { cbn. *)
  (*            change ((ID_Local dst_val_id, TYPE_Double) :: Γ i19) with (Γ {| block_count := block_count i19; local_count := local_count i19; void_count := void_count i19; Γ := (ID_Local dst_val_id, TYPE_Double) :: Γ i19 |}). *)
  (*            reflexivity. *)
  (*       } *)
  (*       4: { *)
  (*         cbn. *)
  (*         reflexivity. *)
  (*       } *)

  (*       { eapply Gamma_safe_protect. *)
  (*         eapply Gamma_safe_shrink; eauto. *)
  (*         solve_gamma. *)
  (*         solve_local_count. *)
  (*       } *)
  (*       3: { *)
  (*         instantiate (1 := {| block_count := block_count i20; local_count := local_count i20; void_count := void_count i20; Γ := (ID_Local dst_val_id, TYPE_Double) :: Γ i19 |}). *)
  (*         cbn. *)
  (*         solve_gamma. *)
  (*       } *)

  (*       all: try (solve [cbn; solve_local_count]). *)

  (*       { intros ? ?. *)
  (*         solve_id_neq. *)
  (*       } *)

  (*       cbn. *)
  (*       solve_gamma. *)

  (*       { intros ? ?. *)
  (*         solve_id_neq. *)
  (*       } *)
  (*     } *)

  (*     { unfold denoteBinCType in NOFAIL. *)
  (*       eapply no_failure_bind_prefix in NOFAIL. *)
  (*       eapply no_failure_helix_bind_prefix in NOFAIL. *)
  (*       eauto. *)
  (*     } *)
  (*   } *)

  (*   intros [[mH_Aexpr t_Aexpr]|] [mV_Aexpr [l_Aexpr [g_Aexpr []]]] POST RetAexp RetAexpCode; [|inv POST]. *)
  (*   destruct POST as [POSTAEXPRSINV POSTAEXPR]. *)

  (*   hred. *)
  (*   vred. *)

  (*   forward LINV_MEXT_NEW; [cbn; lia|]. *)
  (*   edestruct (@read_write_succeeds mV_loop dst_addr _ _ (DVALUE_Double t_Aexpr) LINV_MEXT_NEW) as [mV' WRITE]; [constructor|]. *)

  (*   erewrite denote_instr_store; eauto. *)

  (*   2: { *)
  (*     destruct POSTAEXPR. *)
  (*     cbn in exp_correct. *)
  (*     cbn in POSTAEXPRSINV. *)
  (*     eapply exp_correct. *)
  (*     solve_local_scope_preserved. *)
  (*     solve_gamma_preserved. *)
  (*   } *)
  (*   3: { *)
  (*     cbn. reflexivity. *)
  (*   } *)
  (*   3: { *)
  (*     destruct POSTAEXPR; cbn in is_almost_pure. *)
  (*     assert (mV_Aexpr ≡ mV_loop) by intuition; subst. *)
  (*     apply WRITE. *)
  (*   } *)
  (*   2: { *)
  (*     eapply denote_exp_LR. *)
  (*     destruct POSTAEXPR. *)

  (*     cbn in extends. *)
  (*     cbn. *)

  (*     erewrite local_scope_modif_out. *)
  (*     4: eapply extends. *)
  (*     3: solve_lid_bound_between; cbn; solve_local_count. *)
  (*     2: cbn; solve_local_count. *)

  (*     solve_alist_in. *)
  (*   } *)

  (*   vred. *)
  (*   rewrite denote_term_br_1. *)
  (*   vred. *)

  (*   cbn. *)
  (*   rename b into jump_label. *)
  (*   rewrite denote_ocfg_unfold_not_in. *)
  (*   vred. *)
  (*   2: { *)
  (*     cbn. *)
  (*     assert (b0 ≢ jump_label) as NEQ by solve_id_neq. *)
  (*     rewrite find_block_ineq; eauto. *)
  (*   } *)

  (*   apply eqit_Ret. *)
  (*   split; [|split; [|split]]. *)
  (*   - destruct POSTAEXPR. *)
  (*     cbn in *. *)
  (*     destruct Mono_IRState. *)
  (*     + eapply local_scope_preserve_modif_up in extends. *)
  (*       unfold local_scope_preserved in extends. *)
  (*       rewrite extends. *)
  (*       rewrite alist_find_neq. *)
  (*       2: { intros ID; symmetry in ID; revert ID. *)
  (*            eapply state_bound_between_separate. *)
  (*            eapply incLocalNamed_count_gen_injective. *)
  (*            solve_lid_bound_between. *)
  (*            solve_lid_bound_between. *)
  (*            solve_local_count. *)
  (*       } *)
  (*       2: { unfold lid_bound_between. *)
  (*            unfold state_bound_between. *)
  (*            exists "Power_i". eexists. eexists. *)
  (*            repeat split; eauto. *)
  (*            2: solve_local_count. *)
  (*            instantiate (1 := {| *)
  (*                            block_count := block_count i21; *)
  (*                            local_count := S (local_count i21); *)
  (*                            void_count := void_count i21; *)
  (*                            Γ := Γ i21 |}). *)
  (*            solve_local_count. *)
  (*       } *)
  (*       solve_alist_in. *)
  (*     + subst. *)
  (*       (* Brutally long *) *)
  (*       solve_alist_in. *)
  (*   - exists b0. reflexivity. *)
  (*   - (* I *) *)
  (*     Opaque mem_lookup. (* TODO: HMMM *) *)
  (*     cbn. *)
  (*     split. *)
  (*     { (* TODO: destruct POSTAEXPR in like one place? Maybe *)
  (*              automate pulling out almost_pure? *) *)
  (*       pose proof POSTAEXPR as PUREAEXPR. *)
  (*       apply is_almost_pure in PUREAEXPR. *)
  (*       cbn in PUREAEXPR. destruct PUREAEXPR as [? [? ?]]. *)
  (*       subst. *)
  (*       eauto. *)

  (*       pose proof POSTAEXPR as AEXPR_LSM. *)
  (*       eapply extends in AEXPR_LSM. *)
  (*       cbn in AEXPR_LSM. *)

  (*       destruct POSTAEXPR. *)
  (*       cbn in POSTAEXPRSINV. *)

  (*       destruct POSTAEXPRSINV. *)
  (*       cbn in st_no_llvm_ptr_aliasing. *)

  (*       destruct LINV_SINV. *)
  (*       eauto. *)

  (*       split; auto. *)
  (*       (* TODO: can I pull these out into lemmas? *) *)
  (*       (* TODO: probably similar to state_invariant_escape_scope, but with a write *) *)
  (*       (* TODO: might want to not destruct and look at the state_invariant_write_double stuff? *) *)
  (*       - cbn in extends. *)
  (*         unfold memory_invariant. *)
  (*         pose proof mem_is_inv as MINV. *)
  (*         unfold memory_invariant in MINV. *)
  (*         intros n v0 b τ x NTH_σ NTH_Γ. *)

  (*         pose proof NTH_σ as NTH_σ_orig. *)
  (*         pose proof NTH_Γ as NTH_Γ_orig. *)
  (*         do 2 erewrite <- nth_error_Sn in NTH_σ. *)
  (*         do 2 erewrite <- nth_error_Sn in NTH_Γ. *)

  (*         pose proof Heqo0 as NTH_σ_dst. *)
  (*         apply nth_error_protect_eq' in NTH_σ_dst. *)
  (*         do 2 erewrite <- nth_error_Sn in NTH_σ_dst. *)

  (*         cbn in Gamma_cst. *)
  (*         assert (Γ s2 ≡ Γ i19) as Γ_s2i19 by solve_gamma. *)

  (*         pose proof LUn0 as NTH_Γ_dst. *)
  (*         do 2 erewrite <- nth_error_Sn in NTH_Γ_dst. *)
  (*         rewrite Γ_S1S2 in NTH_Γ_dst. *)
  (*         rewrite Γ_s2i19 in NTH_Γ_dst. *)
  (*         rewrite <- Gamma_cst in NTH_Γ_dst. *)

  (*         rewrite Γ_s2i19 in NTH_Γ. *)
  (*         rewrite <- Gamma_cst in NTH_Γ. *)

  (*         specialize (MINV _ _ _ _ _ NTH_σ NTH_Γ). *)

  (*         (* TODO: automate this? *) *)
  (*         assert (local_scope_modif s1 s2 l l_Aexpr) as LSM_FULL. *)
  (*         { nexpr_modifs. *)
  (*           Ltac solve_single_trans_local_scope_modif := *)
  (*             match goal with *)
  (*             | L1 : local_scope_modif ?s1 ?s2 ?l1 ?l2, *)
  (*                    L2 : local_scope_modif ?s2 ?s3 ?l2 ?l3 *)
  (*               |- local_scope_modif ?s1 ?s3 ?l1 ?l3 *)
  (*               => eapply (local_scope_modif_trans'' L1 L2); solve_local_count *)
  (*             end. *)
  (*           Hint Extern 1 (local_scope_modif _ _ _ _) => solve_single_trans_local_scope_modif : LSM. *)

  (*           pose proof LINV_LSM as LSM'. *)
  (*           eapply local_scope_modif_shrink with (s1 := i8) (s4:= s2) in LSM'; solve_local_count. *)
  (*           eapply local_scope_modif_sub'_l in LSM'; [|solve_lid_bound_between]. *)
  (*           eapply local_scope_modif_sub'_l in LSM'; [|solve_lid_bound_between]. *)
  (*           epose proof local_scope_modif_trans'' LSM_yoff LSM'. *)
  (*           repeat (forward H; solve_local_count). *)
  (*           pose proof extends. *)
  (*           eapply local_scope_modif_shrink with (s1 := i8) (s4:= s2) in H0; solve_local_count. *)
  (*           eapply local_scope_modif_sub'_l in H0; [|solve_lid_bound_between]. *)
  (*           eapply local_scope_modif_sub'_l in H0; [|solve_lid_bound_between]. *)
  (*           epose proof local_scope_modif_trans'' H H0. *)
  (*           repeat (forward H4; solve_local_count). *)
  (*           solve_local_scope_modif. *)
  (*         } *)

  (*         destruct x, v0; eauto. *)
  (*         + cbn in MINV. cbn. *)
  (*           destruct MINV as (ptr & τ' & TEQ & FIND & READ). *)
  (*           exists ptr. exists τ'. *)
  (*           repeat split; eauto. *)

  (*           pose proof (IRState_is_WF _ _ _ NTH_σ) as (id' & NTH_Γ'). *)
  (*           (* id can not be id_addr because of the different *)
  (*                    type, and thus must be in a different block *) *)

  (*           (* Find τ' *) *)
  (*           rewrite NTH_Γ in NTH_Γ'; inv NTH_Γ'. *)
  (*           cbn in H1. inv H1. *)

  (*           eapply write_different_blocks; eauto. *)
  (*           2: reflexivity. *)
  (*           2-3: typ_to_dtyp_simplify; constructor. *)

  (*           rewrite <- (handle_gep_addr_array_same_block _ _ _ _ HDST_GEP); eauto. *)

  (*           intros EQ; symmetry in EQ; revert EQ. *)
  (*           eapply st_no_llvm_ptr_aliasing. *)
  (*           eapply NTH_σ. *)
  (*           { do 2 rewrite nth_error_Sn. *)
  (*             apply (nth_error_protect_eq' n3 _ Heqo0). *)
  (*           } *)
  (*           eapply NTH_Γ. *)
  (*           rewrite Gamma_cst. *)
  (*           do 2 rewrite nth_error_Sn. *)
  (*           rewrite <- Γ_s2i19. rewrite <- Γ_S1S2. *)
  (*           eauto. *)
  (*           { intros CONTRA; inv CONTRA. *)
  (*             epose proof (st_no_id_aliasing _ _ _ _ _ _ _ NTH_σ NTH_σ_dst NTH_Γ NTH_Γ_dst) as EQ; inv EQ. *)

  (*             rewrite NTH_Γ in NTH_Γ_dst; inv NTH_Γ_dst. *)
  (*           } *)
  (*           eauto. *)
  (*           { destruct i3. *)
  (*             - eauto. *)
  (*             - assert (lid_bound s1 id0) as LID_BOUND0 by (eapply Correctness_Invariants.st_gamma_bound; solve_lid_bound). *)
  (*               cbn; erewrite <- local_scope_modif_bound_before with (s2:=s2); eauto. *)
  (*           } *)
  (*         + cbn in MINV. cbn. *)
  (*           destruct MINV as (ptr & τ' & TEQ & FIND & READ). *)
  (*           exists ptr. exists τ'. *)
  (*           repeat split; eauto. *)

  (*           pose proof (IRState_is_WF _ _ _ NTH_σ) as (id' & NTH_Γ'). *)
  (*           (* id can not be id_addr because of the different *)
  (*                    type, and thus must be in a different block *) *)

  (*           (* Find τ' *) *)
  (*           rewrite NTH_Γ in NTH_Γ'; inv NTH_Γ'. *)
  (*           cbn in H1. inv H1. *)

  (*           eapply write_different_blocks; eauto. *)
  (*           2: reflexivity. *)
  (*           2-3: typ_to_dtyp_simplify; constructor. *)

  (*           rewrite <- (handle_gep_addr_array_same_block _ _ _ _ HDST_GEP); eauto. *)

  (*           intros EQ; symmetry in EQ; revert EQ. *)
  (*           eapply st_no_llvm_ptr_aliasing. *)
  (*           eapply NTH_σ. *)
  (*           { do 2 rewrite nth_error_Sn. *)
  (*             apply (nth_error_protect_eq' n3 _ Heqo0). *)
  (*           } *)
  (*           eapply NTH_Γ. *)
  (*           rewrite Gamma_cst. *)
  (*           do 2 rewrite nth_error_Sn. *)
  (*           rewrite <- Γ_s2i19. rewrite <- Γ_S1S2. *)
  (*           eauto. *)
  (*           { intros CONTRA; inv CONTRA. *)

  (*             epose proof (st_no_id_aliasing _ _ _ _ _ _ _ NTH_σ NTH_σ_dst NTH_Γ NTH_Γ_dst) as EQ; inv EQ. *)

  (*             rewrite NTH_Γ in NTH_Γ_dst; inv NTH_Γ_dst. *)
  (*           } *)
  (*           eauto. *)
  (*           { destruct i3. *)
  (*             - eauto. *)
  (*             - assert (lid_bound s1 id0) as LID_BOUND0 by (eapply Correctness_Invariants.st_gamma_bound; solve_lid_bound). *)
  (*               cbn; erewrite <- local_scope_modif_bound_before with (s2:=s2); eauto. *)
  (*           } *)
  (*         + (* Global vector *) *)
  (*           cbn in MINV. *)
  (*           destruct MINV as (ptr & τ' & TEQ & FITS & INLG' & LUP). *)
  (*           inv TEQ. *)
  (*           exists ptr. exists τ'. *)
  (*           repeat split; eauto. *)
  (*           eapply dtyp_fits_after_write; eauto. *)
  (*           intros H; destruct b; inv H. *)
  (*           specialize (LUP eq_refl). *)
  (*           destruct LUP as (bkh & MLUP_bk & GETARRAYCELL). *)
  (*           exists bkh. *)
  (*           split; eauto. *)
  (*           intros i v0 H. *)
  (*           specialize (GETARRAYCELL _ _ H). *)

  (*           erewrite write_untouched_ptr_block_get_array_cell; eauto. *)

  (*           rewrite <- (handle_gep_addr_array_same_block _ _ _ _ HDST_GEP); eauto. *)

  (*           eapply st_no_llvm_ptr_aliasing. *)
  (*           eapply NTH_σ. *)
  (*           eapply NTH_σ_dst. *)
  (*           eapply NTH_Γ. *)
  (*           eapply NTH_Γ_dst. *)
  (*           2-3: eauto. *)
  (*           intros CONTRA; inv CONTRA. *)
  (*           assert (S (S n) ≡ S (S n3)). *)
  (*           { eapply st_no_id_aliasing; eauto. } *)
  (*           inv H0. *)
  (*           apply protect_eq_true in NTH_σ_orig. *)
  (*           inv NTH_σ_orig. *)
  (*           { destruct i3. *)
  (*             - eauto. *)
  (*             - assert (lid_bound s1 id0) as LID_BOUND0 by (eapply Correctness_Invariants.st_gamma_bound; solve_lid_bound). *)
  (*               cbn; erewrite <- local_scope_modif_bound_before with (s2:=s2); eauto. *)
  (*           } *)
  (*         + (* Local vector *) *)
  (*           cbn in MINV. *)
  (*           destruct MINV as (ptr & τ' & TEQ & FITS & INLG' & LUP). *)
  (*           inv TEQ. *)
  (*           exists ptr. exists τ'. *)
  (*           repeat split; eauto. *)
  (*           eapply dtyp_fits_after_write; eauto. *)
  (*           intros H; destruct b; inv H. *)
  (*           specialize (LUP eq_refl). *)
  (*           destruct LUP as (bkh & MLUP_bk & GETARRAYCELL). *)
  (*           exists bkh. *)
  (*           split; eauto. *)
  (*           intros i v0 H. *)
  (*           specialize (GETARRAYCELL _ _ H). *)

  (*           erewrite write_untouched_ptr_block_get_array_cell; eauto. *)

  (*           rewrite <- (handle_gep_addr_array_same_block _ _ _ _ HDST_GEP); eauto. *)

  (*           eapply st_no_llvm_ptr_aliasing. *)
  (*           eapply NTH_σ. *)
  (*           eapply NTH_σ_dst. *)
  (*           eapply NTH_Γ. *)
  (*           eapply NTH_Γ_dst. *)

  (*           intros CONTRA; inv CONTRA. *)
  (*           assert (S (S n3) ≡ S (S n)). *)
  (*           { eapply st_no_id_aliasing; eauto. } *)
  (*           inv H0. *)
  (*           apply protect_eq_true in NTH_σ_orig. *)
  (*           inv NTH_σ_orig. *)
  (*           { destruct i3. *)
  (*             - eauto. *)
  (*             - assert (lid_bound s1 id0) as LID_BOUND0 by (eapply Correctness_Invariants.st_gamma_bound; solve_lid_bound). *)
  (*               cbn; erewrite <- local_scope_modif_bound_before with (s2:=s2); eauto. *)
  (*           } *)
  (*           { destruct i3. *)
  (*             - eauto. *)
  (*             - assert (lid_bound s1 id0) as LID_BOUND0 by (eapply Correctness_Invariants.st_gamma_bound; solve_lid_bound). *)
  (*               cbn; erewrite <- local_scope_modif_bound_before with (s2:=s2); eauto. *)
  (*           } *)
  (*       - eapply no_llvm_ptr_aliasing_cons2; eauto. *)
  (*         { cbn in Gamma_cst. *)
  (*           rewrite Gamma_cst. *)
  (*           apply ListUtil.tail_eq. *)
  (*           apply ListUtil.tail_eq. *)
  (*           solve_gamma. *)
  (*         } *)
  (*     } *)

  (*     destruct POSTAEXPR. cbn in extends. *)
  (*     cbn in Mono_IRState. *)

  (*     split. *)
  (*     { (* dst_ptr_id *) *)
  (*       destruct Mono_IRState; subst; solve_alist_in. *)
  (*     } *)

  (*     split. *)
  (*     { (* src_ptr_id *) *)
  (*       destruct Mono_IRState; subst; solve_alist_in. *)
  (*     } *)

  (*     split. *)
  (*     { eapply local_scope_modif_trans'. (* TODO: automate this? *) *)
  (*       solve_local_scope_modif. *)

  (*       eapply local_scope_modif_sub'_l with (r := src_val_id). *)
  (*       solve_lid_bound_between. *)

  (*       eapply local_scope_modif_sub'_l with (r := dst_val_id). *)
  (*       solve_lid_bound_between. *)

  (*       solve_local_scope_modif. *)
  (*     } *)

  (*     split. *)
  (*     { cbn in is_almost_pure. *)
  (*       destruct is_almost_pure as [_ [_ G]]. *)
  (*       subst. *)
  (*       auto. *)
  (*     } *)

  (*     split. *)
  (*     { eapply write_preserves_allocated; eauto. *)
  (*     } *)

  (*     split. *)
  (*     { (* Returns... *) *)
  (*       rewrite tfor_split with (i := 0) (j:= k) (k0:= S k); try lia. *)
  (*       rewrite interp_helix_bind. *)
  (*       eapply Returns_bind; eauto. *)
  (*       cbn. *)

  (*       rewrite tfor_unroll; [|lia]. *)
  (*       rewrite interp_helix_bind. *)

  (*       eapply mem_lookup_err_inr_Some_eq in MEMLUP_xoff. *)
  (*       erewrite MEMLUP_xoff. *)
  (*       cbn. *)
  (*       rewrite bind_ret_l. *)
  (*       unfold denoteBinCType. *)

  (*       eapply Returns_bind. *)

  (*       { rewrite interp_helix_bind. *)
  (*         eapply Returns_bind; eauto. *)
  (*         unfold mem_lookup_err. *)
  (*         rewrite LINV_HELIX_MB_NEW. *)
  (*         cbn. *)
  (*         rewrite interp_helix_ret. *)
  (*         cbn. *)

  (*         constructor. *)
  (*         reflexivity. *)

  (*         rewrite interp_helix_bind. *)
  (*         eapply Returns_bind; eauto. *)
  (*         cbn. *)

  (*         rewrite interp_helix_ret. *)
  (*         cbn. *)

  (*         constructor. *)
  (*         reflexivity. *)
  (*       } *)

  (*       cbn. *)
  (*       rewrite tfor_0. *)
  (*       rewrite interp_helix_ret. *)
  (*       cbn. *)
  (*       constructor. *)
  (*       reflexivity. *)
  (*     } *)

  (*     split. *)
  (*     { (* Helix memory old *) *)
  (*       intros y H. *)
  (*       rewrite mem_lookup_mem_add_neq; eauto. *)
  (*     } *)

  (*     exists t_Aexpr. *)
  (*     split. *)
  (*     { (* Helix memory extended *) *)
  (*       rewrite mem_lookup_mem_add_eq; eauto. *)
  (*     } *)

  (*     { eapply write_correct in WRITE. *)
  (*       destruct WRITE as [ALLOCATED WRITTEN]. *)

  (*       eapply ext_memory_trans; eauto. *)
  (*       eapply WRITTEN. constructor. *)
  (*     } *)

  (*   - (* local_scope_modif sb1 sb2 li l *) *)
  (*     destruct POSTAEXPR. cbn in extends. *)

  (*     cbn in Mono_IRState. *)
  (*     cbn in Gamma_cst. *)

  (*     eapply local_scope_modif_sub'_l with (r:=src_val_id). *)
  (*     solve_lid_bound_between. *)

  (*     eapply local_scope_modif_sub'_l with (r:=dst_val_id). *)
  (*     solve_lid_bound_between. *)

  (*     solve_local_scope_modif. *)
  (* } *)

  (* (* TODO: Might want to do more forward reasoning first *) *)
  (* match goal with *)
  (* | H: _ |- eutt ?R ?x (interp_cfg ?y ?g ?l ?m) *)
  (*   => rewrite <- (bind_ret_r y) *)
  (* end. *)

  (* setoid_rewrite interp_cfg3_bind. *)
  (* eapply eutt_clo_bind. *)
  (* eapply LOOPTFOR. *)

  (* all: solve_local_count. *)

  (* 6: { *)
  (*   intros [[mH_post mb_post]|] [mV_post [l_post [g_post x_pos]]] [POST [Q_POST LSM_POST]]; [|inv Q_POST]. *)
  (*   rewrite interp_helix_MemSet. *)
  (*   cbn. *)
  (*   vred. *)

  (*   apply eutt_Ret. *)
  (*   unfold genIR_post. *)
  (*   split; cbn. *)

  (*   cbn in Q_POST. *)
  (*   { (* State invariant preserved *) *)
  (*     split; eauto. *)
  (*     eapply st_no_id_aliasing; eauto. *)
  (*     eapply st_no_dshptr_aliasing; eauto. *)
  (*     eapply st_no_llvm_ptr_aliasing; eauto. *)

  (*     (* memory_invariant and id_allocated are the only things that care *)
  (*            about the altered memory *)
  (*      *) *)
  (*     { unfold id_allocated. *)
  (*       intros n addr0 val H. *)

  (*       eapply st_id_allocated in Q_POST. *)
  (*       eauto. *)
  (*     } *)

  (*     get_gamma_bounds; solve_gamma_bound. *)
  (*   } *)

  (*   split. *)
  (*   { (* branches *) *)
  (*     cbn. *)
  (*     inv POST; eexists; eauto. *)
  (*   } *)

  (*   { (* local_scope_modif *) *)
  (*     cbn. *)

  (*     (* TODO: incorporate this into solve_local_scope_modif? *) *)
  (*     repeat *)
  (*       match goal with *)
  (*       | POST: genNExpr_post _ _ _ _ _ _ _ _ |- _ *)
  (*         =>  apply Correctness_NExpr.extends in POST; cbn in POST *)
  (*       end. *)

  (*     eapply local_scope_modif_shrink with (s3:=s2) (s4:=s2) (s1:=i8) in LSM_POST; [|solve_local_count|solve_local_count]. *)
  (*     apply local_scope_modif_sub'_l in LSM_POST; [|solve_lid_bound_between]. *)
  (*     apply local_scope_modif_sub'_l in LSM_POST; [|solve_lid_bound_between]. *)

  (*     solve_local_scope_modif_trans. *)
  (*   } *)
  (* } *)

  (* (* TODO: bunch of stuff to deal with here... *)

  (*        Better nail down the other admits first so we're more *)
  (*        confident in the loop invariant. *)
  (*  *) *)

  (* { (* Invariant is stable under the administrative bookkeeping that the loop performs *) *)
  (*   intros k a l' mV g id1 v BOUND HI. *)
  (*   unfold I in *. *)
  (*   destruct a; try inv HI. *)
  (*   destruct p. *)
  (*   destruct HI as [HI_SINV [HI_DST_PTR_ID [HI_SRC_PTR_ID [HI_LSM [HI_G [HI_ALLOC [HI_RET [HI_HELIX_MB_OLD [HI_v [HI_HELIX_MB_NEW HI_MEXT]]]]]]]]]]. *)
  (*   pose proof HI_MEXT as [HI_MEXT_NEW HI_MEXT_OLD]. *)
  (*   split. *)
  (*   { destruct BOUND. *)
  (*     - eapply state_invariant_same_Γ with (s1 := s2); eauto. *)

  (*       (* No variables were bound between i21 and s2, so H should give us a contradiction *) *)
  (*       eapply not_in_Gamma_Gamma_eq; eauto. *)
  (*       eapply not_in_gamma_protect. *)
  (*       eapply GAM. *)
  (*       eapply lid_bound_between_shrink_down. *)
  (*       2: eapply H. *)
  (*       cbn. *)
  (*       solve_local_count. *)
  (*     - eapply state_invariant_same_Γ with (s1 := s2); eauto. *)

  (*       (* No variables were bound between i21 and s2, so H should give us a contradiction *) *)
  (*       eapply not_in_Gamma_Gamma_eq; eauto. *)
  (*       eapply not_in_gamma_protect. *)
  (*       eapply GAM. *)
  (*       eapply lid_bound_between_shrink. *)
  (*       eauto. *)
  (*       solve_local_count. *)
  (*       cbn; solve_local_count. *)
  (*   } *)

  (*   split. *)
  (*   { destruct BOUND. *)
  (*     solve_alist_in. *)
  (*     erewrite alist_find_neq. *)
  (*     solve_alist_in. *)

  (*     (* TODO: automate this *) *)
  (*     eapply state_bound_between_separate. *)
  (*     eapply incLocalNamed_count_gen_injective. *)
  (*     solve_lid_bound_between. *)
  (*     solve_lid_bound_between. *)
  (*     cbn; solve_local_count. *)
  (*   } *)
  (*   split. *)
  (*   { destruct BOUND. *)
  (*     solve_alist_in. *)
  (*     erewrite alist_find_neq. *)
  (*     solve_alist_in. *)

  (*     (* TODO: automate this *) *)
  (*     eapply state_bound_between_separate. *)
  (*     eapply incLocalNamed_count_gen_injective. *)
  (*     solve_lid_bound_between. *)
  (*     solve_lid_bound_between. *)
  (*     solve_local_count. *)
  (*   } *)

  (*   repeat split; auto. *)

  (*   { destruct BOUND. *)
  (*     - eapply local_scope_modif_add'. *)
  (*       eapply lid_bound_between_shrink. (* TODO: fix lid_bound_between *) *)
  (*       eauto. *)
  (*       solve_local_count. *)
  (*       solve_local_count. *)
  (*       solve_local_scope_modif. *)
  (*     - eapply local_scope_modif_add'. *)
  (*       eapply lid_bound_between_shrink; [solve_lid_bound_between | | ]; eauto; solve_local_count. *)
  (*       solve_local_scope_modif. *)
  (*   } *)

  (*   exists HI_v. *)
  (*   auto. *)
  (* } *)

  (* (* TODO: May need to modify P / Q here *) *)
  (* { (* P -> I 0 *) *)
  (*   unfold imp_rel. intros a b2 PR. *)
  (*   red. red in PR. *)
  (*   destruct a. 2: inv PR. *)
  (*   destruct p as [mH mb]. *)
  (*   destruct b2 as [mV [l' g]]. *)
  (*   destruct PR as [SINV [DST [SRC [LSM [G [MH [MB MV]]]]]]]. *)

  (*   split. *)
  (*   solve [eauto]. *)

  (*   subst. *)
  (*   repeat split; eauto. *)

  (*   { assert (allocated ptrll_yoff mV_yoff); [solve_allocated|]. *)
  (*     eapply write_preserves_allocated; eauto. *)
  (*   } *)

  (*   { rewrite tfor_0. *)
  (*     rewrite interp_helix_ret. cbn. *)
  (*     constructor. *)
  (*     reflexivity. *)
  (*   } *)

  (*   { intros y H. *)
  (*     rewrite mem_lookup_mem_add_neq; eauto. *)
  (*   } *)

  (*   { exists initial. *)
  (*     pose proof (write_correct WRITE_INIT) as [WRITE_ALLOCATED WRITE_EXT]. *)
  (*     split. *)
  (*     - apply mem_lookup_mem_add_eq. *)
  (*     - (* extended LLVM memory *) *)
  (*       specialize (WRITE_EXT DTYPE_Double). *)
  (*       forward WRITE_EXT; [constructor|]. *)
  (*       destruct WRITE_EXT as [WRITE_NEW WRITE_OLD]. *)
  (*       split; eauto. *)
  (*   } *)
  (* } *)

  (* { (* I loop_end -> Q *) *)
  (*   unfold imp_rel. intros a b2 H. *)
  (*   red. red in H. *)
  (*   break_match; try inv H. *)
  (*   break_match_hyp. *)
  (*   break_match_hyp. *)
  (*   break_match_hyp. *)
  (*   destruct H as [SINV [DST [SRC [LSM [G [ALLOCI [RET [MEMH_OLD [v [MEMH_NEW EXT_MEM]]]]]]]]]]. *)
  (*   subst. *)

  (*   eapply state_invariant_write_double_result with (sz:=sz0); eauto. *)
  (*   3: { intros i v0 H H0. *)
  (*        pose proof GETARRAYCELL_yoff. *)
  (*        pose proof get_array_cell_mlup_ext. *)

  (*        pose proof (write_correct WRITE_INIT) as [ALLOC WRITE_EXT]. *)
  (*        specialize (WRITE_EXT DTYPE_Double). *)
  (*        forward WRITE_EXT; [constructor|]. *)

  (*        (* GETARRAYCELL_yoff starts at mV_yoff. mV_init extends that, and m1 extends mV_init *) *)
  (*        epose proof get_array_cell_mlup_ext bkh_yoff ptrll_yoff _ _ _ _ WRITE_EXT. *)
  (*        forward H3. solve_allocated. *)

  (*        epose proof @get_array_cell_mlup_ext' bkh_yoff ptrll_yoff _ _ _ mV_init m1. *)
  (*        epose proof @get_array_cell_mlup_ext' bkh_yoff ptrll_yoff _ _ _ mV_init m1 v H3. *)

  (*        eapply H5; eauto. *)
  (*        rewrite repr_of_nat_to_nat; eauto. *)
  (*   } *)
  (*   rewrite <- Γ_S1S2; eauto. *)
  (*   eauto. *)

  (*   { (* Should be able to use INLG_yoff *) *)
  (*     cbn. cbn in INLG_yoff. *)

  (*     (* TODO: another automation candidate. *) *)
  (*     nexpr_modifs. *)
  (*     epose proof local_scope_modif_trans'' PostLoopEndNExpr PostXoffNExpr. *)
  (*     repeat (forward H; solve_local_count). *)
  (*     epose proof local_scope_modif_trans'' H PostYoffNExpr. *)
  (*     repeat (forward H0; solve_local_count). *)
  (*     pose proof LSM. *)
  (*     eapply local_scope_modif_shrink with (s1 := i8) (s4:= s2) in H1; solve_local_count. *)
  (*     eapply local_scope_modif_sub'_l in H1; [|solve_lid_bound_between]. *)
  (*     eapply local_scope_modif_sub'_l in H1; [|solve_lid_bound_between]. *)
  (*     epose proof local_scope_modif_trans'' H0 H1. *)
  (*     repeat (forward H2; solve_local_count). *)

  (*     { destruct i3. *)
  (*       - eauto. *)
  (*       - assert (lid_bound s1 id) as LID_BOUND0 by (eapply Correctness_Invariants.st_gamma_bound; solve_lid_bound). *)
  (*         cbn; erewrite <- local_scope_modif_bound_before with (s2:=s2); eauto. *)
  (*         solve_lid_bound. *)
  (*     } *)
  (*   } *)
  (* } *)

  (* { (* IDENT *) *)
  (*   intros x H; inv H. *)
  (*   pose proof (genNExpr_ident_bound _ Heqs3 GBi5). *)
  (*   repeat (rewrite alist_find_neq); try solve_id_neq. *)
  (*   pose proof PostLoopEndNExpr. *)
  (*   destruct H0. *)
  (*   cbn in *. *)
  (*   (* This is where I need exp_in_scope... *) *)
  (*   pose proof (exp_in_scope x eq_refl). *)
  (*   destruct H0 as [[INL BOUNDX] | [INL [BOUNDX LT]]]; unfold alist_In in INL. *)
  (*   - *)

  (*     edestruct lid_bound_before_bound_between with (s2 := i5) (id:=x). *)
  (*     solve_lid_bound. *)
  (*     solve_local_count. *)

  (*     destruct Mono_IRState. *)
  (*     + erewrite local_scope_preserve_modif. *)
  (*       eauto. *)
  (*       2: solve_local_scope_modif. *)
  (*       solve_local_count. *)
  (*       eauto. *)
  (*     + subst. *)
  (*       erewrite local_scope_preserve_modif; eauto. *)
  (*   - nexpr_modifs. *)
  (*     epose proof local_scope_modif_trans'' PostXoffNExpr PostYoffNExpr as LSM_yoff'. *)
  (*     repeat (forward LSM_yoff'; solve_local_count). *)

  (*     erewrite local_scope_preserve_modif. *)
  (*     eauto. *)
  (*     2: eauto. *)
  (*     solve_local_scope_modif. *)
  (* } *)

  (* { (* P holds initially *) *)
  (*   red. *)
  (*   split. *)
  (*   { (* State invariant *) *)
  (*     repeat *)
  (*       (eapply state_invariant_same_Γ'; cycle 1; *)
  (*        [get_gamma_bounds; solve_gamma_bound | solve_not_in_gamma | | solve_gamma]). *)

  (*     assert (Γ s2 ≡ Γ i8) as Γ_s2i8 by solve_gamma. *)
  (*     eapply state_invariant_Γ' with (s1:=i8); [eauto|eauto|get_gamma_bounds; solve_gamma_bound]. *)
  (*     { destruct i3. *)
  (*       { eapply write_state_invariant with (ptrll := ptrll_yoff) (dst_addr := dst_addr). *)
  (*         eauto. *)
  (*         assert (Γ s1 ≡ Γ i8) as Γ_s1i8 by solve_gamma. *)
  (*         rewrite <- Γ_s1i8. eauto. *)
  (*         eauto. *)
  (*         eauto. *)
  (*         eapply handle_gep_addr_array_same_block; eauto. *)
  (*         eauto. *)
  (*         constructor. *)
  (*       } *)
  (*       { eapply write_state_invariant with (ptrll := ptrll_yoff) (dst_addr := dst_addr). *)
  (*         eauto. *)
  (*         assert (Γ s1 ≡ Γ i8) as Γ_s1i8 by solve_gamma. *)
  (*         rewrite <- Γ_s1i8. eauto. *)
  (*         eauto. *)
  (*         { (* another alist in thing *) *)
  (*           assert (lid_bound s1 id) as LID_BOUND0 by (eapply Correctness_Invariants.st_gamma_bound; solve_lid_bound). *)
  (*           cbn. cbn in INLG_yoff. *)

  (*           nexpr_modifs. *)
  (*           epose proof local_scope_modif_trans'' PostLoopEndNExpr PostXoffNExpr. *)
  (*           repeat (forward H; solve_local_count). *)
  (*           epose proof local_scope_modif_trans'' H PostYoffNExpr. *)
  (*           repeat (forward H0; solve_local_count). *)
  (*           cbn; erewrite <- local_scope_modif_bound_before with (s2:=i8); eauto. *)
  (*           solve_lid_bound. *)
  (*         } *)
  (*         eapply handle_gep_addr_array_same_block; eauto. *)
  (*         eauto. *)
  (*         constructor. *)
  (*       } *)
  (*     } *)
  (*   } *)

  (*   (* Local environments *) *)
  (*   repeat split; solve_alist_in. *)
  (* } *)

  (* Unshelve. *)
  (* all: eauto. *)
    (* all: eapply from_N_intval in EQsz0; subst; auto. *)
Admitted.
