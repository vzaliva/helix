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

  Definition DSHPower_tfor_body (σ : evalContext) (f : AExpr) (xv : binary64) (y : mem_block) (yoffset : nat) (acc : mem_block) :=
    yv <- lift_Derr (mem_lookup_err "Error reading 'yv' memory in denoteDSHBinOp" yoffset acc) ;;
    v' <- denoteBinCType σ f yv xv ;;
    ret (mem_add yoffset v' acc).

  Definition DSHPower_tfor
             (σ: evalContext)
             (n: nat)
             (f: AExpr)
             (xv : binary64)
             (y: mem_block)
             (yoffset: nat) :
    itree Event mem_block
    :=
      tfor (fun i acc =>
              DSHPower_tfor_body σ f xv y yoffset acc
           ) 0 n y.

  Definition DSHPower_interpreted_tfor
             {E}
             (σ: evalContext)
             (n: nat)
             (f: AExpr)
             (xv : binary64)
             (y: mem_block)
             (yoffset: nat) m
    : itree E (option (memoryH * mem_block))
    :=
      tfor (fun i acc =>
              match acc with
              | None => Ret None
              | Some (m',acc) =>
                interp_helix (DSHPower_tfor_body σ f xv y yoffset acc) m'
              end
           ) 0 n (Some (m, y)).

  Lemma denoteDSHPower_as_tfor :
    forall (σ: evalContext)
      (n: nat)
      (f: AExpr)
      (xv : binary64)
      (y: mem_block)
      (yoffset: nat),
      denoteDSHPower σ n f xv y yoffset
                     ≈
                     DSHPower_tfor σ n f xv y yoffset.
  Proof.
    intros σ n; revert σ.
    induction n; unfold DSHPower_tfor; intros σ f xv y yoffset.
    - cbn.
      rewrite tfor_0.
      reflexivity.
    - cbn.
      rewrite tfor_unroll_down; [|lia|].
      + cbn.
        repeat setoid_rewrite bind_bind.
        eapply eutt_clo_bind; [reflexivity|].
        intros u1 u2 H; subst.
        eapply eutt_clo_bind; [reflexivity|].
        intros u0 u3 H0.
        subst.
        rewrite bind_ret_l.
        unfold DSHPower_tfor in IHn.
        subst.
        apply IHn.
      + intros x0 i j.
        reflexivity.
  Qed.

  Lemma denoteDSHPower_interpreted_as_tfor :
    forall (σ: evalContext)
      (n: nat)
      (f: AExpr)
      (xv : binary64)
      (y: mem_block)
      (yoffset: nat) m E,
      interp_helix (E:=E) (denoteDSHPower σ n f xv y yoffset) m
                     ≈
                     DSHPower_interpreted_tfor σ n f xv y yoffset m.
  Proof.
    intros.
    rewrite denoteDSHPower_as_tfor.
    unfold DSHPower_tfor.
    rewrite interp_helix_tfor; [|lia].
    cbn.
    apply eutt_tfor.
    intros [[m' acc]|] i; [| reflexivity].
    unfold DSHPower_tfor_body.
    cbn.
    repeat rewrite interp_helix_bind.
    rewrite bind_bind.
    apply eutt_eq_bind; intros [[?m ?] |]; [| rewrite bind_ret_l; reflexivity].
    bind_ret_r2.
    apply eutt_eq_bind.
    intros [|]; reflexivity.
  Qed.

  Lemma DSHPower_as_tfor : forall σ ne x_p xoffset y_p yoffset f initial,
      denoteDSHOperator σ (DSHPower ne (x_p,xoffset) (y_p,yoffset) f initial)
                        ≈
                        '(x_i,x_size) <- denotePExpr σ x_p ;;
      '(y_i,y_size) <- denotePExpr σ y_p ;;
      x <- trigger (MemLU "Error looking up 'x' in DSHPower" x_i) ;;
      y <- trigger (MemLU "Error looking up 'y' in DSHPower" y_i) ;;
      n <- denoteNExpr σ ne ;; (* [n] denoteuated once at the beginning *)
      xoff <- denoteNExpr σ xoffset ;;
      yoff <- denoteNExpr σ yoffset ;;
      lift_Derr (assert_NT_lt "DSHPower 'y' offset out of bounds" yoff y_size) ;;
      xv <- lift_Derr (mem_lookup_err "Error reading 'xv' memory in denoteDSHBinOp" (MInt64asNT.to_nat xoff) x) ;;
      let y' := mem_add (MInt64asNT.to_nat yoff) initial y in
      y'' <- DSHPower_tfor σ (MInt64asNT.to_nat n) f xv y' (MInt64asNT.to_nat yoff) ;;
      trigger (MemSet y_i y'').
  Proof.
    intros σ ne x_p xoffset y_p yoffset f initial.
    unfold denoteDSHOperator.
    cbn.
    repeat (eapply eutt_clo_bind; [reflexivity|intros; try break_match_goal; subst]).
    setoid_rewrite denoteDSHPower_as_tfor.
    reflexivity.
  Qed.

  Lemma DSHPower_intepreted_as_tfor : forall σ ne x_p xoffset y_p yoffset f initial E m,
      interp_helix (E := E) (denoteDSHOperator σ (DSHPower ne (x_p,xoffset) (y_p,yoffset) f initial)) m
                        ≈
      interp_helix (E := E)
      ('(x_i,x_size) <- denotePExpr σ x_p ;;
       '(y_i,y_size) <- denotePExpr σ y_p ;;
       x <- trigger (MemLU "Error looking up 'x' in DSHPower" x_i) ;;
       y <- trigger (MemLU "Error looking up 'y' in DSHPower" y_i) ;;
       n <- denoteNExpr σ ne ;; (* [n] denoteuated once at the beginning *)
       xoff <- denoteNExpr σ xoffset ;;
       yoff <- denoteNExpr σ yoffset ;;
       lift_Derr (assert_NT_lt "DSHPower 'y' offset out of bounds" yoff y_size) ;;
       xv <- lift_Derr (mem_lookup_err "Error reading 'xv' memory in denoteDSHBinOp" (MInt64asNT.to_nat xoff) x) ;;
       let y' := mem_add (MInt64asNT.to_nat yoff) initial y in
       y'' <- DSHPower_tfor σ (MInt64asNT.to_nat n) f xv y' (MInt64asNT.to_nat yoff) ;;
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

  (* be careful about local_scope_modif *)
  Lemma DSHPower_body_eutt :
    forall σ f y yoffset acc px py xv xvid yv xtyp xptyp x_c src_nexpr fexpr fexpcode storeid loopcontblock g li mV mH _label body_entry,
          eutt
            (fun x y => True)
            (interp_helix (DSHPower_tfor_body σ f xv y yoffset acc) mH)
            (interp_cfg (denote_ocfg (convert_typ [] [(DSHPower_block body_entry loopcontblock px py xvid yv xtyp xptyp x_c src_nexpr fexpr fexpcode storeid)]) (_label, body_entry)) g li mV).
  Proof.
    intros σ f y yoffset acc px py xv xvid yv xtyp xptyp x_c src_nexpr fexpr fexpcode storeid loopcontblock g li
           mV mH _label body_entry.
    cbn* in *; simp.
    break_match_goal; simp.
    - admit.
    - break_match_goal; simp.
      + admit.
      + unfold DSHPower_block. cbn.
        unfold fmap. unfold Fmap_block.
        cbn.
        rewrite denote_ocfg_unfold_in.
        2: { apply find_block_eq; auto. }

        cbn.
        rewrite denote_block_unfold.
        cbn.
        vstep.
        hstep.
        rewrite denote_no_phis.
        rewrite bind_ret_l.
        vstep.
        rewrite denote_code_cons.
  Admitted.


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

Lemma DSHPower_correct:
  ∀ (n : NExpr) (src dst : MemRef) (f : AExpr) (initial : binary64) (s1 s2 : IRState) (σ : evalContext) (memH : memoryH) (nextblock bid_in bid_from : block_id) (bks : list (LLVMAst.block typ)) (g : global_env) 
    (ρ : local_env) (memV : memoryV),
    genIR (DSHPower n src dst f initial) nextblock s1 ≡ inr (s2, (bid_in, bks))
    → bid_bound s1 nextblock
    → state_invariant σ s1 memH (memV, (ρ, g))
    → Gamma_safe σ s1 s2
    → no_failure (E := E_cfg) (interp_helix (denoteDSHOperator σ (DSHPower n src dst f initial)) memH)
    → eutt (succ_cfg (genIR_post σ s1 s2 nextblock ρ)) (interp_helix (denoteDSHOperator σ (DSHPower n src dst f initial)) memH) (interp_cfg (denote_ocfg (convert_typ [] bks) (bid_from, bid_in)) g ρ memV).
Proof.
  intros n src dst f initial s1 s2 σ memH nextblock bid_in bid_from bks g ρ memV GEN NEXT PRE GAM NOFAIL.

  cbn in * |-; simp.
  rewrite DSHPower_as_tfor; cbn.
  inv_resolve_PVar Heqs0.
  inv_resolve_PVar Heqs1.
  unfold denotePExpr in *.
  cbn* in *.
  destruct u.
  simp; try_abs.
  repeat apply no_failure_Ret in NOFAIL.
  do 2 (apply no_failure_helix_LU in NOFAIL; destruct NOFAIL as (? & NOFAIL & ?); cbn in NOFAIL).

  (* Symbolically reducing the concrete prefix on the Helix side *)
  hred.
  hstep; [eassumption |].
  hred; hstep; [eassumption |].
  hred.

  rename l into loop_blocks.

  assert (wf_ocfg_bid loop_blocks) as WFBLAH by admit.
  assert (free_in_cfg loop_blocks nextblock) as FREEBLAH by admit.
  assert (~ (b ≡ bid_in \/ False)) as BBID_IN.
  { intros [CONTRA | []].
    admit.
  }
  assert (b0 ≡ b0 ∨ False) as B0B0 by auto.
  epose proof @genWhileLoop_init _ _ _ _ _ _ _ _ _ _ _ _ _ bid_from Heqs2 WFBLAH BBID_IN FREEBLAH B0B0 as INIT.
  cbn in INIT.
  destruct INIT as (body_bks' & GEN' & INIT).
  clear Heqs2.

  (* TODO: i5 and i21 are just an uneducated guess *)
  match goal with
  | H: genWhileLoop ?prefix ?x ?y ?loopvar ?loopcontblock ?body_entry ?body_blocks [] ?nextblock ?s1 ≡ inr (?s2, (?bid_in, ?bks)) |- _
    => epose proof @genWhileLoop_tfor_correct prefix loopvar loopcontblock body_entry body_blocks nextblock bid_in s1 s2 i5 i21 bks as LOOPTFOR
  end.

  assert (In b0
               (inputs
                  [{| blk_id := b0;
                      blk_phis := [];
                      blk_code :=
                        (IId r0,
                         (INSTR_Op (OP_GetElementPtr
                                      (TYPE_Array (Z.to_N (Int64.intval i1)) TYPE_Double)
                                      (TYPE_Pointer
                                         (TYPE_Array (Z.to_N (Int64.intval i1))
                                                     TYPE_Double), EXP_Ident i0)
                                      [(TYPE_I (Npos 64), EXP_Integer 0%Z); (TYPE_I (Npos 64), e)]))) ::
                                                                                                      (IId r2, INSTR_Load false TYPE_Double (TYPE_Pointer TYPE_Double, (EXP_Ident (ID_Local r0))) (Some 8%Z)) ::
                                                                                                      (IId r1, INSTR_Load false TYPE_Double (TYPE_Pointer TYPE_Double, (EXP_Ident (ID_Local r))) (Some 8%Z))
                                                                                                      :: c2 ++
                                                                                                      [(IVoid i16,
                                                                                                        INSTR_Store false (TYPE_Double, e2)
                                                                                                                    (TYPE_Pointer TYPE_Double, (EXP_Ident (ID_Local r))) (Some 8%Z)) : (instr_id * instr typ)];
                      blk_term := TERM_Br_1 b;
                      blk_comments := None
                   |}])) as Inb0 by auto.

  assert (is_correct_prefix "Power") as PREF_POWER by solve_prefix.

  assert (wf_ocfg_bid body_bks') as WF_BODY_BKS' by admit.

  (* TODO: make solve_lid_bound_between do this *)
  assert (lid_bound_between i5 i21
                 ("Power_i" @@ string_of_nat (local_count i5))) as LID_BOUND_BETWEEN_POWER_I by admit.

  assert (free_in_cfg body_bks' nextblock) as FREE_BODY_BKS'_NEXTBLOCK by admit.

  specialize (LOOPTFOR Inb0 PREF_POWER WF_BODY_BKS' LID_BOUND_BETWEEN_POWER_I).
  specialize (LOOPTFOR FREE_BODY_BKS'_NEXTBLOCK).

  (* Need to know how many times we loop, this is determined by the
  result of evaluating the expression e1 *)
  pose proof Heqs7 as LOOP_END.

  (* Clean up LLVM side a bit *)
  setoid_rewrite add_comment_eutt.

  (* Substitute blocks *)
  rewrite INIT.

  rename e into xoff_exp.
  rename e0 into yoff_exp.
  rename e1 into loop_end_exp.
  rename c into xoff_code.
  rename c0 into yoff_code.
  rename c1 into loop_end_code.

  rename n0 into xoff_nexpr.
  rename n1 into yoff_nexpr.
  rename n into loop_end_nexpr.

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


  assert (eutt Logic.eq
               (interp_cfg (denote_code (convert_typ [] (xoff_code ++ yoff_code ++ loop_end_code)%list)) g ρ memV)
               (interp_cfg (denote_code (convert_typ [] (loop_end_code ++ xoff_code ++ yoff_code)%list)) g ρ memV)) as COMMUTE_INIT.
  { admit.
  }

  repeat rewrite app_assoc.
  replace ((xoff_code ++ yoff_code) ++ loop_end_code)%list with (xoff_code ++ yoff_code ++ loop_end_code)%list by apply app_assoc.

  rewrite convert_typ_code_app.
  rewrite denote_code_app.

  (* TODO: this is a complete lie *)
  replace (xoff_code ++ yoff_code ++ loop_end_code)%list with (loop_end_code ++ xoff_code ++ yoff_code)%list by admit.

  repeat rewrite convert_typ_code_app.
  repeat setoid_rewrite denote_code_app.

  vstep.
  vred.

  (* loop_end *)
  eapply eutt_clo_bind_returns.
  { eapply genNExpr_correct; eauto.
    admit. (* solve_state_invariant. *)
    solve_gamma_safe.
  }

  intros [[m_loopend t_loopend] |] [mV_loopend [l_loopend [g_loopend []]]] PostLoopEnd RetLoopNExp RetLoopCode; [|inversion PostLoopEnd].
  destruct PostLoopEnd as [PostLoopEndSINV PostLoopEndNExpr]. cbn in PostLoopEndSINV.
  pose proof (Correctness_NExpr.is_almost_pure PostLoopEndNExpr) as [MHPURE [MVPURE GPURE]]; subst.
  vred; hred; vred.

  (* xoff *)
  eapply eutt_clo_bind_returns.
  { eapply genNExpr_correct.
    eauto.
    admit. (* solve_state_invariant. *)
    solve_gamma_safe. (* TODO: make solve_gamma_safe work here *)
    cbn.
    solve_local_count.

    (* TODO: Should look into automating this. In particular we need
    to fix the hint DB for eauto which can loop indefinitely. *)
    eapply no_failure_helix_bind_continuation in NOFAIL; [|eassumption].
    eauto.
  }

  intros [[m_xoff xoff_res] |] [mV_xoff [l_xoff [g_xoff []]]] PostXoff RetXoffNExp RetXoffCode; [|inversion PostXoff].
  destruct PostXoff as [PostXoffSINV PostXoffNExpr]. cbn in PostXoffSINV.
  pose proof (Correctness_NExpr.is_almost_pure PostXoffNExpr) as [MHPURE [MVPURE GPURE]]; subst.
  vred; hred; vred.

  Ltac solve_no_failure_helix :=
    first [ eassumption
          | eapply no_failure_helix_bind_prefix; solve_no_failure_helix
          ].

  (* yoff *)
  eapply eutt_clo_bind_returns.
  { eapply genNExpr_correct.
    eauto.
    admit. (* solve_state_invariant. *)
    solve_gamma_safe. (* TODO: make solve_gamma_safe work here *)
    cbn.
    solve_local_count.

    (* TODO: Should look into automating this. In particular we need
    to fix the hint DB for eauto which can loop indefinitely. *)
    eapply no_failure_helix_bind_continuation in NOFAIL; [|eassumption].
    eapply no_failure_helix_bind_continuation in NOFAIL; [|eassumption].
    eauto.
  }

  intros [[m_yoff yoff_res] |] [mV_yoff [l_yoff [g_yoff []]]] PostYoff RetYoffNExp RetYoffCode; [|inversion PostYoff].
  destruct PostYoff as [PostYoffSINV PostYoffNExpr]. cbn in PostYoffSINV.
  pose proof (Correctness_NExpr.is_almost_pure PostYoffNExpr) as [MHPURE [MVPURE GPURE]]; subst.

  hred.

  (* TODO: clean this up? *)
  pose proof NOFAIL as NOFAIL_Assert.
  eapply no_failure_helix_bind_continuation in NOFAIL_Assert; [|eassumption].
  eapply no_failure_helix_bind_continuation in NOFAIL_Assert; [|eassumption].
  eapply no_failure_helix_bind_continuation in NOFAIL_Assert; [|eassumption].
  pose proof NOFAIL_Assert as NOFAIL_MLUP_xoff.
  eapply no_failure_helix_bind_prefix in NOFAIL_Assert.

  (* TODO: I feel like I should be able to automate all of this no failure stuff. *)
  break_match_goal; break_match_hyp.
  { exfalso; eapply failure_helix_throw; eassumption. }
  { rewrite bind_ret_l in NOFAIL_MLUP_xoff; eapply no_failure_helix_bind_prefix in NOFAIL_MLUP_xoff;
    exfalso; eapply failure_helix_throw; eassumption. }
  { eapply no_failure_helix_bind_prefix in NOFAIL_MLUP_xoff;
    exfalso; eapply failure_helix_throw; eassumption. }

  hred.
  repeat rewrite bind_ret_l in NOFAIL_MLUP_xoff.
  rename NOFAIL_MLUP_xoff into NOFAIL_Power.

  unfold assert_NT_lt, assert_true_to_err in Heqs1.
  break_if; inv Heqs1. rename Heqb2 into LT_yoff.

  break_match_hyp; inv Heqs0.
  rename Heqo1 into MEMLUP_xoff.
  

  (* Need to figure out the corresponding pointer for id (i3).

     Need to get this from the memory_invariant *)


  (* TODO: move this *)
  Set Nested Proofs Allowed.
  Lemma typ_to_dtyp_P :
    forall t s,
      typ_to_dtyp s (TYPE_Pointer t) ≡ DTYPE_Pointer.
  Proof.
    intros t s.
    apply typ_to_dtyp_equation.
  Qed.

  Ltac typ_to_dtyp_simplify :=
    repeat
      (try rewrite typ_to_dtyp_I in *;
       try rewrite typ_to_dtyp_D in *;
       try rewrite typ_to_dtyp_D_array in *;
       try rewrite typ_to_dtyp_P in *).

  pose proof state_invariant_memory_invariant PRE as MINV_YOFF.
  pose proof state_invariant_memory_invariant PRE as MINV_XOFF.
  unfold memory_invariant in MINV_YOFF.
  unfold memory_invariant in MINV_XOFF.
  specialize (MINV_YOFF n3 _ _ _ Heqo0 LUn0).
  specialize (MINV_XOFF n2 _ _ _ Heqo LUn).
  cbn in MINV_YOFF, MINV_XOFF.

  destruct MINV_YOFF as (bkh_yoff & ptrll_yoff & τ_yoff & MLUP_yoff & TEQ_yoff & FITS_yoff & INLG_yoff & GETARRAYCELL_yoff).
  destruct MINV_XOFF as (bkh_xoff & ptrll_xoff & τ_xoff & MLUP_xoff & TEQ_xoff & FITS_xoff & INLG_xoff & GETARRAYCELL_xoff).
  rewrite MLUP_xoff in H; symmetry in H; inv H.
  rewrite MLUP_yoff in H0; symmetry in H0; inv H0.

  inv TEQ_yoff. inv TEQ_xoff. cbn. vred.
  destruct i0 as [id0 | id0].
  { (* Global case *)
    (* TODO: can I automate this? *)
    edestruct denote_instr_gep_array_no_read with (m:=mV_yoff) (g:=g_yoff) (ρ:=l_yoff) (size:=(Z.to_N (Int64.intval i1))) (τ:=DTYPE_Double) (i:=r0) (ptr := @EXP_Ident dtyp (ID_Global id0)) (a:= ptrll_xoff) (e_ix:=convert_typ [] xoff_exp) (ix:=(MInt64asNT.to_nat xoff_res)).
    { rewrite denote_exp_GR.
      change (UVALUE_Addr ptrll_xoff) with (dvalue_to_uvalue (DVALUE_Addr ptrll_xoff)).
      reflexivity.
      auto.
    }

    { (* TODO: wrap into automation? *)
      apply Correctness_NExpr.exp_correct in PostXoffNExpr.
      cbn in PostXoffNExpr.
      rewrite repr_of_nat_to_nat.
      eapply PostXoffNExpr.

      admit. (* solve_local_scope_preserved. *)
      admit. (* solve_gamma_preserved. *)
    }

    (* TODO: move all of this *)
    Lemma genNExpr_post_memoryV :
      forall e σ s1 s2 mh mv ρ g mh' t mv' ρ' g',
        genNExpr_post e σ s1 s2 mh (mk_config_cfg mv ρ g) (mh', t) (mv', (ρ', (g', ()))) ->
        mv ≡ mv'.
    Proof.
      intros e σ s1 s2 mh mv ρ g mh' t mv' ρ' g' H.
      destruct H.
      unfold almost_pure in is_almost_pure.
      cbn in is_almost_pure.
      apply is_almost_pure.
    Qed.

    Lemma genNExpr_memoryV :
      forall e σ s1 s2 s3 mh mv ρ g mh' t mv' ρ' g',
        (lift_Rel_cfg (state_invariant σ s3) ⩕ genNExpr_post e σ s1 s2 mh (mk_config_cfg mv ρ g)) (mh', t) (mv', (ρ', (g', ()))) ->
        mv ≡ mv'.
    Proof.
      intros e σ s1 s2 s3 mh mv ρ g mh' t mv' ρ' g' H.
      destruct H.
      eapply genNExpr_post_memoryV; eauto.
    Qed.

    Ltac get_mem_eqs :=
      cbn in *;
      repeat match goal with
             | H: (lift_Rel_cfg (state_invariant ?σ1 ?s3) ⩕ genNExpr_post ?e ?σ2 ?s1 ?s2 ?mh (mk_config_cfg ?mv ?ρ ?g)) (?mh', ?t) (?mv', (?ρ', (?g', ()))) |- _
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

    { typ_to_dtyp_simplify.
      erewrite <- from_N_intval; eauto.
    }

    rename x into src_addr.
    destruct H as [HSRC_GEP HSRC_GEP_EUTT].
    cbn.
    rewrite HSRC_GEP_EUTT.

    vred; hred; vred.

    destruct i3 as [id | id].
    { (* Global case for yoff *)
      (* TODO: can I automate this? *)
        edestruct denote_instr_gep_array_no_read with (m:=mV_yoff) (g:=g_yoff) (ρ:=(alist_add r1 (UVALUE_Double b1) (alist_add r0 (UVALUE_Addr src_addr) l_yoff))) (size:=(Z.to_N (Int64.intval i4))) (τ:=DTYPE_Double) (i:=r) (ptr := @EXP_Ident dtyp (ID_Global id)) (a:= ptrll_yoff) (e_ix:=fmap (typ_to_dtyp []) yoff_exp) (ix:=(MInt64asNT.to_nat yoff_res)).

    { rewrite denote_exp_GR.
      change (UVALUE_Addr ptrll_yoff) with (dvalue_to_uvalue (DVALUE_Addr ptrll_yoff)).
      reflexivity.
      auto.
    }

    { (* TODO: wrap into automation? *)
      apply Correctness_NExpr.exp_correct in PostYoffNExpr.
      cbn in PostYoffNExpr.
      rewrite repr_of_nat_to_nat.
      eapply PostYoffNExpr.

      admit. (* solve_local_scope_preserved. *)
      admit. (* solve_gamma_preserved. *)
    }

    { typ_to_dtyp_simplify.
      erewrite <- from_N_intval; eauto.
    }

    rename x into dst_addr.
    destruct H as [HDST_GEP HDST_GEP_EUTT].
    cbn.

    (* Load src *)
    unfold DSHPower_tfor.
    unfold DSHPower_tfor_body.
    rewrite denote_instr_load.
    2: {
      apply denote_exp_LR.

      cbn.
      apply alist_find_add_eq.
    }
    2: { pose proof GETARRAYCELL_xoff as GET.
         specialize (GET  _ _ MEMLUP_xoff).

         erewrite read_array; eauto.

         eapply dtyp_fits_allocated; eauto.
    }

    vred.
    rewrite denote_code_cons.
    vred.

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
      epose proof (vellvm_helix_ptr_size _ LUn0 Heqo0 PRE); subst.

      Lemma Int64_intval_pos :
        forall i,
          (0 <= Int64.intval i)%Z.
      Proof.
        intros i.
        pose proof Int64.intrange i; lia.
      Qed.

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
    cbn in *.
    rewrite STORE_INIT.

    vred.

    cbn in PostLoopEndNExpr.
    pose proof Correctness_NExpr.exp_correct PostLoopEndNExpr as PostLoopEndNExprCorrect.
    cbn in PostLoopEndNExprCorrect.

    epose proof (denote_exp_i64 _ t_loopend) as T_LOOPEND_EUTT.
    assert (eutt Logic.eq (interp_cfg (translate exp_E_to_instr_E (denote_exp (Some (DTYPE_I (Npos 64))) (EXP_Integer (Integers.Int64.intval t_loopend)))) g_yoff ρ mV_yoff)
                   (interp_cfg
                      (translate exp_E_to_instr_E
                                 (denote_exp (Some (DTYPE_I (Npos 64)))
                                             (convert_typ [] loop_end_exp))) g_yoff ρ mV_yoff)) as EUTT_INT.
    rewrite T_LOOPEND_EUTT.
    rewrite PostLoopEndNExprCorrect.
    reflexivity.

    admit. (* solve_local_scope_preserved. *)
    admit. (* solve_gamma_preserved. *)

    specialize (LOOPTFOR (MInt64asNT.to_nat t_loopend)).
    forward LOOPTFOR.
    { cbn.
      unfold MInt64asNT.to_nat.
      rewrite Znat.Z2Nat.id; [|apply Int64_intval_pos].

      (* ** WARNING ** *)
      (* TODO: this isn't actually true because e1 is different than
         EXP_Integer n, but this should be eutt *)
      admit.
    }.

    (* TODO: may be able to separate this out into the DSHPower_body_eutt lemma *)
    unfold DSHPower_tfor.
    rewrite interp_helix_tfor; [|lia].

    match goal with
      |- eutt _ (ITree.bind' _ (tfor ?bod _ _ _)) _ => specialize (LOOPTFOR _ bod)
    end.

    forward LOOPTFOR.
    { (* TODO: automate this kind of thing / separate into lemma? *)
      unfold MInt64asNT.to_nat.
      rewrite intval_to_from_nat_id.
      pose proof (Integers.Int64.intrange t_loopend).
      lia.
    }

    (* Will need to set up loop invariants and such, just like loop case *)

    (* TODO: these are just stolen and probably lies *)
    (* TODO: this happens way too soon. I need to finish GEPs *)
    (* Invariant at each iteration *)
    set (I := (fun (k : nat) (mH : option (memoryH * mem_block)) (stV : memoryV * (local_env * global_env)) =>
                 match mH with
                 | None => False
                 | Some (mH,mb) =>
                   match stV with
                   | (mV, (ρ, g)) =>
                     state_invariant σ s2 mH stV /\
                     local_scope_modif i21 s2 (alist_add r (UVALUE_Addr dst_addr) (alist_add r0 (UVALUE_Addr src_addr) l_yoff)) ρ /\
                     ext_memory mV_init dst_addr DTYPE_Double (UVALUE_Double initial) mV (* TODO: obviously initial is wrong here *)
                   end
                 end)).

    (* Precondition and postcondition *)
    set (P := (fun (mH : option (memoryH * mem_block)) (stV : memoryV * (local_env * global_env)) =>
                 match mH with
                 | None => False
                 | Some (mH,mb) => state_invariant σ s2 mH stV
                 end)).

      specialize (LOOPTFOR I P P (Some (m_yoff, mem_add (MInt64asNT.to_nat yoff_res) initial bkh_yoff))).

      forward LOOPTFOR.
      { intros g_loop l_loop mV_loop [[mH_loop mb_loop] |] k _label [HI [POWERI [POWERI_VAL RETURNS]]]; [|inv HI].
        cbn in HI.
        destruct HI as [LINV_SINV [LINV_LSM [LINV_MEXT_NEW LINV_MEXT_OLD]]].
        unfold DSHPower_tfor_body.

        unfold mem_lookup_err.
        unfold trywith.
        break_match_goal; [|admit]. (* Failure should be caught by NOFAIL *)

        cbn.
        hred; vred.
        unfold denoteBinCType.

        rewrite denote_ocfg_unfold_in.
        2: {
          apply find_block_eq; auto.
        }

        cbn; vred.

        rewrite denote_no_phis.
        vred; cbn.

        rewrite denote_code_cons.
        vred.

        (* Load dst *)
        rewrite denote_instr_load.
        2: {
          apply denote_exp_LR.

          (* TODO: probably need something in the loop invariant? *)
          cbn.
          erewrite <- local_scope_modif_external.
          2: { eapply local_scope_modif_trans'. eapply LINV_LSM. admit. (* Should be fine... *) }
          2: { intros CONTRA. admit. (* Seems fine... *) }

          apply alist_find_add_eq.
        }
        2: {
          pose proof GETARRAYCELL_yoff.

          (* H is not sufficient! It's in terms of mV_yoff, not
             mV_loop. Need to extend invariant. *)

          (* ALSO mb_loop instead of bkh_yoff here *)

          (* I *think* src and dst can actually alias, which will make
          the invariant more difficult *)
          admit.
        }

        vred.
        rewrite map_app.
        cbn.
        typ_to_dtyp_simplify.
        rewrite denote_code_app.
        rewrite bind_bind.
        vred.

        eapply eutt_clo_bind.
        {
          eapply genAExpr_correct.
          eauto.
          { split; cbn.
            - (* Memory invariant *)
              admit.
            - cbn.
              (* TODO: WF_IRState cons lemma *)

              unfold WF_IRState.
              cbn.
              Lemma evalContext_typechecks_cons :
                forall σ Γ v id τ,
                  evalContext_typechecks σ Γ ->
                  getWFType id (DSHType_of_DSHVal v) ≡ τ ->
                  evalContext_typechecks (v :: σ) ((id, τ) :: Γ).
              Proof.
                intros σ Γ v id τ TC TYP.
                unfold evalContext_typechecks.
                intros v0 [|n] LUP.
                - cbn in LUP. inv LUP.
                  exists id. reflexivity.
                - rewrite nth_error_Sn in LUP.
                  rewrite nth_error_Sn.
                  apply TC in LUP.
                  auto.
              Qed.


              (* TODO: should be able to automate this *)
              do 2 (eapply evalContext_typechecks_cons; eauto).
              admit.
            - admit.
            - admit.
            - admit.
            - admit.
          }
          admit. (* solve_gamma_safe. *)
          admit. (* solve_no_failure. *)
        }

        intros [[mH_Aexpr t_Aexpr]|] [mV_Aexpr [l_Aexpr [g_Aexpr []]]] POST; [|inv POST].
        destruct POST as [POSTAEXPRSINV POSTAEXPR].

        hred.
        vred.

        erewrite denote_instr_store; eauto.

        2: {
          destruct POSTAEXPR.
          cbn in exp_correct.
          cbn in POSTAEXPRSINV.
          eapply exp_correct.
          solve_local_scope_preserved.
          solve_gamma_preserved.
        }
        3: {
          cbn. reflexivity.
        }
        2: {
          eapply denote_exp_LR.
          destruct POSTAEXPR.
          (* Should follow from extends. Need to solve some evars... *)
          (*
  extends : local_scope_modif
              {|
              block_count := block_count i19;
              local_count := local_count i19;
              void_count := void_count i19;
              Γ := (%r2, TYPE_Double) :: (%r1, TYPE_Double) :: Γ i19 |} i20
              ((li [r2 : ?Goal28@{r:=important}]) [r1 : ?Goal27@{r:=important}]) l_Aexpr
           *)
          admit. (* solve_local_lookup. *)
        }
        2: {
          (* TODO: this is the result of the AExpr being written to memory *)
          destruct POSTAEXPR.
          cbn in exp_correct.
          cbn in is_almost_pure.
          cbn in POSTAEXPRSINV.
          destruct POSTAEXPRSINV.
          cbn in mem_is_inv.
          assert (mV_Aexpr ≡ mV_loop) by admit; subst.
          admit. (* Write *)
        }

        vred.
        rewrite denote_term_br_1.
        vred.

        cbn.
        rename b into jump_label.
        rewrite denote_ocfg_unfold_not_in.
        vred.
        2: {
          cbn.
          (* Is bid_in b0? I think it might not be... *)
          (* Probably know b0 <> jump_label by states, though... *)
          assert (b0 ≢ jump_label) as NEQ by admit.
          rewrite find_block_ineq; eauto.
        }

        apply eqit_Ret.
        split; [|split; [|split]].
        - admit.
        - exists b0. reflexivity.
        - admit. (* I *)
        - admit.        
      }

      (* TODO: Might want to do more forward reasoning first *)
      (* I have some extra stuff after the loop, so I can't directly apply LOOPTFOR here.

         May be able to use bind_ret_r and then eutt_clo_bind... Or something.
       *)
      replace     (interp_cfg_to_L3 defined_intrinsics
       (denote_ocfg (convert_typ nil body_bks') (pair bid_from bid_in)) g_yoff
       (alist_add r (UVALUE_Addr dst_addr)
          (alist_add r1 (UVALUE_Double b1)
             (alist_add r0 (UVALUE_Addr src_addr) l_yoff)))
       mV_init) with     (interp_cfg_to_L3 defined_intrinsics
       (x <- denote_ocfg (convert_typ nil body_bks') (pair bid_from bid_in) ;; ret x) g_yoff

       (alist_add r (UVALUE_Addr dst_addr)
          (alist_add r1 (UVALUE_Double b1)
                     (alist_add r0 (UVALUE_Addr src_addr) l_yoff)))
       mV_init) by admit. (* Obviously this is wrong because replace uses eq instead of eutt, but should give us an idea of how this reasoning should go *)

      setoid_rewrite interp_cfg_to_L3_bind.
      eapply eutt_clo_bind.
      eapply LOOPTFOR.

      7: {
        intros [[mH_meh mb_meh]|] [mV_meh [l_meh [g_meh x_meh]]] [MEH [P_MEH LSM_MEH]]; [|inv P_MEH].
        rewrite interp_helix_MemSet.
        cbn.
        vred.

        apply eutt_Ret.
        unfold genIR_post.
        admit.
      }
      
      rewrite LOOPTFOR.
    rewrite denote_ocfg_unfold_in.
    2: {
      apply find_block_eq; auto.
    }

      destruct i0.
      { (* Global case for xoff *)
        (* TODO: can I automate this? *)
        rename x1 into ptrll_x.

        edestruct denote_instr_gep_array_no_read with (m:=x2) (g:=g_yoff) (ρ:=(alist_add r (UVALUE_Addr ptrll_x) l_yoff)) (size:=(Z.to_N (Int64.intval i1))) (τ:=DTYPE_Double) (i:=r0) (ptr := @EXP_Ident dtyp (ID_Global id0)) (a:= ptrll_x) (e_ix:=fmap (typ_to_dtyp []) xoff_exp) (ix:=(MInt64asNT.to_nat xoff_res)).
        2: {
          (* TODO: wrap into automation? *)
          destruct PostXoff.
          destruct g0.
          cbn in exp_correct.
          rewrite repr_of_nat_to_nat.
          pose proof exp_correct.
          Unset Printing Notations.

          (* g_yoff should = g_xoff *)
          (* mV_xoff = x2?? mV_yoff after a write to ptrll_x... and I think mV_yoff = mV_xoff *)
          (* I don't think NEXprs read from memory anyway... *)
          apply exp_correct.
          solve_local_scope_preserved.
          solve_gamma_preserved.
        }
        2: {
          (* dtyp_fits *)
          admit.
        }

        { change (UVALUE_Addr ptrll_x) with (dvalue_to_uvalue (DVALUE_Addr ptrll_x)).
          rewrite denote_exp_GR; eauto.

          reflexivity.

          cbn in INLG_xoff.
          cbn.
          (* I think g = g_xoff *)
          admit.
        }

        destruct H6.
        cbn.
        vred.
        rewrite H7.
        
        vred. cbn.
        rewrite denote_code_cons.
        vred.

        rewrite denote_instr_load.
        2: {
          apply denote_exp_LR.

          (* TODO: probably need something in the loop invariant? *)
          match goal with
          | |- Maps.lookup ?r ?l ≡ Some (UVALUE_Addr ?x)
            => assert (Maps.lookup r l  ≡ Some (UVALUE_Addr x1)) by admit
          end.

          eapply H7.
        }
          2: {
            admit.
          }

          vred.
          rewrite map_app.
          cbn.
          typ_to_dtyp_simplify.
          rewrite denote_code_app.
          rewrite bind_bind.
          vred.

          eapply eutt_clo_bind.
          {
            eapply genAExpr_correct.
            eauto.
            admit. (* solve_state_invariant. *)
            admit. (* solve_gamma_safe. *)
            admit. (* solve_no_failure. *)
          }

          intros [[mH_Aexpr t_Aexpr]|] [mV_Aexpr [l_Aexpr [g_Aexpr []]]] POST; [|inv POST].
          destruct POST as [POSTAEXPRSINV POSTAEXPR].

          hred.
          vred.

          erewrite denote_instr_store; eauto.
          2: {
            destruct POSTAEXPR.
            cbn in exp_correct.
            eapply exp_correct.
            solve_local_scope_preserved.
            solve_gamma_preserved.
          }
          3: {
            cbn. reflexivity.
          }
          2: {
            eapply denote_exp_LR.
            destruct POSTAEXPR.
            (* Should follow from extends. Need to solve some evars... *)
            (*
  extends : local_scope_modif
              {|
              block_count := block_count i19;
              local_count := local_count i19;
              void_count := void_count i19;
              Γ := (%r2, TYPE_Double) :: (%r1, TYPE_Double) :: Γ i19 |} i20
              ((li [r2 : ?Goal28@{r:=important}]) [r1 : ?Goal27@{r:=important}]) l_Aexpr
             *)
            admit. (* solve_local_lookup. *)
          }
          2: {
            admit. (* Write *)
          }

          vred.
          rewrite denote_term_br_1.
          vred.

          cbn.
          rename b into jump_label.
          rewrite denote_ocfg_unfold_not_in.
          vred.
          2: {
            cbn.
            (* Is bid_in b0? I think it might not be... *)
            (* Probably know b0 <> jump_label by states, though... *)
            assert (b0 ≢ jump_label) as NEQ by admit.
            rewrite find_block_ineq; eauto.
          }

          apply eqit_Ret.
          split; [|split; [|split]].
          - admit.
          - exists b0. reflexivity.
          - admit. (* I *)
          - admit.
        }

        { rewrite denote_exp_GR.
          change (UVALUE_Addr ptrll) with (dvalue_to_uvalue (DVALUE_Addr ptrll)).
          reflexivity.

          cbn in INLG.
          (* I think g = g''' *)
          admit.
        }

        { (* Should hold, pretty much the same as earlier case *)
          admit.
        }
      }

      { (* Should be pretty much the same as above... Local case. *)
        admit.
      }

      
Admitted.
