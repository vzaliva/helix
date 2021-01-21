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
        repeat setoid_rewrite bind_bind.
        eapply eutt_clo_bind; [reflexivity|].
        intros u1 u2 H.
        eapply eutt_clo_bind; [reflexivity|].
        intros u0 u3 H0.
        subst.
        eapply eutt_clo_bind; [reflexivity|].
        intros u1 u0 H.
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
      (x y: mem_block)
      (xoffset yoffset: nat) m E,
      interp_helix (E:=E) (denoteDSHPower σ n f x y xoffset yoffset) m
                     ≈
                     DSHPower_interpreted_tfor σ n f x y xoffset yoffset m.
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
      '(y_i,y_sixe) <- denotePExpr σ y_p ;;
      x <- trigger (MemLU "Error looking up 'x' in DSHPower" x_i) ;;
      y <- trigger (MemLU "Error looking up 'y' in DSHPower" y_i) ;;
      n <- denoteNExpr σ ne ;; (* [n] denoteuated once at the beginning *)
      xoff <- denoteNExpr σ xoffset ;;
      yoff <- denoteNExpr σ yoffset ;;
      let y' := mem_add (MInt64asNT.to_nat yoff) initial y in
      y'' <-  DSHPower_tfor σ (MInt64asNT.to_nat n) f x y' (MInt64asNT.to_nat xoff) (MInt64asNT.to_nat yoff) ;;
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
       '(y_i,y_sixe) <- denotePExpr σ y_p ;;
       x <- trigger (MemLU "Error looking up 'x' in DSHPower" x_i) ;;
       y <- trigger (MemLU "Error looking up 'y' in DSHPower" y_i) ;;
       n <- denoteNExpr σ ne ;; (* [n] denoteuated once at the beginning *)
       xoff <- denoteNExpr σ xoffset ;;
       yoff <- denoteNExpr σ yoffset ;;
       let y' := mem_add (MInt64asNT.to_nat yoff) initial y in
       y'' <-  DSHPower_tfor σ (MInt64asNT.to_nat n) f x y' (MInt64asNT.to_nat xoff) (MInt64asNT.to_nat yoff) ;;
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
    forall σ f x y xoffset yoffset acc px py xv yv xtyp xptyp x_c src_nexpr fexpr fexpcode storeid loopcontblock g li mV mH _label body_entry,
          eutt
            (fun x y => True)
            (interp_helix (DSHPower_tfor_body σ f x y xoffset yoffset acc) mH)
            (interp_cfg (denote_ocfg (convert_typ [] [(DSHPower_block body_entry loopcontblock px py xv yv xtyp xptyp x_c src_nexpr fexpr fexpcode storeid)]) (_label, body_entry)) g li mV).
  Proof.
    intros σ f x y xoffset yoffset acc px py xv yv xtyp xptyp x_c src_nexpr fexpr fexpcode storeid loopcontblock
           g li mV mH _label body_entry.
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
  Abort.


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

  pose proof genWhileLoop_tfor_correct.

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
                                                                                                      [(IVoid i14,
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

  eapply eutt_clo_bind.
  { eapply genNExpr_correct; eauto.
    admit.
    admit.
  }

  intros [[m t] |] [mV' [l' [g' []]]] H2; [|inversion H2].

  vred; hred.
  vred.

  eapply eutt_clo_bind.
  { eapply genNExpr_correct.
    apply Heqs3.
    admit.
    admit.
    admit.
  }

  intros [[m' t'] |] [mV'' [l'' [g'' []]]] H3; [|inversion H3].

  vred; hred; vred.

  eapply eutt_clo_bind.
  { eapply genNExpr_correct.
    apply Heqs4.
    admit.
    admit.
    admit.
  }

  intros [[m'' t''] |] [mV''' [l''' [g''' []]]] H4; [|inversion H4].

  vred; hred; vred.

  cbn.
  vred.

  (* Need to figure out the corresponding pointer for id (i3).

     Need to get this from the memory_invariant *)

  pose proof state_invariant_memory_invariant PRE as MINV.
  unfold memory_invariant in MINV.
  specialize (MINV n3 _ _ _ Heqo0 LUn0).
  cbn in MINV.
  destruct MINV as (bkh & ptrll & τ' & MLUP & TEQ & FITS & INLG & GETARRAYCELL).
  inv TEQ.
  destruct i3.
  { (* Global case *)
    edestruct denote_instr_gep_array_no_read with (m:=mV''') (g:=g''') (ρ:=l''') (size:=(Z.to_N (Int64.intval i4))) (τ:=DTYPE_Double) (i:=r) (ptr := @EXP_Ident dtyp (ID_Global id)) (a:= ptrll).
    4: {
      destruct H5.
      cbn.
      rewrite H6.

      rewrite bind_ret_l.
      vred.

      edestruct denote_instr_store_exists with (a := x1) (m:=mV''').

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

      { eapply dtyp_fits_array_elem; eauto. admit. admit.
      }

      (* 2: { destruct H7. *)
      (*      cbn in *. *)
      (*      rewrite H8. *)
      (*      admit. *)
      (*    } *)
      {
      (* Will need to set up loop invariants and such, just like loop case *)
      admit.
      }
    }

    { rewrite denote_exp_GR.
      change (UVALUE_Addr ptrll) with (dvalue_to_uvalue (DVALUE_Addr ptrll)).
      reflexivity.

      cbn in INLG.
      (* I think g = g''' *)
      admit.
    }

    { admit.

    }

    { (* Should hold in new memory too *)
      rewrite typ_to_dtyp_D_array in FITS.
      (* EQsz0 : MInt64asNT.from_N sz0 ≡ inr i4 *)
      admit.
    }
  }

  { (* Should be pretty much the same as above... Local case. *)

  
Admitted.
