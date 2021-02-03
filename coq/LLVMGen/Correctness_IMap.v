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

  Lemma eqit_Proper_mono {E}:
    forall A B : Type, Proper (@subrelationH A B ==> subrelationH (B:=itree E B)) eutt.
  Proof.
  - intros A B. do 3 red.
    intros x y. pcofix CIH. pstep. red.
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

  Lemma eq_rev :
    forall σ f n x y
      (swap_body :
        forall (n : nat) (σ : evalContext) (f : AExpr) (x : mem_block) (n0 : nat) (u2 : mem_block),
          eutt eq (ITree.bind' (fun x0 : mem_block => DSHIMap_body σ f n0 x x0) (DSHIMap_body σ f n x u2))
                (ITree.bind' (fun x0 : mem_block => DSHIMap_body σ f n x x0) (DSHIMap_body σ f n0 x u2))),
      DSHIMap_tfor_up σ f 0 n x y ≈ DSHIMap_tfor_down σ f 0 n n x y.
  Proof.
    unfold DSHIMap_tfor_up, DSHIMap_tfor_down.
    intros. revert σ f x y.
    Opaque DSHIMap_body.
    induction n. intros. cbn.
    - rewrite! tfor_0. reflexivity.
    - intros. setoid_rewrite tfor_unroll at 2.
      cbn. 2 : lia.
      assert (EQ : n - 0 - 0 ≡ n) by lia; rewrite EQ; clear EQ.
      assert (EQ : n - 0 ≡ n) by lia; rewrite EQ; clear EQ.
      etransitivity; cycle 1.
      eapply eutt_clo_bind. reflexivity.
      intros * ->.
      setoid_rewrite tfor_ss_dep at 2. reflexivity. intros. 2 : lia.
      Unshelve. 3 : exact (fun i x0 => DSHIMap_body σ f (n - 1 - i) x x0). cbn.
      assert (EQ : n - S i ≡ n - 1 - i) by lia; rewrite EQ; clear EQ.
      reflexivity.
      setoid_rewrite <- IHn.

      setoid_rewrite tfor_split with (j := n) at 1. 2, 3 : lia.
      clear IHn.
      etransitivity. eapply eutt_clo_bind. reflexivity. intros * ->.
      setoid_rewrite tfor_unroll at 1. setoid_rewrite tfor_0 at 1. setoid_rewrite bind_ret_r at 1.
      reflexivity. lia.
      remember n.
      remember (λ x0 : mem_block, DSHIMap_body σ f n0 x x0).
      rewrite Heqn0. clear Heqn0. subst.
      revert x y n0.
      induction n.
      + intros. setoid_rewrite tfor_0. rewrite bind_ret_r. rewrite bind_ret_l. reflexivity.
      + intros. setoid_rewrite tfor_split with (j := n) at 1. 2, 3 : lia.
        etransitivity. eapply eutt_clo_bind. eapply eutt_clo_bind.
        reflexivity. intros * ->.
        setoid_rewrite tfor_unroll at 1. setoid_rewrite tfor_0 at 1. setoid_rewrite bind_ret_r at 1.
        reflexivity. lia. intros * ->. reflexivity.
        etransitivity; cycle 1.
        eapply eutt_clo_bind.
        reflexivity. intros * ->.
        setoid_rewrite tfor_split with (j := n) at 2.
        eapply eutt_clo_bind. reflexivity. intros * ->.
        setoid_rewrite tfor_unroll at 2. setoid_rewrite tfor_0 at 2. setoid_rewrite bind_ret_r at 2.
        reflexivity. lia. lia. lia. cbn.
        rewrite <- bind_bind.
        rewrite <- IHn.
        rewrite !bind_bind.
        eapply eutt_clo_bind. reflexivity.
        intros * ->.
        clear IHn.
        apply swap_body.
  Qed.

  Lemma swap_body_interp:
    forall E (n : nat) (σ : evalContext) (f : AExpr) (x : mem_block) (n0 : nat) m1 m2 ,
    eutt (E := E) eq (interp_helix (ITree.bind' (DSHIMap_body σ f n0 x) (DSHIMap_body σ f n x m2)) m1)
         (interp_helix (ITree.bind' (DSHIMap_body σ f n x) (DSHIMap_body σ f n0 x m2)) m1).
  Proof.
  Admitted.

  Lemma eq_rev_interp :
    forall σ f n x y memH E,
      interp_helix (E := E) (DSHIMap_tfor_up σ f 0 n x y) memH ≈
      interp_helix (E := E) (DSHIMap_tfor_down σ f 0 n n x y) memH.
  Proof.
    unfold DSHIMap_tfor_up, DSHIMap_tfor_down.
    intros. revert σ f x y memH.
    Opaque DSHIMap_body.
    induction n. intros. cbn.
    - rewrite! tfor_0. reflexivity.
    - intros. setoid_rewrite tfor_unroll at 2.
      cbn. 2 : lia.
      assert (EQ : n - 0 - 0 ≡ n) by lia; rewrite EQ; clear EQ.
      assert (EQ : n - 0 ≡ n) by lia; rewrite EQ; clear EQ.
      etransitivity; cycle 1.
      rewrite interp_helix_bind.
      eapply eutt_clo_bind. reflexivity.
      intros [[]|] [[]|] EQ; inv EQ.
      {
        setoid_rewrite tfor_ss_dep at 2. 3 : lia.
        2 : {
          intros. Unshelve.
          3 : { exact (fun i x0 => DSHIMap_body σ f (n - 1 - i) x x0). }
          cbn.
          assert (EQ : n - S i ≡ n - 1 - i) by lia; rewrite EQ; clear EQ.
          reflexivity.
          shelve.
        }
        rewrite <- IHn.
        Unshelve.
        2 : exact (fun a =>
            match a with
            | Some (m1, m2) =>
              interp_helix (tfor (λ (i : nat) (acc : mem_block), DSHIMap_body σ f i x acc) 0 n m2) m1
            | None => Ret None
            end).
        cbn. reflexivity.
      }
      { cbn. reflexivity. }
      cbn.

      setoid_rewrite tfor_split with (j := n) at 1. 2, 3 : lia.
      clear IHn.
      etransitivity.
      {
        rewrite interp_helix_bind. eapply eutt_clo_bind. reflexivity.
        intros [[]|] [[]|] EQ; inv EQ.
        setoid_rewrite tfor_unroll at 1. setoid_rewrite tfor_0 at 1. setoid_rewrite bind_ret_r at 1.
        2 : lia. Unshelve.
        3 : exact (fun a =>
            match a with
            | Some (m1, m2) => interp_helix (DSHIMap_body σ f n x m2) m1
            | None => Ret None
            end).
        cbn. reflexivity.
        cbn. reflexivity.
      }
      cbn.

      remember n.
      remember (λ x0 : mem_block, DSHIMap_body σ f n0 x x0).
      rewrite Heqn0. clear Heqn0. subst.
      revert x y n0.
      induction n.
      + intros.
        setoid_rewrite tfor_0.
        rewrite interp_helix_ret. cbn. rewrite bind_ret_l.
        etransitivity; cycle 1.
        eapply eutt_clo_bind.
        reflexivity.
        {
          intros [[]|] [[]|] EQ; inv EQ.
          Unshelve.
          setoid_rewrite tfor_0 at 2. rewrite interp_helix_ret. cbn.
          3 : exact (fun a => Ret a).
          cbn. reflexivity. cbn. reflexivity.
        }
        cbn. rewrite bind_ret_r. reflexivity.
      + intros.
        (* 1 *)
        setoid_rewrite tfor_split with (j := n) at 1. 2, 3 : lia.
        etransitivity.
        {
          rewrite interp_helix_bind.
          eapply eutt_clo_bind. eapply eutt_clo_bind.
          reflexivity.
          intros [[]|] [[]|] EQ; inv EQ.
          setoid_rewrite tfor_unroll at 1. setoid_rewrite tfor_0 at 1.
          setoid_rewrite bind_ret_r at 1.
          2 : lia.
          Unshelve.
          7 : exact (fun a =>
              match a with
              | Some (m1, m2) => interp_helix (DSHIMap_body σ f n x m2) m1
              | None => Ret None
              end).
          cbn. reflexivity. cbn. reflexivity.
          intros [[]|] [[]|] EQ; inv EQ.
          3 : exact (fun a =>
              match a with
              | Some (m1, m2) => interp_helix (DSHIMap_body σ f n0 x m2) m1
              | None => Ret None
              end).
          1, 2 : cbn ; reflexivity.
        }

        etransitivity; cycle 1.
        {
          eapply eutt_clo_bind.
          reflexivity.
          intros [[]|] [[]|] EQ; inv EQ.
          setoid_rewrite tfor_split with (j := n) at 2.
          rewrite interp_helix_bind. 2, 3 : lia.
          Unshelve.
          3 : exact (fun a =>
              match a with
              | Some (m1, m2) =>
                  '(m3, m4) <- interp_helix (tfor (λ (i : nat) (acc : mem_block), DSHIMap_body σ f i x acc) 0 n m2 ) m1 ;;
                    interp_helix (DSHIMap_body σ f n x m4) m3
              | None => Ret None
              end).
          cbn.
          eapply eutt_clo_bind. reflexivity.

          intros [[]|] [[]|] EQ; inv EQ.
          setoid_rewrite tfor_unroll. setoid_rewrite tfor_0. setoid_rewrite bind_ret_r.
          reflexivity. lia. reflexivity.
          cbn. reflexivity.
        }
        cbn.
        etransitivity; cycle 1.
        eapply eutt_clo_bind. reflexivity.
        {
          intros [[]|] [[]|] EQ; inv EQ.
          rewrite <- interp_helix_bind.

          Unshelve.
          3 : {
            exact
              (fun a =>
                match a with
                | Some (m1, m2) =>
                  (interp_helix (ITree.bind' (DSHIMap_body σ f n x)
                          (tfor (fun (i : nat) (acc : mem_block) => DSHIMap_body σ f i x acc) O n m2)) m1)
                | None => Ret None
                end).
          }
          reflexivity.
          cbn. reflexivity.
        }

        rewrite <- interp_helix_bind.
        rewrite <- interp_helix_bind.
        rewrite <- interp_helix_bind.
        setoid_rewrite <- bind_bind.
        setoid_rewrite interp_helix_bind at 2.
        setoid_rewrite interp_helix_bind at 2.
        rewrite <- IHn.
        rewrite !bind_bind.
        clear IHn.
        setoid_rewrite interp_helix_bind.
        eapply eutt_clo_bind. reflexivity.

        intros [[]|] [[]|] EQ; inv EQ.
        rewrite <- interp_helix_bind.
        2 : { rewrite bind_ret_l. reflexivity. }
        eapply swap_body_interp.
  Qed.

  Transparent DSHIMap_body.

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
    rewrite <- eq_rev_interp.
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
  destruct (assert_nat_le "DSHIMap 'n' index out of bounds" n (MInt64asNT.to_nat i0)) eqn : BOUNDS; try_abs.
  repeat apply no_failure_Ret in NOFAIL.

  edestruct @no_failure_helix_LU as (? & NOFAIL' & ?); eauto; []; clear NOFAIL; rename NOFAIL' into NOFAIL; cbn in NOFAIL; eauto.
  edestruct @no_failure_helix_LU as (? & NOFAIL' & ?); eauto; []; clear NOFAIL; rename NOFAIL' into NOFAIL; cbn in NOFAIL; eauto.


  clean_goal.

  hred.

  repeat apply no_failure_Ret in NOFAIL.
  rewrite XNEQY.

  hred.
  rewrite BOUNDS.
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

  assert (OVERFLOW: (Z.of_nat n < Integers.Int64.modulus)%Z). {
    clear -Heqs5.
    unfold MInt64asNT.from_nat in Heqs5.
    unfold MInt64asNT.from_Z in Heqs5.
    simp.
    apply l0.
  }

  forward GENC; [clear GENC |]; eauto.

  inv VG.
  rewrite add_comment_eutt.

  rename memV into mV_init.
  rename sz0 into y_sz.
  rename sz into x_sz.

  destruct u. unfold assert_nat_neq in XNEQY.
  unfold assert_false_to_err in XNEQY. break_match_hyp; try inv XNEQY.
  apply beq_nat_false in Heqb1.
  unfold assert_nat_le, assert_true_to_err in BOUNDS.
  break_match_hyp; inv BOUNDS.
  rename Heqb1 into XNEQY.
  rename Heqb0 into BOUNDS.
  apply Nat.leb_le in BOUNDS.

  Definition memory_invariant_partial_write' (configV : config_cfg) (index loopsize : nat) (ptr_llvm : addr)
             (bk_helix : mem_block) (x : ident) sz : Prop :=
      let '(mem_llvm, (ρ, g)) := configV in
      dtyp_fits mem_llvm ptr_llvm (typ_to_dtyp [] (TYPE_Array sz TYPE_Double)) /\
      in_local_or_global_addr ρ g x ptr_llvm /\
              (∀ (i : Int64.int) (v0 : binary64),
                  (MInt64asNT.to_nat i) < index \/ (MInt64asNT.to_nat i) >= loopsize ->
                    (mem_lookup (MInt64asNT.to_nat i) bk_helix ≡ Some v0
                     → get_array_cell mem_llvm ptr_llvm (MInt64asNT.to_nat i) DTYPE_Double ≡ inr (UVALUE_Double v0))).

              (*     (((MInt64asNT.to_nat i) >= BinNat.N.to_nat sz) /\ *)
              (*       (mem_lookup (MInt64asNT.to_nat i) bk_helix ≡ Some v0 *)
              (*       → get_array_cell mem_llvm ptr_llvm (MInt64asNT.to_nat i) DTYPE_Double ≡ inr (UVALUE_Double v0))) *)
              (* ). *)

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
                 memory_invariant_partial_write' stV k n ptrll_yoff b y y_sz /\
                 mH ≡ memH /\ g ≡ g' /\
                 allocated ptrll_yoff mV
                  (* forall i, i <= k -> *)
                  (* exists dst_addr, handle_gep_addr (DTYPE_Array y_sz DTYPE_Double) ptrll_yoff *)
                  (*   [DVALUE_I64 (DynamicValues.Int64.repr 0); DVALUE_I64 (DynamicValues.Int64.repr (Z.of_nat i))] ≡ inr dst_addr /\ *)
                    (* exists v, mem_lookup i b ≡ Some v /\ *)
                    (*     ext_memory mV_init dst_addr DTYPE_Double (UVALUE_Double v) mV *)
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
               | Some (mH,mb) => state_invariant σ s12 (memory_set mH y_h_ptr mb) stV /\
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

    - unfold memory_invariant_partial_write in *.

      destruct H1 as (? & ? & ?).
      intuition.
      + unfold alist_add; cbn. cbn.
        destruct y; auto. cbn in *.
         break_match_goal.
        * rewrite rel_dec_correct in Heqb1; subst.
          assert (Gamma_safe σ s0 s12). solve_gamma_safe.

          Transparent addVars.
          inv Heqs12.
          cbn in Heqs13.

          assert (NIN: not (in_Gamma σ s0 id)). apply H.
          eapply lid_bound_between_shrink. eauto.
          Transparent newLocalVar.
          cbn in *.
          inv Heqs4.
          solve_local_count. solve_local_count.
          exfalso; eapply NIN.
          econstructor. apply Heqo0. eauto.
          eauto.
        * apply neg_rel_dec_correct in Heqb1.
          rewrite remove_neq_alist; eauto.
          all: typeclasses eauto.

      + unfold alist_add; cbn. cbn.
        destruct y; auto. cbn in *.
          break_match_goal.
        * rewrite rel_dec_correct in Heqb1; subst.
          assert (Gamma_safe σ s0 s12). solve_gamma_safe.

          Transparent addVars.
          inv Heqs12.
          cbn in Heqs13.

          assert (NIN: not (in_Gamma σ s0 id)). apply H.
          eapply lid_bound_between_shrink. eauto. solve_local_count. solve_local_count.
          exfalso; eapply NIN.
          econstructor. apply Heqo0. eauto.
          eauto.
        * apply neg_rel_dec_correct in Heqb1.
          rewrite remove_neq_alist; eauto.
          all: typeclasses eauto.
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

    assert (Y_SIZE : y_sz ≡ Z.to_N (Int64.intval i0)). {
      epose proof (vellvm_helix_ptr_size _ LUn0 Heqo0).
      eapply state_invariant_cons2 in PRE_INV'. 3 : eauto. 2 : solve_local_count.
      specialize (H1 PRE_INV'). eauto.
    }

    (* 2. Store  *)
    edestruct write_succeeds with (m1 := mV) (v := DVALUE_Double t_Aexpr) (a := dst_addr).
    apply DVALUE_Double_typ.
    {
      typ_to_dtyp_simplify.

      pose proof (from_N_intval _ EQsz0) as EQ.
      rewrite Y_SIZE in EQ.
      eapply dtyp_fits_array_elem.
      subst y_size. 2 : eauto.
      rewrite <- EQ. rewrite <- Y_SIZE. eauto.
      subst y_size. rewrite <- EQ.

      eapply to_nat_repr_nat in EQk.


      rewrite Znat.Z2N.id; [|apply Int64_intval_pos].

      pose proof Znat.inj_le _ _ BOUNDS as LE.
      unfold MInt64asNT.to_nat in LE.

      rewrite Znat.Z2Nat.id in LE; [|apply Int64_intval_pos].

      rewrite !Int64.unsigned_repr_eq.
      f_equal.
      rewrite Zdiv.Zmod_small; try lia.
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

  - (* Re-establish loop invariant *)
    eapply INV_STABLE. right. solve_lid_bound_between.

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
          (* It's a pointer! Pointer ! *)
          clean_goal. subst I. clear INV_STABLE. clear WHILE Heqs6 Heqs14 Heqs13.
          clear E.
          clean_goal.
          clear EQ_y_HG'.
          revert MINV_YOFF; intros.

          (* pose proof HDST_GEP. *)
          (* pose proof (from_N_intval _ EQsz0) as EQ. *)
          edestruct mem_is_inv as (? & ? & ? & ? & ? & ?); clear mem_is_inv.

          eexists. eexists. split; eauto.

          split. eapply dtyp_fits_after_write; eauto.

          split; eauto. intros.
          specialize (H6 H7).
          destruct H6 as (? & ? & ? ).
          eexists. split; eauto.
          intros.
          inv H3.
          erewrite write_untouched_ptr_block_get_array_cell.
          2 : eauto.
          2 : eauto.
          eauto.

          assert (fst x1 ≢ fst ptrll_yoff). {
            do 2 red in st_no_llvm_ptr_aliasing.
            rewrite <- EE in CEq. 
            specialize (st_no_llvm_ptr_aliasing x0 x1 y ptrll_yoff n2 (S (S n1))).
            cbn in st_no_llvm_ptr_aliasing.
            eapply st_no_llvm_ptr_aliasing. eauto. eauto. rewrite <- EE. eauto. rewrite <- EE. eauto. eauto. eauto.
            eauto.
          }

          assert (fst ptrll_yoff ≡ fst dst_addr). {
            revert HDST_GEP; intros.
            unfold handle_gep_addr in HDST_GEP.
            destruct ptrll_yoff. cbn in HDST_GEP. inv HDST_GEP. cbn. auto.
          }
          rewrite <- H7. auto.
        }
      }
    }

    {
      eapply dtyp_fits_after_write; eauto.
      destruct INV_p; auto.
    }

    (* Partial memory up to (S k) *)
    {
      (* intros. *)
      intros i v0 Bounds_sz MLU_k.
      rename MINV_YOFF into MINV_partial.
      revert MINV_partial; intros.

      destruct (@dec_eq_nat (MInt64asNT.to_nat i) k).
      {
        (* This is the index that _was_ written to. *)
        subst.
        rewrite mem_lookup_mem_add_eq in MLU_k. inv MLU_k.
        erewrite <- read_array.
        pose proof @write_read as WR.
        specialize (WR _ _ DTYPE_Double  _ _ H1).
        cbn in WR. eapply WR. constructor. solve_allocated.
        eauto.
      }
      {
        (* This wasn't written to, and is covered by the partial memory
           invariant up to this point. *)
        destruct Bounds_sz.
        assert (Bounds_rest: MInt64asNT.to_nat i < k). {
          lia.
        }
        specialize (MINV_partial i v0).

        - erewrite write_array_cell_untouched.
          eapply MINV_partial.
          left; auto.
          rewrite mem_lookup_mem_add_neq in MLU_k; eauto.
          erewrite <- write_array_lemma. eauto. solve_allocated. eauto. constructor.
          pose proof @to_nat_unsigned.

          repeat rewrite repr_of_nat_to_nat.
          pose proof EQk.
          eapply to_nat_repr_nat in H4.

          intros CONTRA.
          rewrite <- H4 in H0.
          eapply to_nat_unsigned in H0. apply H0.
          rewrite repr_of_nat_to_nat. rewrite <- CONTRA.
          rewrite H4. reflexivity.


        - erewrite write_array_cell_untouched.
          eapply MINV_partial.
          right; auto.
          rewrite mem_lookup_mem_add_neq in MLU_k; eauto.
          erewrite <- write_array_lemma. eauto. solve_allocated. eauto. constructor.
          pose proof @to_nat_unsigned.

          repeat rewrite repr_of_nat_to_nat.
          pose proof EQk.
          eapply to_nat_repr_nat in H4.

          intros CONTRA.
          rewrite <- H4 in H0.
          eapply to_nat_unsigned in H0. apply H0.
          rewrite repr_of_nat_to_nat. rewrite <- CONTRA.
          rewrite H4. reflexivity.

      }
    }

    solve_allocated.

    (* local_scope_modif s1 s11 li (li' [py : UVALUE_Addr y_GEP_addr]) *)
  -  eapply local_scope_modif_add'.
     solve_lid_bound_between.
     eapply local_scope_modif_sub'_l; cycle 1.
     eapply local_scope_modif_sub'_l; cycle 1.
     eapply local_scope_modif_shrink. eauto.
     solve_local_count. solve_local_count.
     solve_lid_bound_between.
     solve_lid_bound_between.
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
  destruct H as (? & ? & ? & ?). subst. destruct H2.
  subst.
  split ;[|split]; eauto.
  destruct H.
  split; eauto; cycle 1.
  eapply WF_IRState_protect; eauto.
  eapply no_id_aliasing_protect; eauto.
  eapply no_dshptr_aliasing_protect; eauto.
  eapply no_llvm_ptr_aliasing_protect; eauto.

  (* id's are still well-allocated. *)
  {
    red in st_id_allocated. red. intros.
    destruct (@dec_eq_nat n1 n2). subst.
    rewrite Heqo0 in H. inv H.
    apply mem_block_exists_memory_set_eq. reflexivity.
    apply mem_block_exists_memory_set. eapply st_id_allocated.
    eapply nth_error_protect_ineq in H. 2 : eauto.
    eauto.
  }

  clear INV_STABLE. clear NOFAIL_cont.

  cbn in *. intros.
  rename H0 into PARTIAL_MEM_COMPLETE.
  destruct PARTIAL_MEM_COMPLETE as (FITS & INLG & MLU).
  (* Two possible cases : either the index isn't with the pointer location,
     which is where we can use the normal memory invariant [mem_is_inv].
     Ohterwise, we can show that the [partial memory write] is complete
     and use [MLU] to restate the memory lookup. *)
  destruct (Nat.eq_dec n1 n2); cycle 1.
  {
    (* Case 1 : The address in question was not written to : use normal memory
      invariant. *)
    subst. eapply nth_error_protect_ineq in H; eauto.
    specialize (mem_is_inv _ _ _ _ _ H H1). destruct v0; eauto.
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
}

setoid_rewrite <- bind_ret_r at 6.

vstep.
eapply eutt_clo_bind_returns.

(* PRECONDITION *)

eapply GENC.
{
  subst P I. clear GENC.
  cbn. split; [|split]; eauto.
  apply state_invariant_protect.
  eapply state_invariant_Γ. eauto.
  solve_gamma. solve_local_count.
}

intros [[]|]; intros (? & ? & ? & []) (? & ? & ?) RET1 RET2; subst P I; try_abs;
cbn in H0; try destruct H0 as (? & <- & <- & ?); try contradiction.
  rewrite interp_helix_MemSet.
2 : { destruct H; inv H. } (* absurd *)

vred.
apply eqit_Ret.


(* genIR *)
{
  split; [| split]; cbn; eauto.
  - destruct H0 as (? & ? & ?); subst.
    destruct H0.

    split; eauto.
  - destruct H; eauto.
  - solve_local_scope_modif.
}
Qed.
