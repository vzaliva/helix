Require Import Coq.Arith.Arith.
Require Import Psatz.

Require Import Coq.Strings.String.

Open Scope string_scope.
Open Scope char_scope.

Require Import Coq.Lists.List.

Require Import Coq.Numbers.BinNums. (* for Z scope *)
Require Import Coq.ZArith.BinInt.

Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.FSigmaHCOL.Int64asNT.
Require Import Helix.FSigmaHCOL.Float64asCT.
Require Import Helix.DSigmaHCOL.DSigmaHCOLITree.
Require Import Helix.LLVMGen.Compiler.
Require Import Helix.LLVMGen.Externals.
Require Import Helix.LLVMGen.Data.
Require Import Helix.LLVMGen.Utils.
Require Import Helix.LLVMGen.tmp_aux_Vellvm.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.Util.ErrorSetoid.
Require Import Helix.Util.ListUtil.
Require Import Helix.Tactics.HelixTactics.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Map.FMapAList.

Require Import Vellvm.Tactics.
Require Import Vellvm.Util.
Require Import Vellvm.LLVMEvents.
Require Import Vellvm.DynamicTypes.
Require Import Vellvm.Denotation.
Require Import Vellvm.Handlers.Handlers.
Require Import Vellvm.TopLevel.
Require Import Vellvm.LLVMAst.
Require Import Vellvm.CFG.
Require Import Vellvm.InterpreterMCFG.
Require Import Vellvm.InterpreterCFG.
Require Import Vellvm.TopLevelRefinements.
Require Import Vellvm.TypToDtyp.
Require Import Vellvm.LLVMEvents.

Require Import Ceres.Ceres.

Require Import ITree.Interp.TranslateFacts.
Require Import ITree.Basics.CategoryFacts.
Require Import ITree.Events.State.
Require Import ITree.Events.StateFacts.
Require Import ITree.ITree.
Require Import ITree.Eq.Eq.
Require Import ITree.Basics.Basics.
Require Import ITree.Interp.InterpFacts.

Require Import Flocq.IEEE754.Bits.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.misc.decision.

Require Import Helix.LLVMGen.Correctness_Invariants.

Set Implicit Arguments.
Set Strict Implicit.

Import MDSHCOLOnFloat64.
Import D.
Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

Opaque incBlockNamed.
Opaque incVoid.
Opaque incLocal.


Section MExpr.

  Definition invariant_MExpr
             (σ : evalContext)
             (s : IRState) (mexp : MExpr) : Rel_cfg_T (mem_block * Int64.int) uvalue :=
    fun '(memH, (mb, mb_sz)) '(memV, (ρ, (g, res))) =>
      (exists ptr i (vid : nat) (mid : mem_block_id) (size : Int64.int) (sz : int), (* TODO: sz ≈ size? *)
        res ≡ UVALUE_Addr ptr /\
        memory_lookup memH mid ≡ Some mb /\
        in_local_or_global ρ g memV i (DVALUE_Addr ptr) (TYPE_Array sz TYPE_Double) /\
        nth_error σ vid ≡ Some (DSHPtrVal mid size) /\
        nth_error (Γ s) vid ≡ Some (i, TYPE_Pointer (TYPE_Array sz TYPE_Double))) /\
      evalMExpr memH σ mexp ≡ inr (mb, mb_sz).

  (* TODO: like ext_local, but locals also don't change. Not sure what to call this... *)
  Definition preserves_states {R S}: memoryH -> config_cfg -> Rel_cfg_T R S :=
    fun mh '(mi,(li,gi)) '(mh',_) '(m,(l,(g,_))) => mh ≡ mh' /\ mi ≡ m /\ gi ≡ g /\ li ≡ l.

  Lemma preserves_states_refl:
  forall {R S} memH memV l g n v,
    @preserves_states R S memH (mk_config_cfg memV l g) (memH, n) (memV, (l, (g, v))).
  Proof.
    intros; repeat split; reflexivity.
  Qed.
  Hint Resolve preserves_states_refl: core.

  Record genMExpr_rel
         (σ : evalContext)
         (s : IRState)
         (mexp : MExpr)
         (mi : memoryH) (sti : config_cfg)
         (mf : memoryH * (mem_block * Int64.int)) (stf : config_cfg_T uvalue)
    : Prop :=
    {
    mexp_correct :invariant_MExpr σ s mexp mf stf;
    m_preserves : preserves_states mi sti mf stf
    }.

  Lemma memory_invariant_Ptr : forall vid σ s memH memV l g a size x sz,
      state_invariant σ s memH (memV, (l, g)) ->
      nth_error σ vid ≡ Some (DSHPtrVal a size) ->
      nth_error (Γ s) vid ≡ Some (x, TYPE_Pointer (TYPE_Array sz TYPE_Double)) ->
      ∃ (bk_helix : mem_block) (ptr_llvm : Addr.addr),
        memory_lookup memH a ≡ Some bk_helix
        ∧ in_local_or_global l g memV x (DVALUE_Addr ptr_llvm) (TYPE_Pointer (TYPE_Array sz TYPE_Double))
        ∧ (∀ (i : Memory.NM.key) (v : binary64), mem_lookup i bk_helix ≡ Some v → get_array_cell memV ptr_llvm i DTYPE_Double ≡ inr (UVALUE_Double v)).
  Proof.
    intros * [MEM _ _] LU1 LU2; eapply MEM in LU1; eapply LU1 in LU2; eauto.
  Qed.

  (** ** Compilation of MExpr
  *)
  Lemma genMExpr_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *)   (mexp: MExpr) (σ: evalContext) (memH: memoryH) v
      (* Vellvm bits *)   (exp: exp typ) (c: code typ) (g : global_env) (l : local_env) (memV : memoryV) (τ: typ),
      genMExpr mexp s1 ≡ inr (s2, (exp, c, τ)) -> (* Compilation succeeds *)
      evalMExpr memH σ mexp ≡ inr v    -> (* Evaluation succeeds *)
      state_invariant σ s1 memH (memV, (l, g)) ->
      eutt (lift_Rel_cfg (state_invariant σ s2) ⩕ genMExpr_rel σ s2 mexp memH (mk_config_cfg memV l g))
           (with_err_RB
              (interp_Mem (denoteMExpr σ mexp)
                          memH))
           (with_err_LB
              ((interp_cfg (D.denote_code (convert_typ [] c) ;; translate exp_E_to_instr_E (D.denote_exp (Some DTYPE_Pointer (* (DTYPE_I 64%Z) *)) (convert_typ [] exp))))
                 g l memV)).
  Proof.
    intros * Hgen Heval Hmeminv.
    generalize Hmeminv; intros WF; apply IRState_is_WF in WF.

    unfold denoteMExpr; cbn*.
    destruct mexp as [[vid] | mblock].
    - (* PtrDeref case *)

      unfold denotePExpr; cbn*.
      cbn* in Hgen; simp.
      cbn*; repeat norm_v.
      norm_h.
      break_inner_match_goal; try abs_by_WF.
      2: cbn* in Heval; rewrite Heqo0 in Heval; inv Heval.
      norm_h.
      break_inner_match_goal; try abs_by_WF.
      subst.

      edestruct memory_invariant_Ptr as (bkH & ptrV & Mem_LU & LUV & EQ); eauto.

      destruct i0.
      + (* Global *)
        cbn in *.
        (* This case should be absurd if I'm not mistaken: we read in memory at an Array type, and yet find an address *)
        exfalso.
        clear - LUV.
        destruct LUV as (ptr & τ' & EQ & LU & READ).
        inv EQ.
        clear -READ.

        do 2 rewrite typ_to_dtyp_equation in READ.
        cbn in READ.

        assert (not_undef (UVALUE_Addr ptrV)) as NU.
        { intros t TYP. inversion TYP. }
        eapply read_array_not_pointer; eauto.
        reflexivity.
        constructor.
      + (*  Local *)
        cbn in *.
        repeat norm_h.
        2: apply memory_lookup_err_inr_Some_eq; eassumption.
        rewrite denote_code_nil; cbn.
        repeat norm_v.
        2:eauto.
        cbn*; repeat norm_v.
        apply eutt_Ret.
        split; auto.
        split; auto.
        red.
        split.
        { do 6 eexists.
          splits; eauto.
          cbn; auto.
        }
        { destruct v as (v & bk_sz). assert (v ≡ bkH) as VBKH.
          { simp.
            inv_memory_lookup_err.
            inversion Mem_LU.
            auto.
          }

          subst.
          cbn.
          match_rewrite.
          rewrite Heqo0 in Heval.
          unfold memory_lookup_err in *.
          rewrite Mem_LU.
          rewrite Mem_LU in Heval.
          cbn in *.
          inversion Heval.
          reflexivity.
        }
    - (* Const *)
      cbn* in Hgen; simp.
  Qed.

  (* TODO: move these, and use them more. *)

  Lemma genMExpr_memH : forall σ s e memH memV memH' memV' l g l' g' mb uv,
      genMExpr_rel σ s e memH (mk_config_cfg memV l g) (memH', mb)
                   (memV', (l', (g', uv))) ->
      memH ≡ memH'.
  Proof.
    intros * H.
    destruct H; cbn in *; intuition.
  Qed.

  Lemma genMExpr_memV : forall σ s e memH memV memH' memV' l g l' g' mb uv,
      genMExpr_rel σ s e memH (mk_config_cfg memV l g) (memH', mb)
                   (memV', (l', (g', uv))) ->
      memV ≡ memV'.
  Proof.
    intros * H.
    destruct H; cbn in *; intuition.
  Qed.

  Lemma genMExpr_g : forall σ s e memH memV memH' memV' l g l' g' mb uv,
      genMExpr_rel σ s e memH (mk_config_cfg memV l g) (memH', mb)
                   (memV', (l', (g', uv))) ->
      g ≡ g'.
  Proof.
    intros * H.
    destruct H; cbn in *; intuition.
  Qed.

  Lemma genMExpr_l : forall σ s e memH memV memH' memV' l g l' g' mb uv,
      genMExpr_rel σ s e memH (mk_config_cfg memV l g) (memH', mb)
                   (memV', (l', (g', uv))) ->
      l ≡ l'.
  Proof.
    intros * H.
    destruct H; cbn in *; intuition.
  Qed.

  Lemma genMExpr_preserves_WF:
    forall mexp s s' σ x,
      WF_IRState σ s ->
      genMExpr mexp s ≡ inr (s',x) ->
      WF_IRState σ s'.
  Proof.
    induction mexp; intros * WF GEN; cbn* in GEN; simp; auto.
  Qed.

  Lemma genMExpr_array : forall {s1 s2 m e c t},
      genMExpr m s1 ≡ inr (s2, (e, c, t)) ->
      exists sz, t ≡ TYPE_Array sz TYPE_Double.
  Proof.
    intros s1 s2 m e c t H.
    destruct m; cbn in H; inv H.
    simp.
    exists sz.
    reflexivity.
  Qed.

End MExpr.

Ltac genMExpr_rel_subst :=
  match goal with
  | MEXP : genMExpr_rel ?σ ?s ?e ?memH (mk_config_cfg ?memV ?l ?g) (?memH', ?mb) (?memV', (?l', (?g', ?uv))) |- _ =>
    let H := fresh in
    pose proof genMExpr_memH MEXP as H; subst memH';
    pose proof genMExpr_memV MEXP as H; subst memV';
    pose proof genMExpr_g MEXP as H; subst g';
    pose proof genMExpr_l MEXP as H; subst l'
  end.

