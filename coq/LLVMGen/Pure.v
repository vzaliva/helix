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
From ITree Require Import ITree Eq.Eq HeterogeneousRelations.

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


Section pure.

  Ltac interp_MF_ret := setoid_rewrite interp_Mem_ret; setoid_rewrite interp_fail_ret; cbn.
  Ltac interp_MF_bind := setoid_rewrite interp_Mem_bind; setoid_rewrite interp_fail_bind; cbn.

  Lemma interp_fail_throw :
    forall T s mH, interp_fail handle_failure (interp_Mem (T := T) (throw s) mH) ≈ Ret None.
  Proof.
    intros. setoid_rewrite interp_Mem_vis_eqit.
    unfold pure_state in *; cbn in *.
    rewrite !interp_fail_bind.
    rewrite !interp_fail_vis.
    cbn in *.
    rewrite Eq.bind_bind, !bind_ret_l. reflexivity.
  Qed.

  Ltac fail_f := left;
                 solve [ rewrite bind_ret_l; reflexivity | unfold Dfail, Sfail; rewrite interp_fail_throw; reflexivity ].
  Ltac ret_f := right; setoid_rewrite interp_Mem_ret; setoid_rewrite interp_fail_ret; cbn; eexists; reflexivity.

  Ltac break_classic name :=
    match goal with
    | [ H : forall (σ : evalContext) (memH : memoryH),
          interp_fail handle_failure (interp_Mem (denoteNExpr σ ?nexp1) memH) ≈ Ret None \/ _ |-
          ITree.bind (interp_fail _ (interp_Mem (denoteNExpr _ ?nexp1) _)) _ ≈ _ \/ _] =>
      edestruct H as [name | (? & name)]
    end.

  Ltac fail_or_ret := solve [fail_f | ret_f].

  Ltac fr_crush He1 He2 :=
    cbn* in *; interp_MF_bind;
    break_classic He1; setoid_rewrite He1;
      [ fail_f | setoid_rewrite bind_ret_l; interp_MF_bind;
                break_classic He2;
                setoid_rewrite He2; [fail_f | setoid_rewrite bind_ret_l; try break_match; fail_or_ret ]].

  Lemma genNExpr_correct_pure_classic :
    forall (* Helix  bits *)   (nexp: NExpr) (σ: evalContext) (memH: memoryH),
      eutt eq (interp_fail handle_failure (interp_Mem (denoteNExpr σ nexp) memH)) (Ret None) \/
      exists t, eutt eq (interp_fail handle_failure (interp_Mem (denoteNExpr σ nexp) memH)) (Ret (Some (memH, t))).
  Proof.
    intros nexp; induction nexp; intros *.
    all : try solve [unfold denoteNExpr; fail_or_ret |
                  unfold denoteNExpr in *; cbn* in *; break_match; simp; fail_or_ret |
                  fr_crush He1 He2].
  Qed.

  Lemma genMExpr_correct_pure_classic :
    forall (* Helix  bits *)   (mexp: MExpr) (σ: evalContext) (memH: memoryH),
    eutt eq (interp_fail handle_failure (interp_Mem (denoteMExpr σ mexp) memH)) (Ret None) \/
      exists t, eutt eq (interp_fail handle_failure (interp_Mem (denoteMExpr σ mexp) memH)) (Ret (Some (memH, t))).
  Proof.
    intros mexp; induction mexp; intros *; unfold denoteMExpr, denotePExpr in *; cbn* in *.

    - break_match; simp; try_abs.
      interp_MF_bind. rewrite interp_fail_throw.
      setoid_rewrite bind_ret_l. left. reflexivity.
      setoid_rewrite bind_ret_l.
      interp_MF_bind.
      unfold interp_Mem.
      setoid_rewrite interp_state_trigger.
      cbn. break_match.
      cbn. setoid_rewrite interp_fail_vis. cbn.
      setoid_rewrite bind_ret_l. left. setoid_rewrite bind_ret_l. reflexivity.
      cbn. setoid_rewrite interp_fail_ret. cbn.
      setoid_rewrite bind_ret_l.
      setoid_rewrite interp_state_ret. setoid_rewrite interp_fail_ret. right.
      eexists. cbn. reflexivity.
    - interp_MF_ret. right. eexists. reflexivity.
  Qed.

  Lemma genAExpr_correct_helix_pure_classic :
    forall (aexp: AExpr) (σ: evalContext) (memH: memoryH),
    eutt eq (interp_fail handle_failure (interp_Mem (denoteAExpr σ aexp) memH)) (Ret None) \/
      exists t, eutt eq (interp_fail handle_failure (interp_Mem (denoteAExpr σ aexp) memH)) (Ret (Some (memH, t))).
  Proof.
    intros aexp; induction aexp; intros *.
    - (* Variable case *)
      (* Reducing the compilation *)
      (* The variable maps to an integer in the IRState *)
      unfold denoteAExpr in *; cbn* in *; break_match; simp; interp_MF_bind.
      left. rewrite interp_fail_throw, bind_ret_l. reflexivity.
      interp_MF_ret.
      setoid_rewrite bind_ret_l.
      break_match; simp; fail_or_ret.
    - (* Constant *)
      cbn* in *; ret_f.
    - (* ANth m n: lookup to m[n] *)
      cbn* in *.
      edestruct genNExpr_correct_pure_classic with (nexp := n) as [? | (? & ?)];
        interp_MF_bind; setoid_rewrite H.
      setoid_rewrite bind_ret_l.
      left; reflexivity.
      setoid_rewrite bind_ret_l.
      edestruct genMExpr_correct_pure_classic with (mexp := m) as [? | (? & ?)];
        interp_MF_bind; setoid_rewrite H0.
      setoid_rewrite bind_ret_l. left; reflexivity.
      setoid_rewrite bind_ret_l. destruct x0.
      break_match; simp; break_match; simp.
      left. interp_MF_bind. rewrite interp_fail_throw. rewrite bind_ret_l. reflexivity.
      left. interp_MF_bind. rewrite interp_fail_throw. rewrite bind_ret_l. reflexivity.
      left. cbn. rewrite bind_ret_l. rewrite interp_fail_throw. reflexivity.
      right. setoid_rewrite bind_ret_l. interp_MF_ret. eexists; reflexivity.
    - (* AAbs *) 
      cbn* in *; simp.
      edestruct IHaexp; eauto.

      interp_MF_bind.
      setoid_rewrite H.
      setoid_rewrite bind_ret_l. left; reflexivity.
      destruct H. interp_MF_bind. setoid_rewrite H.
      setoid_rewrite bind_ret_l. interp_MF_ret.
      right. eexists. reflexivity.

    (* - (* APlus *) *)
    - cbn* in *; simp;
      edestruct IHaexp1 as [He1 | (? & He1)]; interp_MF_bind; setoid_rewrite He1;
      setoid_rewrite bind_ret_l; [left; reflexivity |
      edestruct IHaexp2 as [He2 | (? & He2)]; interp_MF_bind; setoid_rewrite He2; setoid_rewrite bind_ret_l;
      [left; reflexivity |
      right; interp_MF_ret; eexists; reflexivity]].


    - cbn* in *; simp;
      edestruct IHaexp1 as [He1 | (? & He1)]; interp_MF_bind; setoid_rewrite He1;
      setoid_rewrite bind_ret_l; [left; reflexivity |
      edestruct IHaexp2 as [He2 | (? & He2)]; interp_MF_bind; setoid_rewrite He2; setoid_rewrite bind_ret_l;
      [left; reflexivity |
      right; interp_MF_ret; eexists; reflexivity]].

    - cbn* in *; simp;
      edestruct IHaexp1 as [He1 | (? & He1)]; interp_MF_bind; setoid_rewrite He1;
      setoid_rewrite bind_ret_l; [left; reflexivity |
      edestruct IHaexp2 as [He2 | (? & He2)]; interp_MF_bind; setoid_rewrite He2; setoid_rewrite bind_ret_l;
      [left; reflexivity |
      right; interp_MF_ret; eexists; reflexivity]].

    - cbn* in *; simp;
      edestruct IHaexp1 as [He1 | (? & He1)]; interp_MF_bind; setoid_rewrite He1;
      setoid_rewrite bind_ret_l; [left; reflexivity |
      edestruct IHaexp2 as [He2 | (? & He2)]; interp_MF_bind; setoid_rewrite He2; setoid_rewrite bind_ret_l;
      [left; reflexivity |
      right; interp_MF_ret; eexists; reflexivity]].

    - cbn* in *; simp;
      edestruct IHaexp1 as [He1 | (? & He1)]; interp_MF_bind; setoid_rewrite He1;
      setoid_rewrite bind_ret_l; [left; reflexivity |
      edestruct IHaexp2 as [He2 | (? & He2)]; interp_MF_bind; setoid_rewrite He2; setoid_rewrite bind_ret_l;
      [left; reflexivity |
      right; interp_MF_ret; eexists; reflexivity]].

    - cbn* in *; simp;
      edestruct IHaexp1 as [He1 | (? & He1)]; interp_MF_bind; setoid_rewrite He1;
      setoid_rewrite bind_ret_l; [left; reflexivity |
      edestruct IHaexp2 as [He2 | (? & He2)]; interp_MF_bind; setoid_rewrite He2; setoid_rewrite bind_ret_l;
      [left; reflexivity |
      right; interp_MF_ret; eexists; reflexivity]].
  Qed. (* TODO: crush-ey Ltac.. *)


  Lemma genMExpr_correct_pure :
    forall (* Helix  bits *)   (mexp: MExpr) (σ: evalContext) (memH: memoryH),
      no_failure (interp_helix (E := E_cfg) (denoteMExpr σ mexp) memH) -> (* Source semantics defined *)
      exists t, eutt eq (interp_fail handle_failure (interp_Mem (denoteMExpr σ mexp) memH)) (Ret (Some (memH, t))).
  Proof.
    intros * NOFAIL.
    destruct mexp as [[vid] | mblock]; cbn* in *; simp.
    unfold denoteMExpr, denotePExpr in *; cbn* in *.

    simp; try_abs. subst.
    setoid_rewrite bind_ret_l.
    setoid_rewrite bind_ret_l in NOFAIL.
    2 : { interp_MF_ret. eexists. reflexivity. }
    interp_MF_bind.
    unfold interp_Mem.
    setoid_rewrite interp_state_trigger.
    cbn* in *.

    assert (NOFAIL' := NOFAIL).

    setoid_rewrite interp_helix_bind in NOFAIL.
    unfold interp_helix, interp_Mem in NOFAIL.

    apply no_failure_bind_prefix in NOFAIL.

    unfold Exception.throw in *.
    unfold interp_helix in *.

    unfold interp_fail in NOFAIL.
    setoid_rewrite interp_state_vis in NOFAIL.
    unfold pure_state in *; cbn in *.
    setoid_rewrite interp_fail_bind in NOFAIL.

    cbn* in *. simp; try_abs. exfalso.

    setoid_rewrite interp_fail_vis in NOFAIL.
    cbn in *.
    rewrite Eq.bind_bind, !bind_ret_l in NOFAIL.
    rewrite translate_ret in NOFAIL. red in NOFAIL. red in NOFAIL.
    apply eutt_Ret in NOFAIL.
    apply NOFAIL; auto.
    clear NOFAIL.

    setoid_rewrite interp_fail_ret. setoid_rewrite bind_ret_l.
    eexists.
    setoid_rewrite interp_state_ret.
    setoid_rewrite interp_fail_ret.
    cbn. reflexivity.
  Qed.


  Lemma genNExpr_correct_pure :
    forall (* Helix  bits *)   (nexp: NExpr) (σ: evalContext) (memH: memoryH),
      no_failure (interp_helix (E := E_cfg) (denoteNExpr σ nexp) memH) -> (* Source semantics defined *)
      exists t, eutt eq (interp_fail handle_failure (interp_Mem (denoteNExpr σ nexp) memH)) (Ret (Some (memH, t))).
  Proof.
    intros nexp; induction nexp; intros * NOFAIL.
    - (* Variable case *)
      (* Reducing the successful compilation *)
      simp.
      (* The variable maps to an integer in the IRState *)
      unfold denoteNExpr in *; cbn* in *; simp; try_abs.
      interp_MF_ret. eexists. reflexivity.

    - (* Const *)
      unfold denoteNExpr in *; cbn in *; simp; try_abs.
      interp_MF_ret. eexists. reflexivity.

    - (* NDiv *)
      cbn* in *; simp; try_abs.
      interp_MF_bind.
      clean_goal.


      edestruct IHnexp1.
      assert (NOFAIL' := NOFAIL).
      apply no_failure_helix_bind_prefix in NOFAIL'; eauto.
      setoid_rewrite H.
      setoid_rewrite bind_ret_l.

      edestruct IHnexp2.
      rewrite interp_helix_bind in NOFAIL.
      unfold interp_helix at 1 in NOFAIL.
      setoid_rewrite H in NOFAIL.
      rewrite translate_ret in NOFAIL. rewrite bind_ret_l in NOFAIL.
      rewrite interp_helix_bind in NOFAIL.
      eapply no_failure_bind_prefix in NOFAIL; eauto.

      interp_MF_bind.
      setoid_rewrite H0.
      setoid_rewrite bind_ret_l.
      rewrite interp_helix_bind in NOFAIL.
      unfold interp_helix at 1 in NOFAIL.
      setoid_rewrite H in NOFAIL.
      rewrite translate_ret in NOFAIL. rewrite bind_ret_l in NOFAIL.
      rewrite interp_helix_bind in NOFAIL.

      unfold interp_helix at 1 in NOFAIL.
      setoid_rewrite H0 in NOFAIL.
      rewrite translate_ret in NOFAIL. rewrite bind_ret_l in NOFAIL.

      destruct (MInt64asNT.NTypeEqDec x0 MInt64asNT.NTypeZero ).
      try_abs.

      interp_MF_ret. eexists. reflexivity.

    - (* NMod *)
      cbn* in *; simp; try_abs.
      interp_MF_bind.
      clean_goal.

      edestruct IHnexp1.
      assert (NOFAIL' := NOFAIL).
      apply no_failure_helix_bind_prefix in NOFAIL'; eauto.
      setoid_rewrite H.
      setoid_rewrite bind_ret_l.

      edestruct IHnexp2.
      rewrite interp_helix_bind in NOFAIL.
      unfold interp_helix at 1 in NOFAIL.
      setoid_rewrite H in NOFAIL.
      rewrite translate_ret in NOFAIL. rewrite bind_ret_l in NOFAIL.
      rewrite interp_helix_bind in NOFAIL.
      eapply no_failure_bind_prefix in NOFAIL; eauto.

      interp_MF_bind.
      setoid_rewrite H0.
      setoid_rewrite bind_ret_l.
      rewrite interp_helix_bind in NOFAIL.
      unfold interp_helix at 1 in NOFAIL.
      setoid_rewrite H in NOFAIL.
      rewrite translate_ret in NOFAIL. rewrite bind_ret_l in NOFAIL.
      rewrite interp_helix_bind in NOFAIL.

      unfold interp_helix at 1 in NOFAIL.
      setoid_rewrite H0 in NOFAIL.
      rewrite translate_ret in NOFAIL. rewrite bind_ret_l in NOFAIL.

      destruct (MInt64asNT.NTypeEqDec x0 MInt64asNT.NTypeZero ).
      try_abs.

      interp_MF_ret. eexists. reflexivity.

   - (* NAdd *)

      cbn* in *; simp; try_abs.
      interp_MF_bind.
      clean_goal.

      edestruct IHnexp1.
      assert (NOFAIL' := NOFAIL).
      apply no_failure_helix_bind_prefix in NOFAIL'; eauto.
      setoid_rewrite H.
      setoid_rewrite bind_ret_l.

      edestruct IHnexp2.
      rewrite interp_helix_bind in NOFAIL.
      unfold interp_helix at 1 in NOFAIL.
      setoid_rewrite H in NOFAIL.
      rewrite translate_ret in NOFAIL. rewrite bind_ret_l in NOFAIL.
      rewrite interp_helix_bind in NOFAIL.
      eapply no_failure_bind_prefix in NOFAIL; eauto.

      interp_MF_bind.
      setoid_rewrite H0.
      setoid_rewrite bind_ret_l.
      rewrite interp_helix_bind in NOFAIL.
      unfold interp_helix at 1 in NOFAIL.
      setoid_rewrite H in NOFAIL.
      rewrite translate_ret in NOFAIL. rewrite bind_ret_l in NOFAIL.
      rewrite interp_helix_bind in NOFAIL.

      unfold interp_helix at 1 in NOFAIL.
      setoid_rewrite H0 in NOFAIL.
      rewrite translate_ret in NOFAIL. rewrite bind_ret_l in NOFAIL.

      destruct (MInt64asNT.NTypeEqDec x0 MInt64asNT.NTypeZero ).
      try_abs.

      interp_MF_ret. eexists. reflexivity.
      interp_MF_ret. eexists. reflexivity.
       
   - (* NMinus *)


      cbn* in *; simp; try_abs.
      interp_MF_bind.
      clean_goal.

      edestruct IHnexp1.
      assert (NOFAIL' := NOFAIL).
      apply no_failure_helix_bind_prefix in NOFAIL'; eauto.
      setoid_rewrite H.
      setoid_rewrite bind_ret_l.

      edestruct IHnexp2.
      rewrite interp_helix_bind in NOFAIL.
      unfold interp_helix at 1 in NOFAIL.
      setoid_rewrite H in NOFAIL.
      rewrite translate_ret in NOFAIL. rewrite bind_ret_l in NOFAIL.
      rewrite interp_helix_bind in NOFAIL.
      eapply no_failure_bind_prefix in NOFAIL; eauto.

      interp_MF_bind.
      setoid_rewrite H0.
      setoid_rewrite bind_ret_l.
      rewrite interp_helix_bind in NOFAIL.
      unfold interp_helix at 1 in NOFAIL.
      setoid_rewrite H in NOFAIL.
      rewrite translate_ret in NOFAIL. rewrite bind_ret_l in NOFAIL.
      rewrite interp_helix_bind in NOFAIL.

      unfold interp_helix at 1 in NOFAIL.
      setoid_rewrite H0 in NOFAIL.
      rewrite translate_ret in NOFAIL. rewrite bind_ret_l in NOFAIL.

      destruct (MInt64asNT.NTypeEqDec x0 MInt64asNT.NTypeZero ).
      try_abs.

      interp_MF_ret. eexists. reflexivity.
      interp_MF_ret. eexists. reflexivity.

    - (* NMult *)
      cbn* in *; simp; try_abs.
      interp_MF_bind.
      clean_goal.

      edestruct IHnexp1.
      assert (NOFAIL' := NOFAIL).
      apply no_failure_helix_bind_prefix in NOFAIL'; eauto.
      setoid_rewrite H.
      setoid_rewrite bind_ret_l.

      edestruct IHnexp2.
      rewrite interp_helix_bind in NOFAIL.
      unfold interp_helix at 1 in NOFAIL.
      setoid_rewrite H in NOFAIL.
      rewrite translate_ret in NOFAIL. rewrite bind_ret_l in NOFAIL.
      rewrite interp_helix_bind in NOFAIL.
      eapply no_failure_bind_prefix in NOFAIL; eauto.

      interp_MF_bind.
      setoid_rewrite H0.
      setoid_rewrite bind_ret_l.
      rewrite interp_helix_bind in NOFAIL.
      unfold interp_helix at 1 in NOFAIL.
      setoid_rewrite H in NOFAIL.
      rewrite translate_ret in NOFAIL. rewrite bind_ret_l in NOFAIL.
      rewrite interp_helix_bind in NOFAIL.

      unfold interp_helix at 1 in NOFAIL.
      setoid_rewrite H0 in NOFAIL.
      rewrite translate_ret in NOFAIL. rewrite bind_ret_l in NOFAIL.

      destruct (MInt64asNT.NTypeEqDec x0 MInt64asNT.NTypeZero ).
      try_abs.

      interp_MF_ret. eexists. reflexivity.
      interp_MF_ret. eexists. reflexivity.

    - (* NMin *)
      cbn* in *; simp; try_abs.
      interp_MF_bind.
      clean_goal.

      edestruct IHnexp1.
      assert (NOFAIL' := NOFAIL).
      apply no_failure_helix_bind_prefix in NOFAIL'; eauto.
      setoid_rewrite H.
      setoid_rewrite bind_ret_l.

      edestruct IHnexp2.
      rewrite interp_helix_bind in NOFAIL.
      unfold interp_helix at 1 in NOFAIL.
      setoid_rewrite H in NOFAIL.
      rewrite translate_ret in NOFAIL. rewrite bind_ret_l in NOFAIL.
      rewrite interp_helix_bind in NOFAIL.
      eapply no_failure_bind_prefix in NOFAIL; eauto.

      interp_MF_bind.
      setoid_rewrite H0.
      setoid_rewrite bind_ret_l.
      rewrite interp_helix_bind in NOFAIL.
      unfold interp_helix at 1 in NOFAIL.
      setoid_rewrite H in NOFAIL.
      rewrite translate_ret in NOFAIL. rewrite bind_ret_l in NOFAIL.
      rewrite interp_helix_bind in NOFAIL.

      unfold interp_helix at 1 in NOFAIL.
      setoid_rewrite H0 in NOFAIL.
      rewrite translate_ret in NOFAIL. rewrite bind_ret_l in NOFAIL.

      destruct (MInt64asNT.NTypeEqDec x0 MInt64asNT.NTypeZero ).
      try_abs.

      interp_MF_ret. eexists. reflexivity.
      interp_MF_ret. eexists. reflexivity.

    - (* NMax *)

      cbn* in *; simp; try_abs.
      interp_MF_bind.
      clean_goal.

      edestruct IHnexp1.
      assert (NOFAIL' := NOFAIL).
      apply no_failure_helix_bind_prefix in NOFAIL'; eauto.
      setoid_rewrite H.
      setoid_rewrite bind_ret_l.

      edestruct IHnexp2.
      rewrite interp_helix_bind in NOFAIL.
      unfold interp_helix at 1 in NOFAIL.
      setoid_rewrite H in NOFAIL.
      rewrite translate_ret in NOFAIL. rewrite bind_ret_l in NOFAIL.
      rewrite interp_helix_bind in NOFAIL.
      eapply no_failure_bind_prefix in NOFAIL; eauto.

      interp_MF_bind.
      setoid_rewrite H0.
      setoid_rewrite bind_ret_l.
      rewrite interp_helix_bind in NOFAIL.
      unfold interp_helix at 1 in NOFAIL.
      setoid_rewrite H in NOFAIL.
      rewrite translate_ret in NOFAIL. rewrite bind_ret_l in NOFAIL.
      rewrite interp_helix_bind in NOFAIL.

      unfold interp_helix at 1 in NOFAIL.
      setoid_rewrite H0 in NOFAIL.
      rewrite translate_ret in NOFAIL. rewrite bind_ret_l in NOFAIL.

      destruct (MInt64asNT.NTypeEqDec x0 MInt64asNT.NTypeZero ).
      try_abs.

      interp_MF_ret. eexists. reflexivity.
      interp_MF_ret. eexists. reflexivity.
  Qed.


  Lemma genAExpr_correct_helix_pure :
    forall (aexp: AExpr) (σ: evalContext) (memH: memoryH),
      no_failure (interp_helix (E := E_cfg) (denoteAExpr σ aexp) memH) -> (* Source semantics defined *)
      exists t, eutt eq (interp_fail handle_failure (interp_Mem (denoteAExpr σ aexp) memH)) (Ret (Some (memH, t))).
  Proof.
    intros aexp; induction aexp; intros * NOFAIL.
    - (* Variable case *)
      (* Reducing the compilation *)
      (* The variable maps to an integer in the IRState *)
      unfold denoteAExpr in *; cbn* in *.
      simp; try_abs.
      setoid_rewrite bind_ret_l.
      break_inner_match_goal; try_abs.

      interp_MF_ret. eexists. reflexivity.
    - (* Constant *)
      cbn* in *; simp.

      interp_MF_ret.
      eexists. reflexivity.

    - (* ANth m n: lookup to m[n] *)
      cbn* in *; simp.



      edestruct genNExpr_correct_pure. apply no_failure_helix_bind_prefix in NOFAIL; eauto.

      interp_MF_bind. setoid_rewrite H.
      setoid_rewrite bind_ret_l.

      edestruct genMExpr_correct_pure.

      setoid_rewrite interp_helix_bind in NOFAIL.
      unfold interp_helix at 1 in NOFAIL.
      setoid_rewrite H in NOFAIL.
      rewrite translate_ret in NOFAIL. rewrite bind_ret_l in NOFAIL.

      apply no_failure_helix_bind_prefix in NOFAIL.
      eauto.

      interp_MF_bind. setoid_rewrite H0.
      setoid_rewrite bind_ret_l. destruct x0.

      setoid_rewrite interp_helix_bind in NOFAIL.
      unfold interp_helix at 1 in NOFAIL.
      setoid_rewrite H in NOFAIL.
      rewrite translate_ret in NOFAIL. rewrite bind_ret_l in NOFAIL.

      setoid_rewrite interp_helix_bind in NOFAIL.
      unfold interp_helix at 1 in NOFAIL.
      setoid_rewrite H0 in NOFAIL.
      rewrite translate_ret in NOFAIL. rewrite bind_ret_l in NOFAIL.

      simp; try_abs. setoid_rewrite bind_ret_l.
      interp_MF_ret. eexists. reflexivity.

    - (* AAbs *) 
      cbn* in *; simp.
      edestruct IHaexp; eauto.


      interp_MF_bind.
      setoid_rewrite H.
      setoid_rewrite bind_ret_l.
      interp_MF_ret.
      eexists. reflexivity.

    - (* APlus *)
      cbn* in *; simp...
      interp_MF_bind.
      edestruct IHaexp1; eauto.

      setoid_rewrite H.
      setoid_rewrite bind_ret_l.

      eapply no_failure_helix_bind_continuation in NOFAIL; [| ]. eapply eutt_translate_gen in H.
      2 : { unfold interp_helix. rewrite H; eauto; econstructor. rewrite translate_ret. reflexivity. }
      edestruct IHaexp2. eauto.
      apply no_failure_helix_bind_prefix in NOFAIL. eauto.
      interp_MF_bind ; setoid_rewrite H0;
        setoid_rewrite bind_ret_l.
      eexists; interp_MF_ret; cbn; reflexivity.

    - (* AMinus *)

      cbn* in *; simp...
      interp_MF_bind.
      edestruct IHaexp1; eauto.

      setoid_rewrite H.
      setoid_rewrite bind_ret_l.

      eapply no_failure_helix_bind_continuation in NOFAIL; [| ]. eapply eutt_translate_gen in H.
      2 : { unfold interp_helix. rewrite H; eauto; econstructor. rewrite translate_ret. reflexivity. }
      edestruct IHaexp2. eauto.
      apply no_failure_helix_bind_prefix in NOFAIL. eauto.
      interp_MF_bind ; setoid_rewrite H0;
        setoid_rewrite bind_ret_l.
      eexists; interp_MF_ret; cbn; reflexivity .

    - (* AMult *)

      cbn* in *; simp...
      interp_MF_bind.
      edestruct IHaexp1; eauto.

      setoid_rewrite H.
      setoid_rewrite bind_ret_l.

      eapply no_failure_helix_bind_continuation in NOFAIL; [| ]. eapply eutt_translate_gen in H.
      2 : { unfold interp_helix. rewrite H; eauto; econstructor. rewrite translate_ret. reflexivity. }
      edestruct IHaexp2. eauto.
      apply no_failure_helix_bind_prefix in NOFAIL. eauto.
      interp_MF_bind ; setoid_rewrite H0;
        setoid_rewrite bind_ret_l.
      eexists; interp_MF_ret; cbn; reflexivity .

    - (* AMin *)

      cbn* in *; simp...
      interp_MF_bind.
      edestruct IHaexp1; eauto.

      setoid_rewrite H.
      setoid_rewrite bind_ret_l.

      eapply no_failure_helix_bind_continuation in NOFAIL; [| ]. eapply eutt_translate_gen in H.
      2 : { unfold interp_helix. rewrite H; eauto; econstructor. rewrite translate_ret. reflexivity. }
      edestruct IHaexp2. eauto.
      apply no_failure_helix_bind_prefix in NOFAIL. eauto.
      interp_MF_bind ; setoid_rewrite H0;
        setoid_rewrite bind_ret_l.
      eexists; interp_MF_ret; cbn; reflexivity .


    - (* AMax *)

      cbn* in *; simp...
      interp_MF_bind.
      edestruct IHaexp1; eauto.

      setoid_rewrite H.
      setoid_rewrite bind_ret_l.

      eapply no_failure_helix_bind_continuation in NOFAIL; [| ]. eapply eutt_translate_gen in H.
      2 : { unfold interp_helix. rewrite H; eauto; econstructor. rewrite translate_ret. reflexivity. }
      edestruct IHaexp2. eauto.
      apply no_failure_helix_bind_prefix in NOFAIL. eauto.
      interp_MF_bind ; setoid_rewrite H0;
        setoid_rewrite bind_ret_l.
      eexists; interp_MF_ret; cbn; reflexivity .

    - (* AZless *)

      cbn* in *; simp...
      interp_MF_bind.
      edestruct IHaexp1; eauto.

      setoid_rewrite H.
      setoid_rewrite bind_ret_l.

      eapply no_failure_helix_bind_continuation in NOFAIL; [| ]. eapply eutt_translate_gen in H.
      2 : { unfold interp_helix. rewrite H; eauto; econstructor. rewrite translate_ret. reflexivity. }
      edestruct IHaexp2. eauto.
      apply no_failure_helix_bind_prefix in NOFAIL. eauto.
      interp_MF_bind ; setoid_rewrite H0;
        setoid_rewrite bind_ret_l.
      eexists; interp_MF_ret; cbn; reflexivity .
      Unshelve.
      all : try eauto.
      all : intros * [].
  Qed.


End pure.
