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

Section DSHLoop_is_tfor.

  Definition DSHPower_tfor
             (σ: evalContext)
             (n: nat)
             (f: AExpr)
             (x y: mem_block)
             (xoffset yoffset: nat) :
    itree Event mem_block
    :=
      tfor (fun i acc =>
              xv <- lift_Derr (mem_lookup_err "Error reading 'xv' memory in denoteDSHBinOp" xoffset x) ;;
              yv <- lift_Derr (mem_lookup_err "Error reading 'yv' memory in denoteDSHBinOp" yoffset acc) ;;
              v' <- denoteBinCType σ f yv xv ;;
              ret (mem_add yoffset v' acc)
           ) 0 n y.

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

End DSHLoop_is_tfor.


