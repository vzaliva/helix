Require Import Helix.LLVMGen.Correctness_Prelude.
Require Import Helix.LLVMGen.Correctness_Invariants.
Require Import Helix.LLVMGen.Correctness_NExpr.
Require Import Helix.LLVMGen.Correctness_MExpr.
Require Import Helix.LLVMGen.IdLemmas.
Require Import Helix.LLVMGen.StateCounters.
Require Import Helix.LLVMGen.VariableBinding.
Require Import Helix.LLVMGen.BidBound.

Require Import Helix.LLVMGen.Correctness_GenIR.
Set Nested Proofs Allowed.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.

Global Opaque resolve_PVar.

Import ProofMode.

(* DSHIMap case for [compile_FSHCOL_correct]. *)
Lemma compile_DSHIMap_correct:
  ∀ (n : nat)
    (x_p y_p : PExpr)
    (f : AExpr)
    (s1 s2 : IRState)
    (σ : evalContext)
    (memH : memoryH)
    (nextblock bid_in bid_from : block_id)
    (bks : list (LLVMAst.block typ))
    (g : global_env)
    (ρ : local_env)
    (memV : memoryV)
    (NEXT : bid_bound s1 nextblock)
    (BISIM : GenIR_Rel σ s1 bid_in (memH, ()) (memV, (ρ, (g, inl (bid_from, bid_in)))))
    (NOFAIL : @no_failure E_cfg (memoryH * ())
                          (interp_helix (denoteDSHOperator σ (DSHIMap n x_p y_p f)) memH))
    (GEN : genIR (DSHIMap n x_p y_p f) nextblock s1 ≡ inr (s2, (bid_in, bks))),
    eutt (succ_cfg (GenIR_Rel σ s2 nextblock))
         (interp_helix (denoteDSHOperator σ (DSHIMap n x_p y_p f)) memH)
         (interp_cfg (denote_bks (convert_typ [] bks) (bid_from, bid_in)) g ρ memV).
Proof.
  intros.

  Opaque genWhileLoop.
  cbn* in *.
  simp.
  unfold denotePExpr in *; cbn* in *.
  simp; try now (exfalso; clear -NOFAIL; try apply no_failure_Ret in NOFAIL; try_abs).
  apply no_failure_Ret in NOFAIL; simp; cbn in *; try_abs.

  hide_strings'.
  inv_resolve_PVar Heqs0.
  inv_resolve_PVar Heqs1.
  cbn* in *.
  simp.

  eutt_hide_right.
  repeat apply no_failure_Ret in NOFAIL.
  repeat (edestruct @no_failure_helix_LU as (? & NOFAIL' & ?); eauto; []; clear NOFAIL; rename NOFAIL' into NOFAIL; cbn in NOFAIL; eauto). 

  rauto:L.
  all:eauto.
  Ltac rewrite_nth_error :=
    match goal with
    | h: nth_error _ _ ≡ _ |- _ => rewrite h
    end.

  Ltac rewrite_memory_lookup :=
    match goal with
    | h: memory_lookup _ _ ≡ _ |- _ => rewrite h
    end.

  subst; eutt_hide_left.
  cbn in *.
  rewrite add_comment_eutt. subst.

  (* | DSHIMap n x_p y_p f => *)
  (*   '(x,i) <- resolve_PVar x_p ;; *)
  (*   '(y,o) <- resolve_PVar y_p ;; *)
  (*   loopcontblock <- incBlockNamed "IMap_lcont" ;; *)
  (*   loopvar <- incLocalNamed "IMap_i" ;; *)
  (*   '(body_entry, body_blocks) <- genIMapBody i o x y f loopvar loopcontblock ;; *)
  (*   add_comment *)
  (*     (genWhileLoop "IMap" (EXP_Integer 0%Z) (EXP_Integer (Z.of_nat n)) loopvar loopcontblock body_entry body_blocks [] nextblock) *)

  (*  TODO : use [genWhileLoop] *)

Admitted.
