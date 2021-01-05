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

Lemma mem_union_tfor : 
  forall i value x,
    Ret (mem_union (mem_const_block (MInt64asNT.to_nat i) value) x) ≈
        tfor (E := void1) (fun k x => Ret (mem_add k value x)) 0 (S (MInt64asNT.to_nat i)) x.
Proof.
Admitted.

Set Nested Proofs Allowed.
Lemma MemInit_Correct:
  ∀ (y_p : PExpr) (value : binary64) (s1 s2 : IRState) (σ : evalContext) 
    (memH : memoryH) (nextblock bid_in bid_from : block_id) (bks : list (LLVMAst.block typ)) 
    (g : global_env) (ρ : local_env) (memV : memoryV),
    genIR (DSHMemInit y_p value) nextblock s1 ≡ inr (s2, (bid_in, bks))
    → bid_bound s1 nextblock
    → state_invariant σ s1 memH (memV, (ρ, g))
    → Gamma_safe σ s1 s2
    → no_failure (E := E_cfg) (interp_helix (denoteDSHOperator σ (DSHMemInit y_p value)) memH)
    → eutt (succ_cfg (genIR_post σ s1 s2 nextblock ρ))
           (interp_helix (denoteDSHOperator σ (DSHMemInit y_p value)) memH)
           (interp_cfg (denote_ocfg (convert_typ [] bks) (bid_from, bid_in)) g ρ memV).
Proof.
  intros y_p value s1 s2 σ memH nextblock bid_in bid_from bks g ρ memV GEN NEXT PRE GAM NOFAIL.
  cbn in *.
  unfold denotePExpr in *.
  cbn* in *; simp.
  try_abs.
  hred.
  apply no_failure_Ret in NOFAIL.
  edestruct @no_failure_helix_LU as (? & NOFAIL' & ?); eauto; []; clear NOFAIL; rename NOFAIL' into NOFAIL; cbn in NOFAIL; eauto.
  hstep; eauto.
  hred.
  rename x into mem_bkH.

  (* (* Should mem_bkH be empty? *) *)

   

  (* (* Memory.NM.map2 *) *)


  (* rewrite DSHPower_as_tfor; cbn. *)
  (* inv_resolve_PVar Heqs0. *)
  (* inv_resolve_PVar Heqs1. *)
  (* unfold denotePExpr in *. *)
  (* cbn* in *. *)
  (* destruct u. *)
  (* simp; try_abs. *)
  (* repeat apply no_failure_Ret in NOFAIL. *)
  (* do 2 (apply no_failure_helix_LU in NOFAIL; destruct NOFAIL as (? & NOFAIL & ?); cbn in NOFAIL). *)

  (* (* Symbolically reducing the concrete prefix on the Helix side *) *)
  (* hred. *)
  (* hstep; [eassumption |]. *)
  (* hred; hstep; [eassumption |]. *)
  (* hred. *)

  (* Symbolically reducing the concrete prefix on the VIR side *)

Admitted.
