From ITree Require Import
     ITree
     ITreeFacts
     Events.State
     Events.StateFacts
     InterpFacts
     Eq.Eq.

From Vellvm Require Import
     Util
     LLVMEvents
     PropT
     DynamicTypes
     CFG
     Memory
     Refinement
     Environment
     TopLevel
     LLVMAst
     Handlers.Intrinsics
     Handlers.Global
     Handlers.Local
     Handlers.Stack
     Handlers.UndefinedBehaviour.

From ExtLib Require Import
     Structures.Functor.

From Coq Require Import
     Strings.String
     Logic
     Morphisms
     Relations
     List.

Import ListNotations.
Import ITree.Basics.Basics.Monads.

Module R := Refinement.Make(Memory.A)(IO)(TopLevelEnv).
Import R.
Import TopLevelEnv.
Import IO.
Import IS.
Import M.


(**
   Partial interpretations of the trees produced by the
   denotation of cfg. They differ from the ones of Vellvm programs by
   their event signature, as well as by the lack of a stack of local event.
   The intent is to allow us to only interpret as many layers as needed
   to perform the required semantic reasoning, and lift for free the
   equivalence down the pipe.
   This gives us a _vertical_ notion of compositionality.
 *)

(**
   NOTE: Can we avoid this duplication w.r.t. [interp_to_Li]?
*)

Definition interp_cfg_to_L1 {R} user_intrinsics (t: itree instr_E R) (g: global_env) :=
  let L0_trace       := INT.interpret_intrinsics user_intrinsics t in
  let L1_trace       := runState (interp_global L0_trace) g in
  L1_trace.

Definition interp_cfg_to_L2 {R} user_intrinsics (t: itree instr_E R) (g: global_env) (l: local_env) :=
  let L0_trace       := INT.interpret_intrinsics user_intrinsics t in
  let L1_trace       := runState (interp_global L0_trace) g in
  let L2_trace       := runState (interp_local L1_trace) l in
  L2_trace.

Definition interp_cfg_to_L3 {R} user_intrinsics (t: itree instr_E R) (g: global_env) (l: local_env) (m: memory_stack) :=
  let L0_trace       := INT.interpret_intrinsics user_intrinsics t in
  let L1_trace       := runState (interp_global L0_trace) g in
  let L2_trace       := runState (interp_local L1_trace) l in
  let L3_trace       := runState (M.interp_memory L2_trace) m in
  L3_trace.

Definition interp_cfg_to_L4 {R} user_intrinsics (t: itree instr_E R) (g: global_env) (l: local_env) (m: memory_stack) :=
  let L0_trace       := INT.interpret_intrinsics user_intrinsics t in
  let L1_trace       := runState (interp_global L0_trace) g in
  let L2_trace       := runState (interp_local L1_trace) l in
  let L3_trace       := runState (M.interp_memory L2_trace) m in
  let L4_trace       := P.model_undef L3_trace in
  L4_trace.

Definition interp_cfg_to_L5 {R} user_intrinsics (t: itree instr_E R) (g: global_env) (l: local_env) (m: memory_stack) :=
  let L0_trace       := INT.interpret_intrinsics user_intrinsics t in
  let L1_trace       := runState (interp_global L0_trace) g in
  let L2_trace       := runState (interp_local L1_trace) l in
  let L3_trace       := runState (M.interp_memory L2_trace) m in
  let L4_trace       := P.model_undef L3_trace in
  UndefinedBehaviour.model_UB L4_trace.

From Vellvm Require Import TopLevelRefinements.

(* Specialization of [eutt_clo_bind] to the reccurent case of [UU := eq] to avoid having to provide the relation manually everytime *)
Lemma eutt_eq_bind : forall E R U (t: itree E U) (k1 k2: U -> itree E R), (forall u, k1 u ≈ k2 u) -> ITree.bind t k1 ≈ ITree.bind t k2.
Proof.
  intros.
  apply eutt_clo_bind with (UU := Logic.eq); [reflexivity |].
  intros ? ? ->; apply H.
Qed.

Lemma interp_cfg_to_L1_bind :
  forall ui {R S} (t: itree instr_E R) (k: R -> itree instr_E S) g, 
    interp_cfg_to_L1 ui (ITree.bind t k) g ≈
                 (ITree.bind (interp_cfg_to_L1 ui t g) (fun '(g',x) => interp_cfg_to_L1 ui (k x) g')).
Proof.
  intros.
  unfold interp_cfg_to_L1.
  rewrite INT.interp_intrinsics_bind, interp_global_bind.
  apply eutt_eq_bind; intros (? & ?); reflexivity.
Qed.

Lemma interp_cfg_to_L1_ret : forall ui (R : Type) g (x : R), interp_cfg_to_L1 ui (Ret x) g ≈ Ret (g,x).
Proof.
  intros; unfold interp_cfg_to_L1.
  rewrite INT.interp_intrinsics_ret, interp_global_ret; reflexivity.
Qed.

Lemma interp_cfg_to_L2_bind :
  forall ui {R S} (t: itree instr_E R) (k: R -> itree instr_E S) g l,
    interp_cfg_to_L2 ui (ITree.bind t k) g l ≈
                 (ITree.bind (interp_cfg_to_L2 ui t g l) (fun '(g',(l',x)) => interp_cfg_to_L2 ui (k x) l' g')).
Proof.
  intros.
  unfold interp_cfg_to_L2.
  rewrite INT.interp_intrinsics_bind, interp_global_bind, interp_local_bind.
  apply eutt_eq_bind; intros (? & ? & ?); reflexivity.
Qed.

Lemma interp_cfg_to_L2_ret : forall ui (R : Type) g l (x : R), interp_cfg_to_L2 ui (Ret x) g l ≈ Ret (l, (g, x)).
Proof.
  intros; unfold interp_cfg_to_L2.
  rewrite INT.interp_intrinsics_ret, interp_global_ret, interp_local_ret; reflexivity.
Qed.

Lemma interp_cfg_to_L3_bind :
  forall ui {R S} (t: itree instr_E R) (k: R -> itree instr_E S) g l m,
    interp_cfg_to_L3 ui (ITree.bind t k) g l m ≈
                 (ITree.bind (interp_cfg_to_L3 ui t g l m) (fun '(m',(l',(g',x))) => interp_cfg_to_L3 ui (k x) g' l' m')).
Proof.
  intros.
  unfold interp_cfg_to_L3.
  rewrite INT.interp_intrinsics_bind, interp_global_bind, interp_local_bind, interp_memory_bind.
  apply eutt_eq_bind; intros (? & ? & ? & ?); reflexivity.
Qed.

Lemma interp_cfg_to_L3_ret : forall ui (R : Type) g l m (x : R), interp_cfg_to_L3 ui (Ret x) g l m ≈ Ret (m, (l, (g,x))).
Proof.
  intros; unfold interp_cfg_to_L3.
  rewrite INT.interp_intrinsics_ret, interp_global_ret, interp_local_ret, interp_memory_ret; reflexivity.
Qed.

Import CatNotations.

Lemma denote_bks_nil: forall s, D.denote_bks [] s ≈ ret (inl s).
Proof.
  intros s; unfold D.denote_bks.
  unfold loop.
  cbn. rewrite bind_ret_l.
  match goal with
  | |- CategoryOps.iter (C := ktree _) ?body ?s ≈ _ =>
    rewrite (unfold_iter body s)
  end.
  repeat (cbn; (rewrite bind_bind || rewrite bind_ret_l)).
  reflexivity.
Qed.

Lemma normalize_types_block_bid :
  forall (env : list (ident * typ)) (b: LLVMAst.block typ),
    blk_id (TransformTypes.fmap_block _ _ (TypeUtil.normalize_type_dtyp env) b) = blk_id b.
Proof.
  intros env b.
  destruct b. reflexivity.
Qed.

Lemma normalize_types_block_term :
  forall (env : list (ident * typ)) (b: LLVMAst.block typ) (nextblock : block_id),
    snd (blk_term b) = TERM_Br_1 nextblock ->
    snd (blk_term (TransformTypes.fmap_block typ dtyp (TypeUtil.normalize_type_dtyp env) b)) = TERM_Br_1 nextblock.
Proof.
  intros env b nextblock Hterm.
  destruct b. cbn in *. rewrite Hterm.
  reflexivity.
Qed.


(* Instance eutt_interp_cfg_to_L3 (defs: intrinsic_definitions) {T}: *)
(*   Proper (eutt Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp_cfg_to_L3 T defs). *)
(* Proof. *)
(*   repeat intro. *)
(*   unfold interp_cfg_to_L3, Util.runState. *)
(*   subst; rewrite H. *)
(*   reflexivity. *)
(* Qed. *)


