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

Require Import Ceres.Ceres.

Import ListNotations.
Import ITree.Basics.Basics.Monads.

Module R := Refinement.Make(Memory.A)(IO)(TopLevelEnv).
Import R.
Import TopLevelEnv.
Import IO.
Import IS.
Import M.
Import Integers.
Import BinInt.
Import INT.

Section Translations.

  (** TODOYZ : MOVE ITree *)
  Lemma translate_trigger {E F G} `{E -< F} :
    forall X (e: E X) (h: F ~> G),
     translate h (trigger e) ≈ trigger (h _ (subevent X e)).
  Proof.
    intros; unfold trigger; rewrite translate_vis; setoid_rewrite translate_ret; reflexivity.
  Qed.

  (** TODOYZ : MOVE (Vellvm)  *)
  (* Technicality: translations by [lookup_E_to_exp_E] and [exp_E_to_instr_E] leave these events unphased *)
  Lemma lookup_E_to_exp_E_Global : forall {X} (e : LLVMGEnvE X),
      lookup_E_to_exp_E (subevent X e) = subevent X e.
  Proof.
    reflexivity.
  Qed.

  Lemma exp_E_to_instr_E_Global : forall {X} (e : LLVMGEnvE X),
      exp_E_to_instr_E (subevent X e) = subevent X e.
  Proof.
    reflexivity.
  Qed.

  Lemma lookup_E_to_exp_E_Local : forall {X} (e : LLVMEnvE X),
      lookup_E_to_exp_E (subevent X e) = subevent X e.
  Proof.
    reflexivity.
  Qed.

  Lemma exp_E_to_instr_E_Local : forall {X} (e : LLVMEnvE X),
      exp_E_to_instr_E (subevent X e) = subevent X e.
  Proof.
    reflexivity.
  Qed.

End Translations.

Section InterpreterCFG.

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
  let L0_trace       := interp_intrinsics user_intrinsics t in
  let L1_trace       := interp_global L0_trace g in
  L1_trace.

Definition interp_cfg_to_L2 {R} user_intrinsics (t: itree instr_E R) (g: global_env) (l: local_env) :=
  let L0_trace       := interp_intrinsics user_intrinsics t in
  let L1_trace       := interp_global L0_trace g in
  let L2_trace       := interp_local L1_trace l in
  L2_trace.

Definition interp_cfg_to_L3 {R} user_intrinsics (t: itree instr_E R) (g: global_env) (l: local_env) (m: memory_stack) :=
  let L0_trace       := interp_intrinsics user_intrinsics t in
  let L1_trace       := interp_global L0_trace g in
  let L2_trace       := interp_local L1_trace l in
  let L3_trace       := M.interp_memory L2_trace m in
  L3_trace.

Definition interp_cfg_to_L4 {R} user_intrinsics (t: itree instr_E R) (g: global_env) (l: local_env) (m: memory_stack) :=
  let L0_trace       := interp_intrinsics user_intrinsics t in
  let L1_trace       := interp_global L0_trace g in
  let L2_trace       := interp_local L1_trace l in
  let L3_trace       := M.interp_memory L2_trace m in
  let L4_trace       := P.model_undef L3_trace in
  L4_trace.

Definition interp_cfg_to_L5 {R} user_intrinsics (t: itree instr_E R) (g: global_env) (l: local_env) (m: memory_stack) :=
  let L0_trace       := interp_intrinsics user_intrinsics t in
  let L1_trace       := interp_global L0_trace g in
  let L2_trace       := interp_local L1_trace l in
  let L3_trace       := M.interp_memory L2_trace m in
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
  rewrite interp_intrinsics_bind, interp_global_bind.
  apply eutt_eq_bind; intros (? & ?); reflexivity.
Qed.

Lemma interp_cfg_to_L1_ret : forall ui (R : Type) g (x : R), interp_cfg_to_L1 ui (Ret x) g ≈ Ret (g,x).
Proof.
  intros; unfold interp_cfg_to_L1.
  rewrite interp_intrinsics_ret, interp_global_ret; reflexivity.
Qed.

Lemma interp_cfg_to_L2_bind :
  forall ui {R S} (t: itree instr_E R) (k: R -> itree instr_E S) g l,
    interp_cfg_to_L2 ui (ITree.bind t k) g l ≈
                 (ITree.bind (interp_cfg_to_L2 ui t g l) (fun '(g',(l',x)) => interp_cfg_to_L2 ui (k x) l' g')).
Proof.
  intros.
  unfold interp_cfg_to_L2.
  rewrite interp_intrinsics_bind, interp_global_bind, interp_local_bind.
  apply eutt_eq_bind; intros (? & ? & ?); reflexivity.
Qed.

Lemma interp_cfg_to_L2_ret : forall ui (R : Type) g l (x : R), interp_cfg_to_L2 ui (Ret x) g l ≈ Ret (l, (g, x)).
Proof.
  intros; unfold interp_cfg_to_L2.
  rewrite interp_intrinsics_ret, interp_global_ret, interp_local_ret; reflexivity.
Qed.

Lemma interp_cfg_to_L3_bind :
  forall ui {R S} (t: itree instr_E R) (k: R -> itree instr_E S) g l m,
    interp_cfg_to_L3 ui (ITree.bind t k) g l m ≈
                 (ITree.bind (interp_cfg_to_L3 ui t g l m) (fun '(m',(l',(g',x))) => interp_cfg_to_L3 ui (k x) g' l' m')).
Proof.
  intros.
  unfold interp_cfg_to_L3.
  rewrite interp_intrinsics_bind, interp_global_bind, interp_local_bind, interp_memory_bind.
  apply eutt_eq_bind; intros (? & ? & ? & ?); reflexivity.
Qed.

Lemma interp_cfg_to_L3_ret : forall ui (R : Type) g l m (x : R), interp_cfg_to_L3 ui (Ret x) g l m ≈ Ret (m, (l, (g,x))).
Proof.
  intros; unfold interp_cfg_to_L3.
  rewrite interp_intrinsics_ret, interp_global_ret, interp_local_ret, interp_memory_ret; reflexivity.
Qed.

Global Instance eutt_interp_cfg_to_L1 (defs: intrinsic_definitions) {T}:
  Proper (eutt Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp_cfg_to_L1 T defs).
Proof.
  repeat intro.
  unfold interp_cfg_to_L1.
  subst; rewrite H.
  reflexivity.
Qed.

Global Instance eutt_interp_cfg_to_L2 (defs: intrinsic_definitions) {T}:
  Proper (eutt Logic.eq ==> Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp_cfg_to_L2 T defs).
Proof.
  repeat intro.
  unfold interp_cfg_to_L2.
  subst; rewrite H.
  reflexivity.
Qed.


Global Instance eutt_interp_cfg_to_L3 (defs: intrinsic_definitions) {T}:
  Proper (eutt Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp_cfg_to_L3 T defs).
Proof.
  repeat intro.
  unfold interp_cfg_to_L3.
  subst; rewrite H.
  reflexivity.
Qed.

(**
   The whole family. More than we need, but at least we'll have what we need.
 *)

  Lemma interp_global_vis_eqit:
    forall (k v map : Type) (M : Maps.Map k v map) (SK : Serialize k) (E F G : Type -> Type)
      (H0 : FailureE -< G) (g : map) S X
      (kk : X -> itree (E +' F +' GlobalE k v +' G) S)
      (e : (E +' F +' GlobalE k v +' G) X),
      interp_global (Vis e kk) g ≅ ITree.bind (interp_global_h e g) (fun (sx : map * X) => Tau (interp_global (kk (snd sx)) (fst sx))).
  Proof.
    intros.
    unfold interp_global.
    setoid_rewrite interp_state_vis.
    reflexivity.
  Qed.

  Lemma interp_global_vis:
    forall (k v map : Type) (M : Maps.Map k v map) (SK : Serialize k) (E F G : Type -> Type)
      (H0 : FailureE -< G) (g : map) S X
      (kk : X -> itree (E +' F +' GlobalE k v +' G) S)
      (e : (E +' F +' GlobalE k v +' G) X),
      interp_global (Vis e kk) g ≈ ITree.bind (interp_global_h e g) (fun (sx : map * X) => interp_global (kk (snd sx)) (fst sx)).
  Proof.
    intros.
    rewrite interp_global_vis_eqit.
    apply eutt_eq_bind.
    intros ?; tau_steps; reflexivity.
  Qed.

  (** TODOYZ : Send this to StateFacts *)
  (** TODOYZ : Define a tactic for this recurrent [bind_ret_r] trick *)
  Lemma interp_state_trigger' {E F : Type -> Type} {R S : Type}
        (e : E R) (f : E ~> Monads.stateT S (itree F)) (s : S)
    : interp_state f (ITree.trigger e) s ≈ f _ e s.
  Proof.
    unfold ITree.trigger. rewrite interp_state_vis.
    match goal with
      |- _ ≈ ?x => rewrite <- (bind_ret_r x) at 2
    end.
    eapply eqit_bind; try reflexivity.
    intros []; rewrite interp_state_ret,tau_eutt.
    reflexivity.
  Qed.

  Lemma interp_global_trigger:
    forall (k v map : Type) (M : Maps.Map k v map) (SK : Serialize k) (E F G : Type -> Type)
      (H0 : FailureE -< G) (g : map) X
      (e : (E +' F +' GlobalE k v +' G) X),
      interp_global (ITree.trigger e) g ≈ interp_global_h e g.
  Proof.
    intros.
    unfold interp_global.
    rewrite interp_state_trigger'.
    reflexivity.
  Qed.

  Lemma interp_global_bind_trigger_eqit:
    forall (k v map : Type) (M : Maps.Map k v map) (SK : Serialize k) (E F G : Type -> Type)
      (H0 : FailureE -< G) (g : map) S X
      (kk : X -> itree (E +' F +' GlobalE k v +' G) S)
      (e : (E +' F +' GlobalE k v +' G) X),
      interp_global (ITree.bind (trigger e) kk) g ≅ ITree.bind (interp_global_h e g) (fun (sx : map * X) => Tau (interp_global (kk (snd sx)) (fst sx))).
  Proof.
    intros.
    unfold interp_global.
    rewrite bind_trigger.
    setoid_rewrite interp_state_vis.
    reflexivity.
  Qed.

  Lemma interp_global_bind_trigger:
    forall (k v map : Type) (M : Maps.Map k v map) (SK : Serialize k) (E F G : Type -> Type)
      (H0 : FailureE -< G) (g : map) S X
      (kk : X -> itree (E +' F +' GlobalE k v +' G) S)
      (e : (E +' F +' GlobalE k v +' G) X),
      interp_global (ITree.bind (trigger e) kk) g ≈ ITree.bind (interp_global_h e g) (fun (sx : map * X) => interp_global (kk (snd sx)) (fst sx)).
  Proof.
    intros.
    rewrite interp_global_bind_trigger_eqit.
    apply eutt_eq_bind.
    intros ?; tau_steps; reflexivity.
  Qed.

  Lemma interp_local_vis_eqit:
    forall (k v map : Type) (M : Maps.Map k v map) (SK : Serialize k) (E F G : Type -> Type)
      (H0 : FailureE -< G) (g : map) S X
      (kk : X -> itree (E +' F +' LocalE k v +' G) S)
      (e : (E +' F +' LocalE k v +' G) X),
      interp_local (Vis e kk) g ≅ ITree.bind (interp_local_h e g) (fun (sx : map * X) => Tau (interp_local (kk (snd sx)) (fst sx))).
  Proof.
    intros.
    unfold interp_local.
    setoid_rewrite interp_state_vis.
    reflexivity.
  Qed.

  Lemma interp_local_vis:
    forall (k v map : Type) (M : Maps.Map k v map) (SK : Serialize k) (E F G : Type -> Type)
      (H0 : FailureE -< G) (g : map) S X
      (kk : X -> itree (E +' F +' LocalE k v +' G) S)
      (e : (E +' F +' LocalE k v +' G) X),
      interp_local (Vis e kk) g ≈ ITree.bind (interp_local_h e g) (fun (sx : map * X) => interp_local (kk (snd sx)) (fst sx)).
  Proof.
    intros.
    rewrite interp_local_vis_eqit.
    apply eutt_eq_bind.
    intros ?; tau_steps; reflexivity.
  Qed.

  Lemma interp_local_trigger:
    forall (k v map : Type) (M : Maps.Map k v map) (SK : Serialize k) (E F G : Type -> Type)
      (H0 : FailureE -< G) (g : map) X
      (e : (E +' F +' LocalE k v +' G) X),
      interp_local (ITree.trigger e) g ≈ interp_local_h e g.
  Proof.
    intros.
    unfold interp_local.
    rewrite interp_state_trigger'.
    reflexivity.
  Qed.

  Lemma interp_local_bind_trigger_eqit:
    forall (k v map : Type) (M : Maps.Map k v map) (SK : Serialize k) (E F G : Type -> Type)
      (H0 : FailureE -< G) (g : map) S X
      (kk : X -> itree (E +' F +' LocalE k v +' G) S)
      (e : (E +' F +' LocalE k v +' G) X),
      interp_local (ITree.bind (trigger e) kk) g ≅ ITree.bind (interp_local_h e g) (fun (sx : map * X) => Tau (interp_local (kk (snd sx)) (fst sx))).
  Proof.
    intros.
    unfold interp_local.
    rewrite bind_trigger.
    setoid_rewrite interp_state_vis.
    reflexivity.
  Qed.

  Lemma interp_local_trigger_bind:
    forall (k v map : Type) (M : Maps.Map k v map) (SK : Serialize k) (E F G : Type -> Type)
      (H0 : FailureE -< G) (g : map) S X
      (kk : X -> itree (E +' F +' LocalE k v +' G) S)
      (e : (E +' F +' LocalE k v +' G) X),
      interp_local (ITree.bind (trigger e) kk) g ≈ ITree.bind (interp_local_h e g) (fun (sx : map * X) => interp_local (kk (snd sx)) (fst sx)).
  Proof.
    intros.
    rewrite interp_local_bind_trigger_eqit.
    apply eutt_eq_bind.
    intros ?; tau_steps; reflexivity.
  Qed.

  Lemma interp_intrinsics_vis_eqit:
    forall E F X R (HF : FailureE -< F) (e : (E +' IntrinsicE +' F) X)
      (kk : X -> itree (E +' IntrinsicE +' F) R) defs,
      interp_intrinsics defs (Vis e kk) ≅
      ITree.bind (interp_intrinsics_h defs e) (fun x : X => Tau (interp (INT.interp_intrinsics_h defs) (kk x))).
  Proof.
    intros.
    unfold interp_intrinsics.
    rewrite interp_vis.
    reflexivity.
  Qed.

  Lemma interp_intrinsics_vis:
    forall E F X R (HF : FailureE -< F) (e : (E +' IntrinsicE +' F) X)
      (kk : X -> itree (E +' IntrinsicE +' F) R) defs,
      interp_intrinsics defs (Vis e kk) ≈
      ITree.bind (interp_intrinsics_h defs e) (fun x : X => interp (INT.interp_intrinsics_h defs) (kk x)).
  Proof.
    intros.
    rewrite interp_intrinsics_vis_eqit.
    apply eutt_eq_bind.
    intros ?; tau_steps; reflexivity.
  Qed.

  Lemma interp_intrinsics_trigger:
    forall E F X (HF : FailureE -< F) (e : (E +' IntrinsicE +' F) X) defs,
      interp_intrinsics defs (ITree.trigger e) ≈ interp_intrinsics_h defs e.
  Proof.
    intros *.
    unfold interp_intrinsics.
    rewrite interp_trigger.
    reflexivity.
  Qed.

  Lemma interp_intrinsics_bind_trigger_eqit:
    forall E F X R (HF : FailureE -< F) (e : (E +' IntrinsicE +' F) X)
      (kk : X -> itree (E +' IntrinsicE +' F) R) defs,
      interp_intrinsics defs (ITree.bind (trigger e) kk) ≅
      ITree.bind (interp_intrinsics_h defs e) (fun x : X => Tau (interp (INT.interp_intrinsics_h defs) (kk x))).
  Proof.
    intros E F X R HF e kk h.
    unfold interp_intrinsics.
    rewrite bind_trigger.
    rewrite interp_vis.
    reflexivity.
  Qed.

  Lemma interp_intrinsics_bind_trigger:
    forall E F X R (HF : FailureE -< F) (e : (E +' IntrinsicE +' F) X)
      (kk : X -> itree (E +' IntrinsicE +' F) R) defs,
      interp_intrinsics defs (ITree.bind (trigger e) kk) ≈
      ITree.bind (interp_intrinsics_h defs e) (fun x : X => interp (INT.interp_intrinsics_h defs) (kk x)).
  Proof.
    intros.
    rewrite interp_intrinsics_bind_trigger_eqit.
    apply eutt_eq_bind.
    intros ?; tau_steps; reflexivity.
  Qed.

  (* NOTEYZ: This can probably be refined to [eqit eq] instead of [eutt eq], but I don't think it matters to us *)
  Lemma interp_cfg_to_L3_vis (defs: IS.intrinsic_definitions):
    forall T R (e : instr_E T) (k : T -> itree instr_E R) g l m,
      interp_cfg_to_L3 defs (Vis e k) g l m ≈ 
                       ITree.bind (interp_cfg_to_L3 defs (trigger e) g l m)
                       (fun '(m, (l, (g, x)))=> interp_cfg_to_L3 defs (k x) g l m).
  Proof.
    intros.
    unfold interp_cfg_to_L3.
    rewrite interp_intrinsics_vis.
    rewrite interp_global_bind, interp_local_bind, interp_memory_bind.
    unfold trigger; rewrite interp_intrinsics_vis.
    rewrite interp_global_bind, interp_local_bind, interp_memory_bind.
    rewrite Eq.bind_bind.
    apply eutt_eq_bind.
    intros (? & ? & ? & ?).
    do 2 match goal with
      |- context[interp ?x ?t] => replace (interp x t) with (interp_intrinsics defs t) by reflexivity
    end. 
    rewrite interp_intrinsics_ret, interp_global_ret, interp_local_ret, interp_memory_ret, bind_ret_l.
    reflexivity.
  Qed.

  Lemma interp_cfg_to_L3_bind_trigger (defs: IS.intrinsic_definitions):
    forall T R (e : instr_E T) (k : T -> itree instr_E R) g l m,
      interp_cfg_to_L3 defs (ITree.bind (trigger e) k) g l m ≈ 
                       ITree.bind (interp_cfg_to_L3 defs (trigger e) g l m)
                       (fun '(m, (l, (g, x)))=> interp_cfg_to_L3 defs (k x) g l m).
  Proof.
    intros.
    rewrite bind_trigger.
    rewrite interp_cfg_to_L3_vis at 1.
    reflexivity.
  Qed.

  Lemma interp_cfg_to_L3_GR : forall defs id g l m v,
      Maps.lookup id g = Some v ->
      interp_cfg_to_L3 defs (trigger (GlobalRead id)) g l m ≈ ret (m,(l,(g,v))).
  Proof.
    intros * LU.
    unfold interp_cfg_to_L3.
    rewrite interp_intrinsics_trigger.
    cbn.
    unfold INT.F_trigger.
    rewrite interp_global_trigger.
    cbn in *; rewrite LU.
    rewrite interp_local_ret, interp_memory_ret.
    reflexivity.
  Qed.

  Lemma interp_cfg_to_L3_LR : forall defs id g l m v,
      Maps.lookup id l = Some v ->
      interp_cfg_to_L3 defs (trigger (LocalRead id)) g l m ≈ ret (m,(l,(g,v))).
  Proof.
    intros * LU.
    unfold interp_cfg_to_L3.
    rewrite interp_intrinsics_trigger.
    cbn.
    unfold INT.F_trigger.
    rewrite interp_global_trigger.
    cbn.
    rewrite interp_local_bind, interp_local_trigger.
    cbn in *; rewrite LU.
    rewrite bind_ret_l, interp_local_ret, interp_memory_ret.
    reflexivity.
  Qed.

End InterpreterCFG.

Section Denotation.
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

  From Vellvm Require Import Util.
  Require Import State.

(* TODOYZ: This is weird, I need to import again this file for the rewriting to work.
   A bit unsure as to why this happen, but somehow some subsequent import breaks it.
 *)
Require Import ITree.Eq.Eq.

Lemma denote_bks_singleton :
  forall (b : LLVMAst.block dtyp) (bid : block_id) (nextblock : block_id),
    blk_id b = bid ->
    (snd (blk_term b)) = (TERM_Br_1 nextblock) ->
    (blk_id b) <> nextblock ->
    eutt (Logic.eq) (D.denote_bks [b] bid) (D.denote_block b).
Proof.
  intros b bid nextblock Heqid Heqterm Hneq.
  cbn.
  rewrite bind_ret_l.
  rewrite KTreeFacts.unfold_iter_ktree.
  cbn.
  destruct (Eqv.eqv_dec_p (blk_id b) bid) eqn:Heq'; try contradiction.
  repeat rewrite bind_bind.
  rewrite Heqterm.
  cbn.
  setoid_rewrite translate_ret.
  setoid_rewrite bind_ret_l.
  destruct (Eqv.eqv_dec_p (blk_id b) nextblock); try contradiction.
  repeat setoid_rewrite bind_ret_l. unfold Datatypes.id.
  reflexivity.
Qed.

Lemma denote_code_app :
  forall a b,
    D.denote_code (a ++ b)%list ≈ ITree.bind (D.denote_code a) (fun _ => D.denote_code b).
Proof.
  induction a; intros b.
  - cbn. rewrite bind_ret_l.
    reflexivity.
  - cbn. rewrite bind_bind. setoid_rewrite IHa.
    reflexivity.
Qed.

Lemma denote_code_cons :
  forall a l,
    D.denote_code (a::l) ≈ ITree.bind (D.denote_instr a) (fun _ => D.denote_code l).
Proof.
  cbn; reflexivity.
Qed.

End Denotation.

(** 
Section NormalizeTypes.

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

Definition normalize_types_blocks (env: list _) (bks: list (LLVMAst.block typ))
  : list (LLVMAst.block DynamicTypes.dtyp) :=
  List.map
    (TransformTypes.fmap_block _ _ (TypeUtil.normalize_type_dtyp env)) bks.

(* NOTEYZ: [TypeUtil.normalize_type_dtyp] seems unusable as is.
   Need to look into it.
 *)
  Lemma normalize_IntType :
    forall env,
      TypeUtil.normalize_type_dtyp env (TYPE_I 64%Z) = DTYPE_I 64.
  Proof.
  Admitted.

End NormalizeTypes.
**)

Section MemoryModel.

  Definition get_logical_block (mem: M.memory) (ptr: A.addr): option M.logical_block :=
    let '(b,a) := ptr in
    M.lookup_logical b mem.

End MemoryModel.

Section Integers.

  (* NOTEYZ: I doubt that the following is true, unless proof irrelevance is assumed *)
  Lemma repr_intval (i: int64):
    DynamicValues.Int64.repr (Int64.intval i) = i.
  Proof.
  Admitted.

End Integers.

Section ValuePred.

  (* TODOYZ: Double check how useful those are *)
  Definition int64_dvalue_rel (n : Int64.int) (dv : dvalue) : Prop :=
    match dv with
    | DVALUE_I64 i => BinInt.Z.eq (Int64.intval n) (unsigned i)
    | _ => False
    end.

  Definition nat_dvalue_rel (n : nat) (dv : dvalue) : Prop :=
    match dv with
    | DVALUE_I64 i => Z.eq (Z.of_nat n) (unsigned i)
    | _ => False
    end.

  Definition int64_concrete_uvalue_rel (n : Int64.int) (uv : uvalue) : Prop :=
    match uvalue_to_dvalue uv with
    | inr dv => int64_dvalue_rel n dv
    | _ => False
    end.

  Definition nat_concrete_uvalue_rel (n : nat) (uv : uvalue) : Prop :=
    match uvalue_to_dvalue uv with
    | inr dv => nat_dvalue_rel n dv
    | _ => False
    end.

End ValuePred.

(** ** Event elimination
    This is a pure [itree] feature.

    We want to be able to express that a computation does not contain a particular event,
    and eliminate it safely from the signature if that is so.
 *)
From Paco Require Import paco.
Section ElimEvent.

  (* Since we cannot test equality of event, I rely on the exact order for now.
     As usual, the generalization of subevent may help with that?
   *)

  Definition helim_l {E F}: E +' F ~> itree F :=
    fun _ e => match e with
            | inl1 _ => ITree.spin
            | inr1 e => trigger e
            end.

  Definition helim_r {E F}: E +' F ~> itree E :=
    fun _ e => match e with
            | inr1 _ => ITree.spin
            | inl1 e => trigger e
            end.

  Definition elim_l {E F}: itree (E +' F) ~> itree F := interp helim_l. 
  Definition elim_r {E F}: itree (E +' F) ~> itree E := interp helim_r. 

  Variant no_left_eventF {E F X} (R: itree (E +' F) X -> Prop): itree (E +' F) X -> Prop :=
  | no_left_event_ret: forall (x: X), no_left_eventF R (ret x)
  | no_left_event_tau: forall t, R t -> no_left_eventF R (Tau t)
  | no_left_event_vis: forall {Y} (e: F Y) k, (forall x, R (k x)) -> no_left_eventF R (Vis (inr1 e) k).

  Definition no_left_event {E F X} := paco1 (@no_left_eventF E F X) bot1. 

  (* Lemma safe_helim_l: *)
  (*   forall {E F X} (t: itree (E +' F) X) (NOL: no_left_event t) (h: E ~> itree F), *)
  (*     elim_l _ t ≈  interp (case_ h ((fun _ e => trigger e): Handler F F)) t. *)

End ElimEvent.
