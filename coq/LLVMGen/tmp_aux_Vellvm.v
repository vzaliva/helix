From ITree Require Import
     ITree
     ITreeFacts
     Events.State
     Events.StateFacts
     InterpFacts
     Eq.Eq.

From Vellvm Require Import
     Util
     AstLib
     LLVMEvents
     DynamicTypes
     CFG
     Handlers.Memory
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

From Vellvm Require Import TopLevelRefinements.

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

  (**
     TODO YZ: Can we expose better than this? It's super low level
   *)
  Lemma interp_cfg_to_L3_LM : forall defs t a size offset g l m v bytes concrete_id,
      lookup_logical a (fst m) = Some (LBlock size bytes concrete_id) ->
      deserialize_sbytes (lookup_all_index offset (sizeof_dtyp t) bytes SUndef) t = v ->
      interp_cfg_to_L3 defs (trigger (Load t (DVALUE_Addr (a, offset)))) g l m ≈ Ret (m,(l,(g,v))).
  Proof.
    intros * LUL EQ.
    unfold interp_cfg_to_L3.
    rewrite interp_intrinsics_trigger.
    cbn.
    unfold INT.F_trigger.
    rewrite interp_global_trigger.
    cbn.
    rewrite interp_local_bind, interp_local_trigger.
    cbn; rewrite bind_bind.
    rewrite interp_memory_bind, interp_memory_trigger.
    cbn.
    destruct m as [mem memstack]. cbn.
    cbn in LUL; rewrite LUL.
    rewrite 2 bind_ret_l, interp_local_ret, interp_memory_ret.
    rewrite EQ.
    reflexivity.
  Qed.

End InterpreterCFG.

Section InterpreterMCFG.

  Lemma interp_to_L3_bind :
    forall ui {R S} (t: itree L0 R) (k: R -> itree L0 S) g l m,
      interp_to_L3 ui (ITree.bind t k) g l m ≈
                   (ITree.bind (interp_to_L3 ui t g l m) (fun '(m',(l',(g',x))) => interp_to_L3 ui (k x) g' l' m')).
  Proof.
    intros.
    unfold interp_to_L3.
    rewrite interp_intrinsics_bind, interp_global_bind, interp_local_stack_bind, interp_memory_bind.
    apply eutt_eq_bind; intros (? & ? & ? & ?); reflexivity.
  Qed.

  Lemma interp_to_L3_ret : forall ui (R : Type) g l m (x : R), interp_to_L3 ui (Ret x) g l m ≈ Ret (m, (l, (g,x))).
  Proof.
    intros; unfold interp_to_L3.
    rewrite interp_intrinsics_ret, interp_global_ret, interp_local_stack_ret, interp_memory_ret; reflexivity.
  Qed.

End  InterpreterMCFG.

From Vellvm Require Import Util.
Require Import State.

(* TODOYZ: This is weird, I need to import again this file for the rewriting to work.
   A bit unsure as to why this happen, but somehow some subsequent import breaks it.
 *)
Require Import ITree.Eq.Eq.

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

(* I want an Ltac library for Vellvm. Here are a few first elementary pieces *)
(* TODO YZ : do it right, learn Ltac(2) *)

Ltac flatten_goal :=
  match goal with
  | |- context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

Ltac flatten_hyp h :=
  match type of h with
  | context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

Ltac flatten_all :=
  match goal with
  | h: context[match ?x with | _ => _ end] |- _ => let Heq := fresh "Heq" in destruct x eqn:Heq
  | |- context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

Ltac inv H := inversion H; try subst; clear H.

Global Tactic Notation "intros !" := repeat intro.

(* inv by name of the Inductive relation *)
Ltac invn f :=
    match goal with
    | [ id: f |- _ ] => inv id
    | [ id: f _ |- _ ] => inv id
    | [ id: f _ _ |- _ ] => inv id
    | [ id: f _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ |- _ ] => inv id
    end.

(* destruct by name of the Inductive relation *)
Ltac destructn f :=
    match goal with
    | [ id: f |- _ ] => destruct id
    | [ id: f _ |- _ ] => destruct id
    | [ id: f _ _ |- _ ] => destruct id
    | [ id: f _ _ _ |- _ ] => destruct id
    | [ id: f _ _ _ _ |- _ ] => destruct id
    | [ id: f _ _ _ _ _ |- _ ] => destruct id
    | [ id: f _ _ _ _ _ _ |- _ ] => destruct id
    | [ id: f _ _ _ _ _ _ _ |- _ ] => destruct id
    | [ id: f _ _ _ _ _ _ _ _ |- _ ] => destruct id
    end.

(* apply by name of the Inductive relation *)
Ltac appn f :=
    match goal with
    | [ id: f |- _ ] => apply id
    | [ id: f _ |- _ ] => apply id
    | [ id: f _ _ |- _ ] => apply id
    | [ id: f _ _ _ |- _ ] => apply id
    | [ id: f _ _ _ _ |- _ ] => apply id
    | [ id: f _ _ _ _ _ |- _ ] => apply id
    | [ id: f _ _ _ _ _ _ |- _ ] => apply id
    | [ id: f _ _ _ _ _ _ _ |- _ ] => apply id
    | [ id: f _ _ _ _ _ _ _ _ |- _ ] => apply id
    end.

(* eapply by name of the Inductive relation *)
Ltac eappn f :=
    match goal with
    | [ id: f |- _ ] => eapply id
    | [ id: f _ |- _ ] => eapply id
    | [ id: f _ _ |- _ ] => eapply id
    | [ id: f _ _ _ |- _ ] => eapply id
    | [ id: f _ _ _ _ |- _ ] => eapply id
    | [ id: f _ _ _ _ _ |- _ ] => eapply id
    | [ id: f _ _ _ _ _ _ |- _ ] => eapply id
    | [ id: f _ _ _ _ _ _ _ |- _ ] => eapply id
    | [ id: f _ _ _ _ _ _ _ _ |- _ ] => eapply id
    end.

(** [break_match_hyp] looks for a [match] construct in some
    hypothesis, and destructs the discriminee, while retaining the
    information about the discriminee's value leading to the branch
    being taken. *)
Ltac break_match_hyp :=
  match goal with
    | [ H : context [ match ?X with _ => _ end ] |- _] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

(** [break_match_goal] looks for a [match] construct in your goal, and
    destructs the discriminee, while retaining the information about
    the discriminee's value leading to the branch being taken. *)
Ltac break_match_goal :=
  match goal with
    | [ |- context [ match ?X with _ => _ end ] ] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

(** [break_match] breaks a match, either in a hypothesis or in your
    goal. *)
Ltac break_match := break_match_goal || break_match_hyp.

Ltac inv_option :=
  match goal with
  | h: Some _ = Some _ |-  _ => inv h
  | h: None   = Some _ |-  _ => inv h
  | h: Some _ = None   |-  _ => inv h
  | h: None   = None   |-  _ => inv h
  end.

Ltac inv_sum :=
  match goal with
  | h: inl _ = inl _ |-  _ => inv h
  | h: inr _ = inr _ |-  _ => inv h
  | h: inl _ = inr _ |-  _ => inv h
  | h: inr _ = inl _ |-  _ => inv h
  end.

Section TLE_To_Modul.

  Definition opt_first {T: Type} (o1 o2: option T): option T :=
    match o1 with | Some x => Some x | None => o2 end.

  Definition modul_app {T X} (m1 m2: modul T X): modul T X :=
    let (name1, target1, layout1, tdefs1, globs1, decls1, defs1) := m1 in
    let (name2, target2, layout2, tdefs2, globs2, decls2, defs2) := m2 in
    {|
      m_name := opt_first name1 name2;
      m_target := opt_first target1 target2;
      m_datalayout := opt_first layout1 layout2;
      m_type_defs := tdefs1 ++ tdefs2;
      m_globals := globs1 ++ globs2;
      m_declarations := decls1 ++ decls2;
      m_definitions := defs1 ++ defs2
    |}.

  Lemma modul_of_toplevel_entities_cons:
    forall {T X} tle tles, 
      @modul_of_toplevel_entities T X (tle :: tles) = modul_app (modul_of_toplevel_entities T [tle]) (modul_of_toplevel_entities T tles).
  Proof.
    intros.
    unfold modul_of_toplevel_entities; cbn; f_equal;
      try ((break_match_goal; reflexivity) || (rewrite <- !app_nil_end; reflexivity)).
  Qed.

  Lemma modul_of_toplevel_entities_app:
    forall {T X} tle1 tle2, 
    @modul_of_toplevel_entities T X (tle1 ++ tle2) = modul_app (modul_of_toplevel_entities T tle1) (modul_of_toplevel_entities T tle2).
  Proof.
    induction tle1 as [| tle tle1 IH]; intros; cbn; [reflexivity |].
    rewrite modul_of_toplevel_entities_cons, IH; cbn.
    f_equal;
      try ((break_match_goal; reflexivity) || (rewrite <- !app_nil_end, app_assoc; reflexivity)).
  Qed.

  Infix "@" := (modul_app) (at level 60).

  Open Scope list.
  Lemma m_definitions_app: forall {T X} (p1 p2 : modul T X),
      m_definitions (p1 @ p2) = m_definitions p1 ++ m_definitions p2.
  Proof.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma m_name_app: forall {T X} (p1 p2 : modul T X),
      m_name (p1 @ p2) = opt_first (m_name p1) (m_name p2).
  Proof.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma m_target_app: forall {T X} (p1 p2 : modul T X),
      m_target (p1 @ p2) = opt_first (m_target p1) (m_target p2).
  Proof.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma m_datalayout_app: forall {T X} (p1 p2 : modul T X),
      m_datalayout (p1 @ p2) = opt_first (m_datalayout p1) (m_datalayout p2).
  Proof.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma m_type_defs_app: forall {T X} (p1 p2 : modul T X),
      m_type_defs (p1 @ p2) = m_type_defs p1 ++ m_type_defs p2.
  Proof.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma m_globals_app: forall {T X} (p1 p2 : modul T X),
      m_globals (p1 @ p2) = m_globals p1 ++ m_globals p2.
  Proof.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma m_declarations_app: forall {T X} (p1 p2 : modul T X),
      m_declarations (p1 @ p2) = m_declarations p1 ++ m_declarations p2.
  Proof.
    intros ? ? [] []; reflexivity.
  Qed.

  Lemma map_option_cons_inv: forall {A B} (f : A -> option B) (a : A) (l : list A) (r : list B),
      map_option f (a :: l) = Some r ->
       exists b r',
        f a = Some b /\
        map_option f l = Some r' /\
        r = b :: r'.
  Proof.      
    intros.
    (* YZ TODO : Test on 8.11 if cbn also behaves annoyingly here *)
    simpl in H; do 2 (break_match_hyp; try inv_option). 
    do 2 eexists; repeat split; auto.
  Qed.

  Lemma map_option_cons: forall {A B} (f : A -> option B) (a : A) (b : B) (l : list A) (r : list B),
        f a = Some b ->
        map_option f l = Some r ->
        map_option f (a :: l) = Some (b :: r).
  Proof.      
    intros * EQ1 EQ2; simpl; rewrite EQ1, EQ2; reflexivity.
  Qed.

  Lemma map_option_app_inv: forall {A B} (f : A -> option B) (l1 l2 : list A) (r : list B),
      map_option f (l1 ++ l2) = Some r ->
      exists r1 r2,
        map_option f l1 = Some r1 /\
        map_option f l2 = Some r2 /\
        r = r1 ++ r2.
  Proof.
    induction l1 as [| x l1 IH]; intros * EQ.
    - do 2 eexists; repeat split; try reflexivity; auto. 
    - generalize EQ; intros EQ'; apply map_option_cons_inv in EQ'; destruct EQ' as (b & ? & EQ1 & EQ2 & ->). 
      apply IH in EQ2; destruct EQ2 as (r1 & r2 & EQ2 & EQ3 & ->).
      exists (b::r1), r2; repeat split; auto. 
      apply map_option_cons; auto.
  Qed.

  Lemma mcfg_of_app_modul: forall {T} p1 p2 (m : mcfg T),
      mcfg_of_modul _ (p1 @ p2) = Some m ->
      exists m1 m2, mcfg_of_modul _ p1 = Some m1 /\
               mcfg_of_modul _ p2 = Some m2 /\
               m1 @ m2 = m.
  Proof.
    intros * EQ; cbn in EQ.
    break_match_hyp; inv_option.
    rewrite m_definitions_app in Heqo.
    apply map_option_app_inv in Heqo; destruct Heqo as (? & ? & EQ1 & EQ2 & ->).
    cbn; rewrite EQ1, EQ2; do 2 eexists; repeat split; try reflexivity.
    cbn.
    rewrite m_name_app, m_target_app, m_datalayout_app, m_type_defs_app, m_globals_app, m_declarations_app; reflexivity. 
  Qed.

End TLE_To_Modul.

Infix "@" := (modul_app) (at level 60).
