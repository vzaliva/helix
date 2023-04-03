From ITree Require Import
     ITree
     ITreeFacts
     Events.State
     Events.StateFacts
     InterpFacts
     Eq.Eq.

From Vellvm Require Import
     Utils.Tactics
     Utils.Util
     Syntax.LLVMAst
     Syntax.Traversal
     Syntax.AstLib
     Syntax.DynamicTypes
     Syntax.CFG
     Syntax.TypToDtyp
     Semantics.LLVMEvents
     Semantics.DynamicValues
     Semantics.TopLevel
     Semantics.InterpretationStack
     Handlers.Handlers
     Theory.Refinement
     Theory.DenotationTheory
     Theory.InterpreterCFG
     Theory.InterpreterMCFG.

From ExtLib Require Import
     Structures.Functor.

From Coq Require Import
     Strings.String
     Logic
     Morphisms
     Relations
     List
     Program
     ZArith.

Require Import Ceres.Ceres.
Import BinInt.
Import ListNotations.
Import ITree.Basics.Basics.Monads.

From Vellvm Require Import Util.
Require Import ITree.Events.State.

Require Import ITree.Eq.Eq.

From Vellvm Require Import Utils.AListFacts.

Import Traversal.

(* YZ: Should they be Opaque or simpl never? *)
Global Opaque denote_ocfg.
Global Opaque assoc.
Global Opaque denote_instr.
Global Opaque denote_terminator.
Global Opaque denote_phi.
Global Opaque denote_code.

Ltac typ_to_dtyp_simplify :=
  repeat
    (try rewrite typ_to_dtyp_I in *;
     try rewrite typ_to_dtyp_D in *;
     try rewrite typ_to_dtyp_D_array in *;
     try rewrite typ_to_dtyp_P in *).

From Paco Require Import paco.
Lemma eutt_mon {E R1 R2} (RR RR' : R1 -> R2 -> Prop)
      (LERR: RR <2= RR') :
  @eutt E R1 R2 RR <2= eutt RR'.
Proof.
  eapply eqit_mon; eauto.
Qed.

From Vellvm Require Import Syntax.Scope.

(* Enforcing these definitions to be unfolded systematically by [cbn] *)
Arguments endo /.
Arguments Endo_id /.
Arguments Endo_ident /.

Arguments find_block : simpl never.

From Vellvm Require Import Theory.SymbolicInterpreter.

Module eutt_Notations.
  Notation "t '======================' '======================' u '======================' '{' R '}'"
    := (eutt R t u)
         (only printing, at level 200,
          format "'//' '//' t '//' '======================' '======================' '//' u '//' '======================' '//' '{' R '}'"
         ).
End eutt_Notations.

Import D.
Module VIR_denotation_Notations.
  (* Notation "'ℐ' '(' t ')' g l m" := (interp_cfg_to_L3 _ t g l m) (only printing, at level 10). *)
  Notation "'global.' g 'local.' l 'memory.' m 'ℐ' t" :=
    (interp_cfg3 t g l m)
      (only printing, at level 10,
       format "'global.'  g '//' 'local.'  l '//' 'memory.'  m '//' 'ℐ'  t").

  Notation "⟦ c ⟧" := (denote_code c) (only printing, at level 10).
  Notation "⟦ i ⟧" := (denote_instr i) (only printing, at level 10).
  Notation "⟦ t ⟧" := (denote_terminator t) (only printing, at level 10).
  Notation "⟦ e ⟧" := (denote_exp None e) (only printing, at level 10).
  Notation "⟦ τ e ⟧" := (denote_exp (Some τ) e) (only printing, at level 10).
  Notation "x" := (translate exp_to_instr x) (only printing, at level 10).

  (* Should be part of the surface notations *)
  Notation "'call' x args" := ((IVoid _, INSTR_Call x args)) (at level 30, only printing).

  Notation "'λ' a b c d ',' k" := (fun '(a,(b,(c,d))) => k) (only printing, at level 0, format "'λ'  a  b  c  d ',' '[' '//' k ']'").

End VIR_denotation_Notations.

Import ITreeNotations.

From Vellvm Require Import InstrLemmas ExpLemmas.

Ltac vred_r :=
  let R := fresh
  in eutt_hide_rel_named R;
     let X := fresh
     in eutt_hide_left_named X; vred_C3;
        subst X; subst R.

Ltac vred_l :=
  let R := fresh
  in eutt_hide_rel_named R;
     let X := fresh
     in eutt_hide_right_named X; vred_C3;
        subst X; subst R.

Ltac vstep := vstep3.

Ltac tred := autorewrite with itree.

Arguments denote_exp : simpl never.
(* TODO: fmap (mk_block _ _ _ _ _) does not reduce, although we would like.
   However if I do the following to force the unfolding, then fmap always
   unfolds even in many other cases where we don't want it to do so.
   Solution?
 *)
(* Arguments fmap /. *)
(* Arguments Fmap_block /. *)
Arguments denote_phis : simpl never.
Arguments denote_code : simpl never.
Arguments denote_terminator : simpl never.
Arguments denote_block : simpl never.

From Vellvm Require Import
     Utils.TFor
     Utils.NoFailure
     Utils.PropT
.
Require Export ITree.Events.FailFacts.

From Vellvm Require Import Utils.PostConditions.

(** * Naming conventions for configurations and predicates over configurations *)

Notation memoryV := memory_stack.

(* Return state of a denoted and interpreted [cfg].
     Note the lack of local stack *)
Definition config_cfg
  := memoryV * (local_env * (global_env)).

(* Constructor to avoid having to worry about the nesting *)
Definition mk_config_cfg m l g: config_cfg := (m,(l,g)).

(* Return state of a denoted and interpreted [mcfg] *)
Definition config_mcfg
  := memoryV *
       (local_env * @Stack.stack (local_env) * (global_env)).

(* Return state and value of a denoted and interpreted (open) [cfg].
     Note the lack of local stack.
     Note that we may return a [block_id] alternatively to a [uvalue]
 *)
Definition config_cfg_T (T:Type): Type
  := memoryV * (local_env * (global_env * T)).
Definition config_res_cfg
  := config_cfg_T (block_id + uvalue).

(* Return state and value of a denoted and interpreted [mcfg]. *)
Definition config_mcfg_T (T:Type): Type
  := memoryV * (local_env * @Stack.stack (local_env) * (global_env * T)).
Definition config_res_mcfg :=
  config_mcfg_T uvalue.

(* -- Injections -- *)
(* The nested state transformers associate the products the other way,
     we therefore define injections of memory states and values into return
     types of computations.
 *)
Definition mk_config_cfg_T (T:Type) (v:T): config_cfg -> (config_cfg_T T)
  := fun '(m, (ρ, g)) => (m, (ρ, (g, v))).

Definition mk_config_mcfg_T (T:Type) (v:T): config_mcfg -> (config_mcfg_T T)
  := fun '(m, (ρ, g)) => (m, (ρ, (g, v))).


(* Facilities to refer to the type of relations used during the simulations
   of various pieces of denotions we manipulate.
   In particular, all relations we state assume success on the Helix side, and
   we will lift systematically these relations to the option type.
 *)

(** * Predicates  *)
(** Predicate on mcfg-level states *)
Definition Pred_mcfg: Type := config_mcfg -> Prop.
Definition Pred_mcfg_T (TV: Type): Type := config_mcfg_T TV -> Prop.
(** Predicate on cfg-level states *)
Definition Pred_cfg: Type := config_cfg -> Prop.
Definition Pred_cfg_T (TV: Type): Type := config_cfg_T TV -> Prop.

Require Import ExtLib.Data.Map.FMapAList.
Import SemNotations.

(** * Specifications for alloc *)

Lemma allocated_allocate_allocated (m1 m2 : memoryV) (d : dtyp) (a a' : Addr.addr) :
  allocated a m1 -> allocate m1 d = inr (m2, a') -> allocated a m2.
Proof.
  intros A AS.
  unfold allocate, allocated in *.
  destruct d; inv AS.
  all: repeat break_let; subst.
  all: unfold add_logical_block, add_logical_block_mem, add_to_frame in *.
  all: repeat break_match; inv Heqm1.
  all: apply member_add_ineq; [| assumption].
  all: unfold next_logical_key, next_logical_key_mem.
  all: simpl.
  all: intros C; rewrite C in A; contradict A.
  all: apply next_logical_key_fresh.
Qed.

Lemma allocate_allocated (m1 m2 : memoryV) (d : dtyp) (a : Addr.addr) :
  allocate m1 d = inr (m2, a) -> allocated a m2.
Proof.
  intros AS.
  unfold allocate, allocated in *.
  destruct d; inv AS.
  all: repeat break_let; subst.
  all: unfold add_logical_block, add_logical_block_mem, add_to_frame in *.
  all: repeat break_match; inv Heqm; inv Heqm0.
  all: apply member_add_eq.
Qed.

(** * MISC *)

Lemma eutt_trans : forall {E A} (R : A -> A -> Prop),
    Transitive R ->
    Transitive (eutt (E := E) R).
Proof.
  repeat intro.
  eapply eqit_trans in H1; [| apply H0].
  eapply eqit_mon with (RR := rcompose R R); eauto.
  intros.
  apply trans_rcompose; eauto.
Qed.

Lemma eutt_ret_inv_strong {E X Y} (R : X -> Y -> Prop) (x : X) (t : itree E Y) :
  eutt R (Ret x) t ->
  exists y, t ≈ Ret y /\ R x y.
Proof.
  intros EQ; punfold EQ.
  red in EQ.
  dependent induction EQ.
  - exists r2; split; auto.
    rewrite itree_eta, <-x; reflexivity.
  - edestruct IHEQ as (y & EQ1 & HR); auto.
    exists y; split; auto.
    now rewrite itree_eta, <- x, tau_eutt.
Qed.

Lemma eutt_ret_inv_strong' {E X Y} (R : X -> Y -> Prop) (t : itree E X) (y : Y) :
  eutt R t (Ret y) ->
  exists x, t ≈ Ret x /\ R x y.
Proof.
  intros EQ; punfold EQ.
  red in EQ.
  dependent induction EQ.
  - exists r1; split; auto.
    rewrite itree_eta, <-x; reflexivity.
  - edestruct IHEQ as (?x & EQ1 & HR); auto.
    exists x0; split; auto.
    now rewrite itree_eta, <- x, tau_eutt.
Qed.

Lemma typ_to_dtyp_void s : typ_to_dtyp s TYPE_Void = DTYPE_Void.
Proof.
  intros; rewrite typ_to_dtyp_equation; reflexivity.
Qed.

Lemma option_rel_trans : forall {A} (R : A -> A -> Prop),
    Transitive R ->
    Transitive (option_rel R).
Proof.
  repeat intro.
  cbv in *.
  repeat break_match; intuition.
  subst.
  eapply H; eauto.
Qed.

Lemma exp_eq_dec: forall e1 e2 : exp dtyp, {e1 = e2} + {e1 <> e2}.
Admitted.

Lemma global_eq_dec: forall g1 g2 : global dtyp, {g1 = g2} + {g1 <> g2}.
Proof.
  repeat decide equality.
  apply exp_eq_dec.
  apply dtyp_eq_dec.
Qed.

(** * [interp_local_stack] theory *)
Lemma interp_local_stack_tau:
  forall (k v map : Type) (M : Maps.Map k v map) (SK : CeresSerialize.Serialize k) (E F G : Type -> Type) (H : FailureE -< E +' F +' G) (R : Type) (l : map * stack) (t : itree (E +' F +' (LocalE k v +' StackE k v) +' G) R),
    interp_local_stack (Tau t) l ≅ Tau (interp_local_stack t l).
Proof.
  intros.
  unfold interp_local_stack at 1.
  rewrite interp_state_tau.
  reflexivity.
Qed.


(** * [interp_mcfg3] theory *)

Lemma interp3_ret : forall (R : Type) (g : global_env) (l : local_env * stack) (m : memoryV) (x : R), ℑs3 (Ret x) g l m ≅ Ret3 g l m x.
Proof.
  intros; unfold ℑs3.
  rewrite interp_intrinsics_ret, interp_global_ret, interp_local_stack_ret, interp_memory_ret.
  reflexivity.
Qed.

Lemma interp3_tau : forall R (t : itree L0 R) g l m,
    interp_mcfg3 (Tau t) g l m ≅ Tau (interp_mcfg3 t g l m).
Proof.
  intros; unfold ℑs3.
  rewrite interp_intrinsics_Tau, interp_global_Tau, interp_local_stack_tau, interp_memory_Tau.
  reflexivity.
Qed.

Lemma interp_cfg3_tau : forall R (t : itree _ R) g l m,
    interp_cfg3 (Tau t) g l m ≅ Tau (interp_cfg3 t g l m).
Proof.
  intros; unfold ℑ3.
  rewrite interp_intrinsics_Tau, interp_global_Tau, interp_local_Tau, interp_memory_Tau.
  reflexivity.
Qed.

Lemma interp3_map_monad {A B} g l m (xs : list A) (ts : A -> itree _ B) :
  ℑs3 (map_monad ts xs) g l m ≈
    map_monad (m := Monads.stateT _ (Monads.stateT _ (Monads.stateT _ (itree _))))
    (fun a => ℑs3 (ts a)) xs g l m.
Proof.
  intros; revert g l m; induction xs as [| a xs IH]; simpl; intros.
  - rewrite interp3_ret; reflexivity.
  - rewrite interp3_bind.
    apply eutt_eq_bind; intros (? & ? & ? & ?); cbn.
    rewrite interp3_bind, IH.
    apply eutt_eq_bind; intros (? & ? & ? & ?); cbn.
    rewrite interp3_ret; reflexivity.
Qed.

Instance eq_itree_interp3:
  forall T : Type, Proper (eq_itree eq ==> eq ==> eq ==> eq ==> eq_itree eq) (@interp_mcfg3 T).
Proof.
  repeat intro.
  unfold ℑs3.
  subst; rewrite H.
  reflexivity.
Qed.

Instance eq_itree_interp_cfg3:
  forall T : Type, Proper (eq_itree eq ==> eq ==> eq ==> eq ==> eq_itree eq) (@interp_cfg3 T).
Proof.
  repeat intro.
  unfold ℑ3.
  subst; rewrite H.
  reflexivity.
Qed.

Lemma interp3_MemPush: forall g l m,
    ℑs3 (trigger MemPush) g l m ≈ Ret3 g l (push_fresh_frame m) tt.
Proof.
  intros.
  unfold ℑs3.
  MCFGTactics.go.
  rewrite interp_memory_trigger.
  cbn.
  MCFGTactics.go.
  reflexivity.
Qed.

Lemma interp3_StackPush: forall g a sbot m s,
    ℑs3 (trigger (StackPush s)) g (a,sbot) m ≈
      Ret3 g (fold_right (fun '(x, dv) => alist_add x dv) [] s, a :: sbot) m tt.
Proof.
  intros.
  unfold ℑs3.
  MCFGTactics.go.
  reflexivity.
Qed.

Lemma interp3_GR : forall id g l m v,
  Maps.lookup id g = Some v ->
  interp_mcfg3 (trigger (GlobalRead id)) g l m ≈ Ret (m,(l,(g,v))).
Proof.
  intros * LU.
  unfold interp_mcfg3.
  rewrite interp_intrinsics_trigger.
  cbn.
  unfold Intrinsics.F_trigger.
  rewrite interp_global_trigger.
  cbn in *; rewrite LU.
  rewrite interp_local_stack_ret, interp_memory_ret.
  reflexivity.
Qed.

Lemma interp3_denote_exp_double : forall t g l m,
    interp_mcfg3
      (translate exp_to_L0
                 (denote_exp (Some (DTYPE_Double))
                             (EXP_Double t)))
      g l m
    ≈
    Ret (m, (l, (g, UVALUE_Double t))).
Proof.
  intros; unfold denote_exp; cbn.
  rewrite translate_ret, interp3_ret.
  reflexivity.
Qed.

Lemma interp3_denote_exp_i64 : forall t g l m,
    interp_mcfg3
      (translate exp_to_L0
                 (denote_exp (Some (DTYPE_I 64))
                             (EXP_Integer (unsigned t))))
       g l m
    ≈
    Ret (m, (l, (g, UVALUE_I64 (DynamicValues.Int64.repr (unsigned t))))).
Proof.
  intros; unfold denote_exp; cbn.
  rewrite translate_ret, interp3_ret.
  reflexivity.
Qed.

Lemma interp3_concretize_or_pick_concrete :
  forall (uv : uvalue) (dv : dvalue) P g ρ m,
    is_concrete uv ->
    uvalue_to_dvalue uv = inr dv ->
    interp_mcfg3 (concretize_or_pick uv P) g ρ m ≈ Ret (m, (ρ, (g, dv))).
Proof.
  intros uv dv P g ρ m CONC CONV.
  unfold concretize_or_pick.
  rewrite CONC.
  cbn.
  unfold lift_err.
  now rewrite CONV, interp3_ret.
Qed.

Lemma interp3_concretize_or_pick_concrete_exists :
  forall (uv : uvalue) P g ρ m,
    is_concrete uv ->
    exists dv, uvalue_to_dvalue uv = inr dv /\
          interp_mcfg3 (concretize_or_pick uv P) g ρ m ≈ Ret (m, (ρ, (g, dv))).
Proof.
  intros uv P g ρ m CONC.
  pose proof is_concrete_uvalue_to_dvalue uv CONC as (dv & CONV).
  exists dv.
  split; auto.
  now apply interp3_concretize_or_pick_concrete.
Qed.

Lemma interp3_store:
  forall (m m' : memoryV) (val : dvalue) (a : addr) g l,
    write m a val = inr m' ->
    interp_mcfg3 (trigger (Store (DVALUE_Addr a) val)) g l m ≈ Ret (m', (l, (g, ()))).
Proof.
  intros m m' val a g l WRITE.
  unfold interp_mcfg3.
  rewrite interp_intrinsics_trigger.
  cbn.
  unfold Intrinsics.F_trigger.
  rewrite interp_global_trigger.
  rewrite subevent_subevent.
  cbn.
  rewrite interp_local_stack_bind, interp_local_stack_trigger.
  cbn; rewrite subevent_subevent.
  rewrite Eq.bind_bind.
  rewrite interp_memory_bind, interp_memory_store; eauto.
  cbn; rewrite Eq.bind_ret_l.
  rewrite interp_memory_bind, interp_memory_ret, Eq.bind_ret_l.
  rewrite interp_local_stack_ret, interp_memory_ret.
  reflexivity.
Qed.

(** * [interp_mrec] theory *)

#[local] Definition mcfg_ctx fundefs :
  forall T : Type,
    CallE T
    -> itree (CallE +' ExternalCallE +' IntrinsicE +' LLVMGEnvE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' PickE +' UBE +' DebugE +' FailureE) T :=

  (fun (T : Type) (call : CallE T) =>
    match call in (CallE T0) return (itree (CallE +' ExternalCallE +' IntrinsicE +' LLVMGEnvE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' PickE +' UBE +' DebugE +' FailureE) T0) with
    | LLVMEvents.Call dt0 fv args0 =>
        dfv <- concretize_or_pick fv True;;
        match lookup_defn dfv fundefs with
        | Some f_den => f_den args0
        | None =>
            dargs <- map_monad (fun uv : uvalue => pickUnique uv) args0;;
            Functor.fmap dvalue_to_uvalue (trigger (ExternalCall dt0 fv dargs))
        end
    end).

Lemma denote_mcfg_unfold_in : forall G τ addr args f,
    lookup_defn (DVALUE_Addr addr) G = Some f ->
    denote_mcfg G τ (UVALUE_Addr addr) args ≈
      interp_mrec (mcfg_ctx G) (f args).
Proof.
  intros * LU.
  unfold denote_mcfg at 1.
  rewrite RecursionFacts.mrec_as_interp.
  simpl bind. rewrite interp_bind.
  cbn.
  rewrite interp_ret, bind_ret_l.
  rewrite LU.
  rewrite <- RecursionFacts.interp_mrec_as_interp.
  reflexivity.
Qed.

Lemma interp_mrec_ret :
  forall (D E : Type -> Type) (ctx : forall T : Type, D T -> itree (D +' E) T) (U : Type) (u : U),
    interp_mrec ctx (Ret u) ≅ (Ret u).
Proof.
  intros.
  rewrite unfold_interp_mrec; reflexivity.
Qed.

Lemma interp_mrec_tau : forall D E (ctx : D ~> itree (D +' E)) R (t : itree _ R),
    interp_mrec ctx (Tau t) ≅ Tau (interp_mrec ctx t).
Proof.
  intros.
  now rewrite unfold_interp_mrec.
Qed.

#[global] Instance interp_mrec_eutt {D E}
  (ctx : D ~> itree (D +' E)) T :
  Proper (eutt eq ==> eutt eq) (interp_mrec ctx (T := T)).
Proof.
  repeat intro.
  eapply Proper_interp_mrec; auto.
  intros ??.
  reflexivity.
Qed.

Lemma interp3_call_void : forall G n τ f fdfn args g s m addr,
    prefix "llvm." f = false ->
    Maps.lookup (Name f) g = Some (DVALUE_Addr addr) ->
    lookup_defn (DVALUE_Addr addr) G = Some fdfn ->

    ℑs3 (interp_mrec (mcfg_ctx G)
           (Interp.translate instr_to_L0'
              ⟦(IVoid n, INSTR_Call (τ, EXP_Ident (ID_Global (Name f))) args) ⟧i)) g s m
      ≈
      '(m,(s,(g,vs))) <- ℑs3 (interp_mrec (mcfg_ctx G)
                               (Interp.translate instr_to_L0'
                                  (map_monad (fun '(t, op) => Interp.translate exp_to_instr ⟦ op at t ⟧e) args))) g s m
    ;;

    '(m,(s,(g,v))) <- ℑs3 (interp_mrec (mcfg_ctx G) (fdfn vs)) g s m;;
    Ret (m,(s,(g,tt))).
Proof.
  intros * PRE LU LUD.
  Transparent denote_instr.
  cbn.
  rewrite translate_bind, interp_mrec_bind, interp3_bind.
  (* Expressions are pure, lifted by induction over map_monad *)
  apply eutt_clo_bind with
    (UU := fun '(m1,(s1,(g1,v))) m2 =>
             (m1,(s1,(g1,v))) = m2 /\ m1 = m /\ s1 = s /\ g1 = g).
  admit.
  intros (m1,(s1,(g1,v1))) (m2,(s2,(g2,v2))) (EQ & -> & -> & ->).
  symmetry in EQ; inv EQ.
  rewrite PRE.
  (* repeat break_and. *)
  rewrite bind_bind.
  rewrite translate_bind, interp_mrec_bind, interp3_bind.
  Transparent denote_exp.
  unfold denote_exp.
  cbn.
  rewrite bind_trigger.
  rewrite translate_vis.
  rewrite translate_vis.
  rewrite translate_vis.
  cbn.
  rewrite <- bind_trigger.
  rewrite interp_mrec_bind.
  rewrite interp_mrec_trigger.
  cbn.
  rewrite interp3_bind.
  match goal with
    |- context[ℑs3 ?e] =>
      let eqn := fresh in
      assert (eqn:e = trigger (@GlobalRead raw_id dvalue (Name f))) by reflexivity;
      rewrite eqn; clear eqn
  end.
  rewrite interp3_GR; [| apply LU].
  rewrite bind_ret_l.
  rewrite 3translate_ret.
  rewrite interp_mrec_ret, interp3_ret, bind_ret_l.

  rewrite !translate_bind, interp_mrec_bind, interp3_bind.
  rewrite translate_trigger, interp_mrec_trigger.
  cbn.
  rewrite mrec_as_interp.
  cbn.
  rewrite bind_ret_l.
  rewrite LUD.
  cbn.
  rewrite <- RecursionFacts.interp_mrec_as_interp.

  apply eutt_eq_bind.
  intros (? & ? & ? & ?).
  rewrite translate_ret, interp_mrec_ret, interp3_ret.
  reflexivity.
  Opaque denote_instr.
  Opaque denote_exp.

Admitted.

(* Weirdly specific... Shouldn't we lift results that do not depend on [interp_mrec]? *)
Lemma denote_mcfg_ID_Global :
  forall ctx (g : global_env) s (m : memoryV) id (τ : dtyp) (ptr : Addr.addr),
    alist_find id g = Some (DVALUE_Addr ptr) ->

    ℑs3 (interp_mrec ctx
           (Interp.translate instr_to_L0'
              (Interp.translate exp_to_instr (denote_exp (Some τ) (EXP_Ident (ID_Global id)))))) g s m
      ≈
      Ret3 g s m (UVALUE_Addr ptr)
.
Proof.
  intros * LU.
  Transparent denote_exp.
  unfold denote_exp.
  cbn.
  rewrite 3translate_bind, interp_mrec_bind, interp3_bind.
  rewrite !translate_trigger.
  cbn.
  rewrite interp_mrec_trigger.
  cbn.

  match goal with
    |- context[ℑs3 ?e] =>
      let eqn := fresh in
      assert (eqn:e = trigger (@GlobalRead raw_id dvalue id)) by reflexivity;
      rewrite eqn; clear eqn
  end.

  rewrite interp3_GR; [| apply LU].
  rewrite bind_ret_l.
  rewrite !translate_ret,interp_mrec_ret,interp3_ret.
  reflexivity.
Qed.

(** * [allocate_globals] theory *)

Import AlistNotations.
Definition global_ptr_exists fnname : Pred_mcfg :=
  fun '(mem_llvm, (ρ,g)) => exists mf, g @ fnname = Some (DVALUE_Addr mf).

Definition global_ptr_existsT {T} fnname : Pred_mcfg_T T :=
  fun '(mem_llvm, (ρ,(g,_))) => exists mf, g @ fnname = Some (DVALUE_Addr mf).

Record gs_wf (gs : list (global dtyp)) : Prop :=
  {
    gs_wf_nodup  : NoDup (List.map g_ident gs);
    gs_wf_novoid : Forall (fun x => non_void (g_typ x)) gs
  }.

Definition global_is_init (g : global_env) (m : memoryV) (glob : global dtyp) : Prop :=
  exists mf, g @ (g_ident glob) = Some (DVALUE_Addr mf) /\ allocated mf m.

Definition globals_are_uniquely_init (g : global_env) (globs : list (global dtyp)) : Prop :=
  forall glob glob', In glob globs -> In glob' globs -> g_ident glob <> g_ident glob' ->
                g @ (g_ident glob) <> g @ (g_ident glob').

(* TODO
   [gs_init_fresh] should be replaced by a predicate specifying
   the current domain of [g], and take into account the declarations
   that have already be allocated
 *)
Record init_globals (globs : list (global dtyp)) (g : global_env) (m : memoryV) : Prop :=
  {
    gs_init          : Forall (global_is_init g m) globs;
    gs_init_distinct : globals_are_uniquely_init g globs;
    gs_init_fresh    : forall id, ~ In id (map g_ident globs) -> g @ id = None
  }
.

Definition init_globalsT {T} globs : Pred_mcfg_T T :=
  fun '(m, (_,(g,_))) => init_globals globs g m.

(*   In (dc_name d) (map dc_name IntrinsicsDefinitions.defined_intrinsics_decls) *)
(*   \/  *)
(* . *)

(* exists mf, g @ (g_ident glob) = Some (DVALUE_Addr mf) *)
(*         /\ allocated mf m. *)


(* Record init_decls (decls : list (declaration dtyp)) *)
(*   (g : global_env) (m : memoryV) : Prop := *)
(*   { *)
(*     gs_init_decls          : Forall (global_is_init g m) globs; *)
(*     gs_init_distinct_decls : globals_are_uniquely_init g globs; *)
(*     gs_init_fresh_decls    : forall id, ~ In id (map g_ident globs) -> g @ id = None *)
(*   } *)
(* . *)


(* Lemma allocate_declaration_spec : forall (d : declaration dtyp), *)
(*     allocate_declaration d ⤳  *)


(* One proper round of global initialization preserves the invariant *)
Lemma gs_init_extend :
  forall g m m' τ a (glob : global dtyp) globs v,
    ~ In (g_ident glob) (map g_ident globs) ->
    init_globals globs g m ->
    allocate m τ = inr (m', a) ->
    Forall (global_is_init (alist_add (g_ident glob) v g) m') globs.
Proof.
  intros * NIN [FA _ FR] AS.
  rewrite Forall_forall in FA.
  apply Forall_forall.
  intros * IN; apply FA in IN as (? & EQ & AL).
  eexists.
  split.
  - rewrite alist_find_neq.
    apply EQ.
    intros abs.
    apply FR in NIN.
    rewrite <- abs, EQ in NIN.
    inv NIN.
  - eapply allocated_allocate_allocated; eauto.
Qed.

Lemma allocate_global_spec : forall (glob : global dtyp) globs g s m,
    non_void (g_typ glob) ->
    ~ In (g_ident glob) (map g_ident globs) ->
    init_globals globs g m ->
    ℑs3 (allocate_global glob) g s m ⤳ init_globalsT (glob :: globs).
Proof.
  intros * NV FR INV; pose proof INV as [].
  unfold allocate_global.
  cbn.
  rewrite interp3_bind.
  edestruct interp3_alloca as (? & mf & ? & EQ); [eauto |].
  rewrite EQ; clear EQ.
  cbn; rewrite bind_ret_l.
  rewrite interp3_GW.
  apply eutt_Ret.
  cbn.
  split.
  - apply Forall_cons; auto.
    2: eapply gs_init_extend; eauto.
    eexists.
    split.
    rewrite alist_find_add_eq; reflexivity.
    eapply allocate_allocated; eauto.
  - intros ? ? IN IN' NEQ.
    destruct IN as [<- | IN].
    + rewrite alist_find_add_eq.
      destruct IN' as [<- | IN'].
      * now contradiction NEQ.
      * rewrite alist_find_neq; auto.
        eapply Forall_forall in gs_init0; [| apply IN'].
        destruct gs_init0 as (mf' & EQ & AL).
        unfold global_id in *; rewrite EQ.
        intros abs; inv abs.
        apply allocate_correct, was_fresh in H.
        intuition.
    + destruct IN' as [<- | IN'].
      * rewrite alist_find_neq; auto.
        rewrite alist_find_add_eq.
        eapply Forall_forall in gs_init0; [| apply IN].
        destruct gs_init0 as (mf' & EQ & AL).
        unfold global_id in *; rewrite EQ.
        intros abs; inv abs.
        apply allocate_correct, was_fresh in H.
        intuition.
      * rewrite 2 alist_find_neq; auto.
        all:intros abs; apply FR; rewrite <- abs; now apply in_map.
  - intros * NIN.
    destruct (raw_id_eq_dec id (g_ident glob)).
    + subst.
      exfalso; apply NIN; left; reflexivity.
    + rewrite alist_find_neq; auto.
      apply gs_init_fresh0.
      intros abs; apply NIN; right; auto.
Qed.


Lemma allocate_globals_cons :
  forall g gs,
    allocate_globals (g :: gs) ≈ allocate_global g;; allocate_globals gs.
Proof.
  intros; cbn.
  rewrite !bind_bind.
  apply eutt_eq_bind; intros ?.
  apply eutt_eq_bind; intros ?.
  rewrite !bind_bind.
  apply eutt_eq_bind; intros ?.
  rewrite bind_ret_l.
  reflexivity.
Qed.

Lemma init_globals_shuffle_snoc : forall glob globs g m,
      init_globals  (glob :: globs) g m ->
      init_globals (globs ++ [glob]) g m.
Proof.
  intros * [].
  constructor.
  - apply Forall_app; apply List.Forall_cons_iff in gs_init0 as [? ?].
    split; auto.
  - intros ? ? IN IN' NEQ.
    apply in_app_or in IN, IN'.
    apply gs_init_distinct0; auto.
    destruct IN as [IN | IN]; [right; auto| destruct IN as [<- |[]]; left; reflexivity].
    destruct IN' as [IN' | IN']; [right; auto| destruct IN' as [<- |[]]; left; reflexivity].
  - intros ? NIN.
    apply gs_init_fresh0; auto.
    intros abs; apply NIN; destruct abs as [<- | IN].
    rewrite map_app; apply in_or_app; right; left; reflexivity.
    rewrite map_app; apply in_or_app; now left.
Qed.

Lemma init_globalsT_shuffle_snoc : forall {T} glob globs cfn,
      init_globalsT (T := T) (glob :: globs) cfn ->
      init_globalsT (globs ++ [glob]) cfn.
Proof.
  intros ??? [m' [ρ' [g' ?]]]. apply init_globals_shuffle_snoc.
Qed.

Lemma init_globals_shuffle_snoc' : forall glob globs g m,
      init_globals (globs ++ [glob]) g m ->
      init_globals (glob :: globs) g m.
Proof.
  intros * [].
  constructor.
  - apply Forall_app in gs_init0 as [? ?]; apply List.Forall_cons_iff.
    inv H0; split; auto.
  - intros ? ? IN IN' NEQ.
    apply gs_init_distinct0; auto.
    apply in_or_app; destruct IN as [<- | IN]; auto; right; left; auto.
    apply in_or_app; destruct IN' as [<- | IN']; auto; right; left; auto.
  - intros ? NIN.
    apply gs_init_fresh0; auto.
    intros abs; apply NIN. rewrite map_app in abs.
    apply in_app_or in abs.
    cbn.
    destruct abs; auto.
    destruct H; auto.
    contradiction H.
Qed.

Lemma init_globalsT_shuffle_snoc' : forall {T} glob globs cfn,
      init_globalsT (globs ++ [glob]) cfn ->
      init_globalsT (T := T) (glob :: globs) cfn.
Proof.
  intros ??? [m' [ρ' [g' ?]]]. apply init_globals_shuffle_snoc'.
Qed.

Lemma allocate_globals_spec_gen :
  forall (globs_todo globs_done : list (global dtyp)) (g : global_env) s m,
    NoDup (List.map g_ident globs_todo) ->
    Forall (fun x => non_void (g_typ x)) globs_todo ->
    (forall glob, In glob globs_todo -> ~ In (g_ident glob) (map g_ident globs_done)) ->
    init_globals globs_done g m ->
    ℑs3 (allocate_globals globs_todo) g s m ⤳ init_globalsT (globs_todo ++ globs_done).
Proof.
  induction globs_todo as [| glob globs_todo IH]; intros * ND NV FRESH WF.
  - cbn.
    repeat rewrite ?interp3_bind, ?interp3_ret, ?bind_ret_l.
    now apply eutt_Ret.
  - rewrite allocate_globals_cons, interp3_bind.
    eapply has_post_bind_strong
      with (S := init_globalsT (glob :: globs_done)).
    + apply allocate_global_spec.
      * rewrite Forall_forall in NV; apply NV; left; reflexivity.
      * apply FRESH; left; reflexivity.
      * auto.
    + intros [m' [ρ' [g' []]]] HInit.
      apply has_post_weaken with (P := init_globalsT ((globs_todo ++ globs_done) ++ [glob])).
      2: intros; now cbn; apply init_globalsT_shuffle_snoc'.
      rewrite <- app_assoc.
      apply IH.
      * apply NoDup_cons_iff in ND; apply ND.
      * inv NV; auto.
      * intros ? IN abs.
        rewrite map_app in abs; apply in_app_or in abs as [abs | EQ].
        eapply FRESH; [right; eauto | auto].
        destruct EQ as [EQ | []].
        clear -ND EQ IN.
        cbn in ND.
        inv ND.
        apply H1; rewrite EQ.
        now apply in_map.
      * now apply init_globals_shuffle_snoc.
Qed.

Lemma allocate_globals_spec :
  forall (globs : list (global dtyp)) (g : global_env) (Ig : global_env -> Prop) s m,
    (forall g, Ig g -> init_globals [] g m) ->
    Ig g ->
    NoDup (List.map g_ident globs) ->
    Forall (fun x => non_void (g_typ x)) globs ->
    ℑs3 (allocate_globals globs) g s m ⤳ init_globalsT globs.
Proof.
  intros.
  pose proof app_nil_end globs as EQ.
  rewrite EQ at 2.
  apply allocate_globals_spec_gen; auto.
Qed.

Require Import LibHyps.LibHyps.

Ltac eqitree_of_eq h :=
  match type of h with
  | ?t = ?u =>
      let name := fresh in
      assert (name: t ≅ u) by (subst; reflexivity); clear h; rename name into h
  end.
Tactic Notation "eqi_of_eq" ident(h) := eqitree_of_eq h.

Ltac eqitree_of_oeq h :=
  match type of h with
  | ?t = ?u =>
      let name := fresh in
      assert (name: {| _observe := t |} ≅ {| _observe := u |}) by (rewrite h; reflexivity); clear h; rename name into h
  end.
Tactic Notation "eqi_of_oeq" ident(h) := eqitree_of_oeq h.

Lemma interp_trigger_eqit :
  forall {E F : Type -> Type} {R : Type} (f : forall T : Type, E T -> itree F T) (e : E R),
    interp f (ITree.trigger e) ≅ x <- f R e;; Tau (Ret x).
Proof.
  intros.
  unfold ITree.trigger. rewrite interp_vis.
  setoid_rewrite interp_ret.
  reflexivity.
Qed.

Section PARAMS.
  Variable (E F : Type -> Type).
  Context `{FailureE -< F}.
  Notation Eff := (E +' IntrinsicE +' F).

  Lemma interp_intrinsics_trigger_eqit:
    forall X (e : Eff X),
      interp_intrinsics (ITree.trigger e) ≅ x <- interp_intrinsics_h e;; Tau (Ret x).
  Proof.
    intros *.
    unfold interp_intrinsics.
    rewrite interp_trigger_eqit.
    reflexivity.
  Qed.

End PARAMS.

Lemma interp_cfg3_vis_eqit :
  forall T R (e : instr_E T) (k : T -> itree instr_E R) g l m,
    ℑ3 (Vis e k) g l m ≅ '(m, (l, (g, x))) <- ℑ3 (trigger e) g l m;; ℑ3 (k x) g l m.
Proof.
  intros.
  unfold ℑ3.
  rewrite interp_intrinsics_vis_eqit.
  rewrite interp_global_bind, interp_local_bind, interp_memory_bind.
  rewrite interp_intrinsics_trigger_eqit.
  rewrite interp_global_bind, interp_local_bind, interp_memory_bind.
  rewrite bind_bind.
  eapply eq_itree_clo_bind; [reflexivity |].
  intros x y <-; destruct x as [? [? [ ? ?]]].
  rewrite ?interp_global_Tau, ?interp_local_Tau, ?interp_memory_Tau.
  rewrite bind_tau, eqitree_Tau.
  rewrite interp_global_ret, interp_local_ret, interp_memory_ret, bind_ret_l.
  reflexivity.
Qed.

(* Lemma interp_intrinsics_ret_inv : *)
(*   forall {E F} `{FailureE -< F} [R] (t : itree (E +' _ +' F) R) (r : R), *)
(*     interp_intrinsics t ≅ Ret r -> t ≅ Ret r. *)
(* Proof. *)
(*   intros * EQ. *)
(*   unfold interp_intrinsics in EQ. *)
(*   rewrite unfold_interp in EQ. *)
(*   rewrite (itree_eta t). *)
(*   destruct (observe t) eqn:eqo; cbn in EQ; punfold EQ. *)
(*   red in EQ; cbn in EQ; inv EQ; inv CHECK. *)
(*   red in EQ; cbn in EQ; dependent destruction EQ. inv CHECK. *)


Notation E := (ExternalCallE +' PickE +' UBE +' DebugE +' FailureE).
Definition lenv := (local_env * @stack local_env).

Definition handle_all_intrinsics :
  IntrinsicE ~> stateT memoryV (itree E) :=
  fun X '(Intrinsic _ fname args) m =>
    match assoc fname defs_assoc with
    | Some f => match f args with
               | inl msg => raise msg
               | inr result => Ret1 m result
               end
    | None =>
        if string_dec fname "llvm.memcpy.p0i8.p0i8.i32" then
          match handle_memcpy args (fst m) with
          | inl err => raise err
          | inr m' => Ret1 (m', snd m) DVALUE_None
          end
        else
          raise ("Unknown intrinsic: " ++ fname)
    end.
Arguments handle_all_intrinsics [_].

Definition handler3 : L0 ~> stateT global_env (stateT lenv (stateT memoryV (itree E))) :=
  fun T e g l m =>
    match e with
    | inl1 e =>
        v <- trigger e;; Ret3 g l m v
    | inr1 (inl1 e) =>
        '(m,v) <- handle_all_intrinsics e m;; Ret3 g l m v
    | inr1 (inr1 (inl1 e)) =>
        '(g,v) <- handle_global e g;; Ret3 g l m v
    | inr1 (inr1 (inr1 (inl1 (inl1 e)))) =>
        '(l',v) <- handle_local e (fst l);; Ret3 g (l', snd l) m v
    | inr1 (inr1 (inr1 (inl1 (inr1 e)))) =>
        '(l,v) <- handle_stack e l;; Ret3 g l m v
    | inr1 (inr1 (inr1 (inr1 (inl1 e)))) =>
        '(m,v) <- handle_memory e m;; Ret3 g l m v
    | inr1 (inr1 (inr1 (inr1 (inr1 e)))) =>
        v <- trigger e;; Ret3 g l m v
    end.
Arguments handler3 [_].

From ExtLib Require Import
     Structures.Monads
     Structures.Maps.

Section PARAMS.
  Variable (k v:Type).
  Context {map : Type}.
  Context {M: Map k v map}.
  Context {SK : Serialize k}.
  Variable (E F G H : Type -> Type).
  Context `{FailureE -< G}.
  Notation Effin := (E +' F +' (GlobalE k v) +' G).
  Notation Effout := (E +' F +' G).

  Lemma interp_global_trigger_eqit:
    forall (g : map) X (e : Effin X),
      interp_global (ITree.trigger e) g ≅ v <- interp_global_h e g;; Tau (Ret v).
  Proof.
    intros.
    unfold interp_global.
    rewrite interp_state_trigger_eqit.
    reflexivity.
  Qed.

  Lemma interp_global_raise :
    forall (g : map) T s,
    @interp_global k v map _ _ E F G _ T (LLVMEvents.raise s) g ≅ LLVMEvents.raise s.
  Proof.
    intros.
    unfold LLVMEvents.raise.
    rewrite interp_global_bind, interp_global_trigger_eqit, !bind_bind.
    cbn; rewrite ?bind_bind.
    eapply eq_itree_clo_bind.
    reflexivity.
    intros [].
  Qed.

End PARAMS.

Section PARAMS.
  Variable (k v:Type).
  Context {map : Type}.
  Context {M: Map k v map}.
  Context {SK : Serialize k}.
  Variable (E F G : Type -> Type).
  Context `{FailureE -< E +' F +' G}.
  Notation Effin := (E +' F +' (LocalE k v +' StackE k v) +' G).
  Notation Effout := (E +' F +' G).

  Lemma interp_local_stack_trigger_eqit:
    forall s X (e : Effin X),
      interp_local_stack (ITree.trigger e) s ≅
      v <- interp_local_stack_h (handle_local (v:=v)) e s;; Tau (Ret v).
  Proof.
    intros.
    unfold interp_local_stack.
    rewrite interp_state_trigger_eqit.
    reflexivity.
  Qed.

End PARAMS.

Section PARAMS.
  Variable (E F G : Type -> Type).
  Context `{FailureE -< F} `{UBE -< F} `{PickE -< F}.
  Notation Effin := (E +' IntrinsicE +' MemoryE +' F).
  Notation Effout := (E +' F).
  Notation interp_memory := (@interp_memory E F _ _ _).

  Lemma interp_memory_trigger_eqit:
    forall m X (e : Effin X),
      interp_memory (trigger e) m ≅
      v <- interp_memory_h e m;; Tau (Ret v).
  Proof.
    intros.
    unfold interp_memory.
    setoid_rewrite interp_state_trigger_eqit.
    reflexivity.
  Qed.

  Lemma interp_memory_raise :
    forall m T s,
    @interp_memory T (LLVMEvents.raise s) m ≅ LLVMEvents.raise s.
  Proof.
    intros.
    unfold LLVMEvents.raise.
    rewrite interp_memory_bind.
    match goal with
    |- ITree.bind (interp_memory (ITree.trigger ?e) _) _ ≅ _ =>
      rewrite (interp_memory_trigger_eqit _ _ e)
    end.
    cbn; rewrite ?bind_bind.
    eapply eq_itree_clo_bind.
    reflexivity.
    intros [].
  Qed.

End PARAMS.

(* Lemma interp_global_trigger_eqit: *)
(*   forall X (e : Eff X), *)
(*     interp_intrinsics (ITree.trigger e) ≅ x <- interp_intrinsics_h e;; Tau (Ret x). *)
(* Proof. *)
(*   intros *. *)
(*   unfold interp_intrinsics. *)
(*   rewrite interp_trigger_eqit. *)
(*   reflexivity. *)
(* Qed. *)

Ltac go :=
  repeat match goal with
    | |- context [interp_intrinsics (ITree.bind _ _)] => rewrite interp_intrinsics_bind
    | |- context [interp_global (ITree.bind _ _)] => rewrite interp_global_bind
    | |- context [interp_local_stack (ITree.bind _ _)] => rewrite interp_local_stack_bind
    | |- context [interp_memory (ITree.bind _ _)] => rewrite interp_memory_bind
    | |- context [interp_intrinsics (ITree.trigger _)] => rewrite interp_intrinsics_trigger_eqit; cbn; rewrite ?subevent_subevent
    | |- context [interp_global (ITree.trigger _)] => rewrite interp_global_trigger_eqit; cbn; rewrite ?subevent_subevent
    | |- context [interp_local_stack (ITree.trigger _)] => rewrite interp_local_stack_trigger_eqit; cbn; rewrite ?subevent_subevent
    | |- context [interp_memory (ITree.trigger ?e)] =>
        rewrite (interp_memory_trigger_eqit _ _ _ _ e); cbn; rewrite ?subevent_subevent
    | |- context [ITree.bind (ITree.bind _ _) _] => rewrite bind_bind
    | |- context [interp_intrinsics (Ret _)] => rewrite interp_intrinsics_ret
    | |- context [interp_global (Ret _)] => rewrite interp_global_ret
    | |- context [interp_local_stack (Ret _)] => rewrite interp_local_stack_ret
    | |- context [interp_memory (Ret _)] => rewrite interp_memory_ret
    | |- context [ITree.bind (Ret _) _] => rewrite bind_ret_l
    | |- context [ITree.bind (Tau _) _] => rewrite bind_tau
    | |- Tau _ ≈ _ => rewrite tau_euttge
    | |- _ => rewrite ?interp_memory_Tau, ?interp_global_Tau, ?interp_local_stack_tau, ?interp_intrinsics_Tau
    end.

Lemma raise_eutt {E X Y Z} `{FailureE -< E} s (k : X -> itree _ Z) (g : Y -> itree _ Z):
  LLVMEvents.raise s >>= k ≈ LLVMEvents.raise s >>= g.
Proof.
  unfold LLVMEvents.raise; rewrite !bind_bind.
  apply eutt_eq_bind; intros [].
Qed.

  Lemma interp_local_stack_raise :
    forall l T s,
    @interp_local_stack raw_id uvalue _ _ _ ExternalCallE IntrinsicE (MemoryE +' PickE +' UBE +' DebugE +' FailureE) _ _ T (LLVMEvents.raise s) l ≅ LLVMEvents.raise s.
  Proof.
    intros.
    unfold LLVMEvents.raise.
    rewrite interp_local_stack_bind, interp_local_stack_trigger_eqit, !bind_bind.
    cbn.
    go.
    eapply eq_itree_clo_bind.
    reflexivity.
    intros [].
  Qed.


Lemma string_dec_correct (s s' : string) :
  s <> s' -> exists pf, string_dec s s' = right pf.
Admitted.


Lemma foo : forall X (e : L0 X) g l m,
    interp_mcfg3 (trigger e) g l m ≈ handler3 e g l m.
Proof.
  intros.
  unfold ℑs3.
  rewrite interp_intrinsics_trigger; cbn.
  destruct e as [e | e]; cbn.
  - unfold Intrinsics.E_trigger; cbn.
    go.
    apply eutt_eq_bind.
    intros ?.
    go.
    reflexivity.
  - destruct e as [e | [e | [e | [e | [e | [e | [e | e]]]]]]]; cbn.
    + destruct e; cbn.
      repeat break_match_goal; subst; cbn.
      * rewrite interp_global_raise, interp_local_stack_raise, interp_memory_raise.
        rewrite <- bind_ret_r.
        apply raise_eutt.
      * now go.
      * go.
        unfold handle_intrinsic; cbn.
        destruct m; cbn in *; rewrite Heqs; cbn.
        apply raise_eutt.
      * go.
        unfold handle_intrinsic; cbn.
        destruct m; cbn in *; rewrite Heqs; cbn.
        now go.
      * go.
        unfold handle_intrinsic; cbn.
        apply string_dec_correct in n as [? EQ].
        rewrite EQ.
        destruct m.
        apply raise_eutt.
    + go.
      destruct e; cbn; go.
      reflexivity.
      break_match_goal.
      now go.
      rewrite ?interp_global_raise, ?interp_local_stack_raise, ?interp_memory_raise.
      apply raise_eutt.
    + destruct l; go.
      destruct e as [e | e]; cbn; go.
      * unfold ITree.map;
          destruct e; cbn; go.
        reflexivity.
        break_match_goal; cbn; go.
        reflexivity.
        rewrite ?interp_global_raise, ?interp_local_stack_raise, ?interp_memory_raise.
        apply raise_eutt.
      * destruct e; cbn; go.
        reflexivity.
        break_match_goal; cbn; go.
        rewrite ?interp_global_raise, ?interp_local_stack_raise, ?interp_memory_raise.
        apply raise_eutt.
        reflexivity.
    + cbn; go.
      apply eutt_eq_bind; intros [].
      now go.
    + cbn; go.
      apply eutt_eq_bind; intros ?.
      now go.
    + cbn; go.
      apply eutt_eq_bind; intros ?.
      now go.
    + cbn; go.
      apply eutt_eq_bind; intros ?.
      now go.
    + cbn; go.
      apply eutt_eq_bind; intros ?.
      now go.
Qed.

Notation M := (itree _ _).

Fixpoint tick {E R} (r : R) (n : nat) : itree E R :=
  match n with
  | O   => Ret r
  | S n => Tau (tick r n)
  end.

Lemma eutt_ret_eq_itree :
  forall E R (r: R) (t : itree E R),
    t ≈ Ret r ->
    exists n, t ≅ tick r n.
Proof.
  intros * EQ; punfold EQ; red in EQ; cbn in EQ.
  dependent induction EQ.
  - exists O; rewrite itree_eta, <- x; reflexivity.
  - edestruct IHEQ; try reflexivity.
    exists (S x0); rewrite itree_eta, <-x, H.
    apply eqitree_Tau.
    reflexivity.
Qed.

Lemma interp3_vis_eq_itree:
  forall T R (e : L0 T) (k : T -> itree L0 R) g l m,
    ℑs3 (Vis e k) g l m ≅
            '(m, (l, (g, x))) <- ℑs3 (trigger e) g l m;; ℑs3 (k x) g l m.
Proof.
  intros.
  unfold ℑs3.
  rewrite interp_intrinsics_vis_eqit.
  rewrite interp_global_bind, interp_local_stack_bind, interp_memory_bind.
  rewrite interp_intrinsics_trigger_eqit.
  rewrite interp_global_bind, interp_local_stack_bind, interp_memory_bind.
  rewrite bind_bind.
  eapply eq_itree_clo_bind; [reflexivity |].
  intros x y <-; destruct x as [? [? [ ? ?]]].
  rewrite ?interp_global_Tau, ?interp_local_stack_tau, ?interp_memory_Tau.
  rewrite bind_tau, eqitree_Tau.
  rewrite interp_global_ret, interp_local_stack_ret, interp_memory_ret, bind_ret_l.
  reflexivity.
Qed.

Notation gequ r := (gpaco2 (eqit_ eq false false id) (eqitC eq false false) bot2 r).

Lemma interp_trigger_eq_itree {E F : Type -> Type} {R : Type}
      (f : E ~> (itree F))
      (e : E R) :
  interp f (ITree.trigger e) ≅ v <- f _ e;; Tau (Ret v).
Proof.
  unfold ITree.trigger. rewrite interp_vis.
  setoid_rewrite interp_ret; reflexivity.
Qed.

Lemma interp_intrinsics_trigger' {E F} `{FailureE -< F}:
  forall X (e : (E +' _ +' F) X),
    interp_intrinsics (ITree.trigger e) ≅ v <- interp_intrinsics_h e;; Tau (Ret v).
Proof.
  intros *.
  unfold interp_intrinsics.
  rewrite interp_trigger_eq_itree.
  reflexivity.
Qed.

(* WARNING: CALVIN ACCURATELY POINTED OUT THIS DOES NOT HOLD FOR MEM_POP! TO FIX *)
Lemma push_frame_ignore :
  forall R (t : itree L0 R) (g: global_env) (l: lenv) m,
      interp_mcfg3 t g l (push_fresh_frame m)
      ≈
      ITree.map (fun '(a,(b,(c,d))) => (push_fresh_frame a,(b,(c,d)))) (interp_mcfg3 t g l m).
Proof.
  intro R.
  ginit.
  gcofix cih.
  intros.
  rewrite (itree_eta t).
  destruct (observe t) eqn:EQ.
  - rewrite !interp3_ret.
    rewrite map_ret.
    gstep.
    constructor.
    reflexivity.
  - rewrite !interp3_tau.
    gstep.
    red; cbn; apply EqTau.
    gbase; apply cih.
  - rewrite !interp3_vis_eq_itree.
    rewrite map_bind.
    guclo eqit_clo_bind.
    unshelve econstructor.
    exact (fun '(a,(b,(c,d))) '(a',(b',(c',d'))) => a = push_fresh_frame a' /\ b = b' /\ c = c' /\ d = d').
    {
      clear.
      rewrite 2 foo.
      admit.
    }
    intros (? & ? & ? & ?) (m' & l' & g' & x') (-> & -> & -> & ->).
    (* TO FIX: foo has eaten all my guards -> refine it into a eutt_ge equation making explicit that there is at least one tau after the handler? *)
    gbase.
Admitted.


(* Lemma push_frame_ignore : *)
(*   forall R (t : itree L0 R) (g: global_env) (l: lenv) m, *)
(*       interp_mcfg3 t g l (push_fresh_frame m) *)
(*       ≅ *)
(*       ITree.map (fun '(a,(b,(c,d))) => (push_fresh_frame a,(b,(c,d)))) (interp_mcfg3 t g l m). *)
(* Proof. *)
(*   intro R. *)
(*   ginit. *)
(*   gcofix cih. *)
(*   intros. *)
(*   rewrite (itree_eta t). *)
(*   destruct (observe t) eqn:EQ. *)
(*   - rewrite !interp3_ret. *)
(*     rewrite map_ret. *)
(*     gstep. *)
(*     constructor. *)
(*     reflexivity. *)
(*   - rewrite !interp3_tau. *)
(*     gstep. *)
(*     red; cbn; apply EqTau. *)
(*     gbase; apply cih. *)
(*   - rewrite !interp3_vis_eq_itree. *)
(*     rewrite map_bind. *)
(*     guclo eqit_clo_bind. *)
(*     unshelve econstructor. *)
(*     exact (fun '(a,(b,(c,d))) '(a',(b',(c',d'))) => a = push_fresh_frame a' /\ b = b' /\ c = c' /\ d = d'). *)
(*     { *)
(*       clear. *)
(*       match goal with |- eqit ?r _ _ ?t ?u => fold (eq_itree r t u) end. *)
(*       destruct e as [e | e]. *)
(*       - destruct e. *)
(* Admitted. *)


(* Lemma push_frame_ignore : *)
(*   forall R (a : global_env) (b : lenv) c d (t : itree L0 R) (g: global_env) (l: lenv) m, *)
(*     interp_mcfg3 t g l m ≈ Ret3 a b c d -> *)
(*     interp_mcfg3 t g l (push_fresh_frame m) ≈ Ret3 a b (push_fresh_frame c) d. *)
(* Proof. *)
(*   intros R a b c d. *)
(*   intros * EQ. *)
(*   apply eutt_ret_eq_itree in EQ as [n EQ]. *)
(*   revert EQ. *)
(*   induction n. *)
(*   - cbn; intros EQ. *)
(*     cut (ℑs3 t g l (push_fresh_frame m) ≅ Ret3 a b (push_fresh_frame c) d). *)
(*     admit. *)
(*   - intros EQ. *)
(*     cbn in EQ. *)


(*   einit. *)
(*   ecofix CIH. *)
(*   intros * EQ. *)
(*   punfold EQ. *)
(*   red in EQ; cbn in EQ. *)
(*   dependent induction EQ. *)
(*   - *)

(*     Unset Printing Notations. *)
    (*
         denote_cfg vs denote_mcfg -> requires "noevent call" predicate
         interp_cfg3 vs interp_mcfg3
     *)

(* Need to spell out what [ctx] is concretely *)

Lemma interp_cfg3_to_mcfg3 :
  forall R a b c d (ctx : _ ~> itree (_ +' L0)) (t : itree instr_E _) g l s m,
    interp_cfg3  (R := R) t g l m ≈ Ret3 a b c d ->
    interp_mcfg3 (R := R) (interp_mrec ctx (translate instr_to_L0' t))
      g (l,s) m
      ≈
      Ret3 a (b,s) c d.
Proof.
Admitted.


(* Lemma interp_cfg3_to_mcfg3 : *)
(*   forall R a b c d (ctx : _ ~> itree (_ +' L0)) (t : itree instr_E _) g l s m, *)
(*     interp_cfg3  (R := R) t g l m                                                ≈ Ret3 a b c d -> *)
(*     interp_mcfg3 (R := R) (interp_mrec ctx (translate instr_to_L0' t)) g (l,s) m ≈ Ret3 a (b,s) c d . *)
(* Proof. *)
(*   intros *. *)
(*   revert g l m t. *)
(*   einit. *)
(*   ecofix IH. *)
(*   intros * EQ. *)
(*   onAllHyps move_up_types. *)
(*   punfold EQ. *)
(*   red in EQ. *)
(*   dependent induction EQ. *)
(*   2:{ *)

(*   - eqi_of_oeq x. *)
(*     rewrite <- itree_eta in x. *)
(*     rewrite (itree_eta t) in x. *)
(*     destruct (observe t) eqn:EQ. *)
(*     2: rewrite interp_cfg3_tau in x; punfold x; inv x; inv CHECK. *)
(*     2:{ rewrite interp_cfg3_vis_eqit in x. *)
(*         unfold trigger in x. *)
(*         rewrite interp_cfg3_vis_eqit in x. *)
(*         punfold x. inv x. inv CHECK. *)
(*     + eqi_of_eq EQ. *)
(*     { *)
(*       assert (Ret (c, (b, (a, d))) ≅ interp_cfg3 t g l m). *)
(*       now rewrite x, <-itree_eta. *)
(*       rewrite (itree_eta t), EQ, interp_cfg3_tau in H. *)
(*       punfold H; inv H. *)
(*       inv CHECK. *)
(*     } *)

(*   remember (observe (ℑ3 t g  l m)) as ot. *)
(*   remember (observe (Ret3 a b c d)) as ou. *)
(*   revert t Heqou Heqot. *)
(*   induction EQ. *)
(*   - subst. *)
(* (* TODO? Relate [init_globals] to [global_ptr_exists] *) *)
