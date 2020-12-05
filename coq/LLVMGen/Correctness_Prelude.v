(** * Correctness of the pass of compilation from FSHCOL to VIR

We prove the correctness of the pass of compilation defined in the
_Correctness.v_. The proof is based on the Interaction Trees approach: the
semantics of both languages are denoted in terms of trees further interpreted
into a monad built atop of the itree one.

The semantic equivalence is expressed in terms of a weak bisimulation over the
resulting monad.

 **)

(** * Prelude
    This file essentially:
    - setup export the module shared over the whole proof
    - define the semantic domains over which we work
    - define conveniences to work with relations involved in the proof
    - define notations and automations easing the proof effort
 *)

Require Export Coq.Arith.Arith.
Require Export Coq.Lists.List.
Require Export Coq.Strings.String.
Require Export Coq.Numbers.BinNums. (* for Z scope *)
Require Export Coq.ZArith.BinInt.
Require Export Psatz.

Require Export Helix.FSigmaHCOL.FSigmaHCOL.
Require Export Helix.FSigmaHCOL.Int64asNT.
Require Export Helix.FSigmaHCOL.Float64asCT.
Require Export Helix.DSigmaHCOL.DSigmaHCOLITree.
Require Export Helix.LLVMGen.Compiler.
Require Export Helix.LLVMGen.Data.
Require Export Helix.LLVMGen.Utils.
Require Export Helix.LLVMGen.tmp_aux_Vellvm.
Require Export Helix.Util.OptionSetoid.
Require Export Helix.Util.ErrorSetoid.
Require Export Helix.Util.ListUtil.
Require Export Helix.Tactics.HelixTactics.

Require Export Vellvm.Utils.Tactics.
Require Export Vellvm.Utils.AListFacts.
Require Export Vellvm.Utils.Util.
Require Export Vellvm.Utils.PostConditions.
Require Export Vellvm.Utils.NoFailure.
Require Export Vellvm.Utils.PropT.
Require Export Vellvm.Syntax.LLVMAst.
Require Export Vellvm.Syntax.CFG.
Require Export Vellvm.Syntax.AstLib.
Require Export Vellvm.Syntax.Scope.
Require Export Vellvm.Syntax.DynamicTypes.
Require Export Vellvm.Syntax.TypToDtyp.
Require Export Vellvm.Syntax.Traversal.
Require Export Vellvm.Syntax.SurfaceSyntax.
Require Export Vellvm.Semantics.Denotation.
Require Export Vellvm.Semantics.LLVMEvents.
Require Export Vellvm.Semantics.TopLevel.
Require Export Vellvm.Handlers.Handlers.
Require Export Vellvm.Theory.InterpreterMCFG.
Require Export Vellvm.Theory.InterpreterCFG.
Require Export Vellvm.Theory.TopLevelRefinements.
Require Export Vellvm.Theory.DenotationTheory.
Require Export Vellvm.Theory.InstrLemmas.
Require Export Vellvm.Theory.ExpLemmas.
Require Export Vellvm.Theory.SymbolicInterpreter.

Require Export ExtLib.Structures.Monads.
Require Export ExtLib.Data.Map.FMapAList.
Require Export ExtLib.Core.RelDec.

Require Export Ceres.Ceres.

Require Export ITree.Interp.TranslateFacts.
Require Export ITree.Basics.CategoryFacts.
Require Export ITree.Events.State.
Require Export ITree.Events.StateFacts.
Require Export ITree.Events.FailFacts.
Require Export ITree.ITree.
Require Export ITree.Eq.Eq.
Require Export ITree.Basics.Basics.
Require Export ITree.Events.Exception.
Require Export ITree.Interp.InterpFacts.

Require Export Flocq.IEEE754.Binary.
Require Export Flocq.IEEE754.Bits.

Require Export MathClasses.interfaces.canonical_names.
Require Export MathClasses.misc.decision.

Require Export LibHyps.LibHyps.

Import AlistNotations.

Open Scope string_scope.
Open Scope char_scope.

Set Implicit Arguments.
Set Strict Implicit.

Export MDSHCOLOnFloat64.
Export D.

Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

Open Scope string_scope.
Open Scope char_scope.
Open Scope nat_scope.
Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

Arguments IntType /.

(** Semantic domains

  - Facilities to work with the same interface of events on both sides through an outer trivial translation.
  - Definition of the top level definition of FSHCOL's semantics by performing the initialization of the
  state at a meta level.
  TODO: Move this semantic component out of the proof.


 *)

(* A couple of notations to avoid ambiguities while not having to worry about imports and qualified names *)
Notation memoryV := memory_stack.
Notation memoryH := MDSHCOLOnFloat64.memory.

Section EventTranslation.

  (* We relate Helix trees and Vellvm trees at a point where their event signatures are still not empty.
   To do so, we therefore relate them at the join of these signature, using [translate] to do so.
   Unfortunately, since [vellvm] works over two different set of signatures depending whether
   function calls are already resolved or not, we also need two joins here.

   TODOYZ: Principle the approach and move it to [itrees]

   NOTEYZ: An alternative would be to translate everything that remains into failure. That could also be
           part of the library as a generic handler.
   *)

  (* Joined set of residual events for full programs *)
  Definition E_mcfg : Type -> Type := (ExternalCallE +' PickE +' UBE +' DebugE +' FailureE).
  (* Joined set of residual events for cfgs *)
  Definition E_cfg : Type -> Type := (CallE +' PickE +' UBE +' DebugE +' FailureE). 

  (* We therefore have the following resulting denotation functions. *)
  (* On the Vellvm side, for [mcfg]: *)
  Definition semantics_llvm_mcfg p : itree E_mcfg _ := model_to_L3 DTYPE_Void "main" main_args defined_intrinsics p.
  (* Which get lifted to [toplevel_entity] as usual: *)
  Definition semantics_llvm (prog: list (toplevel_entity typ (LLVMAst.block typ * list (LLVMAst.block typ)))) :=
    semantics_llvm_mcfg (convert_types (mcfg_of_tle prog)).

  (* On the Helix side: *)
  (* We first define what amount to initializing the runtime before starting executing the operator *)
  (* TODO YZ : This should be moved somewhere else, it is part of the semantics of the language, not the compiler's problem *)
  (* Initialization of globals *)
  Fixpoint denote_initFSHGlobals
           (data: list binary64)
           (globals: list (string * DSHType))
    : itree Event (list binary64 * evalContext) :=
    match globals with
    | [] => ret (data, [])
    | (_,gt)::gs =>
      match gt with
      | DSHnat => Sfail "Unsupported global type: nat"
      | DSHCType =>
        '(data,σ) <- denote_initFSHGlobals data gs ;;
        let '(x, data) := rotate Float64Zero data in
         ret (data, (DSHCTypeVal x)::σ)
      | DSHPtr n =>
        '(data,σ) <- denote_initFSHGlobals data gs ;;
        let (data,mb) := constMemBlock (MInt64asNT.to_nat n) data in
        k <- trigger (MemAlloc n);;
        trigger (MemSet k mb);;
        let p := DSHPtrVal k n in
        ret (data, (p::σ))
      end
    end.

  (** Top-level denotation of an FSHCOL program:
   * initialization of globals
   * allocation of dedicated memory addresses to host the input and output of the program
   * denotation of the operator itself
   *)
  Definition denote_FSHCOL (p:FSHCOLProgram) (data:list binary64)
    : itree Event (list binary64) :=
    '(data, σ) <- denote_initFSHGlobals data p.(Data.globals) ;;
    xindex <- trigger (MemAlloc p.(i));;
    yindex <- trigger (MemAlloc p.(o));;
    let '(data, x) := constMemBlock (MInt64asNT.to_nat p.(i)) data in
    trigger (MemSet xindex x);;

    let σ := List.app σ [DSHPtrVal yindex p.(o); DSHPtrVal xindex p.(i)] in
    denoteDSHOperator σ (p.(Data.op) : DSHOperator);;
    bk <- trigger (MemLU "denote_FSHCOL" yindex);;
    lift_Derr (mem_to_list "Invalid output memory block" (MInt64asNT.to_nat p.(o)) bk).

  Definition handle_failure: (StaticFailE +' DynamicFailE) ~> failT (itree void1) :=
    fun _ _ => ret None.
 
  Definition inject_signature {E} : void1 ~> E := fun _ (x:void1 _) => match x with end.
  Hint Unfold inject_signature : core.

  Definition interp_helix {X E} (t : itree Event X) (mem : memoryH) : failT (itree E) (memoryH * X) :=
    translate inject_signature (interp_fail handle_failure (interp_Mem t mem)).

  (* Finally, the semantics of FSHCOL for the top-level equivalence *)
  Definition semantics_FSHCOL (p: FSHCOLProgram) (data : list binary64)
    : failT (itree E_mcfg) (memoryH * list binary64) :=
    interp_helix (denote_FSHCOL p data) memory_empty.

End EventTranslation.

Notation "'interp_cfg'"  := (interp_cfg_to_L3 defined_intrinsics).
Notation "'interp_mcfg'" := (interp_to_L3 defined_intrinsics).

(** Smart constructors for states, predicates, relations  *)

(* Facilities to refer to the return types of the various pieces of denotations we manipulate *)

Section StateTypes.

  Local Open Scope type_scope.

  Definition config_helix := memoryH.
  Definition config_helix_O := option memoryH.

  Definition config_helix_T (T : Type) := memoryH * T.
  Definition config_helix_OT (T : Type) := option (memoryH * T).

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

End StateTypes.

(* Facilities to refer to the type of relations used during the simulations
   of various pieces of denotions we manipulate.
   In particular, all relations we state assume success on the Helix side, and
   we will lift systematically these relations to the option type.
 *)
Section RelationTypes.

  (** * Relations used for refinements
      At both the [cfg] and [mcfg] levels, we have relation types:
      - Relating states
      - Relating states and values
      - Relating states and values, and accounting for possible failure on the Helix side.
   *)
  (** Relation on memory states with cfg-level states on the vellvm side *)
  Definition Rel_cfg : Type := config_helix -> config_cfg -> Prop.
  (** Type of bisimulation relations between DSHCOL and VIR internal to CFG states,
      parameterized by the types of the computed values. *)
  Definition Rel_cfg_T (TH TV: Type): Type := config_helix_T TH -> config_cfg_T TV -> Prop.
  Definition Rel_cfg_OT (TH TV: Type): Type := config_helix_OT TH -> config_cfg_T TV -> Prop.

  (** Relation on memory states with mcfg-level states on the vellvm side *)
  Definition Rel_mcfg: Type := config_helix -> config_mcfg -> Prop.
  (** Type of bisimulation relations between DSHCOL and VIR internal to CFG states,
      parameterized by the types of the computed values. *)
  Definition Rel_mcfg_T (TH TV: Type): Type := config_helix_T TH -> config_mcfg_T TV -> Prop.
  Definition Rel_mcfg_OT (TH TV: Type): Type := config_helix_OT TH -> config_mcfg_T TV -> Prop.

  (** * Predicates  *)
  (** Predicate on mcfg-level states *)
  Definition Pred_mcfg: Type := config_mcfg -> Prop.
  Definition Pred_mcfg_T (TV: Type): Type := config_mcfg_T TV -> Prop.
  (** Predicate on cfg-level states *)
  Definition Pred_cfg: Type := config_cfg -> Prop.
  Definition Pred_cfg_T (TV: Type): Type := config_cfg_T TV -> Prop.

  (** * Liftings of relations
      Can be lifted to a relation on states and values:
      - A relation on states
      - A relation on values
      - A pure predicate
      Any relation can be lifted to account for failure on the Helix side by asserting success.
   *)
  (* Lifting a relation on states to one on states and values *)
  Definition lift_Rel_cfg (R: Rel_cfg) (TH TV: Type): Rel_cfg_T TH TV :=
    fun '(memH,_) '(memV,(l,(g,_))) => R memH (memV,(l,g)).
  Definition lift_Rel_mcfg (R: Rel_mcfg) (TH TV: Type): Rel_mcfg_T TH TV :=
    fun '(memH,_) '(memV,(l,(g,_))) => R memH (memV,(l,g)).

  (* Lifting a relation on values to one on states and values *)
  Definition lift_Rel_res_cfg {TH TV: Type} (R: TH -> TV -> Prop): Rel_cfg_T TH TV :=
    fun '(_,vh) '(_,(_,(_,vv))) => R vh vv.
  Definition lift_Rel_res_mcfg {TH TV: Type} (R: TH -> TV -> Prop): Rel_mcfg_T TH TV :=
    fun '(_,vh) '(_,(_,(_,vv))) => R vh vv.

  (* Lifting pure predicates *)
  Definition lift_pure_cfg (P : Prop) {TH TV : Type} : Rel_cfg_T TH TV := fun _ _ => P.
  Definition lift_pure_mcfg (P : Prop) {TH TV : Type} : Rel_mcfg_T TH TV := fun _ _ => P.

  Definition succ_rel_l {A B} (R : A -> B -> Prop) : option A -> B -> Prop :=
    fun ma b => match ma with | Some a => R a b | _ => False end.
  Definition succ_cfg {TH TV}: Rel_cfg_T TH TV -> Rel_cfg_OT TH TV := succ_rel_l.
  Definition succ_mcfg {TH TV}: Rel_mcfg_T TH TV -> Rel_mcfg_OT TH TV := succ_rel_l.

  (** Type of bisimulation relation between DSHCOL and LLVM states.
    This relation could be used for fragments of CFG [cfg].
   *)
  Definition Type_R_partial: Type
    := config_helix_T unit -> config_res_cfg -> Prop.

  (** Type of bisimulation relation between DSHCOL and LLVM states.
      This relation could be used for "closed" CFG [mcfg].
   *)
  Definition Type_R_full: Type
    := config_helix_T (list binary64) -> config_res_mcfg -> Prop.

End RelationTypes.
Arguments lift_Rel_cfg R {_ _}.
Arguments lift_pure_cfg /.
Arguments lift_pure_cfg /.
Coercion succ_cfg : Rel_cfg_T >-> Rel_cfg_OT.
Coercion succ_mcfg : Rel_mcfg_T >-> Rel_mcfg_OT.

(* TODOYZ : MOVE *)
Definition conj_rel {A B : Type} (R S: A -> B -> Prop): A -> B -> Prop :=
  fun a b => R a b /\ S a b.
Infix "⩕" := conj_rel (at level 85, right associativity).

(* Introduction pattern useful after [eutt_clo_bind] *)
Ltac introR :=
  intros [[?memH ?vH] |] (?memV & ?l & ?g & ?vV) ?PRE; [| now inv PRE].

(** Proof automation *)

Ltac unfolder_vellvm       := unfold Traversal.Endo_id.
Ltac unfolder_vellvm_hyp h := unfold Traversal.Endo_id in h.
Ltac unfolder_vellvm_all   := unfold Traversal.Endo_id in *.

Ltac unfolder_helix       := unfold mem_lookup_err, memory_lookup_err, ErrorWithState.option2errS, lift_Serr, lift_Derr, Int64_eq_or_cerr, Z_eq_or_cerr,ErrorWithState.err2errS,Z_eq_or_err, context_lookup, trywith.
Ltac unfolder_helix_hyp h := unfold mem_lookup_err, memory_lookup_err, ErrorWithState.option2errS, lift_Serr, lift_Derr, Int64_eq_or_cerr, Z_eq_or_cerr,ErrorWithState.err2errS,Z_eq_or_err, context_lookup, trywith in h.
Ltac unfolder_helix_all   := unfold mem_lookup_err, memory_lookup_err, ErrorWithState.option2errS, lift_Serr, lift_Derr, Int64_eq_or_cerr, Z_eq_or_cerr,ErrorWithState.err2errS,Z_eq_or_err, context_lookup, trywith in *.

(**
     Better solution (?): use
     `Argument myconstant /.`
     to force `cbn` to unfold `myconstant`
 *)
Tactic Notation "unfolder" := unfolder_helix; unfolder_vellvm.
Tactic Notation "unfolder" "in" hyp(h) := unfolder_helix_hyp h; unfolder_vellvm_hyp h.
Tactic Notation "unfolder" "in" "*" := unfolder_helix_all; unfolder_vellvm_all.

Tactic Notation "cbn*" := (repeat (cbn; unfolder)).
Tactic Notation "cbn*" "in" hyp(h) := (repeat (cbn in h; unfolder in h)).
Tactic Notation "cbn*" "in" "*" := (repeat (cbn in *; unfolder in *)).

(* This tactic is quite dumb, and should be refined if needed, but does a good job at
   reducing the success of a compilation unit to the success of all of its sub-operations.
 *)
Ltac simp := repeat (inv_sum || inv_option || break_and || break_match_hyp).

Section Add_Comment.

  (* NOTEYZ:
     Move this or a similar facility to Vellvm
   *)
  Lemma add_comment_preserves_num_blocks :
    forall l comments blocks,
      add_comment l comments ≡ blocks ->
      List.length l ≡ List.length blocks.
  Proof.
    induction l; intros comments blocks H.
    - inversion H; reflexivity.
    - simpl. inversion H. simpl.
      reflexivity.
  Qed.

  Lemma add_comment_singleton :
    forall l comments block,
      add_comment l comments ≡ [block] ->
      exists b, l ≡ [b].
  Proof.
    intros l comments block H.
    destruct l.
    - inv H.
    - destruct l.
      + exists b. reflexivity.
      + inv H.
  Qed.

  Lemma add_comment_inputs :
    forall (bs : list (LLVMAst.block typ)) env (comments : list string),
      inputs (convert_typ env (add_comment bs comments)) ≡ inputs (convert_typ env bs).
  Proof.
    induction bs; intros env comments; auto.
  Qed.

  Lemma add_comment_outputs :
    forall (bs : list (LLVMAst.block typ)) env (comments : list string),
      outputs (convert_typ env (add_comment bs comments)) ≡ outputs (convert_typ env bs).
  Proof.
    induction bs; intros env comments; auto.
  Qed.

End Add_Comment.

Global Opaque interp_cfg_to_L3.

Section InterpMem.

  Lemma interp_Mem_ret :
    forall T mem x,
      @interp_Mem T (Ret x) mem ≅ Ret (mem, x).
  Proof.
    intros T mem x.
    unfold interp_Mem.
    apply interp_state_ret.
  Qed.

  Lemma interp_Mem_bind :
    forall T U mem (t: itree Event T) (k: T -> itree Event U),
      interp_Mem (ITree.bind t k) mem ≈ ITree.bind (interp_Mem t mem) (fun '(mem',v) => interp_Mem (k v) mem').
  Proof.
    intros; unfold interp_Mem.
    rewrite interp_state_bind.
    apply eutt_eq_bind; intros []; reflexivity.
  Qed.

  Lemma interp_Mem_vis_eqit :
    forall T R mem (e : Event T) (k : T -> itree Event R),
      interp_Mem (vis e k) mem ≅ ITree.bind ((case_ Mem_handler MDSHCOLOnFloat64.pure_state) T e mem) (fun sx => Tau (interp_Mem (k (snd sx)) (fst sx))).
  Proof.
    intros T R mem e k.
    unfold interp_Mem.
    apply interp_state_vis.
  Qed.

  Lemma interp_Mem_MemLU_vis :
    forall R str mem m x (k : _ -> itree _ R),
      memory_lookup_err str mem x ≡ inr m ->
      interp_Mem (vis (MemLU str x) k) mem ≈ interp_Mem (k m) mem.
  Proof.
    intros R str mem m x k H.
    setoid_rewrite interp_Mem_vis_eqit;
      cbn; rewrite H; cbn.
    rewrite bind_ret_l; cbn.
    apply tau_eutt.
  Qed.

  Lemma interp_Mem_MemLU :
    forall str mem m x,
      memory_lookup_err str mem x ≡ inr m ->
      interp_Mem (trigger (MemLU str x)) mem ≈ interp_Mem (Ret m) mem.
  Proof.
    intros str mem m x H.
    unfold trigger.
    rewrite interp_Mem_MemLU_vis; eauto.
    reflexivity.
  Qed.

  Lemma interp_Mem_MemSet :
    forall dst blk mem,
      interp_Mem (trigger (MemSet dst blk)) mem ≈ Ret (memory_set mem dst blk, tt).
  Proof.
    intros dst blk mem.
    setoid_rewrite interp_Mem_vis_eqit; cbn.
    rewrite bind_ret_l.
    rewrite interp_Mem_ret.
    apply tau_eutt.
  Qed.

End InterpMem.

Global Opaque interp_Mem.

Section InterpHelix.

  (* YZ: as with state, there is this tension between "inlining" the monad transformer
     in order to rewrite at the itree level, and develop the infrastructure to "properly"
     work in the transformed monad.
     With the former style, we pay by systematically exposing what should be handled internally
     (threading the state, checking on failure).
     With the latter, we need to be more rigorous with the infrastructure.
   *)

  (* inlined *)
  Lemma interp_helix_Ret :
    forall T E mem x,
      @interp_helix T E (Ret x) mem ≅ Ret (Some (mem, x)).
  Proof.
    intros. 
    unfold interp_helix.
    rewrite interp_Mem_ret, interp_fail_Ret, translate_ret.
    reflexivity.
  Qed.

  (* proper *)
  Lemma interp_helix_ret :
    forall T E mem x,
      @interp_helix T E (Ret x) mem ≅ ret (m := failT _) (mem, x).
  Proof.
    intros. 
    unfold interp_helix.
    rewrite interp_Mem_ret, interp_fail_ret.
    cbn; rewrite translate_ret.
    reflexivity.
  Qed.

  Lemma interp_helix_bind :
    forall T U E mem (t: itree Event T) (k: T -> itree Event U),
      @interp_helix _ E (ITree.bind t k) mem ≈
                    ITree.bind (interp_helix t mem)
                    (fun mx => match mx with | None => Ret None | Some x => let '(mem',v) := x in interp_helix (k v) mem' end).
  Proof.
    intros; unfold interp_helix.
    rewrite interp_Mem_bind, interp_fail_bind, translate_bind.
    eapply eutt_eq_bind; intros [[]|]; cbn.
    reflexivity.
    rewrite translate_ret; reflexivity.
  Qed.

  Lemma interp_helix_bind' :
    forall T U E mem (t: itree Event T) (k: T -> itree Event U),
      @interp_helix _ E (ITree.bind t k) mem ≈
                    bind (interp_helix t mem) (fun '(mem',v) => interp_helix (k v) mem').
  Proof.
    intros; unfold interp_helix.
    cbn.
    rewrite interp_Mem_bind, interp_fail_bind, translate_bind.
    eapply eutt_eq_bind; intros [[]|]; cbn.
    reflexivity.
    rewrite translate_ret; reflexivity.
  Qed.

  Lemma interp_helix_MemLU :
    forall {E} str mem m x,
      memory_lookup mem x ≡ Some m ->
      interp_helix (E := E) (trigger (MemLU str x)) mem ≈ Ret (Some (mem,m)).
  Proof.
    intros * EQ.
    unfold interp_helix.
    setoid_rewrite interp_Mem_vis_eqit.
    cbn*; rewrite EQ; cbn.
    rewrite Eq.bind_ret_l, tau_eutt.
    cbn; rewrite interp_Mem_ret, interp_fail_Ret, translate_ret.
    reflexivity.
  Qed.

  Lemma interp_helix_MemSet :
    forall {E} dst blk mem,
      interp_helix (E := E) (trigger (MemSet dst blk)) mem ≈ Ret (Some (memory_set mem dst blk, tt)).
  Proof.
    intros.
    unfold interp_helix.
    setoid_rewrite interp_Mem_vis_eqit.
    cbn. rewrite Eq.bind_ret_l, tau_eutt.
    cbn; rewrite interp_Mem_ret, interp_fail_Ret, translate_ret.
    reflexivity.
  Qed.

End InterpHelix.

(* Autorewrite and hint databases for more modular rewriting. *)
(* "Normalizing" rewriting hint database. *)
Hint Rewrite @translate_bind : itree.
Hint Rewrite @interp_bind : itree.
Hint Rewrite @bind_bind : itree.
Hint Rewrite @bind_ret_l : itree.

Hint Rewrite @translate_ret : itree.
Hint Rewrite @interp_ret : itree.

Hint Rewrite @translate_trigger : itree.
Hint Rewrite @interp_trigger : itree.

Hint Rewrite interp_cfg_to_L3_bind : vellvm.
Hint Rewrite interp_cfg_to_L3_ret : vellvm.
Hint Rewrite interp_cfg_to_L3_GR : vellvm.
Hint Rewrite interp_cfg_to_L3_LR : vellvm.

Hint Rewrite @lookup_E_to_exp_E_Global : vellvm.
Hint Rewrite @lookup_E_to_exp_E_Local : vellvm.
Hint Rewrite @subevent_subevent : vellvm.
Hint Rewrite @exp_E_to_instr_E_Global : vellvm.
Hint Rewrite @exp_E_to_instr_E_Local : vellvm.
Hint Rewrite @typ_to_dtyp_equation : vellvm.
Hint Rewrite denote_code_nil : vellvm.
Hint Rewrite denote_code_singleton : vellvm.

Hint Rewrite interp_helix_bind : helix.
Hint Rewrite interp_helix_Ret : helix.
Hint Rewrite @interp_helix_MemLU : helix.

Tactic Notation "rauto:R" :=
  repeat (
      match goal with
      | |- eutt _ ?t _ => let x := fresh in remember t as x;
                                          autorewrite with itree;
                                          autorewrite with vellvm;
                                          autorewrite with helix; subst x
      end
    ).

Tactic Notation "rauto:L" :=
  repeat (
      match goal with
      | |- eutt _ _ ?t => let x := fresh in remember t as x;
                                          autorewrite with itree;
                                          autorewrite with vellvm;
                                          autorewrite with helix; subst x
      end
    ).

Tactic Notation "rauto" := (repeat (autorewrite with itree; autorewrite with vellvm; autorewrite with helix)).
Tactic Notation "rauto" "in" hyp(h) :=
  (repeat (autorewrite with itree in h; autorewrite with vellvm in h; autorewrite with helix in h)).

(* We derive lemmas specialized to [interp_helix] to reason about [no_failure] and easily derive contradictions *)
Section Interp_Helix_No_Failure.

  Lemma no_failure_helix_Ret : forall E X x m,
    no_failure (interp_helix (X := X) (E := E) (Ret x) m).
  Proof.
    intros.
    rewrite interp_helix_ret. apply eutt_Ret; intros abs; inv abs.
  Qed.

  Lemma failure_helix_throw : forall E X s m,
      ~ no_failure (interp_helix (X := X) (E := E) (throw s) m).
  Proof.
    intros * abs.
    unfold Exception.throw in *.
    unfold interp_helix in *.
    setoid_rewrite interp_Mem_vis_eqit in abs.
    unfold pure_state in *; cbn in *.
    rewrite interp_fail_bind in abs.
    rewrite interp_fail_vis in abs.
    cbn in *.
    rewrite Eq.bind_bind, !bind_ret_l in abs.
    rewrite translate_ret in abs.
    eapply eutt_Ret in abs.
    apply abs; auto.
  Qed.

  Lemma failure_helix_throw' : forall E Y X s (k : Y -> _) m,
      ~ no_failure (interp_helix (X := X) (E := E) (ITree.bind (throw s) k) m).
  Proof.
    intros * abs.
    rewrite interp_helix_bind in abs.
    eapply no_failure_bind_prefix, failure_helix_throw in abs; auto.
  Qed.

    Lemma no_failure_helix_bind_prefix : forall {E X Y} (t : itree _ X) (k : X -> itree _ Y) m,
        no_failure (interp_helix (E := E) (ITree.bind t k) m) ->
        no_failure (interp_helix (E := E) t m).
    Proof.
      intros * NOFAIL.
      rewrite interp_helix_bind in NOFAIL.
      eapply no_failure_bind_prefix; eapply NOFAIL.
    Qed.

    Lemma no_failure_helix_bind_continuation : forall {E X Y} (t : itree _ X) (k : X -> itree _ Y) m,
        no_failure (interp_helix (E := E) (ITree.bind t k) m) ->
        forall u m', Returns (E := E) (Some (m',u)) (interp_helix t m) -> 
                no_failure (interp_helix (E := E) (k u) m').
    Proof.
      intros * NOFAIL * ISRET.
      rewrite interp_helix_bind in NOFAIL.
      eapply no_failure_bind_cont in NOFAIL; eauto.
      apply NOFAIL.
    Qed.

    Lemma no_failure_Ret: forall {E X Y} (v : X) (k : X -> itree Event Y) m,
        no_failure (E := E) (interp_helix (ITree.bind (Ret v) k) m) -> no_failure (E := E) (interp_helix (k v) m) .
    Proof.
      intros * NOFAIL.
      rewrite interp_helix_bind, interp_helix_Ret, bind_ret_l in NOFAIL; assumption.
    Qed.


    Lemma Returns_helix_throw :
      forall E X x s m,
      not (@Returns E _ (Some x) (@interp_helix X E (throw s) m)).
    Proof.
      intros. red.
      unfold interp_helix. intros abs.
      setoid_rewrite interp_Mem_vis_eqit in abs.
      unfold pure_state in *; cbn in *.
      rewrite interp_fail_bind in abs.
      rewrite interp_fail_vis in abs.
      cbn in *.
      rewrite Eq.bind_bind, !bind_ret_l in abs.
      rewrite translate_ret in abs.
      apply Returns_Ret in abs.
      inversion abs.
    Qed.

    Lemma Returns_helix_throw' : forall E Y X s (k : Y -> _) m x,
        ~ (@Returns E _ (Some x) (interp_helix (X := X) (E := E) (ITree.bind (throw s) k) m)).
    Proof.
      intros * abs.
      rewrite interp_helix_bind in abs.
      eapply Returns_bind_inversion in abs. destruct abs as (? & abs & ?).
      destruct x0. 2 : { apply Returns_Ret in H. inversion H. }
      apply Returns_helix_throw in abs. auto.
    Qed.

    Lemma no_failure_helix_LU : forall {E X} s a (k : _ -> itree _ X) m,
        no_failure (E := E) (interp_helix (ITree.bind (trigger (MemLU s a)) k) m) ->
        exists v,
          no_failure (E := E) (interp_helix (k v) m) /\ memory_lookup m a ≡ Some v.
    Proof.
      intros * NOFAIL.
      rewrite interp_helix_bind in NOFAIL.
      unfold interp_helix in NOFAIL.
      Transparent interp_Mem.
      unfold interp_Mem in NOFAIL.
      rewrite interp_state_trigger in NOFAIL.
      cbn* in *.
      simp.
      - unfold throw in *.
        rewrite interp_fail_vis in NOFAIL.
        cbn in *.
        rewrite bind_ret_l, translate_ret, bind_ret_l in NOFAIL.
        apply eutt_Ret in NOFAIL; contradiction NOFAIL; auto.
      - rewrite interp_fail_ret in NOFAIL.
        cbn in *; rewrite translate_ret, bind_ret_l in NOFAIL.
        eexists; split; eauto.
    Qed.

End Interp_Helix_No_Failure.

Opaque interp_Mem.
Opaque interp_helix.

Hint Resolve no_failure_helix_Ret : core.
Hint Resolve no_failure_helix_bind_prefix : core.
Hint Extern 4 (no_failure _) =>
(match goal with
 | h : no_failure (interp_helix (ITree.bind _ _) _) |- _ =>
   eapply no_failure_helix_bind_continuation in h
 end) : core.

Remove Hints
       abstract_algebra.AbGroup
       abstract_algebra.Bijective
       abstract_algebra.BoundedJoinSemiLattice
       abstract_algebra.BoundedJoinSemiLattice_Morphism
       abstract_algebra.BoundedSemiLattice
       abstract_algebra.Category
       abstract_algebra.CommutativeMonoid
       abstract_algebra.CommutativeSemiGroup
       abstract_algebra.DistributiveLattice
       abstract_algebra.Group
       abstract_algebra.Injective
       abstract_algebra.JoinSemiLattice
       abstract_algebra.JoinSemiLattice_Morphism
       abstract_algebra.Lattice
       abstract_algebra.Lattice_Morphism
       abstract_algebra.MeetSemiLattice
       abstract_algebra.MeetSemiLattice_Morphism
       abstract_algebra.Monoid
       abstract_algebra.Monoid_Morphism
       abstract_algebra.Ring
       abstract_algebra.SemiGroup
       abstract_algebra.SemiGroup_Morphism
       abstract_algebra.SemiLattice
       abstract_algebra.SemiRing
       abstract_algebra.SemiRing_Morphism
       abstract_algebra.Setoid
       abstract_algebra.Setoid_Morphism
       abstract_algebra.StrongSetoid
       abstract_algebra.StrongSetoid_BinaryMorphism
       abstract_algebra.StrongSetoid_Morphism
       abstract_algebra.Surjective
       abstract_algebra.abgroup_commutative
       abstract_algebra.abgroup_group
       abstract_algebra.arrow_equiv
       abstract_algebra.bijective_injective
       abstract_algebra.bijective_surjective
       abstract_algebra.bounded_join_semilattice
       abstract_algebra.bounded_join_slmor_monmor
       abstract_algebra.bounded_semilattice_idempotent
       abstract_algebra.bounded_semilattice_mon
       abstract_algebra.commonoid_commutative
       abstract_algebra.commonoid_mon
       abstract_algebra.comp_assoc
       abstract_algebra.comp_proper
       abstract_algebra.comsg_ass
       abstract_algebra.comsg_setoid
       abstract_algebra.dec_recip_proper
       abstract_algebra.decfield_nontrivial
       abstract_algebra.decfield_ring
       abstract_algebra.distr_lattice_lattice
       abstract_algebra.field_mult_ext
       abstract_algebra.field_nontrivial
       abstract_algebra.field_plus_ext
       abstract_algebra.field_ring
       abstract_algebra.field_strongsetoid
       abstract_algebra.group_monoid
       abstract_algebra.id_l
       abstract_algebra.id_r
       abstract_algebra.intdom_nontrivial
       abstract_algebra.intdom_nozeroes
       abstract_algebra.intdom_ring
       abstract_algebra.join_meet_absorption
       abstract_algebra.join_meet_distr_l
       abstract_algebra.join_semilattice
       abstract_algebra.join_slmor_sgmor
       abstract_algebra.lattice_join
       abstract_algebra.lattice_meet
       abstract_algebra.latticemor_join_mor
       abstract_algebra.latticemor_meet_mor
       abstract_algebra.meet_join_absorption
       abstract_algebra.meet_semilattice
       abstract_algebra.meet_slmor_sgmor
       abstract_algebra.monmor_sgmor
       abstract_algebra.monoid_left_id
       abstract_algebra.monoid_right_id
       abstract_algebra.monoid_semigroup
       abstract_algebra.negate_l
       abstract_algebra.negate_proper
       abstract_algebra.negate_r
       abstract_algebra.recip_proper
       abstract_algebra.ring_dist
       abstract_algebra.ring_group
       abstract_algebra.ring_monoid
       abstract_algebra.semilattice_idempotent
       abstract_algebra.semilattice_sg
       abstract_algebra.semimult_monoid
       abstract_algebra.semiplus_monoid
       abstract_algebra.semiring_distr
       abstract_algebra.semiring_left_absorb
       abstract_algebra.semiringmor_mult_mor
       abstract_algebra.semiringmor_plus_mor
       abstract_algebra.setoid_eq
       abstract_algebra.sg_ass
       abstract_algebra.sg_op_proper
       abstract_algebra.sg_setoid
       abstract_algebra.sgmor_setmor
       abstract_algebra.sm_proper
       abstract_algebra.strong_semiringmor_sr_mor
       abstract_algebra.strong_semiringmor_strong_mor
       abstract_algebra.strong_setoid_cotrans
       abstract_algebra.strong_setoid_irreflexive
       abstract_algebra.strong_setoid_symmetric
       additional_operations.ModEuclid MonadIter categories.Mono
       equiv_default_relation
       minmax.LatticeOrder_instance_0
       orders.join_sl_order
       orders.lattice_order_join
       orders.lattice_order_meet
       orders.le_total
       orders.po_preorder
       orders.srorder_po
       orders.strict_po_po
       orders.total_order_po
       semirings.FullPseudoOrder_instance_0
       strong_setoids.binary_strong_morphism_proper
       workarounds.equivalence_proper : typeclass_instances.


Module Helix_Notations.
  Notation "'ℐ' '(' t ')' m" := (interp_helix t m) (only printing, at level 10).
  Notation "'Name' i" := (Name (_ @@ string_of_nat (local_count i))) (only printing, at level 0, format "'Name' i").
  Notation "'Name' i" := (Name (_ @@ string_of_nat (block_count i))) (only printing, at level 0, format "'Name' i").
  Notation "'Name' i" := (Name (_ @@ string_of_nat (void_count i))) (only printing, at level 0, format "'Name' i").

End Helix_Notations.

Module ProofMode.

  (* Include ITreeNotations. *)
  Notation "t1 ;; k" := (ITree.bind t1 k) (format "t1 ;; '//' k", at level 61, right associativity, only printing) : itree_scope.
  Include VIR_Notations.
  Include VIR_denotation_Notations.
  Include eutt_Notations.
  Include Helix_Notations.
  Notation "g '[' r ':' x ']'" := (alist_add r x g) (only printing, at level 10). 

  (* Notation "⟦ b , p , c , t ⟧" := (fmap _ (mk_block b p c t _)) (only printing).  *)
  (* Notation "'denote_blocks' '...' id " := (denote_bks _ id) (at level 10,only printing).  *)
  (* Notation "'IRS' ctx" := (mkIRState _ _ _ ctx) (only printing, at level 10).  *)
  (* Notation "x" := (with_cfg x) (only printing, at level 10).  *)
  (* Notation "x" := (with_mcfg x) (only printing, at level 10).  *)
  (* (* Notation "'CODE' c" := (denote_code c) (only printing, at level 10, format "'CODE' '//' c"). *) *)
  (* Notation "c" := (denote_code c) (only printing, at level 10). *)
  (* (* Notation "'INSTR' i" := (denote_instr i) (only printing, at level 10, format "'INSTR' '//' i"). *) *)
  (* Notation "i" := (denote_instr i) (only printing, at level 10). *)
  (* Notation "x" := (translate exp_E_to_instr_E (denote_exp _ x)) (only printing, at level 10).  *)
  
End ProofMode.

Ltac hred :=
  let R := fresh
  in eutt_hide_rel_named R;
     let X := fresh
     in eutt_hide_right_named X;
        repeat (rewrite ?interp_helix_bind, ?interp_helix_Ret, ?bind_ret_l);
        subst R; subst X.

Ltac hstep := first [rewrite interp_helix_MemSet | rewrite interp_helix_MemLU; cycle 1 | idtac].

Ltac vred := vred_r.
Ltac hvred := hred; vred_r.

Require Import LibHyps.LibHyps.

Ltac clean_goal :=
  try match goal with
      | h1 : incVoid _ ≡ _,
             h2 : incVoid _ ≡ _,
                  h3 : incVoid _ ≡ _
        |- _ => move h1 at top; move h2 at top; move h3 at top
      | h1 : incVoid _ ≡ _, h2 : incVoid _ ≡ _ |- _ => move h1 at top; move h2 at top
      | h : incVoid _ ≡ _ |- _ => move h at top
      end;

  try match goal with
      | h1 : incLocal _ ≡ _,
             h2 : incLocal _ ≡ _,
                  h3 : incLocal _ ≡ _
        |- _ => move h1 at top; move h2 at top; move h3 at top
      | h1 : incLocal _ ≡ _, h2 : incLocal _ ≡ _ |- _ => move h1 at top; move h2 at top
      | h : incLocal _ ≡ _ |- _ => move h at top
      end;

  try match goal with
      | h1 : incBlockNamed _ _ ≡ _,
             h2 : incBlockNamed _ _ ≡ _,
                  h3 : incBlockNamed _ _ ≡ _
        |- _ => move h1 at top; move h2 at top; move h3 at top
      | h1 : incBlockNamed _ _ ≡ _, h2 : incBlockNamed _ _ ≡ _ |- _ => move h1 at top; move h2 at top
      | h : incBlockNamed _ _ ≡ _ |- _ => move h at top
      end;

  onAllHyps move_up_types.

Section Helix_Mem_Extra_Lemmas.

  Lemma mem_lookup_mem_add_neq :
    forall x y v bk,
      x ≢ y ->
      mem_lookup x (mem_add y v bk) ≡ mem_lookup x bk.
  Proof.
    intros x y v bk H.
    Transparent mem_lookup mem_add.
    cbn.
    Opaque mem_lookup mem_add.
    rewrite Memory.NM.Raw.Proofs.add_find; eauto.
    assert (match OrderedTypeEx.Nat_as_OT.compare x y with
            | OrderedType.EQ _ => Some v
            | _ => Memory.NM.Raw.find x (Memory.NM.this bk)
            end ≡ Memory.NM.Raw.find x (Memory.NM.this bk)).
    { break_match; try reflexivity.
      red in e. contradiction.
    }
    setoid_rewrite H0.
    reflexivity.
    apply Memory.NM.is_bst.
  Qed.

  Lemma mem_lookup_mem_add_eq :
    forall x v bk,
      mem_lookup x (mem_add x v bk) ≡ Some v.
  Proof.
    intros x v bk.
    Transparent mem_lookup mem_add.
    cbn.
    Opaque mem_lookup mem_add.
    rewrite Memory.NM.Raw.Proofs.add_find.
    break_match; try reflexivity;
      red in l; lia.
    apply Memory.NM.is_bst.
  Qed.

  Lemma memory_lookup_memory_set_eq :
    forall x bk m,
      memory_lookup (memory_set m x bk) x ≡ Some bk.
  Proof.
    intros x bk m.
    Transparent memory_lookup memory_set.
    unfold memory_lookup, memory_set.
    Opaque memory_lookup memory_set.
    setoid_rewrite Memory.NM.Raw.Proofs.add_find.
    break_match; try reflexivity; red in l; lia.
    apply Memory.NM.is_bst.
  Qed.

  Lemma memory_lookup_memory_set_neq :
    forall m x y bk,
      x ≢ y ->
      memory_lookup (memory_set m x bk) y ≡ memory_lookup m y.
  Proof.
    intros m x y bk H.
    Transparent memory_lookup memory_set.
    unfold memory_lookup, memory_set.
    Opaque memory_lookup memory_set.
    setoid_rewrite Memory.NM.Raw.Proofs.add_find.
    break_match; try reflexivity.
    red in e. clear Heqc. symmetry in e. contradiction.
    apply Memory.NM.is_bst.
  Qed.

End Helix_Mem_Extra_Lemmas.

Lemma repr_of_nat_to_nat :
  forall x,
    repr (Z.of_nat (MInt64asNT.to_nat x)) ≡ x.
Proof.
  intros x.
  cbn.
  unfold MInt64asNT.to_nat.
  cbn.
  rewrite Znat.Z2Nat.id, repr_intval; auto.
  destruct (Int64.intrange x); lia.
Qed.

Lemma to_nat_unsigned :
  forall x y,
    MInt64asNT.to_nat x ≢ MInt64asNT.to_nat y ->
    DynamicValues.Int64.unsigned (DynamicValues.Int64.repr (Z.of_nat (MInt64asNT.to_nat x))) ≢ DynamicValues.Int64.unsigned (DynamicValues.Int64.repr (Z.of_nat (MInt64asNT.to_nat y))).
Proof.
  intros x y H.
  repeat rewrite repr_of_nat_to_nat.
  intros CONTRA.
  unfold DynamicValues.Int64.unsigned, DynamicValues.Int64.intval in CONTRA.
  destruct x, y.
  unfold MInt64asNT.to_nat in *.
  unfold Z.to_nat in *.
  cbn in H.
  apply H.
  break_match; subst; reflexivity.
Qed.

(* TODO: prove this *)
Lemma from_Z_intval :
  forall sz i,
    MInt64asNT.from_Z sz ≡ inr i ->
    sz ≡ Int64.intval i.
Proof.
  intros sz i H.
Admitted.

Arguments alist_add : simpl never.

