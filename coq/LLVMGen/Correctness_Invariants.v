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

Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.misc.decision.

Require Import Omega.

Set Implicit Arguments.
Set Strict Implicit.

Import MDSHCOLOnFloat64.
Import D.
Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

(* A couple of notations to avoid ambiguities while not having to worry about imports and qualified names *)
Notation memoryV := memory_stack.
Notation memoryH := MDSHCOLOnFloat64.memory.

Ltac splits :=
  repeat match goal with
           |- _ /\ _ => split
         end.

(* TODO: move this *)
Ltac match_rewrite :=
  match goal with
  | H : (?X ≡ ?v) |-
    context [ match ?X with | _ => _ end] =>
    rewrite H
  end.


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
  Definition E_mcfg : Type -> Type := (ExternalCallE +' PickE +' UBE +' DebugE +' FailureE) +' (StaticFailE +' DynamicFailE).
  (* Joined set of residual events for cfgs *)
  Definition E_cfg : Type -> Type := (CallE +' PickE +' UBE +' DebugE +' FailureE) +' (StaticFailE +' DynamicFailE).

  (* We define the translations by injection *)
  Notation "'with_err_LT'" := (@translate (ExternalCallE +' PickE +' UBE +' DebugE +' FailureE) E_mcfg inl_).

  Notation "'with_err_LB'" := (@translate (CallE +' PickE +' UBE +' DebugE +' FailureE) E_cfg inl_).

  Notation "'with_err_RT'" := (@translate (StaticFailE +' DynamicFailE) E_mcfg inr_).

  Notation "'with_err_RB'" := (@translate (StaticFailE +' DynamicFailE) E_cfg inr_).

  (* We therefore have the following resulting denotation functions. *)
  (* On the Vellvm side, for [mcfg]: *)
  Definition semantics_llvm_mcfg p : itree E_mcfg _ := with_err_LT (model_to_L3 DTYPE_Void "main" main_args helix_intrinsics p).
  (* Which get lifted to [toplevel_entity] as usual: *)
  Definition semantics_llvm (prog: list (toplevel_entity typ (LLVMAst.block typ * list (LLVMAst.block typ)))) :=
    semantics_llvm_mcfg (mcfg_of_tle prog).

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
    '(data, σ) <- denote_initFSHGlobals data p.(globals) ;;
    xindex <- trigger (MemAlloc p.(i));;
    yindex <- trigger (MemAlloc p.(o));;
    let '(data, x) := constMemBlock (MInt64asNT.to_nat p.(i)) data in
    trigger (MemSet xindex x);;

    let σ := List.app σ [DSHPtrVal yindex p.(o); DSHPtrVal xindex p.(i)] in
    denoteDSHOperator σ p.(op);;
    bk <- trigger (MemLU "denote_FSHCOL" yindex);;
    lift_Derr (mem_to_list "Invalid output memory block" (MInt64asNT.to_nat p.(o)) bk).

  (* Finally, the semantics of FSHCOL for the top-level equivalence *)
  Definition semantics_FSHCOL (p: FSHCOLProgram) data : itree E_mcfg (memoryH * list binary64) :=
    with_err_RT (interp_Mem (denote_FSHCOL p data) memory_empty).

End EventTranslation.
Notation "'with_err_LT'" := (@translate (ExternalCallE +' PickE +' UBE +' DebugE +' FailureE) E_mcfg inl_).
Notation "'with_err_LB'" := (@translate (CallE +' PickE +' UBE +' DebugE +' FailureE) E_cfg inl_).
Notation "'with_err_RT'" := (@translate (StaticFailE +' DynamicFailE) E_mcfg inr_).
Notation "'with_err_RB'" := (@translate (StaticFailE +' DynamicFailE) E_cfg inr_).
Notation "'interp_cfg'"  := (interp_cfg_to_L3 helix_intrinsics).
Notation "'interp_mcfg'" := (interp_to_L3 helix_intrinsics).

(* Facilities to refer to the return types of the various pieces of denotations we manipulate *)

Section StateTypes.

  Local Open Scope type_scope.

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

(* Facilities to refer to the type of relations used during the simulations of various pieces of denotions we manipulate *)
(* TODOYZ: Think about those, rename. *)
Section RelationTypes.

  (** Relation of memory states which must be held for
      intialization steps *)
  Definition Rel_cfg: Type
    := memoryH -> config_cfg -> Prop.

  (** Relation of memory states which must be held for
      intialization steps *)
  Definition Rel_mcfg: Type
    := memoryH -> config_mcfg -> Prop.

  (** Type of bisimulation relations between DSHCOL and VIR internal to CFG states,
      parameterized by the types of the computed values.
   *)
  Definition Rel_cfg_T (TH TV: Type): Type
    := memoryH * TH -> config_cfg_T TV -> Prop.

  (* Lifting a relation on memory states to one encompassing returned values by ignoring them *)
  Definition lift_Rel_cfg (R: Rel_cfg) (TH TV: Type): Rel_cfg_T TH TV :=
    fun '(memH,_) '(memV,(l,(g,_))) => R memH (memV,(l,g)).

  Definition lift_pure_cfg (P : Prop) {TH TV : Type} : Rel_cfg_T TH TV :=
    fun _ _ => P.

  (* Lifting a relation on results to one encompassing states by ignoring them *)
  Definition lift_Rel_res_cfg {TH TV: Type} (R: TH -> TV -> Prop): Rel_cfg_T TH TV :=
    fun '(_,vh) '(_,(_,(_,vv))) => R vh vv.

  (** Type of bisimulation relations between DSHCOL and VIR internal to CFG states,
      parameterized by the types of the computed values.
   *)
  Definition Rel_mcfg_T (TH TV: Type): Type
    := memoryH * TH -> config_mcfg_T TV -> Prop.

  Definition lift_Rel_mcfg (R: Rel_mcfg) (TH TV: Type): Rel_mcfg_T TH TV :=
    fun '(memH,_) '(memV,(l,(g,_))) => R memH (memV,(l,g)).

  Definition lift_pure_mcfg (P : Prop) {TH TV : Type} : Rel_mcfg_T TH TV :=
    fun _ _ => P.

  (** Type of bisimulation relation between DSHCOL and LLVM states.
    This relation could be used for fragments of CFG [cfg].
   *)
  Definition Type_R_partial: Type
    := memoryH * unit -> config_res_cfg -> Prop.

  (** Type of bisimulation relation between DSHCOL and LLVM states.
      This relation could be used for "closed" CFG [mcfg].
   *)
  Definition Type_R_full: Type
    := memoryH * (list binary64) -> config_res_mcfg -> Prop.

End RelationTypes.
Arguments lift_Rel_cfg R {_ _}.
Arguments lift_pure_cfg /.
Arguments lift_pure_cfg /.

Ltac introR :=
  intros [?memH ?vH] (?memV & ?l & ?g & ?vV) ?PRE.

Ltac unfolder_vellvm       := unfold Traversal.Endo_id.
Ltac unfolder_vellvm_hyp h := unfold Traversal.Endo_id in h.
Ltac unfolder_vellvm_all   := unfold Traversal.Endo_id in *.

Ltac unfolder_helix       := unfold mem_lookup_err, memory_lookup_err, ErrorWithState.option2errS, lift_Serr, Int64_eq_or_cerr, Z_eq_or_cerr,ErrorWithState.err2errS,Z_eq_or_err, context_lookup, trywith.
Ltac unfolder_helix_hyp h := unfold mem_lookup_err, memory_lookup_err, ErrorWithState.option2errS, lift_Serr, Int64_eq_or_cerr, Z_eq_or_cerr,ErrorWithState.err2errS,Z_eq_or_err, context_lookup, trywith in h.
Ltac unfolder_helix_all   := unfold mem_lookup_err, memory_lookup_err, ErrorWithState.option2errS, lift_Serr, Int64_eq_or_cerr, Z_eq_or_cerr,ErrorWithState.err2errS,Z_eq_or_err, context_lookup, trywith in *.

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

Ltac simp := repeat (inv_sum || inv_option || break_and || break_match_hyp).

Ltac abs_by H :=
  exfalso; eapply H; now eauto.

Section WF_IRState.

  (**
     The compiler maintains a sort of typing context named [IRState].
     This typing context should soundly reflect the content of the [evalContext],
     injecting the types from [DSHCOL] to [VIR].
   *)

  Definition getWFType (id : ident) (t: DSHType): typ :=
    match id, t with
    | ID_Local _  , DSHnat   => IntType
    | ID_Global _ , DSHnat   => TYPE_Pointer IntType
    | ID_Local _  , DSHCType => TYPE_Double
    | ID_Global _ , DSHCType => TYPE_Pointer TYPE_Double
    | _           , DSHPtr n => TYPE_Pointer (TYPE_Array (Int64.intval n) TYPE_Double)
    end.

  (* True if σ typechecks in Γ *)
  Definition evalContext_typechecks (σ : evalContext) (Γ : list (ident * typ)) : Prop :=
    forall v n, nth_error σ n ≡ Some v ->
           exists id, (nth_error Γ n ≡ Some (id, getWFType id (DSHType_of_DSHVal v))).

  Definition WF_IRState (σ : evalContext) (s : IRState) : Prop :=
    evalContext_typechecks σ (Γ s).

  Lemma WF_IRState_lookups :
    forall σ s n v id τ,
      WF_IRState σ s ->
      nth_error (Γ s) n ≡ Some (id, τ) ->
      nth_error σ n ≡ Some v ->
      τ ≡ getWFType id (DSHType_of_DSHVal v).
  Proof.
    intros * WF LU_IR LU_SIGMA.
    apply WF in LU_SIGMA; destruct LU_SIGMA as (id' & LU); rewrite LU in LU_IR; inv LU_IR.
    reflexivity.
  Qed.

  Lemma WF_IRState_one_of_local_type:
    forall σ x τ s n v,
      WF_IRState σ s ->
      nth_error (Γ s) n ≡ Some (ID_Local x,τ) ->
      nth_error σ n ≡ Some v ->
      τ ≡ IntType \/
      τ ≡ TYPE_Double \/
      exists k, τ ≡ TYPE_Pointer (TYPE_Array (Int64.intval k) TYPE_Double).
  Proof.
    intros * WF LU LU'.
    eapply WF in LU'; destruct LU' as (id & LU''); rewrite LU in LU''; inv LU''.
    cbn; break_match_goal; eauto.
  Qed.

  Lemma WF_IRState_one_of_global_type:
    forall σ x τ s n v,
      WF_IRState σ s ->
      nth_error (Γ s) n ≡ Some (ID_Global x,τ) ->
      nth_error σ n ≡ Some v ->
      τ ≡ TYPE_Pointer IntType \/
      τ ≡ TYPE_Pointer TYPE_Double \/
      exists k, τ ≡ TYPE_Pointer (TYPE_Array (Int64.intval k) TYPE_Double).
  Proof.
    intros * WF LU LU'.
    edestruct WF as (id & LU''); eauto.
    rewrite LU in LU''; inv LU''.
    cbn in *.
    break_match_goal; eauto.
  Qed.

End WF_IRState.

Ltac abs_by_WF :=
  match goal with
  | h  : nth_error (Γ ?s) _ ≡ ?rhs,
    h': @nth_error DSHVal ?σ _ ≡ ?rhs'
    |- _ =>
    match rhs with
    | Some (?id,?τ) =>
      match rhs' with
      | None => fail
                 (*
        let LUP    := fresh "LUP" in
        let val    := fresh "val" in
        let CONTRA := fresh "CONTRA" in
        epose proof (context_lookup_succeeds _ _ _ h) as (val & LUP & CONTRA);
        rewrite h' in CONTRA;
        discriminate CONTRA *)
      | Some ?val =>
        let WF := fresh "WF" in
        assert (WF : WF_IRState σ s) by eauto;
        let H := fresh in pose proof (WF_IRState_lookups _ WF h h') as H; now (destruct id; inv H)
      end
    | None =>
      match rhs' with
      | None => fail
        (* exfalso; eapply WF_IRState_lookup_cannot_fail_st; now eauto *)
      | Some ?val => fail
      end
    end
  | h : nth_error (Γ ?s) _ ≡ Some (?id,?τ) |- _ =>
    match id with
    | ID_Local _ =>
      eapply WF_IRState_one_of_local_type in h; eauto;
      now (let EQ := fresh in destruct h as [EQ | [EQ | [? EQ]]]; inv EQ)
    | ID_Global _ =>
      eapply WF_IRState_one_of_global_type in h; eauto;
      now (let EQ := fresh in destruct h as [EQ | [EQ | [? EQ]]]; inv EQ)
    end
   end.

(* TODOYZ : MOVE *)
Definition conj_rel {A B : Type} (R S: A -> B -> Prop): A -> B -> Prop :=
  fun a b => R a b /\ S a b.
Infix "⩕" := conj_rel (at level 85, right associativity).

Section SimulationRelations.

  (**
     We define in this section the principal simulation relations used:
     - At the top-level to relate full [FSHCOLProgram]s to the full Vellvm
     program resulting from their compilation: see [compiler_correct]
     - At the top-level to relate these same program after initialization of
     the runtime. (TODOYZ: Do we need one such?)
     - When relating operators to the sub-cfg resulting from their compilation:
     see [compile_FSHCOL_correct]

    These relations also get refined when related sub-structures of the operators,
    we define these refinements in the corresponding sections.
   *)

  (**
     Relation used to relate memories after the initialization phase.
     Recall: [Type_R_memory ≜ memoryH -> LLVM_memory_state_cfg -> Prop]
  *)

  (* Conversion from Helix values to VIR values *)
  Definition dvalue_of_int (v : Int64.int) : dvalue := DVALUE_I64 (DynamicValues.Int64.repr (Int64.intval v)).
  Definition dvalue_of_bin (v: binary64)   : dvalue := DVALUE_Double v.

  (* Check that a pair of [ident] and [dvalue] can be found in the appropriate environment *)
  Definition in_local_or_global
             (ρ : local_env) (g : global_env) (m : memoryV)
             (x : ident) (dv : dvalue) (τ : typ) : Prop
    := match x with
       | ID_Local  x => ρ @ x ≡ Some (dvalue_to_uvalue dv)
       | ID_Global x =>
         exists ptr τ',
         τ ≡ TYPE_Pointer τ' /\
         g @ x ≡ Some (DVALUE_Addr ptr) /\
         read m ptr (typ_to_dtyp [] τ') ≡ inr (dvalue_to_uvalue dv)
       end.

  (* Main memory invariant. Relies on Helix's evaluation context and the [IRState] built by the compiler.
     At any indices, the value and ident/types respectively found are related in that:
     - integers and floats have their translation in the appropriate VIR environment;
     - pointers have a corresponding pointer in the appropriate VIR environment such that they map on identical arrays
   *)
  Definition memory_invariant (σ : evalContext) (s : IRState) : Rel_cfg :=
    fun (mem_helix : MDSHCOLOnFloat64.memory) '(mem_llvm, (ρ,g)) =>
      forall (n: nat) v τ x,
        nth_error σ n ≡ Some v ->
        nth_error (Γ s) n ≡ Some (x,τ) ->
        match v with
        | DSHnatVal v   => in_local_or_global ρ g mem_llvm x (dvalue_of_int v) τ
        | DSHCTypeVal v => in_local_or_global ρ g mem_llvm x (dvalue_of_bin v) τ
        | DSHPtrVal ptr_helix ptr_size_helix =>
          exists bk_helix ptr_llvm,
          memory_lookup mem_helix ptr_helix ≡ Some bk_helix /\
          in_local_or_global ρ g mem_llvm x (DVALUE_Addr ptr_llvm) τ /\
          (forall i v, mem_lookup i bk_helix ≡ Some v ->
                  get_array_cell mem_llvm ptr_llvm i DTYPE_Double ≡ inr (UVALUE_Double v))
        end.

  (* Lookups in [genv] are fully determined by lookups in [Γ] and [σ] *)
  Lemma memory_invariant_GLU : forall σ s v id memH memV t l g n,
      memory_invariant σ s memH (memV, (l, g)) ->
      nth_error (Γ s) v ≡ Some (ID_Global id, TYPE_Pointer t) ->
      nth_error σ v ≡ Some (DSHnatVal n) ->
      exists ptr, Maps.lookup id g ≡ Some (DVALUE_Addr ptr) /\
             read memV ptr (typ_to_dtyp [] t) ≡ inr (dvalue_to_uvalue (DVALUE_I64 n)).
  Proof.
    intros * INV NTH LU; cbn* in *.
    eapply INV in LU; clear INV; eauto.
    destruct LU as (ptr & τ & EQ & LU & READ); inv EQ.
    exists ptr; split; auto.
    cbn in *.
    rewrite repr_intval in READ; auto.
  Qed.

  (* Lookups in [local_env] are fully determined by lookups in [Γ] and [σ] *)
  Lemma memory_invariant_LLU : forall σ s v id memH memV t l g n,
      memory_invariant σ s memH (memV, (l, g)) ->
      nth_error (Γ s) v ≡ Some (ID_Local id, t) ->
      nth_error σ v ≡ Some (DSHnatVal n) ->
      Maps.lookup id l ≡ Some (UVALUE_I64 n).
  Proof.
    intros * INV NTH LU; cbn* in *.
    eapply INV in LU; clear INV; eauto.
    unfold in_local_or_global, dvalue_of_int in LU.
    rewrite repr_intval in LU; auto.
  Qed.

  Hint Resolve memory_invariant_GLU memory_invariant_LLU : core.

  (* Lookups in [local_env] are fully determined by lookups in [vars] and [σ] *)
  Lemma memory_invariant_LLU_AExpr : forall σ s v id memH memV t l g f,
      memory_invariant σ s memH (memV, (l, g)) ->
      nth_error (Γ s) v ≡ Some (ID_Local id, t) ->
      nth_error σ v ≡ Some (DSHCTypeVal f) ->
      Maps.lookup id l ≡ Some (UVALUE_Double f).
  Proof.
    intros * INV NTH LU; cbn* in *.
    eapply INV in LU; clear INV; eauto.
    unfold in_local_or_global, dvalue_of_int in LU.
    cbn in LU; auto.
  Qed.

  (* Lookups in [genv] are fully determined by lookups in [vars] and [σ] *)
  Lemma memory_invariant_GLU_AExpr : forall σ s v id memH memV t l g f,
      memory_invariant σ s memH (memV, (l, g)) ->
      nth_error (Γ s) v ≡ Some (ID_Global id, TYPE_Pointer t) ->
      nth_error σ v ≡ Some (DSHCTypeVal f) ->
      exists ptr, Maps.lookup id g ≡ Some (DVALUE_Addr ptr) /\
             read memV ptr (typ_to_dtyp [] t) ≡ inr (dvalue_to_uvalue (DVALUE_Double f)).
  Proof.
    intros * INV NTH LU; cbn* in *.
    eapply INV in LU; clear INV; eauto.
    destruct LU as (ptr & τ & EQ & LU & READ); inv EQ.
    exists ptr; split; auto.
  Qed.

  Hint Resolve memory_invariant_GLU memory_invariant_LLU memory_invariant_LLU_AExpr memory_invariant_GLU_AExpr : core.

  Lemma memory_invariant_LLU_Ptr : forall σ s v id memH memV t l g m size,
      memory_invariant σ s memH (memV, (l, g)) ->
      nth_error (Γ s) v ≡ Some (ID_Local id, t) ->
      nth_error σ v ≡ Some (DSHPtrVal m size) ->
      exists (bk_h : mem_block) (ptr_v : Addr.addr),
        memory_lookup memH m ≡ Some bk_h
        /\ in_local_or_global l g memV (ID_Local id) (DVALUE_Addr ptr_v) t
        /\ (forall (i : Memory.NM.key) (v : binary64),
              mem_lookup i bk_h ≡ Some v -> get_array_cell memV ptr_v i DTYPE_Double ≡ inr (UVALUE_Double v)).
  Proof.
    intros * INV NTH LU; cbn* in *.
    eapply INV in LU; clear INV; eauto.
    auto.
  Qed.

  (** ** Fresh identifier generator invariant
      Low and high level invariants ensuring that calls to [incLocal] indeed generate fresh variables.
   *)
  Definition incLocal_fresh (l : local_env) (s : IRState) : Prop :=
    forall s' id, incLocal s ≡ inr (s',id) ->
             alist_fresh id l.

  Definition concrete_fresh_inv (s : IRState) : config_cfg -> Prop :=
    fun '(_, (l,g)) =>
      forall id v n, alist_In id l v -> n >= local_count s -> id <> Name ("l" @@ string_of_nat n).

  (* We need to preserve the concrete invariant, but it is sufficient to get the abstract one of interest *)
  Lemma concrete_fresh_fresh: forall s memV l g,
      concrete_fresh_inv s (memV,(l,g)) ->
      incLocal_fresh l s.
  Proof.
    intros * FRESH ? ? LU.
    unfold incLocal, incLocalNamed in LU; cbn in *; inv LU.
    unfold alist_fresh.
    match goal with
    | |- ?x ≡ None => destruct x eqn:EQ; auto; exfalso
    end.
    eapply FRESH; eauto.
  Qed.

  (** ** General state invariant
      The main invariant carried around combine the three properties defined:
      1. the memories satisfy the invariant;
      2. the [IRState] is well formed;
      3. the fresh ident generator is working properly.
   *)
  Record state_invariant (σ : evalContext) (s : IRState) (memH : memoryH) (configV : config_cfg) : Prop :=
    {
    mem_is_inv : memory_invariant σ s memH configV ;
    IRState_is_WF : WF_IRState σ s ;
    incLocal_is_fresh : concrete_fresh_inv s configV
    }.

  (**
   Lifting of [memory_invariant] to include return values in the relation.
   This relation is used to prove the correctness of the compilation of operators.
   The value on the Helix side is trivially [unit]. The value on the Vellvm-side however
   is non trivial, we will most likely have to mention it.
   *)
  (* TODO: Currently this relation just preserves memory invariant.
   Maybe it needs to do something more?
   *)
  Definition bisim_partial (σ : evalContext) (s : IRState) : Type_R_partial
    :=
      fun '(mem_helix, _) '(mem_llvm, x) =>
        let '(ρ, (g, _)) := x in
        memory_invariant σ s mem_helix (mem_llvm, (ρ, g)).

  (**
   Relation over memory and invariant for a full [cfg], i.e. to relate states at
   the top-level. lift_R_memory_mcfg
   Currently a simple lifting of [bisim_partial].
   *)
  Definition bisim_full (σ : evalContext) (s : IRState) : Type_R_full  :=
    fun '(mem_helix, _) mem_llvm =>
      let '(m, ((ρ,_), (g, v))) := mem_llvm in
      bisim_partial σ s (mem_helix, tt) (mk_config_cfg_T (inr v) (m, (ρ, g))).

  (** Relation bewteen the final states of evaluation and execution
    of DHCOL program.

    At this stage we do not care about memory or environemnts, and
    just compare return value of [main] function in LLVM with
    evaulation results of DSHCOL.
   *)
  Definition bisim_final (σ : evalContext) : Type_R_full :=
    fun '(_, h_result) '(_,(_,(_,llvm_result))) =>
      match llvm_result with
      | UVALUE_Array arr => @List.Forall2 _ _
                                         (fun ve de =>
                                            match de with
                                            | UVALUE_Double d =>
                                              Floats.Float.cmp Integers.Ceq d ve
                                            | _ => False
                                            end)
                                         h_result arr
      | _ => False
      end.

End SimulationRelations.

Section Ext_Local.

  (** When compiling expressions, we need to carry on the invariant that
      the meaning of the generated expression will be stable by execution of the
      intermediate code corresponding to the evaluation of the second operand.
      To this end, we rely on the fact that this code does not alter the configuration
      except to extend it with fresh bindings.
   *)
  Definition ext_local {R S}: memoryH -> config_cfg -> Rel_cfg_T R S :=
    fun mh '(mi,(li,gi)) '(mh',_) '(m,(l,(g,_))) => mh ≡ mh' /\ mi ≡ m /\ gi ≡ g /\ li ⊑ l.

 Lemma in_local_or_global_ext_local :
    forall ρ1 ρ2 g m x dv τ,
      in_local_or_global ρ1 g m x dv τ ->
      ρ1 ⊑ ρ2 ->
      in_local_or_global ρ2 g m x dv τ.
  Proof.
    unfold in_local_or_global; intros ? ? ? ? [] ? ? IN MONO; auto.
    apply MONO; auto.
  Qed.

  Lemma memory_invariant_ext_local :
    forall σ s memH memV ρ1 ρ2 g,
      memory_invariant σ s memH (memV, (ρ1, g)) ->
      ρ1 ⊑ ρ2 ->
      memory_invariant σ s memH (memV, (ρ2, g)).
  Proof.
    intros * INV MONO.
    red; intros * NTH NTH'.
    specialize (INV _ _ _ _ NTH NTH').
    destruct v; eauto.
    eapply in_local_or_global_ext_local; eauto.
    eapply in_local_or_global_ext_local; eauto.
    repeat destruct INV as (? & INV).
    do 3 eexists; splits; eauto.
    eapply in_local_or_global_ext_local; eauto.
  Qed.

End Ext_Local.

(* begin tactics *)

(* TODOYZ: This is a redefinition from [DSigmaHCOLITree]. To remove after proper reorganization into two files *)
(* TODOYZ: Actually even more so there should be a clean part of the tactics that do the generic structural
   rewriting, and a wrapper around it doing stuff specific to this denotation. We should only need the former
   here I believe *)
Ltac inv_mem_lookup_err :=
  unfold mem_lookup_err, trywith in *;
  break_match_hyp; cbn in *; try (inl_inr || inv_sum || inv_sum).

Ltac inv_memory_lookup_err :=
  unfold memory_lookup_err, trywith in *;
  break_match_hyp; cbn in *; try (inl_inr || inv_sum || inv_sum).

Ltac state_steps :=
  cbn;
  repeat (
      ((match goal with
        | |- ITree.bind (lift_Derr _) _ ≈ _ => break_match_goal; inv_memory_lookup_err; inv_option
        | |- ITree.bind (lift_Serr _) _ ≈ _ => break_match_goal; inv_memory_lookup_err; inv_option
        | |- ITree.bind (State.interp_state _ (lift_Derr _) _) _ ≈ _ => break_match_goal; inv_option
        | |- ITree.bind (State.interp_state _ (lift_Serr _) _) _ ≈ _ => break_match_goal; inv_option
        end) || state_step); cbn).


Ltac eutt_hide_left_named H :=
  match goal with
    |- eutt _ ?t _ => remember t as H
  end.

(* with hypothesis name provided *)
Tactic Notation "eutt_hide_left" ident(hypname) :=
  eutt_hide_left_named hypname.

(* with hypothesis name auto-generated *)
Tactic Notation "eutt_hide_left" :=
  let H := fresh "EL" in
  eutt_hide_left_named H.

Ltac eutt_hide_right_named H :=
  match goal with
    |- eutt _ _ ?t => remember t as H
  end.

(* with hypothesis name provided *)
Tactic Notation "eutt_hide_right" ident(hypname) :=
  eutt_hide_right_named hypname.

(* with hypothesis name auto-generated *)
Tactic Notation "eutt_hide_right" :=
  let H := fresh "ER" in
  eutt_hide_right_named H.

Ltac eutt_hide_rel_named H :=
  match goal with
    |- eutt ?t _ _ => remember t as H
  end.

(* with hypothesis name provided *)
Tactic Notation "eutt_hide_rel" ident(hypname) :=
  eutt_hide_rel_named hypname.

(* with hypothesis name auto-generated *)
Tactic Notation "eutt_hide_rel" :=
  let H := fresh "EU" in
  eutt_hide_rel_named H.

Ltac hide_string_goal :=
  match goal with
  | |- context [String ?x ?y] => remember (String x y)
  end.

Ltac hide_string_hyp H :=
  match type of H with
  | context [String ?x ?y] => remember (String x y)
  end.

Ltac hide_strings :=
  repeat (
      match goal with
      | h: context [String ?x ?y] |- _ => remember (String x y)
      | |- context [String ?x ?y] => remember (String x y)
      end).

(* end tactics *)

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

End Add_Comment.

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

(* We should do all reasoning about [interp_Mem] through these lemmas, let's make it Opaque to be sure that reduction does not mess with it *)
Global Opaque interp_Mem.
Global Opaque interp_cfg_to_L3.

Ltac break_and :=
  repeat match goal with
         | h: _ * _ |- _ => destruct h
         end.


  (** **
      TODO YZ : This needs to leave other hypotheses that H untouched
   *)
  Ltac simp_comp H :=
    cbn in H; unfolder in H;
    cbn in H; repeat (inv_sum || break_and || break_match_hyp).

  Lemma subevent_subevent : forall {E F} `{E -< F} {X} (e : E X),
      @subevent F F _ X (@subevent E F _ X e) ≡ subevent X e.
  Proof.
    reflexivity.
  Qed.

  (* We associate [bind]s to the right and dismiss leftmost [Ret]s *)
  (* NOTE YZ :
     To help debugging this automation, tactics take an argument [k] representing a boolean flag as an integer.
     I use [do k] to print debug messages if [k≡1].
     I then define two tactic notation [tac] and [tacD] setting the flag to 0 and 1 respectively.
     Question: is there anyway to avoid having to define an intermediate notation just to force k to be parsed as an integer
     rather than a constr?
   *)
  (* TODO YZ :
     Can we avoid the duplication of the tactics into a version for hypotheses and one for goals by being able
     to take a pattern of the form that rewrite admits?
   *)
  Ltac norm_monad_k t k :=
    match t with
    | context[ITree.bind ?t' _] =>
      match t' with
      | ITree.bind _ _ => rewrite bind_bind ;
                         do k idtac "bind_bind"
      | Ret _ => rewrite bind_ret_l ;
                do k idtac "bind_ret"
      end
    end.

  Tactic Notation "norm_monad_k'" constr(t) integer(k) := norm_monad_k t k.
  Tactic Notation "norm_monad" constr(t) := norm_monad_k' t 0.
  Tactic Notation "norm_monadD" constr(t) := norm_monad_k' t 1.

  (* Normalization in an hypothesis h instead of the goal *)
  Ltac norm_monad_hyp_k t h k :=
    match t with
    | context[ITree.bind ?t' _] =>
      match t' with
      | ITree.bind _ _ => rewrite bind_bind in h ; do k idtac "bind_bind"
      | Ret _ => rewrite bind_ret_l in h ; do k idtac "bind_ret"
      end
    end.

  Tactic Notation "norm_monad_hyp_k'" constr(t) hyp(h) integer(k) := norm_monad_hyp_k t h k.
  Tactic Notation "norm_monad_hyp" constr(t) hyp(h) := norm_monad_hyp_k' t h 0.
  Tactic Notation "norm_monad_hypD" constr(t) hyp(h) := norm_monad_hyp_k' t h 1.

  (* We push [translate]s and [interp]s inside of binds, run them through [Ret]s *)
  Ltac norm_interp_k t k :=
    match t with
    | context[translate _ (ITree.bind ?t' _)] => rewrite translate_bind ; do k idtac "trans_bind"
    | context[interp _ (ITree.bind ?t' _)] => rewrite interp_bind ; do k idtac "interp_bind"
    | context[translate _ (Ret _)] => rewrite translate_ret ; do k idtac "trans_ret"
    | context[interp _ (Ret _)] => rewrite interp_ret ; do k idtac "interp_ret"
    | context[translate _ (trigger ?e)] => rewrite (translate_trigger _ e) ; do k idtac "trans_trigger"
    | context[interp _ (trigger _)] => rewrite interp_trigger ; do k idtac "intepr_trigger"
    end.

  Tactic Notation "norm_interp_k'" constr(t) integer(k) := norm_interp_k t k.
  Tactic Notation "norm_interp" constr(t) := norm_interp_k' t 0.
  Tactic Notation "norm_interpD" constr(t) := norm_interp_k' t 1.

  Ltac norm_interp_hyp_k t h k :=
    match t with
    | context[translate _ (ITree.bind ?t' _)] => rewrite translate_bind in h ; do k idtac "trans_bind"
    | context[interp _ (ITree.bind ?t' _)] => rewrite interp_bind in h ; do k idtac "interp_bind"
    | context[translate _ (Ret _)] => rewrite translate_ret in h ; do k idtac "trans_ret"
    | context[interp _ (Ret _)] => rewrite interp_ret in h ; do k idtac "interp_ret"
    | context[translate _ (trigger ?e)] => rewrite (translate_trigger _ e) in h ; do k idtac "trans_trigger"
    | context[interp _ (trigger _)] => rewrite interp_trigger in h ; do k idtac "intepr_trigger"
    end.

  Tactic Notation "norm_interp_hyp_k'" constr(t) hyp(h) integer(k) := norm_interp_hyp_k t h k.
  Tactic Notation "norm_interp_hyp" constr(t) hyp(h) := norm_interp_hyp_k' t h 0.
  Tactic Notation "norm_interp_hypD" constr(t) hyp(h) := norm_interp_hyp_k' t h 1.

  (* We extend [norm_interp] with locally defined interpreters on the helix side *)
  Ltac norm_local_helix_k t k :=
    match t with
    | context[interp_Mem (ITree.bind ?t' _)] => rewrite interp_Mem_bind ; do k idtac "mem_bind"
    | context[interp_Mem (Ret _)] => rewrite interp_Mem_ret ; do k idtac "mem_ret"
    | context[interp_Mem (trigger (MemLU _ _)) _] =>
      rewrite interp_Mem_MemLU; do k idtac "mem_memlu"
    end.

  Tactic Notation "norm_local_helix_k'" constr(t) integer(k) := norm_local_helix_k t k.
  Tactic Notation "norm_local_helix" constr(t) := norm_local_helix_k' t 0.
  Tactic Notation "norm_local_helixD" constr(t) := norm_local_helix_k' t 1.

  Ltac norm_local_helix_hyp_k t h k :=
    match t with
    | context[interp_Mem (ITree.bind ?t' _)] => rewrite interp_Mem_bind in h ; do k idtac "mem_bind"
    | context[interp_Mem (Ret _)] => rewrite interp_Mem_ret in h ; do k idtac "mem_ret"
    end.

  Tactic Notation "norm_local_helix_hyp_k'" constr(t) hyp(h) integer(k) := norm_local_helix_hyp_k t h k.
  Tactic Notation "norm_local_helix_hyp" constr(t) hyp(h) := norm_local_helix_hyp_k' t h 0.
  Tactic Notation "norm_local_helix_hypD" constr(t) hyp(h) := norm_local_helix_hyp_k' t h 1.

  (* We extend [norm_interp] with locally defined interpreters on the vellvm side *)
  Ltac norm_local_vellvm_k t k :=
    match t with
    | context[interp_cfg_to_L3 _ (ITree.bind ?t' _)] => rewrite interp_cfg_to_L3_bind ; do k idtac "cfg_bind"
    | context[interp_cfg_to_L3 _ (Ret _)] => rewrite interp_cfg_to_L3_ret ; do k idtac "cfg_ret"
    | context[interp_cfg_to_L3 _ (trigger (GlobalRead _))] => rewrite interp_cfg_to_L3_GR ; do k idtac "cfg_GR"
    | context[interp_cfg_to_L3 _ (trigger (LocalRead _))] => rewrite interp_cfg_to_L3_LR ; do k idtac "cfg_LR"
    | context[lookup_E_to_exp_E (subevent _ _)] => (rewrite lookup_E_to_exp_E_Global || rewrite lookup_E_to_exp_E_Local); try rewrite subevent_subevent ; do k idtac "luexp"
    | context[exp_E_to_instr_E (subevent _ _)] => (rewrite exp_E_to_instr_E_Global || rewrite exp_E_to_instr_E_Local); try rewrite subevent_subevent ; do k idtac "expinstr"
    end.

  Tactic Notation "norm_local_vellvm_k'" constr(t) integer(k) := norm_local_vellvm_k t k.
  Tactic Notation "norm_local_vellvm" constr(t) := norm_local_vellvm_k' t 0.
  Tactic Notation "norm_local_vellvmD" constr(t) := norm_local_vellvm_k' t 1.

  Ltac norm_local_vellvm_hyp_k t h k :=
    match t with
    | context[interp_cfg_to_L3 _ (ITree.bind ?t' _)] => rewrite interp_cfg_to_L3_bind in h ; do k idtac "cfg_bind"
    | context[interp_cfg_to_L3 _ (Ret _)] => rewrite interp_cfg_to_L3_ret in h ; do k idtac "cfg_ret"
    | context[interp_cfg_to_L3 _ (trigger (GlobalRead _))] => rewrite interp_cfg_to_L3_GR in h ; do k idtac "cfg_GR" | context[interp_cfg_to_L3 _ (trigger (LocalRead _))] => rewrite interp_cfg_to_L3_LR in h ; do k idtac "cfg_LR"
    | context[lookup_E_to_exp_E (subevent _ _)] => (rewrite lookup_E_to_exp_E_Global in h || rewrite lookup_E_to_exp_E_Local in h); try rewrite subevent_subevent in h ; do k idtac "luexp"
    | context[exp_E_to_instr_E (subevent _ _)] => (rewrite exp_E_to_instr_E_Global in h || rewrite exp_E_to_instr_E_Local in h); try rewrite subevent_subevent in h ; do k idtac "expinstr"
    end.

  Tactic Notation "norm_local_vellvm_hyp_k'" constr(t) hyp(h) integer(k) := norm_local_vellvm_hyp_k t h k.
  Tactic Notation "norm_local_vellvm_hyp" constr(t) hyp(h) := norm_local_vellvm_hyp_k' t h 0.
  Tactic Notation "norm_local_vellvmD" constr(t) hyp(h) := norm_local_vellvm_hyp_k' t h 1.

  (**
     QUESTION YZ: the outer repeat does not have any effect. Why and how to fix?
   *)
  Ltac norm_h_k k :=
    match goal with
      |- eutt _ ?t _ =>
      repeat (
          repeat (norm_monad_k t k);
          repeat (norm_interp_k t k);
          repeat (norm_local_helix_k t k))
    end.
  Tactic Notation "norm_h_k'" integer(k) := norm_h_k k.
  Tactic Notation "norm_h" := norm_h_k' 0.
  Tactic Notation "norm_hD" := norm_h_k' 1.

  Ltac norm_h_hyp_k h k :=
    match type of h with
      eutt _ ?t _ =>
      repeat (
          repeat (norm_monad_hyp_k t h k);
          repeat (norm_interp_hyp_k t h k);
          repeat (norm_local_helix_hyp_k t h k))
    end.
  Tactic Notation "norm_h_hyp_k'" hyp(h) integer(k) := norm_h_hyp_k h k.
  Tactic Notation "norm_h" "in" hyp(h) := norm_h_hyp_k' h 0.
  Tactic Notation "norm_hD" "in" hyp(h) := norm_h_hyp_k' h 1.

  Ltac norm_v_k k :=
    match goal with
      |- eutt _ _ ?t =>
      repeat (
          repeat (norm_monad_k t k);
          repeat (norm_interp_k t k);
          repeat (norm_local_vellvm_k t k))
    end.
  Tactic Notation "norm_v_k'" integer(k) := norm_v_k k.
  Tactic Notation "norm_v" := norm_v_k' 0.
  Tactic Notation "norm_vD" := norm_v_k' 1.

  Ltac norm_v_hyp_k h k :=
    match type of h with
      eutt _ _ ?t =>
      repeat (
          repeat (norm_monad_hyp_k t h k);
          repeat (norm_interp_hyp_k t h k);
          repeat (norm_local_vellvm_hyp_k t h k))
    end.

  Tactic Notation "norm_v_hyp_k'" hyp(h) integer(k) := norm_v_hyp_k h k.
  Tactic Notation "norm_v" "in" hyp(h) := norm_v_hyp_k' h 0.
  Tactic Notation "norm_vD" "in" hyp(h) := norm_v_hyp_k' h 1.

Set Nested Proofs Allowed.

From ExtLib Require Import RelDec.
From Vellvm Require Import AstLib.

Lemma state_invariant_WF_IRState :
  forall σ s memH st, state_invariant σ s memH st -> WF_IRState σ s.
Proof.
  intros ? ? ? (? & ? & ?) [_ WF _]; auto.
Qed.

Lemma state_invariant_memory_invariant :
  forall σ s memH st, state_invariant σ s memH st -> memory_invariant σ s memH st.
Proof.
  intros ? ? ? (? & ? & ?) [INV _ _]; auto.
Qed.

Lemma ext_local_refl:
  forall {R S} memH memV l g n v,
    @ext_local R S memH (mk_config_cfg memV l g) (memH, n) (memV, (l, (g, v))).
Proof.
  intros; repeat split; reflexivity.
Qed.
Hint Resolve state_invariant_memory_invariant state_invariant_WF_IRState ext_local_refl: core.

(* YZ TODO MOVE *)
Lemma typ_to_dtyp_I : forall s i, typ_to_dtyp s (TYPE_I i) ≡ DTYPE_I i.
Proof.
  intros; rewrite typ_to_dtyp_equation; reflexivity.
Qed.

Lemma typ_to_dtyp_D : forall s, typ_to_dtyp s TYPE_Double ≡ DTYPE_Double.
Proof.
  intros; rewrite typ_to_dtyp_equation; reflexivity.
Qed.

Lemma typ_to_dtyp_D_array : forall n s, typ_to_dtyp s (TYPE_Array n TYPE_Double) ≡ DTYPE_Array n DTYPE_Double.
Proof.
  intros.
  rewrite typ_to_dtyp_equation.
  rewrite typ_to_dtyp_D.
  reflexivity.
Qed.

Lemma in_local_or_global_same_global : forall l g l' m id dv τ,
    in_local_or_global l g m (ID_Global id) dv τ ->
    in_local_or_global l' g m (ID_Global id) dv τ.
Proof.
  cbn; intros; auto.
Qed.

Lemma incLocal_Γ:
  forall s s' id,
    incLocal s ≡ inr (s', id) ->
    Γ s' ≡ Γ s.
Proof.
  intros; cbn in *; inv_sum; reflexivity.
Qed.

Lemma in_local_or_global_add_fresh_old :
  forall (id : raw_id) (l : local_env) (g : global_env) m (x : ident) dv dv' τ,
    x <> ID_Local id ->
    in_local_or_global l g m x dv τ ->
    in_local_or_global (alist_add id dv' l) g m x dv τ.
Proof.
  intros * INEQ LUV'.
  destruct x; cbn in *; auto.
  rewrite rel_dec_neq_false; try typeclasses eauto; [| intros ->; auto].
  rewrite remove_neq_alist; auto; try typeclasses eauto; intros ->; auto.
Qed.

Lemma fresh_no_lu :
  forall s s' id l g m x dv τ,
    incLocal s ≡ inr (s', id) ->
    incLocal_fresh l s ->
    in_local_or_global l g m x dv τ ->
    x <> ID_Local id.
Proof.
  intros * INC FRESH IN abs; subst.
  apply FRESH in INC.
  unfold alist_fresh in *.
  cbn in *; rewrite INC in IN; inv IN.
Qed.

Lemma append_factor_left : forall s s1 s2,
    s @@ s1 ≡ s @@ s2 ->
    s1 ≡ s2.
Proof.
  induction s as [| c s IH]; cbn; intros * EQ; auto.
  apply IH.
  inv EQ; auto.
Qed.

(* Inversion messes up my goal a bit too much, simpler to use this *)
Lemma Name_inj : forall s1 s2,
    Name s1 ≡ Name s2 ->
    s1 ≡ s2.
Proof.
  intros * EQ; inv EQ; auto.
Qed.

Global Opaque append.
(**
     [memory_invariant] is stable by fresh extension of the local environment.
 *)
Lemma state_invariant_add_fresh :
  forall σ s s' id memH memV l g v,
    incLocal s ≡ inr (s', id) ->
    state_invariant σ s memH (memV, (l, g)) ->
    state_invariant σ s' memH (memV, (alist_add id v l, g)).
Proof.
  intros * INC [MEM WF FRESH].
  split.
  - red; intros * LUH LUV.
    erewrite incLocal_Γ in LUV; eauto.
    generalize LUV; intros INLG;
      eapply MEM in INLG; eauto.
    break_match.
    + subst.
      eapply in_local_or_global_add_fresh_old; eauto.
      eapply fresh_no_lu; eauto.
      eapply concrete_fresh_fresh; eauto.
    + subst.
      eapply in_local_or_global_add_fresh_old; eauto.
      eapply fresh_no_lu; eauto.
      eapply concrete_fresh_fresh; eauto.
    + subst.
      repeat destruct INLG as [? INLG].
      do 3 eexists; splits; eauto.
      eapply in_local_or_global_add_fresh_old; eauto.
      eapply fresh_no_lu; eauto.
      eapply concrete_fresh_fresh; eauto.
  - unfold WF_IRState; erewrite incLocal_Γ; eauto; apply WF.
  - intros ? ? ? LU INEQ.
    clear MEM WF.
    destruct (rel_dec_p id0 id); [subst |];
      destruct s; cbn in INC; inv_sum; cbn in *.
    + intros abs.
      clear - INEQ abs.
      apply Name_inj, append_factor_left,string_of_nat_inj in abs; lia.
    + apply In_add_In_ineq in LU; eauto.
      eapply FRESH; eauto with arith.
Qed.

Lemma ext_local_subalist : forall {R S} memH memV l1 g vH vV l2,
    l1 ⊑ l2 ->
    @ext_local R S memH (mk_config_cfg memV l1 g) (memH, vH) (memV, (l2, (g, vV))).
Proof.
  intros * SUB; cbn; splits; auto.
Qed.

Lemma incVoid_Γ:
  forall s s' id,
    incVoid s ≡ inr (s', id) ->
    Γ s' ≡ Γ s.
Proof.
  intros; cbn in *; inv_sum; reflexivity.
Qed.

Lemma incVoid_local_count:
  forall s s' id,
    incVoid s ≡ inr (s', id) ->
    local_count s' ≡ local_count s.
Proof.
  intros; cbn in *; inv_sum; reflexivity.
Qed.

Lemma state_invariant_incVoid :
  forall σ s s' k memH stV,
    incVoid s ≡ inr (s', k) ->
    state_invariant σ s memH stV ->
    state_invariant σ s' memH stV.
Proof.
  intros * INC [MEM WF FRESH].
  split.
  - red; repeat break_let; intros * LUH LUV.
    erewrite incVoid_Γ in LUV; eauto.
    generalize LUV; intros INLG;
      eapply MEM in INLG; eauto.
  - unfold WF_IRState; erewrite incVoid_Γ; eauto; apply WF.
  - red; repeat break_let; erewrite incVoid_local_count; eauto.
Qed.

Lemma incLocal_local_count: forall s s' x,
    incLocal s ≡ inr (s',x) ->
    local_count s' ≡ S (local_count s).
Proof.
  intros; cbn in *; inv_sum; reflexivity.
Qed.

Lemma state_invariant_incLocal :
  forall σ s s' k memH stV,
    incLocal s ≡ inr (s', k) ->
    state_invariant σ s memH stV ->
    state_invariant σ s' memH stV.
Proof.
  intros * INC [MEM WF FRESH].
  split.
  - red; repeat break_let; intros * LUH LUV.
    erewrite incLocal_Γ in LUV; eauto.
    generalize LUV; intros INLG;
      eapply MEM in INLG; eauto.
  - unfold WF_IRState; erewrite incLocal_Γ; eauto; apply WF.
  - red; repeat break_let; intros ? ? ? LU INEQ.
    clear MEM WF.
    erewrite incLocal_local_count in INEQ; eauto.
    eapply FRESH; eauto with arith.
Qed.

Lemma incBlockNamed_Γ:
  forall s s' msg id,
    incBlockNamed msg s ≡ inr (s', id) ->
    Γ s' ≡ Γ s.
Proof.
  intros; cbn in *; inv_sum; reflexivity.
Qed.

Lemma incBlockNamed_local_count:
  forall s s' msg id,
    incBlockNamed msg s ≡ inr (s', id) ->
    local_count s' ≡ local_count s.
Proof.
  intros; cbn in *; inv_sum; reflexivity.
Qed.

Lemma state_invariant_incBlockNamed :
  forall σ s s' k msg memH stV,
    incBlockNamed msg s ≡ inr (s', k) ->
    state_invariant σ s memH stV ->
    state_invariant σ s' memH stV.
Proof.
  intros * INC [MEM WF FRESH].
  split.
  - red; repeat break_let; intros * LUH LUV.
    erewrite incBlockNamed_Γ in LUV; eauto.
    generalize LUV; intros INLG;
      eapply MEM in INLG; eauto.
  - unfold WF_IRState; erewrite incBlockNamed_Γ; eauto; apply WF.
  - red; repeat break_let; erewrite incBlockNamed_local_count; eauto.
Qed.

Global Opaque incBlockNamed.
Global Opaque incVoid.
Global Opaque incLocal.

Lemma unsigned_is_zero: forall a, Int64.unsigned a ≡ Int64.unsigned Int64.zero ->
                             a = Int64.zero.
Proof.
  intros a H.
  unfold Int64.unsigned, Int64.intval in H.
  repeat break_let; subst.
  destruct Int64.zero.
  inv Heqi0.
  unfold equiv, MInt64asNT.NTypeEquiv, Int64.eq, Int64.unsigned, Int64.intval.
  (* apply Coqlib.zeq_true. *)
(* Qed. *)
Admitted.

Global Opaque denote_code.

(* TO MOVE *)
Variant Box (T: Type): Type := box (t: T).
(* Protects from "direct" pattern matching but not from context one *)
Ltac protect H := apply box in H.
Ltac hide_string_hyp' H :=
  match type of H with
  | context [String ?x ?y] =>
    let msg := fresh "msg" in
    let eqmsg := fresh "EQ_msg" in
    remember (String x y) as msg eqn:eqmsg; protect eqmsg
  end.

Ltac hide_strings' :=
  repeat (
      match goal with
      | h: Box _ |- _ => idtac
      | h: context [String ?x ?y] |- _ =>
        let msg := fresh "msg" in
        let eqmsg := fresh "EQ_msg" in
        remember (String x y) as msg eqn:eqmsg;
        protect eqmsg
      | |- context [String ?x ?y] =>
        let msg := fresh "msg" in
        let eqmsg := fresh "EQ_msg" in
        remember (String x y) as msg eqn:eqmsg;
        protect eqmsg
      end).

Ltac forget_strings :=
  repeat (
      match goal with
      | h: context [String ?x ?y] |- _ =>
        let msg := fresh "msg" in
        generalize (String x y) as msg
      | |- context [String ?x ?y] =>
        let msg := fresh "msg" in
        generalize (String x y) as msg
      end).

