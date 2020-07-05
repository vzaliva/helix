Require Import Coq.Arith.Arith.
Require Import Psatz.

Require Import Coq.Strings.String.

Import Coq.Strings.String Strings.Ascii.
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
    := λ '(m, (ρ, g)), (m, (ρ, (g, v))).

  Definition mk_config_mcfg_T (T:Type) (v:T): config_mcfg -> (config_mcfg_T T)
    := λ '(m, (ρ, g)), (m, (ρ, (g, v))).

End StateTypes.

(* Facilities to refer to the type of relations used during the simulations of various pieces of denotions we manipulate *)
(* TODOYZ: Think about those, rename. *)
Section RelationTypes.

  (** Relation of memory states which must be held for
      intialization steps *)
  Definition Rel_cfg: Type
    := memoryH → config_cfg → Prop.

  (** Relation of memory states which must be held for
      intialization steps *)
  Definition Rel_mcfg: Type
    := memoryH → config_mcfg → Prop.

  (** Type of bisimulation relations between DSHCOL and VIR internal to CFG states,
      parameterized by the types of the computed values.
   *)
  Definition Rel_cfg_T (TH TV: Type): Type
    := memoryH * TH → config_cfg_T TV → Prop.

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
    := memoryH * TH → config_mcfg_T TV → Prop.

  Definition lift_Rel_mcfg (R: Rel_mcfg) (TH TV: Type): Rel_mcfg_T TH TV :=
    fun '(memH,_) '(memV,(l,(g,_))) => R memH (memV,(l,g)).

  Definition lift_pure_mcfg (P : Prop) {TH TV : Type} : Rel_mcfg_T TH TV :=
    fun _ _ => P.

  (** Type of bisimulation relation between DSHCOL and LLVM states.
    This relation could be used for fragments of CFG [cfg].
   *)
  Definition Type_R_partial: Type
    := memoryH * () → config_res_cfg → Prop.

  (** Type of bisimulation relation between DSHCOL and LLVM states.
      This relation could be used for "closed" CFG [mcfg].
   *)
  Definition Type_R_full: Type
    := memoryH * (list binary64) → config_res_mcfg → Prop.

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
           ∃ id, (nth_error Γ n ≡ Some (id, getWFType id (DSHType_of_DSHVal v))).

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
      ∃ (bk_h : mem_block) (ptr_v : Addr.addr),
        memory_lookup memH m ≡ Some bk_h
        ∧ in_local_or_global l g memV (ID_Local id) (DVALUE_Addr ptr_v) t
        ∧ (∀ (i : Memory.NM.key) (v : binary64),
              mem_lookup i bk_h ≡ Some v → get_array_cell memV ptr_v i DTYPE_Double ≡ inr (UVALUE_Double v)).
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

Ltac eutt_hide_left :=
  match goal with
    |- eutt _ ?t _ => remember t
  end.

Ltac eutt_hide_right :=
  match goal with
    |- eutt _ _ ?t => remember t
  end.

Ltac eutt_hide_rel H :=
  match goal with
    |- eutt ?r _ _ => remember r as H
  end.

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
      interp_Mem (trigger (MemSet dst blk)) mem ≈ Ret (memory_set mem dst blk, ()).
  Proof.
    intros dst blk mem.
    setoid_rewrite interp_Mem_vis_eqit; cbn.
    rewrite bind_ret_l.
    rewrite interp_Mem_ret.
    apply tau_eutt.
  Qed.

End InterpMem.

(* We should do all reasoning about [interp_Mem] through these lemmas, let's make it Opaque to be sure that reduction does not mess with it *)
Opaque interp_Mem.
Opaque interp_cfg_to_L3.

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
     I use [do k] to print debug messages if [k=1].
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
  ∀ (id : raw_id) (l : local_env) (g : global_env) m (x : ident) dv dv' τ,
    x <> ID_Local id →
    in_local_or_global l g m x dv τ →
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
    x ≢ ID_Local id.
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

Opaque append.
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

Opaque incBlockNamed.
Opaque incVoid.
Opaque incLocal.

Lemma unsigned_is_zero: forall a, Int64.unsigned a ≡ Int64.unsigned Int64.zero ->
                             a = Int64.zero.
Proof.
  intros a H.
  unfold Int64.unsigned, Int64.intval in H.
  repeat break_let; subst.
  destruct Int64.zero.
  inv Heqi0.
  unfold equiv, MInt64asNT.NTypeEquiv, Int64.eq, Int64.unsigned, Int64.intval.
  apply Coqlib.zeq_true.
Qed.

Section NExpr.

  (**
     We prove in this section the correctness of the compilation of numerical expressions, i.e. [NExpr].
     The corresponding compiling function is [inexpert].

     Helix side:
     * nexp: NExpr
     * σ: evalContext
     * s: IRState

The expression must be closed in [evalContext]. I.e. all variables are below the length of σ
Γ s1 = σ?

   *)
  (* NOTEYZ:
     These expressions are pure. As such, it is true that we do not need to interpret away
     the memory events on Helix side to establish the bisimulation.
     However at least in the current state of affair, I believe it's widely more difficult
     to lift the result before interpretation to the context we need than to simply plug in
     the interpreter.
     In particular we would need to have a clean enough lift that deduces that the memory has
     not been modified. I'm interested in having this, but I do not know how easy it is to get it.
     TODOYZ: Investigate this claim
   *)

  Definition memory_invariant_memory_mcfg (σ : evalContext) (s : IRState) : Rel_mcfg :=
    fun memH '(memV,((l,sl),g)) =>
      memory_invariant σ s memH (memV,(l,g)).

 (** YZ
      At the top level, the correctness of genNExpr is expressed as the denotation of the operator being equivalent
      to the bind of denoting the code followed by denoting the expression.
      However this is not inductively stable, we only want to plug the expression at the top level.
      We therefore instead carry the fact about the denotation of the expression in the invariant. (Is there another clever way?)
      TODO: how to make this (much) less ugly?
   *)
  Definition genNExpr_exp_correct σ (nexp : NExpr) (e: exp typ) : Rel_cfg_T DynamicValues.int64 unit :=
    fun '(_,i) '(memV,(l,(g,v))) =>
      forall l', l ⊑ l' ->
        Ret (memV,(l',(g,UVALUE_I64 i)))
        ≈
        with_err_LB
        (interp_cfg (translate exp_E_to_instr_E (denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] e))) g l' memV) /\ evalNExpr σ nexp ≡ inr i.

  (**
     We package the local specific invariants. Additionally to the evaluation of the resulting expression,
     we also state that evaluating the code preserves most of the state, except for the local state being
     allowed to be extended with fresh bindings.
   *)
  Record genNExpr_rel
         (σ : evalContext)
         (nexp : NExpr)
         (e : exp typ)
         (mi : memoryH) (sti : config_cfg)
         (mf : memoryH * DynamicValues.int64) (stf : config_cfg_T unit)
    : Prop :=
    {
    exp_correct : genNExpr_exp_correct σ nexp e mf stf;
    monotone : ext_local mi sti mf stf
    }.

  Lemma genNExpr_correct_ind :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *)   (nexp: NExpr) (σ: evalContext) (memH: memoryH) (v : Int64.int)
      (* Vellvm bits *)   (e: exp typ) (c: code typ) (g : global_env) (l : local_env) (memV : memoryV),

      genNExpr nexp s1 ≡ inr (s2, (e, c))      -> (* Compilation succeeds *)
      evalNExpr σ nexp ≡ inr v                 -> (* Evaluation succeeds *)
      state_invariant σ s1 memH (memV, (l, g)) -> (* The main state invariant is initially true *)

      eutt (lift_Rel_cfg (state_invariant σ s2) ⩕
            genNExpr_rel σ nexp e memH (mk_config_cfg memV l g) ⩕
            lift_pure_cfg (Γ s1 ≡ Γ s2))
           (with_err_RB (interp_Mem (denoteNExpr σ nexp) memH))
           (with_err_LB (interp_cfg (denote_code (convert_typ [] c)) g l memV)).
  Proof.
    (*
    intros s1 s2 nexp; revert s1 s2; induction nexp; intros * COMPILE EVAL PRE.
    - (* Variable case *)
      (* Reducing the compilation *)
      cbn* in COMPILE; simp.

      + (* The variable maps to an integer in the IRState *)
        unfold denoteNExpr; cbn*.

        repeat norm_v.
        break_inner_match_goal.

        * break_inner_match_goal; try abs_by_WF.
          repeat norm_h.
          destruct i0.
          { (* Global -- Absurd, globals map to pointers, not integers *)
            abs_by_WF.
          }
         { (* Local *)
            apply eutt_Ret; split; [| split]; try now eauto.
            constructor; eauto.
            intros l' MONO; cbn*.
            split.
            { repeat norm_v.
              2: eapply memory_invariant_LLU; eauto.
              2: eapply memory_invariant_ext_local; eauto.
              cbn; repeat norm_v.
              reflexivity.
            }

            rewrite Heqo0.
            reflexivity.

          }

        * (* Variable not in context, [context_lookup] fails *)
          cbn* in EVAL; rewrite Heqo0 in EVAL; inv EVAL.

      + (* The variable maps to a pointer *)
        unfold denoteNExpr; cbn*.
        repeat norm_v.
        break_inner_match_goal; try abs_by_WF.
        * break_inner_match_goal; try abs_by_WF.
          subst.
          destruct i0; try abs_by_WF.
          edestruct memory_invariant_GLU as (ptr & LU & READ); eauto.
          cbn; repeat norm_v.
          2:eassumption.
          cbn; repeat norm_v.
          cbn; repeat norm_v.
          rewrite interp_cfg_to_L3_Load; eauto.
          cbn; repeat norm_v.
          rewrite interp_cfg_to_L3_LW.
          cbn; repeat norm_v.
          repeat norm_h.
          apply eutt_Ret; split; [| split].
          -- eapply state_invariant_add_fresh; eauto; reflexivity.
          -- split.
             {
               intros l' MONO; cbn*.
               split.
               { repeat norm_v.
                 2: eapply MONO, In_add_eq.
                 cbn; repeat norm_v.
                 reflexivity.
               }

               rewrite Heqo0.
               reflexivity.
             }
             {
               repeat (split; auto).
               apply sub_alist_add.
               destruct PRE.
               apply concrete_fresh_fresh in incLocal_is_fresh0.
               unfold incLocal_fresh in incLocal_is_fresh0.
               eapply incLocal_is_fresh0; eauto.
             }
          -- symmetry; eapply incLocal_Γ; eauto.

        * cbn* in EVAL; rewrite Heqo0 in EVAL; inv EVAL.

    - (* Constant *)

      cbn* in COMPILE; simp.
      unfold denoteNExpr; cbn*.
      repeat norm_h.
      repeat norm_v.
      apply eutt_Ret; split; [| split]; try now eauto.
      split; eauto.
      intros l' MONO; cbn*.
      split; try reflexivity.
      rewrite repr_intval; repeat norm_v.
      reflexivity.

    - (* NDiv *)

      cbn* in COMPILE; simp.

      eutt_hide_right.
      unfold denoteNExpr in *; cbn*.

      cbn in EVAL.
      break_inner_match_goal; [| break_inner_match_goal].
      + inversion EVAL. (* Exception in subexpression *)
      + inversion EVAL. (* Division by 0 *)
      + (* Success, Heqs2 *)
        break_inner_match_goal.
        * inversion EVAL. (* Exception in subexpression *)
        * repeat norm_h.
          subst i1.

          (* TODO YZ: gets some super "specialize" tactics that do not require to provide variables *)
          specialize (IHnexp1 _ _ _ _ _ _ _ _ _ _ Heqs Heqs3 PRE).

          cbn* in IHnexp1; rewrite Heqs3 in IHnexp1.
          (* YZ TODO : Why is this one particularly slow? *)
          repeat norm_h in IHnexp1.

          rewrite convert_typ_app, denote_code_app.
          repeat norm_v.

          ret_bind_l_left (memH, i3).
          eapply eutt_clo_bind; [eassumption | clear IHnexp1].

          introR; destruct_unit.
          destruct PRE0 as (PREI & (EXPRI & <- & <- & <- & MONOI) & GAMMAI).
          cbn in *.

          specialize (IHnexp2 _ _ _ _ _ _ _ _ _ _ Heqs0 Heqs2 PREI).

          cbn* in IHnexp2;
            repeat norm_v in IHnexp2;
            repeat norm_h in IHnexp2.
          simpl_match in IHnexp2.
          repeat norm_h in IHnexp2.

          rewrite convert_typ_app, denote_code_app.
          repeat norm_v.
          subst.
          ret_bind_l_left (memH,i2).
          eapply eutt_clo_bind; [eassumption | clear IHnexp2].

          introR; destruct_unit.
          destruct PRE0 as (PREF & (EXPRF & <- & <- & <- & MONOF) & GAMMAF).
          (* cbn takes 5seconds instead of doing this instantaneously... *)
          simpl in *.
          repeat norm_v.
          simpl in *; unfold eval_op; simpl.
          unfold IntType; rewrite typ_to_dtyp_I.

          repeat norm_v.
          specialize (EXPRI _ MONOF) as [EXPRI EVAL_vH].
          rewrite <- EXPRI; auto.

          repeat norm_v.
          assert (l1 ⊑ l1) as L1L1. reflexivity.
          specialize (EXPRF _ L1L1) as [EXPRF EVAL_vH0].
          rewrite <- EXPRF.
          clear L1L1.
          repeat norm_v.
          cbn*.

          rewrite Heqs3 in EVAL_vH; inversion EVAL_vH.
          rewrite Heqs2 in EVAL_vH0; inversion EVAL_vH0.
          subst.

          { break_inner_match_goal.
            + (* Division by 0 *)
              apply Z.eqb_eq in Heqb.
              exfalso. apply n.
              rewrite <- Int64.unsigned_zero in Heqb.
              unfold MInt64asNT.NTypeZero.
              apply unsigned_is_zero; auto.
            + (* Good old division *)
              repeat norm_v.
              rewrite interp_cfg_to_L3_LW.
              cbn; repeat norm_v.
              apply eutt_Ret; split; [| split]; try now eauto.
              cbn. eapply state_invariant_add_fresh; eauto; reflexivity.
              split.
              {
                cbn; intros ? MONO.
                split.
                { repeat norm_v.
                  2: apply MONO, In_add_eq.
                  cbn; repeat norm_v.
                  apply eutt_Ret.
                  do 3 f_equal.
                }

                rewrite Heqs2.
                rewrite Heqd.
                rewrite Heqs3.
                reflexivity.
              }
              {
                apply ext_local_subalist.
                etransitivity; eauto.
                etransitivity; eauto.
                apply sub_alist_add.
                apply incLocal_is_fresh,concrete_fresh_fresh in PREF.
                eapply PREF.
                eauto.
              }
              {
                rewrite GAMMAI, GAMMAF.
                symmetry; eapply incLocal_Γ; eauto.
              }
          }
    - (*NMod *)

      cbn* in COMPILE; simp.

      eutt_hide_right.
      unfold denoteNExpr in *; cbn*.

      cbn in EVAL.
      break_inner_match_goal; [| break_inner_match_goal].
      + inversion EVAL. (* Exception in subexpression *)
      + inversion EVAL. (* Division by 0 *)
      + (* Success, Heqs2 *)
        break_inner_match_goal.
        * inversion EVAL. (* Exception in subexpression *)
        * repeat norm_h.
          subst i1.

          (* TODO YZ: gets some super "specialize" tactics that do not require to provide variables *)
          specialize (IHnexp1 _ _ _ _ _ _ _ _ _ _ Heqs Heqs3 PRE).

          cbn* in IHnexp1; rewrite Heqs3 in IHnexp1.
          (* YZ TODO : Why is this one particularly slow? *)
          repeat norm_h in IHnexp1.

          rewrite convert_typ_app, denote_code_app.
          repeat norm_v.

          ret_bind_l_left (memH, i3).
          eapply eutt_clo_bind; [eassumption | clear IHnexp1].

          introR; destruct_unit.
          destruct PRE0 as (PREI & (EXPRI & <- & <- & <- & MONOI) & GAMMAI).
          cbn in *.

          specialize (IHnexp2 _ _ _ _ _ _ _ _ _ _ Heqs0 Heqs2 PREI).

          cbn* in IHnexp2;
            repeat norm_v in IHnexp2;
            repeat norm_h in IHnexp2.
          simpl_match in IHnexp2.
          repeat norm_h in IHnexp2.

          rewrite convert_typ_app, denote_code_app.
          repeat norm_v.
          subst.
          ret_bind_l_left (memH,i2).
          eapply eutt_clo_bind; [eassumption | clear IHnexp2].

          introR; destruct_unit.
          destruct PRE0 as (PREF & (EXPRF & <- & <- & <- & MONOF) & GAMMAF).
          (* cbn takes 5seconds instead of doing this instantaneously... *)
          simpl in *.
          repeat norm_v.
          simpl in *; unfold eval_op; simpl.
          unfold IntType; rewrite typ_to_dtyp_I.

          repeat norm_v.
          specialize (EXPRI _ MONOF) as [EXPRI EVAL_vH].
          rewrite <- EXPRI; auto.

          repeat norm_v.
          assert (l1 ⊑ l1) as L1L1. reflexivity.
          specialize (EXPRF _ L1L1) as [EXPRF EVAL_vH0].
          rewrite <- EXPRF.
          clear L1L1.
          repeat norm_v.
          cbn*.

          rewrite Heqs3 in EVAL_vH; inversion EVAL_vH.
          rewrite Heqs2 in EVAL_vH0; inversion EVAL_vH0.
          subst.

          { break_inner_match_goal.
            + (* Division by 0 *)
              apply Z.eqb_eq in Heqb.
              exfalso. apply n.
              rewrite <- Int64.unsigned_zero in Heqb.
              unfold MInt64asNT.NTypeZero.
              apply unsigned_is_zero; auto.
            + (* Good old division *)
              repeat norm_v.
              rewrite interp_cfg_to_L3_LW.
              cbn; repeat norm_v.
              apply eutt_Ret; split; [| split].
              cbn. eapply state_invariant_add_fresh; eauto; reflexivity.
              split.
              {
                cbn; intros ? MONO.
                split.
                { repeat norm_v.
                  2: apply MONO, In_add_eq.
                  cbn; repeat norm_v.
                  apply eutt_Ret.
                  do 3 f_equal.
                }

                rewrite Heqs2.
                rewrite Heqd.
                rewrite Heqs3.
                reflexivity.
              }
              {
                apply ext_local_subalist.
                etransitivity; eauto.
                etransitivity; eauto.
                apply sub_alist_add.
                apply incLocal_is_fresh,concrete_fresh_fresh in PREF.
                eapply PREF.
                eauto.
              }
              {
                rewrite GAMMAI, GAMMAF.
                symmetry; eapply incLocal_Γ; eauto.
              }
          }
    - (* NAdd *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in COMPILE; simp.

      eutt_hide_right.
      unfold denoteNExpr in *; cbn*.

      cbn in EVAL.
      break_inner_match_goal; [| break_inner_match_goal];
        try (exfalso; match goal with | h: genNExpr _ _ ≡ _ |- _ => eapply evalNexpr_WF_no_fail in h; now eauto end); try solve [inversion EVAL].

      repeat norm_h.
      (* TODO YZ: gets some super "specialize" tactics that do not require to provide variables *)
      specialize (IHnexp1 _ _ _ _ _ _ _ _ _ _ Heqs Heqs2 PRE).

      cbn* in IHnexp1;
        repeat norm_v in IHnexp1;
        repeat norm_h in IHnexp1.
      simpl_match in IHnexp1.
      (* YZ TODO : Why is this one particularly slow? *)
      repeat norm_h in IHnexp1.

      subst.
      cbn*.
      rewrite convert_typ_app, denote_code_app.
      repeat norm_v.
      subst.
      ret_bind_l_left (memH,i2).
      eapply eutt_clo_bind; [eassumption | clear IHnexp1].

      introR; destruct_unit.
      destruct PRE0 as (PREI & (EXPRI & <- & <- & <- & MONOI) & GAMMAI).
      cbn in *.

      specialize (IHnexp2 _ _ _ _ _ _ _ _ _ _ Heqs0 Heqs3 PREI).

      cbn* in IHnexp2;
        repeat norm_v in IHnexp2;
        repeat norm_h in IHnexp2.
      simpl_match in IHnexp2.
      repeat norm_h in IHnexp2.

      rewrite convert_typ_app, denote_code_app.
      repeat norm_v.
      subst.
      ret_bind_l_left (memH,i3).
      eapply eutt_clo_bind; [eassumption | clear IHnexp2].

      introR; destruct_unit.
      destruct PRE0 as (PREF & (EXPRF & <- & <- & <- & MONOF) & GAMMAF).
      (* cbn takes 5seconds instead of doing this instantaneously... *)
      simpl in *; unfold eval_op; simpl.
      unfold IntType; rewrite typ_to_dtyp_I.

      repeat norm_v.
      specialize (EXPRI _ MONOF) as [EXPRI EVAL_vH].
      rewrite <- EXPRI; auto.

      repeat norm_v.
      assert (l0 ⊑ l0) as L0L0 by reflexivity.
      specialize (EXPRF _ L0L0) as [EXPRF EVAL_vH0].
      rewrite <- EXPRF.
      clear L0L0.
      repeat norm_v.
      cbn*.
      repeat norm_v.
      rewrite interp_cfg_to_L3_LW.
      cbn*; repeat norm_v.
      apply eutt_Ret; split; [| split].
      cbn; eapply state_invariant_add_fresh; eauto.
      split.
      {
        cbn; intros ? MONO.
        split.
        { repeat norm_v.
          2: apply MONO, In_add_eq.
          cbn; repeat norm_v.
          apply eutt_Ret.
          do 3 f_equal.

          rewrite Heqs2 in EVAL_vH; inversion EVAL_vH.
          rewrite Heqs3 in EVAL_vH0; inversion EVAL_vH0.
          subst.
          reflexivity.
        }

        rewrite Heqs2.
        rewrite Heqs3.
        reflexivity.
      }
      {
        apply ext_local_subalist.
        etransitivity; eauto.
        etransitivity; eauto.
        apply sub_alist_add.
        apply incLocal_is_fresh,concrete_fresh_fresh in PREF.
        eapply PREF.
        eauto.
      }
      {
        rewrite GAMMAI, GAMMAF.
        symmetry; eapply incLocal_Γ; eauto.
      }

    - (* NMinus *)
      cbn* in COMPILE; simp.

      eutt_hide_right.
      unfold denoteNExpr in *; cbn*.

      cbn in EVAL.
      break_inner_match_goal; [| break_inner_match_goal];
        try (exfalso; match goal with | h: genNExpr _ _ ≡ _ |- _ => eapply evalNexpr_WF_no_fail in h; now eauto end); try solve [inversion EVAL].

      repeat norm_h.
      (* TODO YZ: gets some super "specialize" tactics that do not require to provide variables *)
      specialize (IHnexp1 _ _ _ _ _ _ _ _ _ _ Heqs Heqs2 PRE).

      cbn* in IHnexp1;
        repeat norm_v in IHnexp1;
        repeat norm_h in IHnexp1.
      simpl_match in IHnexp1.
      (* YZ TODO : Why is this one particularly slow? *)
      repeat norm_h in IHnexp1.

      subst.
      cbn*.
      rewrite convert_typ_app, denote_code_app.
      repeat norm_v.
      subst.
      ret_bind_l_left (memH,i2).
      eapply eutt_clo_bind; [eassumption | clear IHnexp1].

      introR; destruct_unit.
      destruct PRE0 as (PREI & (EXPRI & <- & <- & <- & MONOI) & GAMMAI).
      cbn in *.

      specialize (IHnexp2 _ _ _ _ _ _ _ _ _ _ Heqs0 Heqs3 PREI).

      cbn* in IHnexp2;
        repeat norm_v in IHnexp2;
        repeat norm_h in IHnexp2.
      simpl_match in IHnexp2.
      repeat norm_h in IHnexp2.

      rewrite convert_typ_app, denote_code_app.
      repeat norm_v.
      subst.
      ret_bind_l_left (memH,i3).
      eapply eutt_clo_bind; [eassumption | clear IHnexp2].

      introR; destruct_unit.
      destruct PRE0 as (PREF & (EXPRF & <- & <- & <- & MONOF) & GAMMAF).
      (* cbn takes 5seconds instead of doing this instantaneously... *)
      simpl in *; unfold eval_op; simpl.
      unfold IntType; rewrite typ_to_dtyp_I.

      repeat norm_v.
      specialize (EXPRI _ MONOF) as [EXPRI EVAL_vH].
      rewrite <- EXPRI; auto.

      repeat norm_v.
      assert (l1 ⊑ l1) as L1L1 by reflexivity.
      specialize (EXPRF _ L1L1) as [EXPRF EVAL_vH0].
      rewrite <- EXPRF.
      repeat norm_v.
      cbn*.
      repeat norm_v.
      rewrite interp_cfg_to_L3_LW.
      cbn*; repeat norm_v.
      apply eutt_Ret; split; [| split].
      cbn; eapply state_invariant_add_fresh; eauto.
      split.
      {
        cbn; intros ? MONO.
        split.
        { repeat norm_v.
          2: apply MONO, In_add_eq.
          cbn; repeat norm_v.
          apply eutt_Ret.
          do 3 f_equal.

          rewrite Heqs2 in EVAL_vH; inversion EVAL_vH.
          rewrite Heqs3 in EVAL_vH0; inversion EVAL_vH0.
          subst.
          reflexivity.
        }

        rewrite Heqs2.
        rewrite Heqs3.
        auto.
      }
      {
        apply ext_local_subalist.
        etransitivity; eauto.
        etransitivity; eauto.
        apply sub_alist_add.
        apply incLocal_is_fresh,concrete_fresh_fresh in PREF.
        eapply PREF.
        eauto.
      }
      {
        rewrite GAMMAI, GAMMAF.
        symmetry; eapply incLocal_Γ; eauto.
      }

    - (* NMult *)
      cbn* in COMPILE; simp.

      eutt_hide_right.
      unfold denoteNExpr in *; cbn*.

      cbn in EVAL.
      break_inner_match_goal; [| break_inner_match_goal];
        try (exfalso; match goal with | h: genNExpr _ _ ≡ _ |- _ => eapply evalNexpr_WF_no_fail in h; now eauto end); try solve [inversion EVAL].

      repeat norm_h.
      (* TODO YZ: gets some super "specialize" tactics that do not require to provide variables *)
      specialize (IHnexp1 _ _ _ _ _ _ _ _ _ _ Heqs Heqs2 PRE).

      cbn* in IHnexp1;
        repeat norm_v in IHnexp1;
        repeat norm_h in IHnexp1.
      simpl_match in IHnexp1.
      (* YZ TODO : Why is this one particularly slow? *)
      repeat norm_h in IHnexp1.

      subst.
      cbn*.
      rewrite convert_typ_app, denote_code_app.
      repeat norm_v.
      subst.
      ret_bind_l_left (memH,i2).
      eapply eutt_clo_bind; [eassumption | clear IHnexp1].

      introR; destruct_unit.
      destruct PRE0 as (PREI & (EXPRI & <- & <- & <- & MONOI) & GAMMAI).
      cbn in *.

      specialize (IHnexp2 _ _ _ _ _ _ _ _ _ _ Heqs0 Heqs3 PREI).

      cbn* in IHnexp2;
        repeat norm_v in IHnexp2;
        repeat norm_h in IHnexp2.
      simpl_match in IHnexp2.
      repeat norm_h in IHnexp2.

      rewrite convert_typ_app, denote_code_app.
      repeat norm_v.
      subst.
      ret_bind_l_left (memH,i3).
      eapply eutt_clo_bind; [eassumption | clear IHnexp2].

      introR; destruct_unit.
      destruct PRE0 as (PREF & (EXPRF & <- & <- & <- & MONOF) & GAMMAF).
      (* cbn takes 5seconds instead of doing this instantaneously... *)
      simpl in *; unfold eval_op; simpl.
      unfold IntType; rewrite typ_to_dtyp_I.

      repeat norm_v.
      specialize (EXPRI _ MONOF) as [EXPRI EVAL_vH].
      rewrite <- EXPRI; auto.

      repeat norm_v.
      assert (l1 ⊑ l1) as L1L1 by reflexivity.
      specialize (EXPRF _ L1L1) as [EXPRF EVAL_vH0].
      rewrite <- EXPRF.

      repeat norm_v.
      cbn*.

      break_inner_match_goal.
      + (* 64 = 1, I conjecture an easy to prove absurdity *)
        inversion e.
      + cbn; repeat norm_v.
        rewrite interp_cfg_to_L3_LW.
        cbn*; repeat norm_v.
        apply eutt_Ret; split; [| split].
        cbn; eapply state_invariant_add_fresh; eauto.
        split.
        {
          cbn; intros ? MONO.
          split. {
            repeat norm_v.
            2: apply MONO, In_add_eq.
            cbn; repeat norm_v.
            apply eutt_Ret.
            do 3 f_equal.
            rewrite Heqs2 in EVAL_vH; inversion EVAL_vH.
            rewrite Heqs3 in EVAL_vH0; inversion EVAL_vH0.
            subst.
            reflexivity.
          }

          rewrite Heqs2.
          rewrite Heqs3.
          auto.
        }
        {
          apply ext_local_subalist.
          etransitivity; eauto.
          etransitivity; eauto.
          apply sub_alist_add.
          apply incLocal_is_fresh,concrete_fresh_fresh in PREF.
          eapply PREF.
          eauto.
        }
        {
          rewrite GAMMAI, GAMMAF.
          symmetry; eapply incLocal_Γ; eauto.
        }

    - (* NMin *)
      (* Non-implemented by the compiler *)
      inversion COMPILE.
    - (* NMax *)
      (* Non-implemented by the compiler *)
      inversion COMPILE.
Qed.
     *)
  Admitted.

  Lemma genNExpr_memH : forall σ n e memH memV memH' memV' l g l' g' n',
      genNExpr_rel σ n e memH (mk_config_cfg memV l g) (memH', n')
                   (memV', (l', (g', ()))) ->
      memH ≡ memH'.
  Proof.
    intros σ n e memH memV memH' memV' l g l' g' n' H.
    destruct H; cbn in *; intuition.
  Qed.

  Lemma genNExpr_memV : forall σ n e memH memV memH' memV' l g l' g' n',
      genNExpr_rel σ n e memH (mk_config_cfg memV l g) (memH', n')
                   (memV', (l', (g', ()))) ->
      memV ≡ memV'.
  Proof.
    intros σ n e memH memV memH' memV' l g l' g' n' H.
    destruct H; cbn in *; intuition.
  Qed.

  Lemma genNExpr_g : forall σ n e memH memV memH' memV' l g l' g' n',
      genNExpr_rel σ n e memH (mk_config_cfg memV l g) (memH', n')
                   (memV', (l', (g', ()))) ->
      g ≡ g'.
  Proof.
    intros σ n e memH memV memH' memV' l g l' g' n' H.
    destruct H; cbn in *; intuition.
  Qed.

  Lemma genNExpr_l : forall σ n e memH memV memH' memV' l g l' g' n',
      genNExpr_rel σ n e memH (mk_config_cfg memV l g) (memH', n')
                   (memV', (l', (g', ()))) ->
      l ⊑ l'.
  Proof.
    intros σ n e memH memV memH' memV' l g l' g' n' H.
    destruct H; cbn in *; intuition.
  Qed.

End NExpr.

Ltac genNExpr_rel_subst LL :=
  match goal with
  | NEXP : genNExpr_rel ?σ ?n ?e ?memH (mk_config_cfg ?memV ?l ?g) (?memH', ?n') (?memV', (?l', (?g', ()))) |- _ =>
    let H := fresh in
    pose proof genNExpr_memH NEXP as H; subst memH';
    pose proof genNExpr_memV NEXP as H; subst memV';
    pose proof genNExpr_g NEXP as H; subst g';
    pose proof genNExpr_l NEXP as LL
  end.

Section MExpr.

  Definition invariant_MExpr
             (σ : evalContext)
             (s : IRState) (mexp : MExpr) : Rel_cfg_T (mem_block * Int64.int) uvalue :=
    fun '(memH, (mb, mb_sz)) '(memV, (ρ, (g, res))) =>
      (exists ptr i (vid : nat) (mid : mem_block_id) (size : Int64.int) (sz : int), (* TODO: sz ≈ size? *)
        res ≡ UVALUE_Addr ptr /\
        memory_lookup memH mid ≡ Some mb /\
        in_local_or_global ρ g memV i (DVALUE_Addr ptr) (TYPE_Array sz TYPE_Double) /\
        nth_error σ vid ≡ Some (DSHPtrVal mid size) /\
        nth_error (Γ s) vid ≡ Some (i, TYPE_Pointer (TYPE_Array sz TYPE_Double))) /\
      evalMExpr memH σ mexp ≡ inr (mb, mb_sz).

  (* TODO: like ext_local, but locals also don't change. Not sure what to call this... *)
  Definition preserves_states {R S}: memoryH -> config_cfg -> Rel_cfg_T R S :=
    fun mh '(mi,(li,gi)) '(mh',_) '(m,(l,(g,_))) => mh ≡ mh' /\ mi ≡ m /\ gi ≡ g /\ li ≡ l.

  Lemma preserves_states_refl:
  forall {R S} memH memV l g n v,
    @preserves_states R S memH (mk_config_cfg memV l g) (memH, n) (memV, (l, (g, v))).
  Proof.
    intros; repeat split; reflexivity.
  Qed.
  Hint Resolve preserves_states_refl: core.

  Record genMExpr_rel
         (σ : evalContext)
         (s : IRState)
         (mexp : MExpr)
         (mi : memoryH) (sti : config_cfg)
         (mf : memoryH * (mem_block * Int64.int)) (stf : config_cfg_T uvalue)
    : Prop :=
    {
    mexp_correct :invariant_MExpr σ s mexp mf stf;
    m_preserves : preserves_states mi sti mf stf
    }.

  Lemma memory_invariant_Ptr : forall vid σ s memH memV l g a size x sz,
      state_invariant σ s memH (memV, (l, g)) ->
      nth_error σ vid ≡ Some (DSHPtrVal a size) ->
      nth_error (Γ s) vid ≡ Some (x, TYPE_Pointer (TYPE_Array sz TYPE_Double)) ->
      ∃ (bk_helix : mem_block) (ptr_llvm : Addr.addr),
        memory_lookup memH a ≡ Some bk_helix
        ∧ in_local_or_global l g memV x (DVALUE_Addr ptr_llvm) (TYPE_Pointer (TYPE_Array sz TYPE_Double))
        ∧ (∀ (i : Memory.NM.key) (v : binary64), mem_lookup i bk_helix ≡ Some v → get_array_cell memV ptr_llvm i DTYPE_Double ≡ inr (UVALUE_Double v)).
  Proof.
    intros * [MEM _ _] LU1 LU2; eapply MEM in LU1; eapply LU1 in LU2; eauto.
  Qed.

  (** ** Compilation of MExpr
  *)
  Lemma genMExpr_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *)   (mexp: MExpr) (σ: evalContext) (memH: memoryH) v
      (* Vellvm bits *)   (exp: exp typ) (c: code typ) (g : global_env) (l : local_env) (memV : memoryV) (τ: typ),
      genMExpr mexp s1 ≡ inr (s2, (exp, c, τ)) -> (* Compilation succeeds *)
      evalMExpr memH σ mexp ≡ inr v    -> (* Evaluation succeeds *)
      state_invariant σ s1 memH (memV, (l, g)) ->
      eutt (lift_Rel_cfg (state_invariant σ s2) ⩕ genMExpr_rel σ s2 mexp memH (mk_config_cfg memV l g))
           (with_err_RB
              (interp_Mem (denoteMExpr σ mexp)
                          memH))
           (with_err_LB
              ((interp_cfg (D.denote_code (convert_typ [] c) ;; translate exp_E_to_instr_E (D.denote_exp (Some DTYPE_Pointer (* (DTYPE_I 64%Z) *)) (convert_typ [] exp))))
                 g l memV)).
  Proof.
    intros * Hgen Heval Hmeminv.
    generalize Hmeminv; intros WF; apply IRState_is_WF in WF.

    unfold denoteMExpr; cbn*.
    destruct mexp as [[vid] | mblock].
    - (* PtrDeref case *)

      unfold denotePExpr; cbn*.
      cbn* in Hgen; simp.
      cbn*; repeat norm_v.
      norm_h.
      break_inner_match_goal; try abs_by_WF.
      2: cbn* in Heval; rewrite Heqo0 in Heval; inv Heval.
      norm_h.
      break_inner_match_goal; try abs_by_WF.
      subst.

      edestruct memory_invariant_Ptr as (bkH & ptrV & Mem_LU & LUV & EQ); eauto.

      destruct i0.
      + (* Global *)
        cbn in *.
        (* This case should be absurd if I'm not mistaken: we read in memory at an Array type, and yet find an address *)
        exfalso.
        clear - LUV.
        destruct LUV as (ptr & τ' & EQ & LU & READ).
        inv EQ.
        clear -READ.

        do 2 rewrite typ_to_dtyp_equation in READ.
        cbn in READ.

        assert (not_undef (UVALUE_Addr ptrV)) as NU.
        { intros t TYP. inversion TYP. }
        eapply read_array_not_pointer; eauto.
        reflexivity.
        constructor.
      + (*  Local *)
        cbn in *.
        repeat norm_h.
        2: apply memory_lookup_err_inr_Some_eq; eassumption.
        repeat norm_v.
        2:eauto.
        cbn*; repeat norm_v.
        apply eutt_Ret.
        split; auto.
        split; auto.
        red.
        split.
        { do 6 eexists.
          splits; eauto.
          cbn; auto.
        }
        { destruct v as (v & bk_sz). assert (v ≡ bkH) as VBKH.
          { simp.
            inv_memory_lookup_err.
            inversion Mem_LU.
            auto.
          }

          subst.
          cbn.
          rewrite 
          do 4 (break_match_hyp; try solve [inversion Heval]).
          inversion Heval.
          subst.
          break_match_goal; try solve [inversion Heval].
          break_match; inversion Heval.
          break
          apply Heval.
        }
    - (* Const *)
      cbn* in Hgen; simp.
  Qed.

      (* TODO: move these, and use them more. *)

      Lemma genMExpr_memH : forall σ s e memH memV memH' memV' l g l' g' mb uv,
          genMExpr_rel σ s e memH (mk_config_cfg memV l g) (memH', mb)
                       (memV', (l', (g', uv))) ->
          memH ≡ memH'.
      Proof.
        intros * H.
        destruct H; cbn in *; intuition.
      Qed.

      Lemma genMExpr_memV : forall σ s e memH memV memH' memV' l g l' g' mb uv,
          genMExpr_rel σ s e memH (mk_config_cfg memV l g) (memH', mb)
                       (memV', (l', (g', uv))) ->
          memV ≡ memV'.
      Proof.
        intros * H.
        destruct H; cbn in *; intuition.
      Qed.

      Lemma genMExpr_g : forall σ s e memH memV memH' memV' l g l' g' mb uv,
          genMExpr_rel σ s e memH (mk_config_cfg memV l g) (memH', mb)
                       (memV', (l', (g', uv))) ->
          g ≡ g'.
      Proof.
        intros * H.
        destruct H; cbn in *; intuition.
      Qed.

      Lemma genMExpr_l : forall σ s e memH memV memH' memV' l g l' g' mb uv,
          genMExpr_rel σ s e memH (mk_config_cfg memV l g) (memH', mb)
                       (memV', (l', (g', uv))) ->
          l ≡ l'.
      Proof.
        intros * H.
        destruct H; cbn in *; intuition.
      Qed.

      Lemma genMExpr_preserves_WF:
        forall mexp s s' σ x,
          WF_IRState σ s ->
          genMExpr mexp s ≡ inr (s',x) ->
          WF_IRState σ s'.
      Proof.
        induction mexp; intros * WF GEN; cbn* in GEN; simp; auto.
      Qed.

      Lemma genMExpr_array : forall {s1 s2 m e c t},
          genMExpr m s1 ≡ inr (s2, (e, c, t)) ->
          exists sz, t ≡ TYPE_Array sz TYPE_Double.
      Proof.
        intros s1 s2 m e c t H.
        destruct m; cbn in H; inv H.
        simp.
        exists sz.
        reflexivity.
      Qed.

End MExpr.

Ltac genMExpr_rel_subst :=
  match goal with
  | MEXP : genMExpr_rel ?σ ?s ?e ?memH (mk_config_cfg ?memV ?l ?g) (?memH', ?mb) (?memV', (?l', (?g', ?uv))) |- _ =>
    let H := fresh in
    pose proof genMExpr_memH MEXP as H; subst memH';
    pose proof genMExpr_memV MEXP as H; subst memV';
    pose proof genMExpr_g MEXP as H; subst g';
    pose proof genMExpr_l MEXP as H; subst l'
  end.

*)
Section AExpr.

  Definition R_AExpr_start (σ : evalContext) (s : IRState) (memH : memoryH) (vellvm : memoryV * (local_env * global_env)) : Prop
    := state_invariant σ s memH vellvm.

  Definition R_AExpr
             (σ : evalContext) (s : IRState)
             (helix : memoryH * binary64)
             (vellvm : memoryV * (local_env * res_L1)) : Prop
    :=
      let '(memH, b) := helix in
      let '(memV, (ρ, (g, res))) := vellvm in
      state_invariant σ s memH (memV, (ρ, g)) /\
      res ≡ UVALUE_Double b.

  Hint Unfold R_AExpr: core.

  (** ** Compilation of AExpr TODO
   *)
  Definition genAExpr_exp_correct σ (aexp : AExpr) (e: exp typ) : Rel_cfg_T binary64 unit :=
    fun '(memH,i) '(memV,(l,(g,v))) =>
      forall l', l ⊑ l' ->
        Ret (memV,(l',(g,UVALUE_Double i)))
        ≈
        with_err_LB
        (interp_cfg (translate exp_E_to_instr_E (denote_exp (Some (DTYPE_Double)) (convert_typ [] e))) g l' memV) /\ evalAExpr memH σ aexp ≡ inr i.

  Record genAExpr_rel
         (σ : evalContext)
         (aexp : AExpr)
         (e : exp typ)
         (mi : memoryH) (sti : config_cfg)
         (mf : memoryH * binary64) (stf : config_cfg_T unit)
    : Prop :=
    {
    aexp_correct : genAExpr_exp_correct σ aexp e mf stf;
    amonotone : ext_local mi sti mf stf
    }.

  Lemma genAExpr_memH : forall σ aexp e memH memV memH' memV' l g l' g' mb uv,
      genAExpr_rel σ aexp e memH (mk_config_cfg memV l g) (memH', mb)
                   (memV', (l', (g', uv))) ->
      memH ≡ memH'.
  Proof.
    intros * H.
    destruct H; cbn in *; intuition.
  Qed.

  Lemma genAExpr_memV : forall σ aexp e memH memV memH' memV' l g l' g' mb uv,
      genAExpr_rel σ aexp e memH (mk_config_cfg memV l g) (memH', mb)
                   (memV', (l', (g', uv))) ->
      memV ≡ memV'.
  Proof.
    intros * H.
    destruct H; cbn in *; intuition.
  Qed.

  Lemma genAExpr_g : forall σ aexp e memH memV memH' memV' l g l' g' mb uv,
      genAExpr_rel σ aexp e memH (mk_config_cfg memV l g) (memH', mb)
                   (memV', (l', (g', uv))) ->
      g ≡ g'.
  Proof.
    intros * H.
    destruct H; cbn in *; intuition.
  Qed.

  Lemma genAExpr_l : forall σ aexp e memH memV memH' memV' l g l' g' mb uv,
      genAExpr_rel σ aexp e memH (mk_config_cfg memV l g) (memH', mb)
                   (memV', (l', (g', uv))) ->
      l ⊑ l'.
  Proof.
    intros * H.
    destruct H; cbn in *; intuition.
  Qed.

  Ltac genAExpr_rel_subst LL :=
    match goal with
    | NEXP : genAExpr_rel ?σ ?n ?e ?memH (mk_config_cfg ?memV ?l ?g) (?memH', ?n') (?memV', (?l', (?g', ()))) |- _ =>
      let H := fresh in
      pose proof genAExpr_memH NEXP as H; subst memH';
      pose proof genAExpr_memV NEXP as H; subst memV';
      pose proof genAExpr_g NEXP as H; subst g';
      pose proof genAExpr_l NEXP as LL
    end.


  (*
  Lemma genAExpr_preserves_WF:
    forall aexp s s' σ x,
      WF_IRState σ s ->
      genAExpr aexp s ≡ inr (s',x) ->
      WF_IRState σ s'.
  Proof.
    induction aexp; intros * WF GEN; cbn* in GEN; simp ; auto.
    { apply evalNexpr_preserves_WF with (σ:=σ) in Heqs0; auto.
      apply genMExpr_preserves_WF with (σ:=σ) in Heqs1; auto.
    }
    { pose proof IHaexp _ _ _ _ WF Heqs0.
      eauto.
    }

    all: eapply IHaexp1 in Heqs0; eapply IHaexp2 in Heqs1; eauto.
  Qed. *)

  (* TODO: move this *)
  Lemma int_of_nat :
    forall (i : Int64.int),
    exists (n : nat), i ≡ Int64.repr (Z.of_nat n).
  Proof.
    intros [val [LOWER UPPER]].
    Transparent Int64.repr.
    unfold Int64.repr.
    Opaque Int64.repr.
    exists (Z.to_nat val).
    rewrite Z2Nat.id by lia.

    match goal with
    | |- ?x ≡ ?y => assert (x = y) as EQ;
                    pose proof Int64.eq_spec x y as EQ_real
    end.

    { unfold equiv.
      unfold MInt64asNT.NTypeEquiv.
      unfold Int64.eq.
      cbn.
      rewrite Int64.Z_mod_modulus_eq.

      assert (val mod Int64.modulus ≡ val)%Z as H.
      apply Zdiv.Zmod_small; lia.

      rewrite H.
      apply Coqlib.zeq_true.
    }

    rewrite EQ in EQ_real.
    auto.
  Qed.

  (* TODO: move this *)
  Lemma to_nat_repr_of_nat :
    forall (n : nat),
      MInt64asNT.to_nat (Int64.repr (Z.of_nat n)) ≡ n.
  Proof.
    intros n.

    match goal with
    | |- ?x ≡ ?y => assert (x = y) as EQ
    end.

    { unfold equiv. unfold peano_naturals.nat_equiv.
      Transparent Int64.repr.
      unfold Int64.repr.
      Opaque Int64.repr.

      unfold MInt64asNT.to_nat.
      unfold Int64.intval.
      rewrite Int64.Z_mod_modulus_eq.
      assert (exists m, Int64.modulus ≡ Z.of_nat m) as (m & H).
      admit.

      rewrite H.
      rewrite <- Zdiv.mod_Zmod.
      rewrite Nat2Z.id.

      admit.
      admit.
    }

    rewrite EQ.
    auto.
  Admitted.

  Lemma genAExpr_correct_ind :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *)   (aexp: AExpr) (σ: evalContext) (memH: memoryH) (v : binary64)
      (* Vellvm bits *)   (e: exp typ) (c: code typ) (g : global_env) (l : local_env) (memV : memoryV),

      genAExpr aexp s1 ≡ inr (s2, (e, c))      -> (* Compilation succeeds *)
      evalAExpr memH σ aexp ≡ inr v            -> (* Evaluation succeeds *)
      state_invariant σ s1 memH (memV, (l, g)) -> (* The main state invariant is initially true *)

      eutt (lift_Rel_cfg (state_invariant σ s2) ⩕ genAExpr_rel σ aexp e memH (mk_config_cfg memV l g))
           (with_err_RB (interp_Mem (denoteAExpr σ aexp) memH))
           (with_err_LB (interp_cfg (denote_code (convert_typ [] c)) g l memV)).
  Proof.
    intros s1 s2 aexp; revert s1 s2; induction aexp; intros * COMPILE EVAL PRE.
    - (* Variable case *)
      (* Reducing the compilation *)
      pose proof COMPILE as COMPILE'.
      cbn* in COMPILE; simp.

      + (* The variable maps to an integer in the IRState *)
        unfold denoteAExpr; cbn*.

        repeat norm_v.
        break_inner_match_goal.
        repeat norm_h.

        * pose proof PRE as SINV.
          destruct PRE.
          break_inner_match_goal; try abs_by_WF.

          repeat norm_h.
          destruct i0; try abs_by_WF.

          (* Globals *)
          cbn.
          epose proof (memory_invariant_GLU_AExpr _ mem_is_inv0 Heqo Heqo0).
          destruct H as (ptr & MAP & READ).

          repeat norm_v; eauto.

          cbn. repeat norm_v.
          cbn. repeat norm_v.

          rewrite typ_to_dtyp_equation in *.
          cbn in READ.
          rewrite interp_cfg_to_L3_Load; eauto.

          repeat norm_v.
          rewrite interp_cfg_to_L3_LW.
          cbn. repeat norm_v.

          apply eqit_Ret.
          split.
          { cbn. eapply state_invariant_add_fresh; eauto.
          }
          {
            + split; split; intuition.
              * cbn. repeat norm_v. cbn. norm_v.
                reflexivity.
                cbn.
                erewrite H; eauto.
                eapply In_add_eq.
              * cbn. unfold context_lookup.
                rewrite Heqo0.
                cbn. reflexivity.
              * apply sub_alist_add.
                apply concrete_fresh_fresh in incLocal_is_fresh0.
                unfold incLocal_fresh in incLocal_is_fresh0.
                eapply incLocal_is_fresh0.
                cbn. eauto.
          }
        * (* Variable not in context, [context_lookup] fails *)
          cbn* in EVAL; rewrite Heqo0 in EVAL; inv EVAL.
      + (* The variable maps to a pointer *)
        unfold denoteAExpr; cbn*.
        repeat norm_v.
        destruct PRE.
        break_inner_match_goal; try abs_by_WF.
        * repeat norm_h.
          break_inner_match_goal; try abs_by_WF.
          subst.
          destruct i0; try abs_by_WF.
          repeat norm_h.
          apply eutt_Ret.
          split; split; eauto.
          -- split.
             { cbn; repeat norm_v; cbn; repeat norm_v; eauto.
               reflexivity.

               eapply memory_invariant_LLU_AExpr; eauto;
                 eapply memory_invariant_ext_local;
                 eauto.
             }

             cbn.
             unfold context_lookup.
             rewrite Heqo0. cbn.
             reflexivity.
        * cbn* in EVAL; rewrite Heqo0 in EVAL; inv EVAL.
    - (* Constant *)
      cbn* in COMPILE; simp.
      unfold denoteAExpr; cbn*.
      repeat norm_h.
      repeat norm_v.
      apply eutt_Ret.
      split; eauto.
      split; eauto.
      intros l' MONO; cbn*.
      split; try reflexivity.
      cbn in EVAL. inversion EVAL; subst.
      repeat norm_h.
      repeat norm_v.
      reflexivity.
    - (* ANth *)
      cbn* in COMPILE; simp.

      cbn* in EVAL.
      repeat (break_match; try discriminate EVAL).

      rewrite convert_typ_app.
      rewrite denote_code_app.

      (* I need to know something about c0, which is an NExpr. *)
      epose proof genNExpr_correct_ind _ Heqs Heqs3 PRE as NEXP.

      eutt_hide_right.
      cbn*.
      repeat norm_h.

      subst i4.
      do 2 norm_v.

      eapply eutt_clo_bind; eauto.
      intros [memH' n'] [memV' [l' [g' []]]] [SINV GENN_REL].

      (* Relate MExpr *)
      destruct GENN_REL as [NEXP_CORRECT VARS_s1_i].

      (* Need to know that memH'=memH and memV'=memV ... *)
      genNExpr_rel_subst LL'.

      cbn in SINV.

      (* Need to make sure that we pull e1 out so we can use genMExpr_correct *)
      (*
      epose proof genMExpr_correct _ Heqs0 Heqs4 SINV as MCODE.

      (* Should be able to pull e1 out from the denotation of GEP *)

      (* TODO: this is awful. *)
      change [(IId r,
                  INSTR_Op
                    (OP_GetElementPtr t (TYPE_Pointer t, e1)
                       [(IntType, EXP_Integer 0%Z); (IntType, e0)]));
                 (IId r0,
                 INSTR_Load false TYPE_Double (TYPE_Pointer TYPE_Double, EXP_Ident (ID_Local r))
                            (Some 8%Z))] with
          ([(IId r,
                  INSTR_Op
                    (OP_GetElementPtr t (TYPE_Pointer t, e1)
                       [(IntType, EXP_Integer 0%Z); (IntType, e0)]))] ++
          [(IId r0,
                 INSTR_Load false TYPE_Double (TYPE_Pointer TYPE_Double, EXP_Ident (ID_Local r))
                   (Some 8%Z))]).

      rewrite app_assoc.
      rewrite convert_typ_app.
      rewrite denote_code_app.

      rewrite convert_typ_app.
      rewrite denote_code_app.

      eutt_hide_left.

      (* I want to deconstruct denote_code of OP_GetElementPtr in
         order to expose the underlying denote_exp of e1. *)
      cbn.

      (* TODO: clean this up *)
      set (λ _ : (),
                ITree.bind
                  (ITree.bind
                     (translate exp_E_to_instr_E
                        (translate lookup_E_to_exp_E (trigger (LocalRead (Traversal.endo r)))))
                     (λ ua : uvalue,
                        ITree.bind (concretize_or_pick ua True)
                          (λ da : dvalue,
                             match da with
                             | DVALUE_Poison => raiseUB "Load from poisoned address."
                             | _ =>
                                 ITree.bind (trigger (Load (typ_to_dtyp [ ] TYPE_Double) da))
                                   (λ dv : uvalue, trigger (LocalWrite (Traversal.endo r0) dv))
                             end))) (λ _ : (), Ret ())) as blah.

      repeat rewrite <- bind_bind.
      setoid_rewrite translate_bind.
      rewrite <- bind_bind.

      assert ((denote_exp (Some (typ_to_dtyp [ ] (TYPE_Pointer t)))
                          (Traversal.fmap (typ_to_dtyp [ ]) e1)) ≡ (denote_exp (Some DTYPE_Pointer) (convert_typ [ ] e1))) as He1.
      { rewrite typ_to_dtyp_equation.
        reflexivity.
      }

      rewrite He1.

      set (ITree.bind (denote_code (convert_typ [ ] c1))
                      (λ _ : (),
                             translate exp_E_to_instr_E
                                       (denote_exp (Some DTYPE_Pointer) (convert_typ [ ] e1)))) as MYBIND.
      repeat norm_v.

      subst MYBIND.
      subst i4.
      repeat norm_h.

      (* Might not be true, might be extensions instead *)
      eapply eutt_clo_bind.
      apply MCODE.

      intros [memH'' b'] [memV'' [l'' [g'' uv'']]] MINV.

      subst blah. (* TODO: fix this up *)
      clear He1.

      repeat norm_v.

      destruct MINV as (SINV'' & MINV).

      (* Need to know that genMExpr does not affect memH / memV / g / l *)
      genMExpr_rel_subst.

      assert (mem_lookup (MInt64asNT.to_nat n') b' ≡ Some b) as LUPn'b'.
      { (* i2 = n', because:

           Heqs3: evalNExpr σ n = inr i2
           NEXP_CORRECT : genNExpr_rel σ n e0 memH (mk_config_cfg memV l g) (memH, n') (memV, (l', (g, ())))
         *)
        destruct NEXP_CORRECT as (NEXP_CORRECT & _).
        assert (l' ⊑ l') as L'L' by reflexivity.
        specialize (NEXP_CORRECT _ L'L') as (_ & NEXP_EVAL).
        rewrite Heqs3 in NEXP_EVAL; inv NEXP_EVAL.

        (* m0 = b', because:

           Heqs4 : evalMExpr memH σ m ≡ inr m0
           MINV : (lift_Rel_cfg (state_invariant σ i0) ⩕ genMExpr_rel σ i0 memH (mk_config_cfg memV l' g))
           (memH'', b') (memV'', (l'', (g'', uv'')))
         *)

        destruct MINV as (MINV & _).
        destruct MINV as (MINV & EVAL_MEXP).
        rewrite Heqs4 in EVAL_MEXP; inv EVAL_MEXP.

        auto.
      }

      rewrite LUPn'b'.
      repeat norm_h.

      progress cbn*.
      repeat rewrite typ_to_dtyp_equation.
      cbn*. repeat norm_v.
      destruct NEXP_CORRECT.
      unfold genNExpr_exp_correct in exp_correct0.
      subst.
      assert (l' ⊑ l') as L'L' by reflexivity.
      specialize (exp_correct0 _ L'L') as (NEXP_EUTT & NEXP_EVAL).
      setoid_rewrite <- NEXP_EUTT.

      setoid_rewrite bind_ret_l.
      progress repeat norm_v.

      destruct MINV as (MINV & PRESERVES).
      destruct MINV as ((ptr & i' & vid & mid & size & sz & RES & rest) & EVAL_MEXP).
      destruct rest as (MLUP & ILG & NTH_σ_vid & NTH_Γ_vid).
      subst uv''.

      cbn.
      unfold ITree.map.
      repeat norm_v.

      pose proof int_of_nat n' as (n'_nat & Hn').
      rewrite Hn'.

      (* Long path to rewriting with GEP lemma... *)
      pose proof genMExpr_array Heqs0 as (sz' & ARRAY).
      rewrite ARRAY.
      rewrite typ_to_dtyp_equation.
      rewrite exp_E_to_instr_E_Memory, subevent_subevent.
      epose proof interp_cfg_to_L3_GEP_array _ (DTYPE_Array sz' DTYPE_Double).

      destruct i'; cbn in ILG.
      { destruct ILG as (? & ? & CONTRA & REST).
        inv CONTRA. }

      cbn in SINV''.
      pose proof state_invariant_memory_invariant SINV'' as MINV.
      epose proof memory_invariant_LLU_Ptr vid MINV NTH_Γ_vid NTH_σ_vid as (bk_h & ptr_v & MLUP' & ILG' & GET_ARRAY).
      assert (ptr_v ≡ ptr).
      { (* ptr_v comes from memory_invariant_LLU_Ptr *)
        (* ILG : l' @ id = Some (UVALUE_Addr ptr) *)
        (* Use ILG' to relate... *)
        cbn in ILG'.
        rewrite ILG in ILG'.
        inversion ILG'.
        auto.
      }
      subst.

      rewrite MLUP in MLUP'. inv MLUP'.
      
      replace (MInt64asNT.to_nat (Int64.repr (Z.of_nat n'_nat))) with n'_nat in LUPn'b'.
      2: { symmetry. apply to_nat_repr_of_nat. }
      specialize (GET_ARRAY n'_nat b LUPn'b').
      epose proof interp_cfg_to_L3_GEP_array helix_intrinsics DTYPE_Double ptr sz' g l' memV _ n'_nat GET_ARRAY as (ptr' & EUTT_GEP & READ).

      rewrite EUTT_GEP.
      repeat norm_v.

      rewrite interp_cfg_to_L3_LW; cbn.
      repeat norm_v; cbn.
      repeat norm_v.

      2: { break_match; auto. apply neg_rel_dec_correct in Heqb0. contradiction. }

      cbn.
      repeat norm_v.
      rewrite interp_cfg_to_L3_Load; eauto.

      repeat norm_v.
      rewrite interp_cfg_to_L3_LW; cbn.
      repeat norm_v.

      (* TODO: Can probably be smarter about this *)
      Transparent incLocal.
      assert (r ≡ Name ("l" @@ string_of_nat (local_count i0))) as EQr.
      { unfold incLocal in Heqs1.
        cbn in Heqs1.
        inversion Heqs1.
        reflexivity.
      }
      assert (r0 ≡ Name ("l" @@ string_of_nat (local_count i1))) as EQr0.
      { unfold incLocal in Heqs2.
        cbn in Heqs2.
        inversion Heqs2.
        reflexivity.
      }
      Opaque incLocal.

      apply eqit_Ret.
      split.
      + do 2 (eapply state_invariant_add_fresh; eauto).
      + split; split; intuition.
        * cbn. repeat norm_v. cbn. norm_v.
          reflexivity.
          cbn.
          apply H0.
          apply In_add_eq.
        * (* TODO: ltac, this is horrid *)
          cbn.
          rewrite Heqs3.
          rewrite Heqs4.
          rewrite Heqo.
          reflexivity.
        * eapply sub_alist_trans; eauto.
          eapply sub_alist_trans; eapply sub_alist_add.
          -- unfold alist_fresh.
             apply alist_find_None.
             intros v0 IN.
             eapply In__alist_In in IN as [v' AIN].
             apply incLocal_is_fresh in SINV''.
             eapply SINV''; eauto.
          -- unfold alist_fresh.
             apply alist_find_None.
             intros v0 IN.
             eapply In__alist_In in IN as [v' AIN].
             epose proof (state_invariant_incLocal Heqs1 SINV'') as SINV_i1.
             apply incLocal_is_fresh in SINV_i1.
             eapply SINV_i1 with (id:=r0) (v:=v'); eauto.
             apply In_add_ineq_iff in AIN; auto.
             intros CONTRA; subst.
             (* TODO: don't do this :( *)
             Transparent incLocal.
             unfold incLocal in Heqs1.
             Opaque incLocal.
             cbn in Heqs1. inversion Heqs1.
             rewrite <- H2 in CONTRA.
             cbn in CONTRA.
             unfold Traversal.endo, Traversal.Endo_id in CONTRA.
             apply Name_inj, append_factor_left,string_of_nat_inj in CONTRA; lia.
    - (* AAbs *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in COMPILE; simp.

      cbn in EVAL.
      break_match; try discriminate EVAL.

      cbn*.
      repeat norm_h.

      (* TODO: Ltac for this. *)
      rewrite convert_typ_app.
      rewrite denote_code_app.

      repeat norm_v.
      eapply eutt_clo_bind; try eapply IHaexp; eauto.

      intros [memH2 b2] [memV2 [l2 [g2 []]]] [SINV EXPR_REL].
      cbn in SINV.
      destruct EXPR_REL as [AEXPR EXT].
      unfold genAExpr_exp_correct in AEXPR.
      unfold ext_local in EXT.
      cbn in EXT.
      repeat norm_h.

      cbn.
      repeat norm_v.
      rewrite typ_to_dtyp_equation.
      repeat norm_v.

      epose proof (AEXPR l2 _) as [EUTT EVAL'].
      rewrite <- EUTT.
      repeat norm_v.
      cbn; repeat norm_v.

      (* TODO: Maybe we should have more map lemmas *)
      unfold ITree.map.
      repeat norm_v.

      rewrite interp_cfg_to_L3_intrinsic; try reflexivity.
      cbn; repeat norm_v.

      rewrite interp_cfg_to_L3_LW.
      cbn; repeat norm_v.

      apply eqit_Ret.

      (* TODO: This is repeated a lot... Ltac? *)
      split.
      + eapply state_invariant_add_fresh; eauto.
      + split; split; intuition.
        * cbn. repeat norm_v. cbn. norm_v.
          reflexivity.
          cbn.

          apply H.

          (* TODO: Can't unfold Floats.Float.abs ??? *)
          (* TODO: Use Transparent... Still not obvious. *)
          assert (Floats.Float.abs b2 ≡ MFloat64asCT.CTypeAbs b2).
          admit.
          rewrite H3.
          apply In_add_eq.
        * (* TODO: ltac, this is horrid *)
          cbn. rewrite EVAL'.
          reflexivity.
        * rewrite H3.
          apply sub_alist_add.
          unfold alist_fresh.
          apply alist_find_None.
          intros v0. intros IN.
          eapply In__alist_In in IN as [v' AIN].
          apply incLocal_is_fresh in SINV.
          eapply SINV; eauto.
          (* TODO: there's probably a smarter way to do this case now *)
          Transparent incLocal.
          unfold incLocal in Heqs0.
          cbn in Heqs0.
          inversion Heqs0.
          reflexivity.
          Opaque incLocal.
    - (* APlus *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in COMPILE; simp.

      (* YZ TODO Ltac for this *)
      cbn in EVAL.
      break_match; try discriminate EVAL.
      break_match; try discriminate EVAL.

      cbn*.
      repeat norm_h.

      rewrite convert_typ_app.
      rewrite denote_code_app.
      repeat norm_v.

      eapply eutt_clo_bind; try eapply IHaexp1; eauto.

      intros [memH' b'] [memV' [l' [g' []]]] [INV1 INV2].
      cbn in *.

      repeat norm_h.

      rewrite convert_typ_app.
      rewrite denote_code_app.
      repeat norm_v.

      inversion INV2.
      inversion amonotone0.
      subst.
      eapply eutt_clo_bind; try eapply IHaexp2; eauto.

      intros [memH'' b''] [memV'' [l'' [g'' []]]] [INV1' INV2'].
      inversion INV2'.
      inversion amonotone1.
      subst.

      repeat norm_h.
      cbn. repeat norm_v.
      rewrite typ_to_dtyp_equation.

      unfold genAExpr_exp_correct in aexp_correct0.
      do 2 destruct H1.
      subst.
      specialize (aexp_correct0 l'').
      assert (Ret (memV'', (l'', (g'', UVALUE_Double b')))
                    ≈ with_err_LB
                        (interp_cfg
                           (translate exp_E_to_instr_E
                                      (denote_exp (Some DTYPE_Double) (convert_typ [ ] e0))) g'' l'' memV'')) as EUTT0.
      apply aexp_correct0; eauto.
      rewrite <- EUTT0.
      repeat norm_v.

      unfold genAExpr_exp_correct in aexp_correct1.
      assert (Ret (memV'', (l'', (g'', UVALUE_Double b'')))
                      ≈ with_err_LB
                          (interp_cfg
                             (translate exp_E_to_instr_E
                                        (denote_exp (Some DTYPE_Double) (convert_typ [ ] e1))) g'' l'' memV'')) as EUTT1.
      apply aexp_correct1; eauto. reflexivity.
      rewrite <- EUTT1.
      repeat norm_v.
      cbn.
      repeat norm_v.

      rewrite interp_cfg_to_L3_LW.
      cbn.
      repeat norm_v.

      apply eqit_Ret.
      split; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
      + split; split; intuition.
        * cbn. repeat norm_v. cbn. norm_v.
          reflexivity.
          cbn.

          apply H.

          (* TODO: Can't unfold Floats.Float.add ??? *)
          assert (Floats.Float.add b' b'' ≡ MFloat64asCT.CTypePlus b' b'').
          admit.
          rewrite H3.
          apply In_add_eq.
        * (* TODO: ltac, this is horrid *)
          cbn. rewrite H6.
          epose proof (aexp_correct1 l'' _) as [[] H7].
          rewrite H7.

          reflexivity.
        * rewrite H3. rewrite H2.
          apply sub_alist_add.
          unfold alist_fresh.
          cbn in INV1'.
          destruct INV1'.
          unfold concrete_fresh_inv in incLocal_is_fresh0.
          apply alist_find_None.
          intros v0. intros IN.
          eapply In__alist_In in IN as [v' AIN].
          eapply incLocal_is_fresh0; eauto.
          (* TODO: there's probably a smarter way to do this case now *)
          Transparent incLocal.
          unfold incLocal in Heqs1.
          cbn in Heqs1.
          inversion Heqs1.
          reflexivity.
          Opaque incLocal.
    - (* AMinus *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in COMPILE; simp.

      (* YZ TODO Ltac for this *)
      cbn in EVAL.
      break_match; try discriminate EVAL.
      break_match; try discriminate EVAL.

      cbn*.
      repeat norm_h.

      rewrite convert_typ_app.
      rewrite denote_code_app.
      repeat norm_v.

      eapply eutt_clo_bind; try eapply IHaexp1; eauto.

      intros [memH' b'] [memV' [l' [g' []]]] [INV1 INV2].
      cbn in *.

      repeat norm_h.

      rewrite convert_typ_app.
      rewrite denote_code_app.
      repeat norm_v.

      inversion INV2.
      inversion amonotone0.
      subst.
      eapply eutt_clo_bind; try eapply IHaexp2; eauto.

      intros [memH'' b''] [memV'' [l'' [g'' []]]] [INV1' INV2'].
      inversion INV2'.
      inversion amonotone1.
      subst.

      repeat norm_h.
      cbn. repeat norm_v.
      rewrite typ_to_dtyp_equation.

      unfold genAExpr_exp_correct in aexp_correct0.
      do 2 destruct H1.
      subst.
      specialize (aexp_correct0 l'').
      assert (Ret (memV'', (l'', (g'', UVALUE_Double b')))
                    ≈ with_err_LB
                        (interp_cfg
                           (translate exp_E_to_instr_E
                                      (denote_exp (Some DTYPE_Double) (convert_typ [ ] e0))) g'' l'' memV'')) as EUTT0.
      apply aexp_correct0; eauto.
      rewrite <- EUTT0.
      repeat norm_v.

      unfold genAExpr_exp_correct in aexp_correct1.
      assert (Ret (memV'', (l'', (g'', UVALUE_Double b'')))
                      ≈ with_err_LB
                          (interp_cfg
                             (translate exp_E_to_instr_E
                                        (denote_exp (Some DTYPE_Double) (convert_typ [ ] e1))) g'' l'' memV'')) as EUTT1.
      apply aexp_correct1; eauto. reflexivity.
      rewrite <- EUTT1.
      repeat norm_v.
      cbn.
      repeat norm_v.

      rewrite interp_cfg_to_L3_LW.
      cbn.
      repeat norm_v.

      apply eqit_Ret.
      split; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
      + split; split; intuition.
        * cbn. repeat norm_v. cbn. norm_v.
          reflexivity.
          cbn.

          apply H.

          (* TODO: Can't unfold Floats.Float.add ??? *)
          assert (Floats.Float.sub b' b'' ≡ MFloat64asCT.CTypeSub b' b'').
          admit.
          rewrite H3.
          apply In_add_eq.
        * (* TODO: ltac, this is horrid *)
          cbn. rewrite H6.
          epose proof (aexp_correct1 l'' _) as [[] H7].
          rewrite H7.

          reflexivity.
        * rewrite H3. rewrite H2.
          apply sub_alist_add.
          unfold alist_fresh.
          cbn in INV1'.
          destruct INV1'.
          unfold concrete_fresh_inv in incLocal_is_fresh0.
          apply alist_find_None.
          intros v0. intros IN.
          eapply In__alist_In in IN as [v' AIN].
          eapply incLocal_is_fresh0; eauto.
          (* TODO: there's probably a smarter way to do this case now *)
          Transparent incLocal.
          unfold incLocal in Heqs1.
          cbn in Heqs1.
          inversion Heqs1.
          reflexivity.
          Opaque incLocal.
    - (* AMult *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in COMPILE; simp.

      cbn in EVAL.
      break_match; try discriminate EVAL.
      break_match; try discriminate EVAL.

      cbn*.
      repeat norm_h.

      rewrite convert_typ_app.
      rewrite denote_code_app.
      repeat norm_v.

      eapply eutt_clo_bind; try eapply IHaexp1; eauto.

      intros [memH' b'] [memV' [l' [g' []]]] [INV1 INV2].
      cbn in *.

      repeat norm_h.

      rewrite convert_typ_app.
      rewrite denote_code_app.
      repeat norm_v.

      inversion INV2.
      inversion amonotone0.
      subst.
      eapply eutt_clo_bind; try eapply IHaexp2; eauto.

      intros [memH'' b''] [memV'' [l'' [g'' []]]] [INV1' INV2'].
      inversion INV2'.
      inversion amonotone1.
      subst.

      repeat norm_h.
      cbn. repeat norm_v.
      rewrite typ_to_dtyp_equation.

      unfold genAExpr_exp_correct in aexp_correct0.
      do 2 destruct H1.
      subst.
      specialize (aexp_correct0 l'').
      assert (Ret (memV'', (l'', (g'', UVALUE_Double b')))
                    ≈ with_err_LB
                        (interp_cfg
                           (translate exp_E_to_instr_E
                                      (denote_exp (Some DTYPE_Double) (convert_typ [ ] e0))) g'' l'' memV'')) as EUTT0.
      apply aexp_correct0; eauto.
      rewrite <- EUTT0.
      repeat norm_v.

      unfold genAExpr_exp_correct in aexp_correct1.
      assert (Ret (memV'', (l'', (g'', UVALUE_Double b'')))
                      ≈ with_err_LB
                          (interp_cfg
                             (translate exp_E_to_instr_E
                                        (denote_exp (Some DTYPE_Double) (convert_typ [ ] e1))) g'' l'' memV'')) as EUTT1.
      apply aexp_correct1; eauto. reflexivity.
      rewrite <- EUTT1.
      repeat norm_v.
      cbn.
      repeat norm_v.

      rewrite interp_cfg_to_L3_LW.
      cbn.
      repeat norm_v.

      apply eqit_Ret.
      split; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
      + split; split; intuition.
        * cbn. repeat norm_v. cbn. norm_v.
          reflexivity.
          cbn.

          apply H.

          (* TODO: Can't unfold Floats.Float.add ??? *)
          assert (Floats.Float.mul b' b'' ≡ MFloat64asCT.CTypeMult b' b'').
          admit.
          rewrite H3.
          apply In_add_eq.
        * (* TODO: ltac, this is horrid *)
          cbn. rewrite H6.
          epose proof (aexp_correct1 l'' _) as [[] H7].
          rewrite H7.

          reflexivity.
        * rewrite H3. rewrite H2.
          apply sub_alist_add.
          unfold alist_fresh.
          cbn in INV1'.
          destruct INV1'.
          unfold concrete_fresh_inv in incLocal_is_fresh0.
          apply alist_find_None.
          intros v0. intros IN.
          eapply In__alist_In in IN as [v' AIN].
          eapply incLocal_is_fresh0; eauto.
          (* TODO: there's probably a smarter way to do this case now *)
          Transparent incLocal.
          unfold incLocal in Heqs1.
          cbn in Heqs1.
          inversion Heqs1.
          reflexivity.
          Opaque incLocal.
    - (* AMin *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in COMPILE; simp.

      (* YZ TODO Ltac for this *)
      cbn in EVAL.
      break_match; try discriminate EVAL.
      break_match; try discriminate EVAL.

      cbn*.
      repeat norm_h.

      rewrite convert_typ_app.
      rewrite denote_code_app.
      repeat norm_v.

      eapply eutt_clo_bind; try eapply IHaexp1; eauto.

      intros [memH' b'] [memV' [l' [g' []]]] [INV1 INV2].
      cbn in *.

      repeat norm_h.

      rewrite convert_typ_app.
      rewrite denote_code_app.
      repeat norm_v.

      inversion INV2.
      inversion amonotone0.
      subst.
      eapply eutt_clo_bind; try eapply IHaexp2; eauto.

      intros [memH'' b''] [memV'' [l'' [g'' []]]] [INV1' INV2'].
      inversion INV2'.
      inversion amonotone1.
      subst.

      repeat norm_h.
      cbn. repeat norm_v.
      rewrite typ_to_dtyp_equation.

      unfold genAExpr_exp_correct in aexp_correct0.
      do 2 destruct H1.
      subst.
      specialize (aexp_correct0 l'').
      assert (Ret (memV'', (l'', (g'', UVALUE_Double b')))
                    ≈ with_err_LB
                        (interp_cfg
                           (translate exp_E_to_instr_E
                                      (denote_exp (Some DTYPE_Double) (convert_typ [ ] e0))) g'' l'' memV'')) as EUTT0.
      apply aexp_correct0; eauto.
      rewrite <- EUTT0.
      repeat norm_v.

      unfold genAExpr_exp_correct in aexp_correct1.
      assert (Ret (memV'', (l'', (g'', UVALUE_Double b'')))
                      ≈ with_err_LB
                          (interp_cfg
                             (translate exp_E_to_instr_E
                                        (denote_exp (Some DTYPE_Double) (convert_typ [ ] e1))) g'' l'' memV'')) as EUTT1.
      apply aexp_correct1; eauto. reflexivity.
      rewrite <- EUTT1.
      repeat norm_v.
      cbn.
      repeat norm_v.

      unfold ITree.map.
      repeat norm_v.

      rewrite interp_cfg_to_L3_intrinsic; try reflexivity.
      cbn; repeat norm_v.

      rewrite interp_cfg_to_L3_LW.
      cbn; repeat norm_v.

      apply eqit_Ret.
      split; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
      + split; split; intuition.
        * cbn. repeat norm_v. cbn. norm_v.
          reflexivity.
          cbn.
          apply H.

          (* TODO: Can't unfold Floats.Float.add ??? *)
          assert (Float_minimum b' b'' ≡ MFloat64asCT.CTypeMin b' b'').
          admit.
          rewrite H3.
          apply In_add_eq.
        * (* TODO: ltac, this is horrid *)
          cbn. rewrite H6.
          epose proof (aexp_correct1 l'' _) as [[] H7].
          rewrite H7.

          reflexivity.
        * rewrite H3. rewrite H2.
          apply sub_alist_add.
          unfold alist_fresh.
          cbn in INV1'.
          destruct INV1'.
          unfold concrete_fresh_inv in incLocal_is_fresh0.
          apply alist_find_None.
          intros v0. intros IN.
          eapply In__alist_In in IN as [v' AIN].
          eapply incLocal_is_fresh0; eauto.
          (* TODO: there's probably a smarter way to do this case now *)
          Transparent incLocal.
          unfold incLocal in Heqs1.
          cbn in Heqs1.
          inversion Heqs1.
          reflexivity.
          Opaque incLocal.
    - (* AMax *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in COMPILE; simp.

      cbn in EVAL.
      break_match; try discriminate EVAL.
      break_match; try discriminate EVAL.

      cbn*.
      repeat norm_h.

      rewrite convert_typ_app.
      rewrite denote_code_app.
      repeat norm_v.

      eapply eutt_clo_bind; try eapply IHaexp1; eauto.

      intros [memH' b'] [memV' [l' [g' []]]] [INV1 INV2].
      cbn in *.

      repeat norm_h.

      rewrite convert_typ_app.
      rewrite denote_code_app.
      repeat norm_v.

      inversion INV2.
      inversion amonotone0.
      subst.
      eapply eutt_clo_bind; try eapply IHaexp2; eauto.

      intros [memH'' b''] [memV'' [l'' [g'' []]]] [INV1' INV2'].
      inversion INV2'.
      inversion amonotone1.
      subst.

      repeat norm_h.
      cbn. repeat norm_v.
      rewrite typ_to_dtyp_equation.

      unfold genAExpr_exp_correct in aexp_correct0.
      do 2 destruct H1.
      subst.
      specialize (aexp_correct0 l'').
      assert (Ret (memV'', (l'', (g'', UVALUE_Double b')))
                    ≈ with_err_LB
                        (interp_cfg
                           (translate exp_E_to_instr_E
                                      (denote_exp (Some DTYPE_Double) (convert_typ [ ] e0))) g'' l'' memV'')) as EUTT0.
      apply aexp_correct0; eauto.
      rewrite <- EUTT0.
      repeat norm_v.

      unfold genAExpr_exp_correct in aexp_correct1.
      assert (Ret (memV'', (l'', (g'', UVALUE_Double b'')))
                      ≈ with_err_LB
                          (interp_cfg
                             (translate exp_E_to_instr_E
                                        (denote_exp (Some DTYPE_Double) (convert_typ [ ] e1))) g'' l'' memV'')) as EUTT1.
      apply aexp_correct1; eauto. reflexivity.
      rewrite <- EUTT1.
      repeat norm_v.
      cbn.
      repeat norm_v.

      unfold ITree.map.
      repeat norm_v.

      rewrite interp_cfg_to_L3_intrinsic; try reflexivity.
      cbn; repeat norm_v.

      rewrite interp_cfg_to_L3_LW.
      cbn; repeat norm_v.

      apply eqit_Ret.
      split; cbn; eauto.
      + eapply state_invariant_add_fresh; eauto.
      + split; split; intuition.
        * cbn. repeat norm_v. cbn. norm_v.
          reflexivity.
          cbn.
          apply H.

          assert (Float_maxnum b' b'' ≡ MFloat64asCT.CTypeMax b' b'').
          admit.
          rewrite H3.
          apply In_add_eq.
        * (* TODO: ltac, this is horrid *)
          cbn. rewrite H6.
          epose proof (aexp_correct1 l'' _) as [[] H7].
          rewrite H7.

          reflexivity.
        * rewrite H3. rewrite H2.
          apply sub_alist_add.
          unfold alist_fresh.
          cbn in INV1'.
          destruct INV1'.
          unfold concrete_fresh_inv in incLocal_is_fresh0.
          apply alist_find_None.
          intros v0. intros IN.
          eapply In__alist_In in IN as [v' AIN].
          eapply incLocal_is_fresh0; eauto.
          (* TODO: there's probably a smarter way to do this case now *)
          Transparent incLocal.
          unfold incLocal in Heqs1.
          cbn in Heqs1.
          inversion Heqs1.
          reflexivity.
          Opaque incLocal.
    - (* AZless *)
      rename g into g1, l into l1, memV into memV1.
      cbn* in COMPILE; simp.

      cbn in EVAL.
      break_match; try discriminate EVAL.
      break_match; try discriminate EVAL.

      cbn*.
      repeat norm_h.

      rewrite convert_typ_app.
      rewrite denote_code_app.
      repeat norm_v.

      eapply eutt_clo_bind; try eapply IHaexp1; eauto.

      intros [memH' b'] [memV' [l' [g' []]]] [INV1 INV2].
      cbn in *.

      repeat norm_h.

      rewrite convert_typ_app.
      rewrite denote_code_app.
      repeat norm_v.

      inversion INV2.
      inversion amonotone0.
      subst.
      eapply eutt_clo_bind; try eapply IHaexp2; eauto.

      intros [memH'' b''] [memV'' [l'' [g'' []]]] [INV1' INV2'].
      inversion INV2'.
      inversion amonotone1.
      subst.

      change [(IId r, INSTR_Op (OP_FCmp FOlt TYPE_Double e0 e1));
                (IVoid i4, INSTR_Comment "Casting bool to float");
                (IId r0,
                 INSTR_Op (OP_Conversion Uitofp (TYPE_I 1%Z) (EXP_Ident (ID_Local r)) TYPE_Double))]
        with
          ([(IId r, INSTR_Op (OP_FCmp FOlt TYPE_Double e0 e1))] ++
           [(IVoid i4, INSTR_Comment "Casting bool to float");
            (IId r0,
             INSTR_Op (OP_Conversion Uitofp (TYPE_I 1%Z) (EXP_Ident (ID_Local r)) TYPE_Double))]).

      rewrite convert_typ_app.
      rewrite denote_code_app.

      repeat norm_h.
      repeat norm_v.
      cbn; repeat norm_v.

      unfold genAExpr_exp_correct in aexp_correct0.
      do 2 destruct H1.
      subst.
      specialize (aexp_correct0 l'').
      assert (Ret (memV'', (l'', (g'', UVALUE_Double b')))
                    ≈ with_err_LB
                        (interp_cfg
                           (translate exp_E_to_instr_E
                                      (denote_exp (Some DTYPE_Double) (convert_typ [ ] e0))) g'' l'' memV'')) as EUTT0.
      apply aexp_correct0; eauto.

      (* TODO: This could be cleaner... *)
      repeat rewrite typ_to_dtyp_equation.
      repeat setoid_rewrite translate_bind.
      setoid_rewrite interp_cfg_to_L3_bind.
      repeat setoid_rewrite translate_bind.
      rewrite <- EUTT0.

      repeat norm_v.
      setoid_rewrite translate_bind.

      unfold genAExpr_exp_correct in aexp_correct1.
      assert (Ret (memV'', (l'', (g'', UVALUE_Double b'')))
                      ≈ with_err_LB
                          (interp_cfg
                             (translate exp_E_to_instr_E
                                        (denote_exp (Some DTYPE_Double) (convert_typ [ ] e1))) g'' l'' memV'')) as EUTT1.
      apply aexp_correct1; eauto. reflexivity.
      rewrite <- EUTT1.
      repeat norm_v.
      cbn.
      repeat norm_v.

      rewrite interp_cfg_to_L3_LW.
      cbn; repeat norm_v.
      cbn; repeat norm_v.
      2: apply In_add_eq.

      (* TODO: probably want a lemma for this *)
      unfold uvalue_to_dvalue_uop.
      rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
      cbn.

      unfold Traversal.endo.
      unfold Traversal.Endo_id.

      (* Should probably separate this into an existential lemma *)
      unfold double_cmp.
      destruct (ordered64 b' b'' && Floats.Float.cmp Integers.Clt b' b'')%bool eqn:CMP.
      { cbn.
        unfold ITree.map.
        repeat norm_v.
        rewrite interp_cfg_to_L3_LW.
        cbn.
        repeat norm_v.

        apply eqit_Ret.
        split; cbn; eauto.
        + eapply state_invariant_add_fresh; eauto.
          (* incVoid of i1... *)
          cbn. admit.
          admit.
        + split; split; intuition.
          * cbn. repeat norm_v. cbn. norm_v.
            reflexivity.
            cbn.
            apply H.
            assert ((Floats.Float.of_longu (DynamicValues.Int64.repr 1)) ≡ MFloat64asCT.CTypeZLess b' b'').
            admit.
            rewrite H3.
            apply In_add_eq.
          * (* TODO: ltac, this is horrid *)
            cbn. rewrite H6.
            epose proof (aexp_correct1 l'' _) as [[] H7].
            rewrite H7.

            reflexivity.
          * rewrite H3. rewrite H2.

            cbn in INV1'.
            destruct INV1'.
            unfold concrete_fresh_inv in incLocal_is_fresh0.

            cbn in INV1.
            destruct INV1.
            unfold concrete_fresh_inv in incLocal_is_fresh1.

            Transparent incLocal.
            unfold incLocal in Heqs1, Heqs2.
            inversion Heqs1.
            inversion Heqs2.
            Opaque incLocal.

            assert (l'' ⊑ (alist_add r (UVALUE_I1 DynamicValues.Int1.one) l'')) as TRANS.
            { apply sub_alist_add.
              unfold alist_fresh.
              apply alist_find_None.
              intros v0 IN.
              eapply In__alist_In in IN as [v' AIN].
              eapply incLocal_is_fresh0; eauto.
            }
            
            eapply (sub_alist_trans _ _ _ TRANS).
            unfold ext_local in *.
            cbn in *.

            subst. cbn.
            apply sub_alist_add.
            unfold alist_fresh.
            apply alist_find_None.
            intros v0 IN.
            eapply In__alist_In in IN as [v' AIN].

            eapply incLocal_is_fresh0 with (n:=S (local_count i0)); eauto.
            assert (Name ("l" @@ string_of_nat (S (local_count i0))) <> (Name ("l" @@ string_of_nat (local_count i0)))) as NEQ.
            { intros CONTRA.
              apply Name_inj, append_factor_left,string_of_nat_inj in CONTRA; lia.
            }
            apply (In_add_In_ineq _ _ _ _ _ NEQ AIN).
      }
      {
        admit.
      }
       *)
  Admitted.


  (* TODO: WF_IRState shouldn't be needed, it's part of R_AExpr_start *)
  Lemma genAExpr_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *)   (aexp: AExpr) (σ: evalContext) (memH: memoryH)
      (* Vellvm bits *)   (exp: exp typ) (c: code typ) (g : global_env) (l : local_env) (memV : memoryV) (τ: typ),
      genAExpr aexp s1 ≡ inr (s2, (exp, c)) -> (* Compilation succeeds *)
      state_invariant σ s1 memH (memV, (l, g)) ->
       eutt (R_AExpr σ s2)
            (with_err_RB
               (interp_Mem (denoteAExpr σ aexp)
                           memH))
            (with_err_LB
               ((interp_cfg (D.denote_code (convert_typ [] c) ;; translate exp_E_to_instr_E (D.denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] exp))))
                  g l memV)).
  Proof.
    (* intros s1 s2 aexp σ memH exp c g l memV τ H H0. *)
    (* induction aexp. *)
    (* - (* AVar *) *)
    (*   (* TODO: clean this all up. Extract useful LTAC. *)

    (*      Wait until Vadim gets back about bogus pointer cases. *)
    (*    *) *)
    (*   pose proof Hgen as Hgen'. *)
    (*   simp_comp Hgen. *)
    (*   + cbn*; repeat norm_h; repeat norm_v. *)

    (*     match goal with *)
    (*     | Hwf  : WF_IRState ?σ ?ir, *)
    (*       Hnth : nth_error (Γ ?ir) ?v ≡ Some ?x *)
    (*       |- context[context_lookup ?err ?σ ?v] => *)
    (*       pose proof (context_lookup_succeeds v err Hwf Hnth) as Hctx; *)
    (*       destruct Hctx as [val [Hctx Hnth_σ]] *)
    (*     end. *)

    (*     rewrite Hctx. *)
    (*     repeat norm_h. *)

    (*     destruct val. *)
    (*     admit. Focus 2. admit. (* Exceptions *) *)

    (*     repeat norm_h. *)

    (*     destruct i0 eqn:Hi. *)
    (*     cbn. *)
    (*     repeat norm_v. *)
    (*     setoid_rewrite translate_ret. *)
    (*     repeat norm_v. *)

    (*     (* Lookup *) *)
    (*     Focus 2. cbn*. *)
    (*     unfold Traversal.endo. *)
    (*     unfold R_AExpr_start in Hmem. *)
    (*     unfold memory_invariant in Hmem. *)
    (*     destruct Hmem as [_ Hmem]. *)

    (*     match goal with *)
    (*     | Hnth : nth_error ?σ ?v ≡ Some ?val, *)
    (*       Hnth_ir : nth_error (Γ ?st) ?v ≡ Some (?id, ?τ) *)
    (*       |- _ => *)
    (*       let H := fresh H in *)
    (*       pose proof (Hmem v val τ id) Hnth Hnth_ir as H; *)
    (*         cbn in H *)
    (*     end. *)

    (*     apply H. *)

    (*     cbn. repeat norm_v. *)

    (*     rewrite typ_to_dtyp_equation. *)
    (*     admit. *)

    (*     (* Local case. *) *)
    (*     cbn. *)
    (*     repeat norm_v. *)
    (*     Focus 2. *)
    (*     unfold Traversal.endo. *)
    (*     unfold R_AExpr_start in Hmem. *)
    (*     unfold memory_invariant in Hmem. *)
    (*     destruct Hmem as [_ Hmem]. *)

    (*     match goal with *)
    (*     | Hnth : nth_error ?σ ?v ≡ Some ?val, *)
    (*       Hnth_ir : nth_error (Γ ?st) ?v ≡ Some (?id, ?τ) *)
    (*       |- _ => *)
    (*       let H := fresh H in *)
    (*       pose proof (Hmem v val τ id) Hnth Hnth_ir as H; *)
    (*         cbn in H *)
    (*     end. *)

    (*     apply H. *)

    (*     setoid_rewrite translate_ret. *)
    (*     repeat norm_v. *)
    (*     cbn. *)
    (*     repeat norm_v. *)
    (*     admit. *)
    (*   + cbn*; repeat norm_h; repeat norm_v. *)

    (*     match goal with *)
    (*     | Hwf  : WF_IRState ?σ ?ir, *)
    (*       Hnth : nth_error (Γ ?ir) ?v ≡ Some ?x *)
    (*       |- context[context_lookup ?err ?σ ?v] => *)
    (*       pose proof (context_lookup_succeeds v err Hwf Hnth) as Hctx; *)
    (*       destruct Hctx as [val [Hctx Hnth_σ]] *)
    (*     end. *)

    (*     rewrite Hctx. *)
    (*     repeat norm_h. *)

    (*     destruct val. admit. Focus 2. admit. *)
    (*     repeat norm_h. *)

    (*     destruct i0; *)
    (*       cbn; repeat norm_v; *)
    (*         cbn; repeat norm_v. *)

    (*     Focus 2. *)
    (*     unfold Traversal.endo. *)
    (*     unfold R_AExpr_start in Hmem. *)
    (*     unfold memory_invariant in Hmem. *)
    (*     destruct Hmem as [_ Hmem]. *)

    (*     match goal with *)
    (*     | Hnth : nth_error ?σ ?v ≡ Some ?val, *)
    (*       Hnth_ir : nth_error (Γ ?st) ?v ≡ Some (?id, ?τ) *)
    (*       |- _ => *)
    (*       let H := fresh H in *)
    (*       pose proof (Hmem v val τ id) Hnth Hnth_ir as H; *)
    (*         cbn in H *)
    (*     end. *)

    (*     apply H. *)

    (*     Focus 3. *)
    (*     unfold Traversal.endo. *)
    (*     unfold R_AExpr_start in Hmem. *)
    (*     unfold memory_invariant in Hmem. *)
    (*     destruct Hmem as [_ Hmem]. *)

    (*     match goal with *)
    (*     | Hnth : nth_error ?σ ?v ≡ Some ?val, *)
    (*       Hnth_ir : nth_error (Γ ?st) ?v ≡ Some (?id, ?τ) *)
    (*       |- _ => *)
    (*       let H := fresh H in *)
    (*       pose proof (Hmem v val τ id) Hnth Hnth_ir as H; *)
    (*         cbn in H *)
    (*     end. *)

    (*     apply H. *)

    (*     all: apply eqit_Ret; unfold R_AExpr; auto. *)
    (*  - (* AConst *) *)
    (*   (* TODO: may want to move this to toplevel *) *)
    (*   simp_comp Hgen; *)
    (*     cbn*; repeat norm_h; repeat norm_v. *)

    (*   apply eqit_Ret; auto. *)
    (* - (* ANth *) *)
    (*   admit. *)
    (* - (* AAbs *) *)
    (*   admit. *)
    (* - (* APlus *) *)
    (*   admit. *)
    (* - (* AMinus *) *)
    (*   admit. *)
    (* - (* AMult *) *)
    (*   admit. *)
    (* - (* AMin *) *)
    (*   admit. *)
    (* - (* AMax *) *)
    (*   admit. *)
    (* - (* AZless *) *)
    (*   admit. *)
  Admitted.

End AExpr.

Section MemCopy.
  (** ** Compilation of MemCopy TODO
      Unclear how to state this at the moment.
      What is on the Helix side? What do the arguments correspond to?
   *)

  Lemma genMemCopy_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *)   (σ: evalContext)
      (* Vellvm bits *)   (i o n: Int64.int) (x y: ident) (nextblock bid: block_id) (bks : list (LLVMAst.block typ)),
      genMemCopy i o n x y nextblock s1 ≡ inr (s2, (bid, bks)) -> (* Compilation succeeds *)
      WF_IRState σ s1 ->                                      (* Well-formed IRState *)
      False.
      (* eutt R'
            (translate_E_helix_cfg
               (interp_Mem (denoteAexp σ aexp)
                           memH))
            (translate_E_vellvm_cfg
               ((interp_cfg (D.denote_code (convert_typ [] c) ;; translate exp_E_to_instr_E (D.denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] exp))))
                  g l memV)).
       *)
  Proof.
  Admitted.

End MemCopy.

Section FSHAssign.
  (** ** Compilation of FSHAssign TODO
      Unclear how to state this at the moment
      What is on the Helix side? What do the arguments correspond to?
   *)
  Lemma genFSHAssign_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *)   (σ: evalContext)
      (* Vellvm bits *)   (i o: Int64.int) (x y: ident) (src dst: NExpr) (nextblock bid: block_id) (bks : list (LLVMAst.block typ)),
      genFSHAssign i o x y src dst nextblock s1 ≡ inr (s2, (bid, bks)) -> (* Compilation succeeds *)
      WF_IRState σ s1 ->                                      (* Well-formed IRState *)
      False.
      (* eutt R'
            (translate_E_helix_cfg
               (interp_Mem (denoteAexp σ aexp)
                           memH))
            (translate_E_vellvm_cfg
               ((interp_cfg (D.denote_code (convert_typ [] c) ;; translate exp_E_to_instr_E (D.denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] exp))))
                  g l memV)).
       *)
  Proof.
  Admitted.

End FSHAssign.

Section WhileLoop.
  (** ** Compilation of loops TODO
      Unclear how to state this at the moment
      What is on the Helix side? What do the arguments correspond to?
   *)

  Lemma genWhileLoop_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *) (σ: evalContext)
      (* Vellvm bits *) (prefix: string) (from to: exp typ) (loopvar: raw_id) (loopcontblock: block_id)
                        (body_entry: block_id) (body_blocks: list (LLVMAst.block typ)) (init_code: (code typ))
                        (nextblock: block_id) (bid: block_id) (bks : list (LLVMAst.block typ)),
      genWhileLoop prefix from to loopvar loopcontblock body_entry body_blocks init_code nextblock s1 ≡ inr (s2, (bid, bks)) -> (* Compilation succeeds *)
      WF_IRState σ s1 ->                                      (* Well-formed IRState *)
      False.
      (* eutt R'
            (translate_E_helix_cfg
               (interp_Mem (denoteAexp σ aexp)
                           memH))
            (translate_E_vellvm_cfg
               ((interp_cfg (D.denote_code (convert_typ [] c) ;; translate exp_E_to_instr_E (D.denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] exp))))
                  g l memV)).
       *)
  Proof.
  Admitted.

End WhileLoop.

Section IMapBody.
  (** ** Compilation of IMapBody TODO
   *)

  Lemma genIMapBody_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *) (σ: evalContext) (f: AExpr)
      (* Vellvm bits *) (i o: Int64.int) (x y: ident) (loopvar: raw_id) (nextblock: block_id) (bid: block_id) (bks: list (LLVMAst.block typ)),
      genIMapBody i o x y f loopvar nextblock s1 ≡ inr (s2, (bid, bks)) -> (* Compilation succeeds *)
      WF_IRState σ s1 ->                                      (* Well-formed IRState *)
      False.
      (* eutt R'
            (translate_E_helix_cfg
               (interp_Mem (denoteAexp σ aexp)
                           memH))
            (translate_E_vellvm_cfg
               ((interp_cfg (D.denote_code (convert_typ [] c) ;; translate exp_E_to_instr_E (D.denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] exp))))
                  g l memV)).
       *)
  Proof.
  Admitted.

End IMapBody.

Section BinOpBody.
  (** ** Compilation of IMapBody TODO
   *)

  Lemma genBinOpBody_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *) (σ: evalContext) (f: AExpr)
      (* Vellvm bits *) (i o: Int64.int) (n: nat) (x y: ident) (loopvar: raw_id) (nextblock: block_id) (bid: block_id) (bks: list (LLVMAst.block typ)),
      genBinOpBody i o n x y f loopvar nextblock s1 ≡ inr (s2, (bid, bks)) -> (* Compilation succeeds *)
      WF_IRState σ s1 ->                                      (* Well-formed IRState *)
      False.
      (* eutt R'
            (translate_E_helix_cfg
               (interp_Mem (denoteAexp σ aexp)
                           memH))
            (translate_E_vellvm_cfg
               ((interp_cfg (D.denote_code (convert_typ [] c) ;; translate exp_E_to_instr_E (D.denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] exp))))
                  g l memV)).
       *)
  Proof.
  Admitted.

End BinOpBody.

Section MemMap2Body.
  (** ** Compilation of IMapBody TODO
   *)

  Lemma genMemMap2Body_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *) (σ: evalContext) (f: AExpr)
      (* Vellvm bits *) (i0 i1 o: Int64.int) (n: nat) (x x0 y: ident) (loopvar: raw_id) (nextblock: block_id) (bid: block_id) (bks: list (LLVMAst.block typ)),
      genMemMap2Body i0 i1 o x x0 y f loopvar nextblock s1 ≡ inr (s2, (bid, bks)) -> (* Compilation succeeds *)
      WF_IRState σ s1 ->                                      (* Well-formed IRState *)
      False.
      (* eutt R'
            (translate_E_helix_cfg
               (interp_Mem (denoteAexp σ aexp)
                           memH))
            (translate_E_vellvm_cfg
               ((interp_cfg (D.denote_code (convert_typ [] c) ;; translate exp_E_to_instr_E (D.denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] exp))))
                  g l memV)).
       *)
  Proof.
  Admitted.

End MemMap2Body.

Section MemInit.
  (** ** Compilation of IMapBody TODO
      Hmm this one even refuses to get admitted!
   *)

(*
  Lemma genMemInit_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *) (σ: evalContext) (initial: binary64)
      (* Vellvm bits *) (size: Int64.int) (y: ident) (nextblock: block_id) (bid: block_id) (bks: list (LLVMAst.block typ)),
      genMemInit size y initial nextblock s1 ≡ inr (s2, (bid, bks)) -> (* Compilation succeeds *)
      WF_IRState σ s1 ->                                      (* Well-formed IRState *)
      False.
      (* eutt R'
            (translate_E_helix_cfg
               (interp_Mem (denoteAexp σ aexp)
                           memH))
            (translate_E_vellvm_cfg
               ((interp_cfg (D.denote_code (convert_typ [] c) ;; translate exp_E_to_instr_E (D.denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] exp))))
                  g l memV)).
       *)
  Proof.
  Admitted.
  *)

End MemInit.

Section Power.
  (** ** Compilation of IMapBody TODO
   *)

  Lemma genPower_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *) (σ: evalContext) (src dst: NExpr) (n: NExpr) (f: AExpr)
      (* Vellvm bits *) (i o: Int64.int) (x y: ident) (initial: binary64) (nextblock: block_id) (bid: block_id) (bks: list (LLVMAst.block typ)),
      genPower i o x y src dst n f initial nextblock s1 ≡ inr (s2, (bid, bks)) -> (* Compilation succeeds *)
      WF_IRState σ s1 ->                                      (* Well-formed IRState *)
      False.
      (* eutt R'
            (translate_E_helix_cfg
               (interp_Mem (denoteAexp σ aexp)
                           memH))
            (translate_E_vellvm_cfg
               ((interp_cfg (D.denote_code (convert_typ [] c) ;; translate exp_E_to_instr_E (D.denote_exp (Some (DTYPE_I 64%Z)) (convert_typ [] exp))))
                  g l memV)).
       *)
  Proof.
  Admitted.

End Power.

Section Resolve_PVar.

  (* Lemma compile_FSHCOL_correct : *)
  (*   forall (** Compiler bits *) (s1 s2: IRState) *)
  (*     (** Helix bits    *) (op: DSHOperator) (σ : evalContext) (memH : memoryH) *)
  (*     (** Vellvm bits   *) (nextblock bid_in : block_id) (bks : list (LLVMAst.block typ)) *)
  (*     (env : list (ident * typ))  (g : global_env) (ρ : local_env) (memV : memoryV), *)
  (*     nextblock ≢ bid_in -> (* YZ: not sure about this yet *) *)
  (*     R σ s1 (memH,tt) (memV, (ρ, (g, (inl bid_in)))) -> *)
  (*     genIR op nextblock s1 ≡ inr (s2,(bid_in,bks)) -> *)
  (*     eutt (R σ s1) *)
  (*          (with_err_RB *)
  (*             (interp_Mem (denoteDSHOperator σ op) memH)) *)
  (*          (with_err_LB *)
  (*             (interp_cfg (D.denote_bks (convert_typ env bks) bid_in) *)
  (*                               g ρ memV)). *)
  (* Proof. *)



End Resolve_PVar.


(* TO MOVE *)
Global Instance ConvertTyp_list {A} `{Traversal.Fmap A}: ConvertTyp (fun T => list (A T)) :=
  fun env => Traversal.fmap (typ_to_dtyp env).

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

  Lemma resolve_PVar_simple : forall p s s' x v,
      resolve_PVar p s ≡ inr (s', (x, v)) ->
      exists sz n,
        nth_error (Γ s') n ≡ Some (x, TYPE_Pointer (TYPE_Array sz TYPE_Double)) /\
        MInt64asNT.from_Z sz ≡ inr v /\ p ≡ PVar n /\ s ≡ s'.
  Proof.
    intros * H.
    unfold resolve_PVar in H.
    cbn* in H.
    simp.
    do 2 eexists; eauto.
  Qed.

  Ltac inv_resolve_PVar H :=
    apply resolve_PVar_simple in H;
    destruct H as (?sz & ?n & ?LUn & ?EQsz & -> & <-).

  From Vellvm Require Import Traversal.

  Lemma fmap_list_app: forall U V H H' c1 c2 f,
      @fmap code (@Fmap_code H H') U V f (c1 ++ c2) ≡
            fmap f c1  ++ fmap f c2.
  Proof.
    induction c1 as [| [] c1 IH]; cbn; intros; [reflexivity |].
    rewrite IH; reflexivity.
  Qed.

  (* Lemma convert_typ_list_app: forall H env c1 c2, *)
  (*     @convert_typ code (@ConvertTyp_list LLVMAst.block H) env (c1 ++ c2) ≡ *)
  (*           convert_typ env c1 ++ *)
  (*           convert_typ env c2. *)
  (* Proof. *)
  (*   induction c1 as [| [] c1 IH]; cbn; intros; [reflexivity |]. *)
  (*   rewrite IH; reflexivity. *)
  (* Qed. *)


  Section GenIR.

    (* YZ TODO : reducing denote_bks exposes iter. Should we simply make it opaque? *)
    Opaque denote_bks.
    Opaque resolve_PVar.

    Ltac focus_single_step_v :=
      match goal with
        |- eutt _ _ (ITree.bind _ ?x) => remember x
      end.

    Ltac focus_single_step_h :=
      match goal with
        |- eutt _ (ITree.bind _ ?x) _ => remember x
      end.

    Ltac focus_single_step :=
      match goal with
        |- eutt _ (ITree.bind _ ?x) (ITree.bind _ ?y) => remember x; remember y
      end.

    Axiom int_eq_inv: forall a b, Int64.intval a ≡ Int64.intval b -> a ≡ b.

  Definition GenIR_Rel σ Γ : Rel_cfg_T unit (block_id + uvalue) :=
    lift_Rel_cfg (state_invariant σ Γ).

 Lemma compile_FSHCOL_correct :
    forall (** Compiler bits *) (s1 s2: IRState)
      (** Helix bits    *) (op: DSHOperator) (σ : evalContext) (memH : memoryH) fuel v
      (** Vellvm bits   *) (nextblock bid_in : block_id) (bks : list (LLVMAst.block typ))
      (* (env : list (ident * typ)) *)  (g : global_env) (ρ : local_env) (memV : memoryV),
      nextblock ≢ bid_in -> (* YZ: not sure about this yet *)
      GenIR_Rel σ s1 (memH,tt) (memV, (ρ, (g, (inl bid_in)))) ->
      evalDSHOperator σ op memH fuel ≡ Some (inr v)            -> (* Evaluation succeeds *)
      genIR op nextblock s1 ≡ inr (s2,(bid_in,bks)) ->
      eutt (GenIR_Rel σ s1)
           (with_err_RB
              (interp_Mem (denoteDSHOperator σ op) memH))
           (with_err_LB
              (interp_cfg (D.denote_bks (convert_typ [] bks) bid_in)
                                g ρ memV)).
  Proof.
    intros s1 s2 op; revert s1 s2; induction op; intros * NEXT BISIM EVAL GEN.
    - cbn* in GEN.
      simp.
      hide_strings'.
      cbn*; repeat norm_h.
      rewrite denote_bks_nil.
      cbn*; repeat norm_v.
      apply eqit_Ret; auto.

    - (* Assign case.
         Helix side:
         1. x_i <- evalPExpr σ x_p ;;
         2. y_i <- evalPExpr σ y_p ;;
         3. x <- memory_lookup_err "Error looking up 'x' in DSHAssign" mem x_i ;;
         4. y <- memory_lookup_err "Error looking up 'y' in DSHAssign" mem y_i ;;
         5. src <- evalNExpr σ src_e ;;
         6. dst <- evalNExpr σ dst_e ;;
         7. v <- mem_lookup_err "Error looking up 'v' in DSHAssign" (to_nat src) x ;;
         8. ret (memory_set mem y_i (mem_add (to_nat dst) v y))
       *)

      destruct fuel as [| fuel]; [cbn in *; simp |].
      cbn* in GEN.
      unfold GenIR_Rel in BISIM; cbn in BISIM.
      simp.
      hide_strings'.
      rename i into si, i2 into si',
      i0 into x, i3 into y,
      i1 into v1, i4 into v2.
      inv_resolve_PVar Heqs0.
      inv_resolve_PVar Heqs1.

      eutt_hide_right.
      cbn*.
      rename n1 into x_p, n2 into y_p.

      repeat norm_h.
      unfold denotePExpr; cbn*.
      break_inner_match_goal; cbn* in *; simp.
      eutt_hide_right.
      rename m into x_i, m0 into y_i.

      repeat norm_h.
      2,3:cbn*; apply memory_lookup_err_inr_Some_eq; eauto.

      subst; eutt_hide_left.
      unfold add_comments.
      cbn*.
      rewrite denote_bks_singleton; eauto.
      2:reflexivity.
      cbn*.
      repeat rewrite fmap_list_app.
      rewrite denote_code_app.
      repeat norm_v.
      subst.
      focus_single_step.
      rename x into x_p', y into y_p'.
      rename m1 into x, m2 into y.
      rename n into src_e, n0 into dst_e.
      rename b into v.

      (* Step 5. *)
      eapply eutt_clo_bind.
      eapply genNExpr_correct_ind; try eassumption.
      do 3 (eapply state_invariant_incLocal; eauto).
      do 2 (eapply state_invariant_incVoid; eauto).
      do 1 (eapply state_invariant_incBlockNamed; eauto).

      intros [memH1 src] (memV1 & ρ1 & g1 & []) (INV1 & (EXP1 & <- & <- & <- & MONO1) & GAMMA1); cbn* in *.

      subst.

      rewrite denote_code_app.
      repeat norm_v.
      repeat norm_h.
      focus_single_step.

      (* Step 6. *)
      eapply eutt_clo_bind.
      eapply genNExpr_correct_ind; eauto.

      intros [memH2 dst] (memV2 & ρ2 & g2 & []) (INV2 & (EXP2 & <- & <- & <- & MONO2) & GAMMA2); cbn in GAMMA2; cbn in INV2.
      subst.

      (* Step 7. *)
      eutt_hide_right.

      edestruct EXP1 as (EQ1 & EQ1'); [reflexivity |].
      rewrite EQ1' in Heqs11; inv Heqs11.
      rewrite Heqo0.
      eutt_hide_right.
      (*
      assert (i2 ≡ val2).
      { unfold genNExpr_exp_correct in EXP2.
        assert (ρ2 ⊑ ρ2) as LL by reflexivity.
        specialize (EXP2 _ LL) as (EXP2_EUTT & EXP2_EVAL).
        rewrite EXP2_EVAL in Heqs12.
        inversion Heqs12.
        auto.
      }
      subst.
      rewrite Heqs13.
      cbn*.
      repeat norm_h.
      rewrite interp_Mem_MemSet.
      cbn*.
      repeat norm_h.

      subst; eutt_hide_left.

      simpl.
      norm_v.
      norm_v.
      focus_single_step_v.
      cbn.
      repeat norm_v.
      (* I am looking up an ident x, for which I find the type `TYPE_Pointer (TYPE_Array sz TYPE_Double)`
         in my typing context.
         Can it be a global?
       *)

      (* onAllHyps move_up_types. *)
      subst; focus_single_step_v; eutt_hide_left.
      unfold endo, Endo_ident.

      destruct x_p' as [x_p' | x_p']; [admit |];
        destruct y_p' as [y_p' | y_p']; cbn; [admit |].
      subst; focus_single_step_v; eutt_hide_left.
      edestruct memory_invariant_LLU_Ptr as (bk_x & ptr_x & LUx & INLGx & VEC_LUx); [| exact LUn | exact Heqo |]; eauto.
      rewrite LUx in Heqo2; symmetry in Heqo2; inv Heqo2.
      edestruct memory_invariant_LLU_Ptr as (bk_y & ptr_y & LUy & INLGy & VEC_LUy); [| exact LUn0 | eassumption |]; eauto.
      rewrite LUy in Heqo1; symmetry in Heqo1; inv Heqo1.

      focus_single_step_v; repeat norm_v.
      2: apply MONO2, MONO1; eauto.
      cbn; repeat norm_v.
      subst; focus_single_step_v; repeat norm_v.
      unfold IntType; rewrite typ_to_dtyp_I; cbn.
      subst; focus_single_step_v; repeat norm_v.
      subst; focus_single_step_v; repeat norm_vD.
      focus_single_step_v.

      destruct (EXP1 ρ2) as [EQe ?]; auto.
      rewrite <- EQe.
      repeat norm_v.
      subst; focus_single_step_v; repeat norm_vD.
      cbn.

      rename i into index, v1 into size_array.
      unfold ITree.map.
      repeat norm_v.

      rewrite exp_E_to_instr_E_Memory, subevent_subevent.
      rewrite typ_to_dtyp_D_array.

      cbn in *.

      (* onAllHyps move_up_types. *)

      match goal with
        |- context[interp_cfg_to_L3 ?defs (@ITree.trigger ?E _ (subevent _ (GEP (DTYPE_Array ?size ?t) (DVALUE_Addr ?a) _)))] =>
        edestruct (@interp_cfg_to_L3_GEP_array defs t a size g ρ2) as (add & ?EQ & READ); eauto
      end.

      assert (EQindex: Integers.Int64.repr (Z.of_nat (MInt64asNT.to_nat index)) ≡ index) by admit.
      rewrite EQindex in *.
      rewrite EQ.

      repeat norm_v.
      cbn.
      subst; cbn; repeat norm_v.
      focus_single_step_v.
      rewrite interp_cfg_to_L3_LW.
      cbn*; repeat norm_v.
      subst; simpl; repeat norm_v.
      focus_single_step_v.
      cbn; repeat norm_v.
      subst; cbn; repeat norm_v.
      focus_single_step_v.

      2: apply lookup_alist_add_eq.
      cbn*; repeat norm_v.
      subst; cbn; repeat norm_v; focus_single_step_v.
      rewrite interp_cfg_to_L3_Load.
      2: rewrite typ_to_dtyp_D; eassumption.
      repeat norm_v.
      subst; cbn; repeat norm_v; focus_single_step_v.
      rewrite interp_cfg_to_L3_LW.
      cbn; repeat norm_v.
      subst; cbn; repeat norm_v.

      2:{
        unfold endo.
        assert (y_p' <> r1) by admit.
        assert (y_p' <> r) by admit.
        setoid_rewrite lookup_alist_add_ineq; eauto.
        setoid_rewrite lookup_alist_add_ineq; eauto.
        cbn in *.
        apply MONO2, MONO1; eauto.
      }
      cbn.
      subst.
      unfold IntType;rewrite !typ_to_dtyp_I.
      focus_single_step_v; repeat norm_v.
      subst; cbn; repeat norm_v.
      focus_single_step_v.

      match goal with
        |- eutt _ _ (ITree.bind (_ (interp_cfg _ _ ?l _)) _) => destruct (EXP2 l) as [EQe' ?]; auto
      end.
      rewrite <- sub_alist_add.
      apply sub_alist_add.
      rename r into foo.
      (* Freshness, easy todo *)
      admit.
      admit.

      rewrite <- EQe'.
      repeat norm_v.
      subst; cbn*; repeat norm_v.
      focus_single_step_v.
      repeat norm_v; subst; focus_single_step_v.
      repeat norm_v; subst; focus_single_step_v.
      cbn; unfold ITree.map.
      repeat norm_v; subst; focus_single_step_v.
      rewrite exp_E_to_instr_E_Memory, subevent_subevent.
      rewrite typ_to_dtyp_D_array.

      Set Hyps Limit 50.

      (* Need another GEP lemma?
         The destination is not read on the Helix side, so that I do not know that the GEP succeeds
       *)

      (*
      match goal with
        |- context[interp_cfg_to_L3 ?defs (@ITree.trigger ?E _ (subevent _ (GEP (DTYPE_Array ?size ?t) (DVALUE_Addr ?a) _))) ?g ?l] =>
        edestruct (@interp_cfg_to_L3_GEP_array defs t a size g l) as (add' & ?EQ & READ'); eauto
      end.

      eapply VEC_LUy.
       *)

        admit.
    (* End of genFSHAssign, things are getting a bit complicated *)



    - destruct fuel as [| fuel]; [cbn in *; simp |].

      Opaque genWhileLoop.
      cbn* in GEN.
      unfold GenIR_Rel in BISIM; cbn in BISIM.
      simp.
      hide_strings'.
      inv_resolve_PVar Heqs0.
      inv_resolve_PVar Heqs1.
      cbn* in *.
      simp.
      (* Require Import LibHyps.LibHyps. *)
      (* onAllHyps move_up_types. *)

      eutt_hide_right.

      repeat norm_h.
      unfold denotePExpr; cbn*.

      Ltac rewrite_nth_error :=
        match goal with
        | h: nth_error _ _ ≡ _ |- _ => rewrite h
        end.

      Ltac rewrite_memory_lookup :=
        match goal with
        | h: memory_lookup _ _ ≡ _ |- _ => rewrite h
        end.

      do 2 rewrite_nth_error.

      repeat (norm_h; []).
      norm_h.
      2: cbn*; rewrite_memory_lookup; reflexivity.

      repeat norm_h.
      2: cbn*; rewrite_memory_lookup; reflexivity.

      subst; eutt_hide_left.
      Transparent genWhileLoop.
      cbn in *.
      simp.
      cbn in *.
      unfold add_comments; cbn.
      repeat rewrite fmap_list_app.
      cbn.


      match goal with
        |- context[denote_bks ?x] =>
        remember x as bks
      end.


      erewrite denote_bks_unfold.
      2:{
        subst; cbn.
        clear.
        destruct (Eqv.eqv_dec_p bid_in bid_in) as [foo | foo].
        reflexivity.
        exfalso; apply foo; reflexivity.
      }

      Opaque find_block.

      cbn.
      repeat norm_v.
      unfold IntType; rewrite typ_to_dtyp_I.
      cbn.
      focus_single_step_v; repeat norm_v.
      cbn; repeat norm_v.
      subst.
      repeat norm_v.
      focus_single_step_v; repeat norm_v.
      rewrite interp_cfg_to_L3_LW.
      cbn; repeat norm_v.
      unfold endo.
      subst.
      repeat (norm_v; []).
      focus_single_step_v.
      (* onAllHyps move_up_types. *)
      unfold endo.
      focus_single_step_v.
      norm_v.
      2: apply lookup_alist_add_eq.
      cbn; repeat norm_v.
      subst; cbn; repeat norm_v.
      focus_single_step_v.

      (* Case analysis on whether we ever enter the loop or not *)
      unfold eval_int_icmp.
      cbn.
      break_match_goal.
      -- (* We enter the loop *)
        cbn; repeat norm_v.
        subst; cbn; repeat norm_v.

        rewrite find_block_ineq, find_block_eq.
        2: reflexivity.
        2:cbn; admit.

        repeat norm_v.
(*
        (* loopblock  *)
        rewrite denote_bks_unfold.
        2:{
          cbn.
          match goal with
            |- context[if ?p then true else false] =>
            destruct p as [EQ | INEQ]
          end.
          admit.
          match goal with
            |- context[if ?p then true else false] =>
            destruct p as [?EQ | ?INEQ]
          end.
          reflexivity.
          admit.
        }
*)
      (* Need to denote phis, I cannot denote the block directly :( *)

        admit.

      --
        (* from == to, we go from the entry block to the next one directly *)
        cbn.
        repeat norm_v.
        subst; cbn; repeat norm_v.

        repeat rewrite find_block_ineq.
        2,3,4,5: cbn; admit.
        cbn.
        rewrite find_block_nil.

        cbn; repeat norm_v.
        assert (n ≡ 0) by admit.

        subst.
        cbn; repeat norm_h.
        rewrite interp_Mem_MemSet.
        repeat norm_h.

        apply eutt_Ret.
        split; eauto.
        {
          admit.
        }
        {
          admit.
        }

    - (* DSHBinOp *)
      destruct fuel as [| fuel]; [cbn in *; simp |].
      cbn* in GEN.
      unfold GenIR_Rel in BISIM; cbn in BISIM.
      unfold ErrorWithState.err2errS in *.
      repeat (break_inner_match_hyp; cbn in *; repeat inv_sum; []).
      repeat match goal with
      | h: _ * _ |- _ => destruct h
      | h: () |- _ => destruct h
      end.
      repeat match goal with
      | h: (_,_) ≡ (_,_) |- _ => inv h
             end.
      cbn* in *.

      (* On the Helix side, the computation consists in:
         1. xi <- denotePExpr x
         2. yi <- denotePExpr y
         3. lookup xi in memory
         4. lookup yi in memory
         5. denoteDSHBinop on the values read
         6. write the result in memory at yi
       *)
      eutt_hide_right.
      repeat norm_h.

     subst; eutt_hide_left.

      unfold add_comments.
      cbn.
      match goal with
        |- context[denote_bks ?x] =>
        remember x as bks
      end.

      (* Lemma about while loop instead *)
      (* erewrite denote_bks_unfold. *)
      (* 2:{ *)
      (*   subst; cbn. *)
      (*   destruct (Eqv.eqv_dec_p bid_in bid_in).  *)
      (*   reflexivity. *)
      (*   exfalso. *)
      (*   apply n0. *)
      (*   reflexivity. *)
      (* } *)
      (* cbn. *)
      (* repeat norm_v. *)
      (* unfold IntType; rewrite typ_to_dtyp_I. *)
      (* cbn. *)
      (* setoid_rewrite bind_ret_l. *)
      (* setoid_rewrite bind_ret_l. *)
      (* cbn. *)
      (* repeat norm_v. *)
      (* rewrite interp_cfg_to_L3_LW. *)
      (* cbn*; repeat norm_v. *)
      (* cbn*; repeat norm_v. *)
      (* 2:{ *)
      (*   cbn. *)
      (*   unfold endo. *)
      (*   rewrite rel_dec_eq_true; eauto; typeclasses eauto. *)
      (* } *)
      (* cbn. *)
      (* unfold endo. *)
      (* unfold eval_int_icmp. *)
      (* cbn. *)

      (* focus_single_step_v. *)

      (* unfold Int64_eq_or_cerr, Z_eq_or_cerr, ErrorWithState.err2errS, Z_eq_or_err, memory_lookup_err in *. *)
      (* cbn* in *. *)
      (* simp. *)
      (* inv_resolve_PVar Heqs0. *)
      (* inv_resolve_PVar Heqs1. *)

      (* onAllHyps move_up_types.  *)

  (*     repeat match goal with *)
  (*            | h : Int64.intval _ ≡ Int64.intval _ |- _ => apply int_eq_inv in h; subst *)
  (*            end. *)

  (*     eutt_hide_left. *)
  (*     focus_single_step_v. *)
  (*     unfold MInt64asNT.from_nat in *. *)

  (*     rename n into index1. *)
  (*     break_if. *)
  (*     { *)
  (*       cbn. *)
  (*       repeat norm_v. *)
  (*       subst. *)
  (*       cbn. *)
  (*       repeat norm_v. *)





*)
  Admitted.

  End GenIR.

Section LLVMGen.

  (** YZ TODO
      This is initialized over the empty memory. That is incorrect. Run it over the initialze memory, and add the top level statement about compile
     global_extern == false?
   *)
  Lemma LLVMGen_correct: forall R,
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix bits *)    (i o: Int64.int) (globals: list (string*DSHType)) (globals_extern: bool) (fshcol: DSHOperator) (funname: string) (σ: evalContext)
      (* Vellvm bits *)   tle,
      LLVMGen i o fshcol funname s1 ≡ inr (s2, tle) ->
      eutt (* (bisim_final σ) *) R
           (with_err_RT (interp_Mem (denoteDSHOperator σ fshcol) memory_empty))
           (semantics_llvm tle).
  Proof.
    (* intros p data pll H. *)
    (*   unfold compile_w_main, compile in H. *)
    (*   destruct p as [i o name globals op]. *)
    (*   destruct (initIRGlobals data globals) as [? | [data' ginit]] eqn:EQGlob; [inv H |]. *)
    (*   simpl in H. *)
    (*   destruct (ErrorWithState.evalErrS (LLVMGen i o globals false op name) newState) eqn: EQEVALERR; [inv H | inv H]. *)
    (*   unfold semantics_llvm. *)
    (*   unfold semantics_llvm_mcfg. *)
    (*   unfold lift_sem_to_mcfg. *)
    (*   match goal with *)
    (*     |- context[match ?p with | _ => _ end] => destruct p eqn:EQ *)
    (*   end. { *)
    (*     unfold ErrorWithState.evalErrS in EQEVALERR. *)
    (*     destruct (LLVMGen i o globals false op name newState) eqn:EQGEN; inv EQEVALERR. *)
  Admitted.

End LLVMGen.

(**
   Initialization of the memory
 **)

Definition llvm_empty_memory_state_partial: config_cfg
  := (empty_memory_stack, ([], [])).

(* Scalar *)
Definition eval_const_double_exp (typed_expr:typ*exp typ): err dvalue :=
  match typed_expr with
  | (TYPE_Double, EXP_Double v) => ret (DVALUE_Double v)
  | (_, c_typ) => inl ("Type double expected: " ++ (to_string c_typ))%string
  end.

(* Array *)
Definition eval_const_arr_exp (typed_expr:typ*exp typ): err dvalue :=
  match typed_expr with
  | (TYPE_Array _ TYPE_Double, EXP_Array a) =>
    da <- ListSetoid.monadic_fold_left
           (fun ds d => dd <- eval_const_double_exp d ;; ret (dd::ds))
           [] a ;;
    ret (DVALUE_Array da)
  | (_, c_typ) => inl ("Array of doubles expected: " ++ (to_string c_typ))%string
  end.

Definition eval_const_exp (typed_expr:typ*exp typ): err dvalue :=
  match typed_expr with
  | (TYPE_Array _ TYPE_Double, EXP_Array a) => eval_const_arr_exp typed_expr
  | (TYPE_Double, EXP_Double v) =>  eval_const_double_exp typed_expr
  | (_, c_typ) => inl ("Unsupported constant expression type: " ++ (to_string c_typ))%string
  end.

(* TODO: move to Util *)
Definition assoc_right_to_left {A B C:Type}: (A*(B*C)) -> ((A*B)*C)
  := fun x => let '(a,(b,c)):=x in ((a,b),c).

(* TODO: move to Util *)
Definition assoc_left_to_right {A B C:Type}: ((A*B)*C) -> (A*(B*C))
  := fun x => let '((a,b),c) := x in (a,(b,c)).

(** Empty memories and environments should satisfy [memory_invariant] *)
Lemma memory_invariant_empty: memory_invariant [] newState helix_empty_memory llvm_empty_memory_state_partial.
Proof.
  unfold memory_invariant.
  intros n v τ x Hcontra Hst.
  rewrite nth_error_nil in Hcontra.
  inversion Hcontra.
Qed.

Lemma WF_IRState_empty : WF_IRState [ ] newState.
Proof.
(*   cbn; apply Forall2_nil. *)
(* Qed. *)
Admitted.

Lemma inc_local_fresh_empty : concrete_fresh_inv newState llvm_empty_memory_state_partial.
Proof.
  intros ? ? ? LU; inv LU.
Qed.

Lemma state_invariant_empty: state_invariant [] newState helix_empty_memory llvm_empty_memory_state_partial.
Proof.
  split; auto using memory_invariant_empty, WF_IRState_empty, inc_local_fresh_empty.
Qed.

Fact initFSHGlobals_globals_sigma_len_eq
     {mem mem' data data'} globals σ:
  initFSHGlobals data mem globals ≡ inr (mem', data', σ) ->
  List.length globals ≡ List.length σ.
Proof.
  apply init_with_data_len.
Qed.

(* Maps indices from [σ] to [raw_id].
   Currently [σ := [globals;Y;X]]
   Where globals mapped by name, while [X-> Anon 0] and [Y->Anon 1]
*)
Definition memory_invariant_map (globals : list (string * DSHType)): nat -> raw_id
  := fun j =>
       let l := List.length globals in
       if Nat.eqb j l then Anon 0%Z (* X *)
       else if Nat.eqb j (S l) then Anon 1%Z (* Y *)
            else
              match nth_error globals j with
              | None => Anon 0%Z (* default value *)
              | Some (name,_) => Name name
              end.

Lemma memory_invariant_map_injectivity (globals : list (string * DSHType)):
  list_uniq fst globals ->
  forall (x y : nat),
    x < (Datatypes.length globals + 2)%nat ∧ y < (Datatypes.length globals + 2)%nat
    → memory_invariant_map globals x ≡ memory_invariant_map globals y → x ≡ y.
Proof.
  intros U x y [Hx Hy] E.
  unfold lt, peano_naturals.nat_lt in *.
  unfold memory_invariant_map in E.
  repeat break_if; repeat break_match; bool_to_nat; subst; try inv E; auto.
  - apply nth_error_None in Heqo; lia.
  - apply nth_error_None in Heqo; lia.
  -
    unfold list_uniq in U.
    eapply U; eauto.
  - apply nth_error_None in Heqo; lia.
Qed.
