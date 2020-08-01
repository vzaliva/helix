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

Require Export Vellvm.Tactics.
Require Export Vellvm.Util.
Require Export Vellvm.LLVMEvents.
Require Export Vellvm.DynamicTypes.
Require Export Vellvm.Denotation.
Require Export Vellvm.Handlers.Handlers.
Require Export Vellvm.TopLevel.
Require Export Vellvm.LLVMAst.
Require Export Vellvm.AstLib.
Require Export Vellvm.CFG.
Require Export Vellvm.InterpreterMCFG.
Require Export Vellvm.InterpreterCFG.
Require Export Vellvm.TopLevelRefinements.
Require Export Vellvm.TypToDtyp.
Require Export Vellvm.LLVMEvents.
Require Export Vellvm.Transformations.Traversal.
Require Export Vellvm.Denotation_Theory.
Require Export Vellvm.InstrLemmas.

Require Export ExtLib.Structures.Monads.
Require Export ExtLib.Data.Map.FMapAList.
Require Export ExtLib.Core.RelDec.

Require Export Ceres.Ceres.

Require Export ITree.Interp.TranslateFacts.
Require Export ITree.Basics.CategoryFacts.
Require Export ITree.Events.State.
Require Export ITree.Events.StateFacts.
Require Export ITree.ITree.
Require Export ITree.Eq.Eq.
Require Export ITree.Basics.Basics.
Require Export ITree.Interp.InterpFacts.

Require Export Flocq.IEEE754.Binary.
Require Export Flocq.IEEE754.Bits.

Require Export MathClasses.interfaces.canonical_names.
Require Export MathClasses.misc.decision.

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

(* Starting to toy around tactics to process proofs at a decent level of abstraction.
   Very naive as is.
 *)

(* When working with [denote_bks], we need to lookup for the block associated to
   a given id. This tactic looks for the block, assuming that the identifiers
   can be unified by [reflexivity] or [auto].

   It generates on the way proof obligations of inequality with all the other block
   identifiers encountered on the way. The intent is naturally to pair it with a
   tactic discharging these proof obligations automatically, but this tactic should
   depend on naming schemes.

  *)
Ltac find_block :=
  match goal with
    |- find_block _ (?bk::_) ?b' ≡ _ => 
    first [rewrite find_block_eq; [| (reflexivity || auto)]; reflexivity | rewrite find_block_ineq; [find_block |]]
  end.

(* For when the next step is to process [denote_bks], and that we know the
   identifier we are jumping to is in the list of blocks considered. *)
Ltac jump_in := rewrite denote_bks_unfold_in; [| find_block].

(* Similar in spirit: when processing a single Phi node, this tactic finds the
   assignment that needs to be performed.
 *)
Ltac find_phi :=
  match goal with
    |- context[denote_phi ?b (_,Phi _ ((?b,_)::_))] =>
    rewrite denote_phi_hd
  | _ =>  rewrite denote_phi_tl; [find_phi |]
  end.

(* Enforcing these definitions to be unfolded systematically by [cbn] *)
Arguments endo /.
Arguments Endo_id /.
Arguments Endo_ident /.
Arguments IntType /.

(* General purpose tactics.
   TODO: create a curated library of tactics in Vellvm.
   TODO: when creating such library, ILLUSTRATE EACH TACTIC WITH EXAMPLES!
 *)
Ltac splits :=
  repeat match goal with
           |- _ /\ _ => split
         end.

Ltac abs_by H :=
  exfalso; eapply H; now eauto.

(* TODO: move this *)
Ltac match_rewrite :=
  match goal with
  | H : (?X ≡ ?v) |-
    context [ match ?X with | _ => _ end] =>
    rewrite H
  end.

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
  Definition semantics_llvm_mcfg p : itree E_mcfg _ := with_err_LT (model_to_L3 DTYPE_Void "main" main_args defined_intrinsics p).
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
    '(data, σ) <- denote_initFSHGlobals data p.(Data.globals) ;;
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
Notation "'interp_cfg'"  := (interp_cfg_to_L3 defined_intrinsics).
Notation "'interp_mcfg'" := (interp_to_L3 defined_intrinsics).

(** Smart constructors for states, predicates, relations  *)

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

(* TODOYZ : MOVE *)
Definition conj_rel {A B : Type} (R S: A -> B -> Prop): A -> B -> Prop :=
  fun a b => R a b /\ S a b.
Infix "⩕" := conj_rel (at level 85, right associativity).

(* Introduction pattern useful after [eutt_clo_bind] *)
Ltac introR :=
  intros [?memH ?vH] (?memV & ?l & ?g & ?vV) ?PRE.


(** Long term dream: a cute proof mode in the spirit of Iris
    For now, some naive notations to lighten the goal.
 *)

(* A few print-only notations lightening the display of proof goals
   Those are very dumb at the moment, please feel free to refine, modify or
   simply comment about them.
 *)
Module ProofNotations.

  Export ITreeNotations.

  Notation "⟦ b , p , c , t ⟧" := (fmap _ (mk_block b p c t _)) (only printing). 
  Notation "e" := (EXP_Integer e) (at level 10,only printing). 
  Notation "i" := (EXP_Ident i) (at level 10,only printing). 
  Notation "x ← 'Φ' xs" := (x,Phi _ xs) (at level 10,only printing). 
  Notation "'denote_blocks' '...' id " := (denote_bks _ id) (at level 10,only printing). 
  Notation "'IRS' ctx" := (mkIRState _ _ _ ctx) (only printing, at level 10). 
  Notation "x" := (with_err_LT x) (only printing, at level 10). 
  Notation "x" := (with_err_LB x) (only printing, at level 10). 
  Notation "x" := (with_err_RT x) (only printing, at level 10). 
  Notation "x" := (with_err_RB x) (only printing, at level 10). 
  Notation "⟦ t ⟧ g l m" := (interp_cfg t g l m) (only printing, at level 10).
  Notation "'CODE' c" := (denote_code c) (only printing, at level 10, format "'CODE' '//' c").
  Notation "'INSTR' i" := (denote_instr i) (only printing, at level 10, format "'INSTR' '//' i").
  Notation "'ι' x" := (DTYPE_I x) (at level 10,only printing).
  Notation "⋆" := (DTYPE_Pointer) (at level 10,only printing).
  Notation "x" := (convert_typ _ x) (at level 10, only printing).
  Notation "x" := (fmap (typ_to_dtyp _) x) (at level 10, only printing).

  Notation "'ret' τ e" := (TERM_Ret (τ, e)) (at level 10, only printing).
  Notation "'ret' 'void'" := (TERM_Ret_void) (at level 10, only printing).
  Notation "'br' c ',' 'label' e ',' 'label' f" := (TERM_Br c e f) (at level 10, only printing).
  Notation "'br' 'label' e" := (TERM_Br_1 e) (at level 10, only printing).

  Notation "r '←' 'op' x" := ((IId r, INSTR_Op x)) (at level 10, only printing).
  Notation "r '←' 'call' x args" := ((IId r, INSTR_Call x args)) (at level 10, only printing).
  Notation "'call' x args" := ((IVoid, INSTR_Call x args)) (at level 10, only printing).
  Notation "r '←' 'alloca' t" := ((IId r, INSTR_Alloca t _ _)) (at level 10, only printing).
  Notation "r '←' 'load' t ',' e" := ((IId r, INSTR_Load _ t e _)) (at level 10, only printing).
  Notation "r '←' 'store' e ',' f" := ((IId r, INSTR_Store _ e f _)) (at level 10, only printing).

  Notation "'add' e f"  := (OP_IBinop (Add _ _) _ e f) (at level 10, only printing).
  Notation "'sub' e f"  := (OP_IBinop (Sub _ _) _ e f) (at level 10, only printing).
  Notation "'mul' e f"  := (OP_IBinop (Mul _ _) _ e f) (at level 10, only printing).
  Notation "'shl' e f"  := (OP_IBinop (Shl _ _) _ e f) (at level 10, only printing).
  Notation "'udiv' e f" := (OP_IBinop (UDiv _) _ e f)  (at level 10, only printing).
  Notation "'sdiv' e f" := (OP_IBinop (SDiv _) _ e f)  (at level 10, only printing).
  Notation "'lshr' e f" := (OP_IBinop (LShr _) _ e f)  (at level 10, only printing).
  Notation "'ashr' e f" := (OP_IBinop (AShr _) _ e f)  (at level 10, only printing).
  Notation "'urem' e f" := (OP_IBinop URem _ e f)      (at level 10, only printing).
  Notation "'srem' e f" := (OP_IBinop SRem _ e f)      (at level 10, only printing).
  Notation "'and' e f"  := (OP_IBinop And _ e f)       (at level 10, only printing).
  Notation "'or' e f"   := (OP_IBinop Or _ e f)        (at level 10, only printing).
  Notation "'xor' e f"  := (OP_IBinop Xor _ e f)       (at level 10, only printing).

  Notation "t '======================' '======================' u '======================' '{' R '}'"
    := (eutt R t u)
         (only printing, at level 200,
          format "'//' '//' t '//' '======================' '======================' '//' u '//' '======================' '//' '{' R '}'"
         ).

End ProofNotations.

(** Proof automation *)

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

(* This tactic is quite dumb, and should be refined if needed, but does a good job at
   reducing the success of a compilation unit to the success of all of its sub-operations.
 *)
Ltac simp := repeat (inv_sum || inv_option || break_and || break_match_hyp).

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
  Ltac norm_monad_l_k k :=
    match goal with
      |- eutt _ ?t ?u =>
      let x := fresh in remember u as x;
      match t with
      | context[ITree.bind ?t' _] =>
        match t' with
        | ITree.bind _ _ => rewrite bind_bind ;
                           do k idtac "bind_bind"
        | Ret _ => rewrite bind_ret_l ;
                  do k idtac "bind_ret"
        end
      end; subst x
    end.

  Tactic Notation "norm_monad_l_k'" constr(t) integer(k) := norm_monad_l_k t k.
  Tactic Notation "norm_monad_l" constr(t) := norm_monad_l_k' t 0.
  Tactic Notation "norm_monad_lD" constr(t) := norm_monad_l_k' t 1.

  Ltac norm_monad_r_k k :=
    match goal with
      |- eutt _ ?u ?t =>
      let x := fresh in remember u as x;
      match t with
      | context[ITree.bind ?t' _] =>
        match t' with
        | ITree.bind _ _ => rewrite bind_bind ;
                           do k idtac "bind_bind"
        | Ret _ => rewrite bind_ret_l ;
                  do k idtac "bind_ret"
      end
    end; subst x end.

  Tactic Notation "norm_monad_r_k'" integer(k) := norm_monad_r_k k.
  Tactic Notation "norm_monad_r" := norm_monad_r_k' 0.
  Tactic Notation "norm_monad_rD" := norm_monad_r_k' 1.

  (* Normalization in an hypothesis h instead of the goal *)
  Ltac norm_monad_hyp_l_k h k :=
    match type of h with
      eutt _ ?t ?u =>
      let x := fresh in
      remember u as x;
      match t with
      | context[ITree.bind ?t' _] =>
        match t' with
        | ITree.bind _ _ => rewrite bind_bind in h ; do k idtac "bind_bind"
        | Ret _ => rewrite bind_ret_l in h ; do k idtac "bind_ret"
        end
     end; subst x end.

  Ltac norm_monad_hyp_r_k h k :=
    match type of h with
      eutt _ ?u ?t =>
      let x := fresh in
      remember u as x;
      match t with
      | context[ITree.bind ?t' _] =>
        match t' with
        | ITree.bind _ _ => rewrite bind_bind in h ; do k idtac "bind_bind"
        | Ret _ => rewrite bind_ret_l in h ; do k idtac "bind_ret"
        end
     end; subst x end.

  Tactic Notation "norm_monad_hyp_l_k'" hyp(h) integer(k) := norm_monad_hyp_l_k h k.
  Tactic Notation "norm_monad_hyp_l" hyp(h) := norm_monad_hyp_l_k' h 0.
  Tactic Notation "norm_monad_hyp_lD" hyp(h) := norm_monad_hyp_l_k' h 1.

  Tactic Notation "norm_monad_hyp_r_k'" hyp(h) integer(k) := norm_monad_hyp_r_k h k.
  Tactic Notation "norm_monad_hyp_r" hyp(h) := norm_monad_hyp_r_k' h 0.
  Tactic Notation "norm_monad_hyp_rD" hyp(h) := norm_monad_hyp_r_k' h 1.

  (* We push [translate]s and [interp]s inside of binds, run them through [Ret]s *)
  Ltac norm_interp_l_k k :=
    match goal with
    |- eutt _ ?t ?u =>
      let x := fresh in remember u as x;
    match t with
    | context[translate _ (ITree.bind ?t' _)] => rewrite translate_bind ; do k idtac "trans_bind"
    | context[interp _ (ITree.bind ?t' _)] => rewrite interp_bind ; do k idtac "interp_bind"
    | context[translate _ (Ret _)] => rewrite translate_ret ; do k idtac "trans_ret"
    | context[interp _ (Ret _)] => rewrite interp_ret ; do k idtac "interp_ret"
    | context[translate _ (trigger ?e)] => rewrite (translate_trigger _ e) ; do k idtac "trans_trigger"
    | context[interp _ (trigger _)] => rewrite interp_trigger ; do k idtac "intepr_trigger"
    end; subst x end.

  Tactic Notation "norm_interp_l_k'" integer(k) := norm_interp_l_k k.
  Tactic Notation "norm_interp_l" := norm_interp_l_k' 0.
  Tactic Notation "norm_interp_lD" := norm_interp_l_k' 1.

  Ltac norm_interp_r_k k :=
    match goal with
    |- eutt _ ?u ?t =>
      let x := fresh in remember u as x;
    match t with
    | context[translate _ (ITree.bind ?t' _)] => rewrite translate_bind ; do k idtac "trans_bind"
    | context[interp _ (ITree.bind ?t' _)] => rewrite interp_bind ; do k idtac "interp_bind"
    | context[translate _ (Ret _)] => rewrite translate_ret ; do k idtac "trans_ret"
    | context[interp _ (Ret _)] => rewrite interp_ret ; do k idtac "interp_ret"
    | context[translate _ (trigger ?e)] => rewrite (translate_trigger _ e) ; do k idtac "trans_trigger"
    | context[interp _ (trigger _)] => rewrite interp_trigger ; do k idtac "intepr_trigger"
    end; subst x end.

  Tactic Notation "norm_interp_r_k'" integer(k) := norm_interp_r_k k.
  Tactic Notation "norm_interp_r" := norm_interp_r_k' 0.
  Tactic Notation "norm_interp_rD" := norm_interp_r_k' 1.

  Ltac norm_interp_hyp_l_k h k :=
    match type of h with
      eutt _ ?t ?u =>
      let x := fresh in remember u as x;
    match t with
    | context[translate _ (ITree.bind ?t' _)] => rewrite translate_bind in h ; do k idtac "trans_bind"
    | context[interp _ (ITree.bind ?t' _)] => rewrite interp_bind in h ; do k idtac "interp_bind"
    | context[translate _ (Ret _)] => rewrite translate_ret in h ; do k idtac "trans_ret"
    | context[interp _ (Ret _)] => rewrite interp_ret in h ; do k idtac "interp_ret"
    | context[translate _ (trigger ?e)] => rewrite (translate_trigger _ e) in h ; do k idtac "trans_trigger"
    | context[interp _ (trigger _)] => rewrite interp_trigger in h ; do k idtac "intepr_trigger"
    end; subst x end.

  Ltac norm_interp_hyp_r_k h k :=
    match type of h with
      eutt _ ?u ?t =>
      let x := fresh in remember u as x;
    match t with
    | context[translate _ (ITree.bind ?t' _)] => rewrite translate_bind in h ; do k idtac "trans_bind"
    | context[interp _ (ITree.bind ?t' _)] => rewrite interp_bind in h ; do k idtac "interp_bind"
    | context[translate _ (Ret _)] => rewrite translate_ret in h ; do k idtac "trans_ret"
    | context[interp _ (Ret _)] => rewrite interp_ret in h ; do k idtac "interp_ret"
    | context[translate _ (trigger ?e)] => rewrite (translate_trigger _ e) in h ; do k idtac "trans_trigger"
    | context[interp _ (trigger _)] => rewrite interp_trigger in h ; do k idtac "intepr_trigger"
    end; subst x end.

  Tactic Notation "norm_interp_hyp_l_k'" hyp(h) integer(k) := norm_interp_hyp_l_k h k.
  Tactic Notation "norm_interp_hyp_l"  hyp(h) := norm_interp_hyp_l_k' h 0.
  Tactic Notation "norm_interp_hyp_lD" hyp(h) := norm_interp_hyp_l_k' h 1.

  Tactic Notation "norm_interp_hyp_r_k'" hyp(h) integer(k) := norm_interp_hyp_r_k h k.
  Tactic Notation "norm_interp_hyp_r"  hyp(h) := norm_interp_hyp_r_k' h 0.
  Tactic Notation "norm_interp_hyp_rD" hyp(h) := norm_interp_hyp_r_k' h 1.

  (* We extend [norm_interp] with locally defined interpreters on the helix side *)
  Ltac norm_local_helix_l_k k :=
    match goal with
    |- eutt _ ?t ?u =>
      let x := fresh in remember u as x;
     match t with
    | context[interp_Mem (ITree.bind ?t' _)] => rewrite interp_Mem_bind ; do k idtac "mem_bind"
    | context[interp_Mem (Ret _)] => rewrite interp_Mem_ret ; do k idtac "mem_ret"
    | context[interp_Mem (trigger (MemLU _ _)) _] =>
      rewrite interp_Mem_MemLU; do k idtac "mem_memlu"
                                   end; subst x
                                   end.

  Tactic Notation "norm_local_helix_l_k'" integer(k) := norm_local_helix_l_k k.
  Tactic Notation "norm_local_helix_l" := norm_local_helix_l_k' 0.
  Tactic Notation "norm_local_helix_lD" := norm_local_helix_l_k' 1.

  Ltac norm_local_helix_r_k k :=
    match goal with
    |- eutt _ ?u ?t =>
      let x := fresh in remember u as x;
     match t with
    | context[interp_Mem (ITree.bind ?t' _)] => rewrite interp_Mem_bind ; do k idtac "mem_bind"
    | context[interp_Mem (Ret _)] => rewrite interp_Mem_ret ; do k idtac "mem_ret"
    | context[interp_Mem (trigger (MemLU _ _)) _] =>
      rewrite interp_Mem_MemLU; do k idtac "mem_memlu"
                                   end; subst x
                                   end.

  Tactic Notation "norm_local_helix_r_k'" integer(k) := norm_local_helix_r_k k.
  Tactic Notation "norm_local_helix_r" := norm_local_helix_r_k' 0.
  Tactic Notation "norm_local_helix_rD" := norm_local_helix_r_k' 1.

  Ltac norm_local_helix_hyp_l_k h k :=
    match type of h with
      eutt _ ?t ?u =>
      let x := fresh in remember u as x;
    match t with
    | context[interp_Mem (ITree.bind ?t' _)] => rewrite interp_Mem_bind in h ; do k idtac "mem_bind"
    | context[interp_Mem (Ret _)] => rewrite interp_Mem_ret in h ; do k idtac "mem_ret"
    end; subst x end.

  Ltac norm_local_helix_hyp_r_k h k :=
    match type of h with
      eutt _ ?u ?t =>
      let x := fresh in remember u as x;
    match t with
    | context[interp_Mem (ITree.bind ?t' _)] => rewrite interp_Mem_bind in h ; do k idtac "mem_bind"
    | context[interp_Mem (Ret _)] => rewrite interp_Mem_ret in h ; do k idtac "mem_ret"
    end; subst x end.

  Tactic Notation "norm_local_helix_hyp_l_k'" hyp(h) integer(k) := norm_local_helix_hyp_l_k h k.
  Tactic Notation "norm_local_helix_hyp_l" hyp(h) := norm_local_helix_hyp_l_k' h 0.
  Tactic Notation "norm_local_helix_hyp_lD" hyp(h) := norm_local_helix_hyp_l_k' h 1.

  Tactic Notation "norm_local_helix_hyp_r_k'" hyp(h) integer(k) := norm_local_helix_hyp_r_k h k.
  Tactic Notation "norm_local_helix_hyp_r" hyp(h) := norm_local_helix_hyp_r_k' h 0.
  Tactic Notation "norm_local_helix_hyp_rD" hyp(h) := norm_local_helix_hyp_r_k' h 1.

  (* We extend [norm_interp] with locally defined interpreters on the vellvm side *)
  Ltac norm_local_vellvm_l_k k :=
    match goal with
    |- eutt _ ?t ?u =>
      let x := fresh in remember u as x;
    match t with
    | context[interp_cfg_to_L3 _ (ITree.bind ?t' _)] => rewrite interp_cfg_to_L3_bind ; do k idtac "cfg_bind"
    | context[interp_cfg_to_L3 _ (Ret _)] => rewrite interp_cfg_to_L3_ret ; do k idtac "cfg_ret"
    | context[interp_cfg_to_L3 _ (trigger (GlobalRead _))] => rewrite interp_cfg_to_L3_GR ; do k idtac "cfg_GR"
    | context[interp_cfg_to_L3 _ (trigger (LocalRead _))] => rewrite interp_cfg_to_L3_LR ; do k idtac "cfg_LR"
    | context[lookup_E_to_exp_E (subevent _ _)] => (rewrite lookup_E_to_exp_E_Global || rewrite lookup_E_to_exp_E_Local); try rewrite subevent_subevent ; do k idtac "luexp"
    | context[exp_E_to_instr_E (subevent _ _)] => (rewrite exp_E_to_instr_E_Global || rewrite exp_E_to_instr_E_Local); try rewrite subevent_subevent ; do k idtac "expinstr"
    end; subst x end.

  Tactic Notation "norm_local_vellvm_l_k'" integer(k) := norm_local_vellvm_l_k k.
  Tactic Notation "norm_local_vellvm_l" := norm_local_vellvm_l_k' 0.
  Tactic Notation "norm_local_vellvm_lD" := norm_local_vellvm_l_k' 1.

  Ltac norm_local_vellvm_r_k k :=
    match goal with
    |- eutt _ ?u ?t =>
      let x := fresh in remember u as x;
    match t with
    | context[interp_cfg_to_L3 _ (ITree.bind ?t' _)] => rewrite interp_cfg_to_L3_bind ; do k idtac "cfg_bind"
    | context[interp_cfg_to_L3 _ (Ret _)] => rewrite interp_cfg_to_L3_ret ; do k idtac "cfg_ret"
    | context[interp_cfg_to_L3 _ (trigger (GlobalRead _))] => rewrite interp_cfg_to_L3_GR ; do k idtac "cfg_GR"
    | context[interp_cfg_to_L3 _ (trigger (LocalRead _))] => rewrite interp_cfg_to_L3_LR ; do k idtac "cfg_LR"
    | context[lookup_E_to_exp_E (subevent _ _)] => (rewrite lookup_E_to_exp_E_Global || rewrite lookup_E_to_exp_E_Local); try rewrite subevent_subevent ; do k idtac "luexp"
    | context[exp_E_to_instr_E (subevent _ _)] => (rewrite exp_E_to_instr_E_Global || rewrite exp_E_to_instr_E_Local); try rewrite subevent_subevent ; do k idtac "expinstr"
    end; subst x end.

  Tactic Notation "norm_local_vellvm_r_k'" integer(k) := norm_local_vellvm_r_k k.
  Tactic Notation "norm_local_vellvm_r" := norm_local_vellvm_r_k' 0.
  Tactic Notation "norm_local_vellvm_rD" := norm_local_vellvm_r_k' 1.

  Ltac norm_local_vellvm_hyp_l_k h k :=
    match type of h with
      eutt _ ?t ?u =>
      let x := fresh in remember u as x;
    match t with
    | context[interp_cfg_to_L3 _ (ITree.bind ?t' _)] => rewrite interp_cfg_to_L3_bind in h ; do k idtac "cfg_bind"
    | context[interp_cfg_to_L3 _ (Ret _)] => rewrite interp_cfg_to_L3_ret in h ; do k idtac "cfg_ret"
    | context[interp_cfg_to_L3 _ (trigger (GlobalRead _))] => rewrite interp_cfg_to_L3_GR in h ; do k idtac "cfg_GR" | context[interp_cfg_to_L3 _ (trigger (LocalRead _))] => rewrite interp_cfg_to_L3_LR in h ; do k idtac "cfg_LR"
    | context[lookup_E_to_exp_E (subevent _ _)] => (rewrite lookup_E_to_exp_E_Global in h || rewrite lookup_E_to_exp_E_Local in h); try rewrite subevent_subevent in h ; do k idtac "luexp"
    | context[exp_E_to_instr_E (subevent _ _)] => (rewrite exp_E_to_instr_E_Global in h || rewrite exp_E_to_instr_E_Local in h); try rewrite subevent_subevent in h ; do k idtac "expinstr"
    end; subst x end.

  Ltac norm_local_vellvm_hyp_r_k h k :=
    match type of h with
      eutt _ ?u ?t =>
      let x := fresh in remember u as x;
    match t with
    | context[interp_cfg_to_L3 _ (ITree.bind ?t' _)] => rewrite interp_cfg_to_L3_bind in h ; do k idtac "cfg_bind"
    | context[interp_cfg_to_L3 _ (Ret _)] => rewrite interp_cfg_to_L3_ret in h ; do k idtac "cfg_ret"
    | context[interp_cfg_to_L3 _ (trigger (GlobalRead _))] => rewrite interp_cfg_to_L3_GR in h ; do k idtac "cfg_GR" | context[interp_cfg_to_L3 _ (trigger (LocalRead _))] => rewrite interp_cfg_to_L3_LR in h ; do k idtac "cfg_LR"
    | context[lookup_E_to_exp_E (subevent _ _)] => (rewrite lookup_E_to_exp_E_Global in h || rewrite lookup_E_to_exp_E_Local in h); try rewrite subevent_subevent in h ; do k idtac "luexp"
    | context[exp_E_to_instr_E (subevent _ _)] => (rewrite exp_E_to_instr_E_Global in h || rewrite exp_E_to_instr_E_Local in h); try rewrite subevent_subevent in h ; do k idtac "expinstr"
    end; subst x end.

  Tactic Notation "norm_local_vellvm_hyp_l_k'" hyp(h) integer(k) := norm_local_vellvm_hyp_l_k h k.
  Tactic Notation "norm_local_vellvm_hyp_l" hyp(h) := norm_local_vellvm_hyp_l_k' h 0.
  Tactic Notation "norm_local_vellvm_lD" hyp(h) := norm_local_vellvm_hyp_l_k' h 1.

  Tactic Notation "norm_local_vellvm_hyp_r_k'" hyp(h) integer(k) := norm_local_vellvm_hyp_r_k h k.
  Tactic Notation "norm_local_vellvm_hyp_r" hyp(h) := norm_local_vellvm_hyp_r_k' h 0.
  Tactic Notation "norm_local_vellvm_rD" hyp(h) := norm_local_vellvm_hyp_r_k' h 1.

  Ltac norm_h_k k :=
    simpl ret;
      repeat (
          repeat (norm_monad_l_k k);
          repeat (norm_interp_l_k k);
          repeat (norm_local_helix_l_k k))
  .
  Tactic Notation "norm_h_k'" integer(k) := norm_h_k k.
  Tactic Notation "norm_h" := norm_h_k' 0.
  Tactic Notation "norm_hD" := norm_h_k' 1.

  Ltac norm_h_hyp_k h k :=
    simpl ret in h;
      repeat (
          repeat (norm_monad_hyp_l_k h k);
          repeat (norm_interp_hyp_l_k h k);
          repeat (norm_local_helix_hyp_l_k h k)
        ).
  Tactic Notation "norm_h_hyp_k'" hyp(h) integer(k) := norm_h_hyp_k h k.
  Tactic Notation "norm_h" "in" hyp(h) := norm_h_hyp_k' h 0.
  Tactic Notation "norm_hD" "in" hyp(h) := norm_h_hyp_k' h 1.

  Ltac norm_v_l_k k :=
    simpl ret;
    repeat rewrite typ_to_dtyp_equation;
      repeat (
          repeat (norm_monad_l_k k);
          repeat (norm_interp_l_k k);
          repeat (norm_local_vellvm_l_k k))
  .
  Tactic Notation "norm_vl_k'" integer(k) := norm_v_l_k k.
  Tactic Notation "norm_vl" := norm_vl_k' 0.
  Tactic Notation "norm_vlD" := norm_vl_k' 1.

  Ltac norm_v_r_k k :=
    simpl ret;
    repeat rewrite typ_to_dtyp_equation;
      repeat (
          repeat (norm_monad_r_k k);
          repeat (norm_interp_r_k k);
          repeat (norm_local_vellvm_r_k k))
  .
  Tactic Notation "norm_vr_k'" integer(k) := norm_v_r_k k.
  Tactic Notation "norm_vr" := norm_vr_k' 0.
  Tactic Notation "norm_vrD" := norm_vr_k' 1.

  Tactic Notation "norm_v" := norm_vr.
  Tactic Notation "norm_vD" := norm_vrD.

  Ltac norm_v_hyp_l_k h k :=
    simpl ret in h;
    repeat (
        repeat (norm_monad_hyp_l_k h k);
        repeat (norm_interp_hyp_l_k h k);
        repeat (norm_local_vellvm_hyp_l_k h k))
  .

  Ltac norm_v_hyp_r_k h k :=
    simpl ret in h;
    repeat (
        repeat (norm_monad_hyp_r_k h k);
        repeat (norm_interp_hyp_r_k h k);
        repeat (norm_local_vellvm_hyp_r_k h k))
  .

  Tactic Notation "norm_v_hyp_l_k'" hyp(h) integer(k) := norm_v_hyp_l_k h k.
  Tactic Notation "norm_vl" "in" hyp(h) := norm_v_hyp_l_k' h 0.
  Tactic Notation "norm_vlD" "in" hyp(h) := norm_v_hyp_l_k' h 1.

  Tactic Notation "norm_v_hyp_r_k'" hyp(h) integer(k) := norm_v_hyp_r_k h k.
  Tactic Notation "norm_vr" "in" hyp(h) := norm_v_hyp_r_k' h 0.
  Tactic Notation "norm_vrD" "in" hyp(h) := norm_v_hyp_r_k' h 1.

  Tactic Notation "norm_v" "in" hyp(h) := norm_vr in h.
  Tactic Notation "norm_vD" "in" hyp(h) := norm_vrD in h.

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



