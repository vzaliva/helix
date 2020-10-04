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
Require Export Vellvm.PostConditions.
Require Export Vellvm.Denotation_Theory.
Require Export Vellvm.InstrLemmas.
Require Export Vellvm.NoFailure.
Require Export Vellvm.PropT.

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
  Definition E_mcfg : Type -> Type := (ExternalCallE +' PickE +' UBE +' DebugE +' FailureE).
  (* Joined set of residual events for cfgs *)
  Definition E_cfg : Type -> Type := (CallE +' PickE +' UBE +' DebugE +' FailureE). 

  (* We therefore have the following resulting denotation functions. *)
  (* On the Vellvm side, for [mcfg]: *)
  Definition semantics_llvm_mcfg p : itree E_mcfg _ := model_to_L3 DTYPE_Void "main" main_args defined_intrinsics p.
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
    denoteDSHOperator σ (p.(Data.op) : DSHOperator);;
    bk <- trigger (MemLU "denote_FSHCOL" yindex);;
    lift_Derr (mem_to_list "Invalid output memory block" (MInt64asNT.to_nat p.(o)) bk).

  (* TO MOVE *)

  Definition handle_failure: (StaticFailE +' DynamicFailE) ~> failT (itree void1) :=
    fun _ _ => ret None.
 
  Definition errorT (m : Type -> Type) (a : Type) : Type :=
    m (unit + a)%type.
  Global Instance errotT_fun `{Functor.Functor m} : Functor.Functor (errorT m) :=
    {| Functor.fmap := fun x y f => 
                         Functor.fmap (fun x => match x with | inl _ => inl () | inr x => inr (f x) end) |}.

  Global Instance errorT_monad `{Monad m} : Monad (errorT m) :=
    {| ret := fun _ x => ret (inr x);
       bind := fun _ _ c k =>
                 bind (m := m) c 
                      (fun x => match x with | inl _ => ret (inl ()) | inr x => k x end)
    |}.
  
  Global Instance errotT_iter `{Monad m} `{MonadIter m} : MonadIter (errorT m) :=
    fun A I body i => Basics.iter (M := m) (I := I) (R := unit + A) 
                               (fun i => bind (m := m)
                                           (body i)
                                           (fun x => match x with
                                                  | inl _       => ret (inr (inl ()))
                                                  | inr (inl j) => ret (inl j)
                                                  | inr (inr a) => ret (inr (inr a))
                                                  end))
                               i.

  Definition handle_error: (StaticFailE +' DynamicFailE) ~> errorT (itree void1) :=
    fun _ _ => ret (inl ()).
  Definition interp_error := interp handle_error.

  Definition inject_signature {E} : void1 ~> E := fun _ (x:void1 _) => match x with end.
  Hint Unfold inject_signature : core.

  Definition interp_helix {X E} (t : itree Event X) (mem : memoryH) : failT (itree E) (memoryH * X) :=
    translate inject_signature (interp_fail handle_failure (interp_Mem t mem)).

  (* Finally, the semantics of FSHCOL for the top-level equivalence *)
  Definition semantics_FSHCOL (p: FSHCOLProgram) (data : list binary64)
    : failT (itree E_mcfg) (memoryH * list binary64) :=
    interp_helix (denote_FSHCOL p data) memory_empty.

End EventTranslation.

Notation "'with_cfg'"  := (@translate _ E_cfg (fun _ (x:void1 _) => match x with end)).
Notation "'with_mcfg'" := (@translate _ E_mcfg (fun _ (x:void1 _) => match x with end)).
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
  Notation "x" := (with_cfg x) (only printing, at level 10). 
  Notation "x" := (with_mcfg x) (only printing, at level 10). 
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
From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

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
                    (fun mx => match mx with | None => ret None | Some x => let '(mem',v) := x in interp_helix (k v) mem' end).
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

  (* Lemma interp_helix_vis : *)
  (*   forall T R E mem (e : Event T) (k : T -> itree Event R), *)
  (*     interp_helix (E := E) (vis e k) mem ≈ *)
  (*     interp_helix (vis e k) mem.  *)
  (*     (* ITree.bind ((case_ Mem_handler handle_failure helix_handler MDSHCOLOnFloat64.pure_state) T e mem) *) *)
  (*                (* (fun sx => Tau (interp_helix (k (snd sx)) (fst sx))). *) *)
  (* Proof. *)
  (*   intros.  *)
  (*   unfold interp_helix. *)
  (*   rewrite interp_Mem_vis_eqit. *)
  (*   rewrite interp_fail_bind, translate_bind. *)
    
  (*   apply interp_cbn.state_vis. *)
  (* Qed. *)

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

  (* Global Instance interp_helix_eutt {X E} {R : X -> X -> Prop} : *)
  (*   Proper (eutt R ==> eutt (option_rel R)) (@interp_helix X E). *)
  (* Proof. *)
  (* Qed. *)

End InterpHelix.

       
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


  (* Autorewrite and hint databases for more modular rewriting. *)
  (* "Normalizing" rewriting hint database. *)
  Hint Rewrite @translate_bind : itree.
  Hint Rewrite @interp_bind : itree.
  Hint Rewrite @translate_ret : itree.
  Hint Rewrite @interp_ret : itree.
  Hint Rewrite @translate_trigger : itree.
  Hint Rewrite @interp_trigger : itree.
  Hint Rewrite @bind_bind : itree.
  Hint Rewrite @bind_ret_l : itree.

  Hint Rewrite interp_cfg_to_L3_bind : vellvm.
  Hint Rewrite interp_cfg_to_L3_ret : vellvm.
  Hint Rewrite interp_cfg_to_L3_GR : vellvm.
  Hint Rewrite interp_cfg_to_L3_LR : vellvm.
  Hint Rewrite @lookup_E_to_exp_E_Global : vellvm.
  Hint Rewrite @lookup_E_to_exp_E_Local : vellvm.
  Hint Rewrite @subevent_subevent : vellvm.
  Hint Rewrite @exp_E_to_instr_E_Global : vellvm.
  Hint Rewrite @exp_E_to_instr_E_Local : vellvm.
  Hint Rewrite @subevent_subevent : vellvm.
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

  End Interp_Helix_No_Failure.
  
  Opaque interp_helix.

  Hint Resolve no_failure_helix_Ret : core.
  Hint Resolve no_failure_helix_bind_prefix : core.
  Hint Extern 4 (no_failure _) =>
  (match goal with
   | h : no_failure (interp_helix (ITree.bind _ _) _) |- _ =>
     eapply no_failure_helix_bind_continuation in h
   end) : core.

