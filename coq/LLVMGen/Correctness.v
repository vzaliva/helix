Require Import Coq.Arith.Arith.
Require Import Psatz.

Require Import Coq.Strings.String.

Notation "x @@ y" := (String.append x y) (right associativity, at level 60) : string_scope.

  Lemma string_cons_app :
    forall x y,
      String x y = ((String x "") @@ y)%string.
  Proof.
    reflexivity.
  Qed.

  Lemma string_app_assoc :
    forall (a b c : string),
      eq (a @@ (b @@ c))%string ((a @@ b) @@ c)%string.
  Proof.
    intros a b c.
    induction a.
    - reflexivity.
    - simpl. rewrite IHa.
      reflexivity.
  Qed.

    Ltac rev_str_helper acc s :=
      match s with
      | EmptyString => acc
      | (String ?x ?y) =>
        rev_str_helper (String x acc) y
      end.

    Ltac rev_str s := rev_str_helper EmptyString s.

    Ltac rewrite_str acc s :=
      match s with
      | (String ?x EmptyString) =>
        let r := rev_str acc in
        constr:(r)
      | (String ?x ?y) => rewrite_str (String x acc) y
      end.

    Ltac last_str s :=
      match s with
      | (String ?x EmptyString) => constr:(String x EmptyString)
      | (String ?x ?y) => last_str y
      end.

    Ltac make_append_str s :=
      match s with
      | (String ?x ?y) =>
        let rs := rewrite_str EmptyString (String x y) in
        let ls := last_str y in
        replace (String x y) with (rs @@ ls)%string by reflexivity
      end.

Import Coq.Strings.String Strings.Ascii.
Open Scope string_scope.
Open Scope char_scope.

Require Import Coq.Lists.List.

Require Import Coq.Numbers.BinNums. (* for Z scope *)
Require Import Coq.ZArith.BinInt.

Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.FSigmaHCOL.Int64asNT.
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

Require Import Vellvm.Numeric.Fappli_IEEE_extra.
Require Import Vellvm.Util.
Require Import Vellvm.LLVMEvents.
Require Import Vellvm.DynamicTypes.
Require Import Vellvm.Denotation.
Require Import Vellvm.Handlers.Memory.
Require Import Vellvm.TopLevel.
Require Import Vellvm.LLVMAst.
Require Import Vellvm.CFG.
Require Import Vellvm.TopLevelRefinements.
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
Import IO INT M Global Local.
Import TopLevelEnv.
Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

(* A couple of notations to avoid ambiguities while not having to worry about imports and qualified names *)
Notation memoryV := M.memory_stack.
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

  (* We define the translation by injection *)
  Definition translate_E_vellvm_mcfg : itree (ExternalCallE +' PickE +' UBE +' DebugE +' FailureE) ~> itree E_mcfg :=
    translate inl_.

  Definition translate_E_vellvm_cfg : itree (CallE +' PickE +' UBE +' DebugE +' FailureE) ~> itree E_cfg :=
    translate inl_.

  Definition translate_E_helix_mcfg : itree (StaticFailE +' DynamicFailE) ~> itree E_mcfg :=
    translate inr_.

  Definition translate_E_helix_cfg : itree (StaticFailE +' DynamicFailE) ~> itree E_cfg :=
    translate inr_.

  (* We therefore have the following resulting denotation functions. *)
  (* On the Vellvm side, for [mcfg]: *)
  Definition semantics_llvm_mcfg p : itree E_mcfg _ := translate_E_vellvm_mcfg (model_to_L3 helix_intrinsics p).
  (* Which get lifted to [toplevel_entity] as usual: *)
  Definition semantics_llvm (prog: list (toplevel_entity typ (list (LLVMAst.block typ)))) :=
    lift_sem_to_mcfg semantics_llvm_mcfg prog.

  (* On the Helix side: *)
  (* We first define what amount to initializing the runtime before starting executing the operator *)
  (* NOTEYZ: This should be moved somewhere else, it is part of the semantics of the language, not the compiler's problem *)
  (* NOTEYZ: It's janky that it's happening at the semantics level. Not unheard of, but janky *)
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
    translate_E_helix_mcfg (interp_Mem (denote_FSHCOL p data) memory_empty).

End EventTranslation.

(* Facilities to refer to the return types of the various pieces of denotations we manipulate *)

Section StateTypes.

  Local Open Scope type_scope.

  (* Return state of a denoted and interpreted [cfg].
     Note the lack of local stack *)
  Definition LLVM_memory_state_cfg
    := memoryV * (local_env * (global_env)).

  (* Constructor to avoid having to worry about the nesting *)
  Definition mk_LLVM_memory_state_cfg m l g: LLVM_memory_state_cfg := (m,(l,g)).

  (* Return state of a denoted and interpreted [mcfg] *)
  Definition LLVM_memory_state_mcfg
    := memoryV *
       (local_env * @Stack.stack (local_env) * (global_env)).

  (* Return state and value of a denoted and interpreted (open) [cfg].
     Note the lack of local stack.
     Note that we may return a [block_id] alternatively to a [uvalue]
   *)
  Definition LLVM_state_cfg_T (T:Type): Type
    := memoryV * (local_env * (global_env * T)).
  Definition LLVM_state_cfg
    := LLVM_state_cfg_T (block_id + uvalue).

  (* Return state and value of a denoted and interpreted [mcfg]. *)
  Definition LLVM_state_mcfg_T (T:Type): Type
    := memoryV * (local_env * @Stack.stack (local_env) * (global_env * T)).
  Definition LLVM_state_mcfg :=
    LLVM_state_mcfg_T uvalue.

  (* -- Injections -- *)
  (* The nested state transformers associate the products the other way,
     we therefore define injections of memory states and values into return
     types of computations.
   *)
  Definition mk_LLVM_state_cfg_from_mem (T:Type) (v:T): LLVM_memory_state_cfg -> (LLVM_state_cfg_T T)
    := λ '(m, (ρ, g)), (m, (ρ, (g, v))).

  Definition mk_LLVM_state_mcfg_from_mem (T:Type) (v:T): LLVM_memory_state_mcfg -> (LLVM_state_mcfg_T T)
    := λ '(m, (ρ, g)), (m, (ρ, (g, v))).

End StateTypes.

(* Facilities to refer to the type of relations used during the simulations of various pieces of denotions we manipulate *)
(* TODOYZ: Think about those, rename. *)
Section RelationTypes.

  (** Relation of memory states which must be held for
      intialization steps *)
  Definition Type_R_memory_cfg: Type
    := evalContext ->
       memoryH → LLVM_memory_state_cfg → Prop.

  (** Relation of memory states which must be held for
      intialization steps *)
  Definition Type_R_memory_mcfg: Type
    := evalContext ->
       memoryH → LLVM_memory_state_mcfg → Prop.

  (** Type of bisimulation relations between DSHCOL and VIR internal to CFG states,
      parameterized by the types of the computed values.
   *)
  Definition Type_R_cfg_T (TH TV: Type): Type
    := evalContext ->
       memoryH * TH → LLVM_state_cfg_T TV → Prop.

  (* Lifting a relation on memory states to one encompassing returned values by ignoring them *)
  Definition lift_R_memory_cfg (R: Type_R_memory_cfg) (TH TV: Type): Type_R_cfg_T TH TV :=
    fun σ '(memH,_) '(memV,(l,(g,_))) => R σ memH (memV,(l,g)).

  (* Lifting a relation on results to one encompassing states by ignoring them *)
  Definition lift_R_result_cfg {TH TV: Type} (R: TH -> TV -> Prop): Type_R_cfg_T TH TV :=
    fun _ '(_,vh) '(_,(_,(_,vv))) => R vh vv.

  (** Type of bisimulation relations between DSHCOL and VIR internal to CFG states,
      parameterized by the types of the computed values.
   *)
  Definition Type_R_mcfg_T (TH TV: Type): Type
    := evalContext ->
       memoryH * TH → LLVM_state_mcfg_T TV → Prop.

  Definition lift_R_memory_mcfg (R: Type_R_memory_mcfg) (TH TV: Type): Type_R_mcfg_T TH TV :=
    fun σ '(memH,_) '(memV,(l,(g,_))) => R σ memH (memV,(l,g)).

  (** Type of bisimulation relation between DSHCOL and LLVM states.
    This relation could be used for fragments of CFG [cfg].
   *)
  Definition Type_R_partial: Type
    := evalContext ->
       memoryH * () → LLVM_state_cfg → Prop.

  (** Type of bisimulation relation between DSHCOL and LLVM states.
      This relation could be used for "closed" CFG [mcfg].
   *)
  Definition Type_R_full: Type
    := evalContext ->
       memoryH * (list binary64) → LLVM_state_mcfg → Prop.

End RelationTypes.

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

  (* TODOYZ: Proof read, comment extensively *)

  (**
     [mem_lookup_llvm_at_i bk_llvm i ptr_size_helix v_llvm] is a judgment asserting that
     an array of [i] doubles can be read from the logical_block [bk_llvm],
     and that this array is precisely [v_llvm].

     NOTEYZ: [handle_gep_h] seems to completely dismiss the size argument in the
     array type. Is the [ptr_size_helix] argument useless?

     TODOYZ: This is weirdly low level. Break it into functions provided by
     Vellvm and rewrite it at a higher level?

   *)
  Definition mem_lookup_llvm_at_i (bk_llvm: M.logical_block) (i ptr_size_helix: nat) (v_llvm: uvalue): Prop :=
    exists offset,
      match bk_llvm with
      | M.LBlock _ bk_llvm _ =>
        M.handle_gep_h (DTYPE_Array (Z.of_nat ptr_size_helix) DTYPE_Double)
                       0
                       [DVALUE_I64 (DynamicValues.Int64.repr (Z.of_nat i))] ≡ inr offset /\
        M.deserialize_sbytes
          (M.lookup_all_index offset (M.sizeof_dtyp DTYPE_Double) bk_llvm M.SUndef)
          DTYPE_Double ≡ v_llvm
      end.

  (** Injective function from finite naturals [i<domain] to
   arbitrary type.

   NOTEYZ: To see at use, but this dependent record seems overly fancy to me, I'm a bit worried about it.
   If it turns out annoying, a simple function from teh list of element of interest into the image
   and inlining a trivial characterization of the injectivity in the invariant might be simpler.
   *)
  Record injection_Fin (A:Type) (domain : nat) :=
    mk_injection_Fin
      {
        inj_f : nat -> A;
        inj_f_spec :
          forall x y,
            x < domain /\ y < domain ->
            inj_f x ≡ inj_f y ->
            x ≡ y
      }.

  (**
     Relation used to relate memories after the initialization phase.
     Recall: [Type_R_memory ≜ evalContext -> memoryH -> LLVM_memory_state_cfg -> Prop]
     NOTEYZ: Shouldn't it be [(evalContext * memoryH) -> LLVM_memory_state_cfg -> Prop] rather?

     We have [memory_invariant (σ, memh) (meml,l,g)] when:
     - The [evalContext ≜ list DSHVal] can be mapped in an injective way into
       Vellvm. We make sure that injectivity is interpreted over the union of local
       and global environment.
       TODOYZ: Currently assumes a pointer in memory exists for each of these values.
       This is janky, to rethink.
   *)

(* TODOCB: This needs some changes. I think I need to know something about the relationship betwee ι and the vars list in IRState.

   Additionally, how ι is written down is wrong. Not every value in σ
   is a pointer, some values should be pure integer values for
   instance.
*)
Definition memory_invariant : Type_R_memory_cfg :=
  fun (σ : evalContext) (mem_helix : MDSHCOLOnFloat64.memory) '(mem_llvm, x) =>
    let σ_len := List.length σ in
    σ_len ≡ 0 \/ (* empty env immediately allowed, as injection could not exists *)
    let '(ρ, g) := x in
    exists (ι: injection_Fin raw_id σ_len),
    forall (x: nat) v,
      nth_error σ x ≡ Some v ->
      match v with
      | DSHnatVal v   =>
        exists ptr_llvm,
        ( (* variable in local environment *)
          (alist_find _ (inj_f ι x) ρ ≡ Some (UVALUE_Addr ptr_llvm) /\
           alist_find _ (inj_f ι x) g ≡ None) \/
          (* variable in global environment *)
          (alist_find _ (inj_f ι x) ρ ≡ None /\
           alist_find _ (inj_f ι x) g ≡ Some (DVALUE_Addr ptr_llvm))) /\
        (* the block must exists *)
        (exists  bk_llvm,
            (get_logical_block (fst mem_llvm) ptr_llvm ≡ Some bk_llvm) /\
            (* And value at this pointer must match *)
            (exists v_llvm,  mem_lookup_llvm_at_i bk_llvm 0 1 v_llvm /\ v_llvm ≡ UVALUE_I64 (DynamicValues.Int64.repr (Int64.intval v))))
      | DSHCTypeVal v =>
        exists ptr_llvm,
        ( (* variable in local environment *)
          (alist_find _ (inj_f ι x) ρ ≡ Some (UVALUE_Addr ptr_llvm) /\
           alist_find _ (inj_f ι x) g ≡ None) \/
          (* variable in global environment *)
          (alist_find _ (inj_f ι x) ρ ≡ None /\
           alist_find _ (inj_f ι x) g ≡ Some (DVALUE_Addr ptr_llvm))) /\
        (* the block must exists *)
        (exists  bk_llvm,
            (get_logical_block (fst mem_llvm) ptr_llvm ≡ Some bk_llvm) /\
            (* And value at this pointer must match *)
            (exists v_llvm,  mem_lookup_llvm_at_i bk_llvm 0 1 v_llvm /\ v_llvm ≡ UVALUE_Double v))
      | DSHPtrVal ptr_helix ptr_size_helix =>
        forall bk_helix,
          memory_lookup mem_helix ptr_helix ≡ Some bk_helix ->
          exists ptr_llvm bk_llvm,
            alist_find _ (inj_f ι x) ρ ≡ Some (UVALUE_Addr ptr_llvm) /\
            get_logical_block (fst mem_llvm) ptr_llvm ≡ Some bk_llvm /\
            (fun bk_helix bk_llvm =>
               forall i, Int64.lt i ptr_size_helix ->
                    exists v_helix v_llvm,
                      mem_lookup (MInt64asNT.to_nat i) bk_helix ≡ Some v_helix /\
                      mem_lookup_llvm_at_i bk_llvm (MInt64asNT.to_nat i)
                                           (MInt64asNT.to_nat ptr_size_helix) v_llvm /\
                      v_llvm ≡ UVALUE_Double v_helix
            ) bk_helix bk_llvm
      end.


(**
   Lifting of [memory_invariant] to include return values in the relation.
   This relation is used to prove the correctness of the compilation of operators.
   The value on the Helix side is trivially [unit]. The value on the Vellvm-side however
   is non trivial, we will most likely have to mention it.
*)
(* TODO: Currently this relation just preserves memory invariant.
   Maybe it needs to do something more?
 *)
Definition bisim_partial: Type_R_partial
  :=
    fun σ '(mem_helix, _) '(mem_llvm, x) =>
      let '(ρ, (g, bid_or_v)) := x in
      memory_invariant σ mem_helix (mem_llvm, (ρ, g)).

(**
   Relation over memory and invariant for a full [cfg], i.e. to relate states at
   the top-level.
   Currently a simple lifting of [bisim_partial]. 
*)
Definition bisim_full: Type_R_full  :=
  fun σ  '(mem_helix, v_helix) mem_llvm =>
    let '(m, ((ρ,_), (g, v))) := mem_llvm in
    bisim_partial σ (mem_helix, tt) (mk_LLVM_state_cfg_from_mem (inr v) (m, (ρ, g))).


(** Relation bewteen the final states of evaluation and execution
    of DHCOL program.

    At this stage we do not care about memory or environemnts, and
    just compare return value of [main] function in LLVM with
    evaulation results of DSHCOL.
 *)
Definition bisim_final: Type_R_full :=
  fun σ '(_, h_result) '(_,(_,(_,llvm_result))) =>
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

(* begin tactics *)

(* TODOYZ: This is a redefinition from [DSigmaHCOLITree]. To remove after proper reorganization into two files *)
(* TODOYZ: Actually even more so there should be a clean part of the tactics that do the generic structural
   rewriting, and a wrapper around it doing stuff specific to this denotation. We should only need the former
   here I believe *)

Ltac inv_option :=
  match goal with
  | h: Some _ ≡ Some _ |-  _ => inv h
  | h: None   ≡ Some _ |-  _ => inv h
  | h: Some _ ≡ None   |-  _ => inv h
  | h: None   ≡ None   |-  _ => inv h
  end.

Ltac inv_sum :=
  match goal with
  | h: inl _ ≡ inl _ |-  _ => inv h
  | h: inr _ ≡ inr _ |-  _ => inv h
  | h: inl _ ≡ inr _ |-  _ => inv h
  | h: inr _ ≡ inl _ |-  _ => inv h
  end.

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

Ltac hide_string :=
  match goal with
  | |- context [String ?x ?y] => remember (String x y)
  end.

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

  Lemma interp_Mem_vis_eqit :
    forall T R mem (e : Event T) (k : T -> itree Event R),
      interp_Mem (vis e k) mem ≅ ITree.bind ((case_ Mem_handler MDSHCOLOnFloat64.pure_state) T e mem) (fun sx => Tau (interp_Mem (k (snd sx)) (fst sx))).
  Proof.
    intros T R mem e k.
    unfold interp_Mem.
    apply interp_state_vis.
  Qed.

  (* Lemma interp_Mem_trigger : *)
  (*   forall T R mem (e : Event T) (k : T -> itree Event R), *)
  (*     interp_Mem (ITree.bind (trigger e) k) mem ≈ ITree.bind ((case_ Mem_handler MDSHCOLOnFloat64.pure_state) T e mem) (fun sx => interp_Mem (k (snd sx)) (fst sx)). *)
  (* Proof. *)
  (*   intros T R mem e k. *)
  (*   unfold interp_Mem. *)
  (*   apply interp_state_vis. *)
  (* Qed. *)


  Lemma interp_Mem_MemLU :
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

Section NEXP.

  (**
     We prove in this section the correctness of the compilation of numerical expressions, i.e. [NExpr].
     The corresponding compiling function is [genNExpr].

     Helix side:
     * nexp: NExpr
     * σ: evalContext
     * s: IRState

The expression must be closed in [evalContext]. I.e. all variables are below the length of σ
vars s1 = σ?

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
  Opaque interp_Mem.
  Opaque append.

  Ltac break_and :=
    repeat match goal with
           | h: _ * _ |- _ => destruct h
           end.

  Definition genNExpr_sim σ := (bisim_partial σ).

  (* TOODYZ *)
  (* Definition evalContext_IRState_rel: evalContext -> IRState -> Prop := *)
  (*   fun σ st => *)
  (*     (forall v n, context_lookup "NVar not found" σ v ≡ inr (DSHnatVal n) <-> ) *)
  (* nth_error (vars s2) v ≡ Some (i, TYPE_I 64%Z) /\
     lookup i g/l ≡ n?
   *)
  (*     True. *)

  Ltac simp_comp H :=
    cbn in H; repeat (inv_sum || break_and || break_match_hyp).

  From Vellvm Require Import
       TypToDtyp.

  (**
     NOTEYZ: It is slightly annoying that [IRState] is an extra piece of state introduced by
     the compiler by that belongs to neither language.
     Invariants about it must therefore be carried separately from the simulation relation.
   *)

  (**
     Relational injection of [DSHType] into VIR's [typ]
     TODOYZ : Well, precisely, todo.
     OBSOLETE: replaced by [getIRType]
   *)
  (* Variant DSHType_typ : DSHType -> typ -> Prop := *)
  (* | DSHnat_IntType : DSHType_typ DSHnat IntType *)
  (**
     The compiler maintains a sort of typing context named [IRState].
     It should be essentially a well-formed typing judgment for the current
     value of the [evalContext], but injecting the types from [DSHCOL] to [VIR].
   *)
  Definition WF_IRState (σ: evalContext) (s: IRState): Prop :=
    forall (i: ident) (t: typ) (n: nat),
      nth_error (vars s) n ≡ Some (i,t) ->
      exists (v: DSHVal), nth_error σ n ≡ Some v /\
                     getIRType (DSHType_of_DSHVal v) ≡ t.

  Lemma WF_IRState_lookup_cannot_fail :
    forall σ it s n msg msg',
      WF_IRState σ s ->
      nth_error (vars s) n ≡ Some it ->
      context_lookup msg σ n ≡ inl msg' ->
      False.
  Proof.
    intros ? [] * WF LU1 LU2; apply WF in LU1; destruct LU1 as (? & LU & _).
    unfold context_lookup in LU2; rewrite LU in LU2; inversion LU2.
  Qed.

  Ltac abs_by H :=
    exfalso; eapply H; eauto.

  (* TODOYZ : MOVE *)
  Definition conj_rel {A B : Type} (R S: A -> B -> Prop): A -> B -> Prop :=
    fun a b => R a b /\ S a b.
  Infix "⩕" := conj_rel (at level 85).

  Variable (R: Type_R_memory_cfg).
  Definition R' : Int64.int -> uvalue -> Prop := fun i uv => uv ≡ UVALUE_I64 i.
  (* R, R' to be instantiated *)

  (* Facts that must be derivable *)
  Axiom R_GLU : forall σ s v id memH memV l g n,
  WF_IRState σ s ->
  nth_error (vars s) v ≡ Some (ID_Global id, TYPE_I 64%Z) ->
  R σ memH (memV, (l, g)) ->
  context_lookup "NVar not found" σ v ≡ inr (DSHnatVal n) ->
  Maps.lookup id g ≡ Some (DVALUE_I64 n).

  Axiom R_LLU : forall σ s v id memH memV l g n,
  WF_IRState σ s ->
  nth_error (vars s) v ≡ Some (ID_Local id, TYPE_I 64%Z) ->
  R σ memH (memV, (l, g)) ->
  context_lookup "NVar not found" σ v ≡ inr (DSHnatVal n) ->
  Maps.lookup id l ≡ Some (UVALUE_I64 n).

  (* TODOYZ: name consistency Nexp/NExpr/Nexpr/NExp *) 
  Lemma genNExpr_correct :
    forall (* Compiler bits *) (s1 s2: IRState)
      (* Helix  bits *)   (nexp: NExpr) (σ: evalContext) (memH: memoryH)
      (* Vellvm bits *)   (exp: exp typ) (c: code typ) (g : global_env) (l : local_env) (memV : memoryV),
      genNExpr nexp s1 ≡ inr (s2, (exp, c)) -> (* Compilation succeeds *)
      WF_IRState σ s1 ->                       (* Well-formed IRState *)
      R σ memH (memV, (l, g)) ->
      eutt (lift_R_memory_cfg R σ ⩕ lift_R_result_cfg R' σ)
           (translate_E_helix_cfg  
              (interp_Mem (denoteNexp σ nexp)
                          memH))
           (translate_E_vellvm_cfg
              ((interp_cfg_to_L3 helix_intrinsics
                                 (D.denote_code (convert_typ [] c) ;; translate exp_E_to_instr_E (D.denote_exp None (convert_typ [] exp))))
                 g l memV)).
  Proof.
    induction nexp; intros * COMPILE WFIR PRE;
      assert (FOO: (s2,(exp,c)) ≡ (s2,(exp,c))) by reflexivity. (* TODOYZ: stupid hack to quickly check what case we are in. To remove *)
    - (* Variable case *)

      (* Reducing the compilation *)
      simp_comp COMPILE.
      (* TODO: move unfolding of error wrappers in [simp_comp]? *)
      all: unfold ErrorWithState.option2errS in *; break_match_hyp; cbn in *; try inv_sum.

      + (* The variable maps to an integer in the IRState *)
        
        (* Reducing the [DSHCOL] denotation
           TODO: automate
           TODO: should translate_E_helix_cfg and co be notations?
         *)
        unfold translate_E_helix_cfg; cbn.
        unfold denoteNexp, lift_Serr; cbn.
        break_inner_match_goal.
        * (* Variable not in context, [context_lookup] fails *)
          abs_by WF_IRState_lookup_cannot_fail.
        * destruct d.
          (* DSHnatVal *)
          (* Nat *)
          { unfold translate_E_helix_cfg; cbn; rewrite interp_Mem_ret, translate_ret.
            unfold translate_E_vellvm_cfg; cbn. rewrite interp_cfg_to_L3_bind, interp_cfg_to_L3_ret, bind_ret_l.
            (* TODOYZ: Ltac *)
            destruct i0; cbn.
            { (* Global *)
              unfold Traversal.endo, Traversal.Endo_ident, Traversal.Endo_id.
              rewrite translate_bind.
              rewrite translate_trigger.
              rewrite translate_bind.
              rewrite lookup_E_to_exp_E_Global.
              rewrite translate_trigger.
              rewrite exp_E_to_instr_E_Global.
              rewrite interp_cfg_to_L3_bind.
              rewrite interp_cfg_to_L3_GR with (v := DVALUE_I64 n).
              2: eapply R_GLU; eauto.
              (** TODO: Need to automatize all this boilerplate **)
              cbn; rewrite bind_ret_l.
              rewrite !translate_ret.
              rewrite interp_cfg_to_L3_ret.
              rewrite !translate_ret.
              (** TODO: Define specialized version on eutt for external use *)
              apply eqit_Ret.
              split; [apply PRE | reflexivity].
            }
            { (* Local *)
              unfold Traversal.endo, Traversal.Endo_ident, Traversal.Endo_id.
              rewrite translate_trigger.
              rewrite lookup_E_to_exp_E_Local.
              rewrite translate_trigger.
              rewrite exp_E_to_instr_E_Local.
              rewrite interp_cfg_to_L3_LR with (v := UVALUE_I64 n).
              2: eapply R_LLU; eauto.
              (** TODO: Need to automatize all this boilerplate **)
              cbn; rewrite !translate_ret.
              apply eqit_Ret.
              split; [apply PRE | reflexivity].
            }
          }
          { (* DSHCTypeVal *)
            
        * (* binary64, absurd. *)
          (* Lookup in σ and (vars s) should have matching types? *)
          exfalso.
          admit.
        *  (* block_id, absurd *)
          (* Lookup in σ and (vars s) should have matching types? *)
          exfalso.
          admit.
        * (* We find a pointer in vars *)
          (* Reducing the denotation *)
          unfold translate_E_helix_cfg; cbn.
          unfold denoteNexp, lift_Serr; cbn.
          match goal with |- context[context_lookup ?s ?x ?y] => destruct (context_lookup s x y) as [? | []] eqn:?EQ end.
          exfalso; admit.
          unfold translate_E_helix_cfg; cbn; rewrite interp_Mem_ret, translate_ret.
          admit.
          exfalso; admit.
          exfalso; admit.

    - (* Constant *)
      simp_comp COMPILE.

      unfold translate_E_helix_cfg; cbn; rewrite interp_Mem_ret, translate_ret.
      (* Ret (memH, t) *)
      admit.

    - (* NDiv *)

      simp_comp COMPILE.

      unfold denoteNexp; cbn.
      break_match_goal.
      exfalso; admit.
      break_match_goal.
      exfalso; admit.
      unfold translate_E_helix_cfg; cbn; rewrite interp_Mem_ret, translate_ret.
      admit.

    - 
      simp_comp COMPILE.
      admit.

    - (* NPlus *)

      simp_comp COMPILE.
      admit.

    - admit.

  (* Relations for expressions *)
  (* top might be able to just be Some (DTYPE_I 64) *)
  (* NOTEYZ: I am completely confused by this definition. *)
  Definition nexp_relation
             (env : list (ident * typ))
             (e : exp typ)
             (n : Int64.int)
             (r : (memory * (local_env * (global_env * ())))): Prop :=
    let '(mem_llvm, (ρ, (g, _))) := r in
    eutt (fun n '(_, (_, (_, uv))) => int64_concrete_uvalue_rel n uv)
         (ret n)
         (interp_cfg_to_L3 helix_intrinsics (translate exp_E_to_instr_E (D.denote_exp (Some (DTYPE_I 64)) (TransformTypes.fmap_exp _ _ (TypeUtil.normalize_type_dtyp env) e))) g ρ mem_llvm).

  (**
     Division case. Division by zero is ruled out by assuming that no failure can happen.
     TODOYZ: Do we:
      - rule out failure from the source program (usual assumption, sensible). If so, how to we express it?
      - prove preservation of failure. Unusual, stronger, require a change in our current non-interpretation of errors.
   *)
  (* TODO: Need something about denoteNexp not failing *)
  Lemma denote_nexp_div :
    forall (σ : evalContext) (nexp1 nexp2 : NExpr),
      eutt Logic.eq (denoteNexp σ (NDiv nexp1 nexp2))
           (ITree.bind (denoteNexp σ nexp1)
                       (fun (n1 : Int64.int) => ITree.bind (denoteNexp σ nexp2)
                                                        (fun (n2 : Int64.int) => denoteNexp σ (NDiv (NConst n1) (NConst n2))))).
  Proof.
  Admitted.


  (* TODOCB: do I need something relating IRstate and evalContext? *)
  (* TODOYZ: Cleanup the normalization of types layer.
             Should we have a typeclass to have a uniform way to normalize the sub-pieces of code?
   *)
  (* TODOYZ: Apparently, this might be dead code.
             There's also [denote_exp_nexp], [interp_denoteNexp_genNExpr] and [interp_cfg_to_L3_denote_exp]
   *)

  Lemma denoteNexp_genNExpr :
    forall (* Helix bits  *) (nexp : NExpr) (σ : evalContext) (st st' : IRState) mem_helix
      (* Vellvm bits *) (nexp_r : exp typ) (nexp_code : code typ) (env : list (ident * typ))  g ρ mem_llvm,
      (* TODOCB: Do I need mem_helix?
         YZ: I suspect it depends on whether you run the interpreter [interp_Mem] or not here
       *)
      memory_invariant σ mem_helix (mem_llvm, (ρ, g)) ->
      genNExpr nexp st  ≡ inr (st', (nexp_r, nexp_code)) ->
      eutt (nexp_relation env nexp_r)
           (translate inr_ (denoteNexp σ nexp))
           (translate inl_ (interp_cfg_to_L3 helix_intrinsics
                             (D.denote_code (map
                                               (λ '(id, i),
                                                (id, TransformTypes.fmap_instr typ dtyp (TypeUtil.normalize_type_dtyp env) i))
                                               nexp_code)) g ρ mem_llvm)).
  Proof.
    (*
    induction nexp; intros σ st st' mem_helix nexp_r nexp_code env g ρ mem_llvm Hmem H.
    - (* NVar *)
      cbn in H.
      repeat break_match_hyp; subst; inversion H; simpl.
      + cbn in Heqs.
        subst.
        rewrite interp_cfg_to_L3_ret.
        destruct (nth_error (vars st) v) eqn:Hnth; inversion Heqs; subst.
        unfold denoteNexp. cbn.
        unfold context_lookup.
        destruct (nth_error σ v) eqn:Hnthsigma.
        cbn. destruct d.
        cbn.
        do 2 rewrite translate_ret.
        apply eqit_Ret.
        cbn.
        * destruct i0; cbn.
          rewrite bind_trigger.
          repeat rewrite translate_vis.
          cbn.

          unfold interp_cfg_to_L3.
          unfold INT.interp_intrinsics.
          rewrite interp_vis.
          cbn.
          rewrite interp_global_bind.
          unfold INT.F_trigger.
          unfold interp_global at 2.
          setoid_rewrite interp_state_trigger.
          rewrite bind_bind.
          cbn.
          break_match.
          2: admit. (* exception *)
          rewrite bind_ret_l.
          rewrite bind_tau.
          rewrite tau_eutt.
          rewrite bind_ret_l.
          rewrite tau_eutt.
          rewrite interp_translate.
          cbn.
          rewrite translate_ret.
          rewrite interp_ret.
          rewrite interp_global_ret.
          rewrite interp_local_ret.
          rewrite M.interp_memory_ret.

          apply eqit_Ret.

          unfold int64_concrete_uvalue_rel.
          rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
          unfold int64_dvalue_rel.
          inversion Hmem.
          apply ListUtil.length_0 in H0; subst.
          rewrite ListNth.nth_error_nil in Hnthsigma. inversion Hnthsigma.
          destruct H0.
          pose proof (H0 v (DSHnatVal n) Hnthsigma).
          cbn in H1.
          destruct H1 as (? & ? & ? & ? & ? & ? & ?).
          subst.
          destruct H1. admit.
          cbn.

          admit.
          admit.
        * admit.
        * admit.
        * admit.
      +
      (* exception *) admit.

      (*
        destruct t.
        destruct (Z.eq_dec sz 64).
        inversion H. reflexivity.
        inversion H.
        destruct t.
        *
      + inversion H.
       *)
    - (* NConst *)
      cbn in H; inversion H; cbn.
      rewrite interp_cfg_to_L3_ret.
      repeat rewrite translate_ret.
      apply eqit_Ret.
      cbn.
      rewrite translate_ret.
      rewrite interp_cfg_to_L3_ret.
      apply eqit_Ret.
      cbn.
      rewrite DynamicValues.Int64.unsigned_repr.
      apply Z.eq_refl.
      pose proof (DynamicValues.Int64.intrange t).
      unfold DynamicValues.Int64.max_unsigned.
      omega.
    - cbn in H.
      repeat break_match_hyp; inversion H.

      repeat rewrite map_app.
      repeat setoid_rewrite denote_code_app.

      rewrite denote_nexp_div.
      pose proof IHnexp1 σ _ _ mem_helix _ _ env g ρ mem_llvm Hmem Heqs.
      rewrite interp_cfg_to_L3_bind.
      repeat setoid_rewrite translate_bind.
      eapply eutt_clo_bind; eauto.

      intros u1 u2 H4.
      repeat break_match.
      rewrite interp_cfg_to_L3_bind; rewrite translate_bind.
      eapply eutt_clo_bind; eauto.
      (* eapply H0. *)

      (* intros u0 u3 H5. *)
      (* repeat break_match. *)

      (* (* We executed code that generated the values for the *)
      (* expressions for the binary operations... Now we need to denote *)
      (* the expressions themselves. *) *)
      (* (* simplify left side to ret *) *)
      (* cbn. *)

      (* repeat rewrite translate_bind.       *)
      (* repeat rewrite interp_cfg_to_L3_bind. *)
      (* repeat rewrite bind_bind. *)

      (* genNExpr nexp1 st ≡ inr (i, (e, c)) *)
      (* I need something relating `denote_exp e` and `denoteNexp nexp1`... *)
     *)
  Admitted.

  Lemma denote_exp_nexp:
    forall nexp st i e c mem_llvm σ g ρ env,
      genNExpr nexp st ≡ inr (i, (e, c)) ->
      (* TODO: factor out this relation *)
      eutt (fun n '(m, (l, (g, uv))) => int64_concrete_uvalue_rel n uv)
           (translate inr_ (denoteNexp σ nexp))
           (translate inl_ (interp_cfg_to_L3 helix_intrinsics (translate exp_E_to_instr_E (D.denote_exp (Some (DTYPE_I 64)) (TransformTypes.fmap_exp _ _ (TypeUtil.normalize_type_dtyp env) e))) g ρ mem_llvm)).
  Proof.
    induction nexp; intros st i e c mem_llvm σ g ρ env H.
    - cbn in H; repeat break_match_hyp; try solve [inversion H].
      + (* Int case *)
        cbn.
        unfold denoteNexp. cbn.
        break_match.
        * cbn.
          (* exception *) admit.
        * break_match.
          -- inversion H. cbn.
             (* Need something linking id to global_env / local_env *)
             destruct i1.
             ++ cbn. rewrite bind_trigger.
                repeat rewrite translate_vis.
                admit.
             ++ admit.
          -- cbn. (* exception *) admit.
          -- cbn. (* exception *) admit.
      + (* Pointer case *)
        admit.
    - cbn in H; repeat break_match_hyp; inversion H; cbn.
      admit.
  Admitted.

  (* TODO: awful AWFUL name. Need to figure out which of these we need *)
  Definition nexp_relation_mem (σ : evalContext) (helix_res : MDSHCOLOnFloat64.memory * Int64.int) (llvm_res : TopLevelEnv.memory * (local_env * (global_env * ()))) : Prop
    :=
      let '(mem_helix, n) := helix_res in
      let '(mem_llvm, (ρ, (g, _))) := llvm_res in
      memory_invariant σ mem_helix (mem_llvm, (ρ, g)).

  Lemma interp_denoteNexp_genNExpr :
    forall (nexp : NExpr) (st st' : IRState) (nexp_r : exp typ) (nexp_code : code typ) (env : list (ident * typ)) (σ : evalContext) g ρ mem_llvm memory,
      genNExpr nexp st  ≡ inr (st', (nexp_r, nexp_code)) ->
      eutt (nexp_relation_mem σ)
           (translate inr_ (interp_state (case_ Mem_handler MDSHCOLOnFloat64.pure_state) (denoteNexp σ nexp) memory))
           (translate inl_ (interp_cfg_to_L3 helix_intrinsics
                                             (D.denote_code (map
                                                               (λ '(id, i),
                                                                (id, TransformTypes.fmap_instr typ dtyp (TypeUtil.normalize_type_dtyp env) i))
                                                               nexp_code)) g ρ mem_llvm)).
  Proof.
  Admitted.

  Lemma interp_cfg_to_L3_denote_exp :
    forall nexp s s' ll_exp ll_code n m l g env σ,
      genNExpr nexp s ≡ inr (s', (ll_exp, ll_code)) ->
      denoteNexp σ nexp ≈ Ret n ->
      (interp_cfg_to_L3 helix_intrinsics
                        (translate exp_E_to_instr_E
                                   (D.denote_exp (Some (DTYPE_I 64))
                                                 (TransformTypes.fmap_exp typ dtyp (TypeUtil.normalize_type_dtyp env) ll_exp))) g l m) ≈ Ret (m, (l, (g, UVALUE_I64 n))).
  Proof.
    induction nexp;
      intros s s' ll_exp ll_code n m l g env σ H H0;
      cbn in H; inversion H.
    - (* NVar *)
      admit.
    (* Exceptions due to lookup and type mismatches! *)
    - (* NConst *)
      cbn. rewrite repr_intval.
      rewrite translate_ret, interp_cfg_to_L3_ret.
      apply eqit_inv_ret in H0; subst; auto.
      reflexivity.
    - (* NDiv *)
      rewrite denote_nexp_div in H0.
      cbn in *.
  Admitted.

  Lemma eval_denoteNexp :
    forall σ nexp val,
      evalNexp σ nexp ≡ inr val ->
      denoteNexp σ nexp ≅ Ret val.
  Proof.
    intros σ nexp val H.
    unfold denoteNexp. rewrite H.
    reflexivity.
  Qed.

  (* Unprovable, this should come from some well typedness assumption *)
  Lemma nvar_is_i64 :
    forall {v s s' s'' ll_exp ll_code str i t},
      genNExpr (NVar v) s ≡ inr (s', (ll_exp, ll_code)) ->
      getStateVar str v s ≡ inr (s'', (i, t)) ->
      t ≡ TYPE_I 64%Z.
  Proof.
  Admitted.

  (* TODO: This is WRONG

      Each instruction evaluated in the code that nexp produces can
      add a local variable.
   *)
  Lemma denote_code_of_nexp :
    forall nexp s s' ll_exp ll_code env mem_llvm g ρ,
      genNExpr nexp s ≡ inr (s', (ll_exp, ll_code)) ->
      exists ρ',
        interp_cfg_to_L3 helix_intrinsics
                         (D.denote_code
                            (map (λ '(id, i), (id, TransformTypes.fmap_instr typ dtyp (TypeUtil.normalize_type_dtyp env) i))
                                 ll_code)) g ρ mem_llvm ≈ Ret (mem_llvm, (ρ', (g, ()))).
  Proof.
    induction nexp;
      intros s s' ll_exp ll_code env mem_llvm g ρ H;
      remember H as Hgen eqn:Heqgen; clear Heqgen;
        inversion H; subst; cbn.
    -  cbn in H.
       break_match_hyp; inversion H1.
       destruct p, p.
       pose proof (nvar_is_i64 Hgen Heqs0); subst.
       break_match_hyp; try contradiction.
       exists ρ.
       inversion H1; subst.
       cbn.
       rewrite interp_cfg_to_L3_ret.
       reflexivity.
    - exists ρ. rewrite interp_cfg_to_L3_ret.
      reflexivity.
    - exists ρ. (* TODO: This will need to change *)

        break_match_hyp.
        inversion H1.
        repeat break_match_hyp.
        inversion H1.
        inversion H1.
        cbn in *.
        do 2 rewrite map_app.
        do 2 setoid_rewrite denote_code_app.
        setoid_rewrite bind_bind.

        rewrite interp_cfg_to_L3_bind.
        pose proof IHnexp1 s i e c env mem_llvm g ρ Heqs0 as [ρ' Hnexp1].
        rewrite Hnexp1.
        rewrite bind_ret_l.

        rewrite interp_cfg_to_L3_bind.
        pose proof IHnexp2 i i0 e0 c0 env mem_llvm g ρ' Heqs1 as [ρ'' Hnexp2].
        rewrite Hnexp2.
        rewrite bind_ret_l.

        cbn.
        repeat setoid_rewrite translate_bind.
        rewrite bind_bind.

        rewrite interp_cfg_to_L3_bind.

  Admitted.

  (* TODO: I think I might want to know that ρ comes from denoting ll_code, actually *)
  Lemma denote_exp_of_nexp :
    forall nexp ll_exp ll_code s s' env g ρ mem_llvm mem_helix σ i,
      memory_invariant σ mem_helix (mem_llvm, (ρ, g)) ->
      genNExpr nexp s ≡ inr (s', (ll_exp, ll_code)) ->
      evalNexp σ nexp ≡ inr i ->
      (interp_cfg_to_L3 helix_intrinsics
                        (translate exp_E_to_instr_E
                                   (D.denote_exp (Some (TypeUtil.normalize_type_dtyp env Utils.IntType))
                                                 (TransformTypes.fmap_exp typ dtyp (TypeUtil.normalize_type_dtyp env) ll_exp))) g ρ mem_llvm) ≈ Ret (mem_llvm, (ρ, (g, UVALUE_I64 i))).
  Proof.
    setoid_rewrite normalize_IntType.
    induction nexp;
      intros ll_exp ll_code s s' env g ρ mem_llvm mem_helix σ i Hmem H H0;
      inversion H; inversion H0; subst; cbn.
    - repeat break_match_hyp; inversion H3; inversion H2;
        cbn.
      destruct i1; cbn.
      rewrite bind_trigger.
      repeat setoid_rewrite translate_vis.
      repeat setoid_rewrite translate_ret.


      unfold interp_cfg_to_L3.
      {
        Set Nested Proofs Allowed.

        
      setoid_rewrite interp_intrinsics_vis; cbn.
      unfold INT.F_trigger.
      rewrite bind_trigger.
      setoid_rewrite interp_global_vis; cbn.

      unfold memory_invariant in Hmem.
      unfold context_lookup in Heqs0. destruct (nth_error σ v) eqn:Hlookup; inversion Heqs0.
      destruct Hmem as [Hmem | Hmem].
      { (* Case where sigma is nil *)
        assert (σ ≡ []) by (apply ListUtil.length_0; auto).
        subst; cbn in Hlookup; rewrite ListNth.nth_error_nil in Hlookup.
        inversion Hlookup.
      }

      destruct Hmem as [iota Hmem].
      (* TODO: need to be able to relate

            alist_find AstLib.eq_dec_raw_id id g

            and ι somehow.
       *)

            Lemma gen_var_irstate_rel :
              forall v s s' ll_exp ll_code mem_helix σ mem_llvm ρ g i id sz,
                genNExpr (NVar v) s ≡ inr (s', (ll_exp, ll_code)) ->
                memory_invariant σ mem_helix (mem_llvm, (ρ, g)) ->
                evalNexp σ (NVar v) ≡ inr i ->
                getStateVar "NVar out of range" v s ≡ inr (s', (ID_Global id, TYPE_I sz)) ->
                alist_find AstLib.eq_dec_raw_id id g ≡ Some (DVALUE_I64 i).
            Proof.
              intros v s s' ll_exp ll_code mem_helix σ mem_llvm ρ g i id sz H H0 H1 H2.
              cbn in H1. break_match_hyp; inversion H1.
              break_match_hyp; inversion H1; subst.
              unfold context_lookup in *.
              destruct (nth_error σ v) eqn:Hlookup.
              2: { inversion Heqs0. }
              cbn in H2.
              destruct (nth_error (vars s) v) eqn:Hlookupst.
              2: { inversion H2. }
              cbn in H2.
              inversion H2. subst.
              inversion Heqs0.
              subst.
              unfold memory_invariant in H0.
              rename H0 into Hmem.
              destruct Hmem as [Hmem | Hmem].
              { (* Case where sigma is nil *)
                assert (σ ≡ []) by (apply ListUtil.length_0; auto).
                subst; cbn in Hlookup; rewrite ListNth.nth_error_nil in Hlookup.
                inversion Hlookup.
              }

              destruct Hmem as (Hinj & ?).
              specialize (H0 _ _ Hlookup).

              destruct H0 as [ptr_llvm [[[Hlocal Hnotglobal] | [Hnotlocal Hglobal]]
                                 [bk_llvm [Hlogicalblock [v_llvm [Hlookup_block Hmatches]]]]]]; subst.

              admit. (* locals *)

              cbn.

              cbn in *; subst.

            Qed.



End NEXP.


(* CHECKPOINTYZ: Continue the dive from there Tomorrow *)

(* Lemma LLVMGen_correct: forall i o globals op name newstate pll (σ: evalContext), *)
(*   LLVMGen i o globals false op name newState ≡ inr pll -> *)
(*   eutt (bisim_final σ) *)
(*        (translate (@subevent _ E_mcfg _) *)
(*                   (interp_Mem (denoteDSHOperator σ op) memory_empty)) *)
(*        (semantics_llvm pll). *)

(* Top-level compiler correctness lemma  *)
(* Theorem compiler_correct: *)
(*   forall (p:FSHCOLProgram) *)
(*     (data:list binary64) *)
(*     (pll: toplevel_entities typ (list (LLVMAst.block typ))), *)
(*     compile_w_main p data ≡ inr pll -> *)
(*     eutt (bisim_final []) (semantics_FSHCOL p data) (semantics_llvm pll). *)
(* Proof. *)
(*   intros p data pll H. *)
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

(*   (* This no longer follows from [compiler_correct_aux]. It will *)
(*      at pen-ultimate step when the [main] does [return] on a memory *)
(*      block. *)

(*        eapply eqit_mon. *)
(*        3:apply bisim_full_final_subrelation. *)
(*        3:eapply compiler_correct_aux. *)
(*        tauto. *)
(*        tauto. *)
(*        tauto. *)
(*    *) *)
(* Admitted. *)


Definition blah {T} (defs : IS.intrinsic_definitions) (m : memory) (g : global_env) (l : local_env) (e : instr_E T) :=
  M.interp_memory (interp_local (interp_global (INT.interp_intrinsics_h defs e) g) l) m.
(*
  (State.interp_state
         (case_ (M.E_trigger (F:=PickE +' UBE +' DebugE +' FailureE))
            (case_ M.handle_intrinsic (case_ M.handle_memory (M.F_trigger (F:=PickE +' UBE +' DebugE +' FailureE)))))
         (State.interp_state (interp_local_h (G:=MemoryE +' PickE +' UBE +' DebugE +' FailureE))
            (State.interp_state (interp_global_h (G:=LLVMEnvE +' MemoryE +' PickE +' UBE +' DebugE +' FailureE))
               (INT.interp_intrinsics_h defs e) g) l) m).
*)

Import Coq.Strings.String Strings.Ascii.
Open Scope string_scope.
Open Scope char_scope.

  (* TODO: Prove and move to itrees *)
  Lemma interp_state_interp :
    ∀ (E F G : Type -> Type) (R : Type) (ST : Type) (st : ST)
      (f : ∀ T : Type, E T → itree F T) (g : forall T : Type, F T -> Monads.stateT ST (itree G) T) (t : itree E R),
      interp_state g (interp f t) st ≅ interp_state (fun (T : Type) (e : E T) => interp g (f T e)) t st.
  Proof.
  Admitted.

  (* TODO: Move to itrees? *)
  (* Check interp_interp. *)
  (* Lemma interp_state_interp_state : *)
  (*   forall (E G H : Type -> Type) (R STF STG T: Type) *)
  (*     (f : ∀ T : Type, E T → Monads.stateT STF (itree G) T) *)
  (*     (g : forall T : Type, G T -> Monads.stateT STG (itree H) T) *)
  (*     (sf : STF) (sg : STG) *)
  (*     (t : itree E R) t', *)
  (*     interp_state g (interp_state f t sf) sg ≅ t'. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold interp_state. *)
  (*   Check interp_interp. *)

  (*   Check interp g (fun T e => f T e sf) sg. *)
  (*   setoid_rewrite interp_interp. *)
  (*   Set Nested Proofs Allowed. *)
  (*   assert (itree H (STG * (STF * R))). *)
  (*   refine (interp_state _ _ _). *)
  (*   refine (@interp_state G _ STG _ _ _ _ _). *)

  (*   (fun (T : Type) (e : E T) => _) t). *)
  (* Qed. *)


(*
    for an opeartor, in initialized state
    TODO: We could probably fix [env] to be [nil]
 *)

  Lemma DSHAssign_singleton :
    forall (nextblock : block_id) (src dst : MemVarRef) (st st' : IRState) (bid_in : block_id)
      (bks : list (LLVMAst.block typ)),
      genIR (DSHAssign src dst) nextblock st ≡ inr (st', (bid_in, bks)) ->
      exists b,
        genIR (DSHAssign src dst) nextblock st ≡ inr (st', (bid_in, [b]))
        /\ snd (blk_term b) ≡ TERM_Br_1 nextblock
        /\ blk_id b ≡ bid_in /\ bks ≡ [b].
  Proof.
    intros nextblock src dst st st' bid_in bks HCompile.
    simpl in HCompile. destruct src, dst.
    simpl in HCompile.
    repeat break_match_hyp; try inl_inr.
    inv Heqs; inv HCompile.
    unfold genFSHAssign in Heqs2.
    cbn in Heqs2.
  Admitted.

  Lemma genIR_DSHAssign_to_genFSHAssign :
    forall src dst nextblock st st' b,
      genIR (DSHAssign src dst) nextblock st ≡ inr (st', (blk_id b, [b])) ->
      exists psrc nsrc pdst ndst b_orig comments i i0 i1 i2 i3 n n0,
        src ≡ (psrc, nsrc) /\
        dst ≡ (pdst, ndst) /\
        [b] ≡ add_comment [b_orig] comments /\
        resolve_PVar psrc st ≡ inr (i, (i0, n)) /\
        resolve_PVar pdst i  ≡ inr (i1, (i2, n0)) /\
        genFSHAssign n n0 i0 i2 nsrc ndst nextblock i1 ≡ inr (i3, (blk_id b, [b_orig])).
  Proof.
    intros src dst nextblock st st' b H.
    destruct src as (psrc, nsrc). exists psrc. exists nsrc.
    destruct dst as (pdst, ndst). exists pdst. exists ndst.

    inv H.
    destruct (resolve_PVar psrc st) eqn:Hr. inversion H1.
    destruct p. destruct p.
    destruct (resolve_PVar pdst i) eqn:Hr1. inversion H1.
    destruct p. destruct p.
    destruct (genFSHAssign i1 i4 i0 i3 nsrc ndst nextblock i2) eqn:Hassign. inversion H1.
    destruct p. destruct s.
    match goal with
    | H: context[add_comment _ ?ss] |- _ => remember ss
    end.

    inversion H1.
    apply add_comment_singleton in H3. destruct H3 as (b_orig & Hl).
    exists b_orig. exists l0.
    exists i. exists i0. exists i2. exists i3. exists i5. exists i1. exists i4.
    subst; intuition.
  Qed.

(*   Lemma compile_NExpr_correct : *)
(*     forall (nexp : NExpr) (e : exp typ) (c : code typ) (σ : evalContext) env (mem : MDSHCOLOnFloat64.memory) s s' mem_llvm ρ g, *)
(*       genNExpr nexp s ≡ inr (s', (e, c)) -> *)
(*       eutt _ *)
(*            (translate inr_ (interp_Mem (denoteNexp σ nexp) mem)) *)
(*            (translate inl_ (interp_cfg_to_L3 helix_intrinsics *)
(*                                              (D.denote_code ((map (λ '(id, i), (id, TransformTypes.fmap_instr typ dtyp (TypeUtil.normalize_type_dtyp env) i)) *)
(*                                                                   c))) *)
(*                                              g ρ mem_llvm)). *)

(* (map (λ '(id, i), (id, TransformTypes.fmap_instr typ dtyp (TypeUtil.normalize_type_dtyp env) i)) *)
(*                    src_nexpcode) *)


  (* Probably need to know something about σ and mem_llvm,
     like memory_invariant... *)

  (* Print LLVMGEnvE. *)
  Lemma interp_cfg_to_L3_globalread :
    forall g1 l0 m4 id d,
      alist_find AstLib.eq_dec_raw_id id g1 ≡ Some d ->
      (interp_cfg_to_L3 helix_intrinsics (trigger (GlobalRead id))
                        g1 l0 m4) ≈ (Ret (m4, (l0, (g1, d)))).
  Proof.
    intros.
    unfold interp_cfg_to_L3, M.interp_memory, interp_local, interp_global, INT.interp_intrinsics.
    setoid_rewrite interp_vis.
    repeat setoid_rewrite interp_state_bind.
    cbn. unfold INT.F_trigger.

    setoid_rewrite interp_state_trigger.
    repeat setoid_rewrite interp_state_bind.
    rewrite bind_bind.

    cbn. rewrite H.
    repeat setoid_rewrite interp_state_ret.
    rewrite bind_ret_l.
    repeat rewrite interp_state_tau.
    rewrite bind_tau.
    repeat rewrite interp_state_ret.
    rewrite bind_ret_l.
    cbn.
    repeat rewrite interp_state_tau.
    rewrite interp_ret.
    repeat rewrite interp_state_ret.

    rewrite tau_eutt.
    rewrite tau_eutt.
    reflexivity.
  Qed.

  Lemma denotePexp_eutt_ret :
    forall (σ : evalContext) (v : var_id) a size,
      nth_error σ v ≡ Some (DSHPtrVal a size) ->
      denotePexp σ (PVar v) ≈ Ret a.
  Proof.
    intros σ v a size H.
    unfold denotePexp; cbn.
    rewrite H.
    reflexivity.
  Qed.


(* TODO: only handle cases where there are no exceptions? *)
Lemma compile_FSHCOL_correct
      (op: DSHOperator): forall (nextblock bid_in : block_id) (st st' : IRState) (bks : list (LLVMAst.block typ)) (σ : evalContext) (env : list (ident * typ)) (mem : MDSHCOLOnFloat64.memory) (g : global_env) (ρ : local_env) (mem_llvm : memory),
  nextblock ≢ bid_in ->
  bisim_partial σ (mem,tt) (mem_llvm, (ρ, (g, (inl bid_in)))) ->
  genIR op nextblock st ≡ inr (st',(bid_in,bks)) ->
  eutt (bisim_partial σ)
       (translate inr_
                  (interp_Mem (denoteDSHOperator σ op) mem))
       (translate inl_
                  (interp_cfg_to_L3 helix_intrinsics
                                    (D.denote_bks (fmap (typ_to_dtyp env) bks) bid_in)
                                    g ρ mem_llvm)).
Proof.
  induction op; intros; rename H1 into HCompile.
  - inv HCompile.
    eutt_hide_right; cbn.
    unfold interp_Mem; simpl denoteDSHOperator.
    rewrite interp_state_ret, translate_ret.
    subst i. 
    rewrite denote_bks_nil.
    cbn. rewrite interp_cfg_to_L3_ret, translate_ret.
    apply eqit_Ret; auto.
  - (*
      Assign case.
       Need some reasoning about
       - resolve_PVar
       - genFSHAssign
       - D.denote_bks over singletons
     *)
    apply DSHAssign_singleton in HCompile.
    destruct HCompile as (b & HCompile & Hterm & Hbid & Hbksbk).
    subst.

    (* Start by working on the left hand side *)



    unfold normalize_types_blocks.
    eutt_hide_left.
    unfold fmap; simpl Fmap_list'.
    (* Rewrite denote_bks to denote_block *)
    rewrite denote_bks_singleton; eauto using normalize_types_block_term.

    (* Work with denote_block *)
    (* I need to know something about b... *)
    pose proof genIR_DSHAssign_to_genFSHAssign src dst nextblock st HCompile as H1.
    destruct H1 as (psrc & nsrc & pdst & ndst & b_orig & comments & ist & i0 & ist1 & i1 & ist2 & n & n0 & Hsrc & Hdst & Hb & Hr & Hr' & Hfsh).

    cbn in Hb. inversion Hb.
    cbn.

    (* Now I need to know something about b_orig... *)
    (* I know it's generated from genFSHassign, though... *)
    cbn in Hfsh.

    (* Checkpoint *)
    inversion Hfsh.
    destruct (genNExpr nsrc
                       {|
                         block_count := S (block_count ist1);
                         local_count := S (S (S (local_count ist1)));
                         void_count := S (S (void_count ist1));
                         vars := vars ist1 |}) as [|(s', (src_nexpr, src_nexpcode))] eqn:Hnexp_src. inversion H3.
    destruct (genNExpr ndst s') as [|(s'', (dst_nexpr, dst_nexpcode))] eqn:Hnexp_dst. inversion H3.
    inversion H3.
    cbn.
    (*
    match goal with
    | |- context[D.denote_code (map _ (src_nexpcode ++ dst_nexpcode ++ ?x))] => remember x as assigncode
    end.

    (* start working on right side again *)
    subst i. cbn.
    subst src dst.

    destruct psrc as [src_v] eqn:Hpsrc, pdst as [dst_v] eqn:Hpdst.

    destruct (nth_error σ dst_v) as [d|] eqn:Hdst_v. 2: admit. (* Exception *)
    destruct d as [n_dst | v_dst | a_dst size_dst]. admit. admit. (* should only be able to be pointer *)

    destruct (nth_error σ src_v) as [d|] eqn:Hsrc_v. 2: admit. (* Exception *)
    destruct d as [n_src | v_src | a_src size_src]. admit. admit. (* should only be able to be pointer *)

    setoid_rewrite denotePexp_eutt_ret; eauto.

    repeat rewrite bind_ret_l.
    repeat setoid_rewrite bind_trigger.

    (* Should be able to handle MemLU's in a lemma as well *)
    destruct (memory_lookup_err "Error looking up 'x' in DSHAssign" mem a_src) eqn:Hmem_src.
    admit. (* Exception *)

    destruct (memory_lookup_err "Error looking up 'y' in DSHAssign" mem a_dst) eqn:Hmem_dst.
    admit. (* Exception *)
    cbn.

    repeat (rewrite interp_Mem_MemLU; eauto).

    destruct (evalNexp σ nsrc) as [|eval_src] eqn:Heval_src.
    admit. (* Exception *)

    destruct (evalNexp σ ndst) as [|eval_dst] eqn:Heval_dst.
    admit. (* Exception *)

    setoid_rewrite eval_denoteNexp; eauto.
    repeat setoid_rewrite bind_ret_l.
    cbn.

    destruct (mem_lookup_err "Error looking up 'v' in DSHAssign" (MInt64asNT.to_nat eval_src) m) eqn:Hmemlookup.
    admit. (* Exception *)
    cbn.
    rewrite bind_ret_l.

    rewrite interp_Mem_MemSet.

    (* Work on the right hand side again *)
    (* Unfold denote_code and break it apart. *)
    do 2 rewrite map_app.
    do 2 setoid_rewrite denote_code_app.
    do 2 setoid_rewrite bind_bind.

    repeat setoid_rewrite interp_cfg_to_L3_bind.
    repeat setoid_rewrite translate_bind.

    (* Need to relate denoteNexp and denote_code of genNexpr *)
    match goal with
    | |- context[ ITree.bind ?x ?y ] => remember y as BLAH
    end.

    Set Nested Proofs Allowed.

            Lemma irstate_rel (op: DSHOperator) :
              forall (nextblock bid_in : block_id) (st st' : IRState) (bks : list (LLVMAst.block typ)) (σ : evalContext) (env : list (ident * typ)) (mem : MDSHCOLOnFloat64.memory) (g : global_env) (ρ : local_env) (mem_llvm : memory),
                nextblock ≢ bid_in -> (* Do I need this? *)
                bisim_partial σ (mem,tt) (mem_llvm, (ρ, (g, (inl bid_in)))) ->
                genIR op nextblock st ≡ inr (st',(bid_in,bks)) ->


            Lemma lookup_global:
              forall σ mem_helix mem_llvm ρ g v i id s s' sz,
                memory_invariant σ mem_helix (mem_llvm, (ρ, g)) ->
                getStateVar "NVar out of range" v s ≡ inr (s', (ID_Global id, TYPE_I sz)) ->
                evalNexp σ (NVar v) ≡ inr i ->
                exists a, alist_find AstLib.eq_dec_raw_id id g ≡ Some (DVALUE_Addr a).
            Proof.
              intros σ mem_helix mem_llvm ρ g v i id s s' sz Hmem Hst Heval.
              cbn in Heval.
              unfold context_lookup in *.
              destruct (nth_error σ v) eqn:Hlookup; cbn in Heval; try solve [inversion Heval].
              unfold memory_invariant in Hmem.
              destruct Hmem as [Hmem | Hmem].
              { (* Case where sigma is nil *)
                assert (σ ≡ []) by (apply ListUtil.length_0; auto).
                subst; cbn in Hlookup; rewrite ListNth.nth_error_nil in Hlookup.
                inversion Hlookup.
              }

              destruct Hmem as (Hinj & ?).
              specialize (H _ _ Hlookup).

              (* Determine that d = DSHnatVal i *)
              destruct d eqn:Hd; cbn in Heval; inversion Heval as [Hni]; rewrite Hni in *.

              destruct H as [ptr_llvm [[[Hlocal Hnotglobal] | [Hnotlocal Hglobal]]
                                 [bk_llvm [Hlogicalblock [v_llvm [Hlookup_block Hmatches]]]]]]; subst.

              (* Variable is in the local environment *)
              admit.

              (* Variable is in the global environment *)
              exists ptr_llvm. unfold inj_f in Hglobal.
              destruct Hinj.
              cbn in Hglobal.

              (* Need something relating id and v *)
              destruct (inj_f0 v).

              - (* d = DSHnatVal i *)
                destruct H as
                    [ptr_llvm [[[Hlocal Hnotglobal] | [Hnotlocal Hglobal]]
                                 [bk_llvm [Hlogicalblock [v_llvm [Hlookup_block Hmatches]]]]]]; subst.
                admit.

                exists ptr_llvm.
                unfold inj_f in Hglobal.
                destruct Hinj.
                destruct inj_f0.


                unfold Hinj in

                 destruct Hsearch.

            Qed.
            .
              inversio


            destruct (alist_find AstLib.eq_dec_raw_id id g) eqn:Hg.
            Focus 2. admit. (* Exception *)

            rewrite bind_ret_l.
            repeat rewrite tau_eutt.
            cbn.
            rewrite interp_ret.
            rewrite interp_global_ret.
            cbn.

            setoid_rewrite interp_local_ret.
            unfold M.interp_memory.
            rewrite interp_state_ret.

            (* Need something relating g... memory_invariant ? *)

            setoid_rewrite interp_memory_ret.
            rewrite
            inversion Heqs1; subst.
            rewrite interp_cfg_to_L3_vis.
            setoid_rewrite tau_eutt.
            cbn.
            setoid_rewrite translate_vis.
            repeat rewrite translate_vis.
            do 2 setoid_rewrite interp_cfg_to_L3_vis; cbn.
            rewrite bind_bind.
            setoid_rewrite interp_cfg_to_L3_vis.
            rewrite bind_bind.
            setoid_rewrite interp_cfg_to_L3_vis.
            rewrite bind_bind.
            setoid_rewrite interp_cfg_to_L3_vis.
            rewrite bind_bind.
            repeat setoid_rewrite translate_ret.
            setoid_rewrite interp_intrinsics_vis.
            cbn;
            rewrite interp_cfg_to_L3_vis.
          - rewrite translate_ret, interp_cfg_to_L3_ret, repr_intval.
            reflexivity.
          -
        Qed.

        cbn.
        subst.
        rewrite IHnexp1.

        destruct (genNExpr nexp1 s) eqn:Hnexp1.
        inversion H1.
        destruct p, p.

        destruct (genNExpr nexp1 s) eqn:Hnexp1.
    Qed.



      memory * (local_env * (global_env * ()))memory * (local_env * (global_env * ()))
    Lemma interp_nex
    subst assigncode.
              cbn.

              repeat setoid_rewrite translate_bind.
              repeat setoid_rewrite interp_cfg_to_L3_bind.
              repeat setoid_rewrite bind_bind.

              destruct i0 eqn:Hi0.
              ** (* Global id *)
                repeat setoid_rewrite translate_bind.
                rewrite interp_cfg_to_L3_bind.
                repeat setoid_rewrite translate_vis.
                repeat setoid_rewrite bind_bind.
                repeat setoid_rewrite translate_ret.

                destruct (alist_find AstLib.eq_dec_raw_id id g1) eqn:Hlookup.
                Focus 2. admit. (* Exception *)

                cbn.

                match goal with
                | |- context [ ITree.bind ?x ?y ] => remember y
                end.

                setoid_rewrite interp_cfg_to_L3_globalread; eauto.

                rewrite translate_bind.
                rewrite bind_bind.
                repeat rewrite translate_ret.
                rewrite bind_ret_l.
                repeat rewrite translate_ret.
                rewrite interp_cfg_to_L3_ret.
                rewrite translate_ret.
                rewrite bind_ret_l.

                subst i3; cbn.

                match goal with
                | |- context [ ITree.bind ?x ?y ] => remember y
                end.

                repeat setoid_rewrite bind_bind.
                setoid_rewrite translate_ret.
                setoid_rewrite bind_ret_l.

                rewrite interp_cfg_to_L3_bind.
                rewrite translate_bind.
                rewrite bind_bind.

                rewrite normalize_IntType.
                progress cbn.
                rewrite translate_ret.
                rewrite interp_cfg_to_L3_ret.
                rewrite translate_ret, bind_ret_l.
                cbn.

                rewrite interp_cfg_to_L3_bind.
                rewrite interp_cfg_to_L3_denote_exp; eauto.

                (* This feels very stupid, surely this should all just evaluate? *)
                rewrite translate_bind.
                rewrite translate_ret.
                rewrite bind_ret_l.
                rewrite interp_cfg_to_L3_bind.
                rewrite translate_bind.
                rewrite interp_cfg_to_L3_ret.
                rewrite translate_ret, bind_ret_l.
                repeat rewrite interp_cfg_to_L3_bind.
                rewrite interp_cfg_to_L3_ret.
                rewrite bind_ret_l.
                cbn.

                rewrite uvalue_to_dvalue_of_dvalue_to_uvalue.
                unfold ITree.map.
                rewrite bind_trigger.
                rewrite translate_vis.
                cbn.
                setoid_rewrite translate_ret.

                subst i3.
                cbn.

                all: eauto.
                Focus 2. apply Hnexp_src.
                reflexivity.

                setoid_rewrite bind_ret_l.
                setoid_rewrite <- denote_exp_nexp.
                apply eutt_clo_bind.

                rewrite interp
                rewrite bind_trigger.
                rewrite translate_vis.
                rewrite translate_vis.
                setoid_rewrite translate_ret.
                setoid_rewrite translate_ret.
                cbn.
                repeat setoid_rewrite translate_bind.
                rewrite interp_cfg_to_L3_bind.
                repeat setoid_rewrite translate_vis.
                repeat setoid_rewrite bind_bind.
                repeat setoid_rewrite translate_ret.

                rewrite interp_cfg_to_L3_vis; cbn.
                repeat setoid_rewrite bind_bind.
                cbn.
                rewrite translate_bind.
                rewrite bind_bind.
                cbn.

                match goal with
                | |- context[ITree.bind ?ma ?b] => remember b as blah
                end.

                unfold interp_cfg_to_L3; cbn.
                unfold trigger.
                rewrite interp_intrinsics_vis.
                cbn.
                setoid_rewrite tau_eutt.
                setoid_rewrite interp_ret.
                setoid_rewrite bind_ret_r.
                unfold interp_global.
                cbn.
                unfold M.interp_memory.
                unfold interp_local.
                cbn.

                unfold INT.F_trigger.
                setoid_rewrite interp_state_trigger.
                cbn.
                destruct (alist_find AstLib.eq_dec_raw_id id g1) eqn:Hg1.
                Focus 2.
                (* exception *) admit.
                rewrite bind_ret_l.
                repeat rewrite interp_state_tau.
                rewrite tau_eutt.
                repeat rewrite interp_state_ret.
                rewrite translate_ret.
                rewrite bind_ret_l.

                subst blah.
                match goal with
                | |- context[ITree.bind ?ma ?b] => remember b as blah
                end.

                rewrite interp_cfg_to_L3_ret.
                rewrite tau_eutt.
                rewrite bind_ret_l, translate_ret.
                repeat rewrite translate_ret, interp_cfg_to_L3_ret.
                rewrite translate_ret, bind_ret_l.

                subst blah.
                match goal with
                | |- context[ITree.bind ?ma ?b] => remember b as blah
                end.

                repeat rewrite interp_cfg_to_L3_bind.
                setoid_rewrite translate_ret.
                rewrite interp_cfg_to_L3_ret.
                rewrite bind_ret_l.
                repeat rewrite interp_cfg_to_L3_bind.
                repeat rewrite bind_bind.
                rewrite translate_bind.
                rewrite bind_bind.

                epose proof (@denote_exp_nexp _ _ _ _ _ _ _ _ _ _ Hnexp_src).
                Check eutt_clo_bind.
                eapply eutt_clo_bind.

                rewrite interp_intrinsics_vis.

                destruct id eqn:Hid.
                --- (* Name *)


                  setoid_rewrite interp_interp.

                --- (* Local id *)
                admit.
              ** (* Local id *)
                admit.
        -- (* exceptions *) admit.
    + (* Need to handle exceptions *)
      admit.
     *)
    (* Focus 3. *)
    (* cbn. *)
    (* rewrite bind_ret_l. *)
    (* destruct (nth_error σ v0) eqn:Herr'. *)
    (* destruct d. *)

    (* Focus 3. *)

    (* (* Lookup failure *) *)
    (* Focus 2. cbn. *)
    (* unfold interp_Mem. *)
    (* setoid_rewrite interp_state_bind. *)
    (* unfold Exception.throw. *)
    (* rewrite interp_state_vis. cbn. *)
    (* unfold MDSHCOLOnFloat64.pure_state. *)
    (* rewrite bind_vis. rewrite bind_vis. *)
    (* unfold resum. unfold ReSum_inl. *)
    (* unfold resum. unfold ReSum_id. *)
    (* unfold id_. unfold inl_. *)

    (* rewrite translate_vis. *)
    (* unfold resum. unfold inr_. *)
    (* Check VisF. *)
    (* simpl. *)
    (* unfold interp_state. unfold interp. *)
    (* interp. *)
    (* unfold Exception.Throw. cb *)

    (* inversion H3. cbn. *)
    (* simpl. *)
    (* cbn. *)

    (* subst i. *)
    (* unfold interp_Mem; cbn. *)
    (* destruct src, dst. *)
    (* simpl in HCompile. *)
    (* repeat break_match_hyp; try inl_inr. *)
    (* inv Heqs; inv HCompile. *)
    (* unfold denotePexp, evalPexp, lift_Serr. *)
    (* subst. *)
    (* unfold interp_Mem. (* cbn *) *)
    (* (* match goal with *) *)
    (* (* | |- context[add_comment _ ?ss] => generalize ss; intros ls *) *)
    (* (* end. *) *)
    (* (* match goal with *) *)
    (* (* | |- context[add_comment _ ?ss] => generalize ss; intros ls1 *) *)
    (* (* end. *) *)

    (* (* subst. eutt_hide_right. *) *)
    (* (* cbn. *) *)
    (* (* unfold interp_Mem. *) *)
    (* (* rewrite interp_state_bind. *) *)
    (* (* unfold denotePexp, evalPexp. *) *)
    (* (* cbn. *) *)
    (* (* repeat setoid_rewrite interp_state_bind. *) *)
    (* (* rewrite denote_bks_singleton. *) *)
    (* (* destruct src, dst. *) *)
    (* (* simpl in HCompile. *) *)
    (* (* repeat break_match_hyp; try inl_inr. *) *)
    (* (* inv Heqs; inv HCompile. *) *)
    (* (* match goal with *) *)
    (* (* | |- context[add_comment _ ?ss] => generalize ss; intros ls *) *)
    (* (* end. *) *)
    (* (* unfold interp_Mem. *) *)
    (* (* simpl denoteDSHOperator. *) *)
    (* (* rewrite interp_state_bind, translate_bind. *) *)
    (* (* match goal with *) *)
    (* (*   |- eutt _ ?t _ => remember t *) *)
    (* (* end. *) *)

    (* (* Need a lemma to invert Heqs2. *)
    (*    Should allow us to know that the list of blocks is a singleton in this case. *)
    (*    Need then probably a lemma to reduce proofs about `D.denote_bks [x]` to something like the denotation of x, *)
    (*    avoiding having to worry about iter. *)
    (*  *) *)
    (* (* cbn; rewrite interp_cfg_to_L3_bind, interp_cfg_to_L3_ret, bind_ret_l. *) *)

    (* repeat match goal with *)
    (* | |- context [ String ?x ?y ] => remember (String x y) *)
    (* end. *)

    (* make_append_str in H6. *)
    admit.
  - (*
      Map case.
      Need some reasoning about
      - denotePexp
      - nat_eq_or_cerr
      - genIMapBody
      -
     *)
    simpl genIR in HCompile.

    (* repeat rewrite string_cons_app in HCompile. *)

    repeat break_match_hyp; try inl_inr.
    repeat inv_sum.
    cbn.
    (* Need to solve the issue with the display of strings, it's just absurd *)
    eutt_hide_right.
    unfold interp_Mem.
    rewrite interp_state_bind.
    admit.

  - admit.

  - admit.

  - admit.

  - eutt_hide_right.
    cbn. unfold interp_Mem.

    (*
    Check interp_state_bind.
    Check interp_bind.

interp_state_bind
     : ∀ (f : ∀ T : Type, ?E T → ?S → itree ?F (?S * T)) (t : itree ?E ?A) (k : ?A → itree ?E ?B) (s : ?S),
         interp_state f (ITree.bind t k) s
         ≅ ITree.bind (interp_state f t s) (λ st0 : ?S * ?A, interp_state f (k (snd st0)) (fst st0))

interp_bind
     : ∀ (f : ∀ T : Type, ?E T → itree ?F T) (t : itree ?E ?R) (k : ?R → itree ?E ?S),
         interp f (ITree.bind t k) ≅ ITree.bind (interp f t) (λ r : ?R, interp f (k r))

    rewrite interp_state_bind.
    rewrite interp_iter.
*)
    admit.

  - eutt_hide_right.
    cbn.
    unfold interp_Mem.
    rewrite interp_state_bind.
    (* rewrite bind_trigger.

    Locate ITree.bind.
    rewrite *)
    admit.
  - admit.

  - admit.

  - (* Sequence case.

     *)

    cbn in HCompile.
    break_match_hyp; try inv_sum.
    break_match_hyp; try inv_sum.
    destruct p, s.
    break_match_hyp; try inv_sum.
    destruct p, s; try inv_sum.
    eapply IHop1 with (env := env) (σ := σ) in Heqs1; eauto.
    eapply IHop2 with (env := env) (σ := σ) in Heqs0; eauto.
    clear IHop2 IHop1.
    eutt_hide_right.
    cbn; unfold interp_Mem in *.
    rewrite interp_state_bind.

    rewrite translate_bind.
    (* Opaque D.denote_bks. *)

    (* Set Nested Proofs Allowed. *)

    (* Lemma add_comment_app: forall bs1 bs2 s, *)
    (*     add_comment (bs1 ++ bs2)%list s ≡ (add_comment bs1 s ++ add_comment bs2 s)%list. *)
    (* Proof. *)
    (*   induction bs1 as [| b bs1 IH]; cbn; auto; intros bs2 s. *)
    (*   f_equal. rewrite IH; auto. *)

    (*   subst i0. *)
    (*   eutt_hide_left. *)
    (*   cbn. rewrite bind_ret_l. *)


(* Definition respectful_eutt {E F : Type -> Type} *)
(*   : (itree E ~> itree F) -> (itree E ~> itree F) -> Prop *)
(*   := i_respectful (fun _ => eutt eq) (fun _ => eutt eq). *)


(* Instance eutt_translate {E F R} *)
(*   : @Proper (IFun E F -> (itree E ~> itree F)) *)
(*             (eq2 ==> eutt RR ==> eutt RR) *)
(*             translate. *)
(* Proof. *)
(*   repeat red. *)
(*   intros until T. *)
(*   ginit. gcofix CIH. intros. *)
(*   rewrite !unfold_translate. punfold H1. red in H1. *)
(*   induction H1; intros; subst; simpl. *)
(*   - gstep. econstructor. eauto. *)
(*   - gstep. econstructor. pclearbot. eauto with paco. *)
(*   - gstep. rewrite H. econstructor. pclearbot. red. eauto 7 with paco. *)
(*   - rewrite tau_euttge, unfold_translate. eauto. *)
(*   - rewrite tau_euttge, unfold_translate. eauto. *)
(* Qed. *)

(* Instance eutt_translate' {E F : Type -> Type} {R : Type} (f : E ~> F) : *)
(*   Proper (eutt eq ==> eutt eq) *)
(*          (@translate E F f R). *)
(* Proof. *)
(*   repeat red. *)
(*   apply eutt_translate. *)
(*   reflexivity. *)
(* Qed. *)

(*     rewrite Heqs1. *)
(* eutt_translate' *)

Admitted.

Definition llvm_empty_memory_state_partial: LLVM_memory_state_cfg
  := (M.empty_memory_stack, ([], [])).


(* This code attempts to mimic global variable initialization from
   [Vellvm.Toplevel] and heavily depends on internal memory
   organization of Vellvm, as in [Vellvm.Handlers.Memory] *)
Section LLVM_Memory_Init.

  (* mimics [Alloca] handler *)
  Definition alloc_global (c_name:string) (c_typ:typ) (m:M.memory) (ms:M.mem_stack) :=
    (* TODO: not sure about this [typ] to [dtyp] conversion *)
    let d_typ := typ_to_dtyp [] c_typ in
    let new_block := M.make_empty_block d_typ in
    let key := M.next_logical_key m in
    let new_mem := M.add_logical key new_block m in
    match ms with
    | [] => inl "No stack frame for alloca."%string
    | frame :: stack_rest =>
      let new_stack := (key :: frame) :: stack_rest in
      (*  global_env = alist raw_id dvalue *)
      let a := DVALUE_Addr (key, 0%Z) in
      ret (new_mem, new_stack, (Name c_name, a), a)
    end.

  (* mimics [Store] handler *)
  Definition init_global (m:M.memory) (ms:M.mem_stack) (a: dvalue) (v:dvalue)
    : err (M.memory * M.mem_stack) :=
    match a with
    | DVALUE_Addr (key, i) =>
      match M.lookup_logical key m with
      | Some (M.LBlock sz bytes cid) =>
        let bytes' := M.add_all_index (M.serialize_dvalue v) i bytes in
        let block' := M.LBlock sz bytes' cid in
        ret (M.add_logical key block' m, ms)
      | None => inl "stored to unallocated address"%string
      end
    | _ => inl ("Store got non-address dvalue: " ++ (to_string a))%string
    end.

End LLVM_Memory_Init.

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

Definition init_one_global
           (mem_state: (memory * local_env)%type)
           (g:toplevel_entity typ (list (LLVMAst.block typ)))
  := match g with
     | TLE_Global (mk_global (Name c_name) c_typ
                             true
                             (Some c_initiaizer)
                             (Some LINKAGE_Internal)
                             None None None true None
                             false None None) =>
       let '((m,ms), lenv) := mem_state in
       '(m,ms,g,a) <- alloc_global c_name c_typ m ms ;;
       mms <- (eval_const_exp >=> init_global m ms a) (c_typ, c_initiaizer)
       ;;
       ret ((mms,lenv), g)
     | _ => inl "Usupported global initialization"%string
     end.

(* TODO: move to Util *)
Definition assoc_right_to_left {A B C:Type}: (A*(B*C)) -> ((A*B)*C)
  := fun x => let '(a,(b,c)):=x in ((a,b),c).

(* TODO: move to Util *)
Definition assoc_left_to_right {A B C:Type}: ((A*B)*C) -> (A*(B*C))
  := fun x => let '((a,b),c) := x in (a,(b,c)).

Definition init_llvm_memory
           (p: FSHCOLProgram)
           (data: list binary64) : err LLVM_memory_state_cfg
  :=
    '(data,ginit) <- initIRGlobals data p.(globals) ;;

    let y := Anon 1%Z in
    let ytyp := getIRType (DSHPtr p.(o)) in
    let x := Anon 0%Z in
    let xtyp := getIRType (DSHPtr p.(i)) in

    let xyinit := global_YX p.(i) p.(o) data x xtyp y ytyp in

    (* Will return in order [globals ++ xy] *)
    let '(ms,(le,ge)) := llvm_empty_memory_state_partial in
    res <- init_with_data init_one_global no_chk (ms,le) (ginit ++ xyinit)%list ;;
    ret (assoc_left_to_right res).

(** Empty memories and environments should satisfy [memory_invariant] *)
Lemma memory_invariant_empty: memory_invariant [] helix_empty_memory llvm_empty_memory_state_partial.
Proof.
  unfold memory_invariant.
  break_let.
  left.
  auto.
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

Fact initIRGlobals_cons_head_uniq:
  ∀ (a : string * DSHType) (globals : list (string * DSHType))
    (data : list binary64) (res : list binary64 *
                                  list (toplevel_entity typ (list (LLVMAst.block typ)))),
    initIRGlobals data (a :: globals) ≡ inr res ->
    forall (j : nat) (n : string) (v : DSHType),
      (nth_error globals j ≡ Some (n, v) /\ n ≡ fst a) → False.
Proof.
  intros a globals data res H j n v C.
  unfold initIRGlobals, global_uniq_chk in H.
  cbn in H.
  repeat break_match_hyp; try inl_inr.
  unfold assert_false_to_err in Heqs.
  repeat break_match_hyp; try inl_inr.
  inl_inr_inv.
  subst.
  assert(globals_name_present (fst a) globals ≡ true).
  {
    clear -C.
    apply nth_to_globals_name_present.
    exists (n,v).
    exists j.
    apply C.
  }
  congruence.
Qed.

(* If [initIRGlobals] suceeds, the names of variables in [globals] were unique *)
Lemma initIRGlobals_names_unique {globals data res}:
  initIRGlobals data globals ≡ inr res → list_uniq fst globals.
Proof.
  revert res data.
  induction globals; intros.
  -
    cbn in H.
    inv H.
    apply list_uniq_nil.
  -
    apply list_uniq_cons.
    split.
    +
      cbn in H.
      break_match_hyp;[inl_inr|].
      break_match_hyp;[inl_inr|].
      break_let; subst.
      break_match_hyp;[inl_inr|].
      break_let; subst.
      inv H.
      eapply IHglobals.
      eauto.
    +
      (* [a] must not be present in [globals] *)
      unfold not.
      intros C.
      destruct C as (j & [n v] & C); cbn in C.
      eapply initIRGlobals_cons_head_uniq; eauto.
Qed.

(* Note: this could not be proben for arbitrary [chk] function,
   so we prove this only for [no_chk] *)
Lemma init_with_data_app
      {A: Type} (* input values *)
      {B: Type} (* output values we collect *)
      {C: Type} (* data *)
      (f: C -> A -> err (C*B))
      (c c': C) (* initial data *)
      (l0 l1: list A)
      (b: list B)
  :
    init_with_data f no_chk c (l0++l1) ≡ inr (c',b) ->
    ∃ c1 b1 b2,
      (init_with_data f no_chk c l0 ≡ inr (c1,b1) /\
       init_with_data f no_chk c1 l1 ≡ inr (c',b2) /\
       b ≡ (b1 ++ b2)%list).
Proof.
  revert l0 l1 c c' b.
  induction l0; intros.
  -
    cbn in H.
    repeat eexists.
    eauto.
  -
    cbn in H.
    repeat break_match_hyp; try inl_inr.
    inl_inr_inv.
    subst.
    apply IHl0 in Heqs0; clear IHl0.
    destruct Heqs0 as (c1 & b1 & b2 & H1 & H2 & E).
    repeat eexists; cbn.
    +
      rewrite Heqs.
      rewrite H1.
      eauto.
    +
      eauto.
    +
      cbn.
      f_equiv.
      auto.
Qed.

Lemma monadic_fold_left_err_app
         {A B : Type}
         (f : A -> B -> err A)
         (s0 s2 : A)
         (l0 l1 : list B):
  ListSetoid.monadic_fold_left f s0 (l0++l1) ≡ inr s2
  ->
  ∃ s1,
  ListSetoid.monadic_fold_left f s0 l0 ≡ inr s1 /\
  ListSetoid.monadic_fold_left f s1 l1 ≡ inr s2.
Proof.
  revert l0 l1 s0 s2 f.
  induction l0; intros.
  -
    cbn in *.
    eexists; auto.
  -
    cbn in H.
    break_match_hyp; [inl_inr|].
    eapply IHl0 in H.
    destruct H as [s1 [H1 H2]].
    eexists.
    split; [|eauto].
    cbn.
    rewrite Heqs.
    apply H1.
Qed.

(* TODO: This is general-purpose. Move elsewhere? *)
Lemma mapsto_alist_app_1st
      {K V: Type}
      (R : K → K → Prop)
      `{RD: RelDec.RelDec _ R}
      `{RDC: @RelDec.RelDec_Correct K R RD}
      (g g' : alist K V)
      (v : V)
      (n : K):
  mapsto_alist RD g n v ->
  mapsto_alist RD (g ++ g')%list n v.
Proof.
  revert v n.
  induction g; intros.
  -
    inversion H.
  -
    cbn.
    destruct a as [k0 v0].
    apply mapsto_alist_cons; [apply RDC|].
    destruct (RelDec.rel_dec n k0) eqn:K0.
    +
      right.
      split.
      *
        rewrite RelDec.rel_dec_correct in K0.
        apply K0.
      *
        apply mapsto_alist_cons in H ; [| auto].
        destruct H.
        destruct H.
        rewrite RelDec.rel_dec_correct in K0.
        congruence.
        apply H.
    +
      left.
      split.
      *
        apply IHg.
        apply mapsto_alist_cons in H ; [| auto].
        destruct H.
        apply H.
        destruct H.
        apply RelDec.rel_dec_correct in H.
        congruence.
      *
        apply RelDec.neg_rel_dec_correct in K0.
        apply K0.
Qed.


(* TODO: brute-force proof is slow. Could be optimized *)
Fact init_one_global_empty_local
      (a0 : toplevel_entity typ (list (LLVMAst.block typ)))
      (m0 : M.memory_stack)
      (p : M.memory * M.mem_stack)
      (l0 : local_env)
      (p1 : raw_id * dvalue):
  init_one_global (m0, [ ]) a0 ≡ inr (p, l0, p1) → l0 ≡ [ ].
Proof.
  intros H.
  unfold init_one_global in H.
  repeat (break_match_hyp; try inl_inr).
  cbn in *.
  subst.
  repeat (break_match_hyp; try inl_inr).
  inl_inr_inv.
  reflexivity.
  inl_inr_inv.
  reflexivity.
Qed.

Fact init_with_data_init_one_global_empty_local
     m g m' l g':
  init_with_data init_one_global no_chk (m, [ ]) g ≡ inr (m', l, g') -> l ≡ [].
Proof.
  revert g' l m m'.
  induction g; intros.
  -
    cbn in H.
    inv H.
    reflexivity.
  -
    cbn in H.
    break_match_hyp; try inl_inr.
    break_let; subst.
    break_match_hyp; try inl_inr.
    break_let; subst.
    inl_inr_inv.
    destruct p2.
    tuple_inversion.
    destruct p0.
    destruct p.

    unfold init_one_global in Heqs.
    repeat break_match_hyp; try inl_inr.
    subst.
    inv Heqs.
    break_match_hyp; try inl_inr.
    repeat break_let; subst.
    repeat break_match_hyp; try inl_inr.
    +
      repeat inl_inr_inv.
      subst.
      eapply IHg.
      eauto.
    +
      repeat inl_inr_inv.
      subst.
      eapply IHg.
      eauto.
Qed.

Lemma alist_find_nth_error_list_uniq
      (g : global_env)
      (x : nat)
      (n: raw_id)
      (v : dvalue)
      (U: list_uniq fst g):
  nth_error g x ≡ Some (n, v) →
  alist_find AstLib.eq_dec_raw_id n g ≡ Some v.
Proof.
  revert U.
  revert x v n.
  induction g; intros.
  -
    rewrite nth_error_nil in H.
    some_none.
  -
    cbn.
    break_let.
    break_if.
    +
      unfold RelDec.rel_dec, AstLib.eq_dec_raw_id in Heqb.
      cbn in Heqb.
      break_match; [| inversion Heqb].
      subst.
      destruct x.
      *
        cbn in H.
        some_inv.
        reflexivity.
      *
        cbn in H.
        clear - U H.
        exfalso.
        apply list_uniq_cons in U.
        destruct U.
        contradict H1.
        eexists.
        eexists.
        eauto.
    +
      destruct x.
      *
        clear IHg.
        cbn in *.
        some_inv.
        subst.
        clear - Heqb.
        unfold RelDec.rel_dec, AstLib.eq_dec_raw_id in Heqb.
        cbn in Heqb.
        break_if.
        inversion Heqb.
        contradict n0.
        reflexivity.
      *
        cbn in H.
        eapply IHg.
        eapply list_uniq_de_cons; eauto.
        eapply H.
Qed.

(** [memory_invariant] relation must holds after initialization of global variables *)
Lemma memory_invariant_after_init
      (p: FSHCOLProgram)
      (data: list binary64) :
  forall hmem σ lmem hdata,
                helix_intial_memory p data ≡ inr (hmem,hdata,σ) /\
                init_llvm_memory p data ≡ inr lmem ->
                memory_invariant σ hmem lmem.
Proof.
  (*

  This partial proof was further broken after
  eliminating [FSHValType] and replacing it with [DSHType].
  It needs to be repaired


  intros hmem σ lmem hdata [HI LI].
  unfold memory_invariant.
  repeat break_let; subst.
  unfold helix_intial_memory, init_llvm_memory in *.
  cbn in *.
  repeat break_match_hyp ; try inl_inr.
  subst.
  inv HI.
  cbn in *.
  repeat break_let; subst.

  right. (* as [σ] is never empty after init *)
  rename Heqp0 into HCY, m1 into ydata.
  rename Heqp2 into HCX, m2 into xdata.
  rename Heqs0 into HFSHG, l2 into fdata', e into σ.
  rename Heqs into HIRG, l0 into ldata', l1 into gdecls.
  remember (global_YX i o ldata' (Anon 0%Z) (TYPE_Array (Int64.intval i) TYPE_Double)
                      (Anon 1%Z) (TYPE_Array (Int64.intval o) TYPE_Double)) as xydecls eqn:HXY.
  rename l3 into fdata''.

  inv LI.
  unfold assoc_left_to_right in H0.
  destruct p1.
  destruct p.
  tuple_inversion.

  pose proof (init_with_data_app _ _ _ _ HFSHG)
    as ([m1 l1] & g1 & g2 & HG & HFXY & E).

  (* No local variables initialize in init stage *)
  assert(L1: l1 ≡ []) by eapply init_with_data_init_one_global_empty_local, HG; subst l1.
  assert(L2: l ≡ []) by eapply init_with_data_init_one_global_empty_local, HFXY; subst l.

  cbn in *.

  assert(∀ x y : nat,
            x < Datatypes.length
                  (σ ++
                     [DSHPtrVal (S (Datatypes.length globals)) o;
                      DSHPtrVal (Datatypes.length globals) i])
            ∧ y <
              Datatypes.length
                (σ ++
                   [DSHPtrVal (S (Datatypes.length globals)) o;
                    DSHPtrVal (Datatypes.length globals) i])
            → memory_invariant_map globals x ≡ memory_invariant_map globals y → x ≡ y) as INJ.
  {
    (* Injectivity proof *)
    rewrite app_length.
    erewrite <- initFSHGlobals_globals_sigma_len_eq with (globals0:=globals).
    2: eauto.
    simpl.
    apply memory_invariant_map_injectivity.
    eapply initIRGlobals_names_unique.
    eauto.
  }
  unshelve eexists.
  exists (memory_invariant_map globals).
  apply INJ.

  intros x v Hn.
  break_match.
  -
    (* [DSHnatVal] must end up in globals *)
    (* but currently nat constants are not implemented so we
       shortcut this branch *)
    exfalso.
    clear - Hn Heqs1.
    rename Heqs1 into F.

    apply ListUtil.nth_app in Hn.
    destruct Hn as [[Hn Hx] | [Hn Hx]].
    2:{
      remember (x - Datatypes.length σ)%nat as k.
      destruct k; inv Hn.
      destruct k; inv H0.
      rewrite Util.nth_error_nil in H1.
      inv H1.
    }
    clear Hx.
    revert F Hn.
    revert data fdata' m0 σ x.
    generalize helix_empty_memory as mem.

    intros mem data fdata' m0 σ x F Hn.
    contradict Hn.
    revert x n.
    revert F.
    revert σ m0 data fdata' mem.
    induction globals; intros.
    +
      cbn in F.
      inv F.
      rewrite Util.nth_error_nil.
      intros N.
      inversion N.
    +
      cbn in F.
      break_match_hyp; [inl_inr|].
      break_let; subst.
      break_match_hyp; [inl_inr|].
      break_let; subst.
      inv F.
      destruct a.
      destruct f; cbn in *.
      *
        inl_inr.
      *
        repeat break_let; subst.
        symmetry in Heqs.
        inl_inr_inv.
        subst.
        destruct x.
        cbn.
        intros C. inv C.
        cbn.
        eapply IHglobals, Heqs0.
      *
        repeat break_let; subst.
        symmetry in Heqs.
        inl_inr_inv.
        subst.
        destruct x.
        cbn.
        intros C. inv C.
        cbn.
        eapply IHglobals, Heqs0.
  -
    (* [DSHCTypeVal] must end up in globals as  a pointer *)

    apply ListUtil.nth_app in Hn.
    destruct Hn as [[Hn Hx] | [Hn Hx]].
    2:{
      (* X,Y are pointers, not CType, so [Hn] is [False] *)
      remember (x - Datatypes.length σ)%nat as k.
      destruct k; inv Hn.
      destruct k; inv H0.
      rewrite Util.nth_error_nil in H1.
      inv H1.
    }
    subst v.
    clear HFXY.

    assert(List.length gdecls ≡ List.length g1) as GL
        by eapply init_with_data_len, HG.

    assert(List.length globals ≡ List.length gdecls) as GG
        by eapply init_with_data_len, HIRG.

    rename Heqs1 into F.
    pose proof (initFSHGlobals_globals_sigma_len_eq globals F) as GSL.

    assert(exists gname gtype, nth_error globals x ≡ Some (gname, gtype)).
    {
      assert(L: x < Datatypes.length globals).
      {
        rewrite GSL.
        apply Hx.
      }
      pose proof (nth_error_succeeds globals L) as H.
      destruct H as ([gname gtype] & H).
      exists gname.
      exists gtype.
      apply H.
    }
    destruct H as (gname & gtype & NG).

    assert(exists gd,
              nth_error gdecls x ≡ Some (TLE_Global gd) /\
              g_exp gd ≡ Some (EXP_Double a) /\
              g_ident gd ≡ Name gname
          ) as (gd & XGD & VGD & NGD).
    {
      rewrite <- GSL, GG in Hx.
      clear - F HIRG Hn Hx NG F.
      unfold initFSHGlobals in *.
      pose proof (nth_error_succeeds gdecls Hx) as H.
      destruct H as (te & H).

      (* now prove [te] is [TLE_Global gd] *)
      revert F HIRG Hn NG Hx H.
      revert m0 fdata' σ data ldata' gdecls x.
      generalize helix_empty_memory as m0.
      induction globals; intros.
      -
        rewrite nth_error_nil in NG.
        some_none.
      -
        cbn in F.
        repeat break_match_hyp; try inl_inr.
        repeat inl_inr_inv.
        subst.
        destruct p0.

        destruct gdecls; [rewrite nth_error_nil in H; inversion H|].

        cbn in HIRG.
        repeat break_match_hyp; try inl_inr.
        repeat inl_inr_inv.
        subst.

        unfold initOneIRGlobal in Heqs2.
        repeat break_match_hyp; try inl_inr.
        +
          inl_inr_inv.
          subst.
          cbn in *.
          destruct x.
          *
            cbn in *.
            repeat some_inv.
            subst.
            break_let.
            tuple_inversion.
            inl_inr_inv.
            subst.
            eexists.
            eauto.
          *
            cbn in *.
            repeat some_inv.
            subst.
            break_let.
            tuple_inversion.
            inl_inr_inv.
            subst.
            eapply IHglobals; eauto.
            lia.
        +
          (* Array *)
          inl_inr_inv.
          subst.
          cbn in *.
          destruct x.
          *
            cbn in *.
            repeat some_inv.
            subst.
            break_let.
            inl_inr_inv.
          *
            cbn in *.
            break_let.
            inv Heqs.
            subst.
            eapply IHglobals; eauto.
            assert (LL: l0≡l1).
            {
              clear - Heqp Heqp0.
              unfold constMemBlock in Heqp.
              unfold constArray in Heqp0.
              break_let.
              tuple_inversion.
              tuple_inversion.
              reflexivity.
            }
            rewrite LL.
            eapply Heqs3.
            lia.
    }

    assert(exists ptr_llvm, nth_error g x ≡ Some (Name gname, (DVALUE_Addr ptr_llvm))).
    {
      assert (x < Datatypes.length g1) as L.
      {
        rewrite <- GL, <- GG, GSL.
        apply Hx.
      }
      subst g.
      rewrite app_nth_error1 in * by apply L.
      pose proof (nth_error_succeeds g1 L) as H.
      destruct H as ([did dv] & H).
      clear - HG H NGD XGD.
      revert x HG H XGD.
      generalize M.empty_memory_stack as m0.
      revert g1 did dv.
      induction gdecls; intros.
      -
        cbn in *.
        inv HG.
        rewrite nth_error_nil in H.
        some_none.
      -
        cbn in HG.
        repeat break_match_hyp; try inl_inr.
        repeat inl_inr_inv.
        subst.
        unfold init_one_global in Heqs.
        repeat break_match_hyp; try inl_inr.
        repeat inl_inr_inv.
        cbn in *.
        repeat break_match_hyp; try inl_inr.
        repeat inl_inr_inv.
        subst.
        +
          (* Double *)
          destruct x.
          *
            clear IHgdecls.
            cbn in *.
            some_inv.
            destruct p1.
            some_inv.
            unfold alloc_global in Heqs1.
            repeat break_match_hyp; try inl_inr.
            repeat inl_inr_inv.
            exists (M.next_logical_key m, 0%Z).
            subst.
            f_equiv.
            f_equiv.
            apply NGD.
          *
            cbn.
            eapply IHgdecls; eauto.
        +
          (* Array *)
          destruct x.
          *
            clear IHgdecls.
            cbn in *.
            some_inv.
            destruct p1.
            some_inv.
            unfold alloc_global in Heqs1.
            repeat break_match_hyp; try inl_inr.
            repeat inl_inr_inv.
            exists (M.next_logical_key m, 0%Z).
            subst.
            f_equiv.
            f_equiv.
            cbn in *.
            tuple_inversion.
            apply NGD.
            tuple_inversion.
            eauto.
          *
            cbn.
            destruct p0.
            inl_inr_inv.
            subst.
            eapply IHgdecls; eauto.
    }

    destruct H as (ptr_llvm & NGDECL).
    exists ptr_llvm.

    split.
    right.
    split; [trivial|cbn].
    +
      (* Deal with X,Y first *)
      unfold memory_invariant_map.
      repeat break_if; bool_to_nat; try lia.

      (* X,Y eliminated, [x] somewhere in globals *)
      break_match_goal; try some_none.
      some_inv. subst p.

      (* unify lengths *)
      remember (Datatypes.length σ) as l eqn:SL; symmetry in SL.
      clear Heqb Heqb0.
      rename m0 into fm0.

      (* we know, [gname] is in [gdecls] and not in [xydecls] *)
      clear HCX HCY xdata ydata hdata.

      assert(list_uniq fst g) as GU.
      {
        pose proof (initIRGlobals_names_unique HIRG) as GLU.
        admit.
      }

      eapply alist_find_nth_error_list_uniq; eauto.
    +
      eexists.
      split.
      *
        admit.
      *
        eexists.
        clear - NGDECL HFSHG Hn.
        admit.
  -
    (* [DSHPtrVal] must end up in memory *)
    intros bk_helix HMH.
    eexists.
    eexists.
    admit.
   *)
Admitted.

(* with init step  *)
Lemma compiler_correct_aux:
  forall (p:FSHCOLProgram)
    (data:list binary64)
    (pll: toplevel_entities typ (list (LLVMAst.block typ))),
    compile_w_main p data ≡ inr pll ->
    eutt (bisim_full []) (semantics_FSHCOL p data) (semantics_llvm pll).
Proof.
Admitted.

(** Relation bewteen the final states of evaluation and execution
    of DHCOL program.

    At this stage we do not care about memory or environemnts, and
    just compare return value of [main] function in LLVM with
    evaulation results of DSHCOL.
 *)
Definition bisim_final: Type_R_full :=
  fun σ '(_, h_result) '(_,(_,(_,llvm_result))) =>
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

Lemma bisim_partial_memory_subrelation: forall σ helix_state llvm_state,
    let '(mem_helix, _) := helix_state in
    let '(mem_llvm, (ρ, (g, _))) := llvm_state in
    bisim_partial σ helix_state llvm_state -> memory_invariant σ mem_helix (mem_llvm, (ρ, g)).
Proof.
  intros σ helix_state llvm_state.
  repeat break_let.
  subst.
  intros H.
  auto.
Qed.

Lemma bisim_full_partial_subrelation: forall σ helix_state llvm_state,
    let '(mem_helix, v_helix) := helix_state in
    let '(m, ((ρ,_), (g, v))) := llvm_state in
    bisim_full σ helix_state llvm_state -> bisim_partial σ (mem_helix, tt) (mk_LLVM_sub_state_partial_from_mem (inr v) (m, (ρ, g))).
Proof.
  intros σ helix_state llvm_state.
  repeat break_let.
  subst.
  intros H.
  unfold mk_LLVM_sub_state_partial_from_mem.
  auto.
Qed.

(* Top-level compiler correctness lemma  *)
Theorem compiler_correct:
  forall (p:FSHCOLProgram)
    (data:list binary64)
    (pll: toplevel_entities typ (list (LLVMAst.block typ))),
    compile_w_main p data ≡ inr pll ->
    eutt (bisim_final []) (semantics_FSHCOL p data) (semantics_llvm pll).
Proof.
  intros p data pll H.
  (* This no longer follows from [compiler_correct_aux]. It will
     at pen-ultimate step when the [main] does [return] on a memory
     block.

       eapply eqit_mon.
       3:apply bisim_full_final_subrelation.
       3:eapply compiler_correct_aux.
       tauto.
       tauto.
       tauto.
   *)
Admitted.
