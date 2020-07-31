(* YZ: Can we delete this file or is there anything that should be saved? *)

(*
(* Require Import LibHyps.LibHyps. *)
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
Require Import Helix.LLVMGen.Correctness_Invariants.
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
Require Import Vellvm.Denotation_Theory.

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


Section MemCopy.

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

  Opaque denote_bks.

  Definition Rel_memV (T S : Type) :=
    memoryV * (local_env * (global_env * S)) -> memoryV * T -> Prop.

  Definition lift_Rel_memV (T S : Type) (R : T -> S -> Prop) : Rel_memV T S :=
    fun '(_, (_, (_, s))) '(_, t) => R t s.

  Lemma interp_cfg_to_L3_memory_intrinsic :
    ∀ (defs : intrinsic_definitions) (m : memoryV) (τ : dtyp) (g : global_env)
      (l : local_env)
      (fn : string) (args : list dvalue) (df : semantic_function)
      (res : dvalue),
    assoc string_dec fn (defs_assoc defs) ≡ None
    → df args ≡ inr res
    → eutt (lift_Rel_memV (@Logic.eq dvalue)) (interp_cfg_to_L3 defs (trigger (Intrinsic τ fn args)) g l m) (handle_intrinsic ((Intrinsic τ fn args)) m).
  Proof.
    intros.
  Admitted.

    Lemma interp_cfg_to_L3_memory_intrinsic' :
      ∀ (defs: intrinsic_definitions) (m : memoryV) (τ : typ) (dτ : dtyp)
        (g : global_env) (l : local_env)
        (val1 val2 : uvalue) ptr1 ptr2 sz t,
       TYPE_Pointer (TYPE_Array sz TYPE_Double) ≡ TYPE_Pointer τ ->
        MInt64asNT.from_Z sz ≡ inr t ->
       read m ptr1 dτ ≡ inr val1 ->
       read m ptr2 dτ ≡ inr val2 ->
      interp_cfg_to_L3 defs (trigger (Intrinsic DTYPE_Void
                  "llvm.memcpy.p0i8.p0i8.i32"
                   [DVALUE_Addr ptr1; DVALUE_Addr ptr2;
                   DVALUE_I32 (DynamicValues.Int32.repr (Int64.intval t * 8));
                   DVALUE_I32 (DynamicValues.Int32.repr PtrAlignment);
                   DVALUE_I1 (DynamicValues.Int1.repr 0)])) g l m ≈
                       Ret (m, (l, (g, DVALUE_Addr ptr2))) /\
      read m ptr2 dτ ≡ inr val1.
    Proof.
      intros defs m τ dτ g l val1 val2 ptr1 ptr2 sz t.
      intros Pointer_TYPE SIZE read_ptr1 read_ptr2.
    Admitted.

    Lemma interp_memory_intrinsic_memcpy :
      ∀ (m : memoryV) (a1 a2 : Addr.addr) (i : nat)
        (val1 val2 : uvalue) (dτ : dtyp),
      get_array_cell m a1 i dτ ≡ inr val1 ->
      get_array_cell m a2 i dτ ≡ inr val2 ->
      exists m',
       interp_memory (trigger (Intrinsic DTYPE_Void
                  "llvm.memcpy.p0i8.p0i8.i32"
                   [DVALUE_Addr a1; DVALUE_Addr a2;
                   DVALUE_I64 (Int64.repr 0);
                   DVALUE_I64 (Int64.repr (Z.of_nat i))])) m ≈
                       Ret (m', DVALUE_None) /\
        read m' a2 dτ ≡ inr val1.
    Proof.
      intros m a1 a2 i val1 val2 dτ MEM_ptr1 MEM_ptr2.
      pose proof get_array_succeeds_allocated _ _ _ _ MEM_ptr1 as ALLOC_ptr1.
      pose proof get_array_succeeds_allocated _ _ _ _ MEM_ptr2 as ALLOC_ptr2.
      pose proof read_array_exists m
           (Z.of_nat i) dτ i a1 ALLOC_ptr1 as RARRAY_ptr1.
      pose proof read_array_exists m
           (Z.of_nat i) dτ i a2 ALLOC_ptr2 as RARRAY_ptr2.
      destruct RARRAY_ptr1 as (ptr1 & GEP1 & READ1).
      destruct RARRAY_ptr2 as (ptr2 & GEP2 & READ2).
      - Set Printing Implicit. setoid_rewrite interp_memory_trigger. cbn.
        unfold resum, ReSum_id, id_, Id_IFun.
        (* IY: Something goes wrong here, memory isn't interpreted correctly. *)
        setoid_rewrite bind_trigger.
        admit.
    Admitted.

End MemCopy.
*)
