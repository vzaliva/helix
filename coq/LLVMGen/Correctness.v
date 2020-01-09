Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.BinNums. (* for Z scope *)
Require Import Coq.ZArith.BinInt.

Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLITree.
Require Import Helix.LLVMGen.Compiler.
Require Import Helix.LLVMGen.Externals.
Require Import Helix.Util.ErrorSetoid.

Require Import Vellvm.Numeric.Fappli_IEEE_extra.
Require Import Vellvm.LLVMEvents.
Require Import Vellvm.Denotation.
Require Import Vellvm.Handlers.Memory.
Require Import Vellvm.TopLevel.
Require Import Vellvm.LLVMAst.
Require Import Vellvm.CFG.
Require Import Vellvm.TopLevelRefinements.

Require Import ITree.ITree.
Require Import ITree.Basics.Basics.

Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

Require Import ExtLib.Structures.Monads.


Set Implicit Arguments.
Set Strict Implicit.

Import MDSHCOLOnFloat64.

Definition model_llvm' := model_to_L3 helix_intrinsics.

Definition E: Type -> Type := (StaticFailE +' DynamicFailE) +' (IO.CallE +' IO.PickE +' UBE +' DebugE +' FailureE).

Definition model_llvm p: itree E _ := translate (@subevent _ E _) (model_llvm' p).

Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

Fixpoint denote_initFSHGlobals
         (data: list binary64)
         (globals: list (string * FSHValType))
  : itree Event (list binary64 * evalContext) :=
    match globals with
    | [] => ret (data, [])
    | (_,gt)::gs =>
      match gt with
      | FSHnatValType => Sfail "Unsupported global type: nat"
      | FSHFloatValType =>
        '(data,σ) <- denote_initFSHGlobals data gs ;;
         let '(x, data) := rotate Float64Zero data in
         ret (data, (DSHCTypeVal x)::σ)
      | FSHvecValType n =>
        '(data,σ) <- denote_initFSHGlobals data gs ;;
         let (data,mb) := constMemBlock n data in
         k <- trigger (MemAlloc n);;
         trigger (MemSet k mb);;
         let p := DSHPtrVal k in
         ret (data, (p::σ))
      end
    end.

(* Definition denote_FSHCOL (t:FSHCOLProgram) (data:list binary64) *)
(*   : itree (StaticFailE +' DynamicFailE) (list binary64) := *)
(*   xindex <- trigger (MemAlloc xindex mem_empty);; *)
(*   yindex <- trigger (MemAlloc yindex mem_empty);; *)
(*   '(data, σ) <- initFSHGlobals data mem globals ;; *)
(*   let '(data, x) := constMemBlock i data in *)
(*   let mem := memory_set mem xindex x in *)
(*   let σ := List.app σ [DSHPtrVal yindex; DSHPtrVal xindex] in *)
(*   match evalDSHOperator σ op mem (estimateFuel op) with *)
(*   | Some (inr mem) => *)
(*     yb <- trywith "No output memory block" (memory_lookup mem yindex) ;; *)
(*        mem_to_list "Invalid output memory block" o yb *)
(*   | Some (inl msg) => inl msg *)
(*   | None => raise "evalDSHOperator returns None" *)
(*   end. *)



(* Theorem compiler_correct: *)
(*   forall (i o: nat) *)
(*     (globals: list (string*FSHValType)) *)
(*     (globals_extern: bool) *)
(*     (fshcol: DSHOperator) *)
(*     (funname: string) *)
(*     p σ mem, *)
(*   exists RR, *)
(*     LLVMGen i o globals globals_extern fshcol funname ≡ inr p -> *)
(*     eutt RR (denoteDSHOperator σ fshcol mem) (model_user ). *)

