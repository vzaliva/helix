Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.BinNums. (* for Z scope *)
Require Import Coq.ZArith.BinInt.

Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLITree.
Require Import Helix.LLVMGen.Compiler.
Require Import Helix.LLVMGen.Externals.
Require Import Helix.Util.ErrorSetoid.

Require Import ExtLib.Structures.Monads.

Require Import Vellvm.Numeric.Fappli_IEEE_extra.
Require Import Vellvm.LLVMEvents.
Require Import Vellvm.Denotation.
Require Import Vellvm.Handlers.Memory.
Require Import Vellvm.TopLevel.
Require Import Vellvm.LLVMAst.
Require Import Vellvm.CFG.
Require Import Vellvm.TopLevelRefinements.
Require Import Vellvm.LLVMEvents.

Require Import ITree.ITree.
Require Import ITree.Eq.Eq.
Require Import ITree.Basics.Basics.

Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.misc.decision.

Set Implicit Arguments.
Set Strict Implicit.

Import MDSHCOLOnFloat64.

Definition model_llvm' := model_to_L3 helix_intrinsics.

Definition E: Type -> Type := (StaticFailE +' DynamicFailE) +' (IO.CallE +' IO.PickE +' UBE +' DebugE +' FailureE).

Definition semantics_llvm_mcfg p: itree E _ := translate (@subevent _ E _) (model_llvm' p).

Definition semantics_llvm (prog: list (toplevel_entity typ (list (LLVMAst.block typ)))) :=
  let scfg := Vellvm.AstLib.modul_of_toplevel_entities _ prog in

  match CFG.mcfg_of_modul _ scfg with
  | Some ucfg =>
    let mcfg := TopLevelEnv.normalize_types ucfg in

    semantics_llvm_mcfg mcfg

  | None => raise "Ill-formed program: mcfg_of_modul failed."
  end.

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

Definition mem_to_list (msg:string) (n:nat) (mb:mem_block) : err (list binary64) :=
  ListSetoid.monadic_Lbuild n (fun j _ => trywith msg (mem_lookup j mb)).

Definition denote_FSHCOL (p:FSHCOLProgram) (data:list binary64)
  : itree Event (list binary64) :=
  '(data, σ) <- denote_initFSHGlobals data p.(globals) ;;
  xindex <- trigger (MemAlloc p.(i));;
  yindex <- trigger (MemAlloc p.(o));;
  let '(data, x) := constMemBlock p.(i) data in
  trigger (MemSet xindex x);;

  let σ := List.app σ [DSHPtrVal yindex; DSHPtrVal xindex] in
  denoteDSHOperator σ p.(op);;
  bk <- trigger (MemLU "denote_FSHCOL" yindex);;
  lift_Derr (mem_to_list "Invalid output memory block" p.(o) bk).

Definition semantics_FSHCOL p data: itree E (memory * list binary64) :=
  translate (@subevent _ E _) (interp_Mem (denote_FSHCOL p data) memory_empty).

Theorem compiler_correct:
  exists RR,
  forall (p:FSHCOLProgram) data pll,
    compile p data ≡ inr pll ->
    eutt RR (semantics_FSHCOL p data) (semantics_llvm pll).
Proof.
Admitted.
