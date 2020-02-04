Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.Util.ErrorSetoid.

Require Import Vellvm.LLVMAst.

Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

Require Import Coq.Numbers.BinNums. (* for Z scope *)
Require Import Coq.ZArith.BinInt.

Require Import ExtLib.Structures.Monads.

Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.

Import MDSHCOLOnFloat64.

Definition genFloatV (fv:binary64) : (exp typ) :=  EXP_Double fv.

Section RandomDataPool.

  Definition rotate {A:Type} (default:A) (lst:list (A)): (A*(list A))
    := match lst with
       | [] => (default,[])
       | (x::xs) => (x,app xs [x])
       end.

  Fixpoint constList
           (len: nat)
           (data:list binary64) :
    ((list binary64) * (list binary64))
    :=
      match len with
      | O => (data,[])
      | S len' => let '(x, data') := rotate Float64Zero data in
                 let '(data'',res) := constList len' data' in
                 (data'', x :: res)
      end.

  Definition constArray
             (len: nat)
             (data:list binary64)
    : ((list binary64)*(list (texp typ)))
    :=  let (data, l) := constList len data in
        (data,List.map (fun x => (TYPE_Double, genFloatV x)) l).

  Definition constMemBlock
             (len: nat)
             (data:list binary64)
    : ((list binary64)*mem_block)
    := let (data, l) := constList len data in
       (data, mem_block_of_list l).

End RandomDataPool.

(* Type of values. Used for global variables *)
Inductive FSHValType :=
| FSHnatValType       :FSHValType
| FSHFloatValType     :FSHValType
| FSHvecValType (n:nat) :FSHValType.

Record FSHCOLProgram :=
  mkFSHCOLProgram
    {
      i: nat;
      o: nat;
      name: string;
      globals: list (string * FSHValType) ;
      op: DSHOperator;
    }.


Fixpoint initFSHGlobals
         (data: list binary64)
         (mem: memory)
         (globals: list (string * FSHValType))
: err (memory * list binary64 * evalContext)
:=
  match globals with
  | [] => ret (mem, data, [])
  | (_,gt)::gs => match gt with
                | FSHnatValType => raise "Unsupported global type: nat"
                | FSHFloatValType =>
                  '(mem,data,σ) <- initFSHGlobals data mem gs ;;
                  let '(x, data) := rotate Float64Zero data in
                  ret (mem, data, (DSHCTypeVal x)::σ)
                | FSHvecValType n =>
                  '(mem,data,σ) <- initFSHGlobals data mem gs ;;
                  let (data,mb) := constMemBlock n data in
                  let k := memory_next_key mem in
                  let mem := memory_set mem k mb in
                  let p := DSHPtrVal k n in
                  ret (mem, data, (p::σ))
                end
  end.



Definition helix_empty_memory := memory_empty.

Definition helix_intial_memory
           (p: FSHCOLProgram)
           (data: list binary64)
  : err (MDSHCOLOnFloat64.memory * list binary64 * evalContext)
  := match p with
     | mkFSHCOLProgram i o name globals op =>
       '(mem, data, σ) <- initFSHGlobals data helix_empty_memory globals ;;
       let '(data, x) := constMemBlock i data in
       let '(data, y) := constMemBlock o data in
       let X_mem_block_id : mem_block_id := length globals  in
       let Y_mem_block_id : mem_block_id := S (length globals) in
       let mem := memory_set mem X_mem_block_id x in
       let mem := memory_set mem Y_mem_block_id y in
       let σ := List.app σ [DSHPtrVal Y_mem_block_id o; DSHPtrVal X_mem_block_id i] in
       ret (mem, data, σ)
     end.
