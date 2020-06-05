Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.FSigmaHCOL.Int64asNT.
Require Import Helix.FSigmaHCOL.Float64asCT.
Require Import Helix.Util.ErrorSetoid.
Require Import Helix.Util.ListUtil.
Require Import Helix.Tactics.HelixTactics.

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

Record FSHCOLProgram :=
  mkFSHCOLProgram
    {
      i: Int64.int;
      o: Int64.int;
      name: string;
      globals: list (string * DSHType) ;
      op: DSHOperator;
    }.


(*
   This is a special variant of monadic fold,
   which explicitly build a list.

   It is written to generalize 2 variable initialization
   functions: [initFSHGlobals], [initIRGlobals], and
   [init_llvm_memory].
 *)
Fixpoint init_with_data
         {m: Type -> Type}
         `{Monad m}
         {A: Type} (* input values *)
         {B: Type} (* output values we collect *)
         {C: Type} (* data *)
         (f: C -> A -> m (C*B)%type)
         (chk: A -> list A -> m unit) (* check function *)
         (c: C) (* initial data *)
         (l: list A)
  : m (C * list B)%type
  :=  match l with
      | nil => ret (c,[])
      | cons x xs =>
        _ <- chk x xs ;;
        '(c,b) <- f c x ;;
        '(c,bs) <- init_with_data f chk c xs ;;
        ret (c, b::bs)
      end.

(* Check for [init_with_data] which always succeeds *)
Definition no_chk {A:Type}: A -> list A -> err unit
  := fun _ _ => ret tt.

Lemma init_with_data_len
      {A: Type} (* input values *)
      {B: Type} (* output values we collect *)
      {C: Type} (* data *)
      (f: C -> A -> err (C*B))
      (chk: A -> list A -> err unit) (* check function *)
      (c c': C) (* initial data *)
      (l: list A)
      (bs: list B)
  :
    init_with_data f chk c l = inr (c', bs) ->
    List.length l = List.length bs.
Proof.
  revert bs c c'.
  induction l; intros.
  -
    cbn in H.
    inversion H.
    reflexivity.
  -
    cbn in H.
    repeat break_match_hyp; try inl_inr.
    inl_inr_inv.
    subst.
    apply IHl in Heqs1.
    cbn.
    auto.
Qed.

Definition initOneFSHGlobal
           (st: memory * list binary64)
           (gp: string*DSHType) : err (memory * list binary64 * DSHVal)
  :=
    let (_,gt) := gp in
    let '(mem,data) := st in
    match gt with
    | DSHnat => raise "Unsupported global type: nat"
    | DSHCType =>
      let '(x, data) := rotate Float64Zero data in
      ret (mem, data, DSHCTypeVal x)
    | DSHPtr n =>
      let (data,mb) := constMemBlock (MInt64asNT.to_nat n) data in
      let k := memory_next_key mem in
      let mem := memory_set mem k mb in
      let p := DSHPtrVal k n in
      ret (mem, data, p)
    end.

Definition initFSHGlobals
         (data: list binary64)
         (mem: memory)
         (globals: list (string * DSHType))
: err (memory * list binary64 * evalContext)
  := init_with_data initOneFSHGlobal no_chk (mem, data) globals.

Definition helix_empty_memory := memory_empty.

Definition helix_intial_memory
           (p: FSHCOLProgram)
           (data: list binary64)
  : err (MDSHCOLOnFloat64.memory * list binary64 * evalContext)
  := match p with
     | mkFSHCOLProgram i o name globals op =>
       '(mem, data, globals_σ) <- initFSHGlobals data helix_empty_memory globals ;;
       let '(data, y) := constMemBlock (MInt64asNT.to_nat o) data in
       let '(data, x) := constMemBlock (MInt64asNT.to_nat i) data in
       (* over-estimating id, as some globals may not alocate memory (e.g. scalars) *)
       let X_mem_block_id : mem_block_id := length globals  in
       let Y_mem_block_id : mem_block_id := S (length globals) in
       let mem := memory_set mem Y_mem_block_id y in
       let mem := memory_set mem X_mem_block_id x in
       let σ := globals_σ ++ [DSHPtrVal Y_mem_block_id o; DSHPtrVal X_mem_block_id i] in
       ret (mem, data, σ)
     end.

Definition mem_to_list (msg:string) (n:nat) (mb:mem_block) : err (list binary64) :=
  ListSetoid.monadic_Lbuild n (fun j _ => trywith msg (mem_lookup j mb)).
