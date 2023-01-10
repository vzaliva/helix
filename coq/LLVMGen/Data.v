Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.FSigmaHCOL.Int64asNT.
Require Import Helix.FSigmaHCOL.Float64asCT.
Require Import Helix.Util.ErrorSetoid.
Require Import Helix.Util.ListUtil.
Require Import Helix.Tactics.HelixTactics.

Require Import Vellvm.Syntax.LLVMAst.

Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

Require Import Coq.Numbers.BinNums. (* for Z scope *)
Require Import Coq.ZArith.BinInt.

Require Import ExtLib.Structures.Monads.

Import ListNotations.
Import MonadNotation.
Open Scope monad_scope.

Import FHCOL.

Definition genFloatV (fv:binary64) : (exp typ) :=  EXP_Double fv.

Section RandomDataPool.

  Definition rotateN {A : Type} (n : nat) (l : list A) : list A :=
    Nat.iter n
             (fun l => match l with
                    | [] => []
                    | (x::xs) => xs ++ [x]
                    end)
             l.

  Lemma nat_iter_S 
        {A : Type}
        (n : nat)
        (f : A -> A)
        (a : A)
    :
      Nat.iter (S n) f a = f (Nat.iter n f a).
  Proof.
    reflexivity.
  Qed.

  Lemma nat_iter_add
        {A : Type}
        (n1 n2 : nat)
        (f : A -> A)
        (a : A)
    :
      Nat.iter n1 f (Nat.iter n2 f a) = Nat.iter (n1 + n2) f a.
  Proof.
    induction n1.
    - reflexivity.
    - cbn [Nat.add].
      rewrite !nat_iter_S.
      congruence.
  Qed.

  Lemma rotateN_add
        {A : Type}
        (n1 n2 : nat)
        (l : list A)
    :
      rotateN n1 (rotateN n2 l) = rotateN (n1 + n2) l.
  Proof.
    apply nat_iter_add.
  Qed.

  Definition rotate {A:Type} (default:A) (lst:list (A)): (A*(list A))
    := match lst with
       | [] => (default,[])
       | (x::xs) => (x,app xs [x])
       end.

  Lemma rotate_data
        {A : Type}
        (d x : A)
        (l l' : list A)
    :
      rotate d l = (x, l') ->
      l' = rotateN 1 l.
  Proof.
    destruct l; cbn; congruence.
  Qed.

  Fixpoint constList
           (len: nat)
           (data:list binary64) :
    ((list binary64) * (list binary64))
    :=
      match len with
      | O => (data,[])
      | S len' => let '(x, data') := rotate MFloat64asCT.CTypeZero data in
                 let '(data'',res) := constList len' data' in
                 (data'', x :: res)
      end.

  Lemma constList_data
        (n : nat)
        (data data' l : list binary64)
    :
      constList n data = (data', l) ->
      data' = rotateN n data.
  Proof.
    revert data data' l.
    induction n.
    - cbn; congruence.
    - intros data data' l CL.
      cbn [constList] in CL.
      repeat break_let.
      apply rotate_data in Heqp; subst.
      apply IHn in Heqp0; subst.
      rewrite rotateN_add, PeanoNat.Nat.add_1_r in CL.
      congruence.
  Qed.

  Definition constArray
             (len: nat)
             (data:list binary64)
    : ((list binary64)*(list (texp typ)))
    :=  let (data, l) := constList len data in
        (data,List.map (fun x => (TYPE_Double, genFloatV x)) l).

  Lemma constArray_data
        (n : nat)
        (data data' : list binary64)
        (l : list (texp typ))
    :
      constArray n data = (data', l) ->
      data' = rotateN n data.
  Proof.
    intros CA.
    unfold constArray in *.
    break_let.
    apply constList_data in Heqp.
    congruence.
  Qed.

  Definition constMemBlock
             (len: nat)
             (data:list binary64)
    : ((list binary64)*mem_block)
    := let (data, l) := constList len data in
       (data, mem_block_of_list l).

  Lemma constMemBlock_data
        (n : nat)
        (data data' : list binary64)
        (mb : mem_block)
    :
      constMemBlock n data = (data', mb) ->
      data' = rotateN n data.
  Proof.
    intros CMB.
    unfold constMemBlock in *.
    break_let.
    apply constList_data in Heqp.
    congruence.
  Qed.

  Local Fixpoint intNFromData
        (n : nat)
        (data : list binary64)
        (i : Int64.int)
        {struct n}
    : Int64.int * (list binary64) :=
    match n with
    | O => (Int64.zero, data)
    | S m =>
      let '(f,data) := rotate MFloat64asCT.CTypeZero data in
      let si := Int64.add i Int64.one in
      match f with
      | B754_zero _ => intNFromData m data si
      | _ =>
        let '(x,data) := intNFromData m data si in
        (Int64.add (Int64.repr (ZArith.Zpower.two_power_nat m)) x, data)
      end
    end.

  Local Lemma intNFromData_data
        (n : nat)
        (data data' : list binary64)
        (i i' : Int64.int)
    : 
      intNFromData n data i = (i', data') ->
      data' = rotateN n data.
  Proof.
    revert data data' i i'.
    induction n.
    - cbn in *; congruence.
    -
      intros * I.
      cbn [intNFromData] in *.
      destruct rotate eqn:RD in I;
        apply rotate_data in RD; subst.
      destruct b.
      apply IHn in I.
      2-4: repeat break_let.
      2-4: apply IHn in Heqp; subst.
      all: rewrite rotateN_add, PeanoNat.Nat.add_1_r in I; congruence.
  Qed.
  
  (* Creates 64 bit integer from floating pointer data list by interpreting
     first 64 floating point values as bit values. *)
  Definition int64FromData (data : list binary64) : Int64.int * (list binary64) :=
    intNFromData 64 data Int64.zero.

  Lemma int64FromData_data
        (data data' : list binary64)
        (i : Int64.int)
    :
      int64FromData data = (i, data') ->
      data' = rotateN 64 data.
  Proof.
    apply intNFromData_data.
  Qed.

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
      {f: C -> A -> err (C*B)}
      {chk: A -> list A -> err unit} (* check function *)
      {c c': C} (* initial data *)
      {l: list A}
      {bs: list B}
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
           (gp: string*DSHType) : err (memory * list binary64 * (DSHVal*bool))
  :=
    let (_,gt) := gp in
    let '(mem,data) := st in
    match gt with
    | DSHnat =>
      let '(xi, data) := int64FromData data in
      ret (mem, data, (DSHnatVal xi,false))
    | DSHCType =>
      let '(x, data) := rotate MFloat64asCT.CTypeZero data in
      ret (mem, data, (DSHCTypeVal x,false))
    | DSHPtr n =>
      let (data,mb) := constMemBlock (MInt64asNT.to_nat n) data in
      let k := memory_next_key mem in
      let mem := memory_set mem k mb in
      let p := (DSHPtrVal k n,false) in
      ret (mem, data, p)
    end.

Definition initFSHGlobals
         (data: list binary64)
         (mem: memory)
         (globals: list (string * DSHType))
: err (memory * list binary64 * evalContext)
  := init_with_data initOneFSHGlobal no_chk (mem, data) globals.

Definition helix_empty_memory := memory_empty.

Definition helix_initial_memory
           (p: FSHCOLProgram)
           (data: list binary64)
  : err (FHCOL.memory * list binary64 * evalContext)
  := match p with
     | mkFSHCOLProgram i o name globals op =>
       '(mem, data, globals_σ) <- initFSHGlobals data helix_empty_memory globals ;;
       let '(data, y) := constMemBlock (MInt64asNT.to_nat o) data in
       let '(data, x) := constMemBlock (MInt64asNT.to_nat i) data in
       (* over-estimating id, as some globals may not alocate memory (e.g. scalars) *)
       let X_nat : nat := length globals  in
       let Y_nat : nat := S (length globals) in
       let mem := memory_set mem Y_nat y in
       let mem := memory_set mem X_nat x in
       let σ := globals_σ ++ [(DSHPtrVal Y_nat o,false); (DSHPtrVal X_nat i,false)] in
       ret (mem, data, σ)
     end.

Definition mem_to_list (msg:string) (n:nat) (mb:mem_block) : err (list binary64) :=
  ListSetoid.monadic_Lbuild n (fun j _ => trywith msg (mem_lookup j mb)).
