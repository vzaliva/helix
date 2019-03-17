(*
  Simple memory model. Inspired by Vellvm

  Memory cells all have the same type: `CarrierA`.
 *)

Require Import Coq.FSets.FMapAVL.
Require Export Coq.FSets.FMapInterface.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Arith.Peano_dec.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Require Import Helix.HCOL.CarrierType.

Import MonadNotation.
Open Scope monad_scope.

Definition addr := (nat * nat) % type.
Definition null := (0, 0).

Open Scope nat_scope.

Lemma addr_dec : forall (a b : addr), {a = b} + {a <> b}.
Proof.
  intros [a1 a2] [b1 b2].
  destruct (eq_nat_dec a1 b1);
    destruct (eq_nat_dec a2 b2); subst.
  - left; reflexivity.
  - right. intros H. inversion H; subst. apply n. reflexivity.
  - right. intros H. inversion H; subst. apply n. reflexivity.
  - right. intros H. inversion H; subst. apply n. reflexivity.
Qed.

Module NM := FMapAVL.Make(Nat_as_OT).
Definition NatMap := NM.t.

Module Import NF:=WFacts_fun(Nat_as_OT)(NM).

Definition mem_add k (v:CarrierA) := NM.add k v.
Definition mem_delete k (m:NatMap CarrierA) := NM.remove k m.
Definition mem_member k (m:NatMap CarrierA) := NM.mem k m.
Definition mem_in     k (m:NatMap CarrierA) := NM.In k m.
Definition mem_lookup k (m:NatMap CarrierA) := NM.find k m.
Definition mem_empty := @NM.empty CarrierA.
Definition mem_mapsto k (v:CarrierA) (m:NatMap CarrierA) := @NM.MapsTo CarrierA k v m.

Definition mem_block := NatMap CarrierA.

Definition mem_keys (m:NatMap CarrierA): list nat
  := List.map fst (NM.elements m).

(* Copy of template-coq `monad_fold_left` but using ExtLib
   TODO: move to Util
*)
Fixpoint monadic_fold_left
         {A B:Type}
         {m : Type -> Type}
         {M : Monad m}
         (f : A -> B -> m A) (l : list B) (x : A)
  : m A
  := match l with
     | nil => ret x
     | y :: l => x' <- f x y ;;
                  monadic_fold_left f l x'
     end.

Fixpoint monadic_fold_left_rev
         {A B:Type}
         {m : Type -> Type}
         {M : Monad m}
         (f : A -> B -> m A) (l : list B) (x : A)
  : m A
  := match l with
     | nil => ret x
     | y :: l => x' <- monadic_fold_left_rev f l x ;; f x' y
     end.

Definition mem_try_add (m:mem_block) '(k,v) :=
  match NF.In_dec m k with
  | left _ => None
  | right _ => Some (NM.add k v m)
  end.

(* merge two memory blocks. Return `None` if there is an overlap *)
Definition mem_merge (a b: mem_block) : option mem_block
  := monadic_fold_left_rev mem_try_add
       (NM.elements a) b.

(* merge two memory blocks in (0..n-1) using given operation to combine values *)
Definition mem_merge_with (f: CarrierA -> CarrierA -> CarrierA) (a b: mem_block)
  : mem_block
  :=
    NM.fold (fun k v m =>
               match mem_lookup k m with
               | None => NM.add k v m
               | Some x => NM.add k (f v x) m
               end
            ) a b.

(* block of memory with indices (0..n-1) set to `v` *)
Fixpoint mem_const_block (n:nat) (v: CarrierA) : mem_block
  :=
    match n with
    | O => mem_add n v (mem_empty)
    | S n' => mem_add n v (mem_const_block n' v)
    end.

Definition memory := NatMap mem_block.

Definition mem_block_equiv:= NM.Equal (elt:=CarrierA).
