(* Memory-based implementations of SHCOL operators *)

Require Import Helix.Util.VecUtil.
Require Import Helix.Util.Matrix.
Require Import Helix.Util.VecSetoid.
Require Import Helix.Util.Misc.
Require Import Helix.Util.FinNat.
Require Import Helix.SigmaHCOL.Rtheta.
Require Import Helix.SigmaHCOL.SVector.
Require Import Helix.SigmaHCOL.IndexFunctions.
Require Import Helix.SigmaHCOL.SigmaHCOLImpl.
Require Import Helix.SigmaHCOL.Memory.
Require Import Helix.HCOL.HCOL. (* Presently for HOperator only. Consider moving it elsewhere *)
Require Import Helix.Util.FinNatSet.
Require Import Helix.Util.WriterMonadNoT.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.BoolEq.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Decidable.

Require Import Helix.Tactics.HelixTactics.
Require Import Psatz.
Require Import Omega.

Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.theory.rings.
Require Import MathClasses.implementations.peano_naturals.
Require Import MathClasses.orders.orders.
Require Import MathClasses.orders.semirings.
Require Import MathClasses.theory.setoids.

Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Monoid.

Import Monoid.

Import VectorNotations.
Open Scope vector_scope.

Global Open Scope nat_scope.

Set Implicit Arguments.

Fixpoint avector_to_mem_block' {n} (i:nat) (v:avector n): mem_block
  :=
    match v with
    | Vnil => mem_empty
    | Vcons x xs =>
      mem_add n x (avector_to_mem_block' (S i) xs)
    end.

Definition avector_to_mem_block {n:nat}: (avector n) -> mem_block
  := avector_to_mem_block' 0.

Definition mem_block_to_avector {n} (m: mem_block): option (avector n)
  := vsequence (Vbuild (fun i (ic:i<n) => mem_lookup i m)).

(* HOperator (on dense vector) mapping to memory operator *)
Definition mem_op_of_hop {i o: nat} (op: avector i -> avector o)
  : mem_block -> option mem_block
  := fun x => match mem_block_to_avector x with
           | None => None
           | Some x' => Some (avector_to_mem_block (op x'))
           end.

Section WithFlags.

  Variable fm:Monoid RthetaFlags.

  Fixpoint svector_to_mem_block' {n} (i:nat) (v:svector fm n): mem_block
    :=
      match v with
      | Vnil => mem_empty
      | Vcons x xs =>
        match Is_Val_dec x with
        | left _ => mem_add n (WriterMonadNoT.evalWriter x) (svector_to_mem_block' (S i) xs)
        | right _ => svector_to_mem_block' (S i) xs
        end
      end.

  Definition svector_to_mem_block {n:nat}: (svector fm n) -> mem_block
    := svector_to_mem_block' 0.

  Definition mem_block_to_svector {n} (m: mem_block): svector fm n
    := Vbuild (fun i (ic:i<n) =>
                 match mem_lookup i m with
                 | None => mkSZero
                 | Some x => mkValue x
                 end
              ).

  (* SHOperator (on sparse vectors) mapping to memory operator *)
  Definition mem_op_of_op {i o: nat} (op: svector fm i -> svector fm o)
    : mem_block -> option mem_block
    := fun x => Some (svector_to_mem_block (op (mem_block_to_svector x))).

  (* y[j] := x[i] *)
  Definition map_mem_block_elt (x:mem_block) (i:nat) (y:mem_block) (j:nat)
    : option mem_block :=
    match mem_lookup i x with
    | None => None
    | Some v => Some (mem_add j v y)
    end.

  (* AKA: "embed" *)
  Definition eUnion_mem (b: nat) (x:mem_block): option mem_block :=
    map_mem_block_elt x 0 (mem_empty) b.

  (* AKA "pick" *)
  Definition eT_mem (b: nat) (x:mem_block): option mem_block :=
    map_mem_block_elt x b (mem_empty) 0.

  Fixpoint Gather_mem
           {i o: nat}
           (f: index_map o i)
           (x: mem_block) : option mem_block
    :=
      match o return (index_map o i) -> option mem_block with
      | O => fun _ => map_mem_block_elt x o (mem_empty) (⟦ f ⟧ o)
      | S o' => fun f' =>
                 match @Gather_mem i o' (shrink_index_map_domain f') x with
                 | None => None
                 | Some ys => map_mem_block_elt x o ys (⟦ f ⟧ o)
                 end
      end f.

End WithFlags.
