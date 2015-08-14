(* Coq defintions for Sigma-HCOL operator language *)

Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Numbers.Natural.Peano.NPeano.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.implementations.peano_naturals.
Require Import MathClasses.orders.orders.

Global Open Scope nat_scope.

(* Vector index mapping functon which maps between two sets of natrual
     numers. Mapping is partial and it returns None if there is no correspondance
     between a number in source set and target set. *)
Definition index_map_spec (range domain : nat) :=
  forall n : nat, n < domain -> {v : option nat | forall n' : nat, v ≡ Some n' -> n' < range}.



