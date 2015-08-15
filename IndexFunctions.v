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
Definition index_map_spec (domain range: nat) :=
  forall n : nat, n < domain -> {v : option nat | forall n' : nat, v ≡ Some n' -> n' < range}.

(* Returns upper domain bound for given `index_map_spec` *)
Definition index_map_dom {d r:nat} (s: index_map_spec d r) := d.

(* Returns upper rang bound for given `index_map_spec` *)
Definition index_map_range {d r:nat} (s: index_map_spec d r) := r.

Section TotalIndexMap.

  (* Vector index mapping functon which maps between two sets of natrual
     numers. *)
  Definition total_index_map_spec (domain range: nat) :=
    forall n : nat, n < domain -> {v : nat | v < range}.
  
  (* Returns upper domain bound for given `total_index_map_spec` *)
  Definition total_index_map_dom {d r:nat} (s: total_index_map_spec d r) := d.
  
  (* Returns upper rang bound for given `total_index_map_spec` *)
  Definition total_index_map_range {d r:nat} (s: total_index_map_spec d r) := r.

  Definition total_index_map_compose
             {i o t: nat}
             (g: total_index_map_spec t o)
             (f: total_index_map_spec i t) :
    total_index_map_spec i o
    := fun x xdom_bound =>
         (* manual uncurry *)
         let (fv, fv_dom_bound) := f x xdom_bound in
         g fv fv_dom_bound.

  Program Definition identity_index_map
          {domain range: nat}
          {drdep: domain ≡ range}:
    total_index_map_spec domain range
    :=
      fun i i_dim => i.

End TotalIndexMap.
