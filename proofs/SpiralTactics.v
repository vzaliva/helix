(* ----------- Some handy tactics ----------- *)

Require Export Spiral.CpdtTactics.
Require Export Spiral.StructTactics.

Require Import Coq.Arith.Lt.
Require Import Coq.Arith.Peano_dec.

Require Import MathClasses.interfaces.canonical_names.

Ltac rewrite_clear H := rewrite H; clear H.

Ltac nat_lt_0_contradiction := 
  let H' := fresh in
  match goal with
  | [H: Peano.lt ?x O |- _ ] => pose(H' := H); apply lt_n_0 in H'; contradiction H'
  | [H: MathClasses.interfaces.canonical_names.lt ?x O |- _ ] => pose(H' := H); apply lt_n_0 in H'; contradiction H'
  end.

(* See https://stackoverflow.com/questions/46311353/eta-conversion-tactics/46326616 *)
(* h is a dummy argument to make Coq happy, it gets shadowed with `?h` *)
Ltac eta_reduce_all_private h := repeat change (fun x => ?h x) with h.
Ltac eta_reduce_all := eta_reduce_all_private idtac.

(*
Give equality of two functions of type [∀ p : nat, p < n → A] and and a hypotheis [i0=i1] solves the goal.
*)
Ltac forall_n_lt_eq :=
  let lc := fresh in
  let rc := fresh in
  let Q := fresh in
  let HeqQ := fresh in
  match goal with
  | [ H: ?i0 ≡ ?i1 |-  ?gen ?i0 ?ic0 ≡ ?gen ?i1 ?ic1] =>
    generalize ic0 as lc;
    generalize ic1 as rc;
    intros rc lc ;
    remember i0 as Q eqn:HeqQ;
    rewrite H in HeqQ;
    subst Q;
    apply f_equal, le_unique;
    clear rc lc HeqQ
  end.
