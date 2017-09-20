(* ----------- Some handy tactics ----------- *)

Require Export Spiral.CpdtTactics.
Require Export Spiral.StructTactics.

Require Import Coq.Arith.Lt.

Require Import MathClasses.interfaces.canonical_names.

Ltac rewrite_clear H := rewrite H; clear H.

Ltac nat_lt_0_contradiction := 
  let H' := fresh in
  match goal with
  | [H: Peano.lt ?x O |- _ ] => pose(H' := H); apply lt_n_0 in H'; contradiction H'
  | [H: MathClasses.interfaces.canonical_names.lt ?x O |- _ ] => pose(H' := H); apply lt_n_0 in H'; contradiction H'
  end.

Ltac eta_reduce_all :=
  repeat lazymatch goal with
         | |- context ctx [fun x => ?f x] => change (fun x => f x) with f
         | |- context ctx [fun x y => ?f x y] => change (fun x y => f x y) with f
         | |- context ctx [fun x y z => ?f x y z] => change (fun x y z => f x y z) with f
         end.
