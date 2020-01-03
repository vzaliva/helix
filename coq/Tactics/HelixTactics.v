(* ----------- Some handy tactics ----------- *)

Require Export Helix.Tactics.CpdtTactics.
Require Export Helix.Tactics.StructTactics.

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
Given an equality of two functions of type `∀ p : nat, p < n → A` and and a hypotheis `i0=i1` solves the goal.
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

(*
 Two-dimensional case of [forall_nm_lt_eq]
*)
Ltac forall_nm_lt_eq :=
  let lcj := fresh in
  let rcj := fresh in
  let lci := fresh in
  let rci := fresh in
  let Q := fresh in
  let HeqQ := fresh in
  let R := fresh in
  let HeqR := fresh in
  match goal with
  | [ H1: ?i0 ≡ ?i1, H2 : ?j0 ≡ ?j1 |- ?gen ?i0 ?ic0 ?j0 ?jc0 ≡ ?gen ?i1 ?ic1 ?j1 ?jc1] =>
    generalize ic0 as lci;
    generalize ic1 as rci;
    generalize jc0 as lcj;
    generalize jc1 as rcj;
    intros rci lci rcj lcj ;
    remember i0 as Q eqn:HeqQ;
    remember j0 as R eqn:HeqR;
    rewrite H1 in HeqQ;
    rewrite H2 in HeqR;
    subst Q;
    subst R;
    replace lcj with rcj by apply le_unique;
    replace lci with rci by apply le_unique;
    reflexivity;
    clear rci lci rcj lcj HeqQ HeqR
  end.

Ltac equiv_extensionality v v' E:=
  match goal with
  | [ |- @equiv _ (@ext_equiv _ _ _  _) _ _] => unfold equiv, ext_equiv; intros v v' E
  end.

Require Import Specif.
Ltac inv_exitstT :=  repeat match goal with
                              [ H: eq (existT _ _ _) (existT _ _ _) |- _ ] => apply Coq.Logic.ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 in H
                            end.

Ltac assert_match_equiv H :=
  match goal with
  | [|- match ?a with _ => _  end = match ?b with _ => _  end] =>
    assert(a = b) as H
  end.

Ltac assert_match_eq H :=
  match goal with
  | [|- match ?a with _ => _  end ≡ match ?b with _ => _  end] =>
    assert(a ≡ b) as H
  end.
