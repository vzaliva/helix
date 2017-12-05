(* https://stackoverflow.com/questions/47645059/changing-type-under-lambda-in-coq *)

Require Import Setoid Morphisms Relations.

(* Definitions *)
Record S {i o: nat} : Type.
Definition C {i o: nat} (f: @S i o):  @S i o. Admitted.
Definition B {o:nat} (z:nat): @S (o+o) o. Admitted.

(* Relations *)
Parameter R: forall {i o}, relation (@S i o).
Instance R_proper {i o}: Proper (R ==> R ==> iff) (@R i o). Admitted.

Definition Rext {i o} := pointwise_relation nat (@R i o).

(* Sample rewriting lemma *)
Lemma Rewrite (x:nat): forall z, R (C (@B x z)) (B z). Admitted.

(* Will be used later *)
Ltac Type_Fix :=
  match goal with
  | [ |- context G [ (@C (Datatypes.S _) ?o (@B ?o ?z))] ] =>
    let G' := context G[(@C (o+o) o (@B o z))] in change G'
  end.

(* Simple case with workaround *)
Theorem Foo (p:nat): R (@C 2 1 (@B 1 p)) (@C 2 1 (@B 1 p)).
Proof.
  (*
 The following fails, as expected, with error:

  Error:
  Ltac call to "setoid_rewrite (orient) (glob_constr_with_bindings)" failed.
  Tactic failure: setoid rewrite failed: Nothing to rewrite.

   *)
  Fail setoid_rewrite Rewrite.

  (* The problem is that type of (C (B p)) is (@S 2 1) while our rewriting lemma exepects (@C (1+1) 1)

  We can fix types via LTAC: *)

  repeat Type_Fix.
  setoid_rewrite Rewrite.

Admitted.

(* Now try under lambda: *)
Theorem Bar (p:nat): Rext (fun z => @C 2 1 (@B 1 z)) (fun z => @C 2 1 (@B 1 z)).
Proof.
  (* This still fails *)
  Fail setoid_rewrite Rewrite.

  (* Our LTAC fix no longer works also: *)
  Fail Type_Fix.
Admitted.