

Require Import MathClasses.interfaces.canonical_names.

Record Foo : Type := mkFoo {f:nat}.
Instance fequiv: Equiv Foo. Admitted.
Global Instance fequiv_Equivalence: Equivalence (fequiv). Admitted.

Definition fplus (a b:Foo): Foo := mkFoo ((f a) + (f b)).
Instance fplus_proper: Proper ((=) ==> (=) ==> (=)) (fplus). Admitted.

(* Instance Foo_Default_equiv: @DefaultRelation Foo feqiuv. *)

(* Print Instances DefaultRelation. *)

Example ex1 (a b c: Foo):
  equiv a b -> equiv (fplus a c) (fplus b c).
Proof.
  intros H.
  Typeclasses eauto := debug.
  setoid_replace (a) with (b).
  (* setoid_replace (a) with (b) using relation equiv. *)
  setoid_rewrite H.
  reflexivity.
Qed.