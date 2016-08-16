

Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Setoids.Setoid.

Unset Printing Notations.

Lemma Foo
      {A:Type}
      (f0 f1 f2 f3 f4: A->A)
  :
    compose f1 (compose f2 (compose f3 f4))
    =
    compose f1 (compose (compose f2 f3) f4).
Proof.
  intros.
  (* I know, `using reflexivity` works here, but I want to prove by rewriting *)

  (* The following does not work. Error: Tactic failure: Nothing to rewrite. *)
  try rewrite <- compose_assoc at 2.

  (* However, the following works OK. *)
  replace (compose f2 (compose f3 f4)) with (compose (compose f2 f3) f4)
    by apply compose_assoc.

  reflexivity.
Qed.
