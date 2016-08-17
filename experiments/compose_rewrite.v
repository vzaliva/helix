

Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Setoids.Setoid.

Unset Printing Notations.

Lemma Foo
      {A:Type}
      (f0 f1 f2 f3 f4: A->A)
  :
    (compose f1 (compose f2 (compose f3 f4)))
  =
  (compose f1 (compose (compose f2 f3) f4)).
Proof.
  intros.
  (* I know, `using reflexivity` works here, but I want to prove by rewriting *)

  setoid_rewrite <- compose_assoc at 2.
  reflexivity.
Qed.



Require Import MathClasses.interfaces.canonical_names.

Lemma Bar
      (A: Type)
      `{Equiv A}
      (f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 res: A->A)
      {m1}:
  equiv
    (compose f1
       (m1
          (compose f2
             (compose f3
                (compose f4
                   (compose f5
                      (compose
                         f6
                         f7)))))

          (compose f8
             (compose f9
                (compose f10
                   (compose
                      f11
                      f12))))))  res.
Proof.

  setoid_rewrite <- compose_assoc at 9.

  (* replace (compose f10 (compose f11 f12)) with (compose (compose f10 f11) f12)
    by apply compose_assoc. *)

Qed.