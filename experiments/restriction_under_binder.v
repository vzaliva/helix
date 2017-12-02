Require Import Coq.Relations.Relation_Definitions.
Require Import ProofIrrelevance.
Require Import FunctionalExtensionality.
Require Import Coq.Program.Basics.
Require Import Setoid.
Require Import Morphisms.
Require Import Classes.Morphisms_Prop.


(*

Experimenting with rewriting composition under binder where rewrite
rule has additional constraints on RHS argument of compose.

This is similar to situation with applying rewrite_Reduction_ScatHUnion_max_zero
*)

Section Ex.

  Parameter R: relation nat.
  Instance R_reflexive: Reflexive R. Admitted.
  Instance R_trasitive: Transitive R. Admitted.
  Definition Rext := pointwise_relation nat R.

  Parameter a: nat -> nat.
  Instance a_proper: Proper (R ==> R) (a). Admitted.
  Instance compose_proper: Proper (Rext ==> Rext ==> Rext) (compose). Admitted.

  Open Scope program_scope.

  Lemma Bar (b: nat -> nat) (C: forall x, b x < 10): Rext (a ∘ b) b. Admitted.

  Goal (forall (m n: nat) (c: nat -> nat -> nat) (bm: Proper (R ==> R ==> R) (c)),
           Rext ((fun x => a ∘ (c x)) m) (c 1)).
  Proof.
    intros m n c cm.
    Typeclasses eauto := debug.
    Redirect "log" setoid_rewrite Bar.
  Admitted.
End Ex.
