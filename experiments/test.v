
Class A (n:nat) : Prop.

Definition f (n:nat) `{A n} := n.
Definition g (n:nat) := n.

(* Instance A_g:  forall x, A (g x). *)

Lemma Foo:
  forall x, f (g x) = x.
Proof.
  auto.
Qed.