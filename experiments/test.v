
Class A (n:nat) : Prop.

Definition f (n:nat) `{A n} := n.
Definition g (n:nat) := n.

Lemma Foo:
  exists w, forall x, @f (g x) (w x) = x.
Proof.
  unshelve eexists.
  -
    split.
  -
    auto.
Qed.

(* Instance A_g:  forall x, A (g x). *)

Lemma Foo_Test:
  exists w, 5 + @f (g 1) (w 1) = 5 + 1.
Proof.
  elim Foo.
  intros A_g H.
  exists A_g.
  rewrite H.
  reflexivity.
Qed.