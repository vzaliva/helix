
Class A (n:nat) : Prop.

Definition f (n:nat) `{A n} := n.
Definition g (n:nat) := n.

(*
Instance A_g:  forall x, A (g x).

Lemma Foo:
  forall x, f (g x) = x.
Proof.
  auto.
Qed.
*)


Lemma Foo:
  forall x, exists w, @f (g x) w = x.
Proof.
  intro x.
  unshelve eexists.
  -
    split.
  -
    auto.
Qed.

Lemma Foo_Test:
  exists w, 5 + @f (g 1) (w 1) = 5 + 1.
Proof.
  unshelve eelim Foo.
  exact 1.
  intros A_g H.
  unshelve eexists.
  split.
  erewrite H.
  -
    split.
  -

    eelim Foo.
  intros A_g H.
  exists A_g.
  rewrite H.
  reflexivity.
Qed.

Lemma Foo_Test:
  exists w, 5 + @f (g 1) (w 1) = 5 + 1.
Proof.
  elim Foo.
  intros A_g H.
  exists A_g.
  rewrite H.
  reflexivity.
Qed.