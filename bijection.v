
(* 
Library bijection

Dimitri Hendriks 2013-10-09

http://www.cs.vu.nl/~diem/coq/calkin-wilf/bijection.html
*)

Set Implicit Arguments.

Section bijections.

Variables A B : Set.

Definition injective (f : A -> B) := forall x y : A, f x = f y -> x = y.

Definition surjective (f : A -> B) := forall y : B, {x : A | f x = y}.

Inductive bijective (f : A -> B) : Set :=
  is_bijective : injective f -> surjective f -> bijective f.

Definition left_inverse (f : A -> B) (f' : B -> A) := 
  forall x : A, f' (f x) = x.

Definition right_inverse (f : A -> B) (f' : B -> A) := 
  forall y : B, f (f' y) = y.

Definition inverse f f' := 
  left_inverse f f' /\ right_inverse f f'.

Lemma left_inv_inj f f' : left_inverse f f' -> injective f.
Proof.
intros H x y H0.
rewrite <- (H x).
rewrite H0.
apply H.
Qed.

Lemma right_inv_surj f f' : right_inverse f f' -> surjective f.
Proof.
intros H y.
rewrite <- (H y).
exact (exist (fun x => f x = f (f' y)) (f' y) (refl_equal (f (f' y)))).
Qed.

Lemma inv2bij f f' : inverse f f' -> bijective f.
Proof.
intros [H1 H2].
exact (is_bijective (left_inv_inj H1) (right_inv_surj H2)).
Qed.

End bijections.
