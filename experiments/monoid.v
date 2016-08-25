Require Import Coq.ZArith.ZArith.

Local Open Scope Z_scope.

Class ZMonoid (dot : Z -> Z -> Z) (one : Z)
  := {
      zdot_assoc: forall x y z, dot x (dot y z) = dot (dot x y) z;
      zone_left: forall x, dot one x = x;
      zone_right: forall x, dot x one = x
    }.

(* An existing defintion ZFoo which requires function along with neutral element which form a Monoid. *)
Definition ZFoo (f: Z->Z->Z) (id:Z) `{ZMonoid f id} (x:Z) : Z. Admitted.

(* Let use ZFoo from ZBar for (+) and (0) *)
Instance ZMplus: ZMonoid Zplus 0. Proof. split;intros;ring. Qed.
Definition ZBar0 (x:Z) := ZFoo Zplus 0 x.

(* So far, so good. Let us try to use ZFoo with `abs` and 0 in the context where the argument is always non-negative. *)

(* We can prove that for non-negate integers 'abs' always absorbs 0 *)

Lemma Zmax_zero_left (x:Z):
  (x>=0) -> Z.max 0 x = x.
Proof.
  intros.
  unfold Z.max.
  simpl; destruct x; try reflexivity.
  contradiction H; apply Zlt_neg_0.
Qed.

Lemma Zmax_zero_right (x:Z):
  (x>=0) -> Z.max x 0 = x.
Proof.
  intros.
  rewrite Z.max_comm.
  apply Zmax_zero_left, H.
Qed.

(* However we could not create Zmonoid instance as there is no way to constrain 'abs` arguments to be non-negative *)
Instance Mmax: ZMonoid Zmax 0.
Proof.
  split.
  - apply Zmax_assoc.
  - intros; (* apply Zmax_zero_left. *) admit.
  - intros; (* eapply Zmax_zero_right. *) admit.
Admitted.

(* So this would work: *)
Definition Bar1 (x:Z) := ZFoo Zmax 0 (Zabs x).
