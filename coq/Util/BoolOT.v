(*
Borrowed from https://github.com/QuickChick/QuickChick/blob/master/src/StringOT.v

Ordering code by Antal :)

*)

Require Import Coq.Structures.OrderedType.

Require Import Bool.

Module BoolOT <: OrderedType.

  Definition t := bool.

  Definition eq       := @Logic.eq       bool.
  Definition eq_refl  := @Logic.eq_refl  bool.
  Definition eq_sym   := @Logic.eq_sym   bool.
  Definition eq_trans := @Logic.eq_trans bool.
  Definition eq_dec   := bool_dec.

  Definition lt (b1 b2 : bool) : Prop := b1 = false /\ b2 = true.

  Theorem lt_trans : forall x y z : bool, lt x y -> lt y z -> lt x z.
  Proof. unfold lt; tauto. Qed.

  Theorem lt_not_eq : forall x y : bool, lt x y -> ~ eq x y.
  Proof. unfold lt, eq; intuition; congruence. Qed.

  Theorem compare : forall x y : bool, Compare lt eq x y.
  Proof.
    unfold lt, eq; repeat (let b := fresh in intros b; destruct b);
      [apply EQ | apply GT | apply LT | apply EQ]; auto.
  Qed.

End BoolOT.

