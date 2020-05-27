(*
Borrowed from https://github.com/QuickChick/QuickChick/blob/master/src/StringOT.v

Ordering code by Antal :)

*)

Require Import Coq.Structures.OrderedType.
Require Import Coq.Strings.Ascii.
Require Import Coq.NArith.NArith.

Module AsciiOT <: OrderedType.

  Definition t := ascii.

  Definition eq       := @Logic.eq       ascii.
  Definition eq_refl  := @Logic.eq_refl  ascii.
  Definition eq_sym   := @Logic.eq_sym   ascii.
  Definition eq_trans := @Logic.eq_trans ascii.
  Definition eq_dec   := ascii_dec.

  Definition lt (c d : ascii) : Prop := (N_of_ascii c < N_of_ascii d)%N.

  Theorem lt_trans : forall c d e : ascii, lt c d -> lt d e -> lt c e.
  Proof. intros *; unfold lt; apply N.lt_trans. Qed.

  Theorem lt_not_eq : forall c d : ascii, lt c d -> ~ eq c d.
  Proof.
    unfold lt, eq; red; intros;
      assert (N_of_ascii c = N_of_ascii d) as eq' by (f_equal; assumption);
      generalize dependent eq'; apply N.lt_neq; assumption.
  Qed.

  Theorem compare : forall c d : ascii, Compare lt eq c d.
  Proof.
    unfold lt, eq; intros;
      remember (N_of_ascii c ?= N_of_ascii d)%N as C; symmetry in HeqC; destruct C;
        [ apply EQ; replace c with (ascii_of_N (N_of_ascii c))
            by apply ascii_N_embedding;
          replace d with (ascii_of_N (N_of_ascii d))
            by apply ascii_N_embedding;
          f_equal; apply N.compare_eq
        | apply LT
        | apply GT; apply N.gt_lt];
        assumption.
  Qed.

End AsciiOT.

