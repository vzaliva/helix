Require Import MathClasses.interfaces.canonical_names.

Require Import Coq.Strings.String.

Global Instance string_Equiv : Equiv string :=
  fun a b => is_true (eqb a b).

Global Instance string_Equivalence:
  @Equivalence string (string_Equiv).
Proof.
  split.
  -
    intros x.
    apply eqb_refl.
  -
    intros x y E.
    unfold string_Equiv, is_true in *.
    rewrite <- E.
    apply eqb_sym.
  -
    intros a b c Eab Ebc.
    unfold string_Equiv, is_true in *.
    apply eqb_eq in Eab.
    apply eqb_eq in Ebc.
    rewrite Eab, Ebc.
    apply eqb_refl.
Qed.
