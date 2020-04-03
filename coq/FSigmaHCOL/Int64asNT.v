Require Import Helix.DSigmaHCOL.NType.

Require Import Helix.Util.ErrorSetoid.
Require Import Helix.Util.Misc.
Require Import Helix.Tactics.HelixTactics.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.implementations.peano_naturals.

Require Import Vellvm.Numeric.Integers.

Require Import Coq.Strings.String.
Open Scope string_scope.

Module Int64 := Integers.Int64.

(* =CarrierA= as =CarrierType= *)
Module MInt64asNT <: NType.
  Definition t := Int64.int.

  Instance NTypeEquiv: Equiv t := fun a b => is_true (Int64.eq a b).
  Instance NTypeSetoid: @Setoid t NTypeEquiv.
  Proof.
    unfold Setoid, t, equiv, NTypeEquiv.
    split.
    -
      intros x.
      apply Int64.eq_true.
    -
      intros x y.
      rewrite Int64.eq_sym.
      auto.
    -
      intros x y z Exy Eyz.
      unfold is_true in *.

      generalize (Int64.eq_spec x y).
      case (Int64.eq x y); intros.
      +
        rewrite <- H in Eyz.
        apply Eyz.
      +
        apply Int64.eq_false in H.
        congruence.
  Qed.

  (* could always be converted to `nat` *)
  Definition to_nat (n:t) : nat := BinInt.Z.to_nat (Int64.intval n).
  Definition to_nat_proper: Proper ((=) ==> (=)) to_nat.
  Proof.
    simpl_relation.

    generalize (Int64.eq_spec x y).
    case (Int64.eq x y); intros.
    -
      rewrite H0.
      reflexivity.
    -
      exfalso.
      apply Int64.eq_false in H0.
      congruence.
  Qed.

  Definition from_Z (z:BinInt.Z): err t :=
    match ZArith_dec.Z_lt_dec (BinNums.Zneg BinNums.xH) z with
    | left H0 =>
      match ZArith_dec.Z_lt_dec z Int64.modulus with
      | left H1 => inr (Int64.mkint z (conj H0 H1))
      | in_right => inl "too big"
      end
    | in_right => inl "negative"
    end.

  (* not all nats could be converted to `t` *)
  Definition from_nat (n:nat): err t :=
    from_Z (BinInt.Z.of_nat n).

  Definition from_nat_proper: Proper ((=) ==> (=)) from_nat.
  Proof. solve_proper. Qed.

  (* arithmetics oInt64ators *)
  Definition NTypeDiv   := Int64.divu .
  Definition NTypeMod   := Int64.modu .
  Definition NTypePlus  := Int64.add  .
  Definition NTypeMinus := Int64.sub  .
  Definition NTypeMult  := Int64.mul  .

  Definition NTypeMin (a b:t) : t :=
    if Int64.lt a b then a else b.

  Definition NTypeMax  (a b:t) : t :=
    if Int64.lt a b then b else a.

  Instance NTypeDiv_proper: Proper ((=) ==> (=) ==> (=)) NTypeDiv.
  Proof.
    unfold NTypeDiv, Int64.divu.
    intros x0 y0 E0 x1 y1 E1.

    generalize (Int64.eq_spec x0 y0).
    case (Int64.eq x0 y0); intros.
    -
      rewrite H.
      generalize (Int64.eq_spec x1 y1).
      case (Int64.eq x1 y1); intros.
      +
        rewrite H0.
        reflexivity.
      +
        apply Int64.eq_false in H0.
        congruence.
    -
        apply Int64.eq_false in H.
        congruence.
  Qed.

  Instance NTypeMod_proper: Proper ((=) ==> (=) ==> (=)) NTypeMod  .
  Proof.
    (* Copy-paste from above. TODO: generalize or automate *)
    unfold NTypeDiv, Int64.divu.
    intros x0 y0 E0 x1 y1 E1.

    generalize (Int64.eq_spec x0 y0).
    case (Int64.eq x0 y0); intros.
    -
      rewrite H.
      generalize (Int64.eq_spec x1 y1).
      case (Int64.eq x1 y1); intros.
      +
        rewrite H0.
        reflexivity.
      +
        apply Int64.eq_false in H0.
        congruence.
    -
        apply Int64.eq_false in H.
        congruence.
  Qed.


  Instance NTypePlus_proper: Proper ((=) ==> (=) ==> (=)) NTypePlus .
  Proof.
    (* Copy-paste from above. TODO: generalize or automate *)
    unfold NTypeDiv, Int64.divu.
    intros x0 y0 E0 x1 y1 E1.

    generalize (Int64.eq_spec x0 y0).
    case (Int64.eq x0 y0); intros.
    -
      rewrite H.
      generalize (Int64.eq_spec x1 y1).
      case (Int64.eq x1 y1); intros.
      +
        rewrite H0.
        reflexivity.
      +
        apply Int64.eq_false in H0.
        congruence.
    -
        apply Int64.eq_false in H.
        congruence.
  Qed.

  Instance NTypeMinus_proper: Proper ((=) ==> (=) ==> (=)) NTypeMinus.
  Proof.
    (* Copy-paste from above. TODO: generalize or automate *)
    unfold NTypeDiv, Int64.divu.
    intros x0 y0 E0 x1 y1 E1.

    generalize (Int64.eq_spec x0 y0).
    case (Int64.eq x0 y0); intros.
    -
      rewrite H.
      generalize (Int64.eq_spec x1 y1).
      case (Int64.eq x1 y1); intros.
      +
        rewrite H0.
        reflexivity.
      +
        apply Int64.eq_false in H0.
        congruence.
    -
        apply Int64.eq_false in H.
        congruence.
  Qed.

  Instance NTypeMult_proper: Proper ((=) ==> (=) ==> (=)) NTypeMult .
  Proof.
    (* Copy-paste from above. TODO: generalize or automate *)
    unfold NTypeDiv, Int64.divu.
    intros x0 y0 E0 x1 y1 E1.

    generalize (Int64.eq_spec x0 y0).
    case (Int64.eq x0 y0); intros.
    -
      rewrite H.
      generalize (Int64.eq_spec x1 y1).
      case (Int64.eq x1 y1); intros.
      +
        rewrite H0.
        reflexivity.
      +
        apply Int64.eq_false in H0.
        congruence.
    -
        apply Int64.eq_false in H.
        congruence.
  Qed.

  Instance NTypeMin_proper: Proper ((=) ==> (=) ==> (=)) NTypeMin  .
  Proof.
  Admitted.

  Instance NTypeMax_proper: Proper ((=) ==> (=) ==> (=)) NTypeMax  .
  Proof.
  Admitted.

  Definition to_string (n : t) : String.string := string_of_nat (to_nat n).

End MInt64asNT.
