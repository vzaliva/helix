Require Import Coq.micromega.Lia.

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

  Instance Int64_lt_proper: Proper ((=) ==> (=) ==> (eq)) Int64.lt.
  Proof.
    simpl_relation.
    unfold Int64.lt.
    destruct x as [x [xc1 xc2]].
    destruct y as [y [yc1 yc2]].
    destruct x0 as [x0 [x0c1 x0c2]].
    destruct y0 as [y0 [y0c1 y0c2]].
    inversion H as [H2]; unfold Int64.eq in H2; cbn in H2;
      destruct (Coqlib.zeq x y) as [Ex|_]; try inversion H2; clear H H2; subst.
    inversion H0 as [H2]; unfold Int64.eq in H2; cbn in H2;
      destruct (Coqlib.zeq x0 y0) as [Ex0|_]; try inversion H2; clear H0 H2; subst.
    unfold Int64.signed.
    Opaque Int64.modulus.
    cbn in *.
    repeat break_if; try lia; try congruence.
  Qed.

  Instance NTypeMin_proper: Proper ((=) ==> (=) ==> (=)) NTypeMin  .
  Proof.
    unfold NTypeMin.
    simpl_relation.
    rewrite H, H0.
    break_if;auto.
  Qed.

  Instance NTypeMax_proper: Proper ((=) ==> (=) ==> (=)) NTypeMax  .
  Proof.
    unfold NTypeMax.
    simpl_relation.
    rewrite H, H0.
    break_if;auto.
  Qed.

  Definition to_string (n : t) : String.string := string_of_nat (to_nat n).

  Lemma from_nat_lt:
    forall x xi y,
      from_nat x ≡ inr xi ->
      y<x ->
      exists yi, from_nat y ≡ inr yi.
  Proof.
    intros x xi y H H0.
    unfold from_nat, from_Z in *.
    apply Znat.inj_lt in H0.
    repeat break_match; try inl_inr; try lia.
    eexists.
    eauto.
  Qed.

  Lemma from_nat_zero: exists z, from_nat O ≡ inr z.
  Proof.
    exists (Int64.mkint (Int64.Z_mod_modulus BinNums.Z0) (Int64.Z_mod_modulus_range' BinNums.Z0)).
    cbn.
    pose proof (Int64.unsigned_range Int64.zero) as [H0 H1].
    break_match.
    - f_equiv.
      f_equiv.
      apply proof_irrelevance.
    - contradict n.
      lia.
  Qed.


End MInt64asNT.
