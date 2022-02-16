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

Module Int32 := Integers.Int. (* 32-bit *)

From Coq Require Import ZArith.

(* [Int32.int] as [NType]

We are using singed integer type here because LLVM does not make a
distinction between signed and unsigned integer type, so both will be
lowered to i32. The operations on the unsigned integer, though, will
be translated according to the original type; e.g. a division between
unsigned integers will be udiv while between signed will be sdiv

*)
Module MInt32asNT <: NType.
  Definition t := Int32.int.

  Instance NTypeEquiv: Equiv t := fun a b => is_true (Int32.eq a b).
  Instance NTypeSetoid: @Setoid t NTypeEquiv.
  Proof.
    unfold Setoid, t, equiv, NTypeEquiv.
    split.
    -
      intros x.
      apply Int32.eq_true.
    -
      intros x y.
      rewrite Int32.eq_sym.
      auto.
    -
      intros x y z Exy Eyz.
      unfold is_true in *.

      generalize (Int32.eq_spec x y).
      case (Int32.eq x y); intros.
      +
        rewrite <- H in Eyz.
        apply Eyz.
      +
        apply Int32.eq_false in H.
        congruence.
  Qed.

  Instance NTypeEqDec: forall x y: t, Decision (x = y).
  Proof.
    intros x y.
    simpl_relation.
    destruct x as [x xc].
    destruct y as [y yc].

    destruct (BinInt.Z.eq_dec x y).
    -
      subst.
      left.
      f_equiv.
      apply proof_irrelevance.
    -
      right.
      intros H.
      inversion H.
      unfold Int32.eq in H1.
      break_if;[|congruence].
      cbn in e.
      congruence.
  Qed.

  (* could always be converted to `nat` *)
  Definition to_nat (n:t) : nat := BinInt.Z.to_nat (Int32.intval n).
  Definition to_nat_proper: Proper ((=) ==> (=)) to_nat.
  Proof.
    simpl_relation.

    generalize (Int32.eq_spec x y).
    case (Int32.eq x y); intros.
    -
      rewrite H0.
      reflexivity.
    -
      exfalso.
      apply Int32.eq_false in H0.
      congruence.
  Qed.

  Definition NTypeZero := Int32.zero.
  Definition NTypeOne := Int32.one.

  Definition from_Z (z:BinInt.Z): err t :=
    match ZArith_dec.Z_lt_dec (BinNums.Zneg BinNums.xH) z with
    | left H0 =>
      match ZArith_dec.Z_lt_dec z Int32.modulus with
      | left H1 => inr (Int32.mkint z (conj H0 H1))
      | in_right => inl "too big"
      end
    | in_right => inl "negative"
    end.

  Definition from_N (n:N): err t := from_Z (Z.of_N n).

  (* not all nats could be converted to `t` *)
  Definition from_nat (n:nat): err t :=
    from_Z (BinInt.Z.of_nat n).

  Definition from_nat_proper: Proper ((=) ==> (=)) from_nat.
  Proof. solve_proper. Qed.

  (* arithmetics oInt32ators *)
  Definition NTypeDiv   := Int32.divu .
  Definition NTypeMod   := Int32.modu .
  Definition NTypePlus  := Int32.add  .
  Definition NTypeMinus := Int32.sub  .
  Definition NTypeMult  := Int32.mul  .

  Definition NTypeMin (a b:t) : t :=
    if Int32.ltu a b then a else b.

  Definition NTypeMax  (a b:t) : t :=
    if Int32.ltu a b then b else a.

  Instance NTypeDiv_proper: Proper ((=) ==> (=) ==> (=)) NTypeDiv.
  Proof.
    unfold NTypeDiv, Int32.divu.
    intros x0 y0 E0 x1 y1 E1.

    generalize (Int32.eq_spec x0 y0).
    case (Int32.eq x0 y0); intros.
    -
      rewrite H.
      generalize (Int32.eq_spec x1 y1).
      case (Int32.eq x1 y1); intros.
      +
        rewrite H0.
        reflexivity.
      +
        apply Int32.eq_false in H0.
        congruence.
    -
        apply Int32.eq_false in H.
        congruence.
  Qed.

  Instance NTypeMod_proper: Proper ((=) ==> (=) ==> (=)) NTypeMod  .
  Proof.
    (* Copy-paste from above. TODO: generalize or automate *)
    unfold NTypeDiv, Int32.divu.
    intros x0 y0 E0 x1 y1 E1.

    generalize (Int32.eq_spec x0 y0).
    case (Int32.eq x0 y0); intros.
    -
      rewrite H.
      generalize (Int32.eq_spec x1 y1).
      case (Int32.eq x1 y1); intros.
      +
        rewrite H0.
        reflexivity.
      +
        apply Int32.eq_false in H0.
        congruence.
    -
        apply Int32.eq_false in H.
        congruence.
  Qed.


  Instance NTypePlus_proper: Proper ((=) ==> (=) ==> (=)) NTypePlus .
  Proof.
    (* Copy-paste from above. TODO: generalize or automate *)
    unfold NTypeDiv, Int32.divu.
    intros x0 y0 E0 x1 y1 E1.

    generalize (Int32.eq_spec x0 y0).
    case (Int32.eq x0 y0); intros.
    -
      rewrite H.
      generalize (Int32.eq_spec x1 y1).
      case (Int32.eq x1 y1); intros.
      +
        rewrite H0.
        reflexivity.
      +
        apply Int32.eq_false in H0.
        congruence.
    -
        apply Int32.eq_false in H.
        congruence.
  Qed.

  Instance NTypeMinus_proper: Proper ((=) ==> (=) ==> (=)) NTypeMinus.
  Proof.
    (* Copy-paste from above. TODO: generalize or automate *)
    unfold NTypeDiv, Int32.divu.
    intros x0 y0 E0 x1 y1 E1.

    generalize (Int32.eq_spec x0 y0).
    case (Int32.eq x0 y0); intros.
    -
      rewrite H.
      generalize (Int32.eq_spec x1 y1).
      case (Int32.eq x1 y1); intros.
      +
        rewrite H0.
        reflexivity.
      +
        apply Int32.eq_false in H0.
        congruence.
    -
        apply Int32.eq_false in H.
        congruence.
  Qed.

  Instance NTypeMult_proper: Proper ((=) ==> (=) ==> (=)) NTypeMult .
  Proof.
    (* Copy-paste from above. TODO: generalize or automate *)
    unfold NTypeDiv, Int32.divu.
    intros x0 y0 E0 x1 y1 E1.

    generalize (Int32.eq_spec x0 y0).
    case (Int32.eq x0 y0); intros.
    -
      rewrite H.
      generalize (Int32.eq_spec x1 y1).
      case (Int32.eq x1 y1); intros.
      +
        rewrite H0.
        reflexivity.
      +
        apply Int32.eq_false in H0.
        congruence.
    -
        apply Int32.eq_false in H.
        congruence.
  Qed.

  Instance Int32_ltu_proper: Proper ((=) ==> (=) ==> (eq)) Int32.ltu.
  Proof.
    simpl_relation.
    unfold Int32.ltu.
    destruct x as [x [xc1 xc2]].
    destruct y as [y [yc1 yc2]].
    destruct x0 as [x0 [x0c1 x0c2]].
    destruct y0 as [y0 [y0c1 y0c2]].
    inversion H as [H2]; unfold Int32.eq in H2; cbn in H2;
      destruct (Coqlib.zeq x y) as [Ex|_]; try inversion H2; clear H H2; subst.
    inversion H0 as [H2]; unfold Int32.eq in H2; cbn in H2;
      destruct (Coqlib.zeq x0 y0) as [Ex0|_]; try inversion H2; clear H0 H2; subst.
    unfold Int32.signed.
    Opaque Int32.modulus.
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

  Lemma to_nat_from_nat :
    forall n nt,
      from_nat n = inr nt <-> to_nat nt = n.
  Proof.
    intros.
    unfold from_nat, to_nat, from_Z.
    split; intro E.
    -
      repeat break_match; invc E.
      pose proof Integers.Int.eq_spec
           {| Int32.intval := Z.of_nat n; Int.intrange := conj l l0 |}
           nt
        as EQI.
      rewrite H1 in EQI.
      apply f_equal with (f:=Int32.intval) in EQI.
      rewrite <-EQI.
      cbn.
      now rewrite Nat2Z.id.
    -
      destruct nt as [nv nr]; cbn in *.
      repeat break_match.
      2,3: apply f_equal with (f:=Z.of_nat) in E; lia.
      f_equiv.
      unfold equiv, NTypeEquiv, Int32.eq.
      cbn.
      rewrite <-E, Z2Nat.id by lia.
      break_if.
      reflexivity.
      contradiction.
  Qed.

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

  Lemma to_nat_zero: to_nat NTypeZero ≡ 0.
  Proof.
    reflexivity.
  Qed.

  Lemma to_nat_one: to_nat NTypeOne ≡ 1.
  Proof.
    reflexivity.
  Qed.

End MInt32asNT.
