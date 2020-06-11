Require Import Helix.DSigmaHCOL.NType.

Require Import Helix.Util.ErrorSetoid.
Require Import Helix.Util.Misc.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.implementations.peano_naturals.

(* [nat] as [NType] *)
Module MNatAsNT <: NType.
  Definition t := nat.

  Instance NTypeEquiv : Equiv t := nat_equiv.
  Instance NTypeSetoid: @Setoid t NTypeEquiv := sg_setoid nat.

  Instance NTypeEqDec: forall x y: t, Decision (x = y) := nat_dec.

  Definition NTypeZero := O.

  (* could always be converted to `nat` *)
  Definition to_nat (n:t) : nat := n.
  Instance to_nat_proper: Proper ((=) ==> (=)) to_nat.
  Proof. solve_proper. Qed.

  (* not all nats could be converted to `t` *)
  Definition from_nat (n:nat): err t := inr n.
  Instance from_nat_proper: Proper ((=) ==> (=)) from_nat.
  Proof. solve_proper. Qed.

  (* arithmetics operators *)
  Definition NTypeDiv   := Nat.div    .
  Definition NTypeMod   := Nat.modulo .
  Definition NTypePlus  := Nat.add    .
  Definition NTypeMinus := Nat.sub    .
  Definition NTypeMult  := Nat.mul    .
  Definition NTypeMin   := Nat.min    .
  Definition NTypeMax   := Nat.max    .

  Instance NTypeDiv_proper: Proper ((=) ==> (=) ==> (=)) NTypeDiv.
  Proof. solve_proper. Qed.

  Instance NTypeMod_proper: Proper ((=) ==> (=) ==> (=)) NTypeMod  .
  Proof. solve_proper. Qed.

  Instance NTypePlus_proper: Proper ((=) ==> (=) ==> (=)) NTypePlus .
  Proof. solve_proper. Qed.

  Instance NTypeMinus_proper: Proper ((=) ==> (=) ==> (=)) NTypeMinus.
  Proof. solve_proper. Qed.

  Instance NTypeMult_proper: Proper ((=) ==> (=) ==> (=)) NTypeMult .
  Proof. solve_proper. Qed.

  Instance NTypeMin_proper: Proper ((=) ==> (=) ==> (=)) NTypeMin  .
  Proof. solve_proper. Qed.

  Instance NTypeMax_proper: Proper ((=) ==> (=) ==> (=)) NTypeMax  .
  Proof. solve_proper. Qed.

  Definition to_string (n : t) : String.string := string_of_nat (to_nat n).

  Lemma from_nat_lt:
    forall x xi y,
      from_nat x ≡ inr xi ->
      y<x ->
      exists yi, from_nat y ≡ inr yi.
  Proof.
    intros x xi y H H0.
    unfold from_nat in *.
    exists y.
    reflexivity.
  Qed.

  Lemma from_nat_zero: exists z, from_nat O ≡ inr z.
  Proof.
    eexists.
    auto.
  Qed.

End MNatAsNT.
