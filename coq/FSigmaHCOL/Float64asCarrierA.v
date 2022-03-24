Require Import Coq.ZArith.ZArith Coq.Bool.Bool.
Require Import MathClasses.interfaces.abstract_algebra.
From Flocq Require Import Binary Bits.

Require Import Helix.HCOL.CarrierType.
Require Import Helix.Tactics.StructTactics.

Inductive binary64_lt : relation binary64 :=
| binary64_lt_lt (a b : binary64) :
  Bcompare _ _ a b ≡ Some Datatypes.Lt ->
  binary64_lt a b.

Inductive binary64_eq : relation binary64 :=
| binary64_eq_eq (a b : binary64) :
  Bcompare _ _ a b ≡ Some Datatypes.Eq ->
  binary64_eq a b.

Inductive binary64_le : relation binary64 :=
| binary64_lt_le (a b : binary64) :
  Bcompare _ _ a b ≡ Some Datatypes.Lt ->
  binary64_le a b
| binary64_eq_le (a b : binary64) :
  Bcompare _ _ a b ≡ Some Datatypes.Eq ->
  binary64_le a b.

Lemma Bcompare_fin_refl :
  forall prec emax s m e B,
    Bcompare prec emax (B754_finite _ _ s m e B) (B754_finite _ _ s m e B) ≡ Some Eq.
Admitted.

Instance Abs_binary64 :
  @Abs binary64 binary64_eq binary64_le (B754_zero _ _ false) b64_opp.
Proof.
  econstructor.
  instantiate (1:=b64_abs x).
  split; intros Z.
  -
    unfold b64_abs, Babs.
    unfold le in *.
    destruct x; invc Z.
    unfold zero in *.
    all: cbn in *.
    all: try solve [inv H].
    +
      now constructor.
    +
      break_if; invc H; now constructor.
    +
      break_if; invc H; now constructor.
    +
      break_if; invc H.
      constructor.
      apply Bcompare_fin_refl.
    +
      break_if; invc H.
  -
    unfold b64_abs, Babs.
    unfold le in *.
    destruct x; invc Z.
    unfold zero in *.
    all: cbn in *.
    all: try solve [inv H].
    +
      now constructor.
    +
      break_if; invc H; now constructor.
    +
      break_if; invc H; now constructor.
    +
      break_if; invc H.
      constructor.
      apply Bcompare_fin_refl.
    +
      break_if; invc H.
Defined.

Instance binary64_ltdec
  : ∀ x y : binary64, Decision (binary64_lt x y).
Admitted.

Instance binary64_equivdec
  : ∀ x y : binary64, Decision (binary64_eq x y).
Admitted.

Program Definition binary64_zero : binary64 := Bone _ _ eq_refl eq_refl.

Instance CarrierDefs_b64 : CarrierDefs :=
  { CarrierA := binary64
  ; CarrierAe := binary64_eq
  ; CarrierAle := binary64_le
  ; CarrierAlt := binary64_lt
  ; CarrierAltdec := binary64_ltdec
  ; CarrierAequivdec := binary64_equivdec
  ; CarrierAz := B754_zero _ _ false
  ; CarrierA1 := binary64_zero
  ; CarrierAplus := b64_plus mode_NE
  ; CarrierAmult := b64_mult mode_NE
  ; CarrierAneg := b64_opp
  ; CarrierAabs := Abs_binary64
  }.

Instance CarrierProperties_b64 : @CarrierProperties CarrierDefs_b64.
Admitted. (* does not necessary hold, but required for some test computations *)

Definition b0_0 := b64_of_bits 0%Z. (* 0.0 *)
Definition b0_1 := b64_of_bits 4591870180066957722%Z. (* 0.1 *)
Definition b0_2 := b64_of_bits 4596373779694328218%Z. (* 0.2 *)
Definition b0_21 := b64_of_bits 4596734067664517857%Z. (* 0.21 *)
Definition b0_5 := b64_of_bits 4602678819172646912%Z. (* 0.5 *)
Definition b1_0 := b64_of_bits 4607182418800017408. (* 1.0 *)
Definition b1_2 := b64_of_bits 4608083138725491507%Z. (* 1.2 *)
