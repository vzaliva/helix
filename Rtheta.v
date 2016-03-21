(* R_theta is type which is used as value for vectors in SPIRAL.  *)

Require Export CarrierType.

Require Import Coq.Bool.Bool.
Require Import Ring.

Require Import ExtLib.Core.Type.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Data.Monads.WriterMonad.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import WriterMonadNoT.
Require Import ExtLib.Structures.MonadLaws.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.theory.rings.
Require Import MathClasses.interfaces.orders MathClasses.orders.orders.

Require Import CpdtTactics.
Require Import JRWTactics.


Import MonadNotation.
Local Open Scope monad_scope.

Record RthetaFlags : Type :=
  mkRthetaFlags
    {
      is_struct: bool ;
      is_collision: bool
    }.

(* Propositional predicates *)
Definition IsCollision (x:RthetaFlags) := Is_true (is_collision x).
Definition IsStruct (x:RthetaFlags) := Is_true (is_struct x).
Definition IsVal (x:RthetaFlags) := not (Is_true (is_struct x)).

Definition RthetaFlagsAppend (a b: RthetaFlags) : RthetaFlags :=
  mkRthetaFlags
    (andb (is_struct a) (is_struct b))
    (orb (is_collision a) (orb (is_collision b)
                               (negb (orb (is_struct a) (is_struct b))))).

Definition RthetaFlagsZero := mkRthetaFlags true false.

Definition Monoid_RthetaFlags : ExtLib.Structures.Monoid.Monoid RthetaFlags := ExtLib.Structures.Monoid.Build_Monoid RthetaFlagsAppend RthetaFlagsZero.

Definition flags_m : Type -> Type := writer Monoid_RthetaFlags.
Context {Writer_flags: MonadWriter Monoid_RthetaFlags flags_m}.
Definition Rtheta := flags_m CarrierA.

Global Instance RthetaFlags_equiv:
  Equiv RthetaFlags :=
  fun a b =>
    is_collision a ≡ is_collision b /\
    is_struct a ≡ is_struct b.

Global Instance RthetaFlags_Reflexive_equiv: Reflexive RthetaFlags_equiv.
Proof.
  unfold Reflexive.
  intros x.
  destruct x.
  unfold equiv, RthetaFlags_equiv.
  auto.
Qed.

Global Instance RthetaFlags_Symmetric_equiv: Symmetric RthetaFlags_equiv.
Proof.
  unfold Symmetric.
  intros x y H.
  destruct x,y.
  unfold equiv, RthetaFlags_equiv in *.
  simpl in *.
  split; crush.
Qed.

Global Instance RthetaFlags_Transitive_equiv: Transitive RthetaFlags_equiv.
Proof.
  unfold Transitive.
  intros x y z H0 H1.
  unfold equiv, RthetaFlags_equiv in *.
  crush.
Qed.

Global Instance RthetaFlags_Equivalence_equiv: Equivalence RthetaFlags_equiv.
Proof.
  split.
  apply RthetaFlags_Reflexive_equiv.
  apply RthetaFlags_Symmetric_equiv.
  apply RthetaFlags_Transitive_equiv.
Qed.

Global Instance RthetaFlags_Setoid: @Setoid RthetaFlags RthetaFlags_equiv.
Proof.
  apply RthetaFlags_Equivalence_equiv.
Qed.

(* Some convenience constructros *)

Definition mkStruct (val: CarrierA) : Rtheta := ret val.

Definition mkSZero := mkStruct 0.

Definition mkValue (val: CarrierA) :=
  tell (mkRthetaFlags false false) ;; ret val.

Global Instance Rtheta_equiv: Equiv (Rtheta) :=
  fun am bm => (evalWriter am) = (evalWriter bm).

Global Instance evalWriter_proper:
  Proper ((=) ==> (=)) (@evalWriter RthetaFlags CarrierA _).
Proof.
  simpl_relation.
Qed.

Ltac unfold_Rtheta_equiv := unfold equiv, Rtheta_equiv in *.

Global Instance Rtheta_Reflexive_equiv: Reflexive Rtheta_equiv.
Proof.
  destruct x; (unfold_Rtheta_equiv; crush).
Qed.

Global Instance Rtheta_Symmetric_equiv: Symmetric Rtheta_equiv.
Proof.
  destruct x; (unfold_Rtheta_equiv; crush).
Qed.

Global Instance Rtheta_Transitive_equiv: Transitive Rtheta_equiv.
Proof.
  destruct x; (unfold_Rtheta_equiv; crush).
Qed.

Global Instance Rtheta_Equivalence_equiv: Equivalence Rtheta_equiv.
Proof.
  split.
  apply Rtheta_Reflexive_equiv.
  apply Rtheta_Symmetric_equiv.
  apply Rtheta_Transitive_equiv.
Qed.

Instance Rtheta_Setoid: Setoid (Rtheta).
Proof.
  apply Rtheta_Equivalence_equiv.
Qed.

(* Note: definitional equality *)
Lemma evalWriter_Rtheta_liftM
      (op: CarrierA -> CarrierA)
      {a: Rtheta}
  :
    evalWriter (liftM op a) ≡ op (evalWriter a).
Proof.
  reflexivity.
Qed.

(* Note: definitional equality *)
Lemma evalWriter_Rtheta_liftM2
      (op: CarrierA -> CarrierA -> CarrierA)
      {a b: Rtheta}
  :
    evalWriter (liftM2 op a b) ≡ op (evalWriter a) (evalWriter b).
Proof.
  reflexivity.
Qed.

Lemma Rtheta_eq_equiv:
  forall (a b: Rtheta), eq a b -> Rtheta_equiv a b.
Proof.
  intros.
  crush.
Qed.

Lemma evalWriter_Rtheta_SZero:
  evalWriter mkSZero = zero.
Proof.
  reflexivity.
Qed.
