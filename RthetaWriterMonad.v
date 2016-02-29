
Require Import Coq.Bool.Bool.
Require Import Ring.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.theory.rings.
Require Import MathClasses.interfaces.orders MathClasses.orders.orders.

Require Import Rtheta.

Require Import CpdtTactics.
Require Import JRWTactics.

Require Import ExtLib.Core.Type.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Data.Monads.WriterMonad.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import WriterMonadNoT.
Require Import ExtLib.Structures.MonadLaws.

Import MonadNotation.
Local Open Scope monad_scope.

Definition Monoid_RthetaFlags : Monoid RthetaFlags := Build_Monoid combineFlags RthetaFlags_normal.

Definition flags_m : Type -> Type := writer Monoid_RthetaFlags.
Context {Writer_flags: MonadWriter Monoid_RthetaFlags flags_m}.

Definition Rtheta_liftM
           (op: Rtheta -> Rtheta)
           (xm: flags_m Rtheta) : flags_m Rtheta :=
  x <- xm ;;
    tell
    (let xs := (is_struct x) in
     (computeFlags xs xs))
    ;;
    ret (op x).

Definition Rtheta_liftM2
           (op: Rtheta -> Rtheta -> Rtheta)
           (am bm: flags_m Rtheta) : flags_m Rtheta :=
  a <- am ;;  b <- bm ;;
    tell (computeFlags (is_struct a) (is_struct b)) ;;
    ret (op a b).


Global Instance Rtheta_Mequiv: Equiv (flags_m Rtheta) :=
  fun am bm => (evalWriter am) = (evalWriter bm).

Ltac unfold_Rtheta_Mequiv := unfold equiv, Rtheta_Mequiv in *.

Instance Rtheta_MSetoid: Setoid (flags_m Rtheta).
Proof.
  split.
  unfold Reflexive. destruct x; (unfold_Rtheta_Mequiv; crush).
  unfold Symmetric. intros. destruct x,y; (unfold_Rtheta_Mequiv; crush).
  unfold Transitive. intros. destruct x,y,z; unfold_Rtheta_Mequiv; crush.
Qed.

Lemma evalWriter_Rtheta_liftM
      (op: Rtheta -> Rtheta)
      {a: flags_m Rtheta}
  :
    evalWriter (Rtheta_liftM op a) ≡ op (evalWriter a).
Proof.
  reflexivity.
Qed.

Lemma evalWriter_lift_Rtheta_liftM2
      (op: Rtheta -> Rtheta -> Rtheta)
      {a b: flags_m Rtheta}
  :
    evalWriter (Rtheta_liftM2 op a b) ≡ op (evalWriter a) (evalWriter b).
Proof.
  reflexivity.
Qed.

Definition Rtheta_evalRel
           (rel: Rtheta -> Rtheta -> Prop)
           (am bm: flags_m Rtheta) : Prop :=
  rel (evalWriter am) (evalWriter bm).


Global Instance Rtheta_MZero: Zero (flags_m Rtheta) := ret (Rtheta_normal zero).
Global Instance Rtheta_MOne: One (flags_m Rtheta) := ret (Rtheta_normal one).
Global Instance Rtheta_MPlus: Plus (flags_m Rtheta) := Rtheta_liftM2 (Rtheta_binop plus).
Global Instance Rtheta_MMult: Mult (flags_m Rtheta) := Rtheta_liftM2 (Rtheta_binop mult).
Global Instance Rtheta_MNeg: Negate (flags_m Rtheta) := Rtheta_liftM (Rtheta_unary negate).
Global Instance Rtheta_MLe: Le (flags_m Rtheta) := Rtheta_evalRel (Rtheta_rel_first le).
Global Instance Rtheta_MLt: Lt (flags_m Rtheta) := Rtheta_evalRel (Rtheta_rel_first lt).

Global Instance Rtheta_Commutative_Rtheta_liftM2
       (op: Rtheta -> Rtheta -> Rtheta)
       `{op_mor: !Proper ((=) ==> (=) ==> (=)) op}
       `{C: !Commutative op}
  :
    @Commutative (flags_m Rtheta) Rtheta_Mequiv (flags_m Rtheta) (Rtheta_liftM2 op).
Proof.
  intros x y.
  unfold_Rtheta_Mequiv.
  rewrite 2!evalWriter_lift_Rtheta_liftM2.
  apply C.
Qed.

Global Program Instance Rtheta_val_Mabs: Abs (flags_m Rtheta) := Rtheta_liftM (Rtheta_unary abs).
Next Obligation.
  unfold_Rtheta_Mequiv.
  rewrite evalWriter_Rtheta_liftM.
  unfold le, Rtheta_Le, Rtheta_rel_first, Rtheta_unary.
  unfold abs; crush.
Qed.

Definition Rtheta_MSZero: flags_m Rtheta := ret Rtheta_SZero.
Definition Rtheta_MSOne: flags_m Rtheta := ret Rtheta_SOne.

Lemma evalWriter_Rtheta_MSZero:
  evalWriter Rtheta_MSZero = Rtheta_SZero.
Proof.
  reflexivity.
Qed.




