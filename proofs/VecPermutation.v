Require Import VecUtil.

Require Import Coq.Arith.Arith.
Require Export Coq.Vectors.Vector.

(* CoLoR *)
Require Export CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

Require Import SpiralTactics.

Section VPermutation.

  Variable A:Type.

  Inductive VPermutation: forall n, vector A n -> vector A n -> Prop :=
  | vperm_nil: VPermutation 0 [] []
  | vperm_skip {n} x l l' : VPermutation n l l' -> VPermutation (S n) (x::l) (x::l')
  | vperm_swap {n} x y l : VPermutation (S (S n)) (y::x::l) (x::y::l)
  | vperm_trans {n} l l' l'' :
      VPermutation n l l' -> VPermutation n l' l'' -> VPermutation n l l''.

  Local Hint Constructors VPermutation.

  (** Some facts about [VPermutation] *)

  Theorem VPermutation_nil : forall (l : vector A 0), VPermutation 0 [] l -> l = [].
  Proof.
    intros l HF.
    dep_destruct l.
    auto.
  Qed.

  (** VPermutation over vectors is a equivalence relation *)

  Theorem VPermutation_refl : forall {n} (l: vector A n), VPermutation n l l.
  Proof.
    induction l; constructor. exact IHl.
  Qed.

  Theorem VPermutation_sym : forall {n} (l l' : vector A n),
      VPermutation n l l' -> VPermutation n l' l.
  Proof.
    intros n l l' Hperm.
    induction Hperm; auto.
    apply vperm_trans with (l'0:=l'); auto.
  Qed.

  Theorem VPermutation_trans : forall {n} (l l' l'' : vector A n),
      VPermutation n l l' -> VPermutation n l' l'' -> VPermutation n l l''.
  Proof.
    intros n l l' l''.
    apply vperm_trans.
  Qed.

End VPermutation.

Hint Resolve VPermutation_refl vperm_nil vperm_skip.
