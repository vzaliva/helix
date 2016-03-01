
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

Require Import Rtheta.

Require Import CpdtTactics.
Require Import JRWTactics.


Import MonadNotation.
Local Open Scope monad_scope.

Definition Monoid_RthetaFlags : ExtLib.Structures.Monoid.Monoid RthetaFlags := ExtLib.Structures.Monoid.Build_Monoid combineFlags RthetaFlags_normal.

Definition flags_m : Type -> Type := writer Monoid_RthetaFlags.
Context {Writer_flags: MonadWriter Monoid_RthetaFlags flags_m}.
Definition MRtheta := flags_m Rtheta.

Definition Rtheta_liftM
           (op: Rtheta -> Rtheta)
           (xm: MRtheta) : MRtheta :=
  x <- xm ;;
    tell
    (let xs := (is_struct x) in
     (computeFlags xs xs))
    ;;
    ret (op x).

Definition Rtheta_liftM2
           (op: Rtheta -> Rtheta -> Rtheta)
           (am bm: MRtheta) : MRtheta :=
  a <- am ;;  b <- bm ;;
    tell (computeFlags (is_struct a) (is_struct b)) ;;
    ret (op a b).


Global Instance Rtheta_Mequiv: Equiv (MRtheta) :=
  fun am bm => (evalWriter am) = (evalWriter bm).

Ltac unfold_Rtheta_Mequiv := unfold equiv, Rtheta_Mequiv in *.


Global Instance Rtheta_Reflexive_Mequiv: Reflexive Rtheta_Mequiv.
Proof.
  destruct x; (unfold_Rtheta_Mequiv; crush).
Qed.

Global Instance Rtheta_Symmetric_Mequiv: Symmetric Rtheta_Mequiv.
Proof.
  destruct x; (unfold_Rtheta_Mequiv; crush).
Qed.

Global Instance Rtheta_Transitive_Mequiv: Transitive Rtheta_Mequiv.
Proof.
  destruct x; (unfold_Rtheta_Mequiv; crush).
Qed.

Global Instance Rtheta_Equivalence_Mequiv: Equivalence Rtheta_Mequiv.
Proof.
  split.
  apply Rtheta_Reflexive_Mequiv.
  apply Rtheta_Symmetric_Mequiv.
  apply Rtheta_Transitive_Mequiv.
Qed.


Instance Rtheta_MSetoid: Setoid (MRtheta).
Proof.
  apply Rtheta_Equivalence_Mequiv.
Qed.

(* Note: definitional equality *)
Lemma evalWriter_Rtheta_liftM
      (op: Rtheta -> Rtheta)
      {a: MRtheta}
  :
    evalWriter (Rtheta_liftM op a) ≡ op (evalWriter a).
Proof.
  reflexivity.
Qed.

(* Note: definitional equality *)
Lemma evalWriter_Rtheta_liftM2
      (op: Rtheta -> Rtheta -> Rtheta)
      {a b: MRtheta}
  :
    evalWriter (Rtheta_liftM2 op a b) ≡ op (evalWriter a) (evalWriter b).
Proof.
  reflexivity.
Qed.

Definition Rtheta_liftRel
           (rel: Rtheta -> Rtheta -> Prop)
           (am bm: MRtheta) : Prop :=
  rel (evalWriter am) (evalWriter bm).


Global Instance Rtheta_MZero: Zero (MRtheta) := ret (Rtheta_normal zero).
Global Instance Rtheta_MOne: One (MRtheta) := ret (Rtheta_normal one).
Global Instance Rtheta_MPlus: Plus (MRtheta) := Rtheta_liftM2 (Rtheta_binop plus).
Global Instance Rtheta_MMult: Mult (MRtheta) := Rtheta_liftM2 (Rtheta_binop mult).
Global Instance Rtheta_MNeg: Negate (MRtheta) := Rtheta_liftM (Rtheta_unary negate).
Global Instance Rtheta_MLe: Le (MRtheta) := Rtheta_liftRel (Rtheta_rel_first le).
Global Instance Rtheta_MLt: Lt (MRtheta) := Rtheta_liftRel (Rtheta_rel_first lt).

Definition Rtheta_MSZero: MRtheta := ret Rtheta_SZero.
Definition Rtheta_MSOne: MRtheta := ret Rtheta_SOne.

Lemma evalWriter_Rtheta_MSZero:
  evalWriter Rtheta_MSZero = Rtheta_SZero.
Proof.
  reflexivity.
Qed.

Global Instance Rtheta_Associative_Mplus: Associative Rtheta_MPlus.
Proof.
  intros x y z.
  unfold_Rtheta_Mequiv.
  unfold Rtheta_MPlus.
  rewrite 4!evalWriter_Rtheta_liftM2.
  apply Rtheta_val_Associative_plus.
Qed.

Global Instance Rtheta_Associative_Mmult: Associative Rtheta_MMult.
Proof.
  intros x y z.
  unfold_Rtheta_Mequiv.
  unfold Rtheta_MMult.
  rewrite 4!evalWriter_Rtheta_liftM2.
  apply Rtheta_val_Associative_mult.
Qed.

Global Instance Rtheta_liftM2_proper:
  Proper (((=) ==> (=)) ==> (Rtheta_Mequiv) ==> (Rtheta_Mequiv) ==> (Rtheta_Mequiv)) (Rtheta_liftM2).
Proof.
  simpl_relation.
  rewrite 2!evalWriter_Rtheta_liftM2.
  apply H.
  apply H0.
  apply H1.
Qed.

Global Instance Rtheta_liftM_proper:
  Proper (((=) ==> (=)) ==> (Rtheta_Mequiv) ==> (Rtheta_Mequiv)) (Rtheta_liftM).
Proof.
  simpl_relation.
  rewrite 2!evalWriter_Rtheta_liftM.
  apply H.
  apply H0.
Qed.

Global Instance Rtheta_Mplus_proper:
  Proper ((=) ==> (=) ==> (=)) (Rtheta_MPlus).
Proof.
  apply Rtheta_liftM2_proper.
  apply Rtheta_val_plus_proper.
Qed.

Global Instance Rtheta_Mneg_proper:
  Proper ((=) ==> (=)) (Rtheta_MNeg).
Proof.
  apply Rtheta_liftM_proper.
  apply Rtheta_val_neg_proper.
Qed.

Global Instance Rtheta_Mmult_proper:
  Proper ((=) ==> (=) ==> (=)) (Rtheta_MMult).
Proof.
  apply Rtheta_liftM2_proper.
  apply Rtheta_val_mult_proper.
Qed.

Global Instance Rtheta_SemiGroup_Mplus:
  @SemiGroup (MRtheta) Rtheta_Mequiv plus.
Proof.
  split.
  apply Rtheta_MSetoid.
  apply Rtheta_Associative_Mplus.
  apply Rtheta_Mplus_proper.
Qed.

Global Instance Rtheta_LeftIdentity_Mplus_0:
  @LeftIdentity (MRtheta) (MRtheta) Rtheta_Mequiv plus zero.
Proof.
  unfold LeftIdentity.
  intros y.
  unfold_Rtheta_Mequiv.
  unfold plus, Rtheta_MPlus.
  rewrite evalWriter_Rtheta_liftM2.
  apply Rtheta_val_LeftIdentity_plus_0.
Qed.

Global Instance Rtheta_RightIdentity_Mplus_0:
  @RightIdentity (MRtheta) Rtheta_Mequiv (MRtheta) plus zero.
Proof.
  unfold RightIdentity.
  intros x.
  unfold_Rtheta_Mequiv.
  unfold plus, Rtheta_MPlus.
  rewrite evalWriter_Rtheta_liftM2.
  apply Rtheta_val_RightIdentity_plus_0.
Qed.

(* Note: this is MathClasses monoid, not ExtLib's *)
Global Instance Rtheta_Monoid_Mplus_0:
  @Monoid (MRtheta) Rtheta_Mequiv plus zero.
Proof.
  split.
  apply Rtheta_SemiGroup_Mplus.
  apply Rtheta_LeftIdentity_Mplus_0.
  apply Rtheta_RightIdentity_Mplus_0.
Qed.


Global Instance Rtheta_Commutative_Rtheta_liftM2
       (op: Rtheta -> Rtheta -> Rtheta)
       `{op_mor: !Proper ((=) ==> (=) ==> (=)) op}
       `{C: !Commutative op}
  :
    @Commutative (MRtheta) Rtheta_Mequiv (MRtheta) (Rtheta_liftM2 op).
Proof.
  intros x y.
  unfold_Rtheta_Mequiv.
  rewrite 2!evalWriter_Rtheta_liftM2.
  apply C.
Qed.

Global Instance Rtheta_Commutative_Mplus:
  @Commutative (MRtheta) Rtheta_Mequiv (MRtheta) plus.
Proof.
  unfold Commutative.
  intros x y.
  unfold_Rtheta_Mequiv.
  unfold plus, Rtheta_MPlus.
  rewrite 2!evalWriter_Rtheta_liftM2.
  apply Rtheta_val_Commutative_plus.
Qed.

Global Instance Rtheta_CommutativeMonoid_Mplus_0:
  @CommutativeMonoid (MRtheta) Rtheta_Mequiv plus zero.
Proof.
  split.
  apply Rtheta_Monoid_Mplus_0.
  apply Rtheta_Commutative_Mplus.
Qed.

Global Instance Rtheta_SemiGroup_Mmult:
  @SemiGroup (MRtheta) Rtheta_Mequiv mult.
Proof.
  split.
  apply Rtheta_MSetoid.
  apply Rtheta_Associative_Mmult.
  apply Rtheta_Mmult_proper.
Qed.

Global Instance Rtheta_LeftIdentity_Mmult_1:
  @LeftIdentity (MRtheta) (MRtheta) Rtheta_Mequiv mult one.
Proof.
  unfold LeftIdentity.
  intros y.
  unfold_Rtheta_Mequiv.
  unfold mult, Rtheta_MMult.
  rewrite evalWriter_Rtheta_liftM2.
  apply Rtheta_val_LeftIdentity_mult_1.
Qed.

Global Instance Rtheta_RightIdentity_Mmult_1:
  @RightIdentity (MRtheta) Rtheta_Mequiv (MRtheta) mult one.
Proof.
  unfold RightIdentity.
  intros x.
  unfold_Rtheta_Mequiv.
  unfold mult, Rtheta_MMult.
  rewrite evalWriter_Rtheta_liftM2.
  apply Rtheta_val_RightIdentity_mult_1.
Qed.

Global Instance Rtheta_Monoid_Mmult_1:
  @Monoid (MRtheta) Rtheta_Mequiv mult one.
Proof.
  split.
  apply Rtheta_SemiGroup_Mmult.
  apply Rtheta_LeftIdentity_Mmult_1.
  apply Rtheta_RightIdentity_Mmult_1.
Qed.

Global Instance Rtheta_Commutative_Mmult:
  @Commutative (MRtheta) Rtheta_Mequiv (MRtheta) mult.
Proof.
  unfold Commutative.
  intros x y.
  unfold_Rtheta_Mequiv.
  unfold mult, Rtheta_MMult.
  rewrite 2!evalWriter_Rtheta_liftM2.
  apply Rtheta_val_Commutative_mult.
Qed.

Global Instance Rtheta_LeftDistribute_Mmult_Mplus:
  @LeftDistribute (MRtheta) Rtheta_Mequiv mult plus.
Proof.
  unfold LeftDistribute, LeftHeteroDistribute.
  intros a b c.
  unfold_Rtheta_Mequiv.
  unfold mult, Rtheta_MMult, plus, Rtheta_MPlus.
  rewrite 4!evalWriter_Rtheta_liftM2.
  apply Rtheta_val_LeftDistribute_mult_plus.
Qed.

Global Instance Rtheta_CommutativeMonoid_Mmult_1:
  @CommutativeMonoid (MRtheta) Rtheta_Mequiv mult one.
Proof.
  split.
  apply Rtheta_Monoid_Mmult_1.
  apply Rtheta_Commutative_Mmult.
Qed.

Global Instance Rtheta_MLeftAbsorb:
  @LeftAbsorb (MRtheta) Rtheta_Mequiv (MRtheta) mult 0.
Proof.
  unfold LeftAbsorb.
  intros y.
  unfold_Rtheta_Mequiv.
  unfold mult, Rtheta_MMult.
  rewrite evalWriter_Rtheta_liftM2.
  apply Rtheta_val_LeftAbsorb.
Qed.

Global Instance Rtheta_MRightAbsorb:
  @RightAbsorb (MRtheta) (MRtheta) Rtheta_Mequiv mult 0.
Proof.
  unfold RightAbsorb.
  intros x.
  unfold_Rtheta_Mequiv.
  unfold mult, Rtheta_MMult.
  rewrite evalWriter_Rtheta_liftM2.
  apply Rtheta_val_RightAbsorb.
Qed.

Global Instance Rtheta_MSemiRing: SemiRing (MRtheta).
Proof.
  split.
  apply Rtheta_CommutativeMonoid_Mplus_0.
  apply Rtheta_CommutativeMonoid_Mmult_1.
  apply Rtheta_LeftDistribute_Mmult_Mplus.
  apply Rtheta_MLeftAbsorb.
Qed.

Global Instance Rtheta_LeftInverse_Mplus_neg_0:
  @LeftInverse (MRtheta) (MRtheta) (MRtheta) Rtheta_Mequiv plus negate 0.
Proof.
  unfold LeftInverse.
  intros x.
  unfold_Rtheta_Mequiv.
  unfold plus, Rtheta_MPlus, negate, Rtheta_Neg.
  rewrite evalWriter_Rtheta_liftM2.
  apply Rtheta_val_LeftInverse_plus_neg_0.
Qed.

Global Instance Rtheta_RightInverse_Mplus_neg_0:
  @RightInverse (MRtheta) (MRtheta) (MRtheta) Rtheta_Mequiv plus negate 0.
Proof.
  unfold RightInverse.
  intros x.
  unfold_Rtheta_Mequiv.
  unfold plus, Rtheta_MPlus, negate, Rtheta_Neg.
  rewrite evalWriter_Rtheta_liftM2.
  apply Rtheta_val_RightInverse_plus_neg_0.
Qed.

Global Instance Rtheta_Group_Mplus_0_neg:
  @Group (MRtheta) Rtheta_Mequiv Rtheta_MPlus Rtheta_MZero Rtheta_MNeg.
Proof.
  split.
  apply Rtheta_Monoid_Mplus_0.
  split.
  apply Rtheta_MSetoid.
  apply Rtheta_MSetoid.
  apply Rtheta_Mneg_proper.
  apply Rtheta_LeftInverse_Mplus_neg_0.
  apply Rtheta_RightInverse_Mplus_neg_0.
Qed.

Global Instance Ring_MRtheta: Ring (MRtheta).
Proof.
  split. split.
  apply Rtheta_Group_Mplus_0_neg.
  apply Rtheta_Commutative_Mplus.
  apply Rtheta_CommutativeMonoid_Mmult_1.
  apply Rtheta_LeftDistribute_Mmult_Mplus.
Qed.

Global Instance Rtheta_Mledec (x y: MRtheta): Decision (x ≤ y) :=
  Rtheta_val_ledec (evalWriter x) (evalWriter y).

Global Instance Rtheta_Mltdec (x y: MRtheta): Decision (x < y) :=
  Rtheta_val_ltdec (evalWriter x) (evalWriter y).

Global Program Instance Rtheta_Mabs: Abs (MRtheta) := Rtheta_liftM (Rtheta_unary abs).
Next Obligation.
  unfold_Rtheta_Mequiv.
  rewrite evalWriter_Rtheta_liftM.
  unfold le, Rtheta_Le, Rtheta_rel_first, Rtheta_unary.
  unfold abs; crush.
Qed.


Global Instance Rtheta_liftRel_proper:
  Proper (((=) ==> (=) ==> (iff)) ==> (Rtheta_Mequiv) ==> (Rtheta_Mequiv) ==> (iff))
         (Rtheta_liftRel).
Proof.
  simpl_relation.
  unfold Rtheta_liftRel.
  apply H.
  apply H0.
  apply H1.
Qed.

Global Instance Rtheta_Mle_proper:
  Proper ((=) ==> (=) ==> (iff)) (Rtheta_MLe).
Proof.
  unfold Rtheta_MLe, Rtheta_rel_first.
  apply Rtheta_liftRel_proper.
  apply Rtheta_val_le_proper.
Qed.

Global Instance Rtheta_Mlt_proper:
  Proper ((=) ==> (=) ==> (iff)) (Rtheta_MLt).
Proof.
  unfold Rtheta_MLt, Rtheta_rel_first.
  apply Rtheta_liftRel_proper.
  apply Rtheta_val_lt_proper.
Qed.

Global Instance Rtheta_Mle_Reflexive:
  @Reflexive (MRtheta) le.
Proof.
  unfold Reflexive.
  intros x.
  unfold le, Rtheta_MLe, Rtheta_liftRel.
  apply Rtheta_val_le_Reflexive.
Qed.

Global Instance Rtheta_Mle_Transitive:
  @Transitive (MRtheta) le.
Proof.
  unfold Transitive.
  intros x y z.
  unfold le, Rtheta_MLe, Rtheta_liftRel.
  apply Rtheta_val_le_Transitive.
Qed.

Global Instance Rtheta_Mle_AntiSymmetric:
  @AntiSymmetric MRtheta Rtheta_Mequiv le.
Proof.
  unfold AntiSymmetric.
  intros x y.
  unfold le, Rtheta_MLe, Rtheta_liftRel.
  apply Rtheta_val_le_AntiSymmetric.
Qed.

Global Instance Rtheta_Mle_PreOrder:
  @PreOrder MRtheta le.
Proof.
  split.
  apply Rtheta_Mle_Reflexive.
  apply Rtheta_Mle_Transitive.
Qed.

Global Instance Rtheta_Mle_PartialOrder:
  @PartialOrder MRtheta Rtheta_Mequiv Rtheta_MLe.
Proof.
  split.
  apply Rtheta_MSetoid.
  apply Rtheta_Mle_proper.
  apply Rtheta_Mle_PreOrder.
  apply Rtheta_Mle_AntiSymmetric.
Qed.

Global Instance Rtheta_Mle_TotalRelation:
  @TotalRelation MRtheta le.
Proof.
  unfold TotalRelation.
  intros x y.
  unfold le, Rtheta_MLe, Rtheta_liftRel.
  apply Rtheta_val_le_TotalRelation.
Qed.

Global Instance Rtheta_MTotalOrder:
  TotalOrder Rtheta_MLe.
Proof.
  split.
  apply Rtheta_Mle_PartialOrder.
  apply Rtheta_Mle_TotalRelation.
Qed.

Global Instance Rtheta_Mplus_Order_Morphism:
  ∀ (z : MRtheta), Order_Morphism (plus z).
Proof.
  split.
  split.
  apply Rtheta_MSetoid.
  apply Rtheta_MSetoid.
  apply Rtheta_Mplus_proper.
  reflexivity.
  apply Rtheta_Mle_PartialOrder.
  apply Rtheta_Mle_PartialOrder.
Qed.

Lemma Rtheta_Mle_plus_lemma1:
  ∀ z x y : MRtheta, x ≤ y <-> z + x ≤ z + y.
Proof.
  intros z x y.
  unfold le, Rtheta_MLe, Rtheta_liftRel.
  apply Rtheta_val_le_plus_lemma1.
Qed.

Global Instance Rtheta_Mplus_OrderPreserving:
  ∀ (z : MRtheta), OrderPreserving (plus z).
Proof.
  split.
  apply Rtheta_Mplus_Order_Morphism.
  apply Rtheta_Mle_plus_lemma1.
Qed.

Global Instance Rtheta_Mplus_OrderReflecting:
  ∀ (z : MRtheta), OrderReflecting (plus z).
Proof.
  split.
  apply Rtheta_Mplus_Order_Morphism.
  apply Rtheta_Mle_plus_lemma1.
Qed.

Global Instance Rtheta_Mplus_OrderEmbedding:
  ∀ (z : MRtheta), OrderEmbedding (plus z).
Proof.
  intros.
  split.
  apply Rtheta_Mplus_OrderPreserving.
  apply Rtheta_Mplus_OrderReflecting.
Qed.

Global Instance Rtheta_MSemiRingOrder:
  SemiRingOrder Rtheta_MLe.
Proof.
  split.
  - apply total_order_po.
  - apply Rtheta_MSemiRing.
  -
    intros x y.
    exists (y-x).
    unfold_Rtheta_Mequiv.
    unfold plus, Rtheta_MPlus, negate, Rtheta_MNeg.
    rewrite 2!evalWriter_Rtheta_liftM2, evalWriter_Rtheta_liftM.
    unfold le, Rtheta_MLe, Rtheta_liftRel,Rtheta_rel_first in H.
    apply Rtheta_val_SemiRingOrder, CarrierASRO.
    simpl in *.
    ring.
  - apply Rtheta_Mplus_OrderEmbedding.
  - intros x y.
    unfold le, Rtheta_MLe, Rtheta_liftRel,Rtheta_rel_first.
    apply CarrierASRO.
Qed.

Lemma Rtheta_eq_Mequiv:
  forall (a b: MRtheta), eq a b -> Rtheta_Mequiv a b.
Proof.
  intros.
  crush.
Qed.

