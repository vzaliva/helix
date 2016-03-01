
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


Global Instance MRtheta_equiv: Equiv (MRtheta) :=
  fun am bm => (evalWriter am) = (evalWriter bm).

Ltac unfold_MRtheta_equiv := unfold equiv, MRtheta_equiv in *.


Global Instance MRtheta_Reflexive_equiv: Reflexive MRtheta_equiv.
Proof.
  destruct x; (unfold_MRtheta_equiv; crush).
Qed.

Global Instance MRtheta_Symmetric_equiv: Symmetric MRtheta_equiv.
Proof.
  destruct x; (unfold_MRtheta_equiv; crush).
Qed.

Global Instance MRtheta_Transitive_equiv: Transitive MRtheta_equiv.
Proof.
  destruct x; (unfold_MRtheta_equiv; crush).
Qed.

Global Instance MRtheta_Equivalence_equiv: Equivalence MRtheta_equiv.
Proof.
  split.
  apply MRtheta_Reflexive_equiv.
  apply MRtheta_Symmetric_equiv.
  apply MRtheta_Transitive_equiv.
Qed.


Instance MRtheta_Setoid: Setoid (MRtheta).
Proof.
  apply MRtheta_Equivalence_equiv.
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


Global Instance MRtheta_Zero: Zero (MRtheta) := ret (Rtheta_normal zero).
Global Instance MRtheta_One: One (MRtheta) := ret (Rtheta_normal one).
Global Instance MRtheta_Plus: Plus (MRtheta) := Rtheta_liftM2 (Rtheta_binop plus).
Global Instance MRtheta_Mult: Mult (MRtheta) := Rtheta_liftM2 (Rtheta_binop mult).
Global Instance MRtheta_Neg: Negate (MRtheta) := Rtheta_liftM (Rtheta_unary negate).
Global Instance MRtheta_Le: Le (MRtheta) := Rtheta_liftRel (Rtheta_rel_first le).
Global Instance MRtheta_Lt: Lt (MRtheta) := Rtheta_liftRel (Rtheta_rel_first lt).

Definition MRtheta_SZero: MRtheta := ret Rtheta_SZero.
Definition MRtheta_SOne: MRtheta := ret Rtheta_SOne.

Lemma evalWriter_MRtheta_SZero:
  evalWriter MRtheta_SZero = Rtheta_SZero.
Proof.
  reflexivity.
Qed.

Global Instance MRtheta_Associative_plus: Associative MRtheta_Plus.
Proof.
  intros x y z.
  unfold_MRtheta_equiv.
  unfold MRtheta_Plus.
  rewrite 4!evalWriter_Rtheta_liftM2.
  apply Rtheta_val_Associative_plus.
Qed.

Global Instance MRtheta_Associative_mult: Associative MRtheta_Mult.
Proof.
  intros x y z.
  unfold_MRtheta_equiv.
  unfold MRtheta_Mult.
  rewrite 4!evalWriter_Rtheta_liftM2.
  apply Rtheta_val_Associative_mult.
Qed.

Global Instance Rtheta_liftM2_proper:
  Proper (((=) ==> (=)) ==> (=) ==> (=) ==> (=)) (Rtheta_liftM2).
Proof.
  simpl_relation.
  rewrite 2!evalWriter_Rtheta_liftM2.
  apply H.
  apply H0.
  apply H1.
Qed.

Global Instance Rtheta_liftM_proper:
  Proper (((=) ==> (=)) ==> (=) ==> (=)) (Rtheta_liftM).
Proof.
  simpl_relation.
  rewrite 2!evalWriter_Rtheta_liftM.
  apply H.
  apply H0.
Qed.

Global Instance MRtheta_plus_proper:
  Proper ((=) ==> (=) ==> (=)) (MRtheta_Plus).
Proof.
  apply Rtheta_liftM2_proper.
  apply Rtheta_val_plus_proper.
Qed.

Global Instance MRtheta_neg_proper:
  Proper ((=) ==> (=)) (MRtheta_Neg).
Proof.
  apply Rtheta_liftM_proper.
  apply Rtheta_val_neg_proper.
Qed.

Global Instance MRtheta_mult_proper:
  Proper ((=) ==> (=) ==> (=)) (MRtheta_Mult).
Proof.
  apply Rtheta_liftM2_proper.
  apply Rtheta_val_mult_proper.
Qed.

Global Instance MRtheta_SemiGroup_plus:
  @SemiGroup (MRtheta) MRtheta_equiv plus.
Proof.
  split.
  apply MRtheta_Setoid.
  apply MRtheta_Associative_plus.
  apply MRtheta_plus_proper.
Qed.

Global Instance MRtheta_LeftIdentity_plus_0:
  @LeftIdentity (MRtheta) (MRtheta) MRtheta_equiv plus zero.
Proof.
  unfold LeftIdentity.
  intros y.
  unfold_MRtheta_equiv.
  unfold plus, MRtheta_Plus.
  rewrite evalWriter_Rtheta_liftM2.
  apply Rtheta_val_LeftIdentity_plus_0.
Qed.

Global Instance MRtheta_RightIdentity_plus_0:
  @RightIdentity (MRtheta) MRtheta_equiv (MRtheta) plus zero.
Proof.
  unfold RightIdentity.
  intros x.
  unfold_MRtheta_equiv.
  unfold plus, MRtheta_Plus.
  rewrite evalWriter_Rtheta_liftM2.
  apply Rtheta_val_RightIdentity_plus_0.
Qed.

(* Note: this is MathClasses monoid, not ExtLib's *)
Global Instance MRtheta_Monoid_plus_0:
  @Monoid (MRtheta) MRtheta_equiv plus zero.
Proof.
  split.
  apply MRtheta_SemiGroup_plus.
  apply MRtheta_LeftIdentity_plus_0.
  apply MRtheta_RightIdentity_plus_0.
Qed.

Global Instance Rtheta_Commutative_Rtheta_liftM2
       (op: Rtheta -> Rtheta -> Rtheta)
       `{op_mor: !Proper ((=) ==> (=) ==> (=)) op}
       `{C: !Commutative op}
  :
    @Commutative (MRtheta) MRtheta_equiv (MRtheta) (Rtheta_liftM2 op).
Proof.
  intros x y.
  unfold_MRtheta_equiv.
  rewrite 2!evalWriter_Rtheta_liftM2.
  apply C.
Qed.

Global Instance MRtheta_Commutative_plus:
  @Commutative (MRtheta) MRtheta_equiv (MRtheta) plus.
Proof.
  unfold Commutative.
  intros x y.
  unfold_MRtheta_equiv.
  unfold plus, MRtheta_Plus.
  rewrite 2!evalWriter_Rtheta_liftM2.
  apply Rtheta_val_Commutative_plus.
Qed.

Global Instance MRtheta_CommutativeMonoid_plus_0:
  @CommutativeMonoid (MRtheta) MRtheta_equiv plus zero.
Proof.
  split.
  apply MRtheta_Monoid_plus_0.
  apply MRtheta_Commutative_plus.
Qed.

Global Instance MRtheta_SemiGroup_mult:
  @SemiGroup (MRtheta) MRtheta_equiv mult.
Proof.
  split.
  apply MRtheta_Setoid.
  apply MRtheta_Associative_mult.
  apply MRtheta_mult_proper.
Qed.

Global Instance MRtheta_LeftIdentity_mult_1:
  @LeftIdentity (MRtheta) (MRtheta) MRtheta_equiv mult one.
Proof.
  unfold LeftIdentity.
  intros y.
  unfold_MRtheta_equiv.
  unfold mult, MRtheta_Mult.
  rewrite evalWriter_Rtheta_liftM2.
  apply Rtheta_val_LeftIdentity_mult_1.
Qed.

Global Instance MRtheta_RightIdentity_mult_1:
  @RightIdentity (MRtheta) MRtheta_equiv (MRtheta) mult one.
Proof.
  unfold RightIdentity.
  intros x.
  unfold_MRtheta_equiv.
  unfold mult, MRtheta_Mult.
  rewrite evalWriter_Rtheta_liftM2.
  apply Rtheta_val_RightIdentity_mult_1.
Qed.

Global Instance MRtheta_Monoid_mult_1:
  @Monoid (MRtheta) MRtheta_equiv mult one.
Proof.
  split.
  apply MRtheta_SemiGroup_mult.
  apply MRtheta_LeftIdentity_mult_1.
  apply MRtheta_RightIdentity_mult_1.
Qed.

Global Instance MRtheta_Commutative_mult:
  @Commutative (MRtheta) MRtheta_equiv (MRtheta) mult.
Proof.
  unfold Commutative.
  intros x y.
  unfold_MRtheta_equiv.
  unfold mult, MRtheta_Mult.
  rewrite 2!evalWriter_Rtheta_liftM2.
  apply Rtheta_val_Commutative_mult.
Qed.

Global Instance MRtheta_LeftDistribute_mult_plus:
  @LeftDistribute (MRtheta) MRtheta_equiv mult plus.
Proof.
  unfold LeftDistribute, LeftHeteroDistribute.
  intros a b c.
  unfold_MRtheta_equiv.
  unfold mult, MRtheta_Mult, plus, MRtheta_Plus.
  rewrite 4!evalWriter_Rtheta_liftM2.
  apply Rtheta_val_LeftDistribute_mult_plus.
Qed.

Global Instance MRtheta_CommutativeMonoid_mult_1:
  @CommutativeMonoid (MRtheta) MRtheta_equiv mult one.
Proof.
  split.
  apply MRtheta_Monoid_mult_1.
  apply MRtheta_Commutative_mult.
Qed.

Global Instance MRtheta_LeftAbsorb:
  @LeftAbsorb (MRtheta) MRtheta_equiv (MRtheta) mult 0.
Proof.
  unfold LeftAbsorb.
  intros y.
  unfold_MRtheta_equiv.
  unfold mult, MRtheta_Mult.
  rewrite evalWriter_Rtheta_liftM2.
  apply Rtheta_val_LeftAbsorb.
Qed.

Global Instance MRtheta_RightAbsorb:
  @RightAbsorb (MRtheta) (MRtheta) MRtheta_equiv mult 0.
Proof.
  unfold RightAbsorb.
  intros x.
  unfold_MRtheta_equiv.
  unfold mult, MRtheta_Mult.
  rewrite evalWriter_Rtheta_liftM2.
  apply Rtheta_val_RightAbsorb.
Qed.

Global Instance MRtheta_SemiRing: SemiRing (MRtheta).
Proof.
  split.
  apply MRtheta_CommutativeMonoid_plus_0.
  apply MRtheta_CommutativeMonoid_mult_1.
  apply MRtheta_LeftDistribute_mult_plus.
  apply MRtheta_LeftAbsorb.
Qed.

Global Instance MRtheta_LeftInverse_plus_neg_0:
  @LeftInverse (MRtheta) (MRtheta) (MRtheta) MRtheta_equiv plus negate 0.
Proof.
  unfold LeftInverse.
  intros x.
  unfold_MRtheta_equiv.
  unfold plus, MRtheta_Plus, negate, Rtheta_Neg.
  rewrite evalWriter_Rtheta_liftM2.
  apply Rtheta_val_LeftInverse_plus_neg_0.
Qed.

Global Instance MRtheta_RightInverse_plus_neg_0:
  @RightInverse (MRtheta) (MRtheta) (MRtheta) MRtheta_equiv plus negate 0.
Proof.
  unfold RightInverse.
  intros x.
  unfold_MRtheta_equiv.
  unfold plus, MRtheta_Plus, negate, Rtheta_Neg.
  rewrite evalWriter_Rtheta_liftM2.
  apply Rtheta_val_RightInverse_plus_neg_0.
Qed.

Global Instance MRtheta_Group_plus_0_neg:
  @Group (MRtheta) MRtheta_equiv MRtheta_Plus MRtheta_Zero MRtheta_Neg.
Proof.
  split.
  apply MRtheta_Monoid_plus_0.
  split.
  apply MRtheta_Setoid.
  apply MRtheta_Setoid.
  apply MRtheta_neg_proper.
  apply MRtheta_LeftInverse_plus_neg_0.
  apply MRtheta_RightInverse_plus_neg_0.
Qed.

Global Instance MRtheta_Ring: Ring MRtheta.
Proof.
  split. split.
  apply MRtheta_Group_plus_0_neg.
  apply MRtheta_Commutative_plus.
  apply MRtheta_CommutativeMonoid_mult_1.
  apply MRtheta_LeftDistribute_mult_plus.
Qed.

Global Instance MRtheta_ledec (x y: MRtheta): Decision (x ≤ y) :=
  Rtheta_val_ledec (evalWriter x) (evalWriter y).

Global Instance MRtheta_ltdec (x y: MRtheta): Decision (x < y) :=
  Rtheta_val_ltdec (evalWriter x) (evalWriter y).

Global Program Instance MRtheta_abs: Abs (MRtheta) := Rtheta_liftM (Rtheta_unary abs).
Next Obligation.
  unfold_MRtheta_equiv.
  rewrite evalWriter_Rtheta_liftM.
  unfold le, Rtheta_Le, Rtheta_rel_first, Rtheta_unary.
  unfold abs; crush.
Qed.

Global Instance Rtheta_liftRel_proper:
  Proper (((=) ==> (=) ==> (iff)) ==> (MRtheta_equiv) ==> (MRtheta_equiv) ==> (iff))
         (Rtheta_liftRel).
Proof.
  simpl_relation.
  unfold Rtheta_liftRel.
  apply H.
  apply H0.
  apply H1.
Qed.

Global Instance MRtheta_le_proper:
  Proper ((=) ==> (=) ==> (iff)) (MRtheta_Le).
Proof.
  unfold MRtheta_Le, Rtheta_rel_first.
  apply Rtheta_liftRel_proper.
  apply Rtheta_val_le_proper.
Qed.

Global Instance MRtheta_lt_proper:
  Proper ((=) ==> (=) ==> (iff)) (MRtheta_Lt).
Proof.
  unfold MRtheta_Lt, Rtheta_rel_first.
  apply Rtheta_liftRel_proper.
  apply Rtheta_val_lt_proper.
Qed.

Global Instance MRtheta_le_Reflexive:
  @Reflexive (MRtheta) le.
Proof.
  unfold Reflexive.
  intros x.
  unfold le, MRtheta_Le, Rtheta_liftRel.
  apply Rtheta_val_le_Reflexive.
Qed.

Global Instance MRtheta_le_Transitive:
  @Transitive (MRtheta) le.
Proof.
  unfold Transitive.
  intros x y z.
  unfold le, MRtheta_Le, Rtheta_liftRel.
  apply Rtheta_val_le_Transitive.
Qed.

Global Instance MRtheta_le_AntiSymmetric:
  @AntiSymmetric MRtheta MRtheta_equiv le.
Proof.
  unfold AntiSymmetric.
  intros x y.
  unfold le, MRtheta_Le, Rtheta_liftRel.
  apply Rtheta_val_le_AntiSymmetric.
Qed.

Global Instance MRtheta_le_PreOrder:
  @PreOrder MRtheta le.
Proof.
  split.
  apply MRtheta_le_Reflexive.
  apply MRtheta_le_Transitive.
Qed.

Global Instance MRtheta_le_PartialOrder:
  @PartialOrder MRtheta MRtheta_equiv MRtheta_Le.
Proof.
  split.
  apply MRtheta_Setoid.
  apply MRtheta_le_proper.
  apply MRtheta_le_PreOrder.
  apply MRtheta_le_AntiSymmetric.
Qed.

Global Instance MRtheta_le_TotalRelation:
  @TotalRelation MRtheta le.
Proof.
  unfold TotalRelation.
  intros x y.
  unfold le, MRtheta_Le, Rtheta_liftRel.
  apply Rtheta_val_le_TotalRelation.
Qed.

Global Instance MRtheta_TotalOrder:
  TotalOrder MRtheta_Le.
Proof.
  split.
  apply MRtheta_le_PartialOrder.
  apply MRtheta_le_TotalRelation.
Qed.

Global Instance MRtheta_plus_Order_Morphism:
  ∀ (z : MRtheta), Order_Morphism (plus z).
Proof.
  split.
  split.
  apply MRtheta_Setoid.
  apply MRtheta_Setoid.
  apply MRtheta_plus_proper.
  reflexivity.
  apply MRtheta_le_PartialOrder.
  apply MRtheta_le_PartialOrder.
Qed.

Lemma MRtheta_le_plus_lemma1:
  ∀ z x y : MRtheta, x ≤ y <-> z + x ≤ z + y.
Proof.
  intros z x y.
  unfold le, MRtheta_Le, Rtheta_liftRel.
  apply Rtheta_val_le_plus_lemma1.
Qed.

Global Instance MRtheta_plus_OrderPreserving:
  ∀ (z : MRtheta), OrderPreserving (plus z).
Proof.
  split.
  apply MRtheta_plus_Order_Morphism.
  apply MRtheta_le_plus_lemma1.
Qed.

Global Instance MRtheta_plus_OrderReflecting:
  ∀ (z : MRtheta), OrderReflecting (plus z).
Proof.
  split.
  apply MRtheta_plus_Order_Morphism.
  apply MRtheta_le_plus_lemma1.
Qed.

Global Instance MRtheta_plus_OrderEmbedding:
  ∀ (z : MRtheta), OrderEmbedding (plus z).
Proof.
  intros.
  split.
  apply MRtheta_plus_OrderPreserving.
  apply MRtheta_plus_OrderReflecting.
Qed.

Global Instance MRtheta_SemiRingOrder:
  SemiRingOrder MRtheta_Le.
Proof.
  split.
  - apply total_order_po.
  - apply MRtheta_SemiRing.
  -
    intros x y.
    exists (y-x).
    unfold_MRtheta_equiv.
    unfold plus, MRtheta_Plus, negate, MRtheta_Neg.
    rewrite 2!evalWriter_Rtheta_liftM2, evalWriter_Rtheta_liftM.
    unfold le, MRtheta_Le, Rtheta_liftRel,Rtheta_rel_first in H.
    apply Rtheta_val_SemiRingOrder, CarrierASRO.
    simpl in *.
    ring.
  - apply MRtheta_plus_OrderEmbedding.
  - intros x y.
    unfold le, MRtheta_Le, Rtheta_liftRel, Rtheta_rel_first.
    apply CarrierASRO.
Qed.

Lemma MRtheta_eq_equiv:
  forall (a b: MRtheta), eq a b -> MRtheta_equiv a b.
Proof.
  intros.
  crush.
Qed.

