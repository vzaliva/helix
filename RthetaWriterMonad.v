
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


Instance Rtheta_MSetoid: Setoid (flags_m Rtheta).
Proof.
  apply Rtheta_Equivalence_Mequiv.
Qed.

(* Note: definitional equality *)
Lemma evalWriter_Rtheta_liftM
      (op: Rtheta -> Rtheta)
      {a: flags_m Rtheta}
  :
    evalWriter (Rtheta_liftM op a) ≡ op (evalWriter a).
Proof.
  reflexivity.
Qed.

(* Note: definitional equality *)
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

Definition Rtheta_MSZero: flags_m Rtheta := ret Rtheta_SZero.
Definition Rtheta_MSOne: flags_m Rtheta := ret Rtheta_SOne.

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
  rewrite 4!evalWriter_lift_Rtheta_liftM2.
  apply Rtheta_val_Associative_plus.
Qed.

Global Instance Rtheta_Associative_Mmult: Associative Rtheta_MMult.
Proof.
  intros x y z.
  unfold_Rtheta_Mequiv.
  unfold Rtheta_MMult.
  rewrite 4!evalWriter_lift_Rtheta_liftM2.
  apply Rtheta_val_Associative_mult.
Qed.

Global Instance Rtheta_liftM2_proper:
  Proper (((=) ==> (=)) ==> (Rtheta_Mequiv) ==> (Rtheta_Mequiv) ==> (Rtheta_Mequiv)) (Rtheta_liftM2).
Proof.
  simpl_relation.
  rewrite 2!evalWriter_lift_Rtheta_liftM2.
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
    @SemiGroup (flags_m Rtheta) Rtheta_Mequiv plus.
  Proof.
    split.
    apply Rtheta_MSetoid.
    apply Rtheta_Associative_Mplus.
    apply Rtheta_Mplus_proper.
  Qed.

  Global Instance Rtheta_LeftIdentity_Mplus_0:
    @LeftIdentity (flags_m Rtheta) (flags_m Rtheta) Rtheta_Mequiv plus zero.
  Proof.
    unfold LeftIdentity.
    intros y.
    unfold_Rtheta_Mequiv.
    unfold plus, Rtheta_MPlus.
    rewrite evalWriter_lift_Rtheta_liftM2.
    apply Rtheta_val_LeftIdentity_plus_0.
  Qed.

  Global Instance Rtheta_RightIdentity_Mplus_0:
    @RightIdentity (flags_m Rtheta) Rtheta_Mequiv (flags_m Rtheta) plus zero.
  Proof.
    unfold RightIdentity.
    intros x.
    unfold_Rtheta_Mequiv.
    unfold plus, Rtheta_MPlus.
    rewrite evalWriter_lift_Rtheta_liftM2.
    apply Rtheta_val_RightIdentity_plus_0.
  Qed.

  (* Note: this is MathClasses monoid, not ExtLib's *)
  Global Instance Rtheta_Monoid_Mplus_0:
    @Monoid (flags_m Rtheta) Rtheta_Mequiv plus zero.
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
      @Commutative (flags_m Rtheta) Rtheta_Mequiv (flags_m Rtheta) (Rtheta_liftM2 op).
  Proof.
    intros x y.
    unfold_Rtheta_Mequiv.
    rewrite 2!evalWriter_lift_Rtheta_liftM2.
    apply C.
  Qed.

  Global Instance Rtheta_Commutative_Mplus:
    @Commutative (flags_m Rtheta) Rtheta_Mequiv (flags_m Rtheta) plus.
  Proof.
    unfold Commutative.
    intros x y.
    unfold_Rtheta_Mequiv.
    unfold plus, Rtheta_MPlus.
    rewrite 2!evalWriter_lift_Rtheta_liftM2.
    apply Rtheta_val_Commutative_plus.
  Qed.

  Global Instance Rtheta_CommutativeMonoid_Mplus_0:
    @CommutativeMonoid (flags_m Rtheta) Rtheta_Mequiv plus zero.
  Proof.
    split.
    apply Rtheta_Monoid_Mplus_0.
    apply Rtheta_Commutative_Mplus.
  Qed.

  Global Instance Rtheta_SemiGroup_Mmult:
    @SemiGroup (flags_m Rtheta) Rtheta_Mequiv mult.
  Proof.
    split.
    apply Rtheta_MSetoid.
    apply Rtheta_Associative_Mmult.
    apply Rtheta_Mmult_proper.
  Qed.

  Global Instance Rtheta_LeftIdentity_Mmult_1:
    @LeftIdentity (flags_m Rtheta) (flags_m Rtheta) Rtheta_Mequiv mult one.
  Proof.
    unfold LeftIdentity.
    intros y.
    unfold_Rtheta_Mequiv.
    unfold mult, Rtheta_MMult.
    rewrite evalWriter_lift_Rtheta_liftM2.
    apply Rtheta_val_LeftIdentity_mult_1.
  Qed.

  Global Instance Rtheta_RightIdentity_Mmult_1:
    @RightIdentity (flags_m Rtheta) Rtheta_Mequiv (flags_m Rtheta) mult one.
  Proof.
    unfold RightIdentity.
    intros x.
    unfold_Rtheta_Mequiv.
    unfold mult, Rtheta_MMult.
    rewrite evalWriter_lift_Rtheta_liftM2.
    apply Rtheta_val_RightIdentity_mult_1.    
  Qed.

  Global Instance Rtheta_Monoid_Mmult_1:
    @Monoid (flags_m Rtheta) Rtheta_Mequiv mult one.
  Proof.
    split.
    apply Rtheta_SemiGroup_Mmult.
    apply Rtheta_LeftIdentity_Mmult_1.
    apply Rtheta_RightIdentity_Mmult_1.
  Qed.

  Global Instance Rtheta_Commutative_Mmult:
    @Commutative (flags_m Rtheta) Rtheta_Mequiv (flags_m Rtheta) mult.
  Proof.
    unfold Commutative.
    intros x y.
    unfold_Rtheta_Mequiv.
    unfold mult, Rtheta_MMult.
    rewrite 2!evalWriter_lift_Rtheta_liftM2.
    apply Rtheta_val_Commutative_mult.
  Qed.

  Global Instance Rtheta_LeftDistribute_Mmult_Mplus:
    @LeftDistribute (flags_m Rtheta) Rtheta_Mequiv mult plus.
  Proof.
    unfold LeftDistribute, LeftHeteroDistribute.
    intros a b c.
    unfold_Rtheta_Mequiv.
    unfold mult, Rtheta_MMult, plus, Rtheta_MPlus.
    rewrite 4!evalWriter_lift_Rtheta_liftM2.
    apply Rtheta_val_LeftDistribute_mult_plus.    
  Qed.

  Global Instance Rtheta_CommutativeMonoid_Mmult_1:
    @CommutativeMonoid (flags_m Rtheta) Rtheta_Mequiv mult one.
  Proof.
    split.
    apply Rtheta_Monoid_Mmult_1.
    apply Rtheta_Commutative_Mmult.
  Qed.

  Global Instance Rtheta_MLeftAbsorb:
    @LeftAbsorb (flags_m Rtheta) Rtheta_Mequiv (flags_m Rtheta) mult 0.
  Proof.
    unfold LeftAbsorb.
    intros y.
    unfold_Rtheta_Mequiv.
    unfold mult, Rtheta_MMult.
    rewrite evalWriter_lift_Rtheta_liftM2.
    apply Rtheta_val_LeftAbsorb.
  Qed.

  Global Instance Rtheta_MRightAbsorb:
    @RightAbsorb (flags_m Rtheta) (flags_m Rtheta) Rtheta_Mequiv mult 0.
  Proof.
    unfold RightAbsorb.
    intros x.
    unfold_Rtheta_Mequiv.
    unfold mult, Rtheta_MMult.
    rewrite evalWriter_lift_Rtheta_liftM2.
    apply Rtheta_val_RightAbsorb.
  Qed.

  Global Instance Rtheta_MSemiRing: SemiRing (flags_m Rtheta).
  Proof.
    split.
    apply Rtheta_CommutativeMonoid_Mplus_0.
    apply Rtheta_CommutativeMonoid_Mmult_1.
    apply Rtheta_LeftDistribute_Mmult_Mplus.
    apply Rtheta_MLeftAbsorb.
  Qed.

  Global Instance Rtheta_LeftInverse_Mplus_neg_0:
    @LeftInverse (flags_m Rtheta) (flags_m Rtheta) (flags_m Rtheta) Rtheta_Mequiv plus negate 0.
  Proof.
    unfold LeftInverse.
    intros x.
    unfold_Rtheta_Mequiv.
    unfold plus, Rtheta_MPlus, negate, Rtheta_Neg.
    rewrite evalWriter_lift_Rtheta_liftM2.
    apply Rtheta_val_LeftInverse_plus_neg_0.
  Qed.

  Global Instance Rtheta_RightInverse_Mplus_neg_0:
    @RightInverse (flags_m Rtheta) (flags_m Rtheta) (flags_m Rtheta) Rtheta_Mequiv plus negate 0.
  Proof.
    unfold RightInverse.
    intros x.
    unfold_Rtheta_Mequiv.
    unfold plus, Rtheta_MPlus, negate, Rtheta_Neg.
    rewrite evalWriter_lift_Rtheta_liftM2.
    apply Rtheta_val_RightInverse_plus_neg_0.
  Qed.

  Global Instance Rtheta_Group_Mplus_0_neg:
    @Group (flags_m Rtheta) Rtheta_Mequiv Rtheta_MPlus Rtheta_MZero Rtheta_MNeg.
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

  Global Instance Ring_MRtheta: Ring (flags_m Rtheta).
  Proof.
    split. split.
    apply Rtheta_Group_Mplus_0_neg.
    apply Rtheta_Commutative_Mplus.
    apply Rtheta_CommutativeMonoid_Mmult_1.
    apply Rtheta_LeftDistribute_Mmult_Mplus.
  Qed.

  Global Instance Rtheta_Mledec (x y: flags_m Rtheta): Decision (x ≤ y) :=
    Rtheta_val_ledec (evalWriter x) (evalWriter y).
  
  Global Instance Rtheta_Mltdec (x y: flags_m Rtheta): Decision (x < y) :=
    Rtheta_val_ltdec (evalWriter x) (evalWriter y).

  Global Program Instance Rtheta_Mabs: Abs (flags_m Rtheta) := Rtheta_liftM (Rtheta_unary abs).
  Next Obligation.
    unfold_Rtheta_Mequiv.
    rewrite evalWriter_Rtheta_liftM.
    unfold le, Rtheta_Le, Rtheta_rel_first, Rtheta_unary.
    unfold abs; crush.
  Qed.


  Global Instance Rtheta_evalRel_proper:
    Proper (((=) ==> (=) ==> (iff)) ==> (Rtheta_Mequiv) ==> (Rtheta_Mequiv) ==> (iff))
           (Rtheta_evalRel).
  Proof.
    simpl_relation.
    unfold Rtheta_evalRel.
    apply H.
    apply H0.
    apply H1.
  Qed.
  
  Global Instance Rtheta_Mle_proper:
    Proper ((=) ==> (=) ==> (iff)) (Rtheta_MLe).
  Proof.
    unfold Rtheta_MLe, Rtheta_rel_first.
    apply Rtheta_evalRel_proper.
    apply Rtheta_val_le_proper.
  Qed.

  Global Instance Rtheta_Mlt_proper:
    Proper ((=) ==> (=) ==> (iff)) (Rtheta_MLt).
  Proof.
    unfold Rtheta_MLt, Rtheta_rel_first.
    apply Rtheta_evalRel_proper.
    apply Rtheta_val_lt_proper.
  Qed.

  Global Instance Rtheta_Mle_Reflexive:
    @Reflexive (flags_m Rtheta) le.
  Proof.
    unfold Reflexive.
    intros x.
    unfold le, Rtheta_MLe, Rtheta_evalRel.
    apply Rtheta_val_le_Reflexive.
  Qed.


  (*
    Lemma Rtheta_rel_first
          (rel: relation CarrierA)
          (a b: flags_m Rtheta):
      Rtheta_rel_first rel a b -> rel (evalWriter a) (evalWriter b).
   *)  

  
  Global Instance Rtheta_Mle_Transitive:
    @Transitive (flags_m Rtheta) le.
  Proof.
    unfold Transitive.
    intros x y z H0 H1.
    unfold le, Rtheta_MLe, Rtheta_evalRel.
    apply Rtheta_val_le_Transitive.
  Qed.

  Global Instance Rtheta_val_le_AntiSymmetric:
    @AntiSymmetric Rtheta Rtheta_val_equiv le.
  Proof.
    unfold AntiSymmetric.
    unfold le, Rtheta_Le, Rtheta_rel_first, equiv, Rtheta_val_equiv, Rtheta_rel_first.
    destruct x,y.
    intros.
    simpl in *.
    apply (antisymmetry (≤)); assumption.
  Qed.

  Global Instance Rtheta_val_le_PreOrder:
    @PreOrder Rtheta le.
  Proof.
    split.
    apply Rtheta_val_le_Reflexive.
    apply Rtheta_val_le_Transitive.
  Qed.

  Global Instance Rtheta_val_le_PartialOrder:
    @PartialOrder Rtheta Rtheta_val_equiv Rtheta_Le.
  Proof.
    split.
    apply Rtheta_val_Setoid.
    apply Rtheta_val_le_proper.
    apply Rtheta_val_le_PreOrder.
    apply Rtheta_val_le_AntiSymmetric.
  Qed.

  Global Instance Rtheta_val_le_TotalRelation:
    @TotalRelation Rtheta le.
  Proof.
    unfold TotalRelation.
    unfold le, Rtheta_Le, Rtheta_rel_first.
    destruct x,y.
    simpl.
    apply (total (≤)).
  Qed.

  Global Instance Rtheta_val_TotalOrder:
    TotalOrder Rtheta_Le.
  Proof.
    split.
    apply Rtheta_val_le_PartialOrder.
    apply Rtheta_val_le_TotalRelation.
  Qed.

  Global Instance Rtheta_val_plus_Order_Morphism:
    ∀ (z : Rtheta), Order_Morphism (plus z).
  Proof.
    split.
    split.
    apply Rtheta_val_Setoid.
    apply Rtheta_val_Setoid.
    apply Rtheta_val_plus_proper.
    reflexivity.
    apply Rtheta_val_le_PartialOrder.
    apply Rtheta_val_le_PartialOrder.
  Qed.

  Lemma Rtheta_val_le_plus_lemma1:
    ∀ z x y : Rtheta, x ≤ y <-> z + x ≤ z + y.
  Proof.
    intros z x y.
    destruct x,y,z.
    unfold le, Rtheta_Le, Rtheta_rel_first, plus, Rtheta_Plus, Rtheta_binop.
    simpl.
    assert(H: SemiRingOrder CarrierAle) by apply CarrierASRO.
    destruct H.
    specialize srorder_plus with (z:=val2).
    destruct srorder_plus.
    destruct order_embedding_preserving.
    destruct order_embedding_reflecting.
    split; auto.
  Qed.

  Global Instance Rtheta_val_plus_OrderPreserving:
    ∀ (z : Rtheta), OrderPreserving (plus z).
  Proof.
    split.
    apply Rtheta_val_plus_Order_Morphism.
    apply Rtheta_val_le_plus_lemma1.
  Qed.

  Global Instance Rtheta_val_plus_OrderReflecting:
    ∀ (z : Rtheta), OrderReflecting (plus z).
  Proof.
    split.
    apply Rtheta_val_plus_Order_Morphism.
    apply Rtheta_val_le_plus_lemma1.
  Qed.

  Global Instance Rtheta_val_plus_OrderEmbedding:
    ∀ (z : Rtheta), OrderEmbedding (plus z).
  Proof.
    intros.
    split.
    apply Rtheta_val_plus_OrderPreserving.
    apply Rtheta_val_plus_OrderReflecting.
  Qed.

  Global Instance Rtheta_val_SemiRingOrder:
    SemiRingOrder Rtheta_Le.
  Proof.
    split.
    - apply total_order_po.
    - apply Rtheta_val_SemiRing.
    -
      destruct x,y.
      unfold le, Rtheta_Le, Rtheta_rel_first.
      unfold plus, Rtheta_Plus, Rtheta_binop.
      unfold_Rtheta_val_equiv.
      simpl.
      intros H.
      exists (Rtheta_normal (val1-val0)).
      simpl; ring.
    - apply Rtheta_val_plus_OrderEmbedding.
    - destruct x,y.
      unfold le, Rtheta_Le, Rtheta_rel_first.
      apply CarrierASRO.
  Qed.

  Lemma Rtheta_eq_val_equiv:
    forall (a b: Rtheta), eq a b -> Rtheta_val_equiv a b.
  Proof.
    intros.
    crush.
  Qed.





