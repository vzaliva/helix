(* R_theta is type which is used as value for vectors in SPIRAL.  *)

Require Export CarrierType.

Require Import Coq.Bool.Bool.
Require Import Ring.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.theory.rings.
Require Import MathClasses.interfaces.orders MathClasses.orders.orders.

Require Import CpdtTactics.
Require Import JRWTactics.

Section RthetaFlags.

  Record RthetaFlags : Type :=
    mkRthetaFlags
      {
        structCollision: bool ;
        valueCollision: bool ;
        leftStruct: bool ;
        rightStruct: bool
      }.

  Global Instance RthetaFlags_equiv:
    Equiv RthetaFlags :=
    fun a b =>
      structCollision a ≡ structCollision b /\
      valueCollision a ≡ valueCollision b /\
      leftStruct a ≡ leftStruct b /\
      rightStruct a ≡ rightStruct b.

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

  Definition RthetaFlags_normal := mkRthetaFlags false false false false.

  Definition combineFlags (a b: RthetaFlags): RthetaFlags
    :=  mkRthetaFlags
          (orb (structCollision a) (structCollision b))
          (orb (valueCollision a) (valueCollision b))
          (orb (leftStruct a) (leftStruct b))
          (orb (rightStruct a) (rightStruct b)).
  
  (* Compute flags based on structural properties of two values being combined *)
  Definition computeFlags (sa sb: bool) :=
    match sa, sb with
    | false, false => mkRthetaFlags false true false false (* value collision *)
    | false, true => mkRthetaFlags false false false true (* right struct *)
    | true, false => mkRthetaFlags false false true false (* left struct *)
    | true, true => mkRthetaFlags true false false false (* struct collision *)
    end.
  
End RthetaFlags.

Record Rtheta : Type :=
  mkRtheta  {
      val : CarrierA;
      sL: bool;
      sR: bool
    }.

(* Some convenience constructros *)

Definition Rtheta_normal (val: CarrierA) :=
  mkRtheta val false false.

Definition Rtheta_SZero :=
  mkRtheta 0 true true.

Definition Rtheta_SOne :=
  mkRtheta 1 true true.

Definition RthetaIsStruct (x: Rtheta) :=
  andb (sL x) (sR x).

(* Propositional predicates *)
Definition Is_Struct (x:Rtheta) := Is_true (RthetaIsStruct x).
Definition Is_Val (x:Rtheta) := not (Is_Struct x).

Definition Rtheta_binop
           (op: CarrierA->CarrierA->CarrierA)
           (a b: Rtheta)
  :=
    mkRtheta
      (op (val a) (val b)) (* apply operation to argument value fields *)
      (RthetaIsStruct a) (* preserve structural flag from 1st argument as sL *)
      (RthetaIsStruct b). (* preserve structural flag from 2nd argument as sR *)

(* Unary application of a function to first element, preserving remaining ones *)
Definition Rtheta_unary
           (op: CarrierA->CarrierA)
           (x: Rtheta)
  := let s := (RthetaIsStruct x) in
     mkRtheta (op (val x)) s s.

(* Relation on the first element, ignoring the rest *)
Definition Rtheta_rel_first
           (rel: relation CarrierA)
           (a b: Rtheta)
  := rel (val a) (val b).

Global Instance Rtheta_Zero: Zero Rtheta := Rtheta_normal 0.
Global Instance Rtheta_One: One Rtheta := Rtheta_normal 1.
Global Instance Rtheta_Plus: Plus Rtheta := Rtheta_binop plus.
Global Instance Rtheta_Mult: Mult Rtheta := Rtheta_binop mult.
Global Instance Rtheta_Neg: Negate Rtheta := Rtheta_unary negate.
Global Instance Rtheta_Le: Le Rtheta := Rtheta_rel_first le.
Global Instance Rtheta_Lt: Lt Rtheta := Rtheta_rel_first lt.

Lemma Rtheta_Val_is_not_Struct:
  ∀ z : Rtheta, Is_Val z → ¬Is_Struct z.
Proof.
  intros z H.
  unfold Is_Val in H.
  assumption.
Qed.

Section Rtheta_val_Setoid_equiv.
  (* Setoid equality is defined by taking into account only the first element. *)
  Global Instance Rtheta_val_equiv: Equiv Rtheta | 1 := Rtheta_rel_first equiv.

  Global Instance Rtheta_val_Reflexive_equiv: Reflexive Rtheta_val_equiv.
  Proof.
    unfold Reflexive.
    intros.
    unfold equiv, Rtheta_val_equiv, Rtheta_rel_first in *.
    reflexivity.
  Qed.

  Global Instance Rtheta_val_Symmetric_equiv: Symmetric Rtheta_val_equiv.
  Proof.
    unfold Symmetric.
    intros.
    unfold equiv, Rtheta_val_equiv, Rtheta_rel_first in *.
    auto.
  Qed.

  Global Instance Rtheta_val_Transitive_equiv: Transitive Rtheta_val_equiv.
  Proof.
    unfold Transitive.
    intros.
    unfold equiv, Rtheta_val_equiv, Rtheta_rel_first in *.
    auto.
  Qed.

  Global Instance Rtheta_val_Equivalence_equiv: Equivalence Rtheta_val_equiv.
  Proof.
    split.
    apply Rtheta_val_Reflexive_equiv.
    apply Rtheta_val_Symmetric_equiv.
    apply Rtheta_val_Transitive_equiv.
  Qed.

  Global Instance Rtheta_val_Setoid: @Setoid Rtheta Rtheta_val_equiv.
  Proof.
    apply Rtheta_val_Equivalence_equiv.
  Qed.

  Global Instance Rtheta_val_Associative_plus: Associative Rtheta_Plus.
  Proof.

    unfold Associative, HeteroAssociative, Rtheta_Plus , Rtheta_binop, RthetaIsStruct.
    intros x y z.
    destruct x, y, z.
    unfold equiv, Rtheta_val_equiv, Rtheta_rel_first; simpl.
    apply plus_assoc.
  Qed.

  Global Instance Rtheta_val_Associative_mult: Associative Rtheta_Mult.
  Proof.
    unfold Associative, HeteroAssociative, Rtheta_Mult, Rtheta_binop.
    intros x y z.
    destruct x, y, z.
    unfold equiv, Rtheta_val_equiv, Rtheta_rel_first; simpl.
    apply mult_assoc.
  Qed.

  Global Instance Rtheta_val_val_proper:
    Proper ((=) ==> (=)) (val).
  Proof.
    simpl_relation.
  Qed.

  Global Instance Rtheta_binop_val_proper:
    Proper (((=) ==> (=)) ==> (Rtheta_val_equiv) ==> (Rtheta_val_equiv) ==> (Rtheta_val_equiv)) (Rtheta_binop).
  Proof.
    simpl_relation.
    unfold Rtheta_val_equiv, Rtheta_rel_first in *.
    apply H ; [apply H0 | apply H1].
  Qed.

  Global Instance Rtheta_unary_val_proper:
    Proper (((=) ==> (=)) ==> (Rtheta_val_equiv) ==> (Rtheta_val_equiv)) (Rtheta_unary).
  Proof.
    simpl_relation.
    unfold Rtheta_val_equiv, Rtheta_rel_first in *.
    apply H, H0.
  Qed.

  Global Instance Rtheta_val_plus_proper:
    Proper ((=) ==> (=) ==> (=)) (Rtheta_Plus).
  Proof.
    apply Rtheta_binop_val_proper.
    simpl_relation.
    rewrite H, H0.
    reflexivity.
  Qed.

  Global Instance Rtheta_val_neg_proper:
    Proper ((=) ==> (=)) (Rtheta_Neg).
  Proof.
    apply Rtheta_unary_val_proper.
    simpl_relation.
    rewrite H.
    reflexivity.
  Qed.

  Global Instance Rtheta_val_mult_proper:
    Proper ((=) ==> (=) ==> (=)) (Rtheta_Mult).
  Proof.
    intros a a' aEq b b' bEq.
    unfold Rtheta_Mult, Rtheta_binop, equiv, Rtheta_val_equiv, Rtheta_rel_first.
    destruct a, b, a', b'.
    simpl.
    unfold equiv, Rtheta_val_equiv, Rtheta_rel_first in aEq, bEq. simpl in aEq, bEq.
    rewrite aEq, bEq.
    reflexivity.
  Qed.

  Global Instance Rtheta_val_SemiGroup_plus:
    @SemiGroup Rtheta Rtheta_val_equiv plus.
  Proof.
    split.
    apply Rtheta_val_Setoid.
    apply Rtheta_val_Associative_plus.
    apply Rtheta_val_plus_proper.
  Qed.

  Global Instance Rtheta_val_LeftIdentity_plus_0:
    @LeftIdentity Rtheta Rtheta Rtheta_val_equiv plus zero.
  Proof.
    unfold LeftIdentity.
    intros.
    unfold  plus, zero, equiv, Rtheta_val_equiv, Rtheta_Plus, Rtheta_Zero, Rtheta_rel_first,
    Rtheta_binop.
    destruct y.
    simpl.
    ring.
  Qed.

  Global Instance Rtheta_val_RightIdentity_plus_0:
    @RightIdentity Rtheta Rtheta_val_equiv Rtheta plus zero.
  Proof.
    unfold RightIdentity.
    intros.
    unfold  plus, zero, equiv, Rtheta_val_equiv, Rtheta_Plus, Rtheta_Zero, Rtheta_rel_first,
    Rtheta_binop.
    destruct x.
    simpl.
    ring.
  Qed.

  Global Instance Rtheta_val_Monoid_plus_0:
    @Monoid Rtheta Rtheta_val_equiv plus zero.
  Proof.
    split.
    apply Rtheta_val_SemiGroup_plus.
    apply Rtheta_val_LeftIdentity_plus_0.
    apply Rtheta_val_RightIdentity_plus_0.
  Qed.

  Global Instance Rtheta_val_Commutative_Rtheta_binary
         (op: CarrierA -> CarrierA -> CarrierA)
         `{op_mor: !Proper ((=) ==> (=) ==> (=)) op}
         `{C: !Commutative op}
    :
      @Commutative Rtheta Rtheta_val_equiv Rtheta (Rtheta_binop op).
  Proof.
    intros x y.
    destruct x, y.
    unfold Rtheta_binop.
    unfold equiv, Rtheta_val_equiv, Rtheta_rel_first.
    apply C.
  Qed.

  Global Instance Rtheta_val_Commutative_plus:
    @Commutative Rtheta Rtheta_val_equiv Rtheta plus.
  Proof.
    apply Rtheta_val_Commutative_Rtheta_binary.
    - simpl_relation.
      rewrite H, H0.
      reflexivity.
    - simpl_relation.
      setoid_replace (x + y) with (y + x).
      reflexivity.
      ring.
  Qed.

  Global Instance Rtheta_val_CommutativeMonoid_plus_0:
    @CommutativeMonoid Rtheta Rtheta_val_equiv plus zero.
  Proof.
    split.
    apply Rtheta_val_Monoid_plus_0.
    apply Rtheta_val_Commutative_plus.
  Qed.

  Global Instance Rtheta_val_SemiGroup_mult:
    @SemiGroup Rtheta Rtheta_val_equiv mult.
  Proof.
    split.
    apply Rtheta_val_Setoid.
    apply Rtheta_val_Associative_mult.
    apply Rtheta_val_mult_proper.
  Qed.

  Global Instance Rtheta_val_LeftIdentity_mult_1:
    @LeftIdentity Rtheta Rtheta Rtheta_val_equiv mult one.
  Proof.
    unfold LeftIdentity.
    intros.
    unfold  mult, one, equiv, Rtheta_val_equiv, Rtheta_Mult, Rtheta_One, Rtheta_rel_first,
    Rtheta_binop.
    destruct y.
    simpl.
    ring.
  Qed.

  Global Instance Rtheta_val_RightIdentity_mult_1:
    @RightIdentity Rtheta Rtheta_val_equiv Rtheta mult one.
  Proof.
    unfold RightIdentity.
    intros.
    unfold  mult, one, equiv, Rtheta_val_equiv, Rtheta_Mult, Rtheta_One, Rtheta_rel_first,
    Rtheta_binop.
    destruct x.
    simpl.
    ring.
  Qed.

  Global Instance Rtheta_val_Monoid_mult_1:
    @Monoid Rtheta Rtheta_val_equiv mult one.
  Proof.
    split.
    apply Rtheta_val_SemiGroup_mult.
    apply Rtheta_val_LeftIdentity_mult_1.
    apply Rtheta_val_RightIdentity_mult_1.
  Qed.

  Global Instance Rtheta_val_Commutative_mult:
    @Commutative Rtheta Rtheta_val_equiv Rtheta mult.
  Proof.
    apply Rtheta_val_Commutative_Rtheta_binary.
    - simpl_relation.
      rewrite H, H0.
      reflexivity.
    - simpl_relation.
      setoid_replace (x * y) with (y * x).
      reflexivity.
      ring.
  Qed.

  Global Instance Rtheta_val_LeftDistribute_mult_plus:
    @LeftDistribute Rtheta Rtheta_val_equiv mult plus.
  Proof.
    unfold LeftDistribute, LeftHeteroDistribute, equiv, Rtheta_val_equiv, Rtheta_rel_first, plus, mult, Rtheta_Plus, Rtheta_Mult, Rtheta_binop.
    intros.
    destruct a, b, c.
    simpl.
    ring.
  Qed.

  Global Instance Rtheta_val_CommutativeMonoid_mult_1:
    @CommutativeMonoid Rtheta Rtheta_val_equiv mult one.
  Proof.
    split.
    apply Rtheta_val_Monoid_mult_1.
    apply Rtheta_val_Commutative_mult.
  Qed.

  Global Instance Rtheta_val_LeftAbsorb:
    @LeftAbsorb Rtheta Rtheta_val_equiv Rtheta mult 0.
  Proof.
    unfold LeftAbsorb.
    intros.
    destruct y.
    unfold equiv, Rtheta_val_equiv, Rtheta_rel_first, plus, mult, Rtheta_Mult, Rtheta_binop.
    simpl.
    ring.
  Qed.

  Global Instance Rtheta_val_RightAbsorb:
    @RightAbsorb Rtheta Rtheta Rtheta_val_equiv mult 0.
  Proof.
    unfold RightAbsorb.
    intros.
    destruct x.
    unfold equiv, Rtheta_val_equiv, Rtheta_rel_first, plus, mult, Rtheta_Mult, Rtheta_binop.
    simpl.
    ring.
  Qed.

  Global Instance Rtheta_val_SemiRing: SemiRing Rtheta.
  Proof.
    split.
    apply Rtheta_val_CommutativeMonoid_plus_0.
    apply Rtheta_val_CommutativeMonoid_mult_1.
    apply Rtheta_val_LeftDistribute_mult_plus.
    apply Rtheta_val_LeftAbsorb.
  Qed.

  Global Instance Rtheta_val_LeftInverse_plus_neg_0:
    @LeftInverse Rtheta Rtheta Rtheta Rtheta_val_equiv plus negate 0.
  Proof.
    unfold LeftInverse, equiv, Rtheta_Plus, Rtheta_Neg, Rtheta_unary, Rtheta_val_equiv, Rtheta_rel_first, Rtheta_binop.
    intros.
    destruct x.
    simpl.
    ring.
  Qed.

  Global Instance Rtheta_val_RightInverse_plus_neg_0:
    @RightInverse Rtheta Rtheta Rtheta Rtheta_val_equiv plus negate 0.
  Proof.
    unfold RightInverse, equiv, Rtheta_Plus, Rtheta_Neg, Rtheta_unary, Rtheta_val_equiv, Rtheta_rel_first, Rtheta_binop.
    intros.
    simpl.
    ring.
  Qed.

  Global Instance Rtheta_val_Group_plus_0_neg:
    @Group Rtheta Rtheta_val_equiv Rtheta_Plus Rtheta_Zero Rtheta_Neg.
  Proof.
    split.
    apply Rtheta_val_Monoid_plus_0.
    split.
    apply Rtheta_val_Setoid.
    apply Rtheta_val_Setoid.
    apply Rtheta_val_neg_proper.
    apply Rtheta_val_LeftInverse_plus_neg_0.
    apply Rtheta_val_RightInverse_plus_neg_0.
  Qed.

  Global Instance Ring_Rtheta_val: Ring Rtheta.
  Proof.
    split. split.
    apply Rtheta_val_Group_plus_0_neg.
    apply Rtheta_val_Commutative_plus.
    apply Rtheta_val_CommutativeMonoid_mult_1.
    apply Rtheta_val_LeftDistribute_mult_plus.
  Qed.

  Global Instance Rtheta_val_ledec (x y: Rtheta): Decision (x ≤ y) :=
    CarrierAledec (val x) (val y).

  Global Instance Rtheta_val_ltdec (x y: Rtheta): Decision (x < y) :=
    CarrierAltdec (val x) (val y).

  Global Program Instance Rtheta_val_abs: Abs Rtheta := Rtheta_unary abs.
  Next Obligation.
    unfold le, Rtheta_Le, Rtheta_rel_first, Rtheta_unary.
    split; unfold abs; crush.
  Qed.

  Global Instance Rtheta_val_le_proper:
    Proper ((=) ==> (=) ==> (iff)) (Rtheta_Le).
  Proof.
    intros a a' aEq b b' bEq.
    unfold Rtheta_Le, Rtheta_rel_first, Rtheta_val_equiv, Rtheta_rel_first.
    destruct a, b, a', b'.
    simpl.
    unfold equiv, Rtheta_val_equiv, Rtheta_rel_first in aEq, bEq; simpl in aEq, bEq.
    rewrite <- aEq, <- bEq.
    split; auto.
  Qed.

  Global Instance Rtheta_val_lt_proper:
    Proper ((=) ==> (=) ==> (iff)) (Rtheta_Lt).
  Proof.
    intros a a' aEq b b' bEq.
    unfold Rtheta_Lt, Rtheta_rel_first, Rtheta_val_equiv, Rtheta_rel_first.
    destruct a, b, a', b'.
    simpl.
    unfold equiv, Rtheta_val_equiv, Rtheta_rel_first in aEq, bEq; simpl in aEq, bEq.
    rewrite <- aEq, <- bEq.
    split; auto.
  Qed.

  Global Instance Rtheta_val_le_Reflexive:
    Reflexive le.
  Proof.
    unfold Reflexive.
    intros.
    unfold le, Rtheta_Le, Rtheta_rel_first.
    reflexivity.
  Qed.

  Global Instance Rtheta_val_le_Transitive:
    Transitive le.
  Proof.
    unfold Transitive.
    unfold le, Rtheta_Le, Rtheta_rel_first.
    intros.
    destruct x, y, z.
    simpl in *.
    auto.
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
      unfold equiv, Rtheta_val_equiv, Rtheta_rel_first.
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

End Rtheta_val_Setoid_equiv.

Add Ring RingRthetaVal: (stdlib_ring_theory Rtheta).

Section Rtheta_Zero_Util.
  Definition Is_ValZero (x:Rtheta) := val x = zero.

  Lemma SZero_is_ValZero:
    Is_ValZero Rtheta_SZero.
  Proof.
    unfold Is_ValZero.
    reflexivity.
  Qed.

  Lemma Zero_is_ValZero:
    Is_ValZero zero.
  Proof.
    unfold Is_ValZero.
    reflexivity.
  Qed.

  Lemma Is_ValZero_to_SZero (x: Rtheta):
    Is_ValZero x -> x = Rtheta_SZero.
  Proof.
    intros H.
    unfold Is_ValZero in H.
    unfold equiv, Rtheta_val_equiv, Rtheta_rel_first.
    rewrite H.
    reflexivity.
  Qed.

  Lemma Is_ValZero_to_zero (x: Rtheta):
    Is_ValZero x -> x = zero.
  Proof.
    intros H.
    unfold Is_ValZero in H.
    unfold equiv, Rtheta_val_equiv, Rtheta_rel_first.
    rewrite H.
    reflexivity.
  Qed.
End Rtheta_Zero_Util.

Section Rtheta_Poinitwise_Setoid_equiv.

  (* Setoid equality is defined by pointwise comparison of all elements. *)
  Global Instance Rtheta_pw_equiv: Equiv Rtheta | 2 := fun a b =>
                                                         val a = val b /\
                                                         sL a ≡ sL b /\
                                                         sR a ≡ sR b.

  Lemma Rtheta_poinitwise_equiv_equiv (a b: Rtheta):
    Rtheta_pw_equiv a b -> Rtheta_val_equiv a b.
  Proof.
    destruct a, b.
    unfold Rtheta_pw_equiv, Rtheta_val_equiv, Rtheta_rel_first.
    simpl.
    intros H.
    destruct H as [H0 H1].
    apply H0.
  Qed.

  Lemma Rtheta_eq_pw_equiv:
    forall (a b: Rtheta), eq a b -> Rtheta_pw_equiv a b.
  Proof.
    intros a b H.
    destruct a, b.
    unfold Rtheta_pw_equiv.
    simpl.
    inversion H.
    auto.
  Qed.

  Global Instance Rtheta_pw_Reflexive_equiv: Reflexive Rtheta_pw_equiv.
  Proof.
    unfold Reflexive.
    intros x.
    destruct x.
    unfold equiv, Rtheta_pw_equiv.
    auto.
  Qed.

  Global Instance Rtheta_pw_Symmetric_equiv: Symmetric Rtheta_pw_equiv.
  Proof.
    unfold Symmetric.
    intros x y H.
    destruct x,y.
    unfold equiv, Rtheta_pw_equiv in *.
    split; try symmetry; crush.
  Qed.

  Global Instance Rtheta_pw_Transitive_equiv: Transitive Rtheta_pw_equiv.
  Proof.
    unfold Transitive.
    intros x y z.
    destruct x, y, z.
    unfold equiv, Rtheta_pw_equiv.
    crush.
  Qed.

  Global Instance Rtheta_pw_Equivalence_equiv: Equivalence Rtheta_pw_equiv.
  Proof.
    split.
    apply Rtheta_pw_Reflexive_equiv.
    apply Rtheta_pw_Symmetric_equiv.
    apply Rtheta_pw_Transitive_equiv.
  Qed.

  Global Instance Rtheta_pw_Setoid: @Setoid Rtheta Rtheta_pw_equiv.
  Proof.
    apply Rtheta_pw_Equivalence_equiv.
  Qed.

  Global Instance RthetaVal_pw_proper:
    Proper ((Rtheta_pw_equiv) ==> (=)) (val).
  Proof.
    simpl_relation.
    destruct x, y.
    simpl.
    unfold Rtheta_pw_equiv in H.
    destruct H as [H0 [H1 H2]].
    auto.
  Qed.

  Global Instance Rtheta_pw_plus_proper:
    Proper ((Rtheta_pw_equiv) ==> (Rtheta_pw_equiv) ==> (Rtheta_pw_equiv)) (Rtheta_Plus).
  Proof.
    intros a a' aEq b b' bEq.
    unfold Rtheta_Plus, Rtheta_binop, equiv, Rtheta_pw_equiv, Rtheta_rel_first, RthetaIsStruct.
    destruct a, b, a', b'.
    simpl.
    destruct aEq as [AH0 [AH1 AH2]].
    destruct bEq as [BH0 [BH1 BH2]].
    simpl in *.
    crush.
  Qed.

  Global Instance Rtheta_pw_neg_proper:
    Proper ((Rtheta_pw_equiv) ==> (Rtheta_pw_equiv)) (Rtheta_Neg).
  Proof.
    intros a b aEq.
    unfold Rtheta_Neg, Rtheta_unary, equiv, Rtheta_pw_equiv, Rtheta_rel_first.
    destruct a, b.
    unfold equiv, Rtheta_pw_equiv in aEq.
    crush.
  Qed.

  Global Instance Rtheta_pw_mult_proper:
    Proper ((Rtheta_pw_equiv) ==> (Rtheta_pw_equiv) ==> (Rtheta_pw_equiv)) (Rtheta_Mult).
  Proof.
    intros a a' aEq b b' bEq.
    unfold Rtheta_Mult, Rtheta_binop, equiv, Rtheta_pw_equiv, Rtheta_rel_first.
    destruct a, b, a', b'.
    unfold equiv, Rtheta_pw_equiv in aEq, bEq.
    crush.
  Qed.

End Rtheta_Poinitwise_Setoid_equiv.


