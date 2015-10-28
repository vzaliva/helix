Require Import Arith.
Require Import Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Program. 

Require Import CpdtTactics.
Require Import JRWTactics.
Require Import CaseNaming.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Psatz.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders.
Require Import MathClasses.orders.minmax MathClasses.orders.orders MathClasses.orders.rings.
Require Import MathClasses.theory.rings MathClasses.theory.abs.

Section RType.
  Context
    `{Ae: Equiv A}
    `{Az: Zero A} `{A1: One A}
    `{Aplus: Plus A} `{Amult: Mult A} 
    `{Aneg: Negate A}
    `{Ale: Le A}
    `{Alt: Lt A}
    `{Ato: !@TotalOrder A Ae Ale}
    `{Aabs: !@Abs A Ae Ale Az Aneg}
    `{Asetoid: !@Setoid A Ae}
    `{Aledec: !∀ x y: A, Decision (x ≤ y)}
    `{Aeqdec: !∀ x y, Decision (x = y)}
    `{Altdec: !∀ x y: A, Decision (x < y)}
    `{Ar: !Ring A}
    `{ASRO: !@SemiRingOrder A Ae Aplus Amult Az A1 Ale}
    `{ASSO: !@StrictSetoidOrder A Ae Alt}
  .

  Add Ring RingA: (stdlib_ring_theory A).
  
  Definition Rtheta := prod (prod A bool) bool.

  (* Projections: *)
  Definition Rtheta1 (x:Rtheta) := fst (fst x).
  Definition Rtheta2 (x:Rtheta) := snd (fst x).
  Definition Rtheta3 (x:Rtheta) := snd x.
  
  (* Pointwise application of 3 functions to elements of Rtheta *)
  Definition Rtheta_pointwise 
             (oA:A->A->A) (ob1 ob2: bool->bool->bool)
             (a b: Rtheta)
    :=
      (
        oA (Rtheta1 a) (Rtheta1 b),
        ob1 (Rtheta2 a) (Rtheta2 b),
        ob2  (Rtheta3 a) (Rtheta3 b)
      ).
  
  (* Unary application of a function to first element, preserving remaining ones *)
  Definition Rtheta_unary
             (oA:A->A) 
             (x: Rtheta)
    := (oA (Rtheta1 x), (Rtheta2 x), (Rtheta3 x)).

  (* Relation on the first element, ignoring the rest *)
  Definition Rtheta_rel_first
             (oA:relation A)
             (a b: Rtheta)
    := oA (Rtheta1 a) (Rtheta1 b).

  (* Setoid equality is defined by taking into account only first element. If you need full equality, use 'eq' instead *)
  Instance Rtheta_equiv: Equiv Rtheta := Rtheta_rel_first equiv.

  Instance Rtheta_Reflexive_equiv: Reflexive Rtheta_equiv.
  Proof.
    unfold Reflexive.
    intros. 
    unfold equiv, Rtheta_equiv, Rtheta_rel_first in *.
    crush.
  Qed.

  Instance Rtheta_Symmetric_equiv: Symmetric Rtheta_equiv.
  Proof.
    unfold Reflexive.
    intros. 
    unfold equiv, Rtheta_equiv, Rtheta_rel_first in *.
    crush.
  Qed.

  Instance Rtheta_Transitive_equiv: Transitive Rtheta_equiv.
  Proof.
    unfold Reflexive.
    intros. 
    unfold equiv, Rtheta_equiv, Rtheta_rel_first in *.
    crush.
  Qed.
  
  Instance Rtheta_Setoid: Setoid Rtheta.
  Proof.
    split.
    apply Rtheta_Reflexive_equiv.
    apply Rtheta_Symmetric_equiv.
    apply Rtheta_Transitive_equiv.
  Qed.
      
  Instance Rtheta_Zero: Zero Rtheta := (0, false, false).
  Instance Rtheta_One: One Rtheta := (1, false, false).
  Instance Rtheta_Plus: Plus Rtheta := Rtheta_pointwise plus orb orb.
  Instance Rtheta_Mult: Mult Rtheta := Rtheta_pointwise mult orb orb.
  Instance Rtheta_Neg: Negate Rtheta := Rtheta_unary negate.
  Instance Rtheta_Le: Le Rtheta := Rtheta_rel_first le.
  Instance Rtheta_Lt: Lt Rtheta := Rtheta_rel_first lt.

  Instance Rtheta_Associative_plus: Associative Rtheta_Plus.
  Proof.
    unfold Associative, HeteroAssociative, Rtheta_Plus, Rtheta_pointwise,
    Rtheta1, Rtheta2, Rtheta3, equiv, Rtheta_equiv, Rtheta_rel_first.
    intros.
    apply plus_assoc.
  Qed.

  (* Convenience tactice to destruct 3-tuple into elements *)
  Ltac destruct_Rtheta x :=
    let x01 := fresh x "01" in
    let x2 := fresh x "2" in
    let x0 := fresh x "0" in
    let x1 := fresh x "1" in
    destruct x as (x01, x2); 
      destruct x01 as (x0, x1).
  
  Global Instance Rtheta_plus_proper :
    Proper ((=) ==> (=) ==> (=)) (Rtheta_Plus).
  Proof.
    intros a a' aEq b b' bEq.
    unfold Rtheta_Plus, Rtheta_pointwise, equiv, Rtheta_equiv, Rtheta_rel_first, Rtheta1, Rtheta2, Rtheta3.
    simpl.
    destruct_Rtheta a.
    destruct_Rtheta b.
    destruct_Rtheta a'.
    destruct_Rtheta b'.
    simpl.
    unfold equiv, Rtheta_equiv, Rtheta_rel_first, Rtheta1 in aEq. simpl in aEq.
    unfold equiv, Rtheta_equiv, Rtheta_rel_first, Rtheta1 in bEq. simpl in bEq.
    rewrite aEq, bEq.
    reflexivity.
  Qed.
  
  Instance Rtheta_SemiGroup_plus:
    @SemiGroup Rtheta Rtheta_equiv plus.
  Proof.
    split.
    apply Rtheta_Setoid.
    apply Rtheta_Associative_plus.
    apply Rtheta_plus_proper.
  Qed.

  Instance Rtheta_LeftIdentity_plus_0:
    @LeftIdentity Rtheta Rtheta Rtheta_equiv plus zero.
  Proof.
    unfold LeftIdentity.
    intros.
    unfold  plus, zero, equiv, Rtheta_equiv, Rtheta_Plus, Rtheta_Zero, Rtheta_rel_first,
    Rtheta_pointwise, Rtheta1, Rtheta2, Rtheta3.
    destruct_Rtheta y.
    simpl.
    ring.
  Qed.

  Instance Rtheta_RightIdentity_plus_0:
    @RightIdentity Rtheta Rtheta_equiv Rtheta plus zero.
  Proof.
    unfold RightIdentity.
    intros.
    unfold  plus, zero, equiv, Rtheta_equiv, Rtheta_Plus, Rtheta_Zero, Rtheta_rel_first,
    Rtheta_pointwise, Rtheta1, Rtheta2, Rtheta3.
    destruct_Rtheta x.
    simpl.
    ring.
  Qed.
  
  Instance Rtheta_Monoid_plus_0:
    @Monoid Rtheta Rtheta_equiv plus zero.
  Proof.
    split.
    apply Rtheta_SemiGroup_plus.
    apply Rtheta_LeftIdentity_plus_0.
    apply Rtheta_RightIdentity_plus_0.
  Qed.

  Instance Rtheta_Commutative_plus:
    @Commutative Rtheta Rtheta_equiv Rtheta plus.
  Proof.
    unfold Commutative.
    intros.
    unfold  plus, zero, equiv, Rtheta_equiv, Rtheta_Plus, Rtheta_Zero, Rtheta_rel_first,
    Rtheta_pointwise, Rtheta1, Rtheta2, Rtheta3.
    destruct_Rtheta x.
    destruct_Rtheta y.
    simpl.
    ring.
  Qed.
  
  Instance Rtheta_CommutativeMonoid_plus_0:
    @CommutativeMonoid Rtheta Rtheta_equiv plus zero.
  Proof.
    split.
    apply Rtheta_Monoid_plus_0.
    apply Rtheta_Commutative_plus.
Qed.
  
  Instance: SemiRing Rtheta.
  Proof.
    split.
    apply Rtheta_CommutativeMonoid_plus_0.
  Qed.


End RType.  


  
  