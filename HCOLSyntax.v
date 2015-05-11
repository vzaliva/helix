(* Coq defintions for HCOL operator language *)

Require Import Spiral.

Require Import Arith.
Require Import Coq.Arith.Plus.
Require Import Program. (* compose *)
Require Import Morphisms.

Require Import CpdtTactics.
Require Import CaseNaming.
Require Import Coq.Logic.FunctionalExtensionality.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.implementations.peano_naturals.
Require Import MathClasses.theory.rings.

(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

Require Import HCOL.
Import HCOLOperators.
Open Scope vector_scope.

(* === HCOL Syntax === *)

Section HCOL.
  Context    
    `{Ae: Equiv A}.

  Inductive HOperator : nat -> nat -> Type :=
  | HOPrepend i {n} (a:vector A n): HOperator i (n+i)
  | HOInfinityNorm {i}: HOperator i 1
  | HOReduction i (f: A->A->A) `{pF: !Proper ((=) ==> (=) ==> (=)) f} (idv:A): HOperator i 1
  | HOAppend i {n} (a:vector A n): HOperator i (n+i)
  | HOVMinus o: HOperator (o + o) o
  | HOPointWise2 o (f:A->A->A) `{pF: !Proper ((=) ==> (=) ==> (=)) f}: HOperator (o+o) o
  | HOLess o: HOperator (o+o) o
  | HOEvalPolynomial {n} (a:vector A n): HOperator 1 1
  | HOMonomialEnumerator n: HOperator 1 (S n)
  | HOChebyshevDistance h: HOperator (h+h) 1
  | HOScalarProd {h:nat}: HOperator (h+h) 1
  | HOInduction n (f:A->A->A) `{pF: !Proper ((=) ==> (=) ==> (=)) f} (initial:A): HOperator 1 n
  | HOCompose i {t} o: HOperator t o -> HOperator i t -> HOperator i o
  | HOCross i1 o1 i2 o2:  HOperator i1 o1 -> HOperator i2 o2 -> HOperator (i1+i2) (o1+o2)
  | HOTLess i1 i2 o: HOperator i1 o -> HOperator i2 o -> HOperator (i1+i2) o
  | HOStack i o1 o2: HOperator i o1 -> HOperator i o2 -> HOperator i (o1+o2)
  .

  Section HCOL_Eval.
    Context    
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
      `{ASSO: !@StrictSetoidOrder A Ae Alt}.
    

    Definition evalHCOL: forall {i} {o}, HOperator i o -> vector A i -> vector A o :=
      fix evalHCOL {i} {o} op v :=
      (match op in @HOperator i o return vector A i -> vector A o
       with
         | HOPrepend i n a => Vapp a
         | HOInfinityNorm _ => fun v0 => Vectorize (InfinityNorm v0)
         | HOReduction _ f _ idv => fun v0 => Vectorize (Reduction f idv v0)
         | HOAppend _ _ a => Vapp a
         | HOVMinus o => VMinus  ∘ (vector2pair o)
         | HOPointWise2 o f _ => PointWise2 f ∘ (vector2pair o)
         | HOLess o => ZVLess  ∘ (vector2pair o)
         (* | HOPart p => Vsub v p *)
         | HOEvalPolynomial _ a => Lst ∘ EvalPolynomial a ∘ Scalarize
         | HOMonomialEnumerator n => MonomialEnumerator n ∘ Scalarize
         | HOChebyshevDistance h => Lst ∘ ChebyshevDistance ∘ (vector2pair h)
         | HOScalarProd h => Lst ∘ ScalarProd ∘ (vector2pair h)
         | HOInduction n f _ initial => Induction n f initial ∘ Scalarize
         | HOCompose _ _ _ cop1 cop2 => ((evalHCOL cop1) ∘ (evalHCOL cop2))
         | HOTLess i1 _ _ lop1 lop2 => fun v0 => let (v1,v2) := vector2pair i1 v0 in
                                                 ZVLess (pair (evalHCOL lop1 v1) (evalHCOL lop2 v2))
         | HOCross x _ _ _ xop1 xop2 => pair2vector ∘ (Cross (evalHCOL xop1, evalHCOL xop2)) ∘ (vector2pair x)
         | HOStack _ _ _ op1 op2 => pair2vector ∘ (Stack (evalHCOL op1, evalHCOL op2))
       end) v.


    Global Instance HCOL_equiv {i o:nat}: Equiv (HOperator i o) :=
      fun a b => forall (x:vector A i), evalHCOL a x = evalHCOL b x.

    
    Lemma equal_HCOL: forall {i o:nat} {f g : HOperator i o},
                        f = g -> forall (x:vector A i), evalHCOL f x = evalHCOL g x.
    Proof.
      intros.
      unfold equiv, HCOL_equiv in H.
      auto.
    Qed.

    Lemma HCOL_extensionality {i o} (f g : HOperator i o) :
      (forall v, evalHCOL f v = evalHCOL g v) -> f = g.
    Proof.
      intros.
      unfold equiv, HCOL_equiv.
      auto.
    Qed.

    Global Instance HCOL_Equivalence {i o:nat}
           `{!Equivalence (@equiv A _)}
    : Equivalence (@HCOL_equiv i o).
    Proof.
      unfold HCOL_equiv.
      constructor.
      unfold Reflexive. intros. auto.
      unfold Symmetric. intros. apply HCOL_extensionality. intros. symmetry. auto.
      unfold Transitive. intros. apply HCOL_extensionality. intros. rewrite H. auto.
    Qed.

    Global Instance HCOL_Setoid {i o}: Setoid (HOperator i o).
    Proof.
      unfold Setoid.
      apply HCOL_Equivalence.
    Qed.

    Section HCOL_Proper.

      Global Instance evalHCOL_proper_op_eq i o (op:HOperator i o):
        Setoid_Morphism (@evalHCOL i o op).
      Proof.
        split. apply vec_Setoid. apply vec_Setoid.
        intros v1 v2 vE.

        dependent induction op; simpl; unfold compose, Lst; try apply Vcons_single_elim.
        rewrite vE; reflexivity.
        rewrite vE; reflexivity.
        Case "Reduction".
        unfold Reduction. rewrite 2!Vfold_right_to_Vfold_right_reord.
        rewrite vE. reflexivity.    
        rewrite vE; reflexivity.
        Case "VMinus".
        unfold vector2pair. 
        rewrite vE. reflexivity.
        Case "PointWise2".
        unfold vector2pair. 
        rewrite vE. reflexivity.
        Case "ZVLess".
        unfold vector2pair.
        rewrite vE; reflexivity.
        Case "EvalPolynomial".
        rewrite vE; reflexivity.
        Case "MonomialEnumerator".
        rewrite vE; reflexivity.
        Case "ChebyshevDistance".
        unfold vector2pair.
        rewrite vE; reflexivity.
        Case "ScalaProd".
        unfold vector2pair.
        rewrite vE; reflexivity.
        Case "Induction".
        rewrite vE; reflexivity.

        Case "Compose".
        assert (evalHCOL op2 v1 = evalHCOL op2 v2). 
        apply IHop2. assumption.
        apply IHop1. assumption.
        
        Case "Cross".
        assert (V: vector2pair i1 v1 = vector2pair i1 v2).
        rewrite vE. reflexivity.

        assert(pF: Proper ((=) ==> (=)) (evalHCOL op1)).  auto.
        assert(pG: Proper ((=) ==> (=)) (evalHCOL op2)).  auto.
        rewrite V.
        reflexivity.

        Case "HOTLess".
        assert (V: vector2pair i1 v1 = vector2pair i1 v2).
        rewrite vE. reflexivity.
        destruct (vector2pair i1 v1) as (t0,t1).
        destruct (vector2pair i1 v2) as (t2,t3).
        assert  (M:evalHCOL op1 t0 = evalHCOL op1 t2).
        apply IHop1. apply V. rewrite M. clear M.
        assert  (M:evalHCOL op2 t1 = evalHCOL op2 t3).
        apply IHop2. apply V. rewrite M. clear M.
        reflexivity.
        
        Case "Stack".
        unfold Stack.
        assert  (M:evalHCOL op1 v1 = evalHCOL op1 v2).
        apply IHop1. assumption. rewrite M. clear M.
        assert  (M:evalHCOL op2 v1 = evalHCOL op2 v2).
        apply IHop2. assumption. rewrite M. clear M.
        reflexivity.
      Qed.

      Global Instance evalHCOL_proper i o :
        Proper ((=) ==> (=) ==> (=)) (@evalHCOL i o).
      Proof.
        intros o1 o2 oE  v1 v2 vE.
        rewrite vE.
        apply oE.
      Qed.
      
      Global Instance HOStack_proper i o1 o2:
        Proper ((=) ==> (=) ==> (=)) (@HOStack i o1 o2).
      Proof.
        intros op1 op1' op1E  op2 op2' op2E.
        unfold equiv, HCOL_equiv.
        intros.
        simpl.
        unfold pair2vector, Stack, compose.
        unfold equiv, HCOL_equiv in op1E.
        rewrite op1E, op2E.
        reflexivity.
      Qed.
      
      Global Instance HOCross_proper i1 o1 i2 o2:
        Proper ((=) ==> (=) ==> (=)) (@HOCross i1 o1 i2 o2).
      Proof.
        intros op1 op1' op1E  op2 op2' op2E.
        unfold equiv, HCOL_equiv.
        intros.
        simpl.
        unfold compose.
        generalize (vector2pair i1 x). intros.
        destruct p.
        unfold Cross.
        unfold pair2vector.
        rewrite op1E, op2E.
        reflexivity.
      Qed.

      Global Instance HOTLess_proper i1 i2 o:
        Proper ((=) ==> (=) ==> (=)) (@HOTLess i1 i2 o).
      Proof.
        intros op1 op1' op1E  op2 op2' op2E.
        unfold equiv, HCOL_equiv.
        intros.
        simpl.
        generalize (vector2pair i1 x). intros.
        destruct p.
        rewrite op1E, op2E.
        reflexivity.
      Qed.
      
      Global Instance HOCompose_proper i t o :
        Proper ((=) ==> (=) ==> (=)) (@HOCompose i t o).
      Proof.
        intros op1 op1' op1E  op2 op2' op2E.
        unfold equiv, HCOL_equiv.
        intros.
        simpl.
        unfold compose.
        rewrite op1E, op2E. 
        reflexivity.
      Qed.

    End HCOL_Proper.
  End HCOL_Eval.
End HCOL.
