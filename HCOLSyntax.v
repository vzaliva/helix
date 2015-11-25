(* Coq defintions for HCOL operator language *)

Require Import Spiral.
Require Import Rtheta.
Require Import SVector.

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
Require Import MathClasses.theory.setoids.

(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

Require Import HCOL.
Import HCOLOperators.
Open Scope vector_scope.

(* === HCOL operators === *)

Section HCOL_Language.

  Definition HOPrepend {i n} (a:svector n)
  : svector i -> svector (n+i)
    := Vapp a.

  Definition HOInfinityNorm {i}
    : svector i -> svector 1
    := Vectorize ∘ InfinityNorm.

  Definition HOReduction {i}
             (f: Rtheta->Rtheta->Rtheta)
             `{pF: !Proper ((=) ==> (=) ==> (=)) f}
             (idv:Rtheta)
    : svector i -> svector 1
    := Vectorize ∘ (Reduction f idv).

  Definition HOAppend {i n} (a:svector n)
    : svector i -> svector (i+n)
    := fun x => Vapp x a.

  Definition HOVMinus {o}
    : svector (o+o) -> svector o
    := VMinus  ∘ (vector2pair o).

  Definition HOBinOp {o}
             (f: Rtheta->Rtheta->Rtheta)
             `{pF: !Proper ((=) ==> (=) ==> (=)) f}
    : svector (o+o) -> svector o
    :=  BinOp f ∘ (vector2pair o).

  Definition HOLess {o}
    : svector (o+o) -> svector o
    := ZVLess  ∘ (vector2pair o).

  Definition HOEvalPolynomial {n} (a: svector n): svector 1 -> svector 1
    := Lst ∘ EvalPolynomial a ∘ Scalarize.

  Definition HOMonomialEnumerator n
    : svector 1 -> svector (S n)
    := MonomialEnumerator n ∘ Scalarize.

  Definition HOChebyshevDistance h
    : svector (h+h) -> svector 1
    := Lst ∘ ChebyshevDistance ∘ (vector2pair h).

  Definition HOScalarProd {h}
    : svector (h+h) -> svector 1
    := Lst ∘ ScalarProd ∘ (vector2pair h).

  Definition HOInduction {n}
             (f: Rtheta->Rtheta->Rtheta)
             `{pF: !Proper ((=) ==> (=) ==> (=)) f}
             (initial:Rtheta)
    : svector 1 -> svector n
    := Induction n f initial ∘ Scalarize.

  (* HOCompose becomes just ∘ *)

  Definition HOTLess {i1 i2 o}
             (lop1: svector i1 -> svector o)
             (lop2: svector i2 -> svector o)
    : svector (i1+i2) -> svector o
    := fun v0 => let (v1,v2) := vector2pair i1 v0 in
              ZVLess (lop1 v1, lop2 v2).
  
  Definition HOCross
             {i1 o1 i2 o2}
             (xop1: svector i1 -> svector o1)
             (xop2: svector i2 -> svector o2)
    : svector (i1+i2) -> svector (o1+o2)
    := pair2vector ∘ (Cross (xop1, xop2)) ∘ (vector2pair i1).

  
  Definition HOStack {i o1 o2}
             (op1: svector i -> svector o1)
             (op2: svector i -> svector o2)
    : svector i -> svector (o1+o2)
    := pair2vector ∘ (Stack (op1, op2)).
  
  Section HCOL_Morphisms.

    Global Instance HOScalarProd_proper {n}:
      Proper ((=) ==> (=)) (@HOScalarProd n).
    Proof.
      intros x y E.
      unfold HOScalarProd.
      unfold compose, Lst, vector2pair.
      apply Vcons_single_elim.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HOBinOp_proper {o}
           (f: Rtheta->Rtheta->Rtheta)
           `{pF: !Proper ((=) ==> (=) ==> (=)) f}:
      Proper ((=) ==> (=)) (@HOBinOp o f pF).
    Proof.
      intros x y E.
      unfold HOBinOp.
      unfold compose, Lst, vector2pair.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HOReduction_proper {i}
           (f: Rtheta->Rtheta->Rtheta)
           `{pF: !Proper ((=) ==> (=) ==> (=)) f}
           (idv:Rtheta):
      Proper ((=) ==> (=)) (@HOReduction i f pF idv).
    Proof.
      intros x y E.
      unfold HOReduction .
      unfold compose, Lst, vector2pair.
      apply Vcons_single_elim.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance Compose_Setoid_Morphism
           `{Setoid A}`{Setoid B} `{Setoid C}
           `{Am: !Setoid_Morphism (f : B → C)}
           `{Bm: !Setoid_Morphism (g : A → B)}:
      Setoid_Morphism (f ∘ g).
    Proof.
      split; try assumption.
      unfold compose.
      intros x y E.
      rewrite E.
      reflexivity.
    Qed.

    Lemma HOperator_functional_extensionality
          {m n: nat}
          `{!Proper ((=) ==> (=)) (f : svector m → svector n)}
          `{!Proper ((=) ==> (=)) (g : svector m → svector n)} :
      (∀ v, f v = g v) -> f = g.
    Proof.
      assert(Setoid_Morphism g).
      split; try apply vec_Setoid. assumption.
      assert(Setoid_Morphism f).
      split; try apply vec_Setoid. assumption.
      apply ext_equiv_applied_iff.
    Qed.
    
    
  (*
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
   *)
  End HCOL_Morphisms.
End HCOL_Language.
