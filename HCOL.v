(* Coq defintions for HCOL operator language *)

Require Import Spiral.
Require Import Rtheta.
Require Import SVector.
Require Import HCOLImpl.

Require Import Arith.
Require Import Coq.Arith.Plus.
Require Import Program. (* compose *)
Require Import Morphisms.

Require Import CpdtTactics.
Require Import JRWTactics.
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
Open Scope vector_scope.

(* === HCOL operators === *)

Section HCOL_Language.

  Definition HPrepend {i n} (a:svector n)
  : svector i -> svector (n+i)
    := Vapp a.

  Definition HInfinityNorm {i}
    : svector i -> svector 1
    := Vectorize ∘ InfinityNorm.

  Definition HReduction {i}
             (f: Rtheta->Rtheta->Rtheta)
             `{pF: !Proper ((=) ==> (=) ==> (=)) f}
             (idv:Rtheta)
    : svector i -> svector 1
    := Vectorize ∘ (Reduction f idv).

  Definition HAppend {i n} (a:svector n)
    : svector i -> svector (i+n)
    := fun x => Vapp x a.

  Definition HVMinus {o}
    : svector (o+o) -> svector o
    := VMinus  ∘ (vector2pair o).

  Definition HBinOp {o}
             (f: nat->Rtheta->Rtheta->Rtheta)
             `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
    : svector (o+o) -> svector o
    :=  BinOp f ∘ (vector2pair o).

  Definition HEvalPolynomial {n} (a: svector n): svector 1 -> svector 1
    := Lst ∘ EvalPolynomial a ∘ Scalarize.

  Definition HMonomialEnumerator n
    : svector 1 -> svector (S n)
    := MonomialEnumerator n ∘ Scalarize.

  Definition HChebyshevDistance h
    : svector (h+h) -> svector 1
    := Lst ∘ ChebyshevDistance ∘ (vector2pair h).

  Definition HScalarProd {h}
    : svector (h+h) -> svector 1
    := Lst ∘ ScalarProd ∘ (vector2pair h).

  Definition HInduction (n:nat)
             (f: Rtheta->Rtheta->Rtheta)
             `{pF: !Proper ((=) ==> (=) ==> (=)) f}
             (initial:Rtheta)
    : svector 1 -> svector n
    := Induction n f initial ∘ Scalarize.

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
  
  Section HCOL_operators.
    
    Global Instance HScalarProd_proper {n}:
      Proper ((=) ==> (=)) (@HScalarProd n).
    Proof.
      intros x y E.
      unfold HScalarProd.
      unfold compose, Lst, vector2pair.
      apply Vcons_single_elim.
      rewrite E.
      reflexivity.
    Qed.
    
    Global Instance HBinOp_proper {o}
           (f: nat->Rtheta->Rtheta->Rtheta)
           `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}:
      Proper ((=) ==> (=)) (@HBinOp o f pF).
    Proof.
      intros x y E.
      unfold HBinOp.
      unfold compose, Lst, vector2pair.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HReduction_proper {i}
           (f: Rtheta->Rtheta->Rtheta)
           `{pF: !Proper ((=) ==> (=) ==> (=)) f}
           (idv:Rtheta):
      Proper ((=) ==> (=)) (@HReduction i f pF idv).
    Proof.
      intros x y E.
      unfold HReduction .
      unfold compose, Lst, vector2pair.
      apply Vcons_single_elim.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HEvalPolynomial_proper {n} (a: svector n):
      Proper ((=) ==> (=)) (@HEvalPolynomial n a).
    Proof.
      intros x y E.
      unfold HEvalPolynomial.
      unfold compose, Lst, vector2pair.
      apply Vcons_single_elim.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HPrepend_proper {i n} (a:svector n):
      Proper ((=) ==> (=)) (@HPrepend i n a).
    Proof.
      intros x y E.
      unfold HPrepend.
      unfold compose, Lst, vector2pair.
      apply Vcons_single_elim.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HMonomialEnumerator_proper n:
      Proper ((=) ==> (=)) (@HMonomialEnumerator n).
    Proof.
      intros x y E.
      unfold HMonomialEnumerator.
      unfold compose, Lst, vector2pair.
      apply Vcons_single_elim.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HInfinityNorm_proper n:
      Proper ((=) ==> (=)) (@HInfinityNorm n).
    Proof.
      intros x y E.
      unfold HInfinityNorm.
      unfold compose, Lst, vector2pair.
      apply Vcons_single_elim.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HInduction_proper {n:nat}
           (f: Rtheta->Rtheta->Rtheta)
           `{pF: !Proper ((=) ==> (=) ==> (=)) f}
           (initial:Rtheta):
      Proper ((=) ==> (=)) (HInduction n f initial).
    Proof.
      intros x y E.
      unfold HInduction.
      unfold compose, Lst, vector2pair.
      apply Vcons_single_elim.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HChebyshevDistance_proper h:
      Proper ((=) ==> (=)) (HChebyshevDistance h).
    Proof.
      intros x y E.
      unfold HChebyshevDistance.
      unfold compose, Lst, vector2pair.
      apply Vcons_single_elim.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HVMinus_proper h:
      Proper ((=) ==> (=)) (@HVMinus h).
    Proof.
      intros x y E.
      unfold HVMinus.
      unfold compose, Lst, vector2pair.
      rewrite E.
      reflexivity.
    Qed.

  End HCOL_operators.
End HCOL_Language.
