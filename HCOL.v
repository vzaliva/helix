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
             (f: Rtheta->Rtheta->Rtheta)
             `{pF: !Proper ((=) ==> (=) ==> (=)) f}
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

  (* ***
    Section HOperator_def.
    (* HOperator is a record with contains actual operator function and Proper morphism proof *)
    
    Record HOperator {i o:nat} :=
      Build_HOperator {
          op: svector i -> svector o;
          opf: Proper ((=) ==> (=)) (op)
        }.
    
    Global Instance HOperator_equiv {i o:nat}: Equiv (@HOperator i o)
      := fun f g => (op f) = (op g).

  End HOperator_def.
   *)  

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
    
    (* *** Definition HOScalarProd {n}
      := Build_HOperator (n+n) 1 (@HScalarProd n) HScalarProd_proper. *)
    
    Global Instance HBinOp_proper {o}
           (f: Rtheta->Rtheta->Rtheta)
           `{pF: !Proper ((=) ==> (=) ==> (=)) f}:
      Proper ((=) ==> (=)) (@HBinOp o f pF).
    Proof.
      intros x y E.
      unfold HBinOp.
      unfold compose, Lst, vector2pair.
      rewrite E.
      reflexivity.
    Qed.

  (* ***
    Definition HOBinOp {o}
               (f: Rtheta->Rtheta->Rtheta)
               `{pF: !Proper ((=) ==> (=) ==> (=)) f}
      := Build_HOperator _ _ (@HBinOp o f pF) (HBinOp_proper f) .
   *)    
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

  (* ***
    Definition HOReduction {i}
               (f: Rtheta->Rtheta->Rtheta)
               `{pF: !Proper ((=) ==> (=) ==> (=)) f}
               (idv:Rtheta) :=
      Build_HOperator _ _  (@HReduction i f pF idv) (HReduction_proper f idv) .
*)    
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

  (* ***
    Definition HOEvalPolynomial {n} (a: svector n)
      := Build_HOperator _ _ (HEvalPolynomial a) (HEvalPolynomial_proper a).
*)    
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

  (* ***
    Definition  HOPrepend {i n} (a:svector n)
      := Build_HOperator _ _  (@HPrepend i n a) (HPrepend_proper a).
*)    
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

  (* ***
    Definition HOMonomialEnumerator n
      := Build_HOperator _ _  (HMonomialEnumerator n) (HMonomialEnumerator_proper n).
   *)    
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

  (* ***
    Definition HOInfinityNorm n :=
      Build_HOperator _ _ (@HInfinityNorm n) (HInfinityNorm_proper n).
*)    
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

  (* ***
    Definition HOInduction {n:nat}
               (f: Rtheta->Rtheta->Rtheta)
               `{pF: !Proper ((=) ==> (=) ==> (=)) f}
               (initial:Rtheta) :=
      Build_HOperator _ _ (HInduction n f initial) (HInduction_proper f initial).
*)    
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

  (* ***
    Definition HOChebyshevDistance h :=
      Build_HOperator _ _ (HChebyshevDistance h) (HChebyshevDistance_proper h).
*)    
    Global Instance HVMinus_proper h:
      Proper ((=) ==> (=)) (@HVMinus h).
    Proof.
      intros x y E.
      unfold HVMinus.
      unfold compose, Lst, vector2pair.
      rewrite E.
      reflexivity.
    Qed.

  (* ***
    Definition HOVMinus h :=
      Build_HOperator _ _ (@HVMinus h) (HVMinus_proper h).
*)    
  End HCOL_operators.
End HCOL_Language.
