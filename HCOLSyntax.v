(* Coq defintions for HCOL operator language *)

Require Import Spiral.
Require Import Rtheta.
Require Import SVector.

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

Require Import HCOL.
Import HCOLOperators.
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

  Definition HLess {o}
    : svector (o+o) -> svector o
    := ZVLess  ∘ (vector2pair o).

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

  (* HCompose becomes just ∘ *)

  Definition HTLess {i1 i2 o}
             (lop1: svector i1 -> svector o)
             (lop2: svector i2 -> svector o)
    : svector (i1+i2) -> svector o
    := fun v0 => let (v1,v2) := vector2pair i1 v0 in
              ZVLess (lop1 v1, lop2 v2).
  
  Definition HCross
             {i1 o1 i2 o2}
             `(xop1pf: !Proper ((=) ==> (=)) (xop1: svector i1 -> svector o1))
             `(xop2pf: !Proper ((=) ==> (=)) (xop2: svector i2 -> svector o2))
    : svector (i1+i2) -> svector (o1+o2)
    := pair2vector ∘ (Cross (xop1, xop2)) ∘ (vector2pair i1).
    
  Definition HStack {i o1 o2}
             (op1: svector i -> svector o1)
             (op2: svector i -> svector o2)
    : svector i -> svector (o1+o2)
    := pair2vector ∘ (Stack (op1, op2)).


  (* HOperator is a record with contains actual operator function and Proper morphism proof *)
  
  Record HOperator (i o:nat) :=
    Build_HOperator {
        op: svector i -> svector o;
        opf: Proper ((=) ==> (=)) (op)
      }.
  
  Global Instance HOperator_equiv {i o:nat}:
    Equiv (HOperator i o)
    :=
      fun f g => (op _ _ f) = (op _ _ g).
  
  
  Section HCOL_Morphisms.

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
    
    Definition HOScalarProd {n}: @HOperator (n+n) 1
      := Build_HOperator (n+n) 1 (@HScalarProd n) HScalarProd_proper.
    
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

    Global Instance HTLess_proper {i1 i2 o}
           `{!Proper ((=) ==> (=)) (lop1: svector i1 -> svector o)}
           `{!Proper ((=) ==> (=)) (lop2: svector i2 -> svector o)}:
      Proper ((=) ==> (=)) (@HTLess i1 i2 o lop1 lop2).
    Proof.
      intros x y E.
      unfold HTLess, vector2pair.
      destruct (Vbreak x) as [x0 x1] eqn: X.
      destruct (Vbreak y) as [y0 y1] eqn: Y.
      assert(Ye: Vbreak y = (y0, y1)) by crush.
      assert(Xe: Vbreak x = (x0, x1)) by crush.
      rewrite E in Xe.
      rewrite Xe in Ye.
      clear X Y Xe E.
      inversion Ye. simpl in *.
      rewrite H, H0.
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
       
    Global Instance HCross_arg_proper
           {i1 o1 i2 o2}
           `{xop1pf: !Proper ((=) ==> (=)) (xop1: svector i1 -> svector o1)}
           `{xop2pf: !Proper ((=) ==> (=)) (xop2: svector i2 -> svector o2)}:
      Proper ((=) ==> (=)) (HCross xop1pf xop2pf).
    Proof.
      intros x y E.
      unfold HCross.
      unfold compose, pair2vector, vector2pair.
      destruct (Vbreak x) as [x0 x1] eqn: X.
      destruct (Vbreak y) as [y0 y1] eqn: Y.
      assert(Ye: Vbreak y = (y0, y1)) by crush.
      assert(Xe: Vbreak x = (x0, x1)) by crush.
      rewrite E in Xe.
      rewrite Xe in Ye.
      clear X Y Xe E.
      inversion Ye. simpl in *.
      rewrite H, H0.
      reflexivity.
    Qed.

    (*
    Global Instance HCross_proper {i1 o1 i2 o2}:
      Proper ((=) ==> (=) ==> (=)) (@HCross i1 o1 i2 o2).
    Proof.
      intros op1 op2 E1 xop1 xop2 E2.
      unfold HCross.
      unfold compose, pair2vector, vector2pair.
      destruct (Vbreak x) as [x0 x1] eqn: X.
      destruct (Vbreak y) as [y0 y1] eqn: Y.
      assert(Ye: Vbreak y = (y0, y1)) by crush.
      assert(Xe: Vbreak x = (x0, x1)) by crush.
      rewrite E in Xe.
      rewrite Xe in Ye.
      clear X Y Xe E.
      inversion Ye. simpl in *.
      rewrite H, H0.
      reflexivity.
    Qed.
*)
    
    
  (*
      Global Instance HStack_proper i o1 o2:
        Proper ((=) ==> (=) ==> (=)) (@HStack i o1 o2).
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
      
      Global Instance HCross_proper i1 o1 i2 o2:
        Proper ((=) ==> (=) ==> (=)) (@HCross i1 o1 i2 o2).
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

   *)
  End HCOL_Morphisms.
End HCOL_Language.
