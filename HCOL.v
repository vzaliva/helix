(* Coq defintions for HCOL operator language *)

Require Import Spiral.
Require Import CarrierType.
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

  Class HOperator {i o:nat} (op: avector i -> avector o) :=
    o_setoidmor :> Setoid_Morphism op.

  Lemma HOperator_functional_extensionality
        {m n: nat}
        `{HOperator m n f}
        `{HOperator m n g}:
    (∀ v, f v = g v) -> f = g.
  Proof.
    unfold HOperator in *.
    apply ext_equiv_applied_iff.
  Qed.

  Definition HPrepend {i n} (a:avector n)
    : avector i -> avector (n+i)
    := Vapp a.

  Definition HInfinityNorm {i}
    : avector i -> avector 1
    := Vectorize ∘ InfinityNorm.

  Definition HReduction {i}
             (f: CarrierA -> CarrierA -> CarrierA)
             `{pF: !Proper ((=) ==> (=) ==> (=)) f}
             (idv: CarrierA)
    : avector i -> avector 1
    := Vectorize ∘ (Reduction f idv).

  Definition HAppend {i n} (a:avector n)
    : avector i -> avector (i+n)
    := fun x => Vapp x a.

  Definition HVMinus {o}
    : avector (o+o) -> avector o
    := VMinus  ∘ (vector2pair o).

  Definition HBinOp {o}
             (f: nat -> CarrierA -> CarrierA -> CarrierA)
             `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
    : avector (o+o) -> avector o
    :=  BinOp f ∘ (vector2pair o).

  Definition HEvalPolynomial {n} (a: avector n): avector 1 -> avector 1
    := Lst ∘ EvalPolynomial a ∘ Scalarize.

  Definition HMonomialEnumerator n
    : avector 1 -> avector (S n)
    := MonomialEnumerator n ∘ Scalarize.

  Definition HChebyshevDistance h
    : avector (h+h) -> avector 1
    := Lst ∘ ChebyshevDistance ∘ (vector2pair h).

  Definition HScalarProd {h}
    : avector (h+h) -> avector 1
    := Lst ∘ ScalarProd ∘ (vector2pair h).

  Definition HInduction (n:nat)
             (f: CarrierA -> CarrierA -> CarrierA)
             `{pF: !Proper ((=) ==> (=) ==> (=)) f}
             (initial: CarrierA)
    : avector 1 -> avector n
    := Induction n f initial ∘ Scalarize.

  Section HCOL_operators.

    Global Instance Pointwise_HOperator
           {n: nat}
           (f: { i | i<n} -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=)) f}:
      HOperator (@Pointwise n f pF).
    Proof.
      unfold HOperator. split; try (apply vec_Setoid).
      intros x y E.
      unfold Pointwise.
      apply Vforall2_intro_nth.
      intros i ip.
      rewrite 2!Vbuild_nth.
      assert(Vnth x ip = Vnth y ip).
      apply Vnth_arg_equiv; assumption.
      rewrite H.
      reflexivity.
    Qed.

    Global Instance Atomic_HOperator
           (f: CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=)) f}:
      HOperator (Atomic f).
    Proof.
      unfold HOperator. split; try (apply vec_Setoid).
      intros x y E.
      unfold Atomic.
      unfold equiv, vec_equiv.
      apply Vforall2_intro_nth.
      intros.
      simpl.
      dep_destruct i.
      rewrite E.
      reflexivity.
      reflexivity.
    Qed.

    Global Instance HScalarProd_HOperator {n}:
      HOperator (@HScalarProd n).
    Proof.
      unfold HOperator. split; try (apply vec_Setoid).
      intros x y E.
      unfold HScalarProd.
      unfold compose, Lst, vector2pair.
      apply Vcons_single_elim.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HBinOp_HOperator {o}
           (f: nat -> CarrierA -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}:
      HOperator (@HBinOp o f pF).
    Proof.
      unfold HOperator. split; try (apply vec_Setoid).
      intros x y E.
      unfold HBinOp.
      unfold compose, Lst, vector2pair.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HReduction_HOperator {i}
           (f: CarrierA -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=)) f}
           (idv: CarrierA):
      HOperator (@HReduction i f pF idv).
    Proof.
      unfold HOperator. split; try (apply vec_Setoid).
      intros x y E.
      unfold HReduction .
      unfold compose, Lst, vector2pair.
      apply Vcons_single_elim.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HEvalPolynomial_HOperator {n} (a: avector n):
      HOperator (@HEvalPolynomial n a).
    Proof.
      unfold HOperator. split; try (apply vec_Setoid).
      intros x y E.
      unfold HEvalPolynomial.
      unfold compose, Lst, vector2pair.
      apply Vcons_single_elim.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HPrepend_HOperator {i n} (a:avector n):
      HOperator (@HPrepend i n a).
    Proof.
      unfold HOperator. split; try (apply vec_Setoid).
      intros x y E.
      unfold HPrepend.
      unfold compose, Lst, vector2pair.
      apply Vcons_single_elim.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HMonomialEnumerator_HOperator n:
      HOperator (@HMonomialEnumerator n).
    Proof.
      unfold HOperator. split; try (apply vec_Setoid).
      intros x y E.
      unfold HMonomialEnumerator.
      unfold compose, Lst, vector2pair.
      apply Vcons_single_elim.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HInfinityNorm_HOperator n:
      HOperator (@HInfinityNorm n).
    Proof.
      unfold HOperator. split; try (apply vec_Setoid).
      intros x y E.
      unfold HInfinityNorm.
      unfold compose, Lst, vector2pair.
      apply Vcons_single_elim.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HInduction_HOperator {n:nat}
           (f: CarrierA -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=)) f}
           (initial: CarrierA):
      HOperator (HInduction n f initial).
    Proof.
      unfold HOperator. split; try (apply vec_Setoid).
      intros x y E.
      unfold HInduction.
      unfold compose, Lst, vector2pair.
      apply Vcons_single_elim.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HChebyshevDistance_HOperator h:
      HOperator (HChebyshevDistance h).
    Proof.
      unfold HOperator. split; try (apply vec_Setoid).
      intros x y E.
      unfold HChebyshevDistance.
      unfold compose, Lst, vector2pair.
      apply Vcons_single_elim.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HVMinus_HOperator h:
      HOperator (@HVMinus h).
    Proof.
      unfold HOperator. split; try (apply vec_Setoid).
      intros x y E.
      unfold HVMinus.
      unfold compose, Lst, vector2pair.
      rewrite E.
      reflexivity.
    Qed.

  End HCOL_operators.
End HCOL_Language.

Section IgnoreIndex_wrapper.

  (* Wrapper to replace index parameter for HBinOp kernel. 2 stands for arity of 'f' *)
  Definition SwapIndex2 {A} (i:nat) (f:nat->A->A->A) := fun (_:nat) => f i.

  Global Instance SwapIndex2_proper `{Setoid A} (i:nat)
         (f:nat->A->A->A) `{f_mor: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}:
    Proper ((=) ==> (=) ==> (=) ==> (=)) (@SwapIndex2 A i f).
  Proof.
    intros a a' Ea b b' Eb y y' Ey.
    unfold SwapIndex2.
    f_equiv; assumption.
  Qed.

  (* Wrapper to ignore index parameter for HBinOp kernel. 2 stands for arity of 'f' *)
  Definition IgnoreIndex2 {A} (f:A->A->A) := fun (i:nat) => f.

  Lemma IgnoreIndex2_ignores `{Setoid A}
        (f:A->A->A)`{f_mor: !Proper ((=) ==> (=) ==> (=)) f}
    : forall i0 i1,
      (IgnoreIndex2 f) i0 = (IgnoreIndex2 f) i1.
  Proof.
    intros.
    unfold IgnoreIndex2.
    apply f_mor.
  Qed.

  Global Instance IgnoreIndex2_proper:
    (Proper (((=) ==> (=)) ==> (=)) IgnoreIndex2).
  Proof.
    simpl_relation.
    apply H; assumption.
  Qed.

  Global Instance IgnoreIndex2_preserves_proper
         (f: CarrierA -> CarrierA -> CarrierA)
         `{pF: !Proper ((=) ==> (=) ==> (=)) f}
    :
      (Proper ((=) ==> (=) ==> (=) ==> (=)) (IgnoreIndex2 f)).
  Proof.
    simpl_relation.
    unfold IgnoreIndex2.
    rewrite H0, H1.
    reflexivity.
  Qed.


End IgnoreIndex_wrapper.


