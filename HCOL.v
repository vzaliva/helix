(* Coq defintions for HCOL operator language *)

Require Import VecUtil.
Require Import VecSetoid.
Require Import Spiral.
Require Import CarrierType.
Require Import HCOLImpl.

Require Import Arith.
Require Import Coq.Arith.Plus.
Require Import Program. (* compose *)
Require Import Morphisms.

Require Import CpdtTactics.
Require Import JRWTactics.
Require Import Coq.Logic.FunctionalExtensionality.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.implementations.peano_naturals.
Require Import MathClasses.theory.rings.
Require Import MathClasses.theory.setoids.

Import VectorNotations.
Open Scope vector_scope.

(* === HCOL operators === *)

Section HCOL_Language.

  Class HOperator {i o:nat} (op: avector i -> avector o) :=
    HOperator_setoidmor :> Setoid_Morphism op.

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

  Definition HPointwise
             {n: nat}
             (f: { i | i<n} -> CarrierA -> CarrierA)
             `{pF: !Proper ((=) ==> (=) ==> (=)) f}
             (x: avector n)
    := Vbuild (fun j jd => f (j ↾ jd) (Vnth x jd)).

  (* Special case of pointwise *)
  Definition HAtomic
             (f: CarrierA -> CarrierA)
             `{pF: !Proper ((=) ==> (=)) f}
             (x: avector 1)
    := [f (Vhead x)].

  Section HCOL_operators.

    Global Instance HPointwise_HOperator
           {n: nat}
           (f: { i | i<n} -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=)) f}:
      HOperator (@HPointwise n f pF).
    Proof.
      unfold HOperator. split; try (apply vec_Setoid).
      intros x y E.
      unfold HPointwise.
      vec_index_equiv i ip.
      rewrite 2!Vbuild_nth.
      assert(Vnth x ip = Vnth y ip).
      apply Vnth_arg_equiv; assumption.
      rewrite H.
      reflexivity.
    Qed.

    Global Instance HAtomic_HOperator
           (f: CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=)) f}:
      HOperator (HAtomic f).
    Proof.
      unfold HOperator. split; try (apply vec_Setoid).
      intros x y E.
      unfold HAtomic.
      vec_index_equiv i ip.
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

(* We forced to use this instead of usual 'reflexivity' tactics, as currently there is no way in Coq to define 'Reflexive' class instance constraining 'ext_equiv' function arguments by HOperator class *)
Ltac HOperator_reflexivity := eapply HOperator_functional_extensionality; reflexivity.

Section IgnoreIndex_wrapper.

  (* Wrapper to swap index parameter for HBinOp kernel with given value. 2 stands for arity of 'f' *)
  Definition SwapIndex2 {A} (i:nat) (f:nat->A->A->A) := const (B:=nat) (f i).

  Global Instance SwapIndex2_proper `{Setoid A}:
    Proper ((=) ==> ((=) ==> (=) ==> (=) ==> (=)) ==> (=) ==> (=) ==> (=) ==> (=)) (@SwapIndex2 A).
  Proof.
    simpl_relation.
    apply H1; assumption.
  Qed.

  (* Wrapper to ignore index parameter for HBinOp kernel. 2 stands for arity of 'f' *)
  Definition IgnoreIndex2 {A} (f:A->A->A) := const (B:=nat) f.

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
    (Proper (((=) ==> (=)) ==> (=) ==> (=) ==> (=) ==> (=)) (IgnoreIndex2)).
  Proof.
    simpl_relation.
    unfold IgnoreIndex2.
    apply H; assumption.
  Qed.

  (* Wrapper to ignore index parameter for HPointwise kernel. *)
  Definition IgnoreIndex {A:Type} {n:nat} (f:A->A) := const (B:=@sig nat (fun i : nat => @lt nat peano_naturals.nat_lt i n)) f.

  Global Instance IgnoredIndex_Proper {n:nat}:
    (Proper
       (((=) ==> (=)) ==> (=) ==> (=) ==> (=)) (IgnoreIndex (n:=n))).
  Proof.
    simpl_relation.
    unfold IgnoreIndex.
    apply H.
    assumption.
  Qed.

End IgnoreIndex_wrapper.

Section HCOL_Operator_Lemmas.

  Lemma HPointwise_nth
        {n: nat}
        (f: { i | i<n} -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}
        {j:nat} {jc:j<n}
        (x: avector n):
    Vnth (HPointwise f x) jc = f (j ↾ jc) (Vnth x jc).
  Proof.
    unfold HPointwise.
    rewrite Vbuild_nth.
    reflexivity.
  Qed.

  Lemma HBinOp_nth
        {o}
        {f: nat -> CarrierA -> CarrierA -> CarrierA}
        `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
        {v: avector (o+o)}
        {j:nat}
        {jc: j<o}
        {jc1:j<o+o}
        {jc2: (j+o)<o+o}
    :
      Vnth (@HBinOp o f pF v) jc = f j (Vnth v jc1) (Vnth v jc2).
  Proof.
    unfold HBinOp, compose, vector2pair, HBinOp, HCOLImpl.BinOp.

    break_let.

    replace t with (fst (Vbreak v)) by crush.
    replace t0 with (snd (Vbreak v)) by crush.
    clear Heqp.

    rewrite Vnth_Vmap2Indexed.
    f_equiv.

    rewrite Vnth_fst_Vbreak with (jc3:=jc1); reflexivity.
    rewrite Vnth_snd_Vbreak with (jc3:=jc2); reflexivity.
  Qed.

End HCOL_Operator_Lemmas.


