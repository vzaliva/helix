(* Coq defintions for Sigma-HCOL operator language *)

Require Import Spiral.
Require Import Rtheta.
Require Import SVector.
Require Import IndexFunctions.

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.BoolEq.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Require Import CpdtTactics.
Require Import JRWTactics.
Require Import CaseNaming.
Require Import SpiralTactics.
Require Import Psatz.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.theory.rings.
Require Import MathClasses.implementations.peano_naturals.
Require Import MathClasses.orders.orders.

(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.
Open Scope vector_scope.

Global Open Scope nat_scope.

(* Returns an element of the vector 'x' which is result of mapping of given
natrual number by index mapping function f_spec. *)
Definition VnthIndexMapped
           {i o:nat}
           (x: svector i)
           (f: index_map o i)
           (n:nat) (np: n<o)
  : Rtheta
  := Vnth x (« f » n np).

Definition VnthInverseIndexMapped
           {i o:nat}
           (x: svector i)
           (f': partial_index_map o i)
           (n:nat) (np: n<o)
  : Rtheta
  :=
    let f := partial_index_f _ _ f' in
    let f_spec := partial_index_f_spec _ _  f' in
    match (f n) as fn return f n ≡ fn -> Rtheta with
    | None => fun _ => Rtheta_szero
    | Some z => fun p => Vnth x (f_spec n np z p)
    end eq_refl.

Section SigmaHCOL_Operators.

  Definition Gather
             {i o: nat}
             (f: index_map o i)
             (x: svector i):
    svector o
    := Vbuild (VnthIndexMapped x f).

  Definition GathH
             {i o}
             (base stride: nat)
             {range_bound: ∀ x : nat, x < o → base + x * stride < i}
    :
      (svector i) -> svector o
    :=
      Gather
        (@h_index_map o i base stride range_bound).

  Definition Scatter
             {i o: nat}
             (f: index_map i o)
             (x: svector i) : svector o
    :=
      Vbuild (fun n np =>
                VnthInverseIndexMapped x (build_inverse_index_map f) n np).

  Definition ScatH
             {i o}
             (base stride: nat)
             {domain_bound: ∀ x : nat, x < i → base + x * stride < o}
    :
      (svector i) -> svector o
    :=
      Scatter
        (@h_index_map i o base stride domain_bound).

  Definition Pointwise
             {n: nat}
             (f: forall i, i<n -> Rtheta -> Rtheta)
             (x: svector n)
    := Vbuild (fun j jd => f j jd (Vnth x jd)).

  Definition Atomic
             (f: Rtheta -> Rtheta)
             (x: svector 1)
    := [f (Vhead x)].

End SigmaHCOL_Operators.

(* Specification of gather as mapping from ouptu to input. NOTE:
    we are using definitional equality here, as Scatter does not
    perform any operations on elements of type A *)
Lemma Gather_spec
      {i o: nat}
      (f: index_map o i)
      (x: svector i)
      (y: svector o):
  (Gather f x ≡ y) ->  ∀ n (ip : n < o), Vnth y ip ≡ VnthIndexMapped x f n ip.
Proof.
  unfold Gather, Vbuild.
  destruct (Vbuild_spec (VnthIndexMapped x f)) as [Vv Vs].
  simpl.
  intros.
  subst.
  auto.
Qed.

Lemma Gather_is_endomorphism:
  ∀ (i o : nat)
    (x : svector i),
  ∀ (f: index_map o i),
    Vforall (Vin_aux x)
            (Gather f x).
Proof.
  intros.
  apply Vforall_eq.
  intros.
  unfold Gather in H.
  unfold Vin_aux.
  apply Vbuild_in in H.
  crush.
  unfold VnthIndexMapped.
  apply Vnth_in.
Qed.

Lemma Gather_preserves_P:
  ∀ (i o : nat) (x : svector i) (P: Rtheta->Prop),
    Vforall P x
    → ∀ f : index_map o i,
      Vforall P (Gather f x).
Proof.
  intros.
  assert(Vforall (Vin_aux x) (Gather f x))
    by apply Gather_is_endomorphism.
  generalize dependent (Gather f x).
  intros t.
  rewrite 2!Vforall_eq.
  crush.
  assert (Vin_aux x x0) by (apply H0; assumption).
  rewrite Vforall_eq in H.
  crush.
Qed.

Lemma Gather_preserves_density:
  ∀ (i o : nat) (x : svector i)
    (f: index_map o i),
    svector_is_dense x ->
    svector_is_dense (Gather f x).
Proof.
  intros.
  unfold svector_is_dense in *.
  apply Gather_preserves_P.
  assumption.
Qed.

(* Specification of scatter as mapping from input to output. NOTE:
    we are using definitional equality here, as Scatter does not
    perform any operations on elements of type A *)
Lemma Scatter_spec
      {i o: nat}
      (f: index_map i o)
      (x: svector i)
      (y : svector o):
  index_map_injective f -> (Scatter f x ≡ y) ->  ∀ n (ip : n < i), Vnth x ip ≡ VnthIndexMapped y f n ip.
Proof.
  intros J S n ip.
  unfold VnthIndexMapped.
  unfold Scatter in S.
  subst y.
  rewrite Vbuild_nth.
  assert(L: partial_index_f o i (build_inverse_index_map f) (⟦f ⟧ n) ≡ Some n).
  {
    apply build_inverse_index_map_is_left_inverse; try assumption.
    reflexivity.
  }

  (* At this point 'rewrite L' should work but it does not, so we will generalize the hell out of it, and remove unnecessary hypothesis to work around this problem *)

  remember (build_inverse_index_map f) as f' eqn:F.
  unfold VnthInverseIndexMapped.

  generalize (partial_index_f_spec o i f' (⟦f ⟧ n) («f » n ip));  intros l.
  destruct (partial_index_f o i f' (⟦f ⟧ n)).
  inversion L.
  subst n0.
  generalize (l n eq_refl); intros l0.
  replace l0 with ip by apply proof_irrelevance.
  reflexivity.
  congruence.
Qed.

(* Specification of scatter as mapping from output to input.
    NOTE: we are using definitional equality here, as Scatter does not
    perform any operations on elements of type A *)
Lemma Scatter_rev_spec:
  forall
    {i o: nat}
    (f: index_map i o)
    (x: svector i)
    (y : svector o),
    (Scatter f x ≡ y) ->  (∀ n (ip : n < o), Vnth y ip ≡ VnthInverseIndexMapped x (build_inverse_index_map f) n ip).
Proof.
  intros i o f x y.
  unfold Scatter, Vbuild.
  destruct (Vbuild_spec
              (λ (n : nat) (np : n < o),
               VnthInverseIndexMapped x (build_inverse_index_map f) n np)) as [Vv Vs].
  simpl.
  intros.
  subst.
  auto.
Qed.


