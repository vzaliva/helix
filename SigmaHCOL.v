(* Experimental alternative Sigma-HCOL, which ignores errors *)

(* Coq defintions for Sigma-HCOL operator language *)

Require Import Spiral.
Require Import Rtheta.
Require Import HCOL.
Require Import HCOLSyntax.
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

(* "sparse" vector type: vector holding Rhteta values *)
Notation svector n := (vector Rtheta n) (only parsing).

Section SparseVectors.

  (* Construct vector of Rtheta values from vector of raw values of it's carrier type *)
  Definition svector_from_vector {n} (v:vector A n): svector n :=
    Vmap Rtheta_normal v.

  (* Project out carrier type values from vector of Rheta values *)
  Definition vector_from_svector {n} (v:svector n): vector A n :=
    Vmap RthetaVal v.

  (* Our definition of "dense" vector means that it does not contain "structural" values. *)
  
  Definition svector_is_dense {n} (v:svector n) : Prop :=
    Vforall (not ∘ Is_Struct) v.

  (* Construct "Zero svector". All values are structural zeros. *)
  Definition szero_svector n: svector n := Vconst Rtheta_szero n.
  
End SparseVectors.

(* Scalar union *)
Definition Union 
           (a b: Rtheta): Rtheta
  :=
    match a, b with
    |  (_, true, ae), (bv, false, be) => (bv, false, orb ae be) (* s0 + b = b *)
    |  (av, false, ae), (_, true, be) => (av, false, orb ae be) (* a + s0 = a *)
    |  (_, true, ae), (_, true, be) => (zero, true, orb ae be) (* s0 + s0 = s0 *)
    |  (_, false, _), (_, false, _) => Rtheta_szero_err (* a + b = s0, ERR ! *)
    end.


(* Stronger commutativity, wrt to 'eq' equality *)
Lemma Union_comm: ∀ x y : Rtheta, Union x y ≡ Union y x.
Proof.
  intros x y.
  destruct_Rtheta x.
  destruct_Rtheta y.
  destruct x1, x2, y1, y2; crush.
Qed.

(* Weaker commutativity, wrt to 'equiv' equality *)
Instance Rtheta_Commutative_Union:
  @Commutative Rtheta Rtheta_equiv Rtheta Union.
Proof.
  unfold Commutative.
  intros x y.
  rewrite Union_comm.
  reflexivity.
Qed.

(* Unary union of vector's elements (fold) *)
Definition VecUnion {n} (v:svector n): Rtheta :=
  Vfold_right Union v Rtheta_szero.

(* Binary element-wise union of two vectors *)
Definition Vec2Union {n} (a b: svector n): svector n
  := Vmap2 Union a b.

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

  Definition Scatter 
             {i o: nat}
             (f: index_map i o)
             (x: svector i) : svector o
    :=
      Vbuild (fun n np =>
                VnthInverseIndexMapped x (build_inverse_index_map f) n np).
  
  Definition GathH
             {i o}
             (base stride: nat)
             {range_bound: (base+(pred o)*stride) < i}
             {snz: stride ≢ 0} 
    :
      (svector i) -> svector o
    :=
      Gather 
        (@h_index_map o i base stride range_bound snz).
  
  Definition ScatH
             {i o}
             (base stride: nat)
             {domain_bound: (base+(pred i)*stride) < o}
             {snz: stride ≢ 0} 
    :
      (svector i) -> svector o
    :=
      Scatter 
        (@h_index_map i o base stride domain_bound snz).

  Definition Pointwise
             {n: nat}
             (f: forall i, i<n -> Rtheta -> Rtheta)
             (x: svector n)
    := Vbuild (fun j jd => f j jd (Vnth x jd)).

  Definition Atomic
             (f: Rtheta -> Rtheta)
             (x: svector 1)
    := [f (Vhead x)].
  
  Definition SumUnion
             {o n} (v: vector (svector o) n): svector o
    := Vfold_left Vec2Union (szero_svector o) v.
 
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


