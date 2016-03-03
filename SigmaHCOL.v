(* Coq defintions for Sigma-HCOL operator language *)

Require Import Spiral.
Require Import Rtheta.
Require Import MRtheta.
Require Import SVector.
Require Import IndexFunctions.
Require Import HCOL. (* Presently for HOperator only. Consider moving it elsewhere *)

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
           (x: mvector i)
           (f: index_map o i)
           (n:nat) (np: n<o)
  : MRtheta
  := Vnth x (« f » n np).

Definition VnthInverseIndexMapped
           {i o:nat}
           (x: mvector i)
           (f': partial_index_map o i)
           (n:nat) (np: n<o)
  : MRtheta
  :=
    let f := partial_index_f _ _ f' in
    let f_spec := partial_index_f_spec _ _  f' in
    match (f n) as fn return f n ≡ fn -> MRtheta with
    | None => fun _ => MRtheta_SZero
    | Some z => fun p => Vnth x (f_spec n np z p)
    end eq_refl.

Lemma VnthInverseIndexMapped_arg_equiv:
  ∀ (i o : nat)
    (x y : mvector i) (j : nat)
    (jp : j < o)
    (f' : partial_index_map o i),
    x = y
    → VnthInverseIndexMapped x f' j jp = VnthInverseIndexMapped y f' j jp.
Proof.
  intros i o x y j jp f' H.
  destruct f'.
  unfold VnthInverseIndexMapped; simpl.
  generalize (partial_index_f_spec j jp).
  destruct (partial_index_f j); intros.
  apply Vnth_arg_equiv; assumption.
  reflexivity.
Qed.

Section SigmaHCOL_Operators.

  Definition Gather
             {i o: nat}
             (f: index_map o i)
             (x: mvector i):
    mvector o
    := Vbuild (VnthIndexMapped x f).

  Global Instance Gather_HOperator
         {i o: nat}
         (f: index_map o i):
    HOperator (@Gather i o f).
  Proof.
    unfold HOperator. split; try (apply vec_Setoid).
    intros x y E.
    unfold Gather.
    unfold VnthIndexMapped.
    unfold equiv, vec_equiv.
    apply Vforall2_intro_nth; intros j jp.
    rewrite 2!Vbuild_nth.
    apply Vnth_arg_equiv; assumption.
  Qed.

  Definition GathH
             {i o}
             (base stride: nat)
             {domain_bound: ∀ x : nat, x < o → base + x * stride < i}
    :
      (mvector i) -> mvector o
    :=
      Gather (h_index_map base stride
                          (range_bound:=domain_bound) (* since we swap domain and range, domain bound becomes range boud *)
             ).

  Global Instance GathH_HOperator
         {i o}
         (base stride: nat)
         {domain_bound: ∀ x : nat, x < o → base + x * stride < i}:
    HOperator (@GathH i o base stride domain_bound).
  Proof.
    apply Gather_HOperator.
  Qed.

  Definition Scatter
             {i o: nat}
             (f: index_map i o)
             {f_inj: index_map_injective f}
             (x: mvector i) : mvector o
    :=
      Vbuild (fun n np =>
                VnthInverseIndexMapped x (build_inverse_index_map f) n np).

  Global Instance Scatter_HOperator
         {i o: nat}
         (f: index_map i o)
         {f_inj: index_map_injective f}:
    HOperator (@Scatter i o f f_inj).
  Proof.
    unfold HOperator. split; try (apply vec_Setoid).
    intros x y E.
    unfold Scatter.
    unfold equiv, vec_equiv.
    apply Vforall2_intro_nth.
    intros j jp.
    rewrite 2!Vbuild_nth.
    apply VnthInverseIndexMapped_arg_equiv.
    assumption.
  Qed.

  Definition ScatH
             {i o}
             (base stride: nat)
             {range_bound: ∀ x : nat, x < i → base + x * stride < o}
             {snzord0: stride ≢ 0 \/ i < 2}
    :
      (mvector i) -> mvector o
    :=
      Scatter (h_index_map base stride (range_bound:=range_bound))
              (f_inj := h_index_map_is_injective base stride (snzord0:=snzord0)).

  Global Instance ScatH_HOperator
         {i o}
         (base stride: nat)
         {range_bound: ∀ x : nat, x < i → base + x * stride < o}
         {snzord0: stride ≢ 0 \/ i < 2}:
    HOperator (@ScatH i o base stride range_bound snzord0).
  Proof.
    apply Scatter_HOperator.
  Qed.

  Definition Pointwise
             {n: nat}
             (f: { i | i<n} -> MRtheta -> MRtheta)
             `{pF: !Proper ((=) ==> (=) ==> (=)) f}
             (x: mvector n)
    := Vbuild (fun j jd => f (j ↾ jd) (Vnth x jd)).

  Global Instance Pointwise_HOperator
         {n: nat}
         (f: { i | i<n} -> MRtheta -> MRtheta)
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

  Definition Atomic
             (f: MRtheta -> MRtheta)
             `{pF: !Proper ((=) ==> (=)) f}
             (x: mvector 1)
    := [f (Vhead x)].

  Global Instance Atomic_HOperator
         (f: MRtheta -> MRtheta)
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

End SigmaHCOL_Operators.

(* Specification of gather as mapping from ouptu to input. NOTE:
    we are using definitional equality here, as Scatter does not
    perform any operations on elements of type A *)
Lemma Gather_spec
      {i o: nat}
      (f: index_map o i)
      (x: mvector i)
      (y: mvector o):
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
    (x : mvector i),
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
  ∀ (i o : nat) (x : mvector i) (P: MRtheta -> Prop),
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
  ∀ (i o : nat) (x : mvector i)
    (f: index_map o i),
    mvector_is_dense x ->
    mvector_is_dense (Gather f x).
Proof.
  intros.
  unfold mvector_is_dense in *.
  apply Gather_preserves_P.
  assumption.
Qed.

(* Specification of scatter as mapping from input to output. NOTE:
    we are using definitional equality here, as Scatter does not
    perform any operations on elements of type A *)
Lemma Scatter_spec
      {i o: nat}
      (f: index_map i o)
      {f_inj: index_map_injective f}
      (x: mvector i)
      (n: nat) (ip : n < i):
  Vnth x ip ≡ VnthIndexMapped (Scatter f (f_inj:=f_inj) x) f n ip.
Proof.
  unfold VnthIndexMapped.
  unfold Scatter.
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
Lemma Scatter_rev_spec
      {i o: nat}
      (f: index_map i o)
      {f_inj: index_map_injective f}
      (x: mvector i)
      (n: nat)
      (ip : n < o):
  Vnth (Scatter f (f_inj:=f_inj) x) ip ≡
       VnthInverseIndexMapped x (build_inverse_index_map f) n ip.
Proof.
  unfold Scatter, Vbuild.
  destruct (Vbuild_spec
              (λ (n : nat) (np : n < o),
               VnthInverseIndexMapped x (build_inverse_index_map f) n np)) as [Vv Vs].
  simpl.
  auto.
Qed.

