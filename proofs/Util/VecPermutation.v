
Require Import Coq.Arith.Arith.
Require Export Coq.Vectors.Vector.
Require Import Coq.Program.Equality. (* for dependent induction *)
Require Import Coq.Setoids.Setoid.
Require Import Coq.Logic.ProofIrrelevance.


(* CoLoR: `opam install coq-color`  *)
Require Export CoLoR.Util.Vector.VecUtil.

Open Scope vector_scope.

(* Re-define :: List notation for vectors. Probably not such a good idea *)
Notation "h :: t" := (cons h t) (at level 60, right associativity)
                     : vector_scope.

Import VectorNotations.

Section VPermutation.

  Variable A:Type.

  Inductive VPermutation: forall n, vector A n -> vector A n -> Prop :=
  | vperm_nil: VPermutation 0 [] []
  | vperm_skip {n} x l l' : VPermutation n l l' -> VPermutation (S n) (x::l) (x::l')
  | vperm_swap {n} x y l : VPermutation (S (S n)) (y::x::l) (x::y::l)
  | vperm_trans {n} l l' l'' :
      VPermutation n l l' -> VPermutation n l' l'' -> VPermutation n l l''.

  Local Hint Constructors VPermutation.

  (** Some facts about [VPermutation] *)

  Theorem VPermutation_nil : forall (l : vector A 0), VPermutation 0 [] l -> l = [].
  Proof.
    intros l HF.
    dependent destruction l.
    reflexivity.
  Qed.

  (** VPermutation over vectors is a equivalence relation *)

  Theorem VPermutation_refl : forall {n} (l: vector A n), VPermutation n l l.
  Proof.
    induction l; constructor. exact IHl.
  Qed.

  Theorem VPermutation_sym : forall {n} (l l' : vector A n),
      VPermutation n l l' -> VPermutation n l' l.
  Proof.
    intros n l l' Hperm.
    induction Hperm; auto.
    apply vperm_trans with (l'0:=l'); auto.
  Qed.

  Theorem VPermutation_trans : forall {n} (l l' l'' : vector A n),
      VPermutation n l l' -> VPermutation n l' l'' -> VPermutation n l l''.
  Proof.
    intros n l l' l''.
    apply vperm_trans.
  Qed.

End VPermutation.

Hint Resolve VPermutation_refl vperm_nil vperm_skip.

(* These hints do not reduce the size of the problem to solve and they
   must be used with care to avoid combinatoric explosions *)

Local Hint Resolve vperm_swap vperm_trans.
Local Hint Resolve VPermutation_sym VPermutation_trans.

(* This provides reflexivity, symmetry and transitivity and rewriting
   on morphims to come *)

Instance VPermutation_Equivalence A n : Equivalence (@VPermutation A n) | 10 :=
  {
    Equivalence_Reflexive := @VPermutation_refl A n ;
    Equivalence_Symmetric := @VPermutation_sym A n ;
    Equivalence_Transitive := @VPermutation_trans A n
  }.

Section VPermutation_properties.

Require Import Coq.Sorting.Permutation.
Require Import Spiral.VecUtil.


  Variable A:Type.

  Lemma ListVecPermutation {n} {l1 l2} {v1 v2}:
    l1 = list_of_vec v1 ->
    l2 = list_of_vec v2 ->
    Permutation l1 l2 <->
    VPermutation A n v1 v2.
  Proof.
    intros H1 H2.
    split.
    -
      intros P; revert n v1 v2 H1 H2.
      dependent induction P; intros n v1 v2 H1 H2.
      + dependent destruction v1; inversion H1; subst.
        dependent destruction v2; inversion H2; subst.
        apply vperm_nil.
      + dependent destruction v1; inversion H1; subst.
        dependent destruction v2; inversion H2; subst.
        apply vperm_skip.
        now apply IHP.
      + do 2 (dependent destruction v1; inversion H1; subst).
        do 2 (dependent destruction v2; inversion H2; subst).
        apply list_of_vec_eq in H5; subst.
        apply vperm_swap.
      + assert (n = length l').
        { pose proof (Permutation_length P1) as len.
          subst.
          now rewrite list_of_vec_length in len.
        }
        subst.
        apply vperm_trans with (l' := vec_of_list l').
        * apply IHP1; auto.
          now rewrite list_of_vec_vec_of_list.
        * apply IHP2; auto.
          now rewrite list_of_vec_vec_of_list.
    -
      subst l1 l2.
      intros P.
      dependent induction P.
      +
        subst; auto.
      +
        simpl.
        apply perm_skip.
        apply IHP.
      +
        simpl.
        apply perm_swap.
      +
        apply perm_trans with (l':=list_of_vec l'); auto.
  Qed.

End VPermutation_properties.

Lemma Vsig_of_forall_cons
      {A : Type}
      {n : nat}
      (P : A->Prop)
      (x : A)
      (l : vector A n)
      (P1h : P x)
      (P1x : @Vforall A P n l):
  (@Vsig_of_forall A P (S n) (@cons A x n l) (@conj (P x) (@Vforall A P n l) P1h P1x)) =
  (Vcons (@exist A P x P1h) (Vsig_of_forall P1x)).
Proof.
  simpl.
  f_equal.
  apply subset_eq_compat.
  reflexivity.
  f_equal.
  apply proof_irrelevance.
Qed.

Lemma VPermutation_Vsig_of_forall
      {n: nat}
      {A: Type}
      (P: A->Prop)
      (v1 v2 : vector A n)
      (P1 : Vforall P v1)
      (P2 : Vforall P v2):
  VPermutation A n v1 v2
  -> VPermutation {x : A | P x} n (Vsig_of_forall P1) (Vsig_of_forall P2).
Proof.
  intros V.
  revert P1 P2.
  dependent induction V; intros P1 P2.
  -
    apply vperm_nil.
  -
    destruct P1 as [P1h P1x].
    destruct P2 as [P2h P2x].
    rewrite 2!Vsig_of_forall_cons.
    replace P1h with P2h by apply proof_irrelevance.
    apply vperm_skip.
    apply IHV.
  -
    destruct P1 as [P1y [P1x P1l]].
    destruct P2 as [P1x' [P1y' P1l']].

    repeat rewrite Vsig_of_forall_cons.

    replace P1y' with P1y by apply proof_irrelevance.
    replace P1x' with P1x by apply proof_irrelevance.
    replace P1l' with P1l by apply proof_irrelevance.
    apply vperm_swap.
  -
    assert(Vforall P l').
    {
      apply Vforall_intro.
      intros x H.
      apply list_of_vec_in in H.
      eapply ListVecPermutation in V1; auto.
      apply Permutation_in with (l':=(list_of_vec l)) in H.
      +
        apply Vforall_lforall in P1.
        apply ListUtil.lforall_in with (l:=(list_of_vec l)); auto.
      +
        symmetry.
        auto.
    }
    (* Looks like a coq bug here. It should find H automatically *)
    unshelve eauto.
    apply H.
Qed.

