
Require Import Helix.Util.VecUtil.

Require Import Coq.Arith.Arith.
Require Import Coq.Program.Basics. (* for \circ notation *)
Require Export Coq.Vectors.Vector.
Require Import Omega.

Require Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders.
Require Import MathClasses.orders.minmax MathClasses.orders.orders MathClasses.orders.rings.
Require Import MathClasses.theory.rings MathClasses.theory.abs.
Require Import MathClasses.theory.naturals.

Require Export CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

Require Import Helix.Tactics.HelixTactics.


(* Various definitions related to vector equality and setoid rewriting *)

Section VectorSetoid.

  Global Instance vec_Equiv `{Equiv A} {n}: Equiv (vector A n)
    := Vforall2 (n:=n) equiv.

  Global Instance vec_Equivalence `{Ae: Equiv A} {n:nat}
         `{!Equivalence (@equiv A _)}
    : Equivalence (@vec_Equiv A Ae n).
  Proof.
    unfold vec_Equiv.
    apply Vforall2_equiv.
    assumption.
  Qed.

  Global Instance vec_Setoid `{Setoid A} {n}: Setoid (vector A n).
  Proof.
    unfold Setoid.
    apply vec_Equivalence.
  Qed.

End VectorSetoid.


Global Instance Vconst_proper (A:Type) `{Ae: Equiv A}:
  Proper ((=) ==> forall_relation
              (fun (n : nat) => (@vec_Equiv A _ n)))
         (@Vconst A).
Proof.
  intros a a' aa'.
  intros n.
  induction n.
  - crush.
  -
    simpl.
    unfold equiv, vec_Equiv.
    rewrite Vforall2_cons_eq.
    split; assumption.
Qed.

(* We also have `Proper` instance for `Vold_left_rev` called `Vfold_left_rev_Vforall2` *)
Global Instance Vfold_left_rev_proper
       (A B : Type)
       `{Ae: Equiv A}
       `{Be: Equiv B}:
  Proper (((=) ==> (=) ==> (=)) ==>
                            forall_relation
                            (fun (n : nat) => (=) ==> (@vec_Equiv B _ n) ==> (=)))
         (@Vfold_left_rev A B).
Proof.
  intros f f' Ef n a a' Ea v v' Ev.

  induction v; simpl; intros.
  -
    VOtac.
    simpl.
    apply Ea.
  -
    revert Ev. VSntac v'.
    unfold vec_Equiv.
    rewrite Vforall2_cons_eq. intuition. simpl.
    apply Ef; auto.
Qed.

Global Instance Vfold_left_rev_arg_proper
       (A B : Type)
       `{Ae: Equiv A}
       `{Aeq: Equivalence A Ae}
       `{Be: Equiv B}
       (f : A → B → A)
       `{f_mor: !Proper ((=) ==> (=) ==> (=)) f}
       (n : nat)
       (initial : A)
  :
    Proper ((=) ==> (=)) (@Vfold_left_rev A B f n initial).
Proof.
  intros v v' Ev.
  induction n; simpl; intros.
  -
    dep_destruct v.
    dep_destruct v'.
    reflexivity.
  -
    dep_destruct v.
    dep_destruct v'.
    simpl.
    apply f_mor.
    apply IHn.
    apply Ev.
    apply Ev.
Qed.

Global Instance Vfold_right_proper
       (A B : Type)
       `{Ae: Equiv A}
       `{Be: Equiv B}:
  Proper (((=) ==> (=) ==> (=)) ==>
                            forall_relation
                            (fun (n : nat) => (@vec_Equiv A _ n) ==> (=) ==> (=)))
         (@Vfold_right A B).
Proof.
  intros f f' Ef n v v' Ev a a' Ea.

  induction v; simpl; intros.
  -
    VOtac.
    simpl.
    apply Ea.
  -
    revert Ev. VSntac v'.
    unfold vec_Equiv.
    rewrite Vforall2_cons_eq. intuition. simpl.
    apply Ef; auto.
Qed.

Global Instance Vfold_right_arg_proper
       (A B : Type)
       `{Ae: Equiv A}
       `{Be: Equiv B}
       (f: A → B → B)
       `{f_mor: !Proper ((=) ==> (=) ==> (=)) f}
       {n:nat}
  :
    Proper ((@vec_Equiv A _ n) ==> (=) ==> (=))
         (@Vfold_right A B f n).
Proof.
  apply Vfold_right_proper.
  apply f_mor.
Qed.

Lemma Vcons_single_elim `{Ae: Equiv A} : forall a1 a2,
    Vcons a1 (@Vnil A) = Vcons a2 (@Vnil A) <-> a1 = a2.
Proof.
  intros a1 a2.
  unfold equiv, vec_Equiv.
  rewrite Vforall2_cons_eq.
  assert(Vforall2 equiv (@Vnil A) (@Vnil A)).
  constructor.
  split; tauto.
Qed.

Lemma Vcons_equiv_elim (A:Type) `{Equiv A}: forall a1 a2 n (v1 v2 : vector A n),
    Vcons a1 v1 = Vcons a2 v2 -> a1 = a2 /\ v1 = v2.
Proof.
  intros. auto.
Qed.

Lemma Vcons_equiv_intro (A:Type) `{Equiv A} : forall a1 a2 n (v1 v2 : vector A n),
    a1 = a2 -> v1 = v2 -> Vcons a1 v1 = Vcons a2 v2.
Proof.
  intros.
  apply Vforall2_cons_eq; auto.
Qed.

Global Instance Vcons_proper (A:Type) `{Equiv A}:
  Proper ((=) ==> forall_relation
              (fun (n : nat) => (@vec_Equiv A _ n) ==> (@vec_Equiv A _ (S n))))
         (@Vcons A).
Proof.
  intros a a' Ea.
  intros n.
  intros b b' Eb.
  induction n.
  -
    dep_destruct b.
    dep_destruct b'.
    apply Vcons_single_elim, Ea.
  -
    eapply Vcons_equiv_intro; auto.
Qed.

Global Instance Vcons_arg_proper (A:Type) `{As: Setoid A} {n} {x:A}:
  Proper ((@vec_Equiv A _ n) ==> (@vec_Equiv A _ (S n)))
         (@Vcons A x n).
Proof.
  apply Vcons_proper; reflexivity.
Qed.

Global Instance Vapp_proper `{Sa: Setoid A} (n1 n2:nat):
  Proper ((=) ==>  (=) ==> (=)) (@Vapp A n1 n2).
Proof.
  intros a0 a1 aEq b0 b1 bEq.
  induction n1.
  VOtac. auto.

  dep_destruct a0.
  dep_destruct a1.
  rewrite 2!Vapp_cons.

  assert (h=h0).
  apply aEq.

  rewrite H.

  unfold equiv, vec_Equiv.
  apply Vforall2_cons_eq.
  split. reflexivity.

  unfold equiv, vec_Equiv in IHn1.
  apply IHn1.
  apply aEq.
Qed.

Global Instance Vhead_proper `{Equiv A} n:
  Proper ((=) ==> (=)) (@Vhead A n).
Proof.
  intros a b E.
  dep_destruct a.  dep_destruct b.
  unfold equiv, vec_Equiv, vec_Equiv, relation in E.
  rewrite Vforall2_cons_eq in E.
  intuition.
Qed.

Global Instance Vtail_proper `{Equiv A} n:
  Proper ((=) ==> (=)) (@Vtail A n).
Proof.
  intros a b E.
  unfold equiv, vec_Equiv, vec_Equiv, relation in E.
  apply Vforall2_tail in E.
  unfold vec_Equiv.
  assumption.
Qed.

Global Instance Ptail_proper `{Sa: Setoid A} `{Sb: Setoid B} (n:nat):
  Proper ((=) ==> (=)) (@Ptail A B n).
Proof.
  intros x y E.
  destruct x as [xa xb].
  destruct y as [ya yb].
  destruct E as [E1 E2].
  simpl in E1. simpl in E2.
  unfold Ptail.
  rewrite E1, E2.
  reflexivity.
Qed.

(* Handy tactics to break down equality of two vectors into element-wise equality of theirm elements using index *)
Ltac vec_index_equiv j jc :=
  match goal with
  | [ |- ?a = ?b] => let j' := fresh j in
                   let jc' := fresh jc in
                   unfold equiv, vec_Equiv;
                   apply Vforall2_intro_nth;
                   intros j' jc'
  | [ |- ?a ≡ ?b] => let j' := fresh j in
                   let jc' := fresh jc in
                   apply Veq_nth; intros j' jc'
 end.

Lemma Vfold_right_Vmap_equiv
      {A B C: Type}
      `{Setoid B}
      {n: nat}
      (f : A->B->B)
      (g : C->A)
      (x : vector C n)
      (z:B)
  : Vfold_right f (Vmap g x) z = Vfold_right (f∘g) x z.
Proof.
  rewrite Vfold_right_Vmap.
  reflexivity.
Qed.

Lemma Vmap_as_Vbuild {A B:Type} `{Setoid B}:
  ∀ (n : nat) (v : vector A n) (f:A->B),
    Vmap f v = Vbuild (λ (j : nat) (jd : (j < n)%nat), f (Vnth v jd)).
Proof.
  intros n v f.
  vec_index_equiv i ip.
  rewrite Vnth_map.
  rewrite Vbuild_nth.
  reflexivity.
Qed.

Lemma Vmap2_cons_hd: forall A B C `{Setoid C} (f:A->B->C) n (a:vector A (S n)) (b:vector B (S n)),
    Vmap2 f a b = Vcons (f (Vhead a) (Vhead b)) (Vmap2 f (Vtail a) (Vtail b)).
Proof.
  intros.
  dep_destruct a.
  dep_destruct b.
  reflexivity.
Qed.

Lemma Vmap2_cons: forall A B C `{Setoid C} (f:A->B->C) n (a:A) (b:B) (a':vector A n) (b':vector B n),
    Vmap2 f (Vcons a a') (Vcons b b') = Vcons (f a b) (Vmap2 f a' b').
Proof.
  intros.
  reflexivity.
Qed.

Lemma Vmap2_comm
      (A B:Type)
      `{CO:Commutative B A f}
      `{SB: !Setoid B} {n:nat}:
  Commutative (Vmap2 f (n:=n)).
Proof.
  unfold Commutative.
  intros a b.
  induction n.
  dep_destruct a.
  dep_destruct b.
  reflexivity.
  rewrite Vmap2_cons_hd by apply SB.

  setoid_rewrite <- Vmap2_cons; auto.
  simpl.
  rewrite commutativity.
  apply Vcons_proper.
  reflexivity.
  apply IHn.
Qed.

Lemma hd_equiv: forall `{Equiv A} {n} (u v: vector A (S n)), u=v -> (Vhead u) = (Vhead v).
Proof.
  intros.
  f_equiv.
  assumption.
Qed.

Lemma vector1_equiv_Vhead_equiv
      {A: Type}
      `{As: Equiv A}
      {a b: vector A 1}:
  Vhead a = Vhead b -> a = b.
Proof.
  intros H.
  dep_destruct a.
  dep_destruct b.
  dep_destruct x.
  dep_destruct x0.
  apply Vcons_single_elim.
  simpl in H.
  assumption.
Qed.

Global Instance Vmap_proper (A B:Type) `{Ae: Equiv A} `{Be: Equiv B}:
  Proper (
      ((=) ==> (=)) ==> (forall_relation
                       (fun (n : nat) => (@vec_Equiv A _ n) ==> (@vec_Equiv B _ n))))
         (@Vmap A B).
Proof.
    intros f f' Ef n v v' Ev.
    induction n.
    -
      VOtac; auto.
    -
      dep_destruct v. dep_destruct v'.
      split.
      +
        inversion Ev.
        apply Ef, H.
      + apply IHn, Ev.
Qed.

Global Instance Vmap_arg_proper  (M N:Type) `{Me:!Equiv M} `{Ne: !Equiv N} (f : M->N)
       `{fP: !Proper (Me ==> Ne) f} (n:nat):
  Proper ((@vec_Equiv M _ n) ==> (@vec_Equiv N _ n)) (@Vmap M N f n).
Proof.
  intros a b Ea.
  induction n.
  -
    VOtac; auto.
  -
    dep_destruct a. dep_destruct b.
    split.
    apply fP, Ea.
    apply IHn, Ea.
Qed.


Global Instance VBreak_proper (A:Type) `{Setoid A} (n1 n2:nat) `{Plus nat}:
  Proper ((=) ==> (=)) (@Vbreak A n1 n2).
Proof.
  intros v v1 vE.
  induction n1.
  simpl. setoid_rewrite vE. reflexivity.
  assert (V1: v ≡ Vapp (fst (Vbreak (n1:=1) v)) (snd (Vbreak (n1:=1) v))).
  {
    simpl. dep_destruct v. reflexivity.
  }
  assert (V2: v1 ≡ Vapp (fst (Vbreak (n1:=1) v1)) (snd (Vbreak (n1:=1) v1))).
  {
    simpl. dep_destruct v1. reflexivity.
  }
  rewrite V1. clear V1. rewrite V2. clear V2.
  dep_destruct v. dep_destruct v1.
  simpl.

  assert (E: Vbreak x = Vbreak x0).
  {
    apply IHn1.  apply vE.
  }
  f_equiv.
  +
    apply Vcons_proper.
    inversion vE.
    auto.
    rewrite E.
    reflexivity.
  +
    rewrite E.
    reflexivity.
Qed.

Section Vnth.

  Lemma Vnth_arg_equiv:
    ∀ (A : Type) (Ae : Equiv A) (n : nat) (v1 v2 : vector A n)
      (i : nat) (ip : i < n), v1 = v2 → Vnth v1 ip = Vnth v2 ip.
  Proof.
    intros A Ae n v1 v2 i ip E.
    unfold equiv, vec_Equiv in E.
    apply Vforall2_elim_nth with (i:=i) (ip:=ip) in E.
    assumption.
  Qed.

  Lemma Vnth_equiv `{Equiv A}: forall n (v1 v2 : vector A n) i1 (h1 : i1<n) i2 (h2 : i2<n),
      i1 = i2 -> v1 = v2 -> Vnth v1 h1 = Vnth v2 h2.
  Proof.
    intros n v1 v2 i1 h1 i2 h2 Ei Ev.
    rewrite Vnth_eq with (h2:=h2) by assumption.
    apply Vnth_arg_equiv.
    assumption.
  Qed.

  Global Instance Vnth_aux_arg_proper {n j : nat} (jc:j<n) (A:Type) `{Equiv A}:
    Proper ((=) ==> (=)) (@Vnth_aux A n j jc).
  Proof.
    intros x y E.
    dependent induction n.
    -
      VOtac.
      nat_lt_0_contradiction.
    -
      rewrite (VSn_eq x).
      rewrite (VSn_eq y).
      simpl.
      break_match.
      +
        rewrite (VSn_eq x) in E.
        rewrite (VSn_eq y) in E.
        apply E.
      +
        apply IHn.
        rewrite (VSn_eq x) in E.
        rewrite (VSn_eq y) in E.
        apply E.
  Qed.

  Global Instance Vnth_proper {n : nat} (A:Type) `{Equiv A}:
    Proper ((=) ==> (forall_relation
                     (fun i => pointwise_relation (i < n)%nat equiv)))
           (@Vnth A n).
  Proof.
    intros x y E i ic.
    dependent induction n.
    -
      VOtac.
      nat_lt_0_contradiction.
    -
      rewrite (VSn_eq x).
      rewrite (VSn_eq y).
      simpl.
      break_match.
      +
        rewrite (VSn_eq x) in E.
        rewrite (VSn_eq y) in E.
        apply E.
      +
        apply IHn.
        rewrite (VSn_eq x) in E.
        rewrite (VSn_eq y) in E.
        apply E.
  Qed.

End Vnth.

Global Instance Vmap2Indexed_proper
       `{Equiv A, Equiv B, Equiv C} {n:nat}
  :
    Proper (((=) ==> (=) ==> (=) ==> (=)) ==> (=) ==> (=) ==> (=))
           (@Vmap2Indexed A B C n).
Proof.
  intros fa fb Ef a a' Ea b b' Eb.
  unfold Vmap2Indexed.

  vec_index_equiv i ip.
  rewrite 2!Vbuild_nth.
  apply Ef.
  - reflexivity.
  - apply Vnth_equiv.
    reflexivity.
    assumption.
  - apply Vnth_equiv.
    reflexivity.
    assumption.
Qed.

Global Instance Vmap2SigIndexed_proper
       `{Equiv A, Equiv B, Equiv C} {n:nat}
  :
    Proper (((=) ==> (=) ==> (=) ==> (=)) ==> (=) ==> (=) ==> (=))
           (@Vmap2SigIndexed A B C n).
Proof.
  intros fa fb Ef a a' Ea b b' Eb.
  unfold Vmap2SigIndexed.

  vec_index_equiv i ip.
  rewrite 2!Vbuild_nth.
  apply Ef.
  - reflexivity.
  - apply Vnth_equiv.
    reflexivity.
    assumption.
  - apply Vnth_equiv.
    reflexivity.
    assumption.
Qed.

(* TODO: Check why this is needed *)
Global Instance indexed_vector_equiv `{Equiv A} {n}:
  Equiv (∀ i : nat, i < n → vector A n)
  :=  @forall_relation nat
                       (fun i : nat =>  forall _ : i<n, vector A n)
                       (fun i : nat =>  @pointwise_relation (i < n)
                                                       (vector A n) (=)).

(* @jwiegley version: *)
Global Instance Vbuild_proper {n : nat} {A:Type} `{Equiv A}:
  Proper ((forall_relation
             (fun i => pointwise_relation (i < n)%nat equiv)) ==> equiv)
         (@Vbuild A n).
Proof.
  intros f f' E.
  unfold forall_relation, pointwise_relation in E.
  unfold equiv, vec_Equiv; apply Vforall2_intro_nth; intros j jc.
  rewrite 2!Vbuild_nth.
  apply E.
Qed.

