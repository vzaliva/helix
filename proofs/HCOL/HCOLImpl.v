(* Low-level functions implementing HCOL matrix and vector manupulation operators *)

Require Import Spiral.VecUtil.
Require Import Spiral.VecSetoid.
Require Import Spiral.Spiral.
Require Import Spiral.CarrierType.

Require Import Coq.Arith.Arith.
Require Import Coq.Program.Program. (* compose *)
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relations.

Require Import Spiral.SpiralTactics.

Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.theory.rings.


Import VectorNotations.

Open Scope vector_scope.
Open Scope nat_scope.

Section HCOL_implementations.

  (* --- Type casts --- *)

  (* Promote scalar to unit vector *)
  Definition Vectorize (x:CarrierA): (avector 1) := [x].

  Global Instance Vectorize_proper:
    Proper ((=) ==> (=)) Vectorize.
  Proof.
    unfold Vectorize.
    intros x y E.
    apply Vcons_single_elim, E.
  Qed.

  (* Convert single element vector to scalar *)
  Definition Scalarize (x: avector 1) : CarrierA := Vhead x.

  (* --- Scalar Product --- *)

  Definition ScalarProd
             {n} (ab: (avector n)*(avector n)) : CarrierA :=
    match ab with
    | (a, b) => Vfold_right plus (Vmap2 mult a b) zero
    end.

  (* --- Infinity Norm --- *)
  Definition InfinityNorm
             {n} (v: avector n) : CarrierA :=
    Vfold_right max (Vmap abs v) zero.

  (* --- Chebyshev Distance --- *)
  Definition ChebyshevDistance
             {n} (ab: (avector n)*(avector n)): CarrierA :=
    match ab with
    | (a, b) => InfinityNorm (Vmap2 sub a b)
    end.

  (* --- Vector Subtraction --- *)
  Definition VMinus
             {n} (ab: (avector n)*(avector n)) : avector n :=
    match ab with
    | (a,b) => Vmap2 ((+)∘(-)) a b
    end.

  (* --- Monomial Enumerator --- *)

  Fixpoint MonomialEnumerator
           (n:nat) (x:CarrierA) {struct n} : avector (S n) :=
    match n with
    | O => [one]
    | S p => Vcons one (Vmap (mult x) (MonomialEnumerator p x))
    end.

  (* --- Polynomial Evaluation --- *)

  Fixpoint EvalPolynomial {n}
           (a: avector n) (x:CarrierA) : CarrierA  :=
    match a with
      nil => zero
    | a0 :: a' => plus a0 (mult x (EvalPolynomial a' x))
    end.

  (* === HCOL Basic Operators === *)

  (* Arity 2 function lifted to vectors. Also passes index as first parameter *)
  Definition BinOp {n}
             (f: FinNat n -> CarrierA -> CarrierA -> CarrierA)
             (ab: (avector n)*(avector n))
    : avector n :=
    match ab with
    | (a,b) =>  Vmap2SigIndexed f a b
    end.

  (* --- Induction --- *)

  Definition Induction (n:nat) (f:CarrierA -> CarrierA -> CarrierA)
           (initial: CarrierA) (v: CarrierA) : avector n
    := nat_rect _ [] (fun _ t => Vcons initial (Vmap (fun x => f x v) t)) n.


  (* Old, equal, definition:
  Fixpoint Induction' (n:nat) (f:CarrierA -> CarrierA -> CarrierA)
           (initial: CarrierA) (v: CarrierA) {struct n} : avector n
    :=
      match n with
      | O => []
      | S p => Vcons initial (Vmap (fun x => f x v) (Induction p f initial v))
      end.
   *)

  Definition Inductor (n:nat) (f:CarrierA -> CarrierA -> CarrierA)
           (initial: CarrierA) (v:CarrierA)
    : CarrierA :=  nat_rect _ initial (fun _ x => f x v) n.

  (* Old, equal definition:
  Fixpoint Inductor' (n:nat) (f:CarrierA -> CarrierA -> CarrierA)
           (initial: CarrierA) (v:CarrierA) {struct n}
    : CarrierA :=
    match n with
    | O => initial
    | S p => f (Inductor p f initial v) v
    end.
   *)


  (* --- Reduction --- *)

  (*  Reduction (fold) using single finction. In case of empty list returns 'id' value:
    Reduction f x1 .. xn b = f xn (f x_{n-1} .. (f x1 id) .. )
   *)
  Definition Reduction {n:nat}
             (f: CarrierA -> CarrierA -> CarrierA)
             (id:CarrierA) (a: avector n) : CarrierA
    :=
      Vfold_right f a id.

  (* --- Scale --- *)
  Definition Scale
             {n} (sv:(CarrierA)*(avector n)) : avector n :=
    match sv with
    | (s,v) => Vmap (mult s) v
    end.

  (* --- Concat ---- *)
  Definition Concat {an bn: nat} (ab: (avector an)*(avector bn)) : avector (an+bn) :=
    match ab with
      (a,b) => Vapp a b
    end.

End HCOL_implementations.

(* === Lemmas about functions defined above === *)

Section HCOL_implementation_facts.

  Lemma Induction_cons
        {n: nat}
        {initial: CarrierA}
        {f:CarrierA -> CarrierA -> CarrierA}
        {v:CarrierA}:
    Induction (S n) f initial v = Vcons initial (Vmap (fun x => f x v) (Induction n f initial v)).
  Proof.
    intros; dep_destruct n; reflexivity.
  Qed.

  Lemma EvalPolynomial_reduce:
    forall n (a: avector (S n)) (x:CarrierA),
      EvalPolynomial a x  =
      plus (Vhead a) (mult x (EvalPolynomial (Vtail a) x)).
  Proof.
    intros; dep_destruct a; reflexivity.
  Qed.

  Lemma ScalarProd_reduce:
    forall n (ab: (avector (S n))*(avector (S n))),
      ScalarProd ab = plus (mult (Vhead (fst ab)) (Vhead (snd ab))) (ScalarProd (Ptail ab)).
  Proof.
    intros; dep_destruct ab.
    reflexivity.
  Qed.

  Lemma MonomialEnumerator_cons:
    forall n (x:CarrierA),
      MonomialEnumerator (S n) x = Vcons one (Scale (x, (MonomialEnumerator n x))).
  Proof.
    intros n x.
    destruct n; simpl; reflexivity.
  Qed.

  Lemma ScalarProd_comm: forall n (a b: avector n),
      ScalarProd (a,b) = ScalarProd (b,a).
  Proof.
    intros.
    unfold ScalarProd.
    setoid_replace (Vmap2 mult a b) with (Vmap2 mult b a).
    reflexivity.
    apply Vmap2_comm; typeclasses eauto.
  Qed.

  Lemma ScalarProduct_descale: forall {n} (a b: avector n) (s:CarrierA),
      [ScalarProd ((Scale (s,a)), b)] = Scale (s, [(ScalarProd (a,b))]).
  Proof.
    intros.
    unfold Scale, ScalarProd.
    simpl.
    induction n.
    - (* Case "n=0". *)
      crush.
      VOtac.
      simpl.
      symmetry.
      unfold equiv, vec_Equiv, Vforall2, Vforall2_aux.
      split; try trivial.
      ring.
    - (* Case "S(n)". *)
      VSntac a.  VSntac b.
      simpl.
      symmetry.
      rewrite plus_mult_distr_l.

      (* Remove cons from IHn *)
      assert (HIHn:  forall a0 b0 : avector n, equiv (Vfold_right plus (Vmap2 mult (Vmap (mult s) a0) b0) zero)
                                                (mult s (Vfold_right plus (Vmap2 mult a0 b0) zero))).
      {
        intros.
        rewrite <- Vcons_single_elim.
        apply IHn.
      }
      clear IHn.

      rewrite HIHn.

      setoid_replace (mult s (mult (Vhead a) (Vhead b))) with (mult (mult s (Vhead a)) (Vhead b))
        by apply mult_assoc.
      reflexivity.
  Qed.

  Lemma ScalarProduct_hd_descale: forall {n} (a b: avector n) (s:CarrierA),
      ScalarProd ((Scale (s,a)), b) = Vhead (Scale (s, [(ScalarProd (a,b))])).
  Proof.
    intros.
    apply hd_equiv with (u:=[ScalarProd ((Scale (s,a)),b)]).
    apply ScalarProduct_descale.
  Qed.

End HCOL_implementation_facts.

Section HCOL_implementation_proper.

  Global Instance Scale_proper
         `{!Proper ((=) ==> (=) ==> (=)) mult} (n:nat)
  :
    Proper ((=) ==> (=)) (Scale (n:=n)).
  Proof.
    intros x y Ex.
    destruct x as [xa xb]. destruct y as [ya yb].
    destruct Ex as [H0 H1].
    simpl in H0, H1.
    unfold Scale.
    induction n.
    (* Case "n=0". *)
    VOtac.
    reflexivity.
    (* Case "S n". *)

    dep_destruct xb.  dep_destruct yb.  split.
    assert (HH: h=h0) by apply H1.
    rewrite HH, H0.
    reflexivity.

    setoid_replace (Vmap (mult xa) x) with (Vmap (mult ya) x0).
    replace (Vforall2_aux equiv (Vmap (mult ya) x0) (Vmap (mult ya) x0))
    with (Vforall2 equiv (Vmap (mult ya) x0) (Vmap (mult ya) x0)).
    reflexivity.

    unfold Vforall2. reflexivity.

    apply IHn. clear IHn.
    apply H1.
  Qed.

  Global Instance ScalarProd_proper (n:nat):
    Proper ((=) ==> (=))
           (ScalarProd (n:=n)).
  Proof.
    intros x y Ex.
    destruct x as [xa xb].
    destruct y as [ya yb].
    unfold ScalarProd.
    destruct Ex as [H0 H1].
    simpl in H0, H1.
    rewrite H0, H1.
    reflexivity.
  Qed.

  Global Instance InfinityNorm_proper {n:nat}:
    Proper ((=) ==> (=))
           (InfinityNorm (n:=n)).
  Proof.
    unfold Proper.
    intros a b E1.
    unfold InfinityNorm.
    rewrite E1.
    reflexivity.
  Qed.

  Global Instance BinOp_proper {n:nat}:
    Proper (((=) ==> (=) ==> (=) ==> (=)) ==> (=) ==> (=)) (BinOp (n:=n)).
  Proof.
    intros fa fb Ef a b Ea.
    unfold BinOp.
    destruct a. destruct b.
    destruct Ea as [E1 E2]. simpl in *.
    apply Vmap2SigIndexed_proper; assumption.
  Qed.

  Global Instance Reduction_proper {n:nat}:
    Proper (((=) ==> (=) ==>  (=)) ==> (=) ==> (=) ==> (=)) (Reduction (n:=n)).
  Proof.
    unfold Proper.
    intros fa fb Ef a b E1 x y E2.
    unfold Reduction.
    eapply Vfold_right_proper; assumption.
  Qed.

  Global Instance ChebyshevDistance_proper  (n:nat):
    Proper ((=) ==> (=))  (ChebyshevDistance (n:=n)).
  Proof.
    intros p p' pE.
    dep_destruct p.
    dep_destruct p'.
    unfold ChebyshevDistance.
    inversion pE. clear pE. simpl in *.
    clear p p'.
    rewrite H, H0.
    reflexivity.
  Qed.

  Global Instance EvalPolynomial_proper (n:nat):
    Proper ((=) ==> (=) ==> (=))  (EvalPolynomial (n:=n)).
  Proof.
    intros v v' vE a a' aE.
    induction n.
    VOtac.
    reflexivity.
    rewrite 2!EvalPolynomial_reduce.
    dep_destruct v.
    dep_destruct v'.
    simpl.
    apply Vcons_equiv_elim in vE.
    destruct vE as [HE xE].
    setoid_replace (EvalPolynomial x a) with (EvalPolynomial x0 a')
      by (apply IHn; assumption).
    rewrite HE, aE.
    reflexivity.
  Qed.

  Global Instance MonomialEnumerator_proper (n:nat):
    Proper ((=) ==> (=))  (MonomialEnumerator n).
  Proof.
    intros a a' aE.
    induction n.
    reflexivity.
    rewrite 2!MonomialEnumerator_cons, IHn, aE.
    reflexivity.
  Qed.

  Global Instance Inductor_proper {n:nat}:
    Proper (((=) ==> (=) ==> (=)) ==> (=) ==> (=) ==> (=)) (@Inductor n).
  Proof.
    intros f f' fEq ini ini' iniEq v v' vEq.
    induction n.
    -
      unfold Inductor.
      apply iniEq.
    -
      simpl.
      apply fEq.
      apply IHn.
      apply vEq.
  Qed.

  Global Instance Induction_proper {n:nat}:
    Proper (((=) ==> (=) ==> (=)) ==> (=) ==> (=) ==> (=)) (@Induction n).
  Proof.
    intros f f' fEq ini ini' iniEq v v' vEq.
    induction n.
    reflexivity.
    rewrite 2!Induction_cons.

    apply Vcons_proper.
    apply iniEq.
    eapply Vmap_proper.
    -
      unfold equiv, ext_equiv.
      intros a b E.
      apply fEq; auto.
    -
      apply IHn.
  Qed.

  Global Instance VMinus_proper (n:nat):
    Proper ((=) ==> (=))
           (@VMinus n).
  Proof.
    intros a b E.
    unfold VMinus.
    repeat break_let.
    destruct E as [E1 E2]; simpl in *.
    rewrite E1, E2.
    reflexivity.
  Qed.

End HCOL_implementation_proper.

Close Scope nat_scope.
Close Scope vector_scope.


