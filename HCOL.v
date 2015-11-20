(* Coq defintions for HCOL operator language *)

Require Import Spiral.
Require Import Rtheta.
Require Import SVector.

Require Import Arith.
Require Import Program. (* compose *)
Require Import Morphisms.
Require Import RelationClasses.
Require Import Relations.

Require Import CpdtTactics.
Require Import CaseNaming.
Require Import Coq.Logic.FunctionalExtensionality.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.theory.rings.

(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

Open Scope vector_scope.

(* === HCOL Semantics === *)

Module HCOLOperators.
  
  (* --- Highger order operators --- *)

  (* Apply 2 functions to the same input returning tuple of results *)
  Definition Stack {D R S: Type} (fg:(D->R)*(D->S)) (x:D) : (R*S) :=
    match fg with
      | (f,g) => pair (f x) (g x)
    end.

  (* Apply 2 functions to 2 inputs returning tuple of results *)
  Definition Cross {D R E S: Type} (fg:(D->R)*(E->S)) (x:D*E) : (R*S) :=
    match fg with
      | (f,g) => match x with
                   | (x0,x1) => pair (f x0) (g x1)
                 end
    end.

  (* --- Type casts --- *)

  (* Promote scalar to unit vector *)
  Definition Vectorize (x:Rtheta): (svector 1) := [x].

  (* Convert single element vector to scalar *)
  Definition Scalarize (x: svector 1) : Rtheta := Vhead x.

  (* --- Scalar Product --- *)

  Definition ScalarProd 
             {n} (ab: (svector n)*(svector n)) : Rtheta :=
    match ab with
      | (a, b) => Vfold_right (+) (Vmap2 (.*.) a b) 0
    end.

  (* --- Infinity Norm --- *)
  Definition InfinityNorm
             {n} (v: svector n) : Rtheta :=
    Vfold_right (max) (Vmap (abs) v) 0.

  (* --- Chebyshev Distance --- *)
  Definition ChebyshevDistance 
             {n} (ab: (svector n)*(svector n)): Rtheta :=
    match ab with
      | (a, b) => InfinityNorm (Vmap2 (plus∘negate) a b)
    end.    

  (* --- Vector Subtraction --- *)
  Definition VMinus 
             {n} (ab: (svector n)*(svector n)) : svector n := 
    match ab with
      | (a,b) => Vmap2 ((+)∘(-)) a b
    end.

  (* --- Pointwise Comparison --- *)

  (* Zero/One version *)
  Definition ZVLess {n} 
             {A:Type} `{Lt A} `{Altdec: !∀ x y: A, Decision (x < y)}
             {Z:Type} `{Zero Z, One Z}
             (ab: (vector A n)*(vector A n)) : vector Z n :=
    match ab with
      | (a,b) => Vmap2 (Zless) a b
    end.

  (* --- Monomial Enumerator --- *)

  Fixpoint MonomialEnumerator `{One A, Mult A}
           (n:nat) (x:A) {struct n} : vector A (S n) :=
    match n with 
      | O => [1]
      | S p => Vcons 1 (Vmap (mult x) (MonomialEnumerator p x))
    end.

  (* --- Polynomial Evaluation --- *)

  Fixpoint EvalPolynomial {n} `{SemiRing A}
           (a: vector A n) (x:A) : A  :=
    match a with
        nil => 0
      | cons a0 p a' => a0 + (x * (EvalPolynomial a' x))
    end.

  (* === HCOL Basic Operators === *)

  (* --- Pointwise with single function and two vectors (most common case) --- *)
  Definition PointWise2 {A B C: Type} (f: A->B->C) {n} (ab: (vector A n)*(vector B n)) : vector C n :=
    match ab with
      | (a,b) =>  Vmap2 f a b
    end.

  (* --- Pointwise with single function and one vector --- *)
  Definition PointWise1 {A B: Type} (f: A->B) {n} (a: vector A n) : vector B n := 
    Vmap f a.
  
  (* --- Pointwise with list of functions and two vectors --- *)
  Fixpoint PointWiseF2 {A B C: Type} {n} : (vector (A->B->C) n) -> (vector A n)*(vector B n) -> (vector C n)  := 
    match n return  (vector (A->B->C) n) -> (vector A n)*(vector B n) -> (vector C n)  with
        0 => fun _ _ => Vnil
      | S p => fun  f ab => match ab with
                              | (a,b) => Vcons ((Vhead f) (Vhead a) (Vhead b)) (PointWiseF2 (Vtail f) ((Vtail a), (Vtail b)))
                            end
    end.
  
  (* --- Pointwise with list of functions and one vector --- *)
  Fixpoint PointWiseF1 {A B: Type} {n} : (vector (A->B) n) -> (vector A n) -> (vector B n)  := 
    match n return  (vector (A->B) n) -> (vector A n) -> (vector B n)  with
        0 => fun _ _ => Vnil
      | S p => fun  f a => Vcons ((Vhead f) (Vhead a)) (PointWiseF1 (Vtail f) (Vtail a))
    end.

  (* --- Induction --- *)

  Fixpoint Induction {A B:Type} (n:nat) (f:B->A->B) (initial:B) (v:A) {struct n} : vector B n :=
    match n with 
      | O => []
      | S p => Vcons initial (Vmap (fun x => f x v) (Induction p f initial v))
    end.

  Fixpoint Inductor {A B:Type} (n:nat) (f:B->A->B) (initial:B) (v:A) {struct n} : B :=
    match n with 
      | O => initial
      | S p => f (Inductor p f initial v) v
    end.

  (* --- Reduction --- *)

  (*  Reduction (fold) using single finction. In case of empty list returns 'id' value:
    Reduction f x1 .. xn b = f xn (f x_{n-1} .. (f x1 id) .. )
   *)
  Definition Reduction {A B: Type} (f: A->B->B) {n} (id:B) (a: vector A n) : B := 
    Vfold_right f a id.

  (* --- Atomic --- *)

  (* Atomic with 2 arguments *)
  Definition Atomic2 {A B C: Type} := @prod_curry A B C.

  (* --- Scale --- *)
  Definition Scale `{Mult A}
             {n} (sv:A*(vector A n)) : vector A n :=
    match sv with
      | (s,v) => Vmap (mult s) v
    end.

  (* --- Concat ---- *)
  Definition Concat {A} {an bn: nat} (ab: (vector A an)*(vector A bn)) : vector A (an+bn) :=
    match ab with
        (a,b) => Vapp a b
    end.

End HCOLOperators.

Import HCOLOperators.

(* === Lemmas about HCOL operators === *)

Lemma Induction_reduce A B `{Setoid A, Setoid B}:
  forall n initial (f:B->A->B) (v:A), 
    Induction (S n) f initial v = Vcons initial (Vmap (fun x => f x v) (Induction n f initial v)).
Proof.
  intros.
  dep_destruct n; reflexivity.
Qed.

Lemma EvalPolynomial_0 `{SemiRing A}:
  forall (v:A), EvalPolynomial (Vnil) v = 0.
Proof.
  intros.
  unfold EvalPolynomial.
  reflexivity.
Qed.

Lemma EvalPolynomial_reduce `{SemiRing A}:
  forall n (a: vector A (S n)) (x:A),
    EvalPolynomial a x  =
    (Vhead a) + (x * (EvalPolynomial (Vtail a) x)).
Proof.
  intros.
  dep_destruct a.
  reflexivity.
Qed.

Lemma ScalarProd_reduce `{SemiRing A}:
  forall n (ab: (vector A (S n))*(vector A (S n))),
    ScalarProd ab = (Vhead (fst ab))* (Vhead (snd ab)) + (ScalarProd (Ptail ab)).
Proof.
  intros.
  dep_destruct ab.
  reflexivity.
Qed.

Lemma MonomialEnumerator_reduce `{SemiRing A}:
  forall n (x:A), 
    MonomialEnumerator (S n) x = Vcons 1 (Scale (x, (MonomialEnumerator n x))).
Proof.
  intros.
  dep_destruct n; reflexivity.
Qed.

Lemma ScalarProd_comm `{SR: SemiRing A} `{!Setoid A}: forall n (a b: t A n),
                                                        ScalarProd (a,b) = ScalarProd (b,a).
Proof.
  intros.
  unfold ScalarProd.
  rewrite 2!Vfold_right_to_Vfold_right_reord.
  rewrite Vmap2_comm.
  reflexivity.  
Qed.

Lemma Scale_reduce `{SR: SemiRing A} `{!Setoid A}: forall n (s: A) (v: t A (S n)),
                                                     Scale (s,v) = Vcons (s * (Vhead v)) (Scale (s, (Vtail v))).
Proof.
  intros.
  repeat unfold Scale.
  VSntac v.
  reflexivity.
Qed.

(* Scale distributivitiy *)
Lemma  Scale_dist `{SR: SemiRing A} `{!Setoid A}: forall n a (b: vector A (S n)) (k: A),
                                                    (k * a) + (Vhead (Scale (k,b))) = (k *  (a + (Vhead b))).
Proof.
  intros.
  unfold Scale.
  VSntac b.
  simpl.
  rewrite plus_mult_distr_l.
  reflexivity.
Qed.

Lemma ScalarProduct_descale `{SemiRing A} `{!Setoid A}  : forall {n} (a b: vector A n) (s:A),
                                                            [ScalarProd ((Scale (s,a)), b)] = Scale (s, [(ScalarProd (a,b))]).
Proof.
  intros.
  unfold Scale, ScalarProd.
  simpl.
  induction n.
  Case "n=0".
  VOtac.
  simpl.
  symmetry.
  rewrite_Vcons mult_0_r.
  reflexivity.
  Case "S(n)".
  VSntac a.  VSntac b.
  simpl.
  symmetry.
  rewrite_Vcons plus_mult_distr_l.

  (* Remove cons from IHn *)
  assert (HIHn:  forall a0 b0 : vector A n, equiv (Vfold_right plus (Vmap2 mult (Vmap (mult s) a0) b0) zero)
                                                  (mult s (Vfold_right plus (Vmap2 mult a0 b0) zero))).
  intros.
  rewrite <- Vcons_single_elim.
  apply IHn.
  clear IHn.

  rewrite 2!Vcons_to_Vcons_reord.
  rewrite HIHn.

  (* it should be possible to combine next 3 lines into one *)
  assert (AA: s * (Vhead a * Vhead b)  = s * Vhead a * Vhead b). 
  apply mult_assoc.
  rewrite AA.
  reflexivity.
Qed.

Lemma ScalarProduct_hd_descale `{SemiRing A} `{!Setoid A}: forall {n} (a b: vector A n) (s:A),
                                                             ScalarProd ((Scale (s,a)), b) = Vhead (Scale (s, [(ScalarProd (a,b))])).
Proof.
  intros.
  apply hd_equiv with (u:=[ScalarProd ((Scale (s,a)),b)]).
  apply ScalarProduct_descale.
Qed.

Section HCOLProper.
  Context    
    `{Ae: Equiv A}
    `{Asetoid: !@Setoid A Ae}.

  Global Instance Scale_proper `{Mult A} `{!Proper (Ae ==> Ae ==> Ae) mult} (n:nat):
    Proper ((=) ==> (=))
           (Scale (n:=n)).
  Proof.
    intros x y Ex.
    destruct x as [xa xb]. destruct y as [ya yb].
    destruct Ex.
    simpl in H0. simpl in H1.
    unfold Scale.
    induction n.
    Case "n=0".
    VOtac.
    reflexivity.
    Case "S n".
    
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
  
  Global Instance ScalarProd_proper `{!@SemiRing A Ae Aplus Amult Azero Aone} (n:nat):
    Proper ((=) ==> (=))
           (ScalarProd (n:=n)).
  Proof.
    intros x y Ex.
    destruct x as [xa xb].
    destruct y as [ya yb].
    unfold ScalarProd.
    rewrite 2!Vfold_right_to_Vfold_right_reord.
    destruct Ex.
    simpl in H0, H1.
    rewrite H0, H1.
    reflexivity.
  Qed.

  
  Global Instance InfinityNorm_proper
         `{Ar: !@Ring A Ae Aplus Amult Azero Aone Anegate}
         `{Ato: !@TotalOrder A Ae Ale}
         `{Aabs: !@Abs A Ae Ale Azero Anegate}
         `{∀ x y: A, Decision (x ≤ y)}
         {n:nat}:
    Proper ((=) ==> (=)) (InfinityNorm (n:=n)).
  Proof.
    unfold Proper.
    intros a b E1.
    unfold InfinityNorm.
    rewrite 2!Vfold_right_to_Vfold_right_reord.
    rewrite 2!Vmap_to_Vmap_reord.
    rewrite E1.
    reflexivity.
  Qed.
  
  Global Instance Atomic2_proper  (X Y Z:Type) `{!Equiv X, !Equiv Y, !Equiv Z} (f : X->Y->Z) `{pF: !Proper ((=) ==> (=) ==> (=)) f}:
    Proper ((=) ==> (=)) (Atomic2 f).
  Proof.
    unfold Proper.
    intros a b Ea.
    unfold Atomic2, prod_curry.
    destruct a. destruct b.
    destruct Ea as [H1 H2]. simpl in H1. simpl in H2.
    apply pF;  assumption.
  Qed.              

  Global Instance Pointwise2_proper  (X Y Z:Type)
         `{Ex:!Equiv X, Ey:!Equiv Y, Ez:!Equiv Z}
         `{@Setoid X Ex, @Setoid Y Ey, @Setoid Z Ez}
         {n:nat} (f : X->Y->Z) `{pF: !Proper ((=) ==> (=) ==> (=)) f}:
    Proper ((=) ==> (=)) (@PointWise2 X Y Z f n).
  Proof.
    unfold Proper.
    intros a b Ea.
    unfold PointWise2.
    destruct a. destruct b.
    destruct Ea as [E1 E2]. simpl in E1. simpl in E2.
    rewrite E1, E2.
    reflexivity.
  Qed.
  
  Global Instance Reduction_proper  (X Y:Type)
         `{Ex:!Equiv X, Ey:!Equiv Y}
         `{@Setoid X Ex, @Setoid Y Ey}
         {n:nat} (f : X->Y->Y)
         `{pF: !Proper ((=) ==> (=) ==>  (=)) f}:
    Proper ((=) ==> (=) ==> (=)) (@Reduction X Y f n).
  Proof.
    unfold Proper.
    intros a b E1 x y E2.
    unfold Reduction.
    rewrite 2!Vfold_right_to_Vfold_right_reord.
    rewrite E1, E2.
    reflexivity.
  Qed.
  
  Global Instance ChebyshevDistance_proper
         `{A1: One A}
         `{Aplus: Plus A} `{Amult: Mult A} 
         `{Ato: !@TotalOrder A Ae Ale}
         `{Aabs: !@Abs A Ae Ale Azero Anegate}
         `{∀ x y: A, Decision (x ≤ y)}
         `{Ar: !Ring A}
         (n:nat):
    Proper ((=) ==> (=))  (ChebyshevDistance (n:=n)).
  Proof.
    intros p p' pE.
    dep_destruct p.
    dep_destruct p'.
    unfold ChebyshevDistance.
    assert (E1: t=t1). apply pE.
    assert (E2: t0=t2). apply pE.
    rewrite E1, E2.
    reflexivity.
  Qed.
  
  Global Instance EvalPolynomial_proper `{SemiRing A} (n:nat):
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
    assert (XE: x = x0). apply vE.
    setoid_replace (EvalPolynomial x a) with (EvalPolynomial x0 a').
    assert (HE: h = h0). apply vE.  
    rewrite HE.
    rewrite aE.
    reflexivity.
    apply IHn.
    assumption.
  Qed.

  Global Instance MonomialEnumerator_proper `{!@SemiRing A Ae Aplus Amult Azero Aone} (n:nat):
    Proper ((=) ==> (=))  (MonomialEnumerator n).
  Proof.
    intros a a' aE.
    induction n.
    reflexivity.  
    rewrite 2!MonomialEnumerator_reduce.
    rewrite 2!Vcons_to_Vcons_reord.
    rewrite IHn.
    rewrite aE.
    reflexivity.
  Qed.

  Global Instance Induction_proper `{Setoid B} (f:B->A->B) `{pF: !Proper ((=) ==> (=) ==> (=)) f} (n:nat):
    Proper ((=) ==> (=) ==> (=))  (@Induction A B n f).
  Proof.
    intros ini ini' iniEq v v' vEq.
    induction n.
    reflexivity. 
    rewrite 2!Induction_reduce.
    Focus 2. apply Asetoid.
    Focus 2. assumption.
    Focus 2. assumption.
    Focus 2. assumption.
    rewrite 2!Vcons_to_Vcons_reord.
    rewrite 2!Vmap_to_Vmap_reord.

    assert (Proper (Ae0 ==> Ae0) (λ x : B, f x v)).
    solve_proper.

    rewrite IHn.
    rewrite iniEq.

    assert (EE:ext_equiv (λ x : B, f x v)  (λ x : B, f x v')).
    unfold ext_equiv.
    intros z z' zE.
    rewrite vEq, zE.
    reflexivity.
    
    rewrite EE.
    reflexivity.
  Qed.
  
  Global Instance Cross_proper
         {D R E S: Type}
         `{Equiv D,Equiv R,Equiv E,Equiv S}
         (f:D->R)
         (g:E->S)
         `{pF: !Proper ((=) ==> (=)) f}
         `{pG: !Proper ((=) ==> (=)) g}:
    Proper ((=) ==> (=))  (Cross (f,g)).
  Proof.
    intros fg fg' fgE.
    destruct fg, fg'.
    assert (M1:d=d0). apply fgE.
    assert (M2:e=e0). apply fgE.    
    unfold Cross.
    split; simpl.
    apply pF. assumption.
    apply pG. assumption.
  Qed.

  
End HCOLProper.

Close Scope vector_scope.
