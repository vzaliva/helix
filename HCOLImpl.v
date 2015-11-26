(* Low-level functions implementing HCOL matrix and vector manupulation operators *)

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


Section HCOL_implementations.

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

  Definition Zless (a b:Rtheta): Rtheta
    := if Rtheta_ltdec a b then one else zero.

  Global Instance Zless_proper:
    Proper ((=) ==> (=) ==> (=)) (Zless).
  Proof.
    unfold Proper.
    intros a a' aE z z' zE.
    unfold Zless.
    destruct (Rtheta_ltdec a z), (Rtheta_ltdec a' z'); auto.
    rewrite aE, zE in l; contradiction.
    rewrite <- aE, <- zE in l; contradiction.
  Qed.

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
             (ab: (svector n)*(svector n)) : svector n :=
    match ab with
    | (a,b) => Vmap2 (Zless) a b
    end.

  (* --- Monomial Enumerator --- *)

  Fixpoint MonomialEnumerator
           (n:nat) (x:Rtheta) {struct n} : svector (S n) :=
    match n with 
    | O => [1]
    | S p => Vcons 1 (Vmap (mult x) (MonomialEnumerator p x))
    end.

  (* --- Polynomial Evaluation --- *)

  Fixpoint EvalPolynomial {n} 
           (a: svector n) (x:Rtheta) : Rtheta  :=
    match a with
      nil => 0
    | cons a0 p a' => a0 + (x * (EvalPolynomial a' x))
    end.

  (* === HCOL Basic Operators === *)
  (* formerly known as PointWise2 *)
  Definition BinOp (f: Rtheta->Rtheta->Rtheta) {n} (ab: (svector n)*(svector n)) : svector n :=
    match ab with
    | (a,b) =>  Vmap2 f a b
    end.

  (* --- Induction --- *)

  Fixpoint Induction (n:nat) (f:Rtheta->Rtheta->Rtheta) (initial:Rtheta) (v:Rtheta) {struct n} : svector n :=
    match n with 
    | O => []
    | S p => Vcons initial (Vmap (fun x => f x v) (Induction p f initial v))
    end.

  Fixpoint Inductor (n:nat) (f:Rtheta->Rtheta->Rtheta) (initial:Rtheta) (v:Rtheta) {struct n} : Rtheta :=
    match n with 
    | O => initial
    | S p => f (Inductor p f initial v) v
    end.

  (* --- Reduction --- *)

  (*  Reduction (fold) using single finction. In case of empty list returns 'id' value:
    Reduction f x1 .. xn b = f xn (f x_{n-1} .. (f x1 id) .. )
   *)
  Definition Reduction (f: Rtheta->Rtheta->Rtheta) {n} (id:Rtheta) (a: svector n) : Rtheta := 
    Vfold_right f a id.

  (* --- Scale --- *)
  Definition Scale
             {n} (sv:Rtheta*(svector n)) : svector n :=
    match sv with
    | (s,v) => Vmap (mult s) v
    end.

  (* --- Concat ---- *)
  Definition Concat {an bn: nat} (ab: (svector an)*(svector bn)) : svector (an+bn) :=
    match ab with
      (a,b) => Vapp a b
    end.

End HCOL_implementations.

(* === Lemmas about functions defined above === *)

Section HCOL_implementation_facts.

  Lemma Induction_cons:
    forall n initial (f:Rtheta->Rtheta->Rtheta) (v:Rtheta), 
      Induction (S n) f initial v = Vcons initial (Vmap (fun x => f x v) (Induction n f initial v)).
  Proof.
    intros; dep_destruct n; reflexivity.
  Qed.

  Lemma EvalPolynomial_0:
    forall (v:Rtheta), EvalPolynomial (Vnil) v = 0.
  Proof.
    intros; unfold EvalPolynomial; reflexivity.
  Qed.

  (* TODO: better name. Maybe suffficent to replace with EvalPolynomial_cons *)
  Lemma EvalPolynomial_reduce:
    forall n (a: svector (S n)) (x:Rtheta),
      EvalPolynomial a x  =
      (Vhead a) + (x * (EvalPolynomial (Vtail a) x)).
  Proof.
    intros; dep_destruct a; reflexivity.
  Qed.

  (* TODO: better name. Maybe suffficent to replace with ScalarProd_cons *)
  Lemma ScalarProd_reduce:
    forall n (ab: (svector (S n))*(svector (S n))),
      ScalarProd ab = (Vhead (fst ab))* (Vhead (snd ab)) + (ScalarProd (Ptail ab)).
  Proof.
    intros; dep_destruct ab; reflexivity.
  Qed.

  Lemma MonomialEnumerator_cons:
    forall n (x:Rtheta), 
      MonomialEnumerator (S n) x = Vcons 1 (Scale (x, (MonomialEnumerator n x))).
  Proof.
    intros; dep_destruct n; reflexivity.
  Qed.

  Lemma ScalarProd_comm: forall n (a b: svector n),
      ScalarProd (a,b) = ScalarProd (b,a).
  Proof.
    intros.
    unfold ScalarProd.
    rewrite 2!Vfold_right_to_Vfold_right_reord.
    rewrite Vmap2_comm.
    reflexivity.  
  Qed.

  (* Currently unused *)
  Lemma Scale_cons: forall n (s: Rtheta) (v: svector (S n)),
      Scale (s,v) = Vcons (s * (Vhead v)) (Scale (s, (Vtail v))).
  Proof.
    intros.
    unfold Scale.
    dep_destruct v.
    reflexivity.
  Qed.

  (* Scale distributivitiy *)
  (* Currently unused *)
  Lemma  Scale_dist: forall n a (b: svector (S n)) (k: Rtheta),
      (k * a) + (Vhead (Scale (k,b))) = (k *  (a + (Vhead b))).
  Proof.
    intros.
    unfold Scale.
    dep_destruct b.
    simpl.
    rewrite plus_mult_distr_l.
    reflexivity.
  Qed.

  Lemma ScalarProduct_descale: forall {n} (a b: svector n) (s:Rtheta),
      [ScalarProd ((Scale (s,a)), b)] = Scale (s, [(ScalarProd (a,b))]).
  Proof.
    intros.
    unfold Scale, ScalarProd.
    simpl.
    induction n.
    Case "n=0".
    crush.
    VOtac.
    simpl.
    symmetry.
    destruct_Rtheta s. unfold equiv, vec_equiv, Vforall2, Vforall2_aux.
    split; try trivial.
    unfold mult, Rtheta_Mult, Rtheta_pointwise, equiv, Rtheta_equiv, Rtheta_rel_first, RthetaVal.
    apply mult_0_r.
    Case "S(n)".
    VSntac a.  VSntac b.
    simpl.
    symmetry.
    rewrite_Vcons plus_mult_distr_l.

    (* Remove cons from IHn *)
    assert (HIHn:  forall a0 b0 : svector n, equiv (Vfold_right plus (Vmap2 mult (Vmap (mult s) a0) b0) zero)
                                              (mult s (Vfold_right plus (Vmap2 mult a0 b0) zero))).
    {
      intros.
      rewrite <- Vcons_single_elim.
      apply IHn.
    }
    clear IHn.

    rewrite 2!Vcons_to_Vcons_reord.
    rewrite HIHn.

    (* it should be possible to combine next 3 lines into one *)
    assert (AA: s * (Vhead a * Vhead b)  = s * Vhead a * Vhead b). 
    apply mult_assoc.
    rewrite AA.
    reflexivity.
  Qed.

  Lemma ScalarProduct_hd_descale: forall {n} (a b: svector n) (s:Rtheta),
      ScalarProd ((Scale (s,a)), b) = Vhead (Scale (s, [(ScalarProd (a,b))])).
  Proof.
    intros.
    apply hd_equiv with (u:=[ScalarProd ((Scale (s,a)),b)]).
    apply ScalarProduct_descale.
  Qed.

End HCOL_implementation_facts.

Section HCOL_implementation_proper.

  Global Instance Cross_arg_proper
         `{Equiv D,Equiv R,Equiv E,Equiv F}
         `{pF: !Proper ((=) ==> (=)) (f: D -> R)}
         `{pG: !Proper ((=) ==> (=)) (g: E -> F)}:
    Proper ((=) ==> (=))  (Cross (f,g)).
  Proof.
    intros fg fg' fgE.
    destruct fg, fg'.
    destruct fgE as [M2 M1]. simpl in *.
    split; simpl.
    apply pF; assumption.
    apply pG; assumption.
  Qed.
  
  Global Instance Scale_proper `{!Proper (Rtheta_equiv ==> Rtheta_equiv ==> Rtheta_equiv) mult} (n:nat):
    Proper ((=) ==> (=))
           (Scale (n:=n)).
  Proof.
    intros x y Ex.
    destruct x as [xa xb]. destruct y as [ya yb].
    destruct Ex as [H0 H1].
    simpl in H0, H1.
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
  
  Global Instance ScalarProd_proper (n:nat):
    Proper ((=) ==> (=))
           (ScalarProd (n:=n)).
  Proof.
    intros x y Ex.
    destruct x as [xa xb].
    destruct y as [ya yb].
    unfold ScalarProd.
    rewrite 2!Vfold_right_to_Vfold_right_reord.
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
    rewrite 2!Vfold_right_to_Vfold_right_reord.
    rewrite 2!Vmap_to_Vmap_reord.
    rewrite E1.
    reflexivity.
  Qed.
  
  Global Instance BinOp_proper
         {n:nat} (f : Rtheta->Rtheta->Rtheta) `{pF: !Proper ((=) ==> (=) ==> (=)) f}:
    Proper ((=) ==> (=)) (@BinOp f n).
  Proof.
    unfold Proper.
    intros a b Ea.
    unfold BinOp.
    destruct a. destruct b.
    destruct Ea as [E1 E2]. simpl in *.
    rewrite E1, E2.
    reflexivity.
  Qed.
  
  Global Instance Reduction_proper
         {n:nat} (f : Rtheta->Rtheta->Rtheta)
         `{pF: !Proper ((=) ==> (=) ==>  (=)) f}:
    Proper ((=) ==> (=) ==> (=)) (@Reduction f n).
  Proof.
    unfold Proper.
    intros a b E1 x y E2.
    unfold Reduction.
    rewrite 2!Vfold_right_to_Vfold_right_reord.
    rewrite E1, E2.
    reflexivity.
  Qed.
  
  Global Instance ChebyshevDistance_proper  (n:nat):
    Proper ((=) ==> (=))  (ChebyshevDistance (n:=n)).
  Proof.
    intros p p' pE.
    dep_destruct p.
    dep_destruct p'.
    unfold ChebyshevDistance.
    inversion pE. clear pE. simpl in *.
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
    rewrite 2!MonomialEnumerator_cons, 2!Vcons_to_Vcons_reord, IHn, aE.
    reflexivity.
  Qed.

  Global Instance Induction_proper
         (f:Rtheta->Rtheta->Rtheta)`{pF: !Proper ((=) ==> (=) ==> (=)) f} (n:nat):
    Proper ((=) ==> (=) ==> (=))  (@Induction n f).
  Proof.
    intros ini ini' iniEq v v' vEq.
    induction n.
    reflexivity.
    
    rewrite 2!Induction_cons, 2!Vcons_to_Vcons_reord, 2!Vmap_to_Vmap_reord.
    assert (RP: Proper (Rtheta_equiv ==> Rtheta_equiv) (λ x, f x v)) by solve_proper.
    rewrite IHn,  iniEq.

    assert (EE: ext_equiv (λ x, f x v)  (λ x, f x v')).
    {
      unfold ext_equiv.
      intros z z' zE.
      rewrite vEq, zE.
      reflexivity.
    }
    
    rewrite EE.
    reflexivity.
  Qed.

  Global Instance ZVLess_proper {n:nat}:
    Proper ((=) ==> (=))  (@ZVLess n).
  Proof.
    solve_proper.
  Qed.

End HCOL_implementation_proper.


Close Scope vector_scope.
