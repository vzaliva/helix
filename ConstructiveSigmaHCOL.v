(* Experimental alternative Sigma-HCOL construction, avoiding notion of Error *)

(* Coq defintions for Sigma-HCOL operator language *)

Require Import Spiral.
Require Import SVector.
Require Import HCOL.
Require Import HCOLSyntax.
Require Import IndexFunctions.

Require Import Coq.Arith.Arith.
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

(* Options compatible *)
Definition OptComp {A} (a b: option A) : Prop :=
  match a, b with
  |  Some _, Some _ => False
  |  None, None as x | None, Some _ as x | Some _ as x, None => True
  end.

Program Definition OptionUnion {A}
           (a b: option A)
           (ok: OptComp a b) : option A
  :=
  match a, b with
  |  None, None as x | None, Some _ as x | Some _ as x, None => x
  |  Some _ as x, Some _ => ! (* impossible case *)
  end.

(* Two option vectors compatible *)
Definition OptVecComp {A} {n} (a: svector A n)  (b: svector A n): Prop :=
  Vforall2 OptComp a b.

Lemma OptVecComp_tl {A} {n} {a b: svector A (S n)}:
  OptVecComp a b -> OptVecComp (Vtail a) (Vtail b).
Proof.
  intros C.
  dependent destruction a.
  dependent destruction b.
  unfold OptVecComp, Vforall2 in C.
  destruct C as [H T].
  simpl.
  assumption.
Qed.

Lemma OptVecComp_hd {A} {n} {a b: svector A (S n)}:
  OptVecComp a b -> OptComp (Vhead a) (Vhead b).
Proof.
  intros C.
  dependent destruction a.
  dependent destruction b.
  unfold OptVecComp, Vforall2 in C.
  destruct C as [H T].
  simpl.
  assumption.
Qed.

Fixpoint SparseUnion {A} {n}:
  forall (a b: svector A n), OptVecComp a b -> svector A n
  :=
    match n with
    | O => fun _ _  _=> @Vnil (option A)
    | (S _) => fun a' b' ok=> 
                Vcons
                  (OptionUnion (Vhead a') (Vhead b') (OptVecComp_hd ok))
                  (SparseUnion (Vtail a') (Vtail b')  (OptVecComp_tl ok))
    end.

Module SigmaHCOL_Operators.

  Global Open Scope nat_scope.
  
  Section IndexedOperators.

    (* Returns an element of the vector 'x' which is result of mapping of given
natrual number by index mapping function f_spec. *)
    Definition VnthIndexMapped {A:Type}
               {i o:nat}
               (x: vector A i)
               (f: index_map o i)
               (n:nat) (np: n<o)
    : A
      := Vnth x (« f » n np).

    Definition Gather `{Equiv A}
               {i o: nat}
               (f: index_map o i)
               (x: vector A i):
      vector A o
      := Vbuild (VnthIndexMapped x f).

    (* Specification of gather as mapping from ouptu to input. NOTE:
    we are using definitional equality here, as Scatter does not
    perform any operations on elements of type A *)
    Lemma Gather_spec `{Equiv A}
          {i o: nat}
          (f: index_map o i)
          (x: vector A i)
          (y: vector A o):
      (Gather f x ≡ y) ->  ∀ n (ip : n < o), Vnth y ip ≡ VnthIndexMapped x f n ip.
    Proof.
      unfold Gather, Vbuild. 
      destruct (Vbuild_spec (VnthIndexMapped x f)) as [Vv Vs].
      simpl.
      intros.
      subst.
      auto.
    Qed.
    
    Lemma Gather_is_endomorphism `{Ae: Equiv A}:
      ∀ (i o : nat)
        (x : vector A i),
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

    Lemma Gather_preserves_P `{Ae: Equiv A}:
      ∀ (i o : nat) (x : vector A i) (P: A->Prop),
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

    Lemma Gather_preserves_density `{Ae: Equiv A}:
      ∀ (i o : nat) (x : svector A i)
        (f: index_map o i),
        svector_is_dense x ->
        svector_is_dense (Gather f x).
    Proof.
      intros.
      unfold svector_is_dense in *.
      apply Gather_preserves_P.
      assumption.
    Qed.
    
    Definition VnthInverseIndexMapped {A:Type}
               {i o:nat}
               (x: svector A i)
               (f': partial_index_map o i)
               (n:nat) (np: n<o)
      : option A
      :=
        let f := partial_index_f _ _ f' in
        let f_spec := partial_index_f_spec _ _  f' in
        match (f n) as fn return f n ≡ fn -> option A with        
        | None => fun _ => None
        | Some z => fun p => Vnth x (f_spec n np z p)
        end eq_refl.
    
    Program Definition Scatter {A:Type}
            {i o: nat}
            (f: index_map i o)
            (x: svector A i) : svector A o
      :=
        Vbuild (fun n np =>
                  VnthInverseIndexMapped x (build_inverse_index_map f) n np).

    (* Specification of scatter as mapping from input to output. NOTE:
    we are using definitional equality here, as Scatter does not
    perform any operations on elements of type A *)
    Lemma Scatter_spec `{Equiv A}
          {i o: nat}
          (f: index_map i o)
          (x: svector A i)
          (y : svector A o):
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
    Lemma Scatter_rev_spec `{Equiv A}:
    forall 
          {i o: nat}
          (f: index_map i o)
          (x: svector A i)
          (y : svector A o),
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

  End IndexedOperators.

  Definition GathH `{Equiv A}
             (i o base stride: nat)
             {range_bound: (base+(pred o)*stride) < i}
             {snz: stride ≢ 0} 
    :
      (svector A i) -> svector A o
    :=
      Gather 
        (@h_index_map o i base stride range_bound snz).

  Definition ScatH `{Equiv A}
             (i o base stride: nat)
             {domain_bound: (base+(pred i)*stride) < o}
             {snz: stride ≢ 0} 
    :
      (svector A i) -> svector A o
    :=
      Scatter 
        (@h_index_map i o base stride domain_bound snz).
  
End SigmaHCOL_Operators.

Import SigmaHCOL_Operators.

Section SigmaHCOL_Language.
  (* Sigma-HCOL language, introducing even higher level concepts like variables *)

  Context {A:Type} {Ae: Equiv A}.
  
  Inductive varname : Type :=
    Var : string → varname.
  
  Theorem eq_varname_dec: forall id1 id2 : varname, {id1 ≡ id2} + {id1 ≢ id2}.
  Proof.
    intros id1 id2.
    destruct id1 as [n1]. destruct id2 as [n2].
    destruct (string_dec n1 n2) as [Heq | Hneq].
    left. rewrite Heq. reflexivity.
    right. intros contra. inversion contra. apply Hneq.
    assumption.
  Qed.
  
  Inductive aexp : Set :=
  | AConst : nat → aexp
  | AValue : varname → aexp
  | APlus : aexp → aexp → aexp
  | AMinus : aexp → aexp → aexp
  | AMult : aexp → aexp → aexp.
  
  Inductive SOperator: nat -> nat -> Type :=
  (* --- HCOL basic operators --- *)
  | SHOScatH {i o} (base stride:aexp): SOperator i o
  | SHOGathH {i o} (base stride: aexp): SOperator i o
  (* TODO: proper migh not neccessary be part of SOperator as it only needed for rewriting *)
  | SHOBinOp o (f:A->A->A) `{pF: !Proper ((=) ==> (=) ==> (=)) f}: SOperator (o+o) o
  (* Lifted generic HCOL operator *)
  | SOHCOL {i} {o} (h:HOperator i o): SOperator i o
  (* --- Copies of HCOL operators which can use variabeles --- *)
  | SHOInfinityNorm {i}: SOperator i 1
  | SOReduction i (f: A->A->A) `{pF: !Proper ((=) ==> (=) ==> (=)) f} (idv:A): SOperator i 1
  (* TODO:
  | HOPointWise2 o (f:A->A->A) `{pF: !Proper ((=) ==> (=) ==> (=)) f}: HOperator (o+o) o
  | HOInduction n (f:A->A->A) `{pF: !Proper ((=) ==> (=) ==> (=)) f} (initial:A): HOperator 1 n
  | HOCross i1 o1 i2 o2:  HOperator i1 o1 -> HOperator i2 o2 -> HOperator (i1+i2) (o1+o2)
  | HOTLess i1 i2 o: HOperator i1 o -> HOperator i2 o -> HOperator (i1+i2) o
  | HOStack i o1 o2: HOperator i o1 -> HOperator i o2 -> HOperator i (o1+o2)
   *)
  (* --- HCOL compositional operators --- *)
  | SHOCompose i {t} o: SOperator t o -> SOperator i t -> SOperator i o
  (* NOTE: dimensionality of the body must match that of enclosing ISUMUnion. *)
  | SHOISumUnion {i o} (var:varname) (r:aexp): SOperator i o -> SOperator i o
  .
  
  Definition state := varname -> nat.
  
  Definition empty_state: state :=
    fun x => 0.
  
  Definition update (st : state) (x : varname) (n : nat) : state :=
    fun x' => if eq_varname_dec x x' then n else st x'.
  
  Fixpoint evalAexp (st:state) (e:aexp): nat :=
    match e  with
    | AConst x => x
    | AValue x => st x
    | APlus a b => Peano.plus (evalAexp st a) (evalAexp st b) 
    | AMinus a b => Peano.minus (evalAexp st a) (evalAexp st b) 
    | AMult a b => Peano.mult (evalAexp st a) (evalAexp st b) 
    end.

  Lemma update_apply:
    ∀ (var : varname) (st : state) (x:nat),
      (update st var x var) ≡ x.
  Proof.
    intros var st x.
    compute.
    break_if.
    reflexivity.
    congruence.
  Qed.

  Lemma update_eval:
    ∀ (var : varname) (st : state) (x:nat),
      evalAexp (update st var x) (AValue var) ≡ x.
  Proof.
    intros.
    simpl.
    apply update_apply.
  Qed.

  Fixpoint varFreeIn (v:varname) (e: aexp) : Prop
    :=
      match e with
      | AConst _ => True
      | AValue x => x<>v
      | APlus a b => varFreeIn v a /\ varFreeIn v b
      | AMinus a b => varFreeIn v a /\ varFreeIn v b
      | AMult a b => varFreeIn v a /\ varFreeIn v b
      end.
  
  Lemma eval_update_free:
    ∀ (v: varname) (exp:aexp) (st : state) (x:nat),
      varFreeIn v exp ->
      evalAexp (update st v x) exp ≡ evalAexp st exp.
  Proof.
    Local Ltac uniop_case F :=
      (unfold varFreeIn in F;
       unfold update; simpl;
       destruct eq_varname_dec; congruence).
    
    Local Ltac binop_case F H1 H2:=
      (simpl in F; decompose [and] F; clear F;
       unfold evalAexp; fold evalAexp;
       rewrite H1, H2; 
       [reflexivity | assumption| assumption]).
    
    intros v exp st x F.
    induction exp;
      solve [ auto | uniop_case F | binop_case F IHexp1 IHexp2].
  Qed.
  
  Section SigmaHCOL_Eval.
    Context    
      `{Az: Zero A} `{A1: One A}
      `{Aplus: Plus A} `{Amult: Mult A} 
      `{Aneg: Negate A}
      `{Ale: Le A}
      `{Alt: Lt A}
      `{Ato: !@TotalOrder A Ae Ale}
      `{Aabs: !@Abs A Ae Ale Az Aneg}
      `{Asetoid: !@Setoid A Ae}
      `{Aledec: !∀ x y: A, Decision (x ≤ y)}
      `{Aeqdec: !∀ x y, Decision (x = y)}
      `{Altdec: !∀ x y: A, Decision (lt x y)}
      `{Ar: !Ring A}
      `{ASRO: !@SemiRingOrder A Ae Aplus Amult Az A1 Ale}
      `{ASSO: !@StrictSetoidOrder A Ae Alt}.

    Definition evalScatH
               {i o: nat}
               (st:state)
               (base stride:aexp)
               (snz: evalAexp st stride ≢ 0)
               (domain_bound: (evalAexp st base) + pred i * (evalAexp st stride) < o)
               (v:svector A i):
      @svector A o :=
      ScatH
        (snz:=snz)
        (domain_bound:=domain_bound)
        i o (evalAexp st base) (evalAexp st stride) v.

    Definition evalGathH
               {i o: nat}
               (st:state)
               (base stride:aexp)
               (snz: evalAexp st stride ≢ 0)
               (range_bound: (evalAexp st base) + pred o * (evalAexp st stride) < i)
               (v: svector A i):  svector A o :=
      GathH
        (snz:=snz)
        (range_bound:=range_bound)
        i o (evalAexp st base) (evalAexp st stride) v.
    
    (* TODO: move *)
    Fixpoint vector_from_svector {A} `{Zero A}  {n} (v:svector A n): vector A n :=
      Vmap (fun x => match x with
                  | None => zero
                  | Some v => v
                  end) v.

    (* TODO: just use evalHOperator *)
    Definition evalBinOp
               {o: nat}
               (f: A->A->A) `{pF: !Proper ((=) ==> (=) ==> (=)) f}
               (v: svector A (o+o)):
      svector A o :=
      (svector_from_vector
         ∘ evalHCOL (HOPointWise2 o f (Ae:=Ae) (pF:=pF))
         ∘ vector_from_svector
      ) v.

    (* TODO: just use evalHOperator *)
    Definition evalInfinityNorm
               {i: nat}
               (st:state)
               (v: svector A i):
      svector A 1 :=
      (svector_from_vector
         ∘ evalHCOL (HOInfinityNorm)
         ∘ vector_from_svector
      ) v.

    (* TODO: just use evalHOperator *)
    Definition evalReduction
               {i: nat}
               (st:state)
               (f: A->A->A) `{pF: !Proper ((=) ==> (=) ==> (=)) f}
               (idv:A)
               (v: svector A i):
      svector A 1 :=
      (svector_from_vector
         ∘ evalHCOL (HOReduction i f idv)
         ∘ vector_from_svector
      ) v.

    Definition evalHOperator
               {i o: nat}
               (h: HOperator i o)
               (v: svector A i):
      svector A o :=
      (svector_from_vector
         ∘ evalHCOL h
         ∘ vector_from_svector
      ) v.


    (*TODO: need {rnz: evalAexp st r ≢ 0} *)
    Fixpoint evalSigmaHCOL
             {i o: nat}
             (st:state)
             (op: SOperator i o)
             (v:svector A i): svector A o
      :=
        (match op in @SOperator i o return svector A i -> svector A o
         with
         | SHOISumUnion i o var r body as su =>
           (fun v0 => 
              match (evalAexp st r)
              with
              | O => Error "Invalid SHOISumUnion range"
              | (S p) =>
                Vfold_left (@ErrSparseUnion A o)
                           (OK (empty_svector o))
                           (Vbuild 
                              (fix en (n':nat) (np:n'<S p) := evalSigmaHCOL (update st var n') body v0))
              end
           )
         | SHOCompose _ _ _ f g  =>
           (fun v0 =>
              match evalSigmaHCOL st g v0 with
              | Error msg => Error msg
              | OK gv => evalSigmaHCOL st f gv
              end)
         | SHOScatH _ _ base stride => evalScatH st base stride
         | SHOGathH _ _ base stride => evalGathH st base stride
         | SHOBinOp _ f _ => evalBinOp f
         | SOHCOL _ _ h => evalHOperator h
         | SHOInfinityNorm _ => evalInfinityNorm st
         | SOReduction _ f pf idv => evalReduction st f idv
         end) v.
    
        
    Global Instance SigmaHCOL_equiv {i o:nat}: Equiv (SOperator i o) :=
      fun f g => forall st (x:svector A i), evalSigmaHCOL st f x = evalSigmaHCOL st g x.

    Lemma SigmaHCOL_extensionality {i o} (f g : SOperator i o) :
      (forall v st, evalSigmaHCOL st f v = evalSigmaHCOL st g v) -> f = g.
    Proof.
      intros.
      unfold equiv, SigmaHCOL_equiv.
      auto.
    Qed.

    Global Instance SigmaHCOL_Equivalence {i o:nat}
           `{!Equivalence (@equiv A _)}
      : Equivalence (@SigmaHCOL_equiv i o).
    Proof.
      unfold SigmaHCOL_equiv.
      constructor.
      unfold Reflexive. intros. apply SigmaHCOL_extensionality. intros. reflexivity.
      unfold Symmetric. intros. apply SigmaHCOL_extensionality. intros. symmetry. auto.
      unfold Transitive. intros. apply SigmaHCOL_extensionality. intros. rewrite H. auto.
    Qed.
    
    Global Instance SigmaHCOL_Setoid {i o}: Setoid (SOperator i o).
    Proof.
      unfold Setoid.
      apply SigmaHCOL_Equivalence.
    Qed.
    
  End SigmaHCOL_Eval.
End SigmaHCOL_Language.






