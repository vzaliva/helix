(* Experimental alternative Sigma-HCOL, which ignores errors *)

(* Coq defintions for Sigma-HCOL operator language *)

Require Import Spiral.
Require Import Rtheta.
Require Import HCOL.
Require Import HCOLSyntax.
Require Import IndexFunctions.
Require Import AExp.

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

(* "sparse" vector type *)
Notation svector n := (vector Rtheta n) (only parsing).

Section SparseVectors.

  Definition svector_from_vector {n} (v:vector A n): svector n :=
    Vmap Rtheta_normal v.

  Definition vector_from_svector {n} (v:svector n): vector A n :=
    Vmap RthetaVal v.
  
  Definition svector_is_dense {n} (v:svector n) : Prop :=
    Vforall Is_SZero v.
  
  Definition empty_svector n: svector n := Vconst Rtheta_szero n.
  
  Definition svector_is_empty {n} (v:svector n) := Vforall Is_SZero v.
  
End SparseVectors.

(* Scalar union *)
Definition Union 
           (a b: Rtheta): Rtheta
  :=
    match a, b with
    |  (_, true, ae), (bv, false, be) => (bv, false, andb ae be) (* s0 + b = b *)
    |  (av, false, ae), (_, true, be) => (av, false, andb ae be) (* a + s0 = a *)
    |  (_, true, ae), (_, true, be) => (zero, true, andb ae be) (* s0 + s0 = s0 *)
    |  (_, false, _), (_, false, _) => Rtheta_szero_err (* a + b = s0, ERR ! *)
    end.

(* Unary union of vector's elements (fold) *)
Definition VecUnion {n} (v:svector n): Rtheta :=
  Vfold_right Union v Rtheta_szero.

(* Binary element-wise union of two vectors *)
Definition Vec2Union {n} (a b: svector n): svector n
  := Vmap2 Union a b.

Module SigmaHCOL_Operators.

  Global Open Scope nat_scope.
  
  Section IndexedOperators.

    (* Returns an element of the vector 'x' which is result of mapping of given
natrual number by index mapping function f_spec. *)
    Definition VnthIndexMapped
               {i o:nat}
               (x: svector i)
               (f: index_map o i)
               (n:nat) (np: n<o)
    : Rtheta
      := Vnth x (« f » n np).

    Definition Gather 
               {i o: nat}
               (f: index_map o i)
               (x: svector i):
      svector o
      := Vbuild (VnthIndexMapped x f).

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
    
    Definition Scatter 
            {i o: nat}
            (f: index_map i o)
            (x: svector i) : svector o
      :=
        Vbuild (fun n np =>
                  VnthInverseIndexMapped x (build_inverse_index_map f) n np).

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

  End IndexedOperators.

  Definition GathH
             (i o base stride: nat)
             {range_bound: (base+(pred o)*stride) < i}
             {snz: stride ≢ 0} 
    :
      (svector i) -> svector o
    :=
      Gather 
        (@h_index_map o i base stride range_bound snz).

  Definition ScatH
             (i o base stride: nat)
             {domain_bound: (base+(pred i)*stride) < o}
             {snz: stride ≢ 0} 
    :
      (svector i) -> svector o
    :=
      Scatter 
        (@h_index_map i o base stride domain_bound snz).
  
End SigmaHCOL_Operators.

Import SigmaHCOL_Operators.


Section SigmaHCOL_Language.
  (* Sigma-HCOL language, introducing even higher level concepts like variables *)

  Inductive SOperator: nat -> nat -> Type :=
  (* --- HCOL basic operators --- *)
  | SHOScatH {i o} (base stride:aexp):
      forall st:state,  (evalAexp st stride ≢ 0) -> ((evalAexp st base) + pred i * (evalAexp st stride) < o) -> SOperator i o
  | SHOGathH {i o} (base stride: aexp):
      forall st:state, (evalAexp st stride ≢ 0) -> ((evalAexp st base) + pred o * (evalAexp st stride) < i) ->  SOperator i o
  (* TODO: proper migh not neccessary be part of SOperator as it only needed for rewriting *)
  | SHOBinOp o (f:A->A->A) `{pF: !Proper ((=) ==> (=) ==> (=)) f}: SOperator (o+o) o
  (* Lifted generic HCOL operator *)
  | SOHCOL {i} {o} (h:@HOperator A Ae i o): SOperator i o
  (* --- HCOL compositional operators --- *)
  | SHOCompose i {t} o: SOperator t o -> SOperator i t -> SOperator i o
  | SHOISumUnion {i o} (var:varname) (r:aexp):
      SOperator i o -> forall (st:state), (evalAexp st r ≢ 0) -> SOperator i o
  .

  Section SigmaHCOL_Eval.
    (* The following context is matching one for evalHCOL *)
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
      `{Aeqdec: !∀ (x y: A), Decision (x=y)}
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
               (v:svector i):
      @svector o :=
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
               (v: svector i):  svector o :=
      GathH
        (snz:=snz)
        (range_bound:=range_bound)
        i o (evalAexp st base) (evalAexp st stride) v.
    
    (* TODO: just use evalHOperator *)
    Definition evalBinOp
               {o: nat}
               (f: A->A->A) `{pF: !Proper ((=) ==> (=) ==> (=)) f}
               (v: svector (o+o)):
      svector o :=
      (svector_from_vector
         ∘ evalHCOL (HOPointWise2 o f (Ae:=Ae) (pF:=pF))
         ∘ vector_from_svector
      ) v.

    Definition evalHOperator
               {i o: nat}
               (h: HOperator i o (A:=A))
               (v: svector i):
      svector o :=
      (svector_from_vector
         ∘ evalHCOL h
         ∘ vector_from_svector
      ) v.

    Fixpoint evalSigmaHCOL
             {i o: nat}
             (st:state)
             (op: SOperator i o)
             (v:svector i): svector o
      :=
        (match op in @SOperator i o return svector i -> svector o
         with
         | SHOISumUnion i o var r  body st rnz as su =>
           (fun v0 => 
              match (evalAexp st r)
              with
              | O => !
              | (S p) =>
                Vfold_left Vec2Union (*TODO: Prop missing here *)
                           (empty_svector o)
                           (Vbuild 
                              (fix en (n':nat) (np:n'<S p) := evalSigmaHCOL (update st var n') body v0))
              end
           )
         | SHOCompose _ _ _ f g  => 
           (evalSigmaHCOL st f) ∘ (evalSigmaHCOL st g)
         | SHOScatH _ _ base stride st snz domain_bound => evalScatH st base stride snz domain_bound
         | SHOGathH _ _ base stride st snz range_bound => evalGathH st base stride snz range_bound
         | SHOBinOp _ f _ => evalBinOp f
         | SOHCOL _ _ h => evalHOperator h
         end) v.
    
        
    Global Instance SigmaHCOL_equiv {i o:nat}: Equiv (SOperator i o) :=
      fun f g => forall st (x:svector i), evalSigmaHCOL st f x = evalSigmaHCOL st g x.

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






