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
Require Import CoLoR.Util.List.ListUtil.
Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

Fixpoint SparseUnion {A} {n}: (svector A n) -> (svector A n) -> @maybeError (svector A n) := 
  match n with
  | O => fun _ _ => OK (@Vnil (option A))
  | (S _) => fun a b =>
              match SparseUnion (Vtail a) (Vtail b) as t with
              | Error msg => Error msg
              | OK xs =>
                match Vhead a, Vhead b with
                |  Some _, Some _ => Error "incompatible values"
                |  None, None as x | None, Some _ as x | Some _ as x, None => OK (Vcons x xs)
                end
              end
  end.

Definition ErrSparseUnion {A} {n}
           (a: @maybeError (svector A n))
           (b: @maybeError (svector A n))
           : @maybeError (svector A n)
  := 
    match a, b with
    | Error _ as e, Error _ => e (* TODO: combine error messages *)
    | Error _ as e, OK _ => e
    | OK _, Error _ as e  => e
    | OK a', OK b' => SparseUnion a' b'
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
    
    Definition VnthInverseIndexMapped' {A:Type}
               {i o:nat}
               (x: svector A i)
               (f'_spec: inverse_map_spec i o)
               (n:nat) (np: n<o)
      : option A
      :=
        let f' := proj1_sig f'_spec in
        let f'_dr := proj2_sig f'_spec in
        match (f' n) as fn return f' n ≡ fn -> option A with        
        | None => fun _ => None
        | Some z => fun p => Vnth x (f'_dr n np z p)
        end eq_refl.
    
    Program Definition Scatter {A:Type}
            {i o: nat}
            (f: index_map i o)
            (x: svector A i) : svector A o
      :=
        Vbuild (fun n np =>
                  VnthInverseIndexMapped' x (build_inverse_map_spec f) n np).
    
    Lemma Scatter_spec `{Equiv A}
          {i o: nat}
          (f: index_map i o)
          (x: svector A i)
          (y : svector A o):
      (Scatter f x ≡ y) ->  ∀ n (ip : n < o), Vnth y ip ≡ VnthInverseIndexMapped' x (build_inverse_map_spec f) n ip.
    Proof.
      unfold Scatter, Vbuild. 
      destruct (Vbuild_spec
                  (λ (n : nat) (np : n < o),
       VnthInverseIndexMapped' x (build_inverse_map_spec f) n np)) as [Vv Vs].
      simpl.
      intros.
      subst.
      auto.
    Qed.

  End IndexedOperators.

  (* TODO: additional property, assuring that we access only initialized values? *)
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
  | SHOScatHUnion {i o} (base stride:aexp): SOperator i o
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
  | SHOISumUnion {i o} (var:varname) (r:aexp) : SOperator i o -> SOperator i o
  .
  
  Definition state := varname -> @maybeError nat.
  
  Definition empty_state: state :=
    fun x =>
      match x with 
      | (Var n) => Error ("variable " ++ n ++ " not found")
      end.
  
  Definition update (st : state) (x : varname) (n : nat) : state :=
    fun x' => if eq_varname_dec x x' then OK n else st x'.
  
  Definition has_value (st:state) (x:varname) : Prop := is_OK (st x).

  Definition eval_mayberr_binop (a: @maybeError nat) (b: @maybeError nat) (op: nat->nat->nat) :=
    match a with
    | Error msg => Error msg
    | OK an => match b with
              | Error msg => Error msg
              | OK bn => OK (op bn an)
              end
    end.
  
  Fixpoint evalAexp (st:state) (e:aexp): @maybeError nat :=
    match e  with
    | AConst x => OK x
    | AValue x => st x
    | APlus a b => eval_mayberr_binop (evalAexp st a) (evalAexp st b) plus
    | AMinus a b => eval_mayberr_binop (evalAexp st a) (evalAexp st b) minus
    | AMult a b => eval_mayberr_binop (evalAexp st a) (evalAexp st b) mult
    end.

  Lemma update_eval:
    ∀ (var : varname) (st : state) (x:nat),
      evalAexp (update st var x) (AValue var) ≡ @OK nat x.
  Proof.
    intros.
    compute.
    break_if.
    reflexivity.
    congruence.
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


    Definition cast_vector_operator
               {B C: Type}
               (i0:nat) (o0:nat)
               (i1:nat) (o1:nat)
               (f: (vector B i0) -> (@maybeError (vector C o0))):
      (vector B i1) -> (@maybeError (vector C o1)).
    Proof.
      assert (Di: {i0 = i1} + {i0 <> i1}) by apply (eq_nat_dec).
      assert (Do: {o0 = o1} + {o0 <> o1}) by apply (eq_nat_dec).
      destruct Di, Do.
      rewrite <- e. 
      rewrite <- e0.
      assumption.
      intros.
      exact (Error "incompatible output sizes").
      intros.
      exact (Error "incompatible input sizes").
      intros.
      exact (Error "incompatible input and output sizes").
    Defined.

    Lemma cast_vector_operator_OK_OK {B C: Type}
      : forall i0 i1 o0 o1 (v: vector B i1)
          (op: vector B i0 → vector C o0)
      ,
        (i0 ≡ i1 /\ o0 ≡ o1) -> is_OK ((cast_vector_operator
                                        i0 o0
                                        i1 o1
                                        (OK ∘ op)) v).
    Proof.
      intros.
      destruct H as [Hi Ho].
      rewrite <- Ho. clear o1 Ho.
      revert op.
      rewrite Hi. clear i0 Hi.
      intros.

      unfold compose.
      set (e := (λ x : vector B i1, @OK (vector C o0) (op x))).

      assert(is_OK (e v)).
      {
        unfold e. simpl. trivial.
      }
      revert H.
      generalize dependent e. clear op.
      intros.

      rename i1 into i.
      rename o0 into o.
      (* here we arrived to more generic form of the lemma, stating that is_OK property is preserved by 'cast_vector_operator *)

      unfold cast_vector_operator.
      destruct (eq_nat_dec o o), (eq_nat_dec i i); try congruence.

      compute.
      destruct e0.
      dep_destruct e1.
      auto.
    Qed.

    
    Lemma cast_vector_operator_OK_elim: forall i o (v: vector A i)
                                          (op: vector A i → svector A o)
      ,
        forall (t: svector A o),
          ((cast_vector_operator
              i o
              i o
              (OK ∘ op)) v) ≡ OK t -> op v ≡ t.
    Proof.
      intros i o v op t.
      unfold cast_vector_operator.
      destruct (eq_nat_dec i i); try congruence.
      destruct (eq_nat_dec o o); try congruence.
      compute.
      dep_destruct e.
      dep_destruct e0.
      intros.
      inversion H.
      reflexivity.
    Qed.

    Definition evalScatHUnion
               {i o: nat}
               (st:state)
               (base stride:aexp)
               (v:svector A i):
      @maybeError (svector A o) :=
      match evalAexp st base, evalAexp st stride with
      | OK nbase, OK nstride =>
        match eq_nat_dec nstride 0 with
        | left _ => Error "SHOScatH stride must not be 0"
        | right snz =>
          match lt_dec (nbase+(pred i)*nstride) o with
          | right _ => Error "SHOScatH output size is too small for given params"
          | left domain_bound =>
            OK (ScatH
                  (snz:=snz)
                  (domain_bound:=domain_bound)
                  i o nbase nstride v)
          end
        end
      |  _, _ => Error "Undefined variables in ScatHUnion arguments"
      end.

    Definition evalGathH
               {i o: nat}
               (st:state)
               (base stride:aexp)
               (v: svector A i):  @maybeError (svector A o) :=
      match evalAexp st base, evalAexp st stride with
      | OK nbase, OK nstride =>
        match eq_nat_dec nstride 0 with
        | left _ => Error "SHOGathH stride must not be 0"
        | right snz =>
          match lt_dec (nbase+(pred o)*nstride) i with
          | right _ => Error "SHOGathH input size is too small for given params"
          | left range_bound =>
            OK (GathH
                  (snz:=snz)
                  (range_bound:=range_bound)
                  i o nbase nstride v)
          end
        end
      |  _, _ => Error "Undefined variables in GathH arguments"
      end.
    
    Definition evalBinOp
               {i o: nat}
               (_:state)
               (f: A->A->A) (v: svector A i):
      @maybeError (svector A o) :=
      match try_vector_from_svector v with
      | Error msg => Error "OHScatHUnion expects dense vector!"
      | OK x =>
        (cast_vector_operator
           (o+o) o
           i o
           (OK ∘ svector_from_vector ∘ (HCOLOperators.PointWise2 f) ∘ (vector2pair o))) x
      end.
    
    Definition evalInfinityNorm
               {i: nat}
               (st:state)
               (v: svector A i):
      @maybeError (svector A 1) :=
      match try_vector_from_svector v with
      | Error _ => Error "OHScatHUnion expects dense vector!"
      | OK dv =>
        let h := HOInfinityNorm (i:=i) in
        (OK ∘ svector_from_vector ∘ (evalHCOL h)) dv
      end.

    Definition evalReduction
               {i: nat}
               (st:state)
               (f: A->A->A) `{pF: !Proper ((=) ==> (=) ==> (=)) f}
               (idv:A)
               (v: svector A i):
      @maybeError (svector A 1) :=
      match try_vector_from_svector v with
      | Error _ => Error "Reduction expects dense vector!"
      | OK dv =>
        let h := HOReduction i f idv in
        (OK ∘ svector_from_vector ∘ (evalHCOL h)) dv
      end.

    Definition evalHOperator
               {i o: nat}
               (h: HOperator i o)
               (v: svector A i):
      @maybeError (svector A o) :=
      match try_vector_from_svector v with
      | Error _ => Error "HOperator  expects dense vector!"
      | OK dv =>  (OK ∘ svector_from_vector ∘ (evalHCOL h)) dv
      end.

    Fixpoint evalSigmaHCOL
             {i o: nat}
             (st:state)
             (op: SOperator i o)
             (v:svector A i): @maybeError (svector A o)
      :=
        (match op in @SOperator i o return svector A i -> @maybeError (svector A o)
         with
         | SHOISumUnion i o var r body as su =>
           (fun v0 => 
              match (evalAexp st r)
              with
              | Error _ => Error "Undefined SHOISumUnion range"
              | OK O => Error "Invalid SHOISumUnion range"
              | OK (S p) =>
                let v' := List.map (fix en (n':nat) := evalSigmaHCOL (update st var n') body v0)
                                   (rev_natrange_list (S p)) in
                let z := OK (@Vconst (option A) None o) in 
                List.fold_left (@ErrSparseUnion A o) v' z
              end
           )
         | SHOCompose _ _ _ f g  =>
           (fun v0 =>
              match evalSigmaHCOL st g v0 with
              | Error msg => Error msg
              | OK gv => evalSigmaHCOL st f gv
              end)
         | SHOScatHUnion _ _ base stride => evalScatHUnion st base stride
         | SHOGathH _ _ base stride => evalGathH st base stride
         | SHOBinOp _ f _ => evalBinOp st f
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


Section SigmaHCOL_language_tests.

(* TODO: unit tests using CUnit:
http://coq-blog.clarus.me/simple-unit-testing-in-coq.html
 *)


  
End SigmaHCOL_language_tests.





