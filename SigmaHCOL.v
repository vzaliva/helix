(* Coq defintions for Sigma-HCOL operator language *)

Require Import Spiral.
Require Import SVector.
Require Import HCOL.
Require Import HCOLSyntax.

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.BoolEq.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import Compare_dec.
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

Module SigmaHCOL_Operators.

  Section Coq84Workaround.
    (* 
This section is workaround for Coq 8.4 bug in Program construct. under Coq 8.5 
the following definition suffice:

Program Fixpoint ScatHUnion_0 {A} {n:nat} (pad:nat): t A n -> t (option A) ((S pad)*n) :=
  match n return (t A n) -> (t (option A) ((S pad)*n)) with
  | 0 => fun _ => @nil (option A)
  | S p => fun a => cons _ (Some (hd a)) _ (append (const None pad) (ScatHUnion_0 pad (tl a)))
  end.
Next Obligation.
  ring.
Defined.
     *)
    
    Local Open Scope nat_scope.
    
    Fixpoint ScatHUnion_0 (A:Type) (n:nat) (pad:nat) {struct n}:
      vector A n -> svector A ((S pad)*n).
        refine(
            match n as m return m=n -> _ with
            | O =>  fun _ _ => (fun _ => _) Vnil
            | S p => fun H1 a =>
                      let aa := (fun _ => _) a in
                      let hh := Some (Vhead aa) in
                      let tt := ScatHUnion_0 A p pad (Vtail aa) in
                      let ttt := Vector.append (Vector.const None pad) tt in
                      (fun _ => _) (Vcons hh ttt)
            end
              (eq_refl _)
          );
      try match goal with
          | [ H: ?vector ?t1 ?n1 |- ?vector ?t2 ?n2] => replace n2 with n1 by lia
          end;
      eauto.        
    Defined.
    
    Local Close Scope nat_scope.
  End Coq84Workaround.
  
  Definition ScatHUnion {A} {n:nat} (base:nat) (pad:nat) (v:vector A n): svector A (base+((S pad)*n)) :=
    Vector.append (Vconst None base) (ScatHUnion_0 A n pad v).

  Local Open Scope nat_scope.

  Section IndexedOperators.
    Require Import Coq.Numbers.Natural.Peano.NPeano.

    (* Vector index mapping functon which maps between two sets of natrual
     numers. Mapping is partial and it returns None if there is no correspondance
     between a number in source set and target set. *)
    Definition index_map_spec (range domain : nat) :=
      ∀ n : nat, n < domain → {v : option nat | ∀ n' : nat, v ≡ Some n' → n' < range}.

    (* Returns an element of the vector 'x' which is result of mapping of given
natrual number by index mapping function f_spec. *)
    Definition VnthIndexMapped {A:Type}
               {i o:nat}
               (x: svector A i)
               (f_spec: index_map_spec i o)
               (n:nat) (np: n<o)
      : option A
      := let fv:=f_spec n np in
         let fn := proj1_sig fv in
         let fp := proj2_sig fv in
         match fn as fn' return fn = fn' -> option A with           
         | None => fun _ => None
         | Some fn => fun ep => Vnth x (fp fn ep)
         end (eq_refl fn).
    
    Definition vector_index_backward_operator_spec `{Equiv A}
               {i o: nat}
               (f_spec: index_map_spec i o)
               (x: svector A i):
      {y : svector A o |  ∀ (n : nat) (ip : n < o), Vnth y ip ≡ VnthIndexMapped x f_spec n ip }
      := Vbuild_spec (VnthIndexMapped x f_spec).
    
    Definition vector_index_backward_operator `{Equiv A}
               {i o: nat}
               (f_spec: index_map_spec i o)
               (x: svector A i):
      svector A o
      := proj1_sig (vector_index_backward_operator_spec f_spec x).

    Lemma vector_index_backward_operator_is_partial_map `{Ae: Equiv A}:
      ∀ (i o : nat)
        (x : svector A i),
      ∀ (f_spec: index_map_spec i o),
        Vforall (fun z => is_None z \/ Vin_aux x z)
                (vector_index_backward_operator f_spec x).
    Proof.
      intros.
      unfold index_map_spec in f_spec.
      unfold vector_index_backward_operator, proj1_sig,
      vector_index_backward_operator_spec.
      replace (let (a, _) :=
                   Vbuild_spec (VnthIndexMapped x f_spec) in
               a) with
      (Vbuild (VnthIndexMapped x f_spec)) by reflexivity.
      apply Vforall_eq. intros x0 VB.
      apply Vbuild_in in VB.
      destruct VB as [x1 VB1]. destruct VB1.
      subst x0.
      case_eq (VnthIndexMapped x f_spec x1 x2).
      + right.
        unfold VnthIndexMapped, proj1_sig in H.
        destruct (f_spec x1 x2) in H.
        destruct x0.
        * rewrite <- H.
          unfold Vin_aux.
          apply Vnth_in.
        * congruence.
      + left.
        none_some_elim.
    Qed.

    Lemma vector_index_backward_operator_preserves_P `{Ae: Equiv A}:
      ∀ (i o : nat) (x : svector A i) (P: option A->Prop),
        P None ->
        Vforall P x
        → ∀ f_spec : index_map_spec i o,
            Vforall P (vector_index_backward_operator f_spec x).
    Proof.
      intros.
      unfold index_map_spec in f_spec.
      assert(Vforall (fun z => is_None z \/ Vin_aux x z)
                     (vector_index_backward_operator f_spec x))
        by apply vector_index_backward_operator_is_partial_map.
      generalize dependent (vector_index_backward_operator f_spec x).
      intros t.
      rewrite 2!Vforall_eq.
      crush.
      assert (is_None x0 ∨ Vin_aux x x0) by (apply H1; assumption).
      inversion H3.
      + destruct x0; none_some_elim.
        assumption.
      + rewrite Vforall_eq in H0.
        auto.
    Qed.

    Definition index_map_is_surjective
               (i o : nat)
               (f_spec: index_map_spec i o) :=
      forall (j:nat) (jp:j<o), is_Some(proj1_sig (f_spec j jp)).
    
    Lemma vector_index_backward_operator_is_dense `{Ae: Equiv A}:
      ∀ (i o : nat) (x : svector A i)
        (f_spec: index_map_spec i o),
        svector_is_dense x ->
        index_map_is_surjective i o f_spec -> 
        svector_is_dense (vector_index_backward_operator f_spec x).
    Proof.
      intros i o x f_spec xdense fsurj.
      unfold index_map_spec in f_spec.
      unfold index_map_is_surjective in fsurj.
      unfold svector_is_dense in *.
      unfold vector_index_backward_operator, proj1_sig,
      vector_index_backward_operator_spec.
      
      replace (let (a, _) :=
                   Vbuild_spec (VnthIndexMapped x f_spec) in
               a) with
      (Vbuild (VnthIndexMapped x f_spec)) by reflexivity.
      apply Vforall_eq. intros.
      apply Vbuild_in in H.
      destruct H. destruct H. 
      subst x0.
      case_eq (VnthIndexMapped x f_spec x1 x2). 
      - intros. 
        none_some_elim.
      - intros.
        assert(FS: is_Some (` (f_spec x1 x2))) by apply fsurj.
        unfold VnthIndexMapped, proj1_sig in H.
        destruct (f_spec x1 x2) in H, FS; none_some_elim.
        destruct x0.
        +
          simpl in *.
          generalize dependent (l n eq_refl). 
          clear FS f_spec fsurj l.
          intros.
          (* here we have a contradiction between 'xdense' and 'H' *)
          assert (HS: is_Some (Vnth x l)) by (apply Vforall_nth; assumption).
          destruct (Vnth x l); simpl in *;  congruence.
        +
          simpl in FS. contradiction FS.
    Qed.

  End IndexedOperators.

  Program Definition GathBackwardMap_Spec
          (i o base stride: nat)
          {snz: 0 ≢ stride} 
          {range_bound: (base+(pred o)*stride) < i}: index_map_spec i o :=
    fun n dom_bound => Some (base + n*stride).
  Next Obligation.
    dep_destruct o. crush.
    unfold pred in range_bound.
    assert (n<=x) by lia.
    assert(n * stride <= x*stride).
    apply mult_le_compat_r; assumption.
    apply plus_le_subst_r with (b:=x*stride) (b':=n*stride) in range_bound;
        assumption.
  Defined.
    
  Definition GathH `{Equiv A}
             (i o base stride: nat)
             {snz: 0 ≢ stride} 
             {range_bound: (base+(pred o)*stride) < i}
    :
      (vector (option A) i) -> vector (option A) o :=
    vector_index_backward_operator 
        (@GathBackwardMap_Spec i o base stride snz range_bound).


  Local Open Scope nat_scope.
  
  Program Definition ScatHBackwardMap_Spec
          (i o base pad: nat)
          {iodep: (base + (S pad) * i) ≡ o}: index_map_spec i o :=
    fun n dom_bound =>
      match lt_dec n base with
      | left _ => None
      | right _ => match divmod (n-base) (S pad) 0 (S pad) with
                  | (j, 0) => Some j
                  | _ => None
                  end
      end.
  Next Obligation.
    clear Heq_anonymous.

    assert (W: ¬(n < base)%nat) by auto.
    clear wildcard'. 
    rename Heq_anonymous0 into P.
    
    generalize (divmod_spec (n - base) (S pad) 0 (S pad)).
    destruct divmod as (q,u).
    tuple_inversion.
    simpl. intros.
    assert(H1: n - base + pad * 0 + (pad - pad) ≡ q + (q + pad * q) + S pad
        ∧ 0 <= S pad) by auto. clear H.
    assert(H2: n - base + pad * 0 + (pad - pad) ≡ q + (q + pad * q) + S pad)
      by firstorder. clear H1.

    rewrite Mult.mult_0_r, minus_diag, Plus.plus_0_r, Plus.plus_0_r in H2.
    rename base into b.  rename pad into p.

    apply not_lt_le_flip in W.
    destruct W.
    lia.
    
  Defined.
  
  Local Close Scope nat_scope.
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
  | SHOScatHUnion {i o} (base pad:aexp): SOperator i o
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
      `{Altdec: !∀ x y: A, Decision (x < y)}
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

    Lemma cast_vector_operator_OK_OK: forall i0 i1 o0 o1 (v: vector A i1)
                                        (op: vector A i0 → svector A o0)
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
      set (e := (λ x : vector A i1, @OK (vector (option A) o0) (op x))).

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
               (base pad:aexp)
               (v:svector A i):
      @maybeError (svector A o) :=
      match evalAexp st base, evalAexp st pad with
      | OK nbase, OK npad =>
        match try_vector_from_svector v with
        | Error msg => Error "OHScatHUnion expects dense vector!"
        | OK x => (cast_vector_operator
                    i (nbase + S npad * i)
                    i o
                    (OK ∘ (ScatHUnion (A:=A) (n:=i) nbase npad))) x
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
        match eq_nat_dec 0 nstride with
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
    
    Definition evalSigmaHCOL:
      forall {i o:nat}, state-> SOperator i o -> svector A i -> @maybeError (svector A o) :=
      fix evalSigmaHCOL {i o: nat} st (op: SOperator i o) v :=           
        (match op in @SOperator i o return svector A i -> @maybeError (svector A o)
         with
         | SHOCompose _ _ _ f g  =>
           (fun v0 =>
              match evalSigmaHCOL st g v0 with
              | Error msg => Error msg
              | OK gv => evalSigmaHCOL st f gv
              end)
         | SHOISumUnion _ _ var r body =>
           (fun v0 =>
              match evalAexp st r with
              | OK O => Error "Invalid SHOISumUnion range"
              | OK (S p) =>
                (fix evalISUM (st:state) (nr:nat) {struct nr}:
                   @maybeError (svector A _) :=
                   match nr with
                   | O => evalSigmaHCOL (update st var nr) body v0
                   | S p =>
                     match evalSigmaHCOL (update st var nr) body v0 with
                     | OK x =>
                       match evalISUM st p with
                       | OK xs => SparseUnion x xs
                       |  Error _ as e => e
                       end
                     |  Error _ as e => e
                     end
                   end) st p
              | _  => Error "Undefined variables in SHOISumUnion arguments"
              end) 
         | SHOScatHUnion _ _ base pad => evalScatHUnion st base pad
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





