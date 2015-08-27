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

    Fixpoint build_inverse_f
             (d: nat)
             (f: nat -> nat) : nat -> option nat :=
      match d with
      | O => fun _ => None
      | S x' =>
        fun y => if eq_nat_dec y (f x') then Some x' else build_inverse_f x' f y
      end.

    (* continuation-style definition using map/fold *)
    Definition build_inverse_f_CPS
             (d: nat)
             (f: nat -> nat) :
      nat -> option nat
      :=
        List.fold_left
          (flip apply)
          (List.map (fun x' c y => if eq_nat_dec y (f x') then Some x' else c y)
                    (natrange_list d))
          (fun _ => None).


    (* definition using map/fold_left *)
    Definition build_inverse_f'
             (d: nat)
             (f: nat -> nat) :
      nat -> option nat
      := fun y =>
        List.fold_left
          (fun p x' => if eq_nat_dec y (f x') then Some x' else p)
          (natrange_list d)
          None.

    (* definition using map/fold_right *)
    Definition build_inverse_f''
             (d: nat)
             (f: nat -> nat) :
      nat -> option nat
      := fun y =>
           List.fold_right
          (fun x' p => if eq_nat_dec y (f x') then Some x' else p)
          None
          (rev_natrange_list d).    

    (* To check ourselves prove that these 2 implementations are equivalent *)
    Lemma inverse_f'_eq_f'': forall d f,  build_inverse_f' d f ≡ build_inverse_f'' d f.
    Proof.
      intros.
      induction d.
      auto.
      unfold build_inverse_f''.
      extensionality z.
      replace ((rev_natrange_list (S d))) with (rev (natrange_list (S d))).
      + rewrite List.fold_left_rev_right.
        crush.
      + unfold natrange_list.
        rewrite rev_involutive.
        reflexivity.
    Qed.
    
    Lemma build_inverse_Sd:
      forall d f, build_inverse_f (S d) f ≡
                                fun y => if eq_nat_dec y (f d) then Some d else build_inverse_f d f y.
    Proof.
      intros.
      auto.
    Qed.

    Lemma build_inverse_Sd'':
      forall d f, build_inverse_f'' (S d) f ≡
                              fun y => if eq_nat_dec y (f d) then Some d else build_inverse_f'' d f y.
    Proof.
      crush.
    Qed.
    
    Lemma build_inverse_Sd':
      forall d f, build_inverse_f' (S d) f ≡
                              fun y => if eq_nat_dec y (f d) then Some d else build_inverse_f' d f y.
    Proof.
      intros.
      rewrite 2!inverse_f'_eq_f''.
      apply build_inverse_Sd''.
    Qed.
    
    Lemma inverse_f_eq_f':
      forall d (f:nat->nat) x, build_inverse_f d x ≡ build_inverse_f' d x.
    Proof.
      intros.
      induction d.
      + simpl.
        reflexivity.
      +rewrite build_inverse_Sd, build_inverse_Sd'.
       rewrite IHd.
       reflexivity.
    Qed.
    
    Lemma index_map_inverse_dom_range'
             {domain range: nat}
             (f: index_map domain range)
             (f': nat -> option nat):
      f' ≡ build_inverse_f' domain ⟦ f ⟧ ->
      forall x z, x<range ->
           (((f' x) ≡ Some z) -> z < domain) \/
           is_None (f' x).
    Proof.
      rewrite inverse_f'_eq_f''.
      intros.
      destruct f. simpl in *. subst f'.
      case_eq (build_inverse_f'' domain index_f x).
      - intros.
        left.
        rewrite <- H.  clear H.
        unfold build_inverse_f''.
        induction domain.
        crush.
        simpl.
        destruct (eq_nat_dec x (index_f domain)).
        + intros. inversion H. auto.
        + crush.
      - right.
        none_some_elim.
    Qed.
    
    Lemma index_map_inverse_dom_range
             {domain range: nat}
             (f: index_map domain range)
             (f': nat -> option nat):
      f' ≡ build_inverse_f domain ⟦ f ⟧ ->
      forall x z, x<range ->
           (((f' x) ≡ Some z) -> z < domain) \/
           is_None (f' x).
    Proof.
      intros.
      destruct f.
      simpl in *.
      subst f'.
      induction domain.
      crush.
      apply IHdomain.
    Qed.

(* TODO: change to svector *)
    
    (* Returns an element of the vector 'x' which is result of mapping of given
natrual number by index mapping partial function 'f'*)
    Program Definition VnthIndexMappedOpt {A:Type}
               {i o:nat}
               (x: vector A i)
               (f: nat -> option nat)
               (n:nat) (np: n<o)
    : option A
      := match (f n) with
         | None => None
         | Some z => Some (Vnth x z _)
         end.
    
    Definition Scatter`{Equiv A}
               {i o: nat}
               (f_spec: index_map i o)
               (x: svector A i):
      svector A o : Vbuild (VnthIndexMapped x f).

    Lemma Scatter_spec `{Equiv A}
               {i o: nat}
               (f: index_map i o)
               (x: svector A i)
               (y : svector A o):
      Scatter f x ≡ y -> 
        ∀ ny (yp : ny < o),
          ((exists nx (xp: nx<i), ⟦ f ⟧ nx ≡ ny -> Vnth y yp ≡ Vnth x xp) \/ (is_None (Vnth y yp))).
    Proof.
    Qed.
    
  End IndexedOperators.

  (* TODO: additional property, assuring that we access only initialized values? *)
  Definition GathH `{Equiv A}
             (i o base stride: nat)
             {range_bound: (base+(pred o)*stride) < i}
    :
      (svector A i) -> svector A o
    :=
      Gather 
        (@h_index_map o i base stride range_bound).

  Program Definition ScatHBackwardMap_Spec
          (i o base pad: nat)
          {iodep: (base + (S pad) * i) ≡ o}: index_map_spec o i :=
    fun n dom_bound =>
      match lt_dec n base with
      | left _ => None
      | right _ => let ab := divmod (n-base) pad 0 pad in
                  if eq_nat_dec (snd ab) pad then Some (fst ab) else None
      end.
  Next Obligation.
    rename base into b.  rename pad into p.
    assert (W: ¬(n < b)%nat) by auto.
    clear Heq_anonymous wildcard'. 
    generalize (divmod_spec (n - b) p 0 p).
    destruct divmod as (q,u).
    simpl in *.
    subst.
    nia.
  Defined.
  
  Definition ScatHUnion `{Equiv A}
             {n:nat} (base:nat) (pad:nat):
    svector A n -> svector A (base+((S pad)*n))
    :=
      Gather 
        (@ScatHBackwardMap_Spec n (base + (S pad) * n) base pad
                                (eq_refl _)
        ).

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
               (base pad:aexp)
               (v:svector A i):
      @maybeError (svector A o) :=
      match evalAexp st base, evalAexp st pad with
      | OK nbase, OK npad =>
        (cast_vector_operator (B:=option A) (C:=option A)
                              i (nbase + S npad * i)
                              i o
                              (OK ∘ (ScatHUnion (n:=i) nbase npad))) v
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





