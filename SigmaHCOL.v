(* Coq defintions for Sigma-HCOL operator language *)

Require Import Spiral.
Require Import SVector.
Require Import HCOL.
Require Import HCOLSyntax.

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.BoolEq.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.

Require Import CpdtTactics.
Require Import CaseNaming.
Require Import Psatz.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.theory.rings.
Require Import MathClasses.implementations.peano_naturals.

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


  Section IndexedOperators.
    Require Import Coq.Numbers.Natural.Peano.NPeano.

    Local Open Scope nat_scope.
    
    (* Mapping from input indices to output ones.
This might be applicable in SPIRAL, since operators usually
never write to same element of the output vector more than once,
and some element of input vector can map to more than one element
of output vectors. 

In other words, functions on indices are:
1. injective (every element of the codomain is mapped to by at most one element of the domain)
1. non-surjective (NOT: if every element of the codomain is mapped to by at least one element of the domain)
     *)
    Definition GathForwardMap
               (base stride: nat)
               {snz: 0 ≢ stride} (i:nat): (option nat)
      := match lt_dec i base with
         | left _ => None
         | right _ => match divmod (i-base) stride 0 stride with
                     | (o, O) => Some o
                     | _ => None
                     end
         end.

    Definition GathBackwardMap
               (base stride o: nat)
               {snz: 0 ≢ stride} (n:nat): (option nat)
      := match lt_dec n o with
         | left _ => Some (base + n*stride)
         | right _ =>  None
    end.
    
    Definition opt_nat_max (x:option nat) (y: option nat): option nat :=
      match x, y with
      | None, None => None
      | None, Some y' => Some y'
      | Some x', None => Some x'
      | Some x', Some y' => Some (max x'  y')
      end.

    Definition opt_nat_lt (x:option nat) (y: nat): Prop :=
      match x with
      | None => True
      | Some x' =>  x' < y
      end.

    Definition IndexMapUpperBound
               (f: nat -> (option nat))
               (i: nat) :=
      Vfold_left opt_nat_max None (Vmap f (natrange i)).

    
     (* Build operator on vectors by mapping outputs to inputs
via provided (output_index -> input_index) function *)
        Fixpoint vector_index_backward_operator
             {A}
             {i o: nat}
             (f: nat -> (option nat))
             {ibound: forall (n n':nat), f n ≡ Some n' -> n' < i}
             (x: svector A i):  (svector A o) :=
      (match o return nat -> (svector A o) with 
       | 0 => fun _ => Vnil
       | S p => fun no =>
                 snoc (vector_index_backward_operator (o:=p) (ibound:=ibound) f x)
                      match f p with
                      | None => None
                      | Some a' =>
                        match lt_dec a' i with
                        | left ip => Vnth x ip
                        | right _ => None (* this should never happen *)
                        end
                      end
       end) o.

        (*
    Lemma backward_operator_nth
            `{Ae: Equiv A}
            {i o: nat}
            (f: nat -> (option nat))
             {ibound: forall (n n':nat), f n ≡ Some n' -> n' < i}
            (x: svector A i)  (y: svector A o):
      (y = (vector_index_backward_operator (ibound:=ibound)  f x)) ->
      forall (n n':nat), n<o -> f n ≡ Some n' -> Vnth y ≡ Vnth x.
    Proof.
    Qed.
         *)

        Lemma GathBound
              (i o base stride: nat)
              {snz: 0 ≢ stride}
              {oc: (base+o*stride) < i}
              {onz: 0 ≢ o}:
          forall (n n':nat), GathBackwardMap (snz:=snz) base stride o n ≡ Some n' -> n' < i.
        Proof.
          intros n n'.
          unfold GathBackwardMap.
          case (lt_dec n o).

          crush.
          assert (0 < stride). crush.
          assert ((n * stride) < (o * stride)).
          apply mult_lt_compat_r; assumption.
          omega.

          congruence.
        Qed.

        (* Indexed version of GatH operator *)
        Definition GathH
               {A}
               (i o base stride: nat)
               {snz: 0 ≢ stride}
               {onz: 0 ≢ o}
               {oc: (base+o*stride) < i}:
          (vector (option A) i) -> vector (option A) o :=
          vector_index_backward_operator
            (ibound := GathBound (oc:=oc) (onz:=onz) i o base stride)
            (GathBackwardMap
               (snz:=snz)
               base stride o).
    
    Local Close Scope nat_scope.
  End IndexedOperators.

  
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
        match eq_nat_dec 0 o with
        | left _ => Error "SHOGathH n must not be 0"
        | right onz =>
          match eq_nat_dec 0 nstride with
          | left _ => Error "SHOGathH stride must not be 0"
          | right snz =>
            match lt_dec (nbase+o*nstride) i with
            | right _ => Error "SHOGathH input size is too small for given params"
            | left oc =>
              OK (GathH
                    (snz:=snz)
                    (onz:=onz)
                    (oc:=oc)
                    i o nbase nstride v)
            end
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

(* Lemma test0: @ScatHUnion_0 nat 0 0 Vnil = Vnil.
  Proof.  compute. Qed. *)
  
End SigmaHCOL_language_tests.





