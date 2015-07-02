(* Coq defintions for Sigma-HCOL operator language *)

Require Import Spiral.
Require Import SVector.
Require Import HCOL.
Require Import HCOLSyntax.

Require Import Coq.Arith.EqNat Coq.Arith.Le Coq.Arith.Compare_dec.
Require Import Coq.Arith.Plus Coq.Arith.Minus.
Require Import Coq.Bool.BoolEq.
Require Import Coq.Strings.String.

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

  (* zero - based, (stride-1) parameter *)
  Program Fixpoint GathH'_old {A} {t:nat} (n s:nat) : vector A ((n*(S s)+t)) -> vector A n :=
    let stride := S s in (
      match n return vector A ((n*stride)+t) -> vector A n with
      | O => fun _ => Vnil
      | S p => fun a => Vcons (Vhead a) (GathH'_old p s (t0:=t) (drop_plus stride a))
      end).
  Next Obligation.
    omega.
  Defined.

  (* no base. actual stride value  *)
  Program Fixpoint GathH' {A} {t:nat} (n stride:nat)  {snz: 0 ≢ stride}: vector A ((n*stride+t)) -> vector A n :=
      match n return vector A ((n*stride)+t) -> vector A n with
      | O => fun _ => Vnil
      | S p => fun a => Vcons (Vhead (n:=(pred ((((S p)*stride)+t)))) a) (GathH' p stride (t0:=t) (snz:=snz) (drop_plus stride a))
      end.
  Next Obligation.
    apply nez2gt in snz.
    lia.
  Defined.
  Next Obligation.
    omega.
  Defined.
  
  Program Definition GathH_old {A: Type} (n base stride: nat) {t} {snz: 0 ≢ stride} (v: vector A (base+n*stride+t)) : vector A n :=
    GathH'_old n (pred stride) (t0:=t) (drop_plus base v).
  Next Obligation.
    destruct stride.
    contradiction snz. trivial.
    unfold pred.
    omega.
  Defined.

  Open Local Scope nat_scope.

  Program Definition GathH {A: Type}
          (i n base stride: nat)
          {snz: 0%nat ≢ stride}
          {oc: le (base+n*stride) i}
          (v: vector A i) : vector A n :=
    @GathH' A (i-base-n*stride) n stride snz (drop_plus base v).
  Next Obligation.
    revert oc.
    generalize  (n*stride) as p.
    intros.
    rename base into b.
    clear snz v stride A n.
    rewrite Plus.plus_assoc.
    rewrite le_mius_minus.
    revert oc.
    generalize (b+p) as u.
    intros.
    rewrite  le_plus_minus_r.
    reflexivity.
    assumption.
    tauto.
  Qed.
  Close Local Scope nat_scope.

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
    
    Open Local Scope nat_scope.
    
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
    
    Close Local Scope nat_scope.
  End Coq84Workaround.
  
  Definition ScatHUnion {A} {n:nat} (base:nat) (pad:nat) (v:vector A n): svector A (base+((S pad)*n)) :=
    Vector.append (Vconst None base) (ScatHUnion_0 A n pad v).
  
End SigmaHCOL_Operators.

Import SigmaHCOL_Operators.

(*
Motivating example:

BinOp(2, Lambda([ r4, r5 ], sub(r4, r5)))

-->

ISumUnion(i3, 2,
  ScatHUnion(2, 1, i3, 1) o
  BinOp(1, Lambda([ r4, r5 ], sub(r4, r5))) o
  GathH(4, 2, i3, 2)
)

 *)  


Section SigmaHCOL_language.
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
  | ANum : nat → aexp
  | AName : varname → aexp
  | APlus : aexp → aexp → aexp
  | AMinus : aexp → aexp → aexp
  | AMult : aexp → aexp → aexp.
  
  Inductive SOperator {i o:aexp}: Type :=
  (* --- HCOL basic operators --- *)
  | SHOScatHUnion (base pad:aexp): SOperator
  | SHOGathH (base stride: aexp): SOperator
  | SHOBinOp (f: A->A->A): SOperator
  (* --- lifted HCOL operators --- *)
  | SHOInfinityNorm: SOperator
  (* TODO: All HCOL operators but with aexpes instead of nums *)
  (* --- HCOL compositional operators --- *)
  | SHOCompose {fi fo gi go:aexp}: @SOperator fi fo -> @SOperator gi go -> SOperator
  (* NOTE: dimensionality of the body must match that of enclosing ISUMUnion. *)
  | SHOISumUnion (var:varname) (r:aexp) : SOperator -> SOperator
  .
  
  Definition state := varname -> @maybeError nat.
  
  Definition empty_state: state :=
    fun x =>
      match x with 
      | (Var n) => Error ("variable " ++ n ++ " not found")
      end.
  
  Definition update (st : state) (x : varname) (n : nat) : state :=
    fun x' => if eq_varname_dec x x' then OK n else st x'.

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
    | ANum x => OK x
    | AName x => st x
    | APlus a b => eval_mayberr_binop (evalAexp st a) (evalAexp st b) plus
    | AMinus a b => eval_mayberr_binop (evalAexp st a) (evalAexp st b) minus
    | AMult a b => eval_mayberr_binop (evalAexp st a) (evalAexp st b) mult
    end.

End SigmaHCOL_language.

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
    assert(Decision(i0 ≡ i1 /\ o0 ≡ o1)).
    (repeat apply and_dec); unfold Decision; decide equality.
    case H.
    intros Ha.
    destruct Ha.
    rewrite <- H0, <- H1.
    assumption.
    intros.
    exact (Error "incompatible arguments").
  Defined.

  Definition evalScatHUnion
             {i o: nat}
             (st:state)
             (ai ao base pad:aexp)
             (v:svector A i):
    @maybeError (svector A o) :=
    match evalAexp st ai, evalAexp st ao, evalAexp st base, evalAexp st pad with
    | OK ni, OK no, OK nbase, OK npad =>
      if beq_nat o no then
        match try_vector_from_svector v with
        | Error msg => Error "OHScatHUnion expects dense vector!"
        | OK x => (cast_vector_operator
                    ni (nbase + S npad * ni)
                    i o
                   (fun a => OK (ScatHUnion (A:=A) (n:=ni) nbase npad a))) x
        end
      else
        Error "input and output sizes of OHScatHUnion do not match"
    | _ , _, _, _ => Error "Undefined variables in ScatHUnion arguments"
    end.

  Definition evalGathH
             {i o: nat}
             (st:state)
             (ai ao base stride:aexp)
             (v: svector A i):  @maybeError (svector A o) :=
    match evalAexp st ai, evalAexp st ao, evalAexp st base, evalAexp st stride with
    | OK ni, OK no, OK nbase, OK nstride =>
      match eq_nat_decide 0 nstride with
      | left _ => Error "SHOGathH stride must not be 0"
      | right nsnz =>
        match le_dec (nbase+o*nstride) i with
        | right _ => Error "SHOGathH input size is too small for given params"
        | left oc =>
          if beq_nat i ni && beq_nat o no then
            OK (GathH (A:=option A)
                      (snz:=(neq_nat_to_neq nsnz))
                      (oc:=oc)
                      i o nbase nstride v)
          else
            Error "input and output sizes of SHOGathH do not match"
        end
      end
    | _ , _, _, _ => Error "Undefined variables in GathH arguments"
    end.

  Definition evalBinOp
             {i o: nat}
             (st:state)
             (ai ao: aexp)
             (f: A->A->A) (v: svector A i):
    @maybeError (svector A o) :=
    match evalAexp st ai, evalAexp st ao with
    | OK ni, OK no =>
      if beq_nat i ni && beq_nat o no then
        match try_vector_from_svector v with
        | Error msg => Error "OHScatHUnion expects dense vector!"
        | OK x =>
          (cast_vector_operator
             (o+o) o
             i o
             (OK ∘ svector_from_vector ∘ (HCOLOperators.PointWise2 f) ∘ (vector2pair o))) x
        end
      else
        Error "input and output sizes of evalBinOp do not match"
    | _ , _ => Error "Undefined variables in GathH arguments"
    end.


  Set Printing Implicits.
  Fixpoint evalSigmaHCOL {ai ao: aexp} {i o:nat}
           (st:state) (op: @SOperator A ai ao)
           (v: svector A i): @maybeError (svector A o):=
    match op with
    | SHOScatHUnion base pad => evalScatHUnion st ai ao base pad v
    | SHOGathH base stride => evalGathH st ai ao base stride v
    | SHOBinOp f => evalBinOp st ai ao f v
    | SHOCompose fi fo gi go f g =>
      match evalAexp st fi, evalAexp st fo, evalAexp st gi, evalAexp st go, evalAexp st ai, evalAexp st ao with
      | OK nfi, OK nfo, OK ngi, OK ngo, OK ni, OK no =>
        if beq_nat i ni && beq_nat o no &&
                   beq_nat ngi i && beq_nat nfo o &&
                   beq_nat ngo nfi
        then
          match evalSigmaHCOL st g v with
          | Error _ as e => e
          | OK t => evalSigmaHCOL st f t
          end
        else
          Error "Operators' dimensions in Compose does not match"
      | _ , _, _, _, _, _ => Error "Undefined variables in Compose arguments"
      end
    | SHOISumUnion var r body => 
      match evalAexp st r with
      | OK O => Error "Invalid SHOISumUnion range"
      | OK (S p) =>
        (fix evalISUM (st:state) (nr:nat) {struct nr}:
           @maybeError (svector A o) :=
           match nr with
           | O => evalSigmaHCOL (update st var nr) body v
           | S p =>
             match evalSigmaHCOL (update st var nr) body v with
             | OK x =>
               match evalISUM st p with
               | OK xs => SparseUnion x xs
               |  Error _ as e => e
               end
             |  Error _ as e => e
             end
           end) st p
      | _  => Error "Undefined variables in SHOISumUnion arguments"
      end
    | SHOInfinityNorm =>
      match evalAexp st ai, evalAexp st ao with
      | OK ni, OK no => if beq_nat i ni  && beq_nat o no && beq_nat no 1 then
                         let h := HOInfinityNorm (i:=i) in
                         Error "OK (evalHCOL h  v)"
                       else
                         Error "Invalid output dimensionality in SHOInfinityNorm"
      | _, _ => Error "Undefined variables in SHOInfinityNorm arguments"
      end
    end.
    
End SigmaHCOL_Eval.

Section SigmaHCOL_language_tests.

  (* Lemma test0: @ScatHUnion_0 nat 0 0 Vnil = Vnil.
  Proof.  compute. Qed. *)
  
  Definition a1 := update (empty_state) (Var "A1") 1.
  Definition a2 := update (empty_state) (Var "A2") 2.
  

End SigmaHCOL_language_tests.





