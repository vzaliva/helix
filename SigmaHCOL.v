(* Coq defintions for Sigma-HCOL operator language *)

Require Import Spiral.
Require Import HCOL.

Require Import ArithRing.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.BoolEq.

Require Import Program. (* compose *)
Require Import Morphisms.
Require Import RelationClasses.
Require Import Relations.

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

Require Import Coq.Lists.List.

Global Instance opt_equiv `{Equiv A}: Equiv (option A) :=
  fun a b =>
    match a with
    | None => is_None b
    | Some x => (match b with
                 | None => False
                 | Some y => equiv x y
                 end)
    end.

Global Instance opt_vec_equiv `{Equiv A} {n}: Equiv (vector (option A) n) := Vforall2 (n:=n) opt_equiv.

Fixpoint catSomes {A} {n} (v:vector (option A) n): list A :=
  match v with
  | Vnil => @List.nil A
  | Vcons None _ vs  => catSomes vs
  | Vcons (Some x) _ vs => List.cons x (catSomes vs)
  end.

Module SigmaHCOLOperators.

  Definition OptCast {A} {n:nat} (v:vector A n): vector (option A) n :=
    Vmap (Some) v.

  (* zero - based, (stride-1) parameter *)
  Program Fixpoint GathH_0 {A} {t:nat} (n s:nat) : vector A ((n*(S s)+t)) -> vector A n :=
    let stride := S s in (
      match n return vector A ((n*stride)+t) -> vector A n with
        | O => fun _ => Vnil
        | S p => fun a => Vcons (Vhead a) (GathH_0 p s (t0:=t) (drop_plus stride a))
      end).
  Next Obligation.
    lia.
  Defined.

  Program Definition GathH {A: Type} (n base stride: nat) {t} {snz: 0 ≢ stride} (v: vector A (base+n*stride+t)) : vector A n :=
    GathH_0 n (pred stride) (t0:=t) (drop_plus base v).
  Next Obligation.
    destruct stride.
    contradiction snz. trivial.
    unfold pred.
    lia.
  Defined.

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
    
    Open Scope nat_scope.
    
    Fixpoint ScatHUnion_0 (A:Type) (n:nat) (pad:nat) {struct n}:
      vector A n -> vector (option A) ((S pad)*n).
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
    
    Close Scope nat_scope.
  End Coq84Workaround.
  
  Definition ScatHUnion {A} {n:nat} (base:nat) (pad:nat) (v:vector A n): vector (option A) (base+((S pad)*n)) :=
    Vector.append (Vconst None base) (ScatHUnion_0 A n pad v).
  
End SigmaHCOLOperators.

Import SigmaHCOLOperators.
Require Import HCOLSyntax.

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


Section OHOperator_language.
  (* ---  An extension of HOperator to deal with missing values. Instead of vector of type 'A' they operate on vectors of 'option A'  --- *)

  Context {A:Type} {Ae: Equiv A}.
  
  Inductive OHOperator : nat -> bool -> nat -> bool -> Type :=
  | OHScatHUnion {i} (base pad:nat): OHOperator i false (base+((S pad)*i)) true
  | OHGathH (n base stride: nat) {t} {snz: 0 ≢ stride}: OHOperator (base+n*stride+t) false n false
  | OHBinOp o (f: A->A->A): OHOperator (o+o) false o false
  | OHHOperator {i o} (op: HOperator i o): OHOperator i false o false (* cast classic HOperator to  OHOperator *)
  | OHCompose i ifl {t} {tfl} o ofl: OHOperator t tfl o ofl -> OHOperator i ifl t tfl -> OHOperator i ifl o ofl
  | OHOptCast {i}: OHOperator i false i true (* Cast any vector to vector of options *)
  .

End OHOperator_language.  

Section SOHOperator_language.
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
  
  Inductive SHAOperator: aexp -> bool -> aexp -> bool -> Type :=
  | SHAScatHUnion {i o:aexp} (base pad:aexp): SHAOperator i false o true
  | SHAGathH (i n base stride: aexp): SHAOperator i false n false
  | SHABinOp {i o:aexp} (f: A->A->A): SHAOperator i false o false
  (* TODO: all HCOL operators but with aexpes instead of nums *)
  | SHACompose i ifl o ofl {ai ao} {bi bo} {tifl tofl} : SHAOperator ai tifl ao ofl -> SHAOperator bi ifl bo tofl -> SHAOperator i ifl o ofl
  | SHAOptCast {i}: SHAOperator i false i true
  | SHAISumUnion {i o: aexp} (v:varname) (r:aexp) : SHAOperator i false o true -> SHAOperator i false o false
  .
    
  Inductive maybeError {T:Type} : Type :=
  | OK : T → @maybeError T
  | Error: string -> @maybeError T.

  Definition isError {T:Type}  (x:@maybeError T) :=
    match x with
    | OK _ => False
    | Error _ => True
    end.

  Definition isOK {T:Type}  (x:@maybeError T) :=
    match x with
    | OK _ => True
    | Error _ => False
    end.
  
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
                 | OK bn => OK (bn + an)
                 end
    end.
  
  Fixpoint eval (st:state) (e:aexp): @maybeError nat :=
    match e  with
    | ANum x => OK x
    | AName x => st x
    | APlus a b => eval_mayberr_binop (eval st a) (eval st b) plus
    | AMinus a b => eval_mayberr_binop (eval st a) (eval st b) minus
    | AMult a b => eval_mayberr_binop (eval st a) (eval st b) mult
    end.
        
  Definition cast_OHOperator
             (a0:nat) (b0:bool) (c0:nat) (d0:bool)
             (a1:nat) (b1:bool) (c1:nat) (d1:bool)
             (x: OHOperator a0 b0 c0 d0) : @maybeError (OHOperator a1 b1 c1 d1).
  Proof.
    assert(Decision(a0 ≡ a1 /\ b0 ≡ b1 /\ c0 ≡ c1 /\ d0 ≡ d1)).
    (repeat apply and_dec); unfold Decision; decide equality.
    case H.
    intros Ha.
    destruct Ha. destruct H1. destruct H2.
    rewrite H0, H1, H2, H3 in x.
    left. assumption.
    right. exact "incompatible arguments".
  Defined.

  Definition compileSHAOperator {iflag oflag:bool} {ai ao: aexp} {i o:nat} (st:state)
             (op: (SHAOperator ai iflag ao oflag)): @maybeError (OHOperator (A:=A) i iflag o oflag) :=
    match op with
    | SHAScatHUnion ai ao base pad =>
      match (eval st ai) with
      | Error msg => Error msg
      | OK ni =>
        match (eval st ao) with
        | Error msg => Error msg
        | OK no => 
          match (eval st base) with
          | Error msg => Error msg
          | OK nbase => 
            match (eval st pad) with
            | Error msg => Error msg
            | OK npad =>
              if iflag then
                Error "iflag must be false"
              else if oflag then
                     if beq_nat i ni && beq_nat no (nbase + S npad * ni) then
                       cast_OHOperator
                         ni false (nbase + S npad * ni) true
                         i iflag o oflag
                         (OHScatHUnion (i:=ni) nbase npad)
                     else
                       Error "input and output sizes of OHScatHUnion do not match"
                   else
                     Error "oflag must be true"
            end
          end
        end
      end
    | SHAGathH ai an abase astride =>
      match (eval st ai) with
      | Error msg => Error msg
      | OK ni =>
        match (eval st an) with
        | Error msg => Error msg
        | OK nn =>
          match (eval st abase) with
          | Error msg => Error msg
          | OK nbase =>
            match (eval st astride) with
            | Error msg => Error msg
            | OK O => Error "Zero stride not allowed"
            | OK (S s) =>
              if iflag then
                Error "iflag must be false"
              else if oflag then
                     Error "oflag must be false"
                   else if beq_nat o nn && (Coq.Arith.Compare_dec.leb (nbase + nn*(S s)) ni || beq_nat (nbase+nn*(S s)) ni)
                        then
                          let t := (minus ni (nbase + nn*(S s))) in
                          cast_OHOperator
                            (nbase+nn*(S s)+t) false nn false
                            i iflag o oflag
                            (OHGathH nn nbase (S s) (t:=t) (snz:=O_S _))
                        else
                          Error "input and output sizes of OHScatHUnion do not match"
            end
          end
        end
      end
    | SHABinOp ai ao f =>
      match (eval st ai) with
      | Error msg => Error msg
      | OK ni =>
        match (eval st ao) with
        | Error msg => Error msg
        | OK no =>
          if beq_nat o no && beq_nat i (no+no) then
            cast_OHOperator
              (no+no) false no false
              i iflag o oflag
              (OHBinOp no f)
          else
            Error "input and output sizes of OHBinOp do not match"
        end
      end
    | SHACompose xi ifl xo ofl ai ao bi bo tifl tofl opa opb =>
      match (eval st xi) with
      | Error msg => Error msg
      | OK nxi =>
        match (eval st xo) with
        | Error msg => Error msg
        | OK nxo =>
          match (eval st ai) with
          | Error msg => Error msg
          | OK nai =>
            match (eval st ao) with
            | Error msg => Error msg
            | OK nao =>
              match (eval st bi) with
              | Error msg => Error msg
              | OK nbi =>
                match (eval st bo) with
                | Error msg => Error msg
                | OK nbo => 
                  if beq_nat o nxo && beq_nat i nxi
                             && beq_nat nao nxo
                             && beq_nat nai nbo
                             && beq_nat nbi nxi
                             && eqb oflag ofl && eqb iflag ifl
                  then
                    Error "TODO"
                  else
                    Error "Dimensions or flags of OHBinOp do not match"
                end
              end
            end
          end
        end
      end
    | SHAOptCast ai =>
      match (eval st ai) with
      | Error msg => Error msg
      | OK ni =>
        if beq_nat o ni && beq_nat i ni then
          cast_OHOperator
            ni false ni true
            i iflag o oflag
            (OHOptCast (i:=ni))
        else
          Error "input and output sizes of SHAOptCast do not match"
      end
    | SHAISumUnion i o v r x => Error "TODO"
    end.
  
End SOHOperator_language.

Section SigmaHCOL_language_tests.

  (* Lemma test0: @ScatHUnion_0 nat 0 0 Vnil = Vnil.
  Proof.  compute. Qed. *)
  
  Definition a1 := update (empty_state) (Var "A1") 1.
  Definition a2 := update (empty_state) (Var "A2") 2.
  
  Lemma test1: (compileSHAOperator (i:=1) (o:=2) (empty_state) (SHAScatHUnion (i:=(ANum 1)) (o:=(ANum 2)) (ANum 0) (ANum 1))) ≡ OK (OHScatHUnion 0 1).
  Proof. auto. Qed.

  Lemma test2: isError (compileSHAOperator (i:=2) (o:=2) (empty_state) (SHAScatHUnion (i:=(ANum 1)) (o:=(ANum 2)) (ANum 0) (ANum 1))).
  Proof. compute. trivial. Qed.

  Lemma test3: isError (compileSHAOperator (i:=1) (o:=2) (empty_state) (SHAScatHUnion (i:=(ANum 1)) (o:=(ANum 4)) (ANum 0) (ANum 1))).
  Proof. compute. trivial. Qed.

  Lemma test4: isError (compileSHAOperator (i:=1) (o:=2) (empty_state) (SHAScatHUnion (i:=(AName (Var "A1"))) (o:=(ANum 2)) (ANum 0) (ANum 1))).
  Proof. compute. trivial. Qed.
                 
  Lemma test5: (compileSHAOperator (i:=1) (o:=2) a1 (SHAScatHUnion (i:=(AName (Var "A1"))) (o:=(ANum 2)) (ANum 0) (ANum 1))) ≡ OK (OHScatHUnion 0 1).
  Proof.
    unfold compileSHAOperator.
    assert (eval a1 (AName (Var "A1")) ≡ OK 1).
    compute.
    case eq_varname_dec.
    intros. reflexivity.
    intros. contradiction n. reflexivity.
    rewrite H.
    auto.
  Qed.

  Lemma test6: isError (compileSHAOperator (i:=1) (o:=2) a2 (SHAScatHUnion (i:=(AName (Var "A2"))) (o:=(ANum 2)) (ANum 0) (ANum 1))).
  Proof.
    unfold compileSHAOperator.
    assert (eval a2 (AName (Var "A2")) ≡ OK 2).
    compute.
    case eq_varname_dec.
    intros. reflexivity.
    intros. contradiction n. reflexivity.
    rewrite H.
    compute. trivial.
  Qed.

  Lemma test7: compileSHAOperator (i:=10) (o:=5) empty_state (SHAGathH (ANum 10) (ANum 5) (ANum 0) (ANum 2)) ≡ OK (OHGathH 5 0 2 (snz:=O_S 1)).
  Proof.  compute.  reflexivity. Qed.
                 
  Lemma test8: compileSHAOperator (i:=11) (o:=5) empty_state (SHAGathH (ANum 11) (ANum 5) (ANum 0) (ANum 2)) ≡ OK (OHGathH 5 0 2 (snz:=O_S 1)).
  Proof.  compute.  reflexivity. Qed.

  Lemma test9: isError (compileSHAOperator (i:=11) (o:=5) empty_state (SHAGathH (ANum 10) (ANum 5) (ANum 0) (ANum 2))).
  Proof.  compute.  trivial. Qed.

  Lemma test10: isError (compileSHAOperator (i:=10) (o:=5) empty_state (SHAGathH (ANum 10) (ANum 5) (ANum 1) (ANum 2))).
  Proof.  compute.  trivial. Qed.

End SigmaHCOL_language_tests.



  
  
