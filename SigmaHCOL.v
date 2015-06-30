(* Coq defintions for Sigma-HCOL operator language *)

Require Import Spiral.
Require Import SVector.
Require Import HCOL.

Require Import ArithRing.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Plus.
Require Import Coq.Arith.Minus.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.BoolEq.
Require Import Coq.Strings.String.
Require Import Program. (* compose *)
Require Import Morphisms.
Require Import RelationClasses.
Require Import Relations.

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
              match (SparseUnion (Vtail a) (Vtail b)) as t with
              | Error msg => Error msg
              | OK xs =>
                match (Vhead a), (Vhead b) with
                |  Some _, Some _ => Error "incompatible values"
                |  None, None as x | None, Some _ as x | Some _ as x, None => OK (Vcons x xs)
                end
              end
  end.

Module SigmaHCOL_Operators.

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

  (* TODO: move to Spiral.v *)
  Lemma nez2gt: forall n, 0 ≢ n -> gt n 0.
  Proof.
    crush.
  Defined.
  
  (* no base. actual stride value  *)
  Program Fixpoint GathH_1 {A} {t:nat} (n stride:nat)  {snz: 0 ≢ stride}: vector A ((n*stride+t)) -> vector A n :=
      match n return vector A ((n*stride)+t) -> vector A n with
      | O => fun _ => Vnil
      | S p => fun a => Vcons (Vhead (n:=(pred ((((S p)*stride)+t)))) a) (GathH_1 p stride (t0:=t) (snz:=snz) (drop_plus stride a))
      end.
  Next Obligation.
    apply nez2gt in snz.
    lia.
  Defined.
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

  Open Local Scope nat_scope.

  (* TODO: move *)
  Lemma le_mius_minus : forall a b c, a>=(b+c) -> a-b-c ≡ a - (b+c).
  Proof.
    intros.
    omega.
  Qed.
  
  Program Definition GathH1 {A: Type}
          (i n base stride: nat)
          {snz: 0%nat ≢ stride}
          {oc: le (base+n*stride) i}
          (v: vector A i) : vector A n :=
    @GathH_1 A (i-base-n*stride) n stride snz (drop_plus base v).
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
    
    Close Scope nat_scope.
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

  Section Errors.
    Inductive compileError {A:Type}: Type :=
    | CompileOK : A → @compileError A
    | CompileError: string -> @compileError A.
    
    Inductive runtimeError {A:Type}: Type :=
    | RuntimeOK : A → @runtimeError A
    | RuntimeError: string -> @runtimeError A.    
  End Errors.
  
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
  | SHAScatHUnion (base pad:aexp): SOperator
  | SHAGathH (base stride: aexp): SOperator
  | SHABinOp (f: A->A->A): SOperator
  (* TODO: all HCOL operators but with aexpes instead of nums *)
  | SHACompose: SOperator -> SOperator -> SOperator
  | SHAISumUnion (v:varname) (r:aexp) : SOperator -> SOperator
  .
  
  Definition state := varname -> @compileError nat.
  
  Definition empty_state: state :=
    fun x =>
      match x with 
      | (Var n) => CompileError ("variable " ++ n ++ " not found")
      end.
  
  Definition update (st : state) (x : varname) (n : nat) : state :=
    fun x' => if eq_varname_dec x x' then CompileOK n else st x'.

  Definition eval_mayberr_binop (a: @compileError nat) (b: @compileError nat) (op: nat->nat->nat) :=
    match a with
    | CompileError msg => CompileError msg
    | CompileOK an => match b with
                     | CompileError msg => CompileError msg
                     | CompileOK bn => CompileOK (op bn an)
                     end
    end.
  
  Fixpoint evalAexp (st:state) (e:aexp): @compileError nat :=
    match e  with
    | ANum x => CompileOK x
    | AName x => st x
    | APlus a b => eval_mayberr_binop (evalAexp st a) (evalAexp st b) plus
    | AMinus a b => eval_mayberr_binop (evalAexp st a) (evalAexp st b) minus
    | AMult a b => eval_mayberr_binop (evalAexp st a) (evalAexp st b) mult
    end.

  Set Printing Implicit.

  Definition cast_lift_operator
             (i0:nat) (o0:nat)
             (i1:nat) (o1:nat)
             (f: (svector A i0) -> (svector A o0))  : @compileError ((svector A i1) -> (svector A o1)).
  Proof.
    assert(Decision(i0 ≡ i1 /\ o0 ≡ o1)).
    (repeat apply and_dec); unfold Decision; decide equality.
    case H.
    intros Ha.
    destruct Ha.
    rewrite <- H0, <- H1.
    left. assumption.
    right. exact "incompatible arguments".
  Defined.
  
  (* TODO: better name *)
  Definition add_runtime_error_err
             (i:nat) (o:nat)
             (f: (svector A i) -> (svector A o))  : (svector A i) -> (@runtimeError (svector A o)) :=
    fun v => RuntimeOK (f v).
  

  (* TODO: better name *)
  Definition ugly_cast
             (i o0 o1:nat)
             (f: @compileError (vector (option A) i → @runtimeError (vector (option A) o0))):
    @compileError (vector (option A) i → @runtimeError (vector (option A) o1)).
  Proof.
    assert(Decision(o0 ≡ o1)).
    unfold Decision. decide equality.
    case H.
    intros.
    rewrite <- e. 
    assumption.
    intros.
    right.
    exact "Incompatible vector dimensions".
  Qed.
  
  Definition compileScatHUnion
             (i o: nat)
             (st:state)
             (ai ao base pad:aexp):
    (@compileError ((svector A i) -> (@runtimeError (svector A o)))) :=
    match (evalAexp st ai), (evalAexp st ao), (evalAexp st base), (evalAexp st pad) with
    | CompileOK ni, CompileOK no, CompileOK nbase, CompileOK npad =>
      if beq_nat i ni && beq_nat o no && beq_nat no (nbase + S npad * ni) then
        ugly_cast i (nbase + S npad* i) o
                  (CompileOK
                     (fun dv =>
                        match (try_vector_from_svector dv) with
                        | OK x => RuntimeOK (ScatHUnion (A:=A) (n:=i) nbase npad x) 
                        | Error msg => RuntimeError "ScatHUnion expects dense vector!"
                        end))
      else
        CompileError "input and output sizes of OHScatHUnion do not match"
    | _ , _, _, _ => CompileError "Undefined variables in ScatHUnion arguments"
    end.

  Definition compileGathH
             (i o: nat)
             (st:state)
             (ai ao base stride:aexp):
    (@compileError ((svector A i) -> (@runtimeError (svector A o)))) :=
    match (evalAexp st ai), (evalAexp st ao), (evalAexp st base), (evalAexp st stride) with
    | CompileOK ni, CompileOK no, CompileOK nbase, CompileOK nstride =>

      (* TODO: calculate 't' from 'i' size *)
      (* TODO: check 0 ≢ stride *)

      if beq_nat i ni && beq_nat o no && beq_nat ni (nbase+o*nstride+t) then
        (CompileOK
           (fun v => RuntimeOK (GathH (A:=option A) o nbase nstride v)
        ))
      else
        CompileError "input and output sizes of SHAGathH do not match"
    | _ , _, _, _ => CompileError "Undefined variables in GathH arguments"
    end.
  
              (*ugly_cast i (nbase + S npad* i) o
                         *)
    
  (*   Program Definition GathH {A: Type} (n base stride: nat) {t} {snz: 0 ≢ stride} (v: vector A (base+n*stride+t)) : vector A n *)
  
                                                                             
  Fixpoint compile {ai ao: aexp} {i o:nat}
           (st:state) (op: @SOperator ai ao)
    : @compileError ((svector A i) -> (@runtimeError (svector A o))) :=
    match op with
    | SHAScatHUnion base pad => compileScatHUnion i o st ai ao base pad
    | SHAGathH base stride => compileGathH  i o st ai ao base stride
    | SHABinOp f => CompileError "TODO"
    | SHACompose f g => CompileError "TODO"
    | SHAISumUnion r x op => CompileError "TODO"
    end.
  
  
End SigmaHCOL_language.

Section SigmaHCOL_language_tests.

  (* Lemma test0: @ScatHUnion_0 nat 0 0 Vnil = Vnil.
  Proof.  compute. Qed. *)
  
  Definition a1 := update (empty_state) (Var "A1") 1.
  Definition a2 := update (empty_state) (Var "A2") 2.
  

End SigmaHCOL_language_tests.





