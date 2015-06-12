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

(* Error type *)
Inductive maybeError {T:Type} : Type :=
| OK : T → @maybeError T
| Error: string -> @maybeError T.

Definition is_Error {T:Type}  (x:@maybeError T) :=
  match x with
  | OK _ => False
  | Error _ => True
  end.

Definition is_OK {T:Type}  (x:@maybeError T) :=
  match x with
  | OK _ => True
  | Error _ => False
  end.

(* "sparse" vector *)
Notation svector A n := (vector (option A) n).

Global Instance opt_equiv `{Equiv A}: Equiv (option A) :=
  fun a b =>
    match a with
    | None => is_None b
    | Some x => (match b with
                 | None => False
                 | Some y => equiv x y
                 end)
    end.

Global Instance sparce_vec_equiv `{Equiv A} {n}: Equiv (svector A n) := Vforall2 (n:=n) opt_equiv.

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

Fixpoint catSomes {A} {n} (v:svector A n): list A :=
  match v with
  | Vnil => @List.nil A
  | Vcons None _ vs  => catSomes vs
  | Vcons (Some x) _ vs => List.cons x (catSomes vs)
  end.

Definition SparseCast {A} {n} (v:vector A n): svector A n :=
  Vmap (Some) v.

Definition is_Dense {A} {n} (v:svector A n) : Prop :=
  Vforall is_Some v.

Definition from_Some {A} (x:option A) {S: is_Some x}: A.
Proof.
  destruct x.
  tauto.
  unfold is_Some in S.
  tauto.
Defined.

Lemma dense_get_hd {A} {n} (v:svector A (S n)): is_Dense v -> A.
Proof.
  unfold is_Dense.
  intros.
  assert (is_Some (Vhead v)).
  apply Vforall_hd. assumption.
  revert H0.
  apply from_Some.
Defined.

Lemma dense_tl {A} {n} {v: svector A (S n)}: is_Dense v -> is_Dense (Vtail v).
Proof.
  unfold is_Dense.
  intros.
  dep_destruct v.
  simpl in H.
  simpl.
  apply H.
Defined.

Inductive DenseV {A:Type} {n:nat} : Type :=
| buildDenseV (v:svector A n) (H:is_Dense v): DenseV.

Definition DenseVtail {A:Type} {n:nat} (d:@DenseV A (S n)): @DenseV A n :=
  match d with
  | buildDenseV v H => buildDenseV (Vtail v) (dense_tl H)
  end.
  
Fixpoint DenseCast' {A} {n} (d:@DenseV A n): vector A n :=
  match n return @DenseV A n -> (vector A n) with
  | O => fun _ => @Vnil A
  | (S p) => fun d0 =>
               match d0 return @DenseV A (S p) -> (vector A (S p)) with
               | buildDenseV v i =>
                 fun d2 => Vcons (dense_get_hd v i) (DenseCast' (DenseVtail d2))
               end d0
  end d.

Fixpoint DenseCast {A} {n} (v:svector A n) (H:is_Dense v): vector A n :=
  DenseCast' (buildDenseV v H).
    
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
  
  Inductive SOperator: aexp -> aexp-> Type :=
  | SHAScatHUnion {i o:aexp} (base pad:aexp): SOperator i o 
  | SHAGathH (i n base stride: aexp): SOperator i n 
  | SHABinOp {i o:aexp} (f: A->A->A): SOperator i o 
  (* TODO: all HCOL operators but with aexpes instead of nums *)
  | SHACompose i o {ai ao} {bi bo}: SOperator ai ao -> SOperator bi bo -> SOperator i o
  | SHAISumUnion {i o: aexp} (v:varname) (r:aexp) : SOperator i o  -> SOperator i o
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
  
  Fixpoint eval (st:state) (e:aexp): @maybeError nat :=
    match e  with
    | ANum x => OK x
    | AName x => st x
    | APlus a b => eval_mayberr_binop (eval st a) (eval st b) plus
    | AMinus a b => eval_mayberr_binop (eval st a) (eval st b) minus
    | AMult a b => eval_mayberr_binop (eval st a) (eval st b) mult
    end.

  Set Printing Implicit.


Definition cast_lift_operator
             (i0:nat) (o0:nat)
             (i1:nat) (o1:nat)
             (f: (svector A i0) -> (svector A o0))  : @maybeError ((svector A i1) -> (svector A o1)).
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
  
  Definition semScatHUnion {i o:nat}
             (st:state)
             (ai ao base pad:aexp):
    @maybeError ((svector A i) -> (svector A o)) :=
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
            if beq_nat i ni && beq_nat o no && beq_nat no (nbase + S npad * ni) then
              (cast_lift_operator
                 ni (nbase + S npad * ni)
                 i o
                 (compose
                    (ScatHUnion (A:=A) (n:=ni) nbase npad)
                    (DenseCast))
              )
            else
              Error "input and output sizes of OHScatHUnion do not match"
          end
        end
      end
    end.
  
  (* 
Compute denotational semantics of SOperator expresssion.
Not all expressions have semantics, and in ths case this function
returns 'Error', which means that given expression is incorrect.

Unfortuntatelly not all compiled expressions return valid vector due
to sparcity. Access to sparse vector elements or `SparseUnion` could
give runtime errors, not detectable at this stage.  

A separate proofs could be provided guaranteeing that given SOperator
expression never returns 'Error' or, for example, that it returns
dense (non-sparse) vector.
   *)
  
  Fixpoint sem {ai ao: aexp} {i o:nat}
           (st:state) (op: (SOperator ai ao))
    : @maybeError ((svector A i) -> (@maybeError (svector A o))) :=
      match  op with
      | SHAScatHUnion i o base pad => Error "TODO"
      | SHAGathH i n base stride => Error "TODO"
      | SHABinOp i o f => Error "TODO"
      | SHACompose i o ai ao bi bo x x0 => Error "TODO"
      | SHAISumUnion i o v r x => Error "TODO"
      end.
        
    
End SigmaHCOL_language.

Section SigmaHCOL_language_tests.

  (* Lemma test0: @ScatHUnion_0 nat 0 0 Vnil = Vnil.
  Proof.  compute. Qed. *)
  
  Definition a1 := update (empty_state) (Var "A1") 1.
  Definition a2 := update (empty_state) (Var "A2") 2.
  

End SigmaHCOL_language_tests.



  
  
