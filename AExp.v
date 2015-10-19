(* Simple arithmetic expression language for natural numbers *)

Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.implementations.peano_naturals.

Inductive varname : Type :=
  Var : string -> varname.

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
| AConst : nat -> aexp
| AValue : varname -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.

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
  destruct (eq_varname_dec var var). 
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

