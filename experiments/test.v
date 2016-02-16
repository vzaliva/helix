Require Import Coq.Arith.EqNat.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Data.Monads.WriterMonad.

Set Implicit Arguments.

Section WriterMonad.
  Variable s t : Type.
  Variable Monoid_s : Monoid s.
  
  Definition writer := writerT Monoid_s ident.
  Definition runWriter x := unIdent (@runWriterT s Monoid_s ident t x).
  Definition execWriter x:= snd (runWriter x).
  Definition evalWriter x:= fst (runWriter x).
End WriterMonad.

Section with_monad.
  Import MonadNotation.
  Local Open Scope monad_scope.
  
  Definition FlagsT : Type := bool.
  
  Variable Monoid_B : Monoid FlagsT.
  Variable m : Type -> Type.
  Context {Monad_m: Monad m}.
  Context {Writer_m: MonadWriter Monoid_B m}.
  
  Definition uop 
             (op: nat -> nat)
             (x: nat) : m nat :=
    tell (beq_nat x 0) ;;
         ret (op x).
  
  Definition bop 
             (op: nat -> nat -> nat)
             (x y: nat) : m nat :=
    tell (orb (beq_nat x 0) (beq_nat y 0)) ;;
         ret (op x y).
End with_monad.

Definition sticky := Build_Monoid orb false.
Definition m : Type -> Type := writer sticky.

Definition ex1 : m nat :=  bop plus 1 2.
Definition ex2 : m nat :=  bop plus 0 5.

Compute (runWriter ex1).
Compute (execWriter ex1).
Compute (evalWriter ex1).

Compute (runWriter ex2).



