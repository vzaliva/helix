Require Import Coq.ZArith.ZArith_base Coq.Strings.String.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Data.Monads.WriterMonad.

Require Import Coq.Bool.BoolEq.

(* https://wiki.haskell.org/All_About_Monads#The_Writer_monad *)
     
Section with_monad.
  Import MonadNotation.
  Local Open Scope bool_scope.
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
Definition m : Type -> Type := writerT sticky ident .

Definition ex1 :=  bop _ m plus 1 2.
Definition ex2 :=  bop _ m plus 0 5.

Compute (unIdent (runWriterT ex1)).
Compute (unIdent (runWriterT ex2)).



