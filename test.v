Require Import Coq.ZArith.ZArith_base Coq.Strings.String.
Require Import ExtLib.Data.Monads.StateMonad ExtLib.Structures.Monads.
Require Import Coq.Bool.BoolEq.

Section with_monad.
  Import MonadNotation.
  Local Open Scope bool_scope.
  Local Open Scope monad_scope.

  Definition FlagsT : Type := bool.
  Definition FlagsCombine :  FlagsT -> FlagsT -> FlagsT := orb.
  
  Variable m : Type -> Type.
  Context {Monad_m: Monad m}.
  Context {State_m: MonadState FlagsT m}.
  
  Definition uop 
             (op: nat -> nat)
             (x: nat) : m nat :=
    f <- get ;;
      put (FlagsCombine f (beq_nat x 0)) ;;
      ret (op x).
  
  Definition bop 
             (op: nat -> nat -> nat)
             (x y: nat) : m nat :=
    f <- get ;;
      put (FlagsCombine f (orb (beq_nat x 0) (beq_nat y 0))) ;;
      ret (op x y).

  Definition bop1 
             (op: nat -> nat -> nat)
             (x y: m nat) : m nat :=
    f <- get ;;
      xv <- x ;;
      yv <- y ;;
      put (FlagsCombine f (orb (beq_nat xv 0) (beq_nat yv 0))) ;;
      ret (op xv yv).
    
End with_monad.

Definition m : Type -> Type := state bool.
Definition ex1 :=  bop m plus 1 2.
Definition ex2 :=  bop m plus 0 5.

Compute (runState ex1 false).
Compute (runState ex1 true).
Compute (runState ex2 false).
Compute (runState ex2 true).

