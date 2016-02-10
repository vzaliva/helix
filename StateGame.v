(* See http://lambda-files.crocodile.org/2016/02/state-monad-in-coq-tutorial.html *)

Require Import Coq.ZArith.ZArith_base Coq.Strings.String.
Require Import ExtLib.Data.Monads.StateMonad ExtLib.Structures.Monads.

Section StateGame.
  Import MonadNotation.
  Local Open Scope Z_scope.
  Local Open Scope char_scope.
  Local Open Scope monad_scope.

  Definition GameValue : Type := Z.
  Definition GameState : Type := (prod bool Z).
  
  Variable m : Type -> Type.
  Context {Monad_m: Monad m}.
  Context {State_m: MonadState GameState m}.
  
  Fixpoint playGame (s: string): m GameValue :=
    match s with
    |  EmptyString =>
       v <- get ;;
         let '(on, score) := v in ret score
    |  String x xs =>
       v <- get ;;
         let '(on, score) := v in
         match x, on with
         | "a", true =>  put (on, score + 1)
         | "b", true => put (on, score - 1)
         | "c", _ =>   put (negb on, score)
         |  _, _  =>    put (on, score)
         end ;; playGame xs
    end.

  Definition startState: GameState := (false, 0).
End StateGame.

Definition m : Type -> Type := state GameState.
Definition pg :  state GameState GameValue :=  @playGame m _  _ "abcaaacbbcabbab".
Definition main : GameValue := @evalState GameState GameValue pg startState.

Compute main.

