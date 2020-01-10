Require Import Coq.Strings.String.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadExc.
Require Import ExtLib.Structures.MonadState.

Require Import ExtLib.Data.Monads.EitherMonad.

Import MonadNotation.
Open Scope monad_scope.
Open Scope type_scope.

Definition errS St A := St -> string+(St*A).

Instance Monad_errS St: Monad (errS St) :=
  { ret  := fun _ x => fun s => inr (s,x)
    ; bind := fun _ _ m f => fun s => match m s with
                                | inl v => inl v
                                | inr (s',x) => f x s'
                                end
  }.

Instance Exception_errS St : MonadExc string (errS St) :=
  { raise := fun _ v => fun s => inl v
    ; catch := fun _ c h => fun s => match c s with
                               | inl v => h v s
                               | inr x => inr x
                               end
  }.

Instance State_errS St : MonadState St (errS St) :=
  {
    get := fun s => inr (s,s)
    ; put := fun t s => inr (t, tt)
  }.
