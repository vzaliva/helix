Require Import Coq.Program.Basics. (* for compose *)

Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Data.Monads.WriterMonad.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Data.PPair.

Set Implicit Arguments.
Set Universe Polymorphism.

Section MapWriterT.
  Polymorphic Universe g s d c.
  Variable A: Type@{g}.
  Variable B : Type@{g}.
  Variable W : Type@{s}.
  Variable W' : Type@{s}.
  Variable Monoid_W : Monoid@{d} W.
  Variable Monoid_W' : Monoid@{d} W'.
  Variable m : Type@{d} -> Type@{c}.
  Variable n : Type@{d} -> Type@{c}.

  (** Map both the return value and output of a computation using the given function.
        [[ 'runWriterT' ('mapWriterT' f m) = f ('runWriterT' m) ]]
   *)
  Definition mapWriterT (f: (m (pprod A W)%type) -> (n (pprod B W')%type))
             (x: writerT Monoid_W m A): writerT Monoid_W' n B
    :=
      mkWriterT _ (f (runWriterT x)).

End MapWriterT.


Section CastWriterT.
  Polymorphic Universe g s d c.
  Variable A: Type@{g}.
  Variable W : Type@{s}.
  Variable Monoid_W : Monoid@{d} W.
  Variable Monoid_W' : Monoid@{d} W.
  Variable m : Type@{d} -> Type@{c}.

(* Special case of mapWriterT where mapping functoin is identity *)
  Definition castWriterT (x: writerT Monoid_W m A): writerT Monoid_W' m A
    := mkWriterT _ (runWriterT x).

End CastWriterT.



(** Simple wrapper around ExtLib's WriterMonadT trasformed pairing it with Identity monad to simulate classic Writer Monad *)
Section WriterMonad.
  Polymorphic Universe s d c.

  Variable W: Type@{s}.
  Variable A: Type@{d}.
  Variable Monoid_W : Monoid@{c} W.

  Open Scope program_scope.

  Definition writer := writerT Monoid_W ident.
  Definition runWriter := unIdent ∘ (@runWriterT W Monoid_W ident A).
  Definition execWriter:= psnd ∘ runWriter.
  Definition evalWriter:= pfst ∘ runWriter.

End WriterMonad.

Section MapWriter.
  Polymorphic Universe g s d c.
  Variable A: Type@{g}.
  Variable B : Type@{g}.
  Variable W : Type@{s}.
  Variable W' : Type@{s}.
  Variable Monoid_W : Monoid@{d} W.
  Variable Monoid_W' : Monoid@{d} W'.

  Open Scope program_scope.

  (** Map both the return value and output of a computation using the given function.
        [[ 'runWriter' ('mapWriter' f m) = f ('runWriter' m) ]]
   *)
  Definition mapWriter (f: (pprod A W)%type -> (pprod B W')%type) :
    writer Monoid_W A -> writer Monoid_W' B
    :=
      mapWriterT B Monoid_W' ident (mkIdent ∘ f ∘ unIdent).

End MapWriter.

Section CastWriter.
  Polymorphic Universe g s d c.
  Variable A: Type@{g}.
  Variable W : Type@{s}.
  Variable Monoid_W : Monoid@{d} W.
  Variable Monoid_W' : Monoid@{d} W.

  Open Scope program_scope.

  Definition castWriter: writer Monoid_W A -> writer Monoid_W' A
    := mapWriterT A Monoid_W' ident id.

End CastWriter.
