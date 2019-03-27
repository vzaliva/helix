
Require Import Coq.Program.Basics. (* for (∘) *)

Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Data.Monads.WriterMonad.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Data.PPair.

Set Implicit Arguments.
Set Universe Polymorphism.

Section MapWriterT.
  Variable A B: Type.
  Variable W W': Type.
  Variable Monoid_W : Monoid W.
  Variable Monoid_W' : Monoid W'.
  Variable m n : Type -> Type.

  Open Scope program_scope.

  (** Map both the return value and output of a computation using the given function.
        [[ 'runWriterT' ('mapWriterT' f m) = f ('runWriterT' m) ]]
   *)
  Definition mapWriterT (f: (m (pprod A W)%type) -> (n (pprod B W')%type)):
    (writerT Monoid_W m A) -> writerT Monoid_W' n B
    :=
      mkWriterT Monoid_W' ∘ f ∘ runWriterT.

End MapWriterT.


Section CastWriterT.
  Variable A: Type.
  Variable W : Type.
  Variable Monoid_W Monoid_W': Monoid W.
  Variable m : Type -> Type.

  Open Scope program_scope.

  (* Special case of mapWriterT where mapping functoin is identity *)
  Definition castWriterT:
    writerT Monoid_W m A -> writerT Monoid_W' m A
    := mkWriterT Monoid_W' ∘ runWriterT.

End CastWriterT.


(** Simple wrapper around ExtLib's WriterMonadT trasformed pairing it with Identity monad to simulate classic Writer Monad *)
Section WriterMonad.

  Variable W: Type.
  Variable A: Type.
  Variable Monoid_W : Monoid W.

  Open Scope program_scope.

  Definition writer := writerT Monoid_W ident.
  Definition runWriter := unIdent ∘ (@runWriterT W Monoid_W ident A).
  Definition execWriter:= psnd ∘ runWriter.
  Definition evalWriter:= pfst ∘ runWriter.

End WriterMonad.

Section MapWriter.
  Variable A B: Type.
  Variable W W' : Type.
  Variable Monoid_W: Monoid W.
  Variable Monoid_W': Monoid W'.

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
  Variable A: Type.
  Variable W : Type.
  Variable Monoid_W Monoid_W': Monoid W.

  Open Scope program_scope.

  (* Special case of mapWriter where mapping functoin is identity *)
  Definition castWriter: writer Monoid_W A -> writer Monoid_W' A
    := castWriterT Monoid_W' (m:=ident).

  Lemma evalWriter_castWriter
        {v}
    :
      evalWriter (castWriter v) = evalWriter v.
  Proof.
    unfold castWriter, castWriterT.
    unfold evalWriter.
    unfold compose.
    auto.
  Qed.

  Lemma execWriter_castWriter
        {v}
    :
      execWriter (castWriter v) = execWriter v.
  Proof.
    unfold castWriter, castWriterT.
    unfold execWriter.
    unfold compose.
    auto.
  Qed.

End CastWriter.
