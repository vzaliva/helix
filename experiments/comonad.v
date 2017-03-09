Require Import Coq.Arith.EqNat.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Data.Monads.WriterMonad.
Require Import ExtLib.Data.PPair.
Require Import ExtLib.Structures.CoMonad.

Set Implicit Arguments.
Set Universe Polymorphism.

Import MonadNotation.
Local Open Scope monad_scope.

Section WriterMonad.
  Variable s t : Type.
  Variable Monoid_s : Monoid s.

  Definition writer := writerT Monoid_s ident.
  Definition runWriter x := unIdent (@runWriterT s Monoid_s ident t x).
  Definition execWriter x:= psnd (runWriter x).
  Definition evalWriter x:= pfst (runWriter x).
End WriterMonad.

(*

Class CoMonad (m : Type → Type) : Type :=
{ coret : ∀ {A}, m A → A
; cobind : ∀ {A B}, m A → (m A → B) → m B
}.

*)


Instance WriterCoMonad {w:Type} {m: Monoid w}:
  CoMonad (@writer w m) :=
  {
    coret a := @evalWriter w a m ;
    cobind a b wa f := tell (execWriter wa) ;; ret (f wa)
  }.
