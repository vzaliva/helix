
Require Import Coq.Arith.EqNat.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Data.Monads.WriterMonad.

Set Implicit Arguments.

(* Simple wrapper around ExtLib's WriterMonadT trasformed pairing it with Identity monad to simulate classic Writer Monad *)

Section WriterMonad.
  Variable s t : Type.
  Variable Monoid_s : Monoid s.
  
  Definition writer := writerT Monoid_s ident.
  Definition runWriter x := unIdent (@runWriterT s Monoid_s ident t x).
  Definition execWriter x:= snd (runWriter x).
  Definition evalWriter x:= fst (runWriter x).
End WriterMonad.
