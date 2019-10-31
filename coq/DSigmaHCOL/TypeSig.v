Require Import Coq.Arith.Arith.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Decidable.
Require Import Omega.
Require Import Psatz.

Require Import CoLoR.Util.Nat.NatUtil.

From Coq.FSets Require Import
     FSetAVL
     FSetInterface
     FSetFacts
     FSetProperties
     FSetToFiniteSet
     FMapAVL
     FMapInterface
     FMapFacts.

Require Import Helix.HCOL.CarrierType.

Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.

Require Import MathClasses.misc.util.
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.implementations.peano_naturals.
Require Import MathClasses.orders.orders.
Require Import MathClasses.misc.decision.

Require Import Helix.Util.OptionSetoid.
Require Import Helix.Tactics.HelixTactics.

Open Scope list_scope.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope nat_scope.

Module TM := FMapAVL.Make(Nat_as_OT).
Module Import TP := FMapFacts.WProperties_fun(Nat_as_OT)(TM).
(* [TypeSig] is a signature of an evaluation context, which maps
   De-Brujn indices to expected types *)
Definition TypeSig := TM.t DSHType.

Global Instance DSHValType_Decision (v:DSHVal) (t:DSHType):
  Decision (DSHValType v t).
Proof.
  unfold decidable.
  destruct v,t; try (left;constructor); right; intros H; inversion H.
Qed.

Definition DSHValType_bool (v:DSHVal) (t:DSHType) := bool_decide (DSHValType v t).

(* True if nth context element has expected type. decidable. *)
Definition contextEnsureType (σ: evalContext) (k:nat) (t:DSHType) : Prop :=
  match nth_error σ k with
  | Some v => DSHValType v t
  | _ => False
  end.

Global Instance contextEnsureType_Decision {σ k t}:
  Decision (contextEnsureType σ k t).
Proof.
  unfold Decision, contextEnsureType.
  break_match; auto.
  apply DSHValType_Decision.
Qed.

Definition typecheck_env (tm:TypeSig) (σ: evalContext) :  Prop :=
  forall k t, TM.MapsTo k t tm -> contextEnsureType σ k t.

Global Instance typecheck_env_Decision (tm:TypeSig) (σ: evalContext):
  Decision (typecheck_env tm σ).
Proof.
Admitted.

(* alternative definition on booleans using `for_all` *)
Definition typecheck_env_bool (tm:TypeSig) (σ: evalContext) : bool :=
  TP.for_all (fun k t => bool_decide (contextEnsureType σ k t)) tm.

(* Sanity check *)
Lemma typecheck_env_bool_iff (tm:TypeSig) (σ: evalContext):
  bool_decide (typecheck_env tm σ) ≡ typecheck_env_bool tm σ.
Proof.
Admitted.

Definition TypeSigMExpr (me:MExpr) : TypeSig :=
  match me with
  | MVar v => TM.add v DSHMemBlock (TM.empty _)
  | MConst _ => TM.empty _
  end.


Definition TypeSigUnion := TP.update (elt:=DSHType).


(* True, if given type signatures do not have conflicts.
   A conflict occurs when different values occur at
   different signatures at the same index.
 *)
Definition TypeSigCompat (s1 s2:TypeSig) : Prop. Admitted.

Fixpoint TypeSigNExpr (ne:NExpr) : TypeSig :=
  match ne with
  | NVar v => TM.add v DSHnat (TM.empty _)
  | NConst x => TM.empty _
  | NDiv a b => TypeSigUnion (TypeSigNExpr a) (TypeSigNExpr b)
  | NMod a b => TypeSigUnion (TypeSigNExpr a) (TypeSigNExpr b)
  | NPlus a b => TypeSigUnion (TypeSigNExpr a) (TypeSigNExpr b)
  | NMinus a b => TypeSigUnion (TypeSigNExpr a) (TypeSigNExpr b)
  | NMult a b => TypeSigUnion (TypeSigNExpr a) (TypeSigNExpr b)
  | NMin a b => TypeSigUnion (TypeSigNExpr a) (TypeSigNExpr b)
  | NMax a b => TypeSigUnion (TypeSigNExpr a) (TypeSigNExpr b)
  end.

Fixpoint TypeSigAExpr (ae:AExpr) : TypeSig :=
  match ae with
  | AVar v => TM.add v DSHCarrierA (TM.empty _)
  | AConst _ => TM.empty _
  | ANth m n => TypeSigUnion (TypeSigMExpr m) (TypeSigNExpr n)
  | AAbs a => TypeSigAExpr a
  | APlus a b => TypeSigUnion (TypeSigAExpr a) (TypeSigAExpr b)
  | AMinus a b => TypeSigUnion (TypeSigAExpr a) (TypeSigAExpr b)
  | AMult a b => TypeSigUnion (TypeSigAExpr a) (TypeSigAExpr b)
  | AMin a b => TypeSigUnion (TypeSigAExpr a) (TypeSigAExpr b)
  | AMax a b => TypeSigUnion (TypeSigAExpr a) (TypeSigAExpr b)
  | AZless a b => TypeSigUnion (TypeSigAExpr a) (TypeSigAExpr b)
  end.


(* make sure 2 contexts are quivalent at locations from given [TypeSig].
   additionally makes typechecks both contexts wrt [TypeSig] *)
Definition context_equiv_at_TypeSig (tm:TypeSig) : relation evalContext
  := fun σ0 σ1 =>
       forall k t, TM.MapsTo k t tm ->
              contextEnsureType σ0 k t /\
              contextEnsureType σ1 k t /\
              context_lookup σ0 k = context_lookup σ1 k.

Definition TypeSigAExpr_UnCarrierA (f: DSHIBinCarrierA) : TypeSig := TypeSigAExpr f.
Definition TypeSigAExpr_IUnCarrierA (f: DSHIBinCarrierA) : TypeSig := TypeSigAExpr f.
Definition TypeSigAExpr_BinCarrierA (f: DSHBinCarrierA) : TypeSig := TypeSigAExpr f.
Definition TypeSigAExpr_IBinCarrierA (f: DSHIBinCarrierA) : TypeSig := TypeSigAExpr f.


Lemma context_equiv_at_TypeSig_widening {σ0 σ1 tm foo0 foo1}:
  context_equiv_at_TypeSig tm σ0 σ1 ->
  context_equiv_at_TypeSig tm (foo0 :: σ0) (foo1 :: σ1).
Proof.
  intros H.
Admitted.
