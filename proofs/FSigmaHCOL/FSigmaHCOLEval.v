Require Import Coq.Lists.List.
Require Import Coq.Arith.Peano_dec.
Require Import Helix.Util.Misc.
Require Import Helix.Util.VecUtil.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Structures.Monad.
Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.Tactics.HelixTactics.

Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

Global Open Scope nat_scope.

Definition evalContext (ft:FloatT): Type := list (FSHVal ft).

Definition evalVexp {ft:FloatT} (st:evalContext ft) {n} (exp:VExpr ft n): option (vector (FloatV ft) n) :=
  match exp in (VExpr _ n0) return (option (vector (FloatV ft) n0)) with
  | @VVar _ n0 i =>
    match nth_error st i with
    | Some (@FSHvecVal _ n2 v) =>
      match eq_nat_dec n2 n0 as s0 return (_ = s0 -> option (vector (FloatV ft) n0))
      with
      | left E => fun _ => eq_rect n2 (fun n3 => option (vector (FloatV ft) n3)) (Some v) n0 E
      | right _ => fun _ => None
      end eq_refl
    | _ => None
    end
  | @VConst _ _ t => Some t
  end.

Import MonadNotation.
Open Scope monad_scope.

Fixpoint evalNexp {ft:FloatT} (st:evalContext ft) (e:NExpr ft): option nat :=
  match e with
  | NVar _ i => v <- (nth_error st i) ;;
                 (match v with
                  | FSHnatVal _ x => Some x
                  | _ => None
                  end)
  | NConst _ c => Some c
  | NDiv _ a b => liftM2 Nat.div (evalNexp st a) (evalNexp st b)
  | NMod _ a b => liftM2 Nat.modulo (evalNexp st a) (evalNexp st b)
  | NPlus _ a b => liftM2 Nat.add (evalNexp st a) (evalNexp st b)
  | NMinus _ a b => liftM2 Nat.sub (evalNexp st a) (evalNexp st b)
  | NMult _ a b => liftM2 Nat.mul (evalNexp st a) (evalNexp st b)
  | NMin _ a b => liftM2 Nat.min (evalNexp st a) (evalNexp st b)
  | NMax _ a b => liftM2 Nat.max (evalNexp st a) (evalNexp st b)
  end.

Fixpoint evalAexp {ft:FloatT} (st:evalContext ft) (e:FExpr ft): option (FloatV ft) :=
  match e with
  | AVar _ i => v <- (nth_error st i) ;;
                 (match v with
                  | FSHFloatVal _ x => Some x
                  | _ => None
                  end)
  | AConst _ x => Some x
  | AAbs _ x =>  liftM (Babs _ _) (evalAexp st x)
  | APlus _ a b => liftM2 Bplus (evalAexp st a) (evalAexp st b)
  | AMult _ a b => liftM2 Bmult (evalAexp st a) (evalAexp st b)
  | AMin _ a b => liftM2 min (evalAexp st a) (evalAexp st b)
  | AMax _ a b => liftM2 max (evalAexp st a) (evalAexp st b)
  | AMinus _ a b =>
    a' <- (evalAexp st a) ;;
       b' <- (evalAexp st b) ;;
       ret (Bminus a' b')
  | @ANth _ n v i =>
    v' <- (evalVexp st v) ;;
       i' <- (evalNexp st i) ;;
       match Compare_dec.lt_dec i' n with
       | left ic => Some (Vnth v' ic)
       | in_right => None
       end
  | AZless _ a b => liftM2 (Bcompare) (evalAexp st a) (evalAexp st b)
  end.
