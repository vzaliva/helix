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
Require Import Flocq.Core.Zaux.

Definition evalContext (ft:FloatT): Type := list (@FSHVal ft).

Definition evalVexp {ft:FloatT} (st:evalContext ft) {n} (exp:@VExpr ft n): option (vector (FloatV ft) n) :=
  match exp in (VExpr n0) return (option (vector (FloatV ft) n0)) with
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

Fixpoint evalNexp {ft:FloatT} (st:evalContext ft) (e:@NExpr ft): option nat :=
  match e with
  | NVar i => v <- (nth_error st i) ;;
                 (match v with
                  | FSHnatVal x => Some x
                  | _ => None
                  end)
  | NConst c => Some c
  | NDiv a b => liftM2 Nat.div (evalNexp st a) (evalNexp st b)
  | NMod a b => liftM2 Nat.modulo (evalNexp st a) (evalNexp st b)
  | NPlus a b => liftM2 Nat.add (evalNexp st a) (evalNexp st b)
  | NMinus a b => liftM2 Nat.sub (evalNexp st a) (evalNexp st b)
  | NMult a b => liftM2 Nat.mul (evalNexp st a) (evalNexp st b)
  | NMin a b => liftM2 Nat.min (evalNexp st a) (evalNexp st b)
  | NMax a b => liftM2 Nat.max (evalNexp st a) (evalNexp st b)
  end.

Definition FT_lift_mbin (ft:FloatT) (m:mode)
           (f32: mode -> binary32 -> binary32 -> binary32)
           (f64: mode -> binary64 -> binary64 -> binary64)
           (a b: option (FloatV ft)): option (FloatV ft) :=
  match ft,a,b with
  | Float32, Some (Float32V a32), Some (Float32V b32) => Some (Float32V (f32 m a32 b32))
  | Float64, Some (Float64V a64), Some (Float64V b64) => Some (Float64V (f64 m a64 b64))
  | _, _, _ => None
  end.

Definition FT_lift_obin (ft:FloatT)
           (f32: binary32 -> binary32 -> option binary32)
           (f64: binary64 -> binary64 -> option binary64)
           (a b: option (FloatV ft)): option (FloatV ft) :=
  match ft,a,b with
  | Float32, Some (Float32V a32), Some (Float32V b32) =>
    c <- f32 a32 b32 ;; Some (Float32V c)
  | Float64, Some (Float64V a64), Some (Float64V b64) =>
    c <- f64 a64 b64 ;; Some (Float64V c)
  | _, _, _ => None
  end.

Definition FT_lift_un (ft:FloatT)
           (f32: binary32 -> binary32)
           (f64: binary64 -> binary64)
           (a: option (FloatV ft)): option (FloatV ft) :=
  match ft,a with
  | Float32, Some (Float32V a32) => Some (Float32V (f32 a32))
  | Float64, Some (Float64V a64) => Some (Float64V (f64 a64))
  | _, _ => None
  end.

Definition b32_min (a b: binary32): option binary32 :=
  match (Bcompare _ _ a b) with
  | None => None
  | Some Eq => Some a
  | Some Lt => Some a
  | Some Gt => Some b
  end.

Definition b64_min (a b: binary64): option binary64 :=
  match (Bcompare _ _ a b) with
  | None => None
  | Some Eq => Some a
  | Some Lt => Some a
  | Some Gt => Some b
  end.

Definition b32_max (a b: binary32): option binary32 :=
  match (Bcompare _ _ a b) with
  | None => None
  | Some Eq => Some a
  | Some Lt => Some b
  | Some Gt => Some a
  end.

Definition b64_max (a b: binary64): option binary64 :=
  match (Bcompare _ _ a b) with
  | None => None
  | Some Eq => Some a
  | Some Lt => Some b
  | Some Gt => Some a
  end.

Definition b32_zless (a b: binary32): option binary32 :=
  match (Bcompare _ _ a b) with
  | None => None
  | Some Eq => Some b
  | Some Lt => Some a
  | Some Gt => Some b
  end.

Definition b64_zless (a b: binary64): option binary64 :=
  match (Bcompare _ _ a b) with
  | None => None
  | Some Eq => Some b
  | Some Lt => Some a
  | Some Gt => Some b
  end.

Definition FT_Rounding:mode := mode_NE.

Fixpoint evalAexp {ft:FloatT} (st:evalContext ft) (e:@FExpr ft): option (FloatV ft) :=
  match e with
  | AVar i => v <- (nth_error st i) ;;
                 (match v with
                  | FSHFloatVal x => Some x
                  | _ => None
                  end)
  | AConst x => Some x
  | AAbs x =>  FT_lift_un ft b32_abs b64_abs (evalAexp st x)
  | APlus a b => FT_lift_mbin ft FT_Rounding b32_plus b64_plus (evalAexp st a) (evalAexp st b)
  | AMinus a b => FT_lift_mbin ft FT_Rounding b32_minus b64_minus (evalAexp st a) (evalAexp st b)
  | AMult a b => FT_lift_mbin ft FT_Rounding b32_mult b64_mult (evalAexp st a) (evalAexp st b)
  | AMin a b => FT_lift_obin ft b32_min b64_min (evalAexp st a) (evalAexp st b)
  | AMax a b => FT_lift_obin ft b32_max b64_max (evalAexp st a) (evalAexp st b)
  | @ANth _ n v i =>
    v' <- (evalVexp st v) ;;
       i' <- (evalNexp st i) ;;
       match Compare_dec.lt_dec i' n with
       | left ic => Some (Vnth v' ic)
       | in_right => None
       end
  | AZless a b => FT_lift_obin ft b32_zless b64_zless (evalAexp st a) (evalAexp st b)
  end.
