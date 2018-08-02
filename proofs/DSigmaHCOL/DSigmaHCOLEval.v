Require Import Coq.Lists.List.
Require Import Coq.Arith.Peano_dec.
Require Import CoLoR.Util.Vector.VecUtil.
Require Import Helix.Util.Misc.
Require Import Helix.Util.VecUtil.
Require Import Helix.HCOL.CarrierType.
Require Import Helix.DSigmaHCOL.DSigmaHCOL.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.orders.minmax.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.misc.decision.

Global Open Scope nat_scope.

Definition evalContext:Type := list DSHVar.

Definition evalVexp (st:evalContext) {n} (exp:VExpr n): option (avector n) :=
  match exp in (VExpr n0) return (option (vector CarrierA n0)) with
  | @VVar n0 i =>
    match nth_error st i with
    | Some (@DSHvecVar n2 v) =>
      match eq_nat_dec n2 n0 as s0 return (_ ≡ s0 -> option (vector CarrierA n0))
      with
      | left E => fun _ => eq_rect n2 (fun n3 => option (vector CarrierA n3)) (Some v) n0 E
      | right _ => fun _ => None
      end eq_refl
    | _ => None
    end
  | @VConst _ t => Some t
  end.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Import MonadNotation.
Local Open Scope monad_scope.

Fixpoint evalNexp (st:evalContext) (e:NExpr): option nat :=
  match e with
  | NVar i => v <- (nth_error st i) ;;
               (match v with
                | DSHnatVar x => Some x
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

Fixpoint evalAexp (st:evalContext) (e:AExpr): option CarrierA :=
  match e with
  | AVar i => v <- (nth_error st i) ;;
               (match v with
                | DSHCarrierAVar x => Some x
                | _ => None
                end)
  | AConst x => Some x
  | AAbs x =>  liftM abs (evalAexp st x)
  | APlus a b => liftM2 plus (evalAexp st a) (evalAexp st b)
  | AMult a b => liftM2 mult (evalAexp st a) (evalAexp st b)
  | AMin a b => liftM2 min (evalAexp st a) (evalAexp st b)
  | AMax a b => liftM2 max (evalAexp st a) (evalAexp st b)
  | AMinus a b =>
    a' <- (evalAexp st a) ;;
       b' <- (evalAexp st b) ;;
       ret (plus a' (negate b'))
  | @ANth n v i =>
    v' <- (evalVexp st v) ;;
       i' <- (evalNexp st i) ;;
       match Compare_dec.lt_dec i' n with
       | left ic => Some (Vnth v' ic)
       | in_right => None
       end
  | AZless a b => liftM2 Zless (evalAexp st a) (evalAexp st b)
  end.

Require Import Coq.Arith.Compare_dec.
Require Import Helix.SigmaHCOL.SigmaHCOL.
Require Import Helix.SigmaHCOL.SVector.
Require Import Helix.SigmaHCOL.Rtheta.

Definition unLiftM_HOperator'
           {fm}
           {i o}
           (op: svector fm i -> svector fm o)
  : avector i -> avector o :=
      densify fm ∘ op ∘ sparsify fm.

Definition evalIUnCarrierA (Γ: evalContext) (f: DSHIUnCarrierA)
           (i:nat) (a:CarrierA): option CarrierA :=
  evalAexp (DSHnatVar i :: DSHCarrierAVar a :: Γ) f.

Definition evalDSHPointwise (Γ: evalContext) {i: nat} (f: DSHIUnCarrierA) (x:avector i): option (avector i) :=
  vsequence (Vbuild (fun j jd => evalIUnCarrierA Γ f j (Vnth x jd))).

Definition evalDSHOperator {i o} (Γ: evalContext) (op: DSHOperator i o) (x:avector i): option (avector o) :=
  match op with
  | @DSHeUnion o be z =>
    fun x => b <- evalNexp Γ be ;;
            match lt_dec b o as l return (_ ≡ l → option (vector CarrierA o))
            with
            | left bc => fun _ => Some (unLiftM_HOperator' (eUnion' Monoid_RthetaFlags bc z) x)
            | right _ => fun _ => None
            end eq_refl
  | @DSHeT i be =>
    fun x => b <- evalNexp Γ be ;;
            match lt_dec b i as l return (_ ≡ l → option (vector CarrierA 1))
            with
            | left bc => fun _ => Some (unLiftM_HOperator' (eT' Monoid_RthetaFlags bc) x)
            | right _ => fun _ => None
            end eq_refl
  | @DSHPointwise i f => fun x => evalDSHPointwise Γ f x
  | @DSHBinOp o f => fun _ => None
  | @DSHInductor n f initial => fun _ => None
  | @DSHIUnion i o n dot initial f => fun _ => None
  | @DSHISumUnion i o n f => fun _ => None
  | @DSHIReduction i o n dot initial f => fun _ => None
  | @DSHCompose i1 o2 o3 f g => fun _ => None
  | @DSHHTSUMUnion i o dot f g => fun _ => None
  end x.