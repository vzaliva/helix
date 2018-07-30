(* Deep embedding of a subset of SigmaHCOL *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Peano_dec.
Require Import CoLoR.Util.Vector.VecUtil.
Require Import Helix.Util.Misc.
Require Import Helix.HCOL.CarrierType.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.orders.minmax.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.misc.decision.

Global Open Scope nat_scope.

Inductive DSHVar :=
| DSHnatVar (n:nat) :DSHVar
| DSHCarrierAVar (a:CarrierA): DSHVar
| DSHvecVar {n:nat} (v:avector n): DSHVar.

Definition evalContext:Type := list DSHVar.

(* Expressions which evaluate to `CarrierA` *)
Inductive AExpr : Type :=
| AVar  : nat -> AExpr
| AConst: CarrierA -> AExpr
| ANth  : forall n, VExpr n -> NExpr -> AExpr
| AAbs  : AExpr -> AExpr
| APlus : AExpr -> AExpr -> AExpr
| AMinus: AExpr -> AExpr -> AExpr
| AMult : AExpr -> AExpr -> AExpr
| AMin  : AExpr -> AExpr -> AExpr
| AMax  : AExpr -> AExpr -> AExpr
| AZless: AExpr -> AExpr -> AExpr
with
(* Expressions which evaluate to `nat` *)
NExpr: Type :=
| NVar  : nat -> NExpr
| NConst: nat -> NExpr
| NDiv  : NExpr -> NExpr -> NExpr
| NMod  : NExpr -> NExpr -> NExpr
| NPlus : NExpr -> NExpr -> NExpr
| NMinus: NExpr -> NExpr -> NExpr
| NMult : NExpr -> NExpr -> NExpr
| NMin  : NExpr -> NExpr -> NExpr
| NMax  : NExpr -> NExpr -> NExpr
(* Expressions which evaluate to `avector n` *)
with VExpr: nat -> Type :=
     | VVar  {n:nat}: nat -> VExpr n
     | VConst {n:nat}: avector n -> VExpr n.


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

(* Placeholder *)
Definition DSHBinCarrierA := unit.
Definition DSHNatExpr: Type := unit.
Definition DSHAExpr: Type := unit.

(* Placeholder *)
Definition DSHIBinCarrierA := unit.

Inductive DSHOperator: nat -> nat -> Type :=
| DSHeUnion {o: nat} {b: DSHNatExpr} (z: CarrierA): DSHOperator 1 o
| DSHeT {i: nat} {b:DSHNatExpr}: DSHOperator i 1
| DSHPointwise {i: nat} (f: DSHIBinCarrierA): DSHOperator i i
| DSHBinOp {o} (f: DSHIBinCarrierA): DSHOperator (o+o) o
| DSHInductor (n:DSHNatExpr) (f: DSHBinCarrierA) (initial: CarrierA): DSHOperator 1 1
| DSHIUnion {i o: nat} (n:nat) (dot: DSHBinCarrierA) (initial: CarrierA): DSHOperator i o -> DSHOperator i o
| DSHISumUnion {i o:nat} (n: nat): DSHOperator i o -> DSHOperator i o
| DSHIReduction {i o: nat} (n: nat) (dot: DSHBinCarrierA) (initial: CarrierA): DSHOperator i o -> DSHOperator i o
| DSHCompose {i1 o2 o3: nat}: DSHOperator o2 o3 -> DSHOperator i1 o2 -> DSHOperator i1 o3
| DSHHTSUMUnion {i o:nat} (dot: DSHBinCarrierA): DSHOperator i o -> DSHOperator i o -> @DSHOperator i o.

(* TODO: SHFamilyOperatorCompose *)

Definition evalDSHOperator {i o} (Γ: evalContext) (op: DSHOperator i o): avector i -> option (avector o).
Admitted.
