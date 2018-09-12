(* Deep-embedded SigmaHCOL with floating point arithmetics *)

Require Import Helix.Util.VecUtil.
Require Import Flocq.IEEE754.Binary Flocq.IEEE754.Bits Flocq.Core.Zaux.

Global Open Scope nat_scope.

(* Currently we support only IEE754 single and double-precision FP numbers *)
Inductive FloatT : Type :=
| Float32
| Float64.

Inductive FloatV : FloatT -> Type :=
| Float32V (b32:binary32) : FloatV Float32
| Float64V (b64:binary64) : FloatV Float64.

Inductive FSHVar : Type :=
| FSHnatVar (n:nat): FSHVar
| FSHCarrierAVar {ft:FloatT} (a:FloatV ft): FSHVar
| FSHvecVar {n:nat} {ft:FloatT} (v:vector (FloatV ft) n): FSHVar.

Inductive FExpr (ft:FloatT) : Type :=
| AVar  : nat -> FExpr ft
| AConst: FloatV ft -> FExpr ft
| ANth  : forall n, VExpr ft n -> NExpr ft -> FExpr ft
| AAbs  : FExpr ft -> FExpr ft
| APlus : FExpr ft -> FExpr ft -> FExpr ft
| AMinus: FExpr ft -> FExpr ft -> FExpr ft
| AMult : FExpr ft -> FExpr ft -> FExpr ft
| AMin  : FExpr ft -> FExpr ft -> FExpr ft
| AMax  : FExpr ft -> FExpr ft -> FExpr ft
| AZless: FExpr ft -> FExpr ft -> FExpr ft
with
(* Expressions which evaluate to `nat` *)
NExpr (ft:FloatT): Type :=
| NVar  : nat -> NExpr ft
| NConst: nat -> NExpr ft
| NDiv  : NExpr ft -> NExpr ft -> NExpr ft
| NMod  : NExpr ft -> NExpr ft -> NExpr ft
| NPlus : NExpr ft -> NExpr ft -> NExpr ft
| NMinus: NExpr ft -> NExpr ft -> NExpr ft
| NMult : NExpr ft -> NExpr ft -> NExpr ft
| NMin  : NExpr ft -> NExpr ft -> NExpr ft
| NMax  : NExpr ft -> NExpr ft -> NExpr ft
(* Expressions which evaluate to vector of floats *)
with VExpr (ft:FloatT): nat -> Type :=
     | VVar  {n:nat}: nat -> VExpr ft n
     | VConst {n:nat}: vector (FloatV ft) n -> VExpr ft n.

Definition FSHUnFloat := FExpr.
Definition FSHIUnFloat := FExpr.
Definition FSHBinFloat := FExpr.
Definition FSHIBinFloat := FExpr.

Inductive FSHOperator (ft:FloatT): nat -> nat -> Type :=
| FSHeUnion {o: nat} (b: NExpr ft) (z: (FloatV ft)): FSHOperator ft 1 o
| FSHeT {i: nat} (b:NExpr ft): FSHOperator ft i 1
| FSHPointwise {i: nat} (f: FSHIUnFloat ft): FSHOperator ft i i
| FSHBinOp {o} (f: FSHIBinFloat ft): FSHOperator ft (o+o) o
| FSHInductor (n:NExpr ft) (f: FSHBinFloat ft) (initial: FloatV ft): FSHOperator ft 1 1
| FSHIUnion {i o: nat} (n:nat) (dot: FSHBinFloat ft) (initial: FloatV ft): FSHOperator ft i o -> FSHOperator ft i o
| FSHIReduction {i o: nat} (n: nat) (dot: FSHBinFloat ft) (initial: FloatV ft): FSHOperator ft i o -> FSHOperator ft i o
| FSHCompose {i1 o2 o3: nat}: FSHOperator ft o2 o3 -> FSHOperator ft i1 o2 -> FSHOperator ft i1 o3
| FSHHTSUMUnion {i o:nat} (dot: FSHBinFloat ft): FSHOperator ft i o -> FSHOperator ft i o -> @FSHOperator ft i o.
