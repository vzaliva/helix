(* Deep-embedded SigmaHCOL with floating point arithmetics *)

Require Import Helix.Util.VecUtil.
Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

Global Open Scope nat_scope.

(* Currently we support only IEE754 single and double-precision FP numbers *)
Inductive FloatT : Type :=
| Float32
| Float64.

Inductive FloatV : FloatT -> Type :=
| Float32V (b32:binary32) : FloatV Float32
| Float64V (b64:binary64) : FloatV Float64.

Inductive FSHVal {ft:FloatT}: Type :=
| FSHnatVal (n:nat): FSHVal 
| FSHFloatVal (a:FloatV ft): FSHVal 
| FSHvecVal {n:nat} (v:vector (FloatV ft) n): FSHVal.

Inductive FExpr {ft:FloatT} : Type :=
| AVar  : nat -> FExpr
| AConst: FloatV ft -> FExpr
| ANth  : forall n, VExpr n -> NExpr -> FExpr
| AAbs  : FExpr -> FExpr
| APlus : FExpr -> FExpr  -> FExpr
| AMinus: FExpr -> FExpr  -> FExpr
| AMult : FExpr -> FExpr  -> FExpr
| AMin  : FExpr -> FExpr  -> FExpr
| AMax  : FExpr -> FExpr  -> FExpr
| AZless: FExpr -> FExpr  -> FExpr
with
(* Expressions which evaluate to `nat` *)
NExpr {ft:FloatT}: Type :=
| NVar  : nat -> NExpr
| NConst: nat -> NExpr
| NDiv  : NExpr -> NExpr -> NExpr
| NMod  : NExpr -> NExpr -> NExpr
| NPlus : NExpr -> NExpr -> NExpr
| NMinus: NExpr -> NExpr -> NExpr
| NMult : NExpr -> NExpr -> NExpr
| NMin  : NExpr -> NExpr -> NExpr
| NMax  : NExpr -> NExpr -> NExpr
(* Expressions which evaluate to vector of floats *)
with VExpr {ft:FloatT}: nat -> Type :=
     | VVar  {n:nat}: nat -> VExpr n
     | VConst {n:nat}: vector (FloatV ft) n -> VExpr n.

Definition FSHUnFloat   {ft:FloatT} := @FExpr ft.
Definition FSHIUnFloat  {ft:FloatT} := @FExpr ft.
Definition FSHBinFloat  {ft:FloatT} := @FExpr ft.
Definition FSHIBinFloat {ft:FloatT} := @FExpr ft.

Inductive FSHOperator {ft:FloatT}: nat -> nat -> Type :=
| FSHeUnion {o: nat} (b: @NExpr ft) (z: (FloatV ft)): FSHOperator 1 o
| FSHeT {i: nat} (b:@NExpr ft): FSHOperator i 1
| FSHPointwise {i: nat} (f: @FSHIUnFloat ft): FSHOperator i i
| FSHBinOp {o} (f: @FSHIBinFloat ft): FSHOperator (o+o) o
| FSHInductor (n:@NExpr ft) (f: @FSHBinFloat ft) (initial: FloatV ft): FSHOperator 1 1
| FSHIUnion {i o: nat} (n:nat) (dot: @FSHBinFloat ft) (initial: FloatV ft): FSHOperator i o -> FSHOperator i o
| FSHIReduction {i o: nat} (n: nat) (dot: @FSHBinFloat ft) (initial: FloatV ft): FSHOperator i o -> FSHOperator i o
| FSHCompose {i1 o2 o3: nat}: FSHOperator o2 o3 -> FSHOperator i1 o2 -> FSHOperator i1 o3
| FSHHTSUMUnion {i o:nat} (dot: @FSHBinFloat ft): FSHOperator i o -> FSHOperator i o -> @FSHOperator ft i o.

(* Used in code gen and possibly in reification *)
Inductive FSHValType {ft:FloatT}: Type :=
| FSHnatValType: FSHValType
| FSHFloatValType: FSHValType
| FSHvecValType {n:nat}: FSHValType.
