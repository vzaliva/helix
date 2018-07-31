(* Deep embedding of a subset of SigmaHCOL *)

Require Import Helix.HCOL.CarrierType.

Global Open Scope nat_scope.

Inductive DSHVar :=
| DSHnatVar (n:nat) :DSHVar
| DSHCarrierAVar (a:CarrierA): DSHVar
| DSHvecVar {n:nat} (v:avector n): DSHVar.

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

Definition DSHBinCarrierA := AExpr.
Definition DSHIBinCarrierA := AExpr.

Inductive DSHOperator: nat -> nat -> Type :=
| DSHeUnion {o: nat} {b: NExpr} (z: CarrierA): DSHOperator 1 o
| DSHeT {i: nat} {b:NExpr}: DSHOperator i 1
| DSHPointwise {i: nat} (f: DSHIBinCarrierA): DSHOperator i i
| DSHBinOp {o} (f: DSHIBinCarrierA): DSHOperator (o+o) o
| DSHInductor (n:NExpr) (f: DSHBinCarrierA) (initial: CarrierA): DSHOperator 1 1
| DSHIUnion {i o: nat} (n:nat) (dot: DSHBinCarrierA) (initial: CarrierA): DSHOperator i o -> DSHOperator i o
| DSHISumUnion {i o:nat} (n: nat): DSHOperator i o -> DSHOperator i o
| DSHIReduction {i o: nat} (n: nat) (dot: DSHBinCarrierA) (initial: CarrierA): DSHOperator i o -> DSHOperator i o
| DSHCompose {i1 o2 o3: nat}: DSHOperator o2 o3 -> DSHOperator i1 o2 -> DSHOperator i1 o3
| DSHHTSUMUnion {i o:nat} (dot: DSHBinCarrierA): DSHOperator i o -> DSHOperator i o -> @DSHOperator i o.

