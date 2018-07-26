(* Deep embedding of a subset of SigmaHCOL *)

Require Import Coq.Lists.List.
Require Import Helix.Util.Misc.
Require Import Helix.HCOL.CarrierType.

Require Import MathClasses.interfaces.canonical_names.

Global Open Scope nat_scope.

Inductive DSHBinCarrierA :=
| DSHBinPlus
| DSHBinMinus
| DSHBinMult
| DSHBinMin
| DSHBinMax.

(* Placeholder *)
Definition DSHNatExpr: Type := unit.
Definition DSHAExpr: Type := unit.

(* Placeholder *)
Inductive DSHIBinCarrierA: Type :=
| DSHIBinCarrierA_ign (f: DSHBinCarrierA): DSHIBinCarrierA
| DSHIBinCarrierA_vec {n:nat}
                      (f: DSHBinCarrierA)
                      (nf: DSHNatExpr)
                      (dsf_param: avector n).

Inductive DSHOperator: nat -> nat -> Type :=
| DSHDummy {i o:nat} : DSHOperator i o (* for debugging *)
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

Inductive DSHVar :=
| DSHnatVar (n:nat) :DSHVar
| DSHCarrierAVar (a:CarrierA): DSHVar
| DSHvecVar {n:nat} (v:avector n): DSHVar.

Definition evalContext:Type := list DSHVar.

Definition evalDSHOperator {i o} (Γ: evalContext) (op: DSHOperator i o): avector i -> option (avector o).
Admitted.
