(* Deep embedding of a subset of SigmaHCOL *)

Require Import Coq.Lists.List.

Require Import Helix.Util.Misc.
Require Import Helix.SigmaHCOL.Rtheta.
Require Import Helix.SigmaHCOL.SVector.

Require Import MathClasses.interfaces.canonical_names.

Import Monoid.

Global Open Scope nat_scope.

Inductive DSHBinCarrierA :=
| DSHBinPlus
| DSHBinMinus
| DSHBinMult
| DSHBinMin
| DSHBinMax.

(* Placeholder *)
Definition DSHNatExpr: Type := unit.

(* Placeholder *)
Inductive DSHIBinCarrierA: Type :=
| DSHIBinCarrierA_ign (f: DSHBinCarrierA): DSHIBinCarrierA
| DSHIBinCarrierA_vec {n:nat}
                      (f: DSHBinCarrierA)
                      (nf: DSHNatExpr)
                      (dsf_param: avector n).

Inductive DSHOperator: Monoid RthetaFlags -> nat -> nat -> Type :=
| DSHeUnion {fm}  {o: nat} {b: DSHNatExpr} (z: CarrierA): DSHOperator fm 1 o
| DSHeT {fm} {i: nat} {b:DSHNatExpr}: DSHOperator fm i 1
| DSHPointwise {fm} {i: nat} (f: DSHIBinCarrierA): DSHOperator fm i i
| DSHBinOp {o} {fm} (f: DSHIBinCarrierA): DSHOperator fm (o+o) o
| DSHInductor {fm} (n:DSHNatExpr) (f: DSHBinCarrierA) (initial: CarrierA): DSHOperator fm 1 1
| DSHIUnion {i o: nat} (n:nat) (dot: DSHBinCarrierA) (initial: CarrierA):
    DSHOperator Monoid_RthetaFlags i o -> DSHOperator Monoid_RthetaFlags i o
| DSHISumUnion {i o:nat} (n: nat):
    DSHOperator Monoid_RthetaFlags i o -> DSHOperator Monoid_RthetaFlags i o
| DSHIReduction {i o: nat} (n: nat) (dot: DSHBinCarrierA) (initial: CarrierA):
    DSHOperator Monoid_RthetaSafeFlags i o -> DSHOperator Monoid_RthetaSafeFlags i o
| DSHCompose {fm} {i1 o2 o3: nat}:
    DSHOperator fm o2 o3 -> DSHOperator fm i1 o2 -> DSHOperator fm i1 o3
| DSHSafeCast {i o:nat}:
    DSHOperator Monoid_RthetaSafeFlags i o -> DSHOperator Monoid_RthetaFlags i o
| DSHUnSafeCast {i o:nat}:
    DSHOperator Monoid_RthetaFlags i o -> DSHOperator Monoid_RthetaSafeFlags i o
| DSHHTSUMUnion {fm} {i o:nat} (dot: DSHBinCarrierA):
    DSHOperator fm i o -> DSHOperator fm i o -> @DSHOperator fm i o.

(* TODO: SHFamilyOperatorCompose *)

Inductive DSHVar :=
| DSHNat (n:nat) :DSHVar
| DSHCarrierA (a:CarrierA): DSHVar
| DSHVec {fm} {n:nat} (v:svector fm n): DSHVar.

Definition evalContext:Type := list DSHVar.

Definition evalDSHOperator {fm i o} (Γ: evalContext) (op: DSHOperator fm i o): svector fm i -> option (svector fm o).
Admitted.
