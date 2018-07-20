(* Deep embedding of a subset of SigmaHCOL *)

Require Import Coq.Lists.List.

Require Import Helix.Util.Misc.
Require Import Helix.Util.FinNat.
Require Import Helix.SigmaHCOL.Rtheta.
Require Import Helix.SigmaHCOL.SVector.

Require Import MathClasses.interfaces.canonical_names.

Import Monoid.

Global Open Scope nat_scope.

Inductive DSHBinaryFunction :=
| DSHBinPlus
| DSHBinMinus
| DSHBinMult
| DSHBinMin
| DSHBinMax.

Definition DSHNatFunction: Type := list nat.

Record DSHIBinCarrierA (n:nat): Type
  := mkDSHIBinCarrierA {
         dsf_binf: DSHBinaryFunction ;
         dsf_indf: DSHNatFunction ;
         dsf_param: avector n
       }.

Inductive DSHOperator: Monoid RthetaFlags -> nat -> nat -> Type :=
| DSHeUnion {o: nat} {b: FinNat o} {fm} (z: CarrierA): DSHOperator fm 1 o
| DSHeT {i: nat} {b:FinNat i} {fm}: DSHOperator fm i 1
| DSHPointwise {pn n: nat} {fm} (f: DSHIBinCarrierA pn): DSHOperator fm n n
| DSHBinOp {pn} {o} {fm} (f: DSHIBinCarrierA pn): DSHOperator fm (o+o) o
| DSHIUnion {i o n: nat} (dot: DSHBinaryFunction) (initial: CarrierA):
    DSHOperator Monoid_RthetaFlags i o -> DSHOperator Monoid_RthetaFlags i o
| DSHISumUnion {i o :nat} (n: nat):
    DSHOperator Monoid_RthetaFlags i o -> DSHOperator Monoid_RthetaFlags i o
| DSHIReduction {i o n: nat} (dot: DSHBinaryFunction) (initial: CarrierA):
    DSHOperator Monoid_RthetaSafeFlags i o -> DSHOperator Monoid_RthetaSafeFlags i o
| DSHCompose {i1 o2 o3: nat} {fm}:
    DSHOperator fm o2 o3 -> DSHOperator fm i1 o2 -> DSHOperator fm i1 o3
| DSHSafeCast {i o:nat}:
    DSHOperator Monoid_RthetaSafeFlags i o -> DSHOperator Monoid_RthetaFlags i o
| DSHUnSafeCast {i o:nat}:
    DSHOperator Monoid_RthetaFlags i o -> DSHOperator Monoid_RthetaSafeFlags i o
| DSHHTSUMUnion {i o:nat} {fm} (dot: DSHBinaryFunction):
    DSHOperator fm i o -> DSHOperator fm i o -> @DSHOperator fm i o.


(* TODO: SHFamilyOperatorCompose *)