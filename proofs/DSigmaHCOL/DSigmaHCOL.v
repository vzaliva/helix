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

Definition DSHUnCarrierA := AExpr.
Definition DSHIUnCarrierA := AExpr.
Definition DSHBinCarrierA := AExpr.
Definition DSHIBinCarrierA := AExpr.

Inductive DSHOperator: nat -> nat -> Type :=
| DSHeUnion {o: nat} (b: NExpr) (z: CarrierA): DSHOperator 1 o
| DSHeT {i: nat} (b:NExpr): DSHOperator i 1
| DSHPointwise {i: nat} (f: DSHIUnCarrierA): DSHOperator i i
| DSHBinOp {o} (f: DSHIBinCarrierA): DSHOperator (o+o) o
| DSHInductor (n:NExpr) (f: DSHBinCarrierA) (initial: CarrierA): DSHOperator 1 1
| DSHIUnion {i o: nat} (n:nat) (dot: DSHBinCarrierA) (initial: CarrierA): DSHOperator i o -> DSHOperator i o
| DSHISumUnion {i o:nat} (n: nat): DSHOperator i o -> DSHOperator i o
| DSHIReduction {i o: nat} (n: nat) (dot: DSHBinCarrierA) (initial: CarrierA): DSHOperator i o -> DSHOperator i o
| DSHCompose {i1 o2 o3: nat}: DSHOperator o2 o3 -> DSHOperator i1 o2 -> DSHOperator i1 o3
| DSHHTSUMUnion {i o:nat} (dot: DSHBinCarrierA): DSHOperator i o -> DSHOperator i o -> @DSHOperator i o.

(* Some Setoid stuff below *)

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.implementations.peano_naturals.
Require Import Helix.Util.VecSetoid.
Require Import Helix.Tactics.HelixTactics.

Inductive DSHVar_equiv: DSHVar -> DSHVar -> Prop :=
| DSHnatVar_equiv {n0 n1:nat}: n0=n1 -> DSHVar_equiv (DSHnatVar n0) (DSHnatVar n1)
| DSHCarrierAVar_equiv {a b: CarrierA}: a=b -> DSHVar_equiv (DSHCarrierAVar a) (DSHCarrierAVar b)
| DSHvecVar_equiv {n:nat} {v0 v1: avector n}: v0=v1 -> DSHVar_equiv (DSHvecVar v0) (DSHvecVar v1).

Global Instance DSHVar_Equivalence:
  Equivalence DSHVar_equiv.
Proof.
  split.
  -
    intros x.
    destruct x; constructor; reflexivity.
  -
    intros x y E.
    inversion E; constructor; symmetry;  apply H.
  -
    intros x y z Exy Eyz.
    inversion Exy; inversion Eyz; subst y; try inversion H3.
    +
      constructor.
      rewrite H.
      rewrite <- H5.
      apply H2.
    +
      constructor.
      rewrite <- H2.
      rewrite H5.
      apply H.
    +
      subst.
      constructor.
      inv_exitstT.
      rewrite H.
      rewrite <- H6.
      apply H2.
Qed.

Global Instance DSHVar_Equiv: Equiv DSHVar := DSHVar_equiv.

Inductive NExpr_equiv: NExpr -> NExpr -> Prop :=
| NVar_equiv  {n1 n2}: n1=n2 -> NExpr_equiv (NVar n1)  (NVar n2)
| NConst_equiv {a b}: a=b -> NExpr_equiv (NConst a) (NConst b)
| NDiv_equiv  {a a' b b'}: NExpr_equiv a a' -> NExpr_equiv b b' -> NExpr_equiv (NDiv a b)   (NDiv a' b')
| NMod_equiv  {a a' b b'}: NExpr_equiv a a' -> NExpr_equiv b b' -> NExpr_equiv (NMod a b)   (NMod a' b')
| NPlus_equiv {a a' b b'}: NExpr_equiv a a' -> NExpr_equiv b b' -> NExpr_equiv (NPlus a b)  (NPlus a' b')
| NMinus_equiv {a a' b b'}: NExpr_equiv a a' -> NExpr_equiv b b' -> NExpr_equiv (NMinus a b) (NMinus a' b')
| NMult_equiv {a a' b b'}: NExpr_equiv a a' -> NExpr_equiv b b' -> NExpr_equiv (NMult a b)  (NMult a' b')
| NMin_equiv  {a a' b b'}: NExpr_equiv a a' -> NExpr_equiv b b' -> NExpr_equiv (NMin a b)   (NMin a' b')
| NMax_equiv  {a a' b b'}: NExpr_equiv a a' -> NExpr_equiv b b' -> NExpr_equiv (NMax a b)   (NMax a' b').

Global Instance NExpr_Equiv: Equiv NExpr  := NExpr_equiv.

Global Instance NExpr_Equivalence:
  Equivalence NExpr_equiv.
Proof.
  split.
  -
    intros x.
    induction x; constructor; auto.
  -
    intros x y E.
    induction E; constructor; try symmetry; assumption.
  -

    intros x y z.
    dependent induction x;
      dependent induction y;
      dependent induction z; intros Exy Eyz; try inversion Exy; try inversion Eyz; subst.
    + constructor; auto.
    + constructor; auto.
    + constructor; [apply IHx1 with (y:=y1); auto | apply IHx2 with (y:=y2); auto].
    + constructor; [apply IHx1 with (y:=y1); auto | apply IHx2 with (y:=y2); auto].
    + constructor; [apply IHx1 with (y:=y1); auto | apply IHx2 with (y:=y2); auto].
    + constructor; [apply IHx1 with (y:=y1); auto | apply IHx2 with (y:=y2); auto].
    + constructor; [apply IHx1 with (y:=y1); auto | apply IHx2 with (y:=y2); auto].
    + constructor; [apply IHx1 with (y:=y1); auto | apply IHx2 with (y:=y2); auto].
    + constructor; [apply IHx1 with (y:=y1); auto | apply IHx2 with (y:=y2); auto].
Qed.


Inductive VExpr_equiv {n:nat}: VExpr n -> VExpr n -> Prop :=
| VVar_equiv {n0 n1}: n0=n1 -> VExpr_equiv (VVar n0) (VVar n1)
| VConst_equiv {a b: avector n}: a=b -> VExpr_equiv (VConst a) (VConst b).

Global Instance VExpr_Equiv {n}: Equiv (VExpr n) := VExpr_equiv.

Global Instance VExpr_Equivalence {n}:
  Equivalence (@VExpr_Equiv n).
Proof.
  split.
  -
    intros x.
    induction x; constructor; auto.
  -
    intros x y E.
    induction E; constructor; try symmetry; assumption.
  -
    intros x y z Exy Eyz.
    induction Exy; inversion Eyz; subst;
      constructor; auto.

    inv_exitstT.
    subst.
    auto.
Qed.

Inductive AExpr_equiv: AExpr -> AExpr -> Prop :=
| AVar_equiv  {n0 n1}: n0=n1 -> AExpr_equiv (AVar n0) (AVar n1)
| AConst_equiv {a b}: a=b -> AExpr_equiv (AConst a) (AConst b)
| ANth_equiv {n} {v1 v2:VExpr n} {n1 n2:NExpr} :
    NExpr_equiv n1 n2 ->
    VExpr_equiv v1 v2 ->
    AExpr_equiv (ANth n v1 n1)  (ANth n v2 n2)
| AAbs_equiv  {a b}: AExpr_equiv a b -> AExpr_equiv (AAbs a)  (AAbs b)
| APlus_equiv {a a' b b'}: AExpr_equiv a a' -> AExpr_equiv b b' -> AExpr_equiv (APlus a b) (APlus a' b')
| AMinus_equiv{a a' b b'}: AExpr_equiv a a' -> AExpr_equiv b b' -> AExpr_equiv (AMinus a b) (AMinus a' b')
| AMult_equiv {a a' b b'}: AExpr_equiv a a' -> AExpr_equiv b b' -> AExpr_equiv (AMult a b) ( AMult a' b')
| AMin_equiv  {a a' b b'}: AExpr_equiv a a' -> AExpr_equiv b b' -> AExpr_equiv (AMin a b) (  AMin a' b')
| AMax_equiv  {a a' b b'}: AExpr_equiv a a' -> AExpr_equiv b b' -> AExpr_equiv (AMax a b) (  AMax a' b')
| AZless_equiv {a a' b b'}: AExpr_equiv a a' -> AExpr_equiv b b' -> AExpr_equiv (AZless a b) (AZless a' b').

Global Instance AExpr_Equiv: Equiv AExpr := AExpr_equiv.

Global Instance AExpr_Equivalence:
  Equivalence AExpr_equiv.
Proof.
  split.
  -
    intros x.
    induction x; constructor; auto; reflexivity.
  -
    intros x y.
    dependent induction x; dependent induction y; intros E; try inversion E; subst.
    + constructor; auto.
    + constructor; auto.
    + constructor.
      * symmetry; auto.
      *
        inversion E.
        inv_exitstT.
        subst.
        symmetry.
        auto.
    + constructor; apply IHx; auto.
    + constructor;[ apply IHx1; auto | apply IHx2; auto].
    + constructor;[ apply IHx1; auto | apply IHx2; auto].
    + constructor;[ apply IHx1; auto | apply IHx2; auto].
    + constructor;[ apply IHx1; auto | apply IHx2; auto].
    + constructor;[ apply IHx1; auto | apply IHx2; auto].
    + constructor;[ apply IHx1; auto | apply IHx2; auto].
  -
    intros x y z.
    dependent induction x;
      dependent induction y;
      dependent induction z; intros Exy Eyz; try inversion Exy; try inversion Eyz; subst.
    + constructor; auto.
    + constructor; auto.
    +
      inversion Exy. inversion Eyz.
      inv_exitstT; subst.
      constructor.
      apply transitivity with (y:=n2); auto.
      eapply transitivity with (y:=v0); auto.
    + constructor; apply IHx with (y:=y); auto.
    + constructor; [apply IHx1 with (y:=y1); auto | apply IHx2 with (y:=y2); auto].
    + constructor; [apply IHx1 with (y:=y1); auto | apply IHx2 with (y:=y2); auto].
    + constructor; [apply IHx1 with (y:=y1); auto | apply IHx2 with (y:=y2); auto].
    + constructor; [apply IHx1 with (y:=y1); auto | apply IHx2 with (y:=y2); auto].
    + constructor; [apply IHx1 with (y:=y1); auto | apply IHx2 with (y:=y2); auto].
    + constructor; [apply IHx1 with (y:=y1); auto | apply IHx2 with (y:=y2); auto].
Qed.