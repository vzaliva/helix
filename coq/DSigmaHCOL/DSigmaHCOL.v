(* Deep embedding of a subset of SigmaHCOL *)

Require Import Helix.HCOL.CarrierType.
Require Import Helix.SigmaHCOL.Memory.
Require Import Helix.SigmaHCOL.MemSetoid.

Global Open Scope nat_scope.

(* Variable on stack (De-Brujn index) *)
Definition var_id := nat.

Inductive DSHVal :=
| DSHnatVal (n:nat): DSHVal
| DSHCarrierAVal (a:CarrierA): DSHVal
| DSHvecVal {n:nat} (v:avector n): DSHVal
| DSHmemVal (m:mem_block): DSHVal.

(* Expressions which evaluate to `CarrierA` *)
Inductive AExpr : Type :=
| AVar  : var_id -> AExpr
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
| NVar  : var_id -> NExpr
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
     | VVar  {n:var_id}: nat -> VExpr n
     | VConst {n:nat}: avector n -> VExpr n.

Definition DSHUnCarrierA := AExpr.
Definition DSHIUnCarrierA := AExpr.
Definition DSHBinCarrierA := AExpr.
Definition DSHIBinCarrierA := AExpr.

Definition memory := NatMap mem_block.

(* Memory block address *)
Definition mem_block_id := nat.
(* Memory variable along with offset *)
Definition MemVarRef: Set := (mem_block_id * NExpr).

Inductive DSHOperator :=
| DSHAssign (src dst: MemVarRef) (* formerly [eT] and [eUnion] *)
| DSHIMap (n: nat) (x_i y_i: mem_block_id) (f: DSHIUnCarrierA) (* formerly [Pointwise] *)
| DSHBinOp (n: nat) (x y: mem_block_id) (f: DSHIBinCarrierA) (* formerly [BinOp] *)
| DSHMemMap2 (n: nat) (x0_i x1_i y_i: mem_block_id) (f: DSHBinCarrierA) (* No direct correspondance in SHCOL *)
| DSHPower (n:NExpr) (src dst: MemVarRef) (f: DSHBinCarrierA) (initial: CarrierA) (* formely [Inductor] *)
| DSHLoop (n:nat) (body: DSHOperator) (* Formerly [IUnion] *)
| DSHAlloc (size:nat) (y_i: mem_block_id) (* allocates new uninitialized memory block and puts at specified address. Reading from unitialized offsets is not allowed. *)
| DSHMemInit (size:nat) (y_i: mem_block_id) (value: CarrierA) (* Initialize memory block indices [0-size] with given value *)
| DSHMemCopy (size:nat) (x_i y_i: mem_block_id)(* copy memory blocks. Overwrites output block values, if present *)
| DSHSeq (f g: DSHOperator) (* execute [g] after [f] *)
.

(* Some Setoid stuff below *)

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.implementations.peano_naturals.
Require Import Helix.Util.VecSetoid.
Require Import Helix.Tactics.HelixTactics.

Inductive DSHVal_equiv: DSHVal -> DSHVal -> Prop :=
| DSHnatVal_equiv {n0 n1:nat}: n0=n1 -> DSHVal_equiv (DSHnatVal n0) (DSHnatVal n1)
| DSHCarrierAVal_equiv {a b: CarrierA}: a=b -> DSHVal_equiv (DSHCarrierAVal a) (DSHCarrierAVal b)
| DSHvecVal_equiv {n:nat} {v0 v1: avector n}: v0=v1 -> DSHVal_equiv (DSHvecVal v0) (DSHvecVal v1)
| DSHmemVal_equiv {m0 m1: mem_block}: m0=m1 -> DSHVal_equiv (DSHmemVal m0) (DSHmemVal m1).

Global Instance DSHVar_Equivalence:
  Equivalence DSHVal_equiv.
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
    +
      subst.
      constructor.
      rewrite H.
      apply H2.
Qed.

Global Instance DSHVar_Equiv: Equiv DSHVal := DSHVal_equiv.

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


Module DSHNotation.

  Notation "A ; B" := (DSHSeq A B) (at level 99, right associativity, only printing).
  Notation "A * B" := (AMult A B) (only printing).
  Notation "A - B" := (AMinus A B) (only printing).
  Notation "A + B" := (APlus A B) (only printing).
  Notation "A * B" := (NMult A B) (only printing).
  Notation "A - B" := (NMinus A B) (only printing).
  Notation "A + B" := (NPlus A B) (only printing).
  Notation "A %'N'" := (NConst A) (at level 99, only printing,
                                   format "A %'N'").

End DSHNotation.
