(* Deep embedding of a subset of SigmaHCOL *)

Require Import Helix.HCOL.CarrierType.
Require Import Helix.MSigmaHCOL.Memory.
Require Import Helix.MSigmaHCOL.MemSetoid.

Global Open Scope nat_scope.

(* Variable on stack (De-Brujn index) *)
Definition var_id := nat.

Inductive DSHType :=
| DSHnat : DSHType
| DSHCarrierA : DSHType
| DSHMemBlock : DSHType
| DSHPtr : DSHType.

Inductive DSHVal :=
| DSHnatVal (n:nat): DSHVal
| DSHCarrierAVal (a:CarrierA): DSHVal
| DSHMemVal (m:mem_block): DSHVal
| DSHPtrVal (a:mem_block_id): DSHVal.

Inductive DSHValType: DSHVal -> DSHType -> Prop :=
| DSHnatVal_type (n:nat): DSHValType (DSHnatVal n) DSHnat
| DSHCarrierAVal_type (a:CarrierA): DSHValType (DSHCarrierAVal a) DSHCarrierA
| DSHMemVal_type (m:mem_block): DSHValType (DSHMemVal m)  DSHMemBlock
| DSHMemBlockId_type (a:mem_block_id): DSHValType (DSHPtrVal a) DSHPtr.

(* Expressions which evaluate to `nat` *)
Inductive NExpr : Type :=
| NVar  : var_id -> NExpr
| NConst: nat -> NExpr
| NDiv  : NExpr -> NExpr -> NExpr
| NMod  : NExpr -> NExpr -> NExpr
| NPlus : NExpr -> NExpr -> NExpr
| NMinus: NExpr -> NExpr -> NExpr
| NMult : NExpr -> NExpr -> NExpr
| NMin  : NExpr -> NExpr -> NExpr
| NMax  : NExpr -> NExpr -> NExpr.

(* Expressions which evaluate to `mem_block` *)
Inductive MExpr: Type :=
| MVar:  var_id -> MExpr
| MConst: mem_block -> MExpr.

Inductive PExpr: Type :=
| PVar:  var_id -> PExpr
| PConst: mem_block_id -> PExpr.

(* Expressions which evaluate to `CarrierA` *)
Inductive AExpr : Type :=
| AVar  : var_id -> AExpr
| AConst: CarrierA -> AExpr
| ANth  : MExpr -> NExpr -> AExpr
| AAbs  : AExpr -> AExpr
| APlus : AExpr -> AExpr -> AExpr
| AMinus: AExpr -> AExpr -> AExpr
| AMult : AExpr -> AExpr -> AExpr
| AMin  : AExpr -> AExpr -> AExpr
| AMax  : AExpr -> AExpr -> AExpr
| AZless: AExpr -> AExpr -> AExpr.


Definition DSHUnCarrierA := AExpr.
Definition DSHIUnCarrierA := AExpr.
Definition DSHBinCarrierA := AExpr.
Definition DSHIBinCarrierA := AExpr.

(* Memory variable along with offset *)
Definition MemVarRef: Set := (PExpr * NExpr).

Inductive DSHOperator :=
| DSHAssign (src dst: MemVarRef) (* formerly [eT] and [eUnion] *)
| DSHIMap (n: nat) (x_p y_p: PExpr) (f: DSHIUnCarrierA) (* formerly [Pointwise] *)
| DSHBinOp (n: nat) (x_p y_p: PExpr) (f: DSHIBinCarrierA) (* formerly [BinOp] *)
| DSHMemMap2 (n: nat) (x0_p x1_p y_p: PExpr) (f: DSHBinCarrierA) (* No direct correspondance in SHCOL *)
| DSHPower (n:NExpr) (src dst: MemVarRef) (f: DSHBinCarrierA) (initial: CarrierA) (* formely [Inductor] *)
| DSHLoop (n:nat) (body: DSHOperator) (* Formerly [IUnion] *)
| DSHAlloc (size:nat) (body: DSHOperator) (* allocates new uninitialized memory block and puts pointer to it on stack. The new block will be visible in the scope of [body] *)
| DSHMemInit (size:nat) (y_p: PExpr) (value: CarrierA) (* Initialize memory block indices [0-size] with given value *)
| DSHMemCopy (size:nat) (x_p y_p: PExpr)(* copy memory blocks. Overwrites output block values, if present *)
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
| DSHMemVal_equiv {m0 m1: mem_block}: m0=m1 -> DSHVal_equiv (DSHMemVal m0) (DSHMemVal m1)
| DSHPtr_equiv {p0 p1: mem_block_id}: p0=p1 -> DSHVal_equiv (DSHPtrVal p0) (DSHPtrVal p1).

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
      rewrite H.
      apply H2.
    +
      subst.
      constructor.
      auto.
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


Inductive MExpr_equiv : MExpr -> MExpr -> Prop :=
| MVar_equiv {n0 n1}: n0=n1 -> MExpr_equiv (MVar n0) (MVar n1)
| MConst_equiv {a b: mem_block}: a=b -> MExpr_equiv (MConst a) (MConst b).

Global Instance MExpr_Equiv: Equiv MExpr := MExpr_equiv.

Global Instance MExpr_Equivalence:
  Equivalence MExpr_equiv.
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
Qed.

Inductive PExpr_equiv : PExpr -> PExpr -> Prop :=
| PVar_equiv {n0 n1}: n0=n1 -> PExpr_equiv (PVar n0) (PVar n1)
| PConst_equiv {a b: mem_block_id}: a=b -> PExpr_equiv (PConst a) (PConst b).

Global Instance PExpr_Equiv: Equiv PExpr := PExpr_equiv.

Global Instance PExpr_Equivalence:
  Equivalence PExpr_equiv.
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
Qed.

Inductive AExpr_equiv: AExpr -> AExpr -> Prop :=
| AVar_equiv  {n0 n1}: n0=n1 -> AExpr_equiv (AVar n0) (AVar n1)
| AConst_equiv {a b}: a=b -> AExpr_equiv (AConst a) (AConst b)
| ANth_equiv {v1 v2:MExpr} {n1 n2:NExpr} :
    NExpr_equiv n1 n2 ->
    MExpr_equiv v1 v2 ->
    AExpr_equiv (ANth v1 n1)  (ANth v2 n2)
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
      apply transitivity with (y:=n0); auto.
      eapply transitivity with (y:=m0); auto.
    + constructor; apply IHx with (y:=y); auto.
    + constructor; [apply IHx1 with (y:=y1); auto | apply IHx2 with (y:=y2); auto].
    + constructor; [apply IHx1 with (y:=y1); auto | apply IHx2 with (y:=y2); auto].
    + constructor; [apply IHx1 with (y:=y1); auto | apply IHx2 with (y:=y2); auto].
    + constructor; [apply IHx1 with (y:=y1); auto | apply IHx2 with (y:=y2); auto].
    + constructor; [apply IHx1 with (y:=y1); auto | apply IHx2 with (y:=y2); auto].
    + constructor; [apply IHx1 with (y:=y1); auto | apply IHx2 with (y:=y2); auto].
Qed.

Definition incrPVar (p: PExpr) : PExpr :=
  match p with
  | PVar var_id => PVar (S var_id)
  | _ => p
  end.

Definition incrMVar (p: MExpr) : MExpr :=
  match p with
  | MVar var_id => MVar (S var_id)
  | _ => p
  end.

Fixpoint incrNVar (p: NExpr) : NExpr :=
  match p with
  | NVar var_id => NVar (S var_id)
  | NConst _ => p
  | NDiv  a b => NDiv (incrNVar a) (incrNVar b)
  | NMod  a b => NMod (incrNVar a) (incrNVar b)
  | NPlus a b => NPlus (incrNVar a) (incrNVar b)
  | NMinus a b => NMinus (incrNVar a) (incrNVar b)
  | NMult a b => NMult (incrNVar a) (incrNVar b)
  | NMin  a b => NMin (incrNVar a) (incrNVar b)
  | NMax  a b => NMax (incrNVar a) (incrNVar b)
  end.

Fixpoint incrAVar (p: AExpr) : AExpr :=
  match p with
  | AVar var_id => AVar (S var_id)
  | AConst _ => p
  | ANth m n =>  ANth (incrMVar m) (incrNVar n)
  | AAbs a => AAbs (incrAVar a)
  | APlus  a b => APlus (incrAVar a) (incrAVar b)
  | AMinus a b => AMinus (incrAVar a) (incrAVar b)
  | AMult  a b => AMult (incrAVar a) (incrAVar b)
  | AMin   a b => AMin (incrAVar a) (incrAVar b)
  | AMax   a b => AMax (incrAVar a) (incrAVar b)
  | AZless a b => AZless (incrAVar a) (incrAVar b)
  end.

Fixpoint incrOp (d:DSHOperator) : DSHOperator
  := match d with
     | DSHAssign (src_p,src_o) (dst_p,dst_o) => DSHAssign (incrPVar src_p, incrNVar src_o) (incrPVar dst_p, incrNVar dst_o)
     | DSHIMap n x_p y_p f => DSHIMap n (incrPVar x_p) (incrPVar y_p) (incrAVar f)
     | DSHBinOp n x_p y_p f => DSHBinOp n (incrPVar x_p) (incrPVar y_p) (incrAVar f)
     | DSHMemMap2 n x0_p x1_p y_p f => DSHMemMap2 n (incrPVar x0_p) (incrPVar x1_p) (incrPVar y_p) (incrAVar f)
     | DSHPower n (src_p,src_o) (dst_p,dst_o) f initial =>
       DSHPower n (incrPVar src_p, incrNVar src_o) (incrPVar dst_p,  incrNVar dst_o) (incrAVar f) initial
     | DSHLoop n body => DSHLoop n (incrOp body)
     | DSHAlloc size body => DSHAlloc size (incrOp body)
     | DSHMemInit size y_p value => DSHMemInit size (incrPVar y_p) value
     | DSHMemCopy size x_p y_p => DSHMemCopy size (incrPVar x_p) (incrPVar y_p)
     | DSHSeq f g => DSHSeq (incrOp f) (incrOp g)
     end.

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
