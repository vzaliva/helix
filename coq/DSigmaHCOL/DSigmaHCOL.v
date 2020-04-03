(* Deep embedding of a subset of SigmaHCOL *)

Require Import Coq.Strings.String.
Require Import Coq.Arith.Compare_dec.

Require Import Helix.Tactics.HelixTactics.
Require Import Helix.HCOL.CarrierType.
Require Import Helix.Util.Misc.

Require Import Helix.MSigmaHCOL.Memory.
Require Import Helix.MSigmaHCOL.MemSetoid.
Require Import Helix.MSigmaHCOL.CType.

Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.implementations.peano_naturals.
Require Import MathClasses.misc.decision.

Require Import Helix.DSigmaHCOL.NType.

Global Open Scope nat_scope.

Module Type MDSigmaHCOL (Import CT: CType) (Import NT: NType).

  Include MMemSetoid CT.

  (* Variable on stack (De-Brujn index) *)
  Definition var_id := nat.

  Inductive DSHType :=
  | DSHnat : DSHType
  | DSHCType : DSHType
  | DSHPtr : DSHType.

  Inductive DSHVal :=
  | DSHnatVal (n:NT.t): DSHVal
  | DSHCTypeVal (a:CT.t): DSHVal
  | DSHPtrVal (a:mem_block_id) (size:NT.t): DSHVal.

  Inductive DSHValType: DSHVal -> DSHType -> Prop :=
  | DSHnatVal_type (n:NT.t): DSHValType (DSHnatVal n) DSHnat
  | DSHCTypeVal_type (a:CT.t): DSHValType (DSHCTypeVal a) DSHCType
  | DSHDSHPtrVal_type (a:mem_block_id) (size:NT.t): DSHValType (DSHPtrVal a size) (DSHPtr).

  (* Functional version. *)
  Definition DSHValToType: DSHVal -> DSHType :=
    fun v => match v with
          | DSHnatVal _ => DSHnat
          | DSHCTypeVal _ =>  DSHCType
          | DSHPtrVal _ size => DSHPtr
          end.

  (* Sanity check to make sure 2 definitons above are consistent with each other *)
  Fact DSHValToType_DSHValType:
    forall v, DSHValType v (DSHValToType v).
  Proof.
    intros v.
    destruct v; constructor.
  Qed.

  (* Expressions which evaluate to `NT.t` *)
  Inductive NExpr : Type :=
  | NVar  : var_id -> NExpr
  | NConst: NT.t -> NExpr
  | NDiv  : NExpr -> NExpr -> NExpr
  | NMod  : NExpr -> NExpr -> NExpr
  | NPlus : NExpr -> NExpr -> NExpr
  | NMinus: NExpr -> NExpr -> NExpr
  | NMult : NExpr -> NExpr -> NExpr
  | NMin  : NExpr -> NExpr -> NExpr
  | NMax  : NExpr -> NExpr -> NExpr.

  (* Expressions which evaluate to [mem_block]  *)
  Inductive PExpr: Type :=
  | PVar:  var_id -> PExpr
  (*  | PConst:  constant memory addresses are not implemneted *)
  .

  (* Expressions which evaluate to [mem_block] *)
  Inductive MExpr: Type :=
  | MPtrDeref:  PExpr -> MExpr (* Dereference operator *)
  | MConst: mem_block -> MExpr.


  (* Expressions which evaluate to `CType` *)
  Inductive AExpr : Type :=
  | AVar  : var_id -> AExpr
  | AConst: CT.t -> AExpr
  | ANth  : MExpr -> NExpr -> AExpr
  | AAbs  : AExpr -> AExpr
  | APlus : AExpr -> AExpr -> AExpr
  | AMinus: AExpr -> AExpr -> AExpr
  | AMult : AExpr -> AExpr -> AExpr
  | AMin  : AExpr -> AExpr -> AExpr
  | AMax  : AExpr -> AExpr -> AExpr
  | AZless: AExpr -> AExpr -> AExpr.


  (* Memory variable along with offset *)
  Definition MemVarRef: Type := (PExpr * NExpr).

  Inductive DSHOperator :=
  | DSHNop (* no-op. *)
  | DSHAssign (src dst: MemVarRef) (* formerly [Pick] and [Embed] *)
  | DSHIMap (n: nat) (x_p y_p: PExpr) (f: AExpr) (* formerly [Pointwise] *)
  | DSHBinOp (n: nat) (x_p y_p: PExpr) (f: AExpr) (* formerly [BinOp] *)
  | DSHMemMap2 (n: nat) (x0_p x1_p y_p: PExpr) (f: AExpr) (* No direct correspondance in SHCOL *)
  | DSHPower (n:NExpr) (src dst: MemVarRef) (f: AExpr) (initial: CT.t) (* formely [Inductor] *)
  | DSHLoop (n:nat) (body: DSHOperator) (* Formerly [IUnion] *)
  | DSHAlloc (size:NT.t) (body: DSHOperator) (* allocates new uninitialized memory block and puts pointer to it on stack. The new block will be visible in the scope of [body] *)
  | DSHMemInit (size:NT.t) (y_p: PExpr) (value: CT.t) (* Initialize memory block indices [0-size] with given value *)
  | DSHMemCopy (size:NT.t) (x_p y_p: PExpr)(* copy memory blocks. Overwrites output block values, if present *)
  | DSHSeq (f g: DSHOperator) (* execute [g] after [f] *)
  .


  (* Some Setoid stuff below *)
  Instance DSHType_equiv: Equiv DSHType := eq.

  Instance DSHType_equiv_Decision (a b:DSHType):
    Decision (equiv a b).
  Proof.
    destruct a,b; try (left;constructor); right; intros H; inversion H.
  Qed.

  Instance DSHValType_Decision (v:DSHVal) (t:DSHType):
    Decision (DSHValType v t).
  Proof.
    destruct v,t; try (left;constructor); right; intros H; inversion H.
  Qed.

  Definition DSHValType_bool (v:DSHVal) (t:DSHType) := bool_decide (DSHValType v t).

  Inductive DSHVal_equiv: DSHVal -> DSHVal -> Prop :=
  | DSHnatVal_equiv {n0 n1:NT.t}: n0=n1 -> DSHVal_equiv (DSHnatVal n0) (DSHnatVal n1)
  | DSHCTypeVal_equiv {a b: CT.t}: a=b -> DSHVal_equiv (DSHCTypeVal a) (DSHCTypeVal b)
  | DSHPtr_equiv {p0 p1: mem_block_id} {s0 s1:NT.t}: s0 = s1 /\ p0=p1 -> DSHVal_equiv (DSHPtrVal p0 s0) (DSHPtrVal p1 s1).

  Instance DSHVar_Equivalence:
    Equivalence DSHVal_equiv.
  Proof.
    split.
    -
      intros x.
      destruct x; constructor; auto.
    -
      intros x y E.
      inversion E; constructor; try split; symmetry; apply H.
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
        destruct H as [Hs Hp].
        destruct H2 as [H2s H2p].
        split.
        * rewrite Hs; auto.
        * rewrite Hp; auto.
  Qed.

  Instance DSHVar_Equiv: Equiv DSHVal := DSHVal_equiv.

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

  Instance NExpr_Equiv: Equiv NExpr  := NExpr_equiv.

  Instance NExpr_Equivalence:
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

  Inductive PExpr_equiv : PExpr -> PExpr -> Prop :=
  | PVar_equiv {n0 n1}: n0=n1 -> PExpr_equiv (PVar n0) (PVar n1).

  Instance PExpr_Equiv: Equiv PExpr := PExpr_equiv.

  Instance PExpr_Equivalence:
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

  Inductive MExpr_equiv : MExpr -> MExpr -> Prop :=
  | MPtrDeref_equiv {p0 p1}: p0=p1 -> MExpr_equiv (MPtrDeref p0) (MPtrDeref p1)
  | MConst_equiv {a b: mem_block}: a=b -> MExpr_equiv (MConst a) (MConst b).

  Instance MExpr_Equiv: Equiv MExpr := MExpr_equiv.

  Instance MExpr_Equivalence:
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


  Instance AExpr_Equiv: Equiv AExpr := AExpr_equiv.

  Instance AExpr_Equivalence:
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

  Definition incrPVar (skip:nat) (p: PExpr): PExpr :=
    match p with
    | PVar var_id =>
      PVar (if le_dec skip var_id then (S var_id) else var_id)
    end.

  Definition incrMVar (skip:nat) (m: MExpr): MExpr :=
    match m with
    | MPtrDeref p => MPtrDeref (incrPVar skip p)
    | _ => m
    end.

  Fixpoint incrNVar (skip:nat) (p: NExpr): NExpr :=
    match p with
    | NVar var_id => NVar (if le_dec skip var_id then (S var_id) else var_id)
    | NConst _ => p
    | NDiv  a b => NDiv (incrNVar skip a) (incrNVar skip b)
    | NMod  a b => NMod (incrNVar skip a) (incrNVar skip b)
    | NPlus a b => NPlus (incrNVar skip a) (incrNVar skip b)
    | NMinus a b => NMinus (incrNVar skip a) (incrNVar skip b)
    | NMult a b => NMult (incrNVar skip a) (incrNVar skip b)
    | NMin  a b => NMin (incrNVar skip a) (incrNVar skip b)
    | NMax  a b => NMax (incrNVar skip a) (incrNVar skip b)
    end.

  Fixpoint incrAVar (skip:nat) (p: AExpr) : AExpr :=
    match p with
    | AVar var_id => AVar (if le_dec skip var_id then (S var_id) else var_id)
    | AConst _ => p
    | ANth m n =>  ANth (incrMVar skip m) (incrNVar skip n)
    | AAbs a => AAbs (incrAVar skip a)
    | APlus  a b => APlus (incrAVar skip a) (incrAVar skip b)
    | AMinus a b => AMinus (incrAVar skip a) (incrAVar skip b)
    | AMult  a b => AMult (incrAVar skip a) (incrAVar skip b)
    | AMin   a b => AMin (incrAVar skip a) (incrAVar skip b)
    | AMax   a b => AMax (incrAVar skip a) (incrAVar skip b)
    | AZless a b => AZless (incrAVar skip a) (incrAVar skip b)
    end.

  Definition incrDSHIUnCType (skip:nat) := incrAVar (skip + 2).
  Definition incrDSHIBinCType (skip:nat) := incrAVar (skip + 3).
  Definition incrDSHBinCType (skip:nat) := incrAVar (skip + 2).

  Fixpoint incrOp (skip:nat) (d:DSHOperator) : DSHOperator
    := match d with
       | DSHNop => DSHNop
       | DSHAssign (src_p,src_o) (dst_p,dst_o) => DSHAssign (incrPVar skip src_p, incrNVar skip src_o) (incrPVar skip dst_p, incrNVar skip dst_o)
       | DSHIMap n x_p y_p f => DSHIMap n (incrPVar skip x_p) (incrPVar skip y_p) (incrDSHIUnCType skip f)
       | DSHBinOp n x_p y_p f => DSHBinOp n (incrPVar skip x_p) (incrPVar skip y_p) (incrDSHIBinCType skip f)
       | DSHMemMap2 n x0_p x1_p y_p f => DSHMemMap2 n (incrPVar skip x0_p) (incrPVar skip x1_p) (incrPVar skip y_p) (incrDSHBinCType skip f)
       | DSHPower n (src_p,src_o) (dst_p,dst_o) f initial =>
         DSHPower (incrNVar skip n) (incrPVar skip src_p, incrNVar skip src_o) (incrPVar skip dst_p, incrNVar skip dst_o) (incrDSHBinCType skip f) initial
       | DSHLoop n body => DSHLoop n (incrOp (S skip) body)
       | DSHAlloc size body => DSHAlloc size (incrOp (S skip) body)
       | DSHMemInit size y_p value => DSHMemInit size (incrPVar skip y_p) value
       | DSHMemCopy size x_p y_p => DSHMemCopy size (incrPVar skip x_p) (incrPVar skip y_p)
       | DSHSeq f g => DSHSeq (incrOp skip f) (incrOp skip g)
       end.

  Section Printing.

    (* List of keys of elements in memblock as string.
       E.g. "{1,2,5}"
     *)
    Definition string_of_mem_block_keys (m:mem_block) : string
      :=
        "{"++(concat "," (List.map string_of_nat (mem_keys_lst m)))++"}".

    Definition string_of_PExpr (p:PExpr) : string :=
      match p with
      | PVar x => "(PVar " ++ string_of_nat x ++ ")"
      end.

    (* TODO: Implement *)
    Definition string_of_NExpr (n:NExpr) : string :=
      match n with
      | NVar x => "(NVar " ++ string_of_nat x ++ ")"
      | NConst x => NT.to_string x
      | _ => "?"
      end.

    Definition string_of_MemVarRef (m:MemVarRef) : string :=
      let '(p,n) := m in
      "(" ++ string_of_PExpr p ++ "," ++ string_of_NExpr n ++ ")".

    Definition string_of_DSHOperator (d:DSHOperator) : string :=
      match d with
      | DSHNop => "DSHNop"
      | DSHAssign src dst =>
        "DSHAssign " ++
                     string_of_MemVarRef src ++ " " ++
                     string_of_MemVarRef dst ++ " "
      | DSHIMap n x_p y_p f =>
        "DSHIMap " ++
                   string_of_nat n ++ " " ++
                   string_of_PExpr x_p ++ " " ++
                   string_of_PExpr y_p ++ " ..."
      | DSHBinOp n x_p y_p f =>
        "DSHBinOp " ++
                    string_of_nat n ++ " " ++
                    string_of_PExpr x_p ++ " " ++
                    string_of_PExpr y_p ++ " ..."
      | DSHMemMap2 n x0_p x1_p y_p f =>
        "DSHMemMap2 " ++
                      string_of_nat n ++ " " ++
                      string_of_PExpr x0_p ++ " " ++
                      string_of_PExpr x1_p ++ " " ++
                      string_of_PExpr y_p ++ " ..."
      | DSHPower n src dst f initial =>
        "DSHPower " ++
                    string_of_NExpr n ++ " " ++
                    string_of_MemVarRef src ++ " " ++
                    string_of_MemVarRef dst ++ "..."
      | DSHLoop n body =>
        "DSHLoop " ++
                   string_of_nat n ++ " "
      | DSHAlloc size body =>
        "DSHAlloc " ++
                    NT.to_string size
      | DSHMemInit size y_p value =>
        "DSHMemInit " ++
                      NT.to_string size ++ " " ++
                      string_of_PExpr y_p ++ " ..."
      | DSHMemCopy size x_p y_p =>
        "DSHMemCopy " ++
                      NT.to_string size ++ " " ++
                      string_of_PExpr x_p ++ " " ++
                      string_of_PExpr y_p ++ " ..."
      | DSHSeq f g => "DSHSeq"
      end.

  End Printing.

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

End MDSigmaHCOL.
