Require Import Coq.Lists.List.
Require Import Coq.Arith.Peano_dec.
Require Import CoLoR.Util.Vector.VecUtil.

Require Import Helix.Util.Misc.
Require Import Helix.Util.VecUtil.
Require Import Helix.Util.VecSetoid.
Require Import Helix.Util.ListSetoid.
Require Import Helix.HCOL.CarrierType.
Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.SigmaHCOL.Memory.
Require Import Helix.Tactics.HelixTactics.
Require Import Helix.Util.OptionSetoid.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.orders.minmax.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.misc.decision.

Global Open Scope nat_scope.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Import MonadNotation.
Local Open Scope monad_scope.

Definition evalContext:Type := list DSHVal.

Definition context_lookup
           (c: evalContext)
           (n: var_id)
  : option DSHVal
  := nth_error c n.

Definition context_replace
           (c: evalContext)
           (n: var_id)
           (v: DSHVal)
  : evalContext
  :=
    ListUtil.replace_at c n v.

Definition context_lookup_mem
           (c: evalContext)
           (n: var_id)
  : option mem_block
  := match (nth_error c n) with
     | Some (DSHmemVal m) => ret m
     | _ => None
     end.


(* Evaluation of expressions does not allow for side-effects *)
Definition evalVexp (st:evalContext) {n} (exp:VExpr n): option (avector n) :=
  match exp in (VExpr n0) return (option (vector CarrierA n0)) with
  | @VVar n0 i =>
    match nth_error st i with
    | Some (@DSHvecVal n2 v) =>
      match eq_nat_dec n2 n0 as s0 return (_ ≡ s0 -> option (vector CarrierA n0))
      with
      | left E => fun _ => eq_rect n2 (fun n3 => option (vector CarrierA n3)) (Some v) n0 E
      | right _ => fun _ => None
      end eq_refl
    | _ => None
    end
  | @VConst _ t => Some t
  end.

(* Evaluation of expressions does not allow for side-effects *)
Fixpoint evalNexp (st:evalContext) (e:NExpr): option nat :=
  match e with
  | NVar i => v <- (nth_error st i) ;;
               (match v with
                | DSHnatVal x => Some x
                | _ => None
                end)
  | NConst c => Some c
  | NDiv a b => liftM2 Nat.div (evalNexp st a) (evalNexp st b)
  | NMod a b => liftM2 Nat.modulo (evalNexp st a) (evalNexp st b)
  | NPlus a b => liftM2 Nat.add (evalNexp st a) (evalNexp st b)
  | NMinus a b => liftM2 Nat.sub (evalNexp st a) (evalNexp st b)
  | NMult a b => liftM2 Nat.mul (evalNexp st a) (evalNexp st b)
  | NMin a b => liftM2 Nat.min (evalNexp st a) (evalNexp st b)
  | NMax a b => liftM2 Nat.max (evalNexp st a) (evalNexp st b)
  end.

(* Evaluation of expressions does not allow for side-effects *)
Fixpoint evalAexp (st:evalContext) (e:AExpr): option CarrierA :=
  match e with
  | AVar i => v <- (nth_error st i) ;;
                (match v with
                 | DSHCarrierAVal x => Some x
                 | _ => None
                 end)
  | AConst x => Some x
  | AAbs x =>  liftM abs (evalAexp st x)
  | APlus a b => liftM2 plus (evalAexp st a) (evalAexp st b)
  | AMult a b => liftM2 mult (evalAexp st a) (evalAexp st b)
  | AMin a b => liftM2 min (evalAexp st a) (evalAexp st b)
  | AMax a b => liftM2 max (evalAexp st a) (evalAexp st b)
  | AMinus a b =>
    a' <- (evalAexp st a) ;;
       b' <- (evalAexp st b) ;;
       ret (sub a' b')
  | @ANth n v i =>
    v' <- (evalVexp st v) ;;
       i' <- (evalNexp st i) ;;
       match Compare_dec.lt_dec i' n with
       | left ic => Some (Vnth v' ic)
       | in_right => None
       end
  | AZless a b => liftM2 Zless (evalAexp st a) (evalAexp st b)
  end.

Require Import Coq.Arith.Compare_dec.
Require Import Helix.SigmaHCOL.SigmaHCOL.
Require Import Helix.SigmaHCOL.SVector.
Require Import Helix.SigmaHCOL.Rtheta.

(* Evaluation of functions does not allow for side-effects *)
Definition evalIUnCarrierA (Γ: evalContext) (f: DSHIUnCarrierA)
           (i:nat) (a:CarrierA): option CarrierA :=
  evalAexp (DSHCarrierAVal a :: DSHnatVal i :: Γ) f.

(* Evaluation of functions does not allow for side-effects *)
Definition evalIBinCarrierA (Γ: evalContext) (f: DSHIBinCarrierA)
           (i:nat) (a b:CarrierA): option CarrierA :=
  evalAexp (DSHCarrierAVal b :: DSHCarrierAVal a :: DSHnatVal i :: Γ) f.

(* Evaluation of functions does not allow for side-effects *)
Definition evalBinCarrierA (Γ: evalContext) (f: DSHBinCarrierA)
           (a b:CarrierA): option CarrierA :=
  evalAexp (DSHCarrierAVal b :: DSHCarrierAVal a :: Γ) f.

Fixpoint evalDSHIMap
         (n: nat)
         (f: DSHIUnCarrierA)
         (Γ: evalContext)
         (x y: mem_block) : option (mem_block)
  :=
    v <- mem_lookup n x ;;
      v' <- evalIUnCarrierA Γ f n v ;;
      let y' := mem_add n v' y in
      match n with
      | O => ret y'
      | S n => evalDSHIMap n f Γ x y'
      end.

Fixpoint evalDSHMap2
         (n: nat)
         (f: DSHBinCarrierA)
         (Γ: evalContext)
         (x0 x1 y: mem_block) : option (mem_block)
  :=
    v0 <- mem_lookup n x0 ;;
       v1 <- mem_lookup n x1 ;;
       v' <- evalBinCarrierA Γ f v0 v1 ;;
       let y' := mem_add n v' y in
       match n with
       | O => ret y'
       | S n => evalDSHMap2 n f Γ x0 x1 y'
       end.

Fixpoint evalDSHBinOp
         (n off: nat)
         (f: DSHIBinCarrierA)
         (Γ: evalContext)
         (x y: mem_block) : option (mem_block)
  :=
    v0 <- mem_lookup n x ;;
       v1 <- mem_lookup (n+off) x ;;
       v' <- evalIBinCarrierA Γ f n v0 v1 ;;
       let y' := mem_add n v' y in
       match n with
       | O => ret y'
       | S n => evalDSHBinOp n off f Γ x y'
       end.

Fixpoint evalDSHPower
         (Γ: evalContext)
         (n: nat)
         (f: DSHBinCarrierA)
         (x y: mem_block)
         (xoffset yoffset: nat)
  : option (mem_block)
  :=
    match n with
    | O => ret y
    | S p =>
      xv <- mem_lookup 0 x ;;
         yv <- mem_lookup 0 y ;;
         v' <- evalBinCarrierA Γ f xv yv ;;
         let y' := mem_add 0 v' y in
         evalDSHPower Γ p f x y' xoffset yoffset
    end.

Fixpoint evalDSHOperator
         (Γ: evalContext)
         (op: DSHOperator)
         (fuel: nat)
         {struct fuel}: option (evalContext)
  :=
    match op with
    | DSHAssign (x_i, src_e) (y_i, dst_e) =>
      x <- context_lookup_mem Γ x_i ;;
        y <- context_lookup_mem Γ y_i ;;
        src <- evalNexp Γ src_e ;;
        dst <- evalNexp Γ dst_e ;;
        v <- mem_lookup src x ;;
        let y' := mem_add dst v y in
        ret (context_replace Γ y_i (DSHmemVal y'))
    | @DSHIMap n x_i y_i f =>
      x <- context_lookup_mem Γ x_i ;;
        y <- context_lookup_mem Γ y_i ;;
        y' <- evalDSHIMap n f Γ x y ;;
        ret (context_replace Γ y_i (DSHmemVal y'))
    | @DSHMemMap2 n x0_i x1_i y_i f =>
      match fuel with
      | O => None
      | S fuel =>
        x0 <- context_lookup_mem Γ x0_i ;;
           x1 <- context_lookup_mem Γ x1_i ;;
           y <- context_lookup_mem Γ y_i ;;
           y' <- evalDSHMap2 n f Γ x0 x1 y ;;
           ret (context_replace Γ y_i (DSHmemVal y'))
      end
    | @DSHBinOp n off x_i y_i f =>
      x <- context_lookup_mem Γ x_i ;;
        y <- context_lookup_mem Γ y_i ;;
         y' <- evalDSHBinOp n off f Γ x y ;;
         ret (context_replace Γ y_i (DSHmemVal y'))
    | DSHPower ne (x_i,xoffset) (y_i,yoffset) f initial =>
      x <- context_lookup_mem Γ x_i ;;
        y <- context_lookup_mem Γ y_i ;;
        n <- evalNexp Γ ne ;; (* [n] evaluated once at the beginning *)
        let y' := mem_add 0 initial y in
        xoff <- evalNexp Γ xoffset ;;
        yoff <- evalNexp Γ yoffset ;;
        y' <- evalDSHPower Γ n f x y xoff yoff ;;
           ret (context_replace Γ y_i (DSHmemVal y'))
    | DSHLoop O body => Some Γ
    | DSHLoop (S n) body =>
      match fuel with
      | O => None
      | S fuel =>
        Γ <- evalDSHOperator Γ (DSHLoop n body) fuel ;;
          evalDSHOperator (DSHnatVal n :: Γ) body fuel
      end
    | DSHAlloc size => ret (DSHmemVal (mem_empty) :: Γ)
    | DSHMemInit size y_i value =>
      y <- context_lookup_mem Γ y_i ;;
        let y' := mem_union
                    (mem_const_block size value)
                    y in
        ret (context_replace Γ y_i (DSHmemVal y'))
    | DSHMemCopy size x_i y_i =>
      x <- context_lookup_mem Γ x_i ;;
        y <- context_lookup_mem Γ y_i ;;
        let y' := mem_union x y in
        ret (context_replace Γ y_i (DSHmemVal y'))
    | DSHSeq f g =>
      match fuel with
      | O => None
      | S fuel =>
        Γ <- evalDSHOperator Γ f fuel ;;
          evalDSHOperator Γ g fuel
      end
    end.


Local Ltac proper_eval2 IHe1 IHe2 :=
  simpl;
  repeat break_match;subst; try reflexivity; try some_none;
  f_equiv;
  rewrite <- Some_inj_equiv in IHe1;
  rewrite <- Some_inj_equiv in IHe2;
  rewrite IHe1, IHe2;
  reflexivity.

Global Instance evalNexp_proper:
  Proper ((=) ==> (=) ==> (=)) evalNexp.
Proof.
  intros c1 c2 Ec e1 e2 Ee.
  induction Ee; simpl.
  -
    unfold equiv, peano_naturals.nat_equiv in H.
    subst n2. rename n1 into n.
    assert(E: nth_error c1 n = nth_error c2 n).
    {
      apply nth_error_proper.
      apply Ec.
      reflexivity.
    }
    repeat break_match; subst; try reflexivity; try some_none; try (rewrite <- Some_inj_equiv in E; inversion E).
    subst.
    rewrite H1.
    reflexivity.
  -
    rewrite H.
    reflexivity.
  - proper_eval2 IHEe1 IHEe2.
  - proper_eval2 IHEe1 IHEe2.
  - proper_eval2 IHEe1 IHEe2.
  - proper_eval2 IHEe1 IHEe2.
  - proper_eval2 IHEe1 IHEe2.
  - proper_eval2 IHEe1 IHEe2.
  - proper_eval2 IHEe1 IHEe2.
Qed.

Global Instance evalVexp_proper:
  Proper ((=) ==> (forall_relation (fun n => (=) ==> (=)))) (evalVexp).
Proof.
  intros c1 c2 Ec n e1 e2 Ee.
  induction Ee; simpl.
  -
    unfold equiv, peano_naturals.nat_equiv in H.
    subst n1. rename n0 into v.

    assert(E: nth_error c1 v = nth_error c2 v).
    {
      apply nth_error_proper.
      apply Ec.
      reflexivity.
    }
    repeat break_match; subst; try reflexivity; try some_none; try (rewrite <- Some_inj_equiv in E; inversion E); inv_exitstT; subst; try congruence.
    simpl.
    f_equiv.
    auto.
  -
    rewrite H.
    auto.
Qed.

Global Instance evalAexp_proper:
  Proper ((=) ==> (=) ==> (=)) evalAexp.
Proof.
  intros c1 c2 Ec e1 e2 Ee.
  induction Ee; simpl.
  - unfold equiv, peano_naturals.nat_equiv in H.
    subst n1. rename n0 into n.
    assert(E: nth_error c1 n = nth_error c2 n).
    {
      apply nth_error_proper.
      apply Ec.
      reflexivity.
    }
    repeat break_match; subst; try reflexivity; try some_none; try (rewrite <- Some_inj_equiv in E; inversion E).
    subst.
    rewrite H1.
    reflexivity.
  - f_equiv. apply H.
  - assert(C1:  evalVexp c1 v1 = evalVexp c2 v2)
      by (apply evalVexp_proper; auto).
    assert(C2:  evalNexp c1 n1 = evalNexp c2 n2)
      by (apply evalNexp_proper; auto).
    repeat break_match; subst ; try reflexivity; subst;
      try inversion C1; try inversion C2;
        apply Some_inj_equiv in C1;
        apply Some_inj_equiv in C2; try congruence.
    unfold peano_naturals.nat_equiv in *.
    subst.
    f_equiv.
    apply Vnth_equiv; auto.
  - repeat break_match;subst; try reflexivity; try some_none.
    f_equiv.
    rewrite <- Some_inj_equiv in IHEe.
    rewrite IHEe.
    reflexivity.
  - proper_eval2 IHEe1 IHEe2.
  - proper_eval2 IHEe1 IHEe2.
  - proper_eval2 IHEe1 IHEe2.
  - proper_eval2 IHEe1 IHEe2.
  - proper_eval2 IHEe1 IHEe2.
  - proper_eval2 IHEe1 IHEe2.
Qed.

Global Instance evalBinCarrierA_proper:
  Proper ((=) ==> (=) ==> (=)) evalBinCarrierA.
Proof.
  intros c1 c2 Ec e1 e2 Ee.
  unfold evalBinCarrierA.
  intros a a' Ea b b' Eb.
  apply evalAexp_proper.
  -
    unfold equiv, List_equiv.
    apply List.Forall2_cons; constructor; auto.
    constructor; auto.
  -
    auto.
Qed.

Fixpoint NExpr_var_subst
         (name: nat)
         (value: NExpr)
         (nexp: NExpr): NExpr :=
  match nexp with
  | NVar v =>
    if eq_nat_dec v name
    then value
    else nexp
  | NConst _ => nexp
  | NDiv   a b => NDiv   (NExpr_var_subst name value a) (NExpr_var_subst name value b)
  | NMod   a b => NMod   (NExpr_var_subst name value a) (NExpr_var_subst name value b)
  | NPlus  a b => NPlus  (NExpr_var_subst name value a) (NExpr_var_subst name value b)
  | NMinus a b => NMinus (NExpr_var_subst name value a) (NExpr_var_subst name value b)
  | NMult  a b => NMult  (NExpr_var_subst name value a) (NExpr_var_subst name value b)
  | NMin   a b => NMin   (NExpr_var_subst name value a) (NExpr_var_subst name value b)
  | NMax   a b => NMax   (NExpr_var_subst name value a) (NExpr_var_subst name value b)
  end.

(* No natvars used in vector expressions *)
Definition VExpr_natvar_subst
           {n:nat}
           (name: nat)
           (value: NExpr)
           (vexp: VExpr n): VExpr n := vexp.

Fixpoint AExpr_natvar_subst
         (name: nat)
         (value: NExpr)
         (aexp: AExpr): AExpr :=
  match aexp with
  | AVar _ => aexp
  | AConst _ => aexp
  | ANth n ve ne => ANth n (VExpr_natvar_subst name value ve) (NExpr_var_subst name value ne)
  | AAbs x => AAbs (AExpr_natvar_subst name value x)
  | APlus  a b => APlus (AExpr_natvar_subst name value a) (AExpr_natvar_subst name value b)
  | AMinus a b => AMinus (AExpr_natvar_subst name value a) (AExpr_natvar_subst name value b)
  | AMult  a b => AMult (AExpr_natvar_subst name value a) (AExpr_natvar_subst name value b)
  | AMin   a b => AMin (AExpr_natvar_subst name value a) (AExpr_natvar_subst name value b)
  | AMax   a b => AMax (AExpr_natvar_subst name value a) (AExpr_natvar_subst name value b)
  | AZless a b => AZless (AExpr_natvar_subst name value a) (AExpr_natvar_subst name value b)
  end.


Definition MemVarRef_NVar_subt
           (name: nat)
           (value: NExpr)
           (exp: MemVarRef): MemVarRef
  :=
    let '(v, e) := exp in
    (v, NExpr_var_subst name value e).

Fixpoint DSHOperator_NVar_subt
         (name: nat)
         (value: NExpr)
         (exp: DSHOperator): DSHOperator :=
  match exp with
  | DSHAssign src dst =>
    DSHAssign
      (MemVarRef_NVar_subt name value src)
      (MemVarRef_NVar_subt name value dst)
  | DSHPower n src dst f initial =>
    DSHPower
      (NExpr_var_subst name value n)
      (MemVarRef_NVar_subt name value src)
      (MemVarRef_NVar_subt name value dst)
      f initial
  | _ => exp
  end.
