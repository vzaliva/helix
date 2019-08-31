Require Import Coq.Lists.List.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.Compare_dec.

Require Import Helix.Util.Misc.
Require Import Helix.Util.ListSetoid.
Require Import Helix.HCOL.CarrierType.
Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.MSigmaHCOL.Memory.
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

Definition context_tl (σ: evalContext) : evalContext
  := List.tl σ.

Definition memory_lookup
           (m: memory)
           (n: mem_block_id)
  : option mem_block
  := NM.find n m.

Definition memory_set
           (m: memory)
           (n: mem_block_id)
           (v: mem_block)
  : memory
  :=
    NM.add n v m.

Definition memory_remove
           (m: memory)
           (n: mem_block_id)
  : memory
  :=
    NM.remove n m.

(* Evaluation of expressions does not allow for side-effects *)
Definition evalMexp (σ: evalContext) (exp:MExpr): option (mem_block) :=
  match exp with
  | @MVar i =>
    match nth_error σ i with
    | Some (@DSHmemVal v) => Some v
    | _ => None
    end
  | @MConst t => Some t
  end.

(* Evaluation of expressions does not allow for side-effects *)
Fixpoint evalNexp (σ: evalContext) (e:NExpr): option nat :=
  match e with
  | NVar i => v <- (nth_error σ i) ;;
               (match v with
                | DSHnatVal x => Some x
                | _ => None
                end)
  | NConst c => Some c
  | NDiv a b => liftM2 Nat.div (evalNexp σ a) (evalNexp σ b)
  | NMod a b => liftM2 Nat.modulo (evalNexp σ a) (evalNexp σ b)
  | NPlus a b => liftM2 Nat.add (evalNexp σ a) (evalNexp σ b)
  | NMinus a b => liftM2 Nat.sub (evalNexp σ a) (evalNexp σ b)
  | NMult a b => liftM2 Nat.mul (evalNexp σ a) (evalNexp σ b)
  | NMin a b => liftM2 Nat.min (evalNexp σ a) (evalNexp σ b)
  | NMax a b => liftM2 Nat.max (evalNexp σ a) (evalNexp σ b)
  end.

(* Evaluation of expressions does not allow for side-effects *)
Fixpoint evalAexp (σ: evalContext) (e:AExpr): option CarrierA :=
  match e with
  | AVar i => v <- (nth_error σ i) ;;
                (match v with
                 | DSHCarrierAVal x => Some x
                 | _ => None
                 end)
  | AConst x => Some x
  | AAbs x =>  liftM abs (evalAexp σ x)
  | APlus a b => liftM2 plus (evalAexp σ a) (evalAexp σ b)
  | AMult a b => liftM2 mult (evalAexp σ a) (evalAexp σ b)
  | AMin a b => liftM2 min (evalAexp σ a) (evalAexp σ b)
  | AMax a b => liftM2 max (evalAexp σ a) (evalAexp σ b)
  | AMinus a b =>
    a' <- (evalAexp σ a) ;;
       b' <- (evalAexp σ b) ;;
       ret (sub a' b')
  | ANth m i =>
    m' <- (evalMexp σ m) ;;
       i' <- (evalNexp σ i) ;;
       mem_lookup i' m'
  | AZless a b => liftM2 Zless (evalAexp σ a) (evalAexp σ b)
  end.

(* Evaluation of functions does not allow for side-effects *)
Definition evalIUnCarrierA (σ: evalContext) (f: DSHIUnCarrierA)
           (i:nat) (a:CarrierA): option CarrierA :=
  evalAexp (DSHCarrierAVal a :: DSHnatVal i :: σ) f.

(* Evaluation of functions does not allow for side-effects *)
Definition evalIBinCarrierA (σ: evalContext) (f: DSHIBinCarrierA)
           (i:nat) (a b:CarrierA): option CarrierA :=
  evalAexp (DSHCarrierAVal b :: DSHCarrierAVal a :: DSHnatVal i :: σ) f.

(* Evaluation of functions does not allow for side-effects *)
Definition evalBinCarrierA (σ: evalContext) (f: DSHBinCarrierA)
           (a b:CarrierA): option CarrierA :=
  evalAexp (DSHCarrierAVal b :: DSHCarrierAVal a :: σ) f.

Fixpoint evalDSHIMap
         (n: nat)
         (f: DSHIUnCarrierA)
         (σ: evalContext)
         (x y: mem_block) : option (mem_block)
  :=
      match n with
      | O => ret y
      | S n =>
        v <- mem_lookup n x ;;
          v' <- evalIUnCarrierA σ f n v ;;
          evalDSHIMap n f σ x (mem_add n v' y)
      end.

Fixpoint evalDSHMap2
         (n: nat)
         (f: DSHBinCarrierA)
         (σ: evalContext)
         (x0 x1 y: mem_block) : option (mem_block)
  :=
       match n with
       | O => ret y
       | S n =>
         v0 <- mem_lookup n x0 ;;
            v1 <- mem_lookup n x1 ;;
            v' <- evalBinCarrierA σ f v0 v1 ;;
            evalDSHMap2 n f σ x0 x1 (mem_add n v' y)
       end.

Fixpoint evalDSHBinOp
         (n off: nat)
         (f: DSHIBinCarrierA)
         (σ: evalContext)
         (x y: mem_block) : option (mem_block)
  :=
       match n with
       | O => ret y
       | S n =>
         v0 <- mem_lookup n x ;;
            v1 <- mem_lookup (n+off) x ;;
            v' <- evalIBinCarrierA σ f n v0 v1 ;;
            evalDSHBinOp n off f σ x (mem_add n v' y)
       end.

Fixpoint evalDSHPower
         (σ: evalContext)
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
         v' <- evalBinCarrierA σ f xv yv ;;
         evalDSHPower σ p f x (mem_add 0 v' y) xoffset yoffset
    end.

(* Estimates fuel requirement for [evalDSHOperator] *)
Fixpoint estimateFuel (s:DSHOperator): nat :=
  match s with
  | DSHAssign _ _ => 0
  | @DSHIMap _ _ _ _ => 0
  | @DSHMemMap2 _ _ _ _ _ => 0
  | @DSHBinOp _ _ _ _ => 0
  | DSHPower _ _ _ _ _ => 0
  | DSHLoop n body => (S (estimateFuel body)) * n
  | DSHAlloc _ _ body => S (estimateFuel body)
  | DSHMemInit _ _ _ => 0
  | DSHMemCopy _ _ _ => 0
  | DSHSeq f g =>
    S (Nat.max (estimateFuel f) (estimateFuel g))
  end.

Fixpoint evalDSHOperator
         (σ: evalContext)
         (op: DSHOperator)
         (m: memory)
         (fuel: nat): option (memory)
  :=
    match op with
    | DSHAssign (x_i, src_e) (y_i, dst_e) =>
      x <- memory_lookup m x_i ;;
        y <- memory_lookup m y_i ;;
        src <- evalNexp σ src_e ;;
        dst <- evalNexp σ dst_e ;;
        v <- mem_lookup src x ;;
        ret (memory_set m y_i (mem_add dst v y))
    | @DSHIMap n x_i y_i f =>
      x <- memory_lookup m x_i ;;
        y <- memory_lookup m y_i ;;
        y' <- evalDSHIMap n f σ x y ;;
        ret (memory_set m y_i y')
    | @DSHMemMap2 n x0_i x1_i y_i f =>
      x0 <- memory_lookup m x0_i ;;
         x1 <- memory_lookup m x1_i ;;
         y <- memory_lookup m y_i ;;
         y' <- evalDSHMap2 n f σ x0 x1 y ;;
         ret (memory_set m y_i y')
    | @DSHBinOp n x_i y_i f =>
      x <- memory_lookup m x_i ;;
        y <- memory_lookup m y_i ;;
        y' <- evalDSHBinOp n n f σ x y ;;
        ret (memory_set m y_i y')
    | DSHPower ne (x_i,xoffset) (y_i,yoffset) f initial =>
      x <- memory_lookup m x_i ;;
        y <- memory_lookup m y_i ;;
        n <- evalNexp σ ne ;; (* [n] evaluated once at the beginning *)
        let y' := mem_add 0 initial y in
        xoff <- evalNexp σ xoffset ;;
             yoff <- evalNexp σ yoffset ;;
             y'' <- evalDSHPower σ n f x y' xoff yoff ;;
             ret (memory_set m y_i y'')
    | DSHLoop O body => ret m
    | DSHLoop (S n) body =>
      match fuel with
      | O => None
      | S fuel =>
        m <- evalDSHOperator σ (DSHLoop n body) m fuel ;;
          m' <- evalDSHOperator (DSHnatVal n :: σ) body m fuel ;;
          ret m'
      end
    | DSHAlloc size t_i body =>
      match fuel with
      | O => None
      | S fuel =>
        match memory_lookup m t_i with
        | Some _ => None (* [t_i] already exists! *)
        | None =>
          m' <- evalDSHOperator σ body (memory_set m t_i (mem_empty)) fuel ;;
             ret (memory_remove m' t_i)
        end
      end
    | DSHMemInit size y_i value =>
      y <- memory_lookup m y_i ;;
        let y' := mem_union
                    (mem_const_block size value)
                    y in
        ret (memory_set m y_i y')
    | DSHMemCopy size x_i y_i =>
      x <- memory_lookup m x_i ;;
        y <- memory_lookup m y_i ;;
        let y' := mem_union x y in
        ret (memory_set m y_i y')
    | DSHSeq f g =>
      match fuel with
      | O => None
      | S fuel =>
        m <- evalDSHOperator σ f m fuel ;;
          evalDSHOperator σ g m fuel
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

Global Instance evalMexp_proper:
  Proper ((=) ==> (=) ==> (=)) (evalMexp).
Proof.
  intros c1 c2 Ec e1 e2 Ee.
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
  - assert(C1:  evalMexp c1 v1 = evalMexp c2 v2)
      by (apply evalMexp_proper; auto).
    assert(C2:  evalNexp c1 n1 = evalNexp c2 n2)
      by (apply evalNexp_proper; auto).
    repeat break_match; subst ; try reflexivity; subst;
      try inversion C1; try inversion C2;
        apply Some_inj_equiv in C1;
        apply Some_inj_equiv in C2; try congruence.
    unfold peano_naturals.nat_equiv in *.
    subst.
    f_equiv.
    assumption.
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

Global Instance evalIBinCarrierA_proper
       (σ: evalContext)
       (f: DSHIBinCarrierA)
       (i:nat):
  Proper
    ((=) ==> (=) ==> (=)) (evalIBinCarrierA σ f i).
Proof.
  simpl_relation.
  unfold evalIBinCarrierA.
  apply evalAexp_proper.
  -
    unfold equiv, ListSetoid.List_equiv.
    constructor.
    constructor.
    assumption.
    constructor.
    constructor.
    assumption.
    constructor.
    constructor.
    reflexivity.
    reflexivity.
  -
    reflexivity.
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
Definition MExpr_natvar_subst
           (name: nat)
           (value: NExpr)
           (vexp: MExpr): MExpr := vexp.

Fixpoint AExpr_natvar_subst
         (name: nat)
         (value: NExpr)
         (aexp: AExpr): AExpr :=
  match aexp with
  | AVar _ => aexp
  | AConst _ => aexp
  | ANth ve ne => ANth (MExpr_natvar_subst name value ve) (NExpr_var_subst name value ne)
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


Global Instance evalDSHBinOp_proper
       (n off: nat)
       (f: DSHIBinCarrierA)
       (σ: evalContext):
  Proper
    ((=) ==> (=) ==> (=)) (evalDSHBinOp n off f σ).
Proof.
  intros x y H x0 y0 H0.

  revert x y H x0 y0 H0.
  induction n; intros.
  -
    constructor.
    apply H0.
  -
    unfold equiv, option_Equiv.
    destruct_opt_r_equiv.
    +
      simpl in *.
      repeat break_match; try some_none; try reflexivity.
      eq_to_equiv_hyp.
      rewrite <- H in Heqo;rewrite Heqo in Heqo2;clear Heqo;some_inv.
      rewrite <- H in Heqo0;rewrite Heqo0 in Heqo3; clear Heqo0;some_inv.
      rewrite <- Heqo2 in Heqo4;rewrite <- Heqo3 in Heqo4; rewrite Heqo4 in Heqo1;clear Heqo4; some_inv.

      apply Some_inj_equiv.
      rewrite <- Hb, <- Ha.
      apply IHn.
      apply H.

      rewrite Heqo1.
      rewrite H0.
      reflexivity.
    +
      simpl in *.
      repeat break_match; try some_none; try reflexivity.
      *
        eq_to_equiv_hyp.
        rewrite <- H in Heqo;rewrite Heqo in Heqo2;clear Heqo;some_inv.
        rewrite <- H in Heqo0;rewrite Heqo0 in Heqo3; clear Heqo0;some_inv.
        rewrite <- Heqo2 in Heqo4;rewrite <- Heqo3 in Heqo4; rewrite Heqo4 in Heqo1;clear Heqo4; some_inv.

        assert(mem_add n c4 x0 = mem_add n c1 y0) as H1.
        {
          rewrite Heqo1.
          rewrite H0.
          reflexivity.
        }
        specialize (IHn x y H (mem_add n c4 x0) (mem_add n c1 y0) H1).

        rewrite Hb, Ha in IHn.
        some_none.
      *
        eq_to_equiv_hyp.
        rewrite <- H in Heqo;rewrite Heqo in Heqo2;clear Heqo;some_inv.
        rewrite <- H in Heqo0;rewrite Heqo0 in Heqo3; clear Heqo0;some_inv.
        rewrite <- Heqo2 in Heqo4; rewrite <- Heqo3 in Heqo4; rewrite Heqo4 in Heqo1; clear Heqo4.
        some_none.
      *
        repeat
        eq_to_equiv_hyp.
        rewrite <- H in Heqo. rewrite Heqo in Heqo1;clear Heqo;some_inv.
        rewrite <- H in Heqo0;rewrite Heqo0 in Heqo2; clear Heqo0;some_none.
      *
        eq_to_equiv_hyp.
        rewrite <- H in Heqo; rewrite Heqo in Heqo0; clear Heqo; some_none.
    +
      simpl in *.
      repeat break_match; try some_none; try reflexivity.
      eq_to_equiv_hyp.
      rewrite <- H in Heqo;rewrite Heqo in Heqo2;clear Heqo;some_inv.
      rewrite <- H in Heqo0;rewrite Heqo0 in Heqo3; clear Heqo0;some_inv.
      rewrite <- Heqo2 in Heqo4;rewrite <- Heqo3 in Heqo4; rewrite Heqo4 in Heqo1;clear Heqo4; some_inv.

      assert(mem_add n c4 x0 = mem_add n c1 y0) as H1.
      {
        rewrite Heqo1.
        rewrite H0.
        reflexivity.
      }
      specialize (IHn x y H (mem_add n c4 x0) (mem_add n c1 y0) H1).

      rewrite Hb, Ha in IHn.
      some_none.
      *
        eq_to_equiv_hyp.
        rewrite <- H in Heqo;rewrite Heqo in Heqo2;clear Heqo;some_inv.
        rewrite <- H in Heqo0;rewrite Heqo0 in Heqo3; clear Heqo0;some_inv.
        rewrite <- Heqo2 in Heqo4; rewrite <- Heqo3 in Heqo4; rewrite Heqo4 in Heqo1; clear Heqo4.
        some_none.
      *
        eq_to_equiv_hyp.
        rewrite <- H in Heqo; rewrite Heqo in Heqo2; clear Heqo;some_inv.
        rewrite <- H in Heqo0;rewrite Heqo0 in Heqo3; clear Heqo0; some_none.
      *
        eq_to_equiv_hyp.
        rewrite <- H in Heqo; rewrite Heqo in Heqo2; clear Heqo; some_none.
Qed.
