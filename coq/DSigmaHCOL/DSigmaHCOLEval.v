Require Import Coq.Lists.List.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.Compare_dec.
Require Import Psatz.

Require Import Helix.Util.Misc.
Require Import Helix.Util.ListSetoid.
Require Import Helix.HCOL.CarrierType.
Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.MSigmaHCOL.Memory.
Require Import Helix.MSigmaHCOL.MemSetoid.
Require Import Helix.MSigmaHCOL.CType.
Require Import Helix.Tactics.HelixTactics.
Require Import Helix.Util.OptionSetoid.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.misc.decision.

Global Open Scope nat_scope.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Import MonadNotation.
Local Open Scope monad_scope.

Module Type MDSigmaHCOLEvalSig (Import CT : CType).
  (* Some additiona =CType.t= properties and operations we need for expressions
     used in DHCOL *)

  (* Values *)
  Parameter CTypeZero: t.

  (* predicates *)
  Parameter CTypeLe: relation t.
  Parameter CTypeLt: relation t.

  (* Decidability *)
  Declare Instance CTypeLeDec: forall x y: t, Decision (CTypeLe x y).

  (* operations *)
  Parameter CTypePlus: t -> t -> t.
  Parameter CTypeNeg: t -> t.
  Parameter CTypeMult: t -> t -> t.
  Parameter CTypeAbs: t -> t.
  Parameter CTypeZLess: t -> t -> t.
  Parameter CTypeMin: t -> t -> t.
  Parameter CTypeMax: t -> t -> t.
  Parameter CTypeSub: t -> t -> t.

  (* Proper *)
  Declare Instance Zless_proper: Proper ((=) ==> (=) ==> (=)) CTypeZLess.
  Declare Instance abs_proper: Proper ((=) ==> (=)) CTypeAbs.
  Declare Instance plus_proper: Proper((=) ==> (=) ==> (=)) CTypePlus.
  Declare Instance sub_proper: Proper((=) ==> (=) ==> (=)) CTypeSub.
  Declare Instance mult_proper: Proper((=) ==> (=) ==> (=)) CTypeMult.
  Declare Instance min_proper: Proper((=) ==> (=) ==> (=)) CTypeMin.
  Declare Instance max_proper: Proper((=) ==> (=) ==> (=)) CTypeMax.
End MDSigmaHCOLEvalSig.


Module MDSigmaHCOLEval (Import CT : CType) (Import ESig:MDSigmaHCOLEvalSig CT).

  Include MDSigmaHCOL CT.

  Definition evalContext:Type := list DSHVal.

  Definition context_lookup
             (c: evalContext)
             (n: var_id)
    : option DSHVal
    := nth_error c n.

  Definition context_tl (σ: evalContext) : evalContext
    := List.tl σ.

  (* Evaluation of expressions does not allow for side-effects *)
  Definition evalMexp (σ: evalContext) (exp:MExpr): option (mem_block) :=
    match exp with
    | @MVar i =>
      match nth_error σ i with
      | Some (@DSHMemVal v) => Some v
      | _ => None
      end
    | @MConst t => Some t
    end.

  (* Evaluation of expressions does not allow for side-effects *)
  Definition evalPexp (σ: evalContext) (exp:PExpr): option (mem_block_id) :=
    match exp with
    | @PVar i =>
      match nth_error σ i with
      | Some (@DSHPtrVal v) => Some v
      | _ => None
      end
    | @PConst t => Some t
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
  Fixpoint evalAexp (σ: evalContext) (e:AExpr): option t :=
    match e with
    | AVar i => v <- (nth_error σ i) ;;
                 (match v with
                  | DSHCTypeVal x => Some x
                  | _ => None
                  end)
    | AConst x => Some x
    | AAbs x =>  liftM CTypeAbs (evalAexp σ x)
    | APlus a b => liftM2 CTypePlus (evalAexp σ a) (evalAexp σ b)
    | AMult a b => liftM2 CTypeMult (evalAexp σ a) (evalAexp σ b)
    | AMin a b => liftM2 CTypeMin (evalAexp σ a) (evalAexp σ b)
    | AMax a b => liftM2 CTypeMax (evalAexp σ a) (evalAexp σ b)
    | AMinus a b =>
      a' <- (evalAexp σ a) ;;
         b' <- (evalAexp σ b) ;;
         ret (CTypeSub a' b')
    | ANth m i =>
      m' <- (evalMexp σ m) ;;
         i' <- (evalNexp σ i) ;;
         (* Instead of returning error we default to zero here.
          This situation should never happen for programs
          refined from MSHCOL which ensure bounds via
          dependent types. So DHCOL programs should
          be correct by construction *)
         (match mem_lookup i' m' with
          | Some v => ret v
          | None => ret CTypeZero
          end)
    | AZless a b => liftM2 CTypeZLess (evalAexp σ a) (evalAexp σ b)
    end.

  (* Evaluation of functions does not allow for side-effects *)
  Definition evalIUnCType (σ: evalContext) (f: AExpr)
             (i:nat) (a:t): option t :=
    evalAexp (DSHCTypeVal a :: DSHnatVal i :: σ) f.

  (* Evaluation of functions does not allow for side-effects *)
  Definition evalIBinCType (σ: evalContext) (f: AExpr)
             (i:nat) (a b:t): option t :=
    evalAexp (DSHCTypeVal b :: DSHCTypeVal a :: DSHnatVal i :: σ) f.

  (* Evaluation of functions does not allow for side-effects *)
  Definition evalBinCType (σ: evalContext) (f: AExpr)
             (a b:t): option t :=
    evalAexp (DSHCTypeVal b :: DSHCTypeVal a :: σ) f.

  Fixpoint evalDSHIMap
           (n: nat)
           (f: AExpr)
           (σ: evalContext)
           (x y: mem_block) : option (mem_block)
    :=
      match n with
      | O => ret y
      | S n =>
        v <- mem_lookup n x ;;
          v' <- evalIUnCType σ f n v ;;
          evalDSHIMap n f σ x (mem_add n v' y)
      end.

  Fixpoint evalDSHMap2
           (n: nat)
           (f: AExpr)
           (σ: evalContext)
           (x0 x1 y: mem_block) : option (mem_block)
    :=
      match n with
      | O => ret y
      | S n =>
        v0 <- mem_lookup n x0 ;;
           v1 <- mem_lookup n x1 ;;
           v' <- evalBinCType σ f v0 v1 ;;
           evalDSHMap2 n f σ x0 x1 (mem_add n v' y)
      end.

  Fixpoint evalDSHBinOp
           (n off: nat)
           (f: AExpr)
           (σ: evalContext)
           (x y: mem_block) : option (mem_block)
    :=
      match n with
      | O => ret y
      | S n =>
        v0 <- mem_lookup n x ;;
           v1 <- mem_lookup (n+off) x ;;
           v' <- evalIBinCType σ f n v0 v1 ;;
           evalDSHBinOp n off f σ x (mem_add n v' y)
      end.

  Fixpoint evalDSHPower
           (σ: evalContext)
           (n: nat)
           (f: AExpr)
           (x y: mem_block)
           (xoffset yoffset: nat)
    : option (mem_block)
    :=
      match n with
      | O => ret y
      | S p =>
        xv <- mem_lookup 0 x ;;
           yv <- mem_lookup 0 y ;;
           v' <- evalBinCType σ f xv yv ;;
           evalDSHPower σ p f x (mem_add 0 v' y) xoffset yoffset
      end.

  (* Estimates fuel requirement for [evalDSHOperator] *)
  Fixpoint estimateFuel (s:DSHOperator): nat :=
    match s with
    | DSHNop => 1
    | DSHAssign _ _ => 1
    | @DSHIMap _ _ _ _ => 1
    | @DSHMemMap2 _ _ _ _ _ => 1
    | @DSHBinOp _ _ _ _ => 1
    | DSHPower _ _ _ _ _ => 1
    | DSHLoop n body => S (estimateFuel body * n)
    | DSHAlloc _ body => S (estimateFuel body)
    | DSHMemInit _ _ _ => 1
    | DSHMemCopy _ _ _ => 1
    | DSHSeq f g =>
      S (Nat.max (estimateFuel f) (estimateFuel g))
    end.

  Fixpoint evalDSHOperator
           (σ: evalContext)
           (op: DSHOperator)
           (m: memory)
           (fuel: nat): option (memory)
    :=
      match fuel with
      | O => None
      | S fuel =>
        match op with
        | DSHNop => ret m
        | DSHAssign (x_p, src_e) (y_p, dst_e) =>
          x_i <- evalPexp σ x_p ;;
              y_i <- evalPexp σ y_p ;;
              x <- memory_lookup m x_i ;;
              y <- memory_lookup m y_i ;;
              src <- evalNexp σ src_e ;;
              dst <- evalNexp σ dst_e ;;
              v <- mem_lookup src x ;;
              ret (memory_set m y_i (mem_add dst v y))
        | @DSHIMap n x_p y_p f =>
          x_i <- evalPexp σ x_p ;;
              y_i <- evalPexp σ y_p ;;
              x <- memory_lookup m x_i ;;
              y <- memory_lookup m y_i ;;
              y' <- evalDSHIMap n f σ x y ;;
              ret (memory_set m y_i y')
        | @DSHMemMap2 n x0_p x1_p y_p f =>
          x0_i <- evalPexp σ x0_p ;;
               x1_i <- evalPexp σ x1_p ;;
               y_i <- evalPexp σ y_p ;;
               x0 <- memory_lookup m x0_i ;;
               x1 <- memory_lookup m x1_i ;;
               y <- memory_lookup m y_i ;;
               y' <- evalDSHMap2 n f σ x0 x1 y ;;
               ret (memory_set m y_i y')
        | @DSHBinOp n x_p y_p f =>
          x_i <- evalPexp σ x_p ;;
              y_i <- evalPexp σ y_p ;;
              x <- memory_lookup m x_i ;;
              y <- memory_lookup m y_i ;;
              y' <- evalDSHBinOp n n f σ x y ;;
              ret (memory_set m y_i y')
        | DSHPower ne (x_p,xoffset) (y_p,yoffset) f initial =>
          x_i <- evalPexp σ x_p ;;
              y_i <- evalPexp σ y_p ;;
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
          m <- evalDSHOperator σ (DSHLoop n body) m fuel ;;
            m' <- evalDSHOperator (DSHnatVal n :: σ) body m fuel ;;
            ret m'
        | DSHAlloc size body =>
          let t_i := memory_new m in
          m' <- evalDSHOperator (DSHPtrVal t_i :: σ) body (memory_set m t_i (mem_empty)) fuel ;;
             ret (memory_remove m' t_i)
        | DSHMemInit size y_p value =>
          y_i <- evalPexp σ y_p ;;
              y <- memory_lookup m y_i ;;
              let y' := mem_union
                          (mem_const_block size value)
                          y in
              ret (memory_set m y_i y')
        | DSHMemCopy size x_p y_p =>
          x_i <- evalPexp σ x_p ;;
              y_i <- evalPexp σ y_p ;;
              x <- memory_lookup m x_i ;;
              y <- memory_lookup m y_i ;;
              let y' := mem_union x y in
              ret (memory_set m y_i y')
        | DSHSeq f g =>
          m <- evalDSHOperator σ f m fuel ;;
            evalDSHOperator σ g m fuel
        end
      end.

  Lemma evalDSHOperator_estimateFuel_ge (f:nat) {σ op m}:
    f >= (estimateFuel op) ->
    evalDSHOperator σ op m f ≡ evalDSHOperator σ op m (estimateFuel op).
  Proof.
    intro F.
    generalize dependent f.
    generalize dependent σ.
    generalize dependent m.
    induction op;
      try (intros; destruct F; auto; fail).
    -
      assert (EP : estimateFuel op >= 1) by (destruct op; simpl; lia).
      induction n; intros.
      +
        destruct f;
          [inversion F | reflexivity].
      +
        destruct f; [inversion F |].
        simpl estimateFuel; simpl.

        rewrite IHn by (simpl in *; lia).
        rewrite IHn with (f := estimateFuel op * S n) by (simpl in *; lia).
        break_match; try reflexivity.

        rewrite IHop by (simpl in *; rewrite PeanoNat.Nat.mul_succ_r in F; lia).
        rewrite IHop with (f := estimateFuel op * S n) by (rewrite PeanoNat.Nat.mul_succ_r; lia).
        reflexivity.
    -
      intros.
      destruct f; [inversion F|].
      simpl.
      rewrite IHop by (simpl in F; lia).
      reflexivity.
    -
      intros.
      destruct f; [inversion F|].
      simpl.

      rewrite IHop1 by (simpl in F; lia).
      rewrite IHop1 with (f := Nat.max (estimateFuel op1) (estimateFuel op2)) by lia.
      break_match; try reflexivity.

      rewrite IHop2 by (simpl in F; lia).
      rewrite IHop2 with (f := Nat.max (estimateFuel op1) (estimateFuel op2)) by lia.
      reflexivity.
  Qed.

  Local Ltac proper_eval2 IHe1 IHe2 :=
    simpl;
    repeat break_match;subst; try reflexivity; try some_none;
    f_equiv;
    rewrite <- Some_inj_equiv in IHe1;
    rewrite <- Some_inj_equiv in IHe2;
    rewrite IHe1, IHe2;
    reflexivity.

  Instance evalNexp_proper:
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

  Instance evalMexp_proper:
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

  Instance evalAexp_proper:
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
      +
        unfold equiv, peano_naturals.nat_equiv in *.
        subst_max.
        f_equiv.
        apply Some_inj_equiv.
        rewrite <- Heqo1, <- Heqo4.
        rewrite H3.
        reflexivity.
      +
        unfold equiv, peano_naturals.nat_equiv in *.
        subst_max.
        eq_to_equiv_hyp.
        rewrite H3 in Heqo1.
        some_none.
      +
        unfold equiv, peano_naturals.nat_equiv in *.
        subst_max.
        eq_to_equiv_hyp.
        rewrite H3 in Heqo1.
        some_none.
    - repeat break_match;subst; try reflexivity; try some_none.
      f_equiv.
      rewrite <- Some_inj_equiv in IHEe.
      apply abs_proper, IHEe.
    - proper_eval2 IHEe1 IHEe2.
    - proper_eval2 IHEe1 IHEe2.
    - proper_eval2 IHEe1 IHEe2.
    - proper_eval2 IHEe1 IHEe2.
    - proper_eval2 IHEe1 IHEe2.
    - proper_eval2 IHEe1 IHEe2.
  Qed.

  Instance evalBinCType_proper:
    Proper ((=) ==> (=) ==> (=)) evalBinCType.
  Proof.
    intros c1 c2 Ec e1 e2 Ee.
    unfold evalBinCType.
    intros a a' Ea b b' Eb.
    apply evalAexp_proper.
    -
      unfold equiv, List_equiv.
      apply List.Forall2_cons; constructor; auto.
      constructor; auto.
    -
      auto.
  Qed.

  Instance evalIBinCType_proper
         (σ: evalContext)
         (f: AExpr)
         (i: nat):
    Proper
      ((=) ==> (=) ==> (=)) (evalIBinCType σ f i).
  Proof.
    simpl_relation.
    unfold evalIBinCType.
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

  Instance evalDSHBinOp_proper
         (n off: nat)
         (f: AExpr)
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
          assert(mem_add n t5 x0 = mem_add n t2 y0) as H1.
          {
            rewrite Heqo1.
            rewrite H0.
            reflexivity.
          }
          specialize (IHn x y H _ _ H1).
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

        assert(mem_add n t5 x0 = mem_add n t2 y0) as H1.
        {
          rewrite Heqo1.
          rewrite H0.
          reflexivity.
        }
        specialize (IHn x y H (mem_add n t5 x0) (mem_add n t2 y0) H1).

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

  Section IncrEval.

    Lemma evalPexp_incrPVar
          (p : PExpr)
          (σ : evalContext)
          (foo: DSHVal):
      evalPexp (foo :: σ) (incrPVar 0 p) ≡ evalPexp σ p.
    Proof.
      destruct p;constructor.
    Qed.

    Lemma evalMexp_incrMVar
          (m : MExpr)
          (σ : evalContext)
          (foo: DSHVal):
      evalMexp (foo :: σ) (incrMVar 0 m) ≡ evalMexp σ m.
    Proof.
      destruct m;constructor.
    Qed.

    Lemma evalMexp_incrMVar_1
          (m : MExpr)
          (σ : evalContext)
          (a foo: DSHVal):
      evalMexp (a :: foo :: σ) (incrMVar 1 m) ≡ evalMexp (a :: σ) m.
    Proof.
      destruct m; try reflexivity.
      simpl.
      break_if.
      repeat (try destruct v; try simpl; try reflexivity; try lia).
      repeat (try destruct v; try simpl; try reflexivity; try lia).
    Qed.

    Lemma evalMexp_incrMVar_2
          (m : MExpr)
          (σ : evalContext)
          (a b foo: DSHVal):
      evalMexp (a :: b :: foo :: σ) (incrMVar 2 m) ≡ evalMexp (a :: b :: σ) m.
    Proof.
      destruct m; try reflexivity.
      simpl.
      break_if.
      repeat (try destruct v; try simpl; try reflexivity; try lia).
      repeat (try destruct v; try simpl; try reflexivity; try lia).
    Qed.

    Lemma evalMexp_incrMVar_3
          (m : MExpr)
          (σ : evalContext)
          (a b c foo: DSHVal):
      evalMexp (a :: b :: c :: foo :: σ) (incrMVar 3 m) ≡ evalMexp (a :: b :: c :: σ) m.
    Proof.
      destruct m; try reflexivity.
      simpl.
      break_if.
      repeat (try destruct v; try simpl; try reflexivity; try lia).
      repeat (try destruct v; try simpl; try reflexivity; try lia).
    Qed.

    Lemma evalNexp_incrNVar
          (n : NExpr)
          (σ : evalContext)
          (foo: DSHVal):
      evalNexp (foo :: σ) (incrNVar 0 n) ≡ evalNexp σ n.
    Proof.
      induction n; try constructor;
        (simpl;
         rewrite IHn1, IHn2;
         reflexivity).
    Qed.

    Lemma evalNexp_incrNVar_2
          (m : NExpr)
          (σ : evalContext)
          (a b foo: DSHVal):
      evalNexp (a :: b :: foo :: σ) (incrNVar 2 m) ≡ evalNexp (a :: b :: σ) m.
    Proof.
      revert a b.
      induction m; intros; try reflexivity.
      simpl.
      break_if.
      -
        repeat (try destruct v; try simpl; try reflexivity; try lia).
      -
        repeat (try destruct v; try simpl; try reflexivity; try lia).
      -
        simpl; rewrite IHm1, IHm2;reflexivity.
      -
        simpl; rewrite IHm1, IHm2;reflexivity.
      -
        simpl; rewrite IHm1, IHm2;reflexivity.
      -
        simpl; rewrite IHm1, IHm2;reflexivity.
      -
        simpl; rewrite IHm1, IHm2;reflexivity.
      -
        simpl; rewrite IHm1, IHm2;reflexivity.
      -
        simpl; rewrite IHm1, IHm2;reflexivity.
    Qed.

    Lemma evalNexp_incrNVar_3
          (m : NExpr)
          (σ : evalContext)
          (a b c foo: DSHVal):
      evalNexp (a :: b :: c :: foo :: σ) (incrNVar 3 m) ≡ evalNexp (a :: b :: c :: σ) m.
    Proof.
      revert a b c.
      induction m; intros; try reflexivity.
      simpl.
      break_if.
      -
        repeat (try destruct v; try simpl; try reflexivity; try lia).
      -
        repeat (try destruct v; try simpl; try reflexivity; try lia).
      -
        simpl; rewrite IHm1, IHm2;reflexivity.
      -
        simpl; rewrite IHm1, IHm2;reflexivity.
      -
        simpl; rewrite IHm1, IHm2;reflexivity.
      -
        simpl; rewrite IHm1, IHm2;reflexivity.
      -
        simpl; rewrite IHm1, IHm2;reflexivity.
      -
        simpl; rewrite IHm1, IHm2;reflexivity.
      -
        simpl; rewrite IHm1, IHm2;reflexivity.
    Qed.

    Lemma evalAexp_incrAVar
          (a : AExpr)
          (σ : evalContext)
          (foo: DSHVal):
      evalAexp (foo :: σ) (incrAVar 0 a) ≡ evalAexp σ a.
    Proof.
      induction a; try constructor; simpl;
        (try rewrite evalMexp_incrMVar;
         try rewrite evalNexp_incrNVar;
         try reflexivity);
        (try rewrite IHa; try reflexivity);
        (try rewrite IHa1, IHa2;reflexivity).
    Qed.

    Lemma evalAexp_incrAVar_2
          (m : AExpr)
          (σ : evalContext)
          (a b foo: DSHVal):
      evalAexp (a :: b :: foo :: σ) (incrAVar 2 m) ≡ evalAexp (a :: b :: σ) m.
    Proof.
      revert a b.
      induction m; intros; try reflexivity.
      simpl.
      break_if.
      -
        repeat (try destruct v; try simpl; try reflexivity; try lia).
      -
        repeat (try destruct v; try simpl; try reflexivity; try lia).
      -
        simpl.
        rewrite evalMexp_incrMVar_2, evalNexp_incrNVar_2.
        reflexivity.
      -
        simpl; rewrite IHm; reflexivity.
      -
        simpl; rewrite IHm1, IHm2; reflexivity.
      -
        simpl; rewrite IHm1, IHm2; reflexivity.
      -
        simpl; rewrite IHm1, IHm2; reflexivity.
      -
        simpl; rewrite IHm1, IHm2; reflexivity.
      -
        simpl; rewrite IHm1, IHm2; reflexivity.
      -
        simpl; rewrite IHm1, IHm2; reflexivity.
    Qed.

    Lemma evalAexp_incrAVar_3
          (m : AExpr)
          (σ : evalContext)
          (a b c foo: DSHVal):
      evalAexp (a :: b :: c :: foo :: σ) (incrAVar 3 m) ≡ evalAexp (a :: b :: c :: σ) m.
    Proof.
      revert a b c.
      induction m; intros; try reflexivity.
      simpl.
      break_if.
      -
        repeat (try destruct v; try simpl; try reflexivity; try lia).
      -
        repeat (try destruct v; try simpl; try reflexivity; try lia).
      -
        simpl.
        rewrite evalMexp_incrMVar_3, evalNexp_incrNVar_3.
        reflexivity.
      -
        simpl; rewrite IHm; reflexivity.
      -
        simpl; rewrite IHm1, IHm2; reflexivity.
      -
        simpl; rewrite IHm1, IHm2; reflexivity.
      -
        simpl; rewrite IHm1, IHm2; reflexivity.
      -
        simpl; rewrite IHm1, IHm2; reflexivity.
      -
        simpl; rewrite IHm1, IHm2; reflexivity.
      -
        simpl; rewrite IHm1, IHm2; reflexivity.
    Qed.

    Lemma evalIUnCType_incrDSHIUnCType
          (σ: evalContext)
          (f: AExpr)
          (i:nat)
          (a:t)
          (foo: DSHVal):
      evalIUnCType (foo :: σ) (incrDSHIUnCType f) i a ≡ evalIUnCType σ f i a.
    Proof.
      unfold incrDSHIUnCType.
      apply evalAexp_incrAVar_2.
    Qed.

    Lemma evalIBinCType_incrDSHIBinCType
          (σ: evalContext)
          (f: AExpr)
          (i:nat)
          (a b:t)
          (foo: DSHVal):
      evalIBinCType (foo :: σ) (incrDSHIBinCType f) i a b ≡ evalIBinCType σ f i a b.
    Proof.
      unfold incrDSHIBinCType.
      apply evalAexp_incrAVar_3.
    Qed.

    Lemma evalBinCType_incrDSHBinCType
          (σ: evalContext)
          (f: AExpr)
          (a b:t)
          (foo: DSHVal):
      evalBinCType (foo :: σ) (incrDSHBinCType f) a b ≡ evalBinCType σ f a b.
    Proof.
      unfold incrDSHBinCType.
      apply evalAexp_incrAVar_2.
    Qed.

    Lemma evalDSHBinOp_incrincrDSHIBinCType
          (n off: nat)
          (f: AExpr)
          (σ: evalContext)
          (x y: mem_block)
          (foo: DSHVal):
      evalDSHBinOp n off (incrDSHIBinCType f) (foo :: σ) x y ≡ evalDSHBinOp n off f σ x y.
    Proof.
      revert x y.
      induction n; intros.
      -
        reflexivity.
      -
        simpl.
        repeat break_match; try some_none.
        +
          rewrite IHn.
          f_equiv.
          f_equiv.
          apply Some_inj_eq.
          rewrite <- Heqo1, <- Heqo2.
          apply evalIBinCType_incrDSHIBinCType.
        +
          exfalso.
          rewrite evalIBinCType_incrDSHIBinCType in Heqo1.
          congruence.
        +
          exfalso.
          rewrite evalIBinCType_incrDSHIBinCType in Heqo1.
          congruence.
    Qed.

    Lemma evalDSHIMap_incrDSHIUnCType
          (n: nat)
          (f: AExpr)
          (σ: evalContext)
          (x y: mem_block)
          (foo: DSHVal):
      evalDSHIMap n (incrDSHIUnCType f) (foo :: σ) x y ≡ evalDSHIMap n f σ x y.
    Proof.
      revert x y.
      induction n; intros.
      -
        reflexivity.
      -
        simpl.
        repeat break_match; try some_none.
        +
          rewrite IHn.
          f_equiv.
          f_equiv.
          apply Some_inj_eq.
          rewrite <- Heqo1, <- Heqo0.
          apply evalIUnCType_incrDSHIUnCType.
        +
          exfalso.
          rewrite evalIUnCType_incrDSHIUnCType in Heqo0.
          congruence.
        +
          exfalso.
          rewrite evalIUnCType_incrDSHIUnCType in Heqo0.
          congruence.
    Qed.

    Lemma evalDSHMap2_incrDSHBinCType
          (n: nat)
          (f: AExpr)
          (σ: evalContext)
          (x0 x1 y: mem_block)
          (foo: DSHVal):
      evalDSHMap2 n (incrDSHBinCType f) (foo :: σ) x0 x1 y ≡ evalDSHMap2 n f σ x0 x1 y.
    Proof.
      revert x0 x1 y.
      induction n; intros.
      -
        reflexivity.
      -
        simpl.
        repeat break_match; try some_none.
        +
          rewrite IHn.
          f_equiv.
          f_equiv.
          apply Some_inj_eq.
          rewrite <- Heqo1, <- Heqo2.
          apply evalBinCType_incrDSHBinCType.
        +
          exfalso.
          rewrite evalBinCType_incrDSHBinCType in Heqo1.
          congruence.
        +
          exfalso.
          rewrite evalBinCType_incrDSHBinCType in Heqo1.
          congruence.
    Qed.

    Lemma evalDSHPower_incrDSHBinCType
          (σ: evalContext)
          (n: nat)
          (f: AExpr)
          (x y: mem_block)
          (xoffset yoffset: nat)
          (foo: DSHVal):
      evalDSHPower (foo :: σ) n (incrDSHBinCType f) x y xoffset yoffset
                   ≡ evalDSHPower σ n f x y xoffset yoffset.
    Proof.
      revert x y.
      induction n; intros.
      -
        reflexivity.
      -
        simpl.
        repeat break_match; try some_none.
        +
          rewrite IHn.
          f_equiv.
          f_equiv.
          apply Some_inj_eq.
          rewrite <- Heqo1, <- Heqo2.
          apply evalBinCType_incrDSHBinCType.
        +
          exfalso.
          rewrite evalBinCType_incrDSHBinCType in Heqo1.
          congruence.
        +
          exfalso.
          rewrite evalBinCType_incrDSHBinCType in Heqo1.
          congruence.
    Qed.


  End IncrEval.

End MDSigmaHCOLEval.
