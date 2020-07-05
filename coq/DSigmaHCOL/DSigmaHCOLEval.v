Require Import Coq.Lists.List.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Strings.String.
Require Import Psatz.

Require Import Helix.Util.Misc.
Require Import Helix.Util.ListSetoid.
Require Import Helix.HCOL.CarrierType.
Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.NType.
Require Import Helix.MSigmaHCOL.Memory.
Require Import Helix.MSigmaHCOL.MemSetoid.
Require Import Helix.MSigmaHCOL.CType.
Require Import Helix.Tactics.HelixTactics.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.Util.ErrorSetoid.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.misc.decision.
Require Import MathClasses.misc.util.

Global Open Scope nat_scope.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Import MonadNotation.
Local Open Scope monad_scope.

Module MDSigmaHCOLEval
       (Import CT : CType)
       (Import NT : NType).

  Include MDSigmaHCOL CT NT.

  Definition evalContext:Type := list DSHVal.

  Local Open Scope string_scope.

  Definition mem_lookup_err
             (msg:string)
             (n: nat)
             (mem: mem_block) : err CT.t
    :=
      trywith msg (mem_lookup n mem).

  Instance mem_lookup_err_proper:
    Proper ((=) ==> (=) ==> (=) ==> (=)) mem_lookup_err.
  Proof.
    unfold mem_lookup_err.
    simpl_relation.
    destruct_err_equiv;
      err_eq_to_equiv_hyp;
      rewrite H0, H1, H in Ha;
      rewrite Ha in Hb.
    -
      inversion Hb.
    -
      inl_inr.
    -
      inversion Hb.
      auto.
  Qed.

  Definition memory_lookup_err
             (msg:string)
             (mem: memory)
             (n: mem_block_id)
             : err mem_block
    :=
    trywith msg (memory_lookup mem n).

  Instance memory_lookup_err_proper:
    Proper ((=) ==> (=) ==> (=) ==> (=)) memory_lookup_err.
  Proof.
    unfold memory_lookup_err.
    simpl_relation.
    destruct_err_equiv;
      err_eq_to_equiv_hyp;
      rewrite H0, H1, H in Ha;
      rewrite Ha in Hb.
    -
      inversion Hb.
    -
      inl_inr.
    -
      inversion Hb.
      auto.
  Qed.

  Definition context_lookup
             (msg: string)
             (c: evalContext)
             (n: var_id)
    : err DSHVal
    := trywith msg (nth_error c n).


  Instance context_lookup_proper:
    Proper ((=) ==> (=) ==> (=) ==> (=)) context_lookup.
  Proof.
    unfold context_lookup.
    solve_proper.
  Qed.

  Definition context_tl (σ: evalContext) : evalContext
    := List.tl σ.

    (* Evaluation of expressions does not allow for side-effects *)
  Definition evalPExpr (σ: evalContext) (exp:PExpr): err (mem_block_id*NT.t) :=
    match exp with
    | @PVar i =>
      match nth_error σ i with
      | Some (@DSHPtrVal v size) => ret (v,size)
      | _ => raise "error looking up PVar"
      end
    end.

  (* Evaluation of expressions does not allow for side-effects *)
  Definition evalMExpr (mem:memory) (σ: evalContext) (exp:MExpr): err (mem_block*NT.t) :=
    match exp with
    | @MPtrDeref p =>
      '(bi,size) <- evalPExpr σ p ;;
      m <- memory_lookup_err "MPtrDeref lookup failed" mem bi ;;
      ret (m,size)
    | @MConst t size => ret (t,size)
    end.

  (* Evaluation of expressions does not allow for side-effects *)
  Fixpoint evalNExpr (σ: evalContext) (e:NExpr): err NT.t :=
    match e with
    | NVar i => v <- (context_lookup "NVar not found" σ i) ;;
               (match v with
                | DSHnatVal x => ret x
                | _ => raise "invalid NVar type"
                end)
    | NConst c => ret c
    | NDiv a b =>
      bv <- evalNExpr σ b ;;
      if NTypeEqDec bv NTypeZero then
        raise "Division by 0"
      else
        av <- evalNExpr σ a ;;
        ret (NTypeDiv av bv)
    | NMod a b   =>
      bv <- evalNExpr σ b ;;
      if NTypeEqDec bv NTypeZero then
        raise "Mod by 0"
      else
        av <- evalNExpr σ a ;;
        ret (NTypeMod av bv)
    | NPlus a b  => liftM2 NTypePlus  (evalNExpr σ a) (evalNExpr σ b)
    | NMinus a b => liftM2 NTypeMinus (evalNExpr σ a) (evalNExpr σ b)
    | NMult a b  => liftM2 NTypeMult  (evalNExpr σ a) (evalNExpr σ b)
    | NMin a b   => liftM2 NTypeMin   (evalNExpr σ a) (evalNExpr σ b)
    | NMax a b   => liftM2 NTypeMax   (evalNExpr σ a) (evalNExpr σ b)
    end.

  Definition assert_NT_lt (msg:string) (a b:NT.t) : err unit :=
    assert_true_to_err msg (Nat.ltb (to_nat a) (to_nat b)) tt.

  Definition assert_NT_le (msg:string) (a b:NT.t) : err unit :=
    assert_true_to_err msg (Nat.leb (to_nat a) (to_nat b)) tt.

  (** The following maybe should be moved somwehere. Baiscally it is
      needed for setoid rewriting to work in cases where we deal with units.
      For example, in case or [assert_NT_lt] *)
  Section UnitSetoid.
    Global Instance Unit_Equiv:
      Equiv unit := fun _ _ => True.

    Global Instance Unit_Equivalence:
      Equivalence Unit_Equiv.
    Proof.
      repeat split;auto.
    Qed.
  End UnitSetoid.

  (* Evaluation of expressions does not allow for side-effects *)
  Fixpoint evalAExpr (mem:memory) (σ: evalContext) (e:AExpr): err CT.t :=
    match e with
    | AVar i => v <- (context_lookup "AVar not found" σ i) ;;
                 (match v with
                  | DSHCTypeVal x => ret x
                  | _ => raise "invalid AVar type"
                  end)
    | AConst x => ret x
    | AAbs x =>  liftM CTypeAbs (evalAExpr mem σ x)
    | APlus a b => liftM2 CTypePlus (evalAExpr mem σ a) (evalAExpr mem σ b)
    | AMult a b => liftM2 CTypeMult (evalAExpr mem σ a) (evalAExpr mem σ b)
    | AMin a b => liftM2 CTypeMin (evalAExpr mem σ a) (evalAExpr mem σ b)
    | AMax a b => liftM2 CTypeMax (evalAExpr mem σ a) (evalAExpr mem σ b)
    | AMinus a b => liftM2 CTypeSub (evalAExpr mem σ a) (evalAExpr mem σ b)
    | ANth m i =>
      i' <- evalNExpr σ i ;;
      '(m',size) <- evalMExpr mem σ m ;;
      assert_NT_lt "ANth index out of bounds" i' size ;;
      mem_lookup_err "ANth not in memory" (NT.to_nat i') m'
    | AZless a b => liftM2 CTypeZLess (evalAExpr mem σ a) (evalAExpr mem σ b)
    end.

  (* Evaluation of functions does not allow for side-effects *)
  Definition evalIUnCType (mem:memory) (σ: evalContext) (f: AExpr)
             (i:NT.t) (a:CT.t): err CT.t :=
    evalAExpr mem (DSHCTypeVal a :: DSHnatVal i :: σ) f.

  (* Evaluation of functions does not allow for side-effects *)
  Definition evalIBinCType (mem:memory) (σ: evalContext) (f: AExpr)
             (i:NT.t) (a b:CT.t): err CT.t :=
    evalAExpr mem (DSHCTypeVal b :: DSHCTypeVal a :: DSHnatVal i :: σ) f.

  (* Evaluation of functions does not allow for side-effects *)
  Definition evalBinCType (mem:memory) (σ: evalContext) (f: AExpr)
             (a b:CT.t): err CT.t :=
    evalAExpr mem (DSHCTypeVal b :: DSHCTypeVal a :: σ) f.

  Fixpoint evalDSHIMap
           (mem:memory)
           (n: nat)
           (f: AExpr)
           (σ: evalContext)
           (x y: mem_block) : err (mem_block)
    :=
      match n with
      | O  => ret y
      | S n =>
        v <- mem_lookup_err "Error reading memory evalDSHIMap" n x ;;
        nv <- NT.from_nat n ;;
          v' <- evalIUnCType mem σ f nv v ;;
          evalDSHIMap mem n f σ x (mem_add n v' y)
      end.

  Fixpoint evalDSHMap2
           (mem:memory)
           (n: nat)
           (f: AExpr)
           (σ: evalContext)
           (x0 x1 y: mem_block) : err (mem_block)
    :=
      match n with
      | O => ret y
      | S n =>
        v0 <- mem_lookup_err ("Error reading 1st arg memory in evalDSHMap2 @" ++ (string_of_nat n) ++ " in " ++ string_of_mem_block_keys x0) n x0 ;;
           v1 <- mem_lookup_err ("Error reading 2nd arg memory in evalDSHMap2 @" ++ (string_of_nat n) ++ " in " ++ string_of_mem_block_keys x1) n x1 ;;
           v' <- evalBinCType mem σ f v0 v1 ;;
           evalDSHMap2 mem n f σ x0 x1 (mem_add n v' y)
      end.

  Fixpoint evalDSHBinOp
           (mem:memory)
           (n off: nat)
           (f: AExpr)
           (σ: evalContext)
           (x y: mem_block) : err (mem_block)
    :=
      match n with
      | O => ret y
      | S n =>
        v0 <- mem_lookup_err "Error reading 1st arg memory in evalDSHBinOp" n x ;;
        v1 <- mem_lookup_err "Error reading 2nd arg memory in evalDSHBinOp" (n+off) x ;;
        nv <- NT.from_nat n ;;
        v' <- evalIBinCType mem σ f nv v0 v1 ;;
           evalDSHBinOp mem n off f σ x (mem_add n v' y)
      end.

  Fixpoint evalDSHPower
           (mem:memory)
           (σ: evalContext)
           (n: nat)
           (f: AExpr)
           (x y: mem_block)
           (xoffset yoffset: nat)
    : err (mem_block)
    :=
      match n with
      | O => ret y
      | S p =>
        xv <- mem_lookup_err "Error reading 'xv' memory in evalDSHPower" xoffset x ;;
           yv <- mem_lookup_err "Error reading 'yv' memory in evalDSHPower" yoffset y ;;
           v' <- evalBinCType mem σ f yv xv ;;
           evalDSHPower mem σ p f x (mem_add yoffset v' y) xoffset yoffset
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
           (mem: memory)
           (fuel: nat): option (err memory)
    :=
      match fuel with
      | O => None
      | S fuel =>
        match op with
        | DSHNop => Some (ret mem)
        | DSHAssign (x_p, src_e) (y_p, dst_e) =>
          Some (
              '(x_i,x_size) <- evalPExpr σ x_p ;;
              '(y_i,y_size) <- evalPExpr σ y_p ;;
              x <- memory_lookup_err "Error looking up 'x' in DSHAssign" mem x_i ;;
              y <- memory_lookup_err "Error looking up 'y' in DSHAssign" mem y_i ;;
              src <- evalNExpr σ src_e ;;
              dst <- evalNExpr σ dst_e ;;
              assert_NT_lt "DSHAssign 'dst' out of bounds" dst y_size ;;
              v <- mem_lookup_err "Error looking up 'v' in DSHAssign" (to_nat src) x ;;
              ret (memory_set mem y_i (mem_add (to_nat dst) v y))
            )
        | @DSHIMap n x_p y_p f =>
          Some (
              n' <- from_nat n ;;
              '(x_i,x_size) <- evalPExpr σ x_p ;;
              (* assert_NT_le "DSHIMap 'n' larger than 'x_size'" n' x_size ;; *)
              '(y_i,y_size) <- evalPExpr σ y_p ;;
              assert_NT_le "DSHIMap 'n' larger than 'y_size'" n' x_size ;;
              x <- memory_lookup_err "Error looking up 'x' in DSHIMap" mem x_i ;;
              y <- memory_lookup_err "Error looking up 'y' in DSHIMap" mem y_i ;;
              y' <- evalDSHIMap mem n f σ x y ;;
              ret (memory_set mem y_i y')
            )
        | @DSHMemMap2 n x0_p x1_p y_p f =>
          Some (
              n' <- from_nat n ;;
              '(x0_i,x0_size) <- evalPExpr σ x0_p ;;
              (* assert_NT_le "DSHMemMap2 'n' larger than 'x0_size'" n' x0_size ;; *)
              '(x1_i,x1_size) <- evalPExpr σ x1_p ;;
              (* assert_NT_le "DSHMemMap2 'n' larger than 'x0_size'" n' x1_size ;; *)
              '(y_i,y_size) <- evalPExpr σ y_p ;;
              assert_NT_le "DSHMemMap2 'n' larger than 'y_size'" n' y_size ;;
              x0 <- memory_lookup_err "Error looking up 'x0' in DSHMemMap2" mem x0_i ;;
              x1 <- memory_lookup_err "Error looking up 'x1' in DSHMemMap2" mem x1_i ;;
              y <- memory_lookup_err "Error looking up 'y' in DSHMemMap2" mem y_i ;;
              y' <- evalDSHMap2 mem n f σ x0 x1 y ;;
              ret (memory_set mem y_i y')
            )
        | @DSHBinOp n x_p y_p f =>
          Some (
              n' <- from_nat n ;;
              (* nn' <- from_nat (n+n) ;; *)
              '(x_i,x_size) <- evalPExpr σ x_p ;;
              (* assert_NT_le "DSHBinOp 'n' larger than 'x_size/2'" nn' x_size ;; *)
              '(y_i,y_size) <- evalPExpr σ y_p ;;
              assert_NT_le "DSHBinOp 'n' larger than 'y_size'" n' y_size ;;
              x <- memory_lookup_err "Error looking up 'x' in DSHBinOp" mem x_i ;;
              y <- memory_lookup_err "Error looking up 'y' in DSHBinOp" mem y_i ;;
              y' <- evalDSHBinOp mem n n f σ x y ;;
              ret (memory_set mem y_i y')
            )
        | DSHPower ne (x_p,xoffset) (y_p,yoffset) f initial =>
          Some (
              '(x_i,x_size) <- evalPExpr σ x_p ;;
              '(y_i,y_size) <- evalPExpr σ y_p ;;
              x <- memory_lookup_err "Error looking up 'x' in DSHPower" mem x_i ;;
              y <- memory_lookup_err "Error looking up 'y' in DSHPower" mem y_i ;;
              n <- evalNExpr σ ne ;; (* [n] evaluated once at the beginning *)
              xoff <- evalNExpr σ xoffset ;;
              yoff <- evalNExpr σ yoffset ;;
              assert_NT_lt "DSHPower 'y' offset out of bounds" yoff y_size ;;
              let y' := mem_add (to_nat yoff) initial y in
              y'' <- evalDSHPower mem σ (to_nat n) f x y' (to_nat xoff) (to_nat yoff) ;;
              ret (memory_set mem y_i y'')
            )
        | DSHLoop O body => Some (ret mem)
        | DSHLoop (S n) body =>
          match from_nat n with
          | inl msg => Some (inl msg)
          | inr nv =>
            match evalDSHOperator σ (DSHLoop n body) mem fuel with
            | Some (inr mem) => evalDSHOperator (DSHnatVal nv :: σ) body mem fuel
            | Some (inl msg) => Some (inl msg)
            | None => None
            end
          end
        | DSHAlloc size body =>
          let t_i := memory_next_key mem in
          match evalDSHOperator (DSHPtrVal t_i size :: σ) body (memory_set mem t_i (mem_empty)) fuel with
          | Some (inr mem') => Some (ret (memory_remove mem' t_i))
          | Some (inl msg) => Some (inl msg)
          | None => None
          end
        | DSHMemInit size y_p value =>
          Some (
              '(y_i,y_size) <- evalPExpr σ y_p ;;
              assert_NT_le "DSHMemInit 'size' larger than 'y_size'" size y_size ;;
              y <- memory_lookup_err "Error looking up 'y' in DSHMemInit" mem y_i ;;
              let y' := mem_union (mem_const_block (to_nat size) value) y in
              ret (memory_set mem y_i y')
            )
        | DSHMemCopy size x_p y_p =>
          Some (
              '(x_i, x_size) <- evalPExpr σ x_p ;;
              '(y_i, y_size) <- evalPExpr σ y_p ;;
              assert_NT_le "DSHMemCopy 'size' larger than 'y_size'" size y_size ;;
              x <- memory_lookup_err "Error looking up 'x' in DSHMemCopy" mem x_i ;;
              y <- memory_lookup_err "Error looking up 'y' in DSHMemCopy" mem y_i ;;
              let y' := mem_union x y in
              ret (memory_set mem y_i y'))

        | DSHSeq f g =>
          match evalDSHOperator σ f mem fuel with
          | Some (inr mem') => evalDSHOperator σ g mem' fuel
          | Some (inl msg)  => Some (inl msg)
          | None => None
          end
        end
      end.

  Lemma evalDSHOperator_estimateFuel_ge (f:nat) {σ op m}:
    f >= (estimateFuel op) ->
    evalDSHOperator σ op m f ≡ evalDSHOperator σ op m (estimateFuel op).
  Proof.
    intro F.
    revert f σ m F.
    induction op;
      try (intros; destruct F; auto; fail).
    -
      (* Loop *)
      assert (EP : estimateFuel op >= 1) by (destruct op; simpl; lia).
      induction n; intros.
      +
        destruct f;
          [inversion F | reflexivity].
      +
        destruct f; [inversion F |].
        simpl.
        f_equiv.
        rewrite IHn by (simpl in *; lia).
        rewrite IHn with (f := estimateFuel op * S n) by (simpl in *; lia).
        repeat (break_match; try reflexivity).
        rewrite IHop by (simpl in *; rewrite PeanoNat.Nat.mul_succ_r in F; lia).
        rewrite IHop with (f := estimateFuel op * S n) by (rewrite PeanoNat.Nat.mul_succ_r; lia).
        reflexivity.
    -
      (* Alloc *)
      intros.
      destruct f; [inversion F|].
      simpl.
      rewrite IHop by (simpl in F; lia).
      reflexivity.
    -
      (* Seq *)
      intros.
      destruct f; [inversion F|].
      simpl.

      rewrite IHop1 by (simpl in F; lia).
      rewrite IHop1 with (f := Nat.max (estimateFuel op1) (estimateFuel op2)) by lia.
      repeat break_match.
      1: reflexivity.

      rewrite IHop2 by (simpl in F; lia).
      rewrite IHop2 with (f := Nat.max (estimateFuel op1) (estimateFuel op2)) by lia.
      reflexivity.
      reflexivity.
  Qed.

  Lemma evalDSHOperator_fuel_monotone:
    forall op σ mem fuel res,
      evalDSHOperator σ op mem fuel ≡ Some res ->
      evalDSHOperator σ op mem (S fuel) ≡ Some res.
  Proof.
    intros op.
    induction op; try (simpl; intros; destruct fuel; try inversion H; auto; fail).
    -
      (* Loop *)
      induction n; intros.
      +
        cbn.
        destruct fuel; simpl in H.
        * some_none.
        * assumption.
      + cbn.
        destruct fuel; simpl in H.
        some_none.
        repeat break_match_hyp; simpl in H; subst; try some_inv.
        reflexivity.
        erewrite IHn; eauto; reflexivity.
        erewrite IHn; eauto.
        setoid_rewrite IHop; eauto.
        some_none.
    -
      (* Alloc *)
      intros.
      destruct fuel.
      +
        simpl in H; some_none.
      +
        simpl in H.
        repeat break_match_hyp.
        * some_inv.
          apply IHop in Heqo.
          remember (S fuel) as fuel'.
          cbn; rewrite Heqo.
          reflexivity.
        *
          subst.
          apply IHop in Heqo; clear IHop.
          remember (S fuel) as fuel'.
          cbn.
          rewrite Heqo.
          assumption.
        *
          some_none.
    -
      (* Seq *)
      intros.
      destruct fuel.
      +
        simpl in H; some_none.
      +
        simpl in H.
        repeat break_match_hyp.
        * subst.
          apply IHop1 in Heqo; clear IHop1; some_inv.
          remember (S fuel) as fuel'.
          cbn.
          rewrite Heqo.
          reflexivity.
        * subst.
          apply IHop1 in Heqo; clear IHop1.
          apply IHop2 in H; clear IHop2.
          remember (S fuel) as fuel'.
          cbn.
          rewrite Heqo, H.
          reflexivity.
        *
          some_none.
  Qed.

  Lemma evalDSHOperator_fuel_monotone_None:
    ∀ (op : DSHOperator)  (σ : list DSHVal) (fuel : nat) (m : memory),
      evalDSHOperator σ op m (S fuel) ≡ None
      → evalDSHOperator σ op m fuel ≡ None.
  Proof.
    intros op.
    induction op; intros; try (cbn in H; repeat break_let; subst; some_none).
    -
      (* Loop *)
      destruct n.
      +
        cbn in H.
        some_none.
      + cbn in H.
        destruct fuel; [reflexivity|].
        repeat break_match_hyp; subst.
        * some_none.
        * some_none.
        *
          cbn.
          rewrite Heqs.
          repeat break_match_goal; subst.
          --
            exfalso.
            apply evalDSHOperator_fuel_monotone in Heqo0.
            rewrite Heqo in Heqo0.
            inv Heqo0.
          --
            apply evalDSHOperator_fuel_monotone in Heqo0.
            rewrite Heqo in Heqo0.
            inv Heqo0.
            apply IHop.
            auto.
          --
            reflexivity.
        *
          clear H.
          cbn.
          rewrite Heqs.
          repeat break_match_goal; subst.
          --
            exfalso.
            apply evalDSHOperator_fuel_monotone in Heqo0.
            rewrite Heqo in Heqo0.
            inv Heqo0.
          --
            apply evalDSHOperator_fuel_monotone in Heqo0.
            rewrite Heqo in Heqo0.
            inv Heqo0.
          --
            reflexivity.
    -
      (* Alloc *)
      cbn in H.
      repeat break_match_hyp; subst.
      + some_none.
      + some_none.
      + clear H.
        destruct fuel; [reflexivity|].
        eapply IHop in Heqo.
        cbn.
        rewrite Heqo.
        reflexivity.
    -
      (* Seq *)
      cbn in H.
      destruct fuel; [reflexivity|].
      repeat break_match_hyp; subst.
      + some_none.
      + (* [op1] succeeded [op2] fails *)
        cbn.
        repeat break_match_goal; subst.
        *
          exfalso.
          apply evalDSHOperator_fuel_monotone in Heqo0.
          rewrite Heqo in Heqo0.
          inv Heqo0.
        *
          apply IHop2.
          apply evalDSHOperator_fuel_monotone in Heqo0.
          rewrite Heqo in Heqo0.
          inv Heqo0.
          apply H.
        *
          reflexivity.
      + (* [op1] fails *)
        clear H.
        cbn.
        apply IHop1 in Heqo.
        rewrite Heqo.
        reflexivity.
  Qed.

  (* Generalization of [evalDSHOperator_fuel_monotone] *)
  Lemma evalDSHOperator_fuel_ge (f f':nat) {σ op m res}:
    f' >= f ->
    evalDSHOperator σ op m f ≡ Some res ->
    evalDSHOperator σ op m f' ≡ Some res.
  Proof.
    intros F.
    remember (f' - f) as k eqn:K.
    assert(f' ≡ f + k) by lia.
    clear K F.
    revert k f f' H.
    induction k; intros.
    -
      replace f' with f by nia.
      assumption.
    -
      replace f' with (S (f+k)) by lia.
      apply evalDSHOperator_fuel_monotone.
      eapply IHk; eauto.
  Qed.

  Lemma evalDSHOperator_fuel_ge_is_Some (f f':nat) {σ op m}:
    f' >= f ->
    is_Some (evalDSHOperator σ op m f) ->
    is_Some (evalDSHOperator σ op m f').
  Proof.
    intros F H.
    apply is_Some_def in H.
    destruct H as [res H].
    apply evalDSHOperator_fuel_ge with (f':=f') in H.
    apply is_Some_def.
    exists res.
    apply H.
    apply F.
  Qed.

  Lemma evalDSHOperator_estimateFuel {σ dop m}:
    is_Some (evalDSHOperator σ dop m (estimateFuel dop)).
  Proof.
    revert σ m.
    dependent induction dop; intros; cbn; auto.
    - repeat break_let; some_none.
    - repeat break_let; some_none.
    -
      induction n; intros.
      +
        some_none.
      +
        remember (estimateFuel dop) as f.
        destruct f; [crush|].

        simpl (evalDSHOperator σ (DSHLoop n dop) m (S f * S n)).

        apply is_Some_def in IHn.
        destruct IHn as [y IHn].


        repeat break_match; subst; try repeat some_none;
          try (repeat some_inv; try inl_inr); subst.
        *
          replace (S f * 1) with (S f) by lia; eapply IHdop.
        *
          eapply evalDSHOperator_fuel_ge_is_Some in IHdop.
          eapply IHdop.
          nia.
        *
          eapply evalDSHOperator_fuel_ge_is_Some in IHdop.
          eapply IHdop.
          nia.
        *
          specialize (IHdop (DSHnatVal t1 :: σ) m0).
          eapply evalDSHOperator_fuel_ge_is_Some with (f':=(S n0 + f * S (S n0)))
            in IHdop.
          norm_some_none.
          some_none.
          nia.
        *
          specialize (IHdop (DSHnatVal t1 :: σ) m0).
          eapply evalDSHOperator_fuel_ge_is_Some with (f':=(S n0 + f * S (S n0)))
            in IHdop.
          norm_some_none.
          some_none.
          nia.
        *
          eapply evalDSHOperator_fuel_ge with (f':=(S n0 + f * S (S n0)))
            in Heqo1.
          norm_some_none.
          some_none.
          nia.
        *
          eapply evalDSHOperator_fuel_ge with (f':=(S n0 + f * S (S n0)))
            in Heqo1.
          norm_some_none.
          some_none.
          nia.
    -
      (* Alloc *)
      repeat break_match_goal; try some_none.
      exfalso.
      specialize (IHdop (DSHPtrVal (memory_next_key m) size :: σ)
                        (memory_set m (memory_next_key m) mem_empty)).

      apply is_Some_ne_None in IHdop.
      congruence.
    -
      (* Seq *)
      repeat break_match_goal; try some_none; subst.
      +
        specialize (IHdop2 σ m0).
        erewrite <- evalDSHOperator_estimateFuel_ge in IHdop2.
        eauto.
        nia.
      +
        specialize (IHdop1 σ m).
        rewrite <- evalDSHOperator_estimateFuel_ge
          with (f:=(Nat.max (estimateFuel dop1) (estimateFuel dop2)))
          in IHdop1.
        congruence.
        nia.
  Qed.

  Local Ltac proper_eval2 IHe1 IHe2 :=
      repeat break_match;
        try inversion IHEe1;
        try inversion IHEe2; auto;
          subst;
          f_equiv;
      crush.

  Instance evalNExpr_proper:
    Proper ((=) ==> (=) ==> (=)) evalNExpr.
  Proof.
    intros c1 c2 Ec e1 e2 Ee.
    induction Ee; simpl.
    -
      unfold equiv, peano_naturals.nat_equiv in H.
      subst n2. rename n1 into n.

      assert_match_equiv E.
      {
        unfold context_lookup.
        apply trywith_proper.
        reflexivity.
        apply nth_error_proper.
        apply Ec.
        reflexivity.
      }
      repeat break_match; try inversion E; subst; try (constructor;auto);
      try (inversion H1;auto).
    -
      rewrite H.
      constructor.
      reflexivity.
    -
      repeat break_match; try inl_inr; try auto; try constructor.
      inl_inr_inv; rewrite e in IHEe2; crush.
      inl_inr_inv; rewrite e in IHEe2; crush.
      proper_eval2 IHEe1 IHEe2.
    - 
      repeat break_match; try inl_inr; try auto; try constructor.
      inl_inr_inv; rewrite e in IHEe2; crush.
      inl_inr_inv; rewrite e in IHEe2; crush.
      proper_eval2 IHEe1 IHEe2.
    - proper_eval2 IHEe1 IHEe2.
    - proper_eval2 IHEe1 IHEe2.
    - proper_eval2 IHEe1 IHEe2.
    - proper_eval2 IHEe1 IHEe2.
    - proper_eval2 IHEe1 IHEe2.
  Qed.

  Instance evalPExpr_proper:
    Proper ((=) ==> (=) ==> (=)) (evalPExpr).
  Proof.
    intros c1 c2 Ec e1 e2 Ee.
     destruct Ee; simpl.
     unfold equiv, peano_naturals.nat_equiv in H.
     subst n1. rename n0 into v.
     assert_match_equiv E.
     {
       apply nth_error_proper.
       apply Ec.
       reflexivity.
     }
     repeat break_match; try inversion E; subst; try (constructor;subst;auto);
       try (inversion H1;subst;auto).
     destruct H0.
     subst.
     rewrite H0, H.
     reflexivity.
  Qed.

  Instance evalMExpr_proper:
    Proper ((=) ==> (=) ==> (=) ==> (=)) (evalMExpr).
  Proof.
    intros m1 m2 Em c1 c2 Ec e1 e2 Ee.
    destruct Ee; simpl.
    -
      unfold equiv, peano_naturals.nat_equiv in H.
      assert_match_equiv E.
      {
        rewrite H, Ec.
        reflexivity.
      }
      repeat break_match ; inversion_clear E;  try (constructor;auto);
        inversion_clear H0; cbn in *; subst.
      +
        err_eq_to_equiv_hyp.
        rewrite Em, H1 in Heqs0.
        rewrite Heqs0 in Heqs2.
        inl_inr.
      +
        err_eq_to_equiv_hyp.
        rewrite Em, H1 in Heqs0.
        rewrite Heqs0 in Heqs2.
        inl_inr.
      +
        err_eq_to_equiv_hyp.
        rewrite Em, H1 in Heqs0.
        rewrite Heqs0 in Heqs2.
        inv Heqs2.
        unfold equiv, products.prod_equiv.
        auto.
    -
      constructor.
      auto.
  Qed.

  Instance evalAExpr_proper:
    Proper ((=) ==> (=) ==> (=) ==> (=)) evalAExpr.
  Proof.
    intros m1 m2 Em c1 c2 Ec e1 e2 Ee.
    induction Ee; simpl.
    -
      unfold equiv, peano_naturals.nat_equiv in H.
      subst n1. rename n0 into n.
      assert_match_equiv E.
      {
        unfold context_lookup.
        apply trywith_proper.
        reflexivity.
        apply nth_error_proper.
        apply Ec.
        reflexivity.
      }
      repeat break_match; try inversion E; subst; try (constructor;auto);
      try (inversion H1;auto).
    - f_equiv. apply H.
    - assert(C1:  evalMExpr m1 c1 v1 = evalMExpr m2 c2 v2)
        by (apply evalMExpr_proper; auto).
      assert(C2:  evalNExpr c1 n1 = evalNExpr c2 n2)
        by (apply evalNExpr_proper; auto).
      repeat break_match; subst ; try reflexivity; subst;
        try inversion C1; try inversion C2;
          apply Some_inj_equiv in C1;
          apply Some_inj_equiv in C2; try congruence; try (constructor;auto); subst.
      +
        exfalso.
        clear - Heqs1 Heqs4 C2 H3.
        some_inv.
        unfold assert_NT_lt, assert_true_to_err in *.
        repeat break_if; try inl_inr.
        repeat inl_inr_inv.
        subst.
        apply PeanoNat.Nat.ltb_ge in Heqb0.
        apply PeanoNat.Nat.ltb_lt in Heqb.
        inversion_clear H3; cbn in *.
        rewrite C2,H0 in Heqb0; clear C2 H0.
        lia.
      +
        exfalso.
        clear - Heqs1 Heqs4 C2 H3.
        some_inv.
        unfold assert_NT_lt, assert_true_to_err in *.
        repeat break_if; try inl_inr.
        repeat inl_inr_inv.
        subst.
        apply PeanoNat.Nat.ltb_lt in Heqb0.
        apply PeanoNat.Nat.ltb_ge in Heqb.
        inversion_clear H3; cbn in *.
        rewrite C2,H0 in Heqb0; clear C2 H0.
        lia.
      +
        rewrite H6.
        inversion_clear H3.
        cbn in H1.
        rewrite H1.
        reflexivity.
    -
      repeat break_match;subst; try reflexivity;
        try constructor; try inversion IHEe; auto.
      apply abs_proper, H1.
    - proper_eval2 IHEe1 IHEe2.
    - proper_eval2 IHEe1 IHEe2.
    - proper_eval2 IHEe1 IHEe2.
    - proper_eval2 IHEe1 IHEe2.
    - proper_eval2 IHEe1 IHEe2.
    - proper_eval2 IHEe1 IHEe2.
  Qed.

  Instance evalBinCType_proper:
    Proper ((=) ==> (=) ==> (=) ==> (=)) evalBinCType.
  Proof.
    intros m1 m2 Em c1 c2 Ec e1 e2 Ee.
    unfold evalBinCType.
    intros a a' Ea b b' Eb.
    apply evalAExpr_proper.
    -
      assumption.
    -
      unfold equiv, List_equiv.
      apply List.Forall2_cons; constructor; auto.
      constructor; auto.
    -
      auto.
  Qed.

  Global Instance evalIUnCType_proper :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=)) evalIUnCType.
  Proof.
    intros mem1 mem2 ME σ' σ ΣE f' f FE i' i IE a' a AE.
    unfold evalIUnCType.
    enough (T : DSHCTypeVal a' :: DSHnatVal i' :: σ' = DSHCTypeVal a :: DSHnatVal i :: σ)
      by (rewrite T, ME, FE; reflexivity).
    f_equiv.
    constructor 2.
    assumption.
    constructor.
    constructor; assumption.
    rewrite ΣE; reflexivity.
  Qed.

  Global Instance evalIBinCType_proper :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=)) evalIBinCType.
  Proof.
    intros mem1 mem2 ME σ' σ ΣE f' f FE i' i IE a' a AE b' b BE.
    unfold evalIBinCType.
    enough (T : DSHCTypeVal b' :: DSHCTypeVal a' :: DSHnatVal i' :: σ' =
                DSHCTypeVal b  :: DSHCTypeVal a  :: DSHnatVal i  :: σ)
      by (rewrite ME, T, FE; reflexivity).
    f_equiv.
    constructor; assumption.
    f_equiv.
    constructor; assumption.
    constructor.
    constructor; assumption.
    rewrite ΣE; reflexivity.
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

  Definition MemRef_NVar_subt
             (name: nat)
             (value: NExpr)
             (exp: MemRef): MemRef
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
        (MemRef_NVar_subt name value src)
        (MemRef_NVar_subt name value dst)
    | DSHPower n src dst f initial =>
      DSHPower
        (NExpr_var_subst name value n)
        (MemRef_NVar_subt name value src)
        (MemRef_NVar_subt name value dst)
        f initial
    | _ => exp
    end.


  Ltac solve_match_err_case :=
    match goal with
    | [ Ha: ?la = @inl string ?TH ?a,
            Hb: ?la = @inl string ?TH ?b
        |- ?a = ?b] =>
      let E := fresh "E" in
      assert(@inl string TH a = @inl string TH b) as E
          by
            (rewrite <- Ha, <- Hb; reflexivity);
      inversion E;
      auto
    end.

  (* TODO: This proof is terrible. It contains a lot of copy-paste and
     slow to proceess. Needs to be cleaned-up *)
  Instance evalDSHBinOp_proper
           (mem: memory)
           (n off: nat)
           (f: AExpr)
           (σ: evalContext):
    Proper
      ((=) ==> (=) ==> (=)) (evalDSHBinOp mem n off f σ).
  Proof.
    intros x y H x0 y0 H0.
    revert x y H x0 y0 H0.
    induction n; intros.
    -
      constructor.
      apply H0.
    -
      destruct_err_equiv.
      +
        err_eq_to_equiv_hyp.
        simpl in *.

        repeat break_match_hyp ; try (err_eq_to_equiv_hyp; rewrite H in Heqs0; inl_inr); inversion Ha; inversion Hb; subst; err_eq_to_equiv_hyp;
          try rewrite H in Heqs0;
          try rewrite H in Heqs1;
          try rewrite H in Heqs2;
          try rewrite H in Heqs3;
          try rewrite H in Heqs4;
          try rewrite H in Heqs5;
          try solve_match_err_case;
          try inl_inr.
        *
          rewrite Heqs4 in Heqs0.
          inversion_clear Heqs0.
          rewrite Heqs5 in Heqs1.
          inversion_clear Heqs1.
          rewrite H2, H3 in Heqs6.
          inl_inr.
        *
          rewrite Heqs4 in Heqs0.
          inversion_clear Heqs0.
          rewrite Heqs5 in Heqs1.
          inversion_clear Heqs1.
          rewrite H3, H4 in Heqs6.
          rewrite Heqs6 in Heqs3.
          inversion_clear Heqs3.
          clear H3.
          rewrite IHn with (y:=y) (y0:=mem_add n t3 y0) in H2.
          symmetry in H1.
          rewrite H1 in H2.
          inl_inr.
          apply H.
          rewrite H6, H0.
          reflexivity.
      +
        err_eq_to_equiv_hyp.
        simpl in *.
        repeat break_match_hyp ; try (err_eq_to_equiv_hyp; rewrite H in Heqs0; inl_inr); inversion Ha; inversion Hb; subst; err_eq_to_equiv_hyp;
          try rewrite H in Heqs0;
          try rewrite H in Heqs1;
          try rewrite H in Heqs2;
          try rewrite H in Heqs3;
          try rewrite H in Heqs4;
          try rewrite H in Heqs5;
          try solve_match_err_case;
          try inl_inr.
        *
          rewrite Heqs4 in Heqs0.
          inversion_clear Heqs0.
          rewrite Heqs5 in Heqs1.
          inversion_clear Heqs1.
          rewrite H2, H4 in Heqs6.
          inl_inr.
        *
          rewrite Heqs4 in Heqs0.
          inversion_clear Heqs0.
          rewrite Heqs5 in Heqs1.
          inversion_clear Heqs1.
          rewrite H2, H4 in Heqs6.
          rewrite Heqs6 in Heqs3.
          inversion_clear Heqs3.
          clear H3.
          rewrite IHn with (y:=y) (y0:=mem_add n t3 y0) in H1.
          symmetry in H1.
          clear H4.
          inl_inr.
          apply H.
          rewrite H6, H0.
          reflexivity.
      +
        err_eq_to_equiv_hyp.
        simpl in *.
        repeat break_match_hyp ; try (err_eq_to_equiv_hyp; rewrite H in Heqs0; inl_inr); inversion Ha; inversion Hb; subst; err_eq_to_equiv_hyp;
          try rewrite H in Heqs;
          try rewrite H in Heqs0;
          try rewrite H in Heqs1;
          try rewrite H in Heqs2;
          try rewrite H in Heqs3;
          try rewrite H in Heqs4;
          try rewrite H in Heqs5;
          try solve_match_err_case;
          try inl_inr.

        rewrite Heqs4 in Heqs0.
        inversion_clear Heqs0.
        rewrite Heqs3 in Heqs.
        inversion_clear Heqs.
        rewrite H2, H5 in Heqs5.
        rewrite Heqs5 in Heqs2.
        inversion_clear Heqs2.
        clear H3.
        rewrite IHn with (y:=y) (y0:=mem_add n t3 y0) in Ha.
        assert(@inr string mem_block m = @inr string mem_block m0) as E
            by (rewrite <- Ha, <- Hb; reflexivity).
        inversion E.
        auto.
        apply H.
        rewrite H7, H0.
        reflexivity.
  Qed.

  Global Instance evalDSHIMap_proper
         (mem:memory)
         (n: nat)
         (f: AExpr)
         (σ: evalContext):
    Proper
      ((=) ==> (=) ==> (=)) (evalDSHIMap mem n f σ).
  Proof.
    intros x y H x0 y0 H0.
    revert x y H x0 y0 H0.
    induction n; intros.
    -
      constructor.
      apply H0.
    -
      destruct_err_equiv.
      +
        err_eq_to_equiv_hyp.
        simpl in *.
        repeat break_match_hyp ; try (err_eq_to_equiv_hyp; rewrite H in Heqs0; inl_inr); inversion Ha; inversion Hb; subst; err_eq_to_equiv_hyp;
          try rewrite H in Heqs0;
          try rewrite H in Heqs1;
          try rewrite H in Heqs2;
          try rewrite H in Heqs3;
          try rewrite H in Heqs4;
          try solve_match_err_case;
          try inl_inr.
        *
          rewrite Heqs0 in Heqs3.
          repeat inl_inr_inv.
          rewrite Heqs3 in Heqs2.
          inl_inr.
        *
          rewrite Heqs0 in Heqs3.
          repeat inl_inr_inv.
          rewrite Heqs3 in Heqs0.
          rewrite Heqs3 in Heqs2.
          rewrite IHn with (y:=y) (y0:=mem_add n t2 y0) in H2; auto.
          symmetry in H1.
          rewrite H1 in H2.
          inl_inr.
          rewrite Heqs4 in Heqs2.
          inl_inr_inv.
          rewrite Heqs2, H0.
          reflexivity.
      +
        err_eq_to_equiv_hyp.
        simpl in *.
        repeat break_match_hyp ; try (err_eq_to_equiv_hyp; rewrite H in Heqs0; inl_inr); inversion Ha; inversion Hb; subst; err_eq_to_equiv_hyp;
          try rewrite H in Heqs0;
          try rewrite H in Heqs1;
          try rewrite H in Heqs2;
          try rewrite H in Heqs3;
          try solve_match_err_case;
          try inl_inr.
        *
          rewrite Heqs0 in Heqs3.
          repeat inl_inr_inv.
          rewrite Heqs3 in Heqs2.
          inl_inr.
        *
          rewrite Heqs0 in Heqs3.
          clear Heqs0.
          repeat inl_inr_inv.
          rewrite Heqs3 in Heqs2.
          clear Heqs3.
          rewrite Heqs2 in Heqs4.
          inl_inr_inv.
          rewrite IHn with (y:=y) (y0:=mem_add n t2 y0) in H1; auto.
          symmetry in H1.
          rewrite H1 in H5.
          inl_inr.
          rewrite Heqs4, H0.
          reflexivity.
      +
        err_eq_to_equiv_hyp.
        simpl in *.
        repeat break_match_hyp ; try (err_eq_to_equiv_hyp; rewrite H in Heqs0; inl_inr); inversion Ha; inversion Hb; subst; err_eq_to_equiv_hyp;
          try rewrite H in Heqs0;
          try rewrite H in Heqs1;
          try rewrite H in Heqs2;
          try rewrite H in Heqs3;
          try solve_match_err_case;
          try inl_inr.

        rewrite Heqs in Heqs2.
        clear Heqs.
        repeat inl_inr_inv.
        rewrite Heqs2 in Heqs1.
        rewrite Heqs1 in Heqs3.
        clear Heqs1.
        inl_inr_inv.

        symmetry in H1.
        symmetry in H4.

        rewrite IHn with (y:=y) (y0:=mem_add n t2 y0) in Ha; auto.
        rewrite Ha in Hb.
        inl_inr_inv.
        auto.
        rewrite Heqs3, H0.
        reflexivity.
  Qed.

  Global Instance memory_set_proper :
    Proper ((=) ==> (=) ==> (=)) memory_set.
  Proof.
    intros mem1 mem2 ME k k' KE mb1 mb2 BE.
    cbv in KE; subst k'.
    intros j.
    unfold memory_set.
    destruct (dec_eq_nat j k).
    repeat rewrite NP.F.add_eq_o by congruence; rewrite BE; reflexivity.
    repeat rewrite NP.F.add_neq_o by congruence; apply ME.
  Qed.
  
  Global Instance evalDSHPower_Proper :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=)) evalDSHPower.
  Proof.
    unfold Proper, respectful.
    intros m m' M σ σ' Σ n n' N
           f f' F x x' X y y' Y
           xo xo' XO yo yo' YO.
    inversion_clear N; inversion_clear XO; inversion_clear YO.
    clear n xo yo.
    rename n' into n, xo' into xo, yo' into yo.
    generalize dependent y.
    generalize dependent y'.
    induction n; intros.
    -
      cbn.
      rewrite Y.
      reflexivity.
    -
      cbn.
      repeat break_match; try constructor.
      all: err_eq_to_equiv_hyp.
      
      (* memory lookups *)
      all: try rewrite X in Heqs.
      all: try rewrite Y in Heqs0.
      all: try rewrite Heqs in *.
      all: try rewrite Heqs0 in *.
      all: try inl_inr; repeat inl_inr_inv.
      all: rewrite Heqs2 in *.
      all: rewrite Heqs3 in *.
      
      (* AExp evaluation (evalBinCType *)
      all: rewrite M, Σ, F in Heqs1.
      all: rewrite Heqs1 in Heqs4.
      all: try inl_inr; repeat inl_inr_inv.
      
      eapply IHn.
      rewrite Y, Heqs4.
      reflexivity.
  Qed.
  
  Global Instance evalDSHIMap_mem_proper :
    Proper ((=) ==> (≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡) ==> (=)) evalDSHIMap.
  Proof.
    intros mem1 mem2 ME n' n NE f' f FE σ' σ Σ xb' xb XBE yb' yb YBE.
    subst.
    generalize dependent yb.
    induction n; [reflexivity |].
    intros.
    cbn.
    repeat break_match; try (repeat constructor; fail).
    all: eq_to_equiv_hyp; err_eq_to_equiv_hyp.
    all: rewrite ME in *.
    all: rewrite Heqs1 in Heqs2; try inl_inr; inl_inr_inv.
    rewrite Heqs2.
    apply IHn.
  Qed.
  
  Global Instance evalDSHBinOp_mem_proper :
    Proper ((=) ==> (≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡) ==> (=)) evalDSHBinOp.
  Proof.
    intros mem1 mem2 ME n' n NE off' off OFFE f' f FE σ' σ ΣE x' x XE y' y YE.
    subst.
    generalize dependent y.
    induction n; [reflexivity |].
    intros.
    cbn.
    repeat break_match; try (repeat constructor; fail).
    all: err_eq_to_equiv_hyp; rewrite ME in *; try some_none.
    all: rewrite Heqs2 in Heqs3; try inl_inr; inl_inr_inv.
    rewrite Heqs3.
    apply IHn.
  Qed.
  
  Global Instance evalDSHMap2_proper :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=)) evalDSHMap2.
  Proof.
    intros m1 m2 M n1 n2 N df1 df2 DF σ1 σ2 Σ l1 l2 L r1 r2 R y1 y2 Y.
    cbv in N; subst; rename n2 into n.
    generalize dependent y2.
    generalize dependent y1.
    induction n.
    -
      intros.
      cbn.
      rewrite Y.
      reflexivity.
    -
      intros.
      cbn [evalDSHMap2].
      generalize ("Error reading 2nd arg memory in evalDSHMap2 @" ++
                                                                  Misc.string_of_nat n ++ " in " ++ string_of_mem_block_keys r1)%string.
      generalize ("Error reading 2nd arg memory in evalDSHMap2 @" ++
                                                                  Misc.string_of_nat n ++ " in " ++ string_of_mem_block_keys r2)%string.
      generalize ("Error reading 1st arg memory in evalDSHMap2 @" ++
                                                                  Misc.string_of_nat n ++ " in " ++ string_of_mem_block_keys l1)%string.
      generalize ("Error reading 1st arg memory in evalDSHMap2 @" ++
                                                                  Misc.string_of_nat n ++ " in " ++ string_of_mem_block_keys l2)%string.
      intros.
      cbn.
      assert (mem_lookup_err s0 n l1 = mem_lookup_err s n l2).
      {
        clear - L.
        unfold mem_lookup_err, trywith.
        repeat break_match; try constructor.
        all: eq_to_equiv_hyp.
        all: rewrite L in *.
        all: rewrite Heqo in Heqo0; try some_none.
        some_inv.
        assumption.
      }
      assert (mem_lookup_err s2 n r1 = mem_lookup_err s1 n r2).
      {
        clear - R.
        unfold mem_lookup_err, trywith.
        repeat break_match; try constructor.
        all: eq_to_equiv_hyp.
        all: rewrite R in *.
        all: rewrite Heqo in Heqo0; try some_none.
        some_inv.
        assumption.
      }
      repeat break_match; try inl_inr; repeat inl_inr_inv; try constructor.
      +
        err_eq_to_equiv_hyp.
        rewrite H, H0, DF, M, Σ in Heqs1.
        inl_inr.
      +
        err_eq_to_equiv_hyp.
        rewrite H, H0, DF, M, Σ in Heqs1.
        inl_inr.
      +
        apply IHn.
        err_eq_to_equiv_hyp.
        rewrite H, H0, DF, M, Σ in Heqs1.
        rewrite Heqs1 in Heqs5.
        inl_inr_inv.
        rewrite Heqs5, Y.
        reflexivity.
  Qed.

  Lemma memory_lookup_err_inr_Some_eq
        (msg : string)
        (m : memory)
        (k : mem_block_id)
        (mb : mem_block)
    :
      memory_lookup_err msg m k ≡ inr mb <->
      memory_lookup m k ≡ Some mb.
  Proof.
    unfold memory_lookup_err, trywith.
    split; intros.
    break_match; try inl_inr.
    inversion H.
    reflexivity.
    rewrite H.
    reflexivity.
  Qed.
  
  Lemma memory_lookup_err_inl_None_eq
        (msg msg' : string)
        (m : memory)
        (k : mem_block_id)
    :
      memory_lookup_err msg m k ≡ inl msg' ->
      memory_lookup m k ≡ None.
  Proof.
    unfold memory_lookup_err, trywith.
    intros.
    break_match; try inl_inr.
    reflexivity.
  Qed.

  Lemma memory_lookup_err_inl_None
        (msg msg' : string)
        (mem : memory)
        (n : mem_block_id)
    :
      memory_lookup_err msg mem n = inl msg' <->
      memory_lookup mem n = None.
  Proof.
    unfold memory_lookup_err, trywith.
    split; intros.
    all: break_match.
    all: inversion H.
    all: constructor.
  Qed.
  
  Lemma memory_lookup_err_inr_Some
        (msg : string)
        (mem : memory)
        (n : mem_block_id)
        (mb : mem_block)
    :
      memory_lookup_err msg mem n = inr mb <->
      memory_lookup mem n = Some mb.
  Proof.
    unfold memory_lookup_err, trywith.
    split; intros.
    all: break_match.
    all: inversion H.
    all: rewrite H2.
    all: reflexivity.
  Qed.

  Ltac memory_lookup_err_to_option :=
    repeat
      match goal with
      | [ H: memory_lookup_err _ _ _ = inr _ |- _] =>
        apply memory_lookup_err_inr_Some in H
      | [ H: memory_lookup_err _ _ _ = inl _ |- _] =>
        apply memory_lookup_err_inl_None in H
      | [ H: memory_lookup_err _ _ _ ≡ inr _ |- _] =>
        apply memory_lookup_err_inr_Some_eq in H
      | [ H: memory_lookup_err _ _ _ ≡ inl _ |- _] =>
        apply memory_lookup_err_inl_None_eq in H
      end.

  Lemma mem_lookup_err_inr_Some_eq
        (msg : string)
        (mb : mem_block)
        (n : nat)
        (a : CT.t)
    :
      mem_lookup_err msg n mb ≡ inr a <->
      mem_lookup n mb ≡ Some a.
  Proof.
    unfold mem_lookup_err, trywith.
    split; intros.
    break_match; try inl_inr.
    inversion H.
    reflexivity.
    rewrite H.
    reflexivity.
  Qed.

  Lemma mem_lookup_err_inl_None_eq
        (msg msg' : string)
        (mb : mem_block)
        (n : nat)
    :
      mem_lookup_err msg n mb ≡ inl msg' ->
      mem_lookup n mb ≡ None.
  Proof.
    unfold mem_lookup_err, trywith.
    intros.
    break_match; try inl_inr.
    reflexivity.
  Qed.

  Lemma mem_lookup_err_inl_None
        (msg msg' : string)
        (mb : mem_block)
        (n : nat)
    :
      mem_lookup_err msg n mb = inl msg' <->
      mem_lookup n mb = None.
  Proof.
    unfold mem_lookup_err, trywith.
    split; intros.
    all: break_match.
    all: inversion H.
    all: constructor.
  Qed.

  Lemma mem_lookup_err_inr_Some
        (msg : string)
        (mb : mem_block)
        (n : nat)
        (a : CT.t)
    :
      mem_lookup_err msg n mb = inr a <->
      mem_lookup n mb = Some a.
  Proof.
    unfold mem_lookup_err, trywith.
    split; intros.
    all: break_match.
    all: inversion H.
    all: rewrite H2.
    all: reflexivity.
  Qed.

  Ltac mem_lookup_err_to_option :=
    repeat
      match goal with
      | [ H: mem_lookup_err _ _ _ = inr _ |- _] =>
        apply mem_lookup_err_inr_Some in H
      | [ H: mem_lookup_err _ _ _ = inl _ |- _] =>
        apply mem_lookup_err_inl_None in H
      | [ H: mem_lookup_err _ _ _ ≡ inr _ |- _] =>
        apply mem_lookup_err_inr_Some_eq in H
      | [ H: mem_lookup_err _ _ _ ≡ inl _ |- _] =>
        apply mem_lookup_err_inl_None_eq in H
      end.

  Lemma memory_next_key_struct
        (m m' : memory):
    (forall k, mem_block_exists k m <-> mem_block_exists k m') ->
    memory_next_key m = memory_next_key m'.
  Proof.
    intros H.
    unfold memory_next_key.
    destruct (NS.max_elt (memory_keys_set m)) as [k1|] eqn:H1;
      destruct (NS.max_elt (memory_keys_set m')) as [k2|] eqn:H2.
    -
      f_equiv.
      cut(¬ k1 < k2 /\ ¬ k2 < k1);[lia|].
      split.
      +
        apply (NS.max_elt_2 H1), memory_keys_set_In, H.
        apply NS.max_elt_1, memory_keys_set_In in H2.
        apply H2.
      +
        apply (NS.max_elt_2 H2), memory_keys_set_In, H.
        apply NS.max_elt_1, memory_keys_set_In in H1.
        apply H1.
    - exfalso.
      apply NS.max_elt_1 in H1.
      apply NS.max_elt_3 in H2.
      apply memory_keys_set_In in H1.
      apply H in H1.
      apply memory_keys_set_In in H1.
      apply  NSP.empty_is_empty_1 in H2.
      rewrite H2 in H1.
      apply NSP.FM.empty_iff in H1.
      tauto.
    - exfalso.
      apply NS.max_elt_1 in H2.
      apply NS.max_elt_3 in H1.
      apply memory_keys_set_In in H2.
      apply H in H2.
      apply memory_keys_set_In in H2.
      apply  NSP.empty_is_empty_1 in H1.
      rewrite H1 in H2.
      apply NSP.FM.empty_iff in H2.
      tauto.
    -
      reflexivity.
  Qed.

  Global Instance memory_remove_proper :
    Proper ((=) ==> (=) ==> (=)) memory_remove.
  Proof.
    intros m1 m2 ME k1 k2 KE.
    unfold memory_remove, equiv, memory_Equiv.
    intros k.
    destruct (dec_eq_nat k1 k).
    -
      assert (k2 ≡ k) by (cbv in KE; congruence).
      repeat rewrite NP.F.remove_eq_o by assumption.
      reflexivity.
    -
      assert (k2 ≢ k) by (cbv in KE; congruence).
      repeat rewrite NP.F.remove_neq_o by assumption.
      apply ME.
  Qed.
  
  Global Instance evalDSHOperator_mem_proper:
    Proper ((≡) ==> (≡) ==> (=) ==> (≡) ==> (=)) evalDSHOperator.
  Proof.
    intros σ' σ ΣE dop' dop DE mem1 mem2 ME fuel' fuel FE.
    subst.
    
    generalize dependent mem2.
    generalize dependent mem1.
    generalize dependent fuel.
    generalize dependent σ.
    induction dop.
    -
      intros.
      destruct fuel; [reflexivity |].
      cbn.
      repeat f_equiv.
      assumption.
    -
      intros.
      destruct fuel; [reflexivity |].
      cbn.
      repeat (break_match; try (repeat constructor; fail)).
      all: memory_lookup_err_to_option.
      all: eq_to_equiv_hyp; err_eq_to_equiv_hyp.
      all: rewrite ME in *; try some_none.
      all: rewrite Heqs1 in Heqs7; some_inv.
      all: rewrite Heqs7 in Heqs6.
      all: rewrite Heqs6 in Heqs9.
      all: try inl_inr; inl_inr_inv.
      rewrite Heqs9.
      rewrite Heqs2 in Heqs8; some_inv.
      rewrite Heqs8.
      reflexivity.
    -
      intros.
      destruct fuel; [reflexivity |].
      cbn.
      repeat (break_match; try (repeat constructor; fail)).
      all: memory_lookup_err_to_option.
      all: eq_to_equiv_hyp; err_eq_to_equiv_hyp.
      all: rewrite ME in *; try some_none.
      all: rewrite Heqs3 in Heqs6; some_inv; rewrite Heqs6 in *.
      all: rewrite Heqs4 in Heqs7; some_inv; rewrite Heqs7 in *.
      all: rewrite Heqs5 in Heqs8; try inl_inr; inl_inr_inv.
      do 2 f_equiv.
      rewrite Heqs8.
      reflexivity.
    -
      intros.
      destruct fuel; [reflexivity |].
      cbn.
      repeat (break_match; try (repeat constructor; fail)).
      all: memory_lookup_err_to_option.
      all: eq_to_equiv_hyp; err_eq_to_equiv_hyp.
      all: rewrite ME in *; try some_none.
      all: rewrite Heqs3 in Heqs6; some_inv; rewrite Heqs6 in *.
      all: rewrite Heqs4 in Heqs7; some_inv; rewrite Heqs7 in *.
      all: rewrite Heqs5 in Heqs8; try inl_inr; inl_inr_inv.
      do 2 f_equiv.
      rewrite Heqs8.
      reflexivity.
    -
      intros.
      destruct fuel; [reflexivity |].
      cbn.
      repeat (break_match; try (repeat constructor; fail)).
      all: memory_lookup_err_to_option.
      all: eq_to_equiv_hyp; err_eq_to_equiv_hyp.
      all: rewrite ME in *; try some_none.
      all: rewrite Heqs5 in Heqs9; some_inv; rewrite Heqs9 in *.
      all: rewrite Heqs6 in Heqs10; some_inv; rewrite Heqs10 in *.
      all: rewrite Heqs4 in Heqs8; some_inv; rewrite Heqs8 in *.
      all: rewrite Heqs7 in Heqs11; try inl_inr; inl_inr_inv.
      do 2 f_equiv.
      rewrite Heqs11.
      reflexivity.
    -
      intros.
      destruct fuel; [reflexivity |].
      cbn.
      repeat (break_match; try (repeat constructor; fail)).
      all: memory_lookup_err_to_option.
      all: eq_to_equiv_hyp; err_eq_to_equiv_hyp.
      all: rewrite ME in *; try some_none.
      all: rewrite Heqs1 in Heqs8; some_inv; rewrite Heqs8 in *.
      all: rewrite Heqs2 in Heqs9; some_inv; rewrite Heqs9 in *.
      all: rewrite Heqs7 in Heqs10; try inl_inr; inl_inr_inv.
      do 2 f_equiv.
      rewrite Heqs10.
      reflexivity.
    -
      intros.
      
      generalize dependent fuel.
      induction n.
      +
        intros.
        destruct fuel; [reflexivity |].
        cbn.
        rewrite ME.
        reflexivity.
      +
        intros.
        destruct fuel; [reflexivity |].
        cbn.
        specialize (IHn fuel).
        repeat break_match;
          try some_none; repeat some_inv;
            try inl_inr; repeat inl_inr_inv.
        repeat constructor.
        apply IHdop.
        assumption.
    -
      intros.
      destruct fuel; [reflexivity |].
      cbn.
      replace (memory_next_key mem1) with (memory_next_key mem2).
      2: {
        apply memory_next_key_struct.
        intros.
        repeat rewrite memory_is_set_is_Some.
        assert (memory_lookup mem1 k = memory_lookup mem2 k) by apply ME.
        unfold is_Some.
        repeat break_match; try some_none; intuition.
      }
      
      assert (evalDSHOperator (DSHPtrVal (memory_next_key mem2) size :: σ) dop
                              (memory_set mem1 (memory_next_key mem2) mem_empty) fuel =
              evalDSHOperator (DSHPtrVal (memory_next_key mem2) size :: σ) dop
                              (memory_set mem2 (memory_next_key mem2) mem_empty) fuel)
        by (apply IHdop; rewrite ME; reflexivity).
      
      destruct evalDSHOperator eqn:D1 at 1;
        destruct evalDSHOperator eqn:D2 at 1;
        rewrite D1, D2 in *; try some_none; some_inv.
      repeat break_match; try inl_inr. 
      repeat constructor.
      do 2 f_equiv.
      inl_inr_inv.
      rewrite H.
      reflexivity.
    -
      intros.
      destruct fuel; [reflexivity |].
      cbn.
      repeat break_match; try (repeat constructor; fail).
      all: err_eq_to_equiv_hyp; eq_to_equiv_hyp.
      all: memory_lookup_err_to_option.
      all: rewrite ME in *; try some_none.
      rewrite Heqs1 in Heqs2; some_inv.
      do 3 f_equiv.
      intros k.
      unfold mem_union.
      repeat rewrite NP.F.map2_1bis by reflexivity.
      break_match; try reflexivity.
      apply Heqs2.
    -
      intros.
      destruct fuel; [reflexivity |].
      cbn.
      repeat break_match; try (repeat constructor; fail).
      all: err_eq_to_equiv_hyp.
      all: memory_lookup_err_to_option.
      all: rewrite ME in *; try some_none.
      rewrite Heqs2 in Heqs4; some_inv; rewrite Heqs4 in *.
      rewrite Heqs3 in Heqs5; some_inv; rewrite Heqs5 in *.
      f_equiv.
      f_equiv.
      f_equiv.
      intros k; specialize (Heqs4 k); specialize (Heqs5 k).
      unfold mem_union.
      repeat rewrite NP.F.map2_1bis by reflexivity.
      repeat break_match; try some_none.
      some_inv; rewrite Heqs4; reflexivity.
      assumption.
    -
      intros.
      destruct fuel; [reflexivity |].
      cbn.
      assert (evalDSHOperator σ dop1 mem1 fuel = evalDSHOperator σ dop1 mem2 fuel)
        by (apply IHdop1; assumption).
      repeat break_match;
        try some_none; repeat some_inv;
          try inl_inr; repeat inl_inr_inv.
      repeat constructor.
      apply IHdop2.
      assumption.
  Qed.

  Section IncrEval.

    Lemma evalPExpr_incrPVar
          (p : PExpr)
          (σ : evalContext)
          (foo: DSHVal):
      evalPExpr (foo :: σ) (incrPVar 0 p) ≡ evalPExpr σ p.
    Proof.
      destruct p;constructor.
    Qed.

    Lemma evalMExpr_incrMVar
          (mem: memory)
          (m : MExpr)
          (σ : evalContext)
          (foo: DSHVal):
      evalMExpr mem (foo :: σ) (incrMVar 0 m) ≡ evalMExpr mem σ m.
    Proof.
      destruct m.
      -
        simpl.
        assert_match_eq E.
        apply evalPExpr_incrPVar.
        repeat break_match; try inl_inr; try inl_inr_inv; subst; auto.
        +
          rewrite Heqs0 in Heqs2.
          inl_inr_inv.
          auto.
        +
          rewrite Heqs0 in Heqs2.
          inl_inr.
        +
          rewrite Heqs0 in Heqs2.
          inl_inr.
        +
          rewrite Heqs0 in Heqs2.
          inl_inr_inv.
          f_equiv.
      -
        constructor.
    Qed.

    Lemma evalNExpr_incrNVar
          (n : NExpr)
          (σ : evalContext)
          (foo: DSHVal):
      evalNExpr (foo :: σ) (incrNVar 0 n) ≡ evalNExpr σ n.
    Proof.
      induction n; try constructor;
        (simpl;
         rewrite IHn1, IHn2;
         reflexivity).
    Qed.

    Lemma evalAExpr_incrAVar
          (mem: memory)
          (a : AExpr)
          (σ : evalContext)
          (foo: DSHVal):
      evalAExpr mem (foo :: σ) (incrAVar 0 a) ≡ evalAExpr mem σ a.
    Proof.
      induction a; try constructor; simpl;
        (try rewrite evalMExpr_incrMVar;
         try rewrite evalNExpr_incrNVar;
         try reflexivity);
        (try rewrite IHa; try reflexivity);
        (try rewrite IHa1, IHa2;reflexivity).
    Qed.

  End IncrEval.

End MDSigmaHCOLEval.
