Require Import Coq.Lists.List.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Strings.String.
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
Require Import Helix.Util.ErrorSetoid.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.misc.decision.
Require Import MathClasses.misc.util.

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

  Local Open Scope string_scope.

  Definition mem_lookup_err
             (msg:string)
             (n: nat)
             (mem: mem_block)
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
  Definition evalPexp (σ: evalContext) (exp:PExpr): err (mem_block_id) :=
    match exp with
    | @PVar i =>
      match nth_error σ i with
      | Some (@DSHPtrVal v _) => ret v
      | _ => raise "error looking up PVar"
      end
    end.

  (* Evaluation of expressions does not allow for side-effects *)
  Definition evalMexp (mem:memory) (σ: evalContext) (exp:MExpr): err (mem_block) :=
    match exp with
    | @MPtrDeref p =>
      bi <- evalPexp σ p ;;
         memory_lookup_err "MPtrDeref lookup failed" mem bi
    | @MConst t => ret t
    end.

  (* Evaluation of expressions does not allow for side-effects *)
  Fixpoint evalNexp (σ: evalContext) (e:NExpr): err nat :=
    match e with
    | NVar i => v <- (context_lookup "NVar not found" σ i) ;;
                 (match v with
                  | DSHnatVal x => ret x
                  | _ => raise "invalid NVar type"
                  end)
    | NConst c => ret c
    | NDiv a b => liftM2 Nat.div (evalNexp σ a) (evalNexp σ b)
    | NMod a b => liftM2 Nat.modulo (evalNexp σ a) (evalNexp σ b)
    | NPlus a b => liftM2 Nat.add (evalNexp σ a) (evalNexp σ b)
    | NMinus a b => liftM2 Nat.sub (evalNexp σ a) (evalNexp σ b)
    | NMult a b => liftM2 Nat.mul (evalNexp σ a) (evalNexp σ b)
    | NMin a b => liftM2 Nat.min (evalNexp σ a) (evalNexp σ b)
    | NMax a b => liftM2 Nat.max (evalNexp σ a) (evalNexp σ b)
    end.

  (* Evaluation of expressions does not allow for side-effects *)
  Fixpoint evalAexp (mem:memory) (σ: evalContext) (e:AExpr): err t :=
    match e with
    | AVar i => v <- (context_lookup "AVar not found" σ i) ;;
                 (match v with
                  | DSHCTypeVal x => ret x
                  | _ => raise "invalid AVar type"
                  end)
    | AConst x => ret x
    | AAbs x =>  liftM CTypeAbs (evalAexp mem σ x)
    | APlus a b => liftM2 CTypePlus (evalAexp mem σ a) (evalAexp mem σ b)
    | AMult a b => liftM2 CTypeMult (evalAexp mem σ a) (evalAexp mem σ b)
    | AMin a b => liftM2 CTypeMin (evalAexp mem σ a) (evalAexp mem σ b)
    | AMax a b => liftM2 CTypeMax (evalAexp mem σ a) (evalAexp mem σ b)
    | AMinus a b => liftM2 CTypeSub (evalAexp mem σ a) (evalAexp mem σ b)
    | ANth m i =>
      m' <- (evalMexp mem σ m) ;;
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
    | AZless a b => liftM2 CTypeZLess (evalAexp mem σ a) (evalAexp mem σ b)
    end.

  (* Evaluation of functions does not allow for side-effects *)
  Definition evalIUnCType (mem:memory) (σ: evalContext) (f: AExpr)
             (i:nat) (a:t): err t :=
    evalAexp mem (DSHCTypeVal a :: DSHnatVal i :: σ) f.

  (* Evaluation of functions does not allow for side-effects *)
  Definition evalIBinCType (mem:memory) (σ: evalContext) (f: AExpr)
             (i:nat) (a b:t): err t :=
    evalAexp mem (DSHCTypeVal b :: DSHCTypeVal a :: DSHnatVal i :: σ) f.

  (* Evaluation of functions does not allow for side-effects *)
  Definition evalBinCType (mem:memory) (σ: evalContext) (f: AExpr)
             (a b:t): err t :=
    evalAexp mem (DSHCTypeVal b :: DSHCTypeVal a :: σ) f.

  Fixpoint evalDSHIMap
           (mem:memory)
           (n: nat)
           (f: AExpr)
           (σ: evalContext)
           (x y: mem_block) : err (mem_block)
    :=
      match n with
      | O => ret y
      | S n =>
        v <- mem_lookup_err "Error reading memory evalDSHIMap" n x ;;
          v' <- evalIUnCType mem σ f n v ;;
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
           v' <- evalIBinCType mem σ f n v0 v1 ;;
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
        xv <- mem_lookup_err "Error reading 'xv' memory in evalDSHBinOp" xoffset x ;;
           yv <- mem_lookup_err "Error reading 'yv' memory in evalDSHBinOp" yoffset y ;;
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
          x_i <- evalPexp σ x_p ;;
          y_i <- evalPexp σ y_p ;;
          x <- memory_lookup_err "Error looking up 'x' in DSHAssign" mem x_i ;;
          y <- memory_lookup_err "Error looking up 'y' in DSHAssign" mem y_i ;;
          src <- evalNexp σ src_e ;;
          dst <- evalNexp σ dst_e ;;
          v <- mem_lookup_err "Error looking up 'v' in DSHAssign" src x ;;
          ret (memory_set mem y_i (mem_add dst v y))
            )
        | @DSHIMap n x_p y_p f =>
          Some (
            x_i <- evalPexp σ x_p ;;
              y_i <- evalPexp σ y_p ;;
              x <- memory_lookup_err "Error looking up 'x' in DSHIMap" mem x_i ;;
              y <- memory_lookup_err "Error looking up 'y' in DSHIMap" mem y_i ;;
              y' <- evalDSHIMap mem n f σ x y ;;
              ret (memory_set mem y_i y')
              )
        | @DSHMemMap2 n x0_p x1_p y_p f =>
          Some (
          x0_i <- evalPexp σ x0_p ;;
               x1_i <- evalPexp σ x1_p ;;
               y_i <- evalPexp σ y_p ;;
               x0 <- memory_lookup_err "Error looking up 'x0' in DSHMemMap2" mem x0_i ;;
               x1 <- memory_lookup_err "Error looking up 'x1' in DSHMemMap2" mem x1_i ;;
               y <- memory_lookup_err "Error looking up 'y' in DSHMemMap2" mem y_i ;;
               y' <- evalDSHMap2 mem n f σ x0 x1 y ;;
               ret (memory_set mem y_i y')
               )
        | @DSHBinOp n x_p y_p f =>
          Some (
              x_i <- evalPexp σ x_p ;;
              y_i <- evalPexp σ y_p ;;
              x <- memory_lookup_err "Error looking up 'x' in DSHBinOp" mem x_i ;;
              y <- memory_lookup_err "Error looking up 'y' in DSHBinOp" mem y_i ;;
              y' <- evalDSHBinOp mem n n f σ x y ;;
              ret (memory_set mem y_i y')
              )
        | DSHPower ne (x_p,xoffset) (y_p,yoffset) f initial =>
          Some (
          x_i <- evalPexp σ x_p ;;
              y_i <- evalPexp σ y_p ;;
              x <- memory_lookup_err "Error looking up 'x' in DSHPower" mem x_i ;;
              y <- memory_lookup_err "Error looking up 'y' in DSHPower" mem y_i ;;
              n <- evalNexp σ ne ;; (* [n] evaluated once at the beginning *)
              xoff <- evalNexp σ xoffset ;;
              yoff <- evalNexp σ yoffset ;;
              let y' := mem_add yoff initial y in
              y'' <- evalDSHPower mem σ n f x y' xoff yoff ;;
              ret (memory_set mem y_i y'')
            )
        | DSHLoop O body => Some (ret mem)
        | DSHLoop (S n) body =>
          match evalDSHOperator σ (DSHLoop n body) mem fuel with
          | Some (inr mem) => evalDSHOperator (DSHnatVal n :: σ) body mem fuel
          | Some (inl msg) => Some (inl msg)
          | None => None
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
              y_i <- evalPexp σ y_p ;;
              y <- memory_lookup_err "Error looking up 'y' in DSHMemInit" mem y_i ;;
              let y' := mem_union (mem_const_block size value) y in
              ret (memory_set mem y_i y')
            )
        | DSHMemCopy size x_p y_p =>
          Some (
          x_i <- evalPexp σ x_p ;;
          y_i <- evalPexp σ y_p ;;
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
        *
          cbn.
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
          specialize (IHdop (DSHnatVal n0 :: σ) m0).
          eapply evalDSHOperator_fuel_ge_is_Some with (f':=(S n0 + f * S (S n0)))
            in IHdop.
          norm_some_none.
          some_none.
          nia.
        *
          specialize (IHdop (DSHnatVal n0 :: σ) m0).
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

  Instance evalNexp_proper:
    Proper ((=) ==> (=) ==> (=)) evalNexp.
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
    - proper_eval2 IHEe1 IHEe2.
    - proper_eval2 IHEe1 IHEe2.
    - proper_eval2 IHEe1 IHEe2.
    - proper_eval2 IHEe1 IHEe2.
    - proper_eval2 IHEe1 IHEe2.
    - proper_eval2 IHEe1 IHEe2.
    - proper_eval2 IHEe1 IHEe2.
  Qed.

  Instance evalPexp_proper:
    Proper ((=) ==> (=) ==> (=)) (evalPexp).
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
     repeat break_match; try inversion E; subst; try (constructor;auto);
       try (inversion H1;auto).
     destruct H0.
     auto.
  Qed.

  Instance evalMexp_proper:
    Proper ((=) ==> (=) ==> (=) ==> (=)) (evalMexp).
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
      repeat break_match; try inversion E; subst; try (constructor;auto);
        try (inversion H1;auto).
      rewrite H2, Em.
      reflexivity.
    -
      constructor.
      auto.
  Qed.

  Instance evalAexp_proper:
    Proper ((=) ==> (=) ==> (=) ==> (=)) evalAexp.
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
    - assert(C1:  evalMexp m1 c1 v1 = evalMexp m2 c2 v2)
        by (apply evalMexp_proper; auto).
      assert(C2:  evalNexp c1 n1 = evalNexp c2 n2)
        by (apply evalNexp_proper; auto).
      repeat break_match; subst ; try reflexivity; subst;
        try inversion C1; try inversion C2;
          apply Some_inj_equiv in C1;
          apply Some_inj_equiv in C2; try congruence; try (constructor;auto); subst.

      +
        apply Some_inj_equiv.
        rewrite <- Heqo, <- Heqo0.
        rewrite H3, H6.
        reflexivity.
      +
        eq_to_equiv_hyp.
        rewrite H3, H6 in Heqo.
        some_none.
      +
        eq_to_equiv_hyp.
        rewrite H3, H6 in Heqo.
        some_none.
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

  Instance evalIUnCType_proper
         (mem: memory)
         (σ: evalContext)
         (f: AExpr)
         (i: nat):
    Proper
      ((=) ==> (=)) (evalIUnCType mem σ f i).
  Proof.
    simpl_relation.
    unfold evalIUnCType.
    apply evalAexp_proper.
    -
      reflexivity.
    -
      unfold equiv, ListSetoid.List_equiv.
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

  Instance evalBinCType_proper:
    Proper ((=) ==> (=) ==> (=) ==> (=)) evalBinCType.
  Proof.
    intros m1 m2 Em c1 c2 Ec e1 e2 Ee.
    unfold evalBinCType.
    intros a a' Ea b b' Eb.
    apply evalAexp_proper.
    -
      assumption.
    -
      unfold equiv, List_equiv.
      apply List.Forall2_cons; constructor; auto.
      constructor; auto.
    -
      auto.
  Qed.

  Instance evalIBinCType_proper
         (mem: memory)
         (σ: evalContext)
         (f: AExpr)
         (i: nat):
    Proper
      ((=) ==> (=) ==> (=)) (evalIBinCType mem σ f i).
  Proof.
    simpl_relation.
    unfold evalIBinCType.
    apply evalAexp_proper.
    -
      reflexivity.
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
          try solve_match_err_case;
          try inl_inr.
        *
          rewrite Heqs4 in Heqs1.
          inversion_clear Heqs1.
          rewrite Heqs3 in Heqs0.
          inversion_clear Heqs0.
          rewrite H2, H3 in Heqs5.
          inl_inr.
        *
          rewrite Heqs4 in Heqs1.
          inversion_clear Heqs1.
          rewrite Heqs3 in Heqs0.
          inversion_clear Heqs0.
          rewrite H3, H4 in Heqs5.
          rewrite Heqs5 in Heqs2.
          inversion_clear Heqs2.
          clear H3.
          rewrite IHn with (y:=y) (y0:=mem_add n t2 y0) in H2.
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
          try solve_match_err_case;
          try inl_inr.
        *

          rewrite Heqs4 in Heqs1.
          inversion_clear Heqs1.
          rewrite Heqs3 in Heqs0.
          inversion_clear Heqs0.
          rewrite H2, H4 in Heqs5.
          inl_inr.
        *
          rewrite Heqs4 in Heqs1.
          inversion_clear Heqs1.
          rewrite Heqs3 in Heqs0.
          inversion_clear Heqs0.
          rewrite H2, H4 in Heqs5.
          rewrite Heqs5 in Heqs2.
          inversion_clear Heqs2.
          clear H3.
          rewrite IHn with (y:=y) (y0:=mem_add n t2 y0) in H1.
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
          try rewrite H in Heqs0;
          try rewrite H in Heqs1;
          try rewrite H in Heqs2;
          try rewrite H in Heqs3;
          try rewrite H in Heqs4;
          try solve_match_err_case;
          try inl_inr.

        rewrite Heqs2 in Heqs.
        inversion_clear Heqs.
        rewrite Heqs3 in Heqs0.
        inversion_clear Heqs0.
        rewrite H2, H5 in Heqs4.
        rewrite Heqs4 in Heqs1.
        inversion_clear Heqs1.
        clear H3.
        rewrite IHn with (y:=y) (y0:=mem_add n t2 y0) in Ha.

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
          rewrite Heqs0 in Heqs2.
          repeat inl_inr_inv.
          rewrite Heqs2 in Heqs1.
          inl_inr.
        *
          rewrite Heqs0 in Heqs2.
          repeat inl_inr_inv.
          rewrite Heqs2 in Heqs0.
          rewrite Heqs2 in Heqs1.
          rewrite IHn with (y:=y) (y0:=mem_add n t1 y0) in H2; auto.
          symmetry in H1.
          rewrite H1 in H2.
          inl_inr.
          rewrite Heqs3 in Heqs1.
          inl_inr_inv.
          rewrite Heqs1, H0.
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
          rewrite Heqs0 in Heqs2.
          repeat inl_inr_inv.
          rewrite Heqs2 in Heqs1.
          inl_inr.
        *
          rewrite Heqs0 in Heqs2.
          clear Heqs0.
          repeat inl_inr_inv.
          rewrite Heqs2 in Heqs1.
          clear Heqs2.
          rewrite Heqs1 in Heqs3.
          inl_inr_inv.
          rewrite IHn with (y:=y) (y0:=mem_add n t1 y0) in H1; auto.
          symmetry in H1.
          rewrite H1 in H5.
          inl_inr.
          rewrite Heqs3, H0.
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

        rewrite Heqs in Heqs1.
        clear Heqs.
        repeat inl_inr_inv.
        rewrite Heqs1 in Heqs0.
        rewrite Heqs0 in Heqs2.
        clear Heqs0.
        inl_inr_inv.

        symmetry in H1.
        symmetry in H4.

        rewrite IHn with (y:=y) (y0:=mem_add n t1 y0) in Ha; auto.
        rewrite Ha in Hb.
        inl_inr_inv.
        auto.
        rewrite Heqs2, H0.
        reflexivity.
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
          (mem: memory)
          (m : MExpr)
          (σ : evalContext)
          (foo: DSHVal):
      evalMexp mem (foo :: σ) (incrMVar 0 m) ≡ evalMexp mem σ m.
    Proof.
      destruct m.
      -
        simpl.
        assert_match_eq E.
        apply evalPexp_incrPVar.
        repeat break_match; try inversion E; auto.
      -
        constructor.
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

    Lemma evalAexp_incrAVar
          (mem: memory)
          (a : AExpr)
          (σ : evalContext)
          (foo: DSHVal):
      evalAexp mem (foo :: σ) (incrAVar 0 a) ≡ evalAexp mem σ a.
    Proof.
      induction a; try constructor; simpl;
        (try rewrite evalMexp_incrMVar;
         try rewrite evalNexp_incrNVar;
         try reflexivity);
        (try rewrite IHa; try reflexivity);
        (try rewrite IHa1, IHa2;reflexivity).
    Qed.

  End IncrEval.

End MDSigmaHCOLEval.
