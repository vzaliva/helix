(* Deep embedding of a subset of SigmaHCOL *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
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
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.

Require Import ITree.ITree.
Require Import ITree.Events.Exception.
Require Import ITree.Eq.
Require Import ITree.Interp.InterpFacts.
Require Import ITree.Events.State.
Require Import ITree.Events.StateFacts.
Require Import ITree.Basics.CategoryTheory.
Require Import ITree.Basics.CategoryOps.
Require Import ITree.Basics.CategoryKleisli.
Require Import ITree.Basics.CategoryKleisliFacts.
Require Import ITree.Core.KTree.
Require Import ITree.Core.KTreeFacts.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.misc.decision.

Global Open Scope nat_scope.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Import MonadNotation.
Local Open Scope monad_scope.

Module MDSigmaHCOLITree (Import CT : CType) (Import ESig:MDSigmaHCOLEvalSig CT).

  Include MDSigmaHCOLEval CT ESig.

  Local Open Scope string_scope.

  Variant MemEvent: Type -> Type :=
  | MemLU  (msg: string) (id: mem_block_id): MemEvent mem_block
  | MemSet (id: mem_block_id) (bk: mem_block): MemEvent unit
  | MemAlloc (size: nat): MemEvent mem_block_id
  | MemFree (id: mem_block_id): MemEvent unit.
  Definition StaticFailE := exceptE string.
  Definition StaticThrow (msg: string): StaticFailE void := Throw msg.
  Definition DynamicFailE := exceptE string.
  Definition DynamicThrow (msg: string): DynamicFailE void := Throw msg.
  Definition Event := MemEvent +' StaticFailE +' DynamicFailE.

  Definition Sfail {A: Type} {E} `{DynamicFailE -< E} (msg: string): itree E A :=
    vis (Throw msg) (fun (x: void) => match x with end).

  Definition Dfail {A: Type} {E} `{DynamicFailE -< E} (msg: string): itree E A :=
    vis (Throw msg) (fun (x: void) => match x with end).

  Definition lift_Serr {A} {E} `{StaticFailE -< E} (m:err A) : itree E A :=
    match m with
    | inl x => throw x
    | inr x => ret x
    end.

  Definition lift_Derr {A} {E} `{DynamicFailE -< E} (m:err A) : itree E A :=
    match m with
    | inl x => throw x
    | inr x => ret x
    end.

  Definition denotePexp (σ: evalContext) (exp:PExpr): itree Event (mem_block_id) :=
    lift_Serr (evalPexp σ exp).

  Definition denoteMexp (σ: evalContext) (exp:MExpr): itree Event (mem_block) :=
    match exp with
    | @MPtrDeref p =>
      bi <- denotePexp σ p ;;
      trigger (MemLU "MPtrDeref" bi)
    | @MConst t => ret t
    end.

  Definition denoteNexp (σ: evalContext) (e: NExpr): itree Event nat :=
    lift_Serr (evalNexp σ e).

  Fixpoint denoteAexp (σ: evalContext) (e:AExpr): itree Event t :=
    match e with
    | AVar i =>
      v <- lift_Serr (context_lookup "AVar not found" σ i);;
        (match v with
         | DSHCTypeVal x => ret x
         | _ => Sfail "invalid AVar type"
         end)
    | AConst x => ret x
    | AAbs x =>  liftM CTypeAbs (denoteAexp σ x)
    | APlus a b => liftM2 CTypePlus (denoteAexp σ a) (denoteAexp σ b)
    | AMult a b => liftM2 CTypeMult (denoteAexp σ a) (denoteAexp σ b)
    | AMin a b => liftM2 CTypeMin (denoteAexp σ a) (denoteAexp σ b)
    | AMax a b => liftM2 CTypeMax (denoteAexp σ a) (denoteAexp σ b)
    | AMinus a b =>
      a' <- (denoteAexp σ a) ;;
         b' <- (denoteAexp σ b) ;;
         ret (CTypeSub a' b')
    | ANth m i =>
      m' <- (denoteMexp σ m) ;;
      i' <- denoteNexp σ i ;;
         (* Instead of returning error we default to zero here.
          This situation should never happen for programs
          refined from MSHCOL which ensure bounds via
          dependent types. So DHCOL programs should
          be correct by construction *)
      (match mem_lookup i' m' with
       | Some v => ret v
       | None => ret CTypeZero
       end)
    | AZless a b => liftM2 CTypeZLess (denoteAexp σ a) (denoteAexp σ b)
    end.

  Definition denoteIUnCType (σ: evalContext) (f: AExpr)
             (i:nat) (a:t): itree Event t :=
    denoteAexp (DSHCTypeVal a :: DSHnatVal i :: σ) f.

  Definition denoteIBinCType (σ: evalContext) (f: AExpr)
             (i:nat) (a b:t): itree Event t :=
    denoteAexp (DSHCTypeVal b :: DSHCTypeVal a :: DSHnatVal i :: σ) f.

  Definition denoteBinCType (σ: evalContext) (f: AExpr)
             (a b:t): itree Event t :=
    denoteAexp (DSHCTypeVal b :: DSHCTypeVal a :: σ) f.

  Fixpoint denoteDSHIMap
           (n: nat)
           (f: AExpr)
           (σ: evalContext)
           (x y: mem_block) : itree Event (mem_block)
    :=
      match n with
      | O => ret y
      | S n =>
        v <- lift_Derr (mem_lookup_err "Error reading memory denoteDSHIMap" n x) ;;
        v' <- denoteIUnCType σ f n v ;;
        denoteDSHIMap n f σ x (mem_add n v' y)
      end.

  Fixpoint denoteDSHMap2
           (n: nat)
           (f: AExpr)
           (σ: evalContext)
           (x0 x1 y: mem_block) : itree Event (mem_block)
    :=
      match n with
      | O => ret y
      | S n =>
        v0 <- lift_Derr (mem_lookup_err ("Error reading 1st arg memory in denoteDSHMap2 @" ++ (string_of_nat n) ++ " in " ++ string_of_mem_block_keys x0) n x0) ;;
        v1 <- lift_Derr (mem_lookup_err ("Error reading 2nd arg memory in denoteDSHMap2 @" ++ (string_of_nat n) ++ " in " ++ string_of_mem_block_keys x1) n x1) ;;
        v' <- denoteBinCType σ f v0 v1 ;;
        denoteDSHMap2 n f σ x0 x1 (mem_add n v' y)
      end.

  Fixpoint denoteDSHBinOp
           (n off: nat)
           (f: AExpr)
           (σ: evalContext)
           (x y: mem_block) : itree Event (mem_block)
    :=
      match n with
      | O => ret y
      | S n =>
        v0 <- lift_Derr (mem_lookup_err "Error reading 1st arg memory in denoteDSHBinOp" n x) ;;
        v1 <- lift_Derr (mem_lookup_err "Error reading 2nd arg memory in denoteDSHBinOp" (n+off) x) ;;
        v' <- denoteIBinCType σ f n v0 v1 ;;
        denoteDSHBinOp n off f σ x (mem_add n v' y)
      end.

  Fixpoint denoteDSHPower
           (σ: evalContext)
           (n: nat)
           (f: AExpr)
           (x y: mem_block)
           (xoffset yoffset: nat)
    : itree Event (mem_block)
    :=
      match n with
      | O => ret y
      | S p =>
        xv <- lift_Derr (mem_lookup_err "Error reading 'xv' memory in denoteDSHBinOp" 0 x) ;;
        yv <- lift_Derr (mem_lookup_err "Error reading 'yv' memory in denoteDSHBinOp" 0 y) ;;
        v' <- denoteBinCType σ f xv yv ;;
        denoteDSHPower σ p f x (mem_add 0 v' y) xoffset yoffset
      end.

  Fixpoint denoteDSHOperator
           (σ: evalContext)
           (op: DSHOperator): itree Event unit
    :=
        match op with
        | DSHNop => ret tt

        | DSHAssign (x_p, src_e) (y_p, dst_e) =>
          x_i <- denotePexp σ x_p ;;
          y_i <- denotePexp σ y_p ;;
          x <- trigger (MemLU "Error looking up 'x' in DSHAssign" x_i) ;;
          y <- trigger (MemLU "Error looking up 'y' in DSHAssign" y_i) ;;
          src <- denoteNexp σ src_e ;;
          dst <- denoteNexp σ dst_e ;;
          v <- lift_Derr (mem_lookup_err "Error looking up 'v' in DSHAssign" src x) ;;
          trigger (MemSet y_i (mem_add dst v y))

        | @DSHIMap n x_p y_p f =>
          x_i <- denotePexp σ x_p ;;
              y_i <- denotePexp σ y_p ;;
              x <- trigger (MemLU "Error looking up 'x' in DSHIMap" x_i) ;;
              y <- trigger (MemLU "Error looking up 'y' in DSHIMap" y_i) ;;
              y' <- denoteDSHIMap n f σ x y ;;
              trigger (MemSet y_i y')

        | @DSHMemMap2 n x0_p x1_p y_p f =>
          x0_i <- denotePexp σ x0_p ;;
               x1_i <- denotePexp σ x1_p ;;
               y_i <- denotePexp σ y_p ;;
               x0 <- trigger (MemLU "Error looking up 'x0' in DSHMemMap2" x0_i) ;;
               x1 <- trigger (MemLU "Error looking up 'x1' in DSHMemMap2" x1_i) ;;
               y <- trigger (MemLU "Error looking up 'y' in DSHMemMap2" y_i) ;;
               y' <- denoteDSHMap2 n f σ x0 x1 y ;;
               trigger (MemSet y_i y')
        | @DSHBinOp n x_p y_p f =>
          x_i <- denotePexp σ x_p ;;
              y_i <- denotePexp σ y_p ;;
              x <- trigger (MemLU "Error looking up 'x' in DSHBinOp" x_i) ;;
              y <- trigger (MemLU "Error looking up 'y' in DSHBinOp" y_i) ;;
              y' <- denoteDSHBinOp n n f σ x y ;;
              trigger (MemSet y_i y')

        | DSHPower ne (x_p,xoffset) (y_p,yoffset) f initial =>
          x_i <- denotePexp σ x_p ;;
          y_i <- denotePexp σ y_p ;;
          x <- trigger (MemLU "Error looking up 'x' in DSHPower" x_i) ;;
          y <- trigger (MemLU "Error looking up 'y' in DSHPower" y_i) ;;
          n <- denoteNexp σ ne ;; (* [n] denoteuated once at the beginning *)
          let y' := mem_add 0 initial y in
          xoff <- denoteNexp σ xoffset ;;
          yoff <- denoteNexp σ yoffset ;;
          y'' <- denoteDSHPower σ n f x y' xoff yoff ;;
          trigger (MemSet y_i y'')

        | DSHLoop n body =>
          iter (fun (p: nat) =>
                  if EqNat.beq_nat p n
                  then ret (inr tt)
                  else denoteDSHOperator (DSHnatVal p :: σ) body;;
                       ret (inl (S p))
                  ) 0

        | DSHAlloc size body =>
          t_i <- trigger (MemAlloc size) ;;
          trigger (MemSet t_i (mem_empty)) ;;
          denoteDSHOperator (DSHPtrVal t_i :: σ) body ;;
          trigger (MemFree t_i)

        | DSHMemInit size y_p value =>
          y_i <- denotePexp σ y_p ;;
          y <- trigger (MemLU "Error looking up 'y' in DSHMemInit" y_i) ;;
          let y' := mem_union (mem_const_block size value) y in
          trigger (MemSet y_i y')

       | DSHMemCopy size x_p y_p =>
          x_i <- denotePexp σ x_p ;;
          y_i <- denotePexp σ y_p ;;
          x <- trigger (MemLU "Error looking up 'x' in DSHMemCopy" x_i) ;;
          y <- trigger (MemLU "Error looking up 'y' in DSHMemCopy" y_i) ;;
          let y' := mem_union x y in
          trigger (MemSet y_i y')

       | DSHSeq f g =>
          denoteDSHOperator σ f ;; denoteDSHOperator σ g
      end.

  Definition pure_state {S E} : E ~> Monads.stateT S (itree E)
    := fun _ e s => Vis e (fun x => Ret (s, x)).

  Definition Mem_handler: MemEvent ~> Monads.stateT memory (itree (StaticFailE +' DynamicFailE)) :=
    fun T e mem =>
      match e with
      | MemLU msg id  => lift_Derr (Functor.fmap (fun x => (mem,x)) (memory_lookup_err msg mem id))
      | MemSet id blk => ret (memory_set mem id blk, tt)
      | MemAlloc size => ret (mem, memory_next_key mem)
      | MemFree id    => ret (memory_remove mem id, tt)
      end.

  Definition interp_Mem: itree Event ~> Monads.stateT memory (itree (StaticFailE +' DynamicFailE)) :=
    interp_state (case_ Mem_handler pure_state).
  Arguments interp_Mem {T} _ _.

  Section Eval_Denote_Equiv.

    Ltac state_step :=
      match goal with
      | |- interp_state _ (ITree.bind _ _) _ ≈ _ => rewrite interp_state_bind
      | |- ITree.bind (ITree.bind _ _) _ ≈ _ => rewrite bind_bind
      | |- ITree.bind (Vis _ _) _ ≈ _ => rewrite bind_vis
      | |- ITree.bind (Ret _) _ ≈ _ => rewrite bind_ret_l
      | |- context[interp_state _ (Ret _) _] => rewrite interp_state_ret
      | |- context[interp_state _ (trigger _) _] => rewrite interp_state_trigger
      | |- context[interp_state _ (vis _ _) _] => rewrite interp_state_vis
      | |- context[Tau _] => rewrite tau_eutt
      end.

    Ltac state_steps := cbn; repeat (state_step; cbn).

    Ltac inv_sum :=
      match goal with
      | h: inl _ ≡ inl _ |-  _ => inv h
      | h: inr _ ≡ inr _ |-  _ => inv h
      end.

    Ltac inv_option :=
      match goal with
      | h: Some _ ≡ Some _ |-  _ => inv h
      end.

    Ltac inv_mem_lookup_err :=
      unfold mem_lookup_err, trywith in *;
      break_match_hyp; cbn in *; try (inl_inr || inv_sum || inv_sum).

    Ltac inv_memory_lookup_err :=
      unfold memory_lookup_err, trywith in *;
      break_match_hyp; cbn in *; try (inl_inr || inv_sum || inv_sum).

    Ltac inv_memory_lookup_err_H H :=
      unfold memory_lookup_err, trywith in H;
      break_match_hyp; cbn in H; try (inl_inr || inv_sum || inv_sum).

    Ltac inv_eval := repeat (break_match_hyp; try (inl_inr || inv_sum || inv_sum || inv_option)); repeat try (inv_sum || inv_option).

    Ltac unfold_Mem := unfold interp_Mem in *; cbn in *; unfold denotePexp, denoteNexp, evalIUnCType, denoteIUnCType in *.

    Lemma Denote_Eval_Equiv_Mexp_Succeeds: forall mem σ e bk,
        evalMexp mem σ e ≡ inr bk ->
        eutt eq
             (interp_Mem (denoteMexp σ e) mem)
             (ret (mem, bk)).
    Proof.
      intros mem σ [] bk HEval; unfold_Mem.
      - cbn in *.
        inv_eval.
        state_steps.
        inv_memory_lookup_err.
        state_steps; reflexivity.
      - cbn in *.
        inv_eval.
        state_steps; reflexivity.
    Qed.

    Lemma Denote_Eval_Equiv_Aexp_Succeeds: forall mem σ e v,
        evalAexp mem σ e ≡ inr v ->
        eutt eq
             (interp_Mem (denoteAexp σ e) mem)
             (ret (mem, v)).
    Proof.
      induction e; intros res HEVal; unfold_Mem.
      - cbn in *.
        inv_eval.
        state_steps; reflexivity.
      - cbn in *.
        inv_eval.
        state_steps; reflexivity.
      - cbn in *.
        do 2 (break_match_hyp; try inl_inr).
        state_steps.
        apply Denote_Eval_Equiv_Mexp_Succeeds in Heqe.
        rewrite Heqe; cbn; state_steps.
        inv_eval; state_steps; reflexivity.
      - cbn in *.
        inv_eval.
        state_steps.
        rewrite IHe; eauto.
        state_steps; reflexivity.
      - cbn in *.
        inv_eval.
        state_steps.
        rewrite IHe1; eauto; state_steps.
        rewrite IHe2; eauto; state_steps.
        reflexivity.
      - cbn in *.
        inv_eval.
        state_steps.
        rewrite IHe1; eauto; state_steps.
        rewrite IHe2; eauto; state_steps.
        reflexivity.
      - cbn in *.
        inv_eval.
        state_steps.
        rewrite IHe1; eauto; state_steps.
        rewrite IHe2; eauto; state_steps.
        reflexivity.
      - cbn in *.
        inv_eval.
        state_steps.
        rewrite IHe1; eauto; state_steps.
        rewrite IHe2; eauto; state_steps.
        reflexivity.
      - cbn in *.
        inv_eval.
        state_steps.
        rewrite IHe1; eauto; state_steps.
        rewrite IHe2; eauto; state_steps.
        reflexivity.
      - cbn in *.
        inv_eval.
        state_steps.
        rewrite IHe1; eauto; state_steps.
        rewrite IHe2; eauto; state_steps.
        reflexivity.
    Qed.

    Definition interp_Mem_Fails {T} e mem :=
      exists msg',
        eutt eq (interp_Mem e mem) (Dfail msg') \/
        eutt eq (interp_Mem (T:=T) e mem) (Sfail msg').

    Lemma Denote_Eval_Equiv_Mexp_Fails: forall mem σ e msg,
        evalMexp mem σ e ≡ inl msg ->
        interp_Mem_Fails (denoteMexp σ e) mem.
    Proof.
      unfold interp_Mem_Fails.
      intros mem σ [] bk HEval; unfold_Mem.
      - inv_eval; state_steps.
        + eexists; left; state_steps.
          unfold throw, pure_state.
          state_steps.
          apply eqit_Vis; intros [].
        + eexists; left; state_steps.
          inv_memory_lookup_err.
          unfold throw, pure_state.
          state_steps.
          apply eqit_Vis; intros [].
      - inl_inr.
    Qed.

    Lemma Denote_Eval_Equiv_Aexp_Fails: forall mem σ e msg,
        evalAexp mem σ e ≡ inl msg ->
        interp_Mem_Fails (denoteAexp σ e) mem.
    Proof.
      unfold interp_Mem_Fails.
      intros mem σ e msg; induction e; intros HEVal; unfold_Mem.
      - eexists; right; cbn in *; inv_eval.
        + state_steps; cbn.
          unfold throw, pure_state.
          state_steps.
          apply eqit_Vis; intros [].
        + unfold Sfail, throw, pure_state.
          cbn; state_steps; cbn.
          apply eqit_Vis; intros [].
        + unfold Sfail, throw, pure_state.
          cbn; state_steps; cbn.
          apply eqit_Vis; intros [].
      - inl_inr.
      - inv_eval; state_steps.
        + apply Denote_Eval_Equiv_Mexp_Fails in Heqe; destruct Heqe as (?msg & [Heqe | Heqe]).
          * eexists; left.
            state_steps.
            unfold interp_Mem in Heqe; rewrite Heqe.
            unfold Dfail.
            state_steps.
            apply eqit_Vis; intros [].
          * eexists; right.
            state_steps.
            unfold interp_Mem in Heqe; rewrite Heqe.
            unfold Sfail.
            state_steps.
            apply eqit_Vis; intros [].
        + apply Denote_Eval_Equiv_Mexp_Succeeds in Heqe.
          unfold interp_Mem in Heqe.
          eexists.
          left.
          state_steps; rewrite Heqe; cbn; state_steps.
          unfold throw, pure_state.
          state_steps.
          apply eqit_Vis; intros [].
      - inv_eval.
        destruct IHe as [msg' [IHe | IHe]]; auto; eexists.
        left; state_steps; rewrite IHe; unfold Dfail; cbn; state_steps; apply eqit_Vis; intros [].
        right; state_steps; rewrite IHe; unfold Sfail; cbn; state_steps; apply eqit_Vis; intros [].
      - inv_eval.
        + destruct IHe1 as [msg1 [IHe | IHe]]; auto.
          * eexists; left; cbn; state_steps; rewrite IHe.
            unfold Dfail; cbn; state_steps; apply eqit_Vis; intros [].
          * eexists; right; cbn; state_steps; rewrite IHe.
            unfold Sfail; cbn; state_steps; apply eqit_Vis; intros [].
        + apply Denote_Eval_Equiv_Aexp_Succeeds in Heqe.
          destruct IHe2 as [msg2 [IHe | IHe]]; auto.
          * eexists; left; cbn; state_steps.
            rewrite Heqe; cbn; state_steps.
            rewrite IHe; unfold Dfail; cbn; state_steps; apply eqit_Vis; intros [].
          * eexists; right; cbn; state_steps.
            rewrite Heqe; cbn; state_steps.
            rewrite IHe; unfold Sfail; cbn; state_steps; apply eqit_Vis; intros [].
      - inv_eval.
        + destruct IHe1 as [msg1 [IHe | IHe]]; auto.
          * eexists; left; cbn; state_steps; rewrite IHe.
            unfold Dfail; cbn; state_steps; apply eqit_Vis; intros [].
          * eexists; right; cbn; state_steps; rewrite IHe.
            unfold Sfail; cbn; state_steps; apply eqit_Vis; intros [].
        + apply Denote_Eval_Equiv_Aexp_Succeeds in Heqe.
          destruct IHe2 as [msg2 [IHe | IHe]]; auto.
          * eexists; left; cbn; state_steps.
            rewrite Heqe; cbn; state_steps.
            rewrite IHe; unfold Dfail; cbn; state_steps; apply eqit_Vis; intros [].
          * eexists; right; cbn; state_steps.
            rewrite Heqe; cbn; state_steps.
            rewrite IHe; unfold Sfail; cbn; state_steps; apply eqit_Vis; intros [].
      - inv_eval.
        + destruct IHe1 as [msg1 [IHe | IHe]]; auto.
          * eexists; left; cbn; state_steps; rewrite IHe.
            unfold Dfail; cbn; state_steps; apply eqit_Vis; intros [].
          * eexists; right; cbn; state_steps; rewrite IHe.
            unfold Sfail; cbn; state_steps; apply eqit_Vis; intros [].
        + apply Denote_Eval_Equiv_Aexp_Succeeds in Heqe.
          destruct IHe2 as [msg2 [IHe | IHe]]; auto.
          * eexists; left; cbn; state_steps.
            rewrite Heqe; cbn; state_steps.
            rewrite IHe; unfold Dfail; cbn; state_steps; apply eqit_Vis; intros [].
          * eexists; right; cbn; state_steps.
            rewrite Heqe; cbn; state_steps.
            rewrite IHe; unfold Sfail; cbn; state_steps; apply eqit_Vis; intros [].
      - inv_eval.
        + destruct IHe1 as [msg1 [IHe | IHe]]; auto.
          * eexists; left; cbn; state_steps; rewrite IHe.
            unfold Dfail; cbn; state_steps; apply eqit_Vis; intros [].
          * eexists; right; cbn; state_steps; rewrite IHe.
            unfold Sfail; cbn; state_steps; apply eqit_Vis; intros [].
        + apply Denote_Eval_Equiv_Aexp_Succeeds in Heqe.
          destruct IHe2 as [msg2 [IHe | IHe]]; auto.
          * eexists; left; cbn; state_steps.
            rewrite Heqe; cbn; state_steps.
            rewrite IHe; unfold Dfail; cbn; state_steps; apply eqit_Vis; intros [].
          * eexists; right; cbn; state_steps.
            rewrite Heqe; cbn; state_steps.
            rewrite IHe; unfold Sfail; cbn; state_steps; apply eqit_Vis; intros [].
      - inv_eval.
        + destruct IHe1 as [msg1 [IHe | IHe]]; auto.
          * eexists; left; cbn; state_steps; rewrite IHe.
            unfold Dfail; cbn; state_steps; apply eqit_Vis; intros [].
          * eexists; right; cbn; state_steps; rewrite IHe.
            unfold Sfail; cbn; state_steps; apply eqit_Vis; intros [].
        + apply Denote_Eval_Equiv_Aexp_Succeeds in Heqe.
          destruct IHe2 as [msg2 [IHe | IHe]]; auto.
          * eexists; left; cbn; state_steps.
            rewrite Heqe; cbn; state_steps.
            rewrite IHe; unfold Dfail; cbn; state_steps; apply eqit_Vis; intros [].
          * eexists; right; cbn; state_steps.
            rewrite Heqe; cbn; state_steps.
            rewrite IHe; unfold Sfail; cbn; state_steps; apply eqit_Vis; intros [].
      - inv_eval.
        + destruct IHe1 as [msg1 [IHe | IHe]]; auto.
          * eexists; left; cbn; state_steps; rewrite IHe.
            unfold Dfail; cbn; state_steps; apply eqit_Vis; intros [].
          * eexists; right; cbn; state_steps; rewrite IHe.
            unfold Sfail; cbn; state_steps; apply eqit_Vis; intros [].
        + apply Denote_Eval_Equiv_Aexp_Succeeds in Heqe.
          destruct IHe2 as [msg2 [IHe | IHe]]; auto.
          * eexists; left; cbn; state_steps.
            rewrite Heqe; cbn; state_steps.
            rewrite IHe; unfold Dfail; cbn; state_steps; apply eqit_Vis; intros [].
          * eexists; right; cbn; state_steps.
            rewrite Heqe; cbn; state_steps.
            rewrite IHe; unfold Sfail; cbn; state_steps; apply eqit_Vis; intros [].
    Qed.

    Lemma Denote_Eval_Equiv_IMap_Succeeds: forall mem n f σ m1 m2 id,
        evalDSHIMap mem n f σ m1 m2 ≡ inr id ->
        eutt eq
             (interp_Mem (denoteDSHIMap n f σ m1 m2) mem)
             (ret (mem, id)).
    Proof.
      induction n as [| n IH]; cbn; intros f σ m1 m2 id HEval; unfold_Mem.
      - inv_eval; state_steps; reflexivity.
      - inv_eval; state_steps.
        inv_mem_lookup_err.
        state_steps.
        apply Denote_Eval_Equiv_Aexp_Succeeds in Heqe0.
        unfold_Mem.
        rewrite Heqe0; cbn; state_steps.
        rewrite IH; eauto.
        reflexivity.
    Qed.

    Lemma Denote_Eval_Equiv_IMap_Fails: forall mem n f σ m1 m2 msg,
        evalDSHIMap mem n f σ m1 m2 ≡ inl msg ->
        interp_Mem_Fails  (denoteDSHIMap n f σ m1 m2) mem.
    Proof.
      unfold interp_Mem_Fails.
      induction n as [| n IH]; cbn; intros f σ m1 m2 id HEval; unfold_Mem.
      - inl_inr.
      - inv_eval.
        + inv_mem_lookup_err; eexists; left.
          cbn; state_steps.
          unfold throw, pure_state.
          state_steps.
          unfold Dfail; cbn; state_steps; apply eqit_Vis; intros [].
        + inv_mem_lookup_err.
          apply Denote_Eval_Equiv_Aexp_Fails in Heqe0; destruct Heqe0 as (?msg & [Heqe0 | Heqe0]); unfold interp_Mem in Heqe0.
          * eexists; left; cbn; state_steps; rewrite Heqe0.
            unfold Dfail; cbn; state_steps; apply eqit_Vis; intros [].
          * eexists; left; cbn; state_steps; rewrite Heqe0.
            unfold Sfail; cbn; state_steps; apply eqit_Vis; intros [].
        + inv_mem_lookup_err.
          apply Denote_Eval_Equiv_Aexp_Succeeds in Heqe0.
          apply IH in HEval; destruct HEval as [msg' [EQ | EQ]]; eexists; [left | right].
          * state_steps; rewrite Heqe0; state_steps; rewrite EQ; reflexivity.
          * state_steps; rewrite Heqe0; state_steps; rewrite EQ; reflexivity.
    Qed.

    Lemma Denote_Eval_Equiv_BinCType_Succeeds: forall mem σ f i a b v,
        evalIBinCType mem σ f i a b ≡ inr v ->
        eutt eq
             (interp_Mem (denoteIBinCType σ f i a b) mem)
             (ret (mem, v)).
    Proof.
      unfold evalIBinCType, denoteIBinCType; intros.
      apply Denote_Eval_Equiv_Aexp_Succeeds in H; auto.
    Qed.

    Lemma Denote_Eval_Equiv_BinOp_Succeeds: forall mem n off σ f x y blk,
        evalDSHBinOp mem n off f σ x y ≡ inr blk ->
        eutt eq
             (interp_Mem (denoteDSHBinOp n off f σ x y) mem)
             (ret (mem, blk)).
    Proof.
      induction n as [| n IH]; cbn; intros off f σ x y blk HEval; unfold_Mem.
      - inv_eval; state_steps; reflexivity.
      - inv_eval; state_steps.
        do 2 inv_mem_lookup_err.
        state_steps.
        apply Denote_Eval_Equiv_BinCType_Succeeds in Heqe1; rewrite Heqe1; cbn; state_steps.
        rewrite IH; eauto; reflexivity.
    Qed.

    Definition denote_Loop_for_i_to_N σ body (N i: nat) :=
      iter (fun (p: nat) =>
              if EqNat.beq_nat p N
              then ret (inr tt)
              else denoteDSHOperator (DSHnatVal p :: σ) body;;
                   ret (inl (S p))
           ) i.

    Lemma denote_Loop_for_0_to_N:
      forall σ body N, denote_Loop_for_i_to_N σ body N 0 ≈ denoteDSHOperator σ (DSHLoop N body).
    Proof.
      unfold denote_Loop_for_i_to_N; reflexivity.
    Qed.

    Fixpoint eval_Loop_for_i_to_N σ body (N i: nat) mem fuel :=
      match N with
      | O => Some (ret mem)
      | S N =>
        if EqNat.beq_nat (S N) i then
          Some (ret mem)
        else
          match eval_Loop_for_i_to_N σ body N i mem fuel with
          | Some (inr mem) => evalDSHOperator (DSHnatVal (S N) :: σ) body mem fuel
          | Some (inl msg) => Some (inl msg)
          | None => None
          end
      end.

    Lemma eval_Loop_for_0_to_N:
      forall σ body N mem fuel, eval_Loop_for_i_to_N σ body N 0 mem fuel ≡ evalDSHOperator σ (DSHLoop N body) mem (S fuel).
    Proof.
      induction N as [| N IH]; intros mem fuel.
      - reflexivity.
      - unfold eval_Loop_for_i_to_N in *.
        destruct (PeanoNat.Nat.eqb (S N) 0) eqn:EQ.
        symmetry in EQ; apply beq_nat_eq in EQ; inv EQ.
        clear EQ.
        rewrite IH; clear IH.
        simpl evalDSHOperator at 3.
        admit. (* fuel a bit annoying *)
    Admitted.

    Lemma aux: forall σ n op fuel mem_i mem_f,
        evalDSHOperator σ (DSHLoop (S n) op) mem_i (S fuel) ≡ Some (inr mem_f) ->
        exists mem,
          evalDSHOperator (DSHnatVal n :: σ) op mem_i (S fuel) ≡ Some (inr mem) /\
          evalDSHOperator σ (DSHLoop n op) mem (S fuel) ≡ Some (inr mem_f).
    Admitted.

    (* Lemma loop_is_iter *)

    Theorem Denote_Eval_Equiv_Succeeds:
      forall (σ: evalContext) (op: DSHOperator) (mem: memory) (fuel: nat) (mem': memory),
        evalDSHOperator σ op mem fuel ≡ Some (inr mem') ->
        eutt eq (interp_Mem (denoteDSHOperator σ op) mem) (ret (mem', tt)).
    Proof.
      intros ? ? ? ? ? H; destruct fuel as [| fuel]; [inversion H |].
      revert σ mem' fuel mem H.
      induction op; intros σ mem fuel mem' HEval.
      - unfold_Mem; inv_eval; state_steps; reflexivity.
      - unfold_Mem; destruct src,dst.
        inv_eval.
        cbn; state_steps.
        rewrite Heqe1; cbn; state_steps.
        rewrite Heqe2; cbn; state_steps.
        rewrite Heqe5; cbn; state_steps.
        apply eqit_Ret; auto.
      - unfold_Mem; inv_eval.
        cbn.
        state_steps.
        rewrite Heqe1; cbn; state_steps.
        rewrite Heqe2; cbn; state_steps.
        apply Denote_Eval_Equiv_IMap_Succeeds in Heqe3.
        rewrite Heqe3; cbn; state_steps.
        apply eqit_Ret; auto.
      - unfold_Mem; inv_eval.
        cbn.
        state_steps.
        rewrite Heqe1; cbn; state_steps.
        rewrite Heqe2; cbn; state_steps.
        apply Denote_Eval_Equiv_BinOp_Succeeds in Heqe3; rewrite Heqe3; cbn; state_steps.
        reflexivity.
      - unfold_Mem; inv_eval.
        state_steps.
        rewrite Heqe2.
        state_steps.
        rewrite Heqe3.
        state_steps.
        rewrite Heqe4.
        state_steps.
        admit. (* Map2 case, need a lemma for it *)
      - unfold_Mem; inv_eval.
        state_steps.
        rewrite Heqe1; state_steps.
        rewrite Heqe2; state_steps.
        admit. (* Map2 case, need a lemma for it *)
      -

        (*
          The equivalence between both loops is non-trivial.
          The core of the problem is that the [evalContext] gets
          extended at each step with the current iteration index.
          This means that if you try to conduct naïvely the induction
          by unrolling, i.e. want to exploit simply that:
          [| loop (S n) body |] σ ~ [| body |] (0::σ);; [| loop n body |] σ
          You need to generalize your construct so that the remaining of
          the loop starts binding at 1 and not at 0 once again.

          It is done via [denote_Loop_for_i_to_N] on the denotation side,
          but we also need to do so on the Eval side.

          That is assuming that we did not get lost on the way.
         *)

    (*
      rewrite <- denote_Loop_from_0.
        generalize 0 at 1; intros N.
        revert mem mem' HEval.
        revert dependent σ.
        induction n as [| n IH]; intros σ mem mem' HEval; cbn.
        + unfold denote_Loop_for_i_to_N.
          cbn in HEval. inv_eval.
          clear IHop.
          unfold_Mem.
          match goal with
          | |- interp_state ?h (iter ?k 0) _ ≈ _ =>
            generalize (@iter_unfold _ (ktree _) _ _ _ sum _ _ _ nat unit k)
          end; intros EQ.
          specialize (EQ 0).
          rewrite EQ; clear EQ.
          cbn in *.
          state_steps.
          reflexivity.
        + unfold interp_Mem, denote_Loop_for_i_to_N.
          match goal with
          | |- interp_state ?h (iter ?k _) _ ≈ _ =>
            generalize (@iter_unfold _ (ktree _) _ _ _ sum _ _ _ nat unit k)
          end; intros EQ.
          specialize (EQ 0).
          rewrite EQ; clear EQ.
          cbn.
          state_steps.
          unfold interp_Mem in IH.
          rewrite interp_state_bind.
          apply aux in HEval; destruct HEval as (mem_aux & EQ1 & EQ2).
          rewrite IHop.
          {
            state_steps.
            simpl ret in IH.
            rewrite <- (IH σ mem mem_aux).
            {
              cbn; reflexivity.
            }
            auto.
          }



        induction n as [| n IH]; intros σ mem mem' HEval; cbn.
        + unfold denote_LoopN_at_i.
          cbn in HEval. inv_eval.
          clear IHop.
          unfold_Mem.
          match goal with
          | |- interp_state ?h (iter ?k 0) _ ≈ _ =>
            generalize (@iter_unfold _ (ktree _) _ _ _ sum _ _ _ nat unit k)
          end; intros EQ.
          specialize (EQ 0).
          rewrite EQ; clear EQ.
          cbn in *.
          state_steps.
          reflexivity.
        + unfold interp_Mem, denote_LoopN_at_i.
          match goal with
          | |- interp_state ?h (iter ?k _) _ ≈ _ =>
            generalize (@iter_unfold _ (ktree _) _ _ _ sum _ _ _ nat unit k)
          end; intros EQ.
          specialize (EQ (S n)).
          rewrite EQ; clear EQ.
          cbn.
          state_steps.
          unfold interp_Mem in IH.
          rewrite interp_state_bind.
          apply aux in HEval; destruct HEval as (mem_aux & EQ1 & EQ2).
          rewrite IHop.
          {
            state_steps.
            simpl ret in IH.
            rewrite <- (IH σ mem mem_aux).
            {
              unfold denote_LoopN_at_i.
              cbn; reflexivity.
            }
            auto.
          }


        rewrite <- denote_LoopN_at_N.
        generalize n at 1; intros N.
        revert mem mem' HEval.
        revert dependent σ.

        induction n as [| n IH]; intros σ mem mem' HEval; cbn.
        + unfold denote_LoopN_at_i.
          cbn in HEval. inv_eval.
          clear IHop.
          unfold_Mem.
          match goal with
          | |- interp_state ?h (iter ?k 0) _ ≈ _ =>
            generalize (@iter_unfold _ (ktree _) _ _ _ sum _ _ _ nat unit k)
          end; intros EQ.
          specialize (EQ 0).
          rewrite EQ; clear EQ.
          cbn in *.
          state_steps.
          reflexivity.
        + unfold interp_Mem, denote_LoopN_at_i.
          match goal with
          | |- interp_state ?h (iter ?k _) _ ≈ _ =>
            generalize (@iter_unfold _ (ktree _) _ _ _ sum _ _ _ nat unit k)
          end; intros EQ.
          specialize (EQ (S n)).
          rewrite EQ; clear EQ.
          cbn.
          state_steps.
          unfold interp_Mem in IH.
          rewrite interp_state_bind.
          apply aux in HEval; destruct HEval as (mem_aux & EQ1 & EQ2).
          rewrite IHop.
          {
            state_steps.
            simpl ret in IH.
            rewrite <- (IH σ mem mem_aux).
            {
              unfold denote_LoopN_at_i.
              cbn; reflexivity.
            }
            auto.
          }




        induction n as [| n IH]; intros σ mem mem' HEval; cbn.
        + cbn in HEval; inv_eval.
          clear IHop.
          unfold_Mem.
          match goal with
          | |- interp_state ?h (iter ?k 0) _ ≈ _ =>
            generalize (@iter_unfold _ (ktree _) _ _ _ sum _ _ _ nat unit k)
          end; intros EQ.
          specialize (EQ 0).
          rewrite EQ; clear EQ.
          cbn in *.
          state_steps.
          reflexivity.
        + unfold interp_Mem.
          match goal with
          | |- interp_state ?h (iter ?k _) _ ≈ _ =>
            generalize (@iter_unfold _ (ktree _) _ _ _ sum _ _ _ nat unit k)
          end; intros EQ.
          specialize (EQ (S n)).
          rewrite EQ; clear EQ.
          cbn.
          state_steps.
          unfold interp_Mem in IH.
          rewrite interp_state_bind.
          rewrite IHop.
          { state_steps.
            simpl ret in IH.
            specialize (IH σ mem mem').
            rewrite <- IH.
            cbn.
            {

            rewrite <- IH.

          unfold iter_unfold in Heqe.
          unfold iterative_unfold in Heqe.
          break_let.

          unfold KTree.iter, Iter_Kleisli, Basics.iter, MonadIter_itree.
          pose proof @interp_state_iter'.
          red in H.
          rewrite H.
          match goal with
          | |- Basics.iter ?body 0 mem ≈ _ =>
            erewrite (@iter_unfold _ (Kleisli (Monads.stateT _ (itree _))) _ _ _ sum _ _ _ nat unit body)
          end.

            rewrite (iter_unfold k)
          end.


          pose @iter_unfold.


          unfold KTree.iter. unfold Iter_Kleisli.
          rewrite interp_state_iter.
          match goal with
          | |- interp_state ?h (iter ?k 0) _ ≈ _ =>
pose (iter_unfold k)
          end.

          match goal with
          | |- interp_state ?h (iter ?k 0) _ ≈ _ =>
            generalize (interp_state_iter _ h k (fun _ m => Ret (m,inr ())))
          end.
          intros ?.

          Set Printing Implicit.
          rewrite iterative_unfold.
          rewrite interp_state_iter'.
          *)
    Admitted.

    Theorem Denote_Eval_Equiv_Fails:
      forall (σ: evalContext) (op: DSHOperator) (mem: memory) (fuel: nat) (msg:string),
        evalDSHOperator σ op mem fuel = Some (inl msg) ->
        interp_Mem_Fails (denoteDSHOperator σ op) mem.
    Proof.
      unfold interp_Mem_Fails.
    Admitted.

  End Eval_Denote_Equiv.

End MDSigmaHCOLITree.
