(* Deep embedding of a subset of SigmaHCOL *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Require Import Psatz.

Require Import Paco.paco.

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

Ltac state_step :=
  match goal with
  | |- interp_state _ (ITree.bind _ _) _ ≈ _ => rewrite interp_state_bind
  | |- ITree.bind (ITree.bind _ _) _ ≈ _ => rewrite bind_bind
  | |- ITree.bind (Vis _ _) _ ≈ _ => rewrite bind_vis
  | |- ITree.bind (Ret _) _ ≈ _ => rewrite bind_ret_l
  | |- context[interp_state _ (Ret _) _] => rewrite interp_state_ret
  | |- context[interp_state _ (trigger _) _] => rewrite interp_state_trigger
  | |- context[interp_state _ (vis _ _) _] => rewrite interp_state_vis
  | |- context[Tau _] => rewrite tau_euttge
  end.

Ltac state_steps' := cbn; repeat (state_step; cbn).

Ltac iter_unfold_pointed :=
  match goal with
  | |- context[interp_state ?h (iter ?k ?i) _ ≈ _] =>
    generalize (iter_unfold k); let EQ := fresh "EQ" in intros EQ; rewrite (EQ i); clear EQ
  end.

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

  Notation iter := (@iter _ (ktree _) sum _ _ _).

  Fixpoint denoteDSHOperator
           (σ: evalContext)
           (op: DSHOperator): itree Event unit :=
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
          denoteDSHOperator (DSHPtrVal t_i size :: σ) body ;;
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

    Ltac inv_sum :=
      match goal with
      | h: inl _ ≡ inl _ |-  _ => inv h
      | h: inr _ ≡ inr _ |-  _ => inv h
      | h: inl _ ≡ inr _ |-  _ => inv h
      | h: inr _ ≡ inl _ |-  _ => inv h
      end.

    Ltac inv_option :=
      match goal with
      | h: Some _ ≡ Some _ |-  _ => inv h
      | h: None   ≡ Some _ |-  _ => inv h
      | h: Some _ ≡ None   |-  _ => inv h
      | h: None   ≡ None   |-  _ => inv h
      end.

    Ltac inv_mem_lookup_err :=
      unfold mem_lookup_err, trywith in *;
      break_match_hyp; cbn in *; try (inl_inr || inv_sum || inv_sum).

    Ltac inv_memory_lookup_err :=
      unfold memory_lookup_err, trywith in *;
      break_match_hyp; cbn in *; try (inl_inr || inv_sum || inv_sum).

    Ltac state_steps :=
      cbn;
      repeat (
          ((match goal with
            | |- ITree.bind (lift_Derr _) _ ≈ _ => break_match_goal; inv_memory_lookup_err; inv_option
            | |- ITree.bind (lift_Serr _) _ ≈ _ => break_match_goal; inv_memory_lookup_err; inv_option
            | |- ITree.bind (interp_state _ (lift_Derr _) _) _ ≈ _ => break_match_goal; inv_option
            | |- ITree.bind (interp_state _ (lift_Serr _) _) _ ≈ _ => break_match_goal; inv_option
            end) || state_step); cbn).

    Ltac inv_eval := repeat (break_match_hyp; try (inl_inr || inv_sum || inv_option));
                     repeat try (inv_sum || inv_option);
                     repeat inv_memory_lookup_err;
                     repeat inv_mem_lookup_err.

    (* Ltac unfold_Mem := unfold interp_Mem in *; cbn in *; unfold denotePexp, denoteNexp, evalIUnCType, denoteIUnCType in *. *)
    Ltac unfold_Mem := unfold interp_Mem in *; cbn; unfold denotePexp, denoteNexp, evalIUnCType, denoteIUnCType in *.

    Lemma Denote_Eval_Equiv_Mexp_Succeeds: forall mem σ e bk,
        evalMexp mem σ e ≡ inr bk ->
        eutt eq
             (interp_Mem (denoteMexp σ e) mem)
             (ret (mem, bk)).
    Proof.
      intros mem σ [] bk HEval; unfold_Mem; cbn in HEval.
      - inv_eval; state_steps; reflexivity.
      - inv_eval; state_steps; reflexivity.
    Qed.

    Lemma Denote_Eval_Equiv_Aexp_Succeeds: forall mem σ e v,
        evalAexp mem σ e ≡ inr v ->
        eutt eq
             (interp_Mem (denoteAexp σ e) mem)
             (ret (mem, v)).
    Proof.
      induction e; intros res HEval; unfold_Mem; cbn in HEval;
        try now (inv_eval; state_steps;
                 ((rewrite IHe; eauto; state_steps) ||
                  (rewrite IHe1; eauto; state_steps; rewrite IHe2; eauto; state_steps) ||
                  idtac); reflexivity).
      do 2 (break_match_hyp; try inl_inr).
      state_steps.
      apply Denote_Eval_Equiv_Mexp_Succeeds in Heqe.
      rewrite Heqe; state_steps.
      inv_eval; state_steps; reflexivity.
    Qed.

    Definition interp_Mem_Fails {T} e mem :=
      exists msg',
        eutt eq (interp_Mem e mem) (Dfail msg') \/
        eutt eq (interp_Mem (T:=T) e mem) (Sfail msg').

    Ltac match_failure :=
      state_steps;
      unfold throw, pure_state, Dfail,Sfail; state_steps;
      apply eqit_Vis; intros [].

    Lemma Denote_Eval_Equiv_Mexp_Fails: forall mem σ e msg,
        evalMexp mem σ e ≡ inl msg ->
        interp_Mem_Fails (denoteMexp σ e) mem.
    Proof.
      unfold interp_Mem_Fails.
      intros mem σ [] bk HEval; cbn in HEval; unfold_Mem; cbn in HEval.
      - inv_eval; state_steps; eexists; left; state_steps; match_failure.
      - inl_inr.
    Qed.

    Lemma Denote_Eval_Equiv_Aexp_Fails: forall mem σ e msg,
        evalAexp mem σ e ≡ inl msg ->
        interp_Mem_Fails (denoteAexp σ e) mem.
    Proof.
      unfold interp_Mem_Fails.
      intros mem σ e msg; induction e; intros HEval; cbn in HEval; unfold_Mem; cbn in HEval.
      - eexists; right; cbn in *; inv_eval; state_steps; match_failure.
      - inl_inr.
      - inv_eval; state_steps.
        + apply Denote_Eval_Equiv_Mexp_Fails in Heqe; destruct Heqe as (?msg & [Heqe | Heqe]).
          * eexists; left; state_steps.
            unfold interp_Mem in Heqe; rewrite Heqe; state_steps; match_failure.
          * eexists; right; state_steps.
            unfold interp_Mem in Heqe; rewrite Heqe; match_failure.
        + apply Denote_Eval_Equiv_Mexp_Succeeds in Heqe.
          eexists; left.
          unfold interp_Mem in Heqe.
          state_steps; rewrite Heqe; cbn; state_steps; match_failure.
      - inv_eval.
        destruct IHe as [msg' [IHe | IHe]]; auto; eexists.
        left; state_steps; rewrite IHe; match_failure.
        right; state_steps; rewrite IHe; match_failure.
      - inv_eval.
        + destruct IHe1 as [msg1 [IHe | IHe]]; auto.
          * eexists; left; cbn; state_steps; rewrite IHe; match_failure.
          * eexists; right; cbn; state_steps; rewrite IHe; match_failure.
        + apply Denote_Eval_Equiv_Aexp_Succeeds in Heqe.
          destruct IHe2 as [msg2 [IHe | IHe]]; auto.
          * eexists; left; cbn; state_steps.
            rewrite Heqe; cbn; state_steps.
            rewrite IHe; match_failure.
          * eexists; right; cbn; state_steps.
            rewrite Heqe; cbn; state_steps.
            rewrite IHe; match_failure.
      - inv_eval.
        + destruct IHe1 as [msg1 [IHe | IHe]]; auto.
          * eexists; left; cbn; state_steps; rewrite IHe; match_failure.
          * eexists; right; cbn; state_steps; rewrite IHe; match_failure.
        + apply Denote_Eval_Equiv_Aexp_Succeeds in Heqe.
          destruct IHe2 as [msg2 [IHe | IHe]]; auto.
          * eexists; left; cbn; state_steps.
            rewrite Heqe; cbn; state_steps.
            rewrite IHe; match_failure.
          * eexists; right; cbn; state_steps.
            rewrite Heqe; cbn; state_steps.
            rewrite IHe; match_failure.
      - inv_eval.
        + destruct IHe1 as [msg1 [IHe | IHe]]; auto.
          * eexists; left; cbn; state_steps; rewrite IHe; match_failure.
          * eexists; right; cbn; state_steps; rewrite IHe; match_failure.
        + apply Denote_Eval_Equiv_Aexp_Succeeds in Heqe.
          destruct IHe2 as [msg2 [IHe | IHe]]; auto.
          * eexists; left; cbn; state_steps.
            rewrite Heqe; cbn; state_steps.
            rewrite IHe; match_failure.
          * eexists; right; cbn; state_steps.
            rewrite Heqe; cbn; state_steps.
            rewrite IHe; match_failure.
      - inv_eval.
        + destruct IHe1 as [msg1 [IHe | IHe]]; auto.
          * eexists; left; cbn; state_steps; rewrite IHe; match_failure.
          * eexists; right; cbn; state_steps; rewrite IHe; match_failure.
        + apply Denote_Eval_Equiv_Aexp_Succeeds in Heqe.
          destruct IHe2 as [msg2 [IHe | IHe]]; auto.
          * eexists; left; cbn; state_steps.
            rewrite Heqe; cbn; state_steps.
            rewrite IHe; match_failure.
          * eexists; right; cbn; state_steps.
            rewrite Heqe; cbn; state_steps.
            rewrite IHe; match_failure.
      - inv_eval.
        + destruct IHe1 as [msg1 [IHe | IHe]]; auto.
          * eexists; left; cbn; state_steps; rewrite IHe; match_failure.
          * eexists; right; cbn; state_steps; rewrite IHe; match_failure.
        + apply Denote_Eval_Equiv_Aexp_Succeeds in Heqe.
          destruct IHe2 as [msg2 [IHe | IHe]]; auto.
          * eexists; left; cbn; state_steps.
            rewrite Heqe; cbn; state_steps.
            rewrite IHe; match_failure.
          * eexists; right; cbn; state_steps.
            rewrite Heqe; cbn; state_steps.
            rewrite IHe; match_failure.
      - inv_eval.
        + destruct IHe1 as [msg1 [IHe | IHe]]; auto.
          * eexists; left; cbn; state_steps; rewrite IHe; match_failure.
          * eexists; right; cbn; state_steps; rewrite IHe; match_failure.
        + apply Denote_Eval_Equiv_Aexp_Succeeds in Heqe.
          destruct IHe2 as [msg2 [IHe | IHe]]; auto.
          * eexists; left; cbn; state_steps.
            rewrite Heqe; cbn; state_steps.
            rewrite IHe; match_failure.
          * eexists; right; cbn; state_steps.
            rewrite Heqe; cbn; state_steps.
            rewrite IHe; match_failure.
    Qed.

    Lemma Denote_Eval_Equiv_IMap_Succeeds: forall mem n f σ m1 m2 id,
        evalDSHIMap mem n f σ m1 m2 ≡ inr id ->
        eutt eq
             (interp_Mem (denoteDSHIMap n f σ m1 m2) mem)
             (ret (mem, id)).
    Proof.
      induction n as [| n IH]; cbn; intros f σ m1 m2 id HEval; cbn in HEval; unfold_Mem.
      - inv_eval; state_steps; reflexivity.
      - inv_eval; state_steps.
        rewrite Denote_Eval_Equiv_Aexp_Succeeds; eauto; state_steps.
        rewrite IH; eauto.
        reflexivity.
    Qed.

    Lemma Denote_Eval_Equiv_IMap_Fails: forall mem n f σ m1 m2 msg,
        evalDSHIMap mem n f σ m1 m2 ≡ inl msg ->
        interp_Mem_Fails  (denoteDSHIMap n f σ m1 m2) mem.
    Proof.
      unfold interp_Mem_Fails.
      induction n as [| n IH]; cbn; intros f σ m1 m2 id HEval; unfold_Mem; cbn in HEval.
      - inl_inr.
      - inv_eval.
        + eexists; left.
          state_steps; match_failure.
        + apply Denote_Eval_Equiv_Aexp_Fails in Heqe0; destruct Heqe0 as (?msg & [Heqe0 | Heqe0]); unfold interp_Mem in Heqe0.
          * eexists; left; cbn; state_steps; rewrite Heqe0; match_failure.
          * eexists; left; cbn; state_steps; rewrite Heqe0; match_failure.
        + apply Denote_Eval_Equiv_Aexp_Succeeds in Heqe0.
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
      eapply Denote_Eval_Equiv_Aexp_Succeeds; eauto.
    Qed.

    Lemma Denote_Eval_Equiv_BinCType_Fails: forall mem σ f i a b msg,
        evalIBinCType mem σ f i a b ≡ inl msg ->
        interp_Mem_Fails (denoteIBinCType σ f i a b) mem.
    Proof.
      unfold evalIBinCType, denoteIBinCType; intros.
      eapply Denote_Eval_Equiv_Aexp_Fails; eauto.
    Qed.

    Lemma Denote_Eval_Equiv_BinOp_Succeeds: forall mem n off σ f x y blk,
        evalDSHBinOp mem n off f σ x y ≡ inr blk ->
        eutt eq
             (interp_Mem (denoteDSHBinOp n off f σ x y) mem)
             (ret (mem, blk)).
    Proof.
      induction n as [| n IH]; cbn; intros off f σ x y blk HEval; unfold_Mem; cbn in HEval.
      - inv_eval; state_steps; reflexivity.
      - inv_eval; state_steps.
        apply Denote_Eval_Equiv_BinCType_Succeeds in Heqe1; rewrite Heqe1; cbn; state_steps.
        rewrite IH; eauto; reflexivity.
    Qed.

    Lemma Denote_Eval_Equiv_BinOp_Fails: forall mem n off σ f x y msg,
        evalDSHBinOp mem n off f σ x y ≡ inl msg ->
        interp_Mem_Fails (denoteDSHBinOp n off f σ x y) mem.
    Proof.
      unfold interp_Mem_Fails.
      induction n as [| n IH]; cbn; intros off σ f x y msg HEval; unfold_Mem; cbn in HEval.
      - inv_eval.
      - inv_eval; try (eexists; left; state_steps; match_failure).
        edestruct Denote_Eval_Equiv_BinCType_Fails as [? [H|H]]; eauto;
          eexists; [left | right]; state_steps; rewrite H; match_failure.
        apply Denote_Eval_Equiv_BinCType_Succeeds in Heqe1;
          edestruct IH as [? [H|H]]; eauto;
            eexists; [left | right]; state_steps; rewrite Heqe1; state_steps; rewrite H; match_failure.
    Qed.

    Definition denote_Loop_for_i_to_N σ body (i N: nat) :=
      iter (fun (p: nat) =>
              if EqNat.beq_nat p N
              then ret (inr tt)
              else denoteDSHOperator (DSHnatVal p :: σ) body;;
                   ret (inl (S p))
           ) i.

    Lemma denote_Loop_for_0_to_N:
      forall σ body N, denote_Loop_for_i_to_N σ body 0 N ≈ denoteDSHOperator σ (DSHLoop N body).
    Proof.
      unfold denote_Loop_for_i_to_N; reflexivity.
    Qed.

    (* loop over [i .. N)
       Some boundary cases:
       - i<N => either [Some _] or [None] if runs out of fuel
       - i>N => same as [eval_Loop_for_0_to_N]
       - N=0 =>
         - fuel=0 => [None]
         - fuel>0 => [Some (ret mem)] no-op
       - i=N =>
         - fuel=0 => [None]
         - fuel>0 => [Some (ret mem)] no-op

      NOTE: Struct [{struct N}] works instead of [{struct fuel}] here as well.
     *)
    Fixpoint eval_Loop_for_i_to_N σ body (i N: nat) mem fuel {struct fuel} :=
      match fuel with
      | O => None
      | S fuel =>
             match N with
             | O => Some (ret mem)
             | S N =>
               if EqNat.beq_nat i (S N) then
                 Some (ret mem)
               else
                 match eval_Loop_for_i_to_N σ body i N mem fuel with
                 | Some (inr mem) => evalDSHOperator (DSHnatVal N :: σ) body mem fuel
                 | Some (inl msg) => Some (inl msg)
                 | None => None
                 end
             end
      end.

    (* TODO : MOVE THIS TO ITREE *)
    Instance eutt_interp_state_eq {E F: Type -> Type} {S : Type}
             (h : E ~> Monads.stateT S (itree F)) :
      Proper (eutt eq ==> eq ==> eutt eq) (@interp_state E (itree F) S _ _ _ h R).
    Proof.
      repeat intro. subst. revert_until R.
      einit. ecofix CIH. intros.

      rewrite !unfold_interp_state. punfold H0. red in H0.
      induction H0; intros; subst; simpl; pclearbot.
      - eret.
      - etau.
      - ebind. econstructor; [reflexivity|].
        intros; subst.
        etau. ebase.
      - rewrite tau_euttge, unfold_interp_state; eauto.
      - rewrite tau_euttge, unfold_interp_state; eauto.
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
          repeat break_match_hyp; simpl in H; subst; try inv_option.
          erewrite IHn; eauto; reflexivity.
          erewrite IHn; eauto.
          setoid_rewrite IHop; eauto.
      -
        (* Alloc *)
        intros.
        destruct fuel.
        +
          simpl in H; some_none.
        +
          simpl in H.
          repeat break_match_hyp.
          * inv_option.
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
            apply IHop1 in Heqo; clear IHop1; inv_option.
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

    Lemma eval_Loop_for_N_to_N: forall fuel σ op N mem,
        eval_Loop_for_i_to_N σ op N N mem (S fuel) ≡ Some (ret mem).
    Proof.
      intros fuel σ op [| N] mem; [reflexivity |].
      simpl; rewrite Nat.eqb_refl; reflexivity.
    Qed.

    Lemma eval_Loop_for_i_to_N_invert: forall σ i N op fuel mem_i mem_f,
        i < N ->
        eval_Loop_for_i_to_N σ op i N mem_i fuel ≡ Some (inr mem_f) ->
        exists mem_aux,
          evalDSHOperator (DSHnatVal i :: σ) op mem_i fuel ≡ Some (inr mem_aux) /\
          eval_Loop_for_i_to_N σ op (S i) N mem_aux fuel ≡ Some (inr mem_f).
    Proof.
      (* This proof is surprisingly painful to go through *)
      intros.
      (* Induction on the number of steps remaining *)
      remember (N - i) as k.
      revert σ fuel i N Heqk mem_i mem_f H0 H.
      induction k as [| k IH]; intros σ fuel i N EQ mem_i mem_f Heval ineq; [lia |].

      (* N > 0 for us to be able to take a step *)
      destruct N as [| N]; [lia |].
      (* We got some fuel since the computation succeeded *)
      destruct fuel as [| fuel]; [inv Heval |].
      (* We can now reduce *)
      simpl in Heval.

      (* We know there's still a step to be taken *)
      destruct (i =? S N)%nat eqn:EQ'; [apply beq_nat_true in EQ'; lia | apply beq_nat_false in EQ'].
      (* And that the recursive call succeeded since the computation did *)
      destruct (eval_Loop_for_i_to_N σ op i N mem_i fuel) eqn: HEval'; [| inv Heval].
      destruct e; inv Heval.

      (* Now there are two cases:
         either a single step was remaining and we should be able to conclude directly;
         or more were remaining, and we should be able to conclude by induction
       *)

      destruct (i =? N)%nat eqn: EQ''; [apply beq_nat_true in EQ''; subst; clear IH |].
      - clear EQ' EQ ineq.
        destruct fuel as [| fuel]; [inv HEval' |].
        rewrite eval_Loop_for_N_to_N in HEval'.
        setoid_rewrite eval_Loop_for_N_to_N.
        inv HEval'.
        exists mem_f.
        split; [apply evalDSHOperator_fuel_monotone; auto | auto ].
      - apply IH in HEval'; [| lia | apply beq_nat_false in EQ''; lia].
        destruct HEval' as (mem_aux & STEP & TAIL).
        exists mem_aux; split; [apply evalDSHOperator_fuel_monotone; auto |].
        cbn; rewrite EQ'', TAIL; auto.
    Qed.

    Lemma eval_Loop_for_i_to_N_i_gt_N σ op i N fuel mem:
      i > N ->
      eval_Loop_for_i_to_N σ op i N mem fuel ≡ eval_Loop_for_i_to_N σ op 0 N mem fuel.
    Proof.
      revert fuel.
      induction N; intros.
      +
        destruct fuel;reflexivity.
      +
        destruct fuel; [ reflexivity|].
        cbn.
        break_if; [apply beq_nat_true in Heqb; lia| ].
        apply beq_nat_false in Heqb.
        rewrite IHN.
        reflexivity.
        lia.
    Qed.

    Lemma eval_Loop_for_0_to_N:
      forall σ body N mem fuel,
        eval_Loop_for_i_to_N σ body 0 N mem fuel ≡ evalDSHOperator σ (DSHLoop N body) mem fuel.
    Proof.
      induction N as [| N IH]; intros mem fuel.
      - destruct fuel; reflexivity.
      - destruct fuel as [| fuel ]; [reflexivity |].
        simpl evalDSHOperator.
        simpl.
        rewrite <- IH.
        reflexivity.
    Qed.

    Lemma eval_Loop_for_i_to_N_fuel_monotone:
      forall res σ op i N fuel mem,
        eval_Loop_for_i_to_N σ op i N mem fuel ≡ Some res ->
        eval_Loop_for_i_to_N σ op i N mem (S fuel) ≡ Some res.
    Proof.
      intros res σ op i N fuel mem H.
      revert H.
      revert res σ i fuel.
      induction N; intros.
      -
        destruct fuel; cbn in *; [some_none| apply H].
      -
        cbn.
        destruct fuel; [cbn in H; some_none|].
        break_if.
        +
          apply beq_nat_true in Heqb.
          subst.
          cbn in H.
          rewrite Nat.eqb_refl in H.
          apply H.
        +
          repeat break_match_goal; subst; cbn in H; rewrite Heqb in H.
          *
            unfold err in *.
            rewrite <- Heqo.
            repeat break_match_hyp; subst.
            --
              rewrite <- H.
              apply IHN.
              apply Heqo0.
            --
              apply IHN in Heqo0.
              rewrite Heqo0 in Heqo.
              inv Heqo.
            --
              some_none.
          *
            unfold err in *.
            repeat break_match_hyp; subst.
            --
              apply IHN in Heqo0.
              rewrite Heqo0 in Heqo.
              inv Heqo.
            --
              apply IHN in Heqo0.
              rewrite Heqo0 in Heqo.
              inv Heqo.
              apply evalDSHOperator_fuel_monotone.
              apply H.
            --
              some_none.
          *
            exfalso.
            break_match_hyp.
            --
              apply IHN in Heqo0.
              some_none.
            --
              some_none.
    Qed.

    Lemma eval_Loop_for_i_to_N_fuel_monotone_gt:
      forall res σ op i N fuel fuel' mem,
        fuel'>fuel ->
        eval_Loop_for_i_to_N σ op i N mem fuel ≡ Some res ->
        eval_Loop_for_i_to_N σ op i N mem fuel' ≡ Some res.
    Proof.
      intros H.
      intros σ op i N fuel fuel' mem H0 H1.
      remember (fuel'-fuel) as d.
      assert(F: fuel' ≡ fuel + d) by lia.
      subst fuel'.
      clear H0 Heqd.
      induction d.
      -
        replace (fuel + 0) with fuel by lia.
        auto.
      -
        replace (fuel + S d) with (S (fuel + d)) by lia.
        apply eval_Loop_for_i_to_N_fuel_monotone.
        auto.
    Qed.

    Lemma Loop_is_Iter_aux:
      ∀ (op : DSHOperator)
        (IHop: ∀ (σ : evalContext) (mem' : memory) (fuel : nat) (mem : memory),
            evalDSHOperator σ op mem (S fuel) ≡ Some (inr mem')
            → interp_Mem (denoteDSHOperator σ op) mem ≈ ret (mem', ()))

        (i N: nat)
        (σ : evalContext) (mem : memory) (fuel : nat) (mem' : memory),
        i <= N ->
        eval_Loop_for_i_to_N σ op i N mem (S fuel) ≡ Some (inr mem')
        → interp_state (case_ Mem_handler pure_state) (denote_Loop_for_i_to_N σ op i N) mem ≈ ret (mem', ()).
    Proof.
      intros op IHop i N σ mem fuel mem' ineq HEval.
      remember (N - i) as k.
      revert Heqk σ mem mem' HEval.
      revert i ineq.
      induction k as [| k IH].
      - intros i ineq EQ.
        assert (N ≡ i) by lia; clear EQ ineq; subst.
        intros.
        destruct i as [| i].
        + cbn in HEval.
          inv HEval.
          unfold denote_Loop_for_i_to_N.
          iter_unfold_pointed.
          state_steps.
          reflexivity.
        + cbn in HEval.
          rewrite Nat.eqb_refl in HEval.
          inv HEval.
          unfold interp_Mem, denote_Loop_for_i_to_N.
          iter_unfold_pointed.
          state_steps.
          rewrite Nat.eqb_refl.
          state_steps.
          reflexivity.
      - intros i ineq EQ σ mem mem' HEval.
        destruct N as [| N].
        + cbn in HEval; inv HEval.
          unfold denote_Loop_for_i_to_N.
          iter_unfold_pointed.
          state_steps.
          destruct (i =? 0)%nat eqn:EQ'; [clear EQ'| lia].
          state_steps; reflexivity.
        + destruct (i =? S N)%nat eqn:EQ'.
          * unfold eval_Loop_for_i_to_N in HEval; rewrite EQ' in HEval.
            inv HEval.
            unfold denote_Loop_for_i_to_N.
            iter_unfold_pointed.
            state_steps.
            rewrite EQ'.
            state_steps; reflexivity.
          * unfold denote_Loop_for_i_to_N.
            iter_unfold_pointed.
            state_steps.
            rewrite EQ'; state_steps.
            rewrite interp_state_bind.
            state_steps.
            apply beq_nat_false in EQ'.
            apply eval_Loop_for_i_to_N_invert in HEval; [| lia].
            destruct HEval as (mem_aux & Eval_body & Eval_tail).
            apply evalDSHOperator_fuel_monotone in Eval_body.
            apply IHop in Eval_body.
            unfold interp_Mem in Eval_body.
            rewrite Eval_body.
            state_steps.
            apply IH in Eval_tail; try lia.
            rewrite Eval_tail.
            reflexivity.
    Qed.

    Lemma Loop_is_Iter:
      ∀ (op : DSHOperator)
        (IHop: ∀ (σ : evalContext) (mem' : memory) (fuel : nat) (mem : memory),
            evalDSHOperator σ op mem (S fuel) ≡ Some (inr mem')
            → interp_Mem (denoteDSHOperator σ op) mem ≈ ret (mem', ()))
        (N: nat) (σ : evalContext) (mem : memory) (fuel : nat) (mem' : memory),
        evalDSHOperator σ (DSHLoop N op) mem (S fuel) ≡ Some (inr mem') ->
        interp_state (case_ Mem_handler pure_state) (denoteDSHOperator σ (DSHLoop N op)) mem ≈ ret (mem', ()).
    Proof.
      intros.
      rewrite <- eval_Loop_for_0_to_N, <- denote_Loop_for_0_to_N in *.
      eapply Loop_is_Iter_aux; eauto; lia.
    Qed.

    (* This is "natural" invert following implementation recursion *)
    Lemma eval_Loop_for_i_to_N_Fail_invert': forall σ i N op fuel mem msg,
        eval_Loop_for_i_to_N σ op i (S N) mem fuel ≡ Some (inl msg) ->

        eval_Loop_for_i_to_N σ op i N mem fuel ≡ Some (inl msg) \/
        (exists mem_aux, eval_Loop_for_i_to_N σ op i N mem fuel ≡ Some (inr mem_aux) /\
                    evalDSHOperator (DSHnatVal N :: σ) op mem_aux fuel ≡ Some (inl msg)).
    Proof.
      intros σ i N op fuel mem msg H.
      destruct fuel; [inv H|].
      cbn in H.
      break_if; [inv H|].
      repeat break_match_hyp.
      -
        left.
        inv H.
        apply eval_Loop_for_i_to_N_fuel_monotone.
        assumption.
      -
        right.
        subst.
        exists m.
        split.
        apply eval_Loop_for_i_to_N_fuel_monotone.
        assumption.
        apply evalDSHOperator_fuel_monotone.
        assumption.
      -
        some_none.
    Qed.

    Lemma eval_Loop_for_i_to_N_inl_at_i:
      ∀ (σ : list DSHVal) (i N : nat) (op : DSHOperator) (fuel : nat) (mem : memory),
        i < N
        → ∀ s : string,
          evalDSHOperator (DSHnatVal i :: σ) op mem fuel ≡ Some (inl s)
          → eval_Loop_for_i_to_N σ op i N mem (fuel+N-i) ≡ Some (inl s).
    Proof.
      intros σ i N op fuel mem ic s H.
      induction N.
      -
        inv ic.
      -
        replace (fuel + S N - i) with (S (fuel + N - i)) by lia.
        cbn.
        break_if; [apply beq_nat_true in Heqb; lia|].
        destruct (i =? N)%nat eqn:EN.
        +
          apply beq_nat_true in EN.
          subst i.
          clear IHN.
          repeat break_match_goal; subst.
          *
            apply eval_Loop_for_i_to_N_fuel_monotone in Heqo.
            rewrite  eval_Loop_for_N_to_N in Heqo.
            inv Heqo.
          *
            apply eval_Loop_for_i_to_N_fuel_monotone in Heqo.
            rewrite  eval_Loop_for_N_to_N in Heqo.
            inv Heqo.
            replace (fuel+N-N) with fuel by lia.
            apply H.
          *
            exfalso.
            destruct fuel ; [inv H|].
            replace (S fuel + N - N) with (S fuel) in Heqo by lia.
            rewrite eval_Loop_for_i_to_N_fuel_monotone with (res:=inl s) in Heqo.
            some_none.
            rewrite eval_Loop_for_N_to_N in Heqo.
            some_none.
        +
          repeat break_match_goal; subst.
          *
            apply IHN.
            apply beq_nat_false in EN.
            lia.
          *
            assert (ic1: i<N) by (apply beq_nat_false in EN; lia).
            specialize (IHN ic1).
            inv IHN.
          *
            exfalso.
            assert (ic1: i<N) by (apply beq_nat_false in EN; lia).
            specialize (IHN ic1).
            inv IHN.
    Qed.

    Lemma eval_Loop_for_i_to_N_inr_at_i:
          ∀ (σ : list DSHVal) (i N : nat) (op : DSHOperator) (fuel : nat)
            (mem : memory) (msg : string),
            S i < N
            → eval_Loop_for_i_to_N σ op i N mem fuel ≡ Some (inl msg)
            → ∀ m : memory,
                evalDSHOperator (DSHnatVal i :: σ) op mem fuel ≡ Some (inr m)
                → eval_Loop_for_i_to_N σ op (S i) N m fuel ≡ Some (inl msg).
    Proof.
      intros σ i N.
      remember (N - i) as k.
      revert σ i N Heqk.
      induction k as [| k IH]; intros σ i N Heqk op fuel mem msg ineq Heval m Hi; [lia |].
      destruct N as [| N]; [lia |].
      destruct fuel as [| fuel]; [inv Heval |].
      cbn in Heval.
      destruct (i =? S N)%nat eqn:EQ'; [apply beq_nat_true in EQ'; lia | apply beq_nat_false in EQ'].
      destruct (eval_Loop_for_i_to_N σ op i N mem fuel) eqn: HEval'; [| inv Heval].
      destruct e; inv Heval.
      -
        (* fail in loop [i] to [N] *)
        destruct (S i =? N)%nat eqn: EQ''; [apply beq_nat_true in EQ''; subst; clear IH |].
        +
          apply eval_Loop_for_i_to_N_fuel_monotone in HEval'.
          cbn in HEval'.
          break_if; [apply beq_nat_true in Heqb; lia|].
          repeat break_match_hyp; subst.
          *
            apply eval_Loop_for_i_to_N_fuel_monotone in Heqo.
            rewrite eval_Loop_for_N_to_N in Heqo.
            inv Heqo.
          *
            apply eval_Loop_for_i_to_N_fuel_monotone in Heqo.
            rewrite eval_Loop_for_N_to_N in Heqo.
            inv Heqo.
            apply evalDSHOperator_fuel_monotone in HEval'.
            congruence.
          *
            some_none.
        +
          eapply IH with (m:=m) in HEval'; [| lia | apply beq_nat_false in EQ''; lia | ].
          *
            cbn.
            break_if; [apply beq_nat_true in Heqb; lia|].
            rewrite HEval'.
            reflexivity.
          *
            (* fuel problem!*)
            admit.
      -
        (* succeeds in loop but fails at [N] *)
        clear IH.
        apply eval_Loop_for_i_to_N_invert in HEval'.
        2: lia.
        destruct HEval' as [mem_aux [STEP TAIL]].
        apply evalDSHOperator_fuel_monotone in STEP.
        cbn.
        break_if; [apply beq_nat_true in Heqb; lia|].
        rewrite Hi in STEP. inv STEP.
        rewrite TAIL.
        reflexivity.
    Admitted.

    Lemma eval_Loop_for_i_to_N_Fail_invert: forall σ i N op fuel mem msg,
        S i < N ->

        eval_Loop_for_i_to_N σ op i N mem fuel ≡ Some (inl msg) ->

        evalDSHOperator (DSHnatVal i :: σ) op mem fuel ≡ Some (inl msg) \/

        exists mem_aux,
          evalDSHOperator (DSHnatVal i :: σ) op mem fuel ≡ Some (inr mem_aux) /\
          eval_Loop_for_i_to_N σ op (S i) N mem_aux fuel ≡ Some (inl msg).
    Proof.
      intros σ i N op fuel mem msg ic H.

      destruct (evalDSHOperator (DSHnatVal i :: σ) op mem fuel) eqn:E.
      destruct e.
      -
        (* fails at [i] *)
        destruct (string_dec s msg) as [SE|NSE].
        +
          (* Same message *)
          left.
          subst.
          reflexivity.
        +
          (* different message *)
          exfalso.
          eapply eval_Loop_for_i_to_N_inl_at_i with (N:=N) in E; [|lia].
          eapply eval_Loop_for_i_to_N_fuel_monotone_gt in H.
          rewrite H in E.
          inv E.
          unfold not in NSE. contradict NSE. reflexivity.
          lia.
      -
        (* succeeds at [i] *)
        right.
        exists m.
        split; [reflexivity|].
        eapply eval_Loop_for_i_to_N_inr_at_i; eauto.
      -
        (* out of fuel at [i] *)
        exfalso.
        apply Nat.lt_succ_l in ic.
        assert(eval_Loop_for_i_to_N σ op i N mem fuel ≡ None).
        {
          clear H.
          induction N; intros.
          -
            inversion ic; intros.
          -
            destruct fuel.
            reflexivity.
            destruct (i =? N)%nat eqn:EN.
            *
              apply beq_nat_true in EN.
              subst i.
              clear IHN.
              cbn.
              break_if; [apply beq_nat_true in Heqb; lia|].
              clear Heqb.
              destruct fuel; [reflexivity|].
              rewrite eval_Loop_for_N_to_N.
              break_match; inv Heqe.
              apply evalDSHOperator_fuel_monotone_None, E.
            *
              assert (ic1: i<N) by (apply beq_nat_false in EN; lia).
              specialize (IHN ic1).
              cbn.
              break_if; [apply beq_nat_true in Heqb; lia|].
              repeat break_match_goal; subst.
              --
                apply eval_Loop_for_i_to_N_fuel_monotone in Heqo.
                some_none.
              --
                apply eval_Loop_for_i_to_N_fuel_monotone in Heqo.
                some_none.
              --
                reflexivity.
        }
        some_none.
    Qed.

    Lemma Denote_Eval_Equiv_DSHMap2_Succeeds:
      forall n (σ: evalContext) mem f m1 m2 m3 m4,
        evalDSHMap2 mem n f σ m1 m2 m3  ≡ inr m4 ->
        eutt eq
             (interp_Mem (denoteDSHMap2 n f σ m1 m2 m3) mem)
             (ret (mem, m4)).
    Proof.
      induction n as [| n IH]; intros σ mem f m1 m2 m3 m4 HEval; cbn in HEval.
      - unfold_Mem; inv_sum.
        state_steps; reflexivity.
      - unfold_Mem; inv_eval.
        state_steps.
        apply Denote_Eval_Equiv_Aexp_Succeeds in Heqe1; rewrite Heqe1; state_steps.
        rewrite IH; eauto; reflexivity.
    Qed.

    Lemma Denote_Eval_Equiv_DSHMap2_Fails:
      forall n (σ: evalContext) mem f m1 m2 m3 msg,
        evalDSHMap2 mem n f σ m1 m2 m3 ≡ inl msg ->
        interp_Mem_Fails (denoteDSHMap2 n f σ m1 m2 m3) mem.
    Proof.
      unfold interp_Mem_Fails.
      induction n as [| n IH]; cbn; intros σ mem f m1 m2 m3 msg HEval; unfold_Mem; cbn in HEval.
      - inv_eval.
      - inv_eval; try (eexists; left; state_steps; match_failure).
        edestruct Denote_Eval_Equiv_Aexp_Fails as [? [H|H]]; eauto;
          eexists; [left | right]; state_steps; rewrite H; match_failure.
        apply Denote_Eval_Equiv_Aexp_Succeeds in Heqe1;
        edestruct IH as [? [H|H]]; eauto;
        eexists; [left | right]; state_steps; rewrite Heqe1; state_steps; rewrite H; match_failure.
   Qed.

    Lemma Denote_Eval_Equiv_DSHPower_Succeeds:
      forall n (σ: evalContext) mem f x y xoff yoff m,
        evalDSHPower mem σ n f x y xoff yoff  ≡ inr m ->
        eutt eq
             (interp_Mem (denoteDSHPower σ n f x y xoff yoff) mem)
             (ret (mem, m)).
    Proof.
      induction n as [| n IH]; intros σ mem f x y xoff yoff m HEval; cbn in HEval.
      - unfold_Mem; inv_sum.
        state_steps; reflexivity.
      - unfold_Mem; inv_eval.
        state_steps.
        apply Denote_Eval_Equiv_Aexp_Succeeds in Heqe1; rewrite Heqe1; state_steps.
        rewrite IH; eauto; reflexivity.
    Qed.

    Lemma Denote_Eval_Equiv_DSHPower_Fails:
      forall n (σ: evalContext) mem f x y xoff yoff msg,
        evalDSHPower mem σ n f x y xoff yoff ≡ inl msg ->
        interp_Mem_Fails (denoteDSHPower σ n f x y xoff yoff) mem.
    Proof.
      unfold interp_Mem_Fails.
      induction n as [| n IH]; cbn; intros σ mem f x y xoff yoff msg HEval; unfold_Mem; cbn in HEval.
      - inv_eval.
      - inv_eval; try (eexists; left; state_steps; match_failure).
        edestruct Denote_Eval_Equiv_Aexp_Fails as [? [H|H]]; eauto;
          eexists; [left | right]; state_steps; rewrite H; match_failure.
        apply Denote_Eval_Equiv_Aexp_Succeeds in Heqe1;
        edestruct IH as [? [H|H]]; eauto;
        eexists; [left | right]; state_steps; rewrite Heqe1; state_steps; rewrite H; match_failure.
   Qed.

    Theorem Denote_Eval_Equiv_Succeeds:
      forall (σ: evalContext) (op: DSHOperator) (mem: memory) (fuel: nat) (mem': memory),
        evalDSHOperator σ op mem fuel ≡ Some (inr mem') ->
        eutt eq (interp_Mem (denoteDSHOperator σ op) mem) (ret (mem', tt)).
    Proof.
      intros ? ? ? ? ? H; destruct fuel as [| fuel]; [inversion H |].
      revert σ mem' fuel mem H.
      induction op; intros σ mem fuel mem' HEval; cbn in HEval.
      - unfold_Mem; inv_eval; state_steps; reflexivity.
      - unfold_Mem; destruct src,dst.
        inv_eval.
        state_steps; reflexivity.
      - unfold_Mem; inv_eval.
        state_steps.
        rewrite Denote_Eval_Equiv_IMap_Succeeds; eauto; state_steps.
        reflexivity.
      - unfold_Mem; inv_eval.
        state_steps.
        rewrite Denote_Eval_Equiv_BinOp_Succeeds; eauto; state_steps.
        reflexivity.
      - unfold_Mem; inv_eval.
        state_steps.
        rewrite Denote_Eval_Equiv_DSHMap2_Succeeds; eauto; state_steps.
        reflexivity.
      - unfold_Mem; inv_eval.
        state_steps.
        rewrite Denote_Eval_Equiv_DSHPower_Succeeds; eauto; state_steps.
        reflexivity.
      - unfold interp_Mem.
        eapply Loop_is_Iter; eauto.
      - unfold_Mem; inv_eval.
        state_steps.
        destruct fuel as [| fuel]; [inv Heqo |].
        rewrite IHop; eauto; state_steps.
        reflexivity.
      - unfold_Mem; inv_eval.
        state_steps.
        reflexivity.
      - unfold_Mem; inv_eval.
        state_steps.
        reflexivity.
      - unfold_Mem; inv_eval.
        state_steps; rewrite IHop1; eauto using evalDSHOperator_fuel_monotone.
        state_steps; rewrite IHop2; eauto using evalDSHOperator_fuel_monotone.
        reflexivity.
    Qed.

    Lemma Loop_is_Iter_Fail_aux:
      ∀ (op : DSHOperator)
        (IHop: ∀ (σ : evalContext) (msg : string) (fuel : nat) (mem : memory),
            evalDSHOperator σ op mem (S fuel) ≡ Some (inl msg)
            → ∃ msg' : string,
              interp_Mem (denoteDSHOperator σ op) mem ≈ Dfail msg'
              ∨ interp_Mem (denoteDSHOperator σ op) mem ≈ Sfail msg')
        (i N: nat)
        (σ : evalContext) (mem : memory) (fuel : nat) (msg : string),
        i < S N ->
        eval_Loop_for_i_to_N σ op i (S N) mem (S fuel) ≡ Some (inl msg)
        → exists msg',
            interp_state (case_ Mem_handler pure_state) (denote_Loop_for_i_to_N σ op i (S N)) mem
                         ≈ Dfail msg'
            ∨ interp_state (case_ Mem_handler pure_state) (denote_Loop_for_i_to_N σ op i (S N)) mem
                           ≈ Sfail msg'.
    Proof.
      intros op IHop i N σ mem fuel msg ineq HEval.
      remember ((S N) - i) as k.
      revert Heqk σ mem msg HEval.
      revert i ineq.
      induction k as [| k IH].
      - intros i ineq EQ.
        assert (S N ≡ i) by lia; clear EQ ineq; subst.
        intros.
        cbn in HEval.
        rewrite Nat.eqb_refl in HEval.
        inv HEval.
      - intros i ineq EQ σ mem msg HEval.
        assert(EQ': (i =? S N)%nat ≡ false) by (apply Nat.eqb_neq; lia).
        destruct (Nat.eq_dec i N) as [E|NE].
        +
          unfold denote_Loop_for_i_to_N.
          subst i.
          cbn in HEval.
          rewrite EQ' in HEval.
          repeat break_match_hyp; subst.
          *
            destruct fuel; [inv Heqo|].
            inv HEval.
            rewrite eval_Loop_for_N_to_N in Heqo.
            inv Heqo.
          *
            destruct fuel; [inv Heqo|].
            rewrite eval_Loop_for_N_to_N in Heqo.
            inv Heqo.

            apply IHop in HEval.
            unfold interp_Mem in HEval.
            destruct HEval as [msg' [Eval_body_D | Eval_body_S]].
            --
              eexists.
              left.
              iter_unfold_pointed.
              state_steps.
              rewrite EQ'; state_steps.
              rewrite interp_state_bind.
              rewrite bind_bind.
              apply beq_nat_false in EQ'.
              rewrite Eval_body_D.
              match_failure.
            --
              eexists.
              right.
              iter_unfold_pointed.
              state_steps.
              rewrite EQ'; state_steps.
              rewrite interp_state_bind.
              rewrite bind_bind.
              apply beq_nat_false in EQ'.
              rewrite_clear Eval_body_S.
              match_failure.
          *
            some_none.
        +
          apply eval_Loop_for_i_to_N_Fail_invert in HEval ; [| lia].
          destruct HEval as [Eval_body | [mem_aux [Eval_head Eval_tail]]].
          --
            (* fails @i *)
            unfold denote_Loop_for_i_to_N.
            apply IHop in Eval_body; clear IHop.
            unfold interp_Mem in Eval_body.
            destruct Eval_body as [msg' [Eval_body_D | Eval_body_S]].
            ++
              exists msg'.
              left.
              iter_unfold_pointed.
              state_steps.
              rewrite EQ'; state_steps.
              rewrite interp_state_bind.
              rewrite bind_bind.
              apply beq_nat_false in EQ'.
              rewrite Eval_body_D.
              match_failure.
            ++
              exists msg'.
              right.
              iter_unfold_pointed.
              state_steps.
              rewrite EQ'; state_steps.
              rewrite interp_state_bind.
              rewrite bind_bind.
              apply beq_nat_false in EQ'.
              rewrite_clear Eval_body_S.
              match_failure.
          --
            (* succeeds @i, but fails later *)
            apply IH in Eval_tail; clear IH; try lia.
            apply Denote_Eval_Equiv_Succeeds in Eval_head.
            unfold interp_Mem in Eval_head.
            destruct Eval_tail as [msg' [Eval_tail_D | Eval_tail_S]].
            ++
              exists msg'.
              left.
              unfold denote_Loop_for_i_to_N in *.
              iter_unfold_pointed.
              state_steps.
              rewrite EQ'; state_steps.
              rewrite interp_state_bind.
              rewrite bind_bind.
              rewrite Eval_head.
              state_steps.
              auto.
            ++
              exists msg'.
              right.
              unfold denote_Loop_for_i_to_N in *.
              iter_unfold_pointed.
              state_steps.
              rewrite EQ'; state_steps.
              rewrite interp_state_bind.
              rewrite bind_bind.
              rewrite Eval_head.
              state_steps.
              auto.
    Qed.

    Lemma Loop_is_Iter_Fail:
      ∀ (op : DSHOperator)
        (IHop: ∀ (σ : evalContext) (msg : string) (fuel : nat) (mem : memory),
            evalDSHOperator σ op mem (S fuel) ≡ Some (inl msg)
            → ∃ msg' : string,
              interp_Mem (denoteDSHOperator σ op) mem ≈ Dfail msg'
              ∨ interp_Mem (denoteDSHOperator σ op) mem ≈ Sfail msg')
        (N: nat) (σ : evalContext) (mem : memory) (fuel : nat) (msg: string),
        evalDSHOperator σ (DSHLoop (S N) op) mem (S fuel) ≡ Some (inl msg) ->
        ∃ msg' : string,
          interp_Mem (denoteDSHOperator σ (DSHLoop (S N) op)) mem ≈ Dfail msg'
          ∨ interp_Mem (denoteDSHOperator σ (DSHLoop (S N) op)) mem ≈ Sfail msg'.
    Proof.
      intros.
      rewrite <- eval_Loop_for_0_to_N in H.
      assert(zn: 0 < S N) by lia.
      pose proof (Loop_is_Iter_Fail_aux op IHop 0 N σ mem fuel msg zn H) as AUX.
      destruct AUX as [msg' AUX].
      exists msg'.
      eapply AUX; eauto.
    Qed.

    Theorem Denote_Eval_Equiv_Fails:
      forall (σ: evalContext) (op: DSHOperator) (mem: memory) (fuel: nat) (msg:string),
        evalDSHOperator σ op mem fuel ≡ Some (inl msg) ->
        interp_Mem_Fails (denoteDSHOperator σ op) mem.
    Proof.
      intros σ op mem fuel msg HEval; unfold interp_Mem_Fails.
      destruct fuel as [| fuel]; [inv HEval |].
      revert σ mem fuel msg HEval; induction op; intros; cbn in HEval.
      - inv_option.
      - unfold_Mem; destruct src,dst; inv_eval;
          eexists; left; state_steps; match_failure.
      - unfold_Mem; inv_eval;
          try (eexists; left; state_steps; match_failure).
        edestruct Denote_Eval_Equiv_IMap_Fails as [? [|]]; eauto.
        eexists; left; state_steps; rewrite H; match_failure.
        eexists; right; state_steps; rewrite H; match_failure.
      - unfold_Mem; inv_eval;
          try (eexists; left; state_steps; match_failure).
        edestruct Denote_Eval_Equiv_BinOp_Fails as [? [H|H]]; eauto;
          eexists; [left | right]; state_steps; rewrite H; match_failure.
      - unfold_Mem; inv_eval;
          try (eexists; left; state_steps; match_failure).
        edestruct Denote_Eval_Equiv_DSHMap2_Fails as [? [H|H]]; eauto;
          eexists; [left | right]; state_steps; rewrite H; match_failure.
      - unfold_Mem; inv_eval;
          try (eexists; left; state_steps; match_failure).
        edestruct Denote_Eval_Equiv_DSHPower_Fails as [? [H|H]]; eauto;
          eexists; [left | right]; state_steps; rewrite H; match_failure.
      -
        destruct n;[inv HEval|].
        eapply Loop_is_Iter_Fail; eauto.
      - unfold_Mem; inv_eval.
        destruct fuel as [| fuel]; [inv Heqo |].
        edestruct IHop as [? [H|H]]; eauto;
          eexists; [left | right]; state_steps; rewrite H; state_steps; match_failure.
      - unfold_Mem; inv_eval; eexists; left; state_steps; match_failure.
      - unfold_Mem; inv_eval; eexists; left; state_steps; match_failure.
      - unfold_Mem; inv_eval.
        + edestruct IHop1 as [? [H|H]]; eauto using evalDSHOperator_fuel_monotone;
          eexists; [left | right]; state_steps; rewrite H; state_steps; match_failure.
        + apply Denote_Eval_Equiv_Succeeds in Heqo.
          edestruct IHop2 as [? [H|H]]; eauto using evalDSHOperator_fuel_monotone;
            eexists; [left | right]; state_steps; rewrite Heqo; state_steps; rewrite H; state_steps; match_failure.
   Qed.

  End Eval_Denote_Equiv.

End MDSigmaHCOLITree.
