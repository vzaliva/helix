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
Require Import Helix.DSigmaHCOL.NType.
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

(* TODOYZ: Host this on the Vellvm side? On the ITree side? *)
Ltac state_step :=
  match goal with
  | |- interp_state _ (ITree.bind _ _) _ ≈ _ => rewrite interp_state_bind
  | |- ITree.bind (ITree.bind _ _) _ ≈ _ => rewrite bind_bind
  | |- ITree.bind (Vis _ _) _ ≈ _ => rewrite bind_vis
  | |- ITree.bind (Ret _) _ ≈ _ => rewrite bind_ret_l
  | |- context[interp_state _ (Ret _) _] => rewrite interp_state_ret
  | |- context[interp_state _ (trigger _) _] => rewrite interp_state_trigger_eqit
  | |- context[interp_state _ (vis _ _) _] => rewrite interp_state_vis
  | |- context[Tau _] => rewrite tau_euttge
  end.

Ltac state_steps' := cbn; repeat (state_step; cbn).

Ltac iter_unfold_pointed :=
  match goal with
  | |- context[interp_state ?h (iter ?k ?i) _ ≈ _] =>
    generalize (iter_unfold k); let EQ := fresh "EQ" in intros EQ; rewrite (EQ i); clear EQ
  end.

Module MDSigmaHCOLITree
       (Import CT : CType)
       (Import NT : NType).

  Include MDSigmaHCOLEval CT NT.

  Local Open Scope string_scope.

  Variant MemEvent: Type -> Type :=
  | MemLU  (msg: string) (id: mem_block_id): MemEvent mem_block
  | MemSet (id: mem_block_id) (bk: mem_block): MemEvent unit
  | MemAlloc (size: NT.t): MemEvent mem_block_id
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

  Definition denotePExpr (σ: evalContext) (exp:PExpr): itree Event (mem_block_id) :=
    lift_Serr (evalPExpr σ exp).

  Definition denoteMExpr (σ: evalContext) (exp:MExpr): itree Event (mem_block) :=
    match exp with
    | @MPtrDeref p =>
      bi <- denotePExpr σ p ;;
      trigger (MemLU "MPtrDeref" bi)
    | @MConst t => ret t
    end.

  Definition denoteNExpr (σ: evalContext) (e: NExpr): itree Event NT.t :=
    lift_Serr (evalNExpr σ e).

  Fixpoint denoteAExpr (σ: evalContext) (e:AExpr): itree Event CT.t :=
    match e with
    | AVar i =>
      v <- lift_Serr (context_lookup "AVar not found" σ i);;
        (match v with
         | DSHCTypeVal x => ret x
         | _ => Sfail "invalid AVar type"
         end)
    | AConst x => ret x
    | AAbs x =>  liftM CTypeAbs (denoteAExpr σ x)
    | APlus a b => liftM2 CTypePlus (denoteAExpr σ a) (denoteAExpr σ b)
    | AMult a b => liftM2 CTypeMult (denoteAExpr σ a) (denoteAExpr σ b)
    | AMin a b => liftM2 CTypeMin (denoteAExpr σ a) (denoteAExpr σ b)
    | AMax a b => liftM2 CTypeMax (denoteAExpr σ a) (denoteAExpr σ b)
    | AMinus a b =>
      a' <- (denoteAExpr σ a) ;;
         b' <- (denoteAExpr σ b) ;;
         ret (CTypeSub a' b')
    | ANth m i =>
      m' <- (denoteMExpr σ m) ;;
      i' <- denoteNExpr σ i ;;
         (* Instead of returning error we default to zero here.
          This situation should never happen for programs
          refined from MSHCOL which ensure bounds via
          dependent types. So DHCOL programs should
          be correct by construction *)
      (match mem_lookup (to_nat i') m' with
       | Some v => ret v
       | None => ret CTypeZero
       end)
    | AZless a b => liftM2 CTypeZLess (denoteAExpr σ a) (denoteAExpr σ b)
    end.

  Definition denoteIUnCType (σ: evalContext) (f: AExpr)
             (i:NT.t) (a:CT.t): itree Event CT.t :=
    denoteAExpr (DSHCTypeVal a :: DSHnatVal i :: σ) f.

  Definition denoteIBinCType (σ: evalContext) (f: AExpr)
             (i:NT.t) (a b:CT.t): itree Event CT.t :=
    denoteAExpr (DSHCTypeVal b :: DSHCTypeVal a :: DSHnatVal i :: σ) f.

  Definition denoteBinCType (σ: evalContext) (f: AExpr)
             (a b:CT.t): itree Event CT.t :=
    denoteAExpr (DSHCTypeVal b :: DSHCTypeVal a :: σ) f.

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
        vn <- lift_Serr (NT.from_nat n) ;;
        v' <- denoteIUnCType σ f vn v ;;
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
        vn <- lift_Serr (NT.from_nat n) ;;
        v' <- denoteIBinCType σ f vn v0 v1 ;;
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
        xv <- lift_Derr (mem_lookup_err "Error reading 'xv' memory in denoteDSHBinOp" xoffset x) ;;
        yv <- lift_Derr (mem_lookup_err "Error reading 'yv' memory in denoteDSHBinOp" yoffset y) ;;
        v' <- denoteBinCType σ f yv xv ;;
        denoteDSHPower σ p f x (mem_add yoffset v' y) xoffset yoffset
      end.

  Notation iter := (@iter _ (ktree _) sum _ _ _).

  Fixpoint denoteDSHOperator
           (σ: evalContext)
           (op: DSHOperator): itree Event unit :=
        match op with
        | DSHNop => ret tt

        | DSHAssign (x_p, src_e) (y_p, dst_e) =>
          x_i <- denotePExpr σ x_p ;;
          y_i <- denotePExpr σ y_p ;;
          x <- trigger (MemLU "Error looking up 'x' in DSHAssign" x_i) ;;
          y <- trigger (MemLU "Error looking up 'y' in DSHAssign" y_i) ;;
          src <- denoteNExpr σ src_e ;;
          dst <- denoteNExpr σ dst_e ;;
          v <- lift_Derr (mem_lookup_err "Error looking up 'v' in DSHAssign" (to_nat src) x) ;;
          trigger (MemSet y_i (mem_add (to_nat dst) v y))

        | @DSHIMap n x_p y_p f =>
          x_i <- denotePExpr σ x_p ;;
              y_i <- denotePExpr σ y_p ;;
              x <- trigger (MemLU "Error looking up 'x' in DSHIMap" x_i) ;;
              y <- trigger (MemLU "Error looking up 'y' in DSHIMap" y_i) ;;
              y' <- denoteDSHIMap n f σ x y ;;
              trigger (MemSet y_i y')

        | @DSHMemMap2 n x0_p x1_p y_p f =>
          x0_i <- denotePExpr σ x0_p ;;
               x1_i <- denotePExpr σ x1_p ;;
               y_i <- denotePExpr σ y_p ;;
               x0 <- trigger (MemLU "Error looking up 'x0' in DSHMemMap2" x0_i) ;;
               x1 <- trigger (MemLU "Error looking up 'x1' in DSHMemMap2" x1_i) ;;
               y <- trigger (MemLU "Error looking up 'y' in DSHMemMap2" y_i) ;;
               y' <- denoteDSHMap2 n f σ x0 x1 y ;;
               trigger (MemSet y_i y')
        | @DSHBinOp n x_p y_p f =>
          x_i <- denotePExpr σ x_p ;;
              y_i <- denotePExpr σ y_p ;;
              x <- trigger (MemLU "Error looking up 'x' in DSHBinOp" x_i) ;;
              y <- trigger (MemLU "Error looking up 'y' in DSHBinOp" y_i) ;;
              y' <- denoteDSHBinOp n n f σ x y ;;
              trigger (MemSet y_i y')

        | DSHPower ne (x_p,xoffset) (y_p,yoffset) f initial =>
          x_i <- denotePExpr σ x_p ;;
          y_i <- denotePExpr σ y_p ;;
          x <- trigger (MemLU "Error looking up 'x' in DSHPower" x_i) ;;
          y <- trigger (MemLU "Error looking up 'y' in DSHPower" y_i) ;;
          n <- denoteNExpr σ ne ;; (* [n] denoteuated once at the beginning *)
          xoff <- denoteNExpr σ xoffset ;;
          yoff <- denoteNExpr σ yoffset ;;
          let y' := mem_add (to_nat yoff) initial y in
          y'' <- denoteDSHPower σ (to_nat n) f x y' (to_nat xoff) (to_nat yoff) ;;
          trigger (MemSet y_i y'')
        | DSHLoop n body =>
          iter (fun (p: nat) =>
                  if EqNat.beq_nat p n
                  then ret (inr tt)
                  else
                    vp <- lift_Serr (NT.from_nat p) ;;
                    denoteDSHOperator (DSHnatVal vp :: σ) body ;; ret (inl (S p))
               ) 0

        | DSHAlloc size body =>
          t_i <- trigger (MemAlloc size) ;;
          trigger (MemSet t_i (mem_empty)) ;;
          denoteDSHOperator (DSHPtrVal t_i size :: σ) body ;;
          trigger (MemFree t_i)

        | DSHMemInit size y_p value =>
          y_i <- denotePExpr σ y_p ;;
          y <- trigger (MemLU "Error looking up 'y' in DSHMemInit" y_i) ;;
          let y' := mem_union (mem_const_block (to_nat size) value) y in
          trigger (MemSet y_i y')

       | DSHMemCopy size x_p y_p =>
          x_i <- denotePExpr σ x_p ;;
          y_i <- denotePExpr σ y_p ;;
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

    (* Ltac unfold_Mem := unfold interp_Mem in *; cbn in *; unfold denotePExpr, denoteNExpr, evalIUnCType, denoteIUnCType in *. *)
    Ltac unfold_Mem := unfold interp_Mem in *; cbn; unfold denotePExpr, denoteNExpr, evalIUnCType, denoteIUnCType in *.

    Lemma Denote_Eval_Equiv_MExpr_Succeeds: forall mem σ e bk,
        evalMExpr mem σ e ≡ inr bk ->
        eutt eq
             (interp_Mem (denoteMExpr σ e) mem)
             (ret (mem, bk)).
    Proof.
      intros mem σ [] bk HEval; unfold_Mem; cbn in HEval; inv_eval; state_steps; reflexivity.
    Qed.

    Lemma Denote_Eval_Equiv_AExpr_Succeeds: forall mem σ e v,
        evalAExpr mem σ e ≡ inr v ->
        eutt eq
             (interp_Mem (denoteAExpr σ e) mem)
             (ret (mem, v)).
    Proof.
      induction e; intros res HEval; unfold_Mem; cbn in HEval;
        try now (inv_eval; state_steps;
                 ((rewrite IHe; eauto; state_steps) ||
                  (rewrite IHe1; eauto; state_steps; rewrite IHe2; eauto; state_steps) ||
                  idtac); reflexivity).
      do 2 (break_match_hyp; try inl_inr).
      state_steps.
      apply Denote_Eval_Equiv_MExpr_Succeeds in Heqs.
      rewrite Heqs; state_steps.
      inv_eval; state_steps; reflexivity.
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
        rewrite Denote_Eval_Equiv_AExpr_Succeeds; eauto; state_steps.
        rewrite IH; eauto.
        reflexivity.
    Qed.

    Lemma Denote_Eval_Equiv_BinCType_Succeeds: forall mem σ f i a b v,
        evalIBinCType mem σ f i a b ≡ inr v ->
        eutt eq
             (interp_Mem (denoteIBinCType σ f i a b) mem)
             (ret (mem, v)).
    Proof.
      unfold evalIBinCType, denoteIBinCType; intros.
      eapply Denote_Eval_Equiv_AExpr_Succeeds; eauto.
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
        apply Denote_Eval_Equiv_BinCType_Succeeds in Heqs2; rewrite Heqs2; cbn; state_steps.
        rewrite IH; eauto; reflexivity.
    Qed.

    Definition denote_Loop_for_i_to_N σ body (i N: nat) :=
      iter (fun (p: nat) =>
              if EqNat.beq_nat p N
              then ret (inr tt)
              else
                vp <- lift_Serr (NT.from_nat p) ;;
                denoteDSHOperator (DSHnatVal vp :: σ) body;;
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
            | Some (inr mem) =>
              match from_nat N with
              | inl msg => Some (inl msg)
              | inr vN =>
                evalDSHOperator (DSHnatVal vN :: σ) body mem fuel
              end
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

    Lemma eval_Loop_for_N_to_N: forall fuel σ op N mem,
        eval_Loop_for_i_to_N σ op N N mem (S fuel) ≡ Some (ret mem).
    Proof.
      intros fuel σ op [| N] mem; [reflexivity |].
      simpl; rewrite Nat.eqb_refl; reflexivity.
    Qed.

    Lemma eval_Loop_for_i_to_N_invert: forall σ i ii N op fuel mem_i mem_f,
        i < N ->
        NT.from_nat i ≡ inr ii ->
        eval_Loop_for_i_to_N σ op i N mem_i fuel ≡ Some (inr mem_f) ->
        exists mem_aux,
          evalDSHOperator (DSHnatVal ii :: σ) op mem_i fuel ≡ Some (inr mem_aux) /\
          eval_Loop_for_i_to_N σ op (S i) N mem_aux fuel ≡ Some (inr mem_f).
    Proof.
      (* This proof is surprisingly painful to go through *)
      intros.
      (* Induction on the number of steps remaining *)
      remember (N - i) as k.
      revert σ fuel i ii N Heqk mem_i mem_f H0 H1 H.
      induction k as [| k IH];
      intros σ fuel i ii N EQ mem_i mem_f Hn Heval ineq;[lia|].

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
      destruct s; inv Heval.

      (* Now there are two cases:
         either a single step was remaining and we should be able to conclude directly;
         or more were remaining, and we should be able to conclude by induction
       *)

      destruct (i =? N)%nat eqn: EQ''; [apply beq_nat_true in EQ''; subst; clear IH |].
      - clear EQ' EQ ineq.
        rewrite Hn in H0.
        destruct fuel as [| fuel]; [inv HEval' |].
        rewrite eval_Loop_for_N_to_N in HEval'.
        setoid_rewrite eval_Loop_for_N_to_N.
        inv HEval'.
        exists mem_f.
        split; [apply evalDSHOperator_fuel_monotone; auto | auto ].
        rewrite Hn.
        auto.
      - destruct (from_nat N) eqn:NN.
        +
          eapply IH in HEval';[|lia|eauto|apply beq_nat_false in EQ''; lia].
          destruct HEval' as (mem_aux & STEP & TAIL).
          exists mem_aux; split; [apply evalDSHOperator_fuel_monotone; auto |].
          cbn; rewrite EQ'', TAIL.
          rewrite NN.
          reflexivity.
        +
          eapply IH in HEval';[|lia|eauto|apply beq_nat_false in EQ''; lia].
          destruct HEval' as (mem_aux & STEP & TAIL).
          exists mem_aux; split; [apply evalDSHOperator_fuel_monotone; auto |].
          cbn; rewrite EQ'', TAIL.
          rewrite NN.
          reflexivity.
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

    Lemma eval_Loop_for_0_to_N_Succeeds:
      forall σ body N mem mem' fuel,
        evalDSHOperator σ (DSHLoop N body) mem fuel ≡ Some (inr mem') ->
        eval_Loop_for_i_to_N σ body 0 N mem fuel ≡ Some (inr mem').
    Proof.
      induction N as [| N IH]; intros.
      - destruct fuel; auto.
      - destruct fuel as [| fuel ]; [auto |].
        cbn in *.
        repeat break_match_hyp; try some_none; try some_inv.
        apply IH in Heqo.
        repeat break_match.
        + some_inv.
        + some_inv.
          auto.
        + some_none.
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
              apply IHN in Heqo0.
              rewrite Heqo0 in Heqo.
              inv Heqo.
            --
              some_none.
          *
            repeat break_match_hyp; subst.
            --
              apply IHN in Heqo0.
              rewrite Heqo0 in Heqo.
              inv Heqo.
            --
              apply IHN in Heqo0.
              rewrite Heqo0 in Heqo.
              inv Heqo.
              inv Heqs1.
              apply H.
            --
              inv Heqs1.
            --
              some_none.
          *
            repeat break_match_hyp; subst.
            --
              apply IHN in Heqo0.
              rewrite Heqo0 in Heqo.
              inv Heqo.
            --
              inv Heqs1.
            --
              apply IHN in Heqo0.
              rewrite Heqo0 in Heqo.
              inv Heqo.
              inv Heqs1.
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

    (* Extend [from_nat_lt] to [le] *)
    Lemma from_nat_le:
      forall x xi y,
        from_nat x ≡ inr xi ->
        y<=x ->
        exists yi, from_nat y ≡ inr yi.
    Proof.
      intros.
      destruct (Nat.eq_dec x y).
      -
        subst.
        eexists.
        eauto.
      -
        eapply from_nat_lt; eauto.
        lia.
    Qed.

    Lemma Loop_is_Iter_aux:
      ∀ (op : DSHOperator)
        (IHop: ∀ (σ : evalContext) (mem' : memory) (fuel : nat) (mem : memory),
            evalDSHOperator σ op mem (S fuel) ≡ Some (inr mem')
            → interp_Mem (denoteDSHOperator σ op) mem ≈ ret (mem', ()))

        (i N: nat)
        (σ : evalContext) (mem : memory) (fuel : nat) (mem' : memory) {nn},
        from_nat N ≡ inr nn ->
        i <= (S N) ->
        eval_Loop_for_i_to_N σ op i (S N) mem (S fuel) ≡ Some (inr mem')
        → interp_state (case_ Mem_handler pure_state) (denote_Loop_for_i_to_N σ op i (S N)) mem ≈ ret (mem', ()).
    Proof.
      intros op IHop i N σ mem fuel mem' nn NN ineq HEval.
      remember ((S N) - i) as k.
      revert Heqk σ mem mem' HEval.
      revert i ineq NN.
      induction k as [| k IH].
      - intros i ineq NN EQ.
        assert ((S N) ≡ i) by lia; clear EQ ineq; subst.
        intros.
        cbn in HEval.
        rewrite Nat.eqb_refl in HEval.
        inv HEval.
        unfold interp_Mem, denote_Loop_for_i_to_N.
        iter_unfold_pointed.
        state_steps.
        rewrite Nat.eqb_refl.
        state_steps.
        reflexivity.
      - intros i ineq NN EQ σ mem mem' HEval.
        destruct (i =? S N)%nat eqn:EQ'.
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

            assert(exists ii : t, from_nat i ≡ inr ii) as II.
            {
              assert(i<=N) by lia.
              eapply from_nat_le;
              eauto.
            }
            destruct II as [ii II].
            rewrite II.
            cbn.
            apply eval_Loop_for_i_to_N_invert with (ii:=ii) in HEval; [|lia| apply II].
            destruct HEval as (mem_aux & Eval_body & Eval_tail).
            apply evalDSHOperator_fuel_monotone in Eval_body.
            apply IHop in Eval_body.
            unfold interp_Mem in Eval_body.
            state_steps.
            rewrite interp_state_bind.
            rewrite Eval_body.
            state_steps.
            apply IH in Eval_tail;try lia;auto.
    Qed.

    (* NOTE: Could not be proven for [N]! *)
    Lemma evalDSHLoop_SN_in_range
          {op : DSHOperator} {N : nat} {σ : evalContext} {mem : memory}
          {fuel : nat} {mem' : memory}:
      evalDSHOperator σ (DSHLoop (S N) op) mem fuel ≡ Some (inr mem')
      -> exists nn, from_nat N ≡ inr nn.
    Proof.
      intros H.
      destruct fuel; [cbn in H; some_none|].

      revert σ mem mem' fuel op H.
      induction N; intros.
      -
        apply from_nat_zero.
      -
        cbn in *.
        repeat break_match; try some_none; try some_inv; subst.
        +
          apply (from_nat_lt (S N) t0 N) in Heqs.
          destruct Heqs.
          congruence.
          lia.
        +
          rename Heqo into H1.
          destruct fuel; [cbn in H1; some_none|].
          cbn in H1.
          repeat break_match_hyp; try some_none; try some_inv; subst.
          specialize (IHN σ mem m0 fuel op).
          rewrite Heqo in IHN.
          inv Heqs1.
          eexists.
          auto.
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
      destruct N.
      -
        cbn in H.
        some_inv.
        subst.
        cbn.
        iter_unfold_pointed.
        state_steps.
        reflexivity.
      -
        pose proof (evalDSHLoop_SN_in_range H) as NN.
        destruct NN as [nn NN].
        apply eval_Loop_for_0_to_N_Succeeds in H.
        rewrite  <- denote_Loop_for_0_to_N.
        eapply Loop_is_Iter_aux;eauto.
        lia.
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
        apply Denote_Eval_Equiv_AExpr_Succeeds in Heqs1; rewrite Heqs1; state_steps.
        rewrite IH; eauto; reflexivity.
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
        apply Denote_Eval_Equiv_AExpr_Succeeds in Heqs1; rewrite Heqs1; state_steps.
        rewrite IH; eauto; reflexivity.
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


  End Eval_Denote_Equiv.

End MDSigmaHCOLITree.
