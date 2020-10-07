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
  | MemLU  (msg: string) (id: nat): MemEvent mem_block
  | MemSet (id: nat) (bk: mem_block): MemEvent unit
  | MemAlloc (size: NT.t): MemEvent nat
  | MemFree (id: nat): MemEvent unit.

  Definition StaticFailE := exceptE string.
  Definition StaticThrow (msg: string): StaticFailE void := Throw msg.
  Definition DynamicFailE := exceptE string.
  Definition DynamicThrow (msg: string): DynamicFailE void := Throw msg.
  Definition Event := MemEvent +' StaticFailE +' DynamicFailE.

  Definition Sfail {A: Type} {E} `{DynamicFailE -< E} (msg: string): itree E A :=
    throw msg.

  Definition Dfail {A: Type} {E} `{DynamicFailE -< E} (msg: string): itree E A :=
    throw msg.

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

  Definition denotePExpr (σ: evalContext) (exp:PExpr): itree Event (nat*NT.t) :=
    lift_Serr (evalPExpr σ exp).

  Definition denoteMExpr (σ: evalContext) (exp:MExpr): itree Event (mem_block*NT.t) :=
    match exp with
    | @MPtrDeref p =>
      '(bi,size) <- denotePExpr σ p ;;
      bi' <- trigger (MemLU "MPtrDeref" bi) ;;
      ret (bi', size)
    | @MConst t size => ret (t,size)
    end.

  (* Definition denoteNExpr (σ: evalContext) (e: NExpr): itree Event NT.t := *)
    (* lift_Serr (evalNExpr σ e). *)
  Fixpoint denoteNExpr (σ: evalContext) (e:NExpr): itree Event NT.t :=
    match e with
    | NVar i =>  lift_Serr
                 (v <- (context_lookup "NVar not found" σ i) ;;
                  (match v with
                   | DSHnatVal x => ret x
                   | _ => raise "invalid NVar type"
                   end))
    | NConst c => Ret c
    | NDiv a b =>
      av <- denoteNExpr σ a ;;
      bv <- denoteNExpr σ b ;;
      if NTypeEqDec bv NTypeZero then
        Dfail "Division by 0"
      else
        Ret (NTypeDiv av bv)
  | NMod a b   =>
    av <- denoteNExpr σ a ;;
      bv <- denoteNExpr σ b ;;
      if NTypeEqDec bv NTypeZero then
        Dfail "Mod by 0"
      else
        Ret (NTypeMod av bv)
    | NPlus a b  => liftM2 NTypePlus  (denoteNExpr σ a) (denoteNExpr σ b)
    | NMinus a b => liftM2 NTypeMinus (denoteNExpr σ a) (denoteNExpr σ b)
    | NMult a b  => liftM2 NTypeMult  (denoteNExpr σ a) (denoteNExpr σ b)
    | NMin a b   => liftM2 NTypeMin   (denoteNExpr σ a) (denoteNExpr σ b)
    | NMax a b   => liftM2 NTypeMax   (denoteNExpr σ a) (denoteNExpr σ b)
    end.


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
      i' <- denoteNExpr σ i ;;
      '(m',msize) <- (denoteMExpr σ m) ;;
      lift_Derr (assert_NT_lt "ANth index out of bounds" i' msize) ;;
      lift_Derr (mem_lookup_err "ANth not in memory" (NT.to_nat i') m')
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
          '(x_i,x_size) <- denotePExpr σ x_p ;;
          '(y_i,y_size) <- denotePExpr σ y_p ;;
          x <- trigger (MemLU "Error looking up 'x' in DSHAssign" x_i) ;;
          y <- trigger (MemLU "Error looking up 'y' in DSHAssign" y_i) ;;
          src <- denoteNExpr σ src_e ;;
          dst <- denoteNExpr σ dst_e ;;
          lift_Derr (assert_NT_lt "DSHAssign 'dst' out of bounds" dst y_size) ;;
          v <- lift_Derr (mem_lookup_err "Error looking up 'v' in DSHAssign" (to_nat src) x) ;;
          trigger (MemSet y_i (mem_add (to_nat dst) v y))

        | @DSHIMap n x_p y_p f =>
          '(x_i,x_size) <- denotePExpr σ x_p ;;
          '(y_i,y_sixe) <- denotePExpr σ y_p ;;
          x <- trigger (MemLU "Error looking up 'x' in DSHIMap" x_i) ;;
          y <- trigger (MemLU "Error looking up 'y' in DSHIMap" y_i) ;;
          y' <- denoteDSHIMap n f σ x y ;;
          trigger (MemSet y_i y')

        | @DSHMemMap2 n x0_p x1_p y_p f =>
          '(x0_i,x0_size) <- denotePExpr σ x0_p ;;
          '(x1_i,x1_size) <- denotePExpr σ x1_p ;;
          '(y_i,y_size) <- denotePExpr σ y_p ;;
          x0 <- trigger (MemLU "Error looking up 'x0' in DSHMemMap2" x0_i) ;;
          x1 <- trigger (MemLU "Error looking up 'x1' in DSHMemMap2" x1_i) ;;
          y <- trigger (MemLU "Error looking up 'y' in DSHMemMap2" y_i) ;;
          y' <- denoteDSHMap2 n f σ x0 x1 y ;;
          trigger (MemSet y_i y')
        | @DSHBinOp n x_p y_p f =>
          '(x_i,x_size) <- denotePExpr σ x_p ;;
          '(y_i,y_sixe) <- denotePExpr σ y_p ;;
          x <- trigger (MemLU "Error looking up 'x' in DSHBinOp" x_i) ;;
          y <- trigger (MemLU "Error looking up 'y' in DSHBinOp" y_i) ;;
          y' <- denoteDSHBinOp n n f σ x y ;;
          trigger (MemSet y_i y')

        | DSHPower ne (x_p,xoffset) (y_p,yoffset) f initial =>
          '(x_i,x_size) <- denotePExpr σ x_p ;;
          '(y_i,y_sixe) <- denotePExpr σ y_p ;;
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

        | DSHMemInit y_p value =>
          '(y_i,y_size) <- denotePExpr σ y_p ;;
          y <- trigger (MemLU "Error looking up 'y' in DSHMemInit" y_i) ;;
          let y' := mem_union (mem_const_block (to_nat y_size) value) y in
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

End MDSigmaHCOLITree.
