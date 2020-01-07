(* Deep embedding of a subset of SigmaHCOL *)

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
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.

Require Import ITree.ITree.
Require Import ITree.Events.Exception.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.misc.decision.

Global Open Scope nat_scope.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Import MonadNotation.
Local Open Scope monad_scope.

Module MDSigmaHCOLITree (Import CT : CType) (Import ESig:MDSigmaHCOLEvalSig CT).

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

  Definition Sfail {A: Type} (msg: string): itree Event A :=
    vis (Throw msg) (fun (x: void) => match x with end).

  Definition Dfail {A: Type} (msg: string): itree Event A :=
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

  (* This could be defined as a lift of the same definition in [Eval]. Would require a [MonadT] instance for itree *)
  (* Evaluation of expressions does not allow for side-effects *)
  Definition evalPexp (σ: evalContext) (exp:PExpr): itree Event (mem_block_id) :=
    match exp with
    | @PVar i =>
      match nth_error σ i with
      | Some (@DSHPtrVal v) => ret v
      | _ => Sfail "error looking up PVar"
      end
    end.

  (* Evaluation of expressions does not allow for side-effects *)
  Definition evalMexp (σ: evalContext) (exp:MExpr): itree Event (mem_block) :=
    match exp with
    | @MPtrDeref p =>
      bi <- evalPexp σ p ;;
      trigger (MemLU "MPtrDeref" bi)
    | @MConst t => ret t
    end.

  (* Evaluation of expressions does not allow for side-effects *)
  (* Merge this to be shared with the [Eval] equivalent *)
  Fixpoint evalNexp_aux (σ: evalContext) (e:NExpr): err nat :=
    match e with
    | NVar i => v <- (context_lookup "NVar not found" σ i) ;;
                 (match v with
                  | DSHnatVal x => ret x
                  | _ => raise "invalid NVar type"
                  end)
    | NConst c => ret c
    | NDiv a b => liftM2 Nat.div (evalNexp_aux σ a) (evalNexp_aux σ b)
    | NMod a b => liftM2 Nat.modulo (evalNexp_aux σ a) (evalNexp_aux σ b)
    | NPlus a b => liftM2 Nat.add (evalNexp_aux σ a) (evalNexp_aux σ b)
    | NMinus a b => liftM2 Nat.sub (evalNexp_aux σ a) (evalNexp_aux σ b)
    | NMult a b => liftM2 Nat.mul (evalNexp_aux σ a) (evalNexp_aux σ b)
    | NMin a b => liftM2 Nat.min (evalNexp_aux σ a) (evalNexp_aux σ b)
    | NMax a b => liftM2 Nat.max (evalNexp_aux σ a) (evalNexp_aux σ b)
    end.

  Definition evalNexp (σ: evalContext) (e: NExpr): itree Event nat :=
    lift_Serr (evalNexp_aux σ e).

  (* Evaluation of expressions does not allow for side-effects *)
  Fixpoint evalAexp (σ: evalContext) (e:AExpr): itree Event t :=
    match e with
    | AVar i =>
      v <- lift_Serr (context_lookup "AVar not found" σ i);;
        (match v with
         | DSHCTypeVal x => ret x
         | _ => Sfail "invalid AVar type"
         end)
    | AConst x => ret x
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
      i' <- evalNexp σ i ;;
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
             (i:nat) (a:t): itree Event t :=
    evalAexp (DSHCTypeVal a :: DSHnatVal i :: σ) f.

  (* Evaluation of functions does not allow for side-effects *)
  Definition evalIBinCType (σ: evalContext) (f: AExpr)
             (i:nat) (a b:t): itree Event t :=
    evalAexp (DSHCTypeVal b :: DSHCTypeVal a :: DSHnatVal i :: σ) f.

  (* Evaluation of functions does not allow for side-effects *)
  Definition evalBinCType (σ: evalContext) (f: AExpr)
             (a b:t): itree Event t :=
    evalAexp (DSHCTypeVal b :: DSHCTypeVal a :: σ) f.

  Fixpoint evalDSHIMap
           (n: nat)
           (f: AExpr)
           (σ: evalContext)
           (x y: mem_block) : itree Event (mem_block)
    :=
      match n with
      | O => ret y
      | S n =>
        v <- lift_Derr (mem_lookup_err "Error reading memory evalDSHIMap" n x) ;;
        v' <- evalIUnCType σ f n v ;;
        evalDSHIMap n f σ x (mem_add n v' y)
      end.

  Fixpoint evalDSHMap2
           (n: nat)
           (f: AExpr)
           (σ: evalContext)
           (x0 x1 y: mem_block) : itree Event (mem_block)
    :=
      match n with
      | O => ret y
      | S n =>
        v0 <- lift_Derr (mem_lookup_err ("Error reading 1st arg memory in evalDSHMap2 @" ++ (string_of_nat n) ++ " in " ++ string_of_mem_block_keys x0) n x0) ;;
        v1 <- lift_Derr (mem_lookup_err ("Error reading 2nd arg memory in evalDSHMap2 @" ++ (string_of_nat n) ++ " in " ++ string_of_mem_block_keys x1) n x1) ;;
        v' <- evalBinCType σ f v0 v1 ;;
        evalDSHMap2 n f σ x0 x1 (mem_add n v' y)
      end.

  Fixpoint evalDSHBinOp
           (n off: nat)
           (f: AExpr)
           (σ: evalContext)
           (x y: mem_block) : itree Event (mem_block)
    :=
      match n with
      | O => ret y
      | S n =>
        v0 <- lift_Derr (mem_lookup_err "Error reading 1st arg memory in evalDSHBinOp" n x) ;;
        v1 <- lift_Derr (mem_lookup_err "Error reading 2nd arg memory in evalDSHBinOp" (n+off) x) ;;
        v' <- evalIBinCType σ f n v0 v1 ;;
        evalDSHBinOp n off f σ x (mem_add n v' y)
      end.

  Fixpoint evalDSHPower
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
        xv <- lift_Derr (mem_lookup_err "Error reading 'xv' memory in evalDSHBinOp" 0 x) ;;
        yv <- lift_Derr (mem_lookup_err "Error reading 'yv' memory in evalDSHBinOp" 0 y) ;;
        v' <- evalBinCType σ f xv yv ;;
        evalDSHPower σ p f x (mem_add 0 v' y) xoffset yoffset
      end.

  Fixpoint evalDSHOperator
           (σ: evalContext)
           (op: DSHOperator): itree Event unit
    :=
        match op with
        | DSHNop => ret tt

        | DSHAssign (x_p, src_e) (y_p, dst_e) =>
          x_i <- evalPexp σ x_p ;;
          y_i <- evalPexp σ y_p ;;
          x <- trigger (MemLU "Error looking up 'x' in DSHAssign" x_i) ;;
          y <- trigger (MemLU "Error looking up 'y' in DSHAssign" y_i) ;;
          src <- evalNexp σ src_e ;;
          dst <- evalNexp σ dst_e ;;
          v <- lift_Derr (mem_lookup_err "Error looking up 'v' in DSHAssign" src x) ;;
          trigger (MemSet y_i (mem_add dst v y))

        | @DSHIMap n x_p y_p f =>
          x_i <- evalPexp σ x_p ;;
              y_i <- evalPexp σ y_p ;;
              x <- trigger (MemLU "Error looking up 'x' in DSHIMap" x_i) ;;
              y <- trigger (MemLU "Error looking up 'y' in DSHIMap" y_i) ;;
              y' <- evalDSHIMap n f σ x y ;;
              trigger (MemSet y_i y')

        | @DSHMemMap2 n x0_p x1_p y_p f =>
          x0_i <- evalPexp σ x0_p ;;
               x1_i <- evalPexp σ x1_p ;;
               y_i <- evalPexp σ y_p ;;
               x0 <- trigger (MemLU "Error looking up 'x0' in DSHMemMap2" x0_i) ;;
               x1 <- trigger (MemLU "Error looking up 'x1' in DSHMemMap2" x1_i) ;;
               y <- trigger (MemLU "Error looking up 'y' in DSHMemMap2" y_i) ;;
               y' <- evalDSHMap2 n f σ x0 x1 y ;;
               trigger (MemSet y_i y')
        | @DSHBinOp n x_p y_p f =>
          x_i <- evalPexp σ x_p ;;
              y_i <- evalPexp σ y_p ;;
              x <- trigger (MemLU "Error looking up 'x' in DSHBinOp" x_i) ;;
              y <- trigger (MemLU "Error looking up 'y' in DSHBinOp" y_i) ;;
              y' <- evalDSHBinOp n n f σ x y ;;
              trigger (MemSet y_i y')

        | DSHPower ne (x_p,xoffset) (y_p,yoffset) f initial =>
          x_i <- evalPexp σ x_p ;;
          y_i <- evalPexp σ y_p ;;
          x <- trigger (MemLU "Error looking up 'x' in DSHPower" x_i) ;;
          y <- trigger (MemLU "Error looking up 'y' in DSHPower" y_i) ;;
          n <- evalNexp σ ne ;; (* [n] evaluated once at the beginning *)
          let y' := mem_add 0 initial y in
          xoff <- evalNexp σ xoffset ;;
          yoff <- evalNexp σ yoffset ;;
          y'' <- evalDSHPower σ n f x y' xoff yoff ;;
          trigger (MemSet y_i y'')

        | DSHLoop n body =>
          iter (fun (p: nat) =>
                  match p with
                  | O => ret (inr tt)
                  | S p =>
                    evalDSHOperator (DSHnatVal (n - (S p)) :: σ) body;;
                    ret (inl p)
                  end) n

        | DSHAlloc size body =>
          t_i <- trigger (MemAlloc size) ;;
          trigger (MemSet t_i (mem_empty)) ;;
          evalDSHOperator (DSHPtrVal t_i :: σ) body ;;
          trigger (MemFree t_i)

        | DSHMemInit size y_p value =>
          y_i <- evalPexp σ y_p ;;
          y <- trigger (MemLU "Error looking up 'y' in DSHMemInit" y_i) ;;
          let y' := mem_union (mem_const_block size value) y in
          trigger (MemSet y_i y')

       | DSHMemCopy size x_p y_p =>
          x_i <- evalPexp σ x_p ;;
          y_i <- evalPexp σ y_p ;;
          x <- trigger (MemLU "Error looking up 'x' in DSHMemCopy" x_i) ;;
          y <- trigger (MemLU "Error looking up 'y' in DSHMemCopy" y_i) ;;
          let y' := mem_union x y in
          trigger (MemSet y_i y')

       | DSHSeq f g =>
          evalDSHOperator σ f ;; evalDSHOperator σ g
      end.

  Definition pure_state {S E} : E ~> Monads.stateT S (itree E)
    := fun _ e s => Vis e (fun x => Ret (s, x)).

  Definition Mem_handler: MemEvent ~> Monads.stateT memory (itree (StaticFailE +' DynamicFailE)) :=
    fun T e mem =>
      match e with
      | MemLU msg id  => lift_Derr (Functor.fmap (fun x => (mem,x)) (memory_lookup_err msg mem id))
      | MemSet id blk => ret (memory_set mem id blk, tt)
      | MemAlloc size => ret (mem, memory_new mem)
      | MemFree id    => ret (memory_remove mem id, tt)
      end.

  Definition interp_Mem: itree Event ~> Monads.stateT memory (itree (StaticFailE +' DynamicFailE)) :=
    interp (case_ Mem_handler pure_state).

End MDSigmaHCOLITree.
