(* Translates DHCOL on CarrierA to FHCOL *)

Require Import Coq.Strings.String.

Require Import Helix.MSigmaHCOL.CType.
Require Import Helix.DSigmaHCOL.NType.
Require Import Helix.DSigmaHCOL.DSigmaHCOL.

Require Import Helix.MSigmaHCOL.Memory.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.Util.ErrorSetoid.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Import MonadNotation.
Open Scope monad_scope.
Open Scope string_scope.

(* Translation between two families of DHCOL languages L and L'
   substituting types:
   CT -> CT'
   NT -> NT'
 *)
Module MDHCOLTypeTranslator
       (Import CT: CType)
       (Import CT': CType)
       (Import NT: NType)
       (Import NT': NType)
       (Import L: MDSigmaHCOL(CT)(NT))
       (Import L': MDSigmaHCOL(CT')(NT')).

  Definition translateNTypeValue (a:NT.t): err NT'.t
    := NT'.from_nat (NT.to_nat a).

  Definition translatePExpr (p:L.PExpr): L'.PExpr :=
    match p with
    | L.PVar x => L'.PVar x
    end.

  Fixpoint translateNExpr (n:L.NExpr) : err L'.NExpr :=
    match n with
    | L.NVar x => inr (NVar x)
    | L.NConst x =>
      x' <- translateNTypeValue x ;; ret (NConst x')
    | L.NDiv x x0 => liftM2 NDiv (translateNExpr x) (translateNExpr x0)
    | L.NMod x x0 => liftM2 NMod (translateNExpr x) (translateNExpr x0)
    | L.NPlus x x0 => liftM2 NPlus (translateNExpr x) (translateNExpr x0)
    | L.NMinus x x0 => liftM2 NMinus (translateNExpr x) (translateNExpr x0)
    | L.NMult x x0 => liftM2 NMult (translateNExpr x) (translateNExpr x0)
    | L.NMin x x0 => liftM2 NMin (translateNExpr x) (translateNExpr x0)
    | L.NMax x x0 => liftM2 NMax (translateNExpr x) (translateNExpr x0)
    end.

  Definition translateMemRef: L.MemRef -> err L'.MemRef
    := fun '(p,n) =>
         n' <- translateNExpr n ;;
         ret (translatePExpr p, n').

  (* This one is tricky. There are only 2 known constants we know how to translate:
   '1' and '0'. Everything else will trigger an error *)
  Definition translateCTypeValue (a:CT.t): err CT'.t :=
    if CT.CTypeEquivDec a CT.CTypeZero then inr CT'.CTypeZero
    else if CT.CTypeEquivDec a CT.CTypeOne then inr CT'.CTypeOne
         else (inl "unknown CType constant").

  Set Universe Polymorphism.

  (* This should be defined as:

   Definition NM_err_sequence
           {A: Type}
           (mv: NM.t (err A)): err (NM.t A)
           := @NM_sequence A err Monad_err mv.

   But it gives us a problem:

   The term "Monad_err" has type "Monad err" while it is expected to have type
   "Monad (fun B : Type => err B)".

   *)
  Definition NM_err_sequence
             {A: Type}
             (mv: NM.t (err A)): err (NM.t A)
    := NM.fold
         (fun k v acc =>
            match v with
            | inr v' =>
              match acc with
              | inr acc' => inr (NM.add k v' acc')
              | inl msg => inl msg
              end
            | inl msg => inl msg
            end)
         mv
         (inr (@NM.empty A)).

  (* This should use [NM_sequence] directly making [NM_err_sequence] unecessary, but we run into universe inconsistency *)
  Definition translate_mem_block (m:L.mem_block) : err L'.mem_block
    := NM_err_sequence (NM.map translateCTypeValue m).

  Definition translateMExpr (m:L.MExpr) : err L'.MExpr :=
    match m with
    | L.MPtrDeref x => ret (MPtrDeref (translatePExpr x))
    | L.MConst x size =>
      x' <- translate_mem_block x ;;
      size' <- translateNTypeValue size ;;
      ret (MConst x' size')
    end.

  Fixpoint translateAExpr (a:L.AExpr): err L'.AExpr :=
    match a with
    | L.AVar x => ret (AVar x)
    | L.AConst x => x' <- translateCTypeValue x ;; ret (AConst x')
    | L.ANth m n =>
      m' <- translateMExpr m ;;
      n' <- translateNExpr n ;;
      ret (ANth m' n')
    | L.AAbs x =>
      x' <- translateAExpr x ;;
      ret (AAbs x')
    | L.APlus x x0 =>
      x' <- translateAExpr x ;;
      x0' <- translateAExpr x0 ;;
      ret (APlus x' x0')
    | L.AMinus x x0 =>
      x' <- translateAExpr x ;;
      x0' <- translateAExpr x0 ;;
      ret (AMinus x' x0')
    | L.AMult x x0 =>
      x' <- translateAExpr x ;;
      x0' <- translateAExpr x0 ;;
      ret (AMult x' x0')
    | L.AMin x x0 =>
      x' <- translateAExpr x ;;
      x0' <- translateAExpr x0 ;;
      ret (AMin x' x0')
    | L.AMax x x0 =>
      x' <- translateAExpr x ;;
      x0' <- translateAExpr x0 ;;
      ret (AMax x' x0')
    | L.AZless x x0 =>
      x' <- translateAExpr x ;;
      x0' <- translateAExpr x0 ;;
      ret (AZless x' x0')
    end.

  Fixpoint translate (d: L.DSHOperator): err L'.DSHOperator
    :=
      match d with
      | L.DSHNop =>
        ret DSHNop
      | L.DSHAssign src dst =>
        src' <- translateMemRef src ;;
        dst' <- translateMemRef dst ;;
        ret (DSHAssign src' dst')
      | L.DSHIMap n x_p y_p f =>
        f' <- translateAExpr f ;;
        ret (DSHIMap
               n
               (translatePExpr x_p)
               (translatePExpr y_p)
               f')
      | L.DSHBinOp n x_p y_p f =>
        f' <- translateAExpr f ;;
        ret (DSHBinOp
               n
               (translatePExpr x_p)
               (translatePExpr y_p)
               f')
      | L.DSHMemMap2 n x0_p x1_p y_p f =>
        f' <- translateAExpr f ;;
        ret (DSHMemMap2
               n
               (translatePExpr x0_p)
               (translatePExpr x1_p)
               (translatePExpr y_p)
               f')
      | L.DSHPower n src dst f initial =>
        f' <- translateAExpr f ;;
        initial' <- translateCTypeValue initial ;;
        n' <- translateNExpr n ;;
        src' <- translateMemRef src ;;
        dst' <- translateMemRef dst ;;
        ret (DSHPower
               n'
               src' dst'
               f'
               initial')
      | L.DSHLoop n body =>
        body' <- translate body ;;
        ret (DSHLoop
               n
               body')
      | L.DSHAlloc size body =>
        body' <- translate body ;;
        size' <- translateNTypeValue size ;;
        ret (DSHAlloc
               size'
               body')
      | L.DSHMemInit y_p value =>
        value' <- translateCTypeValue value ;;
        ret (DSHMemInit
               (translatePExpr y_p)
               value')
      | L.DSHSeq f g =>
        f' <- translate f ;;
        g' <- translate g ;;
        ret (DSHSeq f' g')
      end.

End MDHCOLTypeTranslator.
