(* Translates DHCOL on CarrierA to FHCOL *)

Require Import Coq.Strings.String.
Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

Require Import Helix.HCOL.CarrierType.
Require Import Helix.DSigmaHCOL.DSHCOLOnCarrierA.
Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.FSigmaHCOL.Int64asNT.
Require Import Helix.FSigmaHCOL.Float64asCT.
Require Import Helix.MSigmaHCOL.Memory.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.Util.ErrorSetoid.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Import MonadNotation.
Open Scope monad_scope.
Open Scope string_scope.

Definition translatePExpr (p:MDSHCOLOnCarrierA.PExpr): PExpr :=
  match p with
  | MDSHCOLOnCarrierA.PVar x => PVar x
  end.

Fixpoint translateNExpr (n:MDSHCOLOnCarrierA.NExpr) : err NExpr :=
  match n with
  | MDSHCOLOnCarrierA.NVar x => inr (NVar x)
  | MDSHCOLOnCarrierA.NConst x =>
    x' <- MInt64asNT.from_nat x ;; ret (NConst x')
  | MDSHCOLOnCarrierA.NDiv x x0 => liftM2 NDiv (translateNExpr x) (translateNExpr x0)
  | MDSHCOLOnCarrierA.NMod x x0 => liftM2 NMod (translateNExpr x) (translateNExpr x0)
  | MDSHCOLOnCarrierA.NPlus x x0 => liftM2 NPlus (translateNExpr x) (translateNExpr x0)
  | MDSHCOLOnCarrierA.NMinus x x0 => liftM2 NMinus (translateNExpr x) (translateNExpr x0)
  | MDSHCOLOnCarrierA.NMult x x0 => liftM2 NMult (translateNExpr x) (translateNExpr x0)
  | MDSHCOLOnCarrierA.NMin x x0 => liftM2 NMin (translateNExpr x) (translateNExpr x0)
  | MDSHCOLOnCarrierA.NMax x x0 => liftM2 NMax (translateNExpr x) (translateNExpr x0)
  end.

Definition translateMemRef: MDSHCOLOnCarrierA.MemRef -> err MemRef
  := fun '(p,n) =>
       n' <- translateNExpr n ;;
       ret (translatePExpr p, n').

Set Universe Polymorphism.
(* This one is tricky. There are only 2 known constants we know how to translate:
   '1' and '0'. Everything else will trigger an error *)
Definition translateCarrierA (a:CarrierA): err binary64 :=
  if CarrierAequivdec a CarrierAz then inr MFloat64asCT.CTypeZero
  else if CarrierAequivdec a CarrierA1 then inr MFloat64asCT.CTypeOne
       else (inl "unknown CarrierA constaant").

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
Definition translate_mem_block (m:MDSHCOLOnCarrierA.mem_block) : err mem_block
  := NM_err_sequence (NM.map translateCarrierA m).

Definition translateMExpr (m:MDSHCOLOnCarrierA.MExpr) : err MExpr :=
  match m with
  | MDSHCOLOnCarrierA.MPtrDeref x => ret (MPtrDeref (translatePExpr x))
  | MDSHCOLOnCarrierA.MConst x size =>
    x' <- translate_mem_block x ;;
    size' <- MInt64asNT.from_nat size ;;
       ret (MConst x' size')
  end.

Fixpoint translateAExpr (a:MDSHCOLOnCarrierA.AExpr): err AExpr :=
  match a with
  | MDSHCOLOnCarrierA.AVar x => ret (AVar x)
  | MDSHCOLOnCarrierA.AConst x => x' <- translateCarrierA x ;; ret (AConst x')
  | MDSHCOLOnCarrierA.ANth m n =>
    m' <- translateMExpr m ;;
    n' <- translateNExpr n ;;
       ret (ANth m' n')
  | MDSHCOLOnCarrierA.AAbs x =>
    x' <- translateAExpr x ;;
       ret (AAbs x')
  | MDSHCOLOnCarrierA.APlus x x0 =>
    x' <- translateAExpr x ;;
       x0' <- translateAExpr x0 ;;
       ret (APlus x' x0')
  | MDSHCOLOnCarrierA.AMinus x x0 =>
    x' <- translateAExpr x ;;
       x0' <- translateAExpr x0 ;;
       ret (AMinus x' x0')
  | MDSHCOLOnCarrierA.AMult x x0 =>
    x' <- translateAExpr x ;;
       x0' <- translateAExpr x0 ;;
       ret (AMult x' x0')
  | MDSHCOLOnCarrierA.AMin x x0 =>
    x' <- translateAExpr x ;;
       x0' <- translateAExpr x0 ;;
       ret (AMin x' x0')
  | MDSHCOLOnCarrierA.AMax x x0 =>
    x' <- translateAExpr x ;;
       x0' <- translateAExpr x0 ;;
       ret (AMax x' x0')
  | MDSHCOLOnCarrierA.AZless x x0 =>
    x' <- translateAExpr x ;;
       x0' <- translateAExpr x0 ;;
       ret (AZless x' x0')
  end.

Fixpoint DSCHOLtoFHCOL (d: MDSHCOLOnCarrierA.DSHOperator):
  err MDSHCOLOnFloat64.DSHOperator
  :=
    match d with
    | MDSHCOLOnCarrierA.DSHNop =>
      ret DSHNop
    | MDSHCOLOnCarrierA.DSHAssign src dst =>
      src' <- translateMemRef src ;;
      dst' <- translateMemRef dst ;;
      ret (DSHAssign src' dst')
    | MDSHCOLOnCarrierA.DSHIMap n x_p y_p f =>
      f' <- translateAExpr f ;;
         ret (DSHIMap
                n
                (translatePExpr x_p)
                (translatePExpr y_p)
                f')
    | MDSHCOLOnCarrierA.DSHBinOp n x_p y_p f =>
      f' <- translateAExpr f ;;
         ret (DSHBinOp
                n
                (translatePExpr x_p)
                (translatePExpr y_p)
                f')
    | MDSHCOLOnCarrierA.DSHMemMap2 n x0_p x1_p y_p f =>
      f' <- translateAExpr f ;;
         ret (DSHMemMap2
                n
                (translatePExpr x0_p)
                (translatePExpr x1_p)
                (translatePExpr y_p)
                f')
    | MDSHCOLOnCarrierA.DSHPower n src dst f initial =>
      f' <- translateAExpr f ;;
      initial' <- translateCarrierA initial ;;
      n' <- translateNExpr n ;;
      src' <- translateMemRef src ;;
      dst' <- translateMemRef dst ;;
      ret (DSHPower
             n'
             src' dst'
             f'
             initial')
    | MDSHCOLOnCarrierA.DSHLoop n body =>
      body' <- DSCHOLtoFHCOL body ;;
            ret (DSHLoop
                   n
                   body')
    | MDSHCOLOnCarrierA.DSHAlloc size body =>
      body' <- DSCHOLtoFHCOL body ;;
      size' <- MInt64asNT.from_nat size ;;
            ret (DSHAlloc
                   size'
                   body')
    | MDSHCOLOnCarrierA.DSHMemInit size y_p value =>
      value' <- translateCarrierA value ;;
      size' <- MInt64asNT.from_nat size ;;
             ret (DSHMemInit
                    size'
                    (translatePExpr y_p)
                    value')
    | MDSHCOLOnCarrierA.DSHMemCopy size x_p y_p =>
      size' <- MInt64asNT.from_nat size ;;
      ret (DSHMemCopy
             size'
             (translatePExpr x_p)
             (translatePExpr y_p))
    | MDSHCOLOnCarrierA.DSHSeq f g =>
      f' <- DSCHOLtoFHCOL f ;;
         g' <- DSCHOLtoFHCOL g ;;
         ret (DSHSeq f' g')
    end.
