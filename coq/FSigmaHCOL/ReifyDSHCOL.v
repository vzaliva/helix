(* Translates DHCOL on CarrierA to FHCOL *)

Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

Require Import Helix.HCOL.CarrierType.
Require Import Helix.DSigmaHCOL.DSHCOLOnCarrierA.
Require Import Helix.FSigmaHCOL.FSigmaHCOL.
Require Import Helix.MSigmaHCOL.Memory.
Require Import Helix.Util.OptionSetoid.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Import MonadNotation.
Local Open Scope monad_scope.

Definition translatePExpr (p:MDSHCOLOnCarrierA.PExpr): PExpr :=
  match p with
  | MDSHCOLOnCarrierA.PVar x => PVar x
  end.

Fixpoint translateNExpr (n:MDSHCOLOnCarrierA.NExpr) : NExpr :=
  match n with
  | MDSHCOLOnCarrierA.NVar x => NVar x
  | MDSHCOLOnCarrierA.NConst x => NConst x
  | MDSHCOLOnCarrierA.NDiv x x0 => NDiv (translateNExpr x) (translateNExpr x0)
  | MDSHCOLOnCarrierA.NMod x x0 => NMod (translateNExpr x) (translateNExpr x0)
  | MDSHCOLOnCarrierA.NPlus x x0 => NPlus (translateNExpr x) (translateNExpr x0)
  | MDSHCOLOnCarrierA.NMinus x x0 => NMinus (translateNExpr x) (translateNExpr x0)
  | MDSHCOLOnCarrierA.NMult x x0 => NMult (translateNExpr x) (translateNExpr x0)
  | MDSHCOLOnCarrierA.NMin x x0 => NMin (translateNExpr x) (translateNExpr x0)
  | MDSHCOLOnCarrierA.NMax x x0 => NMax (translateNExpr x) (translateNExpr x0)
  end.

Definition translateMemVarRef: MDSHCOLOnCarrierA.MemVarRef -> MemVarRef
  := fun '(p,n) => (translatePExpr p, translateNExpr n).

(* This one is tricky. There are only 2 known constants we know how to translate:
   '1' and '0'. Everything else will trigger an error *)
Definition translateCarrierA (a:CarrierType.CarrierA): option binary64 :=
  if CarrierAequivdec a CarrierAz then Some MDSigmaHCOLEvalSigFloat64.CTypeZero
  else if CarrierAequivdec a CarrierA1 then Some MDSigmaHCOLEvalSigFloat64.CTypeOne
       else None.

(* TODO: Use of generic [NM_sequence] in this context
   causes "universe inconsistency" error when importing this
   module from DynWinProofs.v. This is workaround. To be investigated
   and fixed *)
Definition option_NM_sequence
           {A:Type}
           (mv: NM.t (option A)): option (NM.t A)
  := NM.fold
       (fun k v acc =>
          match v with
          | Some v' =>
            match acc with
            | Some acc' => Some (NM.add k v' acc')
            | None => None
            end
          | None => None
          end)
       mv
       (Some (@NM.empty A)).

Definition translate_mem_block (m:MDSHCOLOnCarrierA.mem_block) : option mem_block
    := option_NM_sequence (NM.map translateCarrierA m).

Definition translateMExpr (m:MDSHCOLOnCarrierA.MExpr) : option MExpr :=
  match m with
  | MDSHCOLOnCarrierA.MVar x => ret (MVar x)
  | MDSHCOLOnCarrierA.MConst x =>
    x' <- translate_mem_block x ;;
       ret (MConst x')
  end.

Fixpoint translateAExpr (a:MDSHCOLOnCarrierA.AExpr): option AExpr :=
  match a with
  | MDSHCOLOnCarrierA.AVar x => ret (AVar x)
  | MDSHCOLOnCarrierA.AConst x => x' <- translateCarrierA x ;; ret (AConst x')
  | MDSHCOLOnCarrierA.ANth m n =>
    m' <- translateMExpr m ;;
       ret (ANth m' (translateNExpr n))
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
  option MDSHCOLOnFloat64.DSHOperator
  :=
    match d with
    | MDSHCOLOnCarrierA.DSHNop =>
      ret DSHNop
    | MDSHCOLOnCarrierA.DSHAssign src dst =>
      ret (DSHAssign
             (translateMemVarRef src)
             (translateMemVarRef dst))
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
         ret (DSHPower
                (translateNExpr n)
                (translateMemVarRef src)
                (translateMemVarRef dst)
                f'
                initial')
    | MDSHCOLOnCarrierA.DSHLoop n body =>
      body' <- DSCHOLtoFHCOL body ;;
            ret (DSHLoop
                   n
                   body')
    | MDSHCOLOnCarrierA.DSHAlloc size body =>
      body' <- DSCHOLtoFHCOL body ;;
            ret (DSHAlloc
                   size
                   body')
    | MDSHCOLOnCarrierA.DSHMemInit size y_p value =>
      value' <- translateCarrierA value ;;
             ret (DSHMemInit
                    size
                    (translatePExpr y_p)
                    value')
    | MDSHCOLOnCarrierA.DSHMemCopy size x_p y_p =>
      ret (DSHMemCopy
             size
             (translatePExpr x_p)
             (translatePExpr y_p))
    | MDSHCOLOnCarrierA.DSHSeq f g =>
      f' <- DSCHOLtoFHCOL f ;;
         g' <- DSCHOLtoFHCOL g ;;
         ret (DSHSeq f' g')
    end.
