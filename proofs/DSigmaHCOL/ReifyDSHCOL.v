Require Import Coq.Strings.String.
Require Import List. Import ListNotations.
Require Import Template.All.

Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.SigmaHCOL.Rtheta.
Require Import Helix.SigmaHCOL.SigmaHCOL.

Import MonadNotation.

(* for testing *)
Require Import Helix.DynWin.DynWin.
Quote Definition dast := Eval cbv delta [dynwin_SHCOL1] in dynwin_SHCOL1.

Inductive DSHCOLType :=
| DSHCOLTypeNat : DSHCOLType
| DSHCOLTypeFinNat (n:nat) : DSHCOLType
| DSHCOLTypeCarrierA : DSHCOLType
| DSHCOLDenseVec (n:nat): DSHCOLType
| DSHCOLSparseVec (n:nat): DSHCOLType.

(* placholder *)
Definition toDSHCOLType (t:term): option DSHCOLType := Some DSHCOLTypeNat.

Require Import Coq.FSets.FSets.
Require Import Coq.FSets.FSetWeakList.
Require Import Coq.FSets.FSetInterface.

Module StringDec.
  Definition t : Set := string.
  Definition eq : t -> t -> Prop := eq.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y} := string_dec.
  Definition eq_refl  := @eq_refl string.
  Definition eq_sym   := @eq_sym string.
  Definition eq_trans := @eq_trans string.
End StringDec.

Module StringSet := FSets.FSetWeakList.Make StringDec.
Module StringMap := FSets.FMapWeakList.Make StringDec.

Definition operator_names :=
  fold_right StringSet.add StringSet.empty
             ["Helix.SigmaHCOL.SigmaHCOL.eUnion" ;
                "Helix.SigmaHCOL.SigmaHCOL.eT" ;
                "Helix.SigmaHCOL.SigmaHCOL.SHPointwise" ;
                "Helix.SigmaHCOL.SigmaHCOL.SHBinOp" ;
                "Helix.SigmaHCOL.SigmaHCOL.SHInductor" ;
                "Helix.SigmaHCOL.SigmaHCOL.IUnion" ;
                "Helix.SigmaHCOL.SigmaHCOL.ISumUnion" ;
                "Helix.SigmaHCOL.SigmaHCOL.IReduction" ;
                "Helix.SigmaHCOL.SigmaHCOL.SHCompose" ;
                "Helix.SigmaHCOL.TSigmaHCOL.SafeCast" ;
                "Helix.SigmaHCOL.TSigmaHCOL.UnSafeCast" ;
                "Helix.SigmaHCOL.TSigmaHCOL.HTSUMUnion"].

Definition isSHOperator (t:term): bool:=
  match t with
  | (tApp (tConst n _) _) => StringSet.mem n operator_names
  | _ => false
  end.

Definition varbindings:Type := StringMap.t DSHCOLType.

Fixpoint stripGlobalParams (vars:varbindings) (t:term): option (varbindings*term) :=
  if isSHOperator t then Some (vars,t)
  else
    match t with
    | tLambda (nNamed n) vt b =>
      match toDSHCOLType vt with
      | Some vt' => stripGlobalParams (StringMap.add n vt' vars) b
      | None => None (* Error: non-SHCOL type encountered *)
      end
    | _ => None
    end.

Definition SHCOL_to_DSHCol {fm i o}: term -> DSHOperator fm i o. Admitted.

Definition varMapToList (v:varbindings): evalContext. Admitted.

Definition reifySHCOL {i o: nat}
           {fm: Monoid.Monoid RthetaFlags}
           (expr: Set): TemplateMonad (option (DSHOperator fm i o)) :=
  ast <- tmQuote expr ;;
      match stripGlobalParams (StringMap.empty DSHCOLType) ast with
      | Some (globals,sterm) =>
        let dshcol := @SHCOL_to_DSHCol fm i o sterm in
        let dshglobals := varMapToList globals in

        tmLemma "foo"
                forall x, forall globals, op (expr globals) x = evalDSHOperator dshglobals dshcol x

        ;; tmReturn (Some dshcol)
      | None => tmReturn None
      end.
