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

Definition varbinding:Type := ident*DSHCOLType.
Definition varbindings:Type := list varbinding.

(* placholder *)
Definition toDSHCOLType (t:term): option DSHCOLType := Some DSHCOLTypeNat.

Require Import Coq.MSets.MSets.
Require Import Coq.MSets.MSetWeakList.
Require Import Coq.MSets.MSetInterface.

Module StringDec.
  Definition t : Set := string.
  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : RelationClasses.Equivalence eq := _.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y} := string_dec.
End StringDec.

Module StringSet := MSets.MSetWeakList.Make StringDec.

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

Fixpoint stripGlobalVars (vars:varbindings) (t:term): option (varbindings*term) :=
  if isSHOperator t then Some (vars,t)
  else
    match t with
    | tLambda (nNamed n) vt b =>
      match toDSHCOLType vt with
      | Some vt' => stripGlobalVars ((n,vt')::vars) b
      | None => None (* Error: non-SHCOL type encountered *)
      end
    | _ => None
    end.

Compute (stripGlobalVars [] dast).

Definition reifySHCOL {i o: nat}
           {fm: Monoid.Monoid RthetaFlags}
           (op: @SHOperator fm i o): TemplateMonad term :=
  ast <- tmQuote op ;;
      tmDefinition "ast" ast ;;
      tmReturn ast.
