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
Definition toDSHCOLType (t:term): option DSHCOLType := None.

(* placholder. tmInferInstance? *)
Definition isSHOperatorInstance (t:term): bool:= false.

Fixpoint stripGlobalVars (vars:varbindings) (t:term): option (varbindings*term) :=
  if isSHOperatorInstance t then Some (vars,t)
  else
    match t with
    | tLambda (nNamed n) vt b =>
      match toDSHCOLType vt with
      | Some vt' => stripGlobalVars ((n,vt')::vars) b
      | None => None (* Error: non-SHCOL type encountered *)
      end
    | _ => None
    end.

Definition reifySHCOL {i o: nat}
           {fm: Monoid.Monoid RthetaFlags}
           (op: @SHOperator fm i o): TemplateMonad term :=
  ast <- tmQuote op ;;
      tmDefinition "ast" ast ;;
      tmReturn ast.
