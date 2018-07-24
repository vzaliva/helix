Require Import Coq.Strings.String.
Require Import List. Import ListNotations.
Require Import Template.All.

Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.SigmaHCOL.Rtheta.
Require Import Helix.SigmaHCOL.SigmaHCOL.
Require Import Helix.SigmaHCOL.SVector.

Import MonadNotation.

(* for testing *)
Require Import Helix.DynWin.DynWin.
Quote Definition dast := Eval cbv delta [dynwin_SHCOL1] in dynwin_SHCOL1.

Inductive DSHCOLType :=
| DSHNat : DSHCOLType
| DSHFinNat (n:nat) : DSHCOLType
| DSHCarrierA : DSHCOLType
| DSHVec (n:nat): DSHCOLType
| DSHSafeVec (n:nat): DSHCOLType.

(* placholder *)
Definition toDSHCOLType (t:term): option DSHCOLType := Some DSHNat.

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

Definition varbindings:Type := list (name*term).

Fixpoint stripGlobalParams (vars:varbindings) (t:term): option (varbindings*term*term*term*term) :=
  match t with
  | (tApp (tConst n _) [fm;i;o;_]) => if StringSet.mem n operator_names
                                     then Some (vars,fm,i,o,t)
                                     else None
  | tLambda (nNamed n) vt b =>
    if toDSHCOLType vt then stripGlobalParams ((nNamed n,vt)::vars) b
    else None
  | _ => None
  end.

Definition SHCOL_to_DSHCol {fm i o}: term -> option (DSHOperator fm i o). Admitted.

Fixpoint build_forall g s:=
  match g with
  | [] => s
  | (n,t)::gs => tProd n t (build_forall gs s)
  end.

Record reifyResult := { rei_i: nat;
                        rei_o: nat;
                        rei_fm: Monoid.Monoid RthetaFlags;
                        rei_op: DSHOperator rei_fm rei_i rei_o;
                      }.

Inductive collisionHandling := CollNorm | CollSafe.

Definition fm_select (t:term): option collisionHandling
  := match t with
     | tConst "Helix.SigmaHCOL.Rtheta.Monoid_RthetaFlags" []%list => Some CollNorm
     | tConst "Helix.SigmaHCOL.Rtheta.Monoid_RthetaSafeFlags" []%list => Some CollSafe
     | _ => None
     end.

Definition fm_unquote (t:term): option (Monoid.Monoid RthetaFlags) :=
  match fm_select t with
  | Some CollNorm => Some Monoid_RthetaFlags
  | Some CollSafe => Some Monoid_RthetaSafeFlags
  | None => None
  end.

Definition fm_equiv_term (t:term): option term :=
  match fm_select t with
  | Some CollNorm => Some (tConst "Helix.SigmaHCOL.Rtheta.Rtheta_equiv" [])
  | Some CollSafe => Some (tConst "Helix.SigmaHCOL.Rtheta.RStheta_equiv" [])
  | None => None
  end.

(* TODO: expr as name *)
Definition reifySHCOL (expr: Set) (lemma_name:string): TemplateMonad (option reifyResult) :=
  ast <- tmQuote expr ;;
      match stripGlobalParams [] ast with
      | Some (globals, a_fm, a_i, a_o, sterm) =>
        i <- tmUnquoteTyped nat a_i ;;
          o <- tmUnquoteTyped nat a_o ;;
          match fm_unquote a_fm, fm_equiv_term a_fm with
          | Some fm, Some a_fmeq =>
            match @SHCOL_to_DSHCol fm i o sterm with
            | Some dshcol =>
              let dshglobals := List.map (compose toDSHCOLType snd) globals in
              x <- tmFreshName "x" ;;
                let x_type := tApp (tInd {| inductive_mind := "Coq.Vectors.VectorDef.t"; inductive_ind := 0 |} []) [tApp (tConst "Helix.SigmaHCOL.Rtheta.Rtheta'" []) [a_fm]; a_i] in
                let lhs := tRel 0 in (* TODO: (op (expr globals) x) *)
                let rhs := tRel 0 in (* TODO: (Some (evalDSHOperator dshglobals dshcol x)) *)
                let lemma_concl :=
                    tProd (nNamed x) x_type
                          (tApp (tConst "Helix.Util.VecSetoid.vec_Equiv" [])
                                [tApp (tConst "Helix.SigmaHCOL.Rtheta.Rtheta'" []) [a_fm];
                                   a_fmeq; a_o; lhs; rhs]) in
                let lemma_ast := build_forall globals lemma_concl in

                lemma_body <- tmUnquote lemma_ast ;;
                           tmLemma lemma_name lemma_body
                           ;; tmReturn (Some {| rei_i := i;
                                                rei_o := o;
                                                rei_fm := fm;
                                                rei_op := dshcol |})
            | None => tmReturn None
            end
          | _,_ => tmReturn None
          end
      | None => tmReturn None
      end.
