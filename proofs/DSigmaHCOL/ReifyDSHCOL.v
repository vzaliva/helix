Require Import Coq.Strings.String.
Require Import List.
Require Import Template.All.

Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.SigmaHCOL.Rtheta.
Require Import Helix.SigmaHCOL.SigmaHCOL.
Require Import Helix.SigmaHCOL.SVector.
Require Import Helix.Util.VecSetoid.
Require Import Helix.Util.OptionSetoid.

Import MonadNotation.
Import ListNotations.

(* for testing *)

Require Import Helix.DynWin.DynWin.
Quote Definition dast := Eval hnf in dynwin_SHCOL1.

Inductive DSHCOLType :=
| DSHnat : DSHCOLType
| DSHCarrierA : DSHCOLType
| DSHvec (n:nat): DSHCOLType.

(* placholder *)
Definition toDSHCOLType (t:term): option DSHCOLType := Some DSHnat.

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
  List.fold_right StringSet.add StringSet.empty
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

(* Find operator in given term. If it is preceeded by lambdas, add them to `varbindings` provided *)
Fixpoint findOp (vars:varbindings) (t:term): option (varbindings*term*term*term*term) :=
  match t with
  | tApp (tConst n _) (fm :: i :: o :: _)
    => (if StringSet.mem n operator_names
       then Some (vars,fm,i,o,t)
       else None)
  | tLambda (nNamed n) vt b =>
    (if toDSHCOLType vt then findOp ((nNamed n,vt)::vars) b
     else None)
  | _ => None
  end.

Definition SHCOL_to_DSHCol {i o} (t:term): option (DSHOperator i o) := Some (@DSHDummy i o).

Fixpoint build_forall g s:=
  match g with
  | [] => s
  | (n,t)::gs => tProd n t (build_forall gs s)
  end.

Record reifyResult := { rei_i: nat;
                        rei_o: nat;
                        rei_op: DSHOperator rei_i rei_o;
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

Fixpoint quoteNat (n:nat) : term :=
  match n with
  | O => tConstruct {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} 0 []
  | S p => tApp (tConstruct {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} 1 []) [quoteNat p]
  end.

Fixpoint build_dsh_globals (g:varbindings) : option term :=
  match g with
  | [] => Some (tApp (tConstruct {| inductive_mind := "Coq.Init.Datatypes.list"; inductive_ind := 0 |} 0 []) [tInd {| inductive_mind := "Helix.DSigmaHCOL.DSigmaHCOL.DSHVar"; inductive_ind := 0 |} []])
  | (n,t)::gs =>
    match toDSHCOLType t with
    | None => None
    | Some dt =>
      let i := length g in
      let dv := (match dt with
                 | DSHnat => tApp (tConstruct {| inductive_mind := "Helix.DSigmaHCOL.DSigmaHCOL.DSHVar"; inductive_ind := 0 |} 0 []) [tRel i]
                 | DSHCarrierA => tApp (tConstruct {| inductive_mind := "Helix.DSigmaHCOL.DSigmaHCOL.DSHVar"; inductive_ind := 0 |} 1 []) [tRel i]
                 | DSHvec n => tApp (tConstruct {| inductive_mind := "Helix.DSigmaHCOL.DSigmaHCOL.DSHVar"; inductive_ind := 0 |} 2 [])
                                   [quoteNat n; tRel i]
                 end) in
      match build_dsh_globals gs with
      | Some ts =>  Some (tApp (tConstruct {| inductive_mind := "Coq.Init.Datatypes.list"; inductive_ind := 0 |} 1 []) [tInd {| inductive_mind := "Helix.DSigmaHCOL.DSigmaHCOL.DSHVar"; inductive_ind := 0 |} []; tRel i; ts])
      | None => None
      end
    end
  end.

(*

Definition fm: Monoid.Monoid RthetaFlags := Monoid_RthetaFlags.
Parameter dshcol : DSHOperator (1 + (2 + 2)) 1.
Definition lfoo := forall (a: avector 3),
    forall (x: svector fm (1 + (2 + 2))),
      option_Equiv
        (Some (densify fm (op fm (dynwin_SHCOL1 a) x)))
        (evalDSHOperator [] dshcol (densify fm x)).

Quote Definition l := Eval hnf in lfoo.
Print l.

Set Printing All. Print lfoo.

lfoo =
forall (a : t CarrierA (S (S (S O))))
  (x : svector fm (Nat.add (S O) (Nat.add (S (S O)) (S (S O))))),
@option_Equiv (t CarrierA (S O)) (@vec_Equiv CarrierA CarrierAe (S O))

  (@Some (t CarrierA (S O))
     (@densify fm (S O)
        (@op fm (Nat.add (S O) (Nat.add (S (S O)) (S (S O)))) (S O) (dynwin_SHCOL1 a) x)))

  (@evalDSHOperator (Nat.add (S O) (Nat.add (S (S O)) (S (S O))))
     (S O) (@Datatypes.nil DSHVar) dshcol
     (@densify fm (Nat.add (S O) (Nat.add (S (S O)) (S (S O)))) x))
     : Prop
 *)


Fixpoint rev_nat_seq_to_1 (len: nat) : list nat :=
  match len with
  | O => []
  | S len' => List.cons len (rev_nat_seq_to_1 len')
  end.

Definition reifySHCOL {A:Type} (expr: A) (lemma_name:string): TemplateMonad (option reifyResult) :=
  a_expr <- @tmQuote A expr ;;
         eexpr <- @tmEval hnf A expr  ;;
         ast <- @tmQuote A eexpr ;;
         match findOp [] ast with
         | Some (globals, a_fm, a_i, a_o, sterm) =>
           i <- tmUnquoteTyped nat a_i ;;
             o <- tmUnquoteTyped nat a_o ;;
             match fm_unquote a_fm, fm_equiv_term a_fm with
             | Some fm, Some a_fmeq =>
               match @SHCOL_to_DSHCol i o sterm, build_dsh_globals globals with
               | Some dshcol, Some dshglobals =>
                 x <- tmFreshName "x" ;;
                   let x_type := tApp (tInd {| inductive_mind := "Coq.Vectors.VectorDef.t"; inductive_ind := 0 |} []) [tApp (tConst "Helix.SigmaHCOL.Rtheta.Rtheta'" []) [a_fm]; a_i] in
                   let global_idx := List.map tRel (rev_nat_seq_to_1 (length globals)) in
                   (* Some (densify fm (op fm (dynwin_SHCOL1 a) x)) *)
                   let lhs := tApp
                                (tConstruct {| inductive_mind := "Coq.Init.Datatypes.option"; inductive_ind := 0 |} 0 [])
                                [tApp (tInd {| inductive_mind := "Coq.Vectors.VectorDef.t"; inductive_ind := 0 |} [])
                                      [tConst "Helix.HCOL.CarrierType.CarrierA" []; a_o];
                                   tApp (tConst "Helix.SigmaHCOL.SVector.densify" [])
                                        [a_fm; a_o;
                                           tApp (tConst "Helix.SigmaHCOL.SigmaHCOL.op" [])
                                                [a_fm;
                                                   a_i;
                                                   a_o;
                                                   tApp a_expr global_idx;
                                                   tRel 0]]] in
                   (* evalDSHOperator [] dshcol (densify fm x) *)
                   a_dshcol <- tmQuote dshcol ;;

                            let rhs := tApp (tConst "Helix.DSigmaHCOL.DSigmaHCOL.evalDSHOperator" [])
                                            [a_i; a_o; dshglobals ; a_dshcol;
                                               (tApp (tConst "Helix.SigmaHCOL.SVector.densify" [])
                                                     [a_fm; a_i; tRel 0])
                                            ] in
                            let lemma_concl :=
                                tProd (nNamed x) x_type
                                      (tApp (tConst "Helix.Util.OptionSetoid.option_Equiv" [])
                                            [
                                              (tApp (tInd {| inductive_mind := "Coq.Vectors.VectorDef.t"; inductive_ind := 0 |} []) [tConst "Helix.HCOL.CarrierType.CarrierA" []; a_i]);
                                                (tApp (tConst "Helix.Util.VecSetoid.vec_Equiv" [])
                                                      [tConst "Helix.HCOL.CarrierType.CarrierA" [];
                                                         tConst "Helix.HCOL.CarrierType.CarrierAe" [];
                                                         a_o]);
                                                lhs;
                                                rhs
                                      ]) in
                            let lemma_ast := build_forall globals lemma_concl in

                            (tmBind (tmUnquoteTyped Prop lemma_ast)
                                    (fun lemma_body => tmLemma lemma_name lemma_body
                                                            ;;
                                                            tmReturn (Some {| rei_i := i;
                                                                              rei_o := o;
                                                                              rei_op := dshcol |})))
               | _,_ => tmReturn None
               end
             | _,_ => tmReturn None
             end
         | None => tmReturn None
         end.


Run TemplateProgram (reifySHCOL dynwin_SHCOL1 "bar").
