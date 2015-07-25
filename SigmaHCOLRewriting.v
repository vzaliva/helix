
Require Import Spiral.
Require Import SVector.
Require Import HCOL.
Require Import SigmaHCOL.
Require Import HCOLSyntax.

Require Import Arith.
Require Import Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Program. 

Require Import CpdtTactics.
Require Import CaseNaming.
Require Import Coq.Logic.FunctionalExtensionality.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders.
Require Import MathClasses.orders.minmax MathClasses.orders.orders MathClasses.orders.rings.
Require Import MathClasses.theory.rings MathClasses.theory.abs.

(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

Section SigmaHCOLRewriting.
  Context

    `{Ae: Equiv A}
    `{Az: Zero A} `{A1: One A}
    `{Aplus: Plus A} `{Amult: Mult A} 
    `{Aneg: Negate A}
    `{Ale: Le A}
    `{Alt: Lt A}
    `{Ato: !@TotalOrder A Ae Ale}
    `{Aabs: !@Abs A Ae Ale Az Aneg}
    `{Asetoid: !@Setoid A Ae}
    `{Aledec: !∀ x y: A, Decision (x ≤ y)}
    `{Aeqdec: !∀ x y, Decision (x = y)}
    `{Altdec: !∀ x y: A, Decision (x < y)}
    `{Ar: !Ring A}
    `{ASRO: !@SemiRingOrder A Ae Aplus Amult Az A1 Ale}
    `{ASSO: !@StrictSetoidOrder A Ae Alt}
  .

  Add Ring RingA: (stdlib_ring_theory A).
  
  Open Scope vector_scope.
  Open Scope nat_scope.


  (*
Motivating example:

BinOp(2, Lambda([ r4, r5 ], sub(r4, r5)))

-->

ISumUnion(i3, 2,
  ScatHUnion(2, 1, i3, 1) o
  BinOp(1, Lambda([ r4, r5 ], sub(r4, r5))) o
  GathH(4, 2, i3, 2)
)

    BinOp := (self, o, opts) >> When(o.N=1, o, let(i := Ind(o.N),
        ISumUnion(i, i.range, OLCompose(
        ScatHUnion(o.N, 1, i, 1),
        BinOp(1, o.op),
        GathH(2*o.N, 2, i, o.N)
        )))),

   *)

  Lemma cast_vector_operator_OK_OK: forall i0 i1 o0 o1 (v: vector A i1)
                                      (op: vector A i0 → svector A o0)
    ,
      (i0 ≡ i1 /\ o0 ≡ o1) -> is_OK ((cast_vector_operator
                                      i0 o0
                                      i1 o1
                                      (OK ∘ op)) v).
  Proof.
    intros.
    destruct H as [Hi Ho].
    rewrite <- Ho. clear o1 Ho.
    revert op.
    rewrite Hi. clear i0 Hi.
    intros.

    unfold compose.
    set (e := (λ x : vector A i1, @OK (vector (option A) o0) (op x))).

    assert(is_OK (e v)).
    unfold e. simpl. trivial.
    revert H.
    generalize dependent e. clear op.
    intros.

    rename i1 into i.
    rename o0 into o.
    (* here we arrived to more generic form of the lemma, stating that is_OK property is preserved by 'cast_vector_operator *)

    unfold cast_vector_operator.
    destruct (eq_nat_dec o o), (eq_nat_dec i i); try congruence.

    compute.
    destruct e0.
    dep_destruct e1.
    auto.
  Qed.
  
  Lemma BinOpIsDense: forall o st
                        (f:A->A->A) `{pF: !Proper ((=) ==> (=) ==> (=)) f}
                        (x: svector A (o+o)),
      svector_is_dense x -> 
      is_OK (evalSigmaHCOL st (SHOBinOp o f) x).
  Proof.
    intros. simpl.
    unfold evalBinOp.
    apply dense_casts_OK in H.
    destruct (try_vector_from_svector x).
    apply cast_vector_operator_OK_OK. omega.
    contradiction.
  Qed.

  (* Checks preconditoins of evaluation of SHOGathH to make sure it succeeds*)
  Lemma GathPre: forall (i o nbase nstride: nat) (base stride:aexp) (st:state)
                   (x: svector A i),
      ((evalAexp st base ≡ OK nbase) /\
       (evalAexp st stride ≡ OK nstride) /\
       nstride ≢ 0 /\
       o ≢ 0 /\
       (nbase+o*nstride) < i) ->
      is_OK (evalSigmaHCOL st (SHOGathH (i:=i) (o:=o) base stride) x).
  Proof.
    intros i o nbase nstride base stride st x.
    simpl.
    unfold evalGathH.
    crush.
    destruct (Compare_dec.lt_dec (nbase + o * nstride) i), o, nstride; 
    try match goal with
        | [ H: 0 ≡ 0 -> False |- _ ] => contradiction H; reflexivity
        | [ |- is_OK (OK _) ] => unfold is_OK; trivial
        | [ H0: ?P ,  H1: ~?P |- _] => contradiction
    end.
  Qed.

  Lemma GathInvariant: forall (i o nbase nstride: nat)
                         (base stride:aexp) (st:state)
                         (x: svector A i) (y: svector A o)
                         (n:nat) (HY: n<o) (HX: (nbase + n*nstride) < i)
                         (snz: nstride ≢ 0) (range_bound: (nbase + o*nstride) < i)
    ,
      (evalAexp st base ≡ OK nbase) ->
      (evalAexp st stride ≡ OK nstride) ->
      (evalSigmaHCOL st (SHOGathH (i:=i) (o:=o) base stride) x) ≡ OK y ->
      Vnth x HX ≡ Vnth y HY.
  Proof.
    simpl.
    intros. 

    revert H1.
    unfold evalGathH.
    rewrite H0, H.

    case (eq_nat_dec 0 nstride).
    intros. symmetry in e. contradiction.
    intros Hsnz. 

    case (Compare_dec.lt_dec (nbase + o * nstride) i).
    Focus 2. congruence.
    intros HD. clear range_bound. (* range_bound = HD *)

    intros. injection H1. clear H1.
    unfold SigmaHCOL_Operators.GathH.
    intros. rewrite <- H1. clear H1.
    unfold SigmaHCOL_Operators.vector_index_backward_operator.
    unfold SigmaHCOL_Operators.vector_index_backward_operator_spec.
    destruct (Vbuild_spec _). simpl. rewrite e. clear e.
    unfold SigmaHCOL_Operators.GathBackwardMap_Spec. 
    generalize (SigmaHCOL_Operators.GathBackwardMap_Spec_obligation_1 i o nbase
                                                                      nstride Hsnz HD) as gath_map_oc. intros.
    unfold SigmaHCOL_Operators.VnthIndexMapped.
    simpl.
    generalize (gath_map_oc n HY (nbase + n * nstride) eq_refl) as HX1. clear gath_map_oc.
    intros.
    assert (HX1 ≡ HX). apply proof_irrelevance. rewrite H1.
    reflexivity.
  Qed.

(*          
  Lemma GathIsMap: forall (i o: nat) (base stride:aexp) (st:state)
                            (y: svector A o)
                            (x: svector A i),
      (evalSigmaHCOL st (SHOGathH (i:=i) (o:=o) base stride) x) ≡ OK y ->
      Vforall (Vin_aux x) y.
  Proof.
    intros.

    intros i o base stride st y x.

    unfold evalSigmaHCOL, evalGathH. simpl.
    (*assert ((SigmaHCOL_Operators.GathH i o nbase nstride x) ≡ y).
    injection y. *)
    
    induction y.
        
    intros. apply Vforall_nil.
 
    unfold evalSigmaHCOL, evalGathH. simpl.
    intros.
    rewrite <- Vforall_cons.
    split.
    admit.
    apply IHy.
  Qed.
        
  (* Gath on dense vector produces dense vector *)
  Lemma GathDenseIsDense: forall (i o nbase nstride: nat) (base stride:aexp) (st:state)
                            (y: svector A o)
                            (x: svector A i),
      svector_is_dense x -> 
      (evalSigmaHCOL st (SHOGathH (i:=i) (o:=o) base stride) x) ≡ OK y ->
      svector_is_dense y.
  Proof.
    intros.
    inversion H0.
    revert H2.
    unfold evalGathH.

    
  Qed.
 *)
  
  Definition ASub: A -> A -> A := (plus∘negate).
 
  Global Instance ASub_proper:
    Proper ((=) ==> (=) ==> (=)) (ASub).
  Proof.
    intros a a' aE b b' bE.
    unfold ASub.
    rewrite aE, bE.
    reflexivity.
  Qed.

  Definition op1 := SHOBinOp 2 ASub.
  Definition vari := AValue (Var "i").
  Definition c2 := AConst 2.
  
  Definition op2 :=
    SHOISumUnion (Var "i") c2
                 (SHOCompose _ _
                             (SHOScatHUnion (o:=2) vari c2)
                             (SHOCompose _ _ 
                                         (SHOBinOp 1 ASub)
                                         (SHOGathH (i:=4) (o:=2) vari c2))).

  Lemma testOp2Op1: forall (st : state) (x : vector (option A) (2 + 2)),
      svector_is_dense x -> evalSigmaHCOL st op1 x = evalSigmaHCOL st op2 x.
  Proof.
    intros.
    unfold equiv, maybeError_equiv, op1.
    assert (op1OK: is_OK (evalSigmaHCOL st (SHOBinOp 2 ASub) x)) by (apply BinOpIsDense; assumption).

    case_eq (evalSigmaHCOL st (SHOBinOp 2 ASub) x); intros; simpl in H0, op1OK.

    Focus 2.
    rewrite H0 in op1OK.
    contradiction.

    Set Printing Implicit.
    unfold op2, vari, c2.

    unfold evalSigmaHCOL.
    simpl.

    assert (is_OK
              (@evalGathH A Ae 4 2
                          (update st (Var "i") 1)
                          (AValue (Var "i"))
                          (AConst 2) x)).

(*
      ((evalAexp st base ≡ OK nbase) /\
       (evalAexp st stride ≡ OK nstride) /\
       nstride ≢ 0 /\
       o ≢ 0 /\
       (nbase+o*nstride) < i) ->
*)

    assert(pre_nbase: evalAexp (update st (Var "i") 1) (AValue (Var "i")) ≡ OK 1).
    simpl. unfold update.
    destruct eq_varname_dec. reflexivity.
    congruence.

    assert(pre_nstride: evalAexp (update st (Var "i") 1) (AConst 2) ≡ OK 2).
    simpl. unfold update.
    reflexivity.
    
    apply GathPre with (nbase:=1) (nstride:=2); repeat (split; try assumption; try auto).
    
  Qed.
  
  Section SigmaHCOLRewriting.
