
Require Import Spiral.
Require Import SVector.
Require Import HCOL.
Require Import SigmaHCOL.
Import SigmaHCOL_Operators.
Require Import HCOLSyntax.

Require Import Arith.
Require Import Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Program. 

Require Import CpdtTactics.
Require Import JRWTactics.
Require Import CaseNaming.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Psatz.


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
  Global Open Scope nat_scope.


  (*
Motivating example:

BinOp(2, Lambda([ r4, r5 ], sub(r4, r5)))

-->

ISumUnion(i3, 2,
  ScatHUnion(2, 1, i3, 1) o
  BinOp(1, Lambda([ r4, r5 ], sub(r4, r5))) o
  GathH(N=4, n=2, base=i3, stride=2)
)

Loop:
1.  GathH(N=4, n=2, base=0, stride=2)
    for j={0,1}: base+j*stride:
             0+0*2=0
             0+1*2=2
1.  GathH(N=4, n=2, base=1, stride=2)
    for j={0,1}: base+j*stride:
             1+0*2=1
             1+1*2=3

Pre-condition:
    (base + (n-1)*stride) < N

    base + n*sride - stride < N
    base + n*stride < N+stride 


    BinOp := (self, o, opts) >> When(o.N=1, o, let(i := Ind(o.N),
        ISumUnion(i, i.range, OLCompose(
        ScatHUnion(o.N, 1, i, 1),
        BinOp(1, o.op),
        GathH(2*o.N, 2, i, o.N)
        )))),

   *)

  Lemma BinOpPre: forall o st
                    (f:A->A->A) `{pF: !Proper ((=) ==> (=) ==> (=)) f}
                    (x: svector A (o+o)),
      svector_is_dense x -> 
      is_OK (evalSigmaHCOL st (SHOBinOp o f) x).
  Proof.
    intros. simpl.
    unfold evalBinOp.
    apply dense_casts_OK in H.
    destruct (try_vector_from_svector x).
    - apply cast_vector_operator_OK_OK. omega.
    - contradiction.
  Qed.

  Lemma BinOpPost: forall o st
                     (f:A->A->A) `{pF: !Proper ((=) ==> (=) ==> (=)) f}
                     (x: svector A (o+o)),
      forall (v: svector A o),
        (evalSigmaHCOL st (SHOBinOp o f) x ≡ OK v) -> svector_is_dense v.
  Proof.
    simpl.
    intros.
    revert H.
    unfold evalBinOp.
    destruct (try_vector_from_svector x).
    - intros.
      apply cast_vector_operator_OK_elim in H.
      apply svector_from_vector_is_dense in H.
      assumption.
    - intros.
      inversion H.
  Qed.

  
  (* Checks preconditoins of evaluation of SHOScatHUnion to make sure it succeeds*)
  Lemma ScatPre: forall (i o nbase npad: nat) (base pad:aexp) (st:state)
                   (x: svector A i),
      ((evalAexp st base ≡ OK nbase) /\
       (evalAexp st pad ≡ OK npad) /\
       (o ≡ (nbase + S npad * i))) ->
      is_OK (evalSigmaHCOL st (SHOScatHUnion  (i:=i) (o:=o) base pad) x).
  Proof.
    (* TODO! *)
  Admitted.

  (* Checks preconditoins of evaluation of SHOGathH to make sure it succeeds*)
  Lemma GathPre: forall (i o nbase nstride: nat) (base stride:aexp) (st:state)
                   (x: svector A i),
      ((evalAexp st base ≡ OK nbase) /\
       (evalAexp st stride ≡ OK nstride) /\
       nstride ≢ 0 /\
       (nbase+(pred o)*nstride) < i) ->
      is_OK (evalSigmaHCOL st (SHOGathH (i:=i) (o:=o) base stride) x).
  Proof.
    intros i o nbase nstride base stride st x.
    simpl.
    unfold evalGathH.
    crush.
    destruct lt_dec, nstride; err_ok_elim.
    contradiction.
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

    case eq_nat_dec.
    - intros. symmetry in e. contradiction.
    - intros Hsnz. 
      case lt_dec.
      + intros HD. clear range_bound. (* range_bound = HD *)
        intros. injection H1. clear H1.
        unfold GathH.
        intros. rewrite <- H1. clear H1.
        unfold vector_index_backward_operator.
        unfold vector_index_backward_operator_spec.
        destruct (Vbuild_spec _). simpl. rewrite e. clear e.
        unfold GathBackwardMap_Spec. 
        generalize (GathBackwardMap_Spec_obligation_1 i o nbase
                                                      nstride Hsnz HD) as gath_map_oc. intros.
        unfold VnthIndexMapped.
        simpl.
        generalize (gath_map_oc n HY (nbase + n * nstride) eq_refl) as HX1. clear gath_map_oc.
        intros.
        assert (HX1 ≡ HX). apply proof_irrelevance. rewrite H1.
        reflexivity.
      + congruence.
  Qed.

  
  (* Gath on dense vector produces dense vector *)
  
  Lemma gath_map_surj:
    ∀ (i o base stride : nat) (snz : 0 ≢ stride) (range_bound : base + pred o * stride < i),
      index_map_is_surjective i o
                                   (GathBackwardMap_Spec
                                      (snz:=snz)
                                      (range_bound:=range_bound)
                                      i o base stride).
  Proof.
    unfold index_map_is_surjective.
    simpl.
    trivial.
  Qed.
  
  Lemma GathDensePost: forall (i o: nat) (base stride:aexp) (st:state)
                         (y: svector A o)
                         (x: svector A i),
      svector_is_dense x -> 
      (evalSigmaHCOL st (SHOGathH (i:=i) (o:=o) base stride) x) ≡ OK y ->
      svector_is_dense y.
  Proof.
    simpl.
    intros.
    revert H0.
    unfold evalGathH.
    destruct (evalAexp st base); try congruence.
    destruct (evalAexp st stride); try congruence.
    destruct (eq_nat_dec 0 n0); try congruence.
    destruct lt_dec; try congruence.
    inversion 1.
    unfold GathH in *.
    apply vector_index_backward_operator_is_dense; try assumption.
    apply gath_map_surj.
  Qed.


  (* Ensures that variable var is not affecting evaluation of expression. to prove it all we need to make sure it is free in exp *)
  Definition evalsToWithVar
             (var:varname)
             (st:state)
             (exp: aexp)
             (v:nat) :=
    forall (x:nat), evalAexp (update st var x) exp ≡ OK v.
  

  Lemma const_eval_OK:
    forall st x, evalAexp st (AConst x) ≡ OK x.
  Proof.
    auto.
  Qed.
  
  Set Printing Implicit.
  
  Lemma BinOpSums
        (o: nat)
        {onz: 0 ≢ o} 
        (f:A->A->A)
        (var:varname)
        (pad stride:aexp)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}
        (st : state) (x : vector (option A) (o + o))
        (padE: evalsToWithVar var st pad o)
        (strideE: evalsToWithVar var st stride o)
        (xdense: svector_is_dense x):
    
    evalSigmaHCOL st (SHOBinOp o f) x =
    evalSigmaHCOL st (SHOISumUnion var (AConst o)
                                   (SHOCompose _ _
                                               (SHOScatHUnion (AValue var) pad)
                                               (SHOCompose _ _ 
                                                           (SHOBinOp 1 f)
                                                           (SHOGathH (i:=o+o) (AValue var) stride)))) x.
  Proof.
    intros.
    unfold evalSigmaHCOL at 1.
    assert(b1OK: is_OK (@evalBinOp A (o + o) o st f x)).
    {
      apply BinOpPre;
      assumption.
    }
    (* LHS taken care of *)
    unfold evalSigmaHCOL at 1.
    break_match_goal; try (simpl in Heqm; err_ok_elim).
    inversion Heqm as [ON]. rewrite <- ON. clear ON.
    break_match_goal; try congruence. 
    induction n0.
    + simpl.
      assert(gOK: is_OK (@evalGathH A Ae 2 2 (update st var 0) (AValue var) stride x)).
      {
        apply GathPre with (nbase:=0) (nstride:=1).
        split. apply update_eval.
        split. apply strideE.
        split; auto.
      } 
      case_eq (@evalGathH A Ae 2 2 (update st var 0) (AValue var) stride x).
      Focus 2. intros s C. rewrite C in gOK. err_ok_elim.

      intros.
      apply GathDensePost in H; try assumption.
      assert(bOK: is_OK (@evalBinOp A 2 1 (update st var 0) f t))
        by (apply BinOpPre; assumption).

      case_eq (@evalBinOp A 2 1 (update st var 0) f t).
      Focus 2. intros s C. rewrite C in bOK. err_ok_elim.

      intros.
      
      assert(sOK: is_OK (@evalScatHUnion A 1 1 (update st var 0) (AValue var) pad t0)).
      {
        apply ScatPre with (nbase:=0) (npad:=1).
        split. apply update_eval.
        split. apply padE.
        (* Something serously wrong here. Perhaps induction was wrong approach *)
        split; auto.
      }

      
  Qed.
  



  (* --- Test on an example --- *)

  
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
    appy BinOpSums.
  Qed.
  
  Section SigmaHCOLRewriting.
