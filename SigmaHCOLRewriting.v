
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

  Lemma half_plus_less_half_less_than_double {i o:nat} (ip: i<o): i+o < o+o.
  Proof.
    lia.
  Defined.

  Lemma less_half_less_double {i o:nat} (ip: i<o): i< o+o.
  Proof.
    lia.
  Defined.

  Lemma try_vector_from_svector_cons:
    ∀ (n : nat)
      (xh : option A) (xt : vector (option A) n) 
      (th : A) (tt : vector A n),
      try_vector_from_svector (Vcons xh xt) ≡ OK (Vcons th tt)
      → xh ≡ Some th ∧ try_vector_from_svector xt ≡ OK tt.
  Proof.
    intros n xh xt th tt P.
    simpl in P.
    break_match_hyp.
    break_match_hyp.
    assert (C: (Vcons a t) ≡ (Vcons th tt)) by crush.
    apply Vcons_eq_elim in C.
    crush.
    err_ok_elim.
    err_ok_elim.
  Qed.    
  
  Lemma VheadSndVector2Pair {p t0} {x: vector A (p+(S t0))} (P: p < (p+(S t0))):
    Vhead (snd (vector2pair p x)) ≡ Vnth x P.
  Proof.
    unfold vector2pair.
    induction p.
    simpl in *.
    dep_destruct x.
    simpl. reflexivity.
    dep_destruct x.
    simpl.
    apply IHp.
  Qed.

    Lemma try_vector_svector_forall:
      ∀ (n : nat)
        (x : svector A n)
        (t : vector A n),
        try_vector_from_svector x ≡ OK t ->
        Vforall is_Some x.
    Proof.
      intros n x t.
      dependent induction n.
      dep_destruct x.
      crush.
      dep_destruct x. rename h into xh. rename x0 into xt.
      dep_destruct t. rename h into th. rename x0 into tt.

      intros TC.
      apply try_vector_from_svector_cons in TC.
      destruct TC as [TH TT].
      
      simpl.
      split.
      + crush.
      + apply IHn with (t0:=tt); assumption.
    Qed.
    
    Lemma vector_svector_eq:
      ∀ (n : nat)
        (x : svector A n)
        (t : vector A n),
        try_vector_from_svector x ≡ OK t
        → ∀ (i : nat) (ip : i < n), Some (Vnth t ip) ≡ Vnth x ip.
    Proof.
      intros n x t XT i ip.
      unfold try_vector_from_svector in XT.

      destruct n.
      crush.
      dep_destruct x.
      simpl in XT.
    Qed.
    
  Lemma evalBinOpSpec: forall o
                         (f:A->A->A) `{pF: !Proper ((=) ==> (=) ==> (=)) f}
                         (x: svector A (o+o)),
      forall (y: svector A o),
        svector_is_dense x -> 
        ((@evalBinOp A (o + o) o f x) ≡ OK y) ->
        forall (i:nat) (ip:i<o) xva xvb, 
          (Vnth x
                (less_half_less_double ip) ≡ Some xva) ->
          (Vnth x
                (half_plus_less_half_less_than_double ip) ≡ Some xvb) ->
          Vnth y ip ≡ Some (f xva xvb).
  Proof.
    intros o f pF x y D B i ip xva xvb XA XB.

    destruct o as [|o].
    assert(¬i < 0) by apply lt_n_0.
    contradiction.
    
    induction i.
    unfold evalBinOp in B.

    revert B.
    case_eq (try_vector_from_svector x); try congruence.
    intros t T B.
    apply cast_vector_operator_OK_elim in B.

    subst y.
    simpl.

    assert(P1: (o < (o+(S o)))) by lia.
    rewrite VheadSndVector2Pair with (P:=P1).
    rewrite Vnth_tail.

    assert(TX: forall (i:nat) (ip:i < (S o + S o)), Some (Vnth t ip) ≡ Vnth x ip).
      

      
  Qed.
  
  (* Checks preconditoins of evaluation of SHOScatHUnion to make sure it succeeds*)
  Lemma ScatHPre: forall (i o nbase nstride: nat) (base stride:aexp) (st:state)
                   (x: svector A i),
      ((evalAexp st base ≡ OK nbase) /\
       (evalAexp st stride ≡ OK nstride) /\
       ((nbase+(pred i)*nstride) < o) /\
       (nstride ≢ 0)) ->
       is_OK (evalSigmaHCOL st (SHOScatHUnion (i:=i) (o:=o) base stride) x).
  Proof.
    intros.
    crush.
    unfold evalScatHUnion.
    crush.
    destruct lt_dec, eq_nat_dec; err_ok_elim.
    contradiction n0.
    contradiction n.
  Qed.

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
    destruct lt_dec, eq_nat_dec; err_ok_elim.
    contradiction.
  Qed.

  Lemma GatHInvariant: forall (i o nbase nstride: nat)
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
    - intros. contradiction.
    - intros Hsnz. 
      case lt_dec.
      + intros HD. clear range_bound. (* range_bound = HD *)
        intros.
        injection H1. clear H1.
        unfold GathH.
        intros.
        
        apply Gather_spec with (IndexFunctions.h_index_map nbase nstride) x y n HY in H1 .
        rewrite H1.
        unfold VnthIndexMapped.
        simpl.
        generalize (IndexFunctions.h_index_map_obligation_1 o i nbase nstride HD Hsnz n
                                                            HY) as gath_map_oc.
        intros.
        assert (gath_map_oc ≡ HX). apply proof_irrelevance.
        rewrite H2.
        reflexivity.
      + congruence.
  Qed.
    
  (* GatH on dense vector produces dense vector *)
  Lemma GatHDensePost: forall (i o: nat) (base stride:aexp) (st:state)
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
    destruct (eq_nat_dec n0 0); try congruence.
    destruct lt_dec; try congruence.
    inversion 1.
    unfold GathH in *.
    apply Gather_preserves_density; try assumption.
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

  Definition MaybeVnth {B : Type} (n : nat)
             (el: @maybeError (svector B n)) {i: nat} {ip: i < n}: option B :=
    match el with
    | Error _ => None
    | OK l => Vnth l ip
    end.

  Lemma SparseUnionOK (n m:nat) (l: vector (@maybeError (svector A m)) n) (z: svector A m):
    (forall (i:nat) (ip: i<m),
        exists j (jp: j<n),
          (
            (exists lj (ljOK: Vnth l jp ≡ OK lj), is_Some (Vnth lj ip))
            /\
            (forall j' (j'p: j'<n),
                (exists lj' (lj'OK: Vnth l j'p ≡ OK lj'), is_Some (Vnth lj' ip))
                -> j' ≡ j)
    ))
    -> is_OK (Vfold_left ErrSparseUnion (OK z) l).
  Proof.
    unfold is_OK.
    destruct (Vfold_left ErrSparseUnion (OK z) l) eqn:VFOK.
    admit.
    admit.
    
  Qed.
      
  Lemma BinOpSums
        (o: nat)
        {onz: 0 ≢ o} 
        (f:A->A->A)
        (var:varname)
        (sstride gstride:aexp)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}
        (st : state) (x : vector (option A) (o + o))
        (gstrideE: evalsToWithVar var st gstride o)
        (sstrideE: evalsToWithVar var st sstride o)
        (xdense: svector_is_dense x):
    
    evalSigmaHCOL st (SHOBinOp o f) x =
    evalSigmaHCOL st (SHOISumUnion var (AConst o)
                                   (SHOCompose _ _
                                               (SHOScatHUnion (AValue var) sstride)
                                               (SHOCompose _ _ 
                                                           (SHOBinOp 1 f)
                                                           (SHOGathH (i:=o+o) (AValue var) gstride)))) x.
  Proof.

    (* unfold left part and assure it is always OK *)
    unfold evalSigmaHCOL at 1.
    assert(BOK': is_OK (@evalBinOp A (o + o) o f x))
      by (apply BinOpPre; assumption).    
    destruct (evalBinOp f x) eqn: BOK; err_ok_elim.

    (* binop output is dense *)
    assert (TD: evalSigmaHCOL st (SHOBinOp o f) x ≡ OK t). auto.
    apply BinOpPost in TD.

    (* unfold right part *)
    unfold evalSigmaHCOL.
    destruct (evalAexp st (AConst o)) eqn: AO.
    simpl in AO. inversion AO as [ON]. clear AO. subst n.
    break_match_goal; try congruence.
    Focus 2. simpl in AO. congruence.
    clear onz.

    symmetry.

    remember (fix en (n' : nat) (np : n' < S n) {struct n'} :
           @maybeError (vector (option A) (S n)) :=
           match
             match
               @evalGathH A Ae (S n + S n) (1 + 1) 
                 (update st var n') (AValue var) gstride x
             with
             | OK gv => @evalBinOp A (1 + 1) 1 f gv
             | Error msg => @Error (vector (option A) 1) msg
             end
           with
           | OK gv =>
               @evalScatHUnion A Ae 1 (S n) (update st var n') 
                 (AValue var) sstride gv
           | Error msg => @Error (vector (option A) (S n)) msg
           end)  as f1 eqn:HF1.
    
    assert (MOK: Vforall is_OK (Vbuild f1)).
    {
      unfold Vbuild.
      destruct (Vbuild_spec f1) eqn: ff.
      simpl.
      apply Vforall_nth_intro.

      assert (e' : ∀ (i : nat) (ip : i < S n), f1 i ip ≡ Vnth x0 ip).
      {
        intros. symmetry. apply e.
      }
      intros.
      specialize e' with (i:=i) (ip:=ip).
      rewrite <- e'. 

      subst f1.

      (* To get rid of 'fix', even though the function is not
      recrusive we need to destruct the argument.*)

      destruct i.

      assert(gOK: is_OK (@evalGathH A Ae (S n + S n) (1 + 1) (update st var 0) 
                                      (AValue var) gstride x)).
      {
        apply GathPre with (nbase:=0) (nstride:=S n).
        split. apply update_eval.
        split. apply gstrideE.
        split. auto.
        simpl.
        nia.
      } 
      case_eq  (@evalGathH A Ae (S n + S n) (1 + 1) (update st var 0) 
                           (AValue var) gstride x).
      Focus 2. intros s C. rewrite C in gOK. err_ok_elim.
      
      intros g G.
      apply GatHDensePost in G; try assumption. 

      assert (bOK: is_OK (@evalBinOp A (1 + 1) 1 f g)).
      {
        apply BinOpPre; assumption.
      }
      
      destruct (@evalBinOp A (1 + 1) 1 f g)  eqn: B1OK; err_ok_elim.

      assert (SOK: is_OK (@evalScatHUnion A Ae 1 (S n) (update st var 0) (AValue var) sstride t0)).
      {
        intros.
        apply ScatHPre with (nbase:=0) (nstride:=S n).
        split. apply update_eval.
        split. apply sstrideE.
        simpl.
        split.
        lia.
        auto.
      }
      crush.

      (* Done with '0' on 'n' *)

      assert(gOK: is_OK (@evalGathH A Ae (S n + S n) (1 + 1) (update st var (S i)) 
                                    (AValue var) gstride x)).
      {
        apply GathPre with (nbase:=(S i)) (nstride:=S n).
        split. apply update_eval.
        split. apply gstrideE.
        split. auto.
        simpl.
        omega.
      } 
      case_eq  (@evalGathH A Ae (S n + S n) (1 + 1) (update st var (S i)) 
                                    (AValue var) gstride x).
      Focus 2. intros s C. rewrite C in gOK. err_ok_elim.

      intros g G.
      apply GatHDensePost in G; try assumption. 

      assert (bOK: is_OK (@evalBinOp A (1 + 1) 1 f g)).
      {
        apply BinOpPre; assumption.
      }
      
      destruct (@evalBinOp A (1 + 1) 1 f g)  eqn: B1OK; err_ok_elim.

      assert (SOK: is_OK (@evalScatHUnion A Ae 1 (S n) (update st var (S i)) (AValue var) sstride t0)).
      {
        intros.
        apply ScatHPre with (nbase:=S i) (nstride:=S n).
        split. apply update_eval.
        split. apply sstrideE.
        simpl.
        split.
        omega.
        auto.
      }
      crush.
    }
    
    assert (FOK: is_OK (Vfold_left ErrSparseUnion (OK (empty_svector (S n)))
                                   (Vbuild f1))).
    apply SparseUnionOK.

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
