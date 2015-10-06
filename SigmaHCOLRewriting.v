
Require Import Spiral.
Require Import SVector.
Require Import HCOL.
Require Import SigmaHCOL.
Import SigmaHCOL_Operators.
Require Import HCOLSyntax.

Require Import Arith.
Require Import Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.ProofIrrelevance.
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
    
    Lemma try_vector_from_svector_elementwise:
      ∀ (n : nat)
        (x : svector A n)
        (t : vector A n),
        try_vector_from_svector x ≡ OK t ->
        ∀ (i : nat) (ip : i < n), Some (Vnth t ip) ≡ Vnth x ip.
    Proof.
      intros n x t X i ip.
      dependent induction n.
      crush.
      dep_destruct x. rename h into xh. rename x0 into xt.
      dep_destruct t. rename h into th. rename x0 into tt.
      apply try_vector_from_svector_cons in X.
      destruct X as [XH XT].
      simpl.
      break_match_goal.
      auto.
      apply IHn.
      assumption.
    Qed.

    Lemma VnthVhead {B:Type} {n} (ip:0<(S n)) (x:vector B (S n)):
      Vnth x ip ≡ Vhead x.
    Proof.
      dependent destruction x.
      reflexivity.
    Qed.

    Lemma SomeConstrEquiv:
      ∀ (T : Type) (a b : T), Some a ≡ Some b ↔ a ≡ b.
    Proof.
      split.
      + intros E.
        inversion E.
        reflexivity.
      + intros R.
        rewrite R.
        reflexivity.
    Qed.

    Lemma VnthVtail : forall n (v : vector A (S n)) i (h : i < n) (h': S i < S n),
        Vnth (Vtail v) h ≡ Vnth v h'.
    Proof.
      intros n v i h h'.
      VSntac v. simpl.
      generalize (lt_S_n h').
      intros h''.
      replace h'' with h by apply proof_irrelevance.
      reflexivity.
    Qed.

    Lemma Vnth_svector_from_vector {B} {n i} {ip:i<n} {v:vector B n}:
      Vnth (svector_from_vector v) ip ≡ Some (Vnth v ip).
    Proof.
      unfold svector_from_vector.
      rewrite Vnth_map.
      reflexivity.
    Qed.

    Lemma Vnth_PointWise2 {B C D: Type} (f: B->C->D) {n} (ab: (vector B n)*(vector C n))
          {i} {ip:i<n}:
      Vnth (HCOLOperators.PointWise2 f ab) ip ≡ f (Vnth (fst ab) ip) (Vnth (snd ab) ip).
    Proof.
      destruct ab as [a b].
      unfold HCOLOperators.PointWise2.
      rewrite Vnth_map2.
      reflexivity.
    Qed.


    Lemma VsubVtail_right:
      ∀ (B : Type) (p t : nat) (v : vector B (S p + t))
        (pti : S p + t <= S p + t) (pti' : p + t <= p + t),
        @Vsub B (p+t) (Vtail v) p t pti' ≡ Vsub v pti.
    Proof.
      intros.
      dep_destruct v.
      simpl.
      rewrite Vsub_cons.
      replace pti' with (Vsub_cons_aux pti) by apply proof_irrelevance.
      reflexivity.
    Qed.
    
    Lemma VsubVtail_left:
      ∀ (B : Type) (p t : nat) (v : vector B (S p + t)) 
        (pti : 0 + p <= p + t) (pti' : 1 + p <= S p + t),
        @Vsub B (p + t) (Vtail v) 0 p pti ≡ Vsub v pti'.
    Proof.
      intros.
      dep_destruct v.
      simpl.
      rewrite Vsub_cons.
      replace pti with (Vsub_cons_aux pti') by apply proof_irrelevance.
      reflexivity.
    Qed.
    
    Lemma fst_vector2pair {B:Type} (p:nat) {t:nat} (v:vector B (p+t))
          (pti: 0 + p <= p + t): 
      fst (vector2pair p v) ≡ @Vsub B (p+t) v 0 p pti.
    Proof.
      unfold vector2pair.
      induction p.
      crush.
      simpl.
      assert(pti':0 + p <= p + t) by omega.
      rewrite IHp with (pti:=pti'). clear IHp.
      assert(H1: Vnth v (Vsub_aux1 0 p pti) ≡ Vhead v)
        by (apply Vnth_0).
      rewrite <- H1.

      assert(H2: (@Vsub B (p + t) (Vtail v) 0 p pti') ≡ Vsub v (Vsub_aux2 0 p pti)).
      apply VsubVtail_left.
      rewrite H2.
      reflexivity.
    Qed.

    Lemma snd_vector2pair {B:Type} (p:nat) {t:nat} (v:vector B (p+t))
          (pti: p + t <= p + t): 
      snd (vector2pair p v) ≡ @Vsub B (p+t) v p t pti.
    Proof.
      unfold vector2pair.
      induction p.
      simpl in *.
      rewrite Vsub_id.
      reflexivity.
      simpl.
      assert(pti':p + t <= p + t) by omega.
      rewrite IHp with (pti:=pti').
      apply VsubVtail_right.
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
    destruct o as [|o]; try nat_lt_0_contradiction.

    unfold evalBinOp in B.
    revert B.
    case_eq (try_vector_from_svector x); try congruence.
    intros t T B.
    apply cast_vector_operator_OK_elim in B.
    subst y.  
    rewrite Vnth_svector_from_vector.
    f_equal.
    remember (vector2pair (S o) t) as tp.
    rewrite Vnth_PointWise2.

    assert(FA: Vnth (fst tp) ip ≡ xva).
    {
      subst tp.
      assert(pti : 0 + S o  <= S o + S o) by omega.
      rewrite fst_vector2pair with (pti0:=pti).
      apply SomeConstrEquiv.
      rewrite <- XA.
      rewrite Vnth_sub.
      generalize  (Vnth_sub_aux 0 pti ip) as c1; intros.
      generalize (less_half_less_double ip) as c2; intros.
      replace (c1) with (c2).
      apply try_vector_from_svector_elementwise; try assumption.
      apply proof_irrelevance.
    }
    rewrite FA.

    assert(FB: Vnth (snd tp) ip  ≡ xvb).
    {
      subst tp.
      assert(pti: S o + S o <= S o + S o) by omega.
      rewrite snd_vector2pair with (pti0:=pti).
      apply SomeConstrEquiv.
      rewrite <- XB.
      rewrite Vnth_sub.
      generalize (Vnth_sub_aux (S o) pti ip) as c1;rewrite Plus.plus_comm; intros.
      generalize (half_plus_less_half_less_than_double ip) as c2. intros.
      replace (c1) with (c2).
      apply try_vector_from_svector_elementwise; try assumption.
      apply proof_irrelevance.
    }
    rewrite FB.
    
    reflexivity.
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

  Definition MaybeVnth {B : Type} {n : nat}
             (el: @maybeError (svector B n)) {i: nat} (ip: i < n): option B :=
    match el with
    | Error _ => None
    | OK l => Vnth l ip
    end.

  Lemma ErrSparseUnionArgOK:
    ∀ (n : nat) 
      (a b : @maybeError (svector A n)),
      is_OK (ErrSparseUnion a b) → (is_OK a) /\ (is_OK b).
  Proof.
    intros.
    unfold is_OK in H.
    break_match_hyp.
    unfold ErrSparseUnion in Heqm.
    + split.
      repeat break_match_hyp; err_ok_elim.
      repeat break_match_hyp; err_ok_elim.
    + contradiction H.
  Qed.

  Fixpoint Vfold_left_err
           {B C : Type}
           (f: C → B → @maybeError C)
           {n}
           (z: C)
           (v: vector B n)
    : @maybeError C
    :=
      match v with
      | Vnil => OK z
      | Vcons a _ w =>
        match Vfold_left_err f z w with
        | OK p => f p a 
        | Error _ as e => e
        end
      end.

  Lemma Vbuild_cons: forall {B} {n} (gen : forall i, i < S n -> B),
      Vbuild gen ≡ Vcons
             (gen 0 (lt_O_Sn n))
             (Vbuild (fun i ip => gen (S i) (lt_n_S ip))).
  Proof.
    intros.
    rewrite <- Vbuild_head.
    rewrite <- Vbuild_tail.
    reflexivity.
  Qed.

(*  
  Lemma FoldErrSpraseUnionSpec
        {n m : nat}
        (l: vector (@maybeError (svector A (S m))) (S n))
        (z v : svector A (S m))
        (Lo:  Vforall is_OK l)
        (Vo: Vfold_left ErrSparseUnion (OK z) l ≡ OK v):
    
    forall i (ip: i<S m),
      Vfold_left_err OptionUnion None
                     (Vbuild (fun j jp => MaybeVnth (Vnth l jp) ip))
                     ≡ OK (Vnth v ip).
  Proof.
    intros i ip.
    remember (Vbuild (λ (j : nat) (jp : j < S n), MaybeVnth (Vnth l jp) ip)) as r eqn:Reqn.
    (* 'r' is row in our matrix *)
    
    dependent induction m.
    crush.
    break_match.
    (*
    break_match.
    Focus 2.
    simpl in Heqm0.
    unfold Vfold_left_err in Heqm0.

    
    rewrite Vbuild_cons in Heqb.
    inversion Heqb. rename H0 into Hh, H1 into Hb.
    apply inj_pair2_eq_dec in Hb; try apply eq_nat_dec.
    clear Heqb.
    *)
    admit.
    admit.
    admit.
  Qed.
    

  Lemma FoldOptionOKUniqueSome:
    ∀ {n} {j : nat} (jp : j < S n) {j' : nat} (j'p : j' < S n)
      (vg : vector (option A) (S n)),
      is_Some (Vnth vg jp)
      → is_Some (Vnth vg j'p) → is_OK (Vfold_left_err OptionUnion None vg) -> j' ≡ j.
  Proof.
    intros n j jp j' j'p vg Sj Sj' Fok.
    admit.
  Qed.
  
  Lemma SparseUnionOK (n m:nat)
        (l: vector (@maybeError (svector A m)) n) (* We can think of 'l' as a matrix stored in column major order. Each column is of type @maybeError (vector) *)
        (z: svector A m)
        (Ze: svector_is_empty z)
        (Lo: Vforall is_OK l):
    is_OK (Vfold_left ErrSparseUnion (OK z) l) ->
    ((n≡0) \/
     (m≡0) \/
     (forall i (ip: i<m) j (jp: j<n) j' (j'p: j'<n) lj lj',
         Vnth l jp ≡ OK lj -> is_Some (Vnth lj ip)  -> 
         Vnth l j'p ≡ OK lj' -> is_Some (Vnth lj' ip)
         -> j' ≡ j)).
  Proof.
    intros K.
    destruct n.
    (* Take care of n=0 case *)
    left; trivial.
    (* now n!=0 *)
    right.
    destruct m.
    (* Now let us take care of m=0 *)
    left. reflexivity.
    right.
    
    (* all special cases for 'm' and 'n' are taken care of *)

    intros i ip j jp j' j'p lj lj' Jo LJs J'o LJ's.
    destruct (Vfold_left ErrSparseUnion (OK z) l) as [v|v] eqn:Ko; err_ok_elim.
    
    assert(Rj: 
            Vfold_left_err OptionUnion None
                            (Vbuild (fun pj pjp => MaybeVnth (Vnth l pjp) ip))
                            ≡ OK (Vnth v ip)).
    {
      apply FoldErrSpraseUnionSpec with (z0:=z).
      assumption.
      assumption.
      }

    (* proof by contradiction *)
     now_show (j' ≡ j).
    
    assert (LoU: forall x (xp:x<S n), is_OK (Vnth l xp)).
    {
      intros.
      apply Vforall_nth with (i:=x) (ip:=xp) in Lo.
      assumption.
    }
    remember (Vbuild (λ (pj : nat) (pjp : pj < S n), MaybeVnth (Vnth l pjp) ip)) as vg.

    assert(is_Some (Vnth vg jp)).
    {
      subst vg.
      rewrite Vbuild_nth.
      crush.
    }

    assert(is_Some (Vnth vg j'p)).
    {
      subst vg.
      rewrite Vbuild_nth.
      crush.
    }

    apply (FoldOptionOKUniqueSome jp j'p vg); try assumption.
    crush.
  Qed.
 *)

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

      assert (bOK: is_OK (@evalBinOp A (1 + 1) 1 f g))
             by (apply BinOpPre; assumption).
      
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

      assert (bOK: is_OK (@evalBinOp A (1 + 1) 1 f g))
             by (apply BinOpPre; assumption).
      
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
    } (* End MOK *)

    assert(BSP: ∀ (i : nat) (ip : i < (S n)) (xva xvb : A),
              Vnth x (less_half_less_double ip) ≡ Some xva
              → Vnth x (half_plus_less_half_less_than_double ip) ≡ Some xvb
              → Vnth t ip ≡ Some (f xva xvb))
    by  (apply evalBinOpSpec; assumption).

    assert (FOK: is_OK (Vfold_left ErrSparseUnion (OK (empty_svector (S n)))
                                   (Vbuild f1))).
    {
      induction n.
      simpl.
      break_match.
      break_match.
      crush.
      break_match_hyp; err_ok_elim.
      simpl in MOK; destruct MOK;
      rewrite Heqm in H; err_ok_elim.
      destruct (Vfold_left ErrSparseUnion (OK (empty_svector (S (S n)))) (Vbuild f1))
                   eqn:FD.
      crush.
      rewrite Vbuild_cons in FD.
      rewrite empty_svector_cons in FD.
      TODO: split Vfold, apply IH.
        

    }

    remember (OK (empty_svector (S n))) as Zn.

    destruct (Vfold_left ErrSparseUnion Zn (Vbuild f1))
             as [t' |  ]
                  eqn: F; err_ok_elim.

    assert(FSP: ∀ (i : nat) (ip : i < S n) (xva xvb : A),
              Vnth x (less_half_less_double ip) ≡ Some xva
              → Vnth x (half_plus_less_half_less_than_double ip) ≡ Some xvb
              → Vnth t' ip ≡ Some (f xva xvb)).
    {
      admit.
    }

    unfold equiv, maybeError_equiv, equiv, svector_equiv.

    apply Vforall2_intro_nth.
    intros.
    
    remember (Vnth x (less_half_less_double ip)) as xa.
    destruct xa as [xva|].
    symmetry in Heqxa.

    remember (Vnth x (half_plus_less_half_less_than_double ip)) as xb.
    destruct xb as [xvb|].
    symmetry in Heqxb.
    
    assert(BN: Vnth t ip ≡ Some (f xva xvb)) by (apply BSP; assumption).
    assert(FN: Vnth t' ip ≡ Some (f xva xvb)) by (apply FSP; assumption).
    rewrite BN, FN.
    unfold opt_Equiv.
    reflexivity.

    assert(H:is_Some (Vnth x (half_plus_less_half_less_than_double ip)))
      by (apply VnthDense; assumption).
    rewrite <- Heqxb in H.
    none_some_elim.
    
    assert(H:is_Some (Vnth x (less_half_less_double ip)))
      by (apply VnthDense; assumption).
    rewrite <- Heqxa in H.
    none_some_elim.
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
    intros.
    apply BinOpSums.
    lia.
    compute; intros; reflexivity.
    compute; intros; reflexivity.
    assumption.
  Qed.
  
  Section SigmaHCOLRewriting.
