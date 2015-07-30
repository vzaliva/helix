
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
    {
      unfold e. simpl. trivial.
    }
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

  
  Lemma cast_vector_operator_OK_elim: forall i o (v: vector A i)
                                        (op: vector A i → svector A o)
    ,
      forall (t: svector A o),
        ((cast_vector_operator
            i o
            i o
            (OK ∘ op)) v) ≡ OK t -> op v ≡ t.
  Proof.
    intros i o v op t.
    unfold cast_vector_operator.
    destruct (eq_nat_dec i i); try congruence.
    destruct (eq_nat_dec o o); try congruence.
    compute.
    dep_destruct e.
    dep_destruct e0.
    intros.
    inversion H.
    reflexivity.
  Qed.
   
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

  (* Checks preconditoins of evaluation of SHOGathH to make sure it succeeds*)
  Lemma GathPre: forall (i o nbase nstride: nat) (base stride:aexp) (st:state)
                   (x: svector A i),
      ((evalAexp st base ≡ OK nbase) /\
       (evalAexp st stride ≡ OK nstride) /\
       nstride ≢ 0 /\
       o ≢ 0 /\
       (nbase+(pred o)*nstride) < i) ->
      is_OK (evalSigmaHCOL st (SHOGathH (i:=i) (o:=o) base stride) x).
  Proof.
    intros i o nbase nstride base stride st x.
    simpl.
    unfold evalGathH.
    crush.
    destruct (Compare_dec.lt_dec (nbase + (pred o) * nstride) i), o, nstride;
      err_ok_elim.
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
    - intros. symmetry in e. contradiction.
    - intros Hsnz. 
      case (Compare_dec.lt_dec (nbase + (pred o) * nstride) i).
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


  Lemma index_op_is_partial_map:
    ∀ (i o : nat)
      (x : svector A i),
        ∀ (f_spec: index_function_spec i o),
          Vforall (fun z => is_None z \/ Vin_aux x z)
                  (vector_index_backward_operator f_spec x).
      Proof.
        intros.
        unfold index_function_spec in f_spec.
        unfold vector_index_backward_operator, proj1_sig,
        vector_index_backward_operator_spec.
        replace (let (a, _) :=
                     Vbuild_spec (VnthIndexMapped x f_spec) in
                 a) with
        (Vbuild (VnthIndexMapped x f_spec)) by reflexivity.
        apply Vforall_eq. intros.
        apply Vbuild_in in H.
        destruct H. destruct H. 
        subst x0.
        case_eq (VnthIndexMapped x f_spec x1 x2).
        + right.
          unfold VnthIndexMapped, proj1_sig in H.
          destruct (f_spec x1 x2) in H.
          destruct x0.
          * rewrite <- H.
            unfold Vin_aux.
            apply Vnth_in.
          * congruence.
        + left.
          none_some_elim.
      Qed.

  Lemma index_op_preserves_P:
    ∀ (i o : nat) (x : svector A i) (P: option A->Prop),
      P None ->
      Vforall P x
      → ∀ f_spec : index_function_spec i o,
          Vforall P (vector_index_backward_operator f_spec x).
  Proof.
    intros.
    unfold index_function_spec in f_spec.
    assert(Vforall (fun z => is_None z \/ Vin_aux x z)
                   (vector_index_backward_operator f_spec x))
      by apply index_op_is_partial_map.
    generalize dependent (vector_index_backward_operator f_spec x).
    intros t.
    rewrite 2!Vforall_eq.
    crush.
    assert (is_None x0 ∨ Vin_aux x x0) by (apply H1; assumption).
    inversion H3.
    + destruct x0; none_some_elim.
      assumption.
    + rewrite Vforall_eq in H0.
      auto.
  Qed.

  Definition index_function_is_surjective
             (i o : nat)
             (f_spec: index_function_spec i o) :=
    forall (j:nat) (jp:j<o), is_Some(proj1_sig (f_spec j jp)).
  
  Lemma index_op_is_dense:
    ∀ (i o : nat) (x : svector A i)
      (f_spec: index_function_spec i o),
      svector_is_dense x ->
      index_function_is_surjective i o f_spec -> 
      svector_is_dense (vector_index_backward_operator f_spec x).
  Proof.
    intros i o x f_spec xdense fsurj.
    unfold index_function_spec in f_spec.
    unfold index_function_is_surjective in fsurj.
    unfold svector_is_dense in *.
    unfold vector_index_backward_operator, proj1_sig,
    vector_index_backward_operator_spec.
    
    replace (let (a, _) :=
                 Vbuild_spec (VnthIndexMapped x f_spec) in
             a) with
    (Vbuild (VnthIndexMapped x f_spec)) by reflexivity.
    apply Vforall_eq. intros.
    apply Vbuild_in in H.
    destruct H. destruct H. 
    subst x0.
    case_eq (VnthIndexMapped x f_spec x1 x2). 
    - intros. 
      none_some_elim.
    - intros.
      assert(FS: is_Some (` (f_spec x1 x2))) by apply fsurj.
      unfold VnthIndexMapped, proj1_sig in H.
      destruct (f_spec x1 x2) in H, FS; none_some_elim.
      destruct x0.
      +
        simpl in *.
        generalize dependent (l n eq_refl). 
        clear FS f_spec fsurj l.
        intros.
        (* here we have a contradiction between 'xdense' and 'H' *)
        assert (HS: is_Some (Vnth x l)) by (apply Vforall_nth; assumption).
        destruct (Vnth x l); simpl in *;  congruence.
      +
        simpl in FS. contradiction FS.
  Qed.


  (* Gath on dense vector produces dense vector *)

    Lemma gath_math_surj:
      ∀ (i o base stride : nat) (snz : 0 ≢ stride) (range_bound : base + pred o * stride < i),
        index_function_is_surjective i o
                                     (GathBackwardMap_Spec
                                        (snz:=snz)
                                        (range_bound:=range_bound)
                                        i o base stride).
    Proof.
      unfold index_function_is_surjective.
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
    destruct (Compare_dec.lt_dec (n + pred o * n0) i); try congruence.
    inversion 1.
    unfold GathH in *.
    apply index_op_is_dense; try assumption.
    apply gath_math_surj.
  Qed.



  (* Ensures that variable var is not affecting evaluation of expression. to prove it all we need to make sure it is free in exp *)
  Definition evalsToWithVar
             (var:varname)
             (st:state)
             (exp: aexp)
             (v:nat) :=
    forall (x:nat), evalAexp (update st var x) exp ≡ OK x.
  

  Set Printing Implicit.
  
  Lemma BinOpSums
        (o: nat)
        {onz: 0 ≢ o} 
        (f:A->A->A)
        (var:varname)
        (pad stride:aexp)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}
    :
      forall (st : state) (x : vector (option A) (o + o)),
        evalsToWithVar var st pad o ->  evalsToWithVar var st stride o ->
        svector_is_dense x ->
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



    break_match_goal; try congruence.

  Qed.
  






  
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
    assert (op1OK: is_OK (evalSigmaHCOL st (SHOBinOp 2 ASub) x)) by (apply BinOpPre; assumption). 

    case_eq (evalSigmaHCOL st (SHOBinOp 2 ASub) x); intros; simpl in H0, op1OK.

    Focus 2.
    rewrite H0 in op1OK.
    contradiction.

    unfold op2, vari, c2, evalSigmaHCOL.
    simpl.
    
    assert (g1OK: is_OK
              (@evalGathH A Ae 4 2
                          (update st (Var "i") 1)
                          (AValue (Var "i"))
                          (AConst 2) x)).
    {
      assert(g1_pre_nbase: evalAexp (update st (Var "i") 1) (AValue (Var "i")) ≡ OK 1).
      {
        simpl. unfold update.
        destruct eq_varname_dec. reflexivity.
        congruence.
      }
      
      assert(g2_pre_nstride: evalAexp (update st (Var "i") 1) (AConst 2) ≡ OK 2).
      {
        simpl. unfold update.
        reflexivity.
      }
      
      apply GathPre with (nbase:=1) (nstride:=2) ; repeat (split; try assumption; try auto).
    }

    case_eq (@evalGathH A Ae 4 2 (update st (Var "i") 1) (AValue (Var "i"))
                        (AConst 2) x); intros.
    Focus 2.  rewrite H1 in g1OK. err_ok_elim.
    apply GathDensePost in H1 ; try assumption.

    assert(b1OK: is_OK (@evalBinOp A 2 1 (update st (Var "i") 1) ASub t0)).
    {
      apply BinOpPre.
      apply ASub_proper.
      assumption.
    }
 
    case_eq (@evalBinOp A 2 1 (update st (Var "i") 1) ASub t0).
    Focus 2. intros. rewrite H2 in b1OK. err_ok_elim.
    intros.
    apply BinOpPost in H0; try apply ASub_proper.


    (* it looks like it could be proven this way but it is work intesive and stupid.
        should be proven in generic form with variables instead of concrete values *)

    
  Qed.
  
  Section SigmaHCOLRewriting.
