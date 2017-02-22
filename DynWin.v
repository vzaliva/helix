Require Import VecUtil.
Require Import VecSetoid.
Require Import SVector.
Require Import Spiral.
Require Import CarrierType.

Require Import HCOL.
Require Import HCOLImpl.
Require Import THCOL.
Require Import THCOLImpl.
Require Import Rtheta.
Require Import SigmaHCOL.
Require Import TSigmaHCOL.
Require Import IndexFunctions.

Require Import Arith.
Require Import Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Program.

Require Import SpiralTactics.

Require Import HCOLBreakdown.
Require Import SigmaHCOLRewriting.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.canonical_names.

Section HCOL_breakdown.

  (* Original dynamic window expression *)
  Definition dynwin_orig (a: avector 3) :=
    (HTLess
       (HEvalPolynomial a)
       (HChebyshevDistance 2)).

  (* dynamic window HCOL expression *)
  Definition dynwin_HCOL (a: avector 3) :=
    (HBinOp (IgnoreIndex2 Zless) ∘
            HCross
            ((HReduction plus 0 ∘ HBinOp (IgnoreIndex2 mult)) ∘ (HPrepend a ∘ HInduction _ mult 1))
            (HReduction minmax.max 0 ∘ (HPointwise (IgnoreIndex abs)) ∘ HBinOp (o:=2) (IgnoreIndex2 sub))).


  (* Initial HCOL breakdown proof *)
  Theorem DynWinOHCOL:  forall (a: avector 3),
      dynwin_orig a = dynwin_HCOL a.
  Proof.
    intros a.
    unfold dynwin_orig, dynwin_HCOL.
    rewrite breakdown_OTLess_Base.
    rewrite breakdown_OEvalPolynomial.
    rewrite breakdown_OScalarProd.
    rewrite breakdown_OMonomialEnumerator.
    rewrite breakdown_OChebyshevDistance.
    rewrite breakdown_OVMinus.
    rewrite breakdown_OTInfinityNorm.
    HOperator_reflexivity.
  Qed.

End HCOL_breakdown.


Section SigmaHCOL_rewriting.

  Local Infix "==" :=
    (@SHOperator_hequiv Monoid_RthetaFlags _ _ _ _ _ _)
      (at level 90, no associativity).

  Local Notation "g ⊚ ( qp ) f" := (@SHCompose Monoid_RthetaFlags _ _ _ _ _ _ _ qp g f) (at level 40, left associativity) : type_scope.


  (*
Final Sigma-HCOL expression:

BinOp(1, Lambda([ r14, r15 ], geq(r15, r14))) o
SUMUnion(
  ScatHUnion(2, 1, 0, 1) o
  Reduction(3, (a, b) -> add(a, b), V(0.0), (arg) -> false) o
  PointWise(3, Lambda([ r16, i14 ], mul(r16, nth(D, i14)))) o
  Induction(3, Lambda([ r9, r10 ], mul(r9, r10)), V(1.0)) o
  GathH(5, 1, 0, 1),
  ScatHUnion(2, 1, 1, 1) o
  Reduction(2, (a, b) -> max(a, b), V(0.0), (arg) -> false) o
  PointWise(2, Lambda([ r11, i13 ], abs(r11))) o
  ISumUnion(i15, 2,
    ScatHUnion(2, 1, i15, 1) o
    BinOp(1, Lambda([ r12, r13 ], sub(r12, r13))) o
    GathH(4, 2, i15, 2)
  ) o
  GathH(5, 4, 1, 1)
)
   *)
  (* HCOL -> SigmaHCOL Value correctness. *)
  Theorem DynWinSigmaHCOL
          (a: avector 3)

          (* LHS arguments *)
          {P: svector Monoid_RthetaFlags (1 + (2 + 2)) -> Prop}
          {Q: svector Monoid_RthetaFlags 1 -> Prop}
          {PQ: forall x : svector Monoid_RthetaFlags (1 + (2 + 2)),
              P x -> Q (liftM_HOperator' Monoid_RthetaFlags (dynwin_HCOL a) x)}

          (* RHS arguments *)
          {P1 Q1 Q2 P3 Q3 P4 Q4 P5 Q5 P6 Q6 P7 Q7 P8 Q8}
          {P9 Q9 P10 Q10 P11 Q11 Q12 P13 Q13}
          {Ps Qs Pg Qg}
          {SK KG R}
          {C1 C2 C3 C4 C5 C6 C7 C8 C9 C10}
          {PQ1 PQ2 PQ3 PQ4 PQ5 PQ6 PQ7 PQ8 PQ9 PQ10 PQ11 PQ12 PQ13 PQ14}
          {PQg PQs}
    :
      liftM_HOperator Monoid_RthetaFlags (P:=P) (Q:=Q) (dynwin_HCOL a) PQ

      ==

      (SHBinOp _ (P:=P1) (Q:=Q1) (IgnoreIndex2 THCOLImpl.Zless) PQ1)
        ⊚(C1)
        (HTSUMUnion _ (P:=P8) (Q1:=Q5) (Q2:=Q9) (Q:=Q2)
                    (
                      ScatH _ 0 1
                            (P:=P5) (Q:=Q5)
                            (range_bound := h_bound_first_half 1 1)
                            (snzord0 := @ScatH_stride1_constr 1 2) PQ5
                            ⊚(C2)
                            (liftM_HOperator _ (P:=P3) (Q:=Q3) (@HReduction _ plus CarrierAPlus_proper 0) PQ3 ⊚(C6)
                                             SHBinOp _ (P:=P4) (Q:=Q4) (IgnoreIndex2 mult) PQ4
                                             ⊚(C4)
                                             liftM_HOperator _ (P:=P6) (Q:=Q6) (HPrepend a ) PQ6
                                             ⊚(C5)
                                             liftM_HOperator _ (P:=P7) (Q:=Q7) (HInduction 3 mult one) PQ7)
                            ⊚(C3)
                            (GathH _ 0 1
                                   (P:=P8) (Q:=Q8)
                                   (domain_bound := h_bound_first_half 1 (2+2)) PQ8)
                    )

                    (
                      (ScatH _ 1 1
                             (P:=P9) (Q:=Q9)
                             (range_bound := h_bound_second_half 1 1)
                             (snzord0 := @ScatH_stride1_constr 1 2) PQ9)
                        ⊚(C7)
                        (liftM_HOperator _ (P:=P10) (Q:=Q10) (@HReduction _ minmax.max _ 0) PQ10)
                        ⊚(C8)
                        (SHPointwise _ (P:=P11) (Q:=Q11) (IgnoreIndex abs) PQ11)
                        ⊚(C9)
                        (USparseEmbedding
                           (n:=2)
                           (Ps:=Ps) (Qs:=Qs) (Pg:=Pg) (Qg:=Qg) (SK:=SK) (KG:=KG) (PQg:=PQg) (PQs:=PQs) (PQ:=PQ14) (R:=R)
                           (mkSHOperatorFamily Monoid_RthetaFlags _ _ _ P13 Q13
                                               (fun j _ => SHBinOp _ (o:=1) (P:=P13) (Q:=Q13)
                                                                (SwapIndex2 j (IgnoreIndex2 HCOLImpl.sub)) (PQ13 j)))
                           (IndexMapFamily 1 2 2 (fun j jc => h_index_map j 1 (range_bound := (ScatH_1_to_n_range_bound j 2 1 jc))))
                           (f_inj := h_j_1_family_injective)
                           (IndexMapFamily _ _ 2 (fun j jc => h_index_map j 2 (range_bound:=GathH_jn_domain_bound j 2 jc))))
                        ⊚(C10)
                        (GathH _ 1 1
                               (P:=P8) (Q:=Q12)
                               (domain_bound := h_bound_second_half 1 (2+2)) PQ12)
                    )
                    plus
                    PQ2
        ).
  Proof.
    unfold dynwin_HCOL.
    setoid_rewrite LiftM_Hoperator_compose.

    (* Actual rewriting *)
    setoid_rewrite expand_HTDirectSum. (* this one does not work with Diamond'_arg_proper *)

    Unset Typeclasses Depth.
    Set Typeclasses Debug.
    Set Typeclasses Debug Verbosity 99.

    Redirect "log.txt" setoid_rewrite LiftM_Hoperator_compose at 1.



    repeat setoid_rewrite LiftM_Hoperator_compose at 1.
    repeat setoid_rewrite <- SHBinOp_equiv_lifted_HBinOp at 1.
    repeat setoid_rewrite <- SHPointwise_equiv_lifted_HPointwise at 1.
    setoid_rewrite expand_BinOp at 3.

    SHOperator_reflexivity.
  Qed.

End SigmaHCOL_rewriting.
