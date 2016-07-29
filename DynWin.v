Require Import VecUtil.
Require Import VecSetoid.
Require Import SVector.
Require Import Spiral.
Require Import CarrierType.

Require Import HCOL.
Require Import HCOLImpl.
Require Import THCOL.
Require Import THCOLImpl.
Require Import SigmaHCOL.
Require Import TSigmaHCOL.
Require Import IndexFunctions.

Require Import Arith.
Require Import Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Program.

Require Import CpdtTactics.
Require Import JRWTactics.
Require Import SpiralTactics.

Require Import HCOLBreakdown.
Require Import SigmaHCOLRewriting.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.canonical_names.


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
Definition dynwin_SigmaHCOL (a: avector 3) : svector (1 + (2 + 2)) -> svector 1
  :=
    SHBinOp (IgnoreIndex2 THCOLImpl.Zless)
                    ∘ HTSUMUnion
                    (ScatH 0 1
                           (range_bound := h_bound_first_half 1 1)
                           (snzord0 := @ScatH_stride1_constr 1 2)
                           ∘ liftM_HOperator
                           (HReduction plus zero ∘ HBinOp (IgnoreIndex2 mult)
                                       ∘ (HPrepend a ∘ HInduction 3 mult one)) ∘
                           GathH 0 1
                           (domain_bound := h_bound_first_half 1 (2+2))

                    )
                    (ScatH 1 1
                           (range_bound := h_bound_second_half 1 1)
                           (snzord0 := @ScatH_stride1_constr 1 2)
                           ∘ liftM_HOperator (
                             (HReduction minmax.max 0) ∘ (HPointwise (IgnoreIndex abs))) ∘
                           (USparseEmbedding
                              (n:=2)
                              (fun j _ => SHBinOp (o:=1) (SwapIndex2 j (IgnoreIndex2 HCOLImpl.sub)))
                              (IndexMapFamily 1 2 2 (fun j jc => h_index_map j 1 (range_bound := (ScatH_1_to_n_range_bound j 2 1 jc))))
                              (f_inj := h_j_1_family_injective)
                              (IndexMapFamily _ _ 2 (fun j jc => h_index_map j 2 (range_bound:=GathH_jn_domain_bound j 2 jc))))
                           ∘ GathH 1 1
                           (domain_bound := h_bound_second_half 1 (2+2))
                    ).


(* HCOL -> SigmaHCOL Value correctness. *)
Theorem DynWinSigmaHCOL:  forall (a: avector 3),
    liftM_HOperator (dynwin_HCOL a) = dynwin_SigmaHCOL a.
Proof.
  intros a.

  unfold dynwin_SigmaHCOL, dynwin_HCOL.
  rewrite LiftM_Hoperator_compose.

  (* Actual rewriting *)
  setoid_rewrite expand_HTDirectSum at 1; try typeclasses eauto.
  setoid_rewrite LiftM_Hoperator_compose at 2.
  setoid_rewrite <- SHBinOp_equiv_lifted_HBinOp.
  setoid_rewrite expand_BinOp at 2 .

  eapply (@SHOperator_functional_extensionality (1+(2+2)) 1).
  -
    split.
    typeclasses eauto.
    typeclasses eauto.
    apply compose_proper with (RA:=equiv) (RB:=equiv).
    apply SHOperator_SHBinOp.
    apply TSHOperator2_HTSUMUnion.
    apply compose_proper with (RA:=equiv) (RB:=equiv).
    apply compose_proper with (RA:=equiv) (RB:=equiv).
    apply SHOperator_ScatH.
    apply SHOperator_liftM_HOperator.
    typeclasses eauto.
    apply SHOperator_GathH.
    apply compose_proper with (RA:=equiv) (RB:=equiv).
    apply compose_proper with (RA:=equiv) (RB:=equiv).
    apply SHOperator_ScatH.
    apply compose_proper with (RA:=equiv) (RB:=equiv).
    apply SHOperator_liftM_HOperator.
    typeclasses eauto.
    apply SHOperator_USparseEmbedding.
    apply SHOperator_GathH.
  -
    split.
    apply vec_Setoid.
    apply vec_Setoid.
    apply compose_proper with (RA:=equiv) (RB:=equiv).
    apply SHOperator_SHBinOp.
    apply TSHOperator2_HTSUMUnion.
    apply compose_proper with (RA:=equiv) (RB:=equiv).
    apply compose_proper with (RA:=equiv) (RB:=equiv).
    apply SHOperator_ScatH.
    apply SHOperator_liftM_HOperator.
    typeclasses eauto.
    apply SHOperator_GathH.
    apply compose_proper with (RA:=equiv) (RB:=equiv).
    apply compose_proper with (RA:=equiv) (RB:=equiv).
    apply compose_proper with (RA:=equiv) (RB:=equiv).
    apply SHOperator_ScatH.
    apply SHOperator_liftM_HOperator.
    typeclasses eauto.
    apply SHOperator_USparseEmbedding.
    apply SHOperator_GathH.
  -
    reflexivity.
  (* SHOperator_reflexivity *)
Qed.
