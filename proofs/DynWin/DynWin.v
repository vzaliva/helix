Require Import Helix.HCOL.HCOL.
Require Import Helix.HCOL.THCOL.
Require Import Helix.Util.Misc.
Require Import Helix.SigmaHCOL.Rtheta.
Require Import Helix.SigmaHCOL.SigmaHCOL.
Require Import Helix.SigmaHCOL.TSigmaHCOL.
Require Import Helix.SigmaHCOL.IndexFunctions.

Require Import Helix.SigmaHCOL.SigmaHCOLRewriting.

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
          (HReduction plus 0 ∘ (HBinOp (IgnoreIndex2 mult) ∘ HPrepend a) ∘ HInduction _ mult 1)
          (HReduction minmax.max 0 ∘ (HPointwise (IgnoreIndex abs)) ∘ HBinOp (o:=2) (IgnoreIndex2 sub))).

Require Import Helix.Util.FinNatSet.

Local Notation "g ⊚ f" := (@SHCompose Monoid_RthetaFlags _ _ _ g f) (at level 40, left associativity) : type_scope.

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
Definition dynwin_SHCOL (a: avector 3) :=
  (SafeCast (SHBinOp _ (IgnoreIndex2 Zless)))
    ⊚
    (HTSUMUnion _ plus (
                  ScatH _ 0 1
                        (range_bound := h_bound_first_half 1 1)
                        (snzord0 := @ScatH_stride1_constr 1 2)
                        zero
                        ⊚
                        (liftM_HOperator _ (@HReduction _ plus 0)  ⊚
                                         SafeCast (SHBinOp _ (IgnoreIndex2 mult))
                                         ⊚
                                         liftM_HOperator _ (HPrepend a )
                                         ⊚
                                         liftM_HOperator _ (HInduction 3 mult one))
                        ⊚
                        (GathH _ 0 1
                               (domain_bound := h_bound_first_half 1 (2+2)))
                )

                (
                  (ScatH _ 1 1
                         (range_bound := h_bound_second_half 1 1)
                         (snzord0 := @ScatH_stride1_constr 1 2)
                         zero)
                    ⊚
                    (liftM_HOperator _ (@HReduction _ minmax.max 0))
                    ⊚
                    (SHPointwise _ (IgnoreIndex abs))
                    ⊚
                    (USparseEmbedding
                       (n:=2)
                       (fun jf => SafeCast (SHBinOp _ (o:=1)
                                                 (Fin1SwapIndex2 jf (IgnoreIndex2 CarrierType.sub))))
                       (fun j => h_index_map (proj1_sig j) 1 (range_bound := (ScatH_1_to_n_range_bound (proj1_sig j) 2 1 (proj2_sig j))))
                       (f_inj := h_j_1_family_injective)
                       zero
                       (fun j => h_index_map (proj1_sig j) 2 (range_bound:=GathH_jn_domain_bound (proj1_sig j) 2 (proj2_sig j))))
                    ⊚
                    (GathH _ 1 1
                           (domain_bound := h_bound_second_half 1 (2+2)))
                )
    ).


Definition dynwin_SHCOL1 (a:avector 3) : @SHOperator Monoid_RthetaFlags (1+(2+2)) 1
  :=   (@SafeCast (Init.Nat.add (S O) (S O)) (S O)
                  (@SHBinOp Monoid_RthetaSafeFlags (S O)
                            (@IgnoreIndex2 CarrierA (@sig nat (fun n : nat => Peano.lt n (S O)))
                                           Zless)
                            (@Reflexive_partial_app_morphism
                               (forall (_ : CarrierA) (_ : CarrierA), CarrierA)
                               (forall (_ : @sig nat (fun n : nat => Peano.lt n (S O)))
                                  (_ : CarrierA) (_ : CarrierA), CarrierA)
                               (@respectful CarrierA (forall _ : CarrierA, CarrierA)
                                            (@equiv CarrierA CarrierAe)
                                            (@equiv (forall _ : CarrierA, CarrierA)
                                                    (@ext_equiv CarrierA CarrierAe CarrierA CarrierAe)))
                               (@respectful (@sig nat (fun n : nat => Peano.lt n (S O)))
                                            (forall (_ : CarrierA) (_ : CarrierA), CarrierA)
                                            (@equiv (@sig nat (fun n : nat => Peano.lt n (S O)))
                                                    (@Sig_Equiv nat peano_naturals.nat_equiv
                                                                (fun n : nat => Peano.lt n (S O))))
                                            (@respectful CarrierA (forall _ : CarrierA, CarrierA)
                                                         (@equiv CarrierA CarrierAe)
                                                         (@respectful CarrierA CarrierA (@equiv CarrierA CarrierAe)
                                                                      (@equiv CarrierA CarrierAe))))
                               (@IgnoreIndex2 CarrierA
                                              (@sig nat (fun n : nat => Peano.lt n (S O))))
                               (@IgnoreIndex2_proper CarrierA CarrierAe
                                                     (@sig nat (fun n : nat => Peano.lt n (S O)))
                                                     (@Sig_Equiv nat peano_naturals.nat_equiv
                                                                 (fun n : nat => Peano.lt n (S O)))) Zless
                               (@proper_proper_proxy
                                  (forall (_ : CarrierA) (_ : CarrierA), CarrierA) Zless
                                  (@respectful CarrierA (forall _ : CarrierA, CarrierA)
                                               (@equiv CarrierA CarrierAe)
                                               (@equiv (forall _ : CarrierA, CarrierA)
                                                       (@ext_equiv CarrierA CarrierAe CarrierA CarrierAe)))
                                  Zless_proper))))
         ⊚ HTSUMUnion Monoid_RthetaFlags plus
         (eUnion Monoid_RthetaFlags (le_S (le_n 1)) 0
                 ⊚ SafeCast
                 (IReduction plus 0
                             (SHFamilyOperatorCompose Monoid_RthetaSafeFlags
                                                      ( λ jf,
                                                        SHCompose Monoid_RthetaSafeFlags
                                                                  (SHPointwise Monoid_RthetaSafeFlags
                                                                               (Fin1SwapIndex
                                                                                  jf
                                                                                  (mult_by_nth a)))
                                                                  (liftM_HOperator Monoid_RthetaSafeFlags
                                                                                   (HInductor (proj1_sig jf) mult 1)) )
                                                      (eT Monoid_RthetaSafeFlags
                                                          (GathH1_domain_bound_to_base_bound (h_bound_first_half 1 4))))))
         (eUnion Monoid_RthetaFlags (le_n 2) 0
                 ⊚ SafeCast
                 (IReduction minmax.max 0
                             (λ jf,
                              SHCompose Monoid_RthetaSafeFlags
                                        (SHBinOp Monoid_RthetaSafeFlags
                                                 (λ i
                                                    (a0 b : CarrierA),
                                                  IgnoreIndex abs i
                                                              (Fin1SwapIndex2
                                                                 jf
                                                                 (IgnoreIndex2 sub) i a0 b)))
                                        (UnSafeCast
                                           (ISumUnion
                                              (λ jf0,
                                               eUnion Monoid_RthetaFlags (proj2_sig jf0)
                                                      0
                                                      ⊚
                                                      eT Monoid_RthetaFlags
                                                      (h_index_map_compose_range_bound
                                                         (GathH_jn_domain_bound (proj1_sig jf) 2 (proj2_sig jf))
                                                         (h_bound_second_half 1 4) (proj1_sig jf0)
                                                         (proj2_sig jf0)) ))) ))).
