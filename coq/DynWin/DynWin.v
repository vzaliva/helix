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


Local Notation "g ⊚ f" := (@SHCompose Monoid_RthetaFlags _ _ _ _ g f) (at level 40, left associativity) : type_scope.

(*

Final SigmaHCOL expression (before translating to h-Code):

BinOp(1, Lambda([ r14, r15 ], geq(r15, r14))) o
SUMUnion(
  eUnion(2, 0) o
  ISumReduction(i17, 3, (a, b) -> add(a, b), V(0.0), (arg) -> false,
    PointWise(1, Lambda([ r16, i19 ], mul(r16, nth(D, i17)))) o
    Inductor(3, i17, Lambda([ r9, r10 ], mul(r9, r10)), V(1.0)) o
    Embed(5, 0)
  ),
  eUnion(2, 1) o
  ISumReduction(i15, 2, (a, b) -> max(a, b), V(0.0), (arg) -> false,
    BinOp(1, Lambda([ r12, r13 ], abs(sub(r12, r13)))) o
    ISumUnion(i18, 2,
      eUnion(2, i18) o
      Embed(5, add(add(i15, V(1)), mul(V(2), i18)))
    )
  )
)
*)
Definition dynwin_SHCOL1 (a:avector 3) : @SHOperator Monoid_RthetaFlags (1+(2+2)) 1 zero
  :=   (@SafeCast _ (Init.Nat.add (S O) (S O)) (S O)
                  (@SHBinOp Monoid_RthetaSafeFlags _ (S O)
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
         (eUnion Monoid_RthetaFlags (le_S (le_n 1))
                 ⊚ SafeCast
                 (IReduction plus
                             (SHFamilyOperatorCompose Monoid_RthetaSafeFlags
                                                      ( λ jf,
                                                        SHCompose Monoid_RthetaSafeFlags
                                                                  (SHPointwise Monoid_RthetaSafeFlags
                                                                               (Fin1SwapIndex
                                                                                  jf
                                                                                  (mult_by_nth a)))
                                                                  (SHInductor _ (proj1_sig jf) mult 1))
                                                      (Embed Monoid_RthetaSafeFlags
                                                          (GathH1_domain_bound_to_base_bound (h_bound_first_half 1 4))))))
         (eUnion Monoid_RthetaFlags (le_n 2)
                 ⊚ SafeCast
                 (IReduction minmax.max
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
                                                      ⊚
                                                      Embed Monoid_RthetaFlags
                                                      (h_index_map_compose_range_bound
                                                         (GathH_jn_domain_bound (proj1_sig jf) 2 (proj2_sig jf))
                                                         (h_bound_second_half 1 4) (proj1_sig jf0)
                                                         (proj2_sig jf0)) ))) ))).


