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


Local Notation "g ⊚ f" := (@SHCompose Monoid_RthetaFlags _ _ _ g f) (at level 40, left associativity) : type_scope.

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
