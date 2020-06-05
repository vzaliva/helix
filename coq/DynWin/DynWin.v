Require Import Helix.HCOL.HCOL.
Require Import Helix.HCOL.THCOL.
Require Import Helix.Util.Misc.
Require Import Helix.SigmaHCOL.Rtheta.
Require Import Helix.SigmaHCOL.SigmaHCOL.
Require Import Helix.SigmaHCOL.TSigmaHCOL.
Require Import Helix.SigmaHCOL.IndexFunctions.

Require Import Helix.SigmaHCOL.SigmaHCOLRewriting.

Require Import MathClasses.interfaces.canonical_names.

Definition dynwin_i:nat := (1 + (2 + 2)).
Definition dynwin_o:nat := 1.

(* Original dynamic window HCOL expression *)
Definition dynwin_orig (a: avector 3) : avector dynwin_i -> avector dynwin_o
  :=
  (HTLess
     (HEvalPolynomial a)
     (HChebyshevDistance 2)).

(* dynamic window HCOL expression after breakdown *)
Definition dynwin_HCOL (a: avector 3) :=
  (HBinOp (IgnoreIndex2 Zless) ∘
          HCross
          (HReduction plus zero ∘ (HBinOp (IgnoreIndex2 mult) ∘ HPrepend a) ∘ HInduction _ mult one)
          (HReduction minmax.max zero ∘ (HPointwise (IgnoreIndex abs)) ∘ HBinOp (o:=2) (IgnoreIndex2 sub))).


Local Notation "g ⊚ f" := (@SHCompose Monoid_RthetaFlags _ _ _ _ g f) (at level 40, left associativity) : type_scope.

(*
Intermediate HCOL -> Sigma-HCOL Translation result

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
Definition dynwin_SHCOL (a: avector 3):
  @SHOperator Monoid_RthetaFlags (1+(2+2)) 1 zero :=

  (SafeCast (SHBinOp _ (IgnoreIndex2 Zless)))
    ⊚
    (Apply2Union _ plus (
                  ScatH _ 0 1
                        (range_bound := h_bound_first_half 1 1)
                        (snzord0 := @ScatH_stride1_constr 1 2)
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
                         (snzord0 := @ScatH_stride1_constr 1 2))
                    ⊚
                    (liftM_HOperator _ (@HReduction _ minmax.max 0))
                    ⊚
                    (SHPointwise _ (IgnoreIndex abs))
                    ⊚
                    (SumSparseEmbedding
                       (n:=2)
                       (fun jf => SafeCast (SHBinOp _ (o:=1)
                                                 (Fin1SwapIndex2 jf (IgnoreIndex2 CarrierType.sub))))
                       (fun j => h_index_map (proj1_sig j) 1 (range_bound := (ScatH_1_to_n_range_bound (proj1_sig j) 2 1 (proj2_sig j))))
                       (f_inj := h_j_1_family_injective)
                       (fun j => h_index_map (proj1_sig j) 2 (range_bound:=GathH_jn_domain_bound (proj1_sig j) 2 (proj2_sig j))))
                    ⊚
                    (GathH _ 1 1
                           (domain_bound := h_bound_second_half 1 (2+2)))
                )
    ).

(*

Final SigmaHCOL expression (before translating to h-Code):

BinOp(1, Lambda([ r14, r15 ], geq(r15, r14))) o
SUMUnion(
  Embed(2, 0) o
  ISumReduction(i17, 3, (a, b) -> add(a, b), V(0.0), (arg) -> false,
    PointWise(1, Lambda([ r16, i19 ], mul(r16, nth(D, i17)))) o
    Inductor(3, i17, Lambda([ r9, r10 ], mul(r9, r10)), V(1.0)) o
    Pick(5, 0)
  ),
  Embed(2, 1) o
  ISumReduction(i15, 2, (a, b) -> max(a, b), V(0.0), (arg) -> false,
    BinOp(1, Lambda([ r12, r13 ], abs(sub(r12, r13)))) o
    ISumUnion(i18, 2,
      Embed(2, i18) o
      Pick(5, add(add(i15, V(1)), mul(V(2), i18)))
    )
  )
)
*)
Definition dynwin_SHCOL1 (a:avector 3) :
  @SHOperator Monoid_RthetaFlags dynwin_i dynwin_o zero
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
         ⊚ Apply2Union Monoid_RthetaFlags plus
         (Embed Monoid_RthetaFlags (le_S (le_n 1))
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
                                                      (Pick Monoid_RthetaSafeFlags
                                                          (GathH1_domain_bound_to_base_bound (h_bound_first_half 1 4))))))
         (Embed Monoid_RthetaFlags (le_n 2)
                 ⊚ SafeCast
                 (IReduction minmax.max
                             (λ jf,
                              SHCompose Monoid_RthetaSafeFlags
                                        (SHBinOp Monoid_RthetaSafeFlags
                                                 (λ i
                                                    (a b : CarrierA),
                                                  IgnoreIndex abs i
                                                              (Fin1SwapIndex2
                                                                 jf
                                                                 (IgnoreIndex2 sub) i a b)))
                                        (UnSafeCast
                                           (ISumUnion
                                              (λ jf0,
                                               Embed Monoid_RthetaFlags (proj2_sig jf0)
                                                      ⊚
                                                      Pick Monoid_RthetaFlags
                                                      (h_index_map_compose_range_bound
                                                         (GathH_jn_domain_bound (proj1_sig jf) 2 (proj2_sig jf))
                                                         (h_bound_second_half 1 4) (proj1_sig jf0)
                                                         (proj2_sig jf0)) ))) ))).


