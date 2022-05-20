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


Section WithCarrierA.

  Context `{CAPROPS: CarrierProperties}.

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


  Local Notation "g ⊚ f" := (@SHCompose _ _ Monoid_RthetaFlags _ _ _ _ g f) (at level 40, left associativity) : type_scope.

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
    @SHOperator _ Monoid_RthetaFlags (1+(2+2)) 1 zero :=

    (SafeCast (SHBinOp _ (IgnoreIndex2 Zless)))
      ⊚
      (Apply2Union _ plus (
                     ScatH _ 0 1
                           (range_bound := h_bound_first_half 1 1)
                           (snzord0 := @ScatH_stride1_constr 1 2)
                           ⊚
                           (liftM_HOperator _ (@HReduction _ _ plus 0)  ⊚
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
                       (liftM_HOperator _ (@HReduction _ _ minmax.max 0))
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
    @SHOperator _ Monoid_RthetaFlags dynwin_i dynwin_o zero
    :=   (@SafeCast _ _ _ (Init.Nat.add (S O) (S O)) (S O)
                    (@SHBinOp _ _ Monoid_RthetaSafeFlags _ (S O)
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

End WithCarrierA.

(* BROKEN
   Error: Anomaly "File "clib/int.ml", line 46, characters 14-20: Assertion failed."
   See [https://github.com/coq/coq/issues/13834]

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import MetaCoq.Template.All.

Require Import Helix.MSigmaHCOL.ReifySHCOL.

Section WithR.

  (** * MSHCOL *)
  MetaCoq Run (reifySHCOL dynwin_SHCOL1 100
              [(BasicAst.MPfile ["DynWin"; "DynWin"; "Helix"], "dynwin_SHCOL1")]
              "dynwin_MSHCOL1").

  (** * DSHCOL *)
  (*
    MetaCoq Run (reifyMSHCOL dynwin_MSHCOL1
    [(BasicAst.MPfile ["DynWinProofs"; "DynWin"; "Helix"], "dynwin_MSHCOL1")]
    "dynwin_RHCOL" "dynwin_RHCOL_globals").
   *)

End WithR.
*)

Require Import Coq.ZArith.ZArith.

Require Import Helix.RSigmaHCOL.RSigmaHCOL.
Require Import Helix.FSigmaHCOL.Int64asNT.
Require Import Helix.FSigmaHCOL.FSigmaHCOL.

Import RHCOL.
Definition DynWin_RHCOL_hard : RHCOL.DSHOperator :=
  (DSHAlloc 2
         (DSHSeq
            (DSHSeq
               (DSHAlloc 1
                  (DSHSeq
                     (DSHSeq (DSHMemInit (PVar 0) CarrierAz)
                        (DSHAlloc 1
                           (DSHLoop 3
                              (DSHSeq
                                 (DSHAlloc 1
                                    (DSHSeq
                                       (DSHAssign
                                          (PVar 7, NConst 0)
                                          (PVar 0, NConst 0))
                                       (DSHAlloc 1
                                          (DSHSeq
                                             (DSHPower (NVar 2)
                                                (PVar 1, NConst 0)
                                                (PVar 0, NConst 0)
                                                (AMult (AVar 1) (AVar 0))
                                                CarrierA1)
                                             (DSHIMap 1 (PVar 0) (PVar 3)
                                                (AMult (AVar 0) (ANth (MPtrDeref (PVar 8)) (NVar 4))))))))
                                 (DSHMemMap2 1 (PVar 2) (PVar 1) (PVar 2) (APlus (AVar 1) (AVar 0)))))))
                     (DSHAssign
                        (PVar 0, NConst 0)
                        (PVar 1, NConst 0))))
               (DSHAlloc 1
                  (DSHSeq
                     (DSHSeq (DSHMemInit (PVar 0) CarrierAz)
                        (DSHAlloc 1
                           (DSHLoop 2
                              (DSHSeq
                                 (DSHAlloc 2
                                    (DSHSeq
                                       (DSHLoop 2
                                          (DSHAlloc 1
                                             (DSHSeq
                                                (DSHAssign
                                                   (PVar 9, NPlus
                                                              (NPlus (NConst 1) (NMult (NVar 3) (NConst 1)))
                                                              (NMult (NVar 1) (NMult (NConst 2) (NConst 1))))
                                                   (PVar 0, NConst 0))
                                                (DSHAssign
                                                   (PVar 0, NConst 0)
                                                   (PVar 2, NVar 1)))))
                                       (DSHBinOp 1 (PVar 0)
                                          (PVar 2)
                                          (AAbs (AMinus (AVar 1) (AVar 0))))))
                                 (DSHMemMap2 1 (PVar 2) (PVar 1) (PVar 2) (AMax (AVar 1) (AVar 0)))))))
                     (DSHAssign
                        (PVar 0, NConst 0)
                        (PVar 1, NConst 1)))))
            (DSHBinOp 1 (PVar 0) (PVar 2)
               (AZless (AVar 1) (AVar 0))))).


Import FHCOL.
Require Import FloatUtil.
Definition DynWin_FHCOL_hard : FHCOL.DSHOperator :=
  (DSHAlloc Int64_2
         (DSHSeq
            (DSHSeq
               (DSHAlloc Int64_1
                  (DSHSeq
                     (DSHSeq (DSHMemInit (PVar 0) b64_0)
                        (DSHAlloc Int64_1
                           (DSHLoop 3
                              (DSHSeq
                                 (DSHAlloc Int64_1
                                    (DSHSeq
                                       (DSHAssign
                                          (PVar 7, NConst Int64_0)
                                          (PVar 0, NConst Int64_0))
                                       (DSHAlloc Int64_1
                                          (DSHSeq
                                             (DSHPower (NVar 2)
                                                (PVar 1, NConst Int64_0)
                                                (PVar 0, NConst Int64_0)
                                                (AMult (AVar 1) (AVar 0))
                                                b64_1)
                                             (DSHIMap 1 (PVar 0) (PVar 3)
                                                (AMult (AVar 0) (ANth (MPtrDeref (PVar 8)) (NVar 4))))))))
                                 (DSHMemMap2 1 (PVar 2) (PVar 1) (PVar 2) (APlus (AVar 1) (AVar 0)))))))
                     (DSHAssign
                        (PVar 0, NConst Int64_0)
                        (PVar 1, NConst Int64_0))))
               (DSHAlloc Int64_1
                  (DSHSeq
                     (DSHSeq (DSHMemInit (PVar 0) b64_0)
                        (DSHAlloc Int64_1
                           (DSHLoop 2
                              (DSHSeq
                                 (DSHAlloc Int64_2
                                    (DSHSeq
                                       (DSHLoop 2
                                          (DSHAlloc Int64_1
                                             (DSHSeq
                                                (DSHAssign
                                                   (PVar 9, NPlus
                                                              (NPlus (NConst Int64_1) (NMult (NVar 3) (NConst Int64_1)))
                                                              (NMult (NVar 1) (NMult (NConst Int64_2) (NConst Int64_1))))
                                                   (PVar 0, NConst Int64_0))
                                                (DSHAssign
                                                   (PVar 0, NConst Int64_0)
                                                   (PVar 2, NVar 1)))))
                                       (DSHBinOp 1 (PVar 0)
                                          (PVar 2)
                                          (AAbs (AMinus (AVar 1) (AVar 0))))))
                                 (DSHMemMap2 1 (PVar 2) (PVar 1) (PVar 2) (AMax (AVar 1) (AVar 0)))))))
                     (DSHAssign
                        (PVar 0, NConst Int64_0)
                        (PVar 1, NConst Int64_1)))))
            (DSHBinOp 1 (PVar 0) (PVar 2)
               (AZless (AVar 1) (AVar 0))))).


Require Import Helix.SymbolicDHCOL.SymbolicCT.
Require Import Helix.SymbolicDHCOL.RHCOLtoSRHCOL.
Require Import Helix.SymbolicDHCOL.FHCOLtoSFHCOL.

Definition DynWin_SFHCOL_hard :=
  (DSHAlloc Int64asNT.Int64_2
       (DSHSeq
          (DSHSeq
             (DSHAlloc Int64asNT.Int64_1
                (DSHSeq
                   (DSHSeq (DSHMemInit (SFHCOL.PVar 0) MSymbolicCT.CTypeZero)
                      (DSHAlloc Int64asNT.Int64_1
                         (DSHLoop 3
                            (DSHSeq
                               (DSHAlloc Int64asNT.Int64_1
                                  (DSHSeq
                                     (DSHAssign
                                        (SFHCOL.PVar 7,
                                        NConst
                                          {|
                                            Int64asNT.Int64.intval := 0;
                                            Int64asNT.Int64.intrange :=
                                              conj eq_refl eq_refl
                                          |})
                                        (SFHCOL.PVar 0,
                                        NConst
                                          {|
                                            Int64asNT.Int64.intval := 0;
                                            Int64asNT.Int64.intrange :=
                                              conj eq_refl eq_refl
                                          |}))
                                     (DSHAlloc Int64asNT.Int64_1
                                        (DSHSeq
                                           (DSHPower (NVar (S 1))
                                              (SFHCOL.PVar 1,
                                              NConst
                                                {|
                                                  Int64asNT.Int64.intval := 0;
                                                  Int64asNT.Int64.intrange :=
                                                    conj eq_refl eq_refl
                                                |})
                                              (SFHCOL.PVar 0,
                                              NConst
                                                {|
                                                  Int64asNT.Int64.intval := 0;
                                                  Int64asNT.Int64.intrange :=
                                                    conj eq_refl eq_refl
                                                |}) (AMult (AVar 1) (AVar 0))
                                              MSymbolicCT.CTypeOne)
                                           (DSHIMap 1 (SFHCOL.PVar 0)
                                              (SFHCOL.PVar (S (S 1)))
                                              (AMult (AVar 0)
                                                 (ANth 
                                                    (MPtrDeref (SFHCOL.PVar 8))
                                                    (NVar (S (S (S 1)))))))))))
                               (DSHMemMap2 1 (SFHCOL.PVar (S 1)) 
                                  (SFHCOL.PVar 1) (SFHCOL.PVar (S 1))
                                  (APlus (AVar 1) (AVar 0)))))))
                   (DSHAssign
                      (SFHCOL.PVar 0,
                      NConst
                        {|
                          Int64asNT.Int64.intval := 0;
                          Int64asNT.Int64.intrange := conj eq_refl eq_refl
                        |})
                      (SFHCOL.PVar 1,
                      NConst
                        {|
                          Int64asNT.Int64.intval := 0;
                          Int64asNT.Int64.intrange := conj eq_refl eq_refl
                        |}))))
             (DSHAlloc Int64asNT.Int64_1
                (DSHSeq
                   (DSHSeq (DSHMemInit (SFHCOL.PVar 0) MSymbolicCT.CTypeZero)
                      (DSHAlloc Int64asNT.Int64_1
                         (DSHLoop 2
                            (DSHSeq
                               (DSHAlloc Int64asNT.Int64_2
                                  (DSHSeq
                                     (DSHLoop 2
                                        (DSHAlloc Int64asNT.Int64_1
                                           (DSHSeq
                                              (DSHAssign
                                                 (SFHCOL.PVar 9,
                                                 NPlus
                                                   (NPlus
                                                      (NConst Int64asNT.Int64_1)
                                                      (NMult 
                                                      (NVar (S (S 1)))
                                                      (NConst Int64asNT.Int64_1)))
                                                   (NMult 
                                                      (NVar 1)
                                                      (NMult
                                                      (NConst Int64asNT.Int64_2)
                                                      (NConst Int64asNT.Int64_1))))
                                                 (SFHCOL.PVar 0,
                                                 NConst
                                                   {|
                                                     Int64asNT.Int64.intval := 0;
                                                     Int64asNT.Int64.intrange :=
                                                      conj eq_refl eq_refl
                                                   |}))
                                              (DSHAssign
                                                 (SFHCOL.PVar 0,
                                                 NConst
                                                   {|
                                                     Int64asNT.Int64.intval := 0;
                                                     Int64asNT.Int64.intrange :=
                                                      conj eq_refl eq_refl
                                                   |}) 
                                                 (SFHCOL.PVar (S 1), NVar 1)))))
                                     (DSHBinOp 1 (SFHCOL.PVar 0)
                                        (SFHCOL.PVar (S 1))
                                        (AAbs (AMinus (AVar 1) (AVar 0))))))
                               (DSHMemMap2 1 (SFHCOL.PVar (S 1)) 
                                  (SFHCOL.PVar 1) (SFHCOL.PVar (S 1))
                                  (AMax (AVar 1) (AVar 0)))))))
                   (DSHAssign
                      (SFHCOL.PVar 0,
                      NConst
                        {|
                          Int64asNT.Int64.intval := 0;
                          Int64asNT.Int64.intrange := conj eq_refl eq_refl
                        |}) (SFHCOL.PVar 1, NConst Int64asNT.Int64_1)))))
          (DSHBinOp 1 (SFHCOL.PVar 0) (SFHCOL.PVar (S 1))
             (AZless (AVar 1) (AVar 0))))).

Definition DynWin_SRHCOL_hard :=
  (SRHCOLEval.DSHAlloc (NatAsNT.MNatAsNT.to_nat 2)
       (SRHCOLEval.DSHSeq
          (SRHCOLEval.DSHSeq
             (SRHCOLEval.DSHAlloc (NatAsNT.MNatAsNT.to_nat 1)
                (SRHCOLEval.DSHSeq
                   (SRHCOLEval.DSHSeq
                      (SRHCOLEval.DSHMemInit (SRHCOL.PVar 0) MSymbolicCT.CTypeZero)
                      (SRHCOLEval.DSHAlloc (NatAsNT.MNatAsNT.to_nat 1)
                         (SRHCOLEval.DSHLoop 3
                            (SRHCOLEval.DSHSeq
                               (SRHCOLEval.DSHAlloc (NatAsNT.MNatAsNT.to_nat 1)
                                  (SRHCOLEval.DSHSeq
                                     (SRHCOLEval.DSHAssign
                                        (SRHCOL.PVar 7,
                                        SRHCOLEval.NConst
                                          (NatAsNT.MNatAsNT.to_nat 0))
                                        (SRHCOL.PVar 0,
                                        SRHCOLEval.NConst
                                          (NatAsNT.MNatAsNT.to_nat 0)))
                                     (SRHCOLEval.DSHAlloc
                                        (NatAsNT.MNatAsNT.to_nat 1)
                                        (SRHCOLEval.DSHSeq
                                           (SRHCOLEval.DSHPower
                                              (SRHCOLEval.NVar (S 1))
                                              (SRHCOL.PVar 1,
                                              SRHCOLEval.NConst
                                                (NatAsNT.MNatAsNT.to_nat 0))
                                              (SRHCOL.PVar 0,
                                              SRHCOLEval.NConst
                                                (NatAsNT.MNatAsNT.to_nat 0))
                                              (SRHCOLEval.AMult 
                                                 (SRHCOLEval.AVar 1)
                                                 (SRHCOLEval.AVar 0))
                                              MSymbolicCT.CTypeOne)
                                           (SRHCOLEval.DSHIMap 1 
                                              (SRHCOL.PVar 0)
                                              (SRHCOL.PVar (S (S 1)))
                                              (SRHCOLEval.AMult 
                                                 (SRHCOLEval.AVar 0)
                                                 (SRHCOLEval.ANth
                                                    (SRHCOLEval.MPtrDeref
                                                      (SRHCOL.PVar 8))
                                                    (SRHCOLEval.NVar (S (S (S 1)))))))))))
                               (SRHCOLEval.DSHMemMap2 1 
                                  (SRHCOL.PVar (S 1)) (SRHCOL.PVar 1)
                                  (SRHCOL.PVar (S 1))
                                  (SRHCOLEval.APlus (SRHCOLEval.AVar 1)
                                     (SRHCOLEval.AVar 0)))))))
                   (SRHCOLEval.DSHAssign
                      (SRHCOL.PVar 0,
                      SRHCOLEval.NConst (NatAsNT.MNatAsNT.to_nat 0))
                      (SRHCOL.PVar 1,
                      SRHCOLEval.NConst (NatAsNT.MNatAsNT.to_nat 0)))))
             (SRHCOLEval.DSHAlloc (NatAsNT.MNatAsNT.to_nat 1)
                (SRHCOLEval.DSHSeq
                   (SRHCOLEval.DSHSeq
                      (SRHCOLEval.DSHMemInit (SRHCOL.PVar 0) MSymbolicCT.CTypeZero)
                      (SRHCOLEval.DSHAlloc (NatAsNT.MNatAsNT.to_nat 1)
                         (SRHCOLEval.DSHLoop 2
                            (SRHCOLEval.DSHSeq
                               (SRHCOLEval.DSHAlloc (NatAsNT.MNatAsNT.to_nat 2)
                                  (SRHCOLEval.DSHSeq
                                     (SRHCOLEval.DSHLoop 2
                                        (SRHCOLEval.DSHAlloc
                                           (NatAsNT.MNatAsNT.to_nat 1)
                                           (SRHCOLEval.DSHSeq
                                              (SRHCOLEval.DSHAssign
                                                 (SRHCOL.PVar 9,
                                                 SRHCOLEval.NPlus
                                                   (SRHCOLEval.NPlus
                                                      (SRHCOLEval.NConst
                                                      (NatAsNT.MNatAsNT.to_nat 1))
                                                      (SRHCOLEval.NMult
                                                      (SRHCOLEval.NVar (S (S 1)))
                                                      (SRHCOLEval.NConst
                                                      (NatAsNT.MNatAsNT.to_nat 1))))
                                                   (SRHCOLEval.NMult
                                                      (SRHCOLEval.NVar 1)
                                                      (SRHCOLEval.NMult
                                                      (SRHCOLEval.NConst
                                                      (NatAsNT.MNatAsNT.to_nat 2))
                                                      (SRHCOLEval.NConst
                                                      (NatAsNT.MNatAsNT.to_nat 1)))))
                                                 (SRHCOL.PVar 0,
                                                 SRHCOLEval.NConst
                                                   (NatAsNT.MNatAsNT.to_nat 0)))
                                              (SRHCOLEval.DSHAssign
                                                 (SRHCOL.PVar 0,
                                                 SRHCOLEval.NConst
                                                   (NatAsNT.MNatAsNT.to_nat 0))
                                                 (SRHCOL.PVar (S 1),
                                                 SRHCOLEval.NVar 1)))))
                                     (SRHCOLEval.DSHBinOp 1 
                                        (SRHCOL.PVar 0) 
                                        (SRHCOL.PVar (S 1))
                                        (SRHCOLEval.AAbs
                                           (SRHCOLEval.AMinus 
                                              (SRHCOLEval.AVar 1)
                                              (SRHCOLEval.AVar 0))))))
                               (SRHCOLEval.DSHMemMap2 1 
                                  (SRHCOL.PVar (S 1)) (SRHCOL.PVar 1)
                                  (SRHCOL.PVar (S 1))
                                  (SRHCOLEval.AMax (SRHCOLEval.AVar 1)
                                     (SRHCOLEval.AVar 0)))))))
                   (SRHCOLEval.DSHAssign
                      (SRHCOL.PVar 0,
                      SRHCOLEval.NConst (NatAsNT.MNatAsNT.to_nat 0))
                      (SRHCOL.PVar 1,
                      SRHCOLEval.NConst (NatAsNT.MNatAsNT.to_nat 1))))))
          (SRHCOLEval.DSHBinOp 1 (SRHCOL.PVar 0) (SRHCOL.PVar (S 1))
             (SRHCOLEval.AZless (SRHCOLEval.AVar 1) (SRHCOLEval.AVar 0))))).
