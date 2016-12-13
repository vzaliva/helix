(* Coq defintions for Sigma-HCOL operator language *)

Require Import VecUtil.
Require Import VecSetoid.
Require Import Spiral.
Require Import Rtheta.
Require Import SVector.
Require Import IndexFunctions.
Require Import HCOL. (* Presently for HOperator only. Consider moving it elsewhere *)

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.BoolEq.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Require Import CpdtTactics.
Require Import JRWTactics.
Require Import SpiralTactics.
Require Import Psatz.
Require Import Omega.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.theory.rings.
Require Import MathClasses.implementations.peano_naturals.
Require Import MathClasses.orders.orders.
Require Import MathClasses.orders.semirings.
Require Import MathClasses.theory.setoids.

(* Ext Lib *)
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Monoid.

Import Monoid.

(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.
Open Scope vector_scope.

Global Open Scope nat_scope.

(* Returns an element of the vector 'x' which is result of mapping of given
natrual number by index mapping function f_spec. *)
Definition VnthIndexMapped
           {i o:nat}
           {A: Type}
           (x: vector A i)
           (f: index_map o i)
           (n:nat) (np: n<o)
  : A
  := Vnth x (« f » n np).

Section SigmaHCOL_Operators.

  Section FlagsMonoidGenericOperators.

    Variable fm:Monoid RthetaFlags.
    Variable fml:@MonoidLaws RthetaFlags RthetaFlags_type fm.

    Record SHOperator
           {i o: nat}
           {preCond : svector fm i → Prop}
           {postCond : svector fm o → Prop}
      : Type
      := mkSHOperator {
             op: svector fm i -> svector fm o ;
             pre_post: forall (x:svector fm i), preCond x -> postCond (op x) ;
             op_proper: Proper ((=) ==> (=)) op
           }.

    Class DensityPreserving
          {i o:nat}
          {P Q}
          (f: @SHOperator i o P Q)
      :=
        o_den_pres : forall x, svector_is_dense fm x -> svector_is_dense fm (op f x).

    (*

    (* Weaker condition: applied to a dense vector without collisions does not produce strucural collisions *)
    Class DenseCauseNoCol {i o:nat} (op: svector fm i -> svector fm o) :=
      o_den_non_col : forall x,
        svector_is_dense fm x ->
        svector_is_non_collision fm x ->
        svector_is_non_collision fm (op x).

    (* Even weaker condition: applied to a vector without collisions does not produce strucural collisions *)
    Class CauseNoCol {i o:nat} (op: svector fm i -> svector fm o) :=
      o_non_col : forall x,
        svector_is_non_collision fm x ->
        svector_is_non_collision fm (op x).
     *)

    (* Evaluation semantics for SHOperator defined used sigma types *)
    Definition evalSHOperator {i o} {P} {Q} (f:@SHOperator i o P Q):
      {x: svector fm i | P x} -> {y: svector fm o | Q y}
      := fun a => let (v,p) := a in
               @exist (svector fm o) Q (op f v)
                      (pre_post f v p).

    (* Equivalence of two SHOperators with same pre and post conditions is defined via functional extensionality *)
    Global Instance SHOperator_equiv
           {i o: nat} {P Q}:
      Equiv (@SHOperator i o P Q) :=
      fun a b => op a = op b.

    Lemma SHOperator_ext_equiv_applied
      {i o: nat} {P Q}
      (f g: @SHOperator i o P Q):
      (f=g) -> (forall v, evalSHOperator f v = evalSHOperator g v).
    Proof.
      intros H v.
      unfold equiv, SHOperator_equiv in H.
      unfold evalSHOperator, equiv, sig_equiv.
      destruct v.
      apply H.
      reflexivity.
    Qed.

    Global Instance SHOperator_equiv_Reflexive
           {i o: nat} {P Q}:
      Reflexive (@SHOperator_equiv i o P Q).
    Proof.
      intros x.
      unfold SHOperator_equiv.
      destruct x.
      auto.
    Qed.

    Global Instance SHOperator_equiv_Symmetric
           {i o: nat} {P Q}:
      Symmetric (@SHOperator_equiv i o P Q).
    Proof.
      intros x y.
      unfold SHOperator_equiv.
      auto.
    Qed.

    Global Instance SHOperator_equiv_Transitive
           {i o: nat} {P Q}:
      Transitive (@SHOperator_equiv i o P Q).
    Proof.
      intros x y z.
      unfold SHOperator_equiv.
      auto.
    Qed.

    Global Instance SHOperator_equiv_Equivalence
           {i o: nat} {P Q}:
      Equivalence (@SHOperator_equiv i o P Q).
    Proof.
      split.
      apply SHOperator_equiv_Reflexive.
      apply SHOperator_equiv_Symmetric.
      apply SHOperator_equiv_Transitive.
    Qed.

    Definition liftM_HOperator'
               {i o}
               (op: avector i -> avector o)
      : svector fm i -> svector fm o :=
      sparsify fm ∘ op ∘ densify fm.

    Global Instance liftM_HOperator'_Proper
           {i o}
           (op: avector i -> avector o)
           `{HOP: HOperator i o op}
      :
        Proper ((=) ==> (=)) (liftM_HOperator' op).
    Proof.
      intros x y H.
      unfold liftM_HOperator'.
      unfold compose.
      f_equiv.
      rewrite H.
      reflexivity.
    Qed.

    (* TODO: maybe post-condition is svector_is_dense? *)
    Definition liftM_HOperator
               {i o}
               {P: svector fm i -> Prop}
               {Q: svector fm o -> Prop}
               (op: avector i -> avector o)
               `{HOP: HOperator i o op}
               (PQ: forall x, P x -> Q (liftM_HOperator' op x))
      := mkSHOperator i o P Q (liftM_HOperator' op) PQ (@liftM_HOperator'_Proper i o op HOP).

    (** Apply family of functions to same fector and return matrix of results *)
    Definition Apply_Family'
               {i o n}
               (op_family: forall k, (k<n) -> svector fm i -> svector fm o)
               (v: svector fm i) :
      vector (svector fm o) n :=
      Vbuild
        (λ (j:nat) (jc:j<n),  (op_family j jc) v).

    Global Instance Apply_Family'_proper
           {i o n}
           (op_family: forall k, (k<n) -> svector fm i -> svector fm o)
           (op_family_proper: forall k (kc:k<n), Proper ((=) ==> (=)) (op_family k kc))
      :
        Proper ((=) ==> (=)) (@Apply_Family' i o n op_family).
    Proof.
      intros x y E.
      unfold Apply_Family'.
      vec_index_equiv j jc.
      rewrite 2!Vbuild_nth.
      apply op_family_proper, E.
    Qed.

    (* Mapping SHOperator family to family of underlying "raw" functions *)
    Definition op_family_op
               {i o n} {P Q}
               (op_family: forall k, (k<n) -> @SHOperator i o P Q):
      forall j (jc:j<n), svector fm i -> svector fm o
      := fun j (jc:j<n) => op (op_family j jc).

    (** Apply family of SHOperator's to same fector and return matrix of results *)
    Definition Apply_Family
               {i o n} {P Q}
               (op_family: forall k, (k<n) -> @SHOperator i o P Q)
      :=
        Apply_Family' (op_family_op op_family).

    Global Instance Apply_Family_proper
           {i o n} {P Q}
           (op_family: forall k, (k<n) -> @SHOperator i o P Q):
      Proper ((=) ==> (=)) (@Apply_Family i o n P Q op_family).
    Proof.
      intros x y E.
      apply Apply_Family'_proper.
      - intros k kc.
        apply op_family.
      - apply E.
    Qed.

    (*
    (* Apply operator family to a vector produced a matrix which have at most one non-zero element per row. Strictly *)
    Class Apply_Family_Single_NonZero_Per_Row
          {i o n}
          (op_family: forall k, (k<n) -> svector fm i -> svector fm o)
          `{Koperator: forall k (kc: k<n), @SHOperator i o (op_family k kc)}
      :=
        apply_family_single_row_nz: forall x, Vforall (Vunique (not ∘ Is_ValZero))
                                                      (transpose
                                                         (Apply_Family op_family x)
                                                      ).
     *)

    Definition Gather'
               {i o: nat}
               (f: index_map o i)
               (x: svector fm i):
      svector fm o
      := Vbuild (VnthIndexMapped x f).

    Global Instance Gather'_Proper
           {i o: nat}
           (f: index_map o i):
      Proper ((=) ==> (=)) (Gather' f).
    Proof.
      intros x y Exy.
      unfold Gather', VnthIndexMapped.
      vec_index_equiv j jp.
      rewrite 2!Vbuild_nth.
      apply Vnth_arg_equiv.
      apply Exy.
    Qed.

    Definition Gather
               {i o: nat}
               {P: svector fm i -> Prop}
               {Q: svector fm o -> Prop}
               (f: index_map o i)
               (PQ: forall x, P x -> Q (Gather' f x))
      := mkSHOperator i o P Q (Gather' f) PQ _.

    Definition GathH
               {i o}
               {P: svector fm i -> Prop}
               {Q: svector fm o -> Prop}
               (base stride: nat)
               {domain_bound: ∀ x : nat, x < o → base + x * stride < i}
               (PQ: forall x, P x -> Q (Gather' (h_index_map base stride
                                                             (range_bound:=domain_bound)) x))
      :=
        Gather (h_index_map base stride
                            (range_bound:=domain_bound) (* since we swap domain and range, domain bound becomes range boud *)
               ) PQ.

    Definition Scatter'
               {i o: nat}
               (f: index_map i o)
               {f_inj: index_map_injective f}
               (x: svector fm i) : svector fm o
      :=
        let f' := build_inverse_index_map f in
        Vbuild (fun n np =>
                  match decide (in_range f n) with
                  | left r => Vnth x (inverse_index_f_spec f f' n r)
                  | right _ => mkSZero
                  end).

    Global Instance Scatter'_Proper
           {i o: nat}
           (f: index_map i o)
           {f_inj: index_map_injective f}:
      Proper ((=) ==> (=)) (Scatter' f (f_inj:=f_inj)).
    Proof.
      intros x y Exy.
      unfold Scatter'.
      vec_index_equiv j jp.
      simpl.
      rewrite 2!Vbuild_nth.
      break_match.
      - apply Vnth_arg_equiv, Exy.
      - reflexivity.
    Qed.

    Definition Scatter
               {i o: nat}
               {P: svector fm i -> Prop}
               {Q: svector fm o -> Prop}
               (f: index_map i o)
               {f_inj: index_map_injective f}
               (PQ: forall x, P x -> Q (Scatter' f (f_inj:=f_inj) x))
      := mkSHOperator i o P Q (Scatter' f (f_inj:=f_inj)) PQ _.

    Definition ScatH
               {i o}
               {P: svector fm i -> Prop}
               {Q: svector fm o -> Prop}
               (base stride: nat)
               {range_bound: ∀ x : nat, x < i → base + x * stride < o}
               {snzord0: stride ≢ 0 \/ i < 2}
               (PQ: forall x, P x -> Q (Scatter'
                                          (h_index_map base stride (range_bound:=range_bound))
                                          (f_inj := h_index_map_is_injective base stride (snzord0:=snzord0)) x))
      :=
        Scatter (h_index_map base stride (range_bound:=range_bound))
                (f_inj := h_index_map_is_injective base stride (snzord0:=snzord0)) PQ.


    Definition SHCompose
               {i1 o2 o3}
               {P1 Q1 P2 Q2}
               (op1: @SHOperator o2 o3 P1 Q1)
               (op2: @SHOperator i1 o2 P2 Q2)
               {QP: forall x, Q2 x -> P1 x}
      : @SHOperator i1 o3 P2 Q1.
    Proof.
      refine (mkSHOperator i1 o3 P2 Q1 (compose (op op1) (op op2)) _ _).
      -
        intros x P.
        unfold compose.
        destruct op1, op2.
        simpl in *.
        auto.
      - eapply compose_proper; [apply op1| apply op2].
    Defined.

    Notation "g ⊚ ( qp ) f" := (@SHCompose _ _ _ _ _ _ _ g f qp) (at level 90) : type_scope.

    (* Sigma-HCOL version of HPointwise. We could not just (liftM_Hoperator HPointwise) but we want to preserve structural flags. *)
    Definition SHPointwise'
               {n: nat}
               (f: { i | i<n} -> CarrierA -> CarrierA)
               `{pF: !Proper ((=) ==> (=) ==> (=)) f}
               (x: svector fm n): svector fm n
      := Vbuild (fun j jd => liftM (f (j ↾ jd)) (Vnth x jd)).

    Global Instance SHPointwise'_Proper
           {n: nat}
           (f: { i | i<n} -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=)) f}:
      Proper ((=) ==> (=)) (SHPointwise' f).
    Proof.
      intros x y Exy.
      unfold SHPointwise'.
      vec_index_equiv j jc.
      rewrite 2!Vbuild_nth.
      unfold_Rtheta_equiv.
      rewrite 2!evalWriter_Rtheta_liftM.
      f_equiv.
      apply evalWriter_proper.
      apply Vnth_arg_equiv.
      apply Exy.
    Qed.

    Definition SHPointwise
               {n: nat}
               {P: svector fm n -> Prop}
               {Q: svector fm n -> Prop}
               (f: { i | i<n} -> CarrierA -> CarrierA)
               `{pF: !Proper ((=) ==> (=) ==> (=)) f}
               (PQ: forall x, P x -> Q (SHPointwise' f x))
      := mkSHOperator n n P Q (SHPointwise' f) PQ _.

    Definition SHBinOp'
               {o}
               (f: nat -> CarrierA -> CarrierA -> CarrierA)
               `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
               (v:svector fm (o+o)): svector fm o
      :=  match (vector2pair o v) with
          | (a,b) => Vbuild (fun i ip => liftM2 (f i) (Vnth a ip) (Vnth b ip))
          end.

    Global Instance SHBinOp'_Proper
           {o}
           (f: nat -> CarrierA -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}:
      Proper ((=) ==> (=)) (SHBinOp' (o:=o) f).
    Proof.
      intros x y E.
      unfold SHBinOp'.

      vec_index_equiv j jc.
      unfold vector2pair.

      repeat break_let.
      rename Heqp into H0, Heqp0 into H1.

      replace t with (fst (Vbreak x)) by (rewrite H0 ; reflexivity).
      replace t0 with (snd (Vbreak x)) by (rewrite H0 ; reflexivity).
      replace t1 with (fst (Vbreak y)) by (rewrite H1 ; reflexivity).
      replace t2 with (snd (Vbreak y)) by (rewrite H1 ; reflexivity).
      clear H0 H1.

      rewrite 2!Vbuild_nth.

      unfold_Rtheta_equiv.
      rewrite 2!evalWriter_Rtheta_liftM2.

      f_equiv.
      - apply evalWriter_proper.
        apply Vnth_arg_equiv.
        rewrite E.
        reflexivity.
      - apply evalWriter_proper.
        apply Vnth_arg_equiv.
        rewrite E.
        reflexivity.
    Qed.

    Definition SHBinOp
               {o}
               {P: svector fm (o+o) -> Prop}
               {Q: svector fm o -> Prop}
               (f: nat -> CarrierA -> CarrierA -> CarrierA)
               `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
               (PQ: forall x, P x -> Q (SHBinOp' f x))
      := mkSHOperator (o+o) o P Q (SHBinOp' f) PQ _.


    (* Sparse Embedding is an operator family *)
    Definition SparseEmbedding
               {n i o ki ko}
               (* kernel pre and post conditions *)
               {Pk: svector fm ki → Prop}
               {Qk: svector fm ko → Prop}
               (* scatter pre and post conditions *)
               {Ps: svector fm ko → Prop}
               {Qs: svector fm o → Prop}
               (* gather pre and post conditions *)
               {Pg: svector fm i → Prop}
               {Qg: svector fm ki → Prop}
               (* Scatter-to-Kernel glue *)
               {SK: ∀ x : svector fm ko, Qk x → Ps x}
               (* Kernel-to-Gather glue *)
               {KG: ∀ x : svector fm ki, Qg x → Pk x}
               (* Kernel *)
               (kernel: forall k, (k<n) -> @SHOperator ki ko Pk Qk)
               `{KD: forall k (kc: k<n), @DensityPreserving ki ko Pk Qk (kernel k kc)}
               (* Scatter index map *)
               (f: index_map_family ko o n)
               {f_inj : index_map_family_injective f}
               (* Gather index map *)
               (g: index_map_family ki i n)
               (* Gather pre and post conditions relation *)
               {PQg: ∀ t tc (y:svector fm i), Pg y → Qg (Gather' (⦃ g ⦄ t tc) y)}
               (* Scatter pre and post conditions relation *)
               {PQs: ∀ t tc (y:svector fm ko), Ps y → Qs (Scatter' (⦃ f ⦄ t tc) y)}
      := fun (j:nat) (jc:j<n) =>
           (Scatter (⦃f⦄ j jc)
                    (f_inj:=index_map_family_member_injective f_inj j jc)
                    (PQs j jc))
             ⊚(SK) (kernel j jc)
             ⊚(KG) (Gather (⦃g⦄ j jc) (PQg j jc)).

  End FlagsMonoidGenericOperators.

  (* re-define notation outside a section *)
  Notation "g ⊚ ( qp ) f" := (@SHCompose _ _ _ _ _ _ _ g f qp) (at level 90) : type_scope.

  Section MUnion.

    Variable fm:Monoid RthetaFlags.

    (* An operator applied to a list of vectors (matrix) with uniform pre and post conditions *)
    Record MSHOperator
           {o n: nat}
           {mPreCond : svector fm o → Prop}
           {mPostCond : svector fm o → Prop}
      : Type
      := mkMSHOperator {
             mop: vector (svector fm o) n -> svector fm o ;
             m_pre_post: forall x, Vforall mPreCond x -> mPostCond (mop x) ;
             mop_proper: Proper ((=) ==> (=)) mop
           }.

    Definition MUnion
               {o n} {P Q}
               (dot: CarrierA->CarrierA->CarrierA)
               `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
               (initial: CarrierA)
               {PQ} :=
      @mkMSHOperator o n P Q (MUnion' fm dot initial) PQ _.


  End MUnion.

  (** This class postulates a property of an operator family.
  A matrix produced by applying family of operators will have at
  at most one non-structural element per row. The name alludes to the
  fact that doing ISumUnion on such matrix will not lead to
  collisions. It should be noted that this is structural
  constraint. It does not impose any restriction in actual values (of
  CarrierA type) *)
  Class IUnionFriendly
        {i o n} {P Q}
        (op_family: forall k (kc: k<n), @SHOperator Monoid_RthetaFlags i o P Q)
    :=
      iunion_friendly: forall x, Vforall (Vunique Is_Val)
                                    (transpose
                                       (Apply_Family Monoid_RthetaFlags op_family x)).

  (** Matrix-union. This is a common implementations for IUnion and IReduction *)
  Definition Diamond'
             {i o n}
             {fm}
             (dot: CarrierA -> CarrierA -> CarrierA)
             (initial: CarrierA)
             (op_family: forall k (kc:k<n), svector fm i -> svector fm o)
             (v:svector fm i): svector fm o
    :=
      MUnion' fm dot initial (@Apply_Family' fm i o n op_family v).


  Global Instance Diamond'_Proper
         {i o n}
         {fm}
         (dot: CarrierA -> CarrierA -> CarrierA)
         `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
         (initial: CarrierA)
         (op_family: forall k (kc:k<n), svector fm i -> svector fm o)
         (op_family_proper: forall k (kc:k<n), Proper ((=) ==> (=)) (op_family k kc))
    : Proper ((=) ==> (=)) (Diamond' dot initial op_family).
  Proof.
    intros x y E.
    unfold Diamond'.
    apply MUnion'_proper; auto.
    apply Apply_Family'_proper; auto.
  Qed.

  (* TODO: density preserving? *)
  Definition IUnion
             {i o n}
             (* op_family pre and post conditions *)
             {P: rvector i → Prop}
             {Q: rvector o → Prop}
             (* IUnion post-condition *)
             {R: rvector o → Prop}
             (dot: CarrierA -> CarrierA -> CarrierA)
             `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
             (initial: CarrierA)
             (op_family: forall k (kc:k<n), @SHOperator Monoid_RthetaFlags i o P Q)
             `{Uf: !IUnionFriendly op_family} (* This is artificial constraint *)
             {PQ: forall x:rvector i, P x -> R (Diamond' dot initial (op_family_op Monoid_RthetaFlags op_family) x)}

    : @SHOperator Monoid_RthetaFlags i o P R.
  Proof.
    refine(
        mkSHOperator Monoid_RthetaFlags i o P R
                     (Diamond' dot initial (op_family_op Monoid_RthetaFlags op_family))
                     PQ _).
    apply Diamond'_Proper.
    apply pdot.
    apply op_family.
  Defined.

  Definition ISumUnion
             {i o n}
             (* op_family pre and post conditions *)
             {P: rvector i → Prop}
             {Q: rvector o → Prop}
             (* IUnion post-condition *)
             {R: rvector o → Prop}
             (op_family: forall k (kc:k<n), @SHOperator Monoid_RthetaFlags i o P Q)
             `{Uf: !IUnionFriendly op_family}
             {PQ}
    :=
      @IUnion i o n P Q R plus _ zero op_family Uf PQ .

  (** IReduction does not have any constraints. Specifically no
  density or Monoid. It just extracts values from Monad and folds them
  row-wise. For example if for (+) id value is 0 and all structural
  values are structural zeros it will do row sums. It could not
  produce new errors, but should propagate errors from before.
   *)
  Definition IReduction
             {i o n}
             (* op_family pre and post conditions *)
             {P: rsvector i → Prop}
             {Q: rsvector o → Prop}
             (* IReduction post-condition *)
             {R: rsvector o → Prop}
             (dot: CarrierA -> CarrierA -> CarrierA)
             `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
             (initial: CarrierA)
             (op_family: forall k (kc:k<n), @SHOperator Monoid_RthetaSafeFlags i o P Q)
             {PQ: forall x:rsvector i, P x -> R (Diamond' dot initial (op_family_op Monoid_RthetaSafeFlags op_family) x)}
    : @SHOperator Monoid_RthetaSafeFlags i o P R.
  Proof.
    refine(
        mkSHOperator Monoid_RthetaSafeFlags i o P R
                     (Diamond' dot initial (op_family_op Monoid_RthetaSafeFlags op_family))
                     PQ _).
    apply Diamond'_Proper.
    apply pdot.
    apply op_family.
  Defined.

  Definition ISumReduction
             {i o n}
             (* op_family pre and post conditions *)
             {P: rsvector i → Prop}
             {Q: rsvector o → Prop}
             (* IUnion post-condition *)
             {R: rsvector o → Prop}
             (op_family: forall k (kc:k<n), @SHOperator Monoid_RthetaSafeFlags i o P Q)
             {PQ}
    :=
      @IReduction i o n P Q R plus _ zero op_family PQ.

End SigmaHCOL_Operators.

(* re-define notation outside a section *)
Notation "g ⊚ ( qp ) f" := (@SHCompose _ _ _ _ _ _ _ g f qp) (at level 90) : type_scope.



(* TODO: maybe <->  *)
Lemma Is_Val_Scatter
      {m n: nat}
      (f: index_map m n)
      {f_inj: index_map_injective f}
      (x: rvector m)
      (j: nat) (jc : j < n):
  Is_Val (Vnth (Scatter' _ f (f_inj:=f_inj) x) jc) ->
  (exists i (ic:i<m), ⟦f⟧ i ≡ j).
Proof.
  intros H.
  unfold Scatter' in H. rewrite Vbuild_nth in H.
  break_match.
  simpl in *.
  -
    generalize dependent (gen_inverse_index_f_spec f j i); intros f_spec H.
    exists (gen_inverse_index_f f j), f_spec.
    apply build_inverse_index_map_is_right_inverse; auto.
  -
    apply Is_Val_mkStruct in H.
    inversion H.
Qed.

Global Instance Apply_Family_SparseEmbedding_SumUnionFriendly
       {n i o ki ko}
       (* kernel pre and post conditions *)
       {Pk: rvector ki → Prop}
       {Qk: rvector ko → Prop}
       (* scatter pre and post conditions *)
       {Ps: rvector ko → Prop}
       {Qs: rvector o → Prop}
       (* gather pre and post conditions *)
       {Pg: rvector i → Prop}
       {Qg: rvector ki → Prop}
       (* Scatter-to-Kernel glue *)
       {SK: ∀ x : rvector ko, Qk x → Ps x}
       (* Kernel-to-Gather glue *)
       {KG: ∀ x : rvector ki, Qg x → Pk x}
       (* Kernel *)
       (kernel: forall k, (k<n) -> {x:rvector ki| Pk x} -> {y:rvector ko| Qk y})
       `{KD: forall k (kc: k<n), @DensityPreserving Monoid_RthetaFlags ki ko Pk Qk (kernel k kc)}
       (f: index_map_family ko o n)
       {f_inj : index_map_family_injective f}
       (g: index_map_family ki i n)
       `{Koperator: forall k (kc: k<n), @SHOperator Monoid_RthetaFlags ki ko Pk Qk (kernel k kc)}
       (* Gather pre and post conditions relation *)
       {PQg: ∀ t tc (y:rvector i), Pg y → Qg (Gather' Monoid_RthetaFlags (⦃ g ⦄ t tc) y)}
       (* Scatter pre and post conditions relation *)
       {PQs: ∀ t tc (y:rvector ko), Ps y → Qs (Scatter' (f_inj:=index_map_family_member_injective f_inj t tc) Monoid_RthetaFlags (⦃ f ⦄ t tc) y)}
  :
    IUnionFriendly
      (@SparseEmbedding Monoid_RthetaFlags
                        n i o ki ko Pk Qk Ps Qs Pg Qg SK KG
                        kernel KD
                        f f_inj
                        g
                        Koperator PQg PQs).
Proof.
  unfold IUnionFriendly.
  intros x.
  apply Vforall_nth_intro.
  intros j jc.
  unfold Vunique.
  intros i0 ic0 i1 ic1.
  unfold transpose.
  rewrite Vbuild_nth.
  unfold row.
  rewrite 2!Vnth_map.
  unfold Apply_Family.
  simpl.
  rewrite 2!Vbuild_nth.
  unfold Vnth_aux.
  unfold SparseEmbedding.
  unfold SHCompose, compose.
  simpl.
  generalize ((Gather Monoid_RthetaFlags (⦃ g ⦄ i0 ic0) (PQg i0 ic0)) x) as x0.
  destruct x0 as [x0 Qgx0].
  generalize (Gather Monoid_RthetaFlags (⦃ g ⦄ i1 ic1) (PQg i1 ic1) x) as x1.
  destruct x1 as [x1 Qgx1].
  repeat break_let; repeat rewrite proj1_sig_exists.
  intros [V0 V1].
  apply Is_Val_Scatter in V0.
  apply Is_Val_Scatter in V1.
  crush.
  unfold index_map_family_injective in f_inj.
  clear PQs.
  specialize (f_inj i0 i1 ic0 ic1 x6 x4 x7 x5).
  destruct f_inj.
  congruence.
  assumption.
Qed.

Definition USparseEmbedding
           {n i o ki ko}
           (* kernel pre and post conditions *)
           {Pk: rvector ki → Prop}
           {Qk: rvector ko → Prop}
           (* scatter pre and post conditions *)
           {Ps: rvector ko → Prop}
           {Qs: rvector o → Prop}
           (* gather pre and post conditions *)
           {Pg: rvector i → Prop}
           {Qg: rvector ki → Prop}
           (* Scatter-to-Kernel glue *)
           {SK: ∀ x : rvector ko, Qk x → Ps x}
           (* Kernel-to-Gather glue *)
           {KG: ∀ x : rvector ki, Qg x → Pk x}
           (* Kernel *)
           (kernel: forall k, (k<n) -> {x:rvector ki| Pk x} -> {y:rvector ko| Qk y})
           `{KD: forall k (kc: k<n), @DensityPreserving Monoid_RthetaFlags ki ko Pk Qk (kernel k kc)}
           (f: index_map_family ko o n)
           {f_inj : index_map_family_injective f}
           (g: index_map_family ki i n)
           `{Koperator: forall k (kc: k<n), @SHOperator Monoid_RthetaFlags ki ko Pk Qk (kernel k kc)}
           (* Gather pre and post conditions relation *)
           {PQg: ∀ t tc (y:rvector i), Pg y → Qg (Gather' Monoid_RthetaFlags (⦃ g ⦄ t tc) y)}
           (* Scatter pre and post conditions relation *)
           {PQs: ∀ t tc (y:rvector ko), Ps y → Qs (Scatter' (f_inj:=index_map_family_member_injective f_inj t tc) Monoid_RthetaFlags (⦃ f ⦄ t tc) y)}
           (* ISumUnion post-condition *)
           {R: vector Rtheta o → Prop}
           (* ISumUnion glue *)
           {PQ: forall x : vector (rvector o) n,  Vforall Qs x → R (MUnion' Monoid_RthetaFlags plus zero x)}
  : {x : rvector i | Pg x} → {x : rvector o | R x}
  :=
    ISumUnion (PQ:=PQ)
              (@SparseEmbedding Monoid_RthetaFlags
                                n i o ki ko Pk Qk Ps Qs Pg Qg SK KG
                                kernel KD
                                f f_inj
                                g
                                Koperator PQg PQs).


Global Instance SHOperator_USparseEmbedding
       {n i o ki ko}
       (* kernel pre and post conditions *)
       {Pk: rvector ki → Prop}
       {Qk: rvector ko → Prop}
       (* scatter pre and post conditions *)
       {Ps: rvector ko → Prop}
       {Qs: rvector o → Prop}
       (* gather pre and post conditions *)
       {Pg: rvector i → Prop}
       {Qg: rvector ki → Prop}
       (* Scatter-to-Kernel glue *)
       {SK: ∀ x : rvector ko, Qk x → Ps x}
       (* Kernel-to-Gather glue *)
       {KG: ∀ x : rvector ki, Qg x → Pk x}
       (* Kernel *)
       (kernel: forall k, (k<n) -> {x:rvector ki| Pk x} -> {y:rvector ko| Qk y})
       `{KD: forall k (kc: k<n), @DensityPreserving Monoid_RthetaFlags ki ko Pk Qk (kernel k kc)}
       (f: index_map_family ko o n)
       {f_inj : index_map_family_injective f}
       (g: index_map_family ki i n)
       `{Koperator: forall k (kc: k<n), @SHOperator Monoid_RthetaFlags ki ko Pk Qk (kernel k kc)}
       (* Gather pre and post conditions relation *)
       {PQg: ∀ t tc (y:rvector i), Pg y → Qg (Gather' Monoid_RthetaFlags (⦃ g ⦄ t tc) y)}
       (* Scatter pre and post conditions relation *)
       {PQs: ∀ t tc (y:rvector ko), Ps y → Qs (Scatter' (f_inj:=index_map_family_member_injective f_inj t tc) Monoid_RthetaFlags (⦃ f ⦄ t tc) y)}
       (* ISumUnion post-condition *)
       {R: vector Rtheta o → Prop}
       (* ISumUnion glue *)
       {PQ: forall x : vector (rvector o) n,  Vforall Qs x → R (MUnion' Monoid_RthetaFlags plus zero x)}:
  SHOperator Monoid_RthetaFlags Pg R (
               @USparseEmbedding
                 n i o ki ko
                 Pk Qk
                 Ps Qs
                 Pg Qg
                 SK KG
                 kernel KD
                 f f_inj
                 g
                 Koperator
                 PQg PQs
                 R PQ
             ).
Proof.
  unfold SHOperator.
  split; repeat apply sig_setoid.
  intros x y E.
  unfold USparseEmbedding, ISumUnion, IUnion, Apply_Family.
  apply ext_equiv_applied_iff'.

  split ; try apply sig_setoid; apply MUnion_proper ; apply CarrierAPlus_proper.
  split ; try apply sig_setoid; apply MUnion_proper ; apply CarrierAPlus_proper.
  reflexivity.
  vec_index_equiv j jc.
  simpl.
  rewrite 2!Vbuild_nth.
  rewrite E.
  reflexivity.
Qed.

Section Subtyping.

  Set Printing Universes.
  (* Subtyping relation between types A and B *)
  Global Class Subtype (A B:Type) := subtype: A -> B -> Prop.

  (* Revert to transparency to allow conversions during unification. *)
  Typeclasses Transparent Subtype.

  Infix "<:" := subtype (at level 40) : type_scope.
  Notation "(<:)" := subtype (at level 40, only parsing) : type_scope.

  Definition TrueP {A} := fun (_:A) => True.

  Global Instance Subtype_Prop:
    Subtype Prop Prop.
  Proof.
    unfold Subtype.
    intros a b.
    exact (a -> b).
  Defined.

  Example PropSubtypeEx1 (x:nat): (x<1) <: (x<5).
  Proof.
    unfold subtype, Subtype_Prop.
    lia.
  Qed.

  Example PropSubtypeEx2 (x:nat): (x<1) <: True.
  Proof.
    unfold subtype, Subtype_Prop.
    tauto.
  Qed.

  Example PropSubtypeEx4 (x:nat): False <: (x<1).
  Proof.
    unfold subtype.
    unfold Subtype_Prop.
    tauto.
  Qed.

  Global Instance Subtype_sig (A:Type) `{Equiv A} {P1 P2}:
    Subtype (@sig A P1) (@sig A P2) :=
    fun a b => `a=`b /\ (forall z, P1 z -> P2 z).

  Example SigSubtypeEx0
          (a:{x:nat|x>5})
          (b:{x:nat|x>1}):
    `a=`b -> a <: b.
  Proof.
    intro Peq.
    unfold subtype, Subtype_sig.
    repeat break_let.
    split.
    - apply Peq.
    - intros z.
      lia.
  Qed.

  Lemma Subtype_sig_simpl
        `{EqA: Equiv A}
        {P1 P2}
        (a:{x:A|P1 x})
        (b:{y:A|P2 y}):
    (a <: b) -> (`a=`b) /\ forall z, P1 z -> P2 z.
  Proof.
    intros S.
    unfold subtype, Subtype_sig in S.
    repeat break_let.
    destruct S as [E1 S1].
    split; [apply E1 | apply S1].
  Qed.

  Global Instance Subtype_psvector {fm} {n} {P1 P2}:
    Subtype (@sig (svector fm n) P1) (@sig (svector fm n) P2).
  Proof.
    apply Subtype_sig.
    apply vec_Equiv.
  Defined.

  Global Instance Subtype_sig_arrow
         {A: Type}
         `{Equiv B}
         {Ps1 Pt1: A -> Prop}
         {Ps2 Pt2: B -> Prop}:
    Subtype (@sig A Ps1 -> @sig B Ps2) (@sig A Pt1 -> @sig B Pt2).
  Proof.
    unfold Subtype.
    intros a b.
    exact (
        (forall z, Pt1 z -> Ps1 z) (* pre-conditions are coercable *)
        /\
        (forall z (Ps1z: Ps1 z) (pt1z: Pt1 z), subtype (a (exist Ps1z)) (b (exist pt1z))) (* functional exensionality *)
      ).

  Defined.

End Subtyping.

(* re-define notation outside the section *)
Infix "<:" := subtype (at level 40) : type_scope.
Notation "(<:)" := subtype (at level 40, only parsing) : type_scope.


Section SubtypingArrows.
  Variable fm : Monoid RthetaFlags.
  Variable i1 o2 o3 : nat.

  Variable P1 : svector fm o2 → Prop.
  Variable Q1 : svector fm o3 → Prop.
  Variable op1 : {x : svector fm o2 | P1 x} → {x : svector fm o3 | Q1 x}.
  Variable op1_SHOperator : SHOperator fm P1 Q1 op1.

  Variable P2 : svector fm i1 → Prop.
  Variable Q2 : svector fm o2 → Prop.
  Variable op2 : {x : svector fm i1 | P2 x} → {x : svector fm o2 | Q2 x}.
  Variable op2_SHOperator : SHOperator fm P2 Q2 op2.

  Variable QP : ∀ x : svector fm o2, Q2 x → P1 x.

  Section Rewrite2ndArg.
    Variable P2' : svector fm i1 → Prop.
    Variable Q2' : svector fm o2 → Prop.
    Variable op2' : {x : svector fm i1 | P2' x} → {x : svector fm o2 | Q2' x}.
    Variable op2'_SHOperator : SHOperator fm P2' Q2' op2'.


    Lemma SHCompose_subtype_2nd (S: op2' <: op2):
      (@SHCompose
         fm
         i1 o2 o3
         P1 Q1 op1 op1_SHOperator
         P2 Q2 op2 op2_SHOperator
         QP)
    <:
      (@SHCompose
         fm
         i1 o2 o3
         P1 Q1 op1 op1_SHOperator
         P2' Q2' op2' op2'_SHOperator
         (Subtype_sig_simpl QP)).



  End Rewrite2ndArg.

End SubtypingArrows.

(*
Section OperatorProperies.

  Variable fm:Monoid RthetaFlags.
  Variable fml:@MonoidLaws RthetaFlags RthetaFlags_type fm.

  (* Specification of gather as mapping from output to input. NOTE:
    we are using definitional equality here, as Scatter does not
    perform any operations on elements of type A *)
  Lemma Gather_spec
        {i o: nat}
        (f: index_map o i)
        (x: svector fm i):
    ∀ n (ip : n < o), Vnth (Gather fm f x) ip ≡ VnthIndexMapped x f n ip.
  Proof.
    unfold Gather, Vbuild.
    destruct (Vbuild_spec (VnthIndexMapped x f)) as [Vv Vs].
    simpl.
    intros.
    subst.
    auto.
  Qed.

  (* Index-function based condition under which Gather output is dense *)
  Lemma Gather_dense_constr (i ki : nat)
        (g: index_map ki i)
        (x: svector fm i)
        (g_dense: forall k (kc:k<ki), Is_Val (Vnth x («g» k kc))):
    Vforall Is_Val (Gather fm g x).
  Proof.
    apply Vforall_nth_intro.
    intros i0 ip.
    rewrite Gather_spec.
    apply g_dense.
  Qed.

  Lemma Gather_is_endomorphism:
    ∀ (i o : nat)
      (x : svector fm i),
      ∀ (f: index_map o i),
        Vforall (Vin_aux x)
                (Gather fm f x).
  Proof.
    intros.
    apply Vforall_eq.
    intros.
    unfold Gather in H.
    unfold Vin_aux.
    apply Vbuild_in in H.
    crush.
    unfold VnthIndexMapped.
    apply Vnth_in.
  Qed.

  Lemma Gather_preserves_P:
    ∀ (i o : nat) (x : svector fm i) (P: Rtheta' fm -> Prop),
      Vforall P x
      → ∀ f : index_map o i,
        Vforall P (Gather fm f x).
  Proof.
    intros.
    assert(Vforall (Vin_aux x) (Gather _ f x))
      by apply Gather_is_endomorphism.
    generalize dependent (Gather _ f x).
    intros t.
    rewrite 2!Vforall_eq.
    crush.
    assert (Vin_aux x x0) by (apply H0; assumption).
    rewrite Vforall_eq in H.
    crush.
  Qed.

  Lemma Gather_preserves_density:
    ∀ (i o : nat) (x : svector fm i)
      (f: index_map o i),
      svector_is_dense fm x ->
      svector_is_dense fm (Gather fm f x).
  Proof.
    intros.
    unfold svector_is_dense in *.
    apply Gather_preserves_P.
    assumption.
  Qed.

  (* Specification of scatter as mapping from input to output. NOTE:
    we are using definitional equality here, as Scatter does not
    perform any operations on elements of type A *)
  Lemma Scatter_spec
        {i o: nat}
        (f: index_map i o)
        {f_inj: index_map_injective f}
        (x: svector fm i)
        (n: nat) (ip : n < i):
    Vnth x ip ≡ VnthIndexMapped (Scatter fm f (f_inj:=f_inj) x) f n ip.
  Proof.
    unfold VnthIndexMapped.
    unfold Scatter.
    rewrite Vbuild_nth.
    break_match.
    simpl.
    apply Vnth_eq.
    symmetry.
    apply build_inverse_index_map_is_left_inverse; try assumption.
    reflexivity.
    absurd (in_range f (⟦ f ⟧ n)).
    - assumption.
    - apply in_range_by_def, ip.
  Qed.

  Lemma Scatter_is_almost_endomorphism
        (i o : nat)
        (x : svector fm i)
        (f: index_map i o)
        {f_inj : index_map_injective f}:
    Vforall (fun p => (Vin p x) \/ (p ≡ mkSZero))
            (Scatter fm f (f_inj:=f_inj) x).
  Proof.
    apply Vforall_nth_intro.
    intros j jp.
    unfold Scatter.
    rewrite Vbuild_nth.
    simpl.
    break_match.
    - left.
      apply Vnth_in.
    - right.
      reflexivity.
  Qed.

  Lemma SHPointwise_nth
        {n: nat}
        (f: { i | i<n} -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}
        {j:nat} {jc:j<n}
        (v: svector fm n):
    Vnth (SHPointwise fm f v) jc = mkValue (f (j ↾ jc) (WriterMonadNoT.evalWriter (Vnth v jc))).
  Proof.
    unfold SHPointwise.
    rewrite Vbuild_nth.
    generalize (Vnth v jc) as x. intros x. clear v.
    rewrite <- evalWriter_Rtheta_liftM.
    rewrite mkValue_evalWriter.
    reflexivity.
  Qed.

  Lemma SHPointwise_nth_eq
        {n: nat}
        (f: { i | i<n} -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}
        {j:nat} {jc:j<n}
        (v: svector fm n):
    Vnth (SHPointwise fm f v) jc ≡ Monad.liftM (f (j ↾ jc)) (Vnth v jc).
  Proof.
    unfold SHPointwise.
    rewrite Vbuild_nth.
    reflexivity.
  Qed.

  Lemma SHPointwise_equiv_lifted_HPointwise
        {n: nat}
        (f: { i | i<n} -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}:
    SHPointwise fm f = liftM_HOperator fm (@HPointwise n f pF).
  Proof.
    apply ext_equiv_applied_iff'; try typeclasses eauto.
    intros x.

    vec_index_equiv j jc.
    rewrite SHPointwise_nth.

    unfold liftM_HOperator.
    unfold compose.
    unfold sparsify; rewrite Vnth_map.
    rewrite HPointwise_nth.
    unfold densify; rewrite Vnth_map.
    reflexivity.
  Qed.

  Lemma SHBinOp_nth
        {o}
        {f: nat -> CarrierA -> CarrierA -> CarrierA}
        `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
        {v: svector fm (o+o)}
        {j:nat}
        {jc: j<o}
        {jc1:j<o+o}
        {jc2: (j+o)<o+o}
    :
      Vnth (@SHBinOp fm o f pF v) jc ≡ liftM2 (f j) (Vnth v jc1) (Vnth v jc2).
  Proof.
    unfold SHBinOp, vector2pair.

    break_let.

    replace t with (fst (Vbreak v)) by crush.
    replace t0 with (snd (Vbreak v)) by crush.
    clear Heqp.

    rewrite Vbuild_nth.
    f_equiv.

    apply Vnth_fst_Vbreak with (jc3:=jc1).
    apply Vnth_snd_Vbreak with (jc3:=jc2).
  Qed.

  Lemma SHBinOp_equiv_lifted_HBinOp
        {o}
        (f: nat -> CarrierA -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}:
    @SHBinOp fm o f pF = liftM_HOperator fm (@HBinOp o f pF).
  Proof.
    apply ext_equiv_applied_iff'; try typeclasses eauto.
    intros x.

    vec_index_equiv j jc.

    assert(jc1: j<o+o) by omega.
    assert(jc2: j+o<o+o) by omega.
    rewrite (@SHBinOp_nth o f pF x j jc jc1 jc2).

    unfold liftM_HOperator.
    unfold compose.
    unfold sparsify; rewrite Vnth_map.
    rewrite (@HBinOp_nth o f pF _ j jc jc1 jc2).
    unfold densify; rewrite 2!Vnth_map.

    rewrite <- evalWriter_Rtheta_liftM2 by apply fml.
    rewrite mkValue_evalWriter.
    reflexivity.
  Qed.

  (* TODO: maybe <->  *)
  Lemma Is_Not_Zero_Scatter
        {m n: nat}
        (f: index_map m n)
        {f_inj: index_map_injective f}
        (x: svector fm m)
        (j: nat) (jc : j < n):
    (not ∘ Is_ValZero) (Vnth (Scatter fm f (f_inj:=f_inj) x) jc) ->
    (exists i (ic:i<m), ⟦f⟧ i ≡ j).
  Proof.
    intros H.
    unfold Scatter in H. rewrite Vbuild_nth in H.
    break_match.
    simpl in *.
    -
      generalize dependent (gen_inverse_index_f_spec f j i); intros f_spec H.
      exists (gen_inverse_index_f f j), f_spec.
      apply build_inverse_index_map_is_right_inverse; auto.
    -
      unfold compose in H.
      assert(C: Is_ValZero (@mkSZero fm)) by apply SZero_is_ValZero.
      congruence.
  Qed.


  Global Instance Apply_Family_SparseEmbedding_Single_NonZero_Per_Row
         {n gi go ki ko}
         (kernel: forall k, (k<n) -> svector fm ki -> svector fm ko)
         `{KD: forall k (kc: k<n), @DensityPreserving _ ki ko (kernel k kc)}
         (f: index_map_family ko go n)
         {f_inj : index_map_family_injective f}
         (g: index_map_family ki gi n)
         `{Koperator: forall k (kc: k<n), @SHOperator _ ki ko (kernel k kc)}
    :
      Apply_Family_Single_NonZero_Per_Row _
                                          (@SparseEmbedding _
                                                            n gi go ki ko
                                                            kernel KD
                                                            f f_inj
                                                            g
                                                            Koperator).
  Proof.
    unfold Apply_Family_Single_NonZero_Per_Row.
    intros x.
    apply Vforall_nth_intro.
    intros j jc.
    unfold Vunique.
    intros i0 ic0 i1 ic1.
    unfold transpose.
    rewrite Vbuild_nth.
    unfold row.
    rewrite 2!Vnth_map.
    unfold Apply_Family.
    rewrite 2!Vbuild_nth.
    unfold Vnth_aux.
    unfold SparseEmbedding.
    unfold compose.
    generalize (kernel i0 ic0 (Gather _ (⦃ g ⦄ i0 ic0) x)) as x0.
    generalize (kernel i1 ic1 (Gather _ (⦃ g ⦄ i1 ic1) x)) as x1.
    intros x0 x1.
    intros [V0 V1].

    apply Is_Not_Zero_Scatter in V0.
    apply Is_Not_Zero_Scatter in V1.
    crush.
    unfold index_map_family_injective in f_inj.
    specialize (f_inj i0 i1 ic0 ic1 x4 x2 x5 x3).
    destruct f_inj.
    congruence.
    assumption.
  Qed.

End OperatorProperies.

Section StructuralProperies.

  Lemma ScatterCollisionFree
        {i o}
        (f: index_map i o)
        {f_inj: index_map_injective f}
        (x: rvector i)
        (Xcf: svector_is_non_collision _ x)
  :
    svector_is_non_collision _ (@Scatter _ i o f f_inj x).
  Proof.
    unfold svector_is_non_collision, Not_Collision in *.
    apply Vforall_nth_intro.
    intros j jp.
    unfold Is_Collision in *.

    assert(E: Vforall
                (fun p => (Vin p x) \/ (p ≡ mkSZero))
                (Scatter _ f (f_inj:=f_inj) x)) by
        apply Scatter_is_almost_endomorphism.

    apply Vforall_nth with (ip:=jp) in E.

    repeat unfold Rtheta', Rtheta in *.
    generalize dependent (@Vnth (Monad_RthetaFlags Monoid_RthetaFlags CarrierA) o (@Scatter Monoid_RthetaFlags i o f f_inj x) j jp).
    intros v E.
    destruct E.
    -
      apply Vforall_in with (v:=x); assumption.
    -
      rewrite_clear H.
      unfold mkSZero, mkStruct, compose.
      tauto.
  Qed.

  Lemma Is_SZero_Scatter_out_of_range
        {m n: nat}
        (f: index_map m n)
        {f_inj: index_map_injective f}
        (x: rvector m)
        (j: nat) (jc : j < n):
    not (in_range f j) ->
    Is_SZero (Vnth (Scatter _ f (f_inj:=f_inj) x) jc).
  Proof.
    intros R.
    unfold Scatter.
    rewrite Vbuild_nth.
    break_match.
    congruence.
    apply Is_SZero_mkSZero.
  Qed.

  Section FlagsMonoidGenericStructuralProperties.
    Variable fm:Monoid RthetaFlags.
    Variable fml:@MonoidLaws RthetaFlags RthetaFlags_type fm.

    (* All lifted HOperators are naturally density preserving *)
    Global Instance liftM_HOperator_DensityPreserving
           {i o}
           (op: avector i -> avector o)
           `{hop: !HOperator op}
      : DensityPreserving fm (liftM_HOperator fm op).
    Proof.
      unfold DensityPreserving.
      intros x D.

      unfold liftM_HOperator, compose.
      generalize (op (densify _ x)) as y. intros y.
      unfold svector_is_dense, sparsify.
      apply Vforall_map_intro.
      apply Vforall_nth_intro.
      intros i0 ip.
      apply IsVal_mkValue.
    Qed.

    Global Instance liftM_HOperator_DenseCauseNoCol
           {i o}
           (op: avector i -> avector o)
           `{hop: !HOperator op}
      : DenseCauseNoCol fm (liftM_HOperator fm op).
    Proof.
      unfold DenseCauseNoCol.
      intros x D NC.
      unfold liftM_HOperator, compose.
      apply sparsify_non_coll.
      apply fml.
    Qed.


    (* Applying Scatter to collision-free vector, using injective family of functions will not cause any collisions *)
    Lemma GatherCollisionFree
          {i o: nat}
          (x: svector fm i)
          (Xcf: svector_is_non_collision fm x)
      :
        forall f, svector_is_non_collision fm (@Gather fm i o f x).
    Proof.
      apply Gather_preserves_P, Xcf.
    Qed.


    Lemma Scatter_eq_mkSZero
          {m n: nat}
          (f: index_map m n)
          {f_inj: index_map_injective f}
          (x: svector fm m)
          (j: nat) (jc : j < n)
          (R: not (in_range f j)):
      Vnth (Scatter _ f (f_inj:=f_inj) x) jc ≡ mkSZero.
    Proof.
      unfold Scatter.
      rewrite Vbuild_nth.
      break_match.
      congruence.
      reflexivity.
    Qed.

  End FlagsMonoidGenericStructuralProperties.


  Lemma Is_Val_LiftM2
        (f : CarrierA → CarrierA → CarrierA)
        (v1 v2 : Rtheta)
        (V1: Is_Val v1)
        (V2: Is_Val v2):
    Is_Val (liftM2 f v2 v1).
  Proof.
    unfold Is_Val, compose, IsVal in *.
    rewrite execWriter_Rtheta_liftM2.
    simpl in *.
    generalize dependent (is_struct (WriterMonadNoT.execWriter v1)); clear v1.
    generalize dependent (is_struct (WriterMonadNoT.execWriter v2)); clear v2.
    intros f1 V1 f2 V2.
    destr_bool.
  Qed.

  Global Instance SHBinOp_DensityPreserving {o}
         (f: nat -> CarrierA -> CarrierA -> CarrierA)
         `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}:
    DensityPreserving Monoid_RthetaFlags (@SHBinOp _ o f pF).
  Proof.
    unfold DensityPreserving.
    intros x D.
    unfold svector_is_dense.
    apply Vforall_nth_intro.
    intros j jc.
    assert (jc1 : j < o + o) by omega.
    assert (jc2 : j + o < o + o) by omega.
    erewrite (@SHBinOp_nth _ o f pF x j jc jc1 jc2).
    assert(V1: Is_Val (Vnth x jc1)) by apply Vforall_nth, D.
    assert(V2: Is_Val (Vnth x jc2)) by apply Vforall_nth, D.
    generalize dependent (Vnth x jc1).
    generalize dependent (Vnth x jc2).
    intros v1 V1 v2 V2.
    apply Is_Val_LiftM2; assumption.
  Qed.

  Lemma USparseEmbeddingIsDense
        {n i o ki ko}
        (kernel: forall k, (k<n) -> rvector ki -> rvector ko)
        `{KD: forall k (kc: k<n), @DensityPreserving _ ki ko (kernel k kc)}
        (f: index_map_family ko o n)
        {f_inj: index_map_family_injective f} (* gives non-col *)
        {f_sur: index_map_family_surjective f} (* gives density *)
        (g: index_map_family ki i n)
        `{Koperator: forall k (kc: k<n), @SHOperator _ ki ko (kernel k kc)}
        (x: rvector i)
        {nz: n ≢ 0}
    :
      (forall j (jc:j<n) k (kc:k<ki), Is_Val (Vnth x («⦃g⦄ j jc» k kc))) ->
      svector_is_dense _
                       (@USparseEmbedding n i o ki ko kernel KD f f_inj g Koperator x).
  Proof.
    intros g_dense.
    apply Vforall_nth_intro.
    intros oi oic.
    unfold compose.
    unfold USparseEmbedding, ISumUnion, IUnion, Apply_Family, SparseEmbedding.
    rewrite AbsorbMUnionIndex_Vbuild.
    unfold compose.
    destruct n.
    - congruence.
    - clear nz.
      apply Is_Val_UnionFold.
      apply Vexists_Vbuild.
      unfold index_map_family_surjective in f_sur.
      specialize (f_sur oi oic).
      destruct f_sur as [z [p [zc [pc F]]]].
      exists p, pc.

      assert(Vforall Is_Val (Gather _ (⦃g ⦄ p pc) x))
        by apply Gather_dense_constr, g_dense.
      generalize dependent (Gather _ (⦃g ⦄ p pc) x).
      intros gx GD.
      clear g_dense g.

      assert(Vforall Is_Val ((kernel p pc) gx)).
      {
        apply KD.
        apply GD.
      }

      generalize dependent ((kernel p pc) gx).
      intros kx KD1.
      clear KD GD gx Koperator kernel.

      unfold Scatter; rewrite Vbuild_nth.


      apply index_map_family_member_injective with (jc:=pc) in f_inj.
      generalize dependent (⦃f ⦄ p pc). intros fp fp_inj F.
      clear f.
      break_match.
      apply Vforall_nth, KD1.
      subst oi.
      absurd (in_range fp (⟦ fp ⟧ z)).
      + assumption.
      + apply in_range_by_def, zc.
  Qed.

  (* Pre-condition for UnionFold not causing any collisions *)
  Lemma Not_Collision_UnionFold
        {n}
        {dot:CarrierA -> CarrierA -> CarrierA}
        {neutral:CarrierA}
        {v: rvector n}
    :
      Vforall Not_Collision v -> Vunique Is_Val v -> Not_Collision (UnionFold _ dot neutral v).
  Proof.
    intros VNC H.
    dependent induction n.
    + dep_destruct v.
      compute.
      trivial.
    +
      dep_destruct v.
      rewrite UnionFold_cons.
      simpl in VNC. destruct VNC as [VNCh VNCx].
      apply UnionCollisionFree.
      *
        apply IHn.
        -- apply VNCx.
        -- clear IHn.
           apply Vunique_cons_tail in H.
           apply H.
      * apply VNCh.
      * cut(¬(Is_Val (UnionFold _ dot neutral x)) \/ (¬ (Is_Val h))).
        firstorder.
        assert(D: Decision (Is_Val h)) by apply Is_Val_dec.
        destruct D as [Ph | Phn].
        -- left.
           clear VNCh VNCx IHn.

           unfold not. intros H0.
           apply Is_Val_UnionFold in H0.
           apply Vexists_eq in H0.
           destruct H0 as [x0 [V1 V2]].
           apply Vin_nth in V1.
           destruct V1 as [i [ip Vx]].
           subst x0.

           unfold Vunique in H.
           assert(jc: 0 < S n) by omega.
           assert(ip': S i < S n) by omega.
           specialize (H 0 jc (S i) ip').
           simpl (Vnth (Vcons h x) jc) in H.
           simpl (Vnth (Vcons h x) ip') in H.
           replace (lt_S_n ip') with ip in H by apply proof_irrelevance.
           assert(H1: Is_Val h ∧ Is_Val (Vnth x ip)) by auto.
           apply H in H1.
           congruence.
        -- right.
           apply Phn.
  Qed.

  Lemma USparseEmbeddingCauseNoCol
        {n i o ki ko}
        (kernel: forall k, (k<n) -> rvector ki -> rvector ko)
        `{KD: forall k (kc: k<n), @DensityPreserving _ ki ko (kernel k kc)}
        `{KNC: forall k (kc: k<n), DenseCauseNoCol _ (kernel k kc)}
        (f: index_map_family ko o n)
        {f_inj: index_map_family_injective f} (* gives non-col *)
        {f_sur: index_map_family_surjective f} (* gives density *)
        (g: index_map_family ki i n)
        `{Koperator: forall k (kc: k<n), @SHOperator _ ki ko (kernel k kc)}
        (x: rvector i)
        {nz: n ≢ 0}
    :
      (forall j (jc:j<n) k (kc:k<ki), Is_Val (Vnth x («⦃g⦄ j jc» k kc))) ->
      (forall j (jc:j<n) k (kc:k<ki), Not_Collision (Vnth x («⦃g⦄ j jc» k kc))) ->
      svector_is_non_collision _
                               (@USparseEmbedding n i o ki ko kernel KD f f_inj g Koperator x).
  Proof.
    intros g_dense GNC.
    apply Vforall_nth_intro.
    intros oi oic.
    unfold compose.
    unfold USparseEmbedding, ISumUnion, IUnion, Apply_Family, SparseEmbedding.
    rewrite AbsorbMUnionIndex_Vbuild.

    destruct n.
    - congruence.
    - (* driving towards apply Not_Collision_UnionFold. *)
      apply Not_Collision_UnionFold.
      +
        clear nz.
        apply Vforall_Vbuild.
        intros j jn.
        unfold compose.
        specialize (GNC j jn).

        (* Get rid of Gather, carring over its properties *)
        assert(GXD: svector_is_dense _ (Gather Monoid_RthetaFlags (⦃ g ⦄ j jn) x)).
        {
          unfold svector_is_dense.
          apply Vforall_nth_intro.
          intros.
          rewrite Gather_spec.
          apply g_dense.
        }

        assert(GXNC: svector_is_non_collision _ (Gather Monoid_RthetaFlags (⦃ g ⦄ j jn) x)).
        {
          unfold svector_is_non_collision.
          apply Vforall_nth_intro.
          intros.
          rewrite Gather_spec.
          apply GNC.
        }
        generalize dependent (Gather _ (⦃ g ⦄ j jn) x).
        intros gx GXD GXNC.
        clear GNC g_dense.

        (* Get rid of lifted kernel, carring over its properties *)
        assert(LD: svector_is_dense Monoid_RthetaFlags ((kernel j jn) gx)).
        {
          apply KD.
          apply GXD.
        }

        assert(KNC1: svector_is_non_collision Monoid_RthetaFlags ((kernel j jn) gx)).
        {
          apply KNC.
          apply GXD.
          apply GXNC.
        }
        generalize dependent ((kernel j jn) gx).
        intros kx KD1 KNC1.
        clear GXD GXNC gx.

        (* Get rid of Scatter  *)
        assert(SNC: svector_is_non_collision Monoid_RthetaFlags (@Scatter _ ko o (family_f ko o (S n) f j jn)
                                                                          (@index_map_family_member_injective ko o (S n) f f_inj j jn) kx)).

        apply ScatterCollisionFree, KNC1.
        generalize dependent (@Scatter Monoid_RthetaFlags ko o (family_f ko o (S n) f j jn)
                                       (@index_map_family_member_injective ko o (S n) f f_inj j jn) kx).
        intros sx SNC.
        unfold svector_is_non_collision in SNC.
        apply Vforall_nth with (ip:=oic) in SNC.
        apply SNC.
      +
        unfold Vunique.
        intros i0 ic j jc.

        rewrite 2!Vbuild_nth.
        unfold compose.

        (* Get rid of Gather, carring over its properties *)
        assert(GXDi0: svector_is_dense _ (Gather Monoid_RthetaFlags (⦃ g ⦄ i0 ic) x)).
        {
          unfold svector_is_dense.
          apply Vforall_nth_intro.
          intros.
          rewrite Gather_spec.
          apply g_dense.
        }
        generalize dependent (Gather _ (⦃ g ⦄ i0 ic) x).
        intros gxi0 GXDi0.

        assert(GXDj: svector_is_dense _ (Gather Monoid_RthetaFlags (⦃ g ⦄ j jc) x)).
        {
          unfold svector_is_dense.
          apply Vforall_nth_intro.
          intros.
          rewrite Gather_spec.
          apply g_dense.
        }
        generalize dependent (Gather _ (⦃ g ⦄ j jc) x).
        intros gxj GXDj.
        clear GNC g_dense.

        (* Get rid of lifted kernel, carring over its properties *)
        assert(svector_is_dense Monoid_RthetaFlags ((kernel i0 ic) gxi0)).
        {
          apply KD.
          apply GXDi0.
        }
        generalize dependent ((kernel i0 ic) gxi0).
        intros kxi KXDi0.
        clear gxi0 GXDi0.

        assert (svector_is_dense Monoid_RthetaFlags ( (kernel j jc) gxj)).
        {
          apply KD.
          apply GXDj.
        }
        generalize dependent ((kernel j jc) gxj).
        intros kxj KXDj.
        clear gxj GXDj.

        (* housekeeping *)
        clear KD KNC Koperator g kernel nz x i ki f_sur.
        rename
          i0 into i,
        n into k,
        kxi into x,
        o into n,
        oi into m,
        oic into mc,
        kxj into y,
        KXDj into YD,
        KXDi0 into XD,
        ko into l.

        intros [Hi Hj].

        apply Is_Val_Scatter in Hi; try assumption; clear XD.
        apply Is_Val_Scatter in Hj; try assumption; clear YD.

        elim Hi; clear Hi; intros x0 H.
        elim H; clear H; intros x0c H0.

        elim Hj; clear Hj; intros x1 H.
        elim H; clear H; intros x1c H1.

        subst m;  clear mc.

        unfold index_map_family_injective in f_inj.
        symmetry in H1.
        specialize (f_inj i j ic jc x0 x1 x0c x1c H1).

        apply f_inj.
  Qed.


  (* Union of UnionFriendly family of operators and collision-free vector will not cause any collisions *)
  Global Instance SumUnion_SumUnionFriendly_CauseNoCol
         {i o n}
         (op_family: forall k, (k<n) -> rvector i -> rvector o)
         `{Koperator: forall k (kc: k<n), @SHOperator _ i o (op_family k kc)}
         `{Uf: !IUnionFriendly op_family}
         {NC: forall k (kc: k<n), CauseNoCol _ (op_family k kc)}:
    CauseNoCol _ (SumUnion _ ∘ (Apply_Family _ op_family)).
  Proof.
    unfold compose, CauseNoCol.
    intros x Xcf.
    unfold IUnionFriendly in Uf.
    specialize (Uf x).
    unfold svector_is_non_collision.
    apply Vforall_nth_intro.
    intros j jc.
    unfold Apply_Family.
    rewrite AbsorbISumUnionIndex_Vbuild.
    apply Not_Collision_UnionFold.
    -
      unfold CauseNoCol in NC.
      apply Vforall_nth_intro.
      intros k kc.
      rewrite Vbuild_nth.
      unfold svector_is_non_collision in NC.
      specialize (NC k kc x Xcf).
      apply Vforall_nth.
      apply NC.

    - apply Vforall_nth with (ip:=jc) in Uf.
      unfold Apply_Family, transpose in Uf.
      rewrite Vbuild_nth in Uf.
      unfold row in Uf.
      rewrite Vmap_Vbuild in Uf.
      unfold Vnth_aux in Uf.
      apply Uf.
  Qed.

End StructuralProperies.
 *)
