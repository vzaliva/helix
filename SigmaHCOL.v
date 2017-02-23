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

    Record SHOperator
           {i o: nat}
           {preCond : svector fm i -> Prop}
           {postCond : svector fm o -> Prop}
      : Type
      := mkSHOperator {
             op: svector fm i -> svector fm o ;
             pre_post: forall (x:svector fm i), preCond x -> postCond (op x) ;
             op_proper: Proper ((=) ==> (=)) op
           }.

    (* Equivalence of two SHOperators with same pre and post conditions is defined via functional extensionality *)
    Global Instance SHOperator_equiv
           {i o: nat} {P Q}:
      Equiv (@SHOperator i o P Q) :=
      fun a b => op a = op b.

    Definition SHOperator_hequiv
               {i o: nat}
               {P Q P' Q'}:
      (@SHOperator i o P Q) -> (@SHOperator i o P' Q') -> Prop :=
      fun a b => op a = op b.


    Record SHOperatorFamily
           {i o n: nat}
           {fPreCond: svector fm i → Prop}
           {fPostCond: svector fm o → Prop}
      : Type
      := mkSHOperatorFamily {
             family_member: (forall j (jc:j<n), @SHOperator i o fPreCond fPostCond)
           }.

    (* Accessors, mapping SHOperator family to family of underlying "raw" functions *)
    Definition get_family_op
               {i o n} {P Q}
               (op_family: @SHOperatorFamily i o n P Q):
      forall j (jc:j<n), svector fm i -> svector fm o
      := fun j (jc:j<n) => op (family_member op_family j jc).

    Definition get_family_proper
               {i o n} {P Q}
               (op_family: @SHOperatorFamily i o n P Q):
      forall j (jc:j<n), Proper ((=) ==> (=)) (get_family_op op_family j jc)
      := fun j (jc:j<n) => op_proper (family_member op_family j jc).


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

    Global Instance SHOperatorFamily_equiv
           {i o n: nat} {P Q}:
      Equiv (@SHOperatorFamily i o n P Q) :=
      fun a b => forall j (jc:j<n), family_member a j jc = family_member b j jc.

    Global Instance SHOperatorFamily_equiv_Reflexive
           {i o n: nat} {P Q}:
      Reflexive (@SHOperatorFamily_equiv i o n P Q).
    Proof.
      intros x.
      unfold SHOperatorFamily_equiv.
      auto.
    Qed.

    Global Instance SHOperatorFamily_equiv_Symmetric
           {i o n: nat} {P Q}:
      Symmetric (@SHOperatorFamily_equiv i o n P Q).
    Proof.
      intros x y.
      unfold SHOperatorFamily_equiv.
      intros H j jc.
      specialize (H j jc).
      auto.
    Qed.

    Global Instance SHOperatorFamily_equiv_Transitive
           {i o n: nat} {P Q}:
      Transitive (@SHOperatorFamily_equiv i o n P Q).
    Proof.
      intros x y z.
      unfold SHOperatorFamily_equiv.
      intros H H0 j jc.
      specialize (H j jc).
      specialize (H0 j jc).
      auto.
    Qed.

    Global Instance SHOperatorFamily_equiv_Equivalence
           {i o n: nat} {P Q}:
      Equivalence (@SHOperatorFamily_equiv i o n P Q).
    Proof.
      split.
      apply SHOperatorFamily_equiv_Reflexive.
      apply SHOperatorFamily_equiv_Symmetric.
      apply SHOperatorFamily_equiv_Transitive.
    Qed.

    Lemma SM_op_SHOperator
          (i o : nat)
          {P Q}:
      forall (a:@SHOperator i o P Q), Setoid_Morphism (op a).
    Proof.
      intros a.
      destruct a as [f pre_post f_proper].
      split; try typeclasses eauto.
    Qed.

    Global Instance SHOperator_op_proper {i o P Q} :
      Proper ((=) ==> (=) ==> (=)) (@op i o P Q).
    Proof.
      intros f f' Ef v v' Ev.
      destruct f as [fop op_pre_post op_proper].
      destruct f' as [fop' op_pre_post' op_proper'].
      simpl.
      apply Ef.
      apply Ev.
    Qed.

    Global Instance get_family_op_proper {i o n P Q} :
      Proper ((=) ==>
                  (forall_relation (λ j : nat, pointwise_relation (j < n) (=))))
             (@get_family_op i o n P Q).
    Proof.
      intros a a' Ea.
      unfold forall_relation, pointwise_relation.
      intros j jc.
      unfold get_family_op.
      apply SHOperator_op_proper.
      apply Ea.
    Qed.

    Global Instance SHOperator_op_arg_proper {i o P Q} (a:@SHOperator i o P Q):
      Proper ((=) ==> (=)) (op a).
    Proof.
      solve_proper.
    Qed.

    Global Instance SHOperator_hequiv_proper
          {i o: nat}
          {P Q P' Q'}:
      Proper ((=) ==> (=) ==> (iff)) (@SHOperator_hequiv i o P Q P' Q').
    Proof.
      simpl_relation.
      unfold SHOperator_hequiv.
      unfold equiv, SHOperator_equiv in H, H0.
      split; intros.
      -
        destruct x, y, x0, y0.
        simpl in *.
        rewrite <- H0, <- H1.
        symmetry.
        apply H.
      -
        rewrite H0, <-H1.
        apply H.
    Qed.

    Section Coercions.

      (* (a' <: a) /\ a=a' *)
      Definition coerce_SHOperator
                 {i o} {P1 P2 Q1 Q2}
                 (a': @SHOperator i o P1 Q1) (a: @SHOperator i o P2 Q2): Prop
        :=
          (SHOperator_hequiv a' a) /\
          (forall x, P1 x -> P2 x) /\
          (forall y, Q2 y -> Q1 y).

      (* (a' <: a) /\ a=a' *)
      Definition coerce_SHOperatorFamily
                 {i o n} {P1 P2 Q1 Q2}
                 (a':@SHOperatorFamily i o n P1 Q1) (a:@SHOperatorFamily i o n P2 Q2): Prop
        :=
          (forall j (jc:j<n),
              get_family_op a' j jc = get_family_op a j jc) /\
          (forall x, P1 x -> P2 x) /\
          (forall y, Q2 y -> Q1 y).


      (* Both SHOperator and SHOperatorFamily are pre-orders as they are Reflexive and Transitive as proven above *)
      Section PreOrders.

        Lemma coerce_SHOperator_transitive
              {i o} {Pv Pu Pt Qv Qu Qt}
              (a: @SHOperator i o Pv Qv)
              (b: @SHOperator i o Pu Qu)
              (c: @SHOperator i o Pt Qt):
          coerce_SHOperator a b -> coerce_SHOperator b c -> coerce_SHOperator a c.
        Proof.
          unfold coerce_SHOperator.
          unfold SHOperator_hequiv.
          crush.
        Qed.

        Lemma coerce_SHOperator_reflexive
              {i o} {P Q}
              (a: @SHOperator i o P Q):
          coerce_SHOperator a a.
        Proof.
          unfold coerce_SHOperator.
          split.
          -
            destruct a as [f pre_post op_proper].
            apply op_proper.
          - auto.
        Qed.

        Lemma coerce_SHOperatorFamily_transitive
              {i o n} {P1 P2 P3 Q1 Q2 Q3}
              (a: @SHOperatorFamily i o n P1 Q1)
              (b: @SHOperatorFamily i o n P2 Q2)
              (c: @SHOperatorFamily i o n P3 Q3):
          coerce_SHOperatorFamily a b -> coerce_SHOperatorFamily b c -> coerce_SHOperatorFamily a c.
        Proof.
          unfold coerce_SHOperatorFamily, get_family_op.
          intros [Rab0 [Rab1 Rab2]] [Rbc0 [Rbc1 Rbc2]].
          split.
          -
            intros j jc.
            rewrite Rab0, Rbc0.
            apply op_proper.
          -
            auto.
        Qed.

        Lemma coerce_SHOperatorFamily_reflexive
              {i o n} {P Q}
              (a: @SHOperatorFamily i o n P Q):
          coerce_SHOperatorFamily a a.
        Proof.
          unfold coerce_SHOperatorFamily.
          split.
          -
            intros j jc.
            unfold get_family_op.
            f_equiv.
          -
            auto.
        Qed.

      End PreOrders.

    End Coercions.

    Class DensityPreserving
          {i o:nat}
          {P: svector fm i -> Prop}
          {Q: svector fm o -> Prop}
          (f: @SHOperator i o P Q)
      :=
        o_den_pres :
          forall x, P x -> svector_is_dense fm x -> svector_is_dense fm (op f x).

    (* More generic definition. However this one has a problem as it require (Q y) to hold on all values of 'y', not just in range of (op f)
    Class DensityPreserving
          {i o:nat}
          {P: svector fm i -> Prop}
          {Q: svector fm o -> Prop}
          (f: @SHOperator i o P Q)
      :=
        o_den_pres :
            (forall x, P x -> svector_is_dense fm x) /\
            (forall y, Q y -> svector_is_dense fm y).
     *)

    Definition liftM_HOperator'
               {i o}
               (op: avector i -> avector o)
      : svector fm i -> svector fm o :=
      sparsify fm ∘ op ∘ densify fm.

    Global Instance liftM_HOperator'_proper
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

    Definition liftM_HOperator
               {i o}
               {P: svector fm i -> Prop}
               {Q: svector fm o -> Prop}
               (op: avector i -> avector o)
               `{HOP: HOperator i o op}
               (PQ: forall x, P x -> Q (liftM_HOperator' op x))
      := mkSHOperator i o P Q (liftM_HOperator' op) PQ (@liftM_HOperator'_proper i o op HOP).

    (** Apply family of functions to same fector and return matrix of results *)
    Definition Apply_Family'
               {i o n}
               (op_family_f: forall k, (k<n) -> svector fm i -> svector fm o)
               (v: svector fm i) :
      vector (svector fm o) n :=
      Vbuild
        (λ (j:nat) (jc:j<n),  (op_family_f j jc) v).


    Global Instance Apply_Family'_arg_proper
           {i o n}
           (op_family_f: forall k, (k<n) -> svector fm i -> svector fm o)
           (op_family_f_proper: forall k (kc:k<n), Proper ((=) ==> (=)) (op_family_f k kc))
      :
        Proper ((=) ==> (=)) (@Apply_Family' i o n op_family_f).
    Proof.
      intros x y E.
      unfold Apply_Family'.
      vec_index_equiv j jc.
      rewrite 2!Vbuild_nth.
      apply op_family_f_proper, E.
    Qed.

    (** Apply family of SHOperator's to same fector and return matrix of results *)
    Definition Apply_Family
               {i o n} {P Q}
               (op_family: @SHOperatorFamily i o n P Q)
      :=
        Apply_Family' (get_family_op op_family).

    Global Instance Apply_Family_proper
           {i o n} {P Q}:
      Proper ((=) ==> (=) ==> (=)) (@Apply_Family i o n P Q).
    Proof.
      intros f f' Ef v v' Ev.
      unfold Apply_Family, Apply_Family'.
      vec_index_equiv j jc.
      rewrite 2!Vbuild_nth.
      unfold get_family_op.
      destruct f as [fmem].
      destruct f' as [fmem'].
      simpl.
      unfold equiv, SHOperatorFamily_equiv in Ef. simpl in Ef.
      rewrite <- Ev.
      specialize (Ef j jc).
      apply SHOperator_op_proper.
      apply Ef.
      reflexivity.
    Qed.

    (* Do we need this in presence of Apply_Family_proper ? *)
    Global Instance Apply_Family_arg_proper
           {i o n} {P Q}
           (op_family: @SHOperatorFamily i o n P Q):
      Proper ((=) ==> (=)) (@Apply_Family i o n P Q op_family).
    Proof.
      intros x y E.
      apply Apply_Family'_arg_proper.
      - intros k kc.
        apply get_family_proper.
      - apply E.
    Qed.

    (* Apply operator family to a vector produced a matrix which have at most one non-zero element per row. Strictly *)
    Definition Apply_Family_Single_NonZero_Per_Row
               {i o n}
               {P Q}
               (op_family: @SHOperatorFamily i o n P Q)
      :=
        forall x, Vforall (Vunique (not ∘ Is_ValZero))
                     (transpose
                        (Apply_Family op_family x)
                     ).

    Definition Gather'
               {i o: nat}
               (f: index_map o i)
               (x: svector fm i):
      svector fm o
      := Vbuild (VnthIndexMapped x f).

    Global Instance Gather'_proper
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

    Global Instance Scatter'_proper
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
               {P1: svector fm o2 -> Prop}
               {Q1 : svector fm o3 -> Prop}
               {P2 : svector fm i1 -> Prop}
               {Q2: svector fm o2 -> Prop}
               (QP: forall x, Q2 x -> P1 x)
               (op1: @SHOperator o2 o3 P1 Q1)
               (op2: @SHOperator i1 o2 P2 Q2)
      : @SHOperator i1 o3 P2 Q1.
    Proof.
      refine (mkSHOperator i1 o3 P2 Q1 (compose (op op1) (op op2)) _ _).
      -
        intros x P.
        unfold compose.
        destruct op1, op2.
        simpl in *.
        auto.
    Defined.

    Local Notation "g ⊚ ( qp ) f" := (@SHCompose _ _ _ _ _ _ _ qp g f) (at level 40, left associativity) : type_scope.

    Lemma SHCompose_val_equal_compose
          {i1 o2 o3}
          {P1 Q1 P2 Q2}
          (op1: @SHOperator o2 o3 P1 Q1)
          (op2: @SHOperator i1 o2 P2 Q2)
          {QP: forall x, Q2 x -> P1 x}
      :
        (op op1) ∘ (op op2) = op (op1 ⊚ ( QP ) op2).
    Proof.
      destruct op1, op2.
      simpl in *.
      unfold equiv, ext_equiv.
      intros x y E.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance SHCompose_proper
           {i1 o2 o3 P1 Q1 P2 Q2 QP}
      :
      Proper ((=) ==> (=) ==> (=)) (@SHCompose i1 o2 o3 P1 Q1 P2 Q2 QP).
    Proof.
      intros x x' Ex y y' Ey.
      unfold SHCompose.
      unfold equiv, SHOperator_equiv in *.
      destruct x, y, x', y'.
      simpl in *.
      rewrite <- Ey, <- Ex.
      unfold equiv, ext_equiv.
      apply compose_proper with (RA:=equiv) (RB:=equiv).
      + apply op_proper0.
      + apply op_proper1.
    Qed.

    Section CoerceComposion.
      Variable i1 o2 o3 : nat.

      Variable P1 : svector fm o2 → Prop.
      Variable Q1 : svector fm o3 → Prop.
      Variable op1 : @SHOperator o2 o3 P1 Q1.

      Variable P2 : svector fm i1 → Prop.
      Variable Q2 : svector fm o2 → Prop.
      Variable op2 : @SHOperator i1 o2 P2 Q2.

      Variable QP : ∀ x : svector fm o2, Q2 x → P1 x.

      Variable P2' : svector fm i1 → Prop.
      Variable Q2' : svector fm o2 → Prop.
      Variable op2' : @SHOperator i1 o2 P2' Q2'.

      Variable P1' : svector fm o2 → Prop.
      Variable Q1' : svector fm o3 → Prop.
      Variable op1' : @SHOperator o2 o3 P1' Q1'.

      Definition coerce_SHOperator_Q2'P1'
                 (S1: coerce_SHOperator op1 op1')
                 (S2: coerce_SHOperator op2 op2'):
        (forall x : svector fm o2, Q2' x → P1' x).
      Proof.
        inversion S1.
        inversion S2.
        crush.
      Defined.

      Lemma coerce_SHCompose
            (S1: coerce_SHOperator op1 op1')
            (S2: coerce_SHOperator op2 op2'):
        coerce_SHOperator (op1 ⊚ ( QP ) op2) (op1' ⊚( coerce_SHOperator_Q2'P1' S1 S2 ) op2').
      Proof.
        split ;inversion S1; inversion S2; crush.
        unfold SHOperator_hequiv in *.
        apply compose_proper with (RA:=equiv) (RB:=equiv).
        apply H.
        apply H1.
      Qed.

    End CoerceComposion.


    (* Sigma-HCOL version of HPointwise. We could not just (liftM_Hoperator HPointwise) but we want to preserve structural flags. *)
    Definition SHPointwise'
               {n: nat}
               (f: { i | i<n} -> CarrierA -> CarrierA)
               `{pF: !Proper ((=) ==> (=) ==> (=)) f}
               (x: svector fm n): svector fm n
      := Vbuild (fun j jd => liftM (f (j ↾ jd)) (Vnth x jd)).

    Global Instance SHPointwise'_proper
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

    Global Instance SHBinOp'_proper
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
               (kernel: @SHOperatorFamily ki ko n Pk Qk)
               (* Scatter index map *)
               (f: index_map_family ko o n)
               {f_inj : index_map_family_injective f}
               (* Gather index map *)
               (g: index_map_family ki i n)
               (* Gather pre and post conditions relation *)
               {PQg: ∀ t tc (y:svector fm i), Pg y → Qg (Gather' (⦃ g ⦄ t tc) y)}
               (* Scatter pre and post conditions relation *)
               {PQs: ∀ t tc (y:svector fm ko), Ps y → Qs (Scatter' (⦃ f ⦄ t tc) y)}
      : @SHOperatorFamily i o n Pg Qs
      := mkSHOperatorFamily i o n Pg Qs
                            (fun (j:nat) (jc:j<n) =>
                               (Scatter (⦃f⦄ j jc)
                                        (f_inj:=index_map_family_member_injective f_inj j jc)
                                        (PQs j jc))
                                 ⊚(SK) (family_member kernel j jc)
                                 ⊚(KG) (Gather (⦃g⦄ j jc) (PQg j jc))).

  End FlagsMonoidGenericOperators.

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

  (** This is a definition of a structiral property of a sparse matrix
stating that it will have at at most one non-structural element per
row. *)
  Definition MatrixWithNoRowCollisions
             {m n: nat}
             {fm: Monoid RthetaFlags}
             (mat: vector (svector fm m) n) : Prop
    :=
      Vforall (Vunique Is_Val) (transpose mat).

  (** This postulates a property of an operator family.
  A matrix produced by applying family of operators will have at
  at most one non-structural element per row. The name alludes to the
  fact that doing ISumUnion on such matrix will not lead to
  collisions. It should be noted that this is structural
  constraint. It does not impose any restriction in actual values (of
  CarrierA type) *)
  Definition FamilyIUnionFriendly
             {i o n} {P Q}
             (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n P Q): Prop
    :=
       forall x, P x -> MatrixWithNoRowCollisions
                                          (Apply_Family Monoid_RthetaFlags op_family x).

  (** Matrix-union. This is a common implementations for IUnion and IReduction *)
  Definition Diamond'
             {i o n}
             {fm}
             (dot: CarrierA -> CarrierA -> CarrierA)
             (initial: CarrierA)
             (op_family_f: forall k (kc:k<n), svector fm i -> svector fm o)
             (v:svector fm i): svector fm o
    :=
      MUnion' fm dot initial (@Apply_Family' fm i o n op_family_f v).


  Global Instance Diamond'_proper
         {i o n} {fm}
    : Proper (
          (=) ==> (=) ==>
              (@forall_relation nat
                                (fun k : nat =>  forall _ : k<n, (svector fm i -> svector fm o))
                                (fun k : nat =>  @pointwise_relation (k < n)
                                                                (svector fm i -> svector fm o) (=)))
              ==> (=) ==> (=)) (@Diamond' i o n fm).
  Proof.
    intros d d' Ed ini ini' Ei f f' Ef v v' Ev.
    unfold Diamond'.
    apply MUnion'_proper; auto.

    unfold Apply_Family'.
    vec_index_equiv j jc.
    rewrite 2!Vbuild_nth.
    unfold forall_relation, pointwise_relation in Ef.
    apply Ef, Ev.
  Qed.

  (* One might think we do not need this in presence of Diamond'_proper. However even this partially applied morphism could be easily proven from Diamond'_proper sometimes helps class resolutuion which does not always find Diamond'_proper *)
  Global Instance Diamond'_arg_proper
         {i o n}
         {fm}
         (dot: CarrierA -> CarrierA -> CarrierA)
         `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
         (initial: CarrierA)
         (op_family_f: forall k (kc:k<n), svector fm i -> svector fm o)
         (op_family_f_proper: forall k (kc:k<n), Proper ((=) ==> (=)) (op_family_f k kc))
    : Proper ((=) ==> (=)) (Diamond' dot initial op_family_f).
  Proof.
    apply Diamond'_proper.
    - apply pdot.
    - reflexivity.
    - unfold forall_relation, pointwise_relation.
      apply op_family_f_proper.
  Qed.

  Definition IUnion
             {i o n}
             (* op_family pre and post conditions *)
             {P: rvector i → Prop}
             {Q: rvector o → Prop}
             (* IUnion post-condition *)
             {R: rvector o → Prop}
             {PQ: forall (mat: vector (rvector o) n) d i,
                 (Vforall Q mat) ->
                 R (MUnion' Monoid_RthetaFlags d i mat)
             }
             (* Functional parameters *)
             (dot: CarrierA -> CarrierA -> CarrierA)
             `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
             (initial: CarrierA)
             (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n P Q)
    : @SHOperator Monoid_RthetaFlags i o P R.
  Proof.
    refine(
        mkSHOperator Monoid_RthetaFlags i o P R
                     (Diamond' dot initial (get_family_op Monoid_RthetaFlags op_family))
                     _ _). (* requires get_family_op_proper OR SHOperator_op_arg_proper *)
    -
      intros x Px.
      unfold Diamond'.
      remember (Apply_Family' Monoid_RthetaFlags (get_family_op Monoid_RthetaFlags op_family) x) as mat'.
      assert(M1: Vforall Q mat').
      {
        subst mat'.
        unfold Apply_Family'.
        apply Vforall_Vbuild.
        intros j jc.
        destruct op_family.
        unfold get_family_op.
        generalize (family_member Monoid_RthetaFlags {| family_member := family_member0 |} j jc) as f.
        intros f.
        destruct f.
        auto.
      }
      apply PQ, M1.
  Defined.


  Lemma coerce_IUnion
        {i o n}
        (* op_family pre and post conditions *)
        {P P': rvector i → Prop}
        {Q Q': rvector o → Prop}
        (* IUnion post-condition *)
        {R R': rvector o → Prop}
        (dot: CarrierA -> CarrierA -> CarrierA)
        `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
        (initial: CarrierA)
        (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n P Q)
        (op_family': @SHOperatorFamily Monoid_RthetaFlags i o n P' Q')
        {PQ: forall (mat: vector (rvector o) n) d i,
            (Vforall Q mat) ->
            R (MUnion' Monoid_RthetaFlags d i mat)
        }
        {PQ': forall (mat: vector (rvector o) n) d i,
            (Vforall Q' mat) ->
            R' (MUnion' Monoid_RthetaFlags d i mat)
        }
        (S: coerce_SHOperatorFamily Monoid_RthetaFlags op_family op_family')
        (RR: forall y, R' y -> R y)
    :
      coerce_SHOperator Monoid_RthetaFlags
                        (IUnion dot initial op_family (R:=R) (PQ:=PQ))
                        (IUnion dot initial op_family' (R:=R') (PQ:=PQ')).
  Proof.
    split.
    -
      destruct S as [S [_ _]].
      unfold get_family_op in S.

      simpl.
      apply Diamond'_proper.
      + apply pdot.
      + apply reflexivity.
      +
        unfold forall_relation, pointwise_relation.
        apply S.
    -
      split.
      unfold coerce_SHOperatorFamily in S.
      destruct S as [H [H0 H1]].
      apply H0.
      apply RR.
  Qed.

  Definition ISumUnion
             {i o n}
             (* op_family pre and post conditions *)
             {P: rvector i → Prop}
             {Q: rvector o → Prop}
             (* IUnion post-condition *)
             {R: rvector o → Prop}
             (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n P Q)
             {PQ} : @SHOperator Monoid_RthetaFlags i o P R
    :=
      @IUnion i o n P Q R PQ CarrierAplus _ zero op_family.

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
             (op_family: @SHOperatorFamily Monoid_RthetaSafeFlags i o n P Q)
             {PQ: forall x:rsvector i, P x -> R (Diamond' dot initial (get_family_op Monoid_RthetaSafeFlags op_family) x)}
    : @SHOperator Monoid_RthetaSafeFlags i o P R :=
    mkSHOperator Monoid_RthetaSafeFlags i o P R
                 (Diamond' dot initial (get_family_op Monoid_RthetaSafeFlags op_family))
                 PQ _.

  Lemma coerce_IReduction
        {i o n}
        (* op_family pre and post conditions *)
        {P P': rsvector i → Prop}
        {Q Q': rsvector o → Prop}
        (* IReduction post-condition *)
        {R R': rsvector o → Prop}
        (dot: CarrierA -> CarrierA -> CarrierA)
        `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
        (initial: CarrierA)
        (op_family: @SHOperatorFamily Monoid_RthetaSafeFlags i o n P Q)
        (op_family': @SHOperatorFamily Monoid_RthetaSafeFlags i o n P' Q')
        {PQ: forall x:rsvector i, P x -> R (Diamond' dot initial (get_family_op Monoid_RthetaSafeFlags op_family) x)}
        {PQ': forall x:rsvector i, P' x -> R' (Diamond' dot initial (get_family_op Monoid_RthetaSafeFlags op_family') x)}
        (S: coerce_SHOperatorFamily Monoid_RthetaSafeFlags op_family op_family')
        (RR: forall y, R' y -> R y)
    :
      coerce_SHOperator Monoid_RthetaSafeFlags
                        (IReduction dot initial op_family (R:=R) (PQ:=PQ))
                        (IReduction dot initial op_family' (R:=R') (PQ:=PQ')).
  Proof.
    (* NB: Same proof as coerce_IUnion! *)
    split.
    -
      destruct S as [S [_ _]].
      unfold get_family_op in S.

      simpl.
      apply Diamond'_proper.
      + apply pdot.
      + apply reflexivity.
      +
        unfold forall_relation, pointwise_relation.
        apply S.
    -
      split.
      unfold coerce_SHOperatorFamily in S.
      destruct S as [H [H0 H1]].
      apply H0.
      apply RR.
  Qed.

  Definition ISumReduction
             {i o n}
             (* op_family pre and post conditions *)
             {P: rsvector i → Prop}
             {Q: rsvector o → Prop}
             (* IUnion post-condition *)
             {R: rsvector o → Prop}
             (op_family: @SHOperatorFamily Monoid_RthetaSafeFlags i o n P Q)
             {PQ}
    :=
      @IReduction i o n P Q R plus _ zero op_family PQ.

End SigmaHCOL_Operators.

(* re-define notation outside a section *)
(* Notation "g ⊚ ( qp ) f" := (@SHCompose _ _ _ _ _ _ _ g f qp) (at level 40, left associativity) : type_scope. *)
(* Infix "==" := SHOperator_hequiv (at level 70, no associativity). *)


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

Lemma Apply_Family_SparseEmbedding_SumUnionFriendly
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
       (kernel: @SHOperatorFamily Monoid_RthetaFlags ki ko n Pk Qk)
       (f: index_map_family ko o n)
       {f_inj : index_map_family_injective f}
       (g: index_map_family ki i n)
       (* Gather pre and post conditions relation *)
       {PQg: ∀ t tc (y:rvector i), Pg y → Qg (Gather' Monoid_RthetaFlags (⦃ g ⦄ t tc) y)}
       (* Scatter pre and post conditions relation *)
       {PQs: ∀ t tc (y:rvector ko), Ps y → Qs (Scatter' Monoid_RthetaFlags (⦃ f ⦄ t tc) y)}
  :
    FamilyIUnionFriendly
      (@SparseEmbedding Monoid_RthetaFlags
                        n i o ki ko Pk Qk Ps Qs Pg Qg SK KG
                        kernel
                        f f_inj
                        g
                        PQg PQs).
Proof.
  unfold FamilyIUnionFriendly.
  intros x.
  intros Pgx.
  apply Vforall_nth_intro.
  intros j jc.
  unfold Vunique.
  intros i0 ic0 i1 ic1.
  unfold transpose.
  rewrite Vbuild_nth.
  unfold row.
  rewrite 2!Vnth_map.
  unfold Apply_Family, Apply_Family'.
  rewrite 2!Vbuild_nth.
  unfold Vnth_aux.
  unfold SparseEmbedding.
  unfold SHCompose, compose.
  unfold get_family_op.
  simpl.

  generalize (Gather' Monoid_RthetaFlags (⦃ g ⦄ i0 ic0) x) as x0; intros x0.
  generalize (Gather' Monoid_RthetaFlags (⦃ g ⦄ i1 ic1) x) as x1; intros x1.
  intros [V0 V1].
  apply Is_Val_Scatter in V0. apply Is_Val_Scatter in V1.

  inversion_clear V0 as [x2 V0']; inversion_clear V0' as [x3 V0''].
  inversion_clear V1  as [x4 V1']; inversion_clear V1' as [x5 V1''].
  subst j.

  unfold index_map_family_injective in f_inj.
  clear PQs.
  specialize (f_inj i0 i1 ic0 ic1 x2 x4 x3 x5).
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
           (kernel: @SHOperatorFamily Monoid_RthetaFlags ki ko n Pk Qk)
           (f: index_map_family ko o n)
           {f_inj : index_map_family_injective f}
           (g: index_map_family ki i n)
           (* Gather pre and post conditions relation *)
           {PQg: ∀ t tc (y:rvector i), Pg y → Qg (Gather' Monoid_RthetaFlags (⦃ g ⦄ t tc) y)}
           (* Scatter pre and post conditions relation *)
           {PQs: ∀ t tc (y:rvector ko), Ps y → Qs (Scatter' Monoid_RthetaFlags (⦃ f ⦄ t tc) y)}
           (* ISumUnion post-condition *)
           {R: vector Rtheta o → Prop}
           (* ISumUnion glue *)
           {PQ}
  : @SHOperator Monoid_RthetaFlags i o Pg R
  :=
    ISumUnion (PQ:=PQ)
              (@SparseEmbedding Monoid_RthetaFlags
                                n i o ki ko Pk Qk Ps Qs Pg Qg SK KG
                                kernel
                                f f_inj
                                g
                                PQg PQs).


Section OperatorProperies.

  Variable fm:Monoid RthetaFlags.
  Variable fml:@MonoidLaws RthetaFlags RthetaFlags_type fm.

  (* Specification of gather as mapping from output to input. NOTE:
    we are using definitional equality here, as Scatter does not
    perform any operations on elements of type A *)
  Lemma Gather'_spec
        {i o: nat}
        (f: index_map o i)
        (x: svector fm i):
    ∀ n (ip : n < o), Vnth (Gather' fm f x) ip ≡ VnthIndexMapped x f n ip.
  Proof.
    unfold Gather', Vbuild.
    destruct (Vbuild_spec (VnthIndexMapped x f)) as [Vv Vs].
    simpl.
    intros.
    subst.
    auto.
  Qed.

  (* Index-function based condition under which Gather output is dense *)
  Lemma Gather'_dense_constr (i ki : nat)
        (g: index_map ki i)
        (x: svector fm i)
        (g_dense: forall k (kc:k<ki), Is_Val (Vnth x («g» k kc))):
    Vforall Is_Val (Gather' fm g x).
  Proof.
    apply Vforall_nth_intro.
    intros i0 ip.
    rewrite Gather'_spec.
    apply g_dense.
  Qed.


  Lemma Gather'_is_endomorphism:
    ∀ (i o : nat)
      (x : svector fm i),
      ∀ (f: index_map o i),
        Vforall (Vin_aux x)
                (Gather' fm f x).
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

  Lemma Gather'_preserves_P:
    ∀ (i o : nat) (x : svector fm i) (P: Rtheta' fm -> Prop),
      Vforall P x
      → ∀ f : index_map o i,
        Vforall P (Gather' fm f x).
  Proof.
    intros.
    assert(Vforall (Vin_aux x) (Gather' _ f x))
      by apply Gather'_is_endomorphism.
    generalize dependent (Gather' _ f x).
    intros t.
    rewrite 2!Vforall_eq.
    crush.
    assert (Vin_aux x x0) by (apply H0; assumption).
    rewrite Vforall_eq in H.
    auto.
  Qed.

  Lemma Gather'_preserves_density:
    ∀ (i o : nat) (x : svector fm i)
      (f: index_map o i),
      svector_is_dense fm x ->
      svector_is_dense fm (Gather' fm f x).
  Proof.
    intros.
    unfold svector_is_dense in *.
    apply Gather'_preserves_P.
    assumption.
  Qed.


  (* Specification of scatter as mapping from input to output. NOTE:
    we are using definitional equality here, as Scatter does not
    perform any operations on elements of type A *)
  Lemma Scatter'_spec
        {i o: nat}
        (f: index_map i o)
        {f_inj: index_map_injective f}
        (x: svector fm i)
        (n: nat) (ip : n < i):
    Vnth x ip ≡ VnthIndexMapped (Scatter' fm f (f_inj:=f_inj) x) f n ip.
  Proof.
    unfold VnthIndexMapped.
    unfold Scatter'.
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


  Lemma Scatter'_is_almost_endomorphism
        (i o : nat)
        (x : svector fm i)
        (f: index_map i o)
        {f_inj : index_map_injective f}:
    Vforall (fun p => (Vin p x) \/ (p ≡ mkSZero))
            (Scatter' fm f (f_inj:=f_inj) x).
  Proof.
    apply Vforall_nth_intro.
    intros j jp.
    unfold Scatter'.
    rewrite Vbuild_nth.
    simpl.
    break_match.
    - left.
      apply Vnth_in.
    - right.
      reflexivity.
  Qed.

  Lemma SHPointwise'_nth
        {n: nat}
        (f: { i | i<n} -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}
        {j:nat} {jc:j<n}
        (v: svector fm n):
    Vnth (SHPointwise' fm f v) jc = mkValue (f (j ↾ jc) (WriterMonadNoT.evalWriter (Vnth v jc))).
  Proof.
    unfold SHPointwise'.
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
        {P Q PQ}
        {j:nat} {jc:j<n}
        (v: svector fm n):
    Vnth (op _ (SHPointwise (P:=P) (Q:=Q) fm f PQ) v) jc ≡ Monad.liftM (f (j ↾ jc)) (Vnth v jc).
  Proof.
    simpl.
    unfold SHPointwise'.
    rewrite Vbuild_nth.
    reflexivity.
  Qed.

  Lemma SHPointwise_equiv_lifted_HPointwise
        {n: nat}
        (f: { i | i<n} -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}
        {P Q PQ PQ1}:
    SHPointwise (P:=P) (Q:=Q) fm f PQ =
    liftM_HOperator fm (@HPointwise n f pF) PQ1.
  Proof.
    apply ext_equiv_applied_iff'.
    - apply SM_op_SHOperator.
    - apply SM_op_SHOperator.
    -
      intros x.
      simpl.
      vec_index_equiv j jc.
      rewrite SHPointwise'_nth.
      unfold liftM_HOperator'.
      unfold compose.
      unfold sparsify; rewrite Vnth_map.
      rewrite HPointwise_nth.
      unfold densify; rewrite Vnth_map.
      reflexivity.
  Qed.

  Lemma SHBinOp'_nth
        {o}
        {f: nat -> CarrierA -> CarrierA -> CarrierA}
        `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
        {v: svector fm (o+o)}
        {j:nat}
        {jc: j<o}
        {jc1:j<o+o}
        {jc2: (j+o)<o+o}
    :
      Vnth (@SHBinOp' fm o f pF v) jc ≡ liftM2 (f j) (Vnth v jc1) (Vnth v jc2).
  Proof.
    unfold SHBinOp', vector2pair.
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
        {P: svector fm (o + o) → Prop}
        {Q: svector fm o → Prop}
        (f: nat -> CarrierA -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
        {PQ: forall x : svector fm (o + o), P x -> Q (SHBinOp' fm f x)}
        {PQ'}
    :
      @SHBinOp fm o P Q f pF PQ = @liftM_HOperator fm (o+o) o P Q (@HBinOp o f pF) _ PQ'.
  Proof.
    apply ext_equiv_applied_iff'.
    -
      simpl.
      split.
      + apply vec_Setoid.
      + apply vec_Setoid.
      + apply SHBinOp'_proper.
    -
      simpl.
      split.
      + apply vec_Setoid.
      + apply vec_Setoid.
      + apply liftM_HOperator'_proper.
        apply HBinOp_HOperator.
    -
      intros x.
      simpl.
      vec_index_equiv j jc.

      assert(jc1: j<o+o) by omega.
      assert(jc2: j+o<o+o) by omega.
      rewrite (@SHBinOp'_nth o f pF x j jc jc1 jc2).

      unfold liftM_HOperator'.
      unfold compose.
      unfold sparsify; rewrite Vnth_map.
      rewrite (@HBinOp_nth o f pF _ j jc jc1 jc2).
      unfold densify; rewrite 2!Vnth_map.

      rewrite <- evalWriter_Rtheta_liftM2 by apply fml.
      rewrite mkValue_evalWriter.
      reflexivity.
  Qed.

  (*


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
 *)
End OperatorProperies.

Section StructuralProperies.

  (*
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

   *)

  Section FlagsMonoidGenericStructuralProperties.
    Variable fm:Monoid RthetaFlags.
    Variable fml:@MonoidLaws RthetaFlags RthetaFlags_type fm.


    Lemma liftM_HOperator'_preserves_density
          {i o: nat}
          (f: avector i -> avector o)
      :
        forall x,
          svector_is_dense fm x -> svector_is_dense fm (liftM_HOperator' fm f x).
    Proof.
      intros x Dx.
      unfold liftM_HOperator', compose.
      generalize (f (densify fm x)) as y. intros y.
      unfold svector_is_dense, sparsify.
      apply Vforall_map_intro.
      apply Vforall_nth_intro.
      intros i0 ip.
      apply IsVal_mkValue.
    Qed.

    (* All lifted HOperators are naturally density preserving *)
    Global Instance liftM_HOperator_DensityPreserving
           {i o}
           {P: svector fm i -> Prop}
           {Q: svector fm o -> Prop}
           (f: avector i -> avector o)
           `{HOP: HOperator i o f}
           (PQ: forall x, P x -> Q (liftM_HOperator' fm f x))
      : DensityPreserving fm (liftM_HOperator fm f PQ).
    Proof.
      unfold DensityPreserving.
      intros x Px Dx.
      unfold liftM_HOperator in *.
      simpl in *.
      apply liftM_HOperator'_preserves_density, Dx.
    Qed.
  (*
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
   *)
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


  Global Instance SHBinOp_DensityPreserving
         {o}
         {P: rvector (o+o) -> Prop}
         {Q: rvector o -> Prop}
         (f: nat -> CarrierA -> CarrierA -> CarrierA)
         `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
         (PQ: forall x, P x -> Q (SHBinOp' _ f x)):
    DensityPreserving Monoid_RthetaFlags (@SHBinOp _ o P Q f pF PQ).
  Proof.
    unfold DensityPreserving.
    intros x Px D.
    unfold svector_is_dense.
    apply Vforall_nth_intro.
    intros j jc.
    assert (jc1 : j < o + o) by omega.
    assert (jc2 : j + o < o + o) by omega.
    simpl.
    erewrite (@SHBinOp'_nth _ o f pF x j jc jc1 jc2).
    assert(V1: Is_Val (Vnth x jc1)) by apply Vforall_nth, D.
    assert(V2: Is_Val (Vnth x jc2)) by apply Vforall_nth, D.
    generalize dependent (Vnth x jc1).
    generalize dependent (Vnth x jc2).
    intros v1 V1 v2 V2.
    apply Is_Val_LiftM2; assumption.
  Qed.


  Lemma USparseEmbeddingIsDense
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
        (kernel: @SHOperatorFamily Monoid_RthetaFlags ki ko n Pk Qk)
        (f: index_map_family ko o n)
        {f_inj : index_map_family_injective f}
        (g: index_map_family ki i n)
        (* Gather pre and post conditions relation *)
        {PQg: ∀ t tc (y:rvector i), Pg y → Qg (Gather' Monoid_RthetaFlags (⦃ g ⦄ t tc) y)}
        (* Scatter pre and post conditions relation *)
        {PQs: ∀ t tc (y:rvector ko), Ps y → Qs (Scatter' Monoid_RthetaFlags (⦃ f ⦄ t tc) y)}
        (* ISumUnion post-condition *)
        {R: vector Rtheta o → Prop}
        (* ISumUnion glue *)
        {PQ}

        (* Extra constraints *)
        {nz: n ≢ 0}
        {f_sur: index_map_family_surjective f} (* gives density *)
    :
      (forall k (kc: k<n), @DensityPreserving Monoid_RthetaFlags ki ko Pk Qk (family_member Monoid_RthetaFlags kernel k kc)) ->
      forall (x: rvector i) (Pgx: Pg x),
        (forall j (jc:j<n) k (kc:k<ki), Is_Val (Vnth x («⦃g⦄ j jc» k kc))) ->
        svector_is_dense _
                         (op _ (@USparseEmbedding n i o ki ko
                                                  Pk Qk Ps Qs Pg Qg
                                                  SK KG
                                                  kernel f f_inj g
                                                  PQg PQs R PQ
                               ) x).
  Proof.
    intros KD x Pgx g_dense.
    apply Vforall_nth_intro.
    intros oi oic.
    unfold compose.
    unfold USparseEmbedding, ISumUnion, IUnion, SparseEmbedding, Diamond', Apply_Family'.
    unfold get_family_op;simpl.
    rewrite AbsorbMUnion'Index_Vbuild.
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

      assert(Vforall Is_Val (Gather' _ (⦃g ⦄ p pc) x))
        by apply Gather'_dense_constr, g_dense.

      specialize (PQg p pc x).
      generalize dependent (Gather' _ (⦃g ⦄ p pc) x).
      intros gx PQg GD.
      clear g_dense.


      assert(Vforall Is_Val (op Monoid_RthetaFlags (family_member Monoid_RthetaFlags kernel p pc) gx)).
      {
        apply KD.
        apply KG, PQg, Pgx.
        apply GD.
      }

      generalize dependent (op Monoid_RthetaFlags (family_member Monoid_RthetaFlags kernel p pc) gx).
      intros kx KD1.
      clear KD GD.

      unfold Scatter'; rewrite Vbuild_nth.

      clear PQs.
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

(*
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
         `{Uf: !FamilyIUnionFriendly op_family}
         {NC: forall k (kc: k<n), CauseNoCol _ (op_family k kc)}:
    CauseNoCol _ (SumUnion _ ∘ (Apply_Family _ op_family)).
  Proof.
    unfold compose, CauseNoCol.
    intros x Xcf.
    unfold FamilyIUnionFriendly in Uf.
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
 *)

End StructuralProperies.
