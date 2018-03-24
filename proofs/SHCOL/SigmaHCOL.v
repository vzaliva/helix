(* Coq defintions for Sigma-HCOL operator language *)

Require Import Spiral.VecUtil.
Require Import Spiral.Matrix.
Require Import Spiral.VecSetoid.
Require Import Spiral.Spiral.
Require Import Spiral.Rtheta.
Require Import Spiral.SVector.
Require Import Spiral.IndexFunctions.
Require Import Spiral.HCOL. (* Presently for HOperator only. Consider moving it elsewhere *)
Require Import Spiral.FinNatSet.
Require Import Spiral.WriterMonadNoT.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.BoolEq.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Decidable.

Require Import Spiral.SpiralTactics.
Require Import Psatz.
Require Import Omega.

Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.theory.rings.
Require Import MathClasses.implementations.peano_naturals.
Require Import MathClasses.orders.orders.
Require Import MathClasses.orders.semirings.
Require Import MathClasses.theory.setoids.

Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Monoid.

Import Monoid.

Import VectorNotations.
Open Scope vector_scope.

Global Open Scope nat_scope.

(* Not currenly used. For future *)
Section BVector.
  Notation bvector n := (vector bool n).

  Definition false_bvector (n:nat) : bvector n := Vconst false n.
  Definition true_bvector (n:nat) : bvector n := Vconst true n.
  Definition or_bvector (n:nat) (a b: bvector n) :=
    Vmap2 orb a b.
  Definition and_bvector (n:nat) (a b: bvector n) :=
    Vmap2 andb a b.

  Definition Monoid_bvector_false_or (n:nat) : Monoid (bvector n) :=
    Build_Monoid (or_bvector n) (false_bvector n).

  Definition Monoid_bvector_true_and (n:nat) : Monoid (bvector n) :=
    Build_Monoid (and_bvector n) (true_bvector n).

End BVector.

(* Returns an element of the vector 'x' which is result of mapping of
given natrual number by index mapping function f_spec. *)
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
      : Type
      := mkSHOperator {
             op: svector fm i -> svector fm o ;
             op_proper: Proper ((=) ==> (=)) op;
             in_index_set: FinNatSet i ;
             out_index_set: FinNatSet o;
           }.


    (* Two vectors (=) at indices at given set *)
    Definition vec_equiv_at_set
               {n:nat}
               (x y: svector fm n)
               (s: FinNatSet n)
      :=
        (forall j (jc:j<n),
            s(mkFinNat jc) -> Vnth x jc = Vnth y jc).

    Lemma vec_equiv_at_subset
          {k:nat}
          (x y: svector fm k)
          (n h: FinNatSet k):
      Included _ n h -> vec_equiv_at_set x y h -> vec_equiv_at_set x y n.
    Proof.
      intros S E.
      unfold vec_equiv_at_set.
      intros j jc H.
      apply E, S, H.
    Qed.

    Lemma vec_equiv_at_Union
          {i : nat}
          (s0 s1 : FinNatSet i)
          (x y : svector fm i):
      vec_equiv_at_set x y (Union _ s0 s1)
      → (vec_equiv_at_set x y s0 /\ vec_equiv_at_set x y s1).
    Proof.
      intros H.
      unfold vec_equiv_at_set in *.
      split.
      -
        intros j jc H0.
        apply H.
        left.
        apply H0.
      -
        intros j jc H0.
        apply H.
        right.
        apply H0.
    Qed.

    Lemma vec_equiv_at_Full_set {i : nat}
          (x y : svector fm i):
      vec_equiv_at_set x y (Full_set (FinNat i)) <-> x = y.
    Proof.
      split.
      -
        intros H.
        vec_index_equiv j jc.
        apply (H j jc).
        apply Full_intro.
      -
        intros H.
        unfold equiv, vec_Equiv in H.
        unfold vec_equiv_at_set.
        intros j jc F.
        apply Vforall2_elim_nth with (ip:=jc) in H.
        apply H.
    Qed.

    Lemma vec_equiv_at_set_narrowing
          {n : nat}
          (s0 : FinNatSet n)
          (s1 : FinNatSet n)
          (C: Included (FinNat n) s0 s1):
      forall x y : svector fm n,
        vec_equiv_at_set x y s1 → vec_equiv_at_set x y s0.
    Proof.
      intros x y E.
      unfold vec_equiv_at_set in *.
      intros j jc H.
      apply C in H.
      apply E.
      apply H.
    Qed.

    Class SHOperator_Facts
          {i o:nat}
          (xop: @SHOperator i o)
      :=
        {
          (* [in_index_set] membership is decidabe *)
          in_dec: FinNatSet_dec (in_index_set xop);

          (* [out_index_set] membership is decidabe *)
          out_dec: FinNatSet_dec (out_index_set xop);

          (* only values in [in_index_set] affect output *)
          in_as_domain:
            forall x y,
              vec_equiv_at_set x y (in_index_set xop) ->
              op xop x = op xop y;

          (* sufficiently (values in right places, no info on empty
          spaces) filled input vector guarantees properly (values are
          only where values expected) filled output vector *)
          out_as_range: forall v,
              (forall j (jc:j<i), in_index_set xop (mkFinNat jc) -> Is_Val (Vnth v jc))
              ->
              (forall j (jc:j<o), out_index_set xop (mkFinNat jc) -> Is_Val (Vnth (op xop v) jc));

          (* never generate values at sparse positions of output vector *)
          no_vals_at_sparse: forall v,
              (forall j (jc:j<o), ¬ out_index_set xop (mkFinNat jc) -> Is_Struct (Vnth (op xop v) jc));

          (* As long there are no collisions in expected non-sparse places, none is expected in nonsparce places on outpyt*)
          no_coll_range: forall v,
              (forall j (jc:j<i), in_index_set xop (mkFinNat jc) -> Not_Collision (Vnth v jc))
              ->
              (forall j (jc:j<o), out_index_set xop (mkFinNat jc) -> Not_Collision (Vnth (op xop v) jc));
          (* Never generate collisions on sparse places *)
          no_coll_at_sparse: forall v,
              (forall j (jc:j<o), ¬ out_index_set xop (mkFinNat jc) -> Not_Collision (Vnth (op xop v) jc));
        }.

    (* Equivalence of two SHOperators is defined via functional extensionality *)
    Global Instance SHOperator_equiv
           {i o: nat}:
      Equiv (@SHOperator i o) :=
      fun a b => op a = op b.

    (* Special subtyping relation on SHOperator's which involves both value and structural correctness. 'a' is subtype and could be used in place of 'b' *)
    Definition SHOperator_subtyping
               {i o: nat}
               (a b: @SHOperator i o)
               `{Afacts: SHOperator_Facts _ _ a}
               `{Bfacts: SHOperator_Facts _ _ b} :=
      a = b /\
      Included _ (in_index_set a) (in_index_set b) /\
      Same_set _ (out_index_set b) (out_index_set a).

    Definition op_Vforall_P
               {i o: nat}
               (P: Rtheta' fm -> Prop)
               (f: @SHOperator i o)
      :=
        forall x, Vforall P ((op f) x).

    Definition SHOperatorFamily {i o n: nat} := FinNat n -> @SHOperator i o.

    Global Instance SHOperatorFamily_equiv {i o n: nat}:
      Equiv(@SHOperatorFamily i o n)
      := @pointwise_relation (FinNat n) (@SHOperator i o) (=).

    (* Accessors, mapping SHOperator family to family of underlying "raw" functions *)
    Definition get_family_op
               {i o n}
               (op_family: @SHOperatorFamily i o n):
      forall j (jc:j<n), svector fm i -> svector fm o
      := fun j (jc:j<n) => op (op_family (mkFinNat jc)).

    Definition shrink_op_family
               {i o n}
               (op_family: @SHOperatorFamily i o (S n)): @SHOperatorFamily i o n
      := fun jf => op_family (mkFinNat (@le_S (S (proj1_sig jf)) n (proj2_sig jf))).

    Lemma shrink_op_family_facts
          (i o k : nat)
          (op_family : SHOperatorFamily)
          (facts: ∀ (j : nat) (jc : j < S k),
              @SHOperator_Facts i o (op_family (mkFinNat jc))):
      (forall (j : nat) (jc : j < k),
          @SHOperator_Facts i o ((shrink_op_family op_family) (mkFinNat jc))).
    Proof.
      intros j jc.
      apply facts.
    Qed.

    Fixpoint family_in_index_set
             {i o n}
             (op_family: @SHOperatorFamily i o n): FinNatSet i
      :=
        match n as y return (y ≡ n -> @SHOperatorFamily i o y -> FinNatSet i) with
        | O => fun _ _ => (Empty_set _)
        | S j => fun E f => Union _
                                  (in_index_set (op_family (mkFinNat (S_j_lt_n E))))
                                  (family_in_index_set (shrink_op_family f))
        end (eq_refl n) op_family.

    Fixpoint family_out_index_set
             {i o n}
             (op_family: @SHOperatorFamily i o n): FinNatSet o
      :=
        match n as y return (y ≡ n -> @SHOperatorFamily i o y -> FinNatSet o) with
        | O => fun _ _ => (Empty_set _)
        | S j => fun E f => Union _
                              (out_index_set (op_family (mkFinNat (S_j_lt_n E))))
                              (family_out_index_set (shrink_op_family f))
        end (eq_refl n) op_family.

    Lemma family_in_set_includes_members:
      ∀ (i o k : nat) (op_family : @SHOperatorFamily i o k)
        (j : nat) (jc : j < k),
        Included (FinNat i)
                 (in_index_set (op_family (mkFinNat jc)))
                 (family_in_index_set op_family).
    Proof.
      intros i o k op_family j jc.
      unfold Included, In.
      intros x H.

      induction k.
      - inversion jc.
      -
        simpl.
        destruct (eq_nat_dec j k) as [E | NE].
        +
          left.
          subst.
          rewrite (le_unique _ _ (S_j_lt_n _) jc).
          apply H.
        +
          right.
          assert(jc1: j<k) by omega.
          apply IHk with (jc:=jc1). clear IHk.
          unfold shrink_op_family, mkFinNat, proj2_sig in *.
          simpl in *.
          rewrite (le_unique _ _ (le_S jc1) jc).
          apply H.
    Qed.

    Lemma family_in_set_implies_members
          (i o k : nat) (op_family : @SHOperatorFamily i o k)
          (j : nat) (jc : j < i):

      family_in_index_set op_family (mkFinNat jc) ->
      ∃ (t : nat) (tc : t < k),
        in_index_set (op_family (mkFinNat tc))
                     (mkFinNat jc).
    Proof.
      intros H.
      induction k.
      -
        inversion H.
      -
        simpl in H.
        inversion_clear H as [H0 | H1].
        +
          subst.
          unfold In in H1.
          exists k, (le_n (S k)).
          rewrite (le_unique _ _  (le_n (S k)) (@S_j_lt_n (S k) k (@eq_refl nat (S k)))).
          apply H1.
        +
          subst.
          specialize (IHk (shrink_op_family op_family) H0).
          destruct IHk as [t [tc  IHk]].
          exists t.
          assert(tc1: t < S k) by omega.
          exists tc1.

          unfold shrink_op_family, mkFinNat, proj2_sig.
          simpl in *.
          rewrite (le_unique _ _ tc1 (le_S tc)).
          apply IHk.
    Qed.

    Lemma family_out_set_includes_members:
      ∀ (i o k : nat) (op_family : @SHOperatorFamily i o k)
        (j : nat) (jc : j < k),
        Included (FinNat o)
                 (out_index_set (op_family (mkFinNat jc)))
                 (family_out_index_set op_family).
    Proof.
      intros i o k op_family j jc.
      unfold Included, In.
      intros x H.

      induction k.
      - inversion jc.
      -
        simpl.
        destruct (eq_nat_dec j k) as [E | NE].
        +
          left.
          subst.
          rewrite (le_unique _ _ (S_j_lt_n _) jc).
          apply H.
        +
          right.
          assert(jc1: j<k) by omega.
          apply IHk with (jc:=jc1).
          unfold shrink_op_family, mkFinNat, proj2_sig.
          simpl in *.
          rewrite (le_unique _ _ (le_S jc1) jc).
          apply H.
    Qed.

    Lemma family_out_set_implies_members
          (i o k : nat) (op_family : @SHOperatorFamily i o k)
          (j : nat) (jc : j < o):

      family_out_index_set op_family (mkFinNat jc) <->
      ∃ (t : nat) (tc : t < k),
        out_index_set (op_family (mkFinNat tc))
                      (mkFinNat jc).
    Proof.
      split.
      - intros H.
        induction k.
        +
          inversion H.
        +
          simpl in H.
          inversion_clear H as [H0 | H1].
          *
            subst.
            unfold In in H1.
            exists k, (le_n (S k)).
            replace (S_j_lt_n _) with (le_n (S k)) in H1 by apply le_unique.
            apply H1.
          *
            subst.
            specialize (IHk (shrink_op_family op_family) H0).
            destruct IHk as [t [tc  IHk]].
            exists t.
            assert(tc1: t < S k) by omega.
            exists tc1.

            unfold shrink_op_family, mkFinNat, proj2_sig in *.
            simpl in *.
            replace (le_S tc) with tc1 in IHk by apply le_unique.
            apply IHk.
      -
        intros H.
        destruct H as [x [xc H]].
        apply family_out_set_includes_members in H.
        auto.
    Qed.

    Lemma fmaily_in_index_set_dec
          (i o k : nat)
          (op_family : @SHOperatorFamily i o k)
          (op_family_facts: forall (j : nat) (jc : j < k),
              SHOperator_Facts (op_family (mkFinNat jc))):
      FinNatSet_dec (family_in_index_set op_family).
    Proof.
      induction k.
      -
        apply Empty_FinNatSet_dec.
      -
        simpl.
        unfold decidable.
        apply Union_FinNatSet_dec.
        +
          apply op_family_facts.
        +
          apply IHk.
          apply shrink_op_family_facts.
          apply op_family_facts.
    Qed.

    Lemma fmaily_out_index_set_dec
          (i o k : nat)
          (op_family : @SHOperatorFamily i o k)
          (op_family_facts: forall (j : nat) (jc : j < k),
              SHOperator_Facts (op_family (mkFinNat jc))):
      FinNatSet_dec (family_out_index_set op_family).
    Proof.
      induction k.
      -
        apply Empty_FinNatSet_dec.
      -
        simpl.
        unfold decidable.
        apply Union_FinNatSet_dec.
        +
          apply op_family_facts.
        +
          apply IHk.
          apply shrink_op_family_facts.
          apply op_family_facts.
    Qed.

    Lemma SHOperator_ext_equiv_applied
          {i o: nat}
          (f g: @SHOperator i o):
      (f=g) <-> (forall v, op f v = op g v).
    Proof.
      split.
      - intros H v.
        unfold equiv, SHOperator_equiv in H.
        apply H.
        reflexivity.
      -
        intros H.
        apply ext_equiv_applied_equiv.
        split ; try apply vec_Setoid. apply f.
        split ; try apply vec_Setoid. apply g.
        apply H.
    Qed.

    Global Instance SHOperator_equiv_Reflexive
           {i o: nat}:
      Reflexive (@SHOperator_equiv i o).
    Proof.
      intros x.
      unfold SHOperator_equiv.
      destruct x.
      auto.
    Qed.

    Global Instance SHOperator_equiv_Symmetric
           {i o: nat}:
      Symmetric (@SHOperator_equiv i o).
    Proof.
      intros x y.
      unfold SHOperator_equiv.
      auto.
    Qed.

    Global Instance SHOperator_equiv_Transitive
           {i o: nat}:
      Transitive (@SHOperator_equiv i o).
    Proof.
      intros x y z.
      unfold SHOperator_equiv.
      auto.
    Qed.

    Global Instance SHOperator_equiv_Equivalence
           {i o: nat}:
      Equivalence (@SHOperator_equiv i o).
    Proof.
      split.
      apply SHOperator_equiv_Reflexive.
      apply SHOperator_equiv_Symmetric.
      apply SHOperator_equiv_Transitive.
    Qed.

    Global Instance SHOperatorFamily_equiv_Reflexive
           {i o n: nat}:
      Reflexive (@SHOperatorFamily_equiv i o n).
    Proof.
      intros x.
      unfold SHOperatorFamily_equiv, pointwise_relation.
      auto.
    Qed.

    Global Instance SHOperatorFamily_equiv_Symmetric
           {i o n: nat}:
      Symmetric (@SHOperatorFamily_equiv i o n).
    Proof.
      intros x y.
      unfold SHOperatorFamily_equiv, pointwise_relation.
      intros H [j jc].
      specialize (H (mkFinNat jc)).
      auto.
    Qed.

    Global Instance SHOperatorFamily_equiv_Transitive
           {i o n: nat}:
      Transitive (@SHOperatorFamily_equiv i o n).
    Proof.
      intros x y z.
      unfold SHOperatorFamily_equiv, pointwise_relation.
      intros H H0 [j jc].
      specialize (H (mkFinNat jc)).
      specialize (H0 (mkFinNat jc)).
      auto.
    Qed.

    Global Instance SHOperatorFamily_equiv_Equivalence
           {i o n: nat}:
      Equivalence (@SHOperatorFamily_equiv i o n).
    Proof.
      split.
      apply SHOperatorFamily_equiv_Reflexive.
      apply SHOperatorFamily_equiv_Symmetric.
      apply SHOperatorFamily_equiv_Transitive.
    Qed.

    Lemma SM_op_SHOperator
          (i o : nat):
      forall (a:@SHOperator i o), Setoid_Morphism (op a).
    Proof.
      intros a.
      destruct a as [f pre_post f_proper].
      split; try typeclasses eauto.
    Qed.

    Global Instance SHOperator_op_proper {i o} :
      Proper ((=) ==> (=) ==> (=)) (@op i o).
    Proof.
      intros f f' Ef v v' Ev.
      destruct f as [fop op_pre_post op_proper].
      destruct f' as [fop' op_pre_post' op_proper'].
      simpl.
      apply Ef.
      apply Ev.
    Qed.

    Global Instance get_family_op_proper {i o n} :
      Proper ((=) ==>
                  (forall_relation (λ j : nat, pointwise_relation (j < n) (=))))
             (@get_family_op i o n).
    Proof.
      intros a a' Ea.
      unfold forall_relation, pointwise_relation.
      intros j jc.
      unfold get_family_op.
      apply SHOperator_op_proper.
      apply Ea.
    Qed.

    Global Instance SHOperator_op_arg_proper {i o} (a:@SHOperator i o):
      Proper ((=) ==> (=)) (op a).
    Proof.
      solve_proper.
    Qed.

    (*
TODO: remove
    Global Instance mkSHOperatorFamily_proper
           {i o n: nat}:
      Proper (forall_relation (λ i : nat, pointwise_relation (i < n) equiv) ==> equiv)
             (mkSHOperatorFamily i o n).
    Proof.
      intros f0 f1 Ef.
      unfold equiv, SHOperatorFamily_equiv, pointwise_relation.
      auto.
    Qed.
     *)

    Global Instance op_Vforall_P_proper {i o: nat}:
      Proper ( ((=) ==> iff) ==> (=) ==> iff) (@op_Vforall_P i o).
    Proof.
      intros P P' Ep x y E.
      unfold op_Vforall_P.
      split.
      -
        intros H x0.
        specialize (H x0).
        apply Vforall_nth_intro.
        intros i0 ip.
        apply Vforall_nth with (ip:=ip) in H.
        specialize (Ep (Vnth (op x x0) ip) (Vnth (op y x0) ip)).
        apply Ep.
        apply Vnth_arg_equiv.
        rewrite E.
        reflexivity.
        apply H.
      -
        intros H x0.
        specialize (H x0).
        apply Vforall_nth_intro.
        intros i0 ip.
        apply Vforall_nth with (ip:=ip) in H.
        specialize (Ep (Vnth (op x x0) ip) (Vnth (op y x0) ip)).
        apply Ep.
        apply Vnth_arg_equiv.
        rewrite E.
        reflexivity.
        apply H.
    Qed.

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
               (op: avector i -> avector o)
               `{HOP: HOperator i o op}
      := mkSHOperator i o (liftM_HOperator' op) (@liftM_HOperator'_proper i o op HOP)
                      (Full_set _) (Full_set _).

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
               {i o n}
               (op_family: @SHOperatorFamily i o n)
      :=
        Apply_Family' (get_family_op op_family).

    Global Instance Apply_Family_proper
           {i o n}:
      Proper ((=) ==> (=) ==> (=)) (@Apply_Family i o n).
    Proof.
      intros f f' Ef v v' Ev.
      unfold Apply_Family, Apply_Family'.
      vec_index_equiv j jc.
      rewrite 2!Vbuild_nth.
      unfold get_family_op, mkFinNat.
      simpl.
      unfold equiv, SHOperatorFamily_equiv, pointwise_relation, mkFinNat in Ef.
      rewrite <- Ev. clear Ev v'.
      specialize (Ef (mkFinNat jc)).
      apply SHOperator_op_proper.
      apply Ef.
      reflexivity.
    Qed.

    (* Do we need this in presence of Apply_Family_proper ? *)
    Global Instance Apply_Family_arg_proper
           {i o n}
           (op_family: @SHOperatorFamily i o n):
      Proper ((=) ==> (=)) (@Apply_Family i o n op_family).
    Proof.
      intros x y E.
      apply Apply_Family'_arg_proper.
      - intros k kc.
        apply get_family_op_proper.
        reflexivity.
      - apply E.
    Qed.

    (* Apply operator family to a vector produced a matrix which have at most one non-zero element per row.
       TODO: This could be expressed via set disjointness? *)
    Definition Apply_Family_Single_NonUnit_Per_Row
               {i o n}
               (op_family: @SHOperatorFamily i o n)
               (aunit: CarrierA)
      :=
        forall x, Vforall (Vunique (not ∘ (equiv aunit) ∘ (@evalWriter _ _ fm)))
                     (transpose
                        (Apply_Family op_family x)
                     ).

    (* States that given [P] holds for all elements of all outputs of this family *)
    Definition Apply_Family_Vforall_P
               {i o n}
               (P: Rtheta' fm -> Prop)
               (op_family: @SHOperatorFamily i o n)
      :=
        forall x (j:nat) (jc:j<n), Vforall P ((get_family_op op_family j jc) x).

    Definition IdOp
               {n: nat}
               (in_out_set:FinNatSet n)
      := mkSHOperator n n id _ in_out_set in_out_set.


    Definition eUnion'
               {o b:nat}
               (bc: b < o)
               (z: CarrierA)
               (x: svector fm 1):
      svector fm o
      := Vbuild (fun j jc =>
                   match Nat.eq_dec j b with
                   | in_left => Vhead x
                   | right fc => mkStruct z
                   end).

    Global Instance eUnion'_arg_proper
           {o b: nat}
           (bc: b < o)
           (z: CarrierA):
      Proper ((=) ==> (=)) (eUnion' bc z).
    Proof.
      intros x x' Ex.
      unfold eUnion'.
      vec_index_equiv j jp.
      rewrite 2!Vbuild_nth.
      break_if.
      rewrite Ex.
      reflexivity.
      reflexivity.
    Qed.

    Definition eUnion
               {o b:nat}
               (bc: b < o)
               (z: CarrierA)
      := mkSHOperator 1 o (eUnion' bc z) _
                      (Full_set _)
                      (FinNatSet.singleton b).

    Definition eT'
               {i b:nat}
               (bc: b < i)
               (v: svector fm i)
      := [Vnth v bc].

    Global Instance eT'_proper
           {i b:nat}
           (bc: b < i):
      Proper ((=) ==> (=)) (eT' bc).
    Proof.
      intros x y E.
      unfold eT'.
      apply Vcons_single_elim.
      apply Vnth_equiv; auto.
    Qed.

    Definition eT
               {i b:nat}
               (bc: b < i)
      := mkSHOperator i 1 (eT' bc) _
                      (FinNatSet.singleton b)
                      (Full_set _).

    Definition Gather'
               {i o: nat}
               (f: index_map o i)
               (x: svector fm i):
      svector fm o
      := Vbuild (VnthIndexMapped x f).

    Global Instance Gather'_proper
           {i o: nat}:
      Proper ((=) ==> (=) ==> (=)) (@Gather' i o).
    Proof.
      intros f g Efg x y Exy.
      unfold Gather', VnthIndexMapped.
      vec_index_equiv j jp.
      rewrite 2!Vbuild_nth.
      apply Vnth_equiv.
      apply Efg, jp.
      apply Exy.
    Qed.

    Definition Gather
               {i o: nat}
               (f: index_map o i)
      := mkSHOperator i o (Gather' f) _
                      (index_map_range_set f) (* Read pattern is governed by index function *)
                      (Full_set _) (* Gater always writes everywhere *).

    Definition GathH
               {i o}
               (base stride: nat)
               {domain_bound: ∀ x : nat, x < o → base + x * stride < i}
      :=
        Gather (h_index_map base stride
                            (range_bound:=domain_bound) (* since we swap domain and range, domain bound becomes range boud *)
               ).

    Definition Scatter'
               {i o: nat}
               (f: index_map i o)
               {f_inj: index_map_injective f}
               (idv: CarrierA)
               (x: svector fm i) : svector fm o
      :=
        let f' := build_inverse_index_map f in
        Vbuild (fun n np =>
                  match decide (in_range f n) with
                  | left r => Vnth x (inverse_index_f_spec f f' n r)
                  | right _ => mkStruct idv
                  end).

    Global Instance Scatter'_proper
           {i o: nat}
           (f: index_map i o)
           {f_inj: index_map_injective f}:
      Proper ((=) ==> (=) ==> (=)) (Scatter' f (f_inj:=f_inj)).
    Proof.
      intros z0 z1 Ez x y Exy.
      unfold Scatter'.
      vec_index_equiv j jp.
      simpl.
      rewrite 2!Vbuild_nth.
      break_match.
      - apply Vnth_arg_equiv, Exy.
      - rewrite Ez.
        reflexivity.
    Qed.

    Definition Scatter
               {i o: nat}
               (f: index_map i o)
               {f_inj: index_map_injective f}
               (idv: CarrierA)
      := mkSHOperator i o (Scatter' f (f_inj:=f_inj) idv) _
                      (Full_set _) (* Scatter always reads evertying *)
                      (index_map_range_set f) (* Write pattern is governed by index function *).

    Definition ScatH
               {i o}
               (base stride: nat)
               {range_bound: ∀ x : nat, x < i → base + x * stride < o}
               {snzord0: stride ≢ 0 \/ i < 2}
      :=
        Scatter (h_index_map base stride (range_bound:=range_bound))
                (f_inj := h_index_map_is_injective base stride (snzord0:=snzord0)).

    (* TODO: Enforce in_index_set op1 = out_index_set op2 *)
    Definition SHCompose
               {i1 o2 o3}
               (op1: @SHOperator o2 o3)
               (op2: @SHOperator i1 o2)
      : @SHOperator i1 o3 := mkSHOperator i1 o3 (compose (op op1) (op op2)) _
                                          (in_index_set op2)
                                          (out_index_set op1).

    Local Notation "g ⊚ f" := (@SHCompose _ _ _ g f) (at level 40, left associativity) : type_scope.

    Lemma SHCompose_val_equal_compose
          {i1 o2 o3}
          (op1: @SHOperator o2 o3)
          (op2: @SHOperator i1 o2)
      :
        (op op1) ∘ (op op2) = op (op1 ⊚ op2).
    Proof.
      destruct op1, op2.
      simpl in *.
      unfold equiv, ext_equiv.
      intros x y E.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance SHCompose_proper
           {i1 o2 o3}
      :
        Proper ((=) ==> (=) ==> (=)) (@SHCompose i1 o2 o3).
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


    Definition Constant_Family {i o n} (f: @SHOperator i o)
      : @SHOperatorFamily i o n := fun _ => f.

    (* Family composition *)
    Definition SHFamilyFamilyCompose
               {i1 o2 o3 n}
               (f: @SHOperatorFamily o2 o3 n)
               (g: @SHOperatorFamily i1 o2 n)
      : @SHOperatorFamily i1 o3 n
      := fun jf => f jf ⊚  g jf.

    Global Instance SHFamilyFamilyCompose_proper
           {i1 o2 o3 n: nat}
      :
        Proper ((=) ==> (=) ==> (=)) (@SHFamilyFamilyCompose i1 o2 o3 n).
    Proof.
      intros f f' Ef g g' Eg.
      unfold equiv, SHOperatorFamily_equiv, pointwise_relation.
      intros j jc.
      unfold SHFamilyFamilyCompose; simpl.

      apply SHCompose_proper.
      unfold equiv, ext_equiv, respectful in Ef.
      apply Ef.
      unfold equiv, ext_equiv, respectful in Eg.
      apply Eg.
    Qed.

    (* Family/operator composition *)
    Definition  SHOperatorFamilyCompose
                {i1 o2 o3 n}
                (f: @SHOperator o2 o3)
                (g: @SHOperatorFamily i1 o2 n)
      : @SHOperatorFamily i1 o3 n
      := fun jf => f  ⊚ g jf.

    Global Instance SHOperatorFamilyCompose_proper
           {i1 o2 o3 n: nat}
      :
        Proper ((=) ==> (=) ==> (=)) (@SHOperatorFamilyCompose i1 o2 o3 n).
    Proof.
      intros f f' Ef g g' Eg.
      unfold equiv, SHOperatorFamily_equiv, pointwise_relation.
      intros j jc.
      unfold SHFamilyFamilyCompose; simpl.

      apply SHCompose_proper.
      apply Ef.
      unfold equiv, ext_equiv, respectful in Eg.
      apply Eg.
    Qed.

    Definition  SHFamilyOperatorCompose
                {i1 o2 o3 n}
                (f: @SHOperatorFamily o2 o3 n)
                (g: @SHOperator i1 o2)
      : @SHOperatorFamily i1 o3 n
      := fun jf => f jf  ⊚ g.

    Global Instance SHFamilyOperatorCompose_proper
           {i1 o2 o3 n: nat}
      :
        Proper ((=) ==> (=) ==> (=)) (@SHFamilyOperatorCompose i1 o2 o3 n).
    Proof.
      intros f f' Ef g g' Eg.
      unfold equiv, SHOperatorFamily_equiv, pointwise_relation.
      intros j jc.
      unfold SHFamilyFamilyCompose; simpl.

      apply SHCompose_proper.
      unfold equiv, ext_equiv, respectful in Ef.
      apply Ef.
      apply Eg.
    Qed.


    (* Sigma-HCOL version of HPointwise. We could not just (liftM_Hoperator HPointwise) but we want to preserve structural flags. *)
    Definition SHPointwise'
               {n: nat}
               (f: { i | i<n} -> CarrierA -> CarrierA)
               (x: svector fm n): svector fm n
      := Vbuild (fun j jd => liftM (f (j ↾ jd)) (Vnth x jd)).

    Global Instance SHPointwise'_proper {n: nat}:
      Proper (((=) ==> (=) ==> (=)) ==> (=) ==> (=)) (@SHPointwise' n).
    Proof.
      intros f f' Ef x y Exy.
      unfold SHPointwise'.
      vec_index_equiv j jc.
      rewrite 2!Vbuild_nth.
      unfold_Rtheta_equiv.
      rewrite 2!evalWriter_Rtheta_liftM.
      f_equiv.
      apply Ef.
      f_equiv.
      apply evalWriter_proper.
      apply Vnth_arg_equiv.
      apply Exy.
    Qed.

    Definition SHPointwise
               {n: nat}
               (f: FinNat n -> CarrierA -> CarrierA)
               `{pF: !Proper ((=) ==> (=) ==> (=)) f}
      := mkSHOperator n n (SHPointwise' f) _ (Full_set _) (Full_set _).

    Definition SHBinOp'
               {o: nat}
               (f: FinNat o -> CarrierA -> CarrierA -> CarrierA)
               (v:svector fm (o+o)): svector fm o
      :=  match (vector2pair o v) with
          | (a,b) => Vbuild (fun i (ip:i<o) => liftM2 (f (mkFinNat ip)) (Vnth a ip) (Vnth b ip))
          end.

    Global Instance SHBinOp'_proper {o:nat}:
      Proper (((=) ==> (=) ==> (=) ==> (=)) ==> (=) ==> (=)) (@SHBinOp' o).
    Proof.
      intros f f' Ef x y E.
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
      apply Ef.
      reflexivity.
      - apply evalWriter_proper.
        apply Vnth_arg_equiv.
        rewrite E.
        reflexivity.
      - apply evalWriter_proper.
        apply Vnth_arg_equiv.
        rewrite E.
        reflexivity.
    Qed.

    (* Sparse Embedding is an operator family *)
    Definition SparseEmbedding
               {n i o ki ko}
               (* Kernel *)
               (kernel: @SHOperatorFamily ki ko n)
               (* Scatter index map *)
               (f: index_map_family ko o n)
               {f_inj : index_map_family_injective f}
               (idv: CarrierA)
               (* Gather index map *)
               (g: index_map_family ki i n)
      : @SHOperatorFamily i o n
      := fun jf => (Scatter (f jf)
                       (f_inj := index_map_family_member_injective f_inj jf) idv)
                ⊚ (kernel jf)
                ⊚ (Gather (g jf)).

    Lemma Scatter'_Unit_at_sparse
          {i o: nat}
          (f: index_map i o)
          {f_inj: index_map_injective f}
          (idv: CarrierA)
          (x: svector fm i)
          (k:nat)
          (kc:k<o):
      ¬ in_range f k -> (Is_ValX idv) (Vnth (Scatter' f (f_inj:=f_inj) idv x) kc).
    Proof.
      intros R.

      unfold Scatter'.
      rewrite Vbuild_nth.
      break_match.
      -
        congruence.
      -
        
        apply Is_ValX_mkStruct.
    Qed.

    Lemma Scatter'_NonUnit_in_range
          {i o: nat}
          (f: index_map i o)
          {f_inj: index_map_injective f}
          (idv: CarrierA)
          (x: svector fm i)
          (k:nat)
          (kc:k<o):
      idv ≠ evalWriter (Vnth (Scatter' f (f_inj:=f_inj) idv x) kc) -> in_range f k.
    Proof.
      intros H.

      unfold Scatter' in H.
      rewrite Vbuild_nth in H.
      break_match.
      -
        assumption.
      -
        contradict H.
        compute.
        reflexivity.
    Qed.

    Lemma SparseEmbedding_Apply_Family_Single_NonUnit_Per_Row
          {n i o ki ko}
          (* Kernel *)
          (kernel: @SHOperatorFamily ki ko n)
          (* Scatter index map *)
          (f: index_map_family ko o n)
          {f_inj : index_map_family_injective f}
          (idv: CarrierA)
          (* Gather index map *)
          (g: index_map_family ki i n):
      Apply_Family_Single_NonUnit_Per_Row
        (SparseEmbedding kernel f (f_inj:=f_inj) idv g) idv.
    Proof.
      unfold Apply_Family_Single_NonUnit_Per_Row.
      intros x.

      unfold Apply_Family, Apply_Family', SparseEmbedding, get_family_op, transpose, row, Vnth_aux.
      rewrite Vforall_Vbuild.
      intros k kc.
      rewrite Vmap_Vbuild.
      simpl.

      unfold Vunique.
      intros j0 jc0 j1 jc1.
      rewrite 2!Vbuild_nth.

      unfold compose.
      generalize
        (@op ki ko (kernel (mkFinNat jc0))
             (@Gather' i ki (g (mkFinNat jc0)) x)),
      (@op ki ko (kernel (mkFinNat jc1))
           (@Gather' i ki (g (mkFinNat jc1)) x)).
      intros x0 x1.

      clear kernel g i x ki. rename ko into i.

      intros [H0 H1].
      apply Scatter'_NonUnit_in_range, in_range_exists in H0; try assumption.
      apply Scatter'_NonUnit_in_range, in_range_exists in H1; try assumption.
      destruct H0 as [x [xc H0]].
      destruct H1 as [y [yc H1]].
      rewrite <- H1 in H0.
      specialize (f_inj j0 j1 jc0 jc1 x y xc yc H0).
      apply f_inj.
    Qed.


    Definition SHBinOp
               {o}
               (f: {n:nat|n<o} -> CarrierA -> CarrierA -> CarrierA)
               `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
      := mkSHOperator (o+o) o (SHBinOp' f) _ (Full_set _) (Full_set _).

  End FlagsMonoidGenericOperators.

  Section MUnion.

    Variable fm:Monoid RthetaFlags.

    (* An operator applied to a list of vectors (matrix) with uniform pre and post conditions *)
    Record MSHOperator
           {o n: nat}
      : Type
      := mkMSHOperator {
             mop: vector (svector fm o) n -> svector fm o ;
             mop_proper: Proper ((=) ==> (=)) mop
           }.

    Definition MUnion
               {o n}
               (dot: CarrierA->CarrierA->CarrierA)
               `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
               (initial: CarrierA)
      :=
        @mkMSHOperator o n (MUnion' fm dot initial) _.

  End MUnion.

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
             (* Functional parameters *)
             (dot: CarrierA -> CarrierA -> CarrierA)
             `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
             (initial: CarrierA)
             (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n)
    : @SHOperator Monoid_RthetaFlags i o
    :=
      mkSHOperator Monoid_RthetaFlags i o
                   (Diamond' dot initial (get_family_op Monoid_RthetaFlags op_family))
                   _
                   (family_in_index_set _ op_family)
                   (family_out_index_set _ op_family)
  . (* requires get_family_op_proper OR SHOperator_op_arg_proper *)

  Definition ISumUnion
             {i o n}
             (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n)
    : @SHOperator Monoid_RthetaFlags i o
    :=
      @IUnion i o n CarrierAplus _ zero op_family.

  (** IReduction does not have any constraints. Specifically no
  density or Monoid. It just extracts values from Monad and folds them
  row-wise. For example if for (+) id value is 0 and all structural
  values are structural zeros it will do row sums. It could not
  produce new errors, but should propagate errors from before.
   *)
  Definition IReduction
             {i o n}
             (dot: CarrierA -> CarrierA -> CarrierA)
             `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
             (initial: CarrierA)
             (op_family: @SHOperatorFamily Monoid_RthetaSafeFlags i o n)
    : @SHOperator Monoid_RthetaSafeFlags i o:=
    mkSHOperator Monoid_RthetaSafeFlags i o
                 (Diamond' dot initial (get_family_op Monoid_RthetaSafeFlags op_family))
                 _
                 (family_in_index_set _ op_family)
                 (family_out_index_set _ op_family) (* All scatters must be the same but we do not enforce it here. However if they are the same, the union will equal to any of them, so it is legit to use union here *)
  .

  (*

  In SPIRAL [ISumReduction] is what we call [ISumReduction] and strictly speaking there is no equivalent to [ISumReduction] as defined below. [ISumReduction] defined below is basically row-wise sum. To avoid confusion we will not use [ISumReduction] name for now.

  Definition ISumReduction
             {i o n}
             (op_family: @SHOperatorFamily Monoid_RthetaSafeFlags i o n)
    :=
      @IReduction i o n plus _ zero op_family.
   *)

  Global Instance IReduction_proper
         {i o n: nat}
         (dot: CarrierA -> CarrierA -> CarrierA)
         `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
    :
      Proper ((=) ==> (=) ==> (=)) (@IReduction i o n dot pdot).
  Proof.
    intros i0 i1 Ei x y E.
    unfold IReduction, equiv,  SHOperator_equiv.
    simpl.
    rewrite E, Ei.
    f_equiv; auto.
    f_equiv; auto.
  Qed.


End SigmaHCOL_Operators.

Lemma Is_Val_Scatter
      {m n: nat}
      (f: index_map m n)
      {f_inj: index_map_injective f}
      (idv: CarrierA)
      (x: rvector m)
      (j: nat) (jc : j < n):
  Is_Val (Vnth (Scatter' _ f (f_inj:=f_inj) idv x) jc) ->
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

Definition USparseEmbedding
           {n i o ki ko}
           (* Kernel *)
           (kernel: @SHOperatorFamily Monoid_RthetaFlags ki ko n)
           (f: index_map_family ko o n)
           {f_inj : index_map_family_injective f}
           (idv: CarrierA)
           (g: index_map_family ki i n)
  : @SHOperator Monoid_RthetaFlags i o
  :=
    ISumUnion
      (@SparseEmbedding Monoid_RthetaFlags
                        n i o ki ko
                        kernel
                        f f_inj idv
                        g).

Section OperatorProperies.

  Variable fm:Monoid RthetaFlags.
  Variable fml:@MonoidLaws RthetaFlags RthetaFlags_type fm.

  Local Notation "g ⊚ f" := (@SHCompose _ _ _ _ g f) (at level 40, left associativity) : type_scope.

  Lemma SHCompose_assoc
        {i1 o2 o3 o4}
        (h: @SHOperator fm o3 o4)
        (g: @SHOperator fm o2 o3)
        (f: @SHOperator fm i1 o2):
    h ⊚ g ⊚ f = h ⊚ (g ⊚ f).
  Proof.
    f_equiv.
  Qed.

  Lemma SHCompose_mid_assoc
        {i1 o1 o2 o3 o4}
        (h: @SHOperator fm o3 o4)
        (g: @SHOperator fm o2 o3)
        (f: @SHOperator fm o1 o2)
        (k: @SHOperator fm i1 o1):
    h ⊚ g ⊚ f ⊚ k = h ⊚ (g ⊚ f) ⊚ k.
  Proof.
    repeat f_equiv.
  Qed.

  Lemma SHFamilyOperatorCompose_SHFamilyOperatorCompose
        {i0 i1 o2 o3 n}
        (F: @SHOperatorFamily fm o2 o3 n)
        (op1: @SHOperator fm i1 o2)
        (op2: @SHOperator fm i0 i1)
    : SHFamilyOperatorCompose fm (SHFamilyOperatorCompose fm F op1) op2 = SHFamilyOperatorCompose fm F (SHCompose fm op1 op2).
  Proof.
    unfold SHFamilyOperatorCompose, SHCompose, compose.
    unfold equiv, SHOperatorFamily_equiv, pointwise_relation.
    intros [j jc].
    unfold equiv, SHOperator_equiv.
    simpl.
    unfold equiv, SHOperator_equiv, ext_equiv.
    intros x y E.
    repeat apply op_proper.
    apply E.
  Qed.

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
        (idv: CarrierA)
        (x: svector fm i)
        (n: nat) (ip : n < i):
    Vnth x ip ≡ VnthIndexMapped (Scatter' fm f (f_inj:=f_inj) idv x) f n ip.
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
        {f_inj : index_map_injective f}
        (idv: CarrierA):
    Vforall (fun p => (Vin p x) \/ (p ≡ mkStruct idv))
            (Scatter' fm f (f_inj:=f_inj) idv x).
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

  Lemma Scatter'_1_1
        (f : index_map 1 1)
        (f_inj : index_map_injective f)
        (idv : CarrierA)
        (h : Rtheta' fm):
    Scatter' fm f (f_inj:=f_inj) idv [h] ≡ [h].
  Proof.
    unfold Scatter'.
    rewrite Vbuild_1.
    break_match.
    -
      rewrite Vnth_1.
      reflexivity.
    -
      contradict n.
      apply in_range_exists.
      auto.
      exists 0.
      eexists; auto.
      destruct (eq_nat_dec (⟦ f ⟧ 0) 0); auto.
      apply not_eq in n.
      destruct n.
      +
        nat_lt_0_contradiction.
      +
        destruct f.
        simpl in *.
        clear f_inj.
        specialize (index_f_spec 0).
        omega.
  Qed.

  Lemma Scatter'_1_Sn
        {n: nat}
        (f: index_map 1 (S n))
        {f_inj: index_map_injective f}
        (idv: CarrierA)
        (x: svector fm 1):
    Scatter' fm f (f_inj:=f_inj) idv x
             ≡
             match Nat.eq_dec (⟦ f ⟧ 0) 0 with
             | in_left =>
               Vcons
                 (Vhead x)
                 (Vconst (mkStruct idv) n)
             | right fc =>
               let f' := (shrink_index_map_1_range f fc) in
               Vcons
                 (mkStruct idv)
                 (Scatter' fm f' (f_inj:= shrink_index_map_1_range_inj f fc f_inj) idv x)
             end.
  Proof.
    break_match.
    -
      (* considering [ ⟦ f ⟧ 0 ≡ 0 ] case *)
      apply vec_eq_elementwise.
      apply Vforall2_intro_nth.
      intros i ip.
      unfold Scatter'.
      rewrite Vbuild_nth.
      destruct (eq_nat_dec i 0).
      +
        (* eq at head *)
        break_match.
        *
          rewrite Vnth_1_Vhead.
          crush.
        *
          contradict n0.
          subst i.
          apply in_range_exists.
          auto.
          exists 0.
          eexists; auto.
      +
        (* eq remaining elements (tail) *)
        break_match.
        *
          destruct i as [|i]; try congruence.
          clear n0.
          rename i0 into H.
          assert(HH: ∃ x (xc:x<1), ⟦ f ⟧ x ≡ S i) by
              apply (@in_range_exists 1 (S n) (S i) f ip), H.
          destruct HH as [j [jc HH]].
          dep_destruct j; omega.
        *
          dep_destruct i; try omega.
          simpl.
          rewrite Vnth_const.
          reflexivity.
    -
      (* considering ⟦ f ⟧ 0 ≢ 0 case *)
      simpl.
      apply vec_eq_elementwise.
      apply Vforall2_intro_nth.
      intros i ip.
      unfold Scatter'.
      rewrite Vbuild_nth.
      destruct (eq_nat_dec i 0).
      +
        (* i=0 *)
        subst i.
        simpl.
        unfold decide.
        break_match; clear Heqd.
        *
          rename i into H.
          assert(HH: ∃ x (xc:x<1), ⟦ f ⟧ x ≡ 0).
          {
            apply in_range_exists.
            apply ip.
            apply H.
          }
          destruct HH as [j [jc HH]].
          dep_destruct j; omega.
        *
          reflexivity.
      +
        unfold decide.
        break_match; clear Heqd.
        *
          (* in_range f 1 *)
          destruct i as [|i]; try congruence.
          simpl.
          rewrite Vbuild_nth.
          rewrite Vnth_1_Vhead.
          break_match; clear Heqd.
          --
            rewrite Vnth_1_Vhead.
            reflexivity.
          --
            clear n1.
            contradict n2.
            unfold shrink_index_map_1_range.
            break_match; simpl in *.
            unfold compose.
            break_if; auto.
            destruct (index_f 0) eqn:Hi; auto.
            break_if; auto.
        *
          (* ¬ in_range f i *)
          destruct i as [|i]; try congruence.
          simpl.
          rewrite Vbuild_nth.
          break_match; clear Heqd.
          --
            clear n1.
            contradict n2.
            unfold shrink_index_map_1_range in i0.
            break_match; simpl in *.
            unfold compose in i0.
            break_if; auto.
            destruct (index_f 0) eqn:Hi; auto.
            break_if; auto.
          --
            reflexivity.
  Qed.

  Lemma SHPointwise'_nth
        {n: nat}
        (f: { i | i<n} -> CarrierA -> CarrierA)
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
        {j:nat} {jc:j<n}
        (v: svector fm n):
    Vnth (op _ (SHPointwise fm f) v) jc ≡ Monad.liftM (f (j ↾ jc)) (Vnth v jc).
  Proof.
    simpl.
    unfold SHPointwise'.
    rewrite Vbuild_nth.
    reflexivity.
  Qed.

  Lemma SHPointwise_equiv_lifted_HPointwise
        {n: nat}
        (f: { i | i<n} -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}:
    SHPointwise fm f =
    liftM_HOperator fm (@HPointwise n f).
  Proof.
    apply ext_equiv_applied_equiv.
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
        {f: FinNat o -> CarrierA -> CarrierA -> CarrierA}
        {v: svector fm (o+o)}
        {j:nat}
        {jc: j<o}
        {jc1:j<o+o}
        {jc2: (j+o)<o+o}
    :
      Vnth (@SHBinOp' fm o f v) jc ≡ liftM2 (f (mkFinNat jc)) (Vnth v jc1) (Vnth v jc2).
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

  Lemma ApplyFamily_SHOperatorFamilyCompose
        {i1 o2 o3 n}
        (f: @SHOperator fm o2 o3)
        (g: @SHOperatorFamily fm i1 o2 n)
        {x}
    : Apply_Family fm (SHOperatorFamilyCompose fm f g) x ≡
                   Vmap (op fm f) (Apply_Family fm g x).
  Proof.
    unfold Apply_Family, Apply_Family', SHOperatorFamilyCompose.
    rewrite Vmap_Vbuild.
    reflexivity.
  Qed.

End OperatorProperies.

Section StructuralProperies.

  Section FlagsMonoidGenericStructuralProperties.
    Variable fm:Monoid RthetaFlags.
    Variable fml:@MonoidLaws RthetaFlags RthetaFlags_type fm.

    Global Instance liftM_HOperator_Facts
           {i o}
           (hop: avector i -> avector o)
           `{HOP: HOperator i o hop}
      : SHOperator_Facts fm (liftM_HOperator fm hop).
    Proof.
      split.
      -
        apply Full_FinNatSet_dec.
      -
        apply Full_FinNatSet_dec.
      -
        intros x y H.

        simpl in *.
        assert (E: x=y).
        {
          vec_index_equiv j jc.
          apply H.
          constructor.
        }
        rewrite E.
        reflexivity.
      -
        intros v H j jc H0.
        simpl in *.
        unfold liftM_HOperator', compose, sparsify, densify.
        rewrite Vnth_map.
        apply Is_Val_mkValue.
      -
        intros v j jc H.
        contradict H.
        split.
      -
        intros v D j jc S.
        simpl in *.
        unfold liftM_HOperator', compose, sparsify, densify.
        rewrite Vnth_map.
        apply Not_Collision_mkValue.
      -
        intros v j jc H.
        unfold not in H.
        destruct H.
        split.
    Qed.

    Global Instance SHCompose_Facts
           {i1 o2 o3}
           (op1: @SHOperator fm o2 o3)
           (op2: @SHOperator fm i1 o2)
           `{fop1: SHOperator_Facts fm _ _ op1}
           `{fop2: SHOperator_Facts fm _ _ op2}
           (compat: Included _ (in_index_set fm op1) (out_index_set fm op2))
      : SHOperator_Facts fm (SHCompose fm op1 op2).
    Proof.
      split.
      -
        apply fop2.
      -
        apply fop1.
      - intros x y H.
        destruct op1, op2, fop1, fop2.
        simpl in *.
        unfold compose in *.
        apply in_as_domain0.
        intros j jc H0.
        apply Vnth_arg_equiv.
        apply in_as_domain1.
        intros j0 jc0 H1.
        apply H, H1.
      -
        intros v D j jc S.
        destruct op1, op2, fop1, fop2.
        simpl in *.
        unfold compose in *.
        apply out_as_range0.
        + intros.
          apply out_as_range1.
          apply D.
          apply compat.
          apply H.
        + apply S.
      -
        intros v j jc S.
        destruct op1, op2, fop1, fop2.
        simpl in *.
        unfold compose in *.
        apply no_vals_at_sparse0.
        apply S.
      -
        intros v D j jc S.
        destruct op1, op2, fop1, fop2.
        simpl in *.
        unfold compose in *.
        apply no_coll_range0.
        intros j0 jc0 H.
        apply no_coll_range1.
        intros j1 jc1 H0.
        apply D.
        apply H0.
        apply compat.
        apply H.
        apply S.
      -
        intros v j jc H.
        destruct op1, op2, fop1, fop2.
        simpl in *.
        unfold compose in *.
        apply no_coll_at_sparse0.
        apply H.
    Qed.

    Global Instance eUnion_Facts
           {o b:nat}
           (bc: b < o)
           (z: CarrierA):
      SHOperator_Facts fm (eUnion fm bc z).
    Proof.
      split.
      -
        apply Full_FinNatSet_dec.
      -
        apply Singleton_FinNatSet_dec.
      -
        intros x y H.
        simpl in *.
        vec_index_equiv j jc.
        unfold eUnion'.
        rewrite 2!Vbuild_nth.
        break_if.
        +
          apply vec_equiv_at_Full_set in H.
          rewrite H.
          reflexivity.
        +
          reflexivity.
      -
        intros v H j jc S.
        simpl in *.
        unfold eUnion'.
        rewrite Vbuild_nth.
        break_if.
        +
          rewrite Vhead_nth.
          apply H.
          unfold mkFinNat.
          apply Full_intro.
        +
          destruct S.
          simpl in n.
          congruence.
      -
        intros v j jc S.
        simpl in *.
        unfold eUnion'.
        rewrite Vbuild_nth.
        break_if.
        +
          subst b.
          contradict S.
          reflexivity.
        +
          apply Is_Struct_mkStruct.
      -
        intros v D j jc S.
        simpl.
        unfold eUnion'.
        rewrite Vbuild_nth.
        break_if.
        +
          rewrite Vhead_nth.
          apply D.
          unfold in_index_set.
          simpl.
          apply Full_intro.
        +
          apply Not_Collision_mkStruct.
      -
        intros v j jc H.
        simpl in *.
        unfold eUnion'.
        rewrite Vbuild_nth.
        break_if.
        +
          subst.
          unfold mkFinNat, FinNatSet.singleton in H.
          simpl in H.
          congruence.
        +
          apply Not_Collision_mkStruct.
    Qed.

    Global Instance eT_Facts
           {i b:nat}
           (bc: b < i)
      : SHOperator_Facts fm (eT fm bc).
    Proof.
      split.
      -
        apply Singleton_FinNatSet_dec.
      -
        apply Full_FinNatSet_dec.
      -
        intros x y H.
        simpl in *.
        apply Vcons_single_elim.
        apply H.
        unfold mkFinNat.
        reflexivity.
      -
        intros v H j jc S.
        simpl.
        break_match.
        +
          apply H.
          unfold in_index_set.
          unfold mkFinNat.
          reflexivity.
        +
          dep_destruct jc.
          lia.
      -
        intros v j jc S.
        contradict S.
        simpl.
        split.
      -
        intros v D j jc S.
        simpl.
        break_match.
        +
          apply D.
          unfold in_index_set.
          unfold mkFinNat.
          reflexivity.
        +
          dep_destruct jc.
          lia.
      -
        intros v j jc H.
        simpl in *.
        destruct H.
        split.
    Qed.

    Global Instance Gather_Facts
           {i o: nat}
           (f: index_map o i)
      : SHOperator_Facts fm (Gather fm f).
    Proof.
      split.
      -
        unfold in_index_set.
        unfold index_map_range_set.
        unfold FinNatSet_dec.
        intros x.
        apply Decidable_decision.
        apply in_range_dec.
      -
        apply Full_FinNatSet_dec.
      - intros x y H.
        simpl in *.
        vec_index_equiv j jc.
        rewrite 2!Gather'_spec.
        unfold VnthIndexMapped.
        apply H.
        unfold mkFinNat.
        apply index_map_range_set_id.
      -
        intros v H j jc S.
        simpl.
        rewrite Gather'_spec.
        unfold VnthIndexMapped.
        apply H.
        simpl.
        unfold mkFinNat.
        apply index_map_range_set_id.
      -
        intros v j jc S.
        contradict S.
        simpl.
        split.
      -
        intros v D j jc S.
        simpl.
        rewrite Gather'_spec.
        unfold VnthIndexMapped.
        apply D.
        simpl.
        unfold mkFinNat.
        apply index_map_range_set_id.
      -
        intros v j jc H.
        simpl in *.
        destruct H.
        split.
    Qed.

    Global Instance SHPointwise_Facts
           {n: nat}
           (f: { i | i<n} -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=)) f}:
      SHOperator_Facts fm (SHPointwise fm f).
    Proof.
      split.
      -
        simpl.
        apply Full_FinNatSet_dec.
      -
        simpl.
        apply Full_FinNatSet_dec.
      -
        intros x y H.
        simpl in *.
        assert (E: x=y).
        {
          vec_index_equiv j jc.
          apply H.
          constructor.
        }
        rewrite E.
        reflexivity.
      -
        intros v H j jc S.
        simpl in *.
        unfold SHPointwise'.
        rewrite Vbuild_nth.
        apply Is_Val_liftM.
        apply H, S.
      -
        intros v j jc S.
        contradict S.
        simpl.
        split.
      - intros v D j jc S.
        simpl in *.
        unfold SHPointwise'.
        rewrite Vbuild_nth.
        apply Not_Collision_liftM.
        apply D, S.
      - intros v D j jc S.
        simpl in *.
        destruct jc.
        split.
    Qed.

  End FlagsMonoidGenericStructuralProperties.

  Global Instance Scatter_Rtheta_Facts
         {i o: nat}
         (f: index_map i o)
         {f_inj: index_map_injective f}
         (idv: CarrierA)
    :
    SHOperator_Facts Monoid_RthetaFlags (Scatter Monoid_RthetaFlags f (f_inj:=f_inj) idv).
  Proof.
    split.
    -
      simpl.
      apply Full_FinNatSet_dec.
    -
      unfold out_index_set.
      unfold index_map_range_set.
      unfold FinNatSet_dec.
      intros x.
      apply Decidable_decision.
      apply in_range_dec.
    - intros x y H.
      simpl in *.
      assert (E: x=y).
      {
        vec_index_equiv j jc.
        apply H.
        constructor.
      }
      rewrite E.
      reflexivity.
    -
      intros v H j jc S.
      simpl.
      unfold Scatter' in *.
      rewrite Vbuild_nth.
      break_match.
      + simpl in *.
        generalize dependent (gen_inverse_index_f_spec f j i0); intros f_spec.
        apply H.
        constructor.
      +
        simpl in *.
        unfold index_map_range_set in S.
        simpl in *.
        congruence.
    -
      intros v j jc S.
      simpl in *.

      unfold index_map_range_set in S.
      unfold Scatter'.
      rewrite Vbuild_nth.
      break_match.
      *
        simpl in S.
        congruence.
      *
        apply Is_Struct_mkSZero.
    - intros v D j jc S.
      simpl.
      unfold Scatter' in *.
      rewrite Vbuild_nth.
      break_match.
      + simpl in *.
        generalize dependent (gen_inverse_index_f_spec f j i0); intros f_spec.
        apply D.
        constructor.
      +
        simpl in *.
        unfold index_map_range_set in S.
        simpl in *.
        congruence.
    -
      intros v D j jc S.
      simpl in *.
      unfold Scatter' in *.
      rewrite Vbuild_nth in S.
      break_match; crush.
  Qed.


  Global Instance SHBinOp_RthetaSafe_Facts
         {o}
         (f: FinNat o -> CarrierA -> CarrierA -> CarrierA)
         `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}:
    SHOperator_Facts Monoid_RthetaSafeFlags (SHBinOp _ f (o:=o)).
  Proof.
    split.
    -
      apply Full_FinNatSet_dec.
    -
      apply Full_FinNatSet_dec.
    -
      intros x y H.
      simpl in *.
      assert (E: x=y).
      {
        vec_index_equiv j jc.
        apply H.
        constructor.
      }
      rewrite E.
      reflexivity.
    -
      intros v H j jc S.
      simpl in *.
      assert(jc2: (j+o)<o+o) by omega.
      assert(jc1:j<o+o) by omega.
      rewrite (@SHBinOp'_nth Monoid_RthetaSafeFlags o f v j jc jc1 jc2).
      apply Is_Val_Safe_liftM2; (apply H; constructor).
    -
      intros v j jc S.
      contradict S.
      simpl.
      split.
    - intros v D j jc S.
      simpl in *.
      assert(jc2: (j+o)<o+o) by omega.
      assert(jc1:j<o+o) by omega.
      rewrite (@SHBinOp'_nth _  o f v j jc jc1 jc2).
      apply Not_Collision_Safe_liftM2; apply D; constructor.
    -
      intros v D j jc S.
      simpl in *.
      destruct jc.
      split.
  Qed.

  Lemma UnionFold_empty_Non_Collision
        (k : nat)
        (dot : CarrierA → CarrierA → CarrierA)
        (initial : CarrierA)
        (v : vector Rtheta k):
    Vforall Not_Collision v
    → Vforall (not ∘ Is_Val) v
    → Not_Collision (UnionFold Monoid_RthetaFlags dot initial v).
  Proof.
    intros Vnc Vempty.
    induction v.
    +
      unfold UnionFold.
      compute.
      tauto.
    +
      rewrite UnionFold_cons.
      apply UnionCollisionFree.
      * apply IHv.
        apply Vnc.
        apply Vempty.
      *
        apply Vnc.
      *
        clear IHv.
        intros [H H1].
        destruct Vempty as [Vh Vt].
        unfold compose, not in Vh.
        tauto.
  Qed.

  Lemma UnionFold_empty_Not_Val
        (k : nat)
        {dot : CarrierA → CarrierA → CarrierA}
        {initial : CarrierA}
        {v : vector Rtheta k}:
    Vforall Not_Collision v
    → Vforall (not ∘ Is_Val) v
    → ¬ Is_Val (UnionFold Monoid_RthetaFlags dot initial v).
  Proof.
    intros Vnc Vempty.
    induction v.
    +
      unfold UnionFold.
      compute.
      tauto.
    +
      rewrite UnionFold_cons.
      unfold not.
      intros H.
      apply ValUnionIsVal in H.
      destruct H as [H0| H1].
      *
        crush.
      *
        crush.
  Qed.

  Lemma UnionFold_VAllBytOne_Non_Collision
        (k : nat)
        (dot : CarrierA → CarrierA → CarrierA) (initial : CarrierA)
        (v : vector Rtheta k)
        (Vnc: Vforall Not_Collision v)
        (i : nat)
        (ic : i < k)
        (Vv: VAllButOne i ic (not ∘ Is_Val) v):
    Not_Collision (UnionFold Monoid_RthetaFlags dot initial v).
  Proof.
    dependent induction v.
    - inversion ic.
    -
      rewrite UnionFold_cons.
      apply UnionCollisionFree.
      +
        destruct i.
        *
          apply VAllButOne_0_Vforall in Vv.
          apply UnionFold_empty_Non_Collision.
          apply Vnc.
          apply Vv.
        *
          assert(¬ Is_Val h).
          {
            apply VallButOne_Sn_cons_not_head in Vv.
            apply Vv.
          }
          assert(ic' : i < n) by omega.
          assert(VAllButOne i ic' (not ∘ Is_Val) v).
          {
            eapply VallButOne_Sn_cases.
            eapply Vv.
          }
          eapply IHv.
          apply Vnc.
          eapply H0.
      +
        apply Vnc.
      +
        intros [H0 H1].
        destruct i.
        *
          clear H1. (* unused in this branch *)
          apply VAllButOne_0_Vforall in Vv.
          eapply UnionFold_empty_Not_Val with (dot:=dot) (initial:=initial) in Vv.
          auto.
          apply Vnc.
        *
          apply VallButOne_Sn_cons_not_head in Vv.
          tauto.
  Qed.

  Lemma UnionFold_Non_Collision
        (k : nat)
        (dot : CarrierA → CarrierA → CarrierA)
        (initial : CarrierA)
        (v : rvector  k)
        (Vnc: Vforall Not_Collision v)
        (Vu: Vunique Is_Val v)
    :
      Not_Collision (UnionFold Monoid_RthetaFlags dot initial v).
  Proof.
    apply Vunique_cases in Vu .
    destruct Vu as [V0 | V1].
    -
      (* Vforall case *)
      apply UnionFold_empty_Non_Collision.
      apply Vnc.
      apply V0.
    -
      (* VAllButOne case *)
      destruct V1 as [i [ic H]].
      apply UnionFold_VAllBytOne_Non_Collision with (ic:=ic).
      apply Vnc.
      apply H.
    -
      apply Is_Val_dec.
  Qed.

  Lemma UnionFold_Safe_Non_Collision
        (k : nat)
        (dot : CarrierA → CarrierA → CarrierA)
        (initial : CarrierA)
        (v : rsvector  k)
        (Vnc: Vforall Not_Collision v)
    :
      Not_Collision (UnionFold Monoid_RthetaSafeFlags dot initial v).
  Proof.
    dependent induction v.
    - unfold UnionFold.
      simpl.
      apply Not_Collision_mkStruct.
    -
      rewrite UnionFold_cons.
      apply UnionCollisionFree_Safe.
      +
        apply IHv.
        apply Vnc.
      +
        apply Vnc.
  Qed.

  Lemma Is_Val_In_outset
        (i o : nat)
        (v: rvector i)
        (j: nat) (jc : j < o)
        (O: SHOperator Monoid_RthetaFlags)
        (F: SHOperator_Facts Monoid_RthetaFlags O)
        (D: FinNatSet_dec (out_index_set Monoid_RthetaFlags O))
    :
      Is_Val (Vnth (op Monoid_RthetaFlags O v) jc) → out_index_set Monoid_RthetaFlags O (mkFinNat jc).
  Proof.
    intros V.
    destruct F as [_ _ _ _ S].
    specialize (S v j jc).
    unfold Is_Struct, compose in S.

    specialize (D (mkFinNat jc)).
    destruct D.
    -
      apply H.
    -
      specialize (S H).
      crush.
  Qed.

  Global Instance IUnion_Facts
         {i o k}
         (dot: CarrierA -> CarrierA -> CarrierA)
         `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
         (initial: CarrierA)
         (op_family: @SHOperatorFamily Monoid_RthetaFlags i o k)
         (op_family_facts: forall j (jc: j<k), SHOperator_Facts Monoid_RthetaFlags (op_family (mkFinNat jc)))
         (compat: forall m (mc:m<k) n (nc:n<k), m ≢ n -> Disjoint _
                                                                  (out_index_set _ (op_family (mkFinNat mc)))
                                                                  (out_index_set _ (op_family (mkFinNat nc)))
         )
    : SHOperator_Facts _ (IUnion dot initial op_family).
  Proof.
    split.
    -
      simpl in *.
      apply fmaily_in_index_set_dec.
      apply op_family_facts.
    -
      simpl in *.
      apply fmaily_out_index_set_dec.
      apply op_family_facts.
    -
      intros x y H.
      simpl in *.
      vec_index_equiv j jc.
      unfold Diamond'.
      unfold Apply_Family'.

      rewrite 2!AbsorbMUnion'Index_Vbuild.
      unfold UnionFold.

      f_equiv.
      apply Vforall2_intro_nth.
      intros i0 ip.
      rewrite 2!Vbuild_nth.
      apply Vnth_arg_equiv.
      clear j jc; rename i0 into j, ip into jc.

      apply op_family_facts.

      apply vec_equiv_at_subset with (h:=(family_in_index_set Monoid_RthetaFlags op_family)).
      apply family_in_set_includes_members.
      apply H.
    -
      intros v H j jc S.
      simpl in *.

      unfold Diamond'.
      unfold Apply_Family'.

      rewrite AbsorbMUnion'Index_Vbuild.
      apply Is_Val_UnionFold.

      apply family_out_set_implies_members in S.
      destruct S as [x X].
      destruct X as [xc X].

      apply Vexists_Vbuild.
      eexists.
      eexists.

      apply out_as_range.
      + apply op_family_facts.
      + intros j0 jc0 H0.
        apply H.
        eapply family_in_set_includes_members.
        unfold In.
        apply H0.
      +
        apply X.
    -
      intros v j jc S.
      simpl in *.

      unfold IUnion, Diamond', Apply_Family'.
      rewrite AbsorbMUnion'Index_Vbuild.
      apply not_Is_Val_Is_Struct.
      unfold Is_Struct, not.
      intros G.
      apply Is_Val_UnionFold in G.
      apply Vexists_Vbuild in G.
      destruct G as [t [tc G]].
      (* G and S contradict *)
      assert(N: ¬ out_index_set Monoid_RthetaFlags
                  (op_family (mkFinNat tc)) (mkFinNat jc)).
      {
        contradict S.
        apply family_out_set_includes_members in S.
        auto.
      }
      apply no_vals_at_sparse with (v:=v) in N.
      unfold Is_Struct, compose, not in N.

      unfold get_family_op in G.
      auto.

      apply op_family_facts.
    -
      (* no_coll_range *)
      intros v D j jc S.
      simpl in *.
      unfold Diamond', Apply_Family'.

      rewrite AbsorbMUnion'Index_Vbuild.
      apply UnionFold_Non_Collision.
      +
        (* no collisions on j-th row accross all families *)
        apply family_out_set_implies_members in S.
        destruct S as [d [dc S]].

        apply Vforall_Vbuild.
        intros t tc.

        destruct (eq_nat_dec d t).
        *
          (* family member in out set *)
          apply no_coll_range.
          --
            auto.
          --
            intros m mc H.
            eapply D, family_in_set_includes_members, H.
          --
            subst.
            replace tc with dc by apply le_unique.
            apply S.
        *
          (* family member in out set *)
          apply no_coll_at_sparse.
          --
            auto.
          --
            specialize (compat d dc t tc n).
            inversion compat as [C]; clear compat.
            specialize (C (mkFinNat jc)). unfold In in C.
            contradict C.
            split; assumption.
      +
        intros m mc n nc [M N].
        rewrite Vbuild_nth in M.
        rewrite Vbuild_nth in N.

        destruct (eq_nat_dec m n) as [E | NE].
        apply E.

        specialize (compat m mc n nc NE).
        inversion compat as [C].
        specialize (C (mkFinNat jc)).

        unfold get_family_op in M.
        unfold get_family_op in N.

        apply Is_Val_In_outset in M; try apply op_family_facts.
        apply Is_Val_In_outset in N; try apply op_family_facts.

        contradict C.

        unfold In.
        apply Intersection_intro.
        apply M.
        apply N.
    -
      (* no_coll_at_sparse *)
      intros v j jc S.
      simpl in *.
      unfold Diamond', Apply_Family'.

      rewrite AbsorbMUnion'Index_Vbuild.
      apply UnionFold_Non_Collision.

      +
        (* no collisions on j-th row accross all families *)
        assert(forall  (t : nat) (tc : t < k),
                  not (out_index_set Monoid_RthetaFlags (op_family (mkFinNat tc))
                                     (mkFinNat jc))).
        {
          intros t tc.
          contradict S.
          apply family_out_set_implies_members.
          exists t, tc.
          apply S.
        }

        apply Vforall_Vbuild.
        intros t tc.

        unfold get_family_op.
        apply no_coll_at_sparse.
        apply op_family_facts.
        apply H.
      +
        intros m mc n _ [M _].
        rewrite Vbuild_nth in M.
        unfold get_family_op in M.
        apply Is_Val_In_outset in M; try apply op_family_facts.
        contradict S.
        apply family_out_set_implies_members.
        exists m, mc.
        apply M.
  Qed.

  Global Instance IReduction_Facts
         {i o k}
         (dot: CarrierA -> CarrierA -> CarrierA)
         `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
         (initial: CarrierA)
         (op_family: @SHOperatorFamily Monoid_RthetaSafeFlags i o k)
         (op_family_facts: forall j (jc:j<k), SHOperator_Facts Monoid_RthetaSafeFlags (op_family (mkFinNat jc)))
    : SHOperator_Facts _ (IReduction dot initial op_family).
  Proof.
    split.
    -
      simpl in *.
      apply fmaily_in_index_set_dec.
      apply op_family_facts.
    -
      simpl in *.
      apply fmaily_out_index_set_dec.
      apply op_family_facts.
    -
      intros x y H.
      simpl in *.
      vec_index_equiv j jc.
      unfold Diamond'.
      unfold Apply_Family'.

      rewrite 2!AbsorbMUnion'Index_Vbuild.
      unfold UnionFold.

      f_equiv.
      apply Vforall2_intro_nth.
      intros i0 ip.
      rewrite 2!Vbuild_nth.
      apply Vnth_arg_equiv.
      clear j jc; rename i0 into j, ip into jc.

      apply op_family_facts.

      apply vec_equiv_at_subset with (h:=(family_in_index_set Monoid_RthetaSafeFlags op_family)).
      apply family_in_set_includes_members.
      apply H.
    -
      intros v D j jc S.
      simpl in *.

      unfold Diamond'.
      unfold Apply_Family'.

      rewrite AbsorbMUnion'Index_Vbuild.
      apply Is_Val_UnionFold_Safe.

      apply family_out_set_implies_members in S.
      destruct S as [x X].
      destruct X as [xc X].

      apply Vexists_Vbuild.
      eexists.
      eexists.

      apply out_as_range.
      + apply op_family_facts.
      + intros j0 jc0 H.
        apply D.
        eapply family_in_set_includes_members.
        unfold In.
        apply H.
      +
        apply X.
    -
      intros v j jc S.
      simpl in *.

      unfold IUnion, Diamond', Apply_Family'.
      rewrite AbsorbMUnion'Index_Vbuild.
      apply not_Is_Val_Is_Struct.
      unfold Is_Struct, not.
      intros G.

      apply Is_Val_UnionFold_Safe in G.
      apply Vexists_Vbuild in G.
      destruct G as [t [tc G]].

      (* G and S contradict *)
      assert(N: ¬ out_index_set Monoid_RthetaSafeFlags
                  (op_family (mkFinNat tc)) (mkFinNat jc)).
      {
        contradict S.
        apply family_out_set_includes_members in S.
        auto.
      }
      apply no_vals_at_sparse with (v:=v) in N.
      unfold Is_Struct, compose, not in N.

      unfold get_family_op in G.
      auto.

      apply op_family_facts.
    -
      (* no_coll_range *)
      intros v D j jc S.
      simpl in *.
      unfold Diamond', Apply_Family'.

      rewrite AbsorbMUnion'Index_Vbuild.
      apply UnionFold_Safe_Non_Collision.

      (* no collisions on j-th row accross all families *)
      apply Vforall_Vbuild.
      intros t tc.

      destruct (op_family_facts t tc).
      specialize (out_dec0 (mkFinNat jc)).
      destruct out_dec0 as [O | NO].

      + apply no_coll_range.
        * auto.
        * intros m mc H.
          eapply D, family_in_set_includes_members, H.
        * auto.
      +
        apply no_coll_at_sparse; auto.
    -
      (* no_coll_at_sparse *)
      intros v j jc S.
      simpl in *.
      unfold Diamond', Apply_Family'.

      rewrite AbsorbMUnion'Index_Vbuild.
      apply UnionFold_Safe_Non_Collision.
      +
        (* no collisions on j-th row accross all families *)
        assert(forall  (t : nat) (tc : t < k),
                  not (out_index_set Monoid_RthetaSafeFlags (op_family (mkFinNat tc))
                                     (mkFinNat jc))).
        {
          intros t tc.
          contradict S.
          apply family_out_set_implies_members.
          exists t, tc.
          apply S.
        }

        apply Vforall_Vbuild.
        intros t tc.

        unfold get_family_op.
        apply no_coll_at_sparse.
        apply op_family_facts.
        apply H.
  Qed.

End StructuralProperies.

