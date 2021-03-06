(* Template HCOL. HCOL meta-operators *)

Require Import Helix.Util.VecUtil.
Require Import Helix.Util.VecSetoid.
Require Import Helix.Util.FinNat.
Require Import Helix.Util.Misc.
Require Import Helix.Util.WriterMonadNoT.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.SigmaHCOL.Rtheta.
Require Import Helix.SigmaHCOL.SVector.
Require Import Helix.SigmaHCOL.IndexFunctions.
Require Import Helix.SigmaHCOL.SigmaHCOL.
Require Import Helix.Util.FinNatSet.

Require Import Coq.Arith.Arith.
Require Import Coq.Program.Program.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relations.

Require Import Helix.Tactics.HelixTactics.
Require Import Coq.Logic.FunctionalExtensionality.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.theory.rings.
Require Import MathClasses.theory.setoids.

(* ExtLib *)
Import ExtLib.Structures.Monoid.

Import Monoid.

Section WithCarrierA.

  Context `{CAPROPS: CarrierProperties}.

  Section RthetaSafetyCast.

    Definition SafeCast'
               {o i}
               (f: rsvector i -> rsvector o):
      rvector i -> rvector o
      := (rsvector2rvector o) ∘ f ∘ (rvector2rsvector i).

    Global Instance SafeCast'_proper (i o : nat):
      Proper (equiv ==> equiv ==> equiv) (@SafeCast' i o).
    Proof.
      intros f f' Ef v v' Ev.
      unfold SafeCast', compose, rsvector2rvector, rvector2rsvector.
      f_equiv.
      vec_index_equiv j jc.
      apply Vnth_arg_equiv.
      unfold equiv, ext_equiv, respectful in Ef.
      apply Ef.
      f_equiv.
      apply Ev.
    Qed.

    Program Definition SafeCast
            {svalue: CarrierA}
            {i o}
            (f: @SHOperator CADEFS Monoid_RthetaSafeFlags i o svalue)
      : @SHOperator CADEFS Monoid_RthetaFlags i o svalue
      :=
        mkSHOperator Monoid_RthetaFlags i o svalue
                     (SafeCast' (op Monoid_RthetaSafeFlags f))
                     _
                     (in_index_set _ f)
                     (out_index_set _ f)
                     _ .
    Next Obligation.
      unfold SafeCast', compose, rsvector2rvector, rvector2rsvector in *.
      rewrite Vnth_map.
      apply svalue_at_sparse; assumption.
    Qed.

    Global Instance SafeCast_proper
           {svalue: CarrierA}
           (i o:nat):
      Proper (equiv ==> equiv) (@SafeCast svalue i o).
    Proof.
      intros f f' Ev.
      unfold SafeCast.
      unfold equiv, SHOperator_equiv.
      simpl.

      destruct f, f'.
      unfold equiv, SHOperator_equiv in Ev.
      simpl in *.

      apply SafeCast'_proper.
      apply Ev.
    Qed.

    Definition SafeFamilyCast
               {svalue: CarrierA}
               {i o n}
               (f: @SHOperatorFamily CADEFS Monoid_RthetaSafeFlags i o n svalue)
      : @SHOperatorFamily CADEFS Monoid_RthetaFlags i o n svalue
      := fun jf => SafeCast (f jf).

    Global Instance SafeFamilyCast_proper
           {svalue: CarrierA}
           (i o n: nat):
      Proper (equiv ==> equiv) (@SafeFamilyCast svalue i o n).
    Proof.
      intros f f' Ev.
      unfold SafeFamilyCast.
      unfold equiv, SHOperatorFamily_equiv, pointwise_relation, mkFinNat.
      intros j jc.
      apply SafeCast'_proper.
      apply SHOperator_op_proper.
      apply Ev.
    Qed.

    Definition UnSafeCast'
               {o i}
               (f: rvector i -> rvector o):
      rsvector i -> rsvector o
      := (rvector2rsvector o) ∘ f ∘ (rsvector2rvector i).


    Global Instance UnSafeCast'_proper (i o : nat):
      Proper (equiv ==> equiv ==> equiv) (@UnSafeCast' i o).
    Proof.
      intros f f' Ef v v' Ev.
      unfold UnSafeCast', compose, rsvector2rvector, rvector2rsvector.
      f_equiv.
      vec_index_equiv j jc.
      apply Vnth_arg_equiv.
      unfold equiv, ext_equiv, respectful in Ef.
      apply Ef.
      f_equiv.
      apply Ev.
    Qed.

    Program Definition UnSafeCast
            {svalue: CarrierA}
            {i o: nat}
            (f: @SHOperator CADEFS Monoid_RthetaFlags i o svalue)
      : @SHOperator CADEFS Monoid_RthetaSafeFlags i o svalue
      :=
        mkSHOperator Monoid_RthetaSafeFlags i o svalue
                     (UnSafeCast' (op Monoid_RthetaFlags f))
                     _
                     (in_index_set _ f)
                     (out_index_set _ f)
                     _ .
    Next Obligation.
      unfold UnSafeCast', compose, rsvector2rvector, rvector2rsvector in *.
      rewrite Vnth_map.
      apply svalue_at_sparse; assumption.
    Qed.

    Global Instance UnSafeCast_proper
           {svalue: CarrierA}
           (i o:nat):
      Proper (equiv ==> equiv) (@UnSafeCast svalue i o).
    Proof.
      intros f f' Ev.
      unfold UnSafeCast.
      unfold equiv, SHOperator_equiv.
      simpl.

      destruct f, f'.
      unfold equiv, SHOperator_equiv in Ev.
      simpl in *.

      apply UnSafeCast'_proper.
      apply Ev.
    Qed.


    Definition UnSafeFamilyCast
               {svalue: CarrierA}
               {i o n}
               (f: @SHOperatorFamily CADEFS Monoid_RthetaFlags i o n svalue)
      : @SHOperatorFamily CADEFS Monoid_RthetaSafeFlags i o n svalue
      := fun jf => UnSafeCast (f jf).


    Global Instance UnSafeFamilyCast_proper
           {svalue: CarrierA}
           (i o n: nat):
      Proper (equiv ==> equiv) (@UnSafeFamilyCast svalue i o n).
    Proof.
      intros f f' Ev.
      unfold UnSafeFamilyCast.
      unfold equiv, SHOperatorFamily_equiv, pointwise_relation.
      intros j jc.
      apply UnSafeCast'_proper.
      apply SHOperator_op_proper.
      apply Ev.
    Qed.

  End RthetaSafetyCast.



  (* For now we are not define special type for TSigmahcolOperators, like we did for SHOperator. Currently we have only 2 of these: SHCompose and Apply2Union. We will generalize in future, if needed *)
  Section TSigmaHCOLOperators.

    Variable fm:Monoid RthetaFlags.

    Section Apply2Union.

      Import ExtLib.Data.Fun.
      Import ExtLib.Structures.Applicative.

      (* For some reason this instance is local. See
     https://github.com/coq-community/coq-ext-lib/issues/88 *)
      Local Existing Instance Applicative_Fun.


      (* Per Vadim's discussion with Franz on 2015-12-14, ISumUnion is
  just Union of two vectors, produced by application of two operators
  to the input.

  This definition is using applicative reader functor.  *)
      Definition Apply2Union' {i o} (dot: CarrierA -> CarrierA -> CarrierA):
        (svector fm i -> svector fm o) -> (svector fm i -> svector fm o) ->
        svector fm i -> svector fm o
        :=
          liftA2 (Vec2Union fm dot).
    End Apply2Union.

    Global Instance Apply2Union'_proper {i o}
      : Proper ( ((=) ==> (=) ==> (=)) ==>
                                       (=) ==> (=) ==> (=) ==> (=)) (Apply2Union' (i:=i) (o:=o)).
    Proof.
      intros dot dot' Edot f f' Ef g g' Eg x y Ex.
      unfold Apply2Union'; simpl. (* cbn. over-eager *)
      unfold Vec2Union.
      vec_index_equiv j jp.
      rewrite 2!Vnth_map2.
      f_equiv.
      apply Edot.
      - apply Vnth_arg_equiv; auto.
      - apply Vnth_arg_equiv; auto.
    Qed.

    Global Instance Apply2Union'_arg_proper {i o}
           (op1: svector fm i -> svector fm o)
           `{op1_proper: !Proper ((=) ==> (=)) op1}
           (op2: svector fm i -> svector fm o)
           `{op2_proper: !Proper ((=) ==> (=)) op2}
           (dot: CarrierA -> CarrierA -> CarrierA)
           `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
      : Proper ((=) ==> (=)) (Apply2Union' (i:=i) (o:=o) dot op1 op2).
    Proof.
      partial_application_tactic. instantiate (1 := equiv).
      partial_application_tactic. instantiate (1 := equiv).
      apply Apply2Union'_proper.
      - apply dot_mor.
      - apply op1_proper.
      - apply op2_proper.
    Qed.

    (* Probably "SUM" shoud be avoided in the name not to confuse
     with [ISUmUnion]. *)
    Program Definition Apply2Union {i o}
            {svalue: CarrierA}
            (dot: CarrierA -> CarrierA -> CarrierA)
            `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
            `{scompat: @BFixpoint CADEFS svalue dot}
            (op1 op2: @SHOperator CADEFS fm i o svalue)
      : @SHOperator CADEFS fm i o svalue
      :=
        mkSHOperator fm i o svalue (Apply2Union' dot (op fm op1) (op fm op2))
                     (@Apply2Union'_arg_proper i o
                                               (op fm op1) (op_proper fm op1)
                                               (op fm op2) (op_proper fm op2)
                                               dot dot_mor)
                     (Ensembles.Union _ (in_index_set _ op1) (in_index_set _ op2))
                     (Ensembles.Union _ (out_index_set _ op1) (out_index_set _ op2))
                     _ .
    Next Obligation.
      rename H into S.
      unfold Apply2Union', Vec2Union.
      simpl.
      rewrite Vnth_map2.
      rewrite evalWriterUnion.
      unfold Apply2Union', Vec2Union in S.
      simpl in *.
      assert(S1: ¬ (out_index_set fm op1 (mkFinNat jc))).
      {
        intros H.
        contradict S.
        apply Union_introl, H.
      }
      assert(S2: ¬ (out_index_set fm op2 (mkFinNat jc))).
      {
        intros H.
        contradict S.
        apply Union_intror, H.
      }
      clear S.

      apply svalue_at_sparse with (v0:=v) in S1; eauto.
      rewrite S1.
      apply svalue_at_sparse with (v0:=v) in S2; eauto.
      rewrite S2.
      apply scompat.
    Qed.

    Global Instance Apply2Union_proper
           {svalue: CarrierA}
           {i o: nat}
           (dot: CarrierA -> CarrierA -> CarrierA)
           `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
           `{scompat: @BFixpoint CADEFS svalue dot}
      : Proper ((=) ==> (=) ==> (=))
               (@Apply2Union i o svalue dot dot_mor _).
    Proof.
      intros x x' Ex y y' Ey.
      unfold Apply2Union.
      unfold equiv, SHOperator_equiv in *.
      destruct x, y, x', y'.
      simpl in *.
      apply Apply2Union'_proper; assumption.
    Qed.

  End TSigmaHCOLOperators.

  Section TSigmaHCOLOperators_StructuralProperties.

    Global Instance SafeCast_Facts
           {i o: nat}
           {svalue: CarrierA}
           (xop: @SHOperator CADEFS Monoid_RthetaSafeFlags i o svalue)
           `{fop: @SHOperator_Facts CADEFS Monoid_RthetaSafeFlags _ _ _ xop}
    :
      SHOperator_Facts Monoid_RthetaFlags (SafeCast xop).
    Proof.
      split.
      - apply fop.
      - apply fop.
      - intros x y H.
        simpl.
        unfold SafeCast, SafeCast', compose, rsvector2rvector, rvector2rsvector in *.
        f_equiv.
        apply fop.
        simpl in *.

        unfold vec_equiv_at_set.
        intros j jc S.
        specialize (H j jc S).
        rewrite 2!Vnth_map.
        f_equiv.
        apply H.
      -
        intros v H j jc S.
        unfold SafeCast, SafeCast', compose, rsvector2rvector, rvector2rsvector in *.
        simpl in *.

        rewrite Vnth_map, <- Is_Val_RStheta2Rtheta.
        apply out_as_range; try assumption.
        intros t tc I.

        rewrite Vnth_map, <- Is_Val_Rtheta2RStheta.
        apply H, I.
      -
        intros v j jc S.
        unfold SafeCast, SafeCast', compose, rsvector2rvector, rvector2rsvector in *.
        simpl in *.

        rewrite Vnth_map, <- Is_Struct_RStheta2Rtheta.
        apply no_vals_at_sparse; assumption.
      -
        intros v H j jc S.
        unfold SafeCast, SafeCast', compose, rsvector2rvector, rvector2rsvector in *.
        simpl in *.

        rewrite Vnth_map, <- Not_Collision_RStheta2Rtheta.
        apply no_coll_range; try assumption.
        intros t tc I.

        rewrite Vnth_map, <- Not_Collision_Rtheta2RStheta.
        apply H, I.
      -
        intros v j jc S.
        unfold SafeCast, SafeCast', compose, rsvector2rvector, rvector2rsvector in *.
        simpl in *.

        rewrite Vnth_map, <- Not_Collision_RStheta2Rtheta.
        apply no_coll_at_sparse; assumption.
    Qed.

    Global Instance UnSafeCast_Facts
           {svalue: CarrierA}
           {i o}
           (xop: @SHOperator CADEFS Monoid_RthetaFlags i o svalue)
           `{fop: @SHOperator_Facts CADEFS Monoid_RthetaFlags _ _ _ xop}
      :
        SHOperator_Facts Monoid_RthetaSafeFlags (UnSafeCast xop).
    Proof.
      split.
      - apply fop.
      - apply fop.
      - intros x y H.
        simpl.
        unfold UnSafeCast, UnSafeCast', compose, rsvector2rvector, rvector2rsvector in *.
        f_equiv.
        apply fop.
        simpl in *.

        unfold vec_equiv_at_set.
        intros j jc S.
        specialize (H j jc S).
        rewrite 2!Vnth_map.
        f_equiv.
        apply H.
      -
        intros v H j jc S.
        unfold UnSafeCast, UnSafeCast', compose, rsvector2rvector, rvector2rsvector in *.
        simpl in *.

        rewrite Vnth_map. rewrite <- Is_Val_Rtheta2RStheta.
        apply out_as_range; try assumption.
        intros t tc I.

        rewrite Vnth_map, <- Is_Val_RStheta2Rtheta.
        apply H, I.
      -
        intros v j jc S.
        unfold UnSafeCast, UnSafeCast', compose, rsvector2rvector, rvector2rsvector in *.
        simpl in *.

        rewrite Vnth_map, <- Is_Struct_Rtheta2RStheta.
        apply no_vals_at_sparse; assumption.
      -
        intros v H j jc S.
        unfold UnSafeCast, UnSafeCast', compose, rsvector2rvector, rvector2rsvector in *.
        simpl in *.

        rewrite Vnth_map, <- Not_Collision_Rtheta2RStheta.
        apply no_coll_range; try assumption.
        intros t tc I.

        rewrite Vnth_map, <- Not_Collision_RStheta2Rtheta.
        apply H, I.
      -
        intros v j jc S.
        unfold UnSafeCast, UnSafeCast', compose, rsvector2rvector, rvector2rsvector in *.
        simpl in *.

        rewrite Vnth_map, <- Not_Collision_Rtheta2RStheta.
        apply no_coll_at_sparse; assumption.
    Qed.

    Global Instance Apply2Union_Facts
           {i o: nat}
           {svalue: CarrierA}
           (dot: CarrierA -> CarrierA -> CarrierA)
           `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
           (op1 op2: @SHOperator CADEFS Monoid_RthetaFlags i o svalue)
           `{fop1: @SHOperator_Facts CADEFS Monoid_RthetaFlags _ _ _ op1}
           `{fop2: @SHOperator_Facts CADEFS Monoid_RthetaFlags _ _ _ op2}
           (compat: Disjoint _
                             (out_index_set _ op1)
                             (out_index_set _ op2)
           )
           `{scompat: @BFixpoint CADEFS svalue dot}
      : SHOperator_Facts Monoid_RthetaFlags (Apply2Union Monoid_RthetaFlags dot op1 op2).
    Proof.
      split.
      -
        apply Union_FinNatSet_dec.
        apply fop1.
        apply fop2.
      -
        apply Union_FinNatSet_dec.
        apply fop1.
        apply fop2.
      - intros x y H.
        destruct op1, op2, fop1, fop2.
        simpl in *.
        unfold Apply2Union', Vec2Union in *.
        simpl. (* cbn. over-eager *)
        vec_index_equiv j jc.
        rewrite 2!Vnth_map2.
        f_equiv.
        + apply dot_mor.
        +
          apply Vnth_arg_equiv.
          apply in_as_domain.
          apply vec_equiv_at_Union in H.
          apply H.
        +
          apply Vnth_arg_equiv.
          apply in_as_domain0.
          apply vec_equiv_at_Union in H.
          apply H.
      - intros v D j jc S.
        simpl in *.
        unfold Apply2Union', Vec2Union in *.
        simpl.
        rewrite Vnth_map2.
        apply ValUnionIsVal.
        destruct op1, op2, fop1, fop2.
        simpl in *.
        dep_destruct S.
        + left.
          apply out_as_range.
          intros j0 jc0 H0.
          apply D.
          left.
          apply H0.
          apply i0.
        + right.
          apply out_as_range0.
          intros j0 jc0 H0.
          apply D.
          right.
          apply H0.
          apply i0.
      -
        intros v j jc S.
        unfold Apply2Union, Apply2Union', Vec2Union.
        simpl.
        rewrite Vnth_map2.
        apply StructUnionIsStruct.

        unfold Is_Struct, IsStruct, compose.
        split.
        +
          apply fop1.
          unfold Apply2Union, Apply2Union', Vec2Union in S.
          simpl in *.
          contradict S.
          apply Union_introl.
          apply S.
        +
          apply fop2.
          unfold Apply2Union, Apply2Union', Vec2Union in S.
          simpl in *.
          contradict S.
          apply Union_intror.
          apply S.
      -
        (* no_coll_range *)
        intros v D j jc S.
        unfold Apply2Union, Apply2Union', Vec2Union in *.
        simpl in *.
        rewrite Vnth_map2.
        apply UnionCollisionFree.
        +
          destruct fop1.
          destruct (out_dec (mkFinNat jc)).
          * apply no_coll_range.
            intros t tc I.
            specialize (D t tc).
            apply D.
            apply Union_introl.
            apply I.
            apply H.
          * apply no_coll_at_sparse.
            apply H.
        +
          destruct fop2.
          destruct (out_dec (mkFinNat jc)).
          * apply no_coll_range.
            intros t tc I.
            specialize (D t tc).
            apply D.
            apply Union_intror.
            apply I.
            apply H.
          * apply no_coll_at_sparse.
            apply H.
        +
          intros [A B].

          destruct compat as [C].
          specialize (C (mkFinNat jc)).
          unfold In in C.

          apply Is_Val_In_outset in A ; auto.
          apply Is_Val_In_outset in B ; auto.

          contradict C.
          apply Intersection_intro; auto.
      -
        (* no_coll_at_sparse *)
        intros v j jc S.
        unfold Apply2Union, Apply2Union', Vec2Union in *.
        simpl in *.
        rewrite Vnth_map2.
        apply UnionCollisionFree.
        +
          apply no_coll_at_sparse.
          apply fop1.
          contradict S.
          apply Union_introl.
          apply S.
        +
          apply no_coll_at_sparse.
          apply fop2.
          contradict S.
          apply Union_intror.
          apply S.
        +
          intros [A B].

          destruct compat as [C].
          specialize (C (mkFinNat jc)).
          unfold In in C.

          apply Is_Val_In_outset in A ; auto.
          apply Is_Val_In_outset in B ; auto.

          contradict C.
          apply Intersection_intro; auto.
    Qed.

  End TSigmaHCOLOperators_StructuralProperties.

End WithCarrierA.
