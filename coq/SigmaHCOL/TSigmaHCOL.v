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
Require Import Helix.SigmaHCOL.SigmaHCOLMem.
Require Import Helix.SigmaHCOL.SigmaHCOL.
Require Import Helix.SigmaHCOL.Memory.
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
Require Import ExtLib.Structures.Monoid.
Import Monoid.

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

  Definition SafeCast
             {svalue: CarrierA}
             {i o}
             (f: @SHOperator Monoid_RthetaSafeFlags i o svalue)
    : @SHOperator Monoid_RthetaFlags i o svalue
    :=
      mkSHOperator Monoid_RthetaFlags i o svalue
                   (SafeCast' (op Monoid_RthetaSafeFlags f))
                   _
                   (in_index_set _ f)
                   (out_index_set _ f).

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
             (f: @SHOperatorFamily Monoid_RthetaSafeFlags i o n svalue)
    : @SHOperatorFamily Monoid_RthetaFlags i o n svalue
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

  Definition UnSafeCast
             {svalue: CarrierA}
             {i o: nat}
             (f: @SHOperator Monoid_RthetaFlags i o svalue)
    : @SHOperator Monoid_RthetaSafeFlags i o svalue
    :=
      mkSHOperator Monoid_RthetaSafeFlags i o svalue
                   (UnSafeCast' (op Monoid_RthetaFlags f))
                   _
                   (in_index_set _ f)
                   (out_index_set _ f).

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
             (f: @SHOperatorFamily Monoid_RthetaFlags i o n svalue)
    : @SHOperatorFamily Monoid_RthetaSafeFlags i o n svalue
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


(* For now we are not define special type for TSigmahcolOperators, like we did for SHOperator. Currently we have only 2 of these: SHCompose and HTSumunion. We will generalize in future, if needed *)
Section TSigmaHCOLOperators.

  Variable fm:Monoid RthetaFlags.

  (* Per Vadim's discussion with Franz on 2015-12-14, ISumUnion is
  just Union of two vectors, produced by application of two operators
  to the input.
   *)
  Definition HTSUMUnion' {i o}
             (dot: CarrierA -> CarrierA -> CarrierA)
             (op1: svector fm i -> svector fm o)
             (op2: svector fm i -> svector fm o):
    svector fm i -> svector fm o
    := fun x => Vec2Union fm dot (op1 x) (op2 x).

  Global Instance HTSUMUnion'_proper {i o}
    : Proper ( ((=) ==> (=) ==> (=)) ==>
                                 (=) ==> (=) ==> (=) ==> (=)) (HTSUMUnion' (i:=i) (o:=o)).
  Proof.
    intros dot dot' Edot f f' Ef g g' Eg x y Ex.
    unfold HTSUMUnion'.
    unfold Vec2Union.
    vec_index_equiv j jp.
    rewrite 2!Vnth_map2.
    f_equiv.
    apply Edot.
    - apply Vnth_arg_equiv; auto.
    - apply Vnth_arg_equiv; auto.
  Qed.

  Global Instance HTSUMUnion'_arg_proper {i o}
         (op1: svector fm i -> svector fm o)
         `{op1_proper: !Proper ((=) ==> (=)) op1}
         (op2: svector fm i -> svector fm o)
         `{op2_proper: !Proper ((=) ==> (=)) op2}
         (dot: CarrierA -> CarrierA -> CarrierA)
         `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
    : Proper ((=) ==> (=)) (HTSUMUnion' (i:=i) (o:=o) dot op1 op2).
  Proof.
    partial_application_tactic. instantiate (1 := equiv).
    partial_application_tactic. instantiate (1 := equiv).
    apply HTSUMUnion'_proper.
    - apply dot_mor.
    - apply op1_proper.
    - apply op2_proper.
  Qed.

  (* Probably "SUM" shoud be avoided in the name not to confuse
     with [ISUmUnion]. *)
  Definition HTSUMUnion {i o}
             {svalue: CarrierA}
             (dot: CarrierA -> CarrierA -> CarrierA)
             `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
             (op1 op2: @SHOperator fm i o svalue)
    : @SHOperator fm i o svalue
    :=
      mkSHOperator fm i o svalue (HTSUMUnion' dot (op fm op1) (op fm op2))
                   (@HTSUMUnion'_arg_proper i o
                                            (op fm op1) (op_proper fm op1)
                                            (op fm op2) (op_proper fm op2)
                                            dot dot_mor)
                   (Ensembles.Union _ (in_index_set _ op1) (in_index_set _ op2))
                   (Ensembles.Union _ (out_index_set _ op1) (out_index_set _ op2)).

  Global Instance HTSUMUnion_proper
         {svalue: CarrierA}
         {i o: nat}
         (dot: CarrierA -> CarrierA -> CarrierA)
         `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
    : Proper ((=) ==> (=) ==> (=))
             (@HTSUMUnion i o svalue dot dot_mor).
  Proof.
    intros x x' Ex y y' Ey.
    unfold HTSUMUnion.
    unfold equiv, SHOperator_equiv in *.
    destruct x, y, x', y'.
    simpl in *.
    apply HTSUMUnion'_proper; assumption.
  Qed.

End TSigmaHCOLOperators.

Section TSigmaHCOLOperators_StructuralProperties.

  Global Instance SafeCast_Facts
         {i o: nat}
         {svalue: CarrierA}
         (xop: @SHOperator Monoid_RthetaSafeFlags i o svalue)
         `{fop: SHOperator_Facts Monoid_RthetaSafeFlags _ _ _ xop}
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
    -
      (* svalue_at_sparse *)
      intros v j jc S.
      unfold SafeCast, SafeCast', compose, rsvector2rvector, rvector2rsvector in *.
      simpl in *.

      rewrite Vnth_map.
      apply svalue_at_sparse; assumption.
  Qed.

  Global Instance UnSafeCast_Facts
         {svalue: CarrierA}
         {i o}
         (xop: @SHOperator Monoid_RthetaFlags i o svalue)
         `{fop: SHOperator_Facts Monoid_RthetaFlags _ _ _ xop}
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
    -
      (* svalue_at_sparse *)
      intros v j jc S.
      unfold UnSafeCast, UnSafeCast', compose, rsvector2rvector, rvector2rsvector in *.
      simpl in *.

      rewrite Vnth_map.
      apply svalue_at_sparse; assumption.
  Qed.

  Global Instance HTSUMUnion_Facts
         {i o: nat}
         {svalue: CarrierA}
         (dot: CarrierA -> CarrierA -> CarrierA)
         `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
         (op1 op2: @SHOperator Monoid_RthetaFlags i o svalue)
         `{fop1: SHOperator_Facts Monoid_RthetaFlags _ _ _ op1}
         `{fop2: SHOperator_Facts Monoid_RthetaFlags _ _ _ op2}
         (compat: Disjoint _
                           (out_index_set _ op1)
                           (out_index_set _ op2)
         )
         (scompat: dot svalue svalue = svalue)
    : SHOperator_Facts Monoid_RthetaFlags (HTSUMUnion Monoid_RthetaFlags dot op1 op2).
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
      unfold HTSUMUnion', Vec2Union in *.
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
      unfold HTSUMUnion', Vec2Union in *.
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
      unfold HTSUMUnion, HTSUMUnion', Vec2Union.
      simpl.
      rewrite Vnth_map2.
      apply StructUnionIsStruct.

      unfold Is_Struct, IsStruct, compose.
      split.
      +
        apply fop1.
        unfold HTSUMUnion, HTSUMUnion', Vec2Union in S.
        simpl in *.
        contradict S.
        apply Union_introl.
        apply S.
      +
        apply fop2.
        unfold HTSUMUnion, HTSUMUnion', Vec2Union in S.
        simpl in *.
        contradict S.
        apply Union_intror.
        apply S.
    -
      (* no_coll_range *)
      intros v D j jc S.
      unfold HTSUMUnion, HTSUMUnion', Vec2Union in *.
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

        apply Is_Val_In_outset in A ; [auto |auto| apply fop1].
        apply Is_Val_In_outset in B ; [auto |auto| apply fop2].

        contradict C.
        apply Intersection_intro; auto.
    -
      (* no_coll_at_sparse *)
      intros v j jc S.
      unfold HTSUMUnion, HTSUMUnion', Vec2Union in *.
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

        apply Is_Val_In_outset in A ; [auto |auto| apply fop1].
        apply Is_Val_In_outset in B ; [auto |auto| apply fop2].

        contradict C.
        apply Intersection_intro; auto.
    -
      (* svalue_at_sparse *)
      intros v j jc S.
      unfold HTSUMUnion, HTSUMUnion', Vec2Union.
      simpl.
      rewrite Vnth_map2.
      rewrite evalWriterUnion.
      unfold HTSUMUnion, HTSUMUnion', Vec2Union in S.
      simpl in *.
      assert(S1: ¬ (out_index_set Monoid_RthetaFlags op1 (mkFinNat jc))).
      {
        intros H.
        contradict S.
        apply Union_introl, H.
      }
      assert(S2: ¬ (out_index_set Monoid_RthetaFlags op2 (mkFinNat jc))).
      {
        intros H.
        contradict S.
        apply Union_intror, H.
      }
      clear S.

      apply svalue_at_sparse with (v:=v) in S1; eauto.
      rewrite S1.
      apply svalue_at_sparse with (v:=v) in S2; eauto.
      rewrite S2.
      apply scompat.
  Qed.

End TSigmaHCOLOperators_StructuralProperties.
