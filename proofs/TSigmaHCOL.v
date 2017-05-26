(* Template HCOL. HCOL meta-operators *)

Require Import VecUtil.
Require Import VecSetoid.
Require Import Spiral.
Require Import Rtheta.
Require Import SVector.
Require Import IndexFunctions.
Require Import SigmaHCOL. (* Presently for SHOperator only. Consider moving it elsewhere *)
Require Import FinNatSet.


Require Import Arith.
Require Import Program. (* compose *)
Require Import Morphisms.
Require Import RelationClasses.
Require Import Relations.

Require Import SpiralTactics.
Require Import Coq.Logic.FunctionalExtensionality.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.theory.rings.
Require Import MathClasses.theory.setoids.

(* ExtLib *)
Require Import ExtLib.Structures.Monoid.
Import Monoid.

(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.


Section RthetaSafetyCast.

  Definition SafeCast'
             {o i}
             (f: rsvector i -> rsvector o):
    rvector i -> rvector o
    := (rsvector2rvector o) ∘ f ∘ (rvector2rsvector i).

  Lemma SafeCast'_proper (i o : nat)
        (op : rsvector i → rsvector o)
        (op_proper: Proper (equiv ==> equiv) (op))
    :
      Proper (equiv ==> equiv) (SafeCast' op).
  Proof.
    intros v v' Ev.
    unfold SafeCast', compose, rsvector2rvector, rvector2rsvector.
    f_equiv.
    f_equiv.
    f_equiv.
    apply Ev.
  Qed.

  Definition SafeCast {i o}
             (f: @SHOperator Monoid_RthetaSafeFlags i o)
    : @SHOperator Monoid_RthetaFlags i o.
  Proof.
    refine (mkSHOperator Monoid_RthetaFlags i o
                         (SafeCast' (op Monoid_RthetaSafeFlags f))
                         _  _ _).
    -
      destruct f.
      simpl.
      apply SafeCast'_proper, op_proper.
    -
      apply f.
    -
      apply f.
  Defined.

  Definition SafeFamilyCast {i o n}
             (f: @SHOperatorFamily Monoid_RthetaSafeFlags i o n)
    : @SHOperatorFamily Monoid_RthetaFlags i o n
    :=
      mkSHOperatorFamily _ _ _ _
                         (fun (j : nat) (jc : j < n) =>
                            SafeCast (family_member Monoid_RthetaSafeFlags f j jc)).


  Definition UnSafeCast'
             {o i}
             (f: rvector i -> rvector o):
    rsvector i -> rsvector o
    := (rvector2rsvector o) ∘ f ∘ (rsvector2rvector i).


  Lemma UnSafeCast'_proper (i o : nat)
        (op : rvector i → rvector o)
        (op_proper: Proper (equiv ==> equiv) (op))
    :
      Proper (equiv ==> equiv) (UnSafeCast' op).
  Proof.
    intros v v' Ev.
    unfold UnSafeCast', compose, rsvector2rvector, rvector2rsvector.
    f_equiv.
    f_equiv.
    f_equiv.
    apply Ev.
  Qed.

  Definition UnSafeCast {i o}
             (f: @SHOperator Monoid_RthetaFlags i o)
    : @SHOperator Monoid_RthetaSafeFlags i o.
  Proof.
    refine (mkSHOperator Monoid_RthetaSafeFlags i o
                         (UnSafeCast' (op Monoid_RthetaFlags f))
                         _  _ _).
    -
      destruct f.
      simpl.
      apply UnSafeCast'_proper, op_proper.
    -
      apply f.
    -
      apply f.
  Defined.

  Definition UnSafeFamilyCast {i o n}
             (f: @SHOperatorFamily Monoid_RthetaFlags i o n)
    : @SHOperatorFamily Monoid_RthetaSafeFlags i o n
    :=
      mkSHOperatorFamily _ _ _ _
                         (fun (j : nat) (jc : j < n) =>
                            UnSafeCast (family_member Monoid_RthetaFlags f j jc)).

End RthetaSafetyCast.


(* For now we are not define special type for TSigmahcolOperators, like we did for SHOperator. Currently we have only 2 of these: SHCompose and HTSumunion. We will generalize in future, if needed *)
Section TSigmaHCOLOperators.

  Variable fm:Monoid RthetaFlags.
  Variable fml:@MonoidLaws RthetaFlags RthetaFlags_type fm.

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


  (* TODO: make dot part of morphism *)
  Global Instance HTSUMUnion'_proper {i o}
         (dot: CarrierA -> CarrierA -> CarrierA)
         `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
    : Proper ((=) ==> (=) ==> (=) ==> (=)) (HTSUMUnion' (i:=i) (o:=o) dot).
  Proof.
    intros f f' Ef g g' Eg x y Ex.
    unfold HTSUMUnion'.
    unfold Vec2Union.
    vec_index_equiv j jp.
    rewrite 2!Vnth_map2.
    setoid_replace (Vnth (f x) jp) with (Vnth (f' y) jp).
    setoid_replace (Vnth (g x) jp) with (Vnth (g' y) jp).
    reflexivity.
    - apply Vnth_arg_equiv.
      apply Eg, Ex.
    - apply Vnth_arg_equiv.
      apply Ef, Ex.
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

  Definition HTSUMUnion {i o}
             (dot: CarrierA -> CarrierA -> CarrierA)
             `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
             (op1 op2: @SHOperator fm i o)
    : @SHOperator fm i o
    :=
      mkSHOperator fm i o (HTSUMUnion' dot (op fm op1) (op fm op2))
                   (@HTSUMUnion'_arg_proper i o
                                            (op fm op1) (op_proper fm op1)
                                            (op fm op2) (op_proper fm op2)
                                            dot dot_mor)
                   (Ensembles.Union _ (in_index_set _ op1) (in_index_set _ op2))
                   (Ensembles.Union _ (out_index_set _ op1) (out_index_set _ op2)).

  Global Instance HTSUMUnion_proper
         {i o}
         (dot: CarrierA -> CarrierA -> CarrierA)
         `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
    : Proper ((=) ==> (=) ==> (=))
             (@HTSUMUnion i o dot dot_mor).
  Proof.
    intros x x' Ex y y' Ey.
    unfold HTSUMUnion.
    unfold equiv, SHOperator_equiv in *.
    destruct x, y, x', y'.
    simpl in *.
    apply HTSUMUnion'_proper; assumption.
  Qed.

End TSigmaHCOLOperators.


Global Instance SafeCast_Facts
       {i o}
       (xop: @SHOperator Monoid_RthetaSafeFlags i o)
       `{fop: SHOperator_Facts Monoid_RthetaSafeFlags _ _ xop}
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
       {i o}
       (xop: @SHOperator Monoid_RthetaFlags i o)
       `{fop: SHOperator_Facts Monoid_RthetaFlags _ _ xop}
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

Global Instance HTSUMUnion_Facts
       {i o}
       (dot: CarrierA -> CarrierA -> CarrierA)
       `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
       (op1 op2: @SHOperator Monoid_RthetaFlags i o)
       `{fop1: SHOperator_Facts Monoid_RthetaFlags _ _ op1}
       `{fop2: SHOperator_Facts Monoid_RthetaFlags _ _ op2}
       (compat: Disjoint _
                         (out_index_set _ op1)
                         (out_index_set _ op2)
       )
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
    unfold Is_Struct, compose, not.
    split.
    +
      intros H.
      apply fop1 in H.
      inversion H.
      unfold HTSUMUnion, HTSUMUnion', Vec2Union in S.
      simpl in *.
      unfold not in S.
      contradict S.
      apply Union_introl.
      apply S.
    +
      intros H.
      apply fop2 in H.
      inversion H.
      unfold HTSUMUnion, HTSUMUnion', Vec2Union in S.
      simpl in *.
      unfold not in S.
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
Qed.