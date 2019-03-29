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

  Definition SafeCast {i o}
             (f: @SHOperator Monoid_RthetaSafeFlags i o)
    : @SHOperator Monoid_RthetaFlags i o
    :=
      mkSHOperator Monoid_RthetaFlags i o
                   (SafeCast' (op Monoid_RthetaSafeFlags f))
                   _
                   (mem_op _ f)
                   (mem_op_proper _ f)
                   (in_index_set _ f)
                   (out_index_set _ f).

  Global Instance SafeCast_proper (i o:nat):
    Proper (equiv ==> equiv) (@SafeCast i o).
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

  Definition SafeFamilyCast {i o n}
             (f: @SHOperatorFamily Monoid_RthetaSafeFlags i o n)
    : @SHOperatorFamily Monoid_RthetaFlags i o n
    := fun jf => SafeCast (f jf).

  Global Instance SafeFamilyCast_proper (i o n:nat):
    Proper (equiv ==> equiv) (@SafeFamilyCast i o n).
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

  Definition UnSafeCast {i o}
             (f: @SHOperator Monoid_RthetaFlags i o)
    : @SHOperator Monoid_RthetaSafeFlags i o
    :=
      mkSHOperator Monoid_RthetaSafeFlags i o
                   (UnSafeCast' (op Monoid_RthetaFlags f))
                   _
                   (mem_op _ f)
                   (mem_op_proper _ f)
                   (in_index_set _ f)
                   (out_index_set _ f).

  Global Instance UnSafeCast_proper (i o:nat):
    Proper (equiv ==> equiv) (@UnSafeCast i o).
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


  Definition UnSafeFamilyCast {i o n}
             (f: @SHOperatorFamily Monoid_RthetaFlags i o n)
    : @SHOperatorFamily Monoid_RthetaSafeFlags i o n
    := fun jf => UnSafeCast (f jf).


  Global Instance UnSafeFamilyCast_proper (i o n:nat):
    Proper (equiv ==> equiv) (@UnSafeFamilyCast i o n).
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
                   (HTSUMUnion_mem
                      (mem_op _ op1)
                      (mem_op _ op2))
                   (HTSUMUnion_mem_proper
                      (mem_op_proper _ op1)
                      (mem_op_proper _ op2))
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

Lemma svector_to_memblock_of_castWriter
      {i : nat} (fm0 fm1: Monoid RthetaFlags)
      (v0 : svector fm0 i):
  svector_to_mem_block v0 = svector_to_mem_block (Vmap (castWriter fm1) v0).
Proof.

  unfold equiv, MemSetoid.mem_block_Equiv, mem_block_equiv.
  unfold svector_to_mem_block.
  svector_to_mem_block_to_spec m0 H0 I0 O0.
  svector_to_mem_block_to_spec m1 H1 I1 O1.
  unfold mem_lookup in *; simpl in *.
  apply NP.F.Equal_mapsto_iff.
  intros k e.

  destruct (lt_dec k i) as [kc |kc].
  -
    (* k<i, normal case *)
    clear O0 O1.
    specialize (H0 k kc). specialize (H1 k kc).
    specialize (I0 k kc). specialize (I1 k kc).

    assert(E: evalWriter (Vnth v0 kc) ≡ evalWriter (Vnth (Vmap (castWriter fm1) v0) kc)).
    {
      rewrite Vnth_map.
      rewrite evalWriter_castWriter.
      reflexivity.
    }

    destruct (NP.F.In_dec m0 k) as [IN0 | NIN0], (NP.F.In_dec m1 k) as [IN1 | NIN1].
    +
      (* both in *)
      assert(V0: Is_Val (Vnth v0 kc)) by apply I0,IN0; clear I0.
      apply H0 in V0; clear H0.
      assert(V1: Is_Val (Vnth (Vmap (castWriter fm1) v0) kc)) by apply I1,IN1; clear I1.
      apply H1 in V1; clear H1.
      split; intros P.
      *
        pose proof(NP.F.MapsTo_fun V0 P).
        subst e.
        setoid_rewrite E.
        apply V1.
      *
        pose proof(NP.F.MapsTo_fun V1 P).
        subst e.
        setoid_rewrite <- E.
        apply V0.
    +
      (* k in m0 but not in m1 *)
      exfalso.
      assert(V0: Is_Val (Vnth v0 kc)) by apply I0,IN0; clear I0.
      assert(V1: Is_Val (Vnth (Vmap (castWriter fm1) v0) kc)).
      {
        unfold Is_Val, compose.
        rewrite Vnth_map.
        rewrite execWriter_castWriter.
        apply V0.
      }
      apply H1 in V1.
      apply MemSetoid.MapsTo_In in V1.
      congruence.
    +
      (* k in m1 but not in m0 *)
      exfalso.
      assert(V1: Is_Val (Vnth (Vmap (castWriter fm1) v0) kc)) by apply I1,IN1; clear I1.
      assert(V0: Is_Val (Vnth v0 kc)).
      {
        rewrite Vnth_map in V1.
        unfold Is_Val, compose in V1.
        rewrite execWriter_castWriter in V1.
        apply V1.
      }
      apply H0 in V0.
      apply MemSetoid.MapsTo_In in V0.
      congruence.
    +
      (* k in neither m0, m1 *)
      split; intros P; apply MemSetoid.MapsTo_In in P; congruence.
  -
    (* k>=i oob case *)
    clear H0 H1 I0 I1.
    apply Nat.nlt_ge in kc.
    specialize (O0 k kc); apply NP.F.not_find_in_iff in O0.
    specialize (O1 k kc); apply NP.F.not_find_in_iff in O1.
    split; intros H;
      apply MemSetoid.MapsTo_In in H;
      congruence.
Qed.

Section TSigmaHCOLOperators_StructuralProperties.

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
    -
      (* mem_out_some *)
      intros v H.
      pose proof (@mem_out_some Monoid_RthetaSafeFlags i o xop fop) as M.
      unfold SafeCast in *.
      simpl in *.
      apply M, H.
    -
      (* out_mem_fill_pattern *)
      intros m0 m H.
      destruct fop.
      apply out_mem_fill_pattern in H; clear out_mem_fill_pattern.
      destruct H as [H NH].
      split; intros.
      +
        split; intros P; specialize (H j jc); apply H, P.
      +
        apply NH, jc.
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
    -
      (* mem_out_some *)
      intros v H.
      pose proof (@mem_out_some Monoid_RthetaFlags i o xop fop) as M.
      unfold UnSafeCast in *.
      simpl in *.
      apply M, H.
    -
      (* out_mem_fill_pattern *)
      intros m0 m H.
      destruct fop.
      apply out_mem_fill_pattern in H; clear out_mem_fill_pattern.
      destruct H as [H NH].
      split; intros.
      +
        split; intros P; specialize (H j jc); apply H, P.
      +
        apply NH, jc.
  Qed.

    Lemma is_disjoint_Disjoint (s s' : NS.t)
    : Disjoint NS.elt (NE.mkEns s) (NE.mkEns s') <-> is_disjoint s s' ≡ true.
  Proof.
    split.
    -
      intros E.
      destruct E as [E].
      unfold is_disjoint.
      apply NS.is_empty_1.
      unfold NS.Empty.
      intros a.
      specialize (E a).
      intros H.
      rewrite NE.In_In in H.
      apply NE.inter_Intersection in H.
      congruence.
    -
      intros D.
      unfold is_disjoint in D.
      apply NS.is_empty_2 in D.
      apply NE.Empty_Empty_set in D.
      apply Disjoint_intro.
      intros x E.
      unfold Ensembles.In in E.
      apply NE.inter_Intersection in E.
      unfold Ensembles.In in E.
      apply D in E. clear D.
      apply Constructive_sets.Noone_in_empty in E.
      tauto.
  Qed.

  (* TODO: could be proven <-> *)
  Lemma mem_merge_is_Some
        (m0 m1 : mem_block)
    :
      Disjoint nat (NE.mkEns (mem_keys_set m0))
               (NE.mkEns (mem_keys_set m1)) → is_Some (mem_merge m0 m1).
  Proof.
    unfold mem_merge.
    unfold mem_keys_set.
    generalize (NSP.of_list (mem_keys_lst m0)) as s0.
    generalize (NSP.of_list (mem_keys_lst m1)) as s1.
    intros s1 s0 H.
    break_if.
    -
      simpl; tauto.
    -
      apply is_disjoint_Disjoint in H.
      congruence.
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
      (* mem_out_some *)
      intros m H.
      unfold is_Some, HTSUMUnion, HTSUMUnion_mem in *.
      simpl in *.
      repeat break_match; try some_none; try auto.
      +
        contradict Heqo0.
        clear H.
        apply is_Some_ne_None.
        apply mem_merge_is_Some.
        pose proof (out_mem_fill_pattern Monoid_RthetaFlags m m0 Heqo1) as [P1 NP1].
        pose proof (out_mem_fill_pattern Monoid_RthetaFlags m m1 Heqo2) as [P2 NP2].

        apply Disjoint_intro.
        intros j.
        destruct (NatUtil.lt_ge_dec j o) as [jc | jc].
        *
          clear NP1 NP2.
          specialize (P1 j jc).
          specialize (P2 j jc).
          destruct compat as [compat].
          specialize (compat (mkFinNat jc)).
          intros C.
          unfold In, not  in *.
          destruct C as [j H0 H1].

          apply NE.In_In, mem_keys_set_In, P1 in H0. clear P1.
          apply NE.In_In, mem_keys_set_In, P2 in H1. clear P2.
          destruct compat.
          apply Intersection_intro; auto.
        *
          specialize (NP1 j jc).
          intros C.
          destruct C as [j H0 _].
          apply NE.In_In, mem_keys_set_In in H0.
          unfold mem_in in NP1.
          congruence.
      +
        clear Heqo0.
        contradict Heqo2.
        apply is_Some_ne_None.
        apply mem_out_some; auto.
        intros j jc H0.
        specialize (H j jc).
        apply H.
        apply Union_intror.
        apply H0.
      +
        clear Heqo0.
        contradict Heqo1.
        apply is_Some_ne_None.
        apply mem_out_some; auto.
        intros j jc H0.
        specialize (H j jc).
        apply H.
        apply Union_introl.
        apply H0.
    -
      (* out_mem_fill_pattern *)
      admit.
  Admitted.

End TSigmaHCOLOperators_StructuralProperties.
