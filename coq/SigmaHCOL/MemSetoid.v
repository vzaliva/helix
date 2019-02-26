Require Import Helix.SigmaHCOL.Memory.
Require Import Helix.Util.FMapSetoid.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.HCOL.CarrierType.

Require Import Coq.Classes.RelationClasses.
Require Import MathClasses.interfaces.canonical_names.

Module NMS := FMapSetoid.Make Coq.Structures.OrderedTypeEx.Nat_as_OT NM
                              CarrierA_as_BooleanDecidableType.

Global Instance mem_block_Equiv:
  Equiv (mem_block) := mem_block_equiv.

Global Instance mem_block_Equiv_Reflexive:
  Reflexive (mem_block_Equiv).
Proof.
  apply NMS.EquivSetoid_Reflexive.
  typeclasses eauto.
Qed.

Global Instance mem_block_Equiv_Symmetric:
  Symmetric (mem_block_Equiv).
Proof.
  apply NMS.EquivSetoid_Symmetric.
  typeclasses eauto.
Qed.

Global Instance mem_block_Equiv_Transitive:
  Transitive (mem_block_Equiv).
Proof.
  apply NMS.EquivSetoid_Transitive.
  typeclasses eauto.
Qed.

Global Instance mem_block_Equiv_Equivalence:
  Equivalence (mem_block_Equiv).
Proof.
  apply NMS.EquivSetoid_Equivalence.
  typeclasses eauto.
Qed.

Global Instance mem_lookup_proper:
  Proper ((eq) ==> (=) ==> (=)) (mem_lookup).
Proof.
  simpl_relation.
  unfold mem_lookup.

  unfold equiv,mem_block_Equiv,mem_block_equiv,NM.Equiv in H0.
  destruct H0 as [H0 H1].
  specialize (H0 y).
  specialize (H1 y).

  destruct ((NM.find (elt:=CarrierA) y x0)) eqn:E1;
    destruct (NM.find (elt:=CarrierA) y y0) eqn:E2; simpl.
  -
    apply RelUtil.opt_r_Some.
    apply H1.
    +
      apply NM.find_2, E1.
    +
      apply NM.find_2, E2.
  -
    exfalso.
    apply NM.find_2, NMS.MapsTo_In, H0 in E1.
    apply NMS.F.not_find_in_iff in E2.
    congruence.
  -
    exfalso.
    apply NM.find_2,NMS.MapsTo_In, H0 in E2.
    apply NMS.F.not_find_in_iff in E1.
    congruence.
  -
    reflexivity.
Qed.

Global Instance mem_mapsto_proper:
  Proper ((eq) ==> (=) ==> (=) ==> iff) (mem_mapsto).
Proof.
  simpl_relation.
  unfold mem_mapsto.

  unfold equiv,mem_block_Equiv,mem_block_equiv,NM.Equiv in H1.
  destruct H1 as [H1 H2].
  specialize (H1 y).
  specialize (H2 y).
  split.
  -
    intros H.

Admitted.


Global Instance mem_in_proper:
  Proper ((eq) ==> (=) ==> iff) (mem_in).
Proof.
  simpl_relation.
  unfold mem_in.
  split.
  -
    intros H.
    apply NMS.In_MapsTo in H.
    destruct H as [e H].
    apply NMS.MapsTo_In with (e:=e).
    rewrite <- H0.
    apply H.
  -
    intros H.
    apply NMS.In_MapsTo in H.
    destruct H as [e H].
    apply NMS.MapsTo_In with (e:=e).
    rewrite H0.
    apply H.
Qed.
