Require Import Helix.Util.VecUtil.
Require Import Helix.Util.Matrix.
Require Import Helix.Util.VecSetoid.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.Util.Misc.
Require Import Helix.Util.FinNat.
Require Import Helix.Util.FMapSetoid.
Require Import Helix.SigmaHCOL.Rtheta.
Require Import Helix.SigmaHCOL.SVector.
Require Import Helix.SigmaHCOL.IndexFunctions.
Require Import Helix.SigmaHCOL.Memory.
Require Import Helix.SigmaHCOL.SigmaHCOLImpl.
Require Import Helix.SigmaHCOL.SigmaHCOL.
Require Import Helix.SigmaHCOL.SigmaHCOLMem.
Require Import Helix.HCOL.HCOL. (* Presently for HOperator only. Consider moving it elsewhere *)
Require Import Helix.Util.FinNatSet.
Require Import Helix.Util.WriterMonadNoT.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.BoolEq.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Decidable.

Require Import Helix.Tactics.HelixTactics.
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

Program Definition svector_to_mem_block_spec
        {fm}
        {n : nat}
        (v : svector fm n):
  { m : mem_block | forall i (ip : i < n),
      Is_Val (Vnth v ip) ->
      mem_lookup i m ≡ Some (evalWriter (Vnth v ip))
  }
  := Vfold_right_indexed' 0
                          (fun k r m =>
                             if Is_Val_dec r then mem_add k (evalWriter r) m
                             else m
                          )
                          v mem_empty.
Next Obligation.
  unfold mem_lookup.
  revert H. revert ip. revert i.
  induction n; intros.
  -
    nat_lt_0_contradiction.
  -
    dep_destruct v;clear v.
    simpl.
    destruct i.
    +
      unfold Vfold_right_indexed, mem_add.
      destruct (Is_Val_dec h).
      *
        apply NM_find_add_1.
        reflexivity.
      *
        simpl in H.
        crush.
    +
      destruct (Is_Val_dec h).
      *
        rewrite NM_find_add_3; auto.
        assert (N: i<n) by apply Lt.lt_S_n, ip.
        specialize (IHn x i N).
        simpl in H.
        replace (Lt.lt_S_n ip) with N by apply le_unique.
        rewrite <- IHn; clear IHn.
        --
          unfold mem_add.
          unfold mem_empty.
          rewrite find_vold_right_indexed'_S_P.
          reflexivity.
        --
          replace N with (lt_S_n ip) by apply le_unique.
          apply H.
      *
        simpl in H.
        rewrite find_vold_right_indexed'_S_P.
        apply IHn.
        apply H.
Qed.

Definition svector_to_mem_block {fm} {n} (v: svector fm n) := proj1_sig (svector_to_mem_block_spec v).

Lemma svector_to_mem_block_key_oob {n:nat} {fm} {v: svector fm n}:
  forall (k:nat) (kc:ge k n), mem_lookup k (svector_to_mem_block v) ≡ None.
Proof.
  intros k kc.
  unfold svector_to_mem_block.
  simpl.
  revert k kc; induction v; intros.
  -
    reflexivity.
  -
    unfold mem_lookup.
    simpl.
    destruct k.
    +
      omega.
    +
      break_if.
      *
        rewrite NM_find_add_3 by omega.
        rewrite find_vold_right_indexed'_S_P.
        rewrite IHv.
        reflexivity.
        omega.
      *
        rewrite find_vold_right_indexed'_S_P.
        rewrite IHv.
        reflexivity.
        omega.
Qed.


Global Instance mem_block_Equiv:
  Equiv (mem_block) := mem_block_equiv.

Module NMS := FMapSetoid.Make Coq.Structures.OrderedTypeEx.Nat_as_OT NM
                              CarrierA_as_BooleanDecidableType.

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

Class SHOperator_MemVecEq
      {fm}
      {i o: nat}
      (f: @SHOperator fm i o)
      `{facts: SHOperator_Facts _ _ _ f}
  :=
    {
      mem_vec_preservation:
        forall x,
          Some (svector_to_mem_block (op fm f x)) =
          mem_op fm f (svector_to_mem_block x)
      ;
    }.

Section MemVecEq.
  Variable fm:Monoid RthetaFlags.
  Variable fml:@MonoidLaws RthetaFlags RthetaFlags_type fm.

  Global Instance liftM_MemVecEq
         {i o}
         (hop: avector i -> avector o)
         `{HOP: HOperator i o hop}
    : SHOperator_MemVecEq (liftM_HOperator fm hop).
  Proof.
    assert (facts: SHOperator_Facts fm (liftM_HOperator fm hop)) by
        typeclasses eauto.
    split.
    intros x.
    simpl.
    unfold mem_op_of_hop.
    unfold liftM_HOperator', avector_to_mem_block, svector_to_mem_block, compose.
    destruct (svector_to_mem_block_spec _) as [m0 H0].
    destruct (svector_to_mem_block_spec _) as [m1 H1].
    break_match.
    -
      f_equiv.
      destruct (avector_to_mem_block_spec _) as [m2 H2].
      simpl in *.
      unfold equiv, mem_block_Equiv, mem_block_equiv, NM.Equiv.
      admit.
    -
      simpl in *.
      admit.
  Qed.

  Global Instance eUnion_MemVecEq
         {o b:nat}
         (bc: b < o)
         (z: CarrierA)
    : SHOperator_MemVecEq (eUnion fm bc z).
  Proof.
    (* assert (facts: SHOperator_Facts fm (eUnion fm bc z)) by
        typeclasses eauto. *)
    split.
    intros x.
    simpl.
    unfold eUnion_mem, map_mem_block_elt.
    unfold svector_to_mem_block, compose.
    break_match.
    -
      f_equiv.
      unfold eUnion'.
      unfold densify in *.
      unfold avector_to_mem_block in *.

      repeat match goal with
      | [|- context[avector_to_mem_block_spec ?x]] => destruct (avector_to_mem_block_spec x) as [m M]
      | [H:context[avector_to_mem_block_spec ?x] |- _] => destruct (avector_to_mem_block_spec x) as [m0 M0]
      end.
      simpl in *.
      rewrite Vmap_Vbuild in *.
      setoid_rewrite Vbuild_nth in M.
      setoid_rewrite Vnth_map in M0.
      specialize (M0 0 (lt_0_Sn 0)).
      rewrite Vnth_0 in M0.
      unfold zero in *.
      rewrite Heqo0 in M0; clear Heqo0 m0.
      some_inv.
      rewrite <- H0.
      admit.
    -
      unfold avector_to_mem_block in *.
      destruct (avector_to_mem_block_spec (densify fm x)) as [m E].
      simpl in Heqo0.
      specialize (E 0 (lt_0_Sn 0)).
      unfold zero in E.
      rewrite E in Heqo0.
      some_none_contradiction.
  Qed.

End MemVecEq.