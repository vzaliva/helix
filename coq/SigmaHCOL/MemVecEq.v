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

Definition svector_to_mem_block {fm} {n}:=
  avector_to_mem_block ∘ @densify fm n.

Global Instance mem_block_Equiv:
  Equiv (mem_block) := mem_block_equiv.

Module NMS := FMapSetoid.Make Coq.Structures.OrderedTypeEx.Nat_as_OT NM
                              CarrierA_as_BooleanDecidableType.
Print NMS.

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

(*
Global Instance avector_to_mem_block_Proper {n}:
  Proper ((=) ==> (=)) (@avector_to_mem_block n).
Proof.
  simpl_relation.
  induction n.
  -
    dep_destruct x.
    dep_destruct y.
    split.
    +
      crush.
    +
      intros;simpl.
      unfold avector_to_mem_block in *.
      unfold mem_empty in *.
      apply NMS.F.empty_mapsto_iff in H0.
      destruct H0.
  -
    split.
    +
      intros k.
      dep_destruct x; clear x; rename h into xh, x0 into xs.
      dep_destruct y; clear y; rename h into yh, x into ys.
      apply Vcons_equiv_elim in H.
      destruct H as [Hh Ht].
      specialize (IHn xs ys Ht).
      destruct IHn as [IHn0 IHn1].
      unfold avector_to_mem_block in *.
      simpl.

Qed.
*)
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
    unfold liftM_HOperator', compose.

    induction x.
    -
      simpl.
      f_equiv.
      induction (hop Vnil).
      +
        simpl.
        unfold svector_to_mem_block, compose.
        reflexivity.
      +
        simpl.
        unfold svector_to_mem_block, compose in *.
        simpl in *.

    -
      simpl.




    induction i.
    -
      simpl.
      f_equiv.
      dep_destruct x. clear x.
      induction o.
      +
        dep_destruct (hop Vnil).
        dep_destruct (liftM_HOperator' (fm:=fm) hop Vnil).
        unfold svector_to_mem_block, compose.
        simpl.
        reflexivity.
      +
        dep_destruct (hop Vnil).
        admit.
    -
      destruct x.
      admit.
      admit.
  Admitted.

End MemVecEq.