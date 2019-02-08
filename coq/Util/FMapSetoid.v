Require Import Coq.Bool.Bool.
Require Import Coq.Structures.DecidableType.
Require Import Coq.Structures.DecidableTypeEx.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Classes.Morphisms.
Require Export Coq.FSets.FMapInterface.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Setoids.Setoid.

Module Make (K:OrderedType) (Import M:WSfun K) (V:BooleanDecidableType).
  Module Import F:=WFacts_fun K M.

  Lemma EquivSetoid_Reflexive :
    Reflexive V.eq -> Reflexive (M.Equiv V.eq).
  Proof.
    intros H.
    split.
    -
      reflexivity.
    -
      intros k e e' H0 H1.
      assert(E: e=e').
      {
        apply F.MapsTo_fun with (m:=x) (x:=k).
        apply H0.
        apply H1.
      }
      rewrite E.
      apply H.
  Qed.

  Lemma MapsTo_In (k:key) (e:V.t) (m:t V.t):
    MapsTo k e m -> In k m.
  Proof.
    intros H.
    apply in_find_iff.
    apply find_1 in H.
    rewrite H.
    unfold not.
    intros.
    congruence.
  Qed.

  Lemma In_MapsTo (k:key) (m:t V.t):
    In k m -> exists e, MapsTo k e m.
  Proof.
    intros H.
    apply in_find_iff in H.
    destruct (find k m) as [e |] eqn:D.
    -
      eexists e.
      apply find_2.
      apply D.
    -
      congruence.
  Qed.

  Lemma EquivSetoid_Symmetric :
    Symmetric V.eq -> Symmetric (M.Equiv V.eq).
  Proof.
    intros H.
    split.
    -
      intros k.
      rewrite F.Equiv_Equivb with (cmp:=V.eqb) in H0.
      +
        symmetry.
        apply H0.
      +
        unfold compat_cmp; apply V.eqb_eq.
    -
      intros k e e' H1 H2.
      rewrite F.Equiv_Equivb with (cmp:=V.eqb) in H0.
      +
        destruct H0.
        unfold Cmp in H3.
        specialize (H3 k e' e H2 H1).
        symmetry.
        apply V.eqb_eq.
        apply H3.
      +
        unfold compat_cmp; apply V.eqb_eq.
  Qed.

  Lemma EquivSetoid_Transitive:
    Transitive V.eq -> Transitive (M.Equiv V.eq).
  Proof.
    intros H.
    split.
    -
      intros k.
      rewrite F.Equiv_Equivb with (cmp:=V.eqb) in H0, H1.
      +
        destruct H0, H1.
        rewrite H0, H1.
        reflexivity.
      +
        unfold compat_cmp; apply V.eqb_eq.
      +
        unfold compat_cmp; apply V.eqb_eq.
    -
      intros k e e' H2 H3.
      destruct H0 as [I0 H0]; specialize (H0 k); specialize (I0 k).
      destruct H1 as [I1 H1]; specialize (H1 k); specialize (I1 k).
      unfold Transitive in H.
      rename e into x', e' into z'.

      assert(exists y', MapsTo k y' y).
      {
        destruct (find k y) as [y' |] eqn:D.
        -
          apply In_MapsTo.
          apply I0.
          eapply MapsTo_In.
          apply H2.
        -
          contradict D.
          apply in_find_iff.
          apply I0.
          apply MapsTo_In with (e:=x').
          apply H2.
      }
      destruct H4 as [y' H4].
      eapply H0 in H2.
      eapply H1 in H3.
      specialize (H x' y' z' H2 H3).
      apply H.
      apply H4.
      apply H4.
  Qed.

  Lemma EquivSetoid_Equivalence :
    Equivalence V.eq -> Equivalence (M.Equiv V.eq).
  Proof.
    intros H.
    split.
    apply EquivSetoid_Reflexive, H.
    apply EquivSetoid_Symmetric, H.
    apply EquivSetoid_Transitive, H.
  Qed.

End Make.
