
Require Import Helix.Util.VecUtil.
Require Import Helix.Util.VecSetoid.
Require Import Helix.Util.Misc.
Require Import Helix.SigmaHCOL.Rtheta.

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Helix.Tactics.HelixTactics.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.abstract_algebra.

Import VectorNotations.

Require Import ExtLib.Structures.Monads.

Require Import Helix.Util.WriterMonadNoT.

Import Monoid.

Open Scope vector_scope.
Open Scope nat_scope.

(* Vector using Rtheta (exlusive) *)
Notation rvector n := (vector Rtheta n) (only parsing).
(* Vector using RStheta (safe) *)
Notation rsvector n := (vector RStheta n) (only parsing).

Definition rvector2rsvector := Vmap Rtheta2RStheta.
Definition rsvector2rvector := Vmap RStheta2Rtheta.

Section SvectorBasics.
  Variable fm:Monoid RthetaFlags.

  (* "sparse" vector for CarrierA type elements could be simulated using Rtheta *)
  Definition svector n := (vector (Rtheta' fm) n).

  (* Construct vector of Rtheta values from vector of raw values of it's carrier type *)
  Definition sparsify {n} (v:avector n): svector n :=
    Vmap mkValue v.

  Global Instance sparsify_proper {n:nat}:
    Proper ((=) ==> (=)) (@sparsify n).
  Proof.
    intros x y E.
    unfold sparsify.
    rewrite E.
    reflexivity.
  Qed.

  (* Project out carrier type values from vector of Rheta values *)
  Definition densify {n} (v:svector n): avector n :=
    Vmap (A:=(Rtheta' fm)) (@evalWriter _ _ _) v.

  Global Instance densify_proper {n:nat}:
    Proper ((=) ==> (=)) (@densify n).
  Proof.
    intros x y E.
    unfold densify.
    rewrite E.
    reflexivity.
  Qed.

  (* Construct "Zero svector". All values are structural zeros. *)
  Definition szero_svector n: svector n := Vconst mkSZero n.

  (* "dense" vector means that it does not contain "structural" values *)
  Definition svector_is_dense {n} (v:svector n) : Prop :=
    Vforall (@Is_Val fm)  v.

  Lemma Vnth_sparsify:
    ∀ (n i : nat) (ip : i < n) (v : avector n),
      Vnth (sparsify v) ip ≡ mkValue (Vnth v ip).
  Proof.
    intros n i ip v.
    unfold sparsify.
    apply Vnth_map.
  Qed.

  Fixpoint Vin_Rtheta_Val {n} (v : svector n) (x : CarrierA) : Prop :=
    match v with
    | Vnil => False
    | Vcons y w => (WriterMonadNoT.evalWriter y) = x \/ Vin_Rtheta_Val w x
    end.

  Lemma Vbreak_dense_vector {n1 n2} {x: svector (n1+n2)} {x0 x1}:
    Vbreak x ≡ (x0, x1) ->
    svector_is_dense x ->  (svector_is_dense x0) /\ (svector_is_dense x1).
  Proof.
    unfold svector_is_dense.
    apply Vbreak_preserves_P.
  Qed.

  Lemma szero_svector_all_zeros:
    ∀ n : nat, Vforall Is_ValZero (szero_svector n).
  Proof.
    intros n.
    apply Vforall_nth_intro.
    intros i ip.
    unfold szero_svector.
    rewrite Vnth_const.
    apply SZero_is_ValZero.
  Qed.

  Definition svector_is_collision {n} (v:svector n) :=
    Vexists Is_Collision v.

  Definition svector_is_non_collision {n} (v:svector n) :=
    Vforall Not_Collision v.

  Lemma sparsify_densify_equiv {n} (x:svector n):
    (sparsify (densify x)) = x.
  Proof.
    unfold densify, sparsify.
    rewrite Vmap_map.
    vec_index_equiv i ip.
    rewrite Vnth_map.
    generalize dependent (Vnth x ip). clear ip i.
    intros r.
    apply mkValue_evalWriter.
  Qed.

  Section WithMonoid.
    Variable fml:@MonoidLaws RthetaFlags RthetaFlags_type fm.

    Lemma sparsify_non_coll: forall n (x:avector n),
        svector_is_non_collision (sparsify x).
    Proof.
      intros n x.
      unfold sparsify.
      unfold svector_is_non_collision, Not_Collision, compose.
      apply Vforall_map_intro.
      apply Vforall_intro.
      intros v N.
      unfold mkValue.
      simpl.
      destruct fml.
      rewrite monoid_runit.
      auto.
    Qed.

    Lemma sparsify_is_dense:
      ∀ (i : nat) (x : vector CarrierA i), svector_is_dense (sparsify x).
    Proof.
      intros i x.
      unfold sparsify, svector_is_dense.
      apply Vforall_map_intro.
      apply Vforall_intro.
      intros v N.
      apply Is_Val_mkValue.
    Qed.

    Lemma sparsify_densify {n} (x:svector n):
      svector_is_dense x ->
      svector_is_non_collision x ->
      (sparsify (densify x)) ≡ x.
    Proof.
      intros D N.
      unfold densify, sparsify.
      rewrite Vmap_map.
      apply Vmap_eq_nth.
      intros i ip.
      unfold svector_is_dense in D.
      apply Vforall_nth with (ip:=ip) in D.
      unfold svector_is_non_collision in N.
      apply Vforall_nth with (ip:=ip) in N.
      generalize dependent (Vnth x ip). clear ip i.
      apply mkValue_evalWriter_VNC.
    Qed.

  End WithMonoid.

End SvectorBasics.

Section Union.

  Variable fm:Monoid RthetaFlags.

  Definition Union (dot : CarrierA -> CarrierA -> CarrierA)
    : Rtheta' fm -> Rtheta' fm -> Rtheta' fm := liftM2 dot.

  Lemma Union_comm (dot : CarrierA -> CarrierA -> CarrierA)
        `{C: !Commutative dot}:
    Commutative (Union dot).
  Proof.
    intros x y.
    unfold Union, equiv, Rtheta'_equiv.
    rewrite 2!evalWriter_Rtheta_liftM2.
    apply C.
  Qed.

  Lemma evalWriterUnion {a b: Rtheta' fm} {dot}:
    evalWriter (Union dot a b) =
    dot (evalWriter a)
        (evalWriter b).
  Proof.
    unfold Union.
    rewrite evalWriter_Rtheta_liftM2.
    reflexivity.
  Qed.

  Global Instance Union_proper:
    Proper (((=) ==> (=) ==> (=)) ==> (=) ==> (=) ==> (=)) Union.
  Proof.
    intros dot dot' DP a b H x y E.
    unfold Union, equiv, Rtheta'_equiv in *.
    rewrite 2!evalWriter_Rtheta_liftM2.
    - apply DP.
      + apply H.
      + apply E.
  Qed.

  (** Unary union of vector's elements (left fold) *)
  Definition UnionFold
             {n}
             (dot:CarrierA->CarrierA->CarrierA)
             (initial:CarrierA)
             (v: svector fm n): Rtheta' fm :=
    Vfold_left_rev (Union dot) (mkStruct initial) v.

  (** Pointwise union of two vectors *)
  Definition Vec2Union
             {n}
             (dot:CarrierA->CarrierA->CarrierA)
             (a b: svector fm n): svector fm n
    := Vmap2 (Union dot) a b.

  Global Instance Vec2Union_proper {n}
    :
      Proper (((=) ==> (=) ==> (=)) ==> (=) ==> (=) ==> (=)) (Vec2Union (n:=n)).
  Proof.
    intros dot dot' Ed a a' Ea b b' Eb.
    unfold Vec2Union, Union.
    vec_index_equiv j jc.
    rewrite 2!Vnth_map2.
    unfold_Rtheta_equiv.
    rewrite 2!evalWriter_Rtheta_liftM2.
    apply Ed; apply evalWriter_proper; apply Vnth_arg_equiv; assumption.
  Qed.

  (** Matrix-union. *)
  Definition MUnion'
             {o n}
             (dot:CarrierA->CarrierA->CarrierA)
             (initial:CarrierA)
             (v: vector (svector fm o) n): svector fm o
    :=  Vfold_left_rev (Vec2Union dot) (Vconst (mkStruct initial) o) v.

  Global Instance MUnion'_proper {o n}
    : Proper (((=) ==> (=) ==> (=)) ==> (=) ==> (=) ==> (=)) (@MUnion' o n).
  Proof.
    intros dot dot' Ed one one' Eo x y E.
    unfold MUnion'.
    eapply Vfold_left_rev_proper.
    apply Vec2Union_proper.
    apply Ed.
    rewrite Eo; reflexivity.
    apply E.
  Qed.

  Definition SumUnion
             {o n}
             (v: vector (svector fm o) n): svector fm o
    := MUnion' plus zero v.

  Global Instance SumUnion_proper {o n}
    : Proper ((=) ==> (=)) (@SumUnion o n).
  Proof.
    intros x y E.
    unfold SumUnion.
    rewrite E.
    reflexivity.
  Qed.

  Lemma UnionFold_cons
        m x (xs : svector fm m)
        (dot: CarrierA -> CarrierA -> CarrierA)
        (neutral: CarrierA):
    UnionFold dot neutral (Vcons x xs) ≡ Union dot (UnionFold dot neutral xs) x.
  Proof.
    unfold UnionFold.
    rewrite Vfold_left_rev_cons.
    reflexivity.
  Qed.

  Lemma Vec2Union_comm
        {n}
        (dot: CarrierA -> CarrierA -> CarrierA)
        `{C: !Commutative dot}
    :
      @Commutative (svector fm n) _ (svector fm n) (Vec2Union dot).
  Proof.
    intros a b.
    induction n.
    VOtac; reflexivity.
    VSntac a. VSntac b.
    simpl.
    apply Vcons_proper.
    apply Union_comm, C.
    apply IHn.
  Qed.

  Lemma MUnion'_0
        {o: nat}
        (dot: CarrierA -> CarrierA -> CarrierA)
        (initial: CarrierA)
        (v: vector (svector fm o) 0):
    MUnion' dot initial v ≡ Vconst (mkStruct initial) o.
  Proof.
    dep_destruct v.
    crush.
  Qed.

  Lemma MUnion'_cons {m n}
        (dot: CarrierA -> CarrierA -> CarrierA)
        (neutral: CarrierA)
        (x: svector fm m) (xs: vector (svector fm m) n):
    MUnion' dot neutral (Vcons x xs) ≡ Vec2Union dot (MUnion' dot neutral xs) x.
  Proof.
    unfold MUnion'.
    apply Vfold_left_rev_cons.
  Qed.

  Lemma SumUnion_cons {m n}
        (x: svector fm m) (xs: vector (svector fm m) n):
    SumUnion (Vcons x xs) ≡ Vec2Union plus (SumUnion xs) x.
  Proof.
    unfold SumUnion.
    apply MUnion'_cons.
  Qed.

  Lemma AbsorbUnionIndexBinary
        (m k : nat)
        (kc : k < m)
        {dot}
        (a b : svector fm m):
    Vnth (Vec2Union dot a b) kc ≡ Union dot (Vnth a kc) (Vnth b kc).
  Proof.
    unfold Vec2Union.
    apply Vnth_map2.
  Qed.

  Lemma AbsorbMUnion'Index_Vbuild
        {o n}
        (dot:CarrierA -> CarrierA -> CarrierA)
        (neutral:CarrierA)
        (body: forall (i : nat) (ic : i < n), svector fm o)
        k (kc: k<o)
    :
      Vnth (MUnion' dot neutral (Vbuild body)) kc ≡
           UnionFold dot neutral
           (Vbuild
              (fun (i : nat) (ic : i < n) =>
                 Vnth (body i ic) kc
           )).
  Proof.
    induction n.
    - rewrite 2!Vbuild_0.
      apply Vnth_const.
    -
      rewrite Vbuild_cons.
      rewrite MUnion'_cons.
      rewrite AbsorbUnionIndexBinary.
      rewrite IHn.
      rewrite <- UnionFold_cons.
      rewrite Vbuild_cons.
      reflexivity.
  Qed.

  (** Move indexing from outside of Union into the loop. Called 'union_index' in Vadim's paper notes. *)
  Lemma AbsorbMUnion'Index_Vmap
        (dot: CarrierA -> CarrierA -> CarrierA)
        (neutral: CarrierA)
        {m n:nat}
        (x: vector (svector fm m) n) k (kc: k<m):
    Vnth (MUnion' dot neutral x) kc ≡
         UnionFold dot neutral
         (Vmap (fun v => Vnth v kc) x).
  Proof.
    induction n.
    + dep_destruct x.
      unfold UnionFold, MUnion', szero_svector; simpl.
      rewrite Vnth_const; reflexivity.
    + dep_destruct x.
      rewrite Vmap_cons, MUnion'_cons, AbsorbUnionIndexBinary, IHn, UnionFold_cons.
      reflexivity.
  Qed.

  Lemma AbsorbSumUnionIndex_Vmap
        m n (x: vector (svector fm m) n) k (kc: k<m):
    Vnth (SumUnion x) kc ≡ UnionFold plus zero (Vmap (fun v => Vnth v kc) x).
  Proof.
    unfold SumUnion.
    apply AbsorbMUnion'Index_Vmap.
  Qed.

  Lemma AbsorbISumUnionIndex_Vbuild
        {o n}
        (body: forall (i : nat) (ic : i < n), svector fm o)
        k (kc: k<o)
    :
      Vnth
        (SumUnion (Vbuild body)) kc ≡
        UnionFold plus zero
        (Vbuild
           (fun (i : nat) (ic : i < n) =>
              Vnth (body i ic) kc
        )).
  Proof.
    apply AbsorbMUnion'Index_Vbuild.
  Qed.

  Lemma Union_SZero_r x:
    (Union plus x mkSZero) = x.
  Proof.
    unfold Union.
    unfold_Rtheta_equiv.
    rewrite evalWriter_Rtheta_liftM2.
    rewrite evalWriter_Rtheta_SZero.
    ring.
  Qed.

  Lemma Union_SZero_l x:
    (Union plus mkSZero x) = x.
  Proof.
    unfold Union.
    unfold_Rtheta_equiv.
    rewrite evalWriter_Rtheta_liftM2.
    rewrite evalWriter_Rtheta_SZero.
    ring.
  Qed.

  Lemma Vec2Union_szero_svector_r {n} {a: svector fm n}:
    Vec2Union plus a (szero_svector fm n) = a.
  Proof.
    unfold szero_svector.
    induction n.
    -
      dep_destruct a; reflexivity.
    -
      simpl.
      unfold equiv, vec_Equiv.
      setoid_rewrite IHn.
      dep_destruct a.
      apply Vforall2_cons_eq.
      split.
      +
        rewrite Union_SZero_r.
        reflexivity.
      +
        reflexivity.
  Qed.

  Lemma Vec2Union_szero_svector_l {n} {a: svector fm n}:
    Vec2Union plus (szero_svector fm n) a = a.
  Proof.
    unfold szero_svector.
    induction n.
    dep_destruct a; reflexivity.
    simpl.
    rewrite IHn by (apply Vforall_tl; assumption). clear IHn.
    rewrite Union_SZero_l.
    dep_destruct a.
    reflexivity.
  Qed.

End Union.

Section ExclusiveUnion.

  Lemma UnionCollisionFree (a b : Rtheta) {dot}:
    ¬Is_Collision a →
    ¬Is_Collision b →
    ¬(Is_Val a ∧ Is_Val b)
    → ¬Is_Collision (Union Monoid_RthetaFlags dot a b).
  Proof.
    intros CA CB C.
    unfold Union, Is_Collision, compose.
    rewrite execWriter_Rtheta_liftM2.
    unfold Is_Collision, Is_Val, compose in *.
    destruct (execWriter a) as [str_a col_a].
    destruct (execWriter b) as [str_b col_b].
    unfold RthetaFlagsAppend.
    unfold IsCollision, IsVal in *.
    destr_bool.
    auto.
  Qed.

  (* Conditions under which Union produces value *)
  Lemma ValUnionIsVal (a b : Rtheta) {dot}:
    Is_Val a \/ Is_Val b <-> Is_Val (Union Monoid_RthetaFlags dot a b).
  Proof.
    split.
    - intros [VA | VB]; (
        unfold Union, Is_Val, compose in *;
        rewrite execWriter_Rtheta_liftM2;
        destruct (execWriter a) as [str_a col_a];
        destruct (execWriter b) as [str_b col_b];
        unfold RthetaFlagsAppend;
        unfold IsVal in *;
        destr_bool; auto).
    -
      intros H.
      unfold Union, Is_Val, compose in *.
      rewrite execWriter_Rtheta_liftM2 in H.
      destruct (execWriter a) as [str_a col_a].
      destruct (execWriter b) as [str_b col_b].
      unfold IsVal in *.
      destr_bool; auto.
  Qed.

  (* Conditions under which Union produces struct *)
  Lemma StructUnionIsStruct (a b : Rtheta) {dot}:
    Is_Struct a /\ Is_Struct b <-> Is_Struct (Union Monoid_RthetaFlags dot a b).
  Proof.
    split.
    -
      intros [SA SB].
      unfold Union, Is_Struct, Is_Val, compose in *.
      rewrite execWriter_Rtheta_liftM2.
      destruct (execWriter a) as [str_a col_a].
      destruct (execWriter b) as [str_b col_b].
      unfold RthetaFlagsAppend.
      destr_bool.
    -
      intros H.
      unfold Union, Is_Struct, IsStruct, compose in *.
      rewrite execWriter_Rtheta_liftM2 in H.
      destruct (execWriter a) as [str_a col_a].
      destruct (execWriter b) as [str_b col_b].
      simpl in *.
      unfold RthetaFlagsAppend in H.
      destr_bool; auto.
  Qed.

  Lemma Is_Val_UnionFold {n} {v: rvector n} {dot} {neutral}:
    Vexists Is_Val v <-> Is_Val (UnionFold Monoid_RthetaFlags dot neutral v).
  Proof.
    split.
    - intros H.
      apply Vexists_eq in H.
      unfold UnionFold.
      destruct H as [x [XI XV]].
      induction v.
      + unfold Vin in XI.
        congruence.
      + apply Vin_cons in XI.
        rewrite Vfold_left_rev_cons.
        destruct XI.
        * subst h.
          apply ValUnionIsVal.
          right.
          assumption.
        *
          clear XV.
          apply IHv in H.
          apply ValUnionIsVal.
          left.
          assumption.
    -
      intros H.
      induction v.
      + crush.
      + simpl in *.
        rewrite UnionFold_cons in H.
        apply ValUnionIsVal in H.
        destruct H.
        apply IHv in H.
        right.
        apply H.
        left.
        apply H.
  Qed.

End ExclusiveUnion.


Section NonExclusiveUnion.

  (* Conditions under which Union produces value *)
  Lemma ValUnionIsVal_Safe (a b : RStheta) {dot}:
    Is_Val a \/ Is_Val b <-> Is_Val (Union Monoid_RthetaSafeFlags dot a b).
  Proof.
    split.
    - intros [VA | VB]; (
        unfold Union, Is_Val, compose in *;
        rewrite execWriter_Rtheta_liftM2;
        destruct (execWriter a) as [str_a col_a];
        destruct (execWriter b) as [str_b col_b];
        unfold RthetaFlagsAppend;
        unfold IsVal in *;
        destr_bool; auto).
    -
      intros H.
      unfold Union, Is_Val, compose in *.
      rewrite execWriter_Rtheta_liftM2 in H.
      destruct (execWriter a) as [str_a col_a].
      destruct (execWriter b) as [str_b col_b].
      unfold IsVal in *.
      destr_bool; auto.
  Qed.

  Lemma Is_Val_UnionFold_Safe {n} {v: rsvector n} {dot} {neutral}:
    Vexists Is_Val v <-> Is_Val (UnionFold Monoid_RthetaSafeFlags dot neutral v).
  Proof.
    split.
    - intros H.
      apply Vexists_eq in H.
      unfold UnionFold.
      destruct H as [x [XI XV]].
      induction v.
      + unfold Vin in XI.
        congruence.
      + apply Vin_cons in XI.
        rewrite Vfold_left_rev_cons.
        destruct XI.
        * subst h.
          apply ValUnionIsVal_Safe.
          right.
          assumption.
        *
          clear XV.
          apply IHv in H.
          apply ValUnionIsVal_Safe.
          left.
          assumption.
    -
      intros H.
      induction v.
      + crush.
      + simpl in *.
        rewrite UnionFold_cons in H.
        apply ValUnionIsVal_Safe in H.
        destruct H.
        apply IHv in H.
        right.
        apply H.
        left.
        apply H.
  Qed.

  Lemma UnionCollisionFree_Safe (a b : RStheta) {dot}:
    ¬Is_Collision a →
    ¬Is_Collision b →
    ¬Is_Collision (Union Monoid_RthetaSafeFlags dot a b).
  Proof.
    intros CA CB.
    unfold Union, Is_Collision, compose.
    rewrite execWriter_Rtheta_liftM2.
    unfold Is_Collision, Is_Val, compose in *.
    destruct (execWriter a) as [str_a col_a].
    destruct (execWriter b) as [str_b col_b].
    destr_bool.
  Qed.

End NonExclusiveUnion.

(* RStheta2Rtheta distributes over Union *)
Lemma RStheta2Rtheta_over_Union {f a b}:
  RStheta2Rtheta
    (Union Monoid_RthetaSafeFlags f a b) =
  (Union Monoid_RthetaFlags f (RStheta2Rtheta a) (RStheta2Rtheta b)).
Proof.
  compute.
  reflexivity.
Qed.

(* For the lack of better place ... *)

Require Import ExtLib.Data.Monads.OptionMonad.
Require Import Helix.Util.OptionSetoid.

Global Instance vsequence_option_proper
       {n:nat} {A:Type} `{Ae: Equiv A} `{Aeq: Equivalence A Ae}:
  Proper ((=) ==> (=)) (@vsequence n A option Monad_option).
Proof.
  intros x y E.
  induction n.
  -
    VOtac.
    simpl.
    f_equiv.
  -
    dep_destruct x.
    dep_destruct y.
    simpl.
    inversion E.
    repeat break_match; try some_none_contradiction; auto.
    +
      f_equiv.
      apply Vcons_equiv_intro.
      apply Some_inj_equiv, H.
      specialize (IHn x0 x1 H0).
      rewrite Heqo0 in IHn.
      rewrite Heqo2 in IHn.
      apply Some_inj_equiv, IHn.
    +
      specialize (IHn x0 x1 H0).
      rewrite Heqo0 in IHn.
      rewrite Heqo2 in IHn.
      some_none_contradiction.
    +
      specialize (IHn x0 x1 H0).
      rewrite Heqo0 in IHn.
      rewrite Heqo2 in IHn.
      some_none_contradiction.
Qed.

Close Scope vector_scope.
Close Scope nat_scope.

