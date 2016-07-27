(* Coq defintions for Sigma-HCOL operator language *)

Require Import VecUtil.
Require Import VecSetoid.
Require Import Spiral.
Require Import Rtheta.
Require Import SVector.
Require Import IndexFunctions.
Require Import HCOL. (* Presently for HOperator only. Consider moving it elsewhere *)

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.BoolEq.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Require Import CpdtTactics.
Require Import JRWTactics.
Require Import SpiralTactics.
Require Import Psatz.
Require Import Omega.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.theory.rings.
Require Import MathClasses.implementations.peano_naturals.
Require Import MathClasses.orders.orders.
Require Import MathClasses.theory.setoids.

(* Ext Lib *)
Require Import ExtLib.Structures.Monad.

(*  CoLoR *)
Require Import CoLoR.Util.Vector.VecUtil.
Import VectorNotations.
Open Scope vector_scope.

Global Open Scope nat_scope.

(* Returns an element of the vector 'x' which is result of mapping of given
natrual number by index mapping function f_spec. *)
Definition VnthIndexMapped
           {i o:nat}
           (x: svector i)
           (f: index_map o i)
           (n:nat) (np: n<o)
  : Rtheta
  := Vnth x (« f » n np).

Section SigmaHCOL_Operators.

  Class SHOperator {i o:nat} (op: svector i -> svector o) :=
    SHOperator_setoidmor :> Setoid_Morphism op.

  Lemma SHOperator_functional_extensionality
        {m n: nat}
        `{SHOperator m n f}
        `{SHOperator m n g}:
    (∀ v, f v = g v) -> f = g.
  Proof.
    unfold SHOperator in *.
    apply ext_equiv_applied_iff.
  Qed.

  Definition Gather
             {i o: nat}
             (f: index_map o i)
             (x: svector i):
    svector o
    := Vbuild (VnthIndexMapped x f).

  Global Instance SHOperator_Gather
         {i o: nat}
         (f: index_map o i):
    SHOperator (Gather f).
  Proof.
    unfold SHOperator.
    split; repeat apply vec_Setoid.
    intros x y E.
    unfold Gather.
    unfold VnthIndexMapped.
    unfold equiv, vec_Equiv.
    apply Vforall2_intro_nth; intros j jp.
    rewrite 2!Vbuild_nth.
    apply Vnth_arg_equiv.
    rewrite E.
    reflexivity.
  Qed.

  Definition GathH
             {i o}
             (base stride: nat)
             {domain_bound: ∀ x : nat, x < o → base + x * stride < i}
    :
      (svector i) -> svector o
    :=
      Gather (h_index_map base stride
                          (range_bound:=domain_bound) (* since we swap domain and range, domain bound becomes range boud *)
             ).

  Global Instance SHOperator_GathH
         {i o}
         (base stride: nat)
         {domain_bound: ∀ x : nat, x < o → base + x * stride < i}:
    SHOperator (@GathH i o base stride domain_bound).
  Proof.
    apply SHOperator_Gather.
  Qed.

  Definition Scatter
             {i o: nat}
             (f: index_map i o)
             {f_inj: index_map_injective f}
             (x: svector i) : svector o
    :=
      let f' := build_inverse_index_map f in
      Vbuild (fun n np =>
                match decide (in_range f n) with
                | left r => Vnth x (inverse_index_f_spec f f' n r)
                | right _ => mkSZero
                end).

  Global Instance SHOperator_Scatter
         {i o: nat}
         (f: index_map i o)
         {f_inj: index_map_injective f}:
    SHOperator (@Scatter i o f f_inj).
  Proof.
    unfold SHOperator.
    split; try apply vec_Setoid.
    intros x y E.
    unfold Scatter.
    unfold equiv, vec_Equiv.
    apply Vforall2_intro_nth.
    intros j jp.
    rewrite 2!Vbuild_nth.
    simpl.
    break_match.
    simpl.
    apply Vnth_arg_equiv, E.
    reflexivity.
  Qed.

  Definition ScatH
             {i o}
             (base stride: nat)
             {range_bound: ∀ x : nat, x < i → base + x * stride < o}
             {snzord0: stride ≢ 0 \/ i < 2}
    :
      (svector i) -> svector o
    :=
      Scatter (h_index_map base stride (range_bound:=range_bound))
              (f_inj := h_index_map_is_injective base stride (snzord0:=snzord0)).

  Global Instance SHOperator_ScatH
         {i o}
         (base stride: nat)
         {range_bound: ∀ x : nat, x < i → base + x * stride < o}
         {snzord0: stride ≢ 0 \/ i < 2}:
    SHOperator (@ScatH i o base stride range_bound snzord0).
  Proof.
    apply SHOperator_Scatter.
  Qed.

  Global Instance SHOperator_compose
         {i1 o2 o3}
         (op1: svector o2 -> svector o3)
         `{S1:!SHOperator op1}
         (op2: svector i1 -> svector o2)
         `{S2: !SHOperator op2}:
    SHOperator (op1 ∘ op2).
  Proof.
    unfold SHOperator in *.
    split; try apply vec_Setoid.
    intros x y Exy.
    unfold compose.
    destruct S1, S2.
    auto.
  Qed.

  (* Sigma-HCOL version of HPointwise. We could not just (liftM_Hoperator HPointwise) but we want to preserve structural flags. *)
  Definition SHPointwise
             {n: nat}
             (f: { i | i<n} -> CarrierA -> CarrierA)
             `{pF: !Proper ((=) ==> (=) ==> (=)) f}
             (x: svector n): svector n
    := Vbuild (fun j jd => liftM (f (j ↾ jd)) (Vnth x jd)).

  Global Instance SHOperator_SHPointwise
         {n: nat}
         (f: { i | i<n} -> CarrierA -> CarrierA)
         `{pF: !Proper ((=) ==> (=) ==> (=)) f}:
    SHOperator (SHPointwise f).
  Proof.
    split; try apply vec_Setoid.
    intros x y E.
    unfold SHPointwise.
    unfold equiv, vec_Equiv.
    apply Vforall2_intro_nth.
    intros j jc.
    rewrite 2!Vbuild_nth.

    unfold_Rtheta_equiv.
    rewrite 2!evalWriter_Rtheta_liftM.

    f_equiv.
    apply evalWriter_proper.
    apply Vnth_arg_equiv.
    apply E.
  Qed.

  Definition SHBinOp {o}
             (f: nat -> CarrierA -> CarrierA -> CarrierA)
             `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
             (v:svector (o+o)): svector o
    :=  match (vector2pair o v) with
        | (a,b) => Vbuild (fun i ip => liftM2 (f i) (Vnth a ip) (Vnth b ip))
        end.

  Global Instance SHOperator_SHBinOp {o}
         (f: nat -> CarrierA -> CarrierA -> CarrierA)
         `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}:
    SHOperator (@SHBinOp o f pF).
  Proof.
    split; try apply vec_Setoid.

    intros x y E.
    unfold SHBinOp.
    unfold equiv, vec_Equiv.
    apply Vforall2_intro_nth.
    intros j jc.
    unfold vector2pair.


    repeat break_let.

    replace t with (fst (Vbreak x)) by crush.
    replace t0 with (snd (Vbreak x)) by crush.
    replace t1 with (fst (Vbreak y)) by crush.
    replace t2 with (snd (Vbreak y)) by crush.
    clear Heqp Heqp0.

    rewrite 2!Vbuild_nth.

    unfold_Rtheta_equiv.
    rewrite 2!evalWriter_Rtheta_liftM2.

    f_equiv.
    - apply evalWriter_proper.
      apply Vnth_arg_equiv.
      rewrite E.
      reflexivity.
    - apply evalWriter_proper.
      apply Vnth_arg_equiv.
      rewrite E.
      reflexivity.
  Qed.

End SigmaHCOL_Operators.

Definition liftM_HOperator
           {i o}
           (op: avector i -> avector o)
  : svector i -> svector o :=
  sparsify ∘ op ∘ densify.

Global Instance SHOperator_liftM_HOperator
       {i o}
       (op: avector i -> avector o)
       `{hop: !HOperator op}
  : SHOperator (liftM_HOperator op).
Proof.
  unfold SHOperator.
  split; try apply vec_Setoid.
  intros x y Exy.
  unfold liftM_HOperator, compose.
  unfold sparsify, densify.
  rewrite Exy.
  reflexivity.
Qed.

Definition SparseEmbedding
           {i o ki ko}
           (kernel: avector ki -> avector ko)
           (f: index_map ko o)
           {f_inj : index_map_injective f}
           (g: index_map ki i)
           `{Koperator: @HOperator ki ko kernel}
           (x: svector i)
  :=
    (Scatter f (f_inj:=f_inj)
             ∘ (liftM_HOperator kernel)
             ∘ (Gather g)) x.

Global Instance SHOperator_SparseEmbedding
       {i o ki ko}
       (kernel: avector ki -> avector ko)
       (f: index_map ko o)
       {f_inj : index_map_injective f}
       (g: index_map ki i)
       `{Koperator: @HOperator ki ko kernel}:
  SHOperator (@SparseEmbedding
                i o ki ko
                kernel
                f
                f_inj
                g
                Koperator).
Proof.
  unfold SHOperator.
  split; repeat apply vec_Setoid.
  intros x y E.
  unfold SparseEmbedding.
  rewrite E.
  reflexivity.
Qed.

Definition USparseEmbedding
           {n i o ki ko}
           (kernel: forall k, (k<n) -> avector ki -> avector ko)
           (f: index_map_family ko o n)
           {f_inj : index_map_family_injective f}
           (g: index_map_family ki i n)
           `{Koperator: forall k (kc: k<n), @HOperator ki ko (kernel k kc)}
           (x: svector i)
  :=
    (SumUnion
       (Vbuild
          (λ (j:nat) (jc:j<n),
           SparseEmbedding
             (f_inj:=index_map_family_member_injective f_inj j jc)
             (kernel j jc)
             ( ⦃f⦄ j jc)
             ( ⦃g⦄ j jc)
             x
    ))).

Global Instance SHOperator_USparseEmbedding
       {n i o ki ko}
       (kernel: forall k, (k<n) -> avector ki -> avector ko)
       (f: index_map_family ko o n)
       {f_inj : index_map_family_injective f}
       (g: index_map_family ki i n)
       `{Koperator: forall k (kc: k<n), @HOperator ki ko (kernel k kc)}:
  SHOperator (@USparseEmbedding
                n i o ki ko
                kernel
                f f_inj
                g
                Koperator).
Proof.
  unfold SHOperator.
  split; repeat apply vec_Setoid.
  intros x y E.
  unfold USparseEmbedding.
  apply ext_equiv_applied_iff'.
  split; repeat apply vec_Setoid.
  apply SumUnion_proper.
  split; repeat apply vec_Setoid.
  apply SumUnion_proper.
  reflexivity.

  unfold equiv, vec_Equiv.
  apply Vforall2_intro_nth.
  intros j jc.
  rewrite 2!Vbuild_nth.
  rewrite E.
  reflexivity.
Qed.


Section OperatorProperies.
  (* Specification of gather as mapping from output to input. NOTE:
    we are using definitional equality here, as Scatter does not
    perform any operations on elements of type A *)
  Lemma Gather_spec
        {i o: nat}
        (f: index_map o i)
        (x: svector i):
    ∀ n (ip : n < o), Vnth (Gather f x) ip ≡ VnthIndexMapped x f n ip.
  Proof.
    unfold Gather, Vbuild.
    destruct (Vbuild_spec (VnthIndexMapped x f)) as [Vv Vs].
    simpl.
    intros.
    subst.
    auto.
  Qed.

  (* Index-function based condition under which Gather output is dense *)
  Lemma Gather_dense_constr (i ki : nat)
        (g: index_map ki i)
        (x: svector i)
        (g_dense: forall k (kc:k<ki), Is_Val (Vnth x («g» k kc))):
    Vforall Is_Val (Gather g x).
  Proof.
    apply Vforall_nth_intro.
    intros i0 ip.
    rewrite Gather_spec.
    apply g_dense.
  Qed.

  Lemma Gather_is_endomorphism:
    ∀ (i o : nat)
      (x : svector i),
    ∀ (f: index_map o i),
      Vforall (Vin_aux x)
              (Gather f x).
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

  Lemma Gather_preserves_P:
    ∀ (i o : nat) (x : svector i) (P: Rtheta -> Prop),
      Vforall P x
      → ∀ f : index_map o i,
        Vforall P (Gather f x).
  Proof.
    intros.
    assert(Vforall (Vin_aux x) (Gather f x))
      by apply Gather_is_endomorphism.
    generalize dependent (Gather f x).
    intros t.
    rewrite 2!Vforall_eq.
    crush.
    assert (Vin_aux x x0) by (apply H0; assumption).
    rewrite Vforall_eq in H.
    crush.
  Qed.

  Lemma Gather_preserves_density:
    ∀ (i o : nat) (x : svector i)
      (f: index_map o i),
      svector_is_dense x ->
      svector_is_dense (Gather f x).
  Proof.
    intros.
    unfold svector_is_dense in *.
    apply Gather_preserves_P.
    assumption.
  Qed.

  (* Specification of scatter as mapping from input to output. NOTE:
    we are using definitional equality here, as Scatter does not
    perform any operations on elements of type A *)
  Lemma Scatter_spec
        {i o: nat}
        (f: index_map i o)
        {f_inj: index_map_injective f}
        (x: svector i)
        (n: nat) (ip : n < i):
    Vnth x ip ≡ VnthIndexMapped (Scatter f (f_inj:=f_inj) x) f n ip.
  Proof.
    unfold VnthIndexMapped.
    unfold Scatter.
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

  Lemma Scatter_is_almost_endomorphism
        (i o : nat)
        (x : svector i)
        (f: index_map i o)
        {f_inj : index_map_injective f}:
    Vforall (fun p => (Vin p x) \/ (p ≡ mkSZero))
            (Scatter f (f_inj:=f_inj) x).
  Proof.
    apply Vforall_nth_intro.
    intros j jp.
    unfold Scatter.
    rewrite Vbuild_nth.
    simpl.
    break_match.
    - left.
      apply Vnth_in.
    - right.
      reflexivity.
  Qed.

  Lemma SHPointwise_nth
        {n: nat}
        (f: { i | i<n} -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}
        {j:nat} {jc:j<n}
        (v: svector n):
    Vnth (SHPointwise f v) jc =   mkValue (f (j ↾ jc) (WriterMonadNoT.evalWriter (Vnth v jc))).
  Proof.
    unfold SHPointwise.
    rewrite Vbuild_nth.
    generalize (Vnth v jc) as x. intros x. clear v.
    rewrite <- evalWriter_Rtheta_liftM.
    rewrite mkValue_evalWriter.
    reflexivity.
  Qed.

  Lemma SHPointwise_equiv_lifted_HPointwise
        {n: nat}
        (f: { i | i<n} -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}:
    SHPointwise f = liftM_HOperator (@HPointwise n f pF).
  Proof.
    apply ext_equiv_applied_iff'; try typeclasses eauto.
    intros x.

    unfold equiv, vec_Equiv.
    apply Vforall2_intro_nth.
    intros j jc.
    rewrite SHPointwise_nth.

    unfold liftM_HOperator.
    unfold compose.
    unfold sparsify; rewrite Vnth_map.
    rewrite HPointwise_nth.
    unfold densify; rewrite Vnth_map.
    reflexivity.
  Qed.

End OperatorProperies.

Section StructuralProperies.
  (* Strong condition: operator preserves vectors' density *)
  Class DensityPreserving {i o:nat} (op: svector i -> svector o) :=
    o_den_pres : forall x, svector_is_dense x -> svector_is_dense (op x).

  (* All lifted HOperators are naturally density preserving *)
  Instance liftM_HOperator_DensityPreserving
           {i o}
           (op: avector i -> avector o)
           `{hop: !HOperator op}
    : DensityPreserving (liftM_HOperator op).
  Proof.
    unfold DensityPreserving.
    intros x D.

    unfold liftM_HOperator, compose.
    generalize (op (densify x)) as y. intros y.
    unfold svector_is_dense, sparsify.
    apply Vforall_map_intro.
    apply Vforall_nth_intro.
    intros i0 ip.
    apply IsVal_mkValue.
  Qed.


  (* Weaker condition: applied to a dense vector without collisions does not produce strucural collisions *)
  Class DenseCauseNoCol {i o:nat} (op: svector i -> svector o) :=
    o_den_non_col : forall x,
      svector_is_dense x ->
      svector_is_non_collision x ->
      svector_is_non_collision (op x).

  Instance liftM_HOperator_DenseCauseNoCol
           {i o}
           (op: avector i -> avector o)
           `{hop: !HOperator op}
    : DenseCauseNoCol (liftM_HOperator op).
  Proof.
    unfold DenseCauseNoCol.
    intros x D NC.
    unfold liftM_HOperator, compose.
    apply sparsify_non_coll.
  Qed.

  (* Applying Scatter to collision-free vector, using injective family of functions will not cause any collisions *)
  Lemma ScatterCollisionFree
        {i o}
        (f: index_map i o)
        {f_inj: index_map_injective f}
        (x: svector i)
        (Xcf: svector_is_non_collision x)
    :
      svector_is_non_collision (@Scatter i o f f_inj x).
  Proof.
    unfold svector_is_non_collision, Not_Collision in *.
    apply Vforall_nth_intro.
    intros j jp.
    unfold Is_Collision in *.

    assert(E: Vforall
                (fun p => (Vin p x) \/ (p ≡ mkSZero))
                (Scatter f (f_inj:=f_inj) x)) by
        apply Scatter_is_almost_endomorphism.

    apply Vforall_nth with (ip:=jp) in E.

    generalize dependent (Vnth (Scatter f (f_inj:=f_inj) x) jp).
    intros v E.
    destruct E.
    -
      unfold svector_is_non_collision in Xcf.
      apply Vforall_in with (v:=x); assumption.
    -
      rewrite_clear H.
      auto.
  Qed.

  Lemma GatherCollisionFree
        {i o: nat}
        (x: svector i)
        (Xcf: svector_is_non_collision x)
    :
      forall f, svector_is_non_collision (@Gather i o f x).
  Proof.
    apply Gather_preserves_P, Xcf.
  Qed.

  Lemma USparseEmbeddingIsDense
        {n i o ki ko}
        (kernel: forall k, (k<n) -> avector ki -> avector ko)
        (f: index_map_family ko o n)
        {f_inj: index_map_family_injective f} (* gives non-col *)
        {f_sur: index_map_family_surjective f} (* gives density *)
        (g: index_map_family ki i n)
        `{Koperator: forall k (kc: k<n), @HOperator ki ko (kernel k kc)}
        (x: svector i)
        {nz: n ≢ 0}
    :
      (forall j (jc:j<n) k (kc:k<ki), Is_Val (Vnth x («⦃g⦄ j jc» k kc))) ->
      svector_is_dense
        (@USparseEmbedding n i o ki ko kernel f f_inj g Koperator x).
  Proof.
    intros g_dense.
    apply Vforall_nth_intro.
    intros oi oic.
    unfold compose.
    unfold USparseEmbedding, SparseEmbedding.
    rewrite AbsorbIUnionIndex.
    unfold compose.
    destruct n.
    - congruence.
    - clear nz.
      apply Is_Val_VecUnion.
      apply Vexists_Vbuild.
      unfold index_map_family_surjective in f_sur.
      specialize (f_sur oi oic).
      destruct f_sur as [z [p [zc [pc F]]]].
      exists p, pc.

      assert(Vforall Is_Val (Gather (⦃g ⦄ p pc) x))
        by apply Gather_dense_constr, g_dense.
      generalize dependent (Gather (⦃g ⦄ p pc) x).
      intros gx GD.
      clear g_dense g.

      assert(Vforall Is_Val (liftM_HOperator (kernel p pc) gx)).
      {
        apply liftM_HOperator_DensityPreserving.
        apply Koperator.
        apply GD.
      }

      generalize dependent (liftM_HOperator (kernel p pc) gx).
      intros kx KD.
      clear GD gx Koperator kernel.

      unfold Scatter; rewrite Vbuild_nth.


      apply index_map_family_member_injective with (jc:=pc) in f_inj.
      generalize dependent (⦃f ⦄ p pc). intros fp fp_inj F.
      clear f.
      break_match.
      apply Vforall_nth, KD.
      subst oi.
      absurd (in_range fp (⟦ fp ⟧ z)).
      + assumption.
      + apply in_range_by_def, zc.
  Qed.

  (* Pre-condition for VecUnion not causing any collisions *)
  Lemma Not_Collision_VecUnion
        {n}
        {v: svector n}
    :
      Vforall Not_Collision v -> Vunique Is_Val v -> Not_Collision (VecUnion v).
  Proof.
    intros VNC H.
    dependent induction n.
    + dep_destruct v.
      compute.
      trivial.
    +
      dep_destruct v.
      rewrite VecUnion_cons.
      simpl in VNC. destruct VNC as [VNCh VNCx].
      apply UnionCollisionFree.
      *
        apply IHn.
        -- apply VNCx.
        -- clear IHn.
           apply Vunique_cons_tail in H.
           apply H.
      * apply VNCh.
      * cut(¬(Is_Val (VecUnion x)) \/ (¬ (Is_Val h))).
        firstorder.
        assert(D: Decision (Is_Val h)) by apply Is_Val_dec.
        destruct D as [Ph | Phn].
        -- left.
           clear VNCh VNCx IHn.

           unfold not. intros H0.
           apply Is_Val_VecUnion in H0.
           apply Vexists_eq in H0.
           destruct H0 as [x0 [V1 V2]].
           apply Vin_nth in V1.
           destruct V1 as [i [ip Vx]].
           subst x0.

           unfold Vunique in H.
           assert(jc: 0 < S n) by omega.
           assert(ip': S i < S n) by omega.
           specialize (H 0 jc (S i) ip').
           simpl (Vnth (Vcons h x) jc) in H.
           simpl (Vnth (Vcons h x) ip') in H.
           replace (lt_S_n ip') with ip in H by apply proof_irrelevance.
           assert(H1: Is_Val h ∧ Is_Val (Vnth x ip)) by auto.
           apply H in H1.
           congruence.
        -- right.
           apply Phn.
  Qed.

  (* TODO: maybe iff  *)
  Lemma Is_Val_Scatter
        {m n: nat}
        (f: index_map m n)
        {f_inj: index_map_injective f}
        (x: svector m)
        (XD: svector_is_dense x)
        (j: nat) (jc : j < n):
    Is_Val (Vnth (Scatter f (f_inj:=f_inj) x) jc) ->
    (exists i (ic:i<m), ⟦f⟧ i ≡ j).
  Proof.
    intros H.
    unfold svector_is_dense in XD.
    unfold Scatter in H. rewrite Vbuild_nth in H.
    break_match.
    simpl in *.
    -
      generalize dependent (gen_inverse_index_f_spec f j i); intros f_spec H.
      exists (gen_inverse_index_f f j), f_spec.
      apply build_inverse_index_map_is_right_inverse; auto.
    -
      apply Is_Val_mkStruct in H.
      inversion H. (* for some reason congruence fails *)
  Qed.

  Lemma USparseEmbeddingCauseNoCol
        {n i o ki ko}
        (kernel: forall k, (k<n) -> avector ki -> avector ko)
        (f: index_map_family ko o n)
        {f_inj: index_map_family_injective f} (* gives non-col *)
        {f_sur: index_map_family_surjective f} (* gives density *)
        (g: index_map_family ki i n)
        `{Koperator: forall k (kc: k<n), @HOperator ki ko (kernel k kc)}
        (x: svector i)
        {nz: n ≢ 0}
    :
      (forall j (jc:j<n) k (kc:k<ki), Is_Val (Vnth x («⦃g⦄ j jc» k kc))) ->
      (forall j (jc:j<n) k (kc:k<ki), Not_Collision (Vnth x («⦃g⦄ j jc» k kc))) ->
      svector_is_non_collision
        (@USparseEmbedding n i o ki ko kernel f f_inj g Koperator x).
  Proof.
    intros g_dense GNC.
    apply Vforall_nth_intro.
    intros oi oic.
    unfold compose.
    unfold USparseEmbedding, SparseEmbedding.
    rewrite AbsorbIUnionIndex.


    destruct n.
    - congruence.
    - (* driving towards apply Not_Collision_VecUnion. *)
      apply Not_Collision_VecUnion.
      +
        clear nz.
        apply Vforall_Vbuild.
        intros j jn.
        unfold compose.
        specialize (GNC j jn).

        (* Get rid of Gather, carring over its properties *)
        assert(GXD: svector_is_dense (Gather (⦃ g ⦄ j jn) x)).
        {
          unfold svector_is_dense.
          apply Vforall_nth_intro.
          intros.
          rewrite Gather_spec.
          apply g_dense.
        }

        assert(GXNC: svector_is_non_collision (Gather (⦃ g ⦄ j jn) x)).
        {
          unfold svector_is_non_collision.
          apply Vforall_nth_intro.
          intros.
          rewrite Gather_spec.
          apply GNC.
        }
        generalize dependent (Gather (⦃ g ⦄ j jn) x).
        intros gx GXD GXNC.
        clear GNC g_dense.

        (* Get rid of lifted kernel, carring over its properties *)
        assert(LD: svector_is_dense (liftM_HOperator (kernel j jn) gx)).
        {
          apply liftM_HOperator_DensityPreserving.
          apply Koperator.
          apply GXD.
        }

        assert(KNC: svector_is_non_collision (liftM_HOperator (kernel j jn) gx)).
        {
          apply liftM_HOperator_DenseCauseNoCol, GXNC.
          apply Koperator.
          apply GXD.
        }
        generalize dependent (liftM_HOperator (kernel j jn) gx).
        intros kx KD KNC.
        clear GXD GXNC gx.

        (* Get rid of Scatter  *)
        assert(SNC: svector_is_non_collision (@Scatter ko o (family_f ko o (S n) f j jn)
                                                       (@index_map_family_member_injective ko o (S n) f f_inj j jn) kx)).

        apply ScatterCollisionFree, KNC.
        generalize dependent (@Scatter ko o (family_f ko o (S n) f j jn)
                                       (@index_map_family_member_injective ko o (S n) f f_inj j jn) kx).
        intros sx SNC.
        unfold svector_is_non_collision in SNC.
        apply Vforall_nth with (ip:=oic) in SNC.
        apply SNC.
      +
        unfold Vunique.
        intros i0 ic j jc.

        rewrite 2!Vbuild_nth.
        unfold compose.

        (* Get rid of Gather, carring over its properties *)
        assert(GXDi0: svector_is_dense (Gather (⦃ g ⦄ i0 ic) x)).
        {
          unfold svector_is_dense.
          apply Vforall_nth_intro.
          intros.
          rewrite Gather_spec.
          apply g_dense.
        }
        generalize dependent (Gather (⦃ g ⦄ i0 ic) x).
        intros gxi0 GXDi0.

        assert(GXDj: svector_is_dense (Gather (⦃ g ⦄ j jc) x)).
        {
          unfold svector_is_dense.
          apply Vforall_nth_intro.
          intros.
          rewrite Gather_spec.
          apply g_dense.
        }
        generalize dependent (Gather (⦃ g ⦄ j jc) x).
        intros gxj GXDj.
        clear GNC g_dense.

        (* Get rid of lifted kernel, carring over its properties *)
        assert(svector_is_dense (@liftM_HOperator ki ko (kernel i0 ic) gxi0)).
        {
          apply liftM_HOperator_DensityPreserving.
          apply Koperator.
          apply GXDi0.
        }
        generalize dependent (@liftM_HOperator ki ko (kernel i0 ic) gxi0).
        intros kxi KXDi0.
        clear gxi0 GXDi0.

        assert (svector_is_dense (@liftM_HOperator ki ko (kernel j jc) gxj)).
        {
          apply liftM_HOperator_DensityPreserving.
          apply Koperator.
          apply GXDj.
        }
        generalize dependent (@liftM_HOperator ki ko (kernel j jc) gxj).
        intros kxj KXDj.
        clear gxj GXDj.


        (* housekeeping *)
        clear Koperator g kernel nz x i ki f_sur.
        rename
          i0 into i,
        n into k,
        kxi into x,
        o into n,
        oi into m,
        oic into mc,
        kxj into y,
        KXDj into YD,
        KXDi0 into XD,
        ko into l.

        intros [Hi Hj].

        apply Is_Val_Scatter in Hi; try assumption; clear XD.
        apply Is_Val_Scatter in Hj; try assumption; clear YD.

        elim Hi; clear Hi; intros x0 H.
        elim H; clear H; intros x0c H0.

        elim Hj; clear Hj; intros x1 H.
        elim H; clear H; intros x1c H1.

        subst m;  clear mc.

        unfold index_map_family_injective in f_inj.
        symmetry in H1.
        specialize (f_inj i j ic jc x0 x1 x0c x1c H1).

        apply f_inj.
  Qed.


End StructuralProperies.
