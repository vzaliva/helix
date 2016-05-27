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
Require Import CaseNaming.
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

Definition VnthInverseIndexMapped
           {i o:nat}
           (x: svector i)
           (f': partial_index_map o i)
           (n:nat) (np: n<o)
  : Rtheta
  :=
    let f := partial_index_f _ _ f' in
    let f_spec := partial_index_f_spec _ _  f' in
    match (f n) as fn return f n ≡ fn -> Rtheta with
    | None => fun _ => mkSZero
    | Some z => fun p => Vnth x (f_spec n np z p)
    end eq_refl.

Lemma VnthInverseIndexMapped_arg_equiv:
  ∀ (i o : nat)
    (x y : svector i) (j : nat)
    (jp : j < o)
    (f' : partial_index_map o i),
    x = y
    → VnthInverseIndexMapped x f' j jp = VnthInverseIndexMapped y f' j jp.
Proof.
  intros i o x y j jp f' H.
  destruct f'.
  unfold VnthInverseIndexMapped; simpl.
  generalize (partial_index_f_spec j jp).
  destruct (partial_index_f j); intros.
  apply Vnth_arg_equiv; assumption.
  reflexivity.
Qed.

Lemma Vin_VnthInverseIndexMapped
      (i o : nat)
      (x : vector Rtheta i)
      (f : partial_index_map o i)
      (j : nat) (jp : j < o):
  Vin (VnthInverseIndexMapped x f j jp) x
  ∨ VnthInverseIndexMapped x f j jp ≡ mkSZero.
Proof.
  unfold VnthInverseIndexMapped, partial_index_f.
  break_let.
  simpl in *.
  clear Heqp f.
  generalize (partial_index_f_spec j jp).
  intros l.
  destruct (partial_index_f j).
  - left.
    apply Vnth_in.
  - right.
    reflexivity.
Qed.


Section SigmaHCOL_Operators.

  Class SHOperator {i o:nat} (op: svector i -> svector o) :=
    o_setoidmor :> Setoid_Morphism op.

  Lemma SHOperator_functional_extensionality
        {m n: nat}
        `{SHOperator m n f}
        `{SHOperator m n g}:
    (∀ v, f v = g v) -> f = g.
  Proof.
    unfold SHOperator in *.
    apply ext_equiv_applied_iff.
  Qed.

  (* Per Vadim's discussion with Franz on 2015-12-14, ISumUnion is
  just Union of two vectors, produced by application of two operators
  to the input. In general HTSUMUnion is not an SHOperator, since Union is
  not Proper wrt equiv. (TODO: maybe not true anymore) *)
  Definition HTSUMUnion {i o}
             (f: svector i -> svector o)
             (g: svector i -> svector o)
             (x: svector i): svector o
    :=  Vec2Union (f x) (g x).

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
      Vbuild (fun n np =>
                VnthInverseIndexMapped x (build_inverse_index_map f) n np).

  Section ExperimenalNewScatter.

    (* Restriction on domain *)
    Definition shrink_index_map_domain {d r:nat} (f: index_map (S d) r)
    : index_map d r.
    Proof.
      destruct f.
      assert (new_spec : ∀ x : nat, x < d → index_f x < r) by auto.
      exact (IndexMap d r index_f new_spec).
    Defined.

    Definition in_range'
               {d r:nat} (f: index_map d r)
               (i:nat)
      : Prop.
    Proof.
      induction d.
      exact False.
      destruct (Nat.eq_dec (⟦ f ⟧ d) i).
      exact True.
      apply IHd, shrink_index_map_domain, f.
    Defined.

    Fixpoint in_range  {d r:nat} (f: index_map d r)
             (i:nat)
      : Prop :=
      match d return (index_map d r) -> Prop with
      | O => fun _ => False
      | S d' => fun f' =>
                 match Nat.eq_dec (⟦f⟧ d') i with
                 | left x => True
                 | right x => in_range (shrink_index_map_domain f') i
                 end
      end f.

    (* Prove that our 2 implementatoins of in_range are compatible *)
    Lemma in_range_compat  {d r:nat} (f: index_map d r):
      in_range' f ≡ in_range f.
    Proof.
      extensionality i.
      induction d.
      - crush.
      -
        unfold in_range.
        rewrite <- IHd.
        break_if.
        + simpl.
          break_if.
          trivial.
          congruence.
        + simpl.
          break_if.
          congruence.
          rewrite IHd.
          reflexivity.
    Qed.

    Global Instance in_range_dec {d r:nat} (f: index_map d r) (i:nat) : Decision (in_range f i).
    Proof.
      unfold Decision.
      induction d.
      crush.
      simpl.
      break_if.
      auto.
      apply IHd.
    Qed.

    Record inverse_index_map {d r: nat} (f: index_map d r)
      :=
        InverseIndexMap {
            inverse_index_f : nat -> nat;
            inverse_index_f_spec: forall x, in_range f x -> ((inverse_index_f x) < d)
          }.

    Fixpoint gen_inverse_index_f {d r: nat} (f: index_map d r)
             (i: nat): nat :=
      let dummy := O in
      match d return (index_map d r) -> nat with
      | O => fun _ => dummy
      | S d' => fun f' =>
                 match Nat.eq_dec (⟦f⟧ d') i with
                 | left x => d'
                 | right x => gen_inverse_index_f (shrink_index_map_domain f') i
                 end
      end f.

    Definition gen_inverse_index_f_spec {d r: nat} (f: index_map d r):
      forall (i: nat), in_range f i -> (gen_inverse_index_f f i) < d.
    Proof.
      intros x R.
      induction d.
      - crush.
      -
        simpl.
        break_if.
        crush.
        rewrite IHd.
        crush.
        unfold in_range in R.
        break_if.
        congruence.
        apply R.
    Defined.

    Definition build_inverse_index_map
               {d r: nat}
               (f: index_map d r)
      : inverse_index_map f
      := let f' := gen_inverse_index_f f in
         @InverseIndexMap d r f f' (gen_inverse_index_f_spec f).

    Definition inverse_index_map_injective
               {d r: nat} {f: index_map d r}
               (f': inverse_index_map f)
      :=
        let f0 := inverse_index_f f f' in
        forall x y v, in_range f x -> in_range f y ->
          (f0 x ≡ v /\ f0 y ≡ v) → x ≡ y.

    Definition inverse_index_map_surjective
               {d r: nat} {f: index_map d r}
               (f': inverse_index_map f)
      :=
        let f0 := inverse_index_f f f' in
        forall (y:nat) (yc: y<d), exists x, in_range f x /\ f0 x ≡ y.

    Definition inverse_index_map_bijective
               {d r: nat} {f: index_map d r}
               (f': inverse_index_map f)
      :=
        (inverse_index_map_injective f') /\ (inverse_index_map_surjective f').

    Lemma shrink_index_map_preserves_injectivity:
      ∀ (d r : nat) (f : index_map (S d) r),
        index_map_injective f → index_map_injective (shrink_index_map_domain f).
    Proof.
      intros d r f f_inj.
      unfold index_map_injective.
      intros x y xc yc H.
      apply f_inj; try auto.
      unfold shrink_index_map_domain in *.
      break_match.
      simpl in *.
      assumption.
    Qed.

    (* The following lemma proves that using `buld_inverse_index_map` on
  injective index_map produces true "left inverse" of it *)
    Lemma build_inverse_index_map_is_left_inverse
          {d r: nat}
          (f: index_map d r)
          (f_inj: index_map_injective f):
      let fp := build_inverse_index_map f in
      let f' := inverse_index_f _ fp in
      forall x y (xc:x<d), ⟦ f ⟧ x ≡ y -> f' y ≡ x.
    Proof.
      simpl.
      intros x y xc H.
      induction d.
      - crush.
      - simpl.
        break_if.
        + crush.
        + apply IHd; clear IHd.
          *
            apply shrink_index_map_preserves_injectivity, f_inj.
          *
            destruct (Nat.eq_dec x d).
            congruence.
            omega.
          *
            unfold shrink_index_map_domain.
            break_match.
            simpl in *.
            congruence.
    Qed.

    Lemma build_inverse_index_map_is_bijective
          {d r: nat}
          (f: index_map d r)
          {f_inj: index_map_injective f}
      : inverse_index_map_bijective (build_inverse_index_map f).
    Proof.
      unfold inverse_index_map_bijective.
      split.
      - unfold inverse_index_map_injective.
        intros x y v Rx Ry H.
        unfold build_inverse_index_map in H.
        destruct H as [Hx Hy].
        simpl in *.
        subst.

        induction d.
        + crush.
        +
          assert(index_map_injective (shrink_index_map_domain f))
            by apply shrink_index_map_preserves_injectivity, f_inj.
          remember (shrink_index_map_domain f) as f0.
          apply IHd with (f:=f0).
          simpl in *.
          break_if; crush.

          HERE

        apply f_equal in Hy.
        f_equal. ; apply proof_irrelevance.
      - unfold inverse_index_map_surjective.
        intros y yc.
        destruct (build_inverse_index_map f) eqn:H.
        unfold build_inverse_index_map in H.
        inversion H. clear H.
        simpl in *.
        subst.
        assert(c:⟦ f ⟧ y < r).
        {
          destruct f.
          apply index_f_spec, yc.
        }
        exists (range_point f (⟦ f ⟧ y) _ c yc eq_refl).
        reflexivity.
    Qed.

    Definition NewScatter
               {i o: nat}
               (f: index_map i o)
               {f_inj: index_map_injective f}
               (x: svector i) : svector o
      :=
        let f' := build_inverse_index_map f (f_inj:=f_inj) in
        Vbuild (fun n np =>
                  if in_range f n then mkValue (f' n)
                  else mkSZero).


  End ExperimenalNewScatter.

  
  
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
    apply VnthInverseIndexMapped_arg_equiv.
    assumption.
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

  Instance SHOperator_compose
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

End SigmaHCOL_Operators.

Definition liftM_HOperator
           {i o}
           (op: avector i -> avector o)
           `{hop: !HOperator op}
  : svector i -> svector o :=
  sparsify ∘ op ∘ densify.

Definition SparseEmbedding
           {i o ki ko}
           (kernel: avector ki -> avector ko)
           (f: index_map ko o)
           {f_inj : index_map_injective f}
           (g: index_map ki i)
           `{Koperator: @HOperator ki ko kernel}
           (x: svector i)
           {g_dense: forall k (kc:k<ki), Is_Val (Vnth x («g» k kc))}

  :=
    (Scatter f (f_inj:=f_inj)
             ∘ (liftM_HOperator kernel)
             ∘ (Gather g)) x.

Definition USparseEmbedding
           {n i o ki ko}
           (kernel: forall k, (k<n) -> avector ki -> avector ko)
           (f: index_map_family ko o n)
           {f_inj : index_map_family_injective f}
           (g: index_map_family ki i n)
           `{Koperator: forall k (kc: k<n), @HOperator ki ko (kernel k kc)}
           (x: svector i)
           {g_dense: forall j (jc:j<n) k (kc:k<ki), Is_Val (Vnth x («⦃g⦄ j jc» k kc))}
           {nz: n ≢ 0} (* only defined for non-empty iterator *)
  :=
    (SumUnion
       (Vbuild
          (λ (j:nat) (jc:j<n),
           SparseEmbedding
             (f_inj:=index_map_family_member_injective f_inj j jc)
             (g_dense:=g_dense j jc)
             (kernel j jc)
             ( ⦃f⦄ j jc)
             ( ⦃g⦄ j jc)
             x
    ))).


Section OperatorProperies.
  (* Specification of gather as mapping from ouptu to input. NOTE:
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
    assert(L: partial_index_f o i (build_inverse_index_map f) (⟦f ⟧ n) ≡ Some n).
    {
      apply build_inverse_index_map_is_left_inverse; try assumption.
      reflexivity.
    }

    (* At this point 'rewrite L' should work but it does not, so we will generalize the hell out of it, and remove unnecessary hypothesis to work around this problem *)

    remember (build_inverse_index_map f) as f' eqn:F.
    unfold VnthInverseIndexMapped.

    generalize (partial_index_f_spec o i f' (⟦f ⟧ n) («f » n ip));  intros l.
    destruct (partial_index_f o i f' (⟦f ⟧ n)).
    inversion L.
    subst n0.
    generalize (l n eq_refl); intros l0.
    replace l0 with ip by apply proof_irrelevance.
    reflexivity.
    congruence.
  Qed.

  (* Specification of scatter as mapping from output to input.
    NOTE: we are using definitional equality here, as Scatter does not
    perform any operations on elements of type A *)
  Lemma Scatter_rev_spec
        {i o: nat}
        (f: index_map i o)
        {f_inj: index_map_injective f}
        (x: svector i)
        (n: nat)
        (ip : n < o):
    Vnth (Scatter f (f_inj:=f_inj) x) ip ≡
         VnthInverseIndexMapped x (build_inverse_index_map f) n ip.
  Proof.
    unfold Scatter, Vbuild.
    destruct (Vbuild_spec
                (λ (n : nat) (np : n < o),
                 VnthInverseIndexMapped x (build_inverse_index_map f) n np)) as [Vv Vs].
    simpl.
    auto.
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
    apply Vin_VnthInverseIndexMapped.
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
        {g_dense: forall j (jc:j<n) k (kc:k<ki), Is_Val (Vnth x («⦃g⦄ j jc» k kc))}
        {nz: n ≢ 0}
    :
      svector_is_dense
        (@USparseEmbedding n i o ki ko kernel f f_inj g Koperator x g_dense nz).
  Proof.
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

      assert(Vforall Is_Val (liftM_HOperator (kernel p pc) gx))
        by apply liftM_HOperator_DensityPreserving, GD.

      generalize dependent (liftM_HOperator (kernel p pc) gx).
      intros kx KD.
      clear GD gx Koperator kernel.

      rewrite Scatter_rev_spec.
      apply index_map_family_member_injective with (jc:=pc) in f_inj.
      generalize dependent (⦃f ⦄ p pc). intros fp fp_inj F.
      clear f.

      assert(ZI: partial_index_f _ _ (build_inverse_index_map fp) oi ≡ Some z)
        by (apply build_inverse_index_map_is_left_inverse; assumption).
      clear F fp_inj F.

      unfold VnthInverseIndexMapped.
      (* Ugly code below. needs to be cleaned up *)
      generalize dependent (build_inverse_index_map fp). intros pm ZI.

      unfold partial_index_f.
      break_match.
      simpl.
      generalize (partial_index_f_spec oi oic). intros.
      break_match.
      apply Vforall_nth, KD.
      simpl in *.
      congruence.
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
    rewrite Scatter_rev_spec in H.
    unfold VnthInverseIndexMapped, partial_index_f in H.

    break_let.
    simpl in *.

    generalize dependent (partial_index_f_spec j jc).
    intros f_spec H.
    break_match.
    -
      exists n0.
      assert(nc: n0<m) by (apply f_spec; reflexivity).
      exists nc.
      replace (f_spec n0 eq_refl) with nc in H by apply proof_irrelevance.
      apply build_inverse_index_map_is_right_inverse; auto.
      inversion Heqp.
      rewrite Heqp.
      apply Heqo.
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
        {g_dense: forall j (jc:j<n) k (kc:k<ki), Is_Val (Vnth x («⦃g⦄ j jc» k kc))}
        {nz: n ≢ 0}
    :

      (forall j (jc:j<n) k (kc:k<ki), Not_Collision (Vnth x («⦃g⦄ j jc» k kc))) ->
      svector_is_non_collision
        (@USparseEmbedding n i o ki ko kernel f f_inj g Koperator x g_dense nz).
  Proof.
    intros GNC.
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
        assert(LD: svector_is_dense (liftM_HOperator (kernel j jn) gx))
          by apply liftM_HOperator_DensityPreserving, GXD.

        assert(KNC: svector_is_non_collision (liftM_HOperator (kernel j jn) gx)).
        {
          apply liftM_HOperator_DenseCauseNoCol, GXNC.
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
        assert(svector_is_dense (@liftM_HOperator ki ko (kernel i0 ic) (Koperator i0 ic) gxi0)) by apply liftM_HOperator_DensityPreserving, GXDi0.
        generalize dependent (@liftM_HOperator ki ko (kernel i0 ic) (Koperator i0 ic) gxi0).
        intros kxi KXDi0.
        clear gxi0 GXDi0.

        assert (svector_is_dense (@liftM_HOperator ki ko (kernel j jc) (Koperator j jc) gxj)) by apply liftM_HOperator_DensityPreserving, GXDj.
        generalize dependent (@liftM_HOperator ki ko (kernel j jc) (Koperator j jc) gxj).
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
