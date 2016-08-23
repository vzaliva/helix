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

  (* Strong condition: operator preserves vectors' density *)
  Class DensityPreserving {i o:nat} (op: svector i -> svector o) :=
    o_den_pres : forall x, svector_is_dense x -> svector_is_dense (op x).

  (* Weaker condition: applied to a dense vector without collisions does not produce strucural collisions *)
  Class DenseCauseNoCol {i o:nat} (op: svector i -> svector o) :=
    o_den_non_col : forall x,
      svector_is_dense x ->
      svector_is_non_collision x ->
      svector_is_non_collision (op x).

  (* Even weaker condition: applied to a vector without collisions does not produce strucural collisions *)
  Class CauseNoCol {i o:nat} (op: svector i -> svector o) :=
    o_non_col : forall x,
      svector_is_non_collision x ->
      svector_is_non_collision (op x).

  Lemma SHOperator_functional_extensionality
        {m n: nat}
        `{SHOperator m n f}
        `{SHOperator m n g}:
    (∀ v, f v = g v) -> f = g.
  Proof.
    unfold SHOperator in *.
    apply ext_equiv_applied_iff.
  Qed.

  (* Apply family of operators to same fector and return matrix of results *)
  Definition Apply_Family
        {i o n}
        (op_family: forall k, (k<n) -> svector i -> svector o)
        `{Koperator: forall k (kc: k<n), @SHOperator i o (op_family k kc)}
        (x: svector i)
    :=
      (Vbuild
         (λ (j:nat) (jc:j<n),  op_family j jc x)).

  Global Instance Apply_Family_proper
         {i o n}
         (op_family: forall k, (k<n) -> svector i -> svector o)
         `{Koperator: forall k (kc: k<n), @SHOperator i o (op_family k kc)}:
    Proper ((=) ==> (=)) (@Apply_Family i o n op_family Koperator).
  Proof.
    intros x y E.
    unfold Apply_Family.
    vec_index_equiv j jc.
    rewrite 2!Vbuild_nth.
    rewrite E.
    reflexivity.
  Qed.

  (* Apply operator family to a vector produced a matrix which have at most one non-structural element per row. The name alludes to the fact that doing SumUnion on such matrix will not lead to collisions. *)
  Class Apply_Family_SumUnionFriendly
        {i o n}
        (op_family: forall k, (k<n) -> svector i -> svector o)
        `{Koperator: forall k (kc: k<n), @SHOperator i o (op_family k kc)}
    :=
      apply_family_union_friendly: forall x, Vforall (Vunique Is_Val)
                                                (transpose
                                                   (Apply_Family op_family x)
                                                ).

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
    vec_index_equiv j jp.
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
    vec_index_equiv j jp.
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
    vec_index_equiv j jc.
    rewrite 2!Vbuild_nth.

    unfold_Rtheta_equiv.
    rewrite 2!evalWriter_Rtheta_liftM.

    f_equiv.
    apply evalWriter_proper.
    apply Vnth_arg_equiv.
    apply E.
  Qed.

  Definition SHBinOp
             {o}
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
    vec_index_equiv j jc.
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

  Definition ISumReduction
             {i o n}
             (f: Rtheta -> Rtheta -> Rtheta)
             (id: Rtheta)
             (op_family: forall k, (k<n) -> svector i -> svector o)
             `{Koperator: forall k (kc: k<n), @SHOperator i o (op_family k kc)}
             `{Uf: !Apply_Family_SumUnionFriendly op_family}
             (x: svector i)
    :=
      VecUnion
        (Vmap (Vfold_right_aux f id)
         (transpose
            (@Apply_Family i o n op_family Koperator x))).

  Definition ISumUnion
             {i o n}
             (op_family: forall k, (k<n) -> svector i -> svector o)
             `{Koperator: forall k (kc: k<n), @SHOperator i o (op_family k kc)}
             `{Uf: !Apply_Family_SumUnionFriendly op_family}
             (x: svector i)
    :=
      SumUnion (@Apply_Family i o n op_family Koperator x).


  Global Instance SHOperator_ISumUnion
         {i o n}
         (op_family: forall k, (k<n) -> svector i -> svector o)
         `{Koperator: forall k (kc: k<n), @SHOperator i o (op_family k kc)}
         `{Uf: !Apply_Family_SumUnionFriendly op_family}:
    SHOperator (@ISumUnion i o n op_family Koperator Uf).
  Proof.
    unfold SHOperator.
    split; repeat apply vec_Setoid.
    unfold ISumUnion.
    solve_proper.
  Qed.


End SigmaHCOL_Operators.



Lemma SHOperator_Reflexivity
      {m n: nat}
      `{SHOperator m n f}:
  f = f.
Proof.
  apply (@SHOperator_functional_extensionality m n).
  assumption.
  assumption.
  intros.
  reflexivity.
Qed.

(* We forced to use this instead of usual 'reflexivity' tactics, as currently there is no way in Coq to define 'Reflexive' class instance constraining 'ext_equiv' function arguments by SHOperator class *)
Ltac SHOperator_reflexivity :=
  match goal with
  | [ |- (@equiv
           (forall _ : svector ?m, svector ?n)
           (@ext_equiv
              (svector ?m)
              (@vec_Equiv Rtheta.Rtheta Rtheta.Rtheta_equiv ?m)
              (svector ?n)
              (@vec_Equiv Rtheta.Rtheta Rtheta.Rtheta_equiv ?n)) _ _)
    ] => eapply (@SHOperator_Reflexivity m n); typeclasses eauto
  end.

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

(* Family of operators *)
Definition SparseEmbedding
           {n i o ki ko}
           (kernel: forall k, (k<n) -> svector ki -> svector ko)
           `{KD: forall k (kc: k<n), @DensityPreserving ki ko (kernel k kc)}
           (f: index_map_family ko o n)
           {f_inj : index_map_family_injective f}
           (g: index_map_family ki i n)
           `{Koperator: forall k (kc: k<n), @SHOperator ki ko (kernel k kc)}
           (j:nat) (jc:j<n)
  :=
    Scatter (⦃f⦄ j jc)
            (f_inj:=index_map_family_member_injective f_inj j jc)
            ∘ (kernel j jc)
            ∘ (Gather (⦃g⦄ j jc)).


Global Instance SHOperator_SparseEmbedding
       {n i o ki ko}
       (kernel: forall k, (k<n) -> svector ki -> svector ko)
       `{KD: forall k (kc: k<n), @DensityPreserving ki ko (kernel k kc)}
       (f: index_map_family ko o n)
       {f_inj : index_map_family_injective f}
       (g: index_map_family ki i n)
       `{Koperator: forall k (kc: k<n), @SHOperator ki ko (kernel k kc)}
       (j:nat) (jc:j<n):
  SHOperator
    (@SparseEmbedding
       n i o ki ko
       kernel
       KD
       f
       f_inj
       g
       Koperator
       j jc).
Proof.
  unfold SHOperator.
  split; repeat apply vec_Setoid.
  intros x y E.
  rewrite E.
  reflexivity.
Qed.



(* TODO: maybe <->  *)
Lemma Is_Val_Scatter
      {m n: nat}
      (f: index_map m n)
      {f_inj: index_map_injective f}
      (x: svector m)
      (j: nat) (jc : j < n):
  Is_Val (Vnth (Scatter f (f_inj:=f_inj) x) jc) ->
  (exists i (ic:i<m), ⟦f⟧ i ≡ j).
Proof.
  intros H.
  unfold Scatter in H. rewrite Vbuild_nth in H.
  break_match.
  simpl in *.
  -
    generalize dependent (gen_inverse_index_f_spec f j i); intros f_spec H.
    exists (gen_inverse_index_f f j), f_spec.
    apply build_inverse_index_map_is_right_inverse; auto.
  -
    apply Is_Val_mkStruct in H.
    inversion H.
Qed.


Global Instance Apply_Family_SparseEmbedding_SumUnionFriendly
       {n gi go ki ko}
       (kernel: forall k, (k<n) -> svector ki -> svector ko)
       `{KD: forall k (kc: k<n), @DensityPreserving ki ko (kernel k kc)}
       (f: index_map_family ko go n)
       {f_inj : index_map_family_injective f}
       (g: index_map_family ki gi n)
       `{Koperator: forall k (kc: k<n), @SHOperator ki ko (kernel k kc)}
  :
    Apply_Family_SumUnionFriendly
      (@SparseEmbedding
         n gi go ki ko
         kernel KD
         f f_inj
         g
         Koperator).
Proof.
  unfold Apply_Family_SumUnionFriendly.
  intros x.
  apply Vforall_nth_intro.
  intros j jc.
  unfold Vunique.
  intros i0 ic0 i1 ic1.
  unfold transpose.
  rewrite Vbuild_nth.
  unfold row.
  rewrite 2!Vnth_map.
  unfold Apply_Family.
  rewrite 2!Vbuild_nth.
  unfold Vnth_aux.
  unfold SparseEmbedding.
  unfold compose.
  generalize (kernel i0 ic0 (Gather (⦃ g ⦄ i0 ic0) x)) as x0.
  generalize (kernel i1 ic1 (Gather (⦃ g ⦄ i1 ic1) x)) as x1.
  intros x0 x1.
  intros [V0 V1].
  apply Is_Val_Scatter in V0.
  apply Is_Val_Scatter in V1.
  crush.
  unfold index_map_family_injective in f_inj.
  specialize (f_inj i0 i1 ic0 ic1 x4 x2 x5 x3).
  destruct f_inj.
  congruence.
  assumption.
Qed.


Definition USparseEmbedding
           {n i o ki ko}
           (kernel: forall k, (k<n) -> svector ki -> svector ko)
           `{KD: forall k (kc: k<n), @DensityPreserving ki ko (kernel k kc)}
           (f: index_map_family ko o n)
           {f_inj : index_map_family_injective f}
           (g: index_map_family ki i n)
           `{Koperator: forall k (kc: k<n), @SHOperator ki ko (kernel k kc)}
  : svector i -> svector o
  :=
    @ISumUnion i o n
               (@SparseEmbedding n i o ki ko
                                 kernel KD
                                 f f_inj g
                                 Koperator)
               (SHOperator_SparseEmbedding kernel f g)
               (Apply_Family_SparseEmbedding_SumUnionFriendly  kernel f g).

Global Instance SHOperator_USparseEmbedding
       {n i o ki ko}
       (kernel: forall k, (k<n) -> svector ki -> svector ko)
       `{KD: forall k (kc: k<n), @DensityPreserving ki ko (kernel k kc)}
       (f: index_map_family ko o n)
       {f_inj : index_map_family_injective f}
       (g: index_map_family ki i n)
       `{Koperator: forall k (kc: k<n), @SHOperator ki ko (kernel k kc)}:
  SHOperator (@USparseEmbedding
                n i o ki ko
                kernel KD
                f f_inj
                g
                Koperator).
Proof.
  unfold SHOperator.
  split; repeat apply vec_Setoid.
  intros x y E.
  unfold USparseEmbedding, ISumUnion, Apply_Family.
  apply ext_equiv_applied_iff'.
  split; repeat apply vec_Setoid.
  apply SumUnion_proper.
  split; repeat apply vec_Setoid.
  apply SumUnion_proper.
  reflexivity.
  vec_index_equiv j jc.
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
    Vnth (SHPointwise f v) jc = mkValue (f (j ↾ jc) (WriterMonadNoT.evalWriter (Vnth v jc))).
  Proof.
    unfold SHPointwise.
    rewrite Vbuild_nth.
    generalize (Vnth v jc) as x. intros x. clear v.
    rewrite <- evalWriter_Rtheta_liftM.
    rewrite mkValue_evalWriter.
    reflexivity.
  Qed.

  Lemma SHPointwise_nth_eq
        {n: nat}
        (f: { i | i<n} -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}
        {j:nat} {jc:j<n}
        (v: svector n):
    Vnth (SHPointwise f v) jc ≡ Monad.liftM (f (j ↾ jc)) (Vnth v jc).
  Proof.
    unfold SHPointwise.
    rewrite Vbuild_nth.
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

    vec_index_equiv j jc.
    rewrite SHPointwise_nth.

    unfold liftM_HOperator.
    unfold compose.
    unfold sparsify; rewrite Vnth_map.
    rewrite HPointwise_nth.
    unfold densify; rewrite Vnth_map.
    reflexivity.
  Qed.

  Lemma SHBinOp_nth
        {o}
        {f: nat -> CarrierA -> CarrierA -> CarrierA}
        `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
        {v: svector (o+o)}
        {j:nat}
        {jc: j<o}
        {jc1:j<o+o}
        {jc2: (j+o)<o+o}
    :
      Vnth (@SHBinOp o f pF v) jc ≡ liftM2 (f j) (Vnth v jc1) (Vnth v jc2).
  Proof.
    unfold SHBinOp, vector2pair.

    break_let.

    replace t with (fst (Vbreak v)) by crush.
    replace t0 with (snd (Vbreak v)) by crush.
    clear Heqp.

    rewrite Vbuild_nth.
    f_equiv.

    apply Vnth_fst_Vbreak with (jc3:=jc1).
    apply Vnth_snd_Vbreak with (jc3:=jc2).
  Qed.

  Lemma SHBinOp_equiv_lifted_HBinOp {o}
        (f: nat -> CarrierA -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}:
    @SHBinOp o f pF = liftM_HOperator (@HBinOp o f pF).
  Proof.
    apply ext_equiv_applied_iff'; try typeclasses eauto.
    intros x.

    vec_index_equiv j jc.

    assert(jc1: j<o+o) by omega.
    assert(jc2: j+o<o+o) by omega.
    rewrite (@SHBinOp_nth o f pF x j jc jc1 jc2).

    unfold liftM_HOperator.
    unfold compose.
    unfold sparsify; rewrite Vnth_map.
    rewrite (@HBinOp_nth o f pF _ j jc jc1 jc2).
    unfold densify; rewrite 2!Vnth_map.

    rewrite <- evalWriter_Rtheta_liftM2.
    rewrite mkValue_evalWriter.
    reflexivity.
  Qed.

End OperatorProperies.

Section StructuralProperies.
  (* All lifted HOperators are naturally density preserving *)
  Global Instance liftM_HOperator_DensityPreserving
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


  Global Instance liftM_HOperator_DenseCauseNoCol
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

  Lemma Is_Val_LiftM2
        (f : CarrierA → CarrierA → CarrierA)
        (v1 v2 : Rtheta)
        (V1: Is_Val v1)
        (V2: Is_Val v2):
    Is_Val (liftM2 f v2 v1).
  Proof.
    unfold Is_Val, compose, IsVal in *.
    rewrite execWriter_Rtheta_liftM2.
    simpl in *.
    generalize dependent (is_struct (WriterMonadNoT.execWriter v1)); clear v1.
    generalize dependent (is_struct (WriterMonadNoT.execWriter v2)); clear v2.
    intros f1 V1 f2 V2.
    destr_bool.
  Qed.

  Global Instance SHBinOp_DensityPreserving {o}
         (f: nat -> CarrierA -> CarrierA -> CarrierA)
         `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}:
    DensityPreserving (@SHBinOp o f pF).
  Proof.
    unfold DensityPreserving.
    intros x D.
    unfold svector_is_dense.
    apply Vforall_nth_intro.
    intros j jc.
    assert (jc1 : j < o + o) by omega.
    assert (jc2 : j + o < o + o) by omega.
    erewrite (@SHBinOp_nth o f pF x j jc jc1 jc2).
    assert(V1: Is_Val (Vnth x jc1)) by apply Vforall_nth, D.
    assert(V2: Is_Val (Vnth x jc2)) by apply Vforall_nth, D.
    generalize dependent (Vnth x jc1).
    generalize dependent (Vnth x jc2).
    intros v1 V1 v2 V2.
    apply Is_Val_LiftM2; assumption.
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
        (kernel: forall k, (k<n) -> svector ki -> svector ko)
        `{KD: forall k (kc: k<n), @DensityPreserving ki ko (kernel k kc)}
        (f: index_map_family ko o n)
        {f_inj: index_map_family_injective f} (* gives non-col *)
        {f_sur: index_map_family_surjective f} (* gives density *)
        (g: index_map_family ki i n)
        `{Koperator: forall k (kc: k<n), @SHOperator ki ko (kernel k kc)}
        (x: svector i)
        {nz: n ≢ 0}
    :
      (forall j (jc:j<n) k (kc:k<ki), Is_Val (Vnth x («⦃g⦄ j jc» k kc))) ->
      svector_is_dense
        (@USparseEmbedding n i o ki ko kernel KD f f_inj g Koperator x).
  Proof.
    intros g_dense.
    apply Vforall_nth_intro.
    intros oi oic.
    unfold compose.
    unfold USparseEmbedding, ISumUnion, Apply_Family, SparseEmbedding.
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

      assert(Vforall Is_Val ((kernel p pc) gx)).
      {
        apply KD.
        apply GD.
      }

      generalize dependent ((kernel p pc) gx).
      intros kx KD1.
      clear KD GD gx Koperator kernel.

      unfold Scatter; rewrite Vbuild_nth.


      apply index_map_family_member_injective with (jc:=pc) in f_inj.
      generalize dependent (⦃f ⦄ p pc). intros fp fp_inj F.
      clear f.
      break_match.
      apply Vforall_nth, KD1.
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

  (* TODO: maybe <->  *)
  Lemma Is_Not_Zero_Scatter
        {m n: nat}
        (f: index_map m n)
        {f_inj: index_map_injective f}
        (x: svector m)
        (j: nat) (jc : j < n):
    (not ∘ Is_ValZero) (Vnth (Scatter f (f_inj:=f_inj) x) jc) ->
    (exists i (ic:i<m), ⟦f⟧ i ≡ j).
  Proof.
    intros H.
    unfold Scatter in H. rewrite Vbuild_nth in H.
    break_match.
    simpl in *.
    -
      generalize dependent (gen_inverse_index_f_spec f j i); intros f_spec H.
      exists (gen_inverse_index_f f j), f_spec.
      apply build_inverse_index_map_is_right_inverse; auto.
    -
      unfold compose in H.
      assert(C: Is_ValZero mkSZero) by apply SZero_is_ValZero.
      congruence.
  Qed.

  Lemma Is_SZero_Scatter_out_of_range
        {m n: nat}
        (f: index_map m n)
        {f_inj: index_map_injective f}
        (x: svector m)
        (j: nat) (jc : j < n):
    not (in_range f j) ->
    Is_SZero (Vnth (Scatter f (f_inj:=f_inj) x) jc).
  Proof.
    intros R.
    unfold Scatter.
    rewrite Vbuild_nth.
    break_match.
    congruence.
    apply Is_SZero_mkSZero.
  Qed.

  Lemma Scatter_eq_mkSZero
        {m n: nat}
        (f: index_map m n)
        {f_inj: index_map_injective f}
        (x: svector m)
        (j: nat) (jc : j < n)
        (R: not (in_range f j)):
    Vnth (Scatter f (f_inj:=f_inj) x) jc ≡ mkSZero.
  Proof.
    unfold Scatter.
    rewrite Vbuild_nth.
    break_match.
    congruence.
    reflexivity.
  Qed.

  Lemma USparseEmbeddingCauseNoCol
        {n i o ki ko}
        (kernel: forall k, (k<n) -> svector ki -> svector ko)
        `{KD: forall k (kc: k<n), @DensityPreserving ki ko (kernel k kc)}
        `{KNC: forall k (kc: k<n), DenseCauseNoCol (kernel k kc)}
        (f: index_map_family ko o n)
        {f_inj: index_map_family_injective f} (* gives non-col *)
        {f_sur: index_map_family_surjective f} (* gives density *)
        (g: index_map_family ki i n)
        `{Koperator: forall k (kc: k<n), @SHOperator ki ko (kernel k kc)}
        (x: svector i)
        {nz: n ≢ 0}
    :
      (forall j (jc:j<n) k (kc:k<ki), Is_Val (Vnth x («⦃g⦄ j jc» k kc))) ->
      (forall j (jc:j<n) k (kc:k<ki), Not_Collision (Vnth x («⦃g⦄ j jc» k kc))) ->
      svector_is_non_collision
        (@USparseEmbedding n i o ki ko kernel KD f f_inj g Koperator x).
  Proof.
    intros g_dense GNC.
    apply Vforall_nth_intro.
    intros oi oic.
    unfold compose.
    unfold USparseEmbedding, ISumUnion, Apply_Family, SparseEmbedding.
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
        assert(LD: svector_is_dense ((kernel j jn) gx)).
        {
          apply KD.
          apply GXD.
        }

        assert(KNC1: svector_is_non_collision ((kernel j jn) gx)).
        {
          apply KNC.
          apply GXD.
          apply GXNC.
        }
        generalize dependent ((kernel j jn) gx).
        intros kx KD1 KNC1.
        clear GXD GXNC gx.

        (* Get rid of Scatter  *)
        assert(SNC: svector_is_non_collision (@Scatter ko o (family_f ko o (S n) f j jn)
                                                       (@index_map_family_member_injective ko o (S n) f f_inj j jn) kx)).

        apply ScatterCollisionFree, KNC1.
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
        assert(svector_is_dense ((kernel i0 ic) gxi0)).
        {
          apply KD.
          apply GXDi0.
        }
        generalize dependent ((kernel i0 ic) gxi0).
        intros kxi KXDi0.
        clear gxi0 GXDi0.

        assert (svector_is_dense ( (kernel j jc) gxj)).
        {
          apply KD.
          apply GXDj.
        }
        generalize dependent ((kernel j jc) gxj).
        intros kxj KXDj.
        clear gxj GXDj.

        (* housekeeping *)
        clear KD KNC Koperator g kernel nz x i ki f_sur.
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


  (* Union of UnionFriendly family of operators and collision-free vector will not cause any collisions *)
  Global Instance SumUnion_SumUnionFriendly_CauseNoCol
         {i o n}
         (op_family: forall k, (k<n) -> svector i -> svector o)
         `{Koperator: forall k (kc: k<n), @SHOperator i o (op_family k kc)}
         `{Uf: !Apply_Family_SumUnionFriendly op_family}
         {NC: forall k (kc: k<n), CauseNoCol (op_family k kc)}:
    CauseNoCol (SumUnion ∘ (Apply_Family op_family)).
  Proof.
    unfold compose, CauseNoCol.
    intros x Xcf.
    unfold Apply_Family_SumUnionFriendly in Uf.
    specialize (Uf x).
    unfold svector_is_non_collision.
    apply Vforall_nth_intro.
    intros j jc.
    unfold Apply_Family.
    rewrite AbsorbIUnionIndex.
    apply Not_Collision_VecUnion.

    -
      unfold CauseNoCol in NC.
      apply Vforall_nth_intro.
      intros k kc.
      rewrite Vbuild_nth.
      unfold svector_is_non_collision in NC.
      specialize (NC k kc x Xcf).
      apply Vforall_nth.
      apply NC.

    - apply Vforall_nth with (ip:=jc) in Uf.
      unfold Apply_Family, transpose in Uf.
      rewrite Vbuild_nth in Uf.
      unfold row in Uf.
      rewrite Vmap_Vbuild in Uf.
      unfold Vnth_aux in Uf.
      apply Uf.
  Qed.

End StructuralProperies.

Section ValueProperties.

  (* Apply operator family to a vector produced a matrix which have at most one non-zero element per row. Strictly *)
  Class Apply_Family_Single_NonZero_Per_Row
        {i o n}
        (op_family: forall k, (k<n) -> svector i -> svector o)
        `{Koperator: forall k (kc: k<n), @SHOperator i o (op_family k kc)}
    :=
      apply_family_single_row_nz: forall x, Vforall (Vunique (not ∘ Is_ValZero))
                                               (transpose
                                                  (Apply_Family op_family x)
                                               ).

  Global Instance Apply_Family_SparseEmbedding_Single_NonZero_Per_Row
         {n gi go ki ko}
         (kernel: forall k, (k<n) -> svector ki -> svector ko)
         `{KD: forall k (kc: k<n), @DensityPreserving ki ko (kernel k kc)}
         (f: index_map_family ko go n)
         {f_inj : index_map_family_injective f}
         (g: index_map_family ki gi n)
         `{Koperator: forall k (kc: k<n), @SHOperator ki ko (kernel k kc)}
    :
      Apply_Family_Single_NonZero_Per_Row
        (@SparseEmbedding
           n gi go ki ko
           kernel KD
           f f_inj
           g
           Koperator).
  Proof.
    unfold Apply_Family_Single_NonZero_Per_Row.
    intros x.
    apply Vforall_nth_intro.
    intros j jc.
    unfold Vunique.
    intros i0 ic0 i1 ic1.
    unfold transpose.
    rewrite Vbuild_nth.
    unfold row.
    rewrite 2!Vnth_map.
    unfold Apply_Family.
    rewrite 2!Vbuild_nth.
    unfold Vnth_aux.
    unfold SparseEmbedding.
    unfold compose.
    generalize (kernel i0 ic0 (Gather (⦃ g ⦄ i0 ic0) x)) as x0.
    generalize (kernel i1 ic1 (Gather (⦃ g ⦄ i1 ic1) x)) as x1.
    intros x0 x1.
    intros [V0 V1].

    apply Is_Not_Zero_Scatter in V0.
    apply Is_Not_Zero_Scatter in V1.
    crush.
    unfold index_map_family_injective in f_inj.
    specialize (f_inj i0 i1 ic0 ic1 x4 x2 x5 x3).
    destruct f_inj.
    congruence.
    assumption.
  Qed.


End ValueProperties.

