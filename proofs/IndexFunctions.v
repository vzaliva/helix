
(* Coq defintions for Sigma-HCOL operator language *)

Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Import Coq.Arith.PeanoNat.Nat.

Require Import SpiralTactics.
Require Import Psatz.
Require Import Omega.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.implementations.peano_naturals.
Require Import MathClasses.orders.orders.
Require Import MathClasses.misc.util.
Require Import MathClasses.interfaces.abstract_algebra.

Require Import Spiral.
Require Import FinNatSet.

(* Setoid equality for option types *)
Section OptionSetoid.
  Global Instance option_Equiv `{Equiv A}: Equiv (option A) :=
    fun a b =>
      match a with
      | None => is_None b
      | Some x => (match b with
                   | None => False
                   | Some y => equiv x y
                   end)
      end.

  Global Instance option_Setoid `{Setoid A}: Setoid (@option A).
  Proof.
    unfold Setoid in H.
    constructor. destruct H.
    unfold Reflexive. destruct x; (unfold equiv; crush).
    unfold Symmetric. intros x y. destruct x,y; (unfold equiv; crush).
    unfold Transitive. intros x y z. destruct x,y,z; unfold equiv, option_Equiv in *; crush.
  Qed.
End OptionSetoid.

Global Open Scope nat_scope.

(* Index maps (total functions) *)

Record index_map (domain range : nat) :=
  IndexMap
    {
      index_f : nat -> nat;
      index_f_spec : forall x, x<domain -> (index_f x) < range;
    }.

Notation "⟦ f ⟧" := (@index_f _ _ f).
Notation "« f »" := (@index_f_spec _ _ f).

Global Instance index_map_equiv {domain range:nat}:
  Equiv (index_map domain range)
  :=
    fun f g => forall (x:nat) (xd: x<domain), ⟦ f ⟧ x = ⟦ g ⟧ x.

Definition index_map_compose
           {i o t: nat}
           (g: index_map t o)
           (f: index_map i t) :
  index_map i o.
Proof.
  refine (IndexMap i o (⟦g⟧ ∘ ⟦f⟧) _).
  intros.
  destruct f, g.
  simpl.
  unfold compose.
  auto.
Defined.

(* Restriction on domain *)
Definition shrink_index_map_domain {d r:nat} (f: index_map (S d) r)
  : index_map d r.
Proof.
  destruct f.
  assert (new_spec : ∀ x : nat, x < d → index_f0 x < r) by auto.
  exact (IndexMap d r index_f0 new_spec).
Defined.

Lemma shrink_non_shrink_eq (d r : nat) (f : index_map (S d) r):
  ⟦ shrink_index_map_domain f ⟧ ≡ ⟦ f ⟧.
Proof.
  unfold shrink_index_map_domain.
  break_match.
  reflexivity.
Qed.

Lemma shrink_index_map_domain_exists_eq {i o : nat}
      (f : index_map (S i) o)
      (j : nat)
      (jc : Peano.lt j (S i))
      (jc1 : Peano.lt j i):
  (@exist nat (fun x : nat => Peano.lt x o)
          (index_f i o (@shrink_index_map_domain i o f) j)
          (index_f_spec i o (@shrink_index_map_domain i o f) j jc1))
    ≡
    (@exist nat (fun x : nat => Peano.lt x o)
            (index_f (S i) o f j)
            (index_f_spec (S i) o f j jc)
    ).
Proof.
  destruct f.
  simpl.
  repeat f_equiv.
  apply le_unique.
Qed.

Definition shrink_index_map_1_range {r:nat} (f: index_map 1 (S r)) (NZ: ⟦ f ⟧ 0 ≢ 0)
  : index_map 1 r.
Proof.
  destruct f.
  simpl in *.

  set (index_f' := compose Nat.pred index_f0).
  assert (new_spec : ∀ x : nat, x < 1 → index_f' x < r).
  {
    intros x xc.
    unfold index_f', compose.
    destruct (index_f0 x) eqn:E.
    -
      destruct x; omega.
    -
      rewrite Nat.pred_succ.
      specialize (index_f_spec0 x xc).
      omega.
  }
  exact (IndexMap 1 r index_f' new_spec).
Defined.

Section InRange.

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

  Lemma in_range_by_def:
    ∀ (d r : nat) (f : index_map d r) (x : nat) (xc: x < d),
      in_range f (⟦ f ⟧ x).
  Proof.
    intros d r f x xc.

    dependent induction d.
    - crush.
    - simpl.
      break_if.
      + trivial.
      +
        remember (shrink_index_map_domain f) as f0.
        case (Nat.eq_dec x d).
        congruence.
        intros nx.
        assert (F: ⟦ f ⟧ x ≡ ⟦ f0 ⟧ x).
        {
          subst f0.
          unfold shrink_index_map_domain.
          break_match.
          auto.
        }
        rewrite F.
        apply IHd.
        omega.
  Qed.

  Lemma in_range_upper_bound:
    ∀ (d r : nat) (f : index_map d r) (x : nat),
      in_range f x → x < r.
  Proof.
    intros d r f x Rx.
    induction d.
    - crush.
    - destruct (Nat.eq_dec (⟦ f ⟧ d) x).
      + destruct f.
        subst x.
        apply index_f_spec.
        auto.
      + simpl in *.
        remember (shrink_index_map_domain f) as f0.
        apply IHd with (f:=f0).
        break_if.
        * congruence.
        * apply Rx.
  Qed.


  Lemma in_range_shrink_index_map_domain (d r y : nat) (f : index_map (S d) r):
    in_range f y → ⟦ f ⟧ d ≢ y → in_range (shrink_index_map_domain f) y.
  Proof.
    intros R N.
    unfold shrink_index_map_domain.
    break_match.
    simpl in *.
    break_if.
    congruence.
    apply R.
  Qed.

  Lemma in_range_exists
        {d r y: nat}
        (f: index_map d r)
        (yc: y<r)
    :
      in_range f y <-> (∃ x (xc:x<d), ⟦ f ⟧ x ≡ y).
  Proof.
    split.
    - intros H.
      induction d.
      + crush.
      + destruct (Nat.eq_dec (⟦ f ⟧ d) y).
        * assert(dc: d<S d) by omega.
          exists d, dc.
          assumption.
        *
          replace (⟦ f ⟧) with (⟦ shrink_index_map_domain f ⟧).
          assert(S: in_range (shrink_index_map_domain f) y)
            by (apply in_range_shrink_index_map_domain; try assumption).
          specialize (IHd (shrink_index_map_domain f) S).
          elim IHd.
          intros x H0.
          elim H0.
          intros x0 H1.
          assert(xc: x < (Datatypes.S  d)) by omega.
          exists x, xc.
          apply H1.
          apply shrink_non_shrink_eq.
    - intros H.
      elim H; intros x H0; clear H.
      elim H0; intros xc H; clear H0.
      apply in_range_by_def with (f:=f) in xc.
      subst y.
      apply xc.
  Qed.

  Lemma in_range_index_map_compose_left {i o t : nat}
        (f : index_map i t)
        (g : index_map t o)
        (j : nat)
        (jc: j<o):
    in_range (index_map_compose g f) j → in_range g j.
  Proof.
    intros H.
    apply in_range_exists in H; try assumption.
    elim H; intros x0 H0; clear H.
    elim H0; intros xc0 H; clear H0.
    simpl in H.
    unfold compose in H.
    subst j.
    apply in_range_by_def.
    apply index_f_spec, xc0.
  Qed.

End InRange.

Section Jections.

  Definition function_injective
             {A B: Set}
             (f: A->B)
    :=
      forall (x y:A),
        f x ≡ f y → x ≡ y.

  Definition function_surjective
             {A B: Set}
             (f: A->B)
    :=
      forall (y:B), exists (x:A), f x ≡ y.

  Definition function_bijective
             {A B: Set}
             (f: A->B)
    :=
      (function_injective f) /\ (function_surjective f).

  Definition index_map_injective
             {d r: nat}
             (f: index_map d r)
    :=
      forall (x y:nat) (xc: x<d) (yc: y<d),
        ⟦ f ⟧ x ≡ ⟦ f ⟧ y → x ≡ y.

  Definition index_map_surjective
             {d r: nat}
             (f: index_map d r)
    :=
      forall (y:nat) (yc: y<r), exists (x:nat) (xc: x<d), ⟦ f ⟧ x ≡ y.

  Definition index_map_bijective
             {n: nat}
             (f: index_map n n)
    :=
      (index_map_injective f) /\ (index_map_surjective f).

  Lemma index_map_compose_injective
        {i o t: nat}
        (f: index_map t o)
        (g: index_map i t)
        (f_inj: index_map_injective f)
        (g_inj: index_map_injective g)
    :
      index_map_injective (index_map_compose f g).
  Proof.
    unfold index_map_injective in *.
    intros x y xc yc H.
    unfold index_map_compose, compose in H. simpl in H.
    apply g_inj; try assumption.
    apply f_inj in H; try assumption.
    apply (index_f_spec), xc.
    apply (index_f_spec), yc.
  Qed.

  Lemma index_map_surjective_in_range
        {d r: nat}
        (f: index_map d r)
        {S: index_map_surjective f}:
    forall x, x<r -> in_range f x.
  Proof.
    intros x H.
    apply in_range_exists; auto.
  Qed.

  Lemma shrink_index_map_1_range_inj
        {r:nat}
        (f: index_map 1 (S r))
        (NZ: ⟦ f ⟧ 0 ≢ 0):
    index_map_injective f ->
    index_map_injective (shrink_index_map_1_range f NZ).
  Proof.
    intros E.
    unfold index_map_injective.
    intros x y xc yc H.
    apply E; auto.

    unfold shrink_index_map_1_range in *.
    break_match.
    simpl in *.
    unfold compose in H.
    destruct x,y; omega.
  Qed.

End Jections.

Section Inversions.
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

  Lemma gen_inverse_index_f_spec {d r: nat} (f: index_map d r):
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
  Qed.

  (* Theoretically, we can only build inverse of injective functions. However this
definition does not enforce this requirement, and the function produced might not be
   true inverse in mathematical sense. To make sure it is, check (index_map_injective f) *)
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
      forall x y, in_range f x -> in_range f y ->
                  f0 x ≡ f0 y → x ≡ y.

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


  (* The following lemma proves that using `buld_inverse_index_map` on
  injective index_map produces true "right inverse" of it *)
  Lemma build_inverse_index_map_is_right_inverse
        {d r: nat}
        (f: index_map d r)
        (f_inj: index_map_injective f):
    let fp := build_inverse_index_map f in
    let f' := inverse_index_f _ fp in
    forall x y (rc:in_range f y), f' y ≡ x -> ⟦ f ⟧ x ≡ y.
  Proof.
    simpl.
    intros x y rc H.
    induction d.
    - crush.
    - simpl in *.
      break_if.
      + crush.
      + apply shrink_index_map_preserves_injectivity in f_inj.
        apply IHd in H; try assumption.
        unfold shrink_index_map_domain in *.
        break_match.
        simpl in *.
        congruence.
  Qed.

  Lemma build_inverse_index_map_is_injective:
    ∀ (d r : nat) (f : index_map d r),
      index_map_injective f →
      inverse_index_map_injective (build_inverse_index_map f).
  Proof.
    intros d r f f_inj.
    unfold inverse_index_map_injective.
    intros x y Rx Ry H.
    remember (inverse_index_f f (build_inverse_index_map f) x) as t eqn:H1.
    symmetry in H1.
    symmetry in H.
    apply build_inverse_index_map_is_right_inverse in H; try assumption.
    apply build_inverse_index_map_is_right_inverse in H1; try assumption.
    subst.
    reflexivity.
  Qed.

  Lemma build_inverse_index_map_is_surjective:
    ∀ (d r : nat) (f : index_map d r), index_map_injective f → inverse_index_map_surjective (build_inverse_index_map f).
  Proof.
    intros d r f f_inj.
    unfold inverse_index_map_surjective.
    intros y yc.
    exists (⟦ f ⟧ y).
    split.
    -
      apply in_range_by_def, yc.
    -
      apply build_inverse_index_map_is_left_inverse; try assumption.
      reflexivity.
  Qed.

  Lemma build_inverse_index_map_is_bijective
        {d r: nat}
        (f: index_map d r)
        {f_inj: index_map_injective f}
    : inverse_index_map_bijective (build_inverse_index_map f).
  Proof.
    unfold inverse_index_map_bijective.
    split;
      [apply build_inverse_index_map_is_injective, f_inj |
       apply build_inverse_index_map_is_surjective, f_inj
      ].
  Qed.

  (*
  Program Definition inverse_index_map_compose
          {i o t : nat}
          {f : index_map i t}
          {g : index_map t o}
          (f': inverse_index_map f)
          (g': inverse_index_map g)
    : inverse_index_map (index_map_compose g f)
    :=
      InverseIndexMap _ _ (index_map_compose g f)
                      ((inverse_index_f f f') ∘ (inverse_index_f g g' )) _.
  Next Obligation.
    unfold compose.
  Defined.
   *)

  Lemma gen_inverse_revert:
    ∀ (d r : nat) (f : index_map d r) (v : nat),
      index_map_injective f ->
      in_range f v ->
      ⟦ f ⟧ (gen_inverse_index_f f v) ≡ v.
  Proof.
    intros d r f v f_inj R.
    induction d.
    - crush.
    - simpl.
      + break_if.
        * assumption.
        * simpl in *.
          destruct (Nat.eq_dec (⟦ f ⟧ d) v).
          -- congruence.
          -- simpl in *.
             apply shrink_index_map_preserves_injectivity in f_inj.
             remember (shrink_index_map_domain f) as f0.
             replace (⟦ f ⟧) with (⟦ f0 ⟧).
             apply IHd; try assumption.
             subst f0.
             unfold shrink_index_map_domain.
             break_match.
             reflexivity.
  Qed.


  Lemma composition_of_inverses_to_invese_of_compositions
        (i o t : nat)
        (f : index_map i t)
        (g : index_map t o)
        (f_inj: index_map_injective f)
        (g_inj: index_map_injective g)
        (j : nat)
        (jc:j < o)
        (Rg: in_range g j)
        (R: in_range f (gen_inverse_index_f g j))
        (Rgf: in_range (index_map_compose g f) j)
    :
      gen_inverse_index_f f (gen_inverse_index_f g j) =
      gen_inverse_index_f (index_map_compose g f) j.
  Proof.
    symmetry.
    apply build_inverse_index_map_is_left_inverse.
    - apply index_map_compose_injective.
      apply g_inj.
      apply f_inj.
    -
      apply gen_inverse_index_f_spec, R.
    -
      unfold index_map_compose, compose.
      simpl.
      rewrite 2!gen_inverse_revert; try assumption.
      reflexivity.
  Qed.

  Lemma in_range_index_map_compose_right {i o t : nat}
        (f : index_map i t)
        (g : index_map t o)
        (g_inj: index_map_injective g)
        (j : nat)
        (jc: j < o):
    in_range g j ->
    in_range (index_map_compose g f) j ->
    in_range f (gen_inverse_index_f g j).
  Proof.
    intros Rj Rgf.

    apply in_range_exists in Rj; try assumption.
    elim Rj; intros x0 H0; clear Rj.
    elim H0; intros xc0 Gj; clear H0.

    apply in_range_exists in Rgf; try assumption.
    elim Rgf; intros x1 H1; clear Rgf.
    elim H1; intros xc1 Rgf; clear H1.

    simpl in Rgf. unfold compose in Rgf.
    assert(Fx1: ⟦ f ⟧ x1 = x0).
    {
      apply g_inj.
      apply (@index_f_spec i t f x1 xc1).
      apply xc0.
      subst j.
      apply Rgf.
    }

    apply build_inverse_index_map_is_left_inverse in Gj; try assumption.
    simpl in Gj.
    rewrite Gj.
    rewrite <- Fx1.
    apply in_range_by_def, xc1.
  Qed.

  Lemma in_range_index_map_compose {i o t : nat}
        (f : index_map i t)
        (g : index_map t o)
        (g_inj: index_map_injective g)
        (j : nat)
        (jc: j<o):
    in_range g j → in_range f (gen_inverse_index_f g j)
    → in_range (index_map_compose g f) j.
  Proof.
    intros R0 R1.

    apply in_range_exists in R1.
    elim R1; intros x H0; clear R1.
    elim H0; intros xc R1; clear H0.
    symmetry in R1.
    apply build_inverse_index_map_is_right_inverse in R1; try assumption.
    replace (⟦ g ⟧ (⟦ f ⟧ x)) with (⟦ index_map_compose g f ⟧ x) in R1.
    ++ subst j.
       apply in_range_by_def.
       apply xc.
    ++
      auto.
    ++
      apply in_range_upper_bound in R1.
      apply R1.
  Qed.

End Inversions.


Record index_map_family (d r n : nat) :=
  IndexMapFamily { family_f : forall k, k<n -> index_map d r }.

Notation "⦃ f ⦄" := (@family_f _ _ _ f).


Section IndexFamilies.

  Definition index_map_family_injective
             {n d r: nat}
             (f: index_map_family d r n)
    :=
      forall (i j: nat) (ic: i<n) (jc: j<n) (x y:nat) (xc: x<d) (yc: y<d),
        ⟦ ⦃f⦄ i ic ⟧ x ≡ ⟦ ⦃f⦄ j jc ⟧ y → (x ≡ y) /\ (i ≡ j).

  Definition index_map_family_surjective
             {n d r: nat}
             (f: index_map_family d r n)
    :=
      forall (y:nat) (yc: y<r), exists (x j:nat) (xc: x<d) (jc: j<n), ⟦ ⦃f⦄ j jc ⟧ x ≡ y.

  Definition index_map_family_bijective
             {n d r}
             (f: index_map_family d r n)
    :=
      (index_map_family_injective f) /\ (index_map_family_surjective f).

  Lemma index_map_family_member_injective
        {d r n: nat}
        {f: index_map_family d r n}:
    index_map_family_injective f -> forall j (jc:j<n), index_map_injective (⦃f⦄ j jc).
  Proof.
    intros H j jc.
    unfold index_map_family_injective in H.
    unfold index_map_injective.
    apply H.
  Qed.

  Lemma index_map_family_injective_in_range_once
        {n d r: nat}
        (f: index_map_family d r n)
        (i j: nat)
        {ic jc}
        {y}
        {yc:y<r}
    :
      index_map_family_injective f ->
      in_range  (⦃ f ⦄ i ic) y ->
      in_range  (⦃ f ⦄ j jc) y -> i ≡ j.
  Proof.
    intros f_inj r0 r1.

    apply in_range_exists in r0; try assumption.
    apply in_range_exists in r1; try assumption.

    elim r0; intros x0; clear r0; intros r0.
    elim r0; intros x0c; clear r0; intros r0.

    elim r1; intros x1; clear r1; intros r1.
    elim r1; intros x1c; clear r1; intros r1.

    rewrite <- r1 in r0; clear r1.

    specialize (f_inj i j ic jc x0 x1 x0c x1c r0).
    destruct f_inj.
    assumption.
  Qed.

End IndexFamilies.


Section Primitive_Functions.

  Program Definition identity_index_map
          (dr: nat) {dp: dr>0}:
    index_map dr dr
    := IndexMap dr dr (id) _.

  Program Definition constant_index_map
          {range: nat}
          (j: nat)
          {jdep: j<range}:
    index_map 1 range
    := IndexMap 1 range (fun _ => j) _.


  Fact add_index_map_spec_conv {d r k: nat}:
    k + d <= r → ∀ x : nat, x < d → x + k < r.
  Proof.
    intros H x H0.
    lia.
  Qed.

  Definition add_index_map
             {domain range: nat}
             (k: nat)
             {kdep: k+domain <= range}:
    index_map domain range
    := IndexMap domain range (fun i => i+k) (add_index_map_spec_conv kdep).

  Program Definition h_index_map
          {domain range: nat}
          (b s: nat)
          {range_bound: forall x, x<domain -> (b+x*s) < range}
    : index_map domain range
    :=
      IndexMap domain range (fun i => b + i*s) _.

  Lemma h_index_map_is_injective
        {domain range: nat}
        (b s: nat)
        {range_bound: forall x, x<domain -> (b+x*s) < range}
        {snzord0: s ≢ 0 \/ domain < 2} (* without this it is not injective! *)
    :
      index_map_injective  (@h_index_map domain range b s range_bound).
  Proof.
    unfold index_map_injective.
    intros x y xc yc H.
    simpl in H.
    nia.
  Qed.

  Lemma in_range_of_h
        {domain range: nat}
        (b s: nat)
        {range_bound: forall x, x<domain -> (b+x*s) < range}
        (y:nat)
        (yc:y<range)
    :
      in_range (@h_index_map domain range b s range_bound) y
      <-> ∃ x (xc:x<domain), b+x*s = y.
  Proof.
    split.
    - intros H.
      rewrite in_range_exists in H.
      auto.
      apply yc.
    -
      intros H.
      apply in_range_exists.
      apply yc.
      apply H.
  Qed.

End Primitive_Functions.


Section PracticalFamilies.

  (* Flattens m-by-n matrix into flat vector of size m*n by column *)
  Program Definition matrixFlattenByColFamily {m n:nat}: index_map_family m (m*n) n
    := (IndexMapFamily m (m*n) n (fun k kc => h_index_map (range_bound:=_)  (k*m) 1)).
  Next Obligation.
    nia.
  Defined.

End PracticalFamilies.


Section Function_Operators.

  Definition tensor_product
             (n N: nat)
             {nz: 0 ≢ n}
             (f: nat -> nat)
             (g: nat -> nat)
             (i: nat): nat
    :=  N * (f (i / n)) + (g (i mod n)).

  Program Definition index_map_tensor_product
          {m n M N: nat}
          {nz: 0 ≢ n}
          (f: index_map m M)
          (g: index_map n N):
    index_map (m*n) (M*N)
    := IndexMap (m*n) (M*N)  (tensor_product n N ⟦f⟧ ⟦g⟧ (nz:=nz))  _.
  Next Obligation.
    destruct f,g.
    unfold tensor_product, div, modulo.
    assert ((fst (divmod x (pred n) 0 (pred n))) < m).
    {
      destruct n.
      congruence. clear nz.
      simpl.
      generalize (divmod_spec x n 0 n).
      destruct divmod as (q,u).
      simpl.
      nia.
    }
    assert (index_f0 (fst (divmod x (pred n) 0 (pred n))) < M) by auto.

    assert ((pred n - snd (divmod x (pred n) 0 (pred n))) < n).
    {
      destruct n.
      congruence. clear nz.
      simpl.
      generalize (divmod_spec x n 0 n).
      destruct divmod as (q,u).
      simpl.
      nia.
    }
    assert (index_f1 (pred n - snd (divmod x (pred n) 0 (pred n))) < N) by auto.
    simpl.
    replace (match n with
             | 0 => n
             | S y' => fst (divmod x y' 0 y')
             end) with (fst (divmod x (pred n) 0 (pred n))).
    replace (match n with
             | 0 => n
             | S y' => y' - snd (divmod x y' 0 y') end) with
    ((pred n) - snd (divmod x (pred n) 0 (pred n))).
    nia.
    break_match; auto.
    break_match; auto.
    congruence.
  Defined.

End Function_Operators.

Notation "g ∘ f" := (index_map_compose g f) : index_f_scope.
Notation "x ⊗ y" := (index_map_tensor_product x y) (at level 90) : index_f_scope.

Section Function_Rules.

  Local Open Scope index_f_scope.

  Lemma index_map_rule_39
        {rf0 rf1 dg0 dg1 rg0 rg1:nat}
        {g0: index_map dg0 rg0}
        {g1: index_map dg1 rg1}
        {f0: index_map rg0 rf0}
        {f1: index_map rg1 rf1}
        {ndg1: 0 ≢ dg1}
        {nrg1: 0 ≢ rg1}
        {ls:  (dg0 * dg1) ≡ (rf0 * rf1)}
    :
      (index_map_tensor_product f0 f1 (nz:=nrg1))
        ∘ (index_map_tensor_product g0 g1 (nz:=ndg1))
      =
      index_map_tensor_product
        (f0 ∘ g0)
        (f1 ∘ g1)
        (nz := ndg1).
  Proof.
    destruct f0 as [f0 f0_spec].
    destruct f1 as [f1 f1_spec].
    destruct g0 as [g0 g0_spec].
    destruct g1 as [g1 g1_spec].

    unfold equiv, index_map_equiv.
    intros. simpl.
    unfold compose, tensor_product.

    assert (X: (rg1 * g0 (x / dg1) + g1 (x mod dg1)) / rg1 ≡ g0 (x / dg1)).
    {
      rewrite plus_comm, mult_comm, Nat.div_add by auto.
      + assert(x mod dg1 < dg1). {
          apply modulo_smaller_than_devisor. assumption.
        }
        assert (g1 (x mod dg1) < rg1). {
          apply g1_spec. assumption.
        }
        assert (X0: g1 (x mod dg1) / rg1 ≡ 0). {
          apply Nat.div_small.  assumption.
        }
        rewrite X0.
        auto.
    }
    rewrite_clear X.

    assert (X: (rg1 * g0 (x / dg1) + g1 (x mod dg1)) mod rg1 ≡  g1 (x mod dg1)).
    {
      rewrite plus_comm, mult_comm.
      rewrite Nat.mod_add by auto.
      rewrite Nat.mod_small.
      reflexivity.
      assert (x mod dg1 < dg1).  {
        apply modulo_smaller_than_devisor.
        assumption.
      }
      auto.
    }
    rewrite_clear X.
    reflexivity.
  Qed.

  Program Lemma index_map_rule_40:
    forall n (np: n>0)
           {range_bound_h_0: ∀ x : nat, x < n → 0 + x * 1 < n}
    ,
      @identity_index_map n np = h_index_map 0 1
                                             (range_bound:=range_bound_h_0).
  Proof.
    intros.
    unfold identity_index_map, h_index_map, equiv, index_map_equiv, id.
    intros. simpl.
    symmetry. apply mult_1_r.
  Qed.


  Local Close Scope index_f_scope.

End Function_Rules.

Section IndexMapSets.

  Definition index_map_range_set
             {d r: nat}
             (f: index_map d r): FinNatSet r :=
    fun x => in_range f (proj1_sig x).

  Lemma index_map_range_set_id:
    ∀ (i o : nat) (f : index_map i o) (j : nat) (jc : j < i),
      index_map_range_set f (⟦ f ⟧ j ↾ « f » j jc).
  Proof.
    intros i o f j jc.
    unfold index_map_range_set.
    induction i.
    - inversion jc.
    - simpl.
      break_if.
      auto.
      apply in_range_shrink_index_map_domain.
      apply in_range_by_def.
      omega.
      assumption.
  Qed.

  Lemma h_index_map_range_set_dec
        {domain range: nat}
        (b s: nat)
        {range_bound: forall x, x<domain -> (b+x*s) < range}:
    FinNatSet_dec (index_map_range_set (@h_index_map domain range b s range_bound)).
  Proof.
    unfold FinNatSet_dec.
    intros y.
    unfold index_map_range_set.
    apply Decidable_decision.
    apply in_range_dec.
  Qed.

End IndexMapSets.
