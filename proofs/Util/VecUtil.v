
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality. (* for dependent induction *)
Require Import Omega.
Require Import Coq.Logic.FunctionalExtensionality.

Require Export Coq.Vectors.Vector.
Require Export CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

Require Import Helix.Tactics.HelixTactics.
Require Import Helix.Util.Misc.
Require Import Helix.Util.FinNat.

Require Import Lia.

Local Open Scope program_scope. (* for \circ notation *)
Open Scope vector_scope.

(* Re-define :: List notation for vectors. Probably not such a good idea *)
Notation "h :: t" := (cons h t) (at level 60, right associativity)
                     : vector_scope.


(* Split vector into a pair: first  'p' elements and the rest. *)
Definition vector2pair {A:Type} (p:nat) {t:nat} (v:vector A (p+t)) : (vector A p)*(vector A t) :=
  @Vbreak A p t v.

(* Split vector into a pair: first  'p' elements and the rest. *)
Definition pair2vector {A:Type} {i j:nat} (p:(vector A i)*(vector A j)) : (vector A (i+j))  :=
  match p with
    (a,b) => Vapp a b
  end.

Lemma vp2pv: forall {T:Type} i1 i2 (p:((vector T i1)*(vector T i2))),
    vector2pair i1 (pair2vector p) = p.
Proof.
  intros.
  unfold vector2pair.
  destruct p.
  unfold pair2vector.
  apply Vbreak_app.
Qed.

Lemma Vmap_cons: forall A B (f:A->B) n (x:A) (xs: vector A n),
    Vmap f (Vcons x xs) = Vcons (f x) (Vmap f xs).
Proof.
  intros.
  constructor.
Qed.

Lemma Vmap_Vconst
      {n : nat}
      {A B: Type}
      {f: A -> B}
      (x : A):
  Vmap f (Vconst x n) = Vconst (f x) n.
Proof.
  induction n.
  -
    auto.
  -
    simpl.
    rewrite IHn.
    reflexivity.
Qed.

Lemma VMapp2_app:
  forall {A B} {f: A->A->B} (n m : nat)
    {a b: vector A m} {a' b':vector A n},
    Vmap2 f (Vapp a a') (Vapp b b')
    = Vapp (Vmap2 f a b) (Vmap2 f a' b').
Proof.
  intros A B f n m a b a' b'.
  induction m.
  - VOtac.
    reflexivity.
  - VSntac a. VSntac b.
    simpl.
    rewrite IHm.
    reflexivity.
Qed.

Lemma Vmap2_Vmap
      {A1 A2 B1 B2 C: Type}
      {n: nat}
      {x1: vector A1 n}
      {x2: vector A2 n}
      {g1: A1->B1}
      {g2: A2->B2}
      {f: B1 -> B2 -> C}
  :
    Vmap2 f
          (Vmap g1 x1)
          (Vmap g2 x2)
    =
    Vmap2 (fun a b => f (g1 a) (g2 b)) x1 x2.
Proof.
  induction n.
  -
    reflexivity.
  -
    simpl.
    rewrite <- IHn.
    dep_destruct  x1.
    dep_destruct  x2.
    reflexivity.
Qed.

Section VFold.

  Lemma Vfold_right_cons: forall A B n (f:A->B->B) (id:B) (h:A) (v:vector A n),
      Vfold_right f (Vcons h v) id = f h (Vfold_right f v id).
  Proof.
    intros.
    reflexivity.
  Qed.

  Lemma Vfold_right_reduce: forall A B n (f:A->B->B) (id:B) (v:vector A (S n)),
      Vfold_right f v id = f (hd v) (Vfold_right f (tl v) id).
  Proof.
    intros.
    dep_destruct v.
    reflexivity.
  Qed.

  (* It directly follows from definition, but haiving it as sepearate lemma helps to do rewiring *)
  Lemma Vfold_left_rev_cons:
    forall A B {n} (f : B->A->B) (b:B) (x: A) (xs : vector A n),
      Vfold_left_rev f b (Vcons x xs) = f (Vfold_left_rev f b xs) x.
  Proof.
    intros A B n f b x xs.
    reflexivity.
  Qed.

  Lemma Vfold_right_Vmap
        {A B C: Type}
        {n: nat}
        (f : A->B->B)
        (g : C->A)
        (x : vector C n)
        (z:B)
    : Vfold_right f (Vmap g x) z = Vfold_right (f∘g) x z.
  Proof.
    induction x.
    - crush.
    - simpl.
      rewrite IHx.
      unfold compose.
      reflexivity.
  Qed.

End VFold.

Section VBreak.
  Lemma Vbreak_arg_app:
    forall {B} (m n : nat) (x : vector B (m + n)) (a: vector B m) (b: vector B n),
      Vbreak x = (a, b) -> x = Vapp a b.
  Proof.
    intros B m n x a b V.
    rewrite Vbreak_eq_app with (v:=x).
    rewrite V.
    reflexivity.
  Qed.

  Lemma Vbreak_preserves_values {A} {n1 n2} {x: vector A (n1+n2)} {x0 x1}:
    Vbreak x = (x0, x1) ->
    forall a, Vin a x <-> ((Vin a x0) \/ (Vin a x1)).
  Proof.
    intros B a.
    apply Vbreak_arg_app in B.
    subst.
    split.
    apply Vin_app.
    intros.
    destruct H.
    apply Vin_appl; assumption.
    apply Vin_appr; assumption.
  Qed.

  Lemma Vbreak_preserves_P {A} {n1 n2} {x: vector A (n1+n2)} {x0 x1} {P}:
    Vbreak x = (x0, x1) ->
    (Vforall P x -> ((Vforall P x0) /\ (Vforall P x1))).
  Proof.
    intros B D.
    assert(N: forall a, Vin a x -> P a).
    {
      intros a.
      apply Vforall_in with (v:=x); assumption.
    }
    (split;
     apply Vforall_intro; intros x2 H;
     apply N;
     apply Vbreak_preserves_values with (a:=x2) in B;
     destruct B as [B0 B1];
     apply B1) ;
      [left | right]; assumption.
  Qed.

  Lemma Vnth_fst_Vbreak
        {A:Type}
        (m n : nat)
        (v : vector A (m + n))
        (j : nat) (jc : j < m)
        (jc1 : j < m + n):
    Vnth (fst (Vbreak v)) jc = Vnth v jc1.
  Proof.
    replace (Vnth v) with (Vnth (Vapp (fst (Vbreak v)) (snd (Vbreak v)))).
    -
      rewrite Vnth_app.
      break_match.
      + omega.
      + apply f_equal, le_unique.
    -
      f_equal. symmetry.
      apply Vbreak_eq_app.
  Qed.

  Lemma Vnth_snd_Vbreak
        {A: Type}
        (m n : nat)
        (v : vector A (m + n)) (j : nat)
        (jc : j < n)
        (jc2 : j + m < m + n):
    Vnth (snd (Vbreak v)) jc = Vnth v jc2.
  Proof.
    replace (Vnth v) with (Vnth (Vapp (fst (Vbreak v)) (snd (Vbreak v)))).
    -
      rewrite Vnth_app.
      break_match.
      +
        generalize (Vnth_app_aux n jc2 l) as g.

        assert(E: j + m - m = j).
        {
          rewrite NatUtil.plus_minus_eq.
          reflexivity.
        }
        rewrite E.
        intros g.
        apply f_equal, le_unique.
      + omega.
    -
      f_equal. symmetry.
      apply Vbreak_eq_app.
  Qed.

End VBreak.

Lemma vec_eq_elementwise n B (v1 v2: vector B n):
  Vforall2 eq v1 v2 -> (v1 = v2).
Proof.
  induction n.
  + dep_destruct v1. dep_destruct v2.
    auto.
  + dep_destruct v1. dep_destruct v2.
    intros H.
    rewrite Vforall2_cons_eq in H.
    destruct H as [Hh Ht].
    apply IHn in Ht.
    rewrite Ht, Hh.
    reflexivity.
Qed.

Lemma Vmap_Vbuild n B C (fm: B->C) (fb : forall i : nat, i < n -> B):
  Vmap fm (Vbuild fb) = Vbuild (fun z zi => fm (fb z zi)).
Proof.
  apply vec_eq_elementwise.
  apply Vforall2_intro_nth.
  intros i ip.
  rewrite Vnth_map.
  rewrite 2!Vbuild_nth.
  reflexivity.
Qed.

Lemma Vexists_Vbuild:
  forall (T:Type) (P: T -> Prop) (n:nat) {f},
    Vexists P (Vbuild (n:=n) f) <-> exists i (ic:i<n), P (f i ic).
Proof.
  intros T P n f.
  split.
  - intros E.
    apply Vexists_eq in E.
    destruct E as[x [V Px]].
    apply Vin_nth in V.
    destruct V as [i [ip V]].
    rewrite Vbuild_nth in V.
    subst x.
    exists i, ip.
    apply Px.
  - intros H.
    apply Vexists_eq.
    destruct H as [i [ic H]].
    exists (f i ic).
    split.
    +
      apply Vin_build.
      exists i, ic.
      reflexivity.
    + assumption.
Qed.

Lemma Vbuild_0:
  forall B gen, @Vbuild B 0 gen = @Vnil B.
Proof.
  intros B gen.
  auto.
Qed.

Lemma Vbuild_1 B gen:
  @Vbuild B 1 gen = [gen 0 (lt_0_Sn 0)].
Proof.
  unfold Vbuild.
  simpl.

  apply Vcons_eq.
  split.
  - apply f_equal, le_unique.
  - reflexivity.
Qed.

Fact lt_0_SSn:  forall n:nat, 0<S (S n). Proof. intros;omega. Qed.

Fact lt_1_SSn:  forall n:nat, 1<S (S n). Proof. intros; omega. Qed.

Lemma Vbuild_2 B gen:
  @Vbuild B 2 gen = [gen 0 (lt_0_SSn 0) ; gen 1 (lt_1_SSn 0)].
Proof.
  unfold Vbuild.
  simpl.


  apply Vcons_eq.
  split.
  - apply f_equal, le_unique.
  - apply Vcons_eq.
    split.
    + apply f_equal, le_unique.
    + reflexivity.
Qed.


Definition Vin_aux {A} {n} (v : vector A n) (x : A) : Prop := Vin x v.

Section Vnth.

  Lemma Vnth_arg_eq:
    forall (A : Type) (n : nat) (v1 v2 : vector A n)
      (i : nat) (ip : i < n), v1 = v2 -> Vnth v1 ip = Vnth v2 ip.
  Proof.
    crush.
  Qed.

  (* Convenience method, swapping arguments on Vnth *)
  Definition Vnth_aux {A:Type} {n i:nat} (ic:i<n) (a: vector A n) :=
    Vnth a ic.

  Lemma Vnth_to_Vnth_aux
        {A:Type} {n i:nat} (ic:i<n) (a: vector A n):
    Vnth a ic = Vnth_aux ic a.
  Proof.
    unfold Vnth_aux.
    reflexivity.
  Qed.

  Lemma Vnth_0
        {B} {n} (v:vector B (S n)) (ip: 0<(S n)):
    Vnth (i:=0) v ip = Vhead v.
  Proof.
    dep_destruct v.
    simpl.
    reflexivity.
  Qed.

  Lemma Vnth_1_Vhead
        {T:Type}
        (x:vector T 1)
        (i:nat) (ic: Peano.lt i 1)
    :
      Vnth x ic = Vhead x.
  Proof.
    destruct i.
    -
      rewrite Vnth_0.
      reflexivity.
    - omega.
  Qed.

  Lemma Vnth_1
        {T:Type}
        (x:T)
        (i:nat) (ic: Peano.lt i 1)
    :
      Vnth [x] ic = x.
  Proof.
    destruct i.
    - auto.
    - omega.
  Qed.

  Lemma Vnth_Sn {B} (n i:nat) (v:B) (vs:vector B n) (ip: S i< S n) (ip': i< n):
    Vnth (Vcons v vs) ip = Vnth vs ip'.
  Proof.
    simpl.
    apply f_equal, le_unique.
  Qed.

  Lemma Vnth_cast_index:
    forall {B} {n : nat} i j (ic: i<n) (jc: j<n) (x : vector B n),
      i = j -> Vnth x ic = Vnth x jc.
  Proof.
    intros B n i j ic jc x E.
    crush.
    apply f_equal, le_unique.
  Qed.

  Lemma P_Vnth_Vcons {T:Type} {P:T -> Prop} {n:nat} (h:T) (t:vector T n):
    forall i (ic:i<S n) (ic': (pred i) < n),
      P (Vnth (Vcons h t) ic) -> P h \/ P (Vnth t ic').
  Proof.
    intros i ic ic' H.
    destruct i.
    + left.
      auto.
    + right.
      simpl in H.
      rewrite (le_unique _ _ ic' (lt_S_n ic)).
      apply H.
  Qed.

  Lemma P_Vnth_Vcons_not_head {T:Type} {P:T -> Prop} {n:nat} (h:T) (t:vector T n):
    forall i (ic:i<S n) (ic': (pred i) < n),
      not (P h) -> P (Vnth (Vcons h t) ic) -> P (Vnth t ic').
  Proof.
    intros i ic ic' Ph Pt.
    destruct i.
    - simpl in Pt; congruence.
    - simpl in Pt.
      rewrite (le_unique _ _ ic' (lt_S_n ic)).
      apply Pt.
  Qed.

End Vnth.

Lemma Vbuild_cons:
  forall B n (gen : forall i, i < S n -> B),
    Vbuild gen = Vcons (gen 0 (lt_O_Sn n)) (Vbuild (fun i ip => gen (S i) (lt_n_S ip))).
Proof.
  intros B n gen.
  rewrite <- Vbuild_head.
  rewrite <- Vbuild_tail.
  auto.
Qed.

Lemma Vforall_Vbuild (T : Type) (P:T -> Prop) (n : nat) (gen : forall i : nat, i < n -> T):
  Vforall P (Vbuild gen) <-> forall (i : nat) (ip : i < n), P (gen i ip).
Proof.
  split.
  - intros H i ip.
    apply Vforall_nth with (ip:=ip) in H.
    rewrite Vbuild_nth in H.
    apply H.
  - intros H.
    apply Vforall_nth_intro.
    intros i ip.
    rewrite Vbuild_nth.
    apply H.
Qed.

Lemma Vbuild_Vapp
      {A: Type}
      {n m: nat}
      {f: forall (t:nat), (t<n+m) -> A}
  : Vbuild f =
    @Vapp A n m
          (Vbuild (fun t (tc:t<n) => f t (Nat.lt_lt_add_r t n m tc)))
          (Vbuild (fun t (tc:t<m) => f (t+n) (add_lt_lt tc))).
Proof.
  apply Veq_nth.
  intros i ip.
  rewrite Vbuild_nth.
  rewrite Vnth_app.
  break_match.
  -
    rewrite Vbuild_nth.
    generalize (@add_lt_lt n m (i - n) (@Vnth_app_aux n m i ip l)).
    intros ic.
    remember (i - n + n) as Q.
    replace (i - n + n) with i in HeqQ.
    subst Q.
    apply f_equal, le_unique.
    lia.
  -
    rewrite Vbuild_nth.
    apply f_equal, le_unique.
Qed.

Lemma Vbuild_range_cast
      {A: Type}
      {n m: nat}
      {f: forall (t:nat), (t<n) -> A}
      (E: m=n)
:
  @Vbuild A n f =
  Vcast (
      @Vbuild A m (fun t tc => f t (eq_lt_lt E tc))
    ) E.
Proof.
  apply Veq_nth.
  intros i ip.
  rewrite Vnth_cast.
  rewrite 2!Vbuild_nth.
  f_equal.
  apply le_unique.
Qed.

Program Definition Vbuild_split_at_def
        {A: Type}
        {n m: nat}
        {f: forall (t:nat), (t<n+(S m)) -> A}
  := Vbuild f =
            @Vapp A n (S m)
            (Vbuild (fun t (tc:t<n) => f t _))
            (Vcons
               (f n _)
               (Vbuild (fun t (tc:t<m) => f (t+1+n) _))
            ).
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.

Lemma Vbuild_split_at
      {A: Type}
      (n m: nat)
      {f: forall (t:nat), (t<n+(S m)) -> A}: @Vbuild_split_at_def A n m f.

Proof.
  unfold Vbuild_split_at_def.
  rewrite Vbuild_Vapp.
  f_equal.
  -
    apply Veq_nth.
    intros i ip.
    rewrite 2!Vbuild_nth.
    f_equal.
    apply le_unique.
  -
    rewrite Vbuild_cons.
    simpl.
    f_equal.
    +
      f_equal.
      apply le_unique.
    +
      apply Veq_nth.
      intros i ip.
      rewrite 2!Vbuild_nth.
      assert(E: i+1+n = S (i+n) ) by omega.
      symmetry.
      forall_n_lt_eq.
Qed.

Section Vunique.
  Local Open Scope nat_scope.

  (* There is at most one element in vector satisfying given predicate *)
  Definition Vunique
             {n} {T:Type}
             (P: T -> Prop)
             (v: vector T n) :=

    (forall (i: nat) (ic: i < n) (j: nat) (jc: j < n),
        (P (Vnth v ic) /\ P (Vnth v jc)) -> i = j).

  Lemma Vunique_Vnil (T : Type) (P : T -> Prop):
    Vunique P (@Vnil T).
  Proof.
    unfold Vunique.
    intros i ic j jc H.
    nat_lt_0_contradiction.
  Qed.

  Lemma Vforall_notP_Vunique:
    forall (n : nat) (T : Type) (P : T -> Prop) (v : vector T n),
      Vforall (not ∘ P) v -> Vunique P v.
  Proof.
    intros n T P v.
    induction v.
    - intros H.
      apply Vunique_Vnil.
    -
      intros H.
      unfold Vunique in *.
      intros i ic j jc V.
      destruct V.
      apply Vforall_nth with (i:=i) (ip:=ic) in H.
      congruence.
  Qed.


  Lemma Vunique_P_Vforall_notP:
    forall (n : nat) (T : Type) (P : T -> Prop) (h:T) (x : vector T n),
      P(h) /\ Vunique P (h::x) -> Vforall (not ∘ P) x.
  Proof.
    intros n T P h x [H V].
    unfold Vunique in V.
    specialize (V 0 (zero_lt_Sn n)).
    simpl (Vnth (h :: x) (zero_lt_Sn n)) in V.
    apply Vforall_nth_intro; intros i ip.
    unfold compose.
    specialize (V (S i) (lt_n_S ip)).
    replace (Vnth (h :: x) (lt_n_S ip)) with (Vnth x ip) in V.
    contradict V.
    crush.
    simpl.
    apply f_equal, le_unique.
  Qed.

  Lemma Vunique_cons_not_head
        {n} {T:Type}
        (P: T -> Prop)
        (h: T) (t: vector T n):
    not (P h) /\ Vunique P t -> Vunique P (Vcons h t).
  Proof.
    intros H.
    destruct H as [Ph Pt].
    unfold Vunique.
    intros i ic j jc H.
    destruct H as [Hi Hj].

    destruct i,j.
    - reflexivity.
    - simpl in Hi. congruence.
    - simpl in Hj. congruence.
    -
      assert(ic': pred (S i) < n) by (apply lt_S_n; apply ic).
      apply P_Vnth_Vcons_not_head with (ic'0:=ic') in Hi; try apply Ph.

      assert(jc': pred (S j) < n) by (apply lt_S_n; apply jc).
      apply P_Vnth_Vcons_not_head with (ic'0:=jc') in Hj; try apply Ph.

      f_equal.
      unfold Vunique in Pt.
      apply Pt with (ic:=ic') (jc:=jc').
      split; [apply Hi| apply Hj].
  Qed.

  Lemma Vunique_cons_head
        {n} {T:Type}
        (P: T -> Prop)
        (h: T) (t: vector T n):
    P h /\ (Vforall (not ∘ P) t) -> Vunique P (Vcons h t).
  Proof.
    intros H.
    destruct H as [Ph Pt].
    unfold Vunique.
    intros i ic j jc H.
    destruct H as [Hi Hj].

    destruct i, j.
    - reflexivity.
    -
      assert(jc':j < n) by omega.
      apply Vforall_nth with (i:=j) (ip:=jc') in Pt.
      unfold compose in Pt.
      rewrite Vnth_Sn with (ip:=jc) (ip':=jc') in Hj.
      congruence.
    -
      assert(ic':i < n) by omega.
      apply Vforall_nth with (i:=i) (ip:=ic') in Pt.
      unfold compose in Pt.
      rewrite Vnth_Sn with (ip:=ic) (ip':=ic') in Hi.
      congruence.
    -
      assert(jc':j < n) by omega.
      apply Vforall_nth with (i:=j) (ip:=jc') in Pt.
      unfold compose in Pt.
      rewrite Vnth_Sn with (ip:=jc) (ip':=jc') in Hj.
      congruence.
  Qed.

  Lemma Vunique_cons {n} {T:Type}
        (P: T -> Prop)
        (h: T) (t: vector T n):
    ((P h /\ (Vforall (not ∘ P) t)) \/
     (not (P h) /\ Vunique P t))
    ->
    Vunique P (Vcons h t).
  Proof.
    intros H.
    destruct H.
    apply Vunique_cons_head; auto.
    apply Vunique_cons_not_head; auto.
  Qed.
  Lemma Vunique_cons_tail {n}
        {T:Type} (P: T -> Prop)
        (h : T) (t : vector T n):
    Vunique P (Vcons h t) -> Vunique P t.
  Proof.
    intros H.
    unfold Vunique in *.
    intros i ic j jc [Vi Vj].
    assert(S i = S j).
    {
      assert(ic': S i < S n) by omega.
      assert(jc': S j < S n) by omega.
      apply H with (ic:=ic') (jc:=jc').
      simpl.
      rewrite (le_unique _ _ (lt_S_n ic') ic).
      rewrite (le_unique _ _ (lt_S_n jc') jc).
      auto.
    }
    auto.
  Qed.

  (* All vector's element except one with given index satisfy given perdicate. It is not known wether the remaining element satisfy it is or not *)
  Definition VAllButOne
             {n} {T:Type}
             i (ic:i<n)
             (P: T -> Prop)
             (x: vector T n)
    :=
      (forall j (jc:j<n), ~(i = j) -> P (Vnth x jc)).

  Lemma VallButOne_Sn_cons_not_head
        {T: Type}
        (h : T)
        (n : nat)
        (v : vector T n)
        (P: T -> Prop)
        (i : nat)
        (ic : S i < S n):
    VAllButOne (S i) ic (not ∘ P) (Vcons h v) -> not (P h).
  Proof.
    intros H.
    unfold VAllButOne in H.
    specialize (H 0).
    unfold compose in H.
    simpl in H.
    apply H ; omega.
  Qed.

  Lemma VAllButOne_0_Vforall
        {T}
        n
        (v: T)
        (vs : vector T n)
        (kc : 0 < S n)
        (P: T -> Prop)
    :
      VAllButOne 0 kc P (Vcons v vs) -> Vforall P vs.
  Proof.
    intros H.
    unfold VAllButOne in H.
    apply Vforall_nth_intro.
    intros i ip.
    assert (ip1: S i < S n) by omega.
    assert (ip2: 0 <> S i) by omega.
    specialize (H (S i) ip1 ip2).
    simpl in *.
    rewrite (le_unique _ _  ip (lt_S_n ip1)).
    apply H.
  Qed.

  (* Always works in this direction *)
  Lemma VAllButOne_Sn
        {n} {T:Type}
        (P: T -> Prop)
        (h: T)
        (t: vector T n)
        i (ic: S i < S n) (ic': i < n):
    VAllButOne (S i) ic P (Vcons h t) -> VAllButOne i ic' P t .
  Proof.
    intros H.
    unfold VAllButOne in *.
    intros j jc N.
    assert(jc': S j < S n) by omega.
    assert(N':S i <> S j) by omega.
    specialize (H (S j) jc' N').
    rewrite <- Vnth_Sn with (v:=h) (ip:=jc').
    assumption.
  Qed.

  Lemma VallButOneSimpl
        {T}
        n
        (vl : vector T n)
        (k : nat)
        (kc : k < n)
        (P0: T -> Prop)
        (P1: T -> Prop)
        (Pimpl: forall x, P0 x -> P1 x)
    :
      VAllButOne k kc P0 vl -> VAllButOne k kc P1 vl.
  Proof.
    unfold VAllButOne.
    intros H j jc H0.
    specialize (H j jc H0).
    apply Pimpl.
    apply H.
  Qed.

  (* In this direction requires additional assumtion  ¬ P h *)
  Lemma VAllButOne_Sn'
        (T : Type)
        (P : T -> Prop)
        (h : T)
        (n : nat)
        (x : vector T n)
        (N: ~P h)
        (i : nat) (ic : i < n) (ic': S i < S n):
    VAllButOne i ic  (not ∘ P) x -> VAllButOne (S i) ic' (not ∘ P) (h :: x).
  Proof.
    intros H.
    unfold VAllButOne in *.
    intros j jc H0.
    destruct j.
    crush.
    assert(jc': j < n) by omega.
    rewrite Vnth_Sn with (ip':=jc').
    apply H.
    omega.
  Qed.

  (* In this direction requires additional assumtion  P h *)
  Lemma Vforall_VAllButOne_P0
        (T : Type)
        (P : T -> Prop)
        (h : T)
        (n : nat)
        (x : vector T n)
        (N: P h):
    Vforall (not ∘ P) x -> VAllButOne 0 (zero_lt_Sn n) (not ∘ P) (h :: x).
  Proof.
    intros H.
    unfold VAllButOne.
    intros j jc H0.
    simpl.
    break_match.
    congruence.
    apply Vforall_nth with (ip:=(lt_S_n jc)) in H.
    assumption.
  Qed.

  Lemma VallButOne_Vunique
        {n} {T:Type}
        (P: T -> Prop)
        {Pdec: forall a, {P a}+{~(P a)}}
        (x: vector T n)
    :
      (exists i ic, VAllButOne i ic (not∘P) x) ->
      Vunique P x.
  Proof.
    intros V.
    elim V. clear V. intros k V.
    elim V. clear V. intros kc V.
    destruct n.
    -
      dep_destruct x.
      apply Vunique_Vnil.
    -
      unfold VAllButOne in V.
      unfold Vunique.
      intros i ic j jc H.
      destruct H as [H0 H1].

      assert(V1:=V).
      rename V into V0.
      specialize (V0 i ic).
      specialize (V1 j jc).

      generalize dependent (Vnth x ic).
      intros x0 V0 H0. unfold compose in V0.
      generalize dependent (Vnth x jc).
      intros x1 H1 V1. unfold compose in V1.
      clear x ic jc kc.
      destruct (Pdec x0), (Pdec x1); try congruence.
      clear Pdec.

      destruct(eq_nat_dec k j).
      + subst j.
        destruct(eq_nat_dec k i).
        subst i.
        reflexivity.
        crush.
      + crush.
  Qed.

  Lemma VallButOne_Sn_cases
        {T: Type}
        (h : T)
        (n : nat)
        (v : vector T n)
        (P: T -> Prop)
        (i : nat)
        (ic : S i < S n)
        (ic' : i < n):
    VAllButOne (S i) ic (not ∘ P) (Vcons h v) <->
    (not (P h) /\ VAllButOne i ic' (not ∘ P) v).
  Proof.
    split.
    -
      intros H.
      split.
      + apply VallButOne_Sn_cons_not_head in H.
        apply H.
      +
        apply VAllButOne_Sn with (h0:=h) (ic0:=ic).
        apply H.
    -
      intros [H0 H1].
      apply VAllButOne_Sn' with (ic:=ic').
      apply H0.
      apply H1.
  Qed.

  Lemma Vunique_cases
        {n} {T:Type}
        (P: T -> Prop)
        `{D: forall (a:T), {P a}+{~P a}}
        (x: vector T n):
    Vunique P x ->
    ({Vforall (not ∘ P) x}+{exists i ic, VAllButOne i ic (not∘P) x}).
  Proof.
    intros U.
    induction x.
    - left.
      crush.
    -
      destruct (D h).
      + right.
        assert(Ux := U); apply Vunique_cons_tail in Ux.
        specialize (IHx Ux); clear Ux.
        exists 0, (zero_lt_Sn n). (* only 0 element could be ^P *)

        apply Vforall_VAllButOne_P0; try assumption.
        apply Vunique_P_Vforall_notP with (h:=h).
        split; assumption.
      +
        apply Vunique_cons_tail in U.
        specialize (IHx U).
        clear U.
        destruct IHx.
        * left.
          crush.
        * right.
          inversion e.
          inversion H.
          clear e H.
          assert(sx0: S x0 < S n) by omega.
          exists (S x0), sx0.
          apply VAllButOne_Sn' with (ic':=sx0) (ic:=x1); assumption.
  Qed.

End Vunique.

Section Vforall.

  Variable A : Type.
  Variable P: A -> Prop.
  Variable n: nat.

  Lemma Vforall_Vhead
        {v:vector A (S n)}:
    Vforall P v -> P (Vhead v).
  Proof.
    intros H.
    eapply Vforall_nth with (i:=0) in H.
    rewrite Vhead_nth.
    apply H.
  Qed.

  Lemma Vforall_Vtail
        {v:vector A (S n)}:
    Vforall P v -> Vforall P (Vtail v).
  Proof.
    intros H.
    dep_destruct v.
    apply H.
  Qed.

End Vforall.



(* Utlity functions for vector products *)

Section VectorPairs.

  Definition Phead {A} {B} {n} (ab:(vector A (S n))*(vector B (S n))): A*B
    := match ab with
       | (va,vb) => ((Vhead va), (Vhead vb))
       end.

  Definition Ptail {A} {B} {n} (ab:(vector A (S n))*(vector B (S n))): (vector A n)*(vector B n)
    := match ab with
       | (va,vb) => ((Vtail va), (Vtail vb))
       end.

End VectorPairs.

Section VMap2_Indexed.

  Definition Vmap2Indexed {A B C : Type} {n}
             (f: nat->A->B->C) (a: vector A n) (b: vector B n)
    := Vbuild (fun i ip => f i (Vnth a ip) (Vnth b ip)).

  Definition Vmap2SigIndexed {A B C : Type} {n}
             (f: FinNat n->A->B->C) (a: vector A n) (b: vector B n)
    := Vbuild (fun i ip => f (mkFinNat ip) (Vnth a ip) (Vnth b ip)).

  Lemma Vnth_Vmap2Indexed:
    forall {A B C : Type} {n:nat} (i : nat) (ip : i < n) (f: nat->A->B->C)
      (a:vector A n) (b:vector B n),
      Vnth (Vmap2Indexed f a b) ip = f i (Vnth a ip) (Vnth b ip).
  Proof.
    intros A B C n i ip f a b.
    unfold Vmap2Indexed.
    rewrite Vbuild_nth.
    reflexivity.
  Qed.

  Lemma Vnth_Vmap2SigIndexed:
    forall {A B C : Type} {n:nat} (i : nat) (ip : i < n) (f: FinNat n->A->B->C)
      (a:vector A n) (b:vector B n),
      Vnth (Vmap2SigIndexed f a b) ip = f (mkFinNat ip) (Vnth a ip) (Vnth b ip).
  Proof.
    intros A B C n i ip f a b.
    unfold Vmap2SigIndexed.
    rewrite Vbuild_nth.
    reflexivity.
  Qed.

End VMap2_Indexed.


Definition Lst {B:Type} (x:B) := [x].

Lemma Vin_cons:
  forall (T:Type) (h : T) (n : nat) (v : vector T n) (x : T),
    Vin x (Vcons h v) -> x = h \/ Vin x v.
Proof.
  crush.
Qed.

Lemma Vin_1
      (A: Type)
      (a:A)
      (v:vector A 1)
  :
    Vin a v -> a = Vhead v.
Proof.
      intros H.
      dep_destruct v.
      dep_destruct x.
      destruct H.
      - auto.
      - contradiction.
Qed.

Lemma Vforall_not_Vexists
      {n} {T}
      (v: vector T n)
      (P: T -> Prop) :
  Vforall (not ∘ P) v -> not (Vexists P v).
Proof.
  intros A.
  unfold not.
  intros E.
  apply Vexists_eq in E.
  destruct E as [x [E E1]].
  apply Vforall_in with (x:=x) in A.
  congruence.
  apply E.
Qed.

Lemma Vforall_Vconst
      {A: Type}
      {n: nat}
      {z: A}
      {P: A->Prop}:
  P z -> Vforall P (Vconst z n).
Proof.
  intros Pz.
  apply Vforall_nth_intro.
  intros i ip.
  rewrite Vnth_const.
  apply Pz.
Qed.

Lemma Vforall_Vmap2
      {A: Type}
      {n: nat}
      {P: A->Prop}
      {f: A->A->A}
      (C: forall x y : A, P x -> P y -> P (f x y))
      {a b: vector A n}
      (PA: Vforall P a)
      (PB: Vforall P b)
  :
    Vforall P (Vmap2 f a b).
Proof.
  apply Vforall_nth_intro.
  intros i ip.
  rewrite Vnth_map2.
  apply C.
  apply Vforall_nth, PA.
  apply Vforall_nth, PB.
Qed.

Lemma Vtail_1:
  forall {A:Type} (x:vector A 1), (Vtail x = @Vnil A).
Proof.
  intros A x.
  dep_destruct x.
  dep_destruct x0.
  simpl.
  reflexivity.
Qed.

Lemma V0_V0_eq:
  forall {A:Type} (x y:vector A 0), x=y.
Proof.
  intros A x y.
  dep_destruct x.
  dep_destruct y.
  reflexivity.
Qed.

Lemma vector1_eq_Vhead_eq
      {A: Type}
      {a b: vector A 1}:
  Vhead a = Vhead b -> a = b.
Proof.
  intros H.
  dep_destruct a.
  dep_destruct b.
  dep_destruct x.
  dep_destruct x0.
  simpl in H.
  apply Vcons_eq_intro.
  assumption.
  reflexivity.
Qed.

Require Import CoLoR.Util.List.ListUtil.

Section List_of_Vec.

  Lemma list_of_vec_eq {A:Type} {n:nat} (v1 v2 : vector A n) :
    list_of_vec v1 = list_of_vec v2 -> v1 = v2.
  Proof.
    induction n.
    -
      dep_destruct v1.
      dep_destruct v2.
      reflexivity.
    -
      intros H.
      dep_destruct v1.
      dep_destruct v2.
      inversion H.
      apply Vcons_eq_intro; auto.
  Qed.

  Lemma list_of_vec_length {A:Type} {n:nat} {v : vector A n} :
    length (list_of_vec v) = n.
  Proof.
    induction n.
    -
      dep_destruct v.
      reflexivity.
    -
      dep_destruct v.
      simpl.
      apply eq_S.
      auto.
  Qed.

  Lemma list_of_vec_vec_of_list {A:Type} {l : list A} :
    list_of_vec (vec_of_list l) = l.
  Proof.
    induction l.
    -
      reflexivity.
    -
      simpl.
      rewrite IHl.
      reflexivity.
  Qed.

  Lemma list_of_vec_Vcast {A:Type} {m n:nat} (v : vector A m) {E:m=n}:
    list_of_vec (Vcast v E) = list_of_vec v.
  Proof.
    dependent induction m.
    -
      crush.
    -
      destruct n; try congruence.
      dep_destruct v.
      simpl.
      rewrite Vcast_cons.
      simpl.
      apply tail_eq.
      eapply IHm.
  Qed.

  (* Note: no [default] param for [nth] is not specified *)
  Lemma nth_cons {A:Type} (l: list A) (a:A) (i:nat):
    nth (S i) (a::l) = nth i l.
  Proof.
    crush.
  Qed.

  (* Note: no [default] param for [nth] is not specified *)
  Lemma list_eq_nth {A:Type} (l1 l2: list A):
    (length l1 = length l2) ->
    (forall i (ic1:i<length l1), nth i l1 = nth i l2) ->
    l1 = l2.
  Proof.
    revert l1 l2.
    induction l1.
    -
      intros L N.
      simpl in L.
      symmetry.
      apply length_zero_iff_nil.
      auto.
    -
      intros l2 L F.
      destruct l2.
      crush.
      apply cons_eq.
      +
        assert(H1: 0 < length (a :: l1)) by crush.
        specialize (F 0 H1).
        simpl in F.
        apply equal_f in F.
        auto.
        exact a0.
      +
        apply IHl1.
        *
          auto.
        *
          intros i ic1.
          rewrite <- nth_cons with (a1:=a).
          rewrite <- nth_cons with (a1:=a0) (l:=l2).
          apply F; crush.
  Qed.

  (* Note: no [default] param for [nth] is not specified *)
  Lemma nth_Vnth {A:Type} {n:nat} {v:vector A n} (i:nat) (ic:i<n):
    nth i (list_of_vec (v)) = fun _ => Vnth v ic.
  Proof.
    revert i ic.
    dependent induction v.
    -
      intros i ic.
      nat_lt_0_contradiction.
    -
      intros i ic.
      destruct i.
      +
        reflexivity.
      +
        simpl.
        apply IHv.
  Qed.

  Lemma list_of_vec_Vapp {A:Type} {m n:nat} {v1: vector A m} {v2: vector A n}:
    list_of_vec (Vapp v1 v2) = List.app (list_of_vec v1) (list_of_vec v2).
  Proof.
    apply list_eq_nth.
    -
      rewrite app_length.
      repeat rewrite list_of_vec_length.
      auto.
    -
      intros i ic1.
      rewrite list_of_vec_length in ic1.
      rewrite nth_Vnth with (ic:=ic1).
      rewrite Vnth_app.
      break_match.
      +
        rewrite <- nth_Vnth.
        extensionality x.
        rewrite app_nth2.
        rewrite list_of_vec_length.
        reflexivity.
        rewrite list_of_vec_length.
        auto.
      +
        rewrite <- nth_Vnth.
        extensionality x.
        rewrite app_nth1.
        reflexivity.
        rewrite list_of_vec_length.
        auto.
  Qed.

End List_of_Vec.


(* --- Some tactics --- *)

(* Given a `Vnth x i0 ic0 = Vnth y i1 ic0` and a hypotheis `i0=i1` reduces goal to `x=y`. *)
Ltac Vnth_eq_index_to_val_eq :=
  let lc := fresh in
  let rc := fresh in
  let Q := fresh in
  let HeqQ := fresh in
  match goal with
  | [ H: ?i0 = ?i1 |- @Vnth ?t ?s ?v0 ?i0 ?ic0 = @Vnth ?t ?s ?v1 ?i1 ?ic1] =>
    generalize ic0 as lc;
    generalize ic1 as rc;
    intros rc lc ;
    remember i0 as Q eqn:HeqQ;
    rewrite H in HeqQ;
    subst Q;
    rewrite (le_unique _ _ lc rc);
    apply Vnth_arg_eq;
    clear rc lc HeqQ
  end.
