Require Import Coq.Unicode.Utf8.
Require Import Coq.Arith.Arith.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Program.Basics. (* for \circ notation *)
Require Import Coq.omega.Omega.
Require Import Coq.Logic.Decidable.

Require Export Coq.Vectors.Vector.
Require Export CoLoR.Util.Vector.VecUtil.
Import VectorNotations.

Require Import CpdtTactics.
Require Import JRWTactics.
Require Import SpiralTactics.

Require Import Spiral.


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

  (* special case of even break. could be proven more generaly *)
  Lemma Vnth_fst_Vbreak
        {A:Type}
        (o : nat) (v : vector A (o + o)) (j : nat)
        (jc : j < o) (jc1 : j < o + o):
    Vnth (fst (Vbreak v)) jc = Vnth v jc1.
  Proof.
    replace (Vnth v) with (Vnth (Vapp (fst (Vbreak v)) (snd (Vbreak v)))).
    -
      rewrite Vnth_app.
      break_match.
      + omega.
      + replace g with jc by apply proof_irrelevance.
        reflexivity.
    -
      f_equal. symmetry.
      apply Vbreak_eq_app.
  Qed.

  (* special case of even break. could be proven more generaly *)
  Lemma Vnth_snd_Vbreak
        {A: Type}
        (o : nat) (v : vector A (o + o)) (j : nat)
        (jc : j < o) (jc2 : j + o < o + o):
    Vnth (snd (Vbreak v)) jc = Vnth v jc2.
  Proof.
    replace (Vnth v) with (Vnth (Vapp (fst (Vbreak v)) (snd (Vbreak v)))).
    -
      rewrite Vnth_app.
      break_match.
      +
        generalize (Vnth_app_aux o jc2 l) as g.

        assert(E: j + o - o = j) by omega.
        rewrite E.
        intros g.
        replace g with jc by apply proof_irrelevance.
        reflexivity.
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
  replace (VecUtil.Vbuild_spec_obligation_4 gen eq_refl) with (lt_0_Sn 0) by apply proof_irrelevance.
  reflexivity.
Qed.

Fact lt_0_SSn:  forall n:nat, 0<S (S n). Proof. intros;omega. Qed.

Fact lt_1_SSn:  forall n:nat, 1<S (S n). Proof. intros; omega. Qed.

Lemma Vbuild_2 B gen:
  @Vbuild B 2 gen = [gen 0 (lt_0_SSn 0) ; gen 1 (lt_1_SSn 0)].
Proof.
  unfold Vbuild.
  simpl.
  replace (VecUtil.Vbuild_spec_obligation_4 gen eq_refl) with (lt_0_SSn 0) by apply proof_irrelevance.
  replace (VecUtil.Vbuild_spec_obligation_3 gen eq_refl
                                            (VecUtil.Vbuild_spec_obligation_4
                                               (fun (i : nat) (ip : i < 1) =>
                                                  gen (S i) (VecUtil.Vbuild_spec_obligation_3 gen eq_refl ip)) eq_refl)) with (lt_1_SSn 0) by apply proof_irrelevance.
  reflexivity.
Qed.


Definition Vin_aux {A} {n} (v : vector A n) (x : A) : Prop := Vin x v.

Section Vnth.

  (* Convenience method, swapping arguments on Vnth *)
  Definition Vnth_aux {A:Type} {n i:nat} (ic:i<n) (a: vector A n) :=
    Vnth a ic.

  Lemma Vnth_0
        {B} {n} (v:vector B (S n)) (ip: 0<(S n)):
    Vnth (i:=0) v ip = Vhead v.
  Proof.
    dep_destruct v.
    simpl.
    reflexivity.
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
    replace (lt_S_n ip) with ip' by apply proof_irrelevance.
    reflexivity.
  Qed.

  Lemma Vnth_cast_index:
    forall {B} {n : nat} i j (ic: i<n) (jc: j<n) (x : vector B n),
      i = j -> Vnth x ic = Vnth x jc.
  Proof.
    intros B n i j ic jc x E.
    crush.
    replace ic with jc by apply proof_irrelevance.
    reflexivity.
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
      replace (lt_S_n ic) with ic' in H by apply proof_irrelevance.
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
      replace (lt_S_n ic) with ic' in Pt by apply proof_irrelevance.
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
      replace (lt_S_n ic') with ic by apply proof_irrelevance.
      replace (lt_S_n jc') with jc by apply proof_irrelevance.
      auto.
    }
    auto.
  Qed.

  (* All vector's element except one with given index satisfy given perdicate. It is not known wether the remaining element satisfy it is or not *)
  Definition VAllButOne
             {n} {T:Type}
             (P: T -> Prop)
             (x: vector T n)
             i (ic:i<n) :=
    (forall j (jc:j<n), ¬(i = j) -> P (Vnth x jc)).

  (* Always works in this direction *)
  Definition VAllButOne_Sn
             {n} {T:Type}
             (P: T -> Prop)
             (h: T)
             (t: vector T n)
             i (ic: S i < S n) (ic': i < n):
    VAllButOne P (Vcons h t) (S i) ic -> VAllButOne P t i ic'.
  Proof.
    intros H.
    unfold VAllButOne in *.
    intros j jc N.
    assert(jc': S j < S n) by omega.
    assert(N':S i ≠ S j) by omega.
    specialize (H (S j) jc' N').
    rewrite <- Vnth_Sn with (v:=h) (ip:=jc').
    assumption.
  Qed.

  (* In this direction requires additional assumtion  ¬ P h *)
  Lemma VAllButOne_Sn'
        (T : Type)
        (P : T → Prop)
        (h : T)
        (n : nat)
        (x : vector T n)
        (N: ¬ P h)
        (i : nat) (ic : i < n) (ic': S i < S n):
    VAllButOne (not ∘ P) x i ic -> VAllButOne (not ∘ P) (h :: x) (S i) ic'.
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

  Lemma VallButOne_Vunique
        {n} {T:Type}
        (P: T -> Prop)
        {Pdec: forall a, {P a}+{¬(P a)}}
        (x: vector T n)
    :
      (exists i ic, VAllButOne (not∘P) x i ic) ->
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

  (* TODO: Too weak. does not guarantee ^P in second disjunct *)
  Lemma Vunique_cases
        {n} {T:Type}
        (P: T -> Prop)
        `{D: forall (a:T), {P a}+{¬P a}}
        (x: vector T n):
    Vunique P x ->
    ({Vforall (not ∘ P) x}+{exists i ic, VAllButOne (not∘P) x i ic}).
  Proof.
    intros U.
    induction x.
    - left.
      crush.
    -
      destruct (D h).
      + right.
        exists 0, (@zero_lt_Sn n).
        admit.
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

End VMap2_Indexed.


Definition Lst {B:Type} (x:B) := [x].

Lemma Vin_cons:
  forall (T:Type) (h : T) (n : nat) (v : vector T n) (x : T),
    Vin x (Vcons h v) -> x = h \/ Vin x v.
Proof.
  crush.
Qed.
