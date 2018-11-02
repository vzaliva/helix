(* Finite natural numbers. TODO: remove, probably unused *)

Require Import Coq.Arith.Arith Coq.Arith.Minus Coq.Arith.Plus Coq.Arith.EqNat Coq.Arith.Lt.
Require Export Coq.Init.Specif.
Require Import Helix.Tactics.HelixTactics.
Require Import Helix.Util.Misc.

Require Import Psatz.

Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.orders.minmax.
Require Import MathClasses.implementations.peano_naturals.

Import ArithRing.

Notation FinNat n := {x:nat | (x<n)%nat}.
Definition mkFinNat {n} {j:nat} (jc:(j<n)%nat) : FinNat n := @exist _ (gt n) j jc.

Local Open Scope nat_scope.

Definition mkSFinNat {d: nat} (x:FinNat d): FinNat (S d) :=
  let (x, xc) := x in
  let sxc : x < S d := le_S xc in mkFinNat sxc.

Definition mkSFinNat' {d d': nat} (E: d ≡ S d'): FinNat d
  := @mkFinNat d d' (eq_ind_r (fun d0 => d' < d0) (le_n (S d')) E).

Lemma mkSFinNat_proj1_eq {d: nat} (x:FinNat d):
  proj1_sig x ≡ proj1_sig (mkSFinNat x).
Proof.
  unfold mkSFinNat.
  break_let.
  reflexivity.
Qed.

Program Definition expandFinNat {d d': nat} (E: d ≡ S d') (x:FinNat d'): FinNat d
  := @mkFinNat d (proj1_sig x) _.

(* TODO: rework *)
Definition castFinNat {n m:nat} {d:nat} (E:m+d=n) (a: FinNat m): FinNat n.
Proof.
  destruct a as [x xc].
  assert(C: x<n).
  {
    rewrite <- E.
    apply lt_plus_trans.
    apply xc.
  }
  exact (mkFinNat C).
Defined.

Definition FinNat_bloat
           {m n:nat}
           (mn: (m < n)%nat):
  FinNat m -> FinNat n.
Proof.
  intros H.
  destruct H.
  assert (xc:(x<n)%nat).
  apply Nat.lt_trans with (m:=m); auto.
  exact (mkFinNat xc).
Defined.

Global Instance FinNat_bloat_proper
       {m n:nat}
       (mn: (m<n)%nat):
  Proper ((=) ==> (=)) (FinNat_bloat mn).
Proof.
  intros x y H.
  destruct x, y.
  unfold FinNat_bloat.
  inversion H.
  simpl in H0.
  clear H.
  unfold mkFinNat.
  unfold equiv, Sig_Equiv.
  simpl.
  rewrite H0.
  reflexivity.
Qed.

(* Quick and dirty  *)
Program Definition FN_div {n m:nat} (a: FinNat n) (b: FinNat m) : FinNat n
  := let (x, xc) := a in
     let (y, yc) := b in
     let d := Nat.div x y in
     @mkFinNat n d _.
Next Obligation.
  destruct y.
  -
    crush.
  -
    apply PeanoNat.Nat.div_lt_upper_bound.
    auto.
    nia.
Defined.

(* Quick and dirty  *)
Program Definition FN_mod {n m:nat} (a: FinNat n) (b: FinNat m) : FinNat m
  := let (x, xc) := a in
     let (y, yc) := b in
     let d := Nat.modulo x y in
     @mkFinNat m d _.
Next Obligation.
  destruct y.
  -
    unfold Nat.modulo.
    auto.
  -
    pose proof PeanoNat.Nat.mod_upper_bound x (S y) as U.
    assert(S: S y ≢ 0) by auto.
    specialize (U S).
    nia.
Defined.

(* Quick and dirty  *)
Program Definition FN_plus {n m:nat} (a: FinNat n) (b: FinNat m) : FinNat (n + m)
  := let (x, xc) := a in
     let (y, yc) := b in
     let d := x + y in
     @mkFinNat _ d _.
Next Obligation.
  nia.
Defined.

Program Definition FN_minus {n m:nat} (a: FinNat n) (b: FinNat m) : FinNat n
  := let (x, xc) := a in
     let (y, yc) := b in
     let d := x - y in
     @mkFinNat _ d _.
Next Obligation.
  nia.
Defined.

Program Definition FN_mult {n m:nat} (a: FinNat n) (b: FinNat m) : FinNat (n * m)
  := let (x, xc) := a in
     let (y, yc) := b in
     let d := x * y in
     @mkFinNat _ d _.
Next Obligation.
  nia.
Defined.

Program Definition FN_min {n m:nat} (a: FinNat n) (b: FinNat m) : FinNat (min n m)
  := let (x, xc) := a in
     let (y, yc) := b in
     let d := min x y in
     @mkFinNat _ d _.
Next Obligation.
  unfold min.
  unfold sort.
  break_if; break_if; simpl; auto.
  -
    clear Heqd Heqd0 a b H0 H.
    apply Compare_dec.not_le in n0.
    destruct l; nia.
  -
    clear Heqd Heqd0 a b H H0.
    apply Compare_dec.not_le in n0.
    nia.
Defined.

Program Definition FN_max {n m:nat} (a: FinNat n) (b: FinNat m) : FinNat (max n m)
  := let (x, xc) := a in
     let (y, yc) := b in
     let d := max x y in
     @mkFinNat _ d _.
Next Obligation.
  unfold max.
  unfold sort.
  break_if; break_if; simpl; auto.
  -
    clear Heqd Heqd0 a b H0 H.
    apply Compare_dec.not_le in n0.
    destruct l; nia.
  -
    clear Heqd Heqd0 a b H H0.
    apply Compare_dec.not_le in n0.
    destruct l.
    nia.
    nia.
Defined.

Global Instance castFinNat_proper {n m d:nat} {E}:
  Proper ((=) ==> (=)) (@castFinNat n m d E).
Proof.
  intros x y Exy.
  unfold castFinNat.
  repeat break_let.
  unfold mkFinNat, equiv, Sig_Equiv.
  simpl.
  auto.
Qed.

Global Instance FN_div_proper {n m:nat}:
  Proper ((=) ==> (=) ==> (=)) (@FN_div n m).
Proof.
  intros x x' Ex y y' Ey.
  unfold FN_div.
  repeat break_let.
  unfold mkFinNat, equiv, Sig_Equiv in *.
  simpl in *.
  subst.
  rewrite Ex, Ey.
  reflexivity.
Qed.

Global Instance FN_mod_proper {n m:nat}:
  Proper ((=) ==> (=) ==> (=)) (@FN_mod n m).
Proof.
  intros x x' Ex y y' Ey.
  unfold FN_mod.
  repeat break_let.
  unfold mkFinNat, equiv, Sig_Equiv in *.
  simpl in *.
  subst.
  rewrite Ex, Ey.
  reflexivity.
Qed.

Global Instance FN_plus_proper {n m:nat}:
  Proper ((=) ==> (=) ==> (=)) (@FN_plus n m).
Proof.
  intros x x' Ex y y' Ey.
  unfold FN_plus.
  repeat break_let.
  unfold mkFinNat, equiv, Sig_Equiv in *.
  simpl in *.
  subst.
  rewrite Ex, Ey.
  reflexivity.
Qed.

Global Instance FN_minus_proper {n m:nat}:
  Proper ((=) ==> (=) ==> (=)) (@FN_minus n m).
Proof.
  intros x x' Ex y y' Ey.
  unfold FN_minus.
  repeat break_let.
  unfold mkFinNat, equiv, Sig_Equiv in *.
  simpl in *.
  subst.
  rewrite Ex, Ey.
  reflexivity.
Qed.

Global Instance FN_mult_proper {n m:nat}:
  Proper ((=) ==> (=) ==> (=)) (@FN_mult n m).
Proof.
  intros x x' Ex y y' Ey.
  unfold FN_mult.
  repeat break_let.
  unfold mkFinNat, equiv, Sig_Equiv in *.
  simpl in *.
  subst.
  rewrite Ex, Ey.
  reflexivity.
Qed.

Global Instance FN_min_proper {n m:nat}:
  Proper ((=) ==> (=) ==> (=)) (@FN_min n m).
Proof.
  intros x x' Ex y y' Ey.
  unfold FN_min.
  repeat break_let.
  unfold mkFinNat, equiv, Sig_Equiv in *.
  simpl in *.
  subst.
  rewrite Ex, Ey.
  reflexivity.
Qed.

Global Instance FN_max_proper {n m:nat}:
  Proper ((=) ==> (=) ==> (=)) (@FN_max n m).
Proof.
  intros x x' Ex y y' Ey.
  unfold FN_max.
  repeat break_let.
  unfold mkFinNat, equiv, Sig_Equiv in *.
  simpl in *.
  subst.
  rewrite Ex, Ey.
  reflexivity.
Qed.

