(* Base Spiral defintions: data types, utility functions, lemmas *)


Global Generalizable All Variables.

Require Import Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Lt.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Program.
Require Import Morphisms.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import CaseNaming.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

(* CoRN MathClasses *)
Require Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders.
Require Import MathClasses.orders.minmax MathClasses.orders.orders MathClasses.orders.rings.
Require Import MathClasses.theory.rings MathClasses.theory.abs.
Require Import MathClasses.theory.products.

Require Export Vector.
Require Export VecUtil.
Import VectorNotations.

Section Error.
  (* Error type *)
  Inductive maybeError {A:Type}: Type :=
  | OK : A → @maybeError A
  | Error: string -> @maybeError A.
  
  Definition is_Error {A:Type}  (x:@maybeError A) :=
    match x with
    | OK _ => False
    | Error _ => True
    end.
  
  Definition is_OK {A:Type}  (x:@maybeError A) :=
    match x with
    | OK _ => True
    | Error _ => False
    end.

  (* Error comparison does not take into account error message *)
Global Instance maybeError_equiv `{Equiv A}: Equiv (@maybeError A) :=
  fun a b =>
    match a, b with
    | Error _, Error _ => True
    | OK _, Error _ => False
    | Error _, OK _ => False
    | OK x, OK y => equiv x y
    end.

Global Instance maybeError_Reflexive `{Ae: Equiv A}
       `{!Reflexive (@equiv A _)}
: Reflexive (@maybeError_equiv A Ae).
Proof.
  unfold Reflexive.
  unfold maybeError_equiv.
  destruct x.
  reflexivity.
  constructor.
Qed.

Global Instance maybeError_Symmetric `{Ae: Equiv A}
       `{!Symmetric (@equiv A _)}
  : Symmetric (@maybeError_equiv A Ae).
Proof.
  unfold Symmetric.
  intros.
  unfold equiv, maybeError_equiv in *.
  destruct x,y; auto.
Qed.

Global Instance maybeError_Transitive `{Ae: Equiv A}
       `{!Transitive (@equiv A _)}
  : Transitive (@maybeError_equiv A Ae).
Proof.
  unfold Transitive.
  intros.
  unfold maybeError_equiv in *.
  destruct x,y,z; auto; contradiction.
Qed.

Global Instance maybeError_Equivalence `{Ae: Equiv A}
       `{!Equivalence (@equiv A _)}
: Equivalence (@maybeError_equiv A Ae).
Proof.
  constructor.
  apply maybeError_Reflexive.
  apply maybeError_Symmetric.
  apply maybeError_Transitive.
Qed.

Global Instance maybeError_Setoid `{Setoid A}: Setoid (@maybeError A).
Proof.
  unfold Setoid.
  apply maybeError_Equivalence.
Qed.

End Error.

(* equality of option types *)
Global Instance opt_Equiv `{Equiv A}: Equiv (option A) :=
  fun a b =>
    match a with
    | None => is_None b
    | Some x => (match b with
                 | None => False
                 | Some y => equiv x y
                 end)
    end.

Global Instance opt_Setoid `{Setoid A}: Setoid (@option A).
Proof.
  unfold Setoid in H.
  constructor. destruct H.
  unfold Reflexive. destruct x; (unfold equiv; crush).
  unfold Symmetric. intros. destruct x,y; (unfold equiv; crush). 
  unfold Transitive. intros. destruct x,y,z; unfold equiv, opt_Equiv in *; crush.
Qed.

(* Various definitions related to vector equality and setoid rewriting *)

Global Instance vec_equiv `{Equiv A} {n}: Equiv (vector A n) := Vforall2 (n:=n) equiv.

Global Instance vec_Equivalence `{Ae: Equiv A} {n:nat}
       `{!Equivalence (@equiv A _)}
: Equivalence (@vec_equiv A Ae n).
Proof.
  unfold vec_equiv.
  apply Vforall2_equiv.
  assumption.
Qed.

Global Instance vec_Setoid `{Setoid A} {n}: Setoid (vector A n).
Proof.
  unfold Setoid.
  apply vec_Equivalence.
Qed.

Section Vfold_right_p.
  Context
    `{eqA: Equiv A}
    `{eqB: Equiv B}
    (f : A->B->B)
    `{pF: !Proper ((=) ==> (=) ==> (=)) f}.

  Definition Vfold_right_reord {A B:Type} {n} (f:A->B->B) (v: vector A n) (initial:B): B := @Vfold_right A B f n v initial.
  
  Lemma Vfold_right_to_Vfold_right_reord: forall {A B:Type} {n} (f:A->B->B) (v: vector A n) (initial:B),
                                            Vfold_right f v initial ≡ Vfold_right_reord f v initial.
  Proof.
    crush.
  Qed.
  
  Global Instance Vfold_right_reord_proper n :
    Proper (@vec_equiv A _ n ==> (=) ==> (=)) (@Vfold_right_reord A B n f).
  Proof.
    intros v v' vEq i i' iEq.
    unfold Vfold_right_reord.
    induction v.
    Case "N=0".
    VOtac. simpl. assumption.
    Case "S(N)".
    revert vEq. VSntac v'. unfold vec_equiv. rewrite Vforall2_cons_eq. intuition. simpl.
    apply pF.
    SCase "Pf - 1".
    assumption.
    SCase "Pf - 2".
    apply IHv. unfold vec_equiv.  assumption.
  Qed.
  
End Vfold_right_p.

Section VCons_p.
  Definition Vcons_reord {A} {n} (t: vector A n) (h:A): vector A (S n) := Vcons h t.

  Lemma Vcons_to_Vcons_reord: forall A n (t: t A n) (h:A), Vcons h t  ≡ Vcons_reord t h.
  Proof.
    crush.
  Qed.
  
  Global Instance Vcons_reord_proper `{Equiv A} n:
    Proper (@vec_equiv A _ n ==> (=) ==> @vec_equiv A _ (S n))
           (@Vcons_reord A n).
  Proof.
    split.
    assumption.
    unfold vec_equiv, Vforall2 in H0.  assumption.
  Qed.

End VCons_p.

(* This tactics rewrites using H in Vcons using temporary conversion
      to Vcons_reord and then back *)
Ltac rewrite_Vcons H := rewrite Vcons_to_Vcons_reord, H, <- Vcons_to_Vcons_reord.

(*
Ltac rewrite_Vcons H := 
  rewrite Vcons_to_Vcons_reord;
  match H with
    | [H1] => rewrite H
    | [N!H1] => rewrite N!H
  end;
  rewrite <- Vcons_to_Vcons_reord.
 *)

Instance Vapp_proper `{Sa: Setoid A} (n1 n2:nat):
  Proper ((=) ==>  (=) ==> (=)) (@Vapp A n1 n2).
Proof.
  intros a0 a1 aEq b0 b1 bEq.
  induction n1.
  VOtac. auto.

  dep_destruct a0.
  dep_destruct a1.
  rewrite 2!Vapp_cons.

  assert (h=h0).
  apply aEq.

  rewrite 2!Vcons_to_Vcons_reord.
  rewrite H.
  rewrite <- 2!Vcons_to_Vcons_reord.

  unfold equiv, vec_equiv.
  apply Vforall2_cons_eq.
  split. reflexivity.

  unfold equiv, vec_equiv in IHn1.
  apply IHn1.
  apply aEq.
Qed.


Global Instance Vhead_proper A `{H:Equiv A} n:
  Proper (@equiv (vector A (S n)) (@vec_equiv A H (S n)) ==> @equiv A H) (@Vhead A n).
Proof.
  intros a b E.
  dep_destruct a.  dep_destruct b.
  unfold equiv, vec_equiv, vec_equiv, relation in E.
  rewrite Vforall2_cons_eq in E.
  intuition.
Defined.

Global Instance Vtail_proper `{Equiv A} n:
  Proper (@vec_equiv A _ (S n) ==> @vec_equiv A _ n)
         (@Vtail A n).
Proof.
  intros a b E.
  unfold equiv, vec_equiv, vec_equiv, relation in E.
  apply Vforall2_tail in E.
  unfold vec_equiv.
  assumption.
Defined.

Global Instance max_proper A `{Le A, TotalOrder A, !Setoid A} `{!∀ x y: A, Decision (x ≤ y)}:
  Proper ((=) ==> (=) ==> (=)) (max).
Proof.
  solve_proper.
Qed.  

Instance negate_proper A `{Ar: Ring A} `{!Setoid A}:
  Setoid_Morphism (negate).
Proof.
  split;try assumption.
  solve_proper.
Qed.

Instance abs_setoid_proper A
         `{Ar: Ring A}
         `{Asetoid: !Setoid A}
         `{Ato: !@TotalOrder A Ae Ale}
         `{Aabs: !@Abs A Ae Ale Azero Anegate}
: Setoid_Morphism abs | 0.
Proof.
  split; try assumption.
  intros x y E.
  unfold abs, abs_sig.
  destruct (Aabs x) as [z1 [Ez1 Fz1]]. destruct (Aabs y) as [z2 [Ez2 Fz2]].
  simpl.
  rewrite <-E in Ez2, Fz2.
  destruct (total (≤) 0 x).
  now rewrite Ez1, Ez2.
  now rewrite Fz1, Fz2.
Qed.

Lemma abs_nonneg_s `{Aabs: Abs A}: forall (x : A), 0 ≤ x → abs x = x.
Proof.
  intros AA AE. unfold abs, abs_sig.
  destruct (Aabs AA).  destruct a.
  auto.
Qed.

Lemma abs_nonpos_s `{Aabs: Abs A} (x : A): x ≤ 0 → abs x = -x.
Proof.
  intros E. unfold abs, abs_sig. destruct (Aabs x) as [z1 [Ez1 Fz1]]. auto.
Qed.

Lemma abs_0_s
      `{Ae: Equiv A}
      `{Ato: !@TotalOrder A Ae Ale}
      `{Aabs: !@Abs A Ae Ale Azero Anegate}
: abs 0 = 0.
Proof.
  apply abs_nonneg_s. auto.
Qed.

Lemma abs_always_nonneg
      `{Ae: Equiv A}
      `{Az: Zero A} `{A1: One A}
      `{Aplus: Plus A} `{Amult: Mult A} 
      `{Aneg: Negate A}
      `{Ale: Le A}
      `{Ato: !@TotalOrder A Ae Ale}
      `{Aabs: !@Abs A Ae Ale Az Aneg}
      `{Ar: !Ring A}
      `{ASRO: !@SemiRingOrder A Ae Aplus Amult Az A1 Ale}
: forall x, 0 ≤ abs x.
Proof.
  intros.
  destruct (total (≤) 0 x).
  rewrite abs_nonneg_s; assumption.
  rewrite abs_nonpos_s.
  rewrite <- flip_nonpos_negate; assumption.
  assumption.
Qed.

Lemma abs_negate_s A (x:A)
      `{Ae: Equiv A}
      `{Az: Zero A} `{A1: One A}
      `{Aplus: Plus A} `{Amult: Mult A} 
      `{Aneg: Negate A}
      `{Ale: Le A}
      `{Ato: !@TotalOrder A Ae Ale}
      `{Aabs: !@Abs A Ae Ale Az Aneg}
      `{Ar: !Ring A}
      `{ASRO: !@SemiRingOrder A Ae Aplus Amult Az A1 Ale}      
: abs (-x) = abs x.
Proof with trivial.
  destruct (total (≤) 0 x).
  rewrite (abs_nonneg x), abs_nonpos...
  apply rings.negate_involutive.
  apply flip_nonneg_negate...
  rewrite (abs_nonneg (-x)), abs_nonpos...
  reflexivity.
  apply flip_nonpos_negate...
Qed.

Instance abs_idempotent
         `{Ae: Equiv A}
         `{Az: Zero A} `{A1: One A}
         `{Aplus: Plus A} `{Amult: Mult A} 
         `{Aneg: Negate A}
         `{Ale: Le A}
         `{Ato: !@TotalOrder A Ae Ale}
         `{Aabs: !@Abs A Ae Ale Az Aneg}
         `{Ar: !Ring A}
         `{ASRO: !@SemiRingOrder A Ae Aplus Amult Az A1 Ale}      
:UnaryIdempotent abs.
Proof.
  intros a b E.
  unfold compose.
  destruct (total (≤) 0 a).
  rewrite abs_nonneg_s.
  auto.
  apply abs_always_nonneg. 
  setoid_replace (abs a) with (-a) by apply abs_nonpos_s.
  rewrite abs_negate_s.
  auto.
  assumption. assumption. assumption. assumption.
Qed.

Lemma abs_max_comm_2nd
      `{Ae: Equiv A}
      `{Az: Zero A} `{A1: One A}
      `{Aplus: Plus A} `{Amult: Mult A} 
      `{Aneg: Negate A}
      `{Ale: Le A}
      `{Ato: !@TotalOrder A Ae Ale}
      `{Aabs: !@Abs A Ae Ale Az Aneg}
      `{Ar: !Ring A}
      `{ASRO: !@SemiRingOrder A Ae Aplus Amult Az A1 Ale}      
      `{Aledec: !∀ x y: A, Decision (x ≤ y)}
: forall (x y:A),  max (abs y) x = abs (max (abs y) x).
Proof.

  intros.
  unfold max, sort, decide_rel.
  destruct (Aledec (abs y) x).
  
  Case "abs y <= x".
  unfold abs, abs_sig.
  simpl.
  destruct (Aabs x) as [z1 [Ez1 Fz1]].
  simpl.
  symmetry.
  assert (XP: 0 ≤ x). revert l. assert (0 ≤ abs y). apply abs_always_nonneg. auto.  
  revert Ez1.
  auto.

  Case "abs y > x".
  simpl.
  rewrite unary_idempotency.
  reflexivity.
Qed.

Open Scope vector_scope.

Notation "h :: t" := (cons h t) (at level 60, right associativity)
                     : vector_scope.

Fixpoint take_plus {A} {m} (p:nat) : vector A (p+m) -> vector A p := 
  match p return vector A (p+m) -> vector A p with
      0%nat => fun _ => Vnil
    | S p' => fun a => Vcons (hd a) (take_plus p' (tl a))
  end.
Program Definition take A n p (a : vector A n) (H : p <= n) : vector A p :=
  take_plus (m := n - p) p a.
Solve Obligations using auto with arith.

Fixpoint drop_plus {A} {m} (p:nat) : vector A (p+m) -> vector A m := 
  match p return vector A (p+m) -> vector A m with
      0 => fun a => a
    | S p' => fun a => drop_plus p' (tl a)
  end.
Program Definition drop A n p (a : vector A n) (H : p <= n) : vector A (n-p) :=
  drop_plus (m := n - p) p a.
Solve Obligations using auto with arith.

(* Split vector into a pair: first  'p' elements and the rest. *)
Definition vector2pair {A:Type} (p:nat) {t:nat} (v:vector A (p+t)) : (vector A p)*(vector A t) :=
  @Vbreak A p t v.

(* Split vector into a pair: first  'p' elements and the rest. *)
Definition pair2vector {A:Type} {i j:nat} (p:(vector A i)*(vector A j)) : (vector A (i+j))  :=
  match p with
      (a,b) => Vapp a b
  end.

Lemma vp2pv: forall {T:Type} i1 i2 (p:((vector T i1)*(vector T i2))),
               vector2pair i1 (pair2vector p) ≡ p.
Proof.
  intros.
  unfold vector2pair.
  destruct p.
  unfold pair2vector.
  apply Vbreak_app.
Qed.

(* reverse CONS, append single element to the end of the list *)
Program Fixpoint snoc {A} {n} (l:vector A n) (v:A) : (vector A (S n)) :=
  match l with
    | nil => [v]
    | h' :: t' => Vcons h' (snoc t' v)
  end.

Notation "h ;; t" := (snoc h t) (at level 60, right associativity).

Section Natrange_List.
  (* Probably will be removed later *)
  
  (* n-1 ... 0 *)
  Fixpoint rev_natrange_list (n:nat) : list nat :=
    match n with
    | 0 => List.nil
    | S p => List.cons p (rev_natrange_list p)
    end.

  (* 0 ...  n-1  *)
  Definition natrange_list (n:nat) : list nat :=
    List.rev (rev_natrange_list n).

  Lemma rev_natrange_list_bound:
    ∀ z x : nat, List.In x (rev_natrange_list z) → (x < z)%nat.
  Proof.
    intros.
    induction z.
    + compute in H.
      contradiction.
    + crush.
  Qed.

  Lemma natrange_list_bound:
    ∀ z x : nat, List.In x (natrange_list z) → (x < z)%nat.
  Proof.
    unfold natrange_list.
    intros.
    rewrite <- in_rev in H.
    apply rev_natrange_list_bound.
    assumption.
  Qed.
End Natrange_List.

(* 0 ... n-1*)
Program Fixpoint natrange (n:nat) : (vector nat n) :=
  match n return (vector nat n) with 
      0 => Vnil
    | S p => snoc (natrange p) p
  end.

(* n-1 ... 0*)
Program Fixpoint rev_natrange (n:nat) : (vector nat n) :=
  match n return (vector nat n) with 
      0 => Vnil
    | S p => Vcons p (rev_natrange p)
  end.

Lemma hd_cons {A} {n} (h:A) {t: vector A n}: Vhead (Vcons h t) ≡ h.
Proof.
  reflexivity.
Qed.

Lemma hd_snoc0: forall {A} (l:vector A 0) v, hd (snoc l v) ≡ v.
Proof.
  intros.
  dep_destruct l.
  reflexivity.
Qed.

Lemma hd_snoc1: forall {A} {n} (l:vector A (S n)) v, hd (snoc l v) ≡ hd l.
Proof.
  intros.
  dep_destruct l.
  reflexivity.
Qed.

Lemma tl_snoc1: forall {A} {n} (l:vector A (S n)) v, tl (snoc l v) ≡ snoc (tl l) v.
Proof.
  intros.
  dep_destruct l.
  reflexivity.
Qed.

Lemma snoc2cons: forall {A} (n:nat) (l:vector A (S n)) v,
                   snoc l v ≡ @cons _ (hd l) _ (snoc (tl l) v).
Proof.
  intros.
  dep_destruct l.
  reflexivity.
Qed.


Lemma hd0: natrange 0 ≡ [].
Proof.
  reflexivity.
Qed.

Lemma hd_natrange1: forall n, hd (natrange (S n)) ≡ O.
Proof.
  intros.
  simpl.
  induction n.
  auto.
  rewrite snoc2cons.
  simpl.
  apply IHn.
Qed.


Lemma last_snoc: forall A n (l:vector A n) v, last (snoc l v) ≡ v.
Proof.
  intros.
  induction l.
  auto.
  rewrite snoc2cons.
  simpl.
  assumption.
Qed.

Lemma last_natrange: forall n, last (natrange (S n)) ≡ n.
Proof.
  intros.
  induction n.
  auto.
  simpl.
  rewrite last_snoc.
  reflexivity.
Qed.

Lemma t0_nil: forall A (x:vector A 0), x ≡ [].
Proof.
  intros.
  dep_destruct x.
  reflexivity.
Qed.

Lemma map_nil: forall A B (f:A->B), map f [] ≡ [].
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma map2_nil: forall A B C (f:A->B->C), map2 f [] [] ≡ [].
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma map_hd: forall A B (f:A->B) n (v:vector A (S n)), hd (map f v) ≡ f (hd v).
Proof.
  intros.
  dep_destruct v.
  reflexivity.
Qed.

Lemma Vmap_cons: forall A B `{Setoid B} (f:A->B) n (x:A) (xs: vector A n) (ys:vector B n), 
    Vmap f (Vcons x xs) = Vcons (f x) (Vmap f xs).
Proof.
  intros.
  constructor. reflexivity.
  fold (Vforall2 (n:=n) equiv (Vmap f xs) (Vmap f xs)).
  fold (vec_equiv (Vmap f xs) (Vmap f xs)).
  fold (equiv (Vmap f xs) (Vmap f xs)).
  reflexivity.
Qed.

Lemma map_cons: forall A B n (f:A->B) (v:vector A (S n)),
                  map f v ≡ @cons _ (f (hd v)) _ (map f (tl v)).
Proof.
  intros.
  dep_destruct v.
  reflexivity.
Qed.

Lemma map2_cons: forall A B C (f:A->B->C) n (a:vector A (S n)) (b:vector B (S n)), 
                   map2 f a b ≡ @cons _ (f (hd a) (hd b)) _ (map2 f (tl a) (tl b)).
Proof.
  intros.
  dep_destruct a.
  dep_destruct b.
  reflexivity.
Qed.

Lemma Vmap2_cons_hd: forall A B C `{Setoid C} (f:A->B->C) n (a:vector A (S n)) (b:vector B (S n)), 
                    Vmap2 f a b = @cons _ (f (Vhead a) (Vhead b)) _ (Vmap2 f (Vtail a) (Vtail b)).
Proof.
  intros.
  dep_destruct a.
  dep_destruct b.
  reflexivity.
Qed.

Lemma Vmap2_cons: forall A B C `{Setoid C} (f:A->B->C) n (a:A) (b:B) (a':vector A n) (b':vector B n), 
                    Vmap2 f (a::a') (b::b') = @cons _ (f a b) _ (Vmap2 f a' b').
Proof.
  intros.
  reflexivity.
Qed.


Lemma shifout_tl_swap: forall {A} n (l:vector A (S (S n))),
                         tl (shiftout l) ≡ shiftout (tl l).
Proof.
  intros.
  dep_destruct l.
  simpl.
  reflexivity.
Qed.

Lemma last_tl: forall {A} n (l:vector A (S (S n))),
                 last (tl l) ≡ last l.
Proof.
  intros.
  dep_destruct l.
  simpl.
  reflexivity.
Qed.

Lemma map_snoc: forall A B n (f:A->B) (l:vector A (S n)),
                  map f l ≡ snoc (map f (shiftout l)) (f (last l)).
Proof.
  intros.
  induction n.
  Case "n=0".
  dep_destruct l.
  assert (L: last (h::x) ≡ h).
  SCase "L".
  rewrite t0_nil with (x:=x).
  reflexivity.
  rewrite L.
  assert (S: forall (z:vector A 1), shiftout z ≡ []).
  SCase "S".
  intros.
  dep_destruct z.
  rewrite t0_nil with (x:=x0).
  reflexivity.
  rewrite t0_nil with (x:=x).
  rewrite S.
  simpl.
  reflexivity.
  Case "S n".
  rewrite map_cons.
  rewrite IHn.  clear_all.  
  symmetry.
  rewrite snoc2cons.
  rewrite map_cons.
  assert (HS: hd (shiftout l) ≡ hd l).
  dep_destruct l.
  reflexivity.
  rewrite HS. clear_all.
  simpl (hd (f (hd l) :: map f (tl (shiftout l)))).
  assert (L:(tl (f (hd l) :: map f (tl (shiftout l)))) ≡ (map f (shiftout (tl l)))).
  simpl. rewrite shifout_tl_swap. reflexivity.
  rewrite L. rewrite last_tl. reflexivity. 
Qed.


Lemma map2_snoc: forall A B C (f:A->B->C) n (a:vector A (S n)) (b:vector B (S n)), 
                   map2 f a b ≡ snoc (map2 f (shiftout a) (shiftout b)) (f (last a) (last b)).
Proof.
  intros.
  induction n.
  Case "n=0".
  dep_destruct a.
  dep_destruct b.
  assert (L: forall T hl (xl:t T 0), last (hl::xl) ≡ hl).
  SCase "L".
  intros.
  rewrite t0_nil with (x:=xl).
  reflexivity.
  repeat rewrite L.
  assert (S: forall T (z:t T 1), shiftout z ≡ []).
  SCase "S".
  intros.
  dep_destruct z.
  rewrite t0_nil with (x:=x1).
  reflexivity.
  rewrite t0_nil with (x:=x).
  rewrite t0_nil with (x:=x0).
  repeat rewrite S.
  simpl.
  reflexivity.
  Case "S n".
  rewrite map2_cons.
  rewrite IHn.  clear_all.  
  symmetry.
  repeat rewrite snoc2cons.
  repeat rewrite map2_cons.
  assert (HS: forall T m (l:t T (S (S m))), hd (shiftout l) ≡ hd l).
  intros. dep_destruct l. reflexivity.
  repeat rewrite HS. clear_all.
  simpl (hd (f (hd a) (hd b) :: map2 f (tl (shiftout a)) (tl (shiftout b)))).

  assert(L:(tl (f (hd a) (hd b) :: map2 f (tl (shiftout a)) (tl (shiftout b)))) ≡ (map2 f (shiftout (tl a)) (shiftout (tl b)))).
  simpl. repeat rewrite shifout_tl_swap. reflexivity.
  rewrite L. repeat rewrite last_tl. reflexivity.   
Qed.


Lemma map2_comm: forall A B (f:A->A->B) n (a b:vector A n), 
                   (forall x y, (f x y) ≡ (f y x)) -> map2 f a b ≡ map2 f b a.
Proof.
  intros.
  induction n.
  dep_destruct a.
  dep_destruct b.
  reflexivity.
  rewrite -> map2_cons.
  rewrite H. (* reorder LHS head *)
  rewrite <- IHn. (* reoder LHS tail *)
  rewrite <- map2_cons.
  reflexivity.
Qed.

Lemma Vmap2_comm : forall `{CO:Commutative B A f} `{SB: !Setoid B},
                   forall n:nat, Commutative (Vmap2 f (n:=n)).
Proof.
  intros.
  unfold Commutative.
  intros a b.
  induction n.
  dep_destruct a.
  dep_destruct b.
  reflexivity.
  rewrite Vmap2_cons_hd by apply SB.
  
  (* reorder LHS head *)
  
  rewrite Vcons_to_Vcons_reord.
  rewrite commutativity.
  rewrite <- IHn. (* reoder LHS tail *)
  setoid_rewrite <- Vmap2_cons.
  reflexivity.
  assumption.
Qed.


(* Shows that two map2 supplied with function which ignores 2nd argument 
will be eqivalent for all values of second list *)
Lemma map2_ignore_2: forall A B C (f:A->B->C) n (a:vector A n) (b0 b1:vector B n),
                       (forall a' b0' b1', f a' b0' ≡ f a' b1') ->
                       map2 f a b0 ≡ map2 f a b1 .
Proof.
  intros.
  induction a.
  rewrite -> t0_nil.
  rewrite -> t0_nil with (x:=b0).
  apply(map2_nil).
  rewrite map2_cons.
  rewrite map2_cons.
  simpl.
  rewrite -> H with (a':=h) (b0':=(hd b0)) (b1':=(hd b1)).

  assert(map2 f a (tl b0) ≡ map2 f a (tl b1)).
  apply(IHa).
  rewrite <- H0.
  reflexivity.
Qed.


(* Shows that two map2 supplied with function which ignores 1st argument 
will be eqivalent for all values of first list *)
Lemma map2_ignore_1: forall A B C (f:A->B->C) n (a0 a1:vector A n) (b:vector B n),
                       (forall a0' a1' b', f a0' b' ≡ f a1' b') ->
                       map2 f a0 b ≡ map2 f a1 b .
Proof.
  intros.
  induction b.
  rewrite -> t0_nil.
  rewrite -> t0_nil with (x:=a0).
  apply(map2_nil).
  rewrite map2_cons.
  rewrite map2_cons.
  simpl.
  rewrite -> H with (b':=h) (a0':=(hd a0)) (a1':=(hd a1)).

  assert(map2 f (tl a0) b ≡ map2 f (tl a1) b).
  apply(IHb).
  rewrite <- H0.
  reflexivity.
Qed.

Lemma shiftout_snoc: forall A n (l:vector A n) v, shiftout (snoc l v) ≡ l.
Proof.
  intros.
  induction l.
  auto.
  simpl.
  rewrite IHl.
  reflexivity.
Qed.

Lemma shifhout_natrange: forall n, shiftout (natrange (S n)) ≡ natrange n.
Proof.
  intros.
  dependent destruction n.
  auto.
  simpl.
  rewrite shiftout_snoc.
  reflexivity.
Qed.

Lemma tl_natrange: forall n, tl (natrange (S n)) ≡ map (S) (natrange n).
Proof.
  intros.
  induction n.
  reflexivity.
  simpl.
  simpl in IHn.
  rewrite tl_snoc1.
  rewrite IHn. clear IHn.
  replace (snoc (natrange n) n) with (natrange (S n)) by reflexivity.
  
  rewrite map_snoc.
  rewrite last_natrange.
  rewrite shifhout_natrange.
  reflexivity.
Qed.

Lemma fold_right_reduce: forall A B n (f:A->B->B) (id:B) (v:vector A (S n)),
                           fold_right f v id ≡ f (hd v) (fold_right f (tl v) id).
Proof.
  intros.
  dep_destruct v.
  reflexivity.
Qed.

Lemma Vfold_right_reduce: forall A B n (f:A->B->B) (id:B) (v:vector A (S n)),
                            Vfold_right f v id ≡ f (hd v) (Vfold_right f (tl v) id).
Proof.
  intros.
  dep_destruct v.
  reflexivity.
Qed.

Lemma Vfold_right_fold_right: forall {A B:Type} {n} (f:A->B->B) (v: vector A n) (initial:B),
                                Vfold_right f v initial ≡ @fold_right A B f n v initial.
Proof.
  intros.
  induction v.
  reflexivity.
  rewrite fold_right_reduce.
  simpl.
  rewrite <- IHv.
  reflexivity.
Qed.

Lemma rev_nil: forall A, rev (@nil A) ≡ [].
Proof.
  intros.
  unfold rev.
  assert (rev_append (@nil A) (@nil A) ≡ (@nil A)).
  unfold rev_append.
  assert (rev_append_tail (@nil A) (@nil A) ≡ (@nil A)).
  auto.
  rewrite H. clear_all.
  dep_destruct (plus_tail_plus 0 0).
  auto.
  rewrite H. clear_all.
  dep_destruct (plus_n_O 0).
  auto.
Qed.

Lemma hd_eq: forall A n (u v: vector A (S n)), u≡v -> (hd u) ≡ (hd v).
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma hd_equiv: forall `{Setoid A} {n} (u v: vector A (S n)), u=v -> (Vhead u) = (Vhead v).
Proof.
  intros.
  rewrite H0.
  f_equiv.
Qed.

Lemma Vcons_equiv_elim `{Equiv A}: forall a1 a2 n (v1 v2 : vector A n),
                                     Vcons a1 v1 = Vcons a2 v2 -> a1 = a2 /\ v1 = v2.
Proof.
  intros. auto.
Qed.

Lemma Vcons_equiv_intro `{Setoid A} : forall a1 a2 n (v1 v2 : vector A n),
                                        a1 = a2 -> v1 = v2 -> Vcons a1 v1 = Vcons a2 v2.
Proof.
  intros.
  rewrite 2!Vcons_to_Vcons_reord.
  rewrite H0.
  rewrite H1.
  reflexivity.
Qed.

Lemma Vcons_single_elim `{Equiv A} : forall a1 a2,
                                       Vcons a1 (@Vnil A) = Vcons a2 (@Vnil A) <-> a1 = a2.
Proof.
  intros a1 a2.
  unfold equiv, vec_equiv.
  rewrite Vforall2_cons_eq.   
  assert(Vforall2 equiv (@Vnil A) (@Vnil A)).
  constructor.
  split; tauto.
Qed.

(* Utlity functions for vector products *)

Definition Phead {A} {B} {n} (ab:(vector A (S n))*(vector B (S n))): A*B
  := match ab with
       | (va,vb) => ((Vhead va), (Vhead vb))
     end.

Definition Ptail {A} {B} {n} (ab:(vector A (S n))*(vector B (S n))): (vector A n)*(vector B n)
  := match ab with
       | (va,vb) => ((Vtail va), (Vtail vb))
     end.

Instance Ptail_proper `{Sa: Setoid A} `{Sb: Setoid B} (n:nat):
  Proper ((=) ==> (=)) (@Ptail A B n).
Proof.
  intros x y E.
  destruct x as [xa xb].
  destruct y as [ya yb].
  destruct E as [E1 E2].
  simpl in E1. simpl in E2.
  unfold Ptail.
  rewrite E1, E2.
  reflexivity.
Qed.

Definition Vmap_reord (A B: Type) (n:nat) (f:A->B) (x: vector A n): vector B n := Vmap f x.

Lemma Vmap_to_Vmap_reord: forall (A B: Type) (n:nat) (f:A->B) (x: vector A n), @Vmap A B f n x ≡ @Vmap_reord A B n f x.
Proof.
  crush.
Qed.

Global Instance Vmap_reord_proper_ext_equiv n  (M N:Type) `{Ne:!Equiv N, Me:!Equiv M}:
  Proper (@ext_equiv M Me N Ne 
                     ==> @vec_equiv M Me n
                     ==> @vec_equiv N Ne n)
         (@Vmap_reord M N n).
Proof.
  intros f g Eext a b Ev.
  induction n.
  Case "N=0".
  VOtac. auto.
  Case "S N".
  dep_destruct a. dep_destruct b.
  split.
  apply Eext, Ev.
  apply IHn, Ev.
Qed.

Global Instance Vmap_arg_proper  (M N:Type) `{Me:!Equiv M} `{Ne: !Equiv N} (f : M->N)
       `{fP: !Proper (Me ==> Ne) f} (n:nat):
  Proper ((@vec_equiv M _ n) ==> (@vec_equiv N _ n)) (@Vmap M N f n).
Proof.
  intros a b Ea.
  unfold vec_equiv.
  induction n.
  Case "N=0".
  VOtac. auto.
  Case "S N".
  dep_destruct a. dep_destruct b.
  split.
  apply fP, Ea.
  apply IHn, Ea.
Qed.

Definition Zless
           {A:Type} `{Lt A} `{Altdec: !∀ x y: A, Decision (x < y)}
           {Z:Type} `{Zero Z, One Z}  (a:A) (b:A) : Z :=
  if Altdec a b then one else zero.


Global Instance zless_proper
       (A:Type) `{Alt:Lt A} `{Altdec: !∀ x y: A, Decision (x < y)} `{Setoid A} `{!StrictSetoidOrder Alt}
       (Z:Type) `{Zero Z, One Z} `{Setoid Z}:
  Proper ((=) ==> (=) ==> (=)) (Zless).
Proof.
  unfold Proper.
  intros a a' aE z z' zE.
  unfold Zless.
  dep_destruct (Altdec a z).
  dep_destruct (Altdec a' z').
  auto.
  rewrite aE in p.
  rewrite zE in p.
  contradiction.
  dep_destruct (Altdec a' z').
  rewrite <- aE in p.
  rewrite <- zE in p.
  contradiction.
  auto.  
Qed.

Definition Lst {B:Type} (x:B) := [x].

Global Instance VBreak_proper (A:Type) `{Setoid A} (n1 n2:nat) `{Plus nat}:
  Proper ((=) ==> (=)) (@Vbreak A n1 n2).
Proof.
  intros v v1 vE.
  induction n1.
  simpl. setoid_rewrite vE. reflexivity.
  assert (V1: v ≡ Vapp (fst (Vbreak (n1:=1) v)) (snd (Vbreak (n1:=1) v))).
  simpl. dep_destruct v. reflexivity.
  assert (V2: v1 ≡ Vapp (fst (Vbreak (n1:=1) v1)) (snd (Vbreak (n1:=1) v1))).
  simpl. dep_destruct v1. reflexivity.
  rewrite V1. clear V1. rewrite V2. clear V2.
  dep_destruct v. dep_destruct v1.
  simpl.

  rewrite 2!Vcons_to_Vcons_reord.
  assert (E: Vbreak x = Vbreak x0).
  apply IHn1.  apply vE. 
  rewrite E.
  setoid_replace h with h0 by apply vE.
  reflexivity.
Qed. 

Lemma Vforall_hd {A:Type} {P:A->Prop} {n:nat} {v:vector A (S n)}:
  Vforall P v -> P (Vhead v).
Proof.
  dep_destruct v.
  simpl.
  tauto.
Qed.

Lemma Vforall_tl {A:Type} {P:A->Prop} {n:nat} {v:vector A (S n)}:
  Vforall P v -> Vforall P (Vtail v).
Proof.
  dep_destruct v.
  simpl.
  tauto.
Qed.

Lemma Vforall_nil:
  ∀ B (P:B->Prop), Vforall P (@Vnil B).
Proof.
  crush.
Qed.

Lemma Vforall_cons {B:Type} {P:B->Prop} {n:nat} {x:B} {xs:vector B n}:
  (P x /\ Vforall P xs) ≡ Vforall P (cons x xs).
Proof.
  auto.
Qed.

Open Local Scope nat_scope.

Lemma  plus_lt_subst_r: forall a b b' c,  b' < b -> a + b < c -> a + b' < c.
Proof.
  intros. omega.
Qed.

Lemma  plus_le_subst_r: forall a b b' c,  b' <= b -> a + b < c -> a + b' < c.
Proof.
  intros. omega.
Qed.

Lemma le_mius_minus : forall a b c, a>=(b+c) -> a-b-c ≡ a - (b+c).
Proof.
  intros.
  omega.
Qed.

Lemma nez2gt: forall n, 0 ≢ n -> gt n 0.
Proof.
  intros.
  omega.
Defined.

Lemma neq_nat_to_neq {a b:nat} (e: ¬eq_nat a b): a ≢ b.
Proof.
  crush.
Defined.

Definition Vin_aux {A} {n} (v : vector A n) (x : A) : Prop := Vin x v.

Lemma Vnth_0 {B} {n} (v:vector B (S n)) (ip: 0<(S n)):
  Vnth (i:=0) v ip ≡ Vhead v.
Proof.
  dep_destruct v.
  simpl.
  reflexivity.
Qed.

Lemma modulo_smaller_than_devisor:
  ∀ x y : nat, 0 ≢ y → x mod y < y.
Proof.
  intros.
  destruct y; try congruence.
  unfold modulo.
  omega.
Qed.

Lemma le_pred_l {n m} (H: S n <= m): n <= m.
Proof.
  auto with arith.
Defined.

Close Local Scope nat_scope.

Close Scope vector_scope.

Lemma  fold_left_once:
  forall (A B:Type) (x:B) (xs:list B) (b:A) (f:A->B->A), 
    List.fold_left f (x::xs) b ≡ List.fold_left f xs (f b x).
Proof.
  auto.
Qed.

Lemma fold_left_map {A B M} (ff:A -> B -> A) (fm:M->B) (l:list M) (a0:A):
  List.fold_left ff (List.map fm l) a0 ≡ List.fold_left (fun a m => ff a (fm m)) l a0.
Proof.
  generalize a0.
  induction l.
  + auto.
  + simpl.
    intros.
    rewrite IHl.
    reflexivity.
Qed.



(* ----------- Some handy tactics ----------- *)

(* simple tactic to get rid is_OK/is_Error and is_None/is_Some goals which are 
frequently produced by cases analsysis on matcing error conditions *)

Global Ltac err_ok_elim := 
          repeat match goal with
                 | [ H: ?x ≢ ?x |- _ ] => congruence
                 | [ H: ?x ≡ ?x |- _ ] => clear H
                                          
                 | [ H : is_OK (Error _)  |- _ ] => unfold is_OK in H; contradiction H
                 | [ H : @OK _ _ ≡ @Error _ _  |- _ ] => congruence
                 | [ H : is_OK (OK _)  |- _ ] => clear H
                 | [ H : is_Error (OK _)  |- _ ] => unfold is_Error in H; contradiction H
                 | [ H : @Error _ _ ≡ @OK _ _  |- _ ] => congruence
                 | [ H : is_Error (Error _)  |- _ ] => clear H
                                                                          
                 | [ H : _ |- is_OK (OK _) ] => unfold is_OK; trivial
                 | [ H : _ |- is_OK (Error _) ] => unfold is_OK; congruence
                 | [ H : _ |- is_Error (Error) ] => unfold is_Error; trivial
                 | [ H : _ |- is_Error (OK _) ] => unfold is_Error; congruence
                 end.

Ltac none_some_elim := 
  repeat match goal with
         | [ H: ?x ≢ ?x |- _ ] => congruence
                                  
         | [ H : is_None (Some _) |- _] => unfold is_None in H; contradiction H
         | [ H : is_None None  |- _ ] => clear H
         | [ H : is_Some None |- _] => unfold is_Some in H; contradiction H
         | [ H : is_Some (Some _) |-_ ] => clear H

         | [ H : _ |- is_None (Some _) ] => unfold is_None; congruence
         | [ H : _ |- is_None None ] => unfold is_None; trivial
         | [ H : _ |- is_Some None ] => unfold is_Some; congruence
         | [ H : _ |- is_Some (Some _) ] => unfold is_Some; trivial
         end. 

Ltac rewrite_clear H := rewrite H; clear H.
