Require Import Coq.Arith.Arith.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Decidable.
Require Import Coq.Strings.String.
Require Import Omega.
Require Import Psatz.

Require Import CoLoR.Util.Nat.NatUtil.

Require Import Helix.DSigmaHCOL.DSHCOLOnCarrierA.
Import MDSHCOLOnCarrierA.

From Coq.FSets Require Import
     FSetAVL
     FSetInterface
     FSetFacts
     FSetProperties
     FSetToFiniteSet
     FMapAVL
     FMapInterface
     FMapFacts.

Require Import Helix.HCOL.CarrierType.

Require Import Helix.MSigmaHCOL.CarrierAasCT.
Require Import Helix.DSigmaHCOL.DSigmaHCOL.
Require Import Helix.DSigmaHCOL.DSigmaHCOLEval.

Require Import MathClasses.misc.util.
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Require Import MathClasses.implementations.peano_naturals.
Require Import MathClasses.implementations.bool.
Require Import MathClasses.orders.orders.
Require Import MathClasses.misc.decision.

Require Import Helix.Util.ErrorSetoid.
Require Import Helix.Util.OptionSetoid.
Require Import Helix.Tactics.HelixTactics.

Local Open Scope string_scope.
Open Scope list_scope.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope nat_scope.

Module TM := FMapAVL.Make(Nat_as_OT).
Module Import TP := FMapFacts.WProperties_fun(Nat_as_OT)(TM).

(* [TypeSig] is a signature of an evaluation context, which maps
   De-Brujn indices to expected types *)
Definition TypeSig := TM.t DSHType.

Section TypeSig_Setoid.

  Global Instance TypeSig_Equiv: Equiv (TypeSig) :=
    fun m m' => forall k : TM.key, TM.find k m = TM.find k m'.

  Global Instance TypeSig_Equiv_Reflexive:
    Reflexive (TypeSig_Equiv).
  Proof.
    unfold TypeSig_Equiv.
    unfold Reflexive.
    reflexivity.
  Qed.

  Global Instance TypeSig_Equiv_Symmetric:
    Symmetric (TypeSig_Equiv).
  Proof.
    unfold TypeSig_Equiv.
    unfold Symmetric.
    intros x y H k.
    specialize (H k).
    auto.
  Qed.

  Global Instance TypeSig_Equiv_Transitive:
    Transitive (TypeSig_Equiv).
  Proof.
    unfold TypeSig_Equiv.
    unfold Transitive.
    intros x y z H0 H1 k.
    specialize (H0 k).
    specialize (H1 k).
    auto.
  Qed.

  Global Instance TypeSig_Equiv_Equivalence:
    Equivalence (TypeSig_Equiv).
  Proof.
    split; typeclasses eauto.
  Qed.

End TypeSig_Setoid.


(* True if nth context element has expected type. decidable. *)
Definition contextEnsureType (σ: evalContext) (k:nat) (t:DSHType) : Prop :=
  match nth_error σ k with
  | Some v => DSHValType v t
  | _ => False
  end.

Global Instance contextEnsureType_Decision {σ k t}:
  Decision (contextEnsureType σ k t).
Proof.
  unfold Decision, contextEnsureType.
  break_match; auto.
  apply DSHValType_Decision.
Qed.

(* typecheck env. starting from [off] index (inclusuve).  *)
Definition typecheck_env_bool (off:nat) (tm:TypeSig) (σ: evalContext) : bool :=
  TP.for_all (fun k t =>
                (k<?off) || (bool_decide (contextEnsureType σ (k-off) t))
             ) tm.

(* Propositional version *)
Definition typecheck_env (off:nat) (tm:TypeSig) (σ: evalContext) :  Prop :=
  typecheck_env_bool off tm σ ≡ true.

Lemma eq_equiv_option_DSHType (a b : option DSHType) :
  a ≡ b <-> a = b.
Proof.
  split; intros.
  -
    rewrite H; reflexivity.
  -
    destruct a, b;
      inversion H; congruence.
Qed.

Global Instance TypeSig_MapsTo_proper {k : TM.key} {v : DSHType} :
  Proper ((=) ==> (iff)) (TM.MapsTo (elt:=DSHType) k v).
Proof.
  simpl_relation.
  unfold equiv, TypeSig_Equiv in H.
  specialize (H k).
  repeat rewrite ->F.find_mapsto_iff.
  apply eq_equiv_option_DSHType in H.
  rewrite H.
  reflexivity.
Qed.

Global Instance DSHValType_proper:
  Proper ((=) ==> (=) ==> iff) DSHValType.
Proof.
  intros v0 v1 Ev t0 t1 Et.
  inversion Et; subst.
  inversion Ev; subst.
  rewrite H. reflexivity.
  all: split; intros;
    inversion H0; subst; constructor.
Qed.

Global Instance typecheck_env_proper:
  Proper ((=) ==> (=) ==> (=) ==> iff) typecheck_env.
Proof.
  intros n0 n1 En t0 t1 Et σ0 σ1 Eσ.
  unfold equiv, nat_equiv in En.
  subst n1. rename n0 into n.
  split; intros H.
  -
    unfold typecheck_env, typecheck_env_bool in *.
    apply for_all_iff; [typeclasses eauto |].
    intros k t M.
    apply for_all_iff with (k:=k) (e:=t) in H.
    destruct (k <? n) eqn:K; [constructor |].
    simpl; apply bool_decide_true.
    apply Nat.ltb_ge in K.
    rewrite orb_false_l in H.
    apply bool_decide_true in H.
    +
      unfold contextEnsureType in *.
      repeat break_match; eq_to_equiv_hyp.
      *
        rewrite Eσ in Heqo0.
        rewrite Heqo0 in Heqo.
        clear Heqo0.
        some_inv.
        clear - Heqo H.
        rewrite <- Heqo.
        assumption.
      *
        rewrite Eσ in Heqo0.
        some_none.
      *
        rewrite Eσ in Heqo0.
        some_none.
      *
        trivial.
    +
      solve_proper.
    +
      rewrite Et.
      assumption.
  - (* this bullet is symmetric to the previous *)
    unfold typecheck_env, typecheck_env_bool in *.
    apply for_all_iff; [typeclasses eauto |].
    intros k t M.
    apply for_all_iff with (k:=k) (e:=t) in H.
    destruct (k <? n) eqn:K; [constructor |].
    simpl; apply bool_decide_true.
    apply Nat.ltb_ge in K.
    rewrite orb_false_l in H.
    apply bool_decide_true in H.
    +
      unfold contextEnsureType in *.
      repeat break_match; eq_to_equiv_hyp.
      *
        rewrite <-Eσ in Heqo0.
        rewrite Heqo0 in Heqo.
        clear Heqo0.
        some_inv.
        clear - Heqo H.
        rewrite <- Heqo.
        assumption.
      *
        rewrite <-Eσ in Heqo0.
        some_none.
      *
        rewrite <-Eσ in Heqo0.
        some_none.
      *
        trivial.
    +
      solve_proper.
    +
      rewrite <-Et.
      assumption.
Qed.


(* Compare two type signatures for conflicts and returns map of
   conflicting entries, for each conflicting key, the value us a tuple
   of 2 incompatible values.

   A conflict occurs when different values occur at different
   signatures at the same index. If for given index the value is
   present only in one signature that does not constiture a
   conflct.  *)
Definition findTypeSigConflicts (s1 s2:TypeSig)
  := TM.map2 (fun a b => match a, b with
                      | Some x, Some y =>
                        if bool_decide (x = y)
                        then None
                        else Some (a,b)
                      | _, _ => None
                      end) s1 s2.

(* Returns [True], if given type signatures do not have conflicts.

   A conflict occurs when different values occur at different
   signatures at the same index. If for given index the value is
   present only in one signature that does not constiture a
   conflct.  *)
Definition TypeSigCompat (s1 s2:TypeSig) : Prop
  := TM.Empty (findTypeSigConflicts s1 s2).

Global Instance TypeSigCompat_Decision {s1 s2}:
  Decision (TypeSigCompat s1 s2).
Proof.
  unfold Decision, TypeSigCompat.
  destruct (TM.is_empty (elt:=option DSHType * option DSHType)
                        (findTypeSigConflicts s1 s2)) eqn:H.
  - left; apply TM.is_empty_2; assumption.
  - right; intro C; apply TM.is_empty_1 in C; congruence.
Qed.

(* This is "unsafe" version which will override conflicting keys *)
Definition TypeSigUnion := TP.update (elt:=DSHType).

(* This is "safe" version which returns error in case of conflct *)
Definition TypeSigUnion_error (s1 s2: TypeSig)
  := if TypeSigCompat_Decision (s1:=s1) (s2:=s2)
     then Some (TypeSigUnion s1 s2)
     else None.

Lemma TypeSigCompat_TypeSigUnion_error {dsig1 dsig2}:
  TypeSigCompat dsig1 dsig2 ->
  TypeSigUnion_error dsig1 dsig2 = Some (TypeSigUnion dsig1 dsig2).
Proof.
  intros H.
  unfold TypeSigUnion_error.
  break_if; [ reflexivity | congruence ].
Qed.

(* Helper wrapper for double bind of [TypeSigUnion_error] *)
Definition TypeSigUnion_error' (os1 os2: option TypeSig): option TypeSig
  := s1 <- os1 ;; s2 <- os2 ;; TypeSigUnion_error s1 s2.

Definition TypeSig_safe_add (k:var_id) (v:DSHType) (ts: TypeSig): option TypeSig
  := match TM.find k ts with
     | Some v' =>
       if bool_decide (v = v')
       then Some ts (* already exists with same value *)
       else None (* already exists, but with different value *)
     | None => Some (TM.add k v ts)
     end.

Definition TypeSigPExpr (me:PExpr) : option TypeSig :=
  match me with
  | PVar v => Some (TM.add v DSHPtr (TM.empty _))
  end.

Definition TypeSigMExpr (me:MExpr) : option TypeSig :=
  match me with
  | MPtrDeref p => TypeSigPExpr p
  | MConst _ => Some (TM.empty _)
  end.

Fixpoint TypeSigNExpr (ne:NExpr) : option TypeSig :=
  match ne with
  | NVar v => TypeSig_safe_add v DSHnat (TM.empty _)
  | NConst x => Some (TM.empty _)
  | NDiv a b => TypeSigUnion_error' (TypeSigNExpr a) (TypeSigNExpr b)
  | NMod a b => TypeSigUnion_error' (TypeSigNExpr a) (TypeSigNExpr b)
  | NPlus a b => TypeSigUnion_error' (TypeSigNExpr a) (TypeSigNExpr b)
  | NMinus a b => TypeSigUnion_error' (TypeSigNExpr a) (TypeSigNExpr b)
  | NMult a b => TypeSigUnion_error' (TypeSigNExpr a) (TypeSigNExpr b)
  | NMin a b => TypeSigUnion_error' (TypeSigNExpr a) (TypeSigNExpr b)
  | NMax a b => TypeSigUnion_error' (TypeSigNExpr a) (TypeSigNExpr b)
  end.

Fixpoint TypeSigAExpr (ae:AExpr) : option TypeSig :=
  match ae with
  | AVar v => TypeSig_safe_add v DSHCType (TM.empty _)
  | AConst _ => Some (TM.empty _)
  | ANth m n => TypeSigUnion_error' (TypeSigMExpr m) (TypeSigNExpr n)
  | AAbs a => TypeSigAExpr a
  | APlus a b => TypeSigUnion_error' (TypeSigAExpr a) (TypeSigAExpr b)
  | AMinus a b => TypeSigUnion_error' (TypeSigAExpr a) (TypeSigAExpr b)
  | AMult a b => TypeSigUnion_error' (TypeSigAExpr a) (TypeSigAExpr b)
  | AMin a b => TypeSigUnion_error' (TypeSigAExpr a) (TypeSigAExpr b)
  | AMax a b => TypeSigUnion_error' (TypeSigAExpr a) (TypeSigAExpr b)
  | AZless a b => TypeSigUnion_error' (TypeSigAExpr a) (TypeSigAExpr b)
  end.

(* make sure 2 contexts are quivalent at locations from given [TypeSig].
   additionally makes typechecks both contexts wrt [TypeSig] *)
Definition context_equiv_at_TypeSig (tm:TypeSig) : relation evalContext
  := fun σ0 σ1 =>
       forall k t, TM.MapsTo k t tm ->
                   contextEnsureType σ0 k t /\
                   contextEnsureType σ1 k t /\ (* this is redundant *)
                   context_lookup "" σ0 k = context_lookup "" σ1 k (* Error messages must be empty *)
.

Global Instance contextEnsureType_proper :
  Proper ((=) ==> (=) ==> (=) ==> iff) contextEnsureType.
Proof.
  intros tm1 tm2 TMeq k1 k2 Keq t1 t2 Teq.
  rewrite Keq, Teq;
    clear k1 t1 Keq Teq; rename k2 into k, t2 into t;
    assert (K: k = k) by reflexivity.
  unfold contextEnsureType.
  pose proof ListSetoid.nth_error_proper tm1 tm2 TMeq k k K.
  repeat break_match;
    inversion H; subst;
    try reflexivity.
  rewrite H2.
  reflexivity.
Qed.

Global Instance context_equiv_at_TypeSig_proper:
  Proper ((=) ==> (=) ==> (=) ==> iff) context_equiv_at_TypeSig.
Proof.
  simpl_relation.
  unfold context_equiv_at_TypeSig.
  split; intros.
  -
    assert (TM.MapsTo k t x) by (rewrite H; assumption).
    specialize (H2 k t H4).
    split; [| split].
    1: rewrite <-H0.
    2: rewrite <-H1.
    3: rewrite <-H0, <-H1.
    all: apply H2.
  -
    assert (TM.MapsTo k t y) by (rewrite <-H; assumption).
    specialize (H2 k t H4).
    split; [| split].
    1: rewrite H0.
    2: rewrite H1.
    3: rewrite H0, H1.
    all: apply H2.
Qed.

(* Similar to [context_equiv_at_TypeSig] but assumes first [off] values
   are not included in eval contexts but still could be referenced in
   type signature. These first [off] keys will not be type checked.
 *)
Definition context_equiv_at_TypeSig_off (tm:TypeSig) (off:nat): relation evalContext
  := fun σ0 σ1 =>
       forall k t, k>=off ->
              TM.MapsTo k t tm ->
              contextEnsureType σ0 (k-off) t /\
              contextEnsureType σ1 (k-off) t /\ (* this is redundant *)
              context_lookup "" σ0 (k-off) = context_lookup "" σ1 (k-off) (* Error messages must be empty *)
.

Definition context_equiv_at_TypeSig_head (tm:TypeSig) (max:nat): relation evalContext
  := fun σ0 σ1 =>
       forall k t, k<max ->
              TM.MapsTo k t tm ->
              contextEnsureType σ0 k t /\
              contextEnsureType σ1 k t /\ (* this is redundant *)
              context_lookup "" σ0 k = context_lookup "" σ1 k. (* Error messages must be empty *)

Lemma context_equiv_at_TypeSig_0 {tm σ0 σ1}:
  context_equiv_at_TypeSig_off tm 0 σ0 σ1 <-> context_equiv_at_TypeSig tm σ0 σ1.
Proof.
  split; intros H.
  -
    unfold context_equiv_at_TypeSig_off in H.
    unfold context_equiv_at_TypeSig.
    intros k t H0.
    specialize (H k t).
    rewrite Nat.sub_0_r in H.
    destruct (lt_ge_dec k 0) as [kc|kc].
    inversion kc.
    auto.
  -
    unfold context_equiv_at_TypeSig_off.
    unfold context_equiv_at_TypeSig in H.
    intros k t kc H1.
    rewrite Nat.sub_0_r.
    apply H.
    auto.
Qed.

Definition TypeSig_incr_n (t:TypeSig) (off:nat): TypeSig :=
  TP.of_list (List.map (fun '(k,v) => (k+off, v)) (TP.to_list t)).

(* Delete all keys < n *)
Definition TypeSig_trunc_first_n (t:TypeSig) (off:nat): TypeSig :=
  TP.filter (fun k _ => off <=? k) t.

Definition TypeSig_decr_n (t:TypeSig) (off:nat): TypeSig :=
  let tc := TypeSig_trunc_first_n t off in
  TP.of_list (List.map (fun '(k,v) => (k-off, v)) (TP.to_list tc)).

(* increases keys in type signature by 1.

TODO: Should be defined as := TypeSig_incr_n t 1.

 *)
Definition TypeSig_incr (t:TypeSig) : TypeSig :=
  TP.of_list (List.map (fun '(k,v) => (S k, v)) (TP.to_list t)).

Definition TypeSig_add (t:TypeSig) (x:DSHType) : TypeSig :=
  TM.add 0 x (TypeSig_incr t).

Definition TypeSig_append (t0 t1: TypeSig) : TypeSig :=
  let l0 := TP.to_list t0 in
  let k0 := List.map fst l0 in
  let off :=
      match k0 with
      | [] => 0%nat
      | _ =>  S (List.fold_left max k0 0%nat)
      end
  in
  let l1 := TP.to_list (TypeSig_incr_n t1 off) in
  TP.of_list (l0++l1).

Lemma InA_map_1 {A : Type}
                (eqA : A -> A -> Prop)
                (x : A)
                (m : list A)
                (f : A -> A) :
  (forall a b, eqA a b -> eqA (f a) (f b)) ->
  InA eqA x m -> InA eqA (f x) (map f m).
Proof.
  intros P H.
  apply InA_alt.
  apply InA_alt in H.
  destruct H as [y [H1 H2]].
  exists (f y).
  split; [apply P; congruence |].
  apply in_map_iff.
  exists y; auto.
Qed.

Lemma InA_map_2 {A : Type}
                (eqA : A -> A -> Prop)
                (x : A)
                (m : list A)
                (f : A -> A) :
  (forall a b, eqA (f a) (f b) -> eqA a b) ->
  InA eqA (f x) (map f m) -> InA eqA x m.
Proof.
  intros P H.
  apply InA_alt.
  apply InA_alt in H.
  destruct H as [fy [H1 H2]].
  apply in_map_iff in H2.
  destruct H2 as [y [H2 H3]].
  exists y; split;
    [apply P; congruence | assumption].
Qed.

Lemma InA_map_prototype {A : Type}
                        (eqA : A -> A -> Prop)
                        (fx : A)
                        (m : list A)
                        (f : A -> A) :
  Reflexive eqA ->
  InA eqA fx (map f m) -> (exists x, InA eqA x m /\ eqA fx (f x)).
Proof.
  intros R H.
  apply InA_alt in H.
  destruct H as [fy [H1 H2]].
  apply in_map_iff in H2.
  destruct H2 as [y [H2 H3]].
  exists y.
  split; [| congruence].
  induction m;
    [inversion H3 |].
  simpl in H3; destruct H3 as [EQ | NEQ].
  -
    apply InA_cons_hd.
    rewrite EQ.
    apply R.
  -
    apply InA_cons_tl.
    intuition.
Qed.

Lemma TypeSig_incr_NoDupA (tm : TypeSig) :
  NoDupA (TM.eq_key (elt:=DSHType)) (map (λ '(k, v), (S k, v)) (to_list tm)).
Proof.
    unfold to_list.
    pose proof TM.elements_3w (elt:=DSHType) tm.
    induction H; [constructor |].
    simpl.
    break_match.
    constructor; [| assumption].
    intros C; contradict H.
    apply InA_alt.
    apply InA_alt in C.
    destruct C as [y [H1 H2]].
    apply in_map_iff in H2.
    destruct H2 as [x' [H2 H3]].
    break_match; subst.
    inversion H1; subst.
    exists (n, d0); split; [reflexivity | assumption].
Qed.


Lemma TypeSig_incr_n_NoDupA (tm : TypeSig) (n : nat) :
  NoDupA (TM.eq_key (elt:=DSHType)) (map (λ '(k, v), (k + n, v)) (to_list tm)).
Proof.
  unfold to_list.
  pose proof TM.elements_3w (elt:=DSHType) tm.
  induction H; [constructor |].
  simpl.
  break_match.
  constructor; [| assumption].
  intros C; contradict H.
  apply InA_alt.
  apply InA_alt in C.
  destruct C as [y [H1 H2]].
  apply in_map_iff in H2.
  destruct H2 as [x' [H2 H3]].
  break_match; subst.
  inversion H1; subst.
  exists (n0, d0); split;
    [cbv; lia | assumption].
Qed.

Lemma InA_eqk_eqke {elt : Type} (k : TM.key) (e' : elt) (l : list (TM.key * elt)) :
  InA (TM.eq_key (elt:=elt)) (k, e') l ->
  exists e, InA (TM.eq_key_elt (elt:=elt)) (k, e) l.
Proof.
  intros.
  apply InA_alt in H.
  destruct H as [(k0, e) [EQK IN]].
  cbv in EQK; subst k0.
  exists e.
  apply In_InA.
  typeclasses eauto.
  assumption.
Qed.

Lemma TypeSig_trunc_first_n_keys (dfs : TypeSig) (n : nat) :
  forall p, InA (TM.eq_key (elt:=DSHType)) p (TM.elements (TypeSig_trunc_first_n dfs n)) ->
       n <= fst p.
Proof.
  intros; destruct p as (k, e'); simpl.

  (* if (k, _) is in [elements], then [k] [MapsTo] something *)
  apply InA_eqk_eqke in H;
    clear e';
    destruct H as [e H];
    apply F.elements_mapsto_iff in H.

  unfold TypeSig_trunc_first_n in H.
  apply filter_iff in H; [| typeclasses eauto].
  apply Nat.leb_le, H.
Qed.

Lemma TypeSig_trunc_first_n_NoDupA (dfs : TypeSig) (n : nat) :
  NoDupA (TM.eq_key (elt:=DSHType))
         (map (λ '(k, v), (k - n, v)) (to_list (TypeSig_trunc_first_n dfs n))).
Proof.
  unfold to_list.
  pose proof TM.elements_3w (elt:=DSHType) (TypeSig_trunc_first_n dfs n) as ND.
  pose proof TypeSig_trunc_first_n_keys dfs n as K.
  induction ND.
  -
    constructor.
  -
    simpl.
    constructor.
    +
      intros C; contradict H.
      clear - K C.
      apply InA_map_prototype in C;
        [| subst; typeclasses eauto].
      destruct C as [x' [C1 C2]].
      destruct x as (k, e), x' as (k', e').
      replace k' with k in *.
      *
        apply InA_alt; apply InA_alt in C1.
        destruct C1 as [p H].
        exists p.
        apply H.
      *
        assert (n <= fst (k, e))
          by (apply K; constructor; reflexivity).
        assert (n <= fst (k', e'))
          by (apply K; constructor 2; assumption).
        inversion C2.
        simpl in *.
        omega.
    +
      apply IHND.
      intros.
      apply K.
      constructor 2.
      assumption.
Qed.

Lemma MapsTo_TypeSig_incr {tm : TypeSig}
                          {k : nat}
                          {t : DSHType} :
  TM.MapsTo (S k) t (TypeSig_incr tm) → TM.MapsTo k t tm.
Proof.
  intros H.
  unfold TypeSig_incr in H.
  apply of_list_1 in H;
    [| apply TypeSig_incr_NoDupA].
  remember (λ '(k, v), (S k, v)) as f.
  remember (TM.eq_key_elt (elt:=DSHType)) as K.
  assert (KP : ∀ a b, K (f a) (f b) → K a b).
  {
    subst; clear.
    intros.
    repeat break_match.
    cbv in *.
    intuition.
  }
  pose proof InA_map_2 K (k, t) (to_list tm) f KP.
  subst; apply H0 in H; clear - H.
  apply TM.elements_2.
  assumption.
Qed.

Lemma InA_to_list_of_list
      {elt : Type}
      (l : list (TM.key * elt))
      (e : TM.key * elt)
      {ND : NoDupA (TM.eq_key (elt:=elt)) l} :
  InA (TM.eq_key_elt (elt:=elt)) e l <->
  InA (TM.eq_key_elt (elt:=elt)) e (to_list (of_list l)).
Proof.
  apply of_list_2 in ND.
  unfold equivlistA in ND.
  apply ND.
Qed.

Lemma find_TypeSig_incr
      {tm : TypeSig}
      {k : nat} :
  TM.find (S k) (TypeSig_incr tm) ≡ TM.find k tm.
Proof.
  destruct TM.find eqn:H1 at 1;
  destruct TM.find eqn:H2 at 1.
  all: try rewrite <-F.find_mapsto_iff in H1.
  all: try rewrite <-F.find_mapsto_iff in H2.
  4:reflexivity.
  2,3:exfalso.
  -
    apply MapsTo_TypeSig_incr in H1.
    f_equal.
    eapply F.MapsTo_fun; eassumption.
  -
    apply MapsTo_TypeSig_incr in H1.
    rewrite F.find_mapsto_iff in H1.
    congruence.
  -
    contradict H1; apply F.in_find_iff.
    apply F.elements_in_iff; exists d.
    apply TM.elements_1 in H2.
    unfold TypeSig_incr.
    rewrite <-InA_to_list_of_list by apply TypeSig_incr_NoDupA.
    apply InA_map_1 with (f := λ '(k0, v), (S k0, v)) in H2.
    assumption.
    clear; cbv; intros.
    repeat break_let; intuition.
Qed.

Lemma TypeSig_decr_n_MapsTo
      (ts : TypeSig)
      (v : DSHType)
      (k n : nat) :
  TM.MapsTo k v (TypeSig_decr_n ts n) <-> TM.MapsTo (n + k) v ts.
Proof.
  split; intros.
  -
    apply TP.filter_iff with (f := λ (k : TM.key) (_ : DSHType), n <=? k);
      [typeclasses eauto |].
    unfold TypeSig_decr_n in H.
    apply TP.of_list_1 in H;
      [| apply TypeSig_trunc_first_n_NoDupA].
    apply InA_map_prototype in H;
      [| typeclasses eauto].
    destruct H as [(pk, pt) [M1 M2]].
    replace (n + k) with pk.
    +
      apply TP.F.elements_mapsto_iff.
      inversion M2; simpl in *; subst.
      unfold to_list, TypeSig_trunc_first_n in M1.
      assumption.
    +
      unfold to_list in M1.
      apply TP.InA_eqke_eqk with (k2:=pk) (e2:=pt) in M1; [| reflexivity].
      apply TypeSig_trunc_first_n_keys in M1.
      inversion M2; simpl in *; omega.
  -
    assert (TM.MapsTo (n + k) v ts /\
            (λ (k : TM.key) (_ : DSHType), n <=? k) (n + k) v = true)
      by (split; [assumption | apply leb_correct; omega]).
    clear H; rename H0 into H.
    apply TP.filter_iff in H; [| typeclasses eauto].
    apply TP.F.elements_mapsto_iff in H.
    apply TP.of_list_1; [apply TypeSig_trunc_first_n_NoDupA |].
    apply InA_map_1 with (f := (λ '(k0, v0), (k0 - n, v0))) in H.
    +
      replace (n + k - n) with k in H by omega.
      assumption.
    +
      clear; intros.
      repeat break_let; subst.
      cbv in H.
      destruct H; subst.
      reflexivity.
Qed.

Lemma context_equiv_at_TypeSig_off_decr {dfs σ0 σ1 n}:
  context_equiv_at_TypeSig (TypeSig_decr_n dfs n) σ0 σ1 <->
  context_equiv_at_TypeSig_off dfs n σ0 σ1.
Proof.
  split; intros H.
  -
    intros k t KN M.
    apply H; clear H.

    remember (λ (k : TM.key) (_ : DSHType), n <=? k) as f eqn:F.
    assert (TM.MapsTo k t (filter f dfs)).
    {
      apply filter_iff.
      simpl_relation.
      split;
        [apply M | subst; apply Nat.leb_le; assumption].
    }

    clear - H F.
    unfold TypeSig_decr_n.
    apply of_list_1;
      [apply TypeSig_trunc_first_n_NoDupA |].
    apply TM.elements_1 in H.
    unfold TypeSig_trunc_first_n; rewrite <-F.
    apply InA_map_1 with (f0:=λ '(k, v), (k - n, v)) in H;
      [apply H |].
    intros.
    repeat break_let.
    cbv in H0.
    destruct H0; subst.
    reflexivity.
  -
    intros k t M.
    specialize (H (n + k) t).
    replace (n + k - n) with k in H by omega.
    apply H; [omega |].
    apply TypeSig_decr_n_MapsTo; assumption.
Qed.

Lemma context_equiv_at_TypeSig_widening {σ0 σ1 tm foo0 foo1}:
  context_equiv_at_TypeSig tm σ0 σ1 ->
  context_equiv_at_TypeSig (TypeSig_incr tm) (foo0 :: σ0) (foo1 :: σ1).
Proof.
  intros H k t M.
  destruct k.
  -
    exfalso.
    apply of_list_1 in M;
      [| apply TypeSig_incr_NoDupA].
    apply InA_alt in M.
    destruct M as [x [H1 H2]].
    apply in_map_iff in H2.
    destruct H2 as [y [H2 H3]].
    break_match; subst.
    inversion H1; discriminate.
  -
    specialize (H k t (MapsTo_TypeSig_incr M)).
    destruct H as [ET0 [ET1 L]].
    repeat split.
    +
      unfold contextEnsureType in *.
      crush.
    +
      unfold contextEnsureType in *.
      crush.
    +
      simpl.
      assumption.
Qed.

Lemma TypeSig_incr_n_0 (ts : TypeSig) :
  TypeSig_incr_n ts 0 = ts.
Proof.
  unfold TypeSig_incr_n.
  assert (forall (A : Type) (l : list (nat * A)), List.map (λ '(k, v), (k + 0, v)) l ≡ l).
  {
    intros.
    induction l; [reflexivity |].
    cbn.
    break_let.
    rewrite IHl.
    replace (n + 0) with n by trivial.
    reflexivity.
  }
  rewrite H.
  unfold equiv, TypeSig_Equiv.
  intros.
  rewrite TP.of_list_3.
  reflexivity.
Qed.

Lemma TypeSig_incr_TypeSig_incr_n (ts : TypeSig) (n : nat) :
  TypeSig_incr_n ts (S n) = TypeSig_incr (TypeSig_incr_n ts n).
Proof.
  unfold equiv, TypeSig_Equiv; intro.
  destruct k.
  -
    (* both sides are [None] *)
    destruct TM.find eqn:H1, TM.find eqn:H2 at 1;
      try reflexivity; exfalso.
    +
      clear - H1.
      rewrite <-F.find_mapsto_iff in *.
      unfold TypeSig_incr_n in *.
      rewrite of_list_1 in * by apply TypeSig_incr_n_NoDupA.
      apply InA_map_prototype in H1; [| typeclasses eauto].
      destruct H1 as [x1 [H11 H12]].
      break_let; inversion H12.
      cbn in *.
      omega.
    +
      clear - H1.
      rewrite <-F.find_mapsto_iff in *.
      unfold TypeSig_incr_n in *.
      rewrite of_list_1 in * by apply TypeSig_incr_n_NoDupA.
      apply InA_map_prototype in H1; [| typeclasses eauto].
      destruct H1 as [x1 [H11 H12]].
      break_let; inversion H12.
      cbn in *.
      omega.
    +
      clear - H2.
      rewrite <-F.find_mapsto_iff in *.
      unfold TypeSig_incr in *.
      rewrite of_list_1 in * by apply TypeSig_incr_NoDupA.
      apply InA_map_prototype in H2; [| typeclasses eauto].
      destruct H2 as [x2 [H21 H22]].
      break_let; inversion H22.
      cbn in *.
      omega.
  -
    rewrite find_TypeSig_incr.
    destruct TM.find eqn:H1, TM.find eqn:H2 at 1.
    4: reflexivity.
    2,3: exfalso.
    +
      rewrite <-F.find_mapsto_iff in *.
      unfold TypeSig_incr_n in *.
      rewrite of_list_1 in * by apply TypeSig_incr_n_NoDupA.
      apply InA_map_prototype in H1; [| typeclasses eauto].
      apply InA_map_prototype in H2; [| typeclasses eauto].
      destruct H1 as [x1 [H11 H12]].
      destruct H2 as [x2 [H21 H22]].
      repeat break_let.
      inversion H12; inversion H22; cbn in *; subst.
      replace k0 with k1 in * by omega.
      rewrite <-of_list_1 in * by apply TM.elements_3w.
      enough (T : d2 ≡ d1) by (rewrite T; reflexivity).
      eapply F.MapsTo_fun; eassumption.
    +
      contradict H2;
        apply F.in_find_iff, F.elements_in_iff;
        exists d.
      unfold TypeSig_incr_n in *;
        rewrite <-InA_to_list_of_list by apply TypeSig_incr_n_NoDupA.
      rewrite <-F.find_mapsto_iff in *.
      rewrite of_list_1 in * by apply TypeSig_incr_n_NoDupA.
      apply InA_map_prototype in H1; [| typeclasses eauto].
      destruct H1 as [x1 [H11 H12]].
      repeat break_let; subst.
      inversion H12; cbn in *; subst.
      apply InA_map_1 with (f := λ '(k1, v), (k1 + n, v)) in H11;
        [| clear; cbv; intros; repeat break_let; intuition].
      replace (k0 + n) with k in * by omega.
      assumption.
    +
      contradict H1;
        apply F.in_find_iff, F.elements_in_iff;
        exists d.
      unfold TypeSig_incr_n in *;
        rewrite <-InA_to_list_of_list by apply TypeSig_incr_n_NoDupA.
      rewrite <-F.find_mapsto_iff in *.
      rewrite of_list_1 in * by apply TypeSig_incr_n_NoDupA.
      apply InA_map_prototype in H2; [| typeclasses eauto].
      destruct H2 as [x2 [H21 H22]].
      repeat break_let; subst.
      inversion H22; cbn in *; subst.
      apply InA_map_1 with (f := λ '(k1, v), (k1 + S n, v)) in H21;
        [| clear; cbv; intros; repeat break_let; intuition].
      replace (k0 + S n) with (S (k0 + n)) in * by omega.
      assumption.
Qed.

Require Import CoLoR.Util.List.ListUtil.

Lemma find_Empty (elt : Type) (m : TM.t elt) :
  TM.Empty (elt:=elt) m <->
  forall k, TM.find k m ≡ None.
Proof.
  split; intros.
  -
    apply elements_Empty in H.
    rewrite F.elements_o, H.
    reflexivity.
  -
    unfold TM.Empty, TM.Raw.Proofs.Empty.
    intros.
    specialize (H a).
    intros C; contradict H.
    pose proof F.find_mapsto_iff.
    unfold TM.MapsTo in H.
    apply H in C.
    congruence.
Qed.

Lemma context_equiv_at_TypeSigUnion_left {σ0 σ1 dsig1 dsig2}:
  TypeSigCompat dsig1 dsig2 ->
  context_equiv_at_TypeSig (TypeSigUnion dsig1 dsig2) σ0 σ1 ->
  context_equiv_at_TypeSig dsig1 σ0 σ1.
Proof.
  unfold context_equiv_at_TypeSig.
  intros; apply H0; clear - H H1.
  apply update_mapsto_iff.
  destruct (F.In_dec (elt:=DSHType) dsig2 k) as [I|];
    [left | auto].
  apply TM.find_2.
  unfold TypeSigCompat, TypeSigUnion in H.
  apply find_Empty with (k := k) in H.
  unfold findTypeSigConflicts, TypeSig in H.
  rewrite TM.map2_1 in H by auto.
  rewrite TM.find_1 with (e := t) in H by assumption.
  unfold bool_decide in H.
  repeat break_match_hyp; try congruence.
  apply F.in_find_iff in I; congruence.
Qed.

Lemma context_equiv_at_TypeSigUnion_right {σ0 σ1 dsig1 dsig2}:
  TypeSigCompat dsig1 dsig2 ->
  context_equiv_at_TypeSig (TypeSigUnion dsig1 dsig2) σ0 σ1 ->
  context_equiv_at_TypeSig dsig2 σ0 σ1.
Proof.
  unfold context_equiv_at_TypeSig.
  intros; apply H0; clear - H H1.
  apply update_mapsto_iff.
  destruct (F.In_dec (elt:=DSHType) dsig1 k) as [I|];
    [left | auto].
  apply TM.find_2.
  unfold TypeSigCompat, TypeSigUnion in H.
  apply find_Empty with (k := k) in H.
  unfold findTypeSigConflicts, TypeSig in H.
  rewrite TM.map2_1 in H by auto.
  rewrite TM.find_1 with (e := t) (m := dsig2) in H by assumption.
  unfold bool_decide in H.
  repeat break_match_hyp; try congruence.
  apply TM.find_1; assumption.
  apply F.in_find_iff in I; congruence.
Qed.

Lemma context_equiv_at_TypeSig_off_both_typcheck
      (off: nat)
      (dfs : TypeSig)
      (σ0 σ1 : evalContext):
  context_equiv_at_TypeSig_off dfs off σ0 σ1 →
  (typecheck_env off dfs σ0 /\ typecheck_env off dfs σ1).
Proof.
  intros H.
  split.
  -
    unfold typecheck_env, typecheck_env_bool.
    apply for_all_iff; [typeclasses eauto |].
    intros k t M.
    destruct (k <? off) eqn:K; [constructor |].
    simpl; apply bool_decide_true.
    apply Nat.ltb_ge in K.
    assert(kc1: k ≥ off) by lia.
    specialize (H k t kc1 M).
    intuition.
  -
    apply for_all_iff.
    typeclasses eauto.
    intros k t M.
    destruct (k <? off) eqn:K; [constructor |].
    simpl; apply bool_decide_true.
    specialize (H k t).
    apply Nat.ltb_ge in K.
    intuition.
Qed.

(* Special case of previous lemma *)
Lemma context_equiv_at_TypeSig_both_typcheck
      (dfs : TypeSig)
      (σ0 σ1 : evalContext):
  context_equiv_at_TypeSig dfs σ0 σ1 →
  (typecheck_env 0 dfs σ0 /\ typecheck_env 0 dfs σ1).
Proof.
  intros H.
  split.
  -
    unfold typecheck_env, typecheck_env_bool.
    apply for_all_iff; [typeclasses eauto |].
    intros k t M.
    destruct (k <? 0); [constructor |].
    simpl; apply bool_decide_true.
    specialize (H k t M).
    rewrite Nat.sub_0_r.
    intuition.
  -
    apply for_all_iff.
    typeclasses eauto.
    intros k t M.
    destruct (k <? 0); [constructor |].
    simpl; apply bool_decide_true.
    specialize (H k t M).
    rewrite Nat.sub_0_r.
    intuition.
Qed.

(* True if all of [needle]'s keys belong to [haystack] with
   the same values. This is boolean predicate. *)
Definition TypeSigIncluded_bool (needle haystack: TypeSig) : bool
  := TP.for_all (fun k v => bool_decide (TM.find k haystack = Some v)) needle.

(* True if all of [needle]'s keys belong to [haystack] with
   the same values. This is propositional predicate *)
Definition TypeSigIncluded (needle haystack: TypeSig) : Prop
  := TypeSigIncluded_bool needle haystack ≡ true.

(* TODO: move somewhere? *)
Lemma eq_equiv_bool:
  forall (a b:bool), a ≡ b <-> a = b.
Proof.
  split; intros; destr_bool.
Qed.

Global Instance TypeSig_find_proper:
  Proper ((eq) ==> (=) ==> (=)) (TM.find (elt:=DSHType)).
Proof.
  simpl_relation.
  apply H0.
Qed.

Global Instance TypeSig_for_all_proper:
  Proper (((=) ==> (=) ==> (=)) ==> (=) ==> (=)) (for_all (elt:=DSHType)).
Proof.
  simpl_relation.
  destruct (for_all x x0) eqn:X,
           (for_all y y0) eqn:Y;
    try reflexivity; [ contradict Y | contradict X ].
  all: apply not_false_iff_true.
  all: rewrite for_all_iff in *; simpl_relation.
  all: unfold Proper, respectful in H.
  all: assert (K : k = k) by reflexivity.
  all: assert (E : e = e) by reflexivity.
  -
    assert (KEX : TM.MapsTo k e x0) by (rewrite H0; assumption).
    specialize (H k k K e e E).
    rewrite eq_equiv_bool, <-H.
    apply X.
    assumption.
  -
    assert (KEY : TM.MapsTo k e y0) by (rewrite <-H0; assumption).
    specialize (H k k K e e E).
    rewrite eq_equiv_bool, H.
    apply Y.
    assumption.
Qed.

Global Instance TypeSigIncluded_proper:
  Proper ((=) ==> (=) ==> iff) TypeSigIncluded.
Proof.
  intros n0 n1 En s0 s1 Es.
  split; intros H.
  -
    unfold TypeSigIncluded, TypeSigIncluded_bool in *.
    rewrite <- H.
    apply eq_equiv_bool.
    f_equiv; auto.

    simpl_relation.
    apply eq_equiv_bool.
    unfold bool_decide.
    repeat break_if; auto.
    +
      exfalso.
      clear Heqd Heqd0.
      rewrite H1, H0 in e.
      rewrite <- e in n.
      crush.
    +
      exfalso.
      clear Heqd Heqd0.
      rewrite <- H1, Es, <- H0 in e.
      rewrite <- e in n.
      crush.
  -
    unfold TypeSigIncluded, TypeSigIncluded_bool in *.
    rewrite <- H.
    apply eq_equiv_bool.
    f_equiv; auto.
    simpl_relation.
    apply eq_equiv_bool.
    unfold bool_decide.
    repeat break_if; auto.
    +
      exfalso.
      clear Heqd Heqd0.
      rewrite H0, H1, Es in e.
      rewrite <- e in n.
      crush.
    +
      exfalso.
      clear Heqd Heqd0.
      rewrite <- H1, <- Es, <- H0 in e.
      rewrite <- e in n.
      crush.
Qed.

(* If given key if in type signature it must have certain type.
   OK if it is not present *)
Definition TypeSig_MaybeMapsTo (k:nat) (t:DSHType) (tm:TypeSig): Prop :=
  match TM.find k tm with
  | Some t' => t = t'
  | None => True
  end.

Lemma typecheck_env_S (off:nat) (tm:TypeSig) (σ: evalContext)
  :
    forall v,
      TypeSig_MaybeMapsTo off (DSHValToType v) tm ->
      typecheck_env (S off) tm (σ) ->
      typecheck_env off tm (v :: σ).
Proof.
  intros v M T.
  unfold typecheck_env, typecheck_env_bool in *.
  rewrite for_all_iff in * by simpl_relation.
  intros k e KM.
  specialize (T k e KM).
  destruct (le_lt_dec k off) eqn:B1.
  -
    destruct (Nat.eq_dec k off) eqn:B2.
    +
      subst.
      rewrite orb_true_iff, Nat.sub_diag; right.
      cbv; break_if; try reflexivity.
      clear - M KM n.
      contradict n.
      cbv.
      unfold TypeSig_MaybeMapsTo in M.
      rewrite F.find_mapsto_iff in KM.
      rewrite KM in M.
      inversion M.
      apply DSHValToType_DSHValType.
    +
      assert (k < off) by omega.
      rewrite orb_true_iff; left.
      apply Nat.ltb_lt.
      assumption.
  -
    rewrite orb_true_iff in *.
    destruct T as [T | T].
    +
      exfalso.
      apply Nat.ltb_lt in T.
      omega.
    +
      right.
      clear - l T.
      unfold bool_decide in *.
      repeat break_if; try congruence.
      exfalso.
      clear - Heqd0 n l.
      contradict n.
      unfold contextEnsureType in *.
      replace (k - off) with (S (k - S off)) by lia.
      simpl.
      assumption.
Qed.

Lemma TypeSigIncluded_at (needle haystack:TypeSig):
  TypeSigIncluded needle haystack ->
  forall k v, TM.MapsTo k v needle -> TM.MapsTo k v haystack.
Proof.
  intros I k v M.
  unfold TypeSigIncluded, TypeSigIncluded_bool in I.
  rewrite ->for_all_iff in I by simpl_relation.
  specialize (I k v M).
  unfold bool_decide in I;
    break_if; try discriminate; clear Heqd.
  rewrite <-eq_equiv_option_DSHType in e.
  apply F.find_mapsto_iff in e.
  assumption.
Qed.

Lemma MaybeMapsTo_Included (needle haystack:TypeSig):
  forall k t,
    TM.MapsTo k t haystack ->
    TypeSigIncluded needle haystack ->
    TypeSig_MaybeMapsTo k t needle.
Proof.
  intros k t M I.
  unfold TypeSig_MaybeMapsTo in *.
  break_match; try trivial.
  apply TM.find_2 in Heqo.
  apply TypeSigIncluded_at with (haystack:=haystack) in Heqo; [|auto].
  eapply TP.F.MapsTo_fun in Heqo; eauto.
Qed.

Lemma context_equiv_at_TypeSig_split {σ0 σ1 σ0' σ1' tm}:
  context_equiv_at_TypeSig_off tm (length σ0') σ0 σ1 ->

  (length σ0' = length σ1') ->
  context_equiv_at_TypeSig_head tm (length σ0') σ0' σ1' ->

  context_equiv_at_TypeSig_off tm 0 (σ0' ++ σ0) (σ1' ++ σ1).
Proof.
  intros T L H.
  intros k t _ M.
  rewrite Nat.sub_0_r.
  unfold equiv, nat_equiv in L.
  destruct (lt_ge_dec k (length σ0')) as [kc|kc].
  -
    (* head *)
    clear T.
    specialize (H k t kc M).

    unfold contextEnsureType in *.
    unfold context_lookup in *.
    rewrite nth_app_left by assumption.
    rewrite nth_app_left by lia.
    auto.
  -
    (* tail *)
    clear H.
    specialize (T k t kc M).
    unfold contextEnsureType in *.
    unfold context_lookup in *.
    rewrite nth_app_right by assumption.
    rewrite nth_app_right by lia.
    rewrite L in T.
    rewrite L.
    auto.
Qed.

Lemma MapsTo_In (tm : TypeSig) (k : TM.key) (e : DSHType) :
  TM.MapsTo k e tm →
  TM.In (elt:=DSHType) k tm.
Proof.
  intros.
  exists e; assumption.
Qed.

Lemma TypeSigCompat_at
      (t0 t1 : TypeSig):
  TypeSigCompat t0 t1 →
  forall (k : TM.key) (e : DSHType),
    TM.MapsTo k e t0 -> TM.In k t1 ->
    TM.MapsTo k e t1.
Proof.
  intros.
  unfold TypeSigCompat in H.
  apply find_Empty with (k:=k) in H.
  unfold findTypeSigConflicts in H.
  rewrite TM.map2_1 in H
    by (left; apply MapsTo_In with (e := e); assumption).
  rewrite TM.find_1 with (e := e) in H by assumption.
  unfold bool_decide in H.
  repeat break_match; try congruence.
  -
    rewrite e0.
    apply TM.find_2.
    assumption.
  -
    exfalso.
    apply F.in_find_iff in H1.
    congruence.
Qed.

Lemma typecheck_env_TypeSigUnion
      (σ : evalContext)
      (t0 t1 : TypeSig) (off : nat)
      (TSC: TypeSigCompat t0 t1):
  typecheck_env off (TypeSigUnion t0 t1) σ
  → typecheck_env off t0 σ ∧ typecheck_env off t1 σ.
Proof.
  intros CU.
  unfold typecheck_env, typecheck_env_bool, for_all in *.
  split.
  -
    eapply TP.for_all_iff.
    solve_proper.
    intros k e H.
    eapply TP.for_all_iff with (k:=k) (e:=e) in CU.
    +
      apply CU.
    +
      solve_proper.
    +
      unfold TypeSigUnion.
      apply update_mapsto_iff.
      destruct (F.In_dec t1 k);
        [left | auto].
      apply TypeSigCompat_at with (t0:=t0);
        assumption.
  -
    eapply TP.for_all_iff.
    solve_proper.
    intros k e H.
    eapply TP.for_all_iff with (k:=k) (e:=e) in CU.
    +
      apply CU.
    +
      solve_proper.
    +
      unfold TypeSigUnion.
      apply update_mapsto_iff.
      left.
      apply H.
Qed.

Lemma TypeSigUnion_error_typecheck_env
      {σ: evalContext}
      {t0 t1 tu: TypeSig}
      {off:nat}
      (TU: TypeSigUnion_error t0 t1 = Some tu):
  typecheck_env off tu σ ->
  typecheck_env off t0 σ /\ typecheck_env off t1 σ.
Proof.
  intros CU.
  unfold TypeSigUnion_error in TU.
  break_if; try some_none.
  some_inv.
  rewrite <- TU in CU.
  clear TU tu Heqd.
  apply typecheck_env_TypeSigUnion; eauto.
Qed.

Lemma TypeSigIncluded_TypeSigUnion_left (ts s1 s2 : TypeSig) :
  TypeSigCompat s1 s2 ->
  TypeSigIncluded (TypeSigUnion s1 s2) ts ->
  TypeSigIncluded s1 ts.
Proof.
  intros C IU.
  unfold TypeSigUnion, TypeSigIncluded, TypeSigIncluded_bool in *.
  rewrite TP.for_all_iff in * by (typeclasses eauto).
  intros; specialize (IU k e).
  apply IU.
  clear - H C.
  apply TP.update_mapsto_iff.
  destruct (TP.F.In_dec s2 k); [left | right].
  - eapply TypeSigCompat_at; eassumption.
  - auto.
Qed.

Lemma TypeSigIncluded_TypeSigUnion_right (ts s1 s2 : TypeSig) :
  TypeSigIncluded (TypeSigUnion s1 s2) ts ->
  TypeSigIncluded s2 ts.
Proof.
  intros IU.
  unfold TypeSigUnion, TypeSigIncluded, TypeSigIncluded_bool in *.
  rewrite TP.for_all_iff in * by (typeclasses eauto).
  intros; specialize (IU k e).
  apply IU.
  apply TP.update_mapsto_iff.
  left.
  assumption.
Qed.

Lemma context_equiv_at_TypeSigIncluded
  (ts s : TypeSig)
  (σ0 σ1 : evalContext) :
  TypeSigIncluded s ts ->
  context_equiv_at_TypeSig ts σ0 σ1 ->
  context_equiv_at_TypeSig s σ0 σ1.
Proof.
  unfold context_equiv_at_TypeSig in *.
  intros.
  apply H0.
  clear - H H1.
  eapply TypeSigIncluded_at; eassumption.
Qed.

Lemma typecheck_env_TypeSigIncluded
      (n : nat)
      (σ : evalContext)
      (ts s : TypeSig) :
  TypeSigIncluded s ts ->
  typecheck_env n ts σ ->
  typecheck_env n s σ.
Proof.
  intros.
  unfold typecheck_env, typecheck_env_bool in *.
  rewrite TP.for_all_iff in * by (typeclasses eauto).
  intros; specialize (H0 k e).
  apply H0.
  eapply TypeSigIncluded_at; eassumption.
Qed.

Lemma TypeSig_decr_n_Included
      (needle haystack : TypeSig)
      (n : nat) :
      TypeSigIncluded needle haystack ->
      TypeSigIncluded (TypeSig_decr_n needle n)
                      (TypeSig_decr_n haystack n).
Proof.
  intros.
  unfold TypeSigIncluded, TypeSigIncluded_bool in *.
  rewrite TP.for_all_iff in * by (typeclasses eauto).
  intros k e KN.
  apply TypeSig_decr_n_MapsTo in KN.
  apply H in KN.
  unfold bool_decide in KN.
  break_if; [| discriminate].
  clear Heqd; rename e0 into H1.
  apply eq_equiv_option_DSHType in H1.
  apply TM.find_2 in H1.
  apply TypeSig_decr_n_MapsTo in H1.
  apply TM.find_1 in H1.
  rewrite H1.
  unfold bool_decide.
  break_if; try reflexivity.
  clear - n0.
  contradict n0; reflexivity.
Qed.

Lemma TypeSigIncluded_reflexive :
  forall ts, TypeSigIncluded ts ts.
Proof.
  intros.
  unfold TypeSigIncluded, TypeSigIncluded_bool.
  rewrite TP.for_all_iff by (typeclasses eauto).
  intros.
  apply TM.find_1 in H.
  rewrite H.
  unfold bool_decide.
  break_if; try reflexivity.
  clear - n; contradict n; reflexivity.
Qed.

Global Instance TypeSigCompat_Symmetric :
  Symmetric TypeSigCompat.
Proof.
  unfold Symmetric.
  intros.
  unfold TypeSigCompat, findTypeSigConflicts in *.
  rewrite find_Empty in *.
  intro k; specialize (H k).
  rewrite TP.F.map2_1bis in * by reflexivity.
  repeat break_match; try congruence.
  exfalso; clear - Heqb Heqb0.
  unfold bool_decide in *.
  repeat break_if; try congruence.
  clear - e n.
  cbv in e, n.
  congruence.
Qed.

Lemma TypeSigUnion_error_sym (ts1 ts2 : TypeSig) :
  TypeSigUnion_error ts1 ts2 = TypeSigUnion_error ts2 ts1.
Proof.
  unfold TypeSigUnion_error.
  repeat break_if; try some_none.
  -
    clear - t t0; rename t into Compat12, t0 into Compat21; constructor.

    assert (H12 : ∀ (k : TM.key) (e : DSHType),
               TM.MapsTo k e ts1 → TM.In (elt:=DSHType) k ts2 → TM.MapsTo k e ts2)
     by (eapply TypeSigCompat_at; eassumption).
    assert (H21 : ∀ (k : TM.key) (e : DSHType),
               TM.MapsTo k e ts2 → TM.In (elt:=DSHType) k ts1 → TM.MapsTo k e ts1)
     by (eapply TypeSigCompat_at; eassumption).
    clear Compat12 Compat21.
    unfold TypeSig_Equiv, TypeSigUnion.
    intros; specialize (H12 k); specialize (H21 k).
    destruct TM.find eqn:F12 at 1; destruct TM.find eqn:F21 at 1.
    all: try constructor.
    2,3: exfalso.
    +
      cbv.
      rewrite <-TP.F.find_mapsto_iff, ->TP.update_mapsto_iff in *.
      destruct F12 as [F12 | [F12 F12']],
               F21 as [F21 | [F21 F21']].
      *
        apply H12 in F21.
        eapply TP.F.MapsTo_fun; eassumption.
        eapply MapsTo_In; eassumption.
      *
        eapply TP.F.MapsTo_fun; eassumption.
      *
        eapply TP.F.MapsTo_fun; eassumption.
      *
        contradict F12'.
        eapply MapsTo_In; eassumption.
    +
      rewrite <-TP.F.not_find_in_iff in F21.
      contradict F21.
      apply TP.update_in_iff.
      rewrite <-TP.F.find_mapsto_iff, ->TP.update_mapsto_iff in *.
      destruct F12 as [F12 | [F12 F12']].
      left; eapply MapsTo_In; eassumption.
      right; eapply MapsTo_In; eassumption.
    +
      rewrite <-TP.F.not_find_in_iff in F12.
      contradict F12.
      apply TP.update_in_iff.
      rewrite <-TP.F.find_mapsto_iff, ->TP.update_mapsto_iff in *.
      destruct F21 as [F21 | [F21 F21']].
      left; eapply MapsTo_In; eassumption.
      right; eapply MapsTo_In; eassumption.
  -
    clear - t n.
    contradict n.
    symmetry.
    assumption.
  -
    clear - t n.
    contradict n.
    symmetry.
    assumption.
Qed.

Lemma empty_TypeSigCompat (t : TypeSig) :
  TypeSigCompat (TM.empty DSHType) t.
Proof.
  unfold TypeSigCompat, findTypeSigConflicts.
  apply find_Empty; intro.
  rewrite TP.F.map2_1bis by reflexivity.
  reflexivity.
Qed.

Lemma TypeSig_update_empty (t : TypeSig) :
  TP.update (TM.empty DSHType) t = t.
Proof.
    unfold equiv, TypeSig_Equiv; intros.
    destruct TM.find eqn:H1 at 1, TM.find eqn:H2 at 1.
    all: try rewrite <-TP.F.find_mapsto_iff in *.
    all: try rewrite <-TP.F.not_find_in_iff in *.
    1,2: apply TP.update_mapsto_iff in H1.
    1,2: destruct H1 as [H1 | [C _]]; [| inversion C].
    4: reflexivity.
    +
      pose proof TP.F.MapsTo_fun H1 H2.
      subst; reflexivity.
    +
      apply MapsTo_In in H1.
      congruence.
    +
      contradict H1.
      apply TP.update_in_iff.
      right.
      eapply MapsTo_In; eassumption.
Qed.

Global Instance TypeSigCompat_proper:
  Proper ((=) ==> (=) ==> (iff)) TypeSigCompat.
Proof.
  unfold TypeSigCompat.
Admitted.
