(* Deep-embedded language of arithmetic expressions for SigmaHCOL. *)

Require Import Coq.Arith.Peano_dec.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Compare.

Require Import Helix.Util.VecSetoid.
Require Import Helix.Util.VecUtil.
Require Import Helix.Util.FinNat.
Require Import Helix.Tactics.HelixTactics.
Require Import Helix.HCOL.CarrierType.

Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.orders.minmax.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.misc.decision.

Local Open Scope nat_scope.

(* Variable names (typed) *)
Inductive varname (t:Type) :=
| VarId: nat -> varname t.

Global Instance eq_varname_dec {t:Type} (n m: varname t):
  Decision (eq n m).
Proof.
  destruct n as [n].
  destruct m as [m].
  pose proof (eq_nat_dec m n) as H.
  destruct H.
  - left; auto.
  - right. congruence.
Defined.

Global Instance varname_Le (T:Type):
  Le (varname T)
  := fun a b => match a, b with
             | VarId _ av, VarId _ bv => le av bv
             end.

Global Instance varname_TotalRelation_le {T:Type}:
  TotalRelation (varname_Le T).
Proof.
  intros a b.
  unfold varname_Le.
  repeat break_match.
  apply total.
  typeclasses eauto.
Qed.

Global Instance le_varname_dec {t:Type} (n m: varname t):
  Decision (le n m).
Proof.
  destruct n as [n].
  destruct m as [m].
  assert(H: Decision (le  n m)) by typeclasses eauto.
  destruct H.
  - left; unfold le, varname_Le; auto.
  - right. unfold le, varname_Le. auto.
Qed.

Definition varname_succ {t:Type} (x:varname t) : varname t
  := match x with
     | VarId _ n => VarId _ (S n)
     end.

Ltac varname_ne_tac :=
  let H := fresh in
  match goal with
  | [ |- ?a≠?b] =>
    match type of a with
    | varname _ => intros H; inversion H
    end
  end.

(* We can get away with regular `eq` here *)
Global Instance varname_Equiv {t:Type}: Equiv (varname t) := eq.

Global Instance varname_equivalence {t:Type}: Equivalence (@varname_Equiv t).
Proof.
  split.
  -
    intros x.
    destruct x; crush.
  -
    intros x y E.
    destruct x,y; crush.
  -
    intros x y z Exy Eyz.
    destruct x,y,z; crush.
Qed.

Inductive varname_avector_jmequiv {n n': nat}: varname (vector CarrierA n) ->  varname (vector CarrierA n') -> Prop
  :=
  | JMEq_varname_avector x y: n=n' ->
                              varname_avector_jmequiv (VarId (vector CarrierA n) x) (VarId (vector CarrierA n') y).

(* Expressions which evaluate to `CarrierA` *)
Inductive AExpr : Type :=
| AVar  : varname CarrierA -> AExpr
| AConst: CarrierA -> AExpr
| ANth  : forall n, VExpr n -> NExpr -> AExpr
| AAbs  : AExpr -> AExpr
| APlus : AExpr -> AExpr -> AExpr
| AMinus: AExpr -> AExpr -> AExpr
| AMult : AExpr -> AExpr -> AExpr
| AMin  : AExpr -> AExpr -> AExpr
| AMax  : AExpr -> AExpr -> AExpr
| AZless: AExpr -> AExpr -> AExpr
with
(* Expressions which evaluate to `nat` *)
NExpr: Type :=
| NVar  : varname nat -> NExpr
| NConst: nat -> NExpr
| NDiv  : NExpr -> NExpr -> NExpr
| NMod  : NExpr -> NExpr -> NExpr
| NPlus : NExpr -> NExpr -> NExpr
| NMinus: NExpr -> NExpr -> NExpr
| NMult : NExpr -> NExpr -> NExpr
| NMin  : NExpr -> NExpr -> NExpr
| NMax  : NExpr -> NExpr -> NExpr
(* Expressions which evaluate to `avector n` *)
with VExpr: nat -> Type :=
     | VVar  {n:nat}: varname (avector n) -> VExpr n
     | VConst {n:nat}: avector n -> VExpr n.

(* We can get away with regular `eq` here *)
Global Instance NExpr_Equiv: Equiv (NExpr) := eq.
Global Instance NExpr_equivalence : Equivalence NExpr_Equiv.
Proof.
  split.
  -
    intros x.
    crush.
  -
    intros x y E.
    crush.
  -
    intros x y z Exy Eyz.
    destruct x,y,z; try congruence.
Qed.

(* TODO: move. For some reason it does not work after moving to Helixtactics.v. Investigate why *)
Ltac simpl_existT_eq :=
  repeat match goal with
         | [ H : existT _ ≡ existT _ |- _] => simplHyp H; intros H
         end.

(* We need custom equality here to use `@equiv (avector n)` to compare `CarrierA` constants which may occur in `VExpr` *)
Inductive VExpr_equiv {n}: (VExpr n) -> (VExpr n) -> Prop :=
| VVar_Eq {v v'}: v=v' -> VExpr_equiv (VVar v) (VVar v')
| VConst_Eq {c c'}: c=c'-> VExpr_equiv (VConst c) (VConst c').

Global Instance VExpr_Equiv {n}: Equiv (VExpr n) := VExpr_equiv.

Global Instance VExpr_equivalence {n} : Equivalence (@VExpr_Equiv n).
Proof.
  split.
  -
    intros x.
    destruct x; constructor; auto.
  -
    intros x y E.
    destruct x,y; try constructor; inversion E; crush.
  -
    intros x y z Exy Eyz.
    destruct x,y,z; try constructor; inversion Exy; inversion Eyz; crush.
Qed.

(* We need custom equality here to use `@equiv CarrierA` to compare `CarrierA` constants which may occur in `AExpr` *)
Inductive AExpr_equiv: AExpr -> AExpr -> Prop :=
| Eq_AVar {v v'}: v = v' -> AExpr_equiv (AVar v) (AVar v')
| Eq_Const {x x'}: x = x' -> AExpr_equiv (AConst x) (AConst x')
| Eq_ANth {n i i' v v'}:  (v = v') -> (i = i') -> AExpr_equiv (ANth n v i) (ANth n v' i')
| Eq_AAbs {x x'}: AExpr_equiv x x' -> AExpr_equiv (AAbs x) (AAbs x')
| Eq_APlus {x y x' y'}: AExpr_equiv x x' -> AExpr_equiv y y' -> AExpr_equiv (APlus x y) (APlus x' y')
| Eq_AMinus {x y x' y'}: AExpr_equiv x x' -> AExpr_equiv y y' -> AExpr_equiv (AMinus x y) (AMinus x' y')
| Eq_AMult {x y x' y'}: AExpr_equiv x x' -> AExpr_equiv y y' -> AExpr_equiv (AMult x y) (AMult x' y')
| Eq_AMin {x y x' y'}: AExpr_equiv x x' -> AExpr_equiv y y' -> AExpr_equiv (AMin x y) (AMin x' y')
| Eq_AMax {x y x' y'}: AExpr_equiv x x' -> AExpr_equiv y y' -> AExpr_equiv (AMax x y) (AMax x' y')
| Eq_AZless {x y x' y'}: AExpr_equiv x x' -> AExpr_equiv y y' -> AExpr_equiv (AZless x y) (AZless x' y')
.

Global Instance AExpr_Equiv: Equiv (AExpr) := AExpr_equiv.

Global Instance AExpr_equivalence : Equivalence AExpr_Equiv.
Proof.
  split.
  -
    intros x.
    induction x; constructor; auto.
  -
    intros x y E.
    induction E; constructor; auto.
  -
    intros x y z Exy.
    revert z.
    induction Exy; intros z Eyz; unfold AExpr_Equiv in *;
      destruct z; try inversion Eyz; subst; constructor; crush.
Qed.

Set Printing All.
Notation varset t := (set (varname t)).

Section Alpha_Equivalence.

  Fixpoint is_natvar_free (x:varname nat) (e:NExpr) : bool
    :=
      match e with
      | NVar v => if eq_varname_dec v x then false else true
      | NConst _ => true
      | NDiv     a b => andb (is_natvar_free x a) (is_natvar_free x b)
      | NMod    a b => andb (is_natvar_free x a) (is_natvar_free x b)
      | NPlus    a b => andb (is_natvar_free x a) (is_natvar_free x b)
      | NMinus a b => andb (is_natvar_free x a) (is_natvar_free x b)
      | NMult   a b => andb (is_natvar_free x a) (is_natvar_free x b)
      | NMin    a b => andb (is_natvar_free x a) (is_natvar_free x b)
      | NMax   a b => andb (is_natvar_free x a) (is_natvar_free x b)
      end.

  Fixpoint free_natvar (e:NExpr) : varname nat
    :=
      match e with
      | NVar v  => varname_succ v
      | NConst _ => VarId _ 0
      | NDiv      a b => max (free_natvar a) (free_natvar b)
      | NMod     a b => max (free_natvar a) (free_natvar b)
      | NPlus     a b => max (free_natvar a) (free_natvar b)
      | NMinus  a b => max (free_natvar a) (free_natvar b)
      | NMult    a b => max (free_natvar a) (free_natvar b)
      | NMin     a b => max (free_natvar a) (free_natvar b)
      | NMax    a b => max (free_natvar a) (free_natvar b)
      end.

  (* Currently VExpr does not even include `(varname nat)` even indirectly so this
   implementation is do-nothing. It is a placeholder for future. *)
  Definition VExpr_natvar_subst
             {n}
             (bound: varset nat)
             (k k': varname nat):
    VExpr n -> VExpr n := id.

  (* Currently VExpr does not even include `(varname CarrierA)` even indirectly so this
   implementation is do-nothing. It is a placeholder for future. *)
  Definition VExpr_avar_subst
             {n}
             (bound: varset CarrierA)
             (k k': varname CarrierA):
    VExpr n -> VExpr n := id.

  (* Currently NExpr does not even include `(varname CarrierA)` even indirectly so this
   implementation is do-nothing. It is a placeholder for future. *)
  Fixpoint NExpr_avar_subst
           (bound: varset CarrierA)
           (k k': varname CarrierA):
    NExpr -> NExpr := id.

  Fixpoint NExpr_natvar_subst
           (bound: varset nat)
           (k k': varname nat)
           (nexp: NExpr): NExpr :=
    match nexp with
    | NVar v =>
      if set_mem eq_varname_dec v bound then
        if eq_varname_dec v k
        then NVar k'
        else nexp
      else nexp
    | NConst _ => nexp
    | NDiv     a b => NDiv (NExpr_natvar_subst bound k k' a) (NExpr_natvar_subst bound k k' b)
    | NMod    a b => NMod (NExpr_natvar_subst bound k k' a) (NExpr_natvar_subst bound k k' b)
    | NPlus    a b => NPlus (NExpr_natvar_subst bound k k' a) (NExpr_natvar_subst bound k k' b)
    | NMinus a b => NMinus (NExpr_natvar_subst bound k k' a) (NExpr_natvar_subst bound k k' b)
    | NMult   a b => NMult (NExpr_natvar_subst bound k k' a) (NExpr_natvar_subst bound k k' b)
    | NMin    a b => NMin (NExpr_natvar_subst bound k k' a) (NExpr_natvar_subst bound k k' b)
    | NMax   a b => NMax (NExpr_natvar_subst bound k k' a) (NExpr_natvar_subst bound k k' b)
    end.

  Fixpoint AExpr_natvar_subst
           (bound: varset nat)
           (k k': varname nat)
           (aexp: AExpr): AExpr :=
    match aexp with
    | AVar _ => aexp
    | AConst _ => aexp
    | ANth n ve ne => ANth n (VExpr_natvar_subst bound k k' ve) (NExpr_natvar_subst bound k k' ne)
    | AAbs a => AAbs (AExpr_natvar_subst bound k k' a)
    | APlus    a b => APlus (AExpr_natvar_subst bound k k' a) (AExpr_natvar_subst bound k k' b)
    | AMinus a b => AMinus (AExpr_natvar_subst bound k k' a) (AExpr_natvar_subst bound k k' b)
    | AMult   a b => AMult   (AExpr_natvar_subst bound k k' a) (AExpr_natvar_subst bound k k' b)
    | AMin    a b => AMin    (AExpr_natvar_subst bound k k' a) (AExpr_natvar_subst bound k k' b)
    | AMax   a b => AMax   (AExpr_natvar_subst bound k k' a) (AExpr_natvar_subst bound k k' b)
    | AZless a b => AZless (AExpr_natvar_subst bound k k' a) (AExpr_natvar_subst bound k k' b)
    end.

  Fixpoint AExpr_avar_subst
           (bound: varset CarrierA)
           (k k': varname CarrierA)
           (aexp: AExpr): AExpr :=
    match aexp with
    | AVar v =>
      if set_mem eq_varname_dec v bound then
        if eq_varname_dec v k
        then AVar k'
        else aexp
      else aexp
    | AConst _ => aexp
    | ANth n ve ne => ANth n (VExpr_avar_subst bound k k' ve) (NExpr_avar_subst bound k k' ne)
    | AAbs a => AAbs (AExpr_avar_subst bound k k' a)
    | APlus    a b => APlus (AExpr_avar_subst bound k k' a) (AExpr_avar_subst bound k k' b)
    | AMinus a b => AMinus (AExpr_avar_subst bound k k' a) (AExpr_avar_subst bound k k' b)
    | AMult   a b => AMult   (AExpr_avar_subst bound k k' a) (AExpr_avar_subst bound k k' b)
    | AMin    a b => AMin    (AExpr_avar_subst bound k k' a) (AExpr_avar_subst bound k k' b)
    | AMax   a b => AMax   (AExpr_avar_subst bound k k' a) (AExpr_avar_subst bound k k' b)
    | AZless a b => AZless (AExpr_avar_subst bound k k' a) (AExpr_avar_subst bound k k' b)
    end.

End Alpha_Equivalence.
