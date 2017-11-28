Require Coq.Program.Basics.
Require Coq.Program.Equality.
Require Coq.omega.Omega.
Require Coq.Logic.FunctionalExtensionality.
Require Coq.Vectors.Vector.
Require CoLoR.Util.Vector.VecUtil.
Require Coq.Logic.Eqdep.
Require Coq.Lists.List.
Require Coq.Logic.JMeq.
Require Coq.Arith.Lt.
Require Coq.Arith.Peano_dec.
Require MathClasses.interfaces.canonical_names.
Require Coq.Arith.Arith.
Require Coq.Arith.Minus.
Require Coq.Arith.EqNat.
Require Coq.Program.Program.
Require Coq.Classes.Morphisms.
Require Coq.Strings.String.
Require Coq.Logic.Decidable.
Require Coq.micromega.Psatz.
Require MathClasses.interfaces.abstract_algebra.
Require MathClasses.interfaces.orders.
Require MathClasses.orders.minmax.
Require MathClasses.orders.orders.
Require MathClasses.orders.rings.
Require MathClasses.theory.abs.
Require MathClasses.theory.setoids.
Require CoLoR.Util.Nat.NatUtil.
Require Coq.micromega.Lia.
Require CoLoR.Util.List.ListUtil.
Require MathClasses.theory.rings.
Require MathClasses.theory.naturals.
Require Coq.Bool.Bool.
Require Coq.setoid_ring.Ring.
Require ExtLib.Core.Type.
Require ExtLib.Structures.Monads.
Require ExtLib.Structures.MonadLaws.
Require ExtLib.Data.Monads.WriterMonad.
Require ExtLib.Data.Monads.IdentityMonad.
Require ExtLib.Structures.Monoid.
Require ExtLib.Data.PPair.
Require Coq.Classes.RelationClasses.
Require Coq.Relations.Relations.
Require Coq.Arith.Plus.
Require MathClasses.implementations.peano_naturals.
Require Coq.Sorting.Permutation.
Require Coq.Init.Specif.
Require Coq.Sets.Ensembles.
Require Coq.Bool.BoolEq.
Require MathClasses.orders.semirings.
Require ExtLib.Structures.Monad.
Require Coq.Arith.Compare_dec.
Require Coq.Setoids.Setoid.
Require Coq.Logic.ProofIrrelevance.
Require Coq.Logic.Eqdep_dec.

Module Spiral_DOT_StructTactics.
Module Spiral.
Module StructTactics.
(** [subst_max] performs as many [subst] as possible, clearing all
    trivial equalities from the context. *)
Ltac subst_max :=
  repeat match goal with
           | [ H : ?X = _ |- _ ]  => subst X
           | [H : _ = ?X |- _] => subst X
         end.

(** The Coq [inversion] tries to preserve your context by only adding
    new equalities, and keeping the inverted hypothesis.  Often, you
    want the resulting equalities to be substituted everywhere.  [inv]
    performs this post-substitution.  Often, you don't need the
    original hypothesis anymore.  [invc] extends [inv] and removes the
    inverted hypothesis.  Sometimes, you also want to perform
    post-simplification.  [invcs] extends [invc] and tries to simplify
    what it can. *)
Ltac inv H := inversion H; subst_max.
Ltac invc H := inv H; clear H.
Ltac invcs H := invc H; simpl in *.

(** [inv_prop] finds the first hypothesis including the term [P] and uses [inv]
    to invert it. *)
Ltac inv_prop P :=
  match goal with
  | [ H : context[P] |- _] =>
    inv H
  end.

(** [inv_prop] finds the first hypothesis including the term [P] and uses [invc]
    to invert it. *)
Ltac invc_prop P :=
  match goal with
  | [ H : context[P] |- _] =>
    invc H
  end.

(** [inv_prop] finds the first hypothesis including the term [P] and uses
    [invcs] to invert it. *)
Ltac invcs_prop P :=
  match goal with
  | [ H : context[P] |- _] =>
    invcs H
  end.

(** [break_if] finds instances of [if _ then _ else _] in your goal or
    context, and destructs the discriminee, while retaining the
    information about the discriminee's value leading to the branch
    being taken. *)
Ltac break_if :=
  match goal with
    | [ |- context [ if ?X then _ else _ ] ] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
    | [ H : context [ if ?X then _ else _ ] |- _] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

(** [break_match_hyp] looks for a [match] construct in some
    hypothesis, and destructs the discriminee, while retaining the
    information about the discriminee's value leading to the branch
    being taken. *)
Ltac break_match_hyp :=
  match goal with
    | [ H : context [ match ?X with _ => _ end ] |- _] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

(** [break_match_goal] looks for a [match] construct in your goal, and
    destructs the discriminee, while retaining the information about
    the discriminee's value leading to the branch being taken. *)
Ltac break_match_goal :=
  match goal with
    | [ |- context [ match ?X with _ => _ end ] ] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

(** [break_match] breaks a match, either in a hypothesis or in your
    goal. *)
Ltac break_match := break_match_goal || break_match_hyp.

(** [break_inner_match' t] tries to destruct the innermost [match] it
    find in [t]. *)
Ltac break_inner_match' t :=
 match t with
   | context[match ?X with _ => _ end] =>
     break_inner_match' X || destruct X eqn:?
   | _ => destruct t eqn:?
 end.

(** [break_inner_match_goal] tries to destruct the innermost [match] it
    find in your goal. *)
Ltac break_inner_match_goal :=
 match goal with
   | [ |- context[match ?X with _ => _ end] ] =>
     break_inner_match' X
 end.

(** [break_inner_match_hyp] tries to destruct the innermost [match] it
    find in a hypothesis. *)
Ltac break_inner_match_hyp :=
 match goal with
   | [ H : context[match ?X with _ => _ end] |- _ ] =>
     break_inner_match' X
 end.

(** [break_inner_match] tries to destruct the innermost [match] it
    find in your goal or a hypothesis. *)
Ltac break_inner_match := break_inner_match_goal || break_inner_match_hyp.

(** [break_exists] destructs an [exists] in your context. *)
Ltac break_exists :=
  repeat match goal with
           | [H : exists _, _ |- _ ] => destruct H
         end.

(** [break_exists_exists] destructs an [exists] in your context, and uses
    the witness found as witness for your current goal. *)
Ltac break_exists_exists :=
  repeat match goal with
           | H:exists _, _ |- _ =>
             let x := fresh "x" in
             destruct H as [x]; exists x
         end.

(** [break_and] destructs all conjunctions in context. *)
Ltac break_and :=
  repeat match goal with
           | [H : _ /\ _ |- _ ] => destruct H
         end.

(** [break_and_goal] splits a conjunctive goal into one goal per
    conjunct.  In simpler terms, it splits a goal of the shape [G1 /\
    ... /\ Gn] into [n] goals [G1], ..., [Gn]. *)
Ltac break_and_goal :=
    repeat match goal with
             | [ |- _ /\ _ ] => split
           end.

(** [solve_by_inverison' tac] succeeds if it can solve your goal by
    inverting a hypothesis and then running [tac]. *)
Ltac solve_by_inversion' tac :=
  match goal with
    | [H : _ |- _] => solve [inv H; tac]
  end.

(** [solve_by_inverison] succeeds if it can solve your goal by
    inverting a hypothesis and then running [auto]. *)
Ltac solve_by_inversion := solve_by_inversion' auto.

(** TODO: document this. *)
Ltac apply_fun f H:=
  match type of H with
    | ?X = ?Y => assert (f X = f Y)
  end.

(** [conclude H tac] assumes [H] is of the form [A -> B] and
    specializes it into [B] if it successfully proves [A] using
    [tac]. *)
Ltac conclude H tac :=
  (let H' := fresh in
   match type of H with
     | ?P -> _ => assert P as H' by (tac)
   end; specialize (H H'); clear H').

(** [concludes] specializes all implication hypotheses if it can prove
    their premise using [auto]. *)
Ltac concludes :=
  match goal with
    | [ H : ?P -> _ |- _ ] => conclude H auto
  end.

(** [forward H] performs forward reasoning in hypothesis [H] of the
    shape [A -> B] by asserting [A] to be proven.  You can
    subsequently call [concludes] to specialize [H] to [B]. *)
Ltac forward H :=
  let H' := fresh in
   match type of H with
     | ?P -> _ => assert P as H'
   end.

(** [forwards] performs forward reasoning in all hypotheses. *)
Ltac forwards :=
  match goal with
    | [ H : ?P -> _ |- _ ] => forward H
  end.

(** [find_elim_prop] finds a hypothesis that includes [P] and eliminates it with
    the built-in [elim] tactic. *)
Ltac find_elim_prop P :=
  match goal with
  | [ H : context [ P ] |- _ ] =>
    elim H
  end.

(** [find_elim_prop] finds a hypothesis that includes [P] and eliminates it with
    the built-in [eelim] tactic. *)
Ltac find_eelim_prop P :=
  match goal with
  | [ H : context [ P ] |- _ ] =>
    eelim H
  end.

(** [find_contradiction] solves a goal if two equalities are
    incompatible. *)
Ltac find_contradiction :=
  match goal with
    | [ H : ?X = _, H' : ?X = _ |- _ ] => rewrite H in H'; solve_by_inversion
  end.

(** [find_rewrite] performs a [rewrite] with some hypothesis in some
    other hypothesis. *)
Ltac find_rewrite :=
  match goal with
    | [ H : ?X _ _ _ _ = _, H' : ?X _ _ _ _ = _ |- _ ] => rewrite H in H'
    | [ H : ?X = _, H' : ?X = _ |- _ ] => rewrite H in H'
    | [ H : ?X = _, H' : context [ ?X ] |- _ ] => rewrite H in H'
    | [ H : ?X = _ |- context [ ?X ] ] => rewrite H
  end.

(** [find_rewrite_lem lem] rewrites with [lem] in some hypothesis. *)
Ltac find_rewrite_lem lem :=
  match goal with
    | [ H : _ |- _ ] =>
      rewrite lem in H; [idtac]
  end.

(** [find_rewrite_lem_by lem t] rewrites with [lem] in some
    hypothesis, discharging the generated obligations with [t]. *)
Ltac find_rewrite_lem_by lem t :=
  match goal with
    | [ H : _ |- _ ] =>
      rewrite lem in H by t
  end.

(** [find_erewrite_lem_by lem] erewrites with [lem] in some hypothesis
    if it can discharge the obligations with [eauto]. *)
Ltac find_erewrite_lem lem :=
  match goal with
    | [ H : _ |- _] => erewrite lem in H by eauto
  end.

(** [find_reverse_rewrite] performs a [rewrite <-] with some hypothesis in some
    other hypothesis. *)
Ltac find_reverse_rewrite :=
  match goal with
    | [ H : _ = ?X _ _ _ _, H' : ?X _ _ _ _ = _ |- _ ] => rewrite <- H in H'
    | [ H : _ = ?X, H' : context [ ?X ] |- _ ] => rewrite <- H in H'
    | [ H : _ = ?X |- context [ ?X ] ] => rewrite <- H
  end.

(** [find_inversion] find a symmetric equality and performs [invc] on it. *)
Ltac find_inversion :=
  match goal with
    | [ H : ?X _ _ _ _ _ _ = ?X _ _ _ _ _ _ |- _ ] => invc H
    | [ H : ?X _ _ _ _ _ = ?X _ _ _ _ _ |- _ ] => invc H
    | [ H : ?X _ _ _ _ = ?X _ _ _ _ |- _ ] => invc H
    | [ H : ?X _ _ _ = ?X _ _ _ |- _ ] => invc H
    | [ H : ?X _ _ = ?X _ _ |- _ ] => invc H
    | [ H : ?X _ = ?X _ |- _ ] => invc H
  end.

(** [prove_eq] derives equalities of arguments from an equality of
    constructed values. *)
Ltac prove_eq :=
  match goal with
    | [ H : ?X ?x1 ?x2 ?x3 = ?X ?y1 ?y2 ?y3 |- _ ] =>
      assert (x1 = y1) by congruence;
        assert (x2 = y2) by congruence;
        assert (x3 = y3) by congruence;
        clear H
    | [ H : ?X ?x1 ?x2 = ?X ?y1 ?y2 |- _ ] =>
      assert (x1 = y1) by congruence;
        assert (x2 = y2) by congruence;
        clear H
    | [ H : ?X ?x1 = ?X ?y1 |- _ ] =>
      assert (x1 = y1) by congruence;
        clear H
  end.

(** [tuple_inversion] inverses an equality of tuple into equalities for
    each component. *)
Ltac tuple_inversion :=
  match goal with
    | [ H : (_, _, _, _) = (_, _, _, _) |- _ ] => invc H
    | [ H : (_, _, _) = (_, _, _) |- _ ] => invc H
    | [ H : (_, _) = (_, _) |- _ ] => invc H
  end.

(** [f_apply H f] derives a hypothesis of type [f X = f Y] if [H] has
    type [X = Y]. *)
Ltac f_apply H f :=
  match type of H with
    | ?X = ?Y =>
      assert (f X = f Y) by (rewrite H; auto)
  end.

(** [break_let] breaks a destructuring [let] for a pair. *)
Ltac break_let :=
  match goal with
    | [ H : context [ (let (_,_) := ?X in _) ] |- _ ] => destruct X eqn:?
    | [ |- context [ (let (_,_) := ?X in _) ] ] => destruct X eqn:?
  end.

(** [break_or_hyp] breaks a disjunctive hypothesis, splitting your
    goal into two. *)
Ltac break_or_hyp :=
  match goal with
    | [ H : _ \/ _ |- _ ] => invc H
  end.

(** [copy_apply lem H] adds a hypothesis obtained by [apply]-ing [lem]
    in [H]. *)
Ltac copy_apply lem H :=
  let x := fresh in
  pose proof H as x;
    apply lem in x.

(** [copy_eapply lem H] adds a hypothesis obtained by [eapply]-ing
    [lem] in [H]. *)
Ltac copy_eapply lem H :=
  let x := fresh in
  pose proof H as x;
    eapply lem in x.

(** [conclude_using tac] specializes a hypothesis if it can prove its
    premise using [tac]. *)
Ltac conclude_using tac :=
  match goal with
    | [ H : ?P -> _ |- _ ] => conclude H tac
  end.

(** [find_higher_order_rewrite] tries to [rewrite] with
    possibly-quantified hypotheses into other hypotheses or the
    goal. *)
Ltac find_higher_order_rewrite :=
  match goal with
    | [ H : _ = _ |- _ ] => rewrite H in *
    | [ H : forall _, _ = _ |- _ ] => rewrite H in *
    | [ H : forall _ _, _ = _ |- _ ] => rewrite H in *
  end.

(** [find_reverse_higher_order_rewrite] tries to [rewrite <-] with
    possibly-quantified hypotheses into other hypotheses or the
    goal. *)
Ltac find_reverse_higher_order_rewrite :=
  match goal with
    | [ H : _ = _ |- _ ] => rewrite <- H in *
    | [ H : forall _, _ = _ |- _ ] => rewrite <- H in *
    | [ H : forall _ _, _ = _ |- _ ] => rewrite <- H in *
  end.

(** [clean] removes any hypothesis of the shape [X = X]. *)
Ltac clean :=
  match goal with
    | [ H : ?X = ?X |- _ ] => clear H
  end.

(** [find_apply_hyp_goal] tries solving the goal applying some
    hypothesis. *)
Ltac find_apply_hyp_goal :=
  match goal with
    | [ H : _ |- _ ] => solve [apply H]
  end.

(** [find_copy_apply_lem_hyp lem] tries to find a hypothesis to which
    [lem] can be applied, and adds a hypothesis resulting from the
    application. *)
Ltac find_copy_apply_lem_hyp lem :=
  match goal with
    | [ H : _ |- _ ] => copy_apply lem H
  end.

(** [find_apply_hyp_hyp] finds a hypothesis which can be applied in
    another hypothesis, and performs the application. *)
Ltac find_apply_hyp_hyp :=
  match goal with
    | [ H : forall _, _ -> _,
        H' : _ |- _ ] =>
      apply H in H'; [idtac]
    | [ H : _ -> _ , H' : _ |- _ ] =>
      apply H in H'; auto; [idtac]
  end.

(** [find_copy_apply_hyp_hyp] finds a hypothesis which can be applied
    in another hypothesis, and adds a hypothesis with the application
    performed. *)
Ltac find_copy_apply_hyp_hyp :=
  match goal with
    | [ H : forall _, _ -> _,
        H' : _ |- _ ] =>
      copy_apply H H'; [idtac]
    | [ H : _ -> _ , H' : _ |- _ ] =>
      copy_apply H H'; auto; [idtac]
  end.

(** [find_apply_lem_hyp lem] finds a hypothesis where [lem] can be
    [apply]-ed, and performes the application. *)
Ltac find_apply_lem_hyp lem :=
  match goal with
    | [ H : _ |- _ ] => apply lem in H
  end.

(** [find_eapply_lem_hyp lem] finds a hypothesis where [lem] can be
    [eapply]-ed, and performes the application. *)
Ltac find_eapply_lem_hyp lem :=
  match goal with
    | [ H : _ |- _ ] => eapply lem in H
  end.

(** TODO: document this. *)
Ltac insterU H :=
  match type of H with
    | forall _ : ?T, _ =>
      let x := fresh "x" in
      evar (x : T);
      let x' := (eval unfold x in x) in
        clear x; specialize (H x')
  end.

(** TODO: document this. *)
Ltac find_insterU :=
  match goal with
    | [ H : forall _, _ |- _ ] => insterU H
  end.

(** [eapply_prop P] finds a hypothesis proving [P] and [eapply]-es it. *)
Ltac eapply_prop P :=
  match goal with
    | H : P _ |- _ =>
      eapply H
  end.

(** [find_eapply_prop P] finds a hypothesis including [P] and [eapply]-es it. *)
Ltac find_eapply_prop P :=
  match goal with
    | H : context [ P ] |- _ =>
      eapply H
  end.

(** [isVar t] succeeds if term [t] is a variable in the context. *)
Ltac isVar t :=
    match goal with
      | v : _ |- _ =>
        match t with
          | v => idtac
        end
    end.

(** [remGen t] is useful when one wants to do induction on a
    hypothesis whose indices are not concrete.  By default, the
    [induction] tactic will first generalize them, losing information
    in the process.  By introducing an equality, one can save this
    information while generalizing the hypothesis. *)
Ltac remGen t :=
  let x := fresh in
  let H := fresh in
  remember t as x eqn:H;
    generalize dependent H.

(** [remGenIfNotVar t] performs [remGen t] unless [t] is a simple
    variable. *)
Ltac remGenIfNotVar t := first [isVar t| remGen t].

(** [rememberNonVars H] will pose an equation for all indices of [H]
    that are concrete.  For instance, given: [H : P a (S b) c], it
    will generalize into [H : P a b' c] and [EQb : b' = S b]. *)
Ltac rememberNonVars H :=
  match type of H with
    | _ ?a ?b ?c ?d ?e =>
      remGenIfNotVar a;
      remGenIfNotVar b;
      remGenIfNotVar c;
      remGenIfNotVar d;
      remGenIfNotVar e
    | _ ?a ?b ?c ?d =>
      remGenIfNotVar a;
      remGenIfNotVar b;
      remGenIfNotVar c;
      remGenIfNotVar d
    | _ ?a ?b ?c =>
      remGenIfNotVar a;
      remGenIfNotVar b;
      remGenIfNotVar c
    | _ ?a ?b =>
      remGenIfNotVar a;
      remGenIfNotVar b
    | _ ?a =>
      remGenIfNotVar a
  end.

(* [generalizeEverythingElse H] tries to generalize everything that is
   not [H]. *)
Ltac generalizeEverythingElse H :=
  repeat match goal with
           | [ x : ?T |- _ ] =>
             first [
                 match H with
                   | x => fail 2
                 end |
                 match type of H with
                   | context [x] => fail 2
                 end |
                 revert x]
         end.

(* [prep_induction H] prepares your goal to perform [induction] on [H] by:
   - remembering all concrete indices of [H] via equations;
   - generalizing all variables that are not depending on [H] to strengthen the
     induction hypothesis. *)
Ltac prep_induction H :=
  rememberNonVars H;
  generalizeEverythingElse H.

(* [econcludes] tries to specialize a hypothesis using [eauto]. *)
Ltac econcludes :=
  match goal with
    | [ H : ?P -> _ |- _ ] => conclude H eauto
  end.

(** [find_copy_eapply_lem_hyp lem] tries to find a hypothesis to which
    [lem] can be [eapply]-ed, and adds a hypothesis resulting from the
    application. *)
Ltac find_copy_eapply_lem_hyp lem :=
  match goal with
    | [ H : _ |- _ ] => copy_eapply lem H
  end.

(** [apply_prop_hyp P Q] tries to [apply] a hypothesis about [P] to a
    hypothesis about [Q]. *)
Ltac apply_prop_hyp P Q :=
  match goal with
  | [ H : context [ P ], H' : context [ Q ] |- _ ] =>
    apply H in H'
  end.

(** [apply_prop_hyp P Q] tries to [eapply] a hypothesis about [P] to a
    hypothesis about [Q]. *)
Ltac eapply_prop_hyp P Q :=
  match goal with
  | [ H : context [ P ], H' : context [ Q ] |- _ ] =>
    eapply H in H'
  end.

(** [apply_prop_hyp P Q] tries to [eapply] a hypothesis about [P] to a
    hypothesis about [Q], posing the result as a new hypothesis. *)
Ltac copy_eapply_prop_hyp P Q :=
  match goal with
    | [ H : context [ P ], H' : context [ Q ] |- _ ] =>
      copy_eapply H H'
  end.

Ltac eapply_lem_prop_hyp lem P :=
  match goal with
  | [ H : context [ P ] |- _ ] =>
    eapply lem in H
  end.

Ltac copy_eapply_lem_prop_hyp lem P :=
  match goal with
  | [ H : context [ P ] |- _ ] =>
    copy_eapply lem H
  end.

(** [find_false] finds a hypothesis of the shape [P -> False] in the
    context and cuts your goal with it, leaving you with the
    obligation of proving its premise [P]. *)
Ltac find_false :=
  match goal with
    | H : _ -> False |- _ => exfalso; apply H
  end.

(** [injc H] performs [injection] on [H], then clears [H] and
    simplifies the context. *)
Ltac injc H :=
  injection H; clear H; intros; subst_max.

(** [find_injection] looks for an [injection] in the context and
    performs [injc]. *)
Ltac find_injection :=
  match goal with
    | [ H : ?X _ _ _ _ _ _ = ?X _ _ _ _ _ _ |- _ ] => injc H
    | [ H : ?X _ _ _ _ _ = ?X _ _ _ _ _ |- _ ] => injc H
    | [ H : ?X _ _ _ _ = ?X _ _ _ _ |- _ ] => injc H
    | [ H : ?X _ _ _ = ?X _ _ _ |- _ ] => injc H
    | [ H : ?X _ _ = ?X _ _ |- _ ] => injc H
    | [ H : ?X _ = ?X _ |- _ ] => injc H
  end.

(** [aggressive_rewrite_goal] rewrites in the goal with any
    hypothesis. *)
Ltac aggressive_rewrite_goal :=
  match goal with H : _ |- _ => rewrite H end.

(** [break_exists_name x] destructs an existential in context and
    names the witness [x]. *)
Ltac break_exists_name x :=
  match goal with
  | [ H : exists _, _ |- _ ] => destruct H as [x H]
  end.

End StructTactics.

End Spiral.

End Spiral_DOT_StructTactics.

Module Spiral_DOT_SpiralTactics.
Module Spiral.
Module SpiralTactics.
Import Spiral_DOT_StructTactics.
Import Spiral_DOT_StructTactics.Spiral.
Export Spiral_DOT_StructTactics.Spiral.StructTactics.
Import Coq.Arith.Lt.
Import Coq.Arith.Peano_dec.
Import MathClasses.interfaces.canonical_names.

Ltac rewrite_clear H := rewrite H; clear H.

Ltac nat_lt_0_contradiction := 
  let H' := fresh in
  match goal with
  | [H: Peano.lt ?x O |- _ ] => pose(H' := H); apply lt_n_0 in H'; contradiction H'
  | [H: MathClasses.interfaces.canonical_names.lt ?x O |- _ ] => pose(H' := H); apply lt_n_0 in H'; contradiction H'
  end.

(* See https://stackoverflow.com/questions/46311353/eta-conversion-tactics/46326616 *)
(* h is a dummy argument to make Coq happy, it gets shadowed with `?h` *)
Ltac eta_reduce_all_private h := repeat change (fun x => ?h x) with h.
Ltac eta_reduce_all := eta_reduce_all_private idtac.

(*
Give equality of two functions of type [∀ p : nat, p < n → A] and and a hypotheis [i0=i1] solves the goal.
*)
Ltac forall_n_lt_eq :=
  let lc := fresh in
  let rc := fresh in
  let Q := fresh in
  let HeqQ := fresh in
  match goal with
  | [ H: ?i0 ≡ ?i1 |-  ?gen ?i0 ?ic0 ≡ ?gen ?i1 ?ic1] =>
    generalize ic0 as lc;
    generalize ic1 as rc;
    intros rc lc ;
    remember i0 as Q eqn:HeqQ;
    rewrite H in HeqQ;
    subst Q;
    apply f_equal, le_unique;
    clear rc lc HeqQ
  end.

(*
 Two-dimensional case of [forall_nm_lt_eq]
*)
Ltac forall_nm_lt_eq :=
  let lcj := fresh in
  let rcj := fresh in
  let lci := fresh in
  let rci := fresh in
  let Q := fresh in
  let HeqQ := fresh in
  let R := fresh in
  let HeqR := fresh in
  match goal with
  | [ H1: ?i0 ≡ ?i1, H2 : ?j0 ≡ ?j1 |- ?gen ?i0 ?ic0 ?j0 ?jc0 ≡ ?gen ?i1 ?ic1 ?j1 ?jc1] =>
    generalize ic0 as lci;
    generalize ic1 as rci;
    generalize jc0 as lcj;
    generalize jc1 as rcj;
    intros rci lci rcj lcj ;
    remember i0 as Q eqn:HeqQ;
    remember j0 as R eqn:HeqR;
    rewrite H1 in HeqQ;
    rewrite H2 in HeqR;
    subst Q;
    subst R;
    replace lcj with rcj by apply le_unique;
    replace lci with rci by apply le_unique;
    reflexivity;
    clear rci lci rcj lcj HeqQ HeqR
  end.

End SpiralTactics.

End Spiral.

End Spiral_DOT_SpiralTactics.

Module Spiral_DOT_Spiral.
Module Spiral.
Module Spiral.
Import Spiral_DOT_StructTactics.
Import Spiral_DOT_SpiralTactics.
Import Spiral_DOT_SpiralTactics.Spiral.
Import Spiral_DOT_StructTactics.Spiral.
(* Base Spiral defintions: data types, utility functions, lemmas *)

Global Generalizable All Variables.
Import Coq.Arith.Arith.
Import Coq.Arith.Minus.
Import Coq.Arith.EqNat.
Import Coq.Arith.Lt.
Import Coq.Program.Program.
Import Coq.Classes.Morphisms.
Import Coq.Strings.String.
Import Coq.Logic.Decidable.
Import Spiral_DOT_SpiralTactics.Spiral.SpiralTactics.
Import Coq.micromega.Psatz.
Import Coq.omega.Omega.
Import Coq.Logic.FunctionalExtensionality.
Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders.
Import MathClasses.orders.minmax MathClasses.orders.orders MathClasses.orders.rings.
Import MathClasses.theory.abs.
Import MathClasses.theory.setoids.
Import CoLoR.Util.Nat.NatUtil.


Global Instance max_proper A `{Le A, TotalOrder A, !Setoid A} `{!∀ x y: A, Decision (x ≤ y)}:
  Proper ((=) ==> (=) ==> (=)) max.
Admitted.

Global Instance negate_proper A `{Ar: Ring A} `{!Setoid A}:
  Setoid_Morphism (negate).
Admitted.

Lemma ne_sym {T:Type} `{E: Equiv T} `{S: @Setoid T E} {a b: T}:
  (a ≠ b) <-> (b ≠ a).
Admitted.

Global Instance abs_Setoid_Morphism A
         `{Ar: Ring A}
         `{Asetoid: !Setoid A}
         `{Ato: !@TotalOrder A Ae Ale}
         `{Aabs: !@Abs A Ae Ale Azero Anegate}
  : Setoid_Morphism abs | 0.
Admitted.

Lemma abs_nonneg_s `{Aabs: Abs A}: forall (x : A), 0 ≤ x → abs x = x.
Admitted.

Lemma abs_nonpos_s `{Aabs: Abs A} (x : A): x ≤ 0 → abs x = -x.
Admitted.

Lemma abs_0_s
      `{Ae: Equiv A}
      `{Ato: !@TotalOrder A Ae Ale}
      `{Aabs: !@Abs A Ae Ale Azero Anegate}
  : abs 0 = 0.
Admitted.

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
Admitted.

Global Instance abs_idempotent
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
Admitted.

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
Admitted.


Local Open Scope nat_scope.

Lemma modulo_smaller_than_devisor:
  ∀ x y : nat, 0 ≢ y → x mod y < y.
Admitted.

Lemma ext_equiv_applied_equiv
      `{Equiv A} `{Equiv B}
      `(!Setoid_Morphism (f : A → B))
      `(!Setoid_Morphism (g : A → B)) :
  f = g ↔ ∀ x, f x = g x.
Admitted.

Lemma zero_lt_Sn:
  forall n:nat, 0<S n.
Admitted.

Lemma S_j_lt_n {n j:nat}:
  S j ≡ n -> j < n.
Admitted.

Lemma Decidable_decision
      (P:Prop):
  Decision P -> decidable P.
Admitted.

Lemma div_iff_0:
  forall m i : nat, m ≢ 0 → i/m≡0 -> m>i.
Admitted.

Lemma div_ne_0:
  ∀ m i : nat, m <= i → m ≢ 0 → i / m ≢ 0.
Admitted.

Lemma add_lt_lt
     {n m t : nat}:
  (t < m) ->  (t + n < n + m).
Admitted.

(* Similar to `Vnth_cast_aux` but arguments in equality hypotheis are swapped *)
Lemma eq_lt_lt {n m k: nat} : n ≡ m -> k < n -> k < m.
Admitted.

Lemma S_pred_simpl:
  forall n : nat, n ≢ 0 -> S (Init.Nat.pred n) ≡ n.
Admitted.


Global Instance Sig_Equiv {A:Type} {Ae : Equiv A} {P:A->Prop}:
  Equiv (@sig A P) := fun a b => (proj1_sig a) = (proj1_sig b).

Instance proj1_Proper {A:Type} {Ae : Equiv A} {P:A->Prop}:
  Proper ((=)==>(=)) (@proj1_sig A P).
Admitted.


End Spiral.

End Spiral.

End Spiral_DOT_Spiral.

Module Spiral_DOT_VecUtil.
Module Spiral.
Module VecUtil.
Import Spiral_DOT_StructTactics.
Import Spiral_DOT_SpiralTactics.
Import Spiral_DOT_Spiral.
Import Spiral_DOT_Spiral.Spiral.
Import Spiral_DOT_SpiralTactics.Spiral.
Import Spiral_DOT_StructTactics.Spiral.
Import Coq.Program.Basics.
Import Coq.Program.Equality. (* for dependent induction *)
Import Coq.omega.Omega.
Import Coq.Logic.FunctionalExtensionality.
Export Coq.Vectors.Vector.
Export CoLoR.Util.Vector.VecUtil.
Import VectorNotations.
Import Spiral_DOT_SpiralTactics.Spiral.SpiralTactics.
Import Spiral_DOT_Spiral.Spiral.Spiral.
Import Coq.micromega.Lia.

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
Admitted.

Lemma Vmap_cons: forall A B (f:A->B) n (x:A) (xs: vector A n),
    Vmap f (Vcons x xs) = Vcons (f x) (Vmap f xs).
Admitted.

Lemma Vmap_Vconst
      {n : nat}
      {A B: Type}
      {f: A -> B}
      (x : A):
  Vmap f (Vconst x n) = Vconst (f x) n.
Admitted.

Lemma VMapp2_app:
  forall {A B} {f: A->A->B} (n m : nat)
    {a b: vector A m} {a' b':vector A n},
    Vmap2 f (Vapp a a') (Vapp b b')
    = Vapp (Vmap2 f a b) (Vmap2 f a' b').
Admitted.

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
Admitted.

Section VFold.
  (* Right fold with vector argument last, so it is easier to use in point-free notation, for example in Vmap *)
  Definition Vfold_right_aux {A B:Type} {n} (f:A->B->B) (initial:B) (v: vector A n): B := @Vfold_right A B f n v initial.

  Lemma Vfold_right_cons: forall A B n (f:A->B->B) (id:B) (h:A) (v:vector A n),
      Vfold_right f (Vcons h v) id = f h (Vfold_right f v id).
Admitted.

  Lemma Vfold_right_reduce: forall A B n (f:A->B->B) (id:B) (v:vector A (S n)),
      Vfold_right f v id = f (hd v) (Vfold_right f (tl v) id).
Admitted.

  (* It directly follows from definition, but haiving it as sepearate lemma helps to do rewiring *)
  Lemma Vfold_left_rev_cons:
    forall A B {n} (f : B->A->B) (b:B) (x: A) (xs : vector A n),
      Vfold_left_rev f b (Vcons x xs) = f (Vfold_left_rev f b xs) x.
Admitted.

  Lemma Vfold_right_Vmap
        {A B C: Type}
        {n: nat}
        (f : A->B->B)
        (g : C->A)
        (x : vector C n)
        (z:B)
    : Vfold_right f (Vmap g x) z = Vfold_right (f∘g) x z.
Admitted.

End VFold.

Section VBreak.
  Lemma Vbreak_arg_app:
    forall {B} (m n : nat) (x : vector B (m + n)) (a: vector B m) (b: vector B n),
      Vbreak x = (a, b) -> x = Vapp a b.
Admitted.

  Lemma Vbreak_preserves_values {A} {n1 n2} {x: vector A (n1+n2)} {x0 x1}:
    Vbreak x = (x0, x1) ->
    forall a, Vin a x <-> ((Vin a x0) \/ (Vin a x1)).
Admitted.

  Lemma Vbreak_preserves_P {A} {n1 n2} {x: vector A (n1+n2)} {x0 x1} {P}:
    Vbreak x = (x0, x1) ->
    (Vforall P x -> ((Vforall P x0) /\ (Vforall P x1))).
Admitted.

  Lemma Vnth_fst_Vbreak
        {A:Type}
        (m n : nat)
        (v : vector A (m + n))
        (j : nat) (jc : j < m)
        (jc1 : j < m + n):
    Vnth (fst (Vbreak v)) jc = Vnth v jc1.
Admitted.

  Lemma Vnth_snd_Vbreak
        {A: Type}
        (m n : nat)
        (v : vector A (m + n)) (j : nat)
        (jc : j < n)
        (jc2 : j + m < m + n):
    Vnth (snd (Vbreak v)) jc = Vnth v jc2.
Admitted.

End VBreak.

Lemma vec_eq_elementwise n B (v1 v2: vector B n):
  Vforall2 eq v1 v2 -> (v1 = v2).
Admitted.

Lemma Vmap_Vbuild n B C (fm: B->C) (fb : forall i : nat, i < n -> B):
  Vmap fm (Vbuild fb) = Vbuild (fun z zi => fm (fb z zi)).
Admitted.

Lemma Vexists_Vbuild:
  forall (T:Type) (P: T -> Prop) (n:nat) {f},
    Vexists P (Vbuild (n:=n) f) <-> exists i (ic:i<n), P (f i ic).
Admitted.

Lemma Vbuild_0:
  forall B gen, @Vbuild B 0 gen = @Vnil B.
Admitted.

Lemma Vbuild_1 B gen:
  @Vbuild B 1 gen = [gen 0 (lt_0_Sn 0)].
Admitted.

Fact lt_0_SSn:  forall n:nat, 0<S (S n). Admitted.
Fact lt_1_SSn:  forall n:nat, 1<S (S n). Admitted.

Lemma Vbuild_2 B gen:
  @Vbuild B 2 gen = [gen 0 (lt_0_SSn 0) ; gen 1 (lt_1_SSn 0)].
Admitted.


Definition Vin_aux {A} {n} (v : vector A n) (x : A) : Prop := Vin x v.

Section Vnth.

  Lemma Vnth_arg_eq:
    forall (A : Type) (n : nat) (v1 v2 : vector A n)
      (i : nat) (ip : i < n), v1 = v2 -> Vnth v1 ip = Vnth v2 ip.
Admitted.

  (* Convenience method, swapping arguments on Vnth *)
  Definition Vnth_aux {A:Type} {n i:nat} (ic:i<n) (a: vector A n) :=
    Vnth a ic.

End Vnth.

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

Section Vunique.
  Local Open Scope nat_scope.

  (* There is at most one element in vector satisfying given predicate *)
  Definition Vunique
             {n} {T:Type}
             (P: T -> Prop)
             (v: vector T n) :=

    (forall (i: nat) (ic: i < n) (j: nat) (jc: j < n),
        (P (Vnth v ic) /\ P (Vnth v jc)) -> i = j).

  Definition VAllButOne
             {n} {T:Type}
             i (ic:i<n)
             (P: T -> Prop)
             (x: vector T n)
    :=
      (forall j (jc:j<n), ~(i = j) -> P (Vnth x jc)).

End Vunique.

Section VectorPairs.

  Definition Ptail {A} {B} {n} (ab:(vector A (S n))*(vector B (S n))): (vector A n)*(vector B n)
    := match ab with
       | (va,vb) => ((Vtail va), (Vtail vb))
       end.

End VectorPairs.

Section VMap2_Indexed.

  Definition Vmap2Indexed {A B C : Type} {n}
             (f: nat->A->B->C) (a: vector A n) (b: vector B n)
    := Vbuild (fun i ip => f i (Vnth a ip) (Vnth b ip)).

End VMap2_Indexed.


Definition Lst {B:Type} (x:B) := [x].

Lemma Vforall_Vconst
      {A: Type}
      {n: nat}
      {z: A}
      {P: A->Prop}:
  P z -> Vforall P (Vconst z n).
Admitted.

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
Admitted.


(* --- Some tactics --- *)


(* Given a [Vnth x i0 ic0 = Vnth y i1 ic0] and a hypotheis [i0=i1] reduces goal to [x=y].
TODO: See if could be generalized to [forall_n_lt_eq] *)
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

End VecUtil.

End Spiral.

End Spiral_DOT_VecUtil.

Module Spiral_DOT_VecSetoid.
Module Spiral.
Module VecSetoid.
Import Spiral_DOT_StructTactics.
Import Spiral_DOT_SpiralTactics.
Import Spiral_DOT_Spiral.
Import Spiral_DOT_VecUtil.
Import Spiral_DOT_VecUtil.Spiral.
Import Spiral_DOT_Spiral.Spiral.
Import Spiral_DOT_SpiralTactics.Spiral.
Import Spiral_DOT_StructTactics.Spiral.
Import Spiral_DOT_VecUtil.Spiral.VecUtil.
Import Coq.Arith.Arith.
Import Coq.Program.Basics. (* for \circ notation *)
Export Coq.Vectors.Vector.
Import Coq.omega.Omega.

(* CoRN MathClasses *)
Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders.
Import MathClasses.orders.minmax MathClasses.orders.orders MathClasses.orders.rings.
Import MathClasses.theory.rings MathClasses.theory.abs.
Import MathClasses.theory.naturals.


(* CoLoR *)
Export CoLoR.Util.Vector.VecUtil.
Import VectorNotations.
Import Spiral_DOT_SpiralTactics.Spiral.SpiralTactics.


(* Various definitions related to vector equality and setoid rewriting *)

Section VectorSetoid.

  Global Instance vec_Equiv `{Equiv A} {n}: Equiv (vector A n)
    := Vforall2 (n:=n) equiv.

  Global Instance vec_Equivalence `{Ae: Equiv A} {n:nat}
         `{!Equivalence (@equiv A _)}
    : Equivalence (@vec_Equiv A Ae n).
Admitted.

  Global Instance vec_Setoid `{Setoid A} {n}: Setoid (vector A n).
Admitted.

End VectorSetoid.


Section Vconst.
  Context
    `{eqA: Equiv A}.

  Definition Vconst_reord {n} (x:A): vector A n :=
    Vconst x n.

  Lemma Vconst_to_Vconst_reord {n} (x:A):
    Vconst x n ≡ @Vconst_reord n x.
Admitted.

  Global Instance Vconst_reord_proper {n}:
    Proper ((=)==>(=)) (@Vconst_reord n).
Admitted.

End Vconst.



(* TODO: check if needed for Coq-8.6 *)
Section Vfold_left.
  Context
    `{eqA: Equiv A}
    `{eqB: Equiv B}.

  Definition Vfold_left_reord {A B:Type} {n} (f:A->B->A) (initial:A) (v: vector B n): A := @Vfold_left A B f n initial v.

  Lemma Vfold_left_to_Vfold_left_reord: forall {A B:Type} {n} (f:A->B->A) (v: vector B n) (initial:A),
      Vfold_left f initial v ≡ Vfold_left_reord f initial v.
Admitted.

  Global Instance Vfold_left_reord_proper n :
    Proper (((=) ==> (=) ==> (=)) ==> ((=) ==> (=) ==> (=)))
           (@Vfold_left_reord A B n).
Admitted.

End Vfold_left.

(* TODO: check if needed for Coq-8.6 *)
Section Vfold_left_rev.
  Context
    `{eqA: Equiv A}
    `{eqB: Equiv B}.

  Definition Vfold_left_rev_reord {A B:Type} {n} (f:A->B->A) (initial:A) (v: vector B n): A := @Vfold_left_rev A B f n initial v.

  Lemma Vfold_left_rev_to_Vfold_left_rev_reord: forall {A B:Type} {n} (f:A->B->A) (v: vector B n) (initial:A),
      Vfold_left_rev f initial v ≡ Vfold_left_rev_reord f initial v.
Admitted.

  Global Instance Vfold_left_rev_reord_proper n :
    Proper (((=) ==> (=) ==> (=)) ==> ((=) ==> (=) ==> (=)))
           (@Vfold_left_rev_reord A B n).
Admitted.

End Vfold_left_rev.

(* TODO: check if needed for Coq-8.6 *)
Section Vfold_right.
  Context
    `{eqA: Equiv A}
    `{eqB: Equiv B}.

  Definition Vfold_right_reord {A B:Type} {n} (f:A->B->B) (v: vector A n) (initial:B): B := @Vfold_right A B f n v initial.

  Lemma Vfold_right_to_Vfold_right_reord: forall {A B:Type} {n} (f:A->B->B) (v: vector A n) (initial:B),
      Vfold_right f v initial ≡ Vfold_right_reord f v initial.
Admitted.

  Global Instance Vfold_right_reord_proper n :
    Proper (((=) ==> (=) ==> (=)) ==> ((=) ==> (=) ==> (=)))
           (@Vfold_right_reord A B n).
Admitted.

  Global Instance Vfold_right_aux_proper n :
    Proper (((=) ==> (=) ==> (=)) ==> (=) ==> (=) ==> (=))
           (@Vfold_right_aux A B n).
Admitted.

End Vfold_right.

(* TODO: check if needed for Coq-8.6 *)
Section VCons.

  Definition Vcons_reord {A} {n} (t: vector A n) (h:A): vector A (S n) := Vcons h t.

  Lemma Vcons_to_Vcons_reord: forall A n (t: t A n) (h:A), Vcons h t  ≡ Vcons_reord t h.
Admitted.

  Global Instance Vcons_reord_proper `{Equiv A} n:
    Proper ((=) ==> (=) ==> (=))
           (@Vcons_reord A n).
Admitted.

End VCons.

Global Instance Vapp_proper `{Sa: Setoid A} (n1 n2:nat):
  Proper ((=) ==>  (=) ==> (=)) (@Vapp A n1 n2).
Admitted.

Global Instance Vhead_proper `{Equiv A} n:
  Proper ((=) ==> (=)) (@Vhead A n).
Admitted.

Global Instance Vtail_proper `{Equiv A} n:
  Proper ((=) ==> (=)) (@Vtail A n).
Admitted.

Global Instance Ptail_proper `{Sa: Setoid A} `{Sb: Setoid B} (n:nat):
  Proper ((=) ==> (=)) (@Ptail A B n).
Admitted.

(* Handy tactics to break down equality of two vectors into element-wise equality of theirm elements using index *)
Ltac vec_index_equiv j jc :=
  let j' := fresh j in
  let jc' := fresh jc in
  unfold equiv, vec_Equiv; apply Vforall2_intro_nth; intros j' jc'.

Lemma Vfold_right_Vmap_equiv
      {A B C: Type}
      `{Setoid B}
      {n: nat}
      (f : A->B->B)
      (g : C->A)
      (x : vector C n)
      (z:B)
  : Vfold_right f (Vmap g x) z = Vfold_right (f∘g) x z.
Admitted.

Lemma Vmap_as_Vbuild {A B:Type} `{Equiv A} `{Setoid B}:
  ∀ (n : nat) (v : vector A n) (f:A->B),
    Vmap f v = Vbuild (λ (j : nat) (jd : (j < n)%nat), f (Vnth v jd)).
Admitted.

Lemma Vmap2_cons_hd: forall A B C `{Setoid C} (f:A->B->C) n (a:vector A (S n)) (b:vector B (S n)),
    Vmap2 f a b = Vcons (f (Vhead a) (Vhead b)) (Vmap2 f (Vtail a) (Vtail b)).
Admitted.

Lemma Vmap2_cons: forall A B C `{Setoid C} (f:A->B->C) n (a:A) (b:B) (a':vector A n) (b':vector B n),
    Vmap2 f (Vcons a a') (Vcons b b') = Vcons (f a b) (Vmap2 f a' b').
Admitted.

Lemma Vmap2_comm
      `{CO:Commutative B A f}
      `{SB: !Setoid B} {n:nat}:
  Commutative (Vmap2 f (n:=n)).
Admitted.

Lemma hd_equiv: forall `{Setoid A} {n} (u v: vector A (S n)), u=v -> (Vhead u) = (Vhead v).
Admitted.

Lemma Vcons_equiv_elim `{Equiv A}: forall a1 a2 n (v1 v2 : vector A n),
    Vcons a1 v1 = Vcons a2 v2 -> a1 = a2 /\ v1 = v2.
Admitted.

Lemma Vcons_equiv_intro `{Setoid A} : forall a1 a2 n (v1 v2 : vector A n),
    a1 = a2 -> v1 = v2 -> Vcons a1 v1 = Vcons a2 v2.
Admitted.

Lemma Vcons_single_elim `{Equiv A} : forall a1 a2,
    Vcons a1 (@Vnil A) = Vcons a2 (@Vnil A) <-> a1 = a2.
Admitted.

(* TODO: Check if it is still needed in Coq-8.6 *)
Section VMap_reord.

  (*
   The following Proper for dependent-typed Vmap does not work.
   As workaround we reorder parameters and define simple typed
   version of [Vmap_reord] for given [A,B,n].

   This general technique was first suggested to us in coq-club mailing
   list by Daniel Schepler <dschepler@gmail.com> in 11/2014

Global Instance Vmap_proper {A B:Type} `{Ae: Setoid A} `{Be: Setoid B}:
  Proper (
      ((=) ==> (=)) ==> (forall_relation
                       (fun (n : nat) => (@vec_Equiv A _ n) ==> (@vec_Equiv B _ n))))
         (@Vmap A B).
*)

  Definition Vmap_reord (A B: Type) (n:nat) (f:A->B) (x: vector A n): vector B n := Vmap f x.

  Lemma Vmap_to_Vmap_reord: forall (A B: Type) (n:nat) (f:A->B) (x: vector A n), @Vmap A B f n x ≡ @Vmap_reord A B n f x.
Admitted.


  Global Instance Vmap_reord_proper n (M N:Type) `{Ne:!Equiv N, Me:!Equiv M}:
    Proper (((=) ==> (=)) ==> (=) ==> (=))
           (@Vmap_reord M N n).
Admitted.


  Global Instance Vmap_arg_proper  (M N:Type) `{Me:!Equiv M} `{Ne: !Equiv N} (f : M->N)
         `{fP: !Proper (Me ==> Ne) f} (n:nat):
    Proper ((@vec_Equiv M _ n) ==> (@vec_Equiv N _ n)) (@Vmap M N f n).
Admitted.

End VMap_reord.


Global Instance VBreak_proper (A:Type) `{Setoid A} (n1 n2:nat) `{Plus nat}:
  Proper ((=) ==> (=)) (@Vbreak A n1 n2).
Admitted.

Section Vnth.

  Lemma Vnth_arg_equiv:
    ∀ (A : Type) (Ae : Equiv A) (n : nat) (v1 v2 : vector A n)
      (i : nat) (ip : i < n), v1 = v2 → Vnth v1 ip = Vnth v2 ip.
Admitted.

  Lemma Vnth_equiv `{Setoid A}: forall n (v1 v2 : vector A n) i1 (h1 : i1<n) i2 (h2 : i2<n),
      i1 = i2 -> v1 = v2 -> Vnth v1 h1 = Vnth v2 h2.
Admitted.

  (* We should have Global Instance Vnth_proper, but it is a bit tricky to define for i<n term, so I will leave it for later *)

End Vnth.

Global Instance Vmap2Indexed_proper
       `{Setoid A, Setoid B, Setoid C} {n:nat}
  :
    Proper (((=) ==> (=) ==> (=) ==> (=)) ==> (=) ==> (=) ==> (=))
           (@Vmap2Indexed A B C n).
Admitted.

Global Instance indexed_vector_equiv `{Equiv A} {n}:
  Equiv (∀ i : nat, i < n → vector A n)
  :=  @forall_relation nat
                       (fun i : nat =>  forall _ : i<n, vector A n)
                       (fun i : nat =>  @pointwise_relation (i < n)
                                                       (vector A n) (=)).

(* @jwiegley version *)
Global Instance Vbuild_proper {n : nat} {A:Type} `{Equiv A}:
  Proper ((forall_relation
             (fun i => pointwise_relation (i < n)%nat equiv)) ==> equiv)
         (@Vbuild A n).
Admitted.

(* --- Tactics --- *)

Ltac vec_to_vec_reord := repeat match goal with
                                | [ |- context [Vfold_right]] => setoid_rewrite Vfold_right_to_Vfold_right_reord
                                | [ |- context [Vfold_left]] => setoid_rewrite Vfold_left_to_Vfold_left_reord
                                | [ |- context [Vfold_left_rev]] => setoid_rewrite Vfold_left_rev_to_Vfold_left_rev_reord
                                | [ |- context [Vconst]] => setoid_rewrite Vconst_to_Vconst_reord
                                | [ |- context [Vmap]] => setoid_rewrite Vmap_to_Vmap_reord
                                end.


End VecSetoid.

End Spiral.

End Spiral_DOT_VecSetoid.

Module Spiral_DOT_CarrierType.
Module Spiral.
Module CarrierType.
Import Spiral_DOT_StructTactics.
Import Spiral_DOT_SpiralTactics.
Import Spiral_DOT_Spiral.
Import Spiral_DOT_VecUtil.
Import Spiral_DOT_VecSetoid.
Import Spiral_DOT_VecSetoid.Spiral.
Import Spiral_DOT_VecUtil.Spiral.
Import Spiral_DOT_Spiral.Spiral.
Import Spiral_DOT_SpiralTactics.Spiral.
Import Spiral_DOT_StructTactics.Spiral.
(*
Carrier type used in all our proofs. Could be real of Float in future.
 *)
Import CoLoR.Util.Vector.VecUtil.
Import MathClasses.interfaces.abstract_algebra.
Import MathClasses.theory.rings.
Import MathClasses.interfaces.orders.

Parameter CarrierA: Type.
Parameter CarrierAe: Equiv CarrierA.
Parameter CarrierAsetoid: @Setoid CarrierA CarrierAe.
Parameter CarrierAz: Zero CarrierA.
Parameter CarrierA1: One CarrierA.
Parameter CarrierAplus: Plus CarrierA.
Parameter CarrierAmult: Mult CarrierA.
Parameter CarrierAneg: Negate CarrierA.
Parameter CarrierAle: Le CarrierA.
Parameter CarrierAlt: Lt CarrierA.
Parameter CarrierAto: @TotalOrder CarrierA CarrierAe CarrierAle.
Parameter CarrierAabs: @Abs CarrierA CarrierAe CarrierAle CarrierAz CarrierAneg.
Parameter CarrierAr: Ring CarrierA.
Parameter CarrierAltdec: ∀ x y: CarrierA, Decision (x < y).
Parameter CarrierAledec: ∀ x y: CarrierA, Decision (x ≤ y).
Parameter CarrierAequivdec: ∀ x y: CarrierA, Decision (x = y).
Parameter CarrierASSO: @StrictSetoidOrder CarrierA CarrierAe CarrierAlt.
Parameter CarrierASRO: @SemiRingOrder CarrierA CarrierAe CarrierAplus CarrierAmult CarrierAz CarrierA1 CarrierAle.

Add Ring RingA: (stdlib_ring_theory CarrierA).

Global Instance CarrierAPlus_proper:
  Proper ((=) ==> (=) ==> (=)) (plus).
Admitted.

Global Instance CommutativeMonoid_plus_zero:
  @MathClasses.interfaces.abstract_algebra.CommutativeMonoid CarrierA _ plus zero.
Admitted.

Notation avector n := (vector CarrierA n) (only parsing).

Ltac decide_CarrierA_equality E NE :=
  let E' := fresh E in
  let NE' := fresh NE in
  match goal with
  | [ |- @equiv CarrierA CarrierAe ?A ?B ] => destruct (CarrierAequivdec A B) as [E'|NE']
  end.



End CarrierType.

End Spiral.

End Spiral_DOT_CarrierType.

Module Spiral_DOT_WriterMonadNoT.
Module Spiral.
Module WriterMonadNoT.
Import Spiral_DOT_StructTactics.
Import Spiral_DOT_SpiralTactics.
Import Spiral_DOT_Spiral.
Import Spiral_DOT_VecUtil.
Import Spiral_DOT_VecSetoid.
Import Spiral_DOT_CarrierType.
Import Spiral_DOT_CarrierType.Spiral.
Import Spiral_DOT_VecSetoid.Spiral.
Import Spiral_DOT_VecUtil.Spiral.
Import Spiral_DOT_Spiral.Spiral.
Import Spiral_DOT_SpiralTactics.Spiral.
Import Spiral_DOT_StructTactics.Spiral.
Import Coq.Program.Basics. (* for (∘) *)
Import ExtLib.Data.Monads.IdentityMonad.
Import ExtLib.Data.Monads.WriterMonad.
Import ExtLib.Structures.Monoid.
Import ExtLib.Data.PPair.

Set Implicit Arguments.
Set Universe Polymorphism.

Section MapWriterT.
  Variable A B: Type.
  Variable W W': Type.
  Variable Monoid_W : Monoid W.
  Variable Monoid_W' : Monoid W'.
  Variable m n : Type -> Type.

  Open Scope program_scope.

  (** Map both the return value and output of a computation using the given function.
        [[ 'runWriterT' ('mapWriterT' f m) = f ('runWriterT' m) ]]
   *)
  Definition mapWriterT (f: (m (pprod A W)%type) -> (n (pprod B W')%type)):
    (writerT Monoid_W m A) -> writerT Monoid_W' n B
    :=
      mkWriterT Monoid_W' ∘ f ∘ runWriterT.

End MapWriterT.


Section CastWriterT.
  Variable A: Type.
  Variable W : Type.
  Variable Monoid_W Monoid_W': Monoid W.
  Variable m : Type -> Type.

  Open Scope program_scope.

  (* Special case of mapWriterT where mapping functoin is identity *)
  Definition castWriterT:
    writerT Monoid_W m A -> writerT Monoid_W' m A
    := mkWriterT Monoid_W' ∘ runWriterT.

End CastWriterT.


(** Simple wrapper around ExtLib's WriterMonadT trasformed pairing it with Identity monad to simulate classic Writer Monad *)
Section WriterMonad.

  Variable W: Type.
  Variable A: Type.
  Variable Monoid_W : Monoid W.

  Open Scope program_scope.

  Definition writer := writerT Monoid_W ident.
  Definition runWriter := unIdent ∘ (@runWriterT W Monoid_W ident A).
  Definition execWriter:= psnd ∘ runWriter.
  Definition evalWriter:= pfst ∘ runWriter.

End WriterMonad.

Section CastWriter.
  Variable A: Type.
  Variable W : Type.
  Variable Monoid_W Monoid_W': Monoid W.

  Open Scope program_scope.

  (* Special case of mapWriter where mapping functoin is identity *)
  Definition castWriter: writer Monoid_W A -> writer Monoid_W' A
    := castWriterT Monoid_W' (m:=ident).

End CastWriter.

End WriterMonadNoT.

End Spiral.

End Spiral_DOT_WriterMonadNoT.

Module Spiral_DOT_Rtheta.
Module Spiral.
Module Rtheta.
Import Spiral_DOT_StructTactics.
Import Spiral_DOT_SpiralTactics.
Import Spiral_DOT_Spiral.
Import Spiral_DOT_VecUtil.
Import Spiral_DOT_VecSetoid.
Import Spiral_DOT_CarrierType.
Import Spiral_DOT_WriterMonadNoT.
Import Spiral_DOT_WriterMonadNoT.Spiral.
Import Spiral_DOT_CarrierType.Spiral.
Import Spiral_DOT_VecSetoid.Spiral.
Import Spiral_DOT_VecUtil.Spiral.
Import Spiral_DOT_Spiral.Spiral.
Import Spiral_DOT_SpiralTactics.Spiral.
Import Spiral_DOT_StructTactics.Spiral.
(* R_theta is type which is used as value for vectors in SPIRAL.  *)
Export Spiral_DOT_CarrierType.Spiral.CarrierType.
Import Coq.Bool.Bool.
Import Coq.setoid_ring.Ring.
Import ExtLib.Core.Type.
Import ExtLib.Structures.Monads.
Import ExtLib.Structures.MonadLaws.
Import ExtLib.Data.Monads.WriterMonad.
Import ExtLib.Data.Monads.IdentityMonad.
Import ExtLib.Structures.Monoid.
Import Spiral_DOT_WriterMonadNoT.Spiral.WriterMonadNoT.
Import ExtLib.Data.PPair.

(* CoRN MathClasses *)
Import MathClasses.interfaces.abstract_algebra.
Import MathClasses.theory.rings.
Import Spiral_DOT_SpiralTactics.Spiral.SpiralTactics.


Import MonadNotation.
Import Monoid.
Local Open Scope monad_scope.


(* Both safe and collision tracking flags monads share same underlying data structure *)

Record RthetaFlags : Type :=
  mkRthetaFlags
    {
      is_struct: bool ;
      is_collision: bool
    }.

(* Propositional predicates *)
Definition IsCollision (x:RthetaFlags) := Is_true (is_collision x).
Definition IsVal (x:RthetaFlags) := not (Is_true (is_struct x)).

Global Instance RthetaFlags_equiv:
  Equiv RthetaFlags :=
  fun a b =>
    is_collision a ≡ is_collision b /\
    is_struct a ≡ is_struct b.

Global Instance RthetaFlags_Reflexive_equiv: Reflexive RthetaFlags_equiv.
Admitted.

Global Instance RthetaFlags_Symmetric_equiv: Symmetric RthetaFlags_equiv.
Admitted.

Global Instance RthetaFlags_Transitive_equiv: Transitive RthetaFlags_equiv.
Admitted.

Global Instance RthetaFlags_Equivalence_equiv: Equivalence RthetaFlags_equiv.
Admitted.

Global Instance RthetaFlags_Setoid: @Setoid RthetaFlags RthetaFlags_equiv.
Admitted.

(* mzero *)
Definition RthetaFlagsZero := mkRthetaFlags true false.

Global Instance RthetaFlags_type:
  type RthetaFlags := type_libniz RthetaFlags.

Section CollisionTrackingRthetaFlags.
  (* mappend which tracks collisions *)
  Definition RthetaFlagsAppend (a b: RthetaFlags) : RthetaFlags :=
    mkRthetaFlags
      (is_struct a && is_struct b)
      (is_collision a || (is_collision b ||
                         (negb (is_struct a || is_struct b)))).

  Definition Monoid_RthetaFlags : Monoid RthetaFlags := Build_Monoid RthetaFlagsAppend RthetaFlagsZero.


  (* Monoid is just a record and equivalence is established pointwise on fields *)
  Global Instance Monoid_equiv `{Equiv f}:
    Equiv (Monoid f) :=
    fun a b =>
      (monoid_plus a = monoid_plus b) /\
      (monoid_unit a = monoid_unit b).

  Lemma RthetaFlags_assoc:
    ∀ a b c : RthetaFlags,
      RthetaFlagsAppend (RthetaFlagsAppend a b) c
                        ≡ RthetaFlagsAppend a (RthetaFlagsAppend b c).
Admitted.

  Lemma RthetaFlags_lunit:
    ∀ a : RthetaFlags, RthetaFlagsAppend RthetaFlagsZero a ≡ a.
Admitted.

  Lemma RthetaFlags_runit:
    ∀ a : RthetaFlags, RthetaFlagsAppend a RthetaFlagsZero ≡ a.
Admitted.

  Global Instance MonoidLaws_RthetaFlags:
    MonoidLaws Monoid_RthetaFlags.
Admitted.
End CollisionTrackingRthetaFlags.

Section SafeRthetaFlags.

  (* mappend which does not track collisions *)
  Definition RthetaFlagsSafeAppend (a b: RthetaFlags) : RthetaFlags :=
    mkRthetaFlags
      (andb (is_struct a) (is_struct b))
      (orb (is_collision a) (is_collision b)).

  Definition Monoid_RthetaSafeFlags : Monoid RthetaFlags := ExtLib.Structures.Monoid.Build_Monoid RthetaFlagsSafeAppend RthetaFlagsZero.

  Lemma RthetaFlags_safe_assoc:
    ∀ a b c : RthetaFlags,
      RthetaFlagsSafeAppend (RthetaFlagsSafeAppend a b) c
                            ≡ RthetaFlagsSafeAppend a (RthetaFlagsSafeAppend b c).
Admitted.

  Lemma RthetaFlags_safe_lunit:
    ∀ a : RthetaFlags, RthetaFlagsSafeAppend RthetaFlagsZero a ≡ a.
Admitted.

  Lemma RthetaFlags_safe_runit:
    ∀ a : RthetaFlags, RthetaFlagsSafeAppend a RthetaFlagsZero ≡ a.
Admitted.

  Global Instance MonoidLaws_SafeRthetaFlags:
    MonoidLaws Monoid_RthetaSafeFlags.
Admitted.

End SafeRthetaFlags.

Section RMonad.
  Variable fm:Monoid RthetaFlags.
  (* Monad_RthetaFlags is just a Writer Monad for RthetaFlags *)
  Definition Monad_RthetaFlags := writer fm.

  (* Generic Rtheta type is parametrized by Monoid, which defines how structural flags are handled. *)
  Definition Rtheta' := Monad_RthetaFlags CarrierA.
End RMonad.

Definition Rtheta := Rtheta' Monoid_RthetaFlags.
Definition RStheta := Rtheta' Monoid_RthetaSafeFlags.

(* Monad morhisms *)

Definition Rtheta2RStheta: Rtheta -> RStheta := castWriter Monoid_RthetaSafeFlags.

Definition RStheta2Rtheta: RStheta -> Rtheta := castWriter Monoid_RthetaFlags.

(* Some convenience constructros *)

Section Rtheta'Utils.
  Context {fm:Monoid RthetaFlags}.

  Definition mkStruct (val: CarrierA) : Rtheta' fm
    := ret val.
  (* Structural zero is 0 value combined with 'mzero' monoid flags *)
  Definition mkSZero : Rtheta' fm := mkStruct 0.

  Definition mkValue (val: CarrierA) : Rtheta' fm :=
    tell (mkRthetaFlags false false) ;; ret val.

  Definition Is_Val: (Rtheta' fm) -> Prop :=
    IsVal ∘ (@execWriter RthetaFlags CarrierA fm).

  Definition Is_Struct:= not ∘ Is_Val.

  Definition Is_Collision (x:Rtheta' fm) :=
    (IsCollision ∘ (@execWriter RthetaFlags CarrierA fm)) x.

  Definition Not_Collision := not ∘ Is_Collision.

  Definition liftRthetaP (P: CarrierA -> Prop): (Rtheta' fm) -> Prop :=
    fun x => P (evalWriter x).

  Definition Is_NonNegative (x:Rtheta' fm) : Prop := liftRthetaP (le 0) x.

  Definition Is_ValX (z:CarrierA)
    := fun (x:Rtheta' fm) => (WriterMonadNoT.evalWriter x) = z.

  Lemma IsVal_mkValue {fml:@MonoidLaws RthetaFlags  RthetaFlags_type fm}
:
    ∀ (v:CarrierA), Is_Val (mkValue v).
Admitted.

  Lemma Not_Collision_mkValue {fml:@MonoidLaws RthetaFlags  RthetaFlags_type fm}:
    ∀ (v:CarrierA), Not_Collision (mkValue v).
Admitted.

  Global Instance Rtheta'_equiv: Equiv (Rtheta' fm) :=
    fun am bm => (evalWriter am) = (evalWriter bm).

  Global Instance evalWriter_proper:
    Proper ((=) ==> (=)) (@evalWriter RthetaFlags CarrierA fm).
Admitted.

  Global Instance liftRthetaP_proper
         (P: CarrierA -> Prop)
         (P_mor: Proper ((=) ==> iff) P)
    :
      Proper ((=) ==> iff) (@liftRthetaP P).
Admitted.

  Global Instance Is_ValX_proper:
      Proper ((=) ==> (=) ==> (iff)) (Is_ValX).
Admitted.

  Ltac unfold_Rtheta'_equiv := unfold equiv, Rtheta'_equiv in *.

  Global Instance Rtheta_Reflexive_equiv:
    @Reflexive (Rtheta' fm) Rtheta'_equiv.
Admitted.

  Global Instance Rtheta_Symmetric_equiv:
    @Symmetric (Rtheta' fm) Rtheta'_equiv.
Admitted.

  Global Instance Rtheta_Transitive_equiv:
    @Transitive (Rtheta' fm) Rtheta'_equiv.
Admitted.

  Global Instance Rtheta_Equivalence_equiv:
    @Equivalence (Rtheta' fm) Rtheta'_equiv.
Admitted.

  Global Instance Rtheta_Setoid:
    @Setoid (Rtheta' fm) Rtheta'_equiv.
Admitted.

  (* Note: definitional equality *)
  Lemma evalWriter_Rtheta_liftM
        (op: CarrierA -> CarrierA)
        `{a: Rtheta' fm}
    :
      evalWriter (liftM op a) ≡ op (evalWriter a).
Admitted.

  Lemma execWriter_liftM {fml:@MonoidLaws RthetaFlags  RthetaFlags_type fm}:
    ∀ (f : CarrierA → CarrierA)
      (x : Rtheta' fm),
      execWriter (Monad.liftM f x) ≡ execWriter x.
Admitted.

  Lemma Is_Val_liftM
        {fml:@MonoidLaws RthetaFlags  RthetaFlags_type fm}
        (f: CarrierA → CarrierA)
        (r : Rtheta' fm):
    Is_Val r → Is_Val (liftM f r).
Admitted.

  Lemma Not_Collision_liftM
        {fml:@MonoidLaws RthetaFlags  RthetaFlags_type fm}
        (f: CarrierA → CarrierA)
        (r : Rtheta' fm):
    Not_Collision r -> Not_Collision (liftM f r).
Admitted.

  Lemma execWriter_Rtheta_liftM2
        {fml:@MonoidLaws RthetaFlags  RthetaFlags_type fm}
        (op: CarrierA -> CarrierA -> CarrierA)
        {a b: Rtheta' fm}
    :
      execWriter (liftM2 op a b) ≡ monoid_plus fm
                 (@execWriter _ _ fm a) (@execWriter _ _ fm b).
Admitted.

  (* Note: definitional equality *)
  Lemma evalWriter_Rtheta_liftM2
        (op: CarrierA -> CarrierA -> CarrierA)
        {a b: Rtheta' fm}
    :
      evalWriter (liftM2 op a b) ≡ op (evalWriter a) (evalWriter b).
Admitted.

  (* mkValue on evalWriter on non-collision value is identity *)
  Lemma mkValue_evalWriter_VNC
        {fml:@MonoidLaws RthetaFlags  RthetaFlags_type fm}
        (r : Rtheta' fm)
    :
      Is_Val r → Not_Collision r -> mkValue (WriterMonadNoT.evalWriter r) ≡ r.
Admitted.


  (* mkValue on evalWriter equiv wrt values *)
  Lemma mkValue_evalWriter
        (r: Rtheta' fm):
    mkValue (WriterMonadNoT.evalWriter r) = r.
Admitted.

  (* mkStruct on evalWriter equiv wrt values *)
  Lemma mkStruct_evalWriter
        (r: Rtheta' fm):
    mkStruct (WriterMonadNoT.evalWriter r) = r.
Admitted.

  (* evalWriter on mkStruct equiv wrt values *)
  Lemma evalWriter_mkStruct
        (c: CarrierA):
     WriterMonadNoT.evalWriter (mkStruct c) ≡ c.
Admitted.

  Lemma evalWriter_mkValue
        (x:CarrierA):
    WriterMonadNoT.evalWriter (mkValue x) ≡ x.
Admitted.

End Rtheta'Utils.

(* For some reason class resolver could not figure this out on it's own *)
Global Instance Rtheta_equiv: Equiv (Rtheta) := Rtheta'_equiv.
Global Instance RStheta_equiv: Equiv (RStheta) := Rtheta'_equiv.

Ltac unfold_Rtheta_equiv := unfold equiv, Rtheta_equiv, Rtheta'_equiv in *.
Ltac unfold_RStheta_equiv := unfold equiv, RStheta_equiv, Rtheta'_equiv in *.

Global Instance Rtheta2RStheta_proper
  : Proper ((=) ==> (=)) (Rtheta2RStheta).
Admitted.

Global Instance RStheta2Rtheta_proper
  : Proper ((=) ==> (=)) (RStheta2Rtheta).
Admitted.

Lemma RStheta2Rtheta_liftM2
      (f : CarrierA → CarrierA → CarrierA)
      (f_mor: Proper (equiv ==> equiv ==> equiv) f)
      {a b: Rtheta}
  :
    RStheta2Rtheta (Monad.liftM2 f (Rtheta2RStheta a) (Rtheta2RStheta b)) =
    Monad.liftM2 f a b.
Admitted.

Lemma RStheta2Rtheta_Rtheta2RStheta {x}:
  RStheta2Rtheta (Rtheta2RStheta x) ≡ x.
Admitted.

Lemma RStheta2Rtheta_Rtheta2RStheta_equiv {x}:
  RStheta2Rtheta (Rtheta2RStheta x) = x.
Admitted.

Lemma Is_Val_mkStruct:
  forall a, not (@Is_Val _ (@mkStruct Monoid_RthetaFlags a)).
Admitted.

Lemma Is_Val_mkSZero:
  @Is_Val _ (@mkSZero Monoid_RthetaFlags) -> False.
Admitted.

Lemma Is_Struct_mkSZero:
  @Is_Struct _ (@mkSZero Monoid_RthetaFlags).
Admitted.

Lemma Is_Val_liftM2
      (f: CarrierA → CarrierA → CarrierA)
      (a b : Rtheta):
  Is_Val a → Is_Val b → Is_Val (liftM2 f a b).
Admitted.

Lemma Is_Val_Safe_liftM2
      (f: CarrierA → CarrierA → CarrierA)
      (a b : RStheta):
  Is_Val a → Is_Val b → Is_Val (liftM2 f a b).
Admitted.

Lemma Is_Val_RStheta2Rtheta
      {x:RStheta}:
  Is_Val x <-> Is_Val (RStheta2Rtheta x).
Admitted.

Lemma Is_Val_Rtheta2RStheta
      {x:Rtheta}:
  Is_Val x <-> Is_Val (Rtheta2RStheta x).
Admitted.

Lemma Is_Struct_RStheta2Rtheta
      {x:RStheta}:
  Is_Struct x <-> Is_Struct (RStheta2Rtheta x).
Admitted.

Lemma Is_Struct_Rtheta2RStheta
      {x:Rtheta}:
  Is_Struct x <-> Is_Struct (Rtheta2RStheta x).
Admitted.

Lemma Not_Collision_RStheta2Rtheta
      {x:RStheta}:
  Not_Collision x <-> Not_Collision (RStheta2Rtheta x).
Admitted.

Lemma Not_Collision_Rtheta2RStheta
      {x:Rtheta}:
  Not_Collision x <-> Not_Collision (Rtheta2RStheta x).
Admitted.


Lemma Not_Collision_liftM2
      (f: CarrierA → CarrierA → CarrierA)
      (a b : Rtheta):
  Not_Collision a → Not_Collision b →
  (Is_Struct a \/ Is_Struct b) ->
  Not_Collision (liftM2 f a b).
Admitted.

Lemma Not_Collision_Safe_liftM2
      (f: CarrierA → CarrierA → CarrierA)
      (a b : RStheta):
  Not_Collision a → Not_Collision b →
  Not_Collision (liftM2 f a b).
Admitted.

Lemma Not_Collision_Safe_mkStruct:
  ∀ (v:CarrierA), @Not_Collision Monoid_RthetaSafeFlags (mkStruct v).
Admitted.

Lemma evalWriter_Rtheta2RStheta_mkValue
      {x}:
  (WriterMonadNoT.evalWriter (Rtheta2RStheta (mkValue x))) ≡ x.
Admitted.

Lemma evalWriter_Rtheta2RStheta_mkValue_equiv {x}:
  (WriterMonadNoT.evalWriter (Rtheta2RStheta (mkValue x))) = x.
Admitted.

Section Decidablitiy.
  Global Instance IsVal_dec (x: RthetaFlags) : Decision (IsVal x).
Admitted.

  Global Instance Is_Val_dec
         {fm:Monoid RthetaFlags}
         (x: Rtheta' fm):
    Decision (Is_Val x).
Admitted.

End Decidablitiy.

Section Zero_Utils.

  Lemma evalWriter_Rtheta_SZero
        (fm:Monoid RthetaFlags)
  :
    @evalWriter _ _ fm (@mkSZero fm) ≡ zero.
Admitted.

  Global Instance mkValue_proper
         {fm:Monoid RthetaFlags}
    :
      Proper((=) ==> (=)) (@mkValue fm).
Admitted.

  Global Instance mkStruct_proper
         {fm:Monoid RthetaFlags}
    :
      Proper((=) ==> (=)) (@mkStruct fm).
Admitted.

  Definition Is_ValZero {fm:Monoid RthetaFlags}
    := @Is_ValX fm 0.

  Global Instance Is_ValZero_dec {fm:Monoid RthetaFlags} (x:Rtheta' fm):
    Decision (Is_ValZero x).
Admitted.

  Global Instance Is_ValZero_proper
         {fm:Monoid RthetaFlags}
    :
      Proper ((=) ==> (iff)) (@Is_ValZero fm).
Admitted.

  Lemma Is_ValZero_to_mkSZero
        {fm:Monoid RthetaFlags}
        (x:Rtheta' fm):
    (Is_ValZero x) <-> (x = mkSZero).
Admitted.

  Lemma SZero_is_ValZero
        {fm:Monoid RthetaFlags}:
    @Is_ValZero fm mkSZero.
Admitted.

  Lemma Is_ValX_mkStruct
        {fm:Monoid RthetaFlags}:
    forall x,
      @Is_ValX fm x (mkStruct x).
Admitted.

  (* Using setoid equalities on both components *)
  Definition Is_SZero
             {fm:Monoid RthetaFlags}
             (x:Rtheta' fm)
    :=
      (evalWriter x = zero) /\
      (execWriter x = RthetaFlagsZero).

  Lemma Is_SZero_mkSZero:
    @Is_SZero Monoid_RthetaFlags mkSZero.
Admitted.

  Lemma Is_ValX_not_not
        {fm:Monoid RthetaFlags}
        `{uf_zero: MonUnit CarrierA}:
    not ∘ (not ∘ (@Is_ValX fm uf_zero)) = Is_ValX uf_zero.
Admitted.

  (* TODO: See if we need this *)
  Lemma Is_ValX_not_not'
        {fm:Monoid RthetaFlags}
        `{uf_zero: MonUnit CarrierA}:
    (not ∘ (not ∘ equiv uf_zero ∘ WriterMonadNoT.evalWriter (Monoid_W:=fm))) = Is_ValX uf_zero.
Admitted.


  (* Double negation on inValZero. Follows from decidability on CarrierA and Propernes of evalWriter. TODO: Very similar to [Is_ValX_not_not] *)
  Lemma Is_ValZero_not_not
        {fm:Monoid RthetaFlags}
    :
      ((not ∘ (not ∘ @Is_ValZero fm)) = Is_ValZero).
Admitted.


  (* Double negation on inValZero. *)
  Lemma not_not_on_decidable
        {A:Type}
        {P: A->Prop}
        `{forall x:A, Decision (P x)}
    :
      forall x, (not ∘ (not ∘ P)) x <-> P x.
Admitted.

End Zero_Utils.


End Rtheta.

End Spiral.

End Spiral_DOT_Rtheta.

Module Spiral_DOT_SVector.
Module Spiral.
Module SVector.
Import Spiral_DOT_StructTactics.
Import Spiral_DOT_SpiralTactics.
Import Spiral_DOT_Spiral.
Import Spiral_DOT_VecUtil.
Import Spiral_DOT_VecSetoid.
Import Spiral_DOT_CarrierType.
Import Spiral_DOT_WriterMonadNoT.
Import Spiral_DOT_Rtheta.
Import Spiral_DOT_Rtheta.Spiral.
Import Spiral_DOT_WriterMonadNoT.Spiral.
Import Spiral_DOT_CarrierType.Spiral.
Import Spiral_DOT_VecSetoid.Spiral.
Import Spiral_DOT_VecUtil.Spiral.
Import Spiral_DOT_Spiral.Spiral.
Import Spiral_DOT_SpiralTactics.Spiral.
Import Spiral_DOT_StructTactics.Spiral.
Import Spiral_DOT_VecUtil.Spiral.VecUtil.
Import Spiral_DOT_VecSetoid.Spiral.VecSetoid.
Import Spiral_DOT_Spiral.Spiral.Spiral.
Import Spiral_DOT_Rtheta.Spiral.Rtheta.
Import Coq.Bool.Bool.
Import Coq.Arith.Arith.
Import Coq.Logic.FunctionalExtensionality.
Import Spiral_DOT_SpiralTactics.Spiral.SpiralTactics.
Import MathClasses.interfaces.canonical_names.
Import MathClasses.interfaces.abstract_algebra.

Import VectorNotations.
Import ExtLib.Structures.Monads.
Import Spiral_DOT_WriterMonadNoT.Spiral.WriterMonadNoT.

Import Monoid.

Open Scope vector_scope.
Open Scope nat_scope.

(* Vector using Rtheta (exlusive) *)
Notation rvector n := (vector Rtheta n) (only parsing).
(* Vector using RStheta (safe) *)
Notation rsvector n := (vector RStheta n) (only parsing).

Definition rvector2rsvector := Vmap Rtheta2RStheta.
Definition rsvector2rvector := Vmap RStheta2Rtheta.

Section SvectorBasics.
  Variable fm:Monoid RthetaFlags.
  Variable fml:@MonoidLaws RthetaFlags RthetaFlags_type fm.

  (* "sparse" vector for CarrierA type elements could be simulated using Rtheta *)
  Definition svector n := (vector (Rtheta' fm) n).

  (* Construct vector of Rtheta values from vector of raw values of it's carrier type *)
  Definition sparsify {n} (v:avector n): svector n :=
    Vmap mkValue v.

  Global Instance sparsify_proper {n:nat}:
    Proper ((=) ==> (=)) (@sparsify n).
Admitted.

  (* Project out carrier type values from vector of Rheta values *)
  Definition densify {n} (v:svector n): avector n :=
    Vmap (A:=(Rtheta' fm)) (@evalWriter _ _ _) v.

  Global Instance densify_proper {n:nat}:
    Proper ((=) ==> (=)) (@densify n).
  Proof.
    intros x y E.
    unfold densify.
    rewrite E.
    reflexivity.
  Qed.

  (* Construct "Zero svector". All values are structural zeros. *)
  Definition szero_svector n: svector n := Vconst mkSZero n.

  (* "dense" vector means that it does not contain "structural" values *)
  Definition svector_is_dense {n} (v:svector n) : Prop :=
    Vforall (@Is_Val fm)  v.

  Lemma Vnth_sparsify:
    ∀ (n i : nat) (ip : i < n) (v : avector n),
      Vnth (sparsify v) ip ≡ mkValue (Vnth v ip).
Admitted.

  Fixpoint Vin_Rtheta_Val {n} (v : svector n) (x : CarrierA) : Prop :=
    match v with
    | Vnil => False
    | Vcons y w => (WriterMonadNoT.evalWriter y) = x \/ Vin_Rtheta_Val w x
    end.

  Lemma Vbreak_dense_vector {n1 n2} {x: svector (n1+n2)} {x0 x1}:
    Vbreak x ≡ (x0, x1) ->
    svector_is_dense x ->  (svector_is_dense x0) /\ (svector_is_dense x1).
Admitted.

  Lemma szero_svector_all_zeros:
    ∀ n : nat, Vforall Is_ValZero (szero_svector n).
Admitted.

  Definition svector_is_collision {n} (v:svector n) :=
    Vexists Is_Collision v.

  Definition svector_is_non_collision {n} (v:svector n) :=
    Vforall Not_Collision v.

  Lemma sparsify_non_coll: forall n (x:avector n),
      svector_is_non_collision (sparsify x).
Admitted.

  Lemma sparsify_is_dense:
    ∀ (i : nat) (x : vector CarrierA i), svector_is_dense (sparsify x).
Admitted.

  Lemma sparsify_densify {n} (x:svector n):
    svector_is_dense x ->
    svector_is_non_collision x ->
    (sparsify (densify x)) ≡ x.
Admitted.

  Lemma sparsify_densify_equiv {n} (x:svector n):
    (sparsify (densify x)) = x.
Admitted.

End SvectorBasics.

Section Union.

  Variable fm:Monoid RthetaFlags.
  Variable fml:@MonoidLaws RthetaFlags RthetaFlags_type fm.

  Definition Union (dot : CarrierA -> CarrierA -> CarrierA)
    : Rtheta' fm -> Rtheta' fm -> Rtheta' fm := liftM2 dot.

  Lemma Union_comm (dot : CarrierA -> CarrierA -> CarrierA)
        `{C: !Commutative dot}:
    Commutative (Union dot).
Admitted.

  Lemma evalWriterUnion {a b: Rtheta' fm} {dot}:
    evalWriter (Union dot a b) =
    dot (evalWriter a)
        (evalWriter b).
Admitted.

  Global Instance Union_proper:
    Proper (((=) ==> (=) ==> (=)) ==> (=) ==> (=) ==> (=)) Union.
  Proof.
    intros dot dot' DP a b H x y E.
    unfold Union, equiv, Rtheta'_equiv in *.
    rewrite 2!evalWriter_Rtheta_liftM2.
    - apply DP.
      + apply H.
      + apply E.
  Qed.

  (** Unary union of vector's elements (left fold) *)
  Definition UnionFold
             {n}
             (dot:CarrierA->CarrierA->CarrierA)
             (initial:CarrierA)
             (v: svector fm n): Rtheta' fm :=
    Vfold_left_rev (Union dot) (mkStruct initial) v.

  (** Pointwise union of two vectors *)
  Definition Vec2Union
             {n}
             (dot:CarrierA->CarrierA->CarrierA)
             (a b: svector fm n): svector fm n
    := Vmap2 (Union dot) a b.

  Global Instance Vec2Union_proper {n}
    :
      Proper (((=) ==> (=) ==> (=)) ==> (=) ==> (=) ==> (=)) (Vec2Union (n:=n)).
  Proof.
    intros dot dot' Ed a a' Ea b b' Eb.
    unfold Vec2Union, Union.
    (* TODO: vec_index_equiv from VecSetoid. Move all vector-related stuff there *)
    unfold equiv, vec_Equiv; apply Vforall2_intro_nth; intros j jc.
    rewrite 2!Vnth_map2.
    unfold_Rtheta_equiv.
    rewrite 2!evalWriter_Rtheta_liftM2.
    apply Ed; apply evalWriter_proper; apply Vnth_arg_equiv; assumption.
  Qed.

  (** Matrix-union. *)
  Definition MUnion'
             {o n}
             (dot:CarrierA->CarrierA->CarrierA)
             (initial:CarrierA)
             (v: vector (svector fm o) n): svector fm o
    :=  Vfold_left_rev (Vec2Union dot) (Vconst (mkStruct initial) o) v.

  Global Instance MUnion'_proper {o n}
    : Proper (((=) ==> (=) ==> (=)) ==> (=) ==> (=) ==> (=)) (@MUnion' o n).
  Proof.
    intros dot dot' Ed one one' Eo x y E.
    unfold MUnion'.
    rewrite 2!Vfold_left_rev_to_Vfold_left_rev_reord.
    apply Vfold_left_rev_reord_proper.
    apply Vec2Union_proper.
    apply Ed.
    rewrite 2!Vconst_to_Vconst_reord.
    apply Vconst_reord_proper.
    rewrite Eo; reflexivity.
    apply E.
  Qed.

  Definition SumUnion
             {o n}
             (v: vector (svector fm o) n): svector fm o
    := MUnion' plus zero v.

  Global Instance SumUnion_proper {o n}
    : Proper ((=) ==> (=)) (@SumUnion o n).
  Proof.
    intros x y E.
    unfold SumUnion.
    rewrite E.
    reflexivity.
  Qed.

  Lemma UnionFold_cons
        m x (xs : svector fm m)
        (dot: CarrierA -> CarrierA -> CarrierA)
        (neutral: CarrierA):
    UnionFold dot neutral (Vcons x xs) ≡ Union dot (UnionFold dot neutral xs) x.
Admitted.

  Lemma Vec2Union_comm
        {n}
        (dot: CarrierA -> CarrierA -> CarrierA)
        `{C: !Commutative dot}
    :
      @Commutative (svector fm n) _ (svector fm n) (Vec2Union dot).
Admitted.

  Lemma MUnion'_0
        {o: nat}
        (dot: CarrierA -> CarrierA -> CarrierA)
        (initial: CarrierA)
        (v: vector (svector fm o) 0):
    MUnion' dot initial v ≡ Vconst (mkStruct initial) o.
Admitted.

  Lemma MUnion'_cons {m n}
        (dot: CarrierA -> CarrierA -> CarrierA)
        (neutral: CarrierA)
        (x: svector fm m) (xs: vector (svector fm m) n):
    MUnion' dot neutral (Vcons x xs) ≡ Vec2Union dot (MUnion' dot neutral xs) x.
Admitted.

  Lemma SumUnion_cons {m n}
        (x: svector fm m) (xs: vector (svector fm m) n):
    SumUnion (Vcons x xs) ≡ Vec2Union plus (SumUnion xs) x.
Admitted.

  Lemma AbsorbUnionIndexBinary
        (m k : nat)
        (kc : k < m)
        {dot}
        (a b : svector fm m):
    Vnth (Vec2Union dot a b) kc ≡ Union dot (Vnth a kc) (Vnth b kc).
Admitted.

  Lemma AbsorbMUnion'Index_Vbuild
        {o n}
        (dot:CarrierA -> CarrierA -> CarrierA)
        (neutral:CarrierA)
        (body: forall (i : nat) (ic : i < n), svector fm o)
        k (kc: k<o)
    :
      Vnth (MUnion' dot neutral (Vbuild body)) kc ≡
           UnionFold dot neutral
           (Vbuild
              (fun (i : nat) (ic : i < n) =>
                 Vnth (body i ic) kc
           )).
Admitted.

  (** Move indexing from outside of Union into the loop. Called 'union_index' in Vadim's paper notes. *)
  Lemma AbsorbMUnion'Index_Vmap
        (dot: CarrierA -> CarrierA -> CarrierA)
        (neutral: CarrierA)
        {m n:nat}
        (x: vector (svector fm m) n) k (kc: k<m):
    Vnth (MUnion' dot neutral x) kc ≡
         UnionFold dot neutral
         (Vmap (fun v => Vnth v kc) x).
Admitted.

  Lemma AbsorbSumUnionIndex_Vmap
        m n (x: vector (svector fm m) n) k (kc: k<m):
    Vnth (SumUnion x) kc ≡ UnionFold plus zero (Vmap (fun v => Vnth v kc) x).
Admitted.

  Lemma AbsorbISumUnionIndex_Vbuild
        {o n}
        (body: forall (i : nat) (ic : i < n), svector fm o)
        k (kc: k<o)
    :
      Vnth
        (SumUnion (Vbuild body)) kc ≡
        UnionFold plus zero
        (Vbuild
           (fun (i : nat) (ic : i < n) =>
              Vnth (body i ic) kc
        )).
Admitted.

  Lemma Union_SZero_r x:
    (Union plus x mkSZero) = x.
Admitted.

  Lemma Union_SZero_l x:
    (Union plus mkSZero x) = x.
Admitted.

  Lemma Vec2Union_szero_svector_r {n} {a: svector fm n}:
    Vec2Union plus a (szero_svector fm n) = a.
Admitted.

  Lemma Vec2Union_szero_svector_l {n} {a: svector fm n}:
    Vec2Union plus (szero_svector fm n) a = a.
Admitted.

End Union.

Section ExclusiveUnion.

  Lemma UnionCollisionFree (a b : Rtheta) {dot}:
    ¬Is_Collision a →
    ¬Is_Collision b →
    ¬(Is_Val a ∧ Is_Val b)
    → ¬Is_Collision (Union Monoid_RthetaFlags dot a b).
Admitted.

  (* Conditions under which Union produces value *)
  Lemma ValUnionIsVal (a b : Rtheta) {dot}:
    Is_Val a \/ Is_Val b <-> Is_Val (Union Monoid_RthetaFlags dot a b).
Admitted.

  (* Conditions under which Union produces struct *)
  Lemma StructUnionIsStruct (a b : Rtheta) {dot}:
    Is_Struct a /\ Is_Struct b <-> Is_Struct (Union Monoid_RthetaFlags dot a b).
Admitted.

  Lemma Is_Val_UnionFold {n} {v: rvector n} {dot} {neutral}:
    Vexists Is_Val v <-> Is_Val (UnionFold Monoid_RthetaFlags dot neutral v).
Admitted.

End ExclusiveUnion.


Section NonExclusiveUnion.

  (* Conditions under which Union produces value *)
  Lemma ValUnionIsVal_Safe (a b : RStheta) {dot}:
    Is_Val a \/ Is_Val b <-> Is_Val (Union Monoid_RthetaSafeFlags dot a b).
Admitted.

  Lemma Is_Val_UnionFold_Safe {n} {v: rsvector n} {dot} {neutral}:
    Vexists Is_Val v <-> Is_Val (UnionFold Monoid_RthetaSafeFlags dot neutral v).
Admitted.

  Lemma UnionCollisionFree_Safe (a b : RStheta) {dot}:
    ¬Is_Collision a →
    ¬Is_Collision b →
    ¬Is_Collision (Union Monoid_RthetaSafeFlags dot a b).
Admitted.

End NonExclusiveUnion.

(* RStheta2Rtheta distributes over Union *)
Lemma RStheta2Rtheta_over_Union {f a b}:
  RStheta2Rtheta
    (Union Monoid_RthetaSafeFlags f a b) =
  (Union Monoid_RthetaFlags f (RStheta2Rtheta a) (RStheta2Rtheta b)).
Admitted.


Section Matrix.
  (* Poor man's matrix is vector of vectors.
     TODO: If it grows, move to separate module. *)

  Set Implicit Arguments.
  Variables (A: Type) (m n:nat).

  Definition row
             {i:nat} (ic: i<m)
             (a: vector (vector A m) n)
    :=
      Vmap (Vnth_aux ic) a.

  Definition col
             {i:nat} (ic: i<n)
             (a: vector (vector A m) n)
    :=
      Vnth a ic.

  Definition transpose
             (a: vector (vector A m) n)
    :=
      Vbuild (fun j jc => row jc a).

End Matrix.

(* "sparse" matrix 'm' rows by 'n' columns *)
Notation smatrix m n := (vector (svector m) n) (only parsing).


Close Scope vector_scope.
Close Scope nat_scope.


End SVector.

End Spiral.

End Spiral_DOT_SVector.

Module Spiral_DOT_HCOLImpl.
Module Spiral.
Module HCOLImpl.
Import Spiral_DOT_StructTactics.
Import Spiral_DOT_SpiralTactics.
Import Spiral_DOT_Spiral.
Import Spiral_DOT_VecUtil.
Import Spiral_DOT_VecSetoid.
Import Spiral_DOT_CarrierType.
Import Spiral_DOT_WriterMonadNoT.
Import Spiral_DOT_Rtheta.
Import Spiral_DOT_SVector.
Import Spiral_DOT_SVector.Spiral.
Import Spiral_DOT_Rtheta.Spiral.
Import Spiral_DOT_WriterMonadNoT.Spiral.
Import Spiral_DOT_CarrierType.Spiral.
Import Spiral_DOT_VecSetoid.Spiral.
Import Spiral_DOT_VecUtil.Spiral.
Import Spiral_DOT_Spiral.Spiral.
Import Spiral_DOT_SpiralTactics.Spiral.
Import Spiral_DOT_StructTactics.Spiral.
(* Low-level functions implementing HCOL matrix and vector manupulation operators *)
Import Spiral_DOT_VecUtil.Spiral.VecUtil.
Import Spiral_DOT_VecSetoid.Spiral.VecSetoid.
Import Spiral_DOT_Spiral.Spiral.Spiral.
Import Spiral_DOT_CarrierType.Spiral.CarrierType.
Import Coq.Arith.Arith.
Import Coq.Program.Program. (* compose *)
Import Coq.Classes.Morphisms.
Import Coq.Classes.RelationClasses.
Import Coq.Relations.Relations.
Import Spiral_DOT_SpiralTactics.Spiral.SpiralTactics.
Import MathClasses.interfaces.abstract_algebra.
Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Import MathClasses.theory.rings.


Import VectorNotations.

Open Scope vector_scope.
Open Scope nat_scope.

Section HCOL_implementations.

  (* --- Type casts --- *)

  (* Promote scalar to unit vector *)
  Definition Vectorize (x:CarrierA): (avector 1) := [x].

  (* Convert single element vector to scalar *)
  Definition Scalarize (x: avector 1) : CarrierA := Vhead x.

  (* --- Scalar Product --- *)

  Definition ScalarProd
             {n} (ab: (avector n)*(avector n)) : CarrierA :=
    match ab with
    | (a, b) => Vfold_right plus (Vmap2 mult a b) zero
    end.

  (* --- Infinity Norm --- *)
  Definition InfinityNorm
             {n} (v: avector n) : CarrierA :=
    Vfold_right max (Vmap abs v) zero.

  (* Poor man's minus *)
  Definition sub := plus∘negate.

  (* The following is not strictly necessary as it follows from "properness" of composition, negation, and addition operations. Unfortunately Coq 8.4 class resolution could not find these automatically so we hint it by adding implicit instance. *)
  Global Instance CarrierA_sub_proper:
    Proper ((=) ==> (=) ==> (=)) (sub).
  Proof.
    intros a b Ha x y Hx .
    unfold sub, compose.
    rewrite Hx, Ha.
    reflexivity.
  Qed.

  (* --- Chebyshev Distance --- *)
  Definition ChebyshevDistance
             {n} (ab: (avector n)*(avector n)): CarrierA :=
    match ab with
    | (a, b) => InfinityNorm (Vmap2 sub a b)
    end.

  (* --- Vector Subtraction --- *)
  Definition VMinus
             {n} (ab: (avector n)*(avector n)) : avector n :=
    match ab with
    | (a,b) => Vmap2 ((+)∘(-)) a b
    end.

  (* --- Monomial Enumerator --- *)

  Fixpoint MonomialEnumerator
           (n:nat) (x:CarrierA) {struct n} : avector (S n) :=
    match n with
    | O => [one]
    | S p => Vcons one (Vmap (mult x) (MonomialEnumerator p x))
    end.

  (* --- Polynomial Evaluation --- *)

  Fixpoint EvalPolynomial {n}
           (a: avector n) (x:CarrierA) : CarrierA  :=
    match a with
      nil => zero
    | a0 :: a' => plus a0 (mult x (EvalPolynomial a' x))
    end.

  (* === HCOL Basic Operators === *)

  (* Arity 2 function lifted to vectors. Also passes index as first parameter *)
  Definition BinOp {n}
             (f: nat -> CarrierA -> CarrierA -> CarrierA)
             (ab: (avector n)*(avector n))
    : avector n :=
    match ab with
    | (a,b) =>  Vmap2Indexed f a b
    end.

  (* --- Induction --- *)

  Fixpoint Induction (n:nat) (f:CarrierA -> CarrierA -> CarrierA)
           (initial: CarrierA) (v: CarrierA) {struct n} : avector n
    :=
      match n with
      | O => []
      | S p => Vcons initial (Vmap (fun x => f x v) (Induction p f initial v))
      end.

  Definition Reduction {n:nat}
             (f: CarrierA -> CarrierA -> CarrierA)
             (id:CarrierA) (a: avector n) : CarrierA
    :=
      Vfold_right f a id.

  (* --- Scale --- *)
  Definition Scale
             {n} (sv:(CarrierA)*(avector n)) : avector n :=
    match sv with
    | (s,v) => Vmap (mult s) v
    end.

End HCOL_implementations.

Section HCOL_implementation_facts.

  Lemma Induction_cons:
    forall n initial (f:CarrierA -> CarrierA -> CarrierA)
      (v:CarrierA),
      Induction (S n) f initial v = Vcons initial (Vmap (fun x => f x v) (Induction n f initial v)).
Admitted.

  (* TODO: better name. Maybe suffficent to replace with EvalPolynomial_cons *)
  Lemma EvalPolynomial_reduce:
    forall n (a: avector (S n)) (x:CarrierA),
      EvalPolynomial a x  =
      plus (Vhead a) (mult x (EvalPolynomial (Vtail a) x)).
Admitted.

End HCOL_implementation_facts.

Section HCOL_implementation_proper.

  Global Instance Scale_proper
         `{!Proper ((=) ==> (=) ==> (=)) mult} (n:nat)
  :
    Proper ((=) ==> (=)) (Scale (n:=n)).
  Admitted.

  Global Instance ScalarProd_proper (n:nat):
    Proper ((=) ==> (=))
           (ScalarProd (n:=n)).
  Proof.
    intros x y Ex.
    destruct x as [xa xb].
    destruct y as [ya yb].
    unfold ScalarProd.
    rewrite 2!Vfold_right_to_Vfold_right_reord.
    destruct Ex as [H0 H1].
    simpl in H0, H1.
    rewrite H0, H1.
    reflexivity.
  Qed.

  Global Instance InfinityNorm_proper {n:nat}:
    Proper ((=) ==> (=))
           (InfinityNorm (n:=n)).
  Proof.
    unfold Proper.
    intros a b E1.
    unfold InfinityNorm.
    rewrite 2!Vfold_right_to_Vfold_right_reord.
    rewrite E1.
    reflexivity.
  Qed.

  Global Instance BinOp_proper {n:nat}:
    Proper (((=) ==> (=) ==> (=) ==> (=)) ==> (=) ==> (=)) (BinOp (n:=n)).
  Proof.
    intros fa fb Ef a b Ea.
    unfold BinOp.
    destruct a. destruct b.
    destruct Ea as [E1 E2]. simpl in *.
    apply Vmap2Indexed_proper; assumption.
  Qed.

  Global Instance Reduction_proper {n:nat}:
    Proper (((=) ==> (=) ==>  (=)) ==> (=) ==> (=) ==> (=)) (Reduction (n:=n)).
  Proof.
    unfold Proper.
    intros fa fb Ef a b E1 x y E2.
    unfold Reduction.
    rewrite 2!Vfold_right_to_Vfold_right_reord.
    apply Vfold_right_reord_proper; assumption.
  Qed.

  Global Instance ChebyshevDistance_proper  (n:nat):
    Proper ((=) ==> (=))  (ChebyshevDistance (n:=n)).
  Admitted.

  Global Instance EvalPolynomial_proper (n:nat):
    Proper ((=) ==> (=) ==> (=))  (EvalPolynomial (n:=n)).
  Admitted.

  Global Instance MonomialEnumerator_proper (n:nat):
    Proper ((=) ==> (=))  (MonomialEnumerator n).
  Admitted.

  Global Instance Induction_proper {n:nat}:
    Proper (((=) ==> (=) ==> (=)) ==> (=) ==> (=) ==> (=)) (@Induction n).
  Proof.
    intros f f' fEq ini ini' iniEq v v' vEq.
    induction n.
    reflexivity.
    rewrite 2!Induction_cons, 2!Vcons_to_Vcons_reord, 2!Vmap_to_Vmap_reord.
    f_equiv; try assumption.
    f_equiv; try apply IHn.
    unfold respectful.
    intros x y H.
    apply fEq; assumption.
  Qed.

  Global Instance VMinus_proper (n:nat):
    Proper ((=) ==> (=))
           (@VMinus n).
  Proof.
    intros a b E.
    unfold VMinus.
    repeat break_let.
    destruct E as [E1 E2]; simpl in *.
    rewrite E1, E2.
    reflexivity.
  Qed.

End HCOL_implementation_proper.

Close Scope nat_scope.
Close Scope vector_scope.



End HCOLImpl.

End Spiral.

End Spiral_DOT_HCOLImpl.

Module Spiral_DOT_HCOL.
Module Spiral.
Module HCOL.
Import Spiral_DOT_StructTactics.
Import Spiral_DOT_SpiralTactics.
Import Spiral_DOT_Spiral.
Import Spiral_DOT_VecUtil.
Import Spiral_DOT_VecSetoid.
Import Spiral_DOT_CarrierType.
Import Spiral_DOT_WriterMonadNoT.
Import Spiral_DOT_Rtheta.
Import Spiral_DOT_SVector.
Import Spiral_DOT_HCOLImpl.
Import Spiral_DOT_HCOLImpl.Spiral.
Import Spiral_DOT_SVector.Spiral.
Import Spiral_DOT_Rtheta.Spiral.
Import Spiral_DOT_WriterMonadNoT.Spiral.
Import Spiral_DOT_CarrierType.Spiral.
Import Spiral_DOT_VecSetoid.Spiral.
Import Spiral_DOT_VecUtil.Spiral.
Import Spiral_DOT_Spiral.Spiral.
Import Spiral_DOT_SpiralTactics.Spiral.
Import Spiral_DOT_StructTactics.Spiral.
Import Spiral_DOT_VecUtil.Spiral.VecUtil.
Import Spiral_DOT_VecSetoid.Spiral.VecSetoid.
Import Spiral_DOT_Spiral.Spiral.Spiral.
Import Spiral_DOT_CarrierType.Spiral.CarrierType.
Import Spiral_DOT_HCOLImpl.Spiral.HCOLImpl.
Import Coq.Arith.Arith.
Import Coq.Arith.Plus.
Import Coq.Program.Program.
Import Coq.Classes.Morphisms.
Import Spiral_DOT_SpiralTactics.Spiral.SpiralTactics.
Import Coq.Logic.FunctionalExtensionality.

(* CoRN MathClasses *)
Import MathClasses.interfaces.abstract_algebra.
Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Import MathClasses.implementations.peano_naturals.
Import MathClasses.theory.setoids.


Import VectorNotations.
Open Scope vector_scope.

(* === HCOL operators === *)

Section HCOL_Language.

  Class HOperator {i o:nat} (op: avector i -> avector o) :=
    HOperator_setoidmor :> Setoid_Morphism op.

  Lemma HOperator_functional_extensionality
        {m n: nat}
        `{HOperator m n f}
        `{HOperator m n g}:
    (∀ v, f v = g v) -> f = g.
Admitted.

  Definition HPrepend {i n} (a:avector n)
    : avector i -> avector (n+i)
    := Vapp a.

  Definition HInfinityNorm {i}
    : avector i -> avector 1
    := Vectorize ∘ InfinityNorm.

  Definition HReduction {i}
             (f: CarrierA -> CarrierA -> CarrierA)
             `{pF: !Proper ((=) ==> (=) ==> (=)) f}
             (idv: CarrierA)
    : avector i -> avector 1
    := Vectorize ∘ (Reduction f idv).

  Definition HVMinus {o}
    : avector (o+o) -> avector o
    := VMinus  ∘ (vector2pair o).

  Definition HBinOp {o}
             (f: nat -> CarrierA -> CarrierA -> CarrierA)
             `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
    : avector (o+o) -> avector o
    :=  BinOp f ∘ (vector2pair o).

  Definition HEvalPolynomial {n} (a: avector n): avector 1 -> avector 1
    := Lst ∘ EvalPolynomial a ∘ Scalarize.

  Definition HMonomialEnumerator n
    : avector 1 -> avector (S n)
    := MonomialEnumerator n ∘ Scalarize.

  Definition HChebyshevDistance h
    : avector (h+h) -> avector 1
    := Lst ∘ ChebyshevDistance ∘ (vector2pair h).

  Definition HScalarProd {h}
    : avector (h+h) -> avector 1
    := Lst ∘ ScalarProd ∘ (vector2pair h).

  Definition HInduction (n:nat)
             (f: CarrierA -> CarrierA -> CarrierA)
             `{pF: !Proper ((=) ==> (=) ==> (=)) f}
             (initial: CarrierA)
    : avector 1 -> avector n
    := Induction n f initial ∘ Scalarize.

  Definition HPointwise
             {n: nat}
             (f: { i | i<n} -> CarrierA -> CarrierA)
             `{pF: !Proper ((=) ==> (=) ==> (=)) f}
             (x: avector n)
    := Vbuild (fun j jd => f (j ↾ jd) (Vnth x jd)).

  Section HCOL_operators.

    Global Instance HPointwise_HOperator
           {n: nat}
           (f: { i | i<n} -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=)) f}:
      HOperator (@HPointwise n f pF).
    Proof.
      unfold HOperator. split; try (apply vec_Setoid).
      intros x y E.
      unfold HPointwise.
      vec_index_equiv i ip.
      rewrite 2!Vbuild_nth.
      assert(Vnth x ip = Vnth y ip).
      apply Vnth_arg_equiv; assumption.
      rewrite H.
      reflexivity.
    Qed.

    Global Instance HScalarProd_HOperator {n}:
      HOperator (@HScalarProd n).
    Proof.
      unfold HOperator. split; try (apply vec_Setoid).
      intros x y E.
      unfold HScalarProd.
      unfold compose, Lst, vector2pair.
      apply Vcons_single_elim.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HBinOp_HOperator {o}
           (f: nat -> CarrierA -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}:
      HOperator (@HBinOp o f pF).
    Proof.
      unfold HOperator. split; try (apply vec_Setoid).
      intros x y E.
      unfold HBinOp.
      unfold compose, Lst, vector2pair.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HReduction_HOperator {i}
           (f: CarrierA -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=)) f}
           (idv: CarrierA):
      HOperator (@HReduction i f pF idv).
    Proof.
      unfold HOperator. split; try (apply vec_Setoid).
      intros x y E.
      unfold HReduction .
      unfold compose, Lst, vector2pair.
      apply Vcons_single_elim.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HEvalPolynomial_HOperator {n} (a: avector n):
      HOperator (@HEvalPolynomial n a).
    Proof.
      unfold HOperator. split; try (apply vec_Setoid).
      intros x y E.
      unfold HEvalPolynomial.
      unfold compose, Lst, vector2pair.
      apply Vcons_single_elim.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HPrepend_HOperator {i n} (a:avector n):
      HOperator (@HPrepend i n a).
    Proof.
      unfold HOperator. split; try (apply vec_Setoid).
      intros x y E.
      unfold HPrepend.
      unfold compose, Lst, vector2pair.
      apply Vcons_single_elim.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HMonomialEnumerator_HOperator n:
      HOperator (@HMonomialEnumerator n).
    Proof.
      unfold HOperator. split; try (apply vec_Setoid).
      intros x y E.
      unfold HMonomialEnumerator.
      unfold compose, Lst, vector2pair.
      apply Vcons_single_elim.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HInfinityNorm_HOperator n:
      HOperator (@HInfinityNorm n).
    Proof.
      unfold HOperator. split; try (apply vec_Setoid).
      intros x y E.
      unfold HInfinityNorm.
      unfold compose, Lst, vector2pair.
      apply Vcons_single_elim.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HInduction_HOperator {n:nat}
           (f: CarrierA -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=)) f}
           (initial: CarrierA):
      HOperator (HInduction n f initial).
    Proof.
      unfold HOperator. split; try (apply vec_Setoid).
      intros x y E.
      unfold HInduction.
      unfold compose, Lst, vector2pair.
      apply Vcons_single_elim.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HChebyshevDistance_HOperator h:
      HOperator (HChebyshevDistance h).
    Proof.
      unfold HOperator. split; try (apply vec_Setoid).
      intros x y E.
      unfold HChebyshevDistance.
      unfold compose, Lst, vector2pair.
      apply Vcons_single_elim.
      rewrite E.
      reflexivity.
    Qed.

    Global Instance HVMinus_HOperator h:
      HOperator (@HVMinus h).
    Proof.
      unfold HOperator. split; try (apply vec_Setoid).
      intros x y E.
      unfold HVMinus.
      unfold compose, Lst, vector2pair.
      rewrite E.
      reflexivity.
    Qed.

  End HCOL_operators.
End HCOL_Language.

(* We forced to use this instead of usual 'reflexivity' tactics, as currently there is no way in Coq to define 'Reflexive' class instance constraining 'ext_equiv' function arguments by HOperator class *)
Ltac HOperator_reflexivity := eapply HOperator_functional_extensionality; reflexivity.

Section IgnoreIndex_wrapper.

  (* Wrapper to swap index parameter for HBinOp kernel with given value. 2 stands for arity of 'f' *)
  Definition SwapIndex2 {A} (i:nat) (f:nat->A->A->A) := const (B:=nat) (f i).

  Global Instance SwapIndex2_proper `{Setoid A}:
    Proper ((=) ==> ((=) ==> (=) ==> (=) ==> (=)) ==> (=) ==> (=) ==> (=) ==> (=)) (@SwapIndex2 A).
  Proof.
    simpl_relation.
    apply H1; assumption.
  Qed.

  (* Partially specialized SwapIndex2 is still proper *)
  Global Instance SwapIndex2_specialized_proper `{Setoid A} (i:nat) (f:nat->A->A->A)
         `{f_mor: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
    :
    Proper ((=) ==> (=) ==> (=) ==> (=)) (@SwapIndex2 A i f).
  Proof.
    partial_application_tactic. instantiate (1 := equiv).
    partial_application_tactic. instantiate (1 := equiv).
    apply SwapIndex2_proper.
    typeclasses eauto.
    apply f_mor.
  Qed.

  (* Wrapper to ignore index parameter for HBinOp kernel. 2 stands for arity of 'f' *)
  Definition IgnoreIndex2 {A} (f:A->A->A) := const (B:=nat) f.

  Lemma IgnoreIndex2_ignores `{Setoid A}
        (f:A->A->A)`{f_mor: !Proper ((=) ==> (=) ==> (=)) f}
    : forall i0 i1,
      (IgnoreIndex2 f) i0 = (IgnoreIndex2 f) i1.
Admitted.

  Global Instance IgnoreIndex2_proper `{Equiv A}:
    (Proper (((=) ==> (=)) ==> (=) ==> (=) ==> (=) ==> (=)) (@IgnoreIndex2 A)).
  Proof.
    simpl_relation.
    unfold IgnoreIndex2.
    apply H0; assumption.
  Qed.

  (* Wrapper to ignore index parameter for HPointwise kernel. *)
  Definition IgnoreIndex {A:Type} {n:nat} (f:A->A) := const (B:=@sig nat (fun i : nat => @lt nat peano_naturals.nat_lt i n)) f.

  Global Instance IgnoredIndex_proper {n:nat} `{Equiv A}:
    (Proper
       (((=) ==> (=)) ==> (=) ==> (=) ==> (=)) (@IgnoreIndex A n)).
  Proof.
    simpl_relation.
    unfold IgnoreIndex.
    apply H0.
    assumption.
  Qed.

End IgnoreIndex_wrapper.

Section HCOL_Operator_Lemmas.

  Lemma HPointwise_nth
        {n: nat}
        (f: { i | i<n} -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}
        {j:nat} {jc:j<n}
        (x: avector n):
    Vnth (HPointwise f x) jc = f (j ↾ jc) (Vnth x jc).
Admitted.

  Lemma HBinOp_nth
        {o}
        {f: nat -> CarrierA -> CarrierA -> CarrierA}
        `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
        {v: avector (o+o)}
        {j:nat}
        {jc: j<o}
        {jc1:j<o+o}
        {jc2: (j+o)<o+o}
    :
      Vnth (@HBinOp o f pF v) jc = f j (Vnth v jc1) (Vnth v jc2).
Admitted.

  Lemma HReduction_nil
        (f: CarrierA -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}
        (idv: CarrierA):
    HReduction f idv [] ≡ [idv].
Admitted.


End HCOL_Operator_Lemmas.




End HCOL.

End Spiral.

End Spiral_DOT_HCOL.

Module Spiral_DOT_THCOLImpl.
Module Spiral.
Module THCOLImpl.
Import Spiral_DOT_StructTactics.
Import Spiral_DOT_SpiralTactics.
Import Spiral_DOT_Spiral.
Import Spiral_DOT_VecUtil.
Import Spiral_DOT_VecSetoid.
Import Spiral_DOT_CarrierType.
Import Spiral_DOT_WriterMonadNoT.
Import Spiral_DOT_Rtheta.
Import Spiral_DOT_SVector.
Import Spiral_DOT_HCOLImpl.
Import Spiral_DOT_HCOL.
Import Spiral_DOT_HCOL.Spiral.
Import Spiral_DOT_HCOLImpl.Spiral.
Import Spiral_DOT_SVector.Spiral.
Import Spiral_DOT_Rtheta.Spiral.
Import Spiral_DOT_WriterMonadNoT.Spiral.
Import Spiral_DOT_CarrierType.Spiral.
Import Spiral_DOT_VecSetoid.Spiral.
Import Spiral_DOT_VecUtil.Spiral.
Import Spiral_DOT_Spiral.Spiral.
Import Spiral_DOT_SpiralTactics.Spiral.
Import Spiral_DOT_StructTactics.Spiral.
Import Spiral_DOT_Spiral.Spiral.Spiral.
Import Spiral_DOT_VecSetoid.Spiral.VecSetoid.
Import Spiral_DOT_CarrierType.Spiral.CarrierType.
Import Coq.Arith.Arith.
Import Coq.Program.Program. (* compose *)
Import Coq.Classes.Morphisms.
Import Coq.Classes.RelationClasses.
Import Coq.Relations.Relations.
Import Spiral_DOT_SpiralTactics.Spiral.SpiralTactics.
Import Coq.Logic.FunctionalExtensionality.

(* CoRN MathClasses *)
Import MathClasses.interfaces.abstract_algebra.
Import MathClasses.orders.minmax MathClasses.interfaces.orders.


Import VectorNotations.
Open Scope vector_scope.

Section THCOL_implementations.

  (* Apply 2 functions to the same input returning tuple of results *)
  Definition Stack {D R F: Type} (fg:(D->R)*(D->F)) (x:D) : (R*F) :=
    match fg with
    | (f,g) => pair (f x) (g x)
    end.

  (* Apply 2 functions to 2 inputs returning tuple of results *)
  Definition Cross {D R E F: Type} (fg:(D->R)*(E->F)) (x:D*E) : (R*F) :=
    match fg with
    | (f,g) => match x with
              | (x0,x1) => pair (f x0) (g x1)
              end
    end.

  Definition Zless (a b: CarrierA): CarrierA
    := if CarrierAltdec a b then one else zero.

  Global Instance Zless_proper:
    Proper ((=) ==> (=) ==> (=)) (Zless).
  Proof.
    unfold Proper.
    intros a a' aE z z' zE.
    unfold Zless.
    destruct (CarrierAltdec a z), (CarrierAltdec a' z'); auto.
    rewrite aE, zE in l; contradiction.
    rewrite <- aE, <- zE in l; contradiction.
  Qed.

  (* --- Pointwise Comparison --- *)

  (* Zero/One version *)
  Definition ZVLess {n}
             (ab: (avector n)*(avector n)) : avector n :=
    match ab with
    | (a,b) => Vmap2 (Zless) a b
    end.

  Global Instance ZVLess_proper {n:nat}:
    Proper ((=) ==> (=))  (@ZVLess n).
  Proof.
    (* solve_proper. *)
    intros x y E.
    unfold ZVLess.
    repeat break_let.
    inversion E. simpl in *.
    unfold equiv, vec_Equiv.
    rewrite H0, H.
    reflexivity.
  Qed.

End THCOL_implementations.


Section THCOL_implementation_proper.

  Global Instance Cross_arg_proper
         `{Equiv D,Equiv R,Equiv E,Equiv F}
         `{pF: !Proper ((=) ==> (=)) (f: D -> R)}
         `{pG: !Proper ((=) ==> (=)) (g: E -> F)}:
    Proper ((=) ==> (=))  (Cross (f,g)).
  Proof.
    intros fg fg' fgE.
    destruct fg, fg'.
    destruct fgE as [M2 M1]. simpl in *.
    split; simpl.
    apply pF; assumption.
    apply pG; assumption.
  Qed.

  Global Instance Stack_arg_proper
         `{Equiv D,Equiv R,Equiv F}
         `{pF: !Proper ((=) ==> (=)) (f: D -> R)}
         `{pG: !Proper ((=) ==> (=)) (g: D -> F)}:
    Proper ((=) ==> (=))  (Stack (f,g)).
  Proof.
    intros fg fg' fgE.
    split; simpl.
    apply pF; assumption.
    apply pG; assumption.
  Qed.

End THCOL_implementation_proper.



End THCOLImpl.

End Spiral.

End Spiral_DOT_THCOLImpl.

Module Spiral_DOT_THCOL.
Module Spiral.
Module THCOL.
Import Spiral_DOT_StructTactics.
Import Spiral_DOT_SpiralTactics.
Import Spiral_DOT_Spiral.
Import Spiral_DOT_VecUtil.
Import Spiral_DOT_VecSetoid.
Import Spiral_DOT_CarrierType.
Import Spiral_DOT_WriterMonadNoT.
Import Spiral_DOT_Rtheta.
Import Spiral_DOT_SVector.
Import Spiral_DOT_HCOLImpl.
Import Spiral_DOT_HCOL.
Import Spiral_DOT_THCOLImpl.
Import Spiral_DOT_THCOLImpl.Spiral.
Import Spiral_DOT_HCOL.Spiral.
Import Spiral_DOT_HCOLImpl.Spiral.
Import Spiral_DOT_SVector.Spiral.
Import Spiral_DOT_Rtheta.Spiral.
Import Spiral_DOT_WriterMonadNoT.Spiral.
Import Spiral_DOT_CarrierType.Spiral.
Import Spiral_DOT_VecSetoid.Spiral.
Import Spiral_DOT_VecUtil.Spiral.
Import Spiral_DOT_Spiral.Spiral.
Import Spiral_DOT_SpiralTactics.Spiral.
Import Spiral_DOT_StructTactics.Spiral.
Import Spiral_DOT_VecUtil.Spiral.VecUtil.
Import Spiral_DOT_VecSetoid.Spiral.VecSetoid.
Import Spiral_DOT_Spiral.Spiral.Spiral.
Import Spiral_DOT_CarrierType.Spiral.CarrierType.
Import Spiral_DOT_THCOLImpl.Spiral.THCOLImpl.
Import Spiral_DOT_HCOL.Spiral.HCOL.
Import Coq.Arith.Arith.
Import Coq.Program.Program.
Import Coq.Classes.Morphisms.
Import Coq.Classes.RelationClasses.
Import Coq.Relations.Relations.
Import Spiral_DOT_SpiralTactics.Spiral.SpiralTactics.
Import Coq.Logic.FunctionalExtensionality.

(* CoRN MathClasses *)
Import MathClasses.interfaces.abstract_algebra.
Import MathClasses.orders.minmax MathClasses.interfaces.orders.


Import VectorNotations.
Open Scope vector_scope.

(* Templete HCOL operator which uses two HOperators to build a new HOperator *)
Class THOperator2 {i1 o1 i2 o2 ix ox} (top: (avector i1 -> avector o1) -> (avector i2 -> avector o2) -> avector ix -> avector ox) :=
  THOperator2_proper :> Proper (((=) ==> (=)) ==> ((=) ==> (=)) ==> (=) ==> (=)) (top).

(* Curried Templete HCOL operator with arity 2 is HOperators *)
Global Instance THOperator_HOperator
         `{O1: @HOperator i1 o1 op1}
         `{O2: @HOperator i2 o2 op2}
         `{T: @THOperator2 i1 o1 i2 o2 ix ox to}:
  HOperator (to op1 op2).
Proof.
  split; try apply vec_Setoid.
  apply T ; [apply O1 | apply O2].
Qed.


Global Instance compose_THOperator2 {o2 o3 i1 o2:nat}:
  @THOperator2 o2 o3 i1 o2 i1 o3 (compose).
Proof.
  intros f f' Ef g g' Eg x y Ex.
  unfold compose, pair2vector, vector2pair.
  apply Ef, Eg, Ex.
Qed.


Global Instance compose_HOperator
         {i1 o2 o3}
        `{hop1: HOperator o2 o3 op1}
        `{hop2: HOperator i1 o2 op2}
:
  HOperator (op1 ∘ op2).
Proof.
  unfold HOperator. split; try (apply vec_Setoid).
  intros x y E.
  unfold compose.
  rewrite E.
  reflexivity.
Qed.

End THCOL.

End Spiral.

End Spiral_DOT_THCOL.

Module Spiral_DOT_FinNatSet.
Module Spiral.
Module FinNatSet.
Import Spiral_DOT_StructTactics.
Import Spiral_DOT_SpiralTactics.
Import Spiral_DOT_Spiral.
Import Spiral_DOT_VecUtil.
Import Spiral_DOT_VecSetoid.
Import Spiral_DOT_CarrierType.
Import Spiral_DOT_WriterMonadNoT.
Import Spiral_DOT_Rtheta.
Import Spiral_DOT_SVector.
Import Spiral_DOT_HCOLImpl.
Import Spiral_DOT_HCOL.
Import Spiral_DOT_THCOLImpl.
Import Spiral_DOT_THCOL.
Import Spiral_DOT_THCOL.Spiral.
Import Spiral_DOT_THCOLImpl.Spiral.
Import Spiral_DOT_HCOL.Spiral.
Import Spiral_DOT_HCOLImpl.Spiral.
Import Spiral_DOT_SVector.Spiral.
Import Spiral_DOT_Rtheta.Spiral.
Import Spiral_DOT_WriterMonadNoT.Spiral.
Import Spiral_DOT_CarrierType.Spiral.
Import Spiral_DOT_VecSetoid.Spiral.
Import Spiral_DOT_VecUtil.Spiral.
Import Spiral_DOT_Spiral.Spiral.
Import Spiral_DOT_SpiralTactics.Spiral.
Import Spiral_DOT_StructTactics.Spiral.
Export Coq.Init.Specif.
Export Coq.Sets.Ensembles.
Import Coq.Logic.Decidable.

Notation FinNat n := {x:nat | (x<n)}.
Notation FinNatSet n := (Ensemble (FinNat n)).

Definition mkFinNat {n} {j:nat} (jc:j<n) : FinNat n := @exist _ (gt n) j jc.

Definition FinNatSet_dec {n: nat} (s: FinNatSet n) := forall x, decidable (s x).

End FinNatSet.

End Spiral.

End Spiral_DOT_FinNatSet.

Module Spiral_DOT_IndexFunctions.
Module Spiral.
Module IndexFunctions.
Import Spiral_DOT_StructTactics.
Import Spiral_DOT_SpiralTactics.
Import Spiral_DOT_Spiral.
Import Spiral_DOT_VecUtil.
Import Spiral_DOT_VecSetoid.
Import Spiral_DOT_CarrierType.
Import Spiral_DOT_WriterMonadNoT.
Import Spiral_DOT_Rtheta.
Import Spiral_DOT_SVector.
Import Spiral_DOT_HCOLImpl.
Import Spiral_DOT_HCOL.
Import Spiral_DOT_THCOLImpl.
Import Spiral_DOT_THCOL.
Import Spiral_DOT_FinNatSet.
Import Spiral_DOT_FinNatSet.Spiral.
Import Spiral_DOT_THCOL.Spiral.
Import Spiral_DOT_THCOLImpl.Spiral.
Import Spiral_DOT_HCOL.Spiral.
Import Spiral_DOT_HCOLImpl.Spiral.
Import Spiral_DOT_SVector.Spiral.
Import Spiral_DOT_Rtheta.Spiral.
Import Spiral_DOT_WriterMonadNoT.Spiral.
Import Spiral_DOT_CarrierType.Spiral.
Import Spiral_DOT_VecSetoid.Spiral.
Import Spiral_DOT_VecUtil.Spiral.
Import Spiral_DOT_Spiral.Spiral.
Import Spiral_DOT_SpiralTactics.Spiral.
Import Spiral_DOT_StructTactics.Spiral.

(* Coq defintions for Sigma-HCOL operator language *)
Import Coq.Arith.Arith.
Import Coq.Strings.String.
Import Coq.Arith.Peano_dec.
Import Coq.Sorting.Permutation.
Import Coq.Lists.List.
Import Coq.Logic.FunctionalExtensionality.
Import Coq.Arith.PeanoNat.Nat.
Import Spiral_DOT_SpiralTactics.Spiral.SpiralTactics.
Import Coq.micromega.Psatz.
Import Coq.omega.Omega.
Import MathClasses.interfaces.canonical_names.
Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Import MathClasses.implementations.peano_naturals.
Import MathClasses.orders.orders.
Import MathClasses.interfaces.abstract_algebra.
Import Spiral_DOT_Spiral.Spiral.Spiral.
Import Spiral_DOT_FinNatSet.Spiral.FinNatSet.


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
  Admitted.
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
Admitted.

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
Admitted.

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
  Admitted.

  Lemma in_range_by_def:
    ∀ (d r : nat) (f : index_map d r) (x : nat) (xc: x < d),
      in_range f (⟦ f ⟧ x).
Admitted.

  Lemma in_range_upper_bound:
    ∀ (d r : nat) (f : index_map d r) (x : nat),
      in_range f x → x < r.
Admitted.


  Lemma in_range_shrink_index_map_domain (d r y : nat) (f : index_map (S d) r):
    in_range f y → ⟦ f ⟧ d ≢ y → in_range (shrink_index_map_domain f) y.
Admitted.

  Lemma in_range_exists
        {d r y: nat}
        (f: index_map d r)
        (yc: y<r)
    :
      in_range f y <-> (∃ x (xc:x<d), ⟦ f ⟧ x ≡ y).
Admitted.

  Lemma in_range_index_map_compose_left {i o t : nat}
        (f : index_map i t)
        (g : index_map t o)
        (j : nat)
        (jc: j<o):
    in_range (index_map_compose g f) j → in_range g j.
Admitted.

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
Admitted.

  Lemma index_map_surjective_in_range
        {d r: nat}
        (f: index_map d r)
        {S: index_map_surjective f}:
    forall x, x<r -> in_range f x.
Admitted.

  Lemma shrink_index_map_1_range_inj
        {r:nat}
        (f: index_map 1 (S r))
        (NZ: ⟦ f ⟧ 0 ≢ 0):
    index_map_injective f ->
    index_map_injective (shrink_index_map_1_range f NZ).
Admitted.

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
Admitted.

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
Admitted.

  (* The following lemma proves that using `buld_inverse_index_map` on
  injective index_map produces true "left inverse" of it *)
  Lemma build_inverse_index_map_is_left_inverse
        {d r: nat}
        (f: index_map d r)
        (f_inj: index_map_injective f):
    let fp := build_inverse_index_map f in
    let f' := inverse_index_f _ fp in
    forall x y (xc:x<d), ⟦ f ⟧ x ≡ y -> f' y ≡ x.
Admitted.


  (* The following lemma proves that using `buld_inverse_index_map` on
  injective index_map produces true "right inverse" of it *)
  Lemma build_inverse_index_map_is_right_inverse
        {d r: nat}
        (f: index_map d r)
        (f_inj: index_map_injective f):
    let fp := build_inverse_index_map f in
    let f' := inverse_index_f _ fp in
    forall x y (rc:in_range f y), f' y ≡ x -> ⟦ f ⟧ x ≡ y.
Admitted.

  Lemma build_inverse_index_map_is_injective:
    ∀ (d r : nat) (f : index_map d r),
      index_map_injective f →
      inverse_index_map_injective (build_inverse_index_map f).
Admitted.

  Lemma build_inverse_index_map_is_surjective:
    ∀ (d r : nat) (f : index_map d r), index_map_injective f → inverse_index_map_surjective (build_inverse_index_map f).
Admitted.

  Lemma build_inverse_index_map_is_bijective
        {d r: nat}
        (f: index_map d r)
        {f_inj: index_map_injective f}
    : inverse_index_map_bijective (build_inverse_index_map f).
Admitted.

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
Admitted.


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
Admitted.

  Lemma in_range_index_map_compose_right {i o t : nat}
        (f : index_map i t)
        (g : index_map t o)
        (g_inj: index_map_injective g)
        (j : nat)
        (jc: j < o):
    in_range g j ->
    in_range (index_map_compose g f) j ->
    in_range f (gen_inverse_index_f g j).
Admitted.

  Lemma in_range_index_map_compose {i o t : nat}
        (f : index_map i t)
        (g : index_map t o)
        (g_inj: index_map_injective g)
        (j : nat)
        (jc: j<o):
    in_range g j → in_range f (gen_inverse_index_f g j)
    → in_range (index_map_compose g f) j.
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

  Lemma in_range_of_h
        {domain range: nat}
        (b s: nat)
        {range_bound: forall x, x<domain -> (b+x*s) < range}
        (y:nat)
        (yc:y<range)
    :
      in_range (@h_index_map domain range b s range_bound) y
      <-> ∃ x (xc:x<domain), b+x*s = y.
Admitted.

End Primitive_Functions.

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
Admitted.

  Program Lemma index_map_rule_40:
    forall n (np: n>0)
           {range_bound_h_0: ∀ x : nat, x < n → 0 + x * 1 < n}
    ,
      @identity_index_map n np = h_index_map 0 1
                                             (range_bound:=range_bound_h_0).
Admitted.


  Local Close Scope index_f_scope.

End Function_Rules.

Section IndexMapSets.

  Definition index_map_range_set
             {d r: nat}
             (f: index_map d r): FinNatSet r :=
    fun x => in_range f (proj1_sig x).

End IndexMapSets.


End IndexFunctions.

End Spiral.

End Spiral_DOT_IndexFunctions.

Module Spiral_DOT_SigmaHCOL.
Module Spiral.
Module SigmaHCOL.
Import Spiral_DOT_StructTactics.
Import Spiral_DOT_SpiralTactics.
Import Spiral_DOT_Spiral.
Import Spiral_DOT_VecUtil.
Import Spiral_DOT_VecSetoid.
Import Spiral_DOT_CarrierType.
Import Spiral_DOT_WriterMonadNoT.
Import Spiral_DOT_Rtheta.
Import Spiral_DOT_SVector.
Import Spiral_DOT_HCOLImpl.
Import Spiral_DOT_HCOL.
Import Spiral_DOT_THCOLImpl.
Import Spiral_DOT_THCOL.
Import Spiral_DOT_FinNatSet.
Import Spiral_DOT_IndexFunctions.
Import Spiral_DOT_IndexFunctions.Spiral.
Import Spiral_DOT_FinNatSet.Spiral.
Import Spiral_DOT_THCOL.Spiral.
Import Spiral_DOT_THCOLImpl.Spiral.
Import Spiral_DOT_HCOL.Spiral.
Import Spiral_DOT_HCOLImpl.Spiral.
Import Spiral_DOT_SVector.Spiral.
Import Spiral_DOT_Rtheta.Spiral.
Import Spiral_DOT_WriterMonadNoT.Spiral.
Import Spiral_DOT_CarrierType.Spiral.
Import Spiral_DOT_VecSetoid.Spiral.
Import Spiral_DOT_VecUtil.Spiral.
Import Spiral_DOT_Spiral.Spiral.
Import Spiral_DOT_SpiralTactics.Spiral.
Import Spiral_DOT_StructTactics.Spiral.
Import Spiral_DOT_VecUtil.Spiral.VecUtil.
Import Spiral_DOT_VecSetoid.Spiral.VecSetoid.
Import Spiral_DOT_Spiral.Spiral.Spiral.
Import Spiral_DOT_Rtheta.Spiral.Rtheta.
Import Spiral_DOT_SVector.Spiral.SVector.
Import Spiral_DOT_IndexFunctions.Spiral.IndexFunctions.
Import Spiral_DOT_HCOL.Spiral.HCOL. (* Presently for HOperator only. Consider moving it elsewhere *)
Import Spiral_DOT_FinNatSet.Spiral.FinNatSet.
Import Spiral_DOT_WriterMonadNoT.Spiral.WriterMonadNoT.
Import Coq.Logic.FunctionalExtensionality.
Import Coq.Arith.Arith.
Import Coq.Bool.Bool.
Import Coq.Bool.BoolEq.
Import Coq.Strings.String.
Import Coq.Arith.Peano_dec.
Import Coq.Logic.Decidable.
Import Spiral_DOT_SpiralTactics.Spiral.SpiralTactics.
Import Coq.micromega.Psatz.
Import Coq.omega.Omega.

(* CoRN MathClasses *)
Import MathClasses.interfaces.abstract_algebra.
Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Import MathClasses.theory.rings.
Import MathClasses.implementations.peano_naturals.
Import MathClasses.orders.orders.
Import MathClasses.orders.semirings.
Import MathClasses.theory.setoids.

(* Ext Lib *)
Import ExtLib.Structures.Monad.
Import ExtLib.Structures.Monoid.

Import Monoid.

(*  CoLoR *)

Import VectorNotations.
Open Scope vector_scope.

Global Open Scope nat_scope.

(* Not currenly used. For future *)
Section BVector.
  Notation bvector n := (vector bool n).

  Definition false_bvector (n:nat) : bvector n := Vconst false n.
  Definition true_bvector (n:nat) : bvector n := Vconst true n.
  Definition or_bvector (n:nat) (a b: bvector n) :=
    Vmap2 orb a b.
  Definition and_bvector (n:nat) (a b: bvector n) :=
    Vmap2 andb a b.

  Definition Monoid_bvector_false_or (n:nat) : Monoid (bvector n) :=
    Build_Monoid (or_bvector n) (false_bvector n).

  Definition Monoid_bvector_true_and (n:nat) : Monoid (bvector n) :=
    Build_Monoid (and_bvector n) (true_bvector n).

End BVector.

(* Returns an element of the vector 'x' which is result of mapping of
given natrual number by index mapping function f_spec. *)
Definition VnthIndexMapped
           {i o:nat}
           {A: Type}
           (x: vector A i)
           (f: index_map o i)
           (n:nat) (np: n<o)
  : A
  := Vnth x (« f » n np).


Section SigmaHCOL_Operators.

  Section FlagsMonoidGenericOperators.

    Variable fm:Monoid RthetaFlags.

    Record SHOperator
           {i o: nat}
      : Type
      := mkSHOperator {
             op: svector fm i -> svector fm o ;
             op_proper: Proper ((=) ==> (=)) op;
             in_index_set: FinNatSet i ;
             out_index_set: FinNatSet o;
           }.


    (* Two vectors (=) at indices at given set *)
    Definition vec_equiv_at_set
               {n:nat}
               (x y: svector fm n)
               (s: FinNatSet n)
      :=
        (forall j (jc:j<n),
            s(mkFinNat jc) -> Vnth x jc = Vnth y jc).

    Lemma vec_equiv_at_subset
          {k:nat}
          (x y: svector fm k)
          (n h: FinNatSet k):
      Included _ n h -> vec_equiv_at_set x y h -> vec_equiv_at_set x y n.
Admitted.

    Lemma vec_equiv_at_Union
          {i : nat}
          (s0 s1 : FinNatSet i)
          (x y : svector fm i):
      vec_equiv_at_set x y (Union _ s0 s1)
      → (vec_equiv_at_set x y s0 /\ vec_equiv_at_set x y s1).
Admitted.

    Lemma vec_equiv_at_Full_set {i : nat}
          (x y : svector fm i):
      vec_equiv_at_set x y (Full_set (FinNat i)) <-> x = y.
Admitted.

    Lemma vec_equiv_at_set_narrowing
          {n : nat}
          (s0 : FinNatSet n)
          (s1 : FinNatSet n)
          (C: Included (FinNat n) s0 s1):
      forall x y : svector fm n,
        vec_equiv_at_set x y s1 → vec_equiv_at_set x y s0.
Admitted.

    (* Equivalence of two SHOperators is defined via functional extensionality *)
    Global Instance SHOperator_equiv
           {i o: nat}:
      Equiv (@SHOperator i o) :=
      fun a b => op a = op b.

    Definition op_Vforall_P
               {i o: nat}
               (P: Rtheta' fm -> Prop)
               (f: @SHOperator i o)
      :=
        forall x, Vforall P ((op f) x).

    Record SHOperatorFamily
           {i o n: nat}
      : Type
      := mkSHOperatorFamily {
             family_member: (forall j (jc:j<n), @SHOperator i o)
           }.

    (* Accessors, mapping SHOperator family to family of underlying "raw" functions *)
    Definition get_family_op
               {i o n}
               (op_family: @SHOperatorFamily i o n):
      forall j (jc:j<n), svector fm i -> svector fm o
      := fun j (jc:j<n) => op (family_member op_family j jc).

    Definition get_family_proper
               {i o n}
               (op_family: @SHOperatorFamily i o n):
      forall j (jc:j<n), Proper ((=) ==> (=)) (get_family_op op_family j jc)
      := fun j (jc:j<n) => op_proper (family_member op_family j jc).

    Definition shrink_op_family
               {i o n}
               (op_family: @SHOperatorFamily i o (S n)): @SHOperatorFamily i o n :=
      match op_family with
      | mkSHOperatorFamily _ _ _ m =>
        mkSHOperatorFamily i o n
                           (fun (j:nat) (jc:j<n) => m j (@le_S (S j) n jc))
      end.

    Fixpoint family_in_index_set
             {i o n}
             (op_family: @SHOperatorFamily i o n): FinNatSet i
      :=
        match n as y return (y ≡ n -> @SHOperatorFamily i o y -> FinNatSet i) with
        | O => fun _ _ => (Empty_set _)
        | S j => fun E f => Union _
                                  (in_index_set (family_member op_family j (S_j_lt_n E)))
                                  (family_in_index_set (shrink_op_family f))
        end (eq_refl n) op_family.

    Fixpoint family_out_index_set
             {i o n}
             (op_family: @SHOperatorFamily i o n): FinNatSet o
      :=
        match n as y return (y ≡ n -> @SHOperatorFamily i o y -> FinNatSet o) with
        | O => fun _ _ => (Empty_set _)
        | S j => fun E f => Union _
                              (out_index_set (family_member op_family j (S_j_lt_n E)))
                              (family_out_index_set (shrink_op_family f))
        end (eq_refl n) op_family.

    Lemma family_in_set_includes_members:
      ∀ (i o k : nat) (op_family : @SHOperatorFamily i o k)
        (j : nat) (jc : j < k),
        Included (FinNat i)
                 (in_index_set (family_member op_family j jc))
                 (family_in_index_set op_family).
Admitted.

    Lemma family_in_set_implies_members
          (i o k : nat) (op_family : @SHOperatorFamily i o k)
          (j : nat) (jc : j < i):

      family_in_index_set op_family (mkFinNat jc) ->
      ∃ (t : nat) (tc : t < k),
        in_index_set (family_member op_family t tc)
                     (mkFinNat jc).
Admitted.

    Lemma family_out_set_includes_members:
      ∀ (i o k : nat) (op_family : @SHOperatorFamily i o k)
        (j : nat) (jc : j < k),
        Included (FinNat o)
                 (out_index_set (family_member op_family j jc))
                 (family_out_index_set op_family).
Admitted.

    Lemma family_out_set_implies_members
          (i o k : nat) (op_family : @SHOperatorFamily i o k)
          (j : nat) (jc : j < o):

      family_out_index_set op_family (mkFinNat jc) <->
      ∃ (t : nat) (tc : t < k),
        out_index_set (family_member op_family t tc)
                      (mkFinNat jc).
Admitted.

    Lemma SHOperator_ext_equiv_applied
          {i o: nat}
          (f g: @SHOperator i o):
      (f=g) <-> (forall v, op f v = op g v).
Admitted.

    Global Instance SHOperator_equiv_Reflexive
           {i o: nat}:
      Reflexive (@SHOperator_equiv i o).
    Proof.
      intros x.
      unfold SHOperator_equiv.
      destruct x.
      auto.
    Qed.

    Global Instance SHOperator_equiv_Symmetric
           {i o: nat}:
      Symmetric (@SHOperator_equiv i o).
    Proof.
      intros x y.
      unfold SHOperator_equiv.
      auto.
    Qed.

    Global Instance SHOperator_equiv_Transitive
           {i o: nat}:
      Transitive (@SHOperator_equiv i o).
    Proof.
      intros x y z.
      unfold SHOperator_equiv.
      auto.
    Qed.

    Global Instance SHOperator_equiv_Equivalence
           {i o: nat}:
      Equivalence (@SHOperator_equiv i o).
    Proof.
      split.
      apply SHOperator_equiv_Reflexive.
      apply SHOperator_equiv_Symmetric.
      apply SHOperator_equiv_Transitive.
    Qed.

    Global Instance SHOperatorFamily_equiv
           {i o n: nat}:
      Equiv (@SHOperatorFamily i o n) :=
      fun a b => forall j (jc:j<n), family_member a j jc = family_member b j jc.

    Global Instance SHOperatorFamily_equiv_Reflexive
           {i o n: nat}:
      Reflexive (@SHOperatorFamily_equiv i o n).
    Proof.
      intros x.
      unfold SHOperatorFamily_equiv.
      auto.
    Qed.

    Global Instance SHOperatorFamily_equiv_Symmetric
           {i o n: nat}:
      Symmetric (@SHOperatorFamily_equiv i o n).
    Proof.
      intros x y.
      unfold SHOperatorFamily_equiv.
      intros H j jc.
      specialize (H j jc).
      auto.
    Qed.

    Global Instance SHOperatorFamily_equiv_Transitive
           {i o n: nat}:
      Transitive (@SHOperatorFamily_equiv i o n).
    Proof.
      intros x y z.
      unfold SHOperatorFamily_equiv.
      intros H H0 j jc.
      specialize (H j jc).
      specialize (H0 j jc).
      auto.
    Qed.

    Global Instance SHOperatorFamily_equiv_Equivalence
           {i o n: nat}:
      Equivalence (@SHOperatorFamily_equiv i o n).
    Proof.
      split.
      apply SHOperatorFamily_equiv_Reflexive.
      apply SHOperatorFamily_equiv_Symmetric.
      apply SHOperatorFamily_equiv_Transitive.
    Qed.

    Lemma SM_op_SHOperator
          (i o : nat):
      forall (a:@SHOperator i o), Setoid_Morphism (op a).
Admitted.

    Global Instance SHOperator_op_proper {i o} :
      Proper ((=) ==> (=) ==> (=)) (@op i o).
    Proof.
      intros f f' Ef v v' Ev.
      destruct f as [fop op_pre_post op_proper].
      destruct f' as [fop' op_pre_post' op_proper'].
      simpl.
      apply Ef.
      apply Ev.
    Qed.

    Global Instance get_family_op_proper {i o n} :
      Proper ((=) ==>
                  (forall_relation (λ j : nat, pointwise_relation (j < n) (=))))
             (@get_family_op i o n).
    Proof.
      intros a a' Ea.
      unfold forall_relation, pointwise_relation.
      intros j jc.
      unfold get_family_op.
      apply SHOperator_op_proper.
      apply Ea.
    Qed.

    Global Instance SHOperator_op_arg_proper {i o} (a:@SHOperator i o):
      Proper ((=) ==> (=)) (op a).
    Proof.
      solve_proper.
    Qed.

    Global Instance mkSHOperatorFamily_proper
           {i o n: nat}:
      Proper (forall_relation (λ i : nat, pointwise_relation (i < n) equiv) ==> equiv)
             (mkSHOperatorFamily i o n).
    Proof.
      intros f0 f1 Ef.
      unfold equiv, SHOperatorFamily_equiv.
      auto.
    Qed.

    Global Instance op_Vforall_P_arg_proper
           {i o: nat}
           (P: Rtheta' fm -> Prop)
           (P_mor: Proper ((=) ==> iff) P):
      Proper ((=) ==> iff) (@op_Vforall_P i o P).
    Proof.
      intros x y E.
      unfold op_Vforall_P.
      split.
      -
        intros H x0.
        specialize (H x0).
        apply Vforall_nth_intro.
        intros i0 ip.
        apply Vforall_nth with (ip:=ip) in H.
        setoid_replace (Vnth (op y x0) ip) with (Vnth (op x x0) ip).
        apply H.
        apply Vnth_arg_equiv.
        rewrite E.
        reflexivity.
      -
        intros H x0.
        specialize (H x0).
        apply Vforall_nth_intro.
        intros i0 ip.
        apply Vforall_nth with (ip:=ip) in H.
        setoid_replace (Vnth (op x x0) ip) with (Vnth (op y x0) ip).
        apply H.
        apply Vnth_arg_equiv.
        rewrite E.
        reflexivity.
    Qed.

    Definition liftM_HOperator'
               {i o}
               (op: avector i -> avector o)
      : svector fm i -> svector fm o :=
      sparsify fm ∘ op ∘ densify fm.

    Global Instance liftM_HOperator'_proper
           {i o}
           (op: avector i -> avector o)
           `{HOP: HOperator i o op}
      :
        Proper ((=) ==> (=)) (liftM_HOperator' op).
    Proof.
      intros x y H.
      unfold liftM_HOperator'.
      unfold compose.
      f_equiv.
      rewrite H.
      reflexivity.
    Qed.

    Definition liftM_HOperator
               {i o}
               (op: avector i -> avector o)
               `{HOP: HOperator i o op}
      := mkSHOperator i o (liftM_HOperator' op) (@liftM_HOperator'_proper i o op HOP)
                      (Full_set _) (Full_set _).

    (** Apply family of functions to same fector and return matrix of results *)
    Definition Apply_Family'
               {i o n}
               (op_family_f: forall k, (k<n) -> svector fm i -> svector fm o)
               (v: svector fm i) :
      vector (svector fm o) n :=
      Vbuild
        (λ (j:nat) (jc:j<n),  (op_family_f j jc) v).


    Global Instance Apply_Family'_arg_proper
           {i o n}
           (op_family_f: forall k, (k<n) -> svector fm i -> svector fm o)
           (op_family_f_proper: forall k (kc:k<n), Proper ((=) ==> (=)) (op_family_f k kc))
      :
        Proper ((=) ==> (=)) (@Apply_Family' i o n op_family_f).
    Proof.
      intros x y E.
      unfold Apply_Family'.
      vec_index_equiv j jc.
      rewrite 2!Vbuild_nth.
      apply op_family_f_proper, E.
    Qed.

    (** Apply family of SHOperator's to same fector and return matrix of results *)
    Definition Apply_Family
               {i o n}
               (op_family: @SHOperatorFamily i o n)
      :=
        Apply_Family' (get_family_op op_family).

    Global Instance Apply_Family_proper
           {i o n}:
      Proper ((=) ==> (=) ==> (=)) (@Apply_Family i o n).
    Proof.
      intros f f' Ef v v' Ev.
      unfold Apply_Family, Apply_Family'.
      vec_index_equiv j jc.
      rewrite 2!Vbuild_nth.
      unfold get_family_op.
      destruct f as [fmem].
      destruct f' as [fmem'].
      simpl.
      unfold equiv, SHOperatorFamily_equiv in Ef. simpl in Ef.
      rewrite <- Ev.
      specialize (Ef j jc).
      apply SHOperator_op_proper.
      apply Ef.
      reflexivity.
    Qed.

    (* Do we need this in presence of Apply_Family_proper ? *)
    Global Instance Apply_Family_arg_proper
           {i o n}
           (op_family: @SHOperatorFamily i o n):
      Proper ((=) ==> (=)) (@Apply_Family i o n op_family).
    Proof.
      intros x y E.
      apply Apply_Family'_arg_proper.
      - intros k kc.
        apply get_family_proper.
      - apply E.
    Qed.

    (* Apply operator family to a vector produced a matrix which have at most one non-zero element per row.
       TODO: This could be expressed via set disjointness? *)
    Definition Apply_Family_Single_NonUnit_Per_Row
               {i o n}
               (op_family: @SHOperatorFamily i o n)
               (aunit: CarrierA)
      :=
        forall x, Vforall (Vunique (not ∘ (equiv aunit) ∘ (@evalWriter _ _ fm)))
                     (transpose
                        (Apply_Family op_family x)
                     ).


    (* States that given [P] holds for all elements of all outputs of this family *)
    Definition Apply_Family_Vforall_P
               {i o n}
               (P: Rtheta' fm -> Prop)
               (op_family: @SHOperatorFamily i o n)
      :=
        forall x (j:nat) (jc:j<n), Vforall P ((get_family_op op_family j jc) x).

    Definition Gather'
               {i o: nat}
               (f: index_map o i)
               (x: svector fm i):
      svector fm o
      := Vbuild (VnthIndexMapped x f).

    Global Instance Gather'_proper
           {i o: nat}
           (f: index_map o i):
      Proper ((=) ==> (=)) (Gather' f).
    Proof.
      intros x y Exy.
      unfold Gather', VnthIndexMapped.
      vec_index_equiv j jp.
      rewrite 2!Vbuild_nth.
      apply Vnth_arg_equiv.
      apply Exy.
    Qed.

    Definition IdOp
               {n: nat}
               (in_out_set:FinNatSet n)
      := mkSHOperator n n id _ in_out_set in_out_set.

    Definition Gather
               {i o: nat}
               (f: index_map o i)
      := mkSHOperator i o (Gather' f) _
                      (index_map_range_set f) (* Read pattern is governed by index function *)
                      (Full_set _) (* Gater always writes everywhere *).

    Definition GathH
               {i o}
               (base stride: nat)
               {domain_bound: ∀ x : nat, x < o → base + x * stride < i}
      :=
        Gather (h_index_map base stride
                            (range_bound:=domain_bound) (* since we swap domain and range, domain bound becomes range boud *)
               ).

    Definition Scatter'
               {i o: nat}
               (f: index_map i o)
               {f_inj: index_map_injective f}
               (idv: CarrierA)
               (x: svector fm i) : svector fm o
      :=
        let f' := build_inverse_index_map f in
        Vbuild (fun n np =>
                  match decide (in_range f n) with
                  | left r => Vnth x (inverse_index_f_spec f f' n r)
                  | right _ => mkStruct idv
                  end).

    Global Instance Scatter'_proper
           {i o: nat}
           (f: index_map i o)
           {f_inj: index_map_injective f}:
      Proper ((=) ==> (=) ==> (=)) (Scatter' f (f_inj:=f_inj)).
    Proof.
      intros z0 z1 Ez x y Exy.
      unfold Scatter'.
      vec_index_equiv j jp.
      simpl.
      rewrite 2!Vbuild_nth.
      break_match.
      - apply Vnth_arg_equiv, Exy.
      - rewrite Ez.
        reflexivity.
    Qed.

    Definition Scatter
               {i o: nat}
               (f: index_map i o)
               {f_inj: index_map_injective f}
               (idv: CarrierA)
      := mkSHOperator i o (Scatter' f (f_inj:=f_inj) idv) _
                      (Full_set _) (* Scatter always reads evertying *)
                      (index_map_range_set f) (* Write pattern is governed by index function *).

    Definition ScatH
               {i o}
               (base stride: nat)
               {range_bound: ∀ x : nat, x < i → base + x * stride < o}
               {snzord0: stride ≢ 0 \/ i < 2}
      :=
        Scatter (h_index_map base stride (range_bound:=range_bound))
                (f_inj := h_index_map_is_injective base stride (snzord0:=snzord0)).

    Definition SHCompose
               {i1 o2 o3}
               (op1: @SHOperator o2 o3)
               (op2: @SHOperator i1 o2)
      : @SHOperator i1 o3 := mkSHOperator i1 o3 (compose (op op1) (op op2)) _
                                          (in_index_set op2)
                                          (out_index_set op1).

    Local Notation "g ⊚ f" := (@SHCompose _ _ _ g f) (at level 40, left associativity) : type_scope.

    Lemma SHCompose_val_equal_compose
          {i1 o2 o3}
          (op1: @SHOperator o2 o3)
          (op2: @SHOperator i1 o2)
      :
        (op op1) ∘ (op op2) = op (op1 ⊚ op2).
Admitted.

    Global Instance SHCompose_proper
           {i1 o2 o3}
      :
        Proper ((=) ==> (=) ==> (=)) (@SHCompose i1 o2 o3).
    Proof.
      intros x x' Ex y y' Ey.
      unfold SHCompose.
      unfold equiv, SHOperator_equiv in *.
      destruct x, y, x', y'.
      simpl in *.
      rewrite <- Ey, <- Ex.
      unfold equiv, ext_equiv.
      apply compose_proper with (RA:=equiv) (RB:=equiv).
      + apply op_proper0.
      + apply op_proper1.
    Qed.


    Definition Constant_Family
               {i o n}
               (f: @SHOperator i o)
      : @SHOperatorFamily i o n
      :=
        mkSHOperatorFamily _ _ _  (fun (j : nat) (_ : j < n) => f).

    (* Family composition *)
    Definition SHFamilyFamilyCompose
               {i1 o2 o3 n}
               (f: @SHOperatorFamily o2 o3 n)
               (g: @SHOperatorFamily i1 o2 n)
      : @SHOperatorFamily i1 o3 n
      :=
        mkSHOperatorFamily _ _ _
                           (fun (j : nat) (jc : j < n) =>
                              family_member f j jc  ⊚ family_member g j jc).

    Global Instance SHFamilyFamilyCompose_proper
           {i1 o2 o3 n: nat}
      :
        Proper ((=) ==> (=) ==> (=)) (@SHFamilyFamilyCompose i1 o2 o3 n).
    Proof.
      intros f f' Ef g g' Eg.
      unfold equiv, SHOperatorFamily_equiv.
      intros j jc.
      unfold SHFamilyFamilyCompose; simpl.

      apply SHCompose_proper.
      unfold equiv, ext_equiv, respectful in Ef.
      apply Ef.
      unfold equiv, ext_equiv, respectful in Eg.
      apply Eg.
    Qed.

    (* Family/operator composition *)
    Definition  SHOperatorFamilyCompose
                {i1 o2 o3 n}
                (f: @SHOperator o2 o3)
                (g: @SHOperatorFamily i1 o2 n)
      : @SHOperatorFamily i1 o3 n
      :=
        mkSHOperatorFamily _ _ _
                           (fun (j : nat) (jc : j < n) =>
                              f  ⊚ family_member g j jc).

    Global Instance SHOperatorFamilyCompose_proper
           {i1 o2 o3 n: nat}
      :
        Proper ((=) ==> (=) ==> (=)) (@SHOperatorFamilyCompose i1 o2 o3 n).
    Proof.
      intros f f' Ef g g' Eg.
      unfold equiv, SHOperatorFamily_equiv.
      intros j jc.
      unfold SHFamilyFamilyCompose; simpl.

      apply SHCompose_proper.
      apply Ef.
      unfold equiv, ext_equiv, respectful in Eg.
      apply Eg.
    Qed.

    Definition  SHFamilyOperatorCompose
                {i1 o2 o3 n}
                (f: @SHOperatorFamily o2 o3 n)
                (g: @SHOperator i1 o2)
      : @SHOperatorFamily i1 o3 n
      :=
        mkSHOperatorFamily _ _ _
                           (fun (j : nat) (jc : j < n) =>
                              family_member f j jc  ⊚ g).

    Global Instance SHFamilyOperatorCompose_proper
           {i1 o2 o3 n: nat}
      :
        Proper ((=) ==> (=) ==> (=)) (@SHFamilyOperatorCompose i1 o2 o3 n).
    Proof.
      intros f f' Ef g g' Eg.
      unfold equiv, SHOperatorFamily_equiv.
      intros j jc.
      unfold SHFamilyFamilyCompose; simpl.

      apply SHCompose_proper.
      unfold equiv, ext_equiv, respectful in Ef.
      apply Ef.
      apply Eg.
    Qed.


    (* Sigma-HCOL version of HPointwise. We could not just (liftM_Hoperator HPointwise) but we want to preserve structural flags. *)
    Definition SHPointwise'
               {n: nat}
               (f: { i | i<n} -> CarrierA -> CarrierA)
               `{pF: !Proper ((=) ==> (=) ==> (=)) f}
               (x: svector fm n): svector fm n
      := Vbuild (fun j jd => liftM (f (j ↾ jd)) (Vnth x jd)).

    Global Instance SHPointwise'_proper
           {n: nat}
           (f: { i | i<n} -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=)) f}:
      Proper ((=) ==> (=)) (SHPointwise' f).
    Proof.
      intros x y Exy.
      unfold SHPointwise'.
      vec_index_equiv j jc.
      rewrite 2!Vbuild_nth.
      unfold_Rtheta_equiv.
      rewrite 2!evalWriter_Rtheta_liftM.
      f_equiv.
      apply evalWriter_proper.
      apply Vnth_arg_equiv.
      apply Exy.
    Qed.

    Definition SHPointwise
               {n: nat}
               (f: { i | i<n} -> CarrierA -> CarrierA)
               `{pF: !Proper ((=) ==> (=) ==> (=)) f}
      := mkSHOperator n n (SHPointwise' f) _ (Full_set _) (Full_set _).

    Definition SHBinOp'
               {o}
               (f: nat -> CarrierA -> CarrierA -> CarrierA)
               `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
               (v:svector fm (o+o)): svector fm o
      :=  match (vector2pair o v) with
          | (a,b) => Vbuild (fun i ip => liftM2 (f i) (Vnth a ip) (Vnth b ip))
          end.

    Global Instance SHBinOp'_proper
           {o}
           (f: nat -> CarrierA -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}:
      Proper ((=) ==> (=)) (SHBinOp' (o:=o) f).
    Proof.
      intros x y E.
      unfold SHBinOp'.

      vec_index_equiv j jc.
      unfold vector2pair.

      repeat break_let.
      rename Heqp into H0, Heqp0 into H1.

      replace t with (fst (Vbreak x)) by (rewrite H0 ; reflexivity).
      replace t0 with (snd (Vbreak x)) by (rewrite H0 ; reflexivity).
      replace t1 with (fst (Vbreak y)) by (rewrite H1 ; reflexivity).
      replace t2 with (snd (Vbreak y)) by (rewrite H1 ; reflexivity).
      clear H0 H1.

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

    (* Sparse Embedding is an operator family *)
    Definition SparseEmbedding
               {n i o ki ko}
               (* Kernel *)
               (kernel: @SHOperatorFamily ki ko n)
               (* Scatter index map *)
               (f: index_map_family ko o n)
               {f_inj : index_map_family_injective f}
               (idv: CarrierA)
               (* Gather index map *)
               (g: index_map_family ki i n)
      : @SHOperatorFamily i o n
      := mkSHOperatorFamily i o n
                            (fun (j:nat) (jc:j<n) =>
                               (Scatter (⦃f⦄ j jc)
                                        (f_inj:=index_map_family_member_injective f_inj j jc) idv)
                                 ⊚ (family_member kernel j jc)
                                 ⊚ (Gather (⦃g⦄ j jc))).


    (* TODO: rename since Zero changed to IDV *)
    Lemma Scatter'_Zero_at_sparse
          {i o: nat}
          (f: index_map i o)
          {f_inj: index_map_injective f}
          (idv: CarrierA)
          (x: svector fm i)
          (k:nat)
          (kc:k<o):
      ¬ in_range f k -> (Is_ValX idv) (Vnth (Scatter' f (f_inj:=f_inj) idv x) kc).
Admitted.

    (* TODO: rename since Zero changed to IDV *)
    Lemma Scatter'_NonZero_in_range
          {i o: nat}
          (f: index_map i o)
          {f_inj: index_map_injective f}
          (idv: CarrierA)
          (x: svector fm i)
          (k:nat)
          (kc:k<o):
      idv ≠ evalWriter (Vnth (Scatter' f (f_inj:=f_inj) idv x) kc) -> in_range f k.
Admitted.

    (* TODO: rename since Zero changed to IDV *)
    Lemma SparseEmbedding_Apply_Family_Single_NonZero_Per_Row
          {n i o ki ko}
          (* Kernel *)
          (kernel: @SHOperatorFamily ki ko n)
          (* Scatter index map *)
          (f: index_map_family ko o n)
          {f_inj : index_map_family_injective f}
          (idv: CarrierA)
          (* Gather index map *)
          (g: index_map_family ki i n):
      Apply_Family_Single_NonUnit_Per_Row
        (SparseEmbedding kernel f (f_inj:=f_inj) idv g) idv.
Admitted.

  End FlagsMonoidGenericOperators.

  Definition SHBinOp
             {o}
             (f: nat -> CarrierA -> CarrierA -> CarrierA)
             `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
    := mkSHOperator Monoid_RthetaSafeFlags
                    (o+o) o (SHBinOp' Monoid_RthetaSafeFlags f) _ (Full_set _) (Full_set _).

  Section MUnion.

    Variable fm:Monoid RthetaFlags.

    (* An operator applied to a list of vectors (matrix) with uniform pre and post conditions *)
    Record MSHOperator
           {o n: nat}
      : Type
      := mkMSHOperator {
             mop: vector (svector fm o) n -> svector fm o ;
             mop_proper: Proper ((=) ==> (=)) mop
           }.

    Definition MUnion
               {o n}
               (dot: CarrierA->CarrierA->CarrierA)
               `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
               (initial: CarrierA)
      :=
        @mkMSHOperator o n (MUnion' fm dot initial) _.

  End MUnion.

  (** Matrix-union. This is a common implementations for IUnion and IReduction *)
  Definition Diamond'
             {i o n}
             {fm}
             (dot: CarrierA -> CarrierA -> CarrierA)
             (initial: CarrierA)
             (op_family_f: forall k (kc:k<n), svector fm i -> svector fm o)
             (v:svector fm i): svector fm o
    :=
      MUnion' fm dot initial (@Apply_Family' fm i o n op_family_f v).


  Global Instance Diamond'_proper
         {i o n} {fm}
    : Proper (
          (=) ==> (=) ==>
              (@forall_relation nat
                                (fun k : nat =>  forall _ : k<n, (svector fm i -> svector fm o))
                                (fun k : nat =>  @pointwise_relation (k < n)
                                                                (svector fm i -> svector fm o) (=)))
              ==> (=) ==> (=)) (@Diamond' i o n fm).
  Proof.
    intros d d' Ed ini ini' Ei f f' Ef v v' Ev.
    unfold Diamond'.
    apply MUnion'_proper; auto.

    unfold Apply_Family'.
    vec_index_equiv j jc.
    rewrite 2!Vbuild_nth.
    unfold forall_relation, pointwise_relation in Ef.
    apply Ef, Ev.
  Qed.

  (* One might think we do not need this in presence of Diamond'_proper. However even this partially applied morphism could be easily proven from Diamond'_proper sometimes helps class resolutuion which does not always find Diamond'_proper *)
  Global Instance Diamond'_arg_proper
         {i o n}
         {fm}
         (dot: CarrierA -> CarrierA -> CarrierA)
         `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
         (initial: CarrierA)
         (op_family_f: forall k (kc:k<n), svector fm i -> svector fm o)
         (op_family_f_proper: forall k (kc:k<n), Proper ((=) ==> (=)) (op_family_f k kc))
    : Proper ((=) ==> (=)) (Diamond' dot initial op_family_f).
  Proof.
    apply Diamond'_proper.
    - apply pdot.
    - reflexivity.
    - unfold forall_relation, pointwise_relation.
      apply op_family_f_proper.
  Qed.

  Definition IUnion
             {i o n}
             (* Functional parameters *)
             (dot: CarrierA -> CarrierA -> CarrierA)
             `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
             (initial: CarrierA)
             (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n)
    : @SHOperator Monoid_RthetaFlags i o
    :=
      mkSHOperator Monoid_RthetaFlags i o
                   (Diamond' dot initial (get_family_op Monoid_RthetaFlags op_family))
                   _
                   (family_in_index_set _ op_family)
                   (family_out_index_set _ op_family)
  . (* requires get_family_op_proper OR SHOperator_op_arg_proper *)

  Definition ISumUnion
             {i o n}
             (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n)
    : @SHOperator Monoid_RthetaFlags i o
    :=
      @IUnion i o n CarrierAplus _ zero op_family.

  (** IReduction does not have any constraints. Specifically no
  density or Monoid. It just extracts values from Monad and folds them
  row-wise. For example if for (+) id value is 0 and all structural
  values are structural zeros it will do row sums. It could not
  produce new errors, but should propagate errors from before.
   *)
  Definition IReduction
             {i o n}
             (dot: CarrierA -> CarrierA -> CarrierA)
             `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
             (initial: CarrierA)
             (op_family: @SHOperatorFamily Monoid_RthetaSafeFlags i o n)
    : @SHOperator Monoid_RthetaSafeFlags i o:=
    mkSHOperator Monoid_RthetaSafeFlags i o
                 (Diamond' dot initial (get_family_op Monoid_RthetaSafeFlags op_family))
                 _
                 (family_in_index_set _ op_family)
                 (family_out_index_set _ op_family) (* All scatters must be the same but we do not enforce it here. However if they are the same, the union will equal to any of them, so it is legit to use union here *)
  .

  (*

  In SPIRAL [ISumReduction] is what we call [ISumReduction] and strictly speaking there is no equivalent to [ISumReduction] as defined below. [ISumReduction] defined below is basically row-wise sum. To avoid confusion we will not use [ISumReduction] name for now.

  Definition ISumReduction
             {i o n}
             (op_family: @SHOperatorFamily Monoid_RthetaSafeFlags i o n)
    :=
      @IReduction i o n plus _ zero op_family.
   *)

  (* TODO: make `dot` part of Morphism *)
  Global Instance IReduction_proper
         {i o n: nat}
         (dot: CarrierA -> CarrierA -> CarrierA)
         `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
    :
      Proper ((=) ==> (=) ==> (=)) (@IReduction i o n dot pdot).
  Proof.
    intros i0 i1 Ei x y E.
    unfold IReduction, equiv,  SHOperator_equiv.
    simpl.
    rewrite E, Ei.
    f_equiv; auto.
    f_equiv; auto.
  Qed.


End SigmaHCOL_Operators.

(* TODO: maybe <->  *)
Lemma Is_Val_Scatter
      {m n: nat}
      (f: index_map m n)
      {f_inj: index_map_injective f}
      (idv: CarrierA)
      (x: rvector m)
      (j: nat) (jc : j < n):
  Is_Val (Vnth (Scatter' _ f (f_inj:=f_inj) idv x) jc) ->
  (exists i (ic:i<m), ⟦f⟧ i ≡ j).
Admitted.

Definition USparseEmbedding
           {n i o ki ko}
           (* Kernel *)
           (kernel: @SHOperatorFamily Monoid_RthetaFlags ki ko n)
           (f: index_map_family ko o n)
           {f_inj : index_map_family_injective f}
           (idv: CarrierA)
           (g: index_map_family ki i n)
  : @SHOperator Monoid_RthetaFlags i o
  :=
    ISumUnion
      (@SparseEmbedding Monoid_RthetaFlags
                        n i o ki ko
                        kernel
                        f f_inj idv
                        g).

Section OperatorProperies.

  Variable fm:Monoid RthetaFlags.
  Variable fml:@MonoidLaws RthetaFlags RthetaFlags_type fm.

  Local Notation "g ⊚ f" := (@SHCompose _ _ _ _ g f) (at level 40, left associativity) : type_scope.

  Lemma SHCompose_assoc
        {i1 o2 o3 o4}
        (h: @SHOperator fm o3 o4)
        (g: @SHOperator fm o2 o3)
        (f: @SHOperator fm i1 o2):
    h ⊚ g ⊚ f = h ⊚ (g ⊚ f).
Admitted.

  Lemma SHCompose_mid_assoc
        {i1 o1 o2 o3 o4}
        (h: @SHOperator fm o3 o4)
        (g: @SHOperator fm o2 o3)
        (f: @SHOperator fm o1 o2)
        (k: @SHOperator fm i1 o1):
    h ⊚ g ⊚ f ⊚ k = h ⊚ (g ⊚ f) ⊚ k.
Admitted.


  (* Specification of gather as mapping from output to input. NOTE:
    we are using definitional equality here, as Scatter does not
    perform any operations on elements of type A *)
  Lemma Gather'_spec
        {i o: nat}
        (f: index_map o i)
        (x: svector fm i):
    ∀ n (ip : n < o), Vnth (Gather' fm f x) ip ≡ VnthIndexMapped x f n ip.
Admitted.

  (* Index-function based condition under which Gather output is dense *)
  Lemma Gather'_dense_constr (i ki : nat)
        (g: index_map ki i)
        (x: svector fm i)
        (g_dense: forall k (kc:k<ki), Is_Val (Vnth x («g» k kc))):
    Vforall Is_Val (Gather' fm g x).
Admitted.


  Lemma Gather'_is_endomorphism:
    ∀ (i o : nat)
      (x : svector fm i),
    ∀ (f: index_map o i),
      Vforall (Vin_aux x)
              (Gather' fm f x).
Admitted.

  Lemma Gather'_preserves_P:
    ∀ (i o : nat) (x : svector fm i) (P: Rtheta' fm -> Prop),
      Vforall P x
      → ∀ f : index_map o i,
        Vforall P (Gather' fm f x).
Admitted.

  Lemma Gather'_preserves_density:
    ∀ (i o : nat) (x : svector fm i)
      (f: index_map o i),
      svector_is_dense fm x ->
      svector_is_dense fm (Gather' fm f x).
Admitted.

  (* Specification of scatter as mapping from input to output. NOTE:
    we are using definitional equality here, as Scatter does not
    perform any operations on elements of type A *)
  Lemma Scatter'_spec
        {i o: nat}
        (f: index_map i o)
        {f_inj: index_map_injective f}
        (idv: CarrierA)
        (x: svector fm i)
        (n: nat) (ip : n < i):
    Vnth x ip ≡ VnthIndexMapped (Scatter' fm f (f_inj:=f_inj) idv x) f n ip.
Admitted.

  Lemma Scatter'_is_almost_endomorphism
        (i o : nat)
        (x : svector fm i)
        (f: index_map i o)
        {f_inj : index_map_injective f}
        (idv: CarrierA):
    Vforall (fun p => (Vin p x) \/ (p ≡ mkStruct idv))
            (Scatter' fm f (f_inj:=f_inj) idv x).
Admitted.

  Lemma Scatter'_1_1
        (f : index_map 1 1)
        (f_inj : index_map_injective f)
        (idv : CarrierA)
        (h : Rtheta' fm):
    Scatter' fm f (f_inj:=f_inj) idv [h] ≡ [h].
Admitted.

  Lemma Scatter'_1_Sn
        {n: nat}
        (f: index_map 1 (S n))
        {f_inj: index_map_injective f}
        (idv: CarrierA)
        (x: svector fm 1):
    Scatter' fm f (f_inj:=f_inj) idv x
             ≡
             match Nat.eq_dec (⟦ f ⟧ 0) 0 with
             | in_left =>
               Vcons
                 (Vhead x)
                 (Vconst (mkStruct idv) n)
             | right fc =>
               let f' := (shrink_index_map_1_range f fc) in
               Vcons
                 (mkStruct idv)
                 (Scatter' fm f' (f_inj:= shrink_index_map_1_range_inj f fc f_inj) idv x)
             end.
Admitted.

  Lemma SHPointwise'_nth
        {n: nat}
        (f: { i | i<n} -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}
        {j:nat} {jc:j<n}
        (v: svector fm n):
    Vnth (SHPointwise' fm f v) jc = mkValue (f (j ↾ jc) (WriterMonadNoT.evalWriter (Vnth v jc))).
Admitted.

  Lemma SHPointwise_nth_eq
        {n: nat}
        (f: { i | i<n} -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}
        {j:nat} {jc:j<n}
        (v: svector fm n):
    Vnth (op _ (SHPointwise fm f) v) jc ≡ Monad.liftM (f (j ↾ jc)) (Vnth v jc).
Admitted.

  Lemma SHPointwise_equiv_lifted_HPointwise
        {n: nat}
        (f: { i | i<n} -> CarrierA -> CarrierA)
        `{pF: !Proper ((=) ==> (=) ==> (=)) f}:
    SHPointwise fm f =
    liftM_HOperator fm (@HPointwise n f pF).
Admitted.

  Lemma SHBinOp'_nth
        {o}
        {f: nat -> CarrierA -> CarrierA -> CarrierA}
        `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
        {v: svector fm (o+o)}
        {j:nat}
        {jc: j<o}
        {jc1:j<o+o}
        {jc2: (j+o)<o+o}
    :
      Vnth (@SHBinOp' fm o f pF v) jc ≡ liftM2 (f j) (Vnth v jc1) (Vnth v jc2).
Admitted.

End OperatorProperies.


  Lemma UnionFold_empty_Non_Collision
        (k : nat)
        (dot : CarrierA → CarrierA → CarrierA)
        (initial : CarrierA)
        (v : vector Rtheta k):
    Vforall Not_Collision v
    → Vforall (not ∘ Is_Val) v
    → Not_Collision (UnionFold Monoid_RthetaFlags dot initial v).
Admitted.

  Lemma UnionFold_empty_Not_Val
        (k : nat)
        {dot : CarrierA → CarrierA → CarrierA}
        {initial : CarrierA}
        {v : vector Rtheta k}:
    Vforall Not_Collision v
    → Vforall (not ∘ Is_Val) v
    → ¬ Is_Val (UnionFold Monoid_RthetaFlags dot initial v).
Admitted.

  Lemma UnionFold_VAllBytOne_Non_Collision
        (k : nat)
        (dot : CarrierA → CarrierA → CarrierA) (initial : CarrierA)
        (v : vector Rtheta k)
        (Vnc: Vforall Not_Collision v)
        (i : nat)
        (ic : i < k)
        (Vv: VAllButOne i ic (not ∘ Is_Val) v):
    Not_Collision (UnionFold Monoid_RthetaFlags dot initial v).
Admitted.

  Lemma UnionFold_Non_Collision
        (k : nat)
        (dot : CarrierA → CarrierA → CarrierA)
        (initial : CarrierA)
        (v : rvector  k)
        (Vnc: Vforall Not_Collision v)
        (Vu: Vunique Is_Val v)
    :
      Not_Collision (UnionFold Monoid_RthetaFlags dot initial v).
Admitted.

  Lemma UnionFold_Safe_Non_Collision
        (k : nat)
        (dot : CarrierA → CarrierA → CarrierA)
        (initial : CarrierA)
        (v : rsvector  k)
        (Vnc: Vforall Not_Collision v)
    :
      Not_Collision (UnionFold Monoid_RthetaSafeFlags dot initial v).
Admitted.


End SigmaHCOL.

End Spiral.

End Spiral_DOT_SigmaHCOL.

Module Spiral_DOT_TSigmaHCOL.
Module Spiral.
Module TSigmaHCOL.
Import Spiral_DOT_StructTactics.
Import Spiral_DOT_SpiralTactics.
Import Spiral_DOT_Spiral.
Import Spiral_DOT_VecUtil.
Import Spiral_DOT_VecSetoid.
Import Spiral_DOT_CarrierType.
Import Spiral_DOT_WriterMonadNoT.
Import Spiral_DOT_Rtheta.
Import Spiral_DOT_SVector.
Import Spiral_DOT_HCOLImpl.
Import Spiral_DOT_HCOL.
Import Spiral_DOT_THCOLImpl.
Import Spiral_DOT_THCOL.
Import Spiral_DOT_FinNatSet.
Import Spiral_DOT_IndexFunctions.
Import Spiral_DOT_SigmaHCOL.
Import Spiral_DOT_SigmaHCOL.Spiral.
Import Spiral_DOT_IndexFunctions.Spiral.
Import Spiral_DOT_FinNatSet.Spiral.
Import Spiral_DOT_THCOL.Spiral.
Import Spiral_DOT_THCOLImpl.Spiral.
Import Spiral_DOT_HCOL.Spiral.
Import Spiral_DOT_HCOLImpl.Spiral.
Import Spiral_DOT_SVector.Spiral.
Import Spiral_DOT_Rtheta.Spiral.
Import Spiral_DOT_WriterMonadNoT.Spiral.
Import Spiral_DOT_CarrierType.Spiral.
Import Spiral_DOT_VecSetoid.Spiral.
Import Spiral_DOT_VecUtil.Spiral.
Import Spiral_DOT_Spiral.Spiral.
Import Spiral_DOT_SpiralTactics.Spiral.
Import Spiral_DOT_StructTactics.Spiral.
Import Spiral_DOT_VecUtil.Spiral.VecUtil.
Import Spiral_DOT_VecSetoid.Spiral.VecSetoid.
Import Spiral_DOT_Spiral.Spiral.Spiral.
Import Spiral_DOT_Rtheta.Spiral.Rtheta.
Import Spiral_DOT_SVector.Spiral.SVector.
Import Spiral_DOT_IndexFunctions.Spiral.IndexFunctions.
Import Spiral_DOT_SigmaHCOL.Spiral.SigmaHCOL. (* Presently for SHOperator only. Consider moving it elsewhere *)
Import Spiral_DOT_FinNatSet.Spiral.FinNatSet.
Import Coq.Arith.Arith.
Import Coq.Program.Program.
Import Coq.Classes.Morphisms.
Import Coq.Classes.RelationClasses.
Import Coq.Relations.Relations.
Import Spiral_DOT_SpiralTactics.Spiral.SpiralTactics.
Import Coq.Logic.FunctionalExtensionality.

(* CoRN MathClasses *)
Import MathClasses.interfaces.abstract_algebra.
Import MathClasses.orders.minmax MathClasses.interfaces.orders.
Import MathClasses.theory.rings.
Import MathClasses.theory.setoids.

(* ExtLib *)
Import ExtLib.Structures.Monoid.
Import Monoid.

Section RthetaSafetyCast.

  Definition SafeCast'
             {o i}
             (f: rsvector i -> rsvector o):
    rvector i -> rvector o
    := (rsvector2rvector o) ∘ f ∘ (rvector2rsvector i).

  Global Instance SafeCast'_proper (i o : nat):
    Proper (equiv ==> equiv ==> equiv) (@SafeCast' i o).
  Proof.
    intros f f' Ef v v' Ev.
    unfold SafeCast', compose, rsvector2rvector, rvector2rsvector.
    f_equiv.
    vec_index_equiv j jc.
    apply Vnth_arg_equiv.
    unfold equiv, ext_equiv, respectful in Ef.
    apply Ef.
    f_equiv.
    apply Ev.
  Qed.

  Definition SafeCast {i o}
             (f: @SHOperator Monoid_RthetaSafeFlags i o)
    : @SHOperator Monoid_RthetaFlags i o.
  Proof.
    refine (mkSHOperator Monoid_RthetaFlags i o
                         (SafeCast' (op Monoid_RthetaSafeFlags f))
                         _  _ _).
    -
      apply f.
    -
      apply f.
  Defined.

  Global Instance SafeCast_proper (i o:nat):
    Proper (equiv ==> equiv) (@SafeCast i o).
  Proof.
    intros f f' Ev.
    unfold SafeCast.
    unfold equiv, SHOperator_equiv.
    simpl.

    destruct f, f'.
    unfold equiv, SHOperator_equiv in Ev.
    simpl in *.

    apply SafeCast'_proper.
    apply Ev.
  Qed.

  Definition SafeFamilyCast {i o n}
             (f: @SHOperatorFamily Monoid_RthetaSafeFlags i o n)
    : @SHOperatorFamily Monoid_RthetaFlags i o n
    :=
      mkSHOperatorFamily _ _ _ _
                         (fun (j : nat) (jc : j < n) =>
                            SafeCast (family_member Monoid_RthetaSafeFlags f j jc)).

  Global Instance SafeFamilyCast_proper (i o n:nat):
    Proper (equiv ==> equiv) (@SafeFamilyCast i o n).
  Proof.
    intros f f' Ev.
    unfold SafeFamilyCast.
    unfold equiv, SHOperatorFamily_equiv.
    simpl.
    intros j jc.

    destruct f, f'.
    unfold equiv, SHOperator_equiv in Ev.
    simpl in *.

    apply SafeCast'_proper.
    apply Ev.
  Qed.

  Definition UnSafeCast'
             {o i}
             (f: rvector i -> rvector o):
    rsvector i -> rsvector o
    := (rvector2rsvector o) ∘ f ∘ (rsvector2rvector i).


  Global Instance UnSafeCast'_proper (i o : nat):
    Proper (equiv ==> equiv ==> equiv) (@UnSafeCast' i o).
  Proof.
    intros f f' Ef v v' Ev.
    unfold UnSafeCast', compose, rsvector2rvector, rvector2rsvector.
    f_equiv.
    vec_index_equiv j jc.
    apply Vnth_arg_equiv.
    unfold equiv, ext_equiv, respectful in Ef.
    apply Ef.
    f_equiv.
    apply Ev.
  Qed.

  Definition UnSafeCast {i o}
             (f: @SHOperator Monoid_RthetaFlags i o)
    : @SHOperator Monoid_RthetaSafeFlags i o.
  Proof.
    refine (mkSHOperator Monoid_RthetaSafeFlags i o
                         (UnSafeCast' (op Monoid_RthetaFlags f))
                         _  _ _).
    -
      apply f.
    -
      apply f.
  Defined.

  Global Instance UnSafeCast_proper (i o:nat):
    Proper (equiv ==> equiv) (@UnSafeCast i o).
  Proof.
    intros f f' Ev.
    unfold UnSafeCast.
    unfold equiv, SHOperator_equiv.
    simpl.

    destruct f, f'.
    unfold equiv, SHOperator_equiv in Ev.
    simpl in *.

    apply UnSafeCast'_proper.
    apply Ev.
  Qed.


  Definition UnSafeFamilyCast {i o n}
             (f: @SHOperatorFamily Monoid_RthetaFlags i o n)
    : @SHOperatorFamily Monoid_RthetaSafeFlags i o n
    :=
      mkSHOperatorFamily _ _ _ _
                         (fun (j : nat) (jc : j < n) =>
                            UnSafeCast (family_member Monoid_RthetaFlags f j jc)).


  Global Instance UnSafeFamilyCast_proper (i o n:nat):
    Proper (equiv ==> equiv) (@UnSafeFamilyCast i o n).
  Proof.
    intros f f' Ev.
    unfold UnSafeFamilyCast.
    unfold equiv, SHOperatorFamily_equiv.
    simpl.

    destruct f, f'.
    unfold equiv, SHOperator_equiv in Ev.
    simpl in *.
    intros j jc.

    apply UnSafeCast'_proper.
    apply Ev.
  Qed.

End RthetaSafetyCast.


(* For now we are not define special type for TSigmahcolOperators, like we did for SHOperator. Currently we have only 2 of these: SHCompose and HTSumunion. We will generalize in future, if needed *)
Section TSigmaHCOLOperators.

  Variable fm:Monoid RthetaFlags.
  Variable fml:@MonoidLaws RthetaFlags RthetaFlags_type fm.

  (* Per Vadim's discussion with Franz on 2015-12-14, ISumUnion is
  just Union of two vectors, produced by application of two operators
  to the input.
   *)
  Definition HTSUMUnion' {i o}
             (dot: CarrierA -> CarrierA -> CarrierA)
             (op1: svector fm i -> svector fm o)
             (op2: svector fm i -> svector fm o):
    svector fm i -> svector fm o
    := fun x => Vec2Union fm dot (op1 x) (op2 x).


  (* TODO: make dot part of morphism *)
  Global Instance HTSUMUnion'_proper {i o}
         (dot: CarrierA -> CarrierA -> CarrierA)
         `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
    : Proper ((=) ==> (=) ==> (=) ==> (=)) (HTSUMUnion' (i:=i) (o:=o) dot).
  Proof.
    intros f f' Ef g g' Eg x y Ex.
    unfold HTSUMUnion'.
    unfold Vec2Union.
    vec_index_equiv j jp.
    rewrite 2!Vnth_map2.
    setoid_replace (Vnth (f x) jp) with (Vnth (f' y) jp).
    setoid_replace (Vnth (g x) jp) with (Vnth (g' y) jp).
    reflexivity.
    - apply Vnth_arg_equiv.
      apply Eg, Ex.
    - apply Vnth_arg_equiv.
      apply Ef, Ex.
  Qed.

  Global Instance HTSUMUnion'_arg_proper {i o}
         (op1: svector fm i -> svector fm o)
         `{op1_proper: !Proper ((=) ==> (=)) op1}
         (op2: svector fm i -> svector fm o)
         `{op2_proper: !Proper ((=) ==> (=)) op2}
         (dot: CarrierA -> CarrierA -> CarrierA)
         `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
    : Proper ((=) ==> (=)) (HTSUMUnion' (i:=i) (o:=o) dot op1 op2).
  Proof.
    partial_application_tactic. instantiate (1 := equiv).
    partial_application_tactic. instantiate (1 := equiv).
    apply HTSUMUnion'_proper.
    - apply dot_mor.
    - apply op1_proper.
    - apply op2_proper.
  Qed.

  Definition HTSUMUnion {i o}
             (dot: CarrierA -> CarrierA -> CarrierA)
             `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
             (op1 op2: @SHOperator fm i o)
    : @SHOperator fm i o
    :=
      mkSHOperator fm i o (HTSUMUnion' dot (op fm op1) (op fm op2))
                   (@HTSUMUnion'_arg_proper i o
                                            (op fm op1) (op_proper fm op1)
                                            (op fm op2) (op_proper fm op2)
                                            dot dot_mor)
                   (Ensembles.Union _ (in_index_set _ op1) (in_index_set _ op2))
                   (Ensembles.Union _ (out_index_set _ op1) (out_index_set _ op2)).

  Global Instance HTSUMUnion_proper
         {i o}
         (dot: CarrierA -> CarrierA -> CarrierA)
         `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
    : Proper ((=) ==> (=) ==> (=))
             (@HTSUMUnion i o dot dot_mor).
  Proof.
    intros x x' Ex y y' Ey.
    unfold HTSUMUnion.
    unfold equiv, SHOperator_equiv in *.
    destruct x, y, x', y'.
    simpl in *.
    apply HTSUMUnion'_proper; assumption.
  Qed.

End TSigmaHCOLOperators.

End TSigmaHCOL.

End Spiral.

End Spiral_DOT_TSigmaHCOL.


Module Spiral_DOT_MonoidalRestriction.
Module Spiral.
Module MonoidalRestriction.
Import Spiral_DOT_StructTactics.
Import Spiral_DOT_SpiralTactics.
Import Spiral_DOT_Spiral.
Import Spiral_DOT_VecUtil.
Import Spiral_DOT_VecSetoid.
Import Spiral_DOT_CarrierType.
Import Spiral_DOT_WriterMonadNoT.
Import Spiral_DOT_Rtheta.
Import Spiral_DOT_SVector.
Import Spiral_DOT_HCOLImpl.
Import Spiral_DOT_HCOL.
Import Spiral_DOT_THCOLImpl.
Import Spiral_DOT_THCOL.
Import Spiral_DOT_FinNatSet.
Import Spiral_DOT_IndexFunctions.
Import Spiral_DOT_SigmaHCOL.
Import Spiral_DOT_TSigmaHCOL.
Import Spiral_DOT_TSigmaHCOL.Spiral.
Import Spiral_DOT_SigmaHCOL.Spiral.
Import Spiral_DOT_IndexFunctions.Spiral.
Import Spiral_DOT_FinNatSet.Spiral.
Import Spiral_DOT_THCOL.Spiral.
Import Spiral_DOT_THCOLImpl.Spiral.
Import Spiral_DOT_HCOL.Spiral.
Import Spiral_DOT_HCOLImpl.Spiral.
Import Spiral_DOT_SVector.Spiral.
Import Spiral_DOT_Rtheta.Spiral.
Import Spiral_DOT_WriterMonadNoT.Spiral.
Import Spiral_DOT_CarrierType.Spiral.
Import Spiral_DOT_VecSetoid.Spiral.
Import Spiral_DOT_VecUtil.Spiral.
Import Spiral_DOT_Spiral.Spiral.
Import Spiral_DOT_SpiralTactics.Spiral.
Import Spiral_DOT_StructTactics.Spiral.
Import MathClasses.interfaces.abstract_algebra.


Section MonoidalRestriction.
  Context A {Ae : Equiv A}.

  (* Predicate on type [A] *)
  Class SgPred A := sg_P: A → Prop.

  (* Restriction of monoid operator and unit values *)
  Class MonRestriction {Aop : SgOp A} {Aunit : MonUnit A} {Apred: SgPred A}: Prop :=
    { rmonoid_unit_P: sg_P mon_unit
      ; rmonoid_plus_closed: forall a b, sg_P a -> sg_P b -> sg_P (a & b)
    }.

  Class RMonoid {Aop : SgOp A} {Aunit : MonUnit A} {Apred: SgPred A} :=
    {  sg_setoid :> Setoid A
       ; mon_restriction :> MonRestriction
       ; rsg_op_proper :> Proper ((=) ==> (=) ==> (=)) (&)

       ; rmonoid_ass: forall x y z,
           sg_P x -> sg_P y -> sg_P z -> x & (y & z) = (x & y) & z
       ; rmonoid_left_id : forall y, sg_P y -> mon_unit & y = y
       ; rmonoid_right_id : forall x, sg_P x -> x & mon_unit = x
    }.
  
  Class CommutativeRMonoid {Aop Aunit Ares} : Prop :=
    {
      comrmonoid_rmon :> @RMonoid Aop Aunit Ares
      ; rcommutativity: forall x y, sg_P x -> sg_P y -> x & y = y & x
    }.

End MonoidalRestriction.

Arguments rsg_op_proper {A Ae Aop Aunit Apred RMonoid}.


End MonoidalRestriction.

End Spiral.

End Spiral_DOT_MonoidalRestriction.

Module Spiral_DOT_VecPermutation.
Module Spiral.
Module VecPermutation.
Import Spiral_DOT_StructTactics.
Import Spiral_DOT_SpiralTactics.
Import Spiral_DOT_Spiral.
Import Spiral_DOT_VecUtil.
Import Spiral_DOT_VecSetoid.
Import Spiral_DOT_CarrierType.
Import Spiral_DOT_WriterMonadNoT.
Import Spiral_DOT_Rtheta.
Import Spiral_DOT_SVector.
Import Spiral_DOT_HCOLImpl.
Import Spiral_DOT_HCOL.
Import Spiral_DOT_THCOLImpl.
Import Spiral_DOT_THCOL.
Import Spiral_DOT_FinNatSet.
Import Spiral_DOT_IndexFunctions.
Import Spiral_DOT_SigmaHCOL.
Import Spiral_DOT_TSigmaHCOL.
Import Spiral_DOT_MonoidalRestriction.
Import Spiral_DOT_MonoidalRestriction.Spiral.
Import Spiral_DOT_TSigmaHCOL.Spiral.
Import Spiral_DOT_SigmaHCOL.Spiral.
Import Spiral_DOT_IndexFunctions.Spiral.
Import Spiral_DOT_FinNatSet.Spiral.
Import Spiral_DOT_THCOL.Spiral.
Import Spiral_DOT_THCOLImpl.Spiral.
Import Spiral_DOT_HCOL.Spiral.
Import Spiral_DOT_HCOLImpl.Spiral.
Import Spiral_DOT_SVector.Spiral.
Import Spiral_DOT_Rtheta.Spiral.
Import Spiral_DOT_WriterMonadNoT.Spiral.
Import Spiral_DOT_CarrierType.Spiral.
Import Spiral_DOT_VecSetoid.Spiral.
Import Spiral_DOT_VecUtil.Spiral.
Import Spiral_DOT_Spiral.Spiral.
Import Spiral_DOT_SpiralTactics.Spiral.
Import Spiral_DOT_StructTactics.Spiral.
Import Coq.Arith.Arith.
Export Coq.Vectors.Vector.
Import Coq.Program.Equality. (* for dependent induction *)
Import Coq.Setoids.Setoid.
Import Coq.Logic.ProofIrrelevance.


(* CoLoR: `opam install coq-color`  *)
Export CoLoR.Util.Vector.VecUtil.

Open Scope vector_scope.

(* Re-define :: List notation for vectors. Probably not such a good idea *)
Notation "h :: t" := (cons h t) (at level 60, right associativity)
                     : vector_scope.

Import VectorNotations.

Section VPermutation.

  Variable A:Type.

  Inductive VPermutation: forall n, vector A n -> vector A n -> Prop :=
  | vperm_nil: VPermutation 0 [] []
  | vperm_skip {n} x l l' : VPermutation n l l' -> VPermutation (S n) (x::l) (x::l')
  | vperm_swap {n} x y l : VPermutation (S (S n)) (y::x::l) (x::y::l)
  | vperm_trans {n} l l' l'' :
      VPermutation n l l' -> VPermutation n l' l'' -> VPermutation n l l''.

  Local Hint Constructors VPermutation.

  (** Some facts about [VPermutation] *)

  Theorem VPermutation_nil : forall (l : vector A 0), VPermutation 0 [] l -> l = [].
Admitted.

  (** VPermutation over vectors is a equivalence relation *)

  Theorem VPermutation_refl : forall {n} (l: vector A n), VPermutation n l l.
Admitted.

  Theorem VPermutation_sym : forall {n} (l l' : vector A n),
      VPermutation n l l' -> VPermutation n l' l.
Admitted.

  Theorem VPermutation_trans : forall {n} (l l' l'' : vector A n),
      VPermutation n l l' -> VPermutation n l' l'' -> VPermutation n l l''.
Admitted.

End VPermutation.

Hint Resolve VPermutation_refl vperm_nil vperm_skip.

(* These hints do not reduce the size of the problem to solve and they
   must be used with care to avoid combinatoric explosions *)

Local Hint Resolve vperm_swap vperm_trans.
Local Hint Resolve VPermutation_sym VPermutation_trans.

(* This provides reflexivity, symmetry and transitivity and rewriting
   on morphims to come *)

Instance VPermutation_Equivalence A n : Equivalence (@VPermutation A n) | 10 :=
  {
    Equivalence_Reflexive := @VPermutation_refl A n ;
    Equivalence_Symmetric := @VPermutation_sym A n ;
    Equivalence_Transitive := @VPermutation_trans A n
  }.

Section VPermutation_properties.
Import Coq.Sorting.Permutation.
Import Spiral_DOT_VecUtil.Spiral.VecUtil.


  Variable A:Type.

  Lemma ListVecPermutation {n} {l1 l2} {v1 v2}:
    l1 = list_of_vec v1 ->
    l2 = list_of_vec v2 ->
    Permutation l1 l2 <->
    VPermutation A n v1 v2.
Admitted.

End VPermutation_properties.

Require Import Coq.Sorting.Permutation.

Lemma Vsig_of_forall_cons
      {A : Type}
      {n : nat}
      (P : A->Prop)
      (x : A)
      (l : vector A n)
      (P1h : P x)
      (P1x : @Vforall A P n l):
  (@Vsig_of_forall A P (S n) (@cons A x n l) (@conj (P x) (@Vforall A P n l) P1h P1x)) =
  (Vcons (@exist A P x P1h) (Vsig_of_forall P1x)).
Admitted.

Lemma VPermutation_Vsig_of_forall
      {n: nat}
      {A: Type}
      (P: A->Prop)
      (v1 v2 : vector A n)
      (P1 : Vforall P v1)
      (P2 : Vforall P v2):
  VPermutation A n v1 v2
  -> VPermutation {x : A | P x} n (Vsig_of_forall P1) (Vsig_of_forall P2).
Admitted.


End VecPermutation.

End Spiral.

End Spiral_DOT_VecPermutation.

Module Spiral_DOT_SigmaHCOLRewriting.
Module Spiral.
Module SigmaHCOLRewriting.
Import Spiral_DOT_StructTactics.
Import Spiral_DOT_SpiralTactics.
Import Spiral_DOT_Spiral.
Import Spiral_DOT_VecUtil.
Import Spiral_DOT_VecSetoid.
Import Spiral_DOT_CarrierType.
Import Spiral_DOT_WriterMonadNoT.
Import Spiral_DOT_Rtheta.
Import Spiral_DOT_SVector.
Import Spiral_DOT_HCOLImpl.
Import Spiral_DOT_HCOL.
Import Spiral_DOT_THCOLImpl.
Import Spiral_DOT_THCOL.
Import Spiral_DOT_FinNatSet.
Import Spiral_DOT_IndexFunctions.
Import Spiral_DOT_SigmaHCOL.
Import Spiral_DOT_TSigmaHCOL.
Import Spiral_DOT_MonoidalRestriction.
Import Spiral_DOT_VecPermutation.
Import Spiral_DOT_VecPermutation.Spiral.
Import Spiral_DOT_MonoidalRestriction.Spiral.
Import Spiral_DOT_TSigmaHCOL.Spiral.
Import Spiral_DOT_SigmaHCOL.Spiral.
Import Spiral_DOT_IndexFunctions.Spiral.
Import Spiral_DOT_FinNatSet.Spiral.
Import Spiral_DOT_THCOL.Spiral.
Import Spiral_DOT_THCOLImpl.Spiral.
Import Spiral_DOT_HCOL.Spiral.
Import Spiral_DOT_HCOLImpl.Spiral.
Import Spiral_DOT_SVector.Spiral.
Import Spiral_DOT_Rtheta.Spiral.
Import Spiral_DOT_WriterMonadNoT.Spiral.
Import Spiral_DOT_CarrierType.Spiral.
Import Spiral_DOT_VecSetoid.Spiral.
Import Spiral_DOT_VecUtil.Spiral.
Import Spiral_DOT_Spiral.Spiral.
Import Spiral_DOT_SpiralTactics.Spiral.
Import Spiral_DOT_StructTactics.Spiral.

Global Generalizable All Variables.
Import Spiral_DOT_VecUtil.Spiral.VecUtil.
Import Spiral_DOT_Spiral.Spiral.Spiral.
Import Spiral_DOT_Rtheta.Spiral.Rtheta.
Import Spiral_DOT_VecSetoid.Spiral.VecSetoid.
Import Spiral_DOT_SVector.Spiral.SVector.
Import Spiral_DOT_HCOL.Spiral.HCOL.
Import Spiral_DOT_THCOL.Spiral.THCOL.
Import Spiral_DOT_SigmaHCOL.Spiral.SigmaHCOL.
Import Spiral_DOT_TSigmaHCOL.Spiral.TSigmaHCOL.
Import Spiral_DOT_IndexFunctions.Spiral.IndexFunctions.
Import Spiral_DOT_MonoidalRestriction.Spiral.MonoidalRestriction.
Import Spiral_DOT_VecPermutation.Spiral.VecPermutation.
Import Coq.Arith.Arith.
Import Coq.Arith.Compare_dec.
Import Coq.Arith.Peano_dec.
Import Coq.Logic.Eqdep_dec.
Import Coq.Logic.ProofIrrelevance.
Import Coq.Program.Program.
Import Coq.Logic.FunctionalExtensionality.
Import Coq.micromega.Psatz.
Import Coq.omega.Omega.
Import Spiral_DOT_SpiralTactics.Spiral.SpiralTactics.

(* CoRN Math-classes *)
Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders.
Import MathClasses.orders.minmax MathClasses.orders.orders MathClasses.orders.rings.
Import MathClasses.theory.rings MathClasses.theory.abs.
Import MathClasses.theory.setoids.

(* ExtLib *)
Import ExtLib.Structures.Monoid.
Import Monoid.

(*  CoLoR *)

Import VectorNotations.

Local Open Scope vector_scope.
Local Open Scope nat_scope.

Section SigmaHCOLHelperLemmas.

  Variable fm:Monoid RthetaFlags.
  Variable fml:@MonoidLaws RthetaFlags RthetaFlags_type fm.

  Lemma Gather'_composition
        {i o t: nat}
        (f: index_map o t)
        (g: index_map t i):
    Gather' fm f ∘ Gather' fm g = Gather' fm (index_map_compose g f).
Admitted.

  Lemma Scatter'_composition
        {i o t: nat}
        (f: index_map i t)
        (g: index_map t o)
        {f_inj: index_map_injective f}
        {g_inj: index_map_injective g}
        (idv: CarrierA):
    Scatter' fm g (f_inj:=g_inj) idv ∘ Scatter' fm f (f_inj:=f_inj) idv
    = Scatter' fm (index_map_compose g f) (f_inj:=index_map_compose_injective g f g_inj f_inj) idv.
Admitted.

  Lemma LiftM_Hoperator_compose
        {i1 o2 o3: nat}
        `{HOperator o2 o3 op1}
        `{HOperator i1 o2 op2}
    :
      liftM_HOperator fm (op1 ∘ op2) =
      SHCompose fm
                (liftM_HOperator fm op1)
                (liftM_HOperator fm op2).
Admitted.

  Fact ScatH_stride1_constr:
  forall {a b:nat}, 1 ≢ 0 ∨ a < b.
Admitted.

  Fact h_bound_first_half (o1 o2:nat):
    ∀ x : nat, x < o1 → 0 + x * 1 < o1 + o2.
Admitted.

  Fact h_bound_second_half (o1 o2:nat):
    ∀ x : nat, x < o2 → o1 + x * 1 < o1 + o2.
Admitted.

  Fact ScatH_1_to_n_range_bound base o stride:
    base < o ->
    ∀ x : nat, x < 1 → base + x * stride < o.
Admitted.

  Fact GathH_j1_domain_bound base i (bc:base<i):
    ∀ x : nat, x < 1 → base + x * 1 < i.
Admitted.

  Lemma UnionFold_a_zero_structs
        (m : nat)
        (x : svector fm m)
        `{uf_zero: MonUnit CarrierA}
        `{f: SgOp CarrierA}
        `{f_mor: !Proper ((=) ==> (=) ==> (=)) f}
        `{f_left_id : @LeftIdentity CarrierA CarrierA CarrierAe
                                    (@sg_op CarrierA f) (@mon_unit CarrierA uf_zero)}
    :
      Vforall (Is_ValX uf_zero) x → Is_ValX uf_zero (UnionFold fm f uf_zero x).
Admitted.

  (* Specialized version of [UnionFold_a_zero_structs]. *)
  Lemma UnionFold_zero_structs
        (m : nat) (x : svector fm m):
    Vforall Is_ValZero x → Is_ValZero (UnionFold fm plus zero x).
Admitted.

  Lemma UnionFold_VallButOne_a_zero
        {n : nat}
        (v : svector fm n)
        {i : nat}
        (ic : i < n)

        `{uf_zero: MonUnit CarrierA}
        `{f: SgOp CarrierA}
        `{f_mor: !Proper ((=) ==> (=) ==> (=)) f}
        `{f_left_id : @LeftIdentity CarrierA CarrierA CarrierAe
                                    (@sg_op CarrierA f) (@mon_unit CarrierA uf_zero)}
        `{f_right_id : @RightIdentity CarrierA CarrierAe CarrierA
                                      (@sg_op CarrierA f) (@mon_unit CarrierA uf_zero)}
    :
      VAllButOne i ic
                 (not ∘ (not ∘ equiv uf_zero ∘ WriterMonadNoT.evalWriter (Monoid_W:=fm))) v -> UnionFold fm f uf_zero v = Vnth v ic.
Admitted.


  (* Specialized version of [UnionFold_VallButOne_a_zero]. *)
  Lemma UnionFold_VallButOne_zero:
    ∀ {n : nat} (v : svector fm n) {k : nat} (kc : k < n),
      VAllButOne k kc (Is_ValZero) v → UnionFold fm plus zero v = Vnth v kc.
Admitted.


  (* Formerly Lemma3. Probably will be replaced by UnionFold_VallButOne *)
  Lemma SingleValueInZeros
        {m} (x:svector fm m) j (jc:j<m):
    (forall i (ic:i<m), i ≢ j -> Is_ValZero (Vnth x ic)) -> (UnionFold fm plus zero x = Vnth x jc).
Admitted.


  Fact GathH_jn_domain_bound i n:
    i < n ->
    ∀ x : nat, x < 2 → i + x * n < (n+n).
Admitted.

End SigmaHCOLHelperLemmas.



Section SigmaHCOLExpansionRules.
  Section Value_Correctness.

    Lemma h_j_1_family_injective {n}:
      index_map_family_injective
        (IndexMapFamily 1 n n (fun j jc => h_index_map j 1 (range_bound := (ScatH_1_to_n_range_bound _ _ j n 1 jc)))).
Admitted.


    (* TODO: should be deriavale from 'h_j_1_family_injective' and 'index_map_family_member_injective' *)
    Lemma h_j_1_family_member_injective {n}:
      forall t (tc:t<n),
        @index_map_injective 1 n
                             ((fun (j:nat) (jc:j<n) =>
                                 @h_index_map 1 n j 1 (ScatH_1_to_n_range_bound _ _ j n (S O) jc)) t tc).
Admitted.

  End Value_Correctness.


End SigmaHCOLExpansionRules.

Section SigmaHCOLRewritingRules.
  Section Value_Correctness.

    Local Notation "g ⊚ f" := (@SHCompose Monoid_RthetaFlags _ _ _ g f) (at level 40, left associativity) : type_scope.

    Lemma RStheta2Rtheta_Vfold_left_rev_mkValue
          {n:nat}
          {v:rsvector n}
          {f: CarrierA -> CarrierA -> CarrierA}
          {initial: CarrierA}
          `{f_mor: !Proper ((=) ==> (=) ==> (=)) f}
      :
        RStheta2Rtheta
          (Vfold_left_rev (Union Monoid_RthetaSafeFlags f) (mkStruct initial) v) =
        mkValue
          (Vfold_left_rev f initial (densify _ v)).
Admitted.

    Fact UnionFold_all_zeroes
         {n:nat}
         `{uf_zero: MonUnit CarrierA}
         `{f: SgOp CarrierA}
         `{f_mor: !Proper ((=) ==> (=) ==> (=)) f}
         `{f_left_id : @LeftIdentity CarrierA CarrierA CarrierAe
                                     (@sg_op CarrierA f) (@mon_unit CarrierA uf_zero)}

         (vl : vector (Rtheta' Monoid_RthetaFlags) n)
         (Uzeros : Vforall
                     (not
                        ∘ (not ∘ equiv uf_zero
                               ∘ WriterMonadNoT.evalWriter (Monoid_W:=Monoid_RthetaFlags))) vl)
      :
        UnionFold Monoid_RthetaFlags f uf_zero vl = mkStruct uf_zero.
Admitted.

    (* Basically states that 'Diamon' applied to a family which guarantees
       single-non zero value per row dows not depend on the function implementation *)
    Lemma Diamond'_f_subst
          {i o n}
          (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n)

          (* Common unit for both monoids *)
          `{uf_zero: MonUnit CarrierA}

          (* 1st Monoid. Used in reduction *)
          `{f: SgOp CarrierA}
          `{f_mon: @MathClasses.interfaces.abstract_algebra.CommutativeMonoid _ _ f uf_zero}
          (* 2nd Monoid. Used in IUnion *)
          `{u: SgOp CarrierA}
          `{u_mon: @MathClasses.interfaces.abstract_algebra.CommutativeMonoid _ _ u uf_zero}
      :
        Apply_Family_Single_NonUnit_Per_Row _ op_family uf_zero
        ->
        Diamond' f uf_zero (get_family_op Monoid_RthetaFlags op_family) =
        Diamond' u uf_zero (get_family_op Monoid_RthetaFlags op_family).
Admitted.


    (* An unfortunatly named section for a group on lemmas related to operations on a type constrained by predicate. *)
    Section Under_P.

      Fact UnionFold_all_zeroes_under_P
           {fm}
           {n:nat}
           `{uf_zero: MonUnit CarrierA}
           `{f: SgOp CarrierA}
           (vl : vector (Rtheta' fm) n)

           (* Monoid on restriction on f *)
           {P: SgPred CarrierA}
           `{f_mon: @RMonoid _ _ f uf_zero P}

           `{Fpos: Vforall (liftRthetaP P) vl}

           (Uzeros : Vforall
                       (not
                          ∘ (not ∘ equiv uf_zero
                                 ∘ WriterMonadNoT.evalWriter (Monoid_W:=fm))) vl)
      :
        UnionFold fm f uf_zero vl = mkStruct uf_zero.
Admitted.

      (* A variant of [UnionFold_VallButOne_a_zero] taking into account restriction *)
      Lemma UnionFold_VallButOne_a_zero_under_P
            {fm}
            {n : nat}
            (v : svector fm n)
            {i : nat}
            (ic : i < n)

            `{uf_zero: MonUnit CarrierA}
            `{f: SgOp CarrierA}

            (* Monoid on restriction on f *)
            {P: SgPred CarrierA}
            `{f_mon: @RMonoid _ _ f uf_zero P}

            `{Fpos: Vforall (liftRthetaP P) v}
        :
          VAllButOne i ic
                     (not ∘ (not ∘ equiv uf_zero ∘ WriterMonadNoT.evalWriter (Monoid_W:=fm))) v -> UnionFold fm f uf_zero v = Vnth v ic.
Admitted.

      Lemma Diamond'_f_subst_under_P
            {i o n}
            (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n)

            (* Common unit for both monoids *)
            `{uf_zero: MonUnit CarrierA}

            `{f: SgOp CarrierA}

            (* Monoid on restriction on f *)
            {P: SgPred CarrierA}
            `{f_mon: @RMonoid _ _ f uf_zero P}

            (* 2nd Monoid *)
            `{u: SgOp CarrierA}
            `{u_mon: @MathClasses.interfaces.abstract_algebra.CommutativeMonoid _ _ u uf_zero}

            (Upoz: Apply_Family_Vforall_P _ (liftRthetaP P) op_family)
            (Uz: Apply_Family_Single_NonUnit_Per_Row _ op_family uf_zero)
        :
          Diamond' f uf_zero (get_family_op Monoid_RthetaFlags op_family) =
          Diamond' u uf_zero (get_family_op Monoid_RthetaFlags op_family).
Admitted.

      Fact eval_2D_Fold
           {o n : nat}
           (uf_zero : CarrierA)
           (f : CarrierA -> CarrierA -> CarrierA)
           (f_mor : Proper (equiv ==> equiv ==> equiv) f)
           (lst : vector (rvector o) n)
        :
          Vmap (WriterMonadNoT.evalWriter (Monoid_W:=Monoid_RthetaFlags))
               (Vfold_left_rev (Vmap2 (Monad.liftM2 f) (n:=o))
                               (Vconst (mkStruct uf_zero) o)
                               lst)
          =
          Vfold_left_rev (Vmap2 f (n:=o)) (Vconst uf_zero o)
                         (Vmap (Vmap (WriterMonadNoT.evalWriter (Monoid_W:=Monoid_RthetaFlags)) (n:=o)) lst).
Admitted.

      Lemma Vfold_right_under_P
            {A: Type} `{Ae: Equiv A}
            {z: MonUnit A}
            {f: SgOp A}
            (P: SgPred A)
            {f_mon: @CommutativeRMonoid _ _ f z P}
            {n:nat}
            (v:vector A n):
        Vforall P v → P (Vfold_right f v z).
Admitted.

      Lemma Vfold_right_left_rev_under_P
            {A: Type} `{Ae: Equiv A}
            {z: MonUnit A}
            {f: SgOp A}
            (P: SgPred A)
            {f_mon: @CommutativeRMonoid _ _ f z P}
            {n:nat}
            (v:vector A n)
            (U: Vforall P v):
        Vfold_left_rev f z v = Vfold_right f v z.
Admitted.

      Lemma VFold_right_split_under_P
            {A: Type}
            {Ae: Equiv A}
            {m n : nat}
            {z: MonUnit A}
            {f: SgOp A}
            (P: SgPred A)
            {f_mon: @CommutativeRMonoid _ _ f z P}
            (h : vector A m)
            (t : vector A n)
            (Uh: Vforall P h)
            (Ut: Vforall P t)
        :
          f (Vfold_right f h z)
            (Vfold_right f t z)
          =
          Vfold_right f (Vapp h t) z.
Admitted.

    End Under_P.


    (* TODO: move this and other helper lemmas to SigmaHCOLHelperLemmas section above *)
    Section VecMap2CommutativeRMonoid.

      Variable n:nat.
      Variable A: Type.
      Variable Ae: Equiv A.
      Variable As: @Setoid A Ae.
      Variable z: MonUnit A.
      Variable f: SgOp A.
      Variable P: SgPred A.

      Global Instance VecMonRestrictionMap2
             {f_mon: @MonRestriction A f z P}:
        @MonRestriction
          (vector A n)
          (Vmap2 f (n:=n))
          (Vconst z n)
          (Vforall P (n:=n)).
      Proof.
        split.
        +
          unfold sg_P, mon_unit.
          apply Vforall_Vconst.
          apply f_mon.
        +
          intros a b Ha Hb.
          apply Vforall_Vmap2.
          apply f_mon.
          apply Ha.
          apply Hb.
      Qed.

      Global Instance VecRMonoidMap2
             {f_mon: @RMonoid A Ae f z P}
        :
          @RMonoid
            (vector A n)
            (=)
            (Vmap2 f (n:=n))
            (Vconst z n)
            (Vforall P (n:=n)).
      Proof.
        split; try typeclasses eauto.
        +
          intros a b c Ha Hb Hc.
          unfold sg_op.
          vec_index_equiv j jc.
          repeat rewrite Vnth_map2.
          destruct f_mon.
          apply rmonoid_ass0.
          apply Vforall_nth, Ha.
          apply Vforall_nth, Hb.
          apply Vforall_nth, Hc.
        +
          intros y H.
          unfold sg_op.
          vec_index_equiv j jc.
          rewrite Vnth_map2.
          destruct f_mon.
          unfold mon_unit. rewrite Vnth_const.
          apply rmonoid_left_id0.
          apply Vforall_nth, H.
        +
          intros y H.
          unfold sg_op.
          vec_index_equiv j jc.
          rewrite Vnth_map2.
          destruct f_mon.
          unfold mon_unit. rewrite Vnth_const.
          apply rmonoid_right_id0.
          apply Vforall_nth, H.
      Qed.

      Global Instance VecCommutativeRMonoidMap2
             {f_mon: @CommutativeRMonoid A Ae f z P}
        :
          @CommutativeRMonoid
            (vector A n)
            (=)
            (Vmap2 f (n:=n))
            (Vconst z n)
            (Vforall P (n:=n)).
      Admitted.

    End VecMap2CommutativeRMonoid.

    Fact Vhead_Vfold_right_Vmap2
         {A:Type}
         (m n : nat)
         (z : A)
         (f : A -> A -> A)
         (gen : forall p : nat, p < n → vector A (S m))
         (tmn : ∀ t : nat, t < S m * n → t mod n < n)
         (tndm : ∀ t : nat, t < S m * n → t / n < S m)
      :
        Vhead
          (Vfold_right
             (λ v1 v2 : vector A (S m),
                        Vcons (f (Vhead v1) (Vhead v2)) (Vmap2 f (Vtail v1) (Vtail v2)))
             (Vbuild gen) (Vcons z (Vconst z m)))
          ≡ Vfold_right f
          (Vbuild
             (λ (t : nat) (tc : t < n),
              Vnth (gen (t mod n) (tmn t (Nat.lt_lt_add_r t n (m * n) tc)))
                   (tndm t (Nat.lt_lt_add_r t n (m * n) tc)))) z.
Admitted.


    Lemma Vtail_Vfold_right_Vmap2
          {A:Type}
          (m n : nat)
          (z : A)
          (f : A -> A -> A)
          (gen : ∀ p : nat, p < n → vector A (S m)):
      Vtail
        (Vfold_right
           (λ v1 v2 : vector A (S m),
                      Vcons (f (Vhead v1) (Vhead v2)) (Vmap2 f (Vtail v1) (Vtail v2)))
           (Vbuild gen) (Vcons z (Vconst z m)))
        ≡ Vfold_right (Vmap2 f (n:=m)) (Vbuild (λ (p : nat) (pc : p < n), Vtail (gen p pc)))
        (Vconst z m).
Admitted.


    Section Vec_Permutations.
      (* TODO: think of good place to move this. Depdens on both [IndexFunctions] and [VecPermutation] *)
      Lemma Vbuild_permutation
            {A: Type}
            {n: nat}
            {f: forall i : nat, i < n -> A}
            (t: index_map n n)
            (P: index_map_bijective t)
      :
        VPermutation A n (Vbuild f) (Vbuild (fun i ic =>
                                               f (⟦t⟧ i) («t» i ic)
                                    )).
Admitted.

      Lemma Vfold_VPermutation
            {n : nat}
            {A: Type} `{Ae: Equiv A}
            (z : MonUnit A)
            (f : SgOp A)
            (f_mon: CommutativeMonoid A):
        forall v1 v2 : vector A n,
          VPermutation A n v1 v2 → Vfold_right f v1 z = Vfold_right f v2 z.
Admitted.

    End Vec_Permutations.

    Lemma Vold_right_sig_wrap_equiv
          {n : nat}
          {A : Type}
          `{As: Setoid A}
          (f : A → A → A)
          {f_mor: Proper (equiv ==> equiv ==> equiv) f}
          (P : A → Prop)
          (f_P_closed: forall a b : A, P a → P b → P (f a b))
          (v : vector A n) (P1 : Vforall P v)
          (z : A) (Pz: P z):
      Vfold_right f v z =
      `
        (Vfold_right
           (λ xs ys : {x : A | P x},
                      f (` xs) (` ys) ↾ f_P_closed (` xs) (` ys) (proj2_sig xs) (proj2_sig ys))
           (Vsig_of_forall P1) (z ↾ Pz)).
Admitted.

    Lemma ComutativeRMonoid_to_sig_CommutativeMonoid
          {A : Type}
          {Ae: Equiv A}
          {As: @Setoid A Ae}
          (z : MonUnit A)
          (f : SgOp A)
          (P : SgPred A)
          (CMR: @CommutativeRMonoid A Ae f z P)
      :
        @CommutativeMonoid {x : A | P x} (@Sig_Equiv A Ae P)
                           (λ (xs ys : {x : A | P x}) (x:=` xs) (y:=` ys),
                            f x y ↾ rmonoid_plus_closed A x y (@proj2_sig A P xs) (@proj2_sig A P ys))
                           (z ↾ (rmonoid_unit_P _)).
Admitted.

    Lemma Vfold_VPermutation_CM
          {n : nat}
          {A: Type}
          `{As: Setoid A}
          (z : MonUnit A)
          (f : SgOp A)
          (P : SgPred A)
          (f_mon: CommutativeRMonoid A)
          (v1 v2 : vector A n)
          (P1: Vforall P v1)
          (P2: Vforall P v2):
      VPermutation A n v1 v2 -> Vfold_right f v1 z = Vfold_right f v2 z.
Admitted.

    Global Instance max_Assoc:
      @Associative CarrierA CarrierAe (@max CarrierA CarrierAle CarrierAledec).
    Admitted.

    Global Instance max_Comm:
      @Commutative CarrierA CarrierAe CarrierA (@max CarrierA CarrierAle CarrierAledec).
    Admitted.

    Section NN.
      (* Non-negative CarrierA subtype *)

      Global Instance NN:
        SgPred CarrierA := CarrierAle CarrierAz.

      Global Instance RMonoid_max_NN:
        @RMonoid CarrierA CarrierAe (@max CarrierA CarrierAle CarrierAledec) CarrierAz NN.
      Proof.
      Admitted.

      Global Instance CommutativeRMonoid_max_NN:
        @CommutativeRMonoid CarrierA CarrierAe (@minmax.max CarrierA CarrierAle CarrierAledec) CarrierAz NN.
      Proof.
      Admitted.

    End NN.

    Lemma SHPointwise'_distr_over_Scatter'
          {fm : Monoid RthetaFlags}
          {o i : nat}
          (pf : CarrierA → CarrierA)
          (pf_mor : Proper (equiv ==> equiv) pf)
          (pfzn: pf zero = zero) (* function with the fixed point 0 *)
          (v : svector fm i)
          (f : index_map i o)
          (f_inj : index_map_injective f):
      SHPointwise' fm (IgnoreIndex pf) (Scatter' fm f zero (f_inj:=f_inj) v) =
      Scatter' fm f zero (SHPointwise' fm (IgnoreIndex pf) v) (f_inj:=f_inj).
Admitted.

    Lemma rewrite_Reduction_ScatHUnion_max_zero
          (n m: nat)
          (fm: Monoid.Monoid RthetaFlags)
          (F: @SHOperator fm m 1)
          (f: index_map 1 (S n))
          (f_inj: index_map_injective f)
          (FP: op_Vforall_P fm Is_NonNegative F)

      :
        SHCompose fm
                  (SHCompose fm
                             (liftM_HOperator fm (HReduction minmax.max zero))
                             (Scatter fm f zero (f_inj:=f_inj)))
                  F
        =
        F.
Admitted.

    Lemma rewrite_SHCompose_IdOp
          {n m: nat}
          {fm}
          (in_out_set: FinNatSet.FinNatSet n)
          (F: @SHOperator fm n m)
      :
      SHCompose fm
                F
                (IdOp fm in_out_set)
      =
      F.
Admitted.

  End Value_Correctness.

End SigmaHCOLRewritingRules.


End SigmaHCOLRewriting.

End Spiral.

End Spiral_DOT_SigmaHCOLRewriting.

Module Spiral_DOT_DynWin.
Module Spiral.
Module DynWin.
Import Spiral_DOT_StructTactics.
Import Spiral_DOT_SpiralTactics.
Import Spiral_DOT_Spiral.
Import Spiral_DOT_VecUtil.
Import Spiral_DOT_VecSetoid.
Import Spiral_DOT_CarrierType.
Import Spiral_DOT_WriterMonadNoT.
Import Spiral_DOT_Rtheta.
Import Spiral_DOT_SVector.
Import Spiral_DOT_HCOLImpl.
Import Spiral_DOT_HCOL.
Import Spiral_DOT_THCOLImpl.
Import Spiral_DOT_THCOL.
Import Spiral_DOT_FinNatSet.
Import Spiral_DOT_IndexFunctions.
Import Spiral_DOT_SigmaHCOL.
Import Spiral_DOT_TSigmaHCOL.
Import Spiral_DOT_MonoidalRestriction.
Import Spiral_DOT_VecPermutation.
Import Spiral_DOT_SigmaHCOLRewriting.
Import Spiral_DOT_SigmaHCOLRewriting.Spiral.
Import Spiral_DOT_VecPermutation.Spiral.
Import Spiral_DOT_MonoidalRestriction.Spiral.
Import Spiral_DOT_TSigmaHCOL.Spiral.
Import Spiral_DOT_SigmaHCOL.Spiral.
Import Spiral_DOT_IndexFunctions.Spiral.
Import Spiral_DOT_FinNatSet.Spiral.
Import Spiral_DOT_THCOL.Spiral.
Import Spiral_DOT_THCOLImpl.Spiral.
Import Spiral_DOT_HCOL.Spiral.
Import Spiral_DOT_HCOLImpl.Spiral.
Import Spiral_DOT_SVector.Spiral.
Import Spiral_DOT_Rtheta.Spiral.
Import Spiral_DOT_WriterMonadNoT.Spiral.
Import Spiral_DOT_CarrierType.Spiral.
Import Spiral_DOT_VecSetoid.Spiral.
Import Spiral_DOT_VecUtil.Spiral.
Import Spiral_DOT_Spiral.Spiral.
Import Spiral_DOT_SpiralTactics.Spiral.
Import Spiral_DOT_StructTactics.Spiral.
Import Spiral_DOT_VecUtil.Spiral.VecUtil.
Import Spiral_DOT_VecSetoid.Spiral.VecSetoid.
Import Spiral_DOT_SVector.Spiral.SVector.
Import Spiral_DOT_Spiral.Spiral.Spiral.
Import Spiral_DOT_CarrierType.Spiral.CarrierType.
Import Spiral_DOT_HCOL.Spiral.HCOL.
Import Spiral_DOT_HCOLImpl.Spiral.HCOLImpl.
Import Spiral_DOT_THCOL.Spiral.THCOL.
Import Spiral_DOT_THCOLImpl.Spiral.THCOLImpl.
Import Spiral_DOT_Rtheta.Spiral.Rtheta.
Import Spiral_DOT_SigmaHCOL.Spiral.SigmaHCOL.
Import Spiral_DOT_TSigmaHCOL.Spiral.TSigmaHCOL.
Import Spiral_DOT_IndexFunctions.Spiral.IndexFunctions.
Import Coq.Arith.Arith.
Import Coq.Arith.Compare_dec.
Import Coq.Arith.Peano_dec.
Import Spiral_DOT_SpiralTactics.Spiral.SpiralTactics.
Import Spiral_DOT_SigmaHCOLRewriting.Spiral.SigmaHCOLRewriting.
Import MathClasses.interfaces.canonical_names.


Section SigmaHCOL_rewriting.

  Local Notation "g ⊚ f" := (@SHCompose Monoid_RthetaFlags _ _ _ g f) (at level 40, left associativity) : type_scope.


Import Spiral_DOT_FinNatSet.Spiral.FinNatSet.


  Parameter dynwin_SHCOL1: (avector 3) -> @SHOperator Monoid_RthetaFlags (1+(2+2)) 1.

  Lemma Bug: forall a : vector CarrierA (S (S (S O))),
  @equiv (@SHOperator Monoid_RthetaFlags (S (S (S (S (S O))))) (S O))
    (@SHOperator_equiv Monoid_RthetaFlags (S (S (S (S (S O))))) (S O))
    (@SHCompose Monoid_RthetaFlags (S (S (S (S (S O))))) (S (S O))
       (S O)
       (@SafeCast (S (S O)) (S O)
          (@SHBinOp (S O) (@IgnoreIndex2 CarrierA Zless)
             (@Reflexive_partial_app_morphism
                (forall (_ : CarrierA) (_ : CarrierA), CarrierA)
                (forall (_ : nat) (_ : CarrierA) (_ : CarrierA), CarrierA)
                (@respectful CarrierA (forall _ : CarrierA, CarrierA)
                   (@equiv CarrierA CarrierAe)
                   (@equiv (forall _ : CarrierA, CarrierA)
                      (@ext_equiv CarrierA CarrierAe CarrierA CarrierAe)))
                (@respectful nat (forall (_ : CarrierA) (_ : CarrierA), CarrierA)
                   (@equiv nat peano_naturals.nat_equiv)
                   (@respectful CarrierA (forall _ : CarrierA, CarrierA)
                      (@equiv CarrierA CarrierAe)
                      (@respectful CarrierA CarrierA (@equiv CarrierA CarrierAe)
                         (@equiv CarrierA CarrierAe)))) (@IgnoreIndex2 CarrierA)
                (@IgnoreIndex2_proper CarrierA CarrierAe) Zless
                (@proper_proper_proxy (forall (_ : CarrierA) (_ : CarrierA), CarrierA)
                   Zless
                   (@respectful CarrierA (forall _ : CarrierA, CarrierA)
                      (@equiv CarrierA CarrierAe)
                      (@equiv (forall _ : CarrierA, CarrierA)
                         (@ext_equiv CarrierA CarrierAe CarrierA CarrierAe)))
                   Zless_proper))))
       (@HTSUMUnion Monoid_RthetaFlags (S (S (S (S (S O)))))
          (S (S O)) (@plus CarrierA CarrierAplus) CarrierAPlus_proper
          (@SHCompose Monoid_RthetaFlags (S (S (S (S (S O)))))
             (S O) (S (S O))
             (@SHCompose Monoid_RthetaFlags (S O) (S (S (S O)))
                (S (S O))
                (@SHCompose Monoid_RthetaFlags (S (S (S O)))
                   (S (S (S (S (S (S O)))))) (S (S O))
                   (@SHCompose Monoid_RthetaFlags (S (S (S (S (S (S O))))))
                      (S (S (S O))) (S (S O))
                      (@SHCompose Monoid_RthetaFlags (S (S (S O)))
                         (S O) (S (S O))
                         (@ScatH Monoid_RthetaFlags (S O) (S (S O)) O
                            (S O)
                            (h_bound_first_half Monoid_RthetaSafeFlags
                               MonoidLaws_SafeRthetaFlags (S O)
                               (S O))
                            (@ScatH_stride1_constr Monoid_RthetaSafeFlags
                               MonoidLaws_SafeRthetaFlags (S O)
                               (S (S O))) (@zero CarrierA CarrierAz))
                         (@liftM_HOperator Monoid_RthetaFlags
                            (S (S (S O))) (S O)
                            (@HReduction (S (S (S O))) (@plus CarrierA CarrierAplus)
                               CarrierAPlus_proper (@zero CarrierA CarrierAz))
                            (@HReduction_HOperator (S (S (S O)))
                               (@plus CarrierA CarrierAplus) CarrierAPlus_proper
                               (@zero CarrierA CarrierAz))))
                      (@SafeCast (S (S (S (S (S (S O)))))) (S (S (S O)))
                         (@SHBinOp (S (S (S O)))
                            (@IgnoreIndex2 CarrierA (@mult CarrierA CarrierAmult))
                            (@Reflexive_partial_app_morphism
                               (forall (_ : CarrierA) (_ : CarrierA), CarrierA)
                               (forall (_ : nat) (_ : CarrierA) (_ : CarrierA), CarrierA)
                               (@respectful CarrierA (forall _ : CarrierA, CarrierA)
                                  (@equiv CarrierA CarrierAe)
                                  (@equiv (forall _ : CarrierA, CarrierA)
                                     (@ext_equiv CarrierA CarrierAe CarrierA CarrierAe)))
                               (@respectful nat
                                  (forall (_ : CarrierA) (_ : CarrierA), CarrierA)
                                  (@equiv nat peano_naturals.nat_equiv)
                                  (@respectful CarrierA (forall _ : CarrierA, CarrierA)
                                     (@equiv CarrierA CarrierAe)
                                     (@respectful CarrierA CarrierA
                                        (@equiv CarrierA CarrierAe)
                                        (@equiv CarrierA CarrierAe))))
                               (@IgnoreIndex2 CarrierA)
                               (@IgnoreIndex2_proper CarrierA CarrierAe)
                               (@mult CarrierA CarrierAmult)
                               (@proper_proper_proxy
                                  (forall (_ : CarrierA) (_ : CarrierA), CarrierA)
                                  (@mult CarrierA CarrierAmult)
                                  (@respectful CarrierA (forall _ : CarrierA, CarrierA)
                                     (@equiv CarrierA CarrierAe)
                                     (@equiv (forall _ : CarrierA, CarrierA)
                                        (@ext_equiv CarrierA CarrierAe CarrierA CarrierAe)))
                                  (@abstract_algebra.sg_op_proper CarrierA CarrierAe
                                     CarrierAmult
                                     (@abstract_algebra.monoid_semigroup CarrierA
                                        CarrierAe CarrierAmult
                                        (@one_is_mon_unit CarrierA CarrierA1)
                                        (@abstract_algebra.commonoid_mon CarrierA
                                           CarrierAe CarrierAmult
                                           (@one_is_mon_unit CarrierA CarrierA1)
                                           (@abstract_algebra.semimult_monoid CarrierA
                                              CarrierAe CarrierAplus CarrierAmult
                                              CarrierAz CarrierA1
                                              (@rings.Ring_Semi CarrierA CarrierAe
                                                 CarrierAplus CarrierAmult CarrierAz
                                                 CarrierA1 CarrierAneg CarrierAr))))))))))
                   (@liftM_HOperator Monoid_RthetaFlags (S (S (S O)))
                      (S (S (S (S (S (S O)))))) (@HPrepend (S (S (S O))) (S (S (S O))) a)
                      (@HPrepend_HOperator (S (S (S O))) (S (S (S O))) a)))
                (@liftM_HOperator Monoid_RthetaFlags (S O) (S (S (S O)))
                   (@HInduction (S (S (S O))) (@mult CarrierA CarrierAmult)
                      (@abstract_algebra.sg_op_proper CarrierA CarrierAe CarrierAmult
                         (@abstract_algebra.monoid_semigroup CarrierA CarrierAe
                            CarrierAmult (@one_is_mon_unit CarrierA CarrierA1)
                            (@abstract_algebra.commonoid_mon CarrierA CarrierAe
                               CarrierAmult (@one_is_mon_unit CarrierA CarrierA1)
                               (@abstract_algebra.semimult_monoid CarrierA CarrierAe
                                  CarrierAplus CarrierAmult CarrierAz CarrierA1
                                  (@rings.Ring_Semi CarrierA CarrierAe CarrierAplus
                                     CarrierAmult CarrierAz CarrierA1 CarrierAneg
                                     CarrierAr))))) (@one CarrierA CarrierA1))
                   (@HInduction_HOperator (S (S (S O))) (@mult CarrierA CarrierAmult)
                      (@abstract_algebra.sg_op_proper CarrierA CarrierAe CarrierAmult
                         (@abstract_algebra.monoid_semigroup CarrierA CarrierAe
                            CarrierAmult (@one_is_mon_unit CarrierA CarrierA1)
                            (@abstract_algebra.commonoid_mon CarrierA CarrierAe
                               CarrierAmult (@one_is_mon_unit CarrierA CarrierA1)
                               (@abstract_algebra.semimult_monoid CarrierA CarrierAe
                                  CarrierAplus CarrierAmult CarrierAz CarrierA1
                                  (@rings.Ring_Semi CarrierA CarrierAe CarrierAplus
                                     CarrierAmult CarrierAz CarrierA1 CarrierAneg
                                     CarrierAr))))) (@one CarrierA CarrierA1))))
             (@GathH Monoid_RthetaFlags (S (S (S (S (S O)))))
                (S O) O (S O)
                (h_bound_first_half Monoid_RthetaSafeFlags MonoidLaws_SafeRthetaFlags
                   (S O) (S (S (S (S O)))))))
          (@SHCompose Monoid_RthetaFlags (S (S (S (S (S O)))))
             (S O) (S (S O))
             (@ScatH Monoid_RthetaFlags (S O) (S (S O)) (S O)
                (S O)
                (h_bound_second_half Monoid_RthetaSafeFlags MonoidLaws_SafeRthetaFlags
                   (S O) (S O))
                (@ScatH_stride1_constr Monoid_RthetaSafeFlags MonoidLaws_SafeRthetaFlags
                   (S O) (S (S O))) (@zero CarrierA CarrierAz))
             (@SafeCast (S (S (S (S (S O))))) (S O)
                (@IReduction (S (S (S (S (S O))))) (S O) (S (S O))
                   (@minmax.max CarrierA CarrierAle CarrierAledec)
                   (@abstract_algebra.sg_op_proper CarrierA CarrierAe
                      (fun x y : CarrierA =>
                       @snd CarrierA CarrierA
                         (@minmax.sort CarrierA CarrierAle CarrierAledec x y))
                      (@abstract_algebra.comsg_setoid CarrierA CarrierAe
                         (fun x y : CarrierA =>
                          @snd CarrierA CarrierA
                            (@minmax.sort CarrierA CarrierAle CarrierAledec x y))
                         (@abstract_algebra.semilattice_sg CarrierA CarrierAe
                            (fun x y : CarrierA =>
                             @snd CarrierA CarrierA
                               (@minmax.sort CarrierA CarrierAle CarrierAledec x y))
                            (@abstract_algebra.join_semilattice CarrierA CarrierAe
                               (fun x y : CarrierA =>
                                @snd CarrierA CarrierA
                                  (@minmax.sort CarrierA CarrierAle CarrierAledec x y))
                               (@abstract_algebra.lattice_join CarrierA CarrierAe
                                  (fun x y : CarrierA =>
                                   @snd CarrierA CarrierA
                                     (@minmax.sort CarrierA CarrierAle CarrierAledec x y))
                                  (@minmax.min CarrierA CarrierAle CarrierAledec)
                                  (@abstract_algebra.distr_lattice_lattice CarrierA
                                     CarrierAe
                                     (fun x y : CarrierA =>
                                      @snd CarrierA CarrierA
                                        (@minmax.sort CarrierA CarrierAle CarrierAledec x
                                           y))
                                     (@minmax.min CarrierA CarrierAle CarrierAledec)
                                     (@minmax.DistributiveLattice_instance_0 CarrierA
                                        CarrierAe CarrierAle CarrierAto CarrierAledec)))))))
                   (@zero CarrierA CarrierAz)
                   (@SHFamilyOperatorCompose Monoid_RthetaSafeFlags
                      (S (S (S (S (S O))))) (S (S (S (S O))))
                      (S O) (S (S O))
                      (mkSHOperatorFamily Monoid_RthetaSafeFlags
                         (S (S (S (S O)))) (S O) (S (S O))
                         (fun (j : nat) (jc : @lt nat Peano.lt j (S (S O))) =>
                          @UnSafeCast (S (S (S (S O)))) (S O)
                            (@SHCompose Monoid_RthetaFlags (S (S (S (S O))))
                               (S O) (S O)
                               (@SHCompose Monoid_RthetaFlags
                                  (S O) (S (S O)) (S O)
                                  (@liftM_HOperator Monoid_RthetaFlags
                                     (S (S O)) (S O)
                                     (@HReduction (S (S O))
                                        (@minmax.max CarrierA CarrierAle CarrierAledec)
                                        (@abstract_algebra.sg_op_proper CarrierA
                                           CarrierAe
                                           (fun x y : CarrierA =>
                                            @snd CarrierA CarrierA
                                              (@minmax.sort CarrierA CarrierAle
                                                 CarrierAledec x y))
                                           (@abstract_algebra.comsg_setoid CarrierA
                                              CarrierAe
                                              (fun x y : CarrierA =>
                                               @snd CarrierA CarrierA
                                                 (@minmax.sort CarrierA CarrierAle
                                                    CarrierAledec x y))
                                              (@abstract_algebra.semilattice_sg CarrierA
                                                 CarrierAe
                                                 (fun x y : CarrierA =>
                                                  @snd CarrierA CarrierA
                                                    (@minmax.sort CarrierA CarrierAle
                                                       CarrierAledec x y))
                                                 (@abstract_algebra.join_semilattice
                                                    CarrierA CarrierAe
                                                    (fun x y : CarrierA =>
                                                     @snd CarrierA CarrierA
                                                       (@minmax.sort CarrierA CarrierAle
                                                          CarrierAledec x y))
                                                    (@abstract_algebra.lattice_join
                                                       CarrierA CarrierAe
                                                       (fun x y : CarrierA =>
                                                        @snd CarrierA CarrierA
                                                          (@minmax.sort CarrierA
                                                            CarrierAle CarrierAledec x y))
                                                       (@minmax.min CarrierA CarrierAle
                                                          CarrierAledec)
                                                       (@abstract_algebra.distr_lattice_lattice
                                                          CarrierA CarrierAe
                                                          (fun x y : CarrierA =>
                                                           @snd CarrierA CarrierA
                                                            (@minmax.sort CarrierA
                                                            CarrierAle CarrierAledec x y))
                                                          (@minmax.min CarrierA
                                                            CarrierAle CarrierAledec)
                                                          (@minmax.DistributiveLattice_instance_0
                                                            CarrierA CarrierAe CarrierAle
                                                            CarrierAto CarrierAledec)))))))
                                        (@zero CarrierA CarrierAz))
                                     (@HReduction_HOperator (S (S O))
                                        (@minmax.max CarrierA CarrierAle CarrierAledec)
                                        (@abstract_algebra.sg_op_proper CarrierA
                                           CarrierAe
                                           (fun x y : CarrierA =>
                                            @snd CarrierA CarrierA
                                              (@minmax.sort CarrierA CarrierAle
                                                 CarrierAledec x y))
                                           (@abstract_algebra.comsg_setoid CarrierA
                                              CarrierAe
                                              (fun x y : CarrierA =>
                                               @snd CarrierA CarrierA
                                                 (@minmax.sort CarrierA CarrierAle
                                                    CarrierAledec x y))
                                              (@abstract_algebra.semilattice_sg CarrierA
                                                 CarrierAe
                                                 (fun x y : CarrierA =>
                                                  @snd CarrierA CarrierA
                                                    (@minmax.sort CarrierA CarrierAle
                                                       CarrierAledec x y))
                                                 (@abstract_algebra.join_semilattice
                                                    CarrierA CarrierAe
                                                    (fun x y : CarrierA =>
                                                     @snd CarrierA CarrierA
                                                       (@minmax.sort CarrierA CarrierAle
                                                          CarrierAledec x y))
                                                    (@abstract_algebra.lattice_join
                                                       CarrierA CarrierAe
                                                       (fun x y : CarrierA =>
                                                        @snd CarrierA CarrierA
                                                          (@minmax.sort CarrierA
                                                            CarrierAle CarrierAledec x y))
                                                       (@minmax.min CarrierA CarrierAle
                                                          CarrierAledec)
                                                       (@abstract_algebra.distr_lattice_lattice
                                                          CarrierA CarrierAe
                                                          (fun x y : CarrierA =>
                                                           @snd CarrierA CarrierA
                                                            (@minmax.sort CarrierA
                                                            CarrierAle CarrierAledec x y))
                                                          (@minmax.min CarrierA
                                                            CarrierAle CarrierAledec)
                                                          (@minmax.DistributiveLattice_instance_0
                                                            CarrierA CarrierAe CarrierAle
                                                            CarrierAto CarrierAledec)))))))
                                        (@zero CarrierA CarrierAz)))
                                  (@Scatter Monoid_RthetaFlags
                                     (S O) (S (S O))
                                     (@h_index_map (S O) (S (S O)) j
                                        (S O)
                                        (ScatH_1_to_n_range_bound Monoid_RthetaSafeFlags
                                           MonoidLaws_SafeRthetaFlags j
                                           (S (S O)) (S O) jc))
                                     (@index_map_family_member_injective
                                        (S O) (S (S O)) (S (S O))
                                        (IndexMapFamily (S O)
                                           (S (S O)) (S (S O))
                                           (fun (j0 : nat) (jc0 : Peano.lt j0 (S (S O)))
                                            =>
                                            @h_index_map (S O)
                                              (S (S O)) j0 (S O)
                                              (ScatH_1_to_n_range_bound
                                                 Monoid_RthetaSafeFlags
                                                 MonoidLaws_SafeRthetaFlags j0
                                                 (S (S O)) (S O) jc0)))
                                        (@h_j_1_family_injective (S (S O))) j jc)
                                     (@zero CarrierA CarrierAz)))
                               (@SHCompose Monoid_RthetaFlags
                                  (S (S (S (S O)))) (S (S O))
                                  (S O)
                                  (@SHCompose Monoid_RthetaFlags
                                     (S (S O)) (S O) (S O)
                                     (@SHPointwise Monoid_RthetaFlags
                                        (S O)
                                        (@IgnoreIndex CarrierA
                                           (S O)
                                           (@abs CarrierA CarrierAe CarrierAle CarrierAz
                                              CarrierAneg CarrierAabs))
                                        (@Reflexive_partial_app_morphism
                                           (forall _ : CarrierA, CarrierA)
                                           (forall
                                              (_ : @sig nat
                                                     (fun i : nat => Peano.lt i (S O)))
                                              (_ : CarrierA), CarrierA)
                                           (@respectful CarrierA CarrierA
                                              (@equiv CarrierA CarrierAe)
                                              (@equiv CarrierA CarrierAe))
                                           (@respectful
                                              (@sig nat (fun i : nat => Peano.lt i (S O)))
                                              (forall _ : CarrierA, CarrierA)
                                              (@equiv
                                                 (@sig nat
                                                    (fun i : nat => Peano.lt i (S O)))
                                                 (@Sig_Equiv nat peano_naturals.nat_equiv
                                                    (fun i : nat => Peano.lt i (S O))))
                                              (@respectful CarrierA CarrierA
                                                 (@equiv CarrierA CarrierAe)
                                                 (@equiv CarrierA CarrierAe)))
                                           (@IgnoreIndex CarrierA (S O))
                                           (@IgnoredIndex_proper (S O) CarrierA CarrierAe)
                                           (@abs CarrierA CarrierAe CarrierAle CarrierAz
                                              CarrierAneg CarrierAabs)
                                           (@proper_proper_proxy
                                              (forall _ : CarrierA, CarrierA)
                                              (@abs CarrierA CarrierAe CarrierAle
                                                 CarrierAz CarrierAneg CarrierAabs)
                                              (@respectful CarrierA CarrierA
                                                 (@equiv CarrierA CarrierAe)
                                                 (@equiv CarrierA CarrierAe))
                                              (@abstract_algebra.sm_proper CarrierA
                                                 CarrierA CarrierAe CarrierAe
                                                 (@abs CarrierA CarrierAe CarrierAle
                                                    CarrierAz CarrierAneg CarrierAabs)
                                                 (@abs_Setoid_Morphism CarrierA CarrierAe
                                                    CarrierAplus CarrierAmult CarrierAz
                                                    CarrierA1 CarrierAneg CarrierAr
                                                    CarrierAsetoid CarrierAle CarrierAto
                                                    CarrierAabs)))))
                                     (@SafeCast (S (S O)) (S O)
                                        (@SHBinOp (S O)
                                           (@SwapIndex2 CarrierA j
                                              (@IgnoreIndex2 CarrierA sub))
                                           (@SwapIndex2_specialized_proper CarrierA
                                              CarrierAe CarrierAsetoid j
                                              (@IgnoreIndex2 CarrierA sub)
                                              (@Reflexive_partial_app_morphism
                                                 (forall (_ : CarrierA) (_ : CarrierA),
                                                  CarrierA)
                                                 (forall (_ : nat)
                                                    (_ : CarrierA)
                                                    (_ : CarrierA), CarrierA)
                                                 (@respectful CarrierA
                                                    (forall _ : CarrierA, CarrierA)
                                                    (@equiv CarrierA CarrierAe)
                                                    (@equiv
                                                       (forall _ : CarrierA, CarrierA)
                                                       (@ext_equiv CarrierA CarrierAe
                                                          CarrierA CarrierAe)))
                                                 (@respectful nat
                                                    (forall (_ : CarrierA) (_ : CarrierA),
                                                     CarrierA)
                                                    (@equiv nat peano_naturals.nat_equiv)
                                                    (@respectful CarrierA
                                                       (forall _ : CarrierA, CarrierA)
                                                       (@equiv CarrierA CarrierAe)
                                                       (@respectful CarrierA CarrierA
                                                          (@equiv CarrierA CarrierAe)
                                                          (@equiv CarrierA CarrierAe))))
                                                 (@IgnoreIndex2 CarrierA)
                                                 (@IgnoreIndex2_proper CarrierA CarrierAe)
                                                 sub
                                                 (@proper_proper_proxy
                                                    (forall (_ : CarrierA) (_ : CarrierA),
                                                     CarrierA) sub
                                                    (@respectful CarrierA
                                                       (forall _ : CarrierA, CarrierA)
                                                       (@equiv CarrierA CarrierAe)
                                                       (@equiv
                                                          (forall _ : CarrierA, CarrierA)
                                                          (@ext_equiv CarrierA CarrierAe
                                                            CarrierA CarrierAe)))
                                                    CarrierA_sub_proper))))))
                                  (@Gather Monoid_RthetaFlags
                                     (S (S (S (S O)))) (S (S O))
                                     (@h_index_map (S (S O))
                                        (S (S (S (S O)))) j (S (S O))
                                        (GathH_jn_domain_bound Monoid_RthetaSafeFlags
                                           MonoidLaws_SafeRthetaFlags j
                                           (S (S O)) jc)))))))
                      (@GathH Monoid_RthetaSafeFlags (S (S (S (S (S O)))))
                         (S (S (S (S O)))) (S O) (S O)
                         (h_bound_second_half Monoid_RthetaSafeFlags
                            MonoidLaws_SafeRthetaFlags (S O)
                            (S (S (S (S O)))))))))))) (dynwin_SHCOL1 a).
  Proof.

    (* --- BEGIN: hack ---
    I would expect the following to work here:

    setoid_rewrite rewrite_Reduction_ScatHUnion_max_zero with
        (fm := Monoid_RthetaFlags)
        (m := 4%nat)
        (n := 1%nat).

     But it does not (hangs forever), so we have to do some manual rewriting
     *)

    match goal with
    | [ |- context G [ mkSHOperatorFamily _ _ _ _ ?f ]] =>
      match f with
      | (fun j jc => UnSafeCast (?torewrite ⊚ ?rest )) =>
        setoid_replace
          (mkSHOperatorFamily _ _ _ _ f) with
            (mkSHOperatorFamily _ _ _ _
                                (fun (j:nat) (jc:j<2) => UnSafeCast rest))
      end
    end.
    all:revgoals.
    f_equiv.
    intros j jc.
    f_equiv.
    apply rewrite_Reduction_ScatHUnion_max_zero.
    (* --- END: hack --- *)

  Admitted.

End SigmaHCOL_rewriting.


End DynWin.

End Spiral.

End Spiral_DOT_DynWin.

