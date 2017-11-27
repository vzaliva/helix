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
Module Spiral_DOT_CpdtTactics.
Module Spiral.
Module CpdtTactics.
(* Copyright (c) 2008-2012, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)
Import Coq.Logic.Eqdep Coq.Lists.List Coq.omega.Omega.

Set Implicit Arguments.


(** A version of [injection] that does some standard simplifications afterward: clear the hypothesis in question, bring the new facts above the double line, and attempt substitution for known variables. *)
Ltac inject H := injection H; clear H; intros; try subst.

(** Try calling tactic function [f] on all hypotheses, keeping the first application that doesn't fail. *)
Ltac appHyps f :=
  match goal with
    | [ H : _ |- _ ] => f H
  end.

(** Succeed iff [x] is in the list [ls], represented with left-associated nested tuples. *)
Ltac inList x ls :=
  match ls with
    | x => idtac
    | (_, x) => idtac
    | (?LS, _) => inList x LS
  end.

(** Try calling tactic function [f] on every element of tupled list [ls], keeping the first call not to fail. *)
Ltac app f ls :=
  match ls with
    | (?LS, ?X) => f X || app f LS || fail 1
    | _ => f ls
  end.

(** Run [f] on every element of [ls], not just the first that doesn't fail. *)
Ltac all f ls :=
  match ls with
    | (?LS, ?X) => f X; all f LS
    | (_, _) => fail 1
    | _ => f ls
  end.

(** Workhorse tactic to simplify hypotheses for a variety of proofs.
   * Argument [invOne] is a tuple-list of predicates for which we always do inversion automatically. *)
Ltac simplHyp invOne :=
  (** Helper function to do inversion on certain hypotheses, where [H] is the hypothesis and [F] its head symbol *)
  let invert H F :=
    (** We only proceed for those predicates in [invOne]. *)
    inList F invOne;
    (** This case covers an inversion that succeeds immediately, meaning no constructors of [F] applied. *)
      (inversion H; fail)
    (** Otherwise, we only proceed if inversion eliminates all but one constructor case. *)
      || (inversion H; [idtac]; clear H; try subst) in

  match goal with
    (** Eliminate all existential hypotheses. *)
    | [ H : ex _ |- _ ] => destruct H

    (** Find opportunities to take advantage of injectivity of data constructors, for several different arities. *)
    | [ H : ?F ?X = ?F ?Y |- ?G ] =>
      (** This first branch of the [||] fails the whole attempt iff the arguments of the constructor applications are already easy to prove equal. *)
      (assert (X = Y); [ assumption | fail 1 ])
      (** If we pass that filter, then we use injection on [H] and do some simplification as in [inject].
         * The odd-looking check of the goal form is to avoid cases where [injection] gives a more complex result because of dependent typing, which we aren't equipped to handle here. *)
      || (injection H;
        match goal with
          | [ |- X = Y -> G ] =>
            try clear H; intros; try subst
        end)
    | [ H : ?F ?X ?U = ?F ?Y ?V |- ?G ] =>
      (assert (X = Y); [ assumption
        | assert (U = V); [ assumption | fail 1 ] ])
      || (injection H;
        match goal with
          | [ |- U = V -> X = Y -> G ] =>
            try clear H; intros; try subst
        end)

    (** Consider some different arities of a predicate [F] in a hypothesis that we might want to invert. *)
    | [ H : ?F _ |- _ ] => invert H F
    | [ H : ?F _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ _ _ |- _ ] => invert H F

    (** Use an (axiom-dependent!) inversion principle for dependent pairs, from the standard library. *)
    | [ H : existT _ ?T _ = existT _ ?T _ |- _ ] => generalize (inj_pair2 _ _ _ _ _ H); clear H

    (** If we're not ready to use that principle yet, try the standard inversion, which often enables the previous rule. *)
    | [ H : existT _ _ _ = existT _ _ _ |- _ ] => inversion H; clear H

    (** Similar logic to the cases for constructor injectivity above, but specialized to [Some], since the above cases won't deal with polymorphic constructors. *)
    | [ H : Some _ = Some _ |- _ ] => injection H; clear H
  end.

(** Find some hypothesis to rewrite with, ensuring that [auto] proves all of the extra subgoals added by [rewrite]. *)
Ltac rewriteHyp :=
  match goal with
    | [ H : _ |- _ ] => rewrite H by solve [ auto ]
  end.

(** Combine [autorewrite] with automatic hypothesis rewrites. *)
Ltac rewriterP := repeat (rewriteHyp; autorewrite with core in *).
Ltac rewriter := autorewrite with core in *; rewriterP.

(** This one is just so darned useful, let's add it as a hint here. *)
Hint Rewrite app_ass.

(** Devious marker predicate to use for encoding state within proof goals *)
Definition done (T : Type) (x : T) := True.

(** Try a new instantiation of a universally quantified fact, proved by [e].
   * [trace] is an accumulator recording which instantiations we choose. *)
Ltac inster e trace :=
  (** Does [e] have any quantifiers left? *)
  match type of e with
    | forall x : _, _ =>
      (** Yes, so let's pick the first context variable of the right type. *)
      match goal with
        | [ H : _ |- _ ] =>
          inster (e H) (trace, H)
        | _ => fail 2
      end
    | _ =>
      (** No more quantifiers, so now we check if the trace we computed was already used. *)
      match trace with
        | (_, _) =>
          (** We only reach this case if the trace is nonempty, ensuring that [inster] fails if no progress can be made. *)
          match goal with
            | [ H : done (trace, _) |- _ ] =>
              (** Uh oh, found a record of this trace in the context!  Abort to backtrack to try another trace. *)
              fail 1
            | _ =>
              (** What is the type of the proof [e] now? *)
              let T := type of e in
                match type of T with
                  | Prop =>
                    (** [e] should be thought of as a proof, so let's add it to the context, and also add a new marker hypothesis recording our choice of trace. *)
                    generalize e; intro;
                      assert (done (trace, tt)) by constructor
                  | _ =>
                    (** [e] is something beside a proof.  Better make sure no element of our current trace was generated by a previous call to [inster], or we might get stuck in an infinite loop!  (We store previous [inster] terms in second positions of tuples used as arguments to [done] in hypotheses.  Proofs instantiated by [inster] merely use [tt] in such positions.) *)
                    all ltac:(fun X =>
                      match goal with
                        | [ H : done (_, X) |- _ ] => fail 1
                        | _ => idtac
                      end) trace;
                    (** Pick a new name for our new instantiation. *)
                    let i := fresh "i" in (pose (i := e);
                      assert (done (trace, i)) by constructor)
                end
          end
      end
  end.

(** After a round of application with the above, we will have a lot of junk [done] markers to clean up; hence this tactic. *)
Ltac un_done :=
  repeat match goal with
           | [ H : done _ |- _ ] => clear H
         end.
Import Coq.Logic.JMeq.

(** A more parameterized version of the famous [crush].  Extra arguments are:
   * - A tuple-list of lemmas we try [inster]-ing 
   * - A tuple-list of predicates we try inversion for *)
Ltac crush' lemmas invOne :=
  (** A useful combination of standard automation *)
  let sintuition := simpl in *; intuition; try subst;
    repeat (simplHyp invOne; intuition; try subst); try congruence in

  (** A fancier version of [rewriter] from above, which uses [crush'] to discharge side conditions *)
  let rewriter := autorewrite with core in *;
    repeat (match goal with
              | [ H : ?P |- _ ] =>
                match P with
                  | context[JMeq] => fail 1 (** JMeq is too fancy to deal with here. *)
                  | _ => rewrite H by crush' lemmas invOne
                end
            end; autorewrite with core in *) in

  (** Now the main sequence of heuristics: *)
    (sintuition; rewriter;
      match lemmas with
        | false => idtac (** No lemmas?  Nothing to do here *)
        | _ =>
          (** Try a loop of instantiating lemmas... *)
          repeat ((app ltac:(fun L => inster L L) lemmas
          (** ...or instantiating hypotheses... *)
            || appHyps ltac:(fun L => inster L L));
          (** ...and then simplifying hypotheses. *)
          repeat (simplHyp invOne; intuition)); un_done
      end;
      sintuition; rewriter; sintuition;
      (** End with a last attempt to prove an arithmetic fact with [omega], or prove any sort of fact in a context that is contradictory by reasoning that [omega] can do. *)
      try omega; try (elimtype False; omega)).

(** [crush] instantiates [crush'] with the simplest possible parameters. *)
Ltac crush := crush' false fail.

(** * Wrap Program's [dependent destruction] in a slightly more pleasant form *)
Import Coq.Program.Equality.

(** Run [dependent destruction] on [E] and look for opportunities to simplify the result.
   The weird introduction of [x] helps get around limitations of [dependent destruction], in terms of which sorts of arguments it will accept (e.g., variables bound to hypotheses within Ltac [match]es). *)
Ltac dep_destruct E :=
  let x := fresh "x" in
    remember E as x; simpl in x; dependent destruction x;
      try match goal with
            | [ H : _ = E |- _ ] => try rewrite <- H in *; clear H
          end.

(** Nuke all hypotheses that we can get away with, without invalidating the goal statement. *)
Ltac clear_all :=
  repeat match goal with
           | [ H : _ |- _ ] => clear H
         end.

(** Instantiate a quantifier in a hypothesis [H] with value [v], or, if [v] doesn't have the right type, with a new unification variable.
   * Also prove the lefthand sides of any implications that this exposes, simplifying [H] to leave out those implications. *)
Ltac guess v H :=
  repeat match type of H with
           | forall x : ?T, _ =>
             match type of T with
               | Prop =>
                 (let H' := fresh "H'" in
                   assert (H' : T); [
                     solve [ eauto 6 ]
                     | specialize (H H'); clear H' ])
                 || fail 1
               | _ =>
                 specialize (H v)
                 || let x := fresh "x" in
                   evar (x : T);
                   let x' := eval unfold x in x in
                     clear x; specialize (H x')
             end
         end.

(** Version of [guess] that leaves the original [H] intact *)
Ltac guessKeep v H :=
  let H' := fresh "H'" in
    generalize H; intro H'; guess v H'.

End CpdtTactics.

End Spiral.

End Spiral_DOT_CpdtTactics.

Module Spiral_DOT_StructTactics.
Module Spiral.
Module StructTactics.
Import Spiral_DOT_CpdtTactics.
Import Spiral_DOT_CpdtTactics.Spiral.
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
Import Spiral_DOT_CpdtTactics.
Import Spiral_DOT_StructTactics.
Import Spiral_DOT_StructTactics.Spiral.
Import Spiral_DOT_CpdtTactics.Spiral.
(* ----------- Some handy tactics ----------- *)
Export Spiral_DOT_CpdtTactics.Spiral.CpdtTactics.
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
Import Spiral_DOT_CpdtTactics.
Import Spiral_DOT_StructTactics.
Import Spiral_DOT_SpiralTactics.
Import Spiral_DOT_SpiralTactics.Spiral.
Import Spiral_DOT_StructTactics.Spiral.
Import Spiral_DOT_CpdtTactics.Spiral.
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
  -
    rewrite (abs_nonneg x), abs_nonpos.
    apply rings.negate_involutive.
    apply flip_nonneg_negate.
    apply H.
    apply H.
  -
    rewrite (abs_nonneg (-x)), abs_nonpos.
    reflexivity.
    apply H.
    apply flip_nonpos_negate.
    apply H.
Qed.

Lemma abs_nz_nz
      `{Ae: Equiv A}
      `{Az: Zero A} `{A1: One A}
      `{Aplus: Plus A} `{Amult: Mult A}
      `{Aneg: Negate A}
      `{Ale: Le A}
      `{Ato: !@TotalOrder A Ae Ale}
      `{Aabs: !@Abs A Ae Ale Az Aneg}
      `{Ar: !Ring A}
      `{Aledec: ∀ x y: A, Decision (x ≤ y)}
  :
    forall v : A, v ≠ zero <-> abs v ≠ zero.
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
  apply Ato.
  apply Ar.
  apply ASRO.
  apply H.
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
Proof. intros; omega. Qed.

Lemma S_pred_simpl:
  forall n : nat, n ≢ 0 -> S (Init.Nat.pred n) ≡ n.
Admitted.


Global Instance Sig_Equiv {A:Type} {Ae : Equiv A} {P:A->Prop}:
  Equiv (@sig A P) := fun a b => (proj1_sig a) = (proj1_sig b).

Instance proj1_Proper {A:Type} {Ae : Equiv A} {P:A->Prop}:
  Proper ((=)==>(=)) (@proj1_sig A P).
Proof.
  intros x y E.
  unfold equiv, Sig_Equiv in E.
  auto.
Qed.


End Spiral.

End Spiral.

End Spiral_DOT_Spiral.

Module Spiral_DOT_VecUtil.
Module Spiral.
Module VecUtil.
Import Spiral_DOT_CpdtTactics.
Import Spiral_DOT_StructTactics.
Import Spiral_DOT_SpiralTactics.
Import Spiral_DOT_Spiral.
Import Spiral_DOT_Spiral.Spiral.
Import Spiral_DOT_SpiralTactics.Spiral.
Import Spiral_DOT_StructTactics.Spiral.
Import Spiral_DOT_CpdtTactics.Spiral.
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

Fact lt_0_SSn:  forall n:nat, 0<S (S n). Proof. intros;omega. Qed.

Fact lt_1_SSn:  forall n:nat, 1<S (S n). Proof. intros; omega. Qed.

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

  Lemma Vnth_0
        {B} {n} (v:vector B (S n)) (ip: 0<(S n)):
    Vnth (i:=0) v ip = Vhead v.
Admitted.

  Lemma Vnth_1_Vhead
        {T:Type}
        (x:vector T 1)
        (i:nat) (ic: Peano.lt i 1)
    :
      Vnth x ic = Vhead x.
Admitted.

  Lemma Vnth_1
        {T:Type}
        (x:T)
        (i:nat) (ic: Peano.lt i 1)
    :
      Vnth [x] ic = x.
Admitted.

  Lemma Vnth_Sn {B} (n i:nat) (v:B) (vs:vector B n) (ip: S i< S n) (ip': i< n):
    Vnth (Vcons v vs) ip = Vnth vs ip'.
Admitted.

  Lemma Vnth_cast_index:
    forall {B} {n : nat} i j (ic: i<n) (jc: j<n) (x : vector B n),
      i = j -> Vnth x ic = Vnth x jc.
Admitted.

  Lemma P_Vnth_Vcons {T:Type} {P:T -> Prop} {n:nat} (h:T) (t:vector T n):
    forall i (ic:i<S n) (ic': (pred i) < n),
      P (Vnth (Vcons h t) ic) -> P h \/ P (Vnth t ic').
Admitted.

  Lemma P_Vnth_Vcons_not_head {T:Type} {P:T -> Prop} {n:nat} (h:T) (t:vector T n):
    forall i (ic:i<S n) (ic': (pred i) < n),
      not (P h) -> P (Vnth (Vcons h t) ic) -> P (Vnth t ic').
Admitted.

End Vnth.

Lemma Vbuild_cons:
  forall B n (gen : forall i, i < S n -> B),
    Vbuild gen = Vcons (gen 0 (lt_O_Sn n)) (Vbuild (fun i ip => gen (S i) (lt_n_S ip))).
Admitted.

Lemma Vforall_Vbuild (T : Type) (P:T -> Prop) (n : nat) (gen : forall i : nat, i < n -> T):
  Vforall P (Vbuild gen) <-> forall (i : nat) (ip : i < n), P (gen i ip).
Admitted.

Lemma Vbuild_Vapp
      {A: Type}
      {n m: nat}
      {f: forall (t:nat), (t<n+m) -> A}
  : Vbuild f =
    @Vapp A n m
          (Vbuild (fun t (tc:t<n) => f t (Nat.lt_lt_add_r t n m tc)))
          (Vbuild (fun t (tc:t<m) => f (t+n) (add_lt_lt tc))).
Admitted.

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
Admitted.

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

Admitted.

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
Admitted.

  Lemma Vforall_notP_Vunique:
    forall (n : nat) (T : Type) (P : T -> Prop) (v : vector T n),
      Vforall (not ∘ P) v -> Vunique P v.
Admitted.


  Lemma Vunique_P_Vforall_notP:
    forall (n : nat) (T : Type) (P : T -> Prop) (h:T) (x : vector T n),
      P(h) /\ Vunique P (h::x) -> Vforall (not ∘ P) x.
Admitted.

  Lemma Vunique_cons_not_head
        {n} {T:Type}
        (P: T -> Prop)
        (h: T) (t: vector T n):
    not (P h) /\ Vunique P t -> Vunique P (Vcons h t).
Admitted.

  Lemma Vunique_cons_head
        {n} {T:Type}
        (P: T -> Prop)
        (h: T) (t: vector T n):
    P h /\ (Vforall (not ∘ P) t) -> Vunique P (Vcons h t).
Admitted.

  Lemma Vunique_cons {n} {T:Type}
        (P: T -> Prop)
        (h: T) (t: vector T n):
    ((P h /\ (Vforall (not ∘ P) t)) \/
     (not (P h) /\ Vunique P t))
    ->
    Vunique P (Vcons h t).
Admitted.
  Lemma Vunique_cons_tail {n}
        {T:Type} (P: T -> Prop)
        (h : T) (t : vector T n):
    Vunique P (Vcons h t) -> Vunique P t.
Admitted.

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
Admitted.

  Lemma VAllButOne_0_Vforall
        {T}
        n
        (v: T)
        (vs : vector T n)
        (kc : 0 < S n)
        (P: T -> Prop)
    :
      VAllButOne 0 kc P (Vcons v vs) -> Vforall P vs.
Admitted.

  (* Always works in this direction *)
  Lemma VAllButOne_Sn
        {n} {T:Type}
        (P: T -> Prop)
        (h: T)
        (t: vector T n)
        i (ic: S i < S n) (ic': i < n):
    VAllButOne (S i) ic P (Vcons h t) -> VAllButOne i ic' P t .
Admitted.

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
Admitted.

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
Admitted.

  (* In this direction requires additional assumtion  P h *)
  Lemma Vforall_VAllButOne_P0
        (T : Type)
        (P : T -> Prop)
        (h : T)
        (n : nat)
        (x : vector T n)
        (N: P h):
    Vforall (not ∘ P) x -> VAllButOne 0 (zero_lt_Sn n) (not ∘ P) (h :: x).
Admitted.

  Lemma VallButOne_Vunique
        {n} {T:Type}
        (P: T -> Prop)
        {Pdec: forall a, {P a}+{~(P a)}}
        (x: vector T n)
    :
      (exists i ic, VAllButOne i ic (not∘P) x) ->
      Vunique P x.
Admitted.

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
Admitted.

  Lemma Vunique_cases
        {n} {T:Type}
        (P: T -> Prop)
        `{D: forall (a:T), {P a}+{~P a}}
        (x: vector T n):
    Vunique P x ->
    ({Vforall (not ∘ P) x}+{exists i ic, VAllButOne i ic (not∘P) x}).
Admitted.

End Vunique.

Section Vforall.

  Variable A : Type.
  Variable P: A -> Prop.
  Variable n: nat.

  Lemma Vforall_Vhead
        {v:vector A (S n)}:
    Vforall P v -> P (Vhead v).
Admitted.

  Lemma Vforall_Vtail
        {v:vector A (S n)}:
    Vforall P v -> Vforall P (Vtail v).
Admitted.

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

  Lemma Vnth_Vmap2Indexed:
    forall {A B C : Type} {n:nat} (i : nat) (ip : i < n) (f: nat->A->B->C)
      (a:vector A n) (b:vector B n),
      Vnth (Vmap2Indexed f a b) ip = f i (Vnth a ip) (Vnth b ip).
Admitted.

End VMap2_Indexed.


Definition Lst {B:Type} (x:B) := [x].

Lemma Vin_cons:
  forall (T:Type) (h : T) (n : nat) (v : vector T n) (x : T),
    Vin x (Vcons h v) -> x = h \/ Vin x v.
Admitted.

Lemma Vin_1
      (A: Type)
      (a:A)
      (v:vector A 1)
  :
    Vin a v -> a = Vhead v.
Admitted.

Lemma Vforall_not_Vexists
      {n} {T}
      (v: vector T n)
      (P: T -> Prop) :
  Vforall (not ∘ P) v -> not (Vexists P v).
Admitted.

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

Lemma Vtail_1:
  forall {A:Type} (x:vector A 1), (Vtail x = @Vnil A).
Admitted.

Lemma V0_V0_eq:
  forall {A:Type} (x y:vector A 0), x=y.
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

Section List_of_Vec.
Import CoLoR.Util.List.ListUtil.

  Lemma list_of_vec_eq {A:Type} {n:nat} (v1 v2 : vector A n) :
    list_of_vec v1 = list_of_vec v2 -> v1 = v2.
Admitted.

  Lemma list_of_vec_length {A:Type} {n:nat} {v : vector A n} :
    length (list_of_vec v) = n.
Admitted.

  Lemma list_of_vec_vec_of_list {A:Type} {l : list A} :
    list_of_vec (vec_of_list l) = l.
Admitted.

  Lemma list_of_vec_Vcast {A:Type} {m n:nat} (v : vector A m) {E:m=n}:
    list_of_vec (Vcast v E) = list_of_vec v.
Admitted.

  (* Note: no [default] param for [nth] is not specified *)
  Lemma nth_cons {A:Type} (l: list A) (a:A) (i:nat):
    nth (S i) (a::l) = nth i l.
Admitted.

  (* Note: no [default] param for [nth] is not specified *)
  Lemma list_eq_nth {A:Type} (l1 l2: list A):
    (length l1 = length l2) ->
    (forall i (ic1:i<length l1), nth i l1 = nth i l2) ->
    l1 = l2.
Admitted.

  (* Note: no [default] param for [nth] is not specified *)
  Lemma nth_Vnth {A:Type} {n:nat} {v:vector A n} (i:nat) (ic:i<n):
    nth i (list_of_vec (v)) = fun _ => Vnth v ic.
Admitted.

  Lemma list_of_vec_Vapp {A:Type} {m n:nat} {v1: vector A m} {v2: vector A n}:
    list_of_vec (Vapp v1 v2) = List.app (list_of_vec v1) (list_of_vec v2).
Admitted.

End List_of_Vec.
End VecUtil.

End Spiral.

End Spiral_DOT_VecUtil.

Module Spiral_DOT_VecSetoid.
Module Spiral.
Module VecSetoid.
Import Spiral_DOT_CpdtTactics.
Import Spiral_DOT_StructTactics.
Import Spiral_DOT_SpiralTactics.
Import Spiral_DOT_Spiral.
Import Spiral_DOT_VecUtil.
Import Spiral_DOT_VecUtil.Spiral.
Import Spiral_DOT_Spiral.Spiral.
Import Spiral_DOT_SpiralTactics.Spiral.
Import Spiral_DOT_StructTactics.Spiral.
Import Spiral_DOT_CpdtTactics.Spiral.
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
  Proof.
    unfold vec_Equiv.
    apply Vforall2_equiv.
    assumption.
  Qed.

  Global Instance vec_Setoid `{Setoid A} {n}: Setoid (vector A n).
  Proof.
    unfold Setoid.
    apply vec_Equivalence.
  Qed.

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
  Proof.
    intros a a' aa'.
    unfold Vconst_reord.
    induction n.
    crush.
    simpl.
    unfold equiv, vec_Equiv.
    rewrite Vforall2_cons_eq.
    split; assumption.
  Qed.

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
  Proof.
    intros f f' Ef i i' iEq v v' vEq .
    revert i i' iEq.
    induction v; simpl; intros.
    -
      VOtac; assumption.
    -
      revert vEq.
      VSntac v'.
      unfold equiv, vec_Equiv.
      rewrite Vforall2_cons_eq; intros [h1 h2]; simpl.
      apply IHv.
      + assumption.
      + apply Ef; assumption.
  Qed.

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
  Proof.
    intros f f' Ef i i' iEq v v' vEq .
    revert i i' iEq.
    induction v; simpl; intros.
    -
      VOtac; assumption.
    -
      revert vEq.
      VSntac v'.
      unfold equiv, vec_Equiv.
      rewrite Vforall2_cons_eq; intros [h1 h2]; simpl.
      apply Ef.
      apply IHv; assumption.
      assumption.
  Qed.

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
  Proof.
    intros f f' Ef v v' vEq i i' iEq.
    unfold Vfold_right_reord.
    induction v.
    (* Case "N=0". *)
    VOtac. simpl. assumption.
    (* Case "S(N)".*)
    revert vEq. VSntac v'. unfold equiv, vec_Equiv. rewrite Vforall2_cons_eq. intuition. simpl.
    apply Ef.
    (* SCase "Pf - 1". *)
    assumption.
    (* SCase "Pf - 2". *)
    apply IHv. unfold equiv, vec_Equiv; assumption.
  Qed.

  Global Instance Vfold_right_aux_proper n :
    Proper (((=) ==> (=) ==> (=)) ==> (=) ==> (=) ==> (=))
           (@Vfold_right_aux A B n).
  Proof.
    simpl_relation.
    unfold Vfold_right_aux.
    rewrite Vfold_right_to_Vfold_right_reord.
    apply Vfold_right_reord_proper; assumption.
  Qed.

End Vfold_right.

(* TODO: check if needed for Coq-8.6 *)
Section VCons.

  Definition Vcons_reord {A} {n} (t: vector A n) (h:A): vector A (S n) := Vcons h t.

  Lemma Vcons_to_Vcons_reord: forall A n (t: t A n) (h:A), Vcons h t  ≡ Vcons_reord t h.
Admitted.

  Global Instance Vcons_reord_proper `{Equiv A} n:
    Proper ((=) ==> (=) ==> (=))
           (@Vcons_reord A n).
  Proof.
    split.
    assumption.
    unfold vec_Equiv, Vforall2 in H0.  assumption.
  Qed.

End VCons.

Global Instance Vapp_proper `{Sa: Setoid A} (n1 n2:nat):
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

  unfold equiv, vec_Equiv.
  apply Vforall2_cons_eq.
  split. reflexivity.

  unfold equiv, vec_Equiv in IHn1.
  apply IHn1.
  apply aEq.
Qed.

Global Instance Vhead_proper `{Equiv A} n:
  Proper ((=) ==> (=)) (@Vhead A n).
Proof.
  intros a b E.
  dep_destruct a.  dep_destruct b.
  unfold equiv, vec_Equiv, vec_Equiv, relation in E.
  rewrite Vforall2_cons_eq in E.
  intuition.
Qed.

Global Instance Vtail_proper `{Equiv A} n:
  Proper ((=) ==> (=)) (@Vtail A n).
Proof.
  intros a b E.
  unfold equiv, vec_Equiv, vec_Equiv, relation in E.
  apply Vforall2_tail in E.
  unfold vec_Equiv.
  assumption.
Qed.

Global Instance Ptail_proper `{Sa: Setoid A} `{Sb: Setoid B} (n:nat):
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
  Proof.
    intros f g Eext a b Ev.
    induction n.
    -
      VOtac; auto.
    -
      dep_destruct a. dep_destruct b.
      split.
      + apply Eext, Ev.
      + apply IHn, Ev.
  Qed.


  Global Instance Vmap_arg_proper  (M N:Type) `{Me:!Equiv M} `{Ne: !Equiv N} (f : M->N)
         `{fP: !Proper (Me ==> Ne) f} (n:nat):
    Proper ((@vec_Equiv M _ n) ==> (@vec_Equiv N _ n)) (@Vmap M N f n).
  Proof.
    intros a b Ea.
    induction n.
    -
      VOtac; auto.
    -
      dep_destruct a. dep_destruct b.
      split.
      apply fP, Ea.
      apply IHn, Ea.
  Qed.

End VMap_reord.


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
Proof.
  intros fa fb Ef a a' Ea b b' Eb.
  unfold Vmap2Indexed.

  vec_index_equiv i ip.
  rewrite 2!Vbuild_nth.
  apply Ef.
  - reflexivity.
  - apply Vnth_equiv.
    reflexivity.
    assumption.
  - apply Vnth_equiv.
    reflexivity.
    assumption.
Qed.

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
Proof.
  intros f f' E.
  unfold forall_relation, pointwise_relation in E.
  unfold equiv, vec_Equiv; apply Vforall2_intro_nth; intros j jc.
  rewrite 2!Vbuild_nth.
  apply E.
Qed.

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
Import Spiral_DOT_CpdtTactics.
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
Import Spiral_DOT_CpdtTactics.Spiral.
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
Proof.
  solve_proper.
Qed.

Global Instance CommutativeMonoid_plus_zero:
  @MathClasses.interfaces.abstract_algebra.CommutativeMonoid CarrierA _ plus zero.
Proof.
  typeclasses eauto.
Qed.

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
Import Spiral_DOT_CpdtTactics.
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
Import Spiral_DOT_CpdtTactics.Spiral.
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

Section MapWriter.
  Variable A B: Type.
  Variable W W' : Type.
  Variable Monoid_W: Monoid W.
  Variable Monoid_W': Monoid W'.

  Open Scope program_scope.

  (** Map both the return value and output of a computation using the given function.
        [[ 'runWriter' ('mapWriter' f m) = f ('runWriter' m) ]]
   *)
  Definition mapWriter (f: (pprod A W)%type -> (pprod B W')%type) :
    writer Monoid_W A -> writer Monoid_W' B
    :=
      mapWriterT B Monoid_W' ident (mkIdent ∘ f ∘ unIdent).

End MapWriter.

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
Import Spiral_DOT_CpdtTactics.
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
Import Spiral_DOT_CpdtTactics.Spiral.
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
Proof.
  unfold Reflexive.
  intros x.
  destruct x.
  unfold equiv, RthetaFlags_equiv.
  auto.
Qed.

Global Instance RthetaFlags_Symmetric_equiv: Symmetric RthetaFlags_equiv.
Proof.
  unfold Symmetric.
  intros x y H.
  destruct x,y.
  unfold equiv, RthetaFlags_equiv in *.
  simpl in *.
  split; crush.
Qed.

Global Instance RthetaFlags_Transitive_equiv: Transitive RthetaFlags_equiv.
Proof.
  unfold Transitive.
  intros x y z H0 H1.
  unfold equiv, RthetaFlags_equiv in *.
  crush.
Qed.

Global Instance RthetaFlags_Equivalence_equiv: Equivalence RthetaFlags_equiv.
Proof.
  split.
  apply RthetaFlags_Reflexive_equiv.
  apply RthetaFlags_Symmetric_equiv.
  apply RthetaFlags_Transitive_equiv.
Qed.

Global Instance RthetaFlags_Setoid: @Setoid RthetaFlags RthetaFlags_equiv.
Proof.
  apply RthetaFlags_Equivalence_equiv.
Qed.

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
  Proof.
    split.
    - (* monoid_assoc *)
      simpl.
      unfold BinOps.Associative.
      apply RthetaFlags_assoc.
    - (* monoid_lunit *)
      simpl.
      unfold BinOps.LeftUnit.
      apply RthetaFlags_lunit.
    - (* monoid_runit *)
      simpl.
      unfold BinOps.RightUnit.
      apply RthetaFlags_runit.
  Qed.
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
  Proof.
    split.
    - (* monoid_assoc *)
      simpl.
      unfold BinOps.Associative.
      apply RthetaFlags_safe_assoc.
    - (* monoid_lunit *)
      simpl.
      unfold BinOps.LeftUnit.
      apply RthetaFlags_safe_lunit.
    - (* monoid_runit *)
      simpl.
      unfold BinOps.RightUnit.
      apply RthetaFlags_safe_runit.
  Qed.

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
  Proof.
    simpl_relation.
  Qed.

  Global Instance liftRthetaP_proper
         (P: CarrierA -> Prop)
         (P_mor: Proper ((=) ==> iff) P)
    :
      Proper ((=) ==> iff) (@liftRthetaP P).
  Proof.
    unfold liftRthetaP.
    solve_proper.
  Qed.

  Global Instance Is_ValX_proper:
      Proper ((=) ==> (=) ==> (iff)) (Is_ValX).
  Proof.
    unfold Is_ValX.
    solve_proper.
  Qed.

  Ltac unfold_Rtheta'_equiv := unfold equiv, Rtheta'_equiv in *.

  Global Instance Rtheta_Reflexive_equiv:
    @Reflexive (Rtheta' fm) Rtheta'_equiv.
  Proof.
    unfold Reflexive.
    destruct x; (unfold_Rtheta'_equiv; crush).
  Qed.

  Global Instance Rtheta_Symmetric_equiv:
    @Symmetric (Rtheta' fm) Rtheta'_equiv.
  Proof.
    unfold Symmetric.
    destruct x; (unfold_Rtheta'_equiv; crush).
  Qed.

  Global Instance Rtheta_Transitive_equiv:
    @Transitive (Rtheta' fm) Rtheta'_equiv.
  Proof.
    unfold Transitive.
    destruct x; (unfold_Rtheta'_equiv; crush).
  Qed.

  Global Instance Rtheta_Equivalence_equiv:
    @Equivalence (Rtheta' fm) Rtheta'_equiv.
  Proof.
    split.
    apply Rtheta_Reflexive_equiv.
    apply Rtheta_Symmetric_equiv.
    apply Rtheta_Transitive_equiv.
  Qed.

  Global Instance Rtheta_Setoid:
    @Setoid (Rtheta' fm) Rtheta'_equiv.
  Proof.
    apply Rtheta_Equivalence_equiv.
  Qed.

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
Proof.
  simpl_relation.
Qed.

Global Instance RStheta2Rtheta_proper
  : Proper ((=) ==> (=)) (RStheta2Rtheta).
Proof.
  simpl_relation.
Qed.

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
  Proof.
    unfold Decision, IsVal.
    destruct x.
    destr_bool; auto.
  Qed.

  Global Instance Is_Val_dec
         {fm:Monoid RthetaFlags}
         (x: Rtheta' fm):
    Decision (Is_Val x).
  Proof.
    unfold Decision.
    unfold Is_Val, compose.
    generalize (WriterMonadNoT.execWriter x). intros f.
    apply IsVal_dec.
  Qed.

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
  Proof.
    simpl_relation.
  Qed.

  Global Instance mkStruct_proper
         {fm:Monoid RthetaFlags}
    :
      Proper((=) ==> (=)) (@mkStruct fm).
  Proof.
    simpl_relation.
  Qed.

  Definition Is_ValZero {fm:Monoid RthetaFlags}
    := @Is_ValX fm 0.

  Global Instance Is_ValZero_dec {fm:Monoid RthetaFlags} (x:Rtheta' fm):
    Decision (Is_ValZero x).
  Proof.
    unfold Is_ValZero.
    unfold Decision.
    destruct (CarrierAequivdec (evalWriter x) zero); crush.
  Qed.

  Global Instance Is_ValZero_proper
         {fm:Monoid RthetaFlags}
    :
      Proper ((=) ==> (iff)) (@Is_ValZero fm).
  Proof.
    unfold Is_ValZero.
    solve_proper.
  Qed.

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
Import Spiral_DOT_CpdtTactics.
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
Import Spiral_DOT_CpdtTactics.Spiral.
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
  Proof.
    intros x y E.
    unfold sparsify.
    rewrite E.
    reflexivity.
  Qed.

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
Import Spiral_DOT_CpdtTactics.
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
Import Spiral_DOT_CpdtTactics.Spiral.
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

  Fixpoint Inductor (n:nat) (f:CarrierA -> CarrierA -> CarrierA)
           (initial: CarrierA) (v:CarrierA) {struct n}
    : CarrierA :=
    match n with
    | O => initial
    | S p => f (Inductor p f initial v) v
    end.

  (* --- Reduction --- *)

  (*  Reduction (fold) using single finction. In case of empty list returns 'id' value:
    Reduction f x1 .. xn b = f xn (f x_{n-1} .. (f x1 id) .. )
   *)
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

  (* --- Concat ---- *)
  Definition Concat {an bn: nat} (ab: (avector an)*(avector bn)) : avector (an+bn) :=
    match ab with
      (a,b) => Vapp a b
    end.

End HCOL_implementations.

(* === Lemmas about functions defined above === *)

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

  (* TODO: better name. Maybe suffficent to replace with ScalarProd_cons *)
  Lemma ScalarProd_reduce:
    forall n (ab: (avector (S n))*(avector (S n))),
      ScalarProd ab = plus (mult (Vhead (fst ab)) (Vhead (snd ab))) (ScalarProd (Ptail ab)).
Admitted.

  Lemma MonomialEnumerator_cons:
    forall n (x:CarrierA),
      MonomialEnumerator (S n) x = Vcons one (Scale (x, (MonomialEnumerator n x))).
Admitted.

  Lemma ScalarProd_comm: forall n (a b: avector n),
      ScalarProd (a,b) = ScalarProd (b,a).
Admitted.

  Lemma ScalarProduct_descale: forall {n} (a b: avector n) (s:CarrierA),
      [ScalarProd ((Scale (s,a)), b)] = Scale (s, [(ScalarProd (a,b))]).
Admitted.

  Lemma ScalarProduct_hd_descale: forall {n} (a b: avector n) (s:CarrierA),
      ScalarProd ((Scale (s,a)), b) = Vhead (Scale (s, [(ScalarProd (a,b))])).
Admitted.

End HCOL_implementation_facts.

Section HCOL_implementation_proper.

  Global Instance Scale_proper
         `{!Proper ((=) ==> (=) ==> (=)) mult} (n:nat)
  :
    Proper ((=) ==> (=)) (Scale (n:=n)).
  Proof.
    intros x y Ex.
    destruct x as [xa xb]. destruct y as [ya yb].
    destruct Ex as [H0 H1].
    simpl in H0, H1.
    unfold Scale.
    induction n.
    (* Case "n=0". *)
    VOtac.
    reflexivity.
    (* Case "S n". *)

    dep_destruct xb.  dep_destruct yb.  split.
    assert (HH: h=h0) by apply H1.
    rewrite HH, H0.
    reflexivity.

    setoid_replace (Vmap (mult xa) x) with (Vmap (mult ya) x0).
    replace (Vforall2_aux equiv (Vmap (mult ya) x0) (Vmap (mult ya) x0))
    with (Vforall2 equiv (Vmap (mult ya) x0) (Vmap (mult ya) x0)).
    reflexivity.

    unfold Vforall2. reflexivity.

    apply IHn. clear IHn.
    apply H1.
  Qed.

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
  Proof.
    intros p p' pE.
    dep_destruct p.
    dep_destruct p'.
    unfold ChebyshevDistance.
    inversion pE. clear pE. simpl in *.
    clear p p'.
    rewrite H, H0.
    reflexivity.
  Qed.

  Global Instance EvalPolynomial_proper (n:nat):
    Proper ((=) ==> (=) ==> (=))  (EvalPolynomial (n:=n)).
  Proof.
    intros v v' vE a a' aE.
    induction n.
    VOtac.
    reflexivity.
    rewrite 2!EvalPolynomial_reduce.
    dep_destruct v.
    dep_destruct v'.
    simpl.
    apply Vcons_equiv_elim in vE.
    destruct vE as [HE xE].
    setoid_replace (EvalPolynomial x a) with (EvalPolynomial x0 a')
      by (apply IHn; assumption).
    rewrite HE, aE.
    reflexivity.
  Qed.

  Global Instance MonomialEnumerator_proper (n:nat):
    Proper ((=) ==> (=))  (MonomialEnumerator n).
  Proof.
    intros a a' aE.
    induction n.
    reflexivity.
    rewrite 2!MonomialEnumerator_cons, 2!Vcons_to_Vcons_reord, IHn, aE.
    reflexivity.
  Qed.

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
Import Spiral_DOT_CpdtTactics.
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
Import Spiral_DOT_CpdtTactics.Spiral.
(* Coq defintions for HCOL operator language *)
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

  Definition HAppend {i n} (a:avector n)
    : avector i -> avector (i+n)
    := fun x => Vapp x a.

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

  (* Special case of pointwise *)
  Definition HAtomic
             (f: CarrierA -> CarrierA)
             `{pF: !Proper ((=) ==> (=)) f}
             (x: avector 1)
    := [f (Vhead x)].

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

    Global Instance HAtomic_HOperator
           (f: CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=)) f}:
      HOperator (HAtomic f).
    Proof.
      unfold HOperator. split; try (apply vec_Setoid).
      intros x y E.
      unfold HAtomic.
      vec_index_equiv i ip.
      simpl.
      dep_destruct i.
      rewrite E.
      reflexivity.
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
Import Spiral_DOT_CpdtTactics.
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
Import Spiral_DOT_CpdtTactics.Spiral.
(* HCOL metaoperators *)
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
Import Spiral_DOT_CpdtTactics.
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
Import Spiral_DOT_CpdtTactics.Spiral.
(* Template HCOL. HCOL meta-operators *)
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

Definition HCross
           {i1 o1 i2 o2}
           (f: avector i1 -> avector o1)
           (g: avector i2 -> avector o2):
  avector (i1+i2) -> avector (o1+o2)
  := pair2vector ∘ Cross (f, g) ∘ (@Vbreak CarrierA i1 i2).

Global Instance HCross_THOperator2 {i1 o1 i2 o2}:
  THOperator2 (@HCross i1 o1 i2 o2).
Proof.
  intros f f' Ef g g' Eg x y Ex.
  unfold HCross, compose, pair2vector, vector2pair.
  destruct (Vbreak x) as [x0 x1] eqn: X.
  destruct (Vbreak y) as [y0 y1] eqn: Y.
  assert(Ye: Vbreak y = (y0, y1)) by crush.
  assert(Xe: Vbreak x = (x0, x1)) by crush.
  rewrite Ex in Xe.
  rewrite Xe in Ye.
  clear X Y Xe Ex.
  inversion Ye. rename H into Ey, H0 into Ex.
  simpl in *.

  assert(A1: f x0 = f' y0).
  apply Ef, Ey.
  rewrite A1.

  assert(A2: g x1 = g' y1).
  apply Eg, Ex.
  rewrite A2.
  reflexivity.
Qed.

Definition HStack
           {i1 o1 o2}
           (f: avector i1 -> avector o1)
           (g: avector i1 -> avector o2)
  : avector i1 -> avector (o1+o2) :=
  fun x =>  pair2vector (Stack (f, g) x).

Global Instance HStack_THOperator2 {i1 o1 o2}:
  THOperator2 (@HStack i1 o1 o2).
Proof.
  intros f f' Ef g g' Eg x y Ex.
  unfold HStack, compose, pair2vector, vector2pair, Stack.
  setoid_replace (f x) with (f' y).
  setoid_replace (g x) with (g' y).
  reflexivity.
  apply Eg; assumption.
  apply Ef; assumption.
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

Definition HTLess {i1 i2 o}
           (f: avector i1 -> avector o)
           (g: avector i2 -> avector o)
  : avector (i1+i2) -> avector o
  := fun v0 => let (v1,v2) := vector2pair i1 v0 in
               ZVLess (f v1, g v2).

Global Instance HTLess_THOperator2 {i1 i2 o}:
  THOperator2 (@HTLess i1 i2 o).
Proof.
  intros f f' Ef g g' Eg x y Ex.
  unfold HTLess, compose, pair2vector, vector2pair, ZVLess.
  destruct (Vbreak x) as [x0 x1] eqn: X.
  destruct (Vbreak y) as [y0 y1] eqn: Y.
  assert(Ye: Vbreak y = (y0, y1)) by crush.
  assert(Xe: Vbreak x = (x0, x1)) by crush.
  rewrite Ex in Xe.
  rewrite Xe in Ye.
  clear X Y Xe Ex.
  inversion Ye. rename H into Ey, H0 into Ex.
  simpl in *.
  setoid_replace (f x0) with (f' y0).
  setoid_replace (g x1) with (g' y1).
  reflexivity.
  apply Eg, Ex.
  apply Ef, Ey.
Qed.

(* Per Vadim's discussion with Franz on 2015-12-14, DirectSum is just
same as Cross, where input vectors are passed as concateneated
vector. Since Coq formalization of HCross is already dfined this way
we just alias DirectSum to it.
 *)
Notation HTDirectSum := HCross.

(* Not sure if this is needed *)
Global Instance HTDirectSum_THOperator2 {i1 o1 i2 o2}:
  THOperator2 (@HTDirectSum i1 o1 i2 o2) := HCross_THOperator2.




End THCOL.

End Spiral.

End Spiral_DOT_THCOL.

Module Spiral_DOT_FinNatSet.
Module Spiral.
Module FinNatSet.
Import Spiral_DOT_CpdtTactics.
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
Import Spiral_DOT_CpdtTactics.Spiral.
Export Coq.Init.Specif.
Export Coq.Sets.Ensembles.
Import Coq.Logic.Decidable.

Notation FinNat n := {x:nat | (x<n)}.
Notation FinNatSet n := (Ensemble (FinNat n)).

Definition mkFinNat {n} {j:nat} (jc:j<n) : FinNat n := @exist _ (gt n) j jc.

Definition singleton {n:nat} (i:nat): FinNatSet n :=
  fun x => proj1_sig x = i.

Definition FinNatSet_dec {n: nat} (s: FinNatSet n) := forall x, decidable (s x).

Lemma Full_FinNatSet_dec:
  forall i : nat, FinNatSet_dec (Full_set (FinNat i)).
Admitted.

Lemma Empty_FinNatSet_dec:
  forall i : nat, FinNatSet_dec (Empty_set (FinNat i)).
Admitted.

Lemma Union_FinNatSet_dec
      {n}
      {a b: FinNatSet n}:
  FinNatSet_dec a -> FinNatSet_dec b ->
  FinNatSet_dec (Union _ a b).
Admitted.

Lemma Union_Empty_set_runit:
  forall n B, FinNatSet_dec B ->
         Same_set _ (Union (FinNat n) B (Empty_set (FinNat n))) B.
Admitted.

Lemma Union_Empty_set_lunit:
  forall n B, FinNatSet_dec B ->
         Same_set _ B (Union (FinNat n) B (Empty_set (FinNat n))).
Admitted.

Lemma Union_comm
      {U:Type}
      {B C: Ensemble U}:
  forall x, In _ (Union U B C) x <-> In _ (Union U C B) x.
Admitted.

End FinNatSet.

End Spiral.

End Spiral_DOT_FinNatSet.

Module Spiral_DOT_IndexFunctions.
Module Spiral.
Module IndexFunctions.
Import Spiral_DOT_CpdtTactics.
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
Import Spiral_DOT_CpdtTactics.Spiral.

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

  Lemma index_map_range_set_id:
    ∀ (i o : nat) (f : index_map i o) (j : nat) (jc : j < i),
      index_map_range_set f (⟦ f ⟧ j ↾ « f » j jc).
Admitted.

  Lemma h_index_map_range_set_dec
        {domain range: nat}
        (b s: nat)
        {range_bound: forall x, x<domain -> (b+x*s) < range}:
    FinNatSet_dec (index_map_range_set (@h_index_map domain range b s range_bound)).
Admitted.

End IndexMapSets.


End IndexFunctions.

End Spiral.

End Spiral_DOT_IndexFunctions.

Module Spiral_DOT_SigmaHCOL.
Module Spiral.
Module SigmaHCOL.
Import Spiral_DOT_CpdtTactics.
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
Import Spiral_DOT_CpdtTactics.Spiral.
(* Coq defintions for Sigma-HCOL operator language *)
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

    Class SHOperator_Facts
          {i o:nat}
          (xop: @SHOperator i o)
      :=
        {
          (* [in_index_set] membership is decidabe *)
          in_dec: FinNatSet_dec (in_index_set xop);

          (* [out_index_set] membership is decidabe *)
          out_dec: FinNatSet_dec (out_index_set xop);

          (* only values in [in_index_set] affect output *)
          in_as_domain:
            forall x y,
              vec_equiv_at_set x y (in_index_set xop) ->
              op xop x = op xop y;

          (* sufficiently (values in right places, no info on empty
          spaces) filled input vector guarantees properly (values are
          only where values expected) filled output vector *)
          out_as_range: forall v,
              (forall j (jc:j<i), in_index_set xop (mkFinNat jc) -> Is_Val (Vnth v jc))
              ->
              (forall j (jc:j<o), out_index_set xop (mkFinNat jc) -> Is_Val (Vnth (op xop v) jc));

          (* never generate values at sparse positions of output vector *)
          no_vals_at_sparse: forall v,
              (forall j (jc:j<o), ¬ out_index_set xop (mkFinNat jc) -> Is_Struct (Vnth (op xop v) jc));

          (* As long there are no collisions in expected non-sparse places, none is expected in nonsparce places on outpyt*)
          no_coll_range: forall v,
              (forall j (jc:j<i), in_index_set xop (mkFinNat jc) -> Not_Collision (Vnth v jc))
              ->
              (forall j (jc:j<o), out_index_set xop (mkFinNat jc) -> Not_Collision (Vnth (op xop v) jc));
          (* Never generate collisions on sparse places *)
          no_coll_at_sparse: forall v,
              (forall j (jc:j<o), ¬ out_index_set xop (mkFinNat jc) -> Not_Collision (Vnth (op xop v) jc));
        }.

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

    Lemma shrink_op_family_facts
          (i o k : nat)
          (op_family : SHOperatorFamily)
          (facts: ∀ (j : nat) (jc : j < S k),
              @SHOperator_Facts i o (family_member op_family j jc)):
      (forall (j : nat) (jc : j < k),
          @SHOperator_Facts i o (family_member (shrink_op_family op_family) j jc)).
Admitted.

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

    Lemma fmaily_in_index_set_dec
          (i o k : nat)
          (op_family : @SHOperatorFamily i o k)
          (op_family_facts: forall (j : nat) (jc : j < k),
              SHOperator_Facts (family_member op_family j jc)):
      FinNatSet_dec (family_in_index_set op_family).
Admitted.

    Lemma fmaily_out_index_set_dec
          (i o k : nat)
          (op_family : @SHOperatorFamily i o k)
          (op_family_facts: forall (j : nat) (jc : j < k),
              SHOperator_Facts (family_member op_family j jc)):
      FinNatSet_dec (family_out_index_set op_family).
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

Section StructuralProperies.

  Section FlagsMonoidGenericStructuralProperties.
    Variable fm:Monoid RthetaFlags.
    Variable fml:@MonoidLaws RthetaFlags RthetaFlags_type fm.

    Global Instance liftM_HOperator_Facts
           {i o}
           (hop: avector i -> avector o)
           `{HOP: HOperator i o hop}
      : SHOperator_Facts fm (liftM_HOperator fm hop).
    Proof.
      split.
      -
        apply Full_FinNatSet_dec.
      -
        apply Full_FinNatSet_dec.
      -
        intros x y H.

        simpl in *.
        assert (E: x=y).
        {
          vec_index_equiv j jc.
          apply H.
          constructor.
        }
        rewrite E.
        reflexivity.
      -
        intros v H j jc H0.
        simpl in *.
        unfold liftM_HOperator', compose, sparsify, densify.
        rewrite Vnth_map.
        apply IsVal_mkValue.
      -
        intros v j jc H.
        contradict H.
        split.
      -
        intros v D j jc S.
        simpl in *.
        unfold liftM_HOperator', compose, sparsify, densify.
        rewrite Vnth_map.
        apply Not_Collision_mkValue.
      -
        intros v j jc H.
        unfold not in H.
        destruct H.
        split.
    Qed.

    Global Instance SHCompose_Facts
           {i1 o2 o3}
           (op1: @SHOperator fm o2 o3)
           (op2: @SHOperator fm i1 o2)
           `{fop1: SHOperator_Facts fm _ _ op1}
           `{fop2: SHOperator_Facts fm _ _ op2}
           (compat: Included _ (in_index_set fm op1) (out_index_set fm op2))
      : SHOperator_Facts fm (SHCompose fm op1 op2).
    Proof.
      split.
      -
        apply fop2.
      -
        apply fop1.
      - intros x y H.
        destruct op1, op2, fop1, fop2.
        simpl in *.
        unfold compose in *.
        apply in_as_domain0.
        intros j jc H0.
        apply Vnth_arg_equiv.
        apply in_as_domain1.
        intros j0 jc0 H1.
        apply H, H1.
      -
        intros v D j jc S.
        destruct op1, op2, fop1, fop2.
        simpl in *.
        unfold compose in *.
        apply out_as_range0.
        + intros.
          apply out_as_range1.
          apply D.
          apply compat.
          apply H.
        + apply S.
      -
        intros v j jc S.
        destruct op1, op2, fop1, fop2.
        simpl in *.
        unfold compose in *.
        apply no_vals_at_sparse0.
        apply S.
      -
        intros v D j jc S.
        destruct op1, op2, fop1, fop2.
        simpl in *.
        unfold compose in *.
        apply no_coll_range0.
        intros j0 jc0 H.
        apply no_coll_range1.
        intros j1 jc1 H0.
        apply D.
        apply H0.
        apply compat.
        apply H.
        apply S.
      -
        intros v j jc H.
        destruct op1, op2, fop1, fop2.
        simpl in *.
        unfold compose in *.
        apply no_coll_at_sparse0.
        apply H.
    Qed.

    Global Instance Gather_Facts
           {i o: nat}
           (f: index_map o i)
      : SHOperator_Facts fm (Gather fm f).
    Proof.
      split.
      -
        unfold in_index_set.
        unfold index_map_range_set.
        unfold FinNatSet_dec.
        intros x.
        apply Decidable_decision.
        apply in_range_dec.
      -
        simpl.
        apply Full_FinNatSet_dec.
      - intros x y H.
        simpl in *.
        vec_index_equiv j jc.
        rewrite 2!Gather'_spec.
        unfold VnthIndexMapped.
        apply H.
        unfold mkFinNat.
        apply index_map_range_set_id.
        auto.
        auto.
      -
        intros v H j jc S.
        simpl.
        rewrite Gather'_spec.
        unfold VnthIndexMapped.
        apply H.
        simpl.
        unfold mkFinNat.
        apply index_map_range_set_id.
        auto.
      -
        intros v j jc S.
        contradict S.
        simpl.
        split.
      -
        intros v D j jc S.
        simpl.
        rewrite Gather'_spec.
        unfold VnthIndexMapped.
        apply D.
        simpl.
        unfold mkFinNat.
        apply index_map_range_set_id.
        auto.
      -
        intros v j jc H.
        simpl in *.
        destruct H.
        split.
    Qed.

    Global Instance SHPointwise_Facts
           {n: nat}
           (f: { i | i<n} -> CarrierA -> CarrierA)
           `{pF: !Proper ((=) ==> (=) ==> (=)) f}:
      SHOperator_Facts fm (SHPointwise fm f).
    Proof.
      split.
      -
        simpl.
        apply Full_FinNatSet_dec.
      -
        simpl.
        apply Full_FinNatSet_dec.
      -
        intros x y H.
        simpl in *.
        assert (E: x=y).
        {
          vec_index_equiv j jc.
          apply H.
          constructor.
        }
        rewrite E.
        reflexivity.
      -
        intros v H j jc S.
        simpl in *.
        unfold SHPointwise'.
        rewrite Vbuild_nth.
        apply Is_Val_liftM.
        apply H, S.
      -
        intros v j jc S.
        contradict S.
        simpl.
        split.
      - intros v D j jc S.
        simpl in *.
        unfold SHPointwise'.
        rewrite Vbuild_nth.
        apply Not_Collision_liftM.
        apply D, S.
      - intros v D j jc S.
        simpl in *.
        destruct jc.
        split.
    Qed.

  End FlagsMonoidGenericStructuralProperties.

  Global Instance Scatter_Rtheta_Facts
         {i o: nat}
         (f: index_map i o)
         {f_inj: index_map_injective f}
         (idv: CarrierA)
    :
    SHOperator_Facts Monoid_RthetaFlags (Scatter Monoid_RthetaFlags f (f_inj:=f_inj) idv).
  Proof.
    split.
    -
      simpl.
      apply Full_FinNatSet_dec.
    -
      unfold out_index_set.
      unfold index_map_range_set.
      unfold FinNatSet_dec.
      intros x.
      apply Decidable_decision.
      apply in_range_dec.
    - intros x y H.
      simpl in *.
      assert (E: x=y).
      {
        vec_index_equiv j jc.
        apply H.
        constructor.
      }
      rewrite E.
      reflexivity.
    -
      intros v H j jc S.
      simpl.
      unfold Scatter' in *.
      rewrite Vbuild_nth.
      break_match.
      + simpl in *.
        generalize dependent (gen_inverse_index_f_spec f j i0); intros f_spec.
        apply H.
        constructor.
      +
        simpl in *.
        unfold index_map_range_set in S.
        simpl in *.
        congruence.
    -
      intros v j jc S.
      simpl in *.

      unfold index_map_range_set in S.
      unfold Scatter'.
      rewrite Vbuild_nth.
      break_match.
      *
        simpl in S.
        congruence.
      *
        apply Is_Struct_mkSZero.
    - intros v D j jc S.
      simpl.
      unfold Scatter' in *.
      rewrite Vbuild_nth.
      break_match.
      + simpl in *.
        generalize dependent (gen_inverse_index_f_spec f j i0); intros f_spec.
        apply D.
        constructor.
      +
        simpl in *.
        unfold index_map_range_set in S.
        simpl in *.
        congruence.
    -
      intros v D j jc S.
      simpl in *.
      unfold Scatter' in *.
      rewrite Vbuild_nth in S.
      break_match; crush.
  Qed.


  Global Instance SHBinOp_RthetaSafe_Facts
         {o}
         (f: nat -> CarrierA -> CarrierA -> CarrierA)
         `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}:
    SHOperator_Facts Monoid_RthetaSafeFlags (SHBinOp f (o:=o)).
  Proof.
    split.
    -
      apply Full_FinNatSet_dec.
    -
      apply Full_FinNatSet_dec.
    -
      intros x y H.
      simpl in *.
      assert (E: x=y).
      {
        vec_index_equiv j jc.
        apply H.
        constructor.
      }
      rewrite E.
      reflexivity.
    -
      intros v H j jc S.
      simpl in *.
      assert(jc2: (j+o)<o+o) by omega.
      assert(jc1:j<o+o) by omega.
      rewrite (@SHBinOp'_nth Monoid_RthetaSafeFlags _ o f pF v j jc jc1 jc2).
      apply Is_Val_Safe_liftM2; (apply H; constructor).
    -
      intros v j jc S.
      contradict S.
      simpl.
      split.
    - intros v D j jc S.
      simpl in *.
      assert(jc2: (j+o)<o+o) by omega.
      assert(jc1:j<o+o) by omega.
      rewrite (@SHBinOp'_nth _  _ o f pF v j jc jc1 jc2).
      apply Not_Collision_Safe_liftM2; apply D; constructor.
    -
      intros v D j jc S.
      simpl in *.
      destruct jc.
      split.
  Qed.

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

  (* TODO: move *)
  Lemma Is_Val_In_outset
        (i o : nat)
        (v : rvector i)
        (j : nat) (jc : j < o)
        (O : SHOperator Monoid_RthetaFlags)
        (F: SHOperator_Facts Monoid_RthetaFlags O)
        (D: FinNatSet_dec (out_index_set Monoid_RthetaFlags O))
    :
      Is_Val (Vnth (op Monoid_RthetaFlags O v) jc) → out_index_set Monoid_RthetaFlags O (mkFinNat jc).
Admitted.

  Global Instance IUnion_Facts
         {i o k}
         (dot: CarrierA -> CarrierA -> CarrierA)
         `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
         (initial: CarrierA)
         (op_family: @SHOperatorFamily Monoid_RthetaFlags i o k)
         (op_family_facts: forall j (jc:j<k), SHOperator_Facts Monoid_RthetaFlags (family_member _ op_family j jc))
         (compat: forall m (mc:m<k) n (nc:n<k), m ≢ n -> Disjoint _
                                                                  (out_index_set _ (family_member _ op_family m mc))
                                                                  (out_index_set _ (family_member _ op_family n nc))
         )
    : SHOperator_Facts _ (IUnion dot initial op_family).
  Proof.
    split.
    -
      simpl in *.
      apply fmaily_in_index_set_dec.
      apply op_family_facts.
    -
      simpl in *.
      apply fmaily_out_index_set_dec.
      apply op_family_facts.
    -
      intros x y H.
      simpl in *.
      vec_index_equiv j jc.
      unfold Diamond'.
      unfold Apply_Family'.

      rewrite 2!AbsorbMUnion'Index_Vbuild.
      unfold UnionFold.

      f_equiv.
      apply Vforall2_intro_nth.
      intros i0 ip.
      rewrite 2!Vbuild_nth.
      apply Vnth_arg_equiv.
      clear j jc; rename i0 into j, ip into jc.

      apply op_family_facts.

      apply vec_equiv_at_subset with (h:=(family_in_index_set Monoid_RthetaFlags op_family)).
      apply family_in_set_includes_members.
      apply H.
      apply MonoidLaws_RthetaFlags.
      apply MonoidLaws_RthetaFlags.
    -
      intros v H j jc S.
      simpl in *.

      unfold Diamond'.
      unfold Apply_Family'.

      rewrite AbsorbMUnion'Index_Vbuild.
      apply Is_Val_UnionFold.

      apply family_out_set_implies_members in S.
      destruct S as [x X].
      destruct X as [xc X].

      apply Vexists_Vbuild.
      eexists.
      eexists.

      apply out_as_range.
      + apply op_family_facts.
      + intros j0 jc0 H0.
        apply H.
        eapply family_in_set_includes_members.
        unfold In.
        apply H0.
      +
        apply X.
      +
        apply MonoidLaws_RthetaFlags.
    -
      intros v j jc S.
      simpl in *.

      unfold IUnion, Diamond', Apply_Family'.
      rewrite AbsorbMUnion'Index_Vbuild.
      unfold Is_Struct, compose, not.
      intros G.
      apply Is_Val_UnionFold in G.
      apply Vexists_Vbuild in G.
      destruct G as [t [tc G]].
      apply op_family_facts in G.
      * tauto.
      *
        (* G and S contradict *)
        assert(N: ¬ out_index_set Monoid_RthetaFlags
                    (family_member Monoid_RthetaFlags op_family t tc) (mkFinNat jc)).
        {
          contradict S.
          apply family_out_set_includes_members in S.
          auto.
        }
        apply no_vals_at_sparse with (v:=v) in N.
        unfold Is_Struct, compose, not in N.

        unfold get_family_op in G.
        auto.

        apply op_family_facts.
      *
        apply MonoidLaws_RthetaFlags.
    -
      (* no_coll_range *)
      intros v D j jc S.
      simpl in *.
      unfold Diamond', Apply_Family'.

      rewrite AbsorbMUnion'Index_Vbuild.
      apply UnionFold_Non_Collision.
      +
        (* no collisions on j-th row accross all families *)
        apply family_out_set_implies_members in S.
        destruct S as [d [dc S]].

        apply Vforall_Vbuild.
        intros t tc.

        destruct (eq_nat_dec d t).
        *
          (* family member in out set *)
          apply no_coll_range.
          --
            auto.
          --
            intros m mc H.
            eapply D, family_in_set_includes_members, H.
          --
            subst.
            replace tc with dc by apply le_unique.
            apply S.
        *
          (* family member in out set *)
          apply no_coll_at_sparse.
          --
            auto.
          --
            specialize (compat d dc t tc n).
            inversion compat as [C]; clear compat.
            specialize (C (mkFinNat jc)). unfold In in C.
            contradict C.
            split; assumption.
      +
        intros m mc n nc [M N].
        rewrite Vbuild_nth in M.
        rewrite Vbuild_nth in N.

        destruct (eq_nat_dec m n) as [E | NE].
        apply E.

        specialize (compat m mc n nc NE).
        inversion compat as [C].
        specialize (C (mkFinNat jc)).

        unfold get_family_op in M.
        unfold get_family_op in N.

        apply Is_Val_In_outset in M; try apply op_family_facts.
        apply Is_Val_In_outset in N; try apply op_family_facts.

        contradict C.

        unfold In.
        apply Intersection_intro.
        apply M.
        apply N.
      +
        apply MonoidLaws_RthetaFlags.
    -
      (* no_coll_at_sparse *)
      intros v j jc S.
      simpl in *.
      unfold Diamond', Apply_Family'.

      rewrite AbsorbMUnion'Index_Vbuild.
      apply UnionFold_Non_Collision.

      +
        (* no collisions on j-th row accross all families *)
        assert(forall  (t : nat) (tc : t < k),
                  not (out_index_set Monoid_RthetaFlags (family_member Monoid_RthetaFlags op_family t tc)
                                     (mkFinNat jc))).
        {
          intros t tc.
          contradict S.
          apply family_out_set_implies_members.
          exists t, tc.
          apply S.
        }

        apply Vforall_Vbuild.
        intros t tc.

        unfold get_family_op.
        apply no_coll_at_sparse.
        apply op_family_facts.
        apply H.
      +
        intros m mc n _ [M _].
        rewrite Vbuild_nth in M.
        unfold get_family_op in M.
        apply Is_Val_In_outset in M; try apply op_family_facts.
        contradict S.
        apply family_out_set_implies_members.
        exists m, mc.
        apply M.
      +
        apply MonoidLaws_RthetaFlags.
  Qed.

  Global Instance IReduction_Facts
         {i o k}
         (dot: CarrierA -> CarrierA -> CarrierA)
         `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
         (initial: CarrierA)
         (op_family: @SHOperatorFamily Monoid_RthetaSafeFlags i o k)
         (op_family_facts: forall j (jc:j<k), SHOperator_Facts Monoid_RthetaSafeFlags (family_member _ op_family j jc))
    : SHOperator_Facts _ (IReduction dot initial op_family).
  Proof.
    split.
    -
      simpl in *.
      apply fmaily_in_index_set_dec.
      apply op_family_facts.
    -
      simpl in *.
      apply fmaily_out_index_set_dec.
      apply op_family_facts.
    -
      intros x y H.
      simpl in *.
      vec_index_equiv j jc.
      unfold Diamond'.
      unfold Apply_Family'.

      rewrite 2!AbsorbMUnion'Index_Vbuild.
      unfold UnionFold.

      f_equiv.
      apply Vforall2_intro_nth.
      intros i0 ip.
      rewrite 2!Vbuild_nth.
      apply Vnth_arg_equiv.
      clear j jc; rename i0 into j, ip into jc.

      apply op_family_facts.

      apply vec_equiv_at_subset with (h:=(family_in_index_set Monoid_RthetaSafeFlags op_family)).
      apply family_in_set_includes_members.
      apply H.
      apply MonoidLaws_SafeRthetaFlags.
      apply MonoidLaws_SafeRthetaFlags.
    -
      intros v D j jc S.
      simpl in *.

      unfold Diamond'.
      unfold Apply_Family'.

      rewrite AbsorbMUnion'Index_Vbuild.
      apply Is_Val_UnionFold_Safe.

      apply family_out_set_implies_members in S.
      destruct S as [x X].
      destruct X as [xc X].

      apply Vexists_Vbuild.
      eexists.
      eexists.

      apply out_as_range.
      + apply op_family_facts.
      + intros j0 jc0 H.
        apply D.
        eapply family_in_set_includes_members.
        unfold In.
        apply H.
      +
        apply X.
      +
      apply MonoidLaws_SafeRthetaFlags.
    -
      intros v j jc S.
      simpl in *.

      unfold IUnion, Diamond', Apply_Family'.
      rewrite AbsorbMUnion'Index_Vbuild.
      unfold Is_Struct, compose, not.
      intros G.

      apply Is_Val_UnionFold_Safe in G.
      apply Vexists_Vbuild in G.
      destruct G as [t [tc G]].
      apply op_family_facts in G.
      * tauto.
      *
        (* G and S contradict *)
        assert(N: ¬ out_index_set Monoid_RthetaSafeFlags
                    (family_member Monoid_RthetaSafeFlags op_family t tc) (mkFinNat jc)).
        {
          contradict S.
          apply family_out_set_includes_members in S.
          auto.
        }
        apply no_vals_at_sparse with (v:=v) in N.
        unfold Is_Struct, compose, not in N.

        unfold get_family_op in G.
        auto.

        apply op_family_facts.
      *
        apply MonoidLaws_SafeRthetaFlags.
    -
      (* no_coll_range *)
      intros v D j jc S.
      simpl in *.
      unfold Diamond', Apply_Family'.

      rewrite AbsorbMUnion'Index_Vbuild.
      apply UnionFold_Safe_Non_Collision.

      (* no collisions on j-th row accross all families *)
      apply Vforall_Vbuild.
      intros t tc.

      destruct (op_family_facts t tc).
      specialize (out_dec0 (mkFinNat jc)).
      destruct out_dec0 as [O | NO].

      + apply no_coll_range.
        * auto.
        * intros m mc H.
          eapply D, family_in_set_includes_members, H.
        * auto.
      +
        apply no_coll_at_sparse; auto.
      +
        apply MonoidLaws_SafeRthetaFlags.
    -
      (* no_coll_at_sparse *)
      intros v j jc S.
      simpl in *.
      unfold Diamond', Apply_Family'.

      rewrite AbsorbMUnion'Index_Vbuild.
      apply UnionFold_Safe_Non_Collision.
      +
        (* no collisions on j-th row accross all families *)
        assert(forall  (t : nat) (tc : t < k),
                  not (out_index_set Monoid_RthetaSafeFlags (family_member Monoid_RthetaSafeFlags op_family t tc)
                                     (mkFinNat jc))).
        {
          intros t tc.
          contradict S.
          apply family_out_set_implies_members.
          exists t, tc.
          apply S.
        }

        apply Vforall_Vbuild.
        intros t tc.

        unfold get_family_op.
        apply no_coll_at_sparse.
        apply op_family_facts.
        apply H.
      +
        apply MonoidLaws_SafeRthetaFlags.
  Qed.

End StructuralProperies.


End SigmaHCOL.

End Spiral.

End Spiral_DOT_SigmaHCOL.

Module Spiral_DOT_TSigmaHCOL.
Module Spiral.
Module TSigmaHCOL.
Import Spiral_DOT_CpdtTactics.
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
Import Spiral_DOT_CpdtTactics.Spiral.
(* Template HCOL. HCOL meta-operators *)
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


Global Instance SafeCast_Facts
       {i o}
       (xop: @SHOperator Monoid_RthetaSafeFlags i o)
       `{fop: SHOperator_Facts Monoid_RthetaSafeFlags _ _ xop}
  :
    SHOperator_Facts Monoid_RthetaFlags (SafeCast xop).
Proof.
  split.
  - apply fop.
  - apply fop.
  - intros x y H.
    simpl.
    unfold SafeCast, SafeCast', compose, rsvector2rvector, rvector2rsvector in *.
    f_equiv.
    apply fop.
    simpl in *.

    unfold vec_equiv_at_set.
    intros j jc S.
    specialize (H j jc S).
    rewrite 2!Vnth_map.
    f_equiv.
    apply H.
  -
    intros v H j jc S.
    unfold SafeCast, SafeCast', compose, rsvector2rvector, rvector2rsvector in *.
    simpl in *.

    rewrite Vnth_map, <- Is_Val_RStheta2Rtheta.
    apply out_as_range; try assumption.
    intros t tc I.

    rewrite Vnth_map, <- Is_Val_Rtheta2RStheta.
    apply H, I.
  -
    intros v j jc S.
    unfold SafeCast, SafeCast', compose, rsvector2rvector, rvector2rsvector in *.
    simpl in *.

    rewrite Vnth_map, <- Is_Struct_RStheta2Rtheta.
    apply no_vals_at_sparse; assumption.
  -
    intros v H j jc S.
    unfold SafeCast, SafeCast', compose, rsvector2rvector, rvector2rsvector in *.
    simpl in *.

    rewrite Vnth_map, <- Not_Collision_RStheta2Rtheta.
    apply no_coll_range; try assumption.
    intros t tc I.

    rewrite Vnth_map, <- Not_Collision_Rtheta2RStheta.
    apply H, I.
  -
    intros v j jc S.
    unfold SafeCast, SafeCast', compose, rsvector2rvector, rvector2rsvector in *.
    simpl in *.

    rewrite Vnth_map, <- Not_Collision_RStheta2Rtheta.
    apply no_coll_at_sparse; assumption.
Qed.

Global Instance UnSafeCast_Facts
       {i o}
       (xop: @SHOperator Monoid_RthetaFlags i o)
       `{fop: SHOperator_Facts Monoid_RthetaFlags _ _ xop}
  :
    SHOperator_Facts Monoid_RthetaSafeFlags (UnSafeCast xop).
Proof.
  split.
  - apply fop.
  - apply fop.
  - intros x y H.
    simpl.
    unfold UnSafeCast, UnSafeCast', compose, rsvector2rvector, rvector2rsvector in *.
    f_equiv.
    apply fop.
    simpl in *.

    unfold vec_equiv_at_set.
    intros j jc S.
    specialize (H j jc S).
    rewrite 2!Vnth_map.
    f_equiv.
    apply H.
  -
    intros v H j jc S.
    unfold UnSafeCast, UnSafeCast', compose, rsvector2rvector, rvector2rsvector in *.
    simpl in *.

    rewrite Vnth_map. rewrite <- Is_Val_Rtheta2RStheta.
    apply out_as_range; try assumption.
    intros t tc I.

    rewrite Vnth_map, <- Is_Val_RStheta2Rtheta.
    apply H, I.
  -
    intros v j jc S.
    unfold UnSafeCast, UnSafeCast', compose, rsvector2rvector, rvector2rsvector in *.
    simpl in *.

    rewrite Vnth_map, <- Is_Struct_Rtheta2RStheta.
    apply no_vals_at_sparse; assumption.
  -
    intros v H j jc S.
    unfold UnSafeCast, UnSafeCast', compose, rsvector2rvector, rvector2rsvector in *.
    simpl in *.

    rewrite Vnth_map, <- Not_Collision_Rtheta2RStheta.
    apply no_coll_range; try assumption.
    intros t tc I.

    rewrite Vnth_map, <- Not_Collision_RStheta2Rtheta.
    apply H, I.
  -
    intros v j jc S.
    unfold UnSafeCast, UnSafeCast', compose, rsvector2rvector, rvector2rsvector in *.
    simpl in *.

    rewrite Vnth_map, <- Not_Collision_Rtheta2RStheta.
    apply no_coll_at_sparse; assumption.
Qed.

Global Instance HTSUMUnion_Facts
       {i o}
       (dot: CarrierA -> CarrierA -> CarrierA)
       `{dot_mor: !Proper ((=) ==> (=) ==> (=)) dot}
       (op1 op2: @SHOperator Monoid_RthetaFlags i o)
       `{fop1: SHOperator_Facts Monoid_RthetaFlags _ _ op1}
       `{fop2: SHOperator_Facts Monoid_RthetaFlags _ _ op2}
       (compat: Disjoint _
                         (out_index_set _ op1)
                         (out_index_set _ op2)
       )
  : SHOperator_Facts Monoid_RthetaFlags (HTSUMUnion Monoid_RthetaFlags dot op1 op2).
Proof.
  split.
  -
    apply Union_FinNatSet_dec.
    apply fop1.
    apply fop2.
  -
    apply Union_FinNatSet_dec.
    apply fop1.
    apply fop2.
  - intros x y H.
    destruct op1, op2, fop1, fop2.
    simpl in *.
    unfold HTSUMUnion', Vec2Union in *.
    vec_index_equiv j jc.
    rewrite 2!Vnth_map2.
    f_equiv.
    + apply dot_mor.
    +
      apply Vnth_arg_equiv.
      apply in_as_domain0.
      apply vec_equiv_at_Union in H.
      apply H.
    +
      apply Vnth_arg_equiv.
      apply in_as_domain1.
      apply vec_equiv_at_Union in H.
      apply H.
  - intros v D j jc S.
    simpl in *.
    unfold HTSUMUnion', Vec2Union in *.
    rewrite Vnth_map2.
    apply ValUnionIsVal.
    destruct op1, op2, fop1, fop2.
    simpl in *.
    dep_destruct S.
    + left.
      apply out_as_range0.
      intros j0 jc0 H0.
      apply D.
      left.
      apply H0.
      apply i0.
    + right.
      apply out_as_range1.
      intros j0 jc0 H0.
      apply D.
      right.
      apply H0.
      apply i0.
  -
    intros v j jc S.
    unfold HTSUMUnion, HTSUMUnion', Vec2Union.
    simpl.
    rewrite Vnth_map2.
    apply StructUnionIsStruct.
    unfold Is_Struct, compose, not.
    split.
    +
      intros H.
      apply fop1 in H.
      inversion H.
      unfold HTSUMUnion, HTSUMUnion', Vec2Union in S.
      simpl in *.
      unfold not in S.
      contradict S.
      apply Union_introl.
      apply S.
    +
      intros H.
      apply fop2 in H.
      inversion H.
      unfold HTSUMUnion, HTSUMUnion', Vec2Union in S.
      simpl in *.
      unfold not in S.
      contradict S.
      apply Union_intror.
      apply S.
  -
    (* no_coll_range *)
    intros v D j jc S.
    unfold HTSUMUnion, HTSUMUnion', Vec2Union in *.
    simpl in *.
    rewrite Vnth_map2.
    apply UnionCollisionFree.
    +
      destruct fop1.
      destruct (out_dec0 (mkFinNat jc)).
      * apply no_coll_range0.
        intros t tc I.
        specialize (D t tc).
        apply D.
        apply Union_introl.
        apply I.
        apply H.
      * apply no_coll_at_sparse0.
        apply H.
    +
      destruct fop2.
      destruct (out_dec0 (mkFinNat jc)).
      * apply no_coll_range0.
        intros t tc I.
        specialize (D t tc).
        apply D.
        apply Union_intror.
        apply I.
        apply H.
      * apply no_coll_at_sparse0.
        apply H.
    +
      intros [A B].

      destruct compat as [C].
      specialize (C (mkFinNat jc)).
      unfold In in C.

      apply Is_Val_In_outset in A ; [auto |auto| apply fop1].
      apply Is_Val_In_outset in B ; [auto |auto| apply fop2].

      contradict C.
      apply Intersection_intro; auto.
  -
    (* no_coll_at_sparse *)
    intros v j jc S.
    unfold HTSUMUnion, HTSUMUnion', Vec2Union in *.
    simpl in *.
    rewrite Vnth_map2.
    apply UnionCollisionFree.
    +
      apply no_coll_at_sparse.
      apply fop1.
      contradict S.
      apply Union_introl.
      apply S.
    +
      apply no_coll_at_sparse.
      apply fop2.
      contradict S.
      apply Union_intror.
      apply S.
    +
      intros [A B].

      destruct compat as [C].
      specialize (C (mkFinNat jc)).
      unfold In in C.

      apply Is_Val_In_outset in A ; [auto |auto| apply fop1].
      apply Is_Val_In_outset in B ; [auto |auto| apply fop2].

      contradict C.
      apply Intersection_intro; auto.
Qed.

End TSigmaHCOL.

End Spiral.

End Spiral_DOT_TSigmaHCOL.

Module Spiral_DOT_HCOLBreakdown.
Module Spiral.
Module HCOLBreakdown.
Import Spiral_DOT_CpdtTactics.
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
Import Spiral_DOT_CpdtTactics.Spiral.
Import Spiral_DOT_VecUtil.Spiral.VecUtil.
Import Spiral_DOT_VecSetoid.Spiral.VecSetoid.
Import Spiral_DOT_Spiral.Spiral.Spiral.
Import Spiral_DOT_CarrierType.Spiral.CarrierType.
Import Spiral_DOT_HCOL.Spiral.HCOL.
Import Spiral_DOT_HCOLImpl.Spiral.HCOLImpl.
Import Spiral_DOT_THCOL.Spiral.THCOL.
Import Spiral_DOT_THCOLImpl.Spiral.THCOLImpl.
Import Coq.Arith.Arith.
Import Coq.Arith.Compare_dec.
Import Coq.Arith.Peano_dec.
Import Coq.Program.Program.
Import Spiral_DOT_SpiralTactics.Spiral.SpiralTactics.
Import Coq.Logic.FunctionalExtensionality.

(* CoRN MathClasses *)
Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders.
Import MathClasses.orders.minmax MathClasses.orders.orders MathClasses.orders.rings.
Import MathClasses.theory.rings.


Import VectorNotations.
Open Scope vector_scope.

Section HCOLBreakdown.

  Lemma Vmap2Indexed_to_VMap2 `{Setoid A} {n} {a b: vector A n}
        (f:A->A->A) `{f_mor: !Proper ((=) ==> (=) ==> (=)) f}
  :
    Vmap2 f a b = Vmap2Indexed (IgnoreIndex2 f) a b.
Admitted.

  Theorem breakdown_ScalarProd: forall (n:nat) (a v: avector n),
      ScalarProd (a,v) =
      ((Reduction (+) 0) ∘ (BinOp (IgnoreIndex2 mult))) (a,v).
Admitted.

  Fact breakdown_OScalarProd: forall {h:nat},
      HScalarProd (h:=h)
      =
      ((HReduction  (+) 0) ∘ (HBinOp (IgnoreIndex2 (A:=CarrierA) mult))).
Admitted.

  Theorem breakdown_EvalPolynomial: forall (n:nat) (a: avector (S n)) (v: CarrierA),
      EvalPolynomial a v = (
        ScalarProd ∘ (pair a) ∘ (MonomialEnumerator n)
      ) v.
Admitted.

  Fact breakdown_OEvalPolynomial: forall (n:nat) (a: avector (S n)),
      HEvalPolynomial a =
      (HScalarProd ∘
                   ((HPrepend  a) ∘
                                  (HMonomialEnumerator n))).
Admitted.

  Theorem breakdown_TInfinityNorm: forall (n:nat) (v:avector n),
      InfinityNorm (n:=n) v = ((Reduction max 0) ∘ (HPointwise (IgnoreIndex abs))) v.
Admitted.

  Fact breakdown_OTInfinityNorm:  forall (n:nat),
      HInfinityNorm =
      (HReduction max 0 (i:=n) ∘ (HPointwise (IgnoreIndex abs))).
Admitted.

  Theorem breakdown_MonomialEnumerator:
    forall (n:nat) (x: CarrierA),
      MonomialEnumerator n x = Induction (S n) (.*.) 1 x.
Admitted.

  Fact breakdown_OMonomialEnumerator:
    forall (n:nat),
      HMonomialEnumerator n =
      HInduction (S n) (.*.) 1.
Admitted.

  Theorem breakdown_ChebyshevDistance:  forall (n:nat) (ab: (avector n)*(avector n)),
      ChebyshevDistance ab = (InfinityNorm ∘ VMinus) ab.
Admitted.

  Fact breakdown_OChebyshevDistance:  forall (n:nat),
      HChebyshevDistance n = (HInfinityNorm ∘ HVMinus).
Admitted.

  Theorem breakdown_VMinus:  forall (n:nat) (ab: (avector n)*(avector n)),
      VMinus ab =  BinOp (IgnoreIndex2 sub) ab.
Admitted.

  Fact breakdown_OVMinus:  forall (n:nat),
      HVMinus = HBinOp (o:=n) (IgnoreIndex2 sub).
Admitted.

  Fact breakdown_OTLess_Base: forall
      {i1 i2 o}
      `{o1pf: !HOperator (o1: avector i1 -> avector o)}
      `{o2pf: !HOperator (o2: avector i2 -> avector o)},
      HTLess o1 o2 = (HBinOp (IgnoreIndex2 Zless) ∘ HCross o1 o2).
Admitted.

End HCOLBreakdown.




End HCOLBreakdown.

End Spiral.

End Spiral_DOT_HCOLBreakdown.

Module Spiral_DOT_MonoidalRestriction.
Module Spiral.
Module MonoidalRestriction.
Import Spiral_DOT_CpdtTactics.
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
Import Spiral_DOT_HCOLBreakdown.
Import Spiral_DOT_HCOLBreakdown.Spiral.
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
Import Spiral_DOT_CpdtTactics.Spiral.
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
Import Spiral_DOT_CpdtTactics.
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
Import Spiral_DOT_HCOLBreakdown.
Import Spiral_DOT_MonoidalRestriction.
Import Spiral_DOT_MonoidalRestriction.Spiral.
Import Spiral_DOT_HCOLBreakdown.Spiral.
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
Import Spiral_DOT_CpdtTactics.Spiral.
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
Import Spiral_DOT_CpdtTactics.
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
Import Spiral_DOT_HCOLBreakdown.
Import Spiral_DOT_MonoidalRestriction.
Import Spiral_DOT_VecPermutation.
Import Spiral_DOT_VecPermutation.Spiral.
Import Spiral_DOT_MonoidalRestriction.Spiral.
Import Spiral_DOT_HCOLBreakdown.Spiral.
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
Import Spiral_DOT_CpdtTactics.Spiral.

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

    Lemma SHBinOp_equiv_lifted_HBinOp
          {o}
          (f: nat -> CarrierA -> CarrierA -> CarrierA)
          `{pF: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
    :
      SafeCast (@SHBinOp o f pF) = @liftM_HOperator Monoid_RthetaFlags (o+o) o (@HBinOp o f pF) _ .
Admitted.


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

    Lemma U_SAG2:
      ∀ (n : nat) (x : rvector (n + n))
        (f: nat -> CarrierA -> CarrierA -> CarrierA)
        `{f_mor: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
        (k : nat) (kp : k < n),

        Vnth
          (SumUnion Monoid_RthetaFlags
                    (Vbuild
                       (λ (j : nat) (jc : j < n),
                        Scatter' Monoid_RthetaFlags (i:=1)
                                 (h_index_map j 1 (range_bound:=ScatH_1_to_n_range_bound _ _ j n 1 jc))
                                 (f_inj :=
                                    @index_map_family_member_injective 1 n n (IndexMapFamily 1 n n
                                                                                             (fun (j0 : nat) (jc0 : j0<n) =>
                                                                                                @h_index_map 1 n j0 1
                                                                                                             (ScatH_1_to_n_range_bound _ _ j0 n 1 jc0))) (@h_j_1_family_injective n) j jc) zero
                                 (SafeCast' (SHBinOp' Monoid_RthetaSafeFlags (SwapIndex2 j f))
                                            (Gather' Monoid_RthetaFlags (@h_index_map (1+1) (n+n) j n (GathH_jn_domain_bound _ _ j n jc)) x))))) kp
        = Vnth ((SHBinOp' _ (o:=n) f) x) kp.
Admitted.


    (*
    BinOp := (self, o, opts) >> When(o.N=1, o, let(i := Ind(o.N),
        ISumUnion(i, i.range, OLCompose(
        ScatHUnion(o.N, 1, i, 1),
        BinOp(1, o.op),
        GathH(2*o.N, 2, i, o.N)
        )))),
     *)
    Theorem expand_BinOp
            (n:nat)
            (f: nat -> CarrierA -> CarrierA -> CarrierA)
            `{f_mor: !Proper ((=) ==> (=) ==> (=) ==> (=)) f}
      :
        SafeCast (SHBinOp f)
        =
        USparseEmbedding (f_inj:=h_j_1_family_injective)
                         (mkSHOperatorFamily Monoid_RthetaFlags _ _ _
                                             (fun j _ => SafeCast (SHBinOp (SwapIndex2 j f))))
                         (IndexMapFamily 1 n n (fun j jc => h_index_map j 1 (range_bound := (ScatH_1_to_n_range_bound _ _ j n 1 jc))))
                         zero
                         (IndexMapFamily _ _ n (fun j jc => h_index_map j n (range_bound:=GathH_jn_domain_bound _ _ j n jc))).
Admitted.

    (*
   ApplyFunc(SUMUnion, List([1..Length(ch)], i->OLCompose(
            ScatHUnion(Rows(o), Rows(ch[i]), Sum(List(ch{[1..i-1]}, c->c.dims()[1])), 1),
            self(ch[i], opts),
            GathH(Cols(o), Cols(ch[i]), Sum(List(ch{[1..i-1]}, c->c.dims()[2])), 1))))),
     *)
    (* TODO: perhaps could be generalized for generic operation, not just plus *)
    Theorem expand_HTDirectSum
            {fm: Monoid RthetaFlags}
            {fml: @MonoidLaws RthetaFlags RthetaFlags_type fm}
            {i1 o1 i2 o2}
            (f: avector i1 -> avector o1)
            (g: avector i2 -> avector o2)
            `{hop1: !HOperator f}
            `{hop2: !HOperator g}
      :
        liftM_HOperator fm (HTDirectSum f g)
        =
        HTSUMUnion
          _
          plus
          (SHCompose fm
                     (ScatH fm 0 1 (snzord0:=(ScatH_stride1_constr _ _)) (range_bound := h_bound_first_half _ _ o1 o2) zero)
                     (SHCompose fm
                                (liftM_HOperator fm f)
                                (GathH fm 0 1 (domain_bound := h_bound_first_half _ _ i1 i2))))

          (SHCompose fm
                     (ScatH fm o1 1 (snzord0:=(ScatH_stride1_constr _ _ )) (range_bound := h_bound_second_half _ _ o1 o2) zero)
                     (SHCompose fm
                                (liftM_HOperator fm g)
                                (GathH fm i1 1 (domain_bound := h_bound_second_half _ _ i1 i2)))).
Admitted.

  End Value_Correctness.

  Section Structural_Correctness.

    (* TODO *)

  End Structural_Correctness.


End SigmaHCOLExpansionRules.

Section SigmaHCOLRewritingRules.
  Section Value_Correctness.

    Local Notation "g ⊚ f" := (@SHCompose Monoid_RthetaFlags _ _ _ g f) (at level 40, left associativity) : type_scope.

    Lemma rewrite_PointWise_ISumUnion
          {i o n}
          (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n)
          (pf: { j | j<o} -> CarrierA -> CarrierA)
          `{pf_mor: !Proper ((=) ==> (=) ==> (=)) pf}
          (pfzn: forall j (jc:j<o), pf (j ↾ jc) zero = zero) (* function with the fixed point 0 *)
          (Uz: Apply_Family_Single_NonUnit_Per_Row _ op_family zero)
      :
        (@SHPointwise _ o pf pf_mor) ⊚ (@ISumUnion i o n op_family)
        =
        (@ISumUnion i o n
                    (SHOperatorFamilyCompose _
                                             (@SHPointwise _ o pf pf_mor)
                                             op_family)
        ).
Admitted.

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
      Proof.
        split.
        -
          apply VecRMonoidMap2.
        -
          intros a b Hx Hy.
          unfold sg_op.
          induction n.
          +
            dep_destruct a.
            dep_destruct b.
            reflexivity.
          +
            simpl.
            rewrite Vcons_to_Vcons_reord.
            destruct f_mon.

            assert(@sg_P A P (Vhead a))
              by apply Vforall_Vhead, Hx.
            assert(@sg_P A P (Vhead b))
              by apply Vforall_Vhead, Hy.

            assert(@sg_P (vector A n0) (@Vforall A P n0) (Vtail a))
              by apply Vforall_Vtail, Hx.
            assert(@sg_P (vector A n0) (@Vforall A P n0) (Vtail b))
              by apply Vforall_Vtail, Hy.


            rewrite rcommutativity0; try assumption.
            rewrite <- IHn0; try assumption.
            rewrite Vcons_to_Vcons_reord.
            reflexivity.
      Qed.

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

    (* In SPIRAL it is called [Reduction_ISumReduction] *)
    Lemma rewrite_Reduction_IReduction
          {i o n}
          (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n)

          (* Common unit for both monoids *)
          `{uf_zero: MonUnit CarrierA}

          (* 1st Monoid. Used in reduction *)
          `{f: SgOp CarrierA}

          (* Monoid on restriction on f *)
          `{P: SgPred CarrierA}
          `{f_mon: @CommutativeRMonoid _ _ f uf_zero P}

          (* 2nd Monoid. Used in IUnion *)
          `{u: SgOp CarrierA}
          `{u_mon: @MathClasses.interfaces.abstract_algebra.CommutativeMonoid _ _ u uf_zero}

          (Uz: Apply_Family_Single_NonUnit_Per_Row _ op_family uf_zero)
          (Upoz: Apply_Family_Vforall_P _ (liftRthetaP P) op_family)
      :

        (liftM_HOperator Monoid_RthetaFlags (@HReduction _ f _ uf_zero))
          ⊚ (@IUnion i o n u _ uf_zero op_family)
        =
        SafeCast (IReduction f uf_zero
                             (UnSafeFamilyCast
                                (SHOperatorFamilyCompose _ (liftM_HOperator Monoid_RthetaFlags (@HReduction _ f _ uf_zero)) op_family))).
Admitted.

    Global Instance max_Assoc:
      @Associative CarrierA CarrierAe (@max CarrierA CarrierAle CarrierAledec).
    Proof.
      unfold Associative, HeteroAssociative.
      intros x y z.
      unfold max, sort.
      repeat break_if; unfold snd in *; crush.
      clear Heqd Heqd0 Heqd1 Heqd2.
      clear_dups.
      apply le_flip in n.
      apply le_flip in n0.
      apply eq_iff_le.
      auto.
    Qed.

    Global Instance max_Comm:
      @Commutative CarrierA CarrierAe CarrierA (@max CarrierA CarrierAle CarrierAledec).
    Proof.
      unfold Commutative.
      intros x y.
      unfold max, sort.
      repeat break_if; unfold snd; auto.
      -
        apply eq_iff_le; auto.
      -
        clear Heqd Heqd0.
        apply le_flip in n.
        apply le_flip in n0.
        apply eq_iff_le.
        auto.
    Qed.

    Section NN.
      (* Non-negative CarrierA subtype *)

      Global Instance NN:
        SgPred CarrierA := CarrierAle CarrierAz.

      Global Instance RMonoid_max_NN:
        @RMonoid CarrierA CarrierAe (@max CarrierA CarrierAle CarrierAledec) CarrierAz NN.
      Proof.
        repeat split; try typeclasses eauto.
        -
          (* zero in P *)
          unfold sg_P, mon_unit, NN.
          reflexivity.
        -
          (* closed *)
          intros a b M0 M1.
          unfold sg_op, max, equiv, mon_unit, sort.
          break_if; crush.
        -
          (* assoc *)
          intros x y z H H0 H1.
          unfold sg_op, max, sort.
          repeat break_if; unfold snd in *; crush.
          clear Heqd Heqd0 Heqd1 Heqd2.
          clear_dups.
          apply le_flip in n0.
          apply le_flip in n.
          apply eq_iff_le.
          auto.
        -
          (* left_unit *)
          intros y H.
          unfold sg_op, max, equiv, mon_unit, sort.
          break_if; crush.
        -
          (* right_unit *)
          intros x H.
          unfold sg_op, max, equiv, mon_unit, sort.
          break_if; crush.
          unfold le in l.
          apply eq_iff_le.
          auto.
      Qed.

      Global Instance CommutativeRMonoid_max_NN:
        @CommutativeRMonoid CarrierA CarrierAe (@minmax.max CarrierA CarrierAle CarrierAledec) CarrierAz NN.
      Proof.
        split.
        -
          apply RMonoid_max_NN.
        -
          (* commutativity *)
          intros x y H H0.
          apply max_Comm.
      Qed.

    End NN.

    (* Specialized version of rewrite_Reduction_IReduction *)
    Lemma rewrite_Reduction_IReduction_max_plus
          {i o n}
          (op_family: @SHOperatorFamily Monoid_RthetaFlags i o n)
          (Uz: Apply_Family_Single_NonUnit_Per_Row _ op_family zero)
          (Upoz: Apply_Family_Vforall_P _ Is_NonNegative op_family)
      :
        (liftM_HOperator Monoid_RthetaFlags (@HReduction _ max _ zero))
          ⊚ (ISumUnion op_family)
        =
        SafeCast (IReduction max zero
                             (UnSafeFamilyCast
                                (SHOperatorFamilyCompose _ (liftM_HOperator Monoid_RthetaFlags (@HReduction _ max _ zero)) op_family))).
Admitted.

    (* Variant of SPIRAL's `rewrite_ISumXXX_YYY` rule for [IReduction] and [GatH] *)
    Lemma rewrite_ISumXXX_YYY_IReduction_GathH
          {i0 i o n b s : nat}
          {db}
          (dot: CarrierA -> CarrierA -> CarrierA)
          `{pdot: !Proper ((=) ==> (=) ==> (=)) dot}
          (initial: CarrierA)
          (op_family: @SHOperatorFamily Monoid_RthetaSafeFlags i o n)
      :
        SHCompose Monoid_RthetaFlags
                  (SafeCast (IReduction dot initial op_family))
                  (@GathH Monoid_RthetaFlags i0 i b s db)
        =
        SafeCast
          (IReduction dot initial
                      (SHFamilyOperatorCompose Monoid_RthetaSafeFlags
                                               op_family
                                               (GathH Monoid_RthetaSafeFlags b s (domain_bound:=db))
          )).
Admitted.

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

    Lemma rewrite_PointWise_ScatHUnion
          {fm: Monoid RthetaFlags}

          (* -- SE params -- *)
          {n i o ki ko}
          (* Kernel *)
          (kernel: @SHOperatorFamily fm ki ko n)
          (* Scatter index map *)
          (f: index_map_family ko o n)
          {f_inj : index_map_family_injective f}
          (* Gather index map *)
          (g: index_map_family ki i n)

          (* -- Scatter params -- *)
          (pf: CarrierA -> CarrierA)
          `{pf_mor: !Proper ((=) ==> (=)) pf}
          (pfzn: pf zero = zero) (* function with the fixed point 0 *)
      :
        SHOperatorFamilyCompose fm
                                (SHPointwise fm (IgnoreIndex pf))
                                (SparseEmbedding fm kernel f zero g (f_inj:=f_inj))
        =
        SparseEmbedding fm
                        (SHOperatorFamilyCompose fm
                                                 (SHPointwise fm (IgnoreIndex pf))
                                                 kernel)
                        f zero g (f_inj:=f_inj).
Admitted.

    Lemma rewrite_Reduction_ScatHUnion
          {n m:nat}
          {fm: Monoid RthetaFlags}

          `{g: SgOp CarrierA}
          `{mzero: MonUnit CarrierA}
          `{P: SgPred CarrierA}
          `(g_mon: @CommutativeRMonoid _ _ g mzero P)

          (F: @SHOperator fm m 1)
          (f:index_map 1 (S n))
          (f_inj: index_map_injective f)
          (FP: op_Vforall_P fm (liftRthetaP P) F)
      :
        SHCompose fm
                  (SHCompose fm
                             (liftM_HOperator fm (HReduction g mzero))
                             (Scatter fm f mzero (f_inj:=f_inj)))
                  F
        =
        F.
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
Import Spiral_DOT_CpdtTactics.
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
Import Spiral_DOT_HCOLBreakdown.
Import Spiral_DOT_MonoidalRestriction.
Import Spiral_DOT_VecPermutation.
Import Spiral_DOT_SigmaHCOLRewriting.
Import Spiral_DOT_SigmaHCOLRewriting.Spiral.
Import Spiral_DOT_VecPermutation.Spiral.
Import Spiral_DOT_MonoidalRestriction.Spiral.
Import Spiral_DOT_HCOLBreakdown.Spiral.
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
Import Spiral_DOT_CpdtTactics.Spiral.
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
Import Spiral_DOT_HCOLBreakdown.Spiral.HCOLBreakdown.
Import Spiral_DOT_SigmaHCOLRewriting.Spiral.SigmaHCOLRewriting.
Import MathClasses.interfaces.canonical_names.


Section HCOL_breakdown.

  (* Original dynamic window expression *)
  Definition dynwin_orig (a: avector 3) :=
    (HTLess
       (HEvalPolynomial a)
       (HChebyshevDistance 2)).

  (* dynamic window HCOL expression *)
  Definition dynwin_HCOL (a: avector 3) :=
    (HBinOp (IgnoreIndex2 Zless) ∘
            HCross
            ((HReduction plus 0 ∘ HBinOp (IgnoreIndex2 mult)) ∘ (HPrepend a ∘ HInduction _ mult 1))
            (HReduction minmax.max 0 ∘ (HPointwise (IgnoreIndex abs)) ∘ HBinOp (o:=2) (IgnoreIndex2 sub))).


  (* Initial HCOL breakdown proof *)
  Theorem DynWinHCOL:  forall (a: avector 3),
      dynwin_orig a = dynwin_HCOL a.
Admitted.

End HCOL_breakdown.


Section SigmaHCOL_rewriting.

  Local Notation "g ⊚ f" := (@SHCompose Monoid_RthetaFlags _ _ _ g f) (at level 40, left associativity) : type_scope.

  (* --- HCOL -> Sigma->HCOL --- *)

  (*
Final Sigma-HCOL expression:

BinOp(1, Lambda([ r14, r15 ], geq(r15, r14))) o
SUMUnion(
  ScatHUnion(2, 1, 0, 1) o
  Reduction(3, (a, b) -> add(a, b), V(0.0), (arg) -> false) o
  PointWise(3, Lambda([ r16, i14 ], mul(r16, nth(D, i14)))) o
  Induction(3, Lambda([ r9, r10 ], mul(r9, r10)), V(1.0)) o
  GathH(5, 1, 0, 1),

  ScatHUnion(2, 1, 1, 1) o
  Reduction(2, (a, b) -> max(a, b), V(0.0), (arg) -> false) o
  PointWise(2, Lambda([ r11, i13 ], abs(r11))) o
  ISumUnion(i15, 2,
    ScatHUnion(2, 1, i15, 1) o
    BinOp(1, Lambda([ r12, r13 ], sub(r12, r13))) o
    GathH(4, 2, i15, 2)
  ) o
  GathH(5, 4, 1, 1)
)
   *)
  Definition dynwin_SHCOL (a: avector 3) :=
    (SafeCast (SHBinOp (IgnoreIndex2 THCOLImpl.Zless)))
      ⊚
      (HTSUMUnion _ plus (
                    ScatH _ 0 1
                          (range_bound := h_bound_first_half _ _ 1 1)
                          (snzord0 := @ScatH_stride1_constr _ _ 1 2)
                          zero
                          ⊚
                          (liftM_HOperator _ (@HReduction _ plus CarrierAPlus_proper 0)  ⊚
                                           SafeCast (SHBinOp (IgnoreIndex2 mult))
                                           ⊚
                                           liftM_HOperator _ (HPrepend a )
                                           ⊚
                                           liftM_HOperator _ (HInduction 3 mult one))
                          ⊚
                          (GathH _ 0 1
                                 (domain_bound := h_bound_first_half _ _ 1 (2+2)))
                  )

                  (
                    (ScatH _ 1 1
                           (range_bound := h_bound_second_half _ _ 1 1)
                           (snzord0 := @ScatH_stride1_constr _ _ 1 2)
                           zero)
                      ⊚
                      (liftM_HOperator _ (@HReduction _ minmax.max _ 0))
                      ⊚
                      (SHPointwise _ (IgnoreIndex abs))
                      ⊚
                      (USparseEmbedding
                         (n:=2)
                         (mkSHOperatorFamily Monoid_RthetaFlags _ _ _
                                             (fun j _ => SafeCast (SHBinOp (o:=1)
                                                                        (SwapIndex2 j (IgnoreIndex2 HCOLImpl.sub)))))
                         (IndexMapFamily 1 2 2 (fun j jc => h_index_map j 1 (range_bound := (ScatH_1_to_n_range_bound _ _ j 2 1 jc))))
                         (f_inj := h_j_1_family_injective)
                         zero
                         (IndexMapFamily _ _ 2 (fun j jc => h_index_map j 2 (range_bound:=GathH_jn_domain_bound _ _ j 2 jc))))
                      ⊚
                      (GathH _ 1 1
                             (domain_bound := h_bound_second_half _ _ 1 (2+2)))
                  )
      ).


  (* HCOL -> SigmaHCOL Value correctness. *)
  Theorem DynWinSigmaHCOL_Value_Correctness
          (a: avector 3)
    :
      liftM_HOperator Monoid_RthetaFlags (dynwin_HCOL a)
      =
      dynwin_SHCOL a.
Admitted.
Import Spiral_DOT_FinNatSet.Spiral.FinNatSet.


  Theorem DynWinSigmaHCOL_dense_input
          (a: avector 3)
    : Same_set _ (in_index_set _ (dynwin_SHCOL a)) (Full_set (FinNat _)).
Admitted.

  Theorem DynWinSigmaHCOL_dense_output
          (a: avector 3)
    : Same_set _ (out_index_set _ (dynwin_SHCOL a)) (Full_set (FinNat _)).
Admitted.

  Fact two_index_maps_span_I_2
       (x : FinNat 2)
       (b2 : forall (x : nat) (_ : x < 1), 0 + (x * 1) < 2)
       (b1 : forall (x : nat) (_ : x < 1), 1 + (x * 1) < 2)
    :
      Union (@sig nat (fun x0 : nat => x0 < 2))
            (@index_map_range_set 1 2 (@h_index_map 1 2 1 1 b1))
            (@index_map_range_set 1 2 (@h_index_map 1 2 O 1 b2)) x.
Admitted.

  Fact two_h_index_maps_disjoint
       (m n: nat)
       (mnen : m ≢ n)
       (b2 : forall (x : nat) (_ : x < 1), n + (x*1) < 2)
       (b1 : forall (x : nat) (_ : x < 1), m + (x*1) < 2)
    :
      Disjoint (FinNat 2)
               (@index_map_range_set 1 2 (@h_index_map 1 2 m 1 b1))
               (@index_map_range_set 1 2 (@h_index_map 1 2 n 1 b2)).
Admitted.

  Ltac solve_facs :=
    repeat match goal with
           | [ |- SHOperator_Facts _ _ ] => apply SHBinOp_RthetaSafe_Facts
           | [ |- @SHOperator_Facts ?m ?i ?o (@SHBinOp ?o _ _) ] =>
             replace (@SHOperator_Facts m i) with (@SHOperator_Facts m (o+o)) by apply eq_refl
           | [ |- SHOperator_Facts _ _ ] => apply SHCompose_Facts
           | [ |- SHOperator_Facts _ _ ] => apply SafeCast_Facts
           | [ |- SHOperator_Facts _ _ ] => apply HTSUMUnion_Facts
           | [ |- SHOperator_Facts _ _ ] => apply SHCompose_Facts
           | [ |- SHOperator_Facts _ _ ] => apply Scatter_Rtheta_Facts
           | [ |- SHOperator_Facts _ _ ] => apply liftM_HOperator_Facts
           | [ |- SHOperator_Facts _ _ ] => apply Gather_Facts
           | [ |- SHOperator_Facts _ _ ] => apply SHPointwise_Facts
           | [ |- SHOperator_Facts _ _ ] => apply IUnion_Facts
           | [ |- SHOperator_Facts _ (USparseEmbedding _ _) ] => unfold USparseEmbedding

           | [ |- Monoid.MonoidLaws Monoid_RthetaFlags] => apply MonoidLaws_RthetaFlags
           | _ => crush
           end.

  Instance DynWinSigmaHCOL_Facts
           (a: avector 3):
    SHOperator_Facts _ (dynwin_SHCOL a).
  Proof.
    unfold dynwin_SHCOL.

    (* First resolve all SHOperator_Facts typeclass instances *)
    solve_facs.

    (* Now let's take care of remaining proof obligations *)

    -
      apply two_h_index_maps_disjoint.
      assumption.

    -
      unfold Included, In.
      intros x H.

      replace (Union _ _ (Empty_set _)) with (@index_map_range_set 1 2 (@h_index_map 1 2 0 1 (ScatH_1_to_n_range_bound _ _ 0 2 1 (@le_S 1 1 (le_n 1))))).
      +
        apply two_index_maps_span_I_2.
      +
        apply Extensionality_Ensembles.
        apply Union_Empty_set_lunit.
        apply h_index_map_range_set_dec.

    -
      unfold Included.
      intros x H.
      apply Full_intro.

    -
      apply two_h_index_maps_disjoint.
      unfold peano_naturals.nat_lt, peano_naturals.nat_plus,
      peano_naturals.nat_1, one, plus, lt.
      crush.

    -
      unfold Included, In.
      intros x H.
      apply Union_comm.
      apply two_index_maps_span_I_2.

  Qed.

  (* --- SigmaHCOL -> Sigma->HCOL --- *)

  Parameter dynwin_SHCOL1: (avector 3) -> @SHOperator Monoid_RthetaFlags (1+(2+2)) 1.

  (* Special case when results of 'g' comply to P. In tihs case we can discard 'g' *)
  Lemma Apply_Family_Vforall_P_move_P
        {fm} {P:Rtheta' fm → Prop}
        {i1 o2 o3 n}
        (f: @SHOperator fm  o2 o3)
        (g: @SHOperatorFamily fm i1 o2 n)
    :
      (forall x, Vforall P ((op fm f) x)) ->
      Apply_Family_Vforall_P fm P (SHOperatorFamilyCompose fm f g).
Admitted.

  (* TODO: move to SigmaHCOLRewriting *)
  Lemma ApplyFamily_SHOperatorFamilyCompose
        {i1 o2 o3 n}
        {fm}
        (f: @SHOperator fm o2 o3)
        (g: @SHOperatorFamily fm i1 o2 n)
        {x}
    : Apply_Family fm (SHOperatorFamilyCompose fm f g) x ≡
      Vmap (op fm f) (Apply_Family fm g x).
Admitted.

  Lemma SHPointwise_preserves_Apply_Family_Single_NonUnit_Per_Row
        {i1 o2 n}
        (fam : @SHOperatorFamily Monoid_RthetaFlags i1 o2 n)
        (H: Apply_Family_Single_NonUnit_Per_Row Monoid_RthetaFlags fam 0)
        (f: FinNat o2 -> CarrierA -> CarrierA)
        {f_mor: Proper (equiv ==> equiv ==> equiv) f}
        (A: forall (i : nat) (ic : i<o2) (v : CarrierA), 0 ≠ f (mkFinNat ic) v -> 0 ≠ v):
    Apply_Family_Single_NonUnit_Per_Row Monoid_RthetaFlags
                                        (SHOperatorFamilyCompose
                                           Monoid_RthetaFlags
                                           (SHPointwise Monoid_RthetaFlags f (n:=o2))
                                           fam)
                                            zero.
Admitted.

  Lemma op_Vforall_P_SHPointwise
        {m n: nat}
        {fm: Monoid.Monoid RthetaFlags}
        {f: CarrierA -> CarrierA}
        `{f_mor: !Proper ((=) ==> (=)) f}
        {P: CarrierA -> Prop}
        (F: @SHOperator fm m n)
    :
      (forall x, P (f x)) ->
           op_Vforall_P fm (liftRthetaP P)
                        (SHCompose fm
                                   (SHPointwise (n:=n) fm (IgnoreIndex f))
                                   F).
Admitted.

  Theorem DynWinSigmaHCOL1_Value_Correctness (a: avector 3)
    : dynwin_SHCOL a = dynwin_SHCOL1 a. Proof.
    unfold dynwin_SHCOL.
    unfold USparseEmbedding.

    (* normalize to left-associativity of compose *)
    repeat rewrite <- SHCompose_assoc; try apply MonoidLaws_RthetaFlags.
    rewrite SHCompose_mid_assoc with (g:=SHPointwise _ _); try apply MonoidLaws_RthetaFlags.

    (* ### RULE: Reduction_ISumReduction *)
    rewrite rewrite_PointWise_ISumUnion.
    all:revgoals.
    (* solve 2 sub-dependent goals *)
    { apply SparseEmbedding_Apply_Family_Single_NonZero_Per_Row. }
    { intros j jc; apply abs_0_s. }

    (* Re-associate compositions before applying next rule *)
    rewrite SHCompose_mid_assoc with (f:=ISumUnion _); try apply MonoidLaws_RthetaFlags.

    (* ### RULE: Reduction_ISumReduction *)
    rewrite rewrite_Reduction_IReduction_max_plus.
    all:revgoals.
    {
      remember (SparseEmbedding  _ _ _ _) as t.
      generalize dependent t.
      intros fam _.

      apply Apply_Family_Vforall_P_move_P.
      intros x.

      apply Vforall_nth_intro.
      intros t tc.
      rewrite SHPointwise_nth_eq.
      unfold Is_NonNegative, liftRthetaP.
      rewrite evalWriter_Rtheta_liftM.
      unfold IgnoreIndex, const.
      apply abs_always_nonneg.
      apply MonoidLaws_RthetaFlags.
    }

    {
      remember (SparseEmbedding _ _ _ _ _) as fam.

      assert(Apply_Family_Single_NonUnit_Per_Row Monoid_RthetaFlags fam 0).
      {
        subst fam.
        apply SparseEmbedding_Apply_Family_Single_NonZero_Per_Row.
      }
      generalize dependent fam.
      intros fam _ H. clear a.

      apply SHPointwise_preserves_Apply_Family_Single_NonUnit_Per_Row.
      +
        apply H.
      +
        intros i ic v V.
        unfold IgnoreIndex, const in V.
        apply ne_sym in V.
        apply ne_sym.
        apply abs_nz_nz, V.
    }

    repeat rewrite SHCompose_assoc; try apply MonoidLaws_RthetaFlags.
    rewrite rewrite_ISumXXX_YYY_IReduction_GathH.
    repeat rewrite <- SHCompose_assoc; try apply MonoidLaws_RthetaFlags.

    rewrite rewrite_PointWise_ScatHUnion by apply abs_0_s.

    unfold SparseEmbedding, SHOperatorFamilyCompose, UnSafeFamilyCast; simpl.
    setoid_rewrite SHCompose_assoc at 5; try apply MonoidLaws_RthetaFlags.
    setoid_rewrite <- SHCompose_assoc at 1; try apply MonoidLaws_RthetaFlags.

    (* --- BEGIN: hack ---
    I would expect the following to work here:

    setoid_rewrite rewrite_Reduction_ScatHUnion_max_zero with
        (fm := Monoid_RthetaFlags)
        (m := S (S (S (S O)))) (n := S (S O)).

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

    setoid_rewrite SHCompose_assoc.
    eapply op_Vforall_P_SHPointwise, abs_always_nonneg.



  Admitted.

End SigmaHCOL_rewriting.


End DynWin.

End Spiral.

End Spiral_DOT_DynWin.

