Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.
Require Import Coq.Init.Specif Coq.Program.Subset.
Require Import Coq.ZArith.ZArith.
Local Open Scope program_scope.
Local Open Scope Z_scope.

(* Integer functoins used in this example:
       Z.sqrt - square root. For negative values returns 0.
       Z.abs - absolute value.
       Z.sgn - sign (returns -1|0|1).
 *)

(* Unrelated simple lemma showing use of function composition, and
pointfree style,proven using function extensionality. SPIRAL ideally
should be written like that. *)
Lemma abs_sgn_comm: (Z.abs ∘ Z.sgn) = (Z.sgn ∘ Z.abs).
Proof.
  apply functional_extensionality.
  intros.
  unfold compose.
  destruct x; auto.
Qed.

(* -- Some helpful facts about function used int this example -- *)
Section Arith_facts.

  Fact zsqrt_always_nneg: forall x, (Z.sqrt x) >= 0.
  Proof.
    intros.
    apply Z.ge_le_iff.
    apply Z.sqrt_nonneg.
  Qed.

  Fact zsqrt_0: Z.sqrt 0 = 0.
  Proof.
    reflexivity.
  Qed.

  Fact zabs_always_nneg: forall x, (Z.abs x) >= 0.
  Proof.
    intros.
    unfold Z.abs.
    destruct x.
    - omega.
    - induction p;auto;omega.
    - induction p;auto;omega.
  Qed.

  Fact zabs_nneg: forall x, x>=0 -> Z.abs x = x.
  Proof.
    intros.
    destruct x.
    - auto.
    - auto.
    - assert(Z.neg p < 0) by apply Pos2Z.neg_is_neg.
      omega.
  Qed.

  (* Helper lemma: same as subset_eq bug for sig2 *)
  Lemma subset2_eq : forall A (P Q: A -> Prop) (n m : sig2 P Q),
      n = m <-> proj1_sig (sig_of_sig2 n) = proj1_sig (sig_of_sig2 m).
  Proof.
    destruct n as (x,p).
    destruct m as (x',p').
    simpl.
    split ; intros ; subst.
    inversion H.
    reflexivity.
    pi.
  Qed.

End Arith_facts.


(* -- GIGO (Garbage-in-Garbage-out) approach. No preconditions on sqrt. --
PROS:
  * can use composition notation
  * can define experessions before reasoning about them.
CONS:
  * not pointfree
  * allows to construct incorrect expresions. E.g. 'bar' below.
  * does not allow to express pre and post-conditions
  *)
Module GIGO.

  (* example of incorrect expression *)
  Definition bar := Z.sqrt (-1234).

  (* We can use composition, but not pointfree because of constraint x>=0 *)
  Lemma foo (x:Z) (xp:x>=0):
    (Z.sqrt ∘ Z.abs) x = Z.sqrt x.
  Proof.
    unfold compose.
    rewrite zabs_nneg.
    - reflexivity.
    - apply xp.
  Qed.

End GIGO.


(* -- Naive approach. Simple precondition on sqrt. --
PROS:
  * does not allow to construct incorrect expresions.
  * all preconditions are clearly spelled and have to be proven manually before constructing the expression. No automatic proof search.
CONS:
  * can not easily compose experessions before reasoning about them.
  * can not use composition notation
  * not pointfree
  * does not allow to express post-conditions
  *)
Module Naive.

  (* Version of sqrt with pre-condition *)
  Definition zsqrt (x:Z) {ac:x>=0} := Z.sqrt x.

  (* Fails: Cannot infer the implicit parameter ac of zsqrt whose type is  "-1234 >= 0". Since it is unporovable, this experession could not be constructed.
   *)
  Fail Definition bar := zsqrt (-1234).

  (* This is lemma about composition of 'zsqrt' and 'Z.abs'. Unfortunately we could not write this in pointfree style using functoin composition *)
  Lemma foo (x:Z) (xp:x>=0):
    @zsqrt (Z.abs x) (zabs_always_nneg x) = @zsqrt x xp.
  Proof.
    unfold zsqrt.
    rewrite zabs_nneg.
    - reflexivity.
    - apply xp.
  Qed.

End Naive.

(* -- Spec approach. Using specifications to refine types of arguments of sqrt as well as return value of abs --
PROS:
  * allows to use composition
  * pointfree
  * values along with their properties are nicely bundled using `sig` or {|}.
  * does not allow to construct incorrect expresions.
  * all preconditions are clearly spelled out. Constructing correct expression is just a matter of correctly matching parameter and return types of expressions.
CONS:
  * requires a bit of type glue here and there (e.g. use of `zsqrt_zabs_glue` in foo_s'.
  * Propositions in spec must match exactly. If not, as seen in foo' a glue is required.
  * there is no logical inference performed on specs. Not even simple structural rules application https://en.wikipedia.org/wiki/Structural_rule. For example {a|(P1 a)/\(P2 a)} could not be used in place of {a|(P2 a)/\(P1 a)} or {a|P1 a}
  *)
Module Specs.

  (* "Refined" using specifications versions of sqrt and abs *)

  (* Sqrt has both post and pre-conditions. To show how multiple
  post-conditions could be specified we specify 2nd post-condition
  even though it could be proven to be the same as the first. *)

  (* When defining our version of `zsqrt` we need to provide the
  proofs that the result indeeds satisfies the post-conditions.

  For demonstration purposes we will use Coq `Program` mechanism which
  will generates sub-goals for each post conndition (an obligation)
  which we will proceed to solve manually. Alternatively both
  obligations' proofs could be specified explicitly, instead of _ *)

  Local Obligation Tactic := idtac.
  Program Definition zsqrt (a:{x:Z|x>=0}): {y:Z|y>=0 & ~(y<0)}
    := exist2 _ _ (Z.sqrt (proj1_sig a))  _  _.
  Next Obligation.
    intros a.
    simpl; apply zsqrt_always_nneg.
  Defined.
  Next Obligation.
    simpl; intros a H.
    assert (Z.sqrt (proj1_sig a)>=0) by
        apply zsqrt_always_nneg.
    congruence.
  Defined.

  (* Abs does not have any pre-condition but has a single
  post-condition. In this case we provide the proof explicitly without
  generating and prooving a subgoal. *)
  Definition zabs: Z -> {x:Z|x>=0} :=
    fun a => exist _ (Z.abs a) (zabs_always_nneg a).

  (* Fails: Cannot infer this placeholder of type "(fun x : Z => x >= 0) (-1234)". *)
  Fail Definition bar := zsqrt (exist _ (-1234) _).

  (* The implicit agrument (which we will make explicit by applying
  'functional_extensionality' has type {x:Z|x>=0}. To use it in zabs
  we have to project a witness from it. We are doing this by composing
  with (@proj1_sig Z _). It is a bit bulky and I wish I did not have
  to specify arguments Z and _ but Coq could not infer them
  automatically.

  Another way to do this would be via automatic coercion mechanism,
  by defining something like this:

  Definition witness {P : Z -> Prop} (x : sig P) := proj1_sig x.
  Coercion witness : sig >-> Z.

  Unfortunately, this does not currently work due to the bug in Coq:

  https://coq.inria.fr/bugs/show_bug.cgi?id=4114
   *)
  Lemma foo:
    zsqrt ∘ zabs ∘ (@proj1_sig Z _) = zsqrt.
  Proof.
    apply functional_extensionality.
    intros b.
    unfold compose, zsqrt, zabs.
    destruct b as [x H].
    simpl.
    apply subset2_eq.
    simpl.
    rewrite zabs_nneg.
    - reflexivity.
    - apply H.
  Qed.


  (* Let us try to change Abs post-condition to semantically
  equivalent, but syntaxically different one: *)
  Program Definition zabs': Z -> {x:Z|x>=0-x} :=
    fun a => exist _ (Z.abs a) _.
  Next Obligation.
    simpl.
    intros a.
    assert (Z.abs a >= 0) by apply zabs_always_nneg.
    omega.
  Qed.

  (* We are no longer allowed to compose (zsqrt ∘ zabs') as their
  types do not match. We will add a glue to convert between them *)
  Fact zsqrt_zabs_glue: {x : Z | x >= 0 - x} -> {x : Z | x >= 0}.
  Proof.
    intros [ x H].
    exists x.
    omega.
  Defined.

  (* Now we can prove our lemma *)
  Lemma foo':
    zsqrt ∘ zsqrt_zabs_glue ∘ zabs' ∘ (@proj1_sig Z _) = zsqrt.
  Proof.
    apply functional_extensionality.
    intros b.
    unfold compose, zsqrt, zabs', zsqrt_zabs_glue.
    destruct b as [x H].
    simpl.
    apply subset2_eq.
    simpl.
    rewrite zabs_nneg.
    - reflexivity.
    - apply H.
  Qed.

End Specs.

(* -- Typelcass approach. Using type classes to refine types of arguments of sqrt --
PROS:
  * Properies are hidden and in some cases could be resolved implicitly.
  * Does not allow to construct incorrect expresions.
  * One have to ballance between specifying type class instances explicitly or leaving them implicit and letting typeclass resolution to resolve them automatically.
CONS:
  * Does not allow to use composition
  * Not pointfree
  * Automatic type class resolution sometimes difficult to debug. It is not very transparent and difficult to guide it in right direction.
  * It is difficult to construct even correct impression. The burden of proofs imposed by pre-conditions is a significant barrier.
  * Type classes instances could not be defined for refined types (refined by a predicate in the context
  *)
Module Typeclasses.

  (* Type class denoting nonnegative numbers *)
  Class NnegZ (val:Z) := nneg: val>=0.

  (* Argument of sqrt is constrained by typeclass NnegZ *)
  Definition zsqrt (a:Z) `{NnegZ a} : Z := Z.sqrt a.

  (* Fails:
         Unable to satisfy the following constraints:
         ?H : "NnegZ (-1234)"
   *)
  Fail Definition bar := zsqrt (-1234).

  (* NnegZ class instance for Z.abs, stating that Z.abs always positive *)
  Local Instance Zabs_nnegZ:
    forall x, NnegZ (Z.abs x).
  Proof.
    intros.
    unfold NnegZ.
    apply zabs_always_nneg.
  Qed.

  Lemma foo (x:Z) `{PZ:NnegZ x}:
    zsqrt (Z.abs x) = zsqrt x.
  Proof.
    unfold compose, zsqrt.
    rewrite zabs_nneg.
    - reflexivity.
    - apply PZ.
  Qed.

End Typeclasses.

