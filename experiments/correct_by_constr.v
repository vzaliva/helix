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


(* -- Naive approach. No preconditions on sqrt. --
PROS:
  * can use composition notation
  * can define experessions before reasoning about them.
CONS:
  * not pointfree
  * allows to construct incorrect expresions. E.g. 'bar' below.
  * does not allow to express post-conditions
  *)
Module Naive.

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

End Naive.


(* -- Pre-conditoins approach. Simple precondition on sqrt. --
PROS:
  * does not allow to construct incorrect expresions.
  * all preconditions are clearly spelled and have to be proven manually before constructing the expression. No automatic proof search.
CONS:
  * can not easily compose experessions before reasoning about them.
  * can not use composition notation
  * not pointfree
  * does not allow to express post-conditions
  *)
Module PreCondition.

  (* Version of sqrt with pre-condition *)
  Definition zsqrt_p (x:Z) {ac:x>=0} := Z.sqrt x.

  (* Fails: Cannot infer the implicit parameter ac of zsqrt_p whose type is  "-1234 >= 0". Since it is unporovable, this experession could not be constructed.
   *)
  Fail Definition bar := zsqrt_p (-1234).

  (* This is lemma about composition of 'zsqrt_p' and 'Z.abs'. Unfortunately we could not write this in pointfree style using functoin composition *)
  Lemma foo_p (x:Z) (xp:x>=0):
    @zsqrt_p (Z.abs x) (zabs_always_nneg x) = @zsqrt_p x xp.
  Proof.
    unfold zsqrt_p.
    rewrite zabs_nneg.
    - reflexivity.
    - apply xp.
  Qed.

End PreCondition.

(* -- Spec approach. Using specifications to refine types of arguments of sqrt as well as return value of abs --
PROS:
  * allows to use composition
  * pointfree
  * values along with their properties are nicely bundled using `sig` or {|}.
  * does not allow to construct incorrect expresions.
  * all preconditions are clearly spelled out. Constructing correct expression is just a matter of correctly matching parameter and return types of expressions.
CONS:
  * requires a bit of syntactic sugar here and there (e.g. use of `proj1_sig_ge0` in 'foo_s'.
  * predicates in spec must match exactly. For example if we have value {a|a>0} we could not directly use it instead of {a|a>=0}.
  * there is no logical inference performed on specs. Not even simple structural rules application https://en.wikipedia.org/wiki/Structural_rule. For example {a|(P1 a)/\(P2 a)} could not be used in place of {a|(P2 a)/\(P1 a)} or {a|P1 a}
  * Return values could contain only one spec. Multiple post-conditions have to be bundled together.
  *)
Module Specs.

  (* "Refined" with specifications versions of sqrt and abs *)
  Definition zsqrt_s (a:{x:Z|x>=0}) := Z.sqrt (proj1_sig a).
  Definition zabs_s: Z -> {x:Z|x>=0} :=
    fun a => exist _ (Z.abs a) (zabs_always_nneg a).

  (* Fails: Cannot infer this placeholder of type "(fun x : Z => x >= 0) (-1234)". *)
  Fail Definition bar := zsqrt_s (exist _ (-1234) _).

  (* The implicit agrument (which we will make explicit by applying
  'functional_extensionality' has type {x:Z|x>=0}. To use it in zabs_s
  we have to project witness from it. We are doing this by composing
  with (@proj1_sig Z _). It is a bit bulky and I wish I did not have
  to specify arguments Z and _ but Coq could not infer them
  automatically.

  Another way to do this would be via automatic coercion mechanism,
  by defining something like this:

  Definition witness {P : Z -> Prop} (x : sig P) := proj1_sig x.
  Coercion witness : sig >-> Z.

  Unfortunately, this does not currently work due to this Coq bug:

  https://coq.inria.fr/bugs/show_bug.cgi?id=4114
   *)
  Lemma foo_s:
    zsqrt_s ∘ zabs_s ∘ (@proj1_sig Z _) = zsqrt_s.
  Proof.
    apply functional_extensionality.
    intros a.
    unfold compose, zsqrt_s, zabs_s.
    simpl.
    rewrite zabs_nneg.
    - reflexivity.
    - apply (proj2_sig a).
  Qed.

End Specs.

(* TODO: document *)
Module Specs1.
  (* "Refined" with specifications versions of sqrt and abs *)

  (* Sqrt has both post and pre-conditions. *)
  (* For demonstration purposes we will solve obligation manually. *)
  Local Obligation Tactic := idtac.
  (* Alternatively both obligations' proofs could be specified explicitly, instead of _
   *)
  Program Definition zsqrt_s (a:{x:Z|x>=0}): {y:Z|y>=0 & not (y<0)}
    := exist2 _ _ (Z.sqrt (proj1_sig a))
              _  _.
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


  (* Abs as only post-condition *)
  Definition zabs_s: Z -> {x:Z|x>=0} :=
    fun a => exist _ (Z.abs a) (zabs_always_nneg a).

  (* Fails: Cannot infer this placeholder of type "(fun x : Z => x >= 0) (-1234)". *)
  Fail Definition bar := zsqrt_s (exist _ (-1234) _).

  Lemma foo_s (b : {x : Z | x >= 0}):
    (zsqrt_s ∘ zabs_s) (proj1_sig b) = zsqrt_s b.
  Proof.
    unfold compose, zsqrt_s, zabs_s.
    destruct b as [x H].
    simpl.
    apply subset2_eq.
    simpl.
    rewrite zabs_nneg.
    - reflexivity.
    - apply H.
  Qed.

End Specs1.

(* -- Typelcass approach. Using type classes to refine types of arguments of sqrt --
PROS:
  * properies are hidden and in some cases could be resolved implicitly.
  * does not allow to construct incorrect expresions.
  * One have to ballance between specifying type class instances explicitly or let them implicit and letting typeclass resolution to resolve them automatically.
  * Multiple post-conditions can be specified using multiple type class instances.
CONS:
  * does not allow to use composition
  * not pointfree
  * Automatic type class resolution sometimes difficult to debug. It is not very transparent and difficult to guide it in right direction.
  * It is difficult to construct even correct impression. The burden of proofs imposed by pre-conditions is a significant barrier.
  *)
Module Typeclasses.

  (* Type class denoting nonnegative numbers *)
  Class NnegZ (val:Z) := nneg: val>=0.

  (* Argument of sqrt is constrained by typeclass NnegZ *)
  Definition zsqrt_t (a:Z) `{NnegZ a} : Z := Z.sqrt a.

  (* Fails:
         Unable to satisfy the following constraints:
         ?H : "NnegZ (-1234)"
   *)
  Fail Definition bar := zsqrt_t (-1234).

  (* NnegZ class instance for Z.abs, stating that Z.abs always positive *)
  Local Instance Zabs_nnegZ:
    forall x, NnegZ (Z.abs x).
  Proof.
    intros.
    unfold NnegZ.
    apply zabs_always_nneg.
  Qed.

  Lemma foo_t (x:Z) `{PZ:NnegZ x}:
    zsqrt_t (Z.abs x) = zsqrt_t x.
  Proof.
    unfold compose, zsqrt_t.
    rewrite zabs_nneg.
    - reflexivity.
    - apply PZ.
  Qed.

End Typeclasses.

(* -- Implicit Typelcass approach. Using type classes to refine types of arguments of sqrt, but resolve tem manually --
PROS:
  * does not allow to construct incorrect expresions.
  * Multiple post-conditions can be specified using multiple type class instances.
CONS:
  * does not allow to use composition
  * not pointfree
  * when constructing expressions all implicit parameters have to be specified making them complex and diffcult to parse
  * when multiple type classes are used multiple 'exists' constructs has to be specified, intricately dependent on each other.
  * Resulting lemmas could not be used directly for rewriting. Need some special handling (using 'unshelve eexists') before applied.
  *)
Module ImplicitTypeclasses.

  (* Type class denoting nonnegative numbers *)
  Class NnegZ_x (val:Z) := nneg_x: val>=0.

  (* Argument of sqrt is constrained by typeclass NnegZ *)
  Definition zsqrt_x (a:Z) `{NN: NnegZ_x a} : Z := Z.sqrt a.

  (* Fails:
         Unable to satisfy the following constraints:
         ?H : "NnegZ (-1234)"
   *)
  Fail Definition bar := zsqrt_x (-1234).

  Lemma foo1_x:
    exists PA, forall (x:Z) `{PZ:NnegZ_x x}, @zsqrt_x (Z.abs x) (PA x) = @zsqrt_x x PZ.
  Proof.
    unshelve eexists.
    -
      unfold NnegZ_x.
      apply zabs_always_nneg.
    -
      intros x PZ.
      unfold zsqrt_x.
      rewrite zabs_nneg.
      + reflexivity.
      + apply PZ.
  Qed.

End ImplicitTypeclasses.

