Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.
Require Import Coq.Init.Specif.
Require Import Coq.ZArith.ZArith.
Local Open Scope program_scope.
Local Open Scope Z_scope.


(* Integer functoins used in this example:
Z.sqrt - square root. For negative values returns 0.
Z.abs - absolute value.
Z.sgn - sign (returns -1|0|1).
 *)

(* Sample lemma showing how we can reason about function composition using function extensionality. SPIRAL rules could be written like that *)
Lemma abs_sgn_comm: (Z.abs ∘ Z.sgn) = (Z.sgn ∘ Z.abs).
Proof.
  apply functional_extensionality.
  intros.
  unfold compose.
  destruct x; auto.
Qed.

(* Some helpful facts about zabs *)
Section ZAbs_facts.

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

End ZAbs_facts.


(* Simple approach. No preconditions on sqrt. *)
Section Simple.

  (* We can use composition, but not pointfree because of constraint x>=0 *)
  Lemma foo (x:Z) (xp:x>=0):
    (Z.sqrt ∘ Z.abs) x = Z.sqrt x.
  Proof.
    unfold compose.
    rewrite zabs_nneg.
    - reflexivity.
    - apply xp.
  Qed.

End Simple.


(* Pre-conditoins approach. Simple preconditions on sqrt. *)
Section PreCondition.

  (* Version of sqrt with pre-condition *)
  Definition zsqrt_p (x:Z) {ac:x>=0} := Z.sqrt x.

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

(* Spec approach. Using specifications to refine types of arguments of sqrt as well as return value of abs *)
Section Specs.

  (* "Refined" with specifications versions of sqrt and abs *)
  Definition zsqrt_s (a:{x:Z|x>=0}) := Z.sqrt (proj1_sig a).
  Definition zabs_s: Z -> {x:Z|x>=0} :=
    fun a => exist _ (Z.abs a) (zabs_always_nneg a).

  (* Helper syntactic sugar to make sure projection types are properly guessed *)
  Definition proj1_sig_ge0 (a:{x:Z|x>=0}): Z := proj1_sig a.

  (* Using specifications we can use pointfree style, but we have to add as projection function as zabs_s takes a value without any specification *)
  Lemma foo_s:
    zsqrt_s ∘ zabs_s ∘ proj1_sig_ge0  = @zsqrt_s.
  Proof.
    apply functional_extensionality.
    intros a.
    unfold compose, proj1_sig_ge0, zsqrt_s, zabs_s.
    simpl.
    rewrite zabs_nneg.
    - reflexivity.
    - apply (proj2_sig a).
  Qed.

End Specs.

(* Typelcass approach. Using type classes to refine types of arguments of sqrt *)
Section Typeclasses.

  (* Type class denoting nonnegative numbers *)
  Class NnegZ (val:Z) := nneg: val>=0.

  (* Argument of sqrt is constrained by typeclass NnegZ *)
  Definition zsqrt_t (a:Z) `{NnegZ a} : Z := Z.sqrt a.

  (* NnegZ class instance for Z.abs, stating that Z.abs always positive *)
  Global Instance Zabs_nnegZ:
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
