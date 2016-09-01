Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.
Require Import Coq.Init.Specif.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Local Open Scope program_scope.
Local Open Scope Z_scope.

(* Functoins used in this example:
Z.sqrt - unconstrained square root
zsqrt - "correct by construction" square root, which requires non-negative argument.
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

  Fact zabs_always_pos: forall x, (Z.abs x) >= 0.
  Proof.
    intros.
    unfold Z.abs.
    destruct x.
    - omega.
    - induction p;auto;omega.
    - induction p;auto;omega.
  Qed.

  Fact zabs_pos: forall x, x>=0 -> Z.abs x = x.
  Proof.
    intros.
    destruct x.
    - auto.
    - auto.
    - assert(Z.neg p < 0) by apply Pos2Z.neg_is_neg.
      omega.
  Qed.

End ZAbs_facts.


Section SimpleConstrain.

  (* "Refined" version of sqrt *)
  Definition zsqrt (x:Z) {ac:x>=0} := Z.sqrt x.

  (* This is lemma about composition of 'zsqrt' and 'zabs'. Unfortunately we could not write this in pointfree style using functoin composition *)
  Lemma foo (x:Z) (xp:x>=0):
    @zsqrt (Z.abs x) (zabs_always_pos x) = @zsqrt x xp.
  Proof.
    unfold zsqrt.
    rewrite zabs_pos.
    - reflexivity.
    - apply xp.
  Qed.

End SimpleConstrain.
