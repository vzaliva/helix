(* Error-carrying type. Similar to 'option' *)

Require Import Coq.Strings.String.

Require Import MathClasses.interfaces.abstract_algebra.

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

Lemma OK_intro {B} {m: @maybeError B}:
  forall x,  (m ≡ OK x) -> is_OK m.
Proof.
  intros x E.
  unfold is_OK.
  destruct m.
  auto.
  congruence.
Qed.

Lemma OK_exists {B} {m: @maybeError B}:
  is_OK m -> (exists x, m ≡ OK x).
Proof.
  intros.
  destruct m.
  exists b. reflexivity.
  unfold is_OK in H.
  contradiction.
Qed.

(* ----------- Some handy tactics ----------- *)

(* simple tactic to get rid is_OK/is_Error goals which are 
frequently produced by cases analsysis on matcing error conditions *)

Ltac err_ok_elim := 
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
Ltac ok_err_elim :=  err_ok_elim.
