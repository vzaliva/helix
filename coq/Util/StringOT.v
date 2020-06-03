(*
Borrowed from https://github.com/QuickChick/QuickChick/blob/master/src/StringOT.v

Ordering code by Antal :)

*)

Require Import Coq.Structures.OrderedType.
Require Import Coq.Strings.String.

Require Import Helix.Util.AsciiOT.

Module StringOT <: OrderedType.

Definition t := string.

Definition eq       := @Logic.eq       string.
Definition eq_refl  := @Logic.eq_refl  string.
Definition eq_sym   := @Logic.eq_sym   string.
Definition eq_trans := @Logic.eq_trans string.
Definition eq_dec   := string_dec.

Inductive SOrdering := SLT | SEQ | SGT.

Fixpoint strcmp (s1 s2 : string) : SOrdering :=
  match s1, s2 with
    | EmptyString,    EmptyString    => SEQ
    | EmptyString,    String _ _     => SLT
    | String _   _,   EmptyString    => SGT
    | String ch1 s1', String ch2 s2' =>
        match AsciiOT.compare ch1 ch2 with
          | LT _ => SLT
          | EQ _ => strcmp s1' s2'
          | GT _ => SGT
        end
  end.

Definition lt (s1 s2 : string) := strcmp s1 s2 = SLT.

Local Ltac do_ascii_lt_trans :=
  match goal with
    | [  _ : AsciiOT.lt ?c1 ?c2
      ,  _ : AsciiOT.lt ?c2 ?c3
      |- _ ]
      => assert (AsciiOT.lt c1 c3) by (eapply AsciiOT.lt_trans; eauto)
  end.

Local Ltac not_ascii_lt_refl :=
  match goal with
    | [ _ : AsciiOT.lt ?c ?c |- _ ]
      => assert (c <> c) by (apply AsciiOT.lt_not_eq; assumption);
         congruence
  end.

Theorem lt_trans : forall s1 s2 s3 : string, lt s1 s2 -> lt s2 s3 -> lt s1 s3.
Proof.
  unfold lt; intros s1 s2; generalize dependent s1; induction s2 as [| c2 s2'].
  (* s2 = "" *)
    destruct s1; [trivial | simpl; congruence].
  (* s2 <> "" *)
    destruct s1 as [| c1 s1']; simpl.
    (* s1 = "" *)
      destruct s3; [congruence | trivial].
    (* s1 <> "" *)
      destruct s3 as [| c3 s3']; [congruence |].
      (* s3 <> "" *)
        destruct (AsciiOT.compare c1 c2) as [? | ? | ?] eqn:?;
        destruct (AsciiOT.compare c2 c3) as [? | ? | ?] eqn:?;
        destruct (AsciiOT.compare c1 c3) as [? | ? | ?] eqn:?;
        unfold AsciiOT.eq in *; subst;
        solve [ apply IHs2'
              | congruence
              | repeat (try not_ascii_lt_refl; do_ascii_lt_trans) ].
Qed.

Theorem lt_not_eq : forall s1 s2 : string, lt s1 s2 -> ~ eq s1 s2.
Proof.
  unfold lt, eq; induction s1 as [| c1 s1'].
  (* s1 = "" *)
    destruct s2; simpl; congruence.
  (* s1 <> "" *)
    destruct s2 as [| c2 s2']; simpl.
    (* s2 = "" *)
      congruence.
    (* s2 <> "" *)
        destruct (AsciiOT.compare c1 c2) as [? | ? | ?] eqn:?;
        intros Hc Heq; inversion Heq.
        (* c1 < c2 *)
          subst; not_ascii_lt_refl.
        (* c1 = c2 *)
          apply IHs1' in Hc; apply Hc; assumption.
        (* c1 > c2 *)
          congruence.
Qed.

Theorem compare : forall s1 s2 : string, Compare lt eq s1 s2.
Proof.
  unfold lt, eq; induction s1 as [| c1 s1'].
  (* s1 = "" *)
    destruct s2; [apply EQ | apply LT]; auto.
  (* s1 <> "" *)
    destruct s2 as [| c2 s2']; [apply GT; auto | ].
    destruct (AsciiOT.compare c1 c2) as [? | ? | ?] eqn:Hcmp.
    (* c1 < c2 *)
      apply LT; simpl; rewrite Hcmp; auto.
    (* c1 = c2 *)
      unfold AsciiOT.eq in *; subst.
      destruct (IHs1' s2'); [apply LT | apply EQ | apply GT];
      first [ simpl; rewrite Hcmp; assumption | subst; reflexivity ].
    (* c1 > c2 *)
      apply GT; simpl.
      destruct (AsciiOT.compare c2 c1) as [? | ? | ?] eqn:Hcmp'.
        reflexivity.
        unfold AsciiOT.eq in *; subst; not_ascii_lt_refl.
        do_ascii_lt_trans; not_ascii_lt_refl.
Qed.

End StringOT.
