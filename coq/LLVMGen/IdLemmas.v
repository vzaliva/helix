(** * Valid identifiers

    When generating variable and block id names, we allow any purely alphabetical prefix
    to be appended with the current freshness generator.
    
    The predicate [is_correct_prefix] is used to check prefixes. It computes and can therefore always simply be discharged by [reflexivity].
    In particular [solve_prefix] takes care of it.

    The main result of this file is [valid_prefix_neq_differ] ensuring that the variables we generate are distinct without having to worry about the prefixes.

 *)

Require Import Helix.LLVMGen.Correctness_Prelude.

Set Implicit Arguments.
Set Strict Implicit.

Import  Ascii. 
Definition is_connector (c : ascii) : bool :=
  match c with
  | "095" => true
  | _ => false
  end.

Definition is_alpha (c : ascii) : bool :=
  if CeresString.is_upper c then true else if
      CeresString.is_lower c then true else
      if is_connector c then true else false.

Definition is_correct_prefix (s : string) : bool :=
  CeresString.string_forall is_alpha s.

Lemma string_of_nat_not_alpha : forall n,
  CeresString.string_forall (fun c => negb (is_alpha c)) (string_of_nat n).
Admitted.

Lemma is_correct_prefix_String : forall c s,
    is_correct_prefix (String c s) ->
    is_correct_prefix s /\ is_alpha c.
Proof.
  intros.
  cbn in H.
  break_match_hyp; auto.
  inv H.
Qed.

Import Ascii String.

Lemma valid_prefix_string_of_nat_aux :
  forall n k s,
    is_correct_prefix s ->
    string_of_nat n ≡ s @@ string_of_nat k ->
    n ≡ k /\ s ≡ EmptyString.
Proof.
  induction s as [| c s IH].
  - unfold append; cbn; intros _ EQ; split; auto.
    edestruct NPeano.Nat.eq_dec; try eassumption.
    apply string_of_nat_inj in n0; contradiction n0; auto. 
  - intros COR EQ; apply is_correct_prefix_String in COR; destruct COR as [PRE ALPHA]. 
    exfalso.
    destruct (string_of_nat n) as [| c' ?] eqn:EQ'; [inv EQ |].
    assert (c' ≡ c) by (unfold append in EQ; cbn in EQ; inv EQ; reflexivity).
    subst.
    pose proof string_of_nat_not_alpha n as H.
    rewrite EQ' in H.
    cbn in H.
    break_match_hyp; auto.
    rewrite ALPHA in Heqb; inv Heqb.
    inv H.
Qed.

Lemma valid_prefix_string_of_nat_forward :
  forall s1 s2 n k,
    is_correct_prefix s1 ->
    is_correct_prefix s2 ->
    s1 @@ string_of_nat n ≡ s2 @@ string_of_nat k ->
    n ≡ k /\ s1 ≡ s2.
Proof.
  induction s1 as [| c s1 IH].
  - cbn; intros.
    unfold append at 1 in H1; cbn in H1.
    apply valid_prefix_string_of_nat_aux in H1; auto; intuition.
  - intros * CORR1 CORR2 EQ.
    destruct s2 as [| c' s2].
    + exfalso.
      unfold append at 2 in EQ.
      symmetry in EQ.
      apply valid_prefix_string_of_nat_aux in EQ; auto.
      destruct EQ as [_ abs]; inv abs.
    + assert (forall c s s', String c s @@ s' ≡ String c (s @@ s')) by (intros; unfold append; reflexivity).
      rewrite 2 H in EQ.
      inv EQ; clear H.
      apply is_correct_prefix_String in CORR1; destruct CORR1 as [CORR1 ALPHA1].
      apply is_correct_prefix_String in CORR2; destruct CORR2 as [CORR2 _].
      edestruct IH; try eassumption.
      subst; auto.
Qed.
      
 Lemma valid_prefix_neq_differ :
  forall s1 s2 n k,
    is_correct_prefix s1 ->
    is_correct_prefix s2 ->
    n ≢ k ->
    s1 @@ string_of_nat n ≢ s2 @@ string_of_nat k.
Proof.
  intros s1 s2 n k NS1 NS2 NK.
  epose proof valid_prefix_string_of_nat_forward s1 s2 n k NS1 NS2 as contra.
  intros abs.
  apply contra in abs as [NK_EQ _].
  contradiction.
Qed.

Lemma string_forall_append:
  forall s s' f,
    CeresString.string_forall f s ->
    CeresString.string_forall f s' ->
    CeresString.string_forall f (s @@ s').
Proof.
  intros s s'. revert s.
  induction s'.
  - cbn. intros. cbn. rewrite append_EmptyString. auto.
  - intros. cbn in H0.
    destruct (f a) eqn: FA.
    2 : { inversion H0. }
Admitted.

Lemma is_correct_prefix_append: forall s1 s2,
    is_correct_prefix s1 ->
    is_correct_prefix s2 ->
    is_correct_prefix (s1 @@ s2).
Proof.
  intros; apply string_forall_append; auto.
Qed.

Ltac solve_prefix :=
  try now (unfold append; cbn; reflexivity).
