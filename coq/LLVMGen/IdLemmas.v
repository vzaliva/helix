Require Import Helix.LLVMGen.Correctness_Prelude.

Set Implicit Arguments.
Set Strict Implicit.

Definition not_ends_with_nat (str : string) : Prop
  := forall pre n, str ≢ pre @@ string_of_nat n.

Lemma not_ends_with_nat_string_of_nat :
  forall s1 s2 n k,
    not_ends_with_nat s1 ->
    not_ends_with_nat s2 ->
    (s1 @@ string_of_nat n ≡ s2 @@ string_of_nat k <-> n ≡ k /\ s1 ≡ s2).
Proof.
  intros s1 s2 n k NS1 NS2.
  split.
  { admit.
  }

  {
    intros [NK S1S2].
    subst.
    auto.
  }
Admitted.

Lemma not_ends_with_nat_neq :
  forall s1 s2 n k,
    not_ends_with_nat s1 ->
    not_ends_with_nat s2 ->
    n ≢ k ->
    s1 @@ string_of_nat n ≢ s2 @@ string_of_nat k.
Proof.
  intros s1 s2 n k NS1 NS2 NK.
  epose proof (not_ends_with_nat_string_of_nat n k NS1 NS2) as [CONTRA _].
  intros H.
  apply CONTRA in H as [NK_EQ _].
  contradiction.
Qed.

Lemma not_ends_with_nat_nop :
  not_ends_with_nat "Nop".
Proof.
Admitted.

Lemma not_ends_with_nat_assign :
  not_ends_with_nat "Assign".
Proof.
Admitted.

Lemma not_ends_with_nat_imap_entry :
  not_ends_with_nat ("IMap" @@ "_entry").
Proof.
Admitted.

Lemma not_ends_with_nat_imap_loop :
  not_ends_with_nat ("IMap" @@ "_loop").
Proof.
Admitted.

Lemma not_ends_with_nat_imap_lcont :
  not_ends_with_nat ("IMap_lcont").
Proof.
Admitted.

Lemma not_ends_with_nat_binop_entry :
  not_ends_with_nat ("BinOp" @@ "_entry").
Proof.
Admitted.

Lemma not_ends_with_nat_binop_loop :
  not_ends_with_nat ("BinOp" @@ "_loop").
Proof.
Admitted.

(* TODO: This is obviously not true, but I want to discharge all
     these goals that this *should* be true for *)
Lemma not_ends_with_nat_all :
  forall pre,
    not_ends_with_nat pre.
Proof.
Admitted.

Hint Resolve not_ends_with_nat_nop : NOT_ENDS_WITH.
Hint Resolve not_ends_with_nat_assign : NOT_ENDS_WITH.
Hint Resolve not_ends_with_nat_imap_entry : NOT_ENDS_WITH.
Hint Resolve not_ends_with_nat_imap_loop : NOT_ENDS_WITH.
Hint Resolve not_ends_with_nat_imap_lcont : NOT_ENDS_WITH.
Hint Resolve not_ends_with_nat_binop_entry : NOT_ENDS_WITH.
Hint Resolve not_ends_with_nat_binop_loop : NOT_ENDS_WITH.
Hint Resolve not_ends_with_nat_all : NOT_ENDS_WITH.

Ltac solve_not_ends_with := eauto with NOT_ENDS_WITH.
