Variable A:Type.
Variable dot: A->A->A.
Notation "x · y" := (dot x y) (at level 80).

(* For paper *)
Theorem For_Paper_1:
  forall (op: CarrierA -> CarrierA -> CarrierA)
    (a b: Rtheta),
    execWriter (liftM2 op a b) =
               RthetaFlagsAppend (execWriter a) (execWriter b).

Proof.
  intros op a b.
  unfold execWriter, liftM2.
  simpl.
  rewrite RthetaFlags_runit.
  reflexivity.
Qed.
