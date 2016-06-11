Require Import MathClasses.interfaces.abstract_algebra.

Section RewritingTest.

  Parameter A:Type.
  Parameter A_Equiv: Equiv A.
  Parameter A_Setoid: Setoid A.

  Variable f: A -> A.
  Variable f': A -> A.
  Variable g: A -> A.

  Lemma E: equiv f f'. Admitted.

  Parameter f_mor : Setoid_Morphism f.
  Parameter f'_mor : Setoid_Morphism f'.
  Parameter g_mor : Setoid_Morphism g.


  Instance equiv_proper:
    @Proper (forall (_ : forall _ : A, A) (_ : forall _ : A, A), Prop)
            (@respectful (forall _ : A, A) (forall _ : forall _ : A, A, Prop)
                         (@equiv (forall _ : A, A) (@ext_equiv A A_Equiv A A_Equiv))
                         (@respectful (forall _ : A, A) Prop
                                      (@equiv (forall _ : A, A) (@ext_equiv A A_Equiv A A_Equiv))
                                      (@flip Prop Prop Prop impl)))
            (@equiv (forall _ : A, A) (@ext_equiv A A_Equiv A A_Equiv)).
  Proof.
    Set Printing Implicit. Show.
  Admitted.


  Lemma Foo:
    f = f'.
  Proof.
    setoid_rewrite E.

  Admitted.

  Lemma Bar:
    compose f g = compose f' g.
  Proof.
    rewrite E.
  Qed.

End RewritingTest.