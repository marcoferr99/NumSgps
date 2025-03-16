From Coq Require Import ClassicalUniqueChoice Description FunctionalExtensionality.

Section Relation.

  Context {A B : Type} (R : A -> B -> Prop).

  Definition rel_ex_func : (forall x, exists ! y, R x y) ->
    exists f,
    (forall x, R x (f x)) /\ forall x y, R x y -> y = f x.
  Proof.
    intros H.
    destruct (unique_choice _ _ _ H) as [f Hf].
    exists f. intros. split; try apply Hf.
    intros x y HR. specialize H with x.
    apply unique_existence in H. apply H; auto.
  Qed.

  Definition rel_func : (forall x, exists ! y, R x y) ->
    {f | (forall x, R x (f x)) /\ forall x y, R x y -> y = f x}.
  Proof.
    intros. apply constructive_definite_description.
    generalize (rel_ex_func H). intros [f Hf].
    exists f. split; try assumption.
    intros g Hg. extensionality x. intuition.
  Qed.

End Relation.
