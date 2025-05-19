From stdpp Require Export sets.


(**************)
(** * Minimum *)
(**************)

Section minimum.
  Context `{ElemOf A C} (R : relation A).

  Definition lower_bound x (X : C) : Prop :=
    forall y, y ∈ X -> R x y.

  Theorem lower_bound_minimal x (X : C) :
    lower_bound x X -> minimal R x X.
  Proof. unfold lower_bound, minimal. intros. auto. Qed.

  Definition minimum x (X : C) : Prop :=
    x ∈ X ∧ lower_bound x X.

  Theorem minimum_unique `{!AntiSymm (=) R} X x y :
    minimum x X -> minimum y X -> x = y.
  Proof.
    unfold minimum, lower_bound. intros.
    apply (anti_symm R x y); intuition.
  Qed.

End minimum.
