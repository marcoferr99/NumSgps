Require Export list_nat nat.
From Coq Require Import Euclid.

Generalizable No Variables.
Generalizable Variables C D M.


(*************************************)
(** * Numerical semigroup definition *)
(*************************************)

Class submonoid `{Set_ nat C} (M : C) : Prop := {
  ns_zero : 0 ∈ M;
  ns_closed : forall a b, a ∈ M -> b ∈ M -> a + b ∈ M
}.

Theorem ns_mul_closed `{submonoid C M} :
  forall n m, m ∈ M -> n * m ∈ M.
Proof.
  intros. induction n.
  - rewrite mul_0_l. apply ns_zero.
  - now apply ns_closed.
Qed.

Class numerical_semigroup `{Set_ nat C} (M : C) : Set := numerical_semigroup_intro {
  ns_submonoid :: submonoid M;
  gaps : list nat;
  sorted_gaps : Sorted lt gaps;
  elem_of_gaps x : x ∈ M <-> x ∉ gaps
}.
Arguments numerical_semigroup_intro {_ _ _ _ _ _ _ _ _}.

Instance ns_Decision `{numerical_semigroup C M} x :
  Decision (x ∈ M).
Proof.
  destruct (elem_of_list_dec x gaps).
  - right. intros N. apply elem_of_gaps in N. auto.
  - left. apply elem_of_gaps. assumption.
Qed.

Theorem elem_of_gaps' `{numerical_semigroup C M} x :
  x ∈ gaps <-> x ∉ M.
Proof.
  split; intros Ha.
  - intros N. apply elem_of_gaps in N. auto.
  - destruct (elem_of_list_dec x gaps); [assumption|].
    exfalso. apply Ha. apply elem_of_gaps. assumption.
Qed.

(** Some definitions over numerical semigroups *)

Section numerical_semigroup.
  Context `{numerical_semigroup C M}.

  Definition genus := length gaps.

  Definition multiplicity := find_gap 1 gaps.

  Theorem multiplicity_min :
    minimum le multiplicity (M ∖ {[0]}).
  Proof.
    split.
    - apply elem_of_difference. split.
      + apply elem_of_gaps.
	apply (find_gap_notin 1); [apply sorted_gaps|].
	apply Forall_forall. intros x Hx.
	assert (x <> 0); [|lia].
	intros X. subst.
	apply elem_of_gaps' in Hx. apply Hx. apply ns_zero.
      + intros N. set_unfold.
	generalize (find_gap_le 1 gaps).
	unfold multiplicity in N. lia.
    - intros n Hn. set_unfold.
      apply find_gap_notin_le.
      + apply sorted_gaps.
      + now apply elem_of_gaps.
      + lia.
  Qed.

  Definition conductor :=
    match gaps with
    | [] => 0
    | h :: t => S (list_max gaps)
    end.

  Theorem conductor_le_in x : conductor <= x -> x ∈ M.
  Proof.
    unfold conductor. intros L.
    apply elem_of_gaps. destruct gaps eqn : ?; [easy|].
    apply list_max_notin. lia.
  Qed.

  Definition small_elements :=
    filter (.∈ M) (seq 0 (S conductor)).

  Theorem small_elements_spec :
    forall x, x ∈ small_elements <->
    x ∈ M ∧ x <= conductor.
  Proof.
    intros. unfold small_elements.
    rewrite elem_of_list_filter, elem_of_seq.
    split; intros []; (split; [assumption|lia]).
  Qed.

End numerical_semigroup.

(** Equivalent definition for a numerical semigroup *)

Definition numerical_semigroup_2 `{submonoid C M} a :
  (forall x, Decision (x ∈ M)) -> a ∈ M -> S a ∈ M ->
  numerical_semigroup M.
Proof.
  intros D Ma MS.
  set (m := (a - 1) * (a + 1)).
  assert (I : forall n, n >= m -> n ∈ M). {
    intros n Hn. destruct a.
    - replace n with (n * 1); [|lia].
      now apply ns_mul_closed.
    - assert (diveucl n (S a)) as [q r g e].
	{ apply eucl_dev. trivial with arith. }
      assert (N : n = (q - r) * S a + r * (S (S a))). {
	assert (q >= r). {
	  apply le_trans with a; try lia.
	  assert (a * S a <= q * S a); try lia.
	  rewrite mul_le_mono_pos_r; [eassumption | lia].
	}
	replace (S (S a)) with (S a + 1); try lia.
	rewrite mul_sub_distr_r, mul_add_distr_l.
	rewrite add_assoc, sub_add; try lia.
	now apply mul_le_mono_r.
      }
      rewrite N.
      apply ns_closed; now apply ns_mul_closed.
  }
  set (l := filter (.∉ M) (seq 0 m)).
  apply (numerical_semigroup_intro _ l).
  - subst l. apply StronglySorted_Sorted.
    apply StronglySorted_filter.
    apply Sorted_StronglySorted; [intros ?; lia|].
    apply Sorted_lt_seq.
  - intros x. subst l.
    rewrite elem_of_list_filter.
    split; intros Hx; [intuition|].
    destruct (D x); try assumption.
    exfalso. apply Hx. split; try assumption.
    destruct (le_gt_cases m x).
    + exfalso. auto.
    + apply elem_of_seq. lia.
Qed.
