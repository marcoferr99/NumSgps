Require Export list nat.
From Coq Require Import Euclid.

Generalizable No Variables.
Generalizable Variable M.


(*************************************)
(** * Numerical semigroup definition *)
(*************************************)

Class submonoid (M : propset nat) : Prop := {
  ns_zero : 0 ∈ M;
  ns_closed : forall a b, a ∈ M -> b ∈ M -> a + b ∈ M
}.

Theorem ns_mul_closed `{submonoid M} :
  forall n m, m ∈ M -> n * m ∈ M.
Proof.
  intros. induction n.
  - rewrite mul_0_l. apply ns_zero.
  - now apply ns_closed.
Qed.

Class numerical_semigroup M : Set := {
  ns_submonoid :: submonoid M;
  gaps : list nat;
  sorted_gaps : Sorted lt gaps;
  elem_of_gaps x : x ∈ M <-> x ∉ gaps
}.

Instance ns_Decision `{numerical_semigroup M} x :
  Decision (x ∈ M).
Proof.
  destruct (elem_of_list_dec x gaps).
  - right. intros N. apply elem_of_gaps in N. auto.
  - left. apply elem_of_gaps. assumption.
Qed.

Theorem elem_of_gaps' `{numerical_semigroup M} x :
  x ∈ gaps <-> x ∉ M.
Proof.
  split; intros Ha.
  - intros N. apply elem_of_gaps in N. auto.
  - destruct (elem_of_list_dec x gaps); [assumption|].
    exfalso. apply Ha. apply elem_of_gaps. assumption.
Qed.

(** Some definitions over numerical semigroups *)

Fixpoint multiplicity_aux x l :=
  match l with
  | [] => x
  | h :: t =>
      if h =? x then multiplicity_aux (S x) t else x
  end.

Theorem multiplicity_aux_le x l :
  x <= multiplicity_aux x l.
Proof.
  generalize dependent x. induction l; simpl; [lia|].
  intros x. destruct (eqb_spec a x); [|lia].
  subst. eapply le_trans; [|apply IHl]. lia.
Qed.

Theorem multiplicity_aux_le_lt_in x l : Sorted lt l ->
  forall n, x <= n < multiplicity_aux x l -> n ∈ l.
Proof.
  intros L n [Le Lt]. generalize dependent x.
  induction l; simpl in *; [lia|].
  intros x Le Lt.
  destruct (eq_dec n a); subst; [constructor|]. right.
  assert (LS : Sorted lt l); [inversion L; assumption|].
  destruct (eqb_spec a x).
  - eapply IHl; [assumption| |eassumption]. lia.
  - eapply IHl; [assumption|eassumption|]. lia.
Qed.

Theorem multiplicity_aux_notin x l : Sorted lt l ->
  Forall (le x) l -> multiplicity_aux x l ∉ l.
Proof.
  intros L. generalize dependent x. induction l; [easy|].
  simpl. intros x F.
  assert (Sorted lt l); [inversion L; assumption|].
  apply Sorted_StronglySorted in L; [|intros ?; lia].
  destruct (eqb_spec a x); intros C; inversion C; subst.
  - generalize (multiplicity_aux_le (S x) l). lia.
  - specialize IHl with (S x). apply IHl; try assumption.
    apply Forall_forall. intros a Ha.
    assert (x < a); [|lia].
    inversion L. eapply Forall_forall; eassumption.
  - contradiction.
  - assert (x <= a). {
      eapply Forall_forall; [eassumption|constructor].
    }
    assert (a < x); [|lia].
    inversion L. subst. eapply Forall_forall; eassumption.
Qed.

Theorem multiplicity_aux_notin_le x l n : Sorted lt l ->
  n ∉ l -> n >= x -> multiplicity_aux x l <= n.
Proof.
  intros L N G.
  destruct (le_gt_cases (multiplicity_aux x l) n);
    [assumption|].
  exfalso. apply N.
  eapply multiplicity_aux_le_lt_in; [assumption|].
  split; eassumption.
Qed.

Section numerical_semigroup.
  Context `{numerical_semigroup M}.

  Definition genus := length gaps.

  Definition multiplicity := multiplicity_aux 1 gaps.

  Theorem multiplicity_min :
    set_min (M ∖ {[0]}) multiplicity.
  Proof.
    split.
    - apply elem_of_difference. split.
      + apply elem_of_gaps.
	apply (multiplicity_aux_notin 1);
	  [apply sorted_gaps|].
	apply Forall_forall. intros x Hx.
	assert (x <> 0); [|lia].
	intros X. subst.
	apply elem_of_gaps' in Hx. apply Hx. apply ns_zero.
      + intros N. apply elem_of_singleton in N.
	generalize (multiplicity_aux_le 1 gaps).
	unfold multiplicity in N. lia.
    - intros n Hn. set_unfold in Hn.
      apply multiplicity_aux_notin_le.
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
    apply elem_of_gaps. destruct gaps eqn : E; [easy|].
    apply list_max_notin. lia.
  Qed.

End numerical_semigroup.

(** Equivalent condition for a numerical semigroup *)

Theorem numerical_semigroup_equiv1 `{numerical_semigroup M} :
  submonoid M /\ exists2 x, x ∈ M & S x ∈ M.
Proof.
  split; [tc_solve|].
  destruct gaps eqn : E.
  + exists 0; apply elem_of_gaps; now rewrite E.
  + assert (I : forall x, x > list_max gaps -> x ∈ M). {
      intros x Hx.
      apply elem_of_gaps. now apply list_max_notin.
    }
    exists conductor; apply I;
      unfold conductor; rewrite E in *; lia.
Qed.

Theorem numerical_semigroup_equiv2 `{submonoid M} :
  (forall x, Decision (x ∈ M)) ->
  (exists2 x, x ∈ M & S x ∈ M) ->
  Logic.inhabited (numerical_semigroup M).
Proof.
  intros D [a Aa AS]. constructor.
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
  set (l := merge_sort le (remove_dups ((filter (.∉ M) (seq 0 m))))).
  apply Build_numerical_semigroup with (gaps := l).
  - assumption.
  - apply Sorted_le_lt. split.
    + apply Sorted_merge_sort. intros ?. lia.
    + unfold l. rewrite merge_sort_Permutation.
      apply NoDup_remove_dups.
  - intros x. subst l. rewrite merge_sort_Permutation.
    rewrite elem_of_remove_dups.
    rewrite elem_of_list_filter.
    split; intros Hx; [intuition|].
    destruct (D x); try assumption.
    exfalso. apply Hx. split; try assumption.
    destruct (le_gt_cases m x).
    + exfalso. auto.
    + apply elem_of_seq. lia.
Qed.


(*****************)
(** * Generators *)
(*****************)

Section generators.
  Context (A : propset nat).

  Inductive generates : nat -> Prop :=
    generates_intro r x l
      (IA : (forall i, i < r -> x i ∈ A)) :
      generates (sum_list_with (fun i => l i * x i) (seq 0 r)).

  Theorem generates_eq a r x l :
    (forall i, i < r -> x i ∈ A) ->
    a = sum_list_with (fun i => l i * x i) (seq 0 r) ->
    generates a.
  Proof. now intros ? ->. Qed.

End generators.

Theorem generates_in `{numerical_semigroup M} A a :
  A ⊆ M -> generates A a -> a ∈ M.
Proof.
  intros I G. inversion G. subst.
  clear G. induction r; [apply ns_zero|].
  rewrite seq_S. rewrite sum_list_with_app.
  apply ns_closed.
  - apply IHr. intros. apply IA. lia.
  - simpl. rewrite add_0_r.
    apply ns_mul_closed. apply I. apply IA. lia.
Qed.

(** Generator of a numerical semigroup *)

Definition generator `{numerical_semigroup M} A :=
  A ⊆ M /\ forall a, a ∈ M -> generates A a.
