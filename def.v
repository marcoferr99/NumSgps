From Coq Require Export Sorting.
From stdpp Require Export propset sorting.
Require Export nat.
From Coq Require Import Euclid.

Generalizable No Variables.


(*************************************)
(** * Numerical semigroup definition *)
(*************************************)

Class submonoid {C} `{ElemOf nat C} (A : C) : Prop := {
  ns_zero : 0 ∈ A;
  ns_closed : forall a b, a ∈ A -> b ∈ A -> a + b ∈ A
}.

Theorem ns_mul_closed {C} A `{submonoid C A} :
  forall n m, m ∈ A -> n * m ∈ A.
Proof.
  intros. induction n.
  - rewrite mul_0_l. apply ns_zero.
  - now apply ns_closed.
Qed.

Class numerical_semigroup {C} (A : C) `{ElemOf nat C} : Type := {
  ns_submonoid :: submonoid A;
  gaps : list nat;
  sorted_gaps : Sorted lt gaps;
  elem_of_gaps x : x ∈ A <-> x ∉ gaps
}.

Theorem ns_decision {C} A `{numerical_semigroup C A} x :
  Decision (x ∈ A).
Proof.
  destruct (elem_of_list_dec x gaps).
  - right. intros N. apply elem_of_gaps in N. auto.
  - left. apply elem_of_gaps. assumption.
Qed.

Theorem elem_of_gaps' {C} A `{numerical_semigroup C A} x :
  x ∈ gaps <-> x ∉ A.
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
  Context {C} A `{numerical_semigroup C A}.

  Definition genus := length gaps.

  Definition multiplicity := multiplicity_aux 1 gaps.

  Theorem multiplicity_min : multiplicity ∈ A /\
    forall x, x ∈ A -> x <> 0 -> multiplicity <= x.
  Proof.
    split.
    - apply elem_of_gaps.
      apply (multiplicity_aux_notin 1);
	[apply sorted_gaps|].
      apply Forall_forall. intros x Hx.
      assert (x <> 0); [|lia].
      intros X. subst.
      apply elem_of_gaps' in Hx. apply Hx. apply ns_zero.
    - intros. apply multiplicity_aux_notin_le.
      + apply sorted_gaps.
      + apply elem_of_gaps. assumption.
      + lia.
  Qed.

  Definition conductor :=
    match gaps with
    | [] => 0
    | h :: t => S (list_max gaps)
    end.

End numerical_semigroup.

(** Equivalent condition for a numerical semigroup *)

Theorem numerical_semigroup_equiv {C} `{ElemOf nat C} (A : C) :
  Logic.inhabited (numerical_semigroup A) <->
  submonoid A /\ exists2 x, x ∈ A & S x ∈ A.
Proof.
  split.
  - intros [NS]. split; [apply NS|].
    remember gaps as l eqn : E. destruct l.
    + exists 0; [apply ns_zero|].
      eapply elem_of_gaps'. rewrite <- E. easy.
    + assert (I : forall x, x > list_max gaps -> x ∈ A). {
	intros x Hx.
	apply list_max_lt in Hx; [|now rewrite <- E].
	eapply elem_of_gaps'. intros N.
	eapply Forall_forall in Hx; [|eassumption].
	lia.
      }
      exists (conductor A); apply I;
	unfold conductor;  rewrite <- E in *; lia.
  - intros [NS [a Aa AS]]. constructor.
    constructor; try assumption.
    apply finite_definitive.
    exists ((a - 1) * (a + 1)).
    intros n Hn. apply not_elem_of_difference. right.
    destruct a.
    + replace n with (n * 1); try lia.
      now eapply ns_mul_closed.
    + assert (diveucl n (S a)) as [q r g e].
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
      apply ns_closed; now eapply ns_mul_closed.
Qed.

(** The set of even natural numbers is not a numerical semigroup *)

(*Example even_not_numerical_semigroup {C} `{TopSet nat C} :
  let E x := exists y, x = 2 * y in
  ~ numerical_semigroup E.
Proof.
  intros E C.
  destruct (numerical_semigroup_equiv E) as [NE _].
  destruct NE as (_ & x & [a ->] & [b H]); try assumption.
  lia.
Qed.*)


(*****************)
(** * Generators *)
(*****************)

Section test.
  Context `{SemiSet nat C}.
Inductive generates (A : C) : nat -> Prop :=
  generates_intro r x l
    (IB : (forall i, i < r -> x i ∈ A)) :
    generates A (sum (fun i => l i * x i) (seq 0 r)).

Theorem generates_eq  (B : C) a r x l :
  (forall i, i < r -> x i ∈ B) ->
  a = sum (fun i => l i * x i) (seq 0 r) ->
  generates B a.
Proof. intros ? ->. easy. Qed.
End test.
Check generates_eq.

Theorem generates_in {C} A `{numerical_semigroup C A} B a :
  B ⊆ A -> generates B a -> a ∈ A.
Proof.
  intros I G. inversion G. subst.
  clear G. induction r; [apply ns_zero|].
  rewrite seq_S. rewrite sum_app. apply ns_closed.
  - apply IHr. intros. apply IB. lia.
  - simpl. rewrite add_0_r.
    eapply ns_mul_closed; [tc_solve|].
    apply I. apply IB. lia.
Qed.

(** Generator of a numerical semigroup *)

Definition generator {C} A `{numerical_semigroup C A} B :=
  B ⊆ A /\ forall a, a ∈ A -> generates B a.


(***********)
(** * Gaps *)
(***********)

Definition l_numerical_semigroup (l : list nat) :=
  NoDup l.

Definition gaps_list {C} `{TopSet nat C} (l : list nat) :=
  numerical_semigroup (top ∖ @list_to_set _ C _ _ _ l).

Definition list_ns l (_ : Sorted lt l) (_ : submonoid {[n | n ∉ l]}) : propset nat :=
  {[n | n ∉ l]}.

Instance test l (S : Sorted lt l) (M : submonoid {[n | n ∉ l]}) : numerical_semigroup (list_ns l S M).
Proof.
  econstructor; try eassumption.
  - intros x. destruct (elem_of_list_dec x l).
    + right. intros N. destruct N. assumption.
    + left. assumption.
  - intros x. split; intros Hx.
    + intros N. destruct N. assumption.
    + destruct (elem_of_list_dec x l); try assumption.
      exfalso. apply Hx. assumption.
Qed.

