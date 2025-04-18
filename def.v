From Coq Require Import Arith Euclid Lia.
Require Export nat.


(*************************************)
(** * Numerical semigroup definition *)
(*************************************)

Class nat_submonoid (A : nat -> Prop) : Prop := {
  ns_zero : A 0;
  ns_closed : forall a b, A a -> A b -> A (a + b)
}.

Theorem sub_mul_closed A `{nat_submonoid A} :
  forall n m, A m -> A (n * m).
Proof.
  intros. induction n.
  - rewrite mul_0_l. apply ns_zero.
  - now apply ns_closed.
Qed.

Class numerical_semigroup (A : nat -> Prop) : Prop := {
  ns_submonoid :: nat_submonoid A;
  ns_cofinite : Finite (Complement A)
}.

(** Some definitions over numerical semigroups *)

Section numerical_semigroup.
  Context A `{numerical_semigroup A}.

  Definition gaps := Complement A.

  Definition genus g := cardinal gaps g.

  Definition multiplicity m := minE (Subtract A 0) m.

End numerical_semigroup.


(** Equivalent condition for a numerical semigroup *)

Theorem numerical_semigroup_equiv A :
  numerical_semigroup A <-> nat_submonoid A /\
  exists x, A x /\ A (S x).
Proof.
  split.
  - intros I. split; try apply I.
    destruct (cofinite_definitive A) as [m Hm];
      try apply I.
    exists m. split; apply Hm; auto.
  - intros [NS I].
    constructor; try assumption.
    destruct I as [a [Aa Ha]].
    apply definitive_cofinite. exists ((a - 1) * (a + 1)).
    intros n Hn. destruct a.
    + replace n with (n * 1); try lia.
      now apply sub_mul_closed.
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
      apply ns_closed; now apply sub_mul_closed.
Qed.

(** The set of even natural numbers is not a numerical semigroup *)

Example even_not_numerical_semigroup :
  let E x := exists y, x = 2 * y in
  ~ numerical_semigroup E.
Proof.
  intros E C.
  destruct (numerical_semigroup_equiv E) as [NE _].
  destruct NE as (_ & x & [a ->] & [b H]); try assumption.
  lia.
Qed.


(*****************)
(** * Generators *)
(*****************)

(** Generating an element from an ensemble [B] *)

Inductive generates (B : nat -> Prop) : nat -> Prop :=
  generates_intro r x l
    (IB : (forall i, i < r -> B (x i))) :
    generates B (sum (fun i => l i * x i) (seq 0 r)).

Arguments generates_intro {B}.

Theorem generates_eq B a r x l :
  (forall i, i < r -> B (x i)) ->
  a = sum (fun i => l i * x i) (seq 0 r) ->
  generates B a.
Proof. intros H ->. easy. Qed.

Theorem generates_in A `{numerical_semigroup A} B a :
  Included B A -> generates B a -> A a.
Proof.
  intros I G. inversion G. subst.
  clear G. induction r; [apply H|].
  rewrite seq_S. rewrite sum_app. apply ns_closed.
  - apply IHr. intros. apply IB. lia.
  - simpl. rewrite add_0_r.
    apply sub_mul_closed; [apply H|].
    apply I. apply IB. lia.
Qed.

(** Generator of a numerical semigroup *)

Definition generator A `{numerical_semigroup A} B :=
  Included B A /\ forall a, A a -> generates B a.
