From Coq Require Export List Permutation.
From Coq Require Import Arith Lia ZArith.
Require Export ensembles.
Export ListNotations Nat.


(** * Ensembles *)

(** A cofinite [nat] ensemble contains all numbers greater than some fixed
    number *)

Theorem cofinite_definitive A : Finite (Complement A) ->
  exists m, forall n, n >= m -> A n.
Proof.
  intros F. remember (Complement A) as C eqn : EC.
  generalize dependent A. induction F; intros.
  - exists 0. intros n Hn.
    rewrite <- (Complement_Complement _ A).
    rewrite <- EC. intros C. contradiction.
  - assert (EA : A = Complement (Add A0 x)). {
      clear IHF.
      unfold Add. rewrite de_morgan_cu. rewrite <- EC.
      ex_ensembles a Ha.
      - constructor; try (constructor; assumption).
	unfold Complement, In. intros C. inversion C.
	subst. contradiction.
      - unfold Complement, In in *. inversion Ha. subst.
	inversion H0; subst; try assumption.
	inversion H2. subst. unfold In in *. contradiction.
    }
    apply IHF in EA. destruct EA as [m Hm].
    exists (x + m + 1). intros n Hn.
    assert (n >= m); try lia. apply Hm in H0.
    inversion H0; try assumption.
    subst. destruct H1. lia.
Qed.

(** The cardinality of the set of natural numbers less than [n] is [n]. *)

Theorem cardinal_lt_n n : cardinal (fun x => x < n) n.
Proof.
  induction n as [ | n IH].
  - replace (fun x => x < 0) with (Empty_set nat);
      try constructor.
    ex_ensembles x Hx; inversion Hx.
  - replace (fun x => x < S n)
      with (Add (fun x => x < n) n).
    + constructor; try assumption. unfold In. lia.
    + ex_ensembles x Hx.
      * destruct Hx; unfold In in *; try lia.
	destruct H. lia.
      * destruct (eq_dec x n).
	-- subst. apply Union_intror. constructor.
	-- constructor. unfold In. lia.
Qed.


(** ** Minimum *)

(** Minimum of an ensemble of nat. *)

Definition minE (A : Ensemble nat) n :=
  A n /\ forall m, A m -> n <= m.

(** The minimum is unique *)

Theorem minE_unique (A : Ensemble nat) n m :
  minE A n -> minE A m -> n = m.
Proof. unfold minE. intuition auto using le_antisymm. Qed.

(** Every nonempty subset of nat has a minimum. *)

Theorem well_ordering_principle A : Inhabited A ->
  exists n, minE A n.
Proof.
  intros.
  assert
    (E := dec_inh_nat_subset_has_unique_least_element A).
  unfold has_unique_least_element in E.
  unfold minE. destruct H. destruct E as [a Ha];
    try eauto using classic.
    destruct Ha. eauto.
Qed.


(** * Congruence modulo *)

(** Congruence modulo [n]. *)

Definition congr_mod n x y := x mod n = y mod n.

(** The congruenece is symmetric. *)

Theorem congr_mod_symm n x y :
  congr_mod n x y -> congr_mod n y x.
Proof. unfold congr_mod. auto. Qed.

(** If x is congruent to y than n divides y - x. *)

Theorem congr_mod_divide n x y :
  congr_mod n x y -> (n | y - x).
Proof.
  intros C. destruct (le_ge_cases y x).
  - exists 0. lia.
  - apply Lcm0.mod_divide.
    apply Nat2Z.inj. rewrite Nat2Z.inj_mod. simpl.
    rewrite Nat2Z.inj_sub; try assumption.
    rewrite Zminus_mod. unfold congr_mod in C.
    apply f_equal with (f := Z.of_nat) in C.
    repeat rewrite Nat2Z.inj_mod in C.
    rewrite C. rewrite Z.sub_diag. reflexivity.
Qed.

Create HintDb congr_mod.

Hint Resolve congr_mod_symm : congr_mod.


(** * Lists *)


(** ** Sum *)

(** Sum of a function [f] over a list of indices [l]. *)

Definition sum {T} (f : T -> nat) l :=
  fold_right (fun x y => f x + y) 0 l.

Theorem fold_right_sum {T} (f : T -> nat) l a :
  fold_right (fun x y => f x + y) a l = sum f l + a.
Proof. induction l; simpl; lia. Qed.

Theorem sum_app {T} (f : T -> nat) l1 l2 :
  sum f (l1 ++ l2) = sum f l1 + sum f l2.
Proof.
  unfold sum. rewrite fold_right_app.
  induction l2; simpl; try lia.
  apply fold_right_sum.
Qed.

Theorem sum_Permutation {T} f (l1 l2 : list T) :
  Permutation l1 l2 -> sum f l1 = sum f l2.
Proof.
  intros P.
  induction P using Permutation_ind_bis; simpl.
  - reflexivity.
  - rewrite IHP. reflexivity.
  - rewrite IHP. lia.
  - rewrite IHP1. assumption.
Qed.

Theorem sum_flat_map {T} (f : T -> nat) g (l : list T) :
  sum f (flat_map g l) = sum (fun x => sum f (g x)) l.
Proof.
  induction l; try reflexivity.
  simpl. rewrite sum_app. auto.
Qed.
