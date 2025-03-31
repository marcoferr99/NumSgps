From Coq Require Export List.
From Coq Require Import Arith Lia Permutation ZArith.
Require Export ensembles.
Export ListNotations Nat.


(* minimum of a subset of nat *)
Definition min (A : Ensemble nat) n : Prop :=
  A n /\ forall m, A m -> n <= m.

Theorem min_unique (A : Ensemble nat) n m :
  min A n -> min A m -> n = m.
Proof. unfold min. intuition auto using le_antisymm. Qed.

(* every nonempty subset of nat has a minimum *)
Theorem well_ordering_principle : forall A : Ensemble nat,
  Inhabited A -> exists n, min A n.
Proof.
  intros.
  assert
    (E := dec_inh_nat_subset_has_unique_least_element A).
  unfold has_unique_least_element in E.
  unfold min. destruct H. destruct E; try eauto.
  - auto using classic.
  - destruct H0. eauto.
Qed.

(* a cofinite nat ensemble contains all numbers greater than some fixed number *)
Theorem cofinite_definitive (A : Ensemble nat) :
  Finite (Complement A) -> exists m, forall n, n >= m -> A n.
Proof.
  intros. remember (Complement A) as C eqn : EC.
  generalize dependent A. induction H; intros.
  - exists 0. intros. rewrite <- (Complement_Complement _ A).
    rewrite <- EC. intros C. contradiction.
  - assert (A = Complement (Add A0 x)). {
      clear IHFinite.
      unfold Add. rewrite de_morgan_cu. rewrite <- EC.
      apply Extensionality_Ensembles.
      split; intros a Ha; unfold In.
      - constructor.
	+ constructor. assumption.
	+ unfold Complement, In. intros C. inversion C.
	  subst. contradiction.
      - unfold Complement, In in *. inversion Ha. subst.
	inversion H1; subst; try assumption.
	inversion H3. subst. unfold In in *. contradiction.
    }
    apply IHFinite in H1. destruct H1 as [m1 Hm1].
    exists (x + m1 + 1). intros.
    assert (n >= m1); try lia. apply Hm1 in H2.
    inversion H2; try assumption.
    subst. destruct H3. lia.
Qed.

(* congruence modulo n *)
Definition congr_mod n x y := x mod n = y mod n.

(* the congruenece is symmetric *)
Theorem congr_symm n x y : congr_mod n x y -> congr_mod n y x.
Proof. unfold congr_mod. auto. Qed.

(* if x is congruent to y than n divides y - x *)
Theorem congr_mod_divide n x y : congr_mod n x y -> (n | y - x).
Proof.
  intros. destruct (le_ge_cases y x).
  - exists 0. lia.
  - apply Lcm0.mod_divide.
    apply Nat2Z.inj. rewrite Nat2Z.inj_mod. simpl.
    rewrite Nat2Z.inj_sub; try assumption.
    rewrite Zminus_mod. unfold congr_mod in H.
    apply f_equal with (f := Z.of_nat) in H.
    repeat rewrite Nat2Z.inj_mod in H.
    rewrite H. rewrite Z.sub_diag. reflexivity.
Qed.

Create HintDb congr_mod.

Hint Resolve congr_symm : congr_mod.


Theorem cardinal_lt_n n : cardinal (fun x => x < n) n.
Proof.
  induction n as [ | n IH].
  - replace (fun x => x < 0) with (Empty_set nat).
    + constructor.
    + apply Extensionality_Ensembles.
      split; unfold Included, In.
      * intros. destruct H.
      * lia.
  - replace (fun x => x < S n) with (Add (fun x => x < n) n).
    + constructor; try assumption.
      * unfold In. lia.
    + apply Extensionality_Ensembles.
      split; unfold Included, In; intros x H.
      * destruct H; unfold In in H; try lia.
	destruct H. lia.
      * destruct (classic (x = n)).
	-- subst. apply Union_intror. constructor.
	-- constructor. unfold In. lia.
Qed.


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
  intros P. induction P using Permutation_ind_bis.
  - reflexivity.
  - simpl. rewrite IHP. reflexivity.
  - simpl. rewrite IHP. lia.
  - rewrite IHP1. assumption.
Qed.

Theorem sum_flat_map {T} (f : T -> nat) g (l : list T) :
  sum f (flat_map g l) = sum (fun x => sum f (g x)) l.
Proof.
  induction l; try reflexivity.
  simpl. rewrite sum_app. auto.
Qed.
