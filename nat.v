From Coq Require Export List Permutation.
From Coq Require Import Arith Lia ZArith.
Require Export ensembles.
Export ListNotations Nat.


(*************************)
(** * Modular congruence *)
(*************************)

Section modulo.
  Variable n : nat.

  Definition congr_mod x y := x mod n = y mod n.

  Theorem congr_mod_symm x y :
    congr_mod x y -> congr_mod y x.
  Proof. unfold congr_mod. auto. Qed.

  Theorem congr_mod_divide x y :
    congr_mod x y -> (n | y - x).
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

End modulo.

Create HintDb congr_mod.

Hint Resolve congr_mod_symm : congr_mod.


(****************)
(** * Ensembles *)
(****************)

(** A cofinite [nat] ensemble contains all numbers
    greater than some fixed number *)

Theorem cofinite_definitive A : Finite (Complement A) ->
  exists m, forall n, n >= m -> A n.
Proof.
  intros F. remember (Complement A) as C eqn : EC.
  generalize dependent A.
  induction F.
  - intros. exists 0. intros n _.
    rewrite <- (Complement_Complement _ A).
    now rewrite <- EC.
  - intros B EC.
    assert (EA : A = Complement (Add B x)). {
      clear IHF.
      unfold Add. rewrite de_morgan_cu. rewrite <- EC.
      ex_ensembles a Ha.
      - constructor; try (constructor; assumption).
	unfold Complement, In. intros C. inversion C.
	subst. contradiction.
      - unfold Complement, In in *.
	inversion Ha as [y Aa]. subst.
	inversion Aa as [|y Sx]; subst; try assumption.
	inversion Sx. subst. unfold In in *. contradiction.
    }
    destruct (IHF _ EA) as [m Hm].
    exists (x + m + 1). intros n Hn.
    assert (L : n >= m); try lia. apply Hm in L.
    inversion L as [|y Sx]; try assumption.
    destruct Sx. lia.
Qed.

Theorem definitive_cofinite A :
  (exists m, forall n, n >= m -> A n) ->
  Finite (Complement A).
Proof.
  intros [m Hm].
  assert (In : Included (Complement A) (gt m)). {
    unfold Included, Complement. simpl. intros x Hx.
    destruct (le_gt_cases m x); try assumption.
    exfalso. auto.
  }
  eapply Finite_downward_closed; try eassumption.
  clear In Hm. induction m.
  - replace (gt 0) with (Empty_set nat); try constructor.
    now ex_ensembles x Hx.
  - replace (gt (S m)) with (Add (gt m) m).
    + constructor; try assumption. simpl. lia.
    + ex_ensembles x Hx.
      * destruct Hx as [ | x Hx]; simpl in *; try lia.
	destruct Hx. lia.
      * destruct (eq_dec x m).
	-- subst. apply Union_intror. constructor.
	-- constructor. simpl. lia.
  Qed.

(** The cardinality of the set of natural
    numbers less than [n] is [n] *)

Theorem cardinal_gt_n n : cardinal (gt n) n.
Proof.
  induction n as [ | n IH].
  - replace (gt 0) with (Empty_set nat);
      try constructor.
    ex_ensembles x Hx; inversion Hx.
  - replace (gt (S n)) with (Add (gt n) n).
    + constructor; try assumption. unfold In. lia.
    + ex_ensembles x Hx.
      * destruct Hx; unfold In in *; try lia.
	destruct H. lia.
      * destruct (eq_dec x n).
	-- subst. now apply Union_intror.
	-- constructor. unfold In. lia.
Qed.


(***************)
(** ** Minimum *)
(***************)

Section minimum.
  Variable A : Ensemble nat.

  (** Minimum of an ensemble of nat *)

  Definition minE m := A m /\ forall n, A n -> m <= n.

  (** The minimum is unique *)

  Theorem minE_unique n m :
    minE n -> minE m -> n = m.
  Proof. unfold minE. intuition auto using le_antisymm. Qed.

  (** Every nonempty subset of nat has a minimum *)

  Theorem well_ordering_principle : Inhabited A ->
    exists m, minE m.
  Proof.
    intros I.
    assert (E := dec_inh_nat_subset_has_unique_least_element A).
    unfold has_unique_least_element in E.
    unfold minE. destruct I. destruct E as [a Ha];
      try eauto using classic.
    destruct Ha. eauto.
  Qed.

End minimum.


(**********)
(** * Sum *)
(**********)

Section sum.
  Context {T} (f : T -> nat).

  (** Sum of a function [f] over a list of indices [l] *)

  Definition sum l := fold_right (fun x y => f x + y) 0 l.

  Theorem fold_right_sum l a :
    fold_right (fun x y => f x + y) a l = sum l + a.
  Proof. induction l; simpl; lia. Qed.

  Theorem sum_app l1 l2 : sum (l1 ++ l2) = sum l1 + sum l2.
  Proof.
    unfold sum. rewrite fold_right_app.
    induction l2; simpl; try lia.
    apply fold_right_sum.
  Qed.

  Theorem sum_Permutation (l1 l2 : list T) :
    Permutation l1 l2 -> sum l1 = sum l2.
  Proof.
    intros P.
    induction P using Permutation_ind_bis;
      simpl; try rewrite IHP; try reflexivity.
    - lia.
    - rewrite IHP1. assumption.
  Qed.

End sum.

Theorem sum_flat_map {T} (f : T -> nat) g (l : list T) :
  sum f (flat_map g l) = sum (fun x => sum f (g x)) l.
Proof.
  induction l; try reflexivity.
  simpl. rewrite sum_app. auto.
Qed.
