From Coq Require Export List Permutation.
From stdpp Require Export sets.
Export ListNotations Nat.
From Coq Require Import Arith Lia ZArith.


About elem_of_seq.
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


(***********)
(** * Sets *)
(***********)

Theorem finite_definitive {C} `{SemiSet nat C} (A : C) :
  set_finite A <-> exists m, forall n, m <= n -> ~ n ∈ A.
Proof.
  split.
  - intros [l Hl].
    destruct l as [ | h t].
    + exists 0. intros n Hn N. apply Hl in N. inversion N.
    + remember (h :: t) as l.
      exists (S (list_max l)).
      intros n Hn N.
      apply list_max_lt in Hn; [|subst; discriminate].
      apply Hl in N. rewrite elem_of_list_In in N.
      apply In_nth with (d := 0) in N as [x [Lx Hx]].
      eapply Forall_nth with (d := 0) in Hn;
	[|eassumption].
      lia.
  - intros [m Hm].
    exists (seq 0 m). intros n Hn.
    destruct (le_gt_cases m n).
    + exfalso. eapply Hm; eassumption.
    + rewrite elem_of_list_In. apply in_seq. lia.
Qed.


(*******************)
(** ** Cardinality *)
(*******************)

Definition set_card {C} `{SemiSet nat C} (A : C) n :=
  exists2 l, (forall x, x ∈ A <-> x ∈ l) &
  length (nodup eq_dec l) = n.


(***************)
(** ** Minimum *)
(***************)

Definition set_min {C} `{SemiSet nat C} (A : C) m :=
  m ∈ A /\ forall n, n ∈ A -> m <= n.


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


(**
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

End minimum.*)


(** The cardinality of the set of natural
    numbers less than [n] is [n] *)
(**
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


*)
