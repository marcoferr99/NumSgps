From Coq Require Export Arith.
From stdpp Require Export propset.
From Coq Require Import Lia ZArith.
Export Nat.

Generalizable No Variables.
Generalizable Variable C.


(*************************)
(** * Modular congruence *)
(*************************)

Theorem mod_divide n x y :
  x mod n = y mod n -> (n | y - x).
Proof.
  intros C.
  destruct (le_ge_cases y x); [exists 0; lia |].
  apply Lcm0.mod_divide.
  apply Nat2Z.inj. rewrite Nat2Z.inj_mod. simpl.
  rewrite Nat2Z.inj_sub; try assumption.
  rewrite Zminus_mod.
  apply f_equal with (f := Z.of_nat) in C.
  repeat rewrite Nat2Z.inj_mod in C.
  rewrite C. now rewrite Z.sub_diag.
Qed.

Theorem mod_mod_le n x y :
  n <> 0 -> x > y -> y - y mod n + x mod n <= x.
Proof.
  intros n0 L.
  rewrite (Div0.div_mod x n) at 2.
  rewrite (Div0.div_mod y n) at 1.
  generalize (Div0.div_le_mono y x n). intros Lm.
  apply add_le_mono; [|lia].
  rewrite <- add_sub_assoc; [|lia].
  rewrite sub_diag.
  remember (y / n) as b eqn : E. clear E.
  remember (x / n) as a eqn : E. clear E.
  induction n; lia.
Qed.

Theorem mod_divide_2 n x y :
  x > y -> x mod n = y mod n -> exists q, x = q * n + y.
Proof.
  intros L M. symmetry in M.
  apply mod_divide in M. destruct M as [q M].
  exists q. lia.
Qed.

(** Compute the smallest number that is greater than or
    equal to [x] and is congruent to [a] modulo [n]. *)

Definition mod_ge n a x :=
  let r := x - x mod n + a mod n in
  if x <=? r then r else r + n.

Theorem mod_ge_mod n a x : (mod_ge n a x) mod n = a mod n.
Proof.
  unfold mod_ge.
  assert (E : (x - x mod n) mod n = 0). {
    generalize (Div0.div_mod x n). intros D.
    replace (x - x mod n) with (n * (x / n)); try lia.
    rewrite mul_comm. apply Div0.mod_mul.
  }
  destruct (leb_spec x (x - x mod n + a mod n)).
  - rewrite <- Div0.add_mod_idemp_l. rewrite E.
    simpl. apply Div0.mod_mod.
  - rewrite <- add_assoc. rewrite <- Div0.add_mod_idemp_l.
    rewrite E. simpl.
    rewrite <- (Div0.add_mod_idemp_r _ n).
    rewrite Div0.mod_same. rewrite add_0_r.
    apply Div0.mod_mod.
Qed.

Theorem mod_ge_ge n a x : n <> 0 -> x <= mod_ge n a x.
Proof.
  intros n0. unfold mod_ge.
  destruct (leb_spec x (x - x mod n + a mod n)); try lia.
  apply (mod_upper_bound a) in n0 as U.
  apply (mod_upper_bound x) in n0. lia.
Qed.

Theorem mod_ge_lt n a x : n <> 0 -> mod_ge n a x < x + n.
Proof.
  intros n0. unfold mod_ge.
  destruct (leb_spec x (x - x mod n + a mod n)); try lia.
  apply (mod_upper_bound a) in n0 as U.
  apply (mod_upper_bound x) in n0. lia.
Qed.

Theorem mod_mod_ge n a x :
  a mod n = x mod n -> mod_ge n a x = x.
Proof.
  intros I. unfold mod_ge.
  destruct (leb_spec x (x - x mod n + a mod n)); [|lia].
  generalize (Div0.mod_le x n). intros D. lia.
Qed.


(**************)
(** * Minimum *)
(**************)

Section minimum.
  Context `{ElemOf nat C} (A : C).

  Definition set_min m :=
    m ∈ A /\ forall n, n ∈ A -> m <= n.

  Definition set_max m :=
    m ∈ A /\ forall n, n ∈ A -> n <= m.

  (** The minimum is unique *)

  Theorem set_min_unique n m :
    set_min n -> set_min m -> n = m.
  Proof.
    unfold set_min. intuition auto using le_antisymm.
  Qed.

End minimum.

(** Every decidable nonempty subset of nat has a minimum *)

Theorem well_ordering_principle `{ElemOf nat C} (A : C) :
  (forall x, x ∈ A \/ x ∉ A) ->
  (exists n, n ∈ A) -> exists m, set_min A m.
Proof.
  intros D I.
  assert (E := dec_inh_nat_subset_has_unique_least_element (fun x => x ∈ A)).
  unfold has_unique_least_element in E.
  unfold set_min.
  destruct E as [a Ha]; try assumption.
  destruct Ha. exists a. auto.
Qed.
