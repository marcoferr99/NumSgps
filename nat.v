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


(***************)
(** ** Minimum *)
(***************)

Section minimum.

  Context `{ElemOf nat C} (A : C).

  Definition set_min m :=
    m ∈ A /\ forall n, n ∈ A -> m <= n.

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
