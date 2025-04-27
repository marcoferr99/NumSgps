From Coq Require Export Arith.
From stdpp Require Export propset.
Export Nat.
From Coq Require Import Lia ZArith.

Generalizable No Variables.
Generalizable Variable C.


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


(***************)
(** ** Minimum *)
(***************)

Section minimum.
  Context `{SemiSet nat C} (A : C).

  Definition set_min m :=
    m ∈ A /\ forall n, n ∈ A -> m <= n.

  (** The minimum is unique *)

  Theorem set_min_unique n m :
    set_min n -> set_min m -> n = m.
  Proof.
    unfold set_min. intuition auto using le_antisymm.
  Qed.
End minimum.

(** Every nonempty subset of nat has a minimum *)

Theorem well_ordering_principle (A : propset nat) :
  (forall x, Decision (x ∈ A)) ->
  (exists n, n ∈ A) -> exists m, set_min A m.
Proof.
  intros D I. destruct A as [A].
  assert (E := dec_inh_nat_subset_has_unique_least_element A).
  unfold has_unique_least_element in E.
  unfold set_min.
  destruct E as [a Ha].
  - intros n. destruct (D n); intuition.
  - assumption.
  - destruct Ha. exists a. auto.
Qed.
