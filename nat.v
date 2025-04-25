From Coq Require Export Arith.
From stdpp Require Export sets.
Export Nat.
From Coq Require Import Lia ZArith.


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

Definition set_min {C} `{ElemOf nat C} (A : C) m :=
  m ∈ A /\ forall n, n ∈ A -> m <= n.
