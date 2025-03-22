From Coq Require Import Euclid Lia.
Require Export nat.


(* submonoid of nat (with addition) *)
Class nat_submonoid (A : nat -> Prop) : Prop := {
  ns_zero : A 0;
  ns_closed : forall a b, A a -> A b -> A (a + b)
}.

Theorem sub_mul_closed A `{nat_submonoid A} :
  forall n m, A m -> A (n * m).
Proof.
  intros. induction n.
  - rewrite mul_0_l. apply ns_zero.
  - apply ns_closed; assumption.
Qed.

(* numerical semigroup definition *)
Class numerical_semigroup (A : nat -> Prop) : Prop := {
  ns_submonoid :: nat_submonoid A;
  ns_cofinite : Finite (Complement A)
}.

Theorem numerical_semigroup_alt A `{nat_submonoid A} :
  numerical_semigroup A <-> exists x y, A x /\ A y /\ x - y = 1.
Proof.
  split; intros I.
  - assert (exists a, A a /\ A (S a)) as [a [Aa As]]. {
      destruct (cofinite_definitive A) as [m Hm];
	try apply I.
      exists m. split; apply Hm; lia.
    }
    exists (S a), a. repeat (split; try assumption).
    clear Aa As. induction a; auto.
  - assert (exists a, A a /\ A (a + 1)) as [a [Aa Ha]]. {
      destruct I as [x [y [Ax [Ay Hxy]]]].
      exists y. split; try assumption.
      replace (y + 1) with x; try lia. assumption.
    }
    assert (Hn : forall n, n >= (a - 1) * (a + 1) -> A n). {
      intros n Hn. destruct a.
      - replace n with (n * 1); try lia.
	apply sub_mul_closed; assumption.
      - assert (diveucl n (S a)) as [q r g e].
	  { apply eucl_dev. lia. }
	assert (N : n = (q - r) * (S a) + r * ((S a) + 1)). {
	  assert (q >= r). {
	    apply le_trans with a; try lia.
	    assert (a * (S a) <= q * (S a)); try lia.
	    rewrite mul_le_mono_pos_r; [eassumption | lia].
	  }
	  rewrite mul_sub_distr_r, mul_add_distr_l.
	  rewrite add_assoc, sub_add; try lia.
	  apply mul_le_mono_r. assumption.
	}
	rewrite N.
	apply ns_closed; apply sub_mul_closed; assumption.
    }
    set (m := (a - 1) * (a + 1)).
    assert (In : Included (Complement A) (fun x => x < m)). {
      unfold Included, In, Complement. intros.
      destruct (le_gt_cases m x); try assumption.
      exfalso. auto with sets.
    }
    constructor; try assumption.
    eapply Finite_downward_closed; try eassumption.
    clear In. induction m.
    + replace (fun x => x < 0) with (Empty_set nat);
	try constructor.
	ex_ensembles x Hx; [contradiction | lia].
    + replace (fun x => x < S m) with (Add (fun x => x < m) m).
      * constructor; try assumption. unfold In. lia.
      * ex_ensembles x Hx.
	-- destruct Hx as [x Hx | x Hx].
	   ++ unfold In in *. lia.
	   ++ inversion Hx. lia.
	-- destruct (eq_dec x m).
	   ++ subst. apply Union_intror. constructor.
	   ++ constructor. unfold In. lia.
Qed.

Example even_not_numerical_semigroup :
  ~ numerical_semigroup (fun x => exists y, x = 2 * y).
Proof.
  intros C.
  destruct (numerical_semigroup_alt (fun x => exists y, x = 2 * y)) as [H _].
  destruct H as [x [y [[a Ha] [[b H2] H3]]]];
    try assumption.
  subst. lia.
Qed.


Section numerical_semigroup.

  Context A `{numerical_semigroup A}.

  Definition gaps := Complement A.

  Definition genus g := cardinal gaps g.

  Definition multiplicity m := min (Subtract A 0) m.

  Inductive generates_el (B : nat -> Prop) : nat -> Prop :=
    generates_el_intro r x l :
      (forall i, i < r -> B (x i)) ->
      generates_el B (sum (fun i => l i * x i) (seq 0 r)).

  #[global] Arguments generates_el_intro {B}.

  Theorem generates_el_eq {B a} r x l :
    (forall i, i < r -> B (x i)) ->
    a = sum (fun i => l i * x i) (seq 0 r) ->
    generates_el B a.
  Proof.
    intros H1 H2. rewrite H2. constructor. assumption.
  Qed.

  Definition generator B := Included B A /\
    forall a, A a -> generates_el B a.

End numerical_semigroup.
 
