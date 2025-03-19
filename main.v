From Coq Require Import Euclid Lia List.
Require Export ensembles functions nat.
Import ListNotations.


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

End numerical_semigroup.
Check gaps.


Section numerical_semigroup.

  Context A `{numerical_semigroup A} (n : nat).

  (* apery set *)
  Definition apery x := A x /\ (n <= x -> ~ A (x - n)).

  (* the apery set of n does not contain two different numbers that are congruent
     modulo n *)
  Theorem apery_congr_unique : A n ->
    forall a b, apery a -> apery b ->
    congr_mod n a b -> a = b.
  Proof.
    intros An.
    assert (T : forall a b, apery a -> apery b -> a <= b -> congr_mod n a b -> a = b). {
      intros a b Aa Ab L C.
      destruct (le_ge_cases n b) as [Ln | Lb].
      - apply Ab in Ln.
	apply congr_mod_divide in C. destruct C as [k Hk].
	destruct k; try lia.
	exfalso. apply Ln.
	replace (b - n) with (k * n + a); try lia.
	apply ns_closed; try apply Aa.
	+ clear Hk Ln.
	  induction k; apply H; try assumption.
      - destruct (le_gt_cases n a); try lia.
        unfold congr_mod in C.
	rewrite mod_small in C; try assumption.
	rewrite mod_small in C; try assumption.
	unfold apery in Ab.
	destruct (le_gt_cases n b); try assumption.
	assert (b = n); try lia. subst.
	destruct Ab.
	exfalso. apply H3; try assumption.
	rewrite sub_diag. apply ns_zero.
    }
    intros. destruct (le_ge_cases a b); try auto.
    symmetry. auto with congr_mod.
  Qed.

  Definition apery_min i w :=
    min (fun x => A x /\ congr_mod n x i) w.

  Theorem apery_min_exists : n <> 0 ->
    forall i, exists w, apery_min i w.
  Proof.
    intros n0 i. apply well_ordering_principle.
    destruct (cofinite_definitive A) as [m Hm];
      try apply ns_cofinite.
    apply (Inhabited_intro (i + m * n)). split.
    + apply Hm. destruct n; lia.
    + unfold congr_mod. apply Div0.mod_add.
  Qed.

  Theorem apery_w_is_func : n <> 0 ->
    forall i : {x | x < n},
    exists ! w, apery_min (proj1_sig i) w.
  Proof.
    intros n0 i.
    destruct (apery_min_exists n0 (proj1_sig i)) as [w Hw].
    exists w. split; try assumption.
    eauto using min_unique.
  Qed.

  Definition apery_w (n0 : n <> 0) :=
    proj1_sig (rel_func _ (apery_w_is_func n0)).

  Definition apery_w_spec (n0 : n <> 0) :
    (forall i, apery_min (proj1_sig i) (apery_w n0 i)) /\ forall i w, apery_min (proj1_sig i) w -> w = apery_w n0 i :=
    proj2_sig (rel_func _ (apery_w_is_func n0)).

  Theorem apery_w_injective (n0 : n <> 0) :
    injective (apery_w n0).
  Proof.
    intros x y I.
    apply proj1_sig_injective.
    destruct (apery_w_spec n0) as [Hw _].
    destruct (Hw x) as [[_ Hx] _].
    destruct (Hw y) as [[_ Hy] _].
    unfold congr_mod in *. rewrite I in Hx.
    rewrite Hx in Hy. clear Hx I n0 Hw.
    destruct x, y. simpl in *.
    rewrite mod_small, mod_small in Hy; assumption.
  Qed.

  Theorem apery_w_congr (n0 : n <> 0) :
    forall x, congr_mod n (apery_w n0 x) (proj1_sig x).
  Proof. apply apery_w_spec. Qed.

  (* apery_alt has a representative for every modulo class *)
  Theorem apery_w_all_classes (n0 : n <> 0) :
    forall x, exists i, congr_mod n x (apery_w n0 i).
  Proof.
    intros x.
    exists (exist (x mod n) (mod_upper_bound _ _ n0)).
    unfold congr_mod. rewrite apery_w_congr. simpl.
    symmetry. apply Div0.mod_mod.
  Qed.

  (* apery and apery_alt are the same set *)
  Theorem apery_w_eq (n0 : n <> 0) : A n ->
    Im (Full_set _) (apery_w n0) = apery.
  Proof.
    intros An.
    assert (I : Included (Im (Full_set _) (apery_w n0)) apery). {
      unfold Included, In. intros w Hw. 
      destruct Hw as [i _ w Hw]. subst w.
      destruct (apery_w_spec n0) as [W _].
      specialize W with i.
      split; try apply W.
      intros L AD.
      assert (N : ~(apery_w n0 i <= apery_w n0 i - n)); try lia.
      apply N. apply W. split; try assumption.
      unfold congr_mod.
      rewrite <- Div0.mod_add with (b := 1).
      replace (apery_w n0 i - n + 1 * n) with (apery_w n0 i); try lia.
      apply W.
    }
    apply Extensionality_Ensembles. split; try assumption.
    unfold Included, In. intros w Hw.
    destruct (apery_w_all_classes n0 w) as [x Hx].
    apply Im_intro with (x := x); try constructor.
    apply apery_congr_unique; try assumption.
    apply I. econstructor; constructor.
  Qed.

  Theorem apery_cardinality : A n -> n <> 0 ->
    cardinal apery n.
  Proof.
    intros An n0.
    rewrite <- (apery_w_eq n0); try assumption.
    apply injective_cardinal.
    - apply apery_w_injective.
    - apply sig_cardinal. apply cardinal_lt_n.
  Qed.

  (* every element of A can be written as k * n + w, where w is an element
     of apery *)
  Theorem apery_generates : A n -> n <> 0 ->
    forall a, A a ->
    exists ! k w, apery w /\ a = k * n + w.
  Proof.
    intros An n0 a Aa.
    destruct (classic (apery a)) as [Ap | Ap].
    - exists 0. split.
      + exists a. split; try auto. intuition.
      + intros x [w [[W1 W2] W3]].
	destruct x; try reflexivity.
	exfalso. apply Ap; try lia.
	replace (a - n) with (x * n + w); try lia.
	apply ns_closed.
	* clear W1 W2 W3. induction x; try apply ns_zero.
	  apply ns_closed; assumption.
	* apply W1.
    - assert (exists k, a >= S k * n /\ ~ (apery (a - k * n)) /\ apery (a - S k * n)) as [k [K1 [K2 K3]]]. {
	assert (exists k, min (fun k => n <= a - S k * n -> ~ A (a - S k * n - n)) k) as [k [M1 M2]]. {
	    apply well_ordering_principle.
	    apply (Inhabited_intro a). unfold In.
	    induction n; lia.
	}
	exists k.
	assert (G : a >= S k * n). {
	  destruct k.
	  - apply not_and_or in Ap. intuition lia.
	  - specialize M2 with k. lia.
	}
	assert (Ak : A (a - S k * n)). {
	  destruct k.
	  - apply not_and_or in Ap.
	    replace (1 * n) with n in *; try lia.
	    destruct Ap; try contradiction.
	    apply NNPP. auto.
	  - specialize M2 with k. apply NNPP. intros C.
	    assert (N : ~ S k <= k); try lia.
	    apply N. apply M2. intros.
	    replace (a - S k * n - n) with (a - S (S k) * n); [assumption | lia].
	}
	split; try assumption.
	unfold apery. split; [ | intuition].
	intros [C1 C2].
	apply C2; try lia.
	replace (a - k * n - n) with (a - S k * n);
	  [assumption | lia].
      }
      exists (S k). split.
      + exists (a - S k * n). split; try lia.
	split; [assumption | lia].
      + intros l [z [[Z1 Z2] Z3]].
	assert (E : z = a - S k * n). {
	  apply apery_congr_unique; try assumption.
	  symmetry.
	  rewrite <- Div0.mod_add with (b := S k).
	  replace (a - S k * n + S k * n) with a; try lia.
	  subst a. rewrite add_comm. apply Div0.mod_add.
	}
	assert (E1 : a = z + S k * n); try lia.
	subst a.
	apply (mul_cancel_r _ _ n); try assumption. lia.
  Qed.

  Definition generator B := Included B A /\
    forall a, A a ->
    exists r x l, (forall y, y < r -> B (x y)) /\
    a = fold_right (fun u v => v + l u * x u) 0 (seq 0 r).
 
  Theorem apery_generator : A n -> n <> 0 ->
    generator (Add apery n).
  Proof.
    intros An n0. split.
    - intros x Hx. unfold In in *.
      destruct Hx as [x Hx | x Hx].
      + unfold apery, In in *. intuition.
      + destruct Hx. assumption.
    - intros a Aa.
      generalize (apery_generates An n0 a Aa).
      intros [k [[w [[Aw E] _]] _]].
      exists 2.
      exists (fun y => match y with
		       | 0 => n
		       | S y => w
		       end).
      exists (fun y => match y with
		       | 0 => k
		       | S y => 1
		       end).
      split.
      + intros. destruct y.
	* apply Union_intror. constructor.
	* constructor. assumption.
      + simpl. lia.
  Qed.

End numerical_semigroup.

Fixpoint ordered_list_add max l :=
  match l with
  | [] => [0]
  | h :: t => if h <? max then S h :: t else
      match ordered_list_add max t with
      | [] => []
      | h :: t => h :: h :: t
      end
  end.

Fixpoint ordered_list_nth max n :=
  match n with
  | 0 => []
  | S n => ordered_list_add max (ordered_list_nth max n)
  end.

Definition nth_sum l n :=
  fold_right (fun x y => y + nth x l 0) 0 (ordered_list_nth (length l - 1) n).

Fixpoint first_congr l m a i n :=
  match i with
  | 0 => 0
  | S i => let x := nth_sum l n in
      if x mod m =? a mod m then x else first_congr l m a i (S n)
  end.
Compute first_congr [4;7;10] 4 1 100 0.

Theorem t1 A `{numerical_semigroup A} l :
  generator A (fun x => List.In x l) ->
  forall n, A (nth_sum l n).
Proof.
  intros G n. unfold nth_sum.
  remember (ordered_list_nth (length l - 1) n) as ls.
  remember (length ls) as ln.
  clear Heqls. generalize dependent ls. induction ln.
  - intros. assert (ls = []).
    + apply length_zero_iff_nil. auto.
    + rewrite H0. simpl. apply ns_zero.
  - intros. destruct ls.
    + discriminate.
    + simpl. apply ns_closed.
      * apply IHln. auto.
      * destruct G as [G _]. unfold Included, In in G.
	apply G. apply nth_In.
Abort.

Compute nth_sum [4;7;10] 9.

Example apery_example1 A `{numerical_semigroup A} :
  generator A (fun x => List.In x [4;7;10]) ->
  apery A 4 = (fun x => List.In x [0;7;10;17]).
Proof.
  intros I.
  assert (n0 : 4 <> 0); try lia.
  assert (A4 : A 4). { apply I. intuition. }
  rewrite <- (apery_w_eq _ 4 n0); try assumption.
  ex_ensembles x Hx.
  - destruct Hx as [x _ y Hy]. subst.
    destruct x as [x p].
    assert (O : x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4); try lia.
    repeat destruct O as [O | O]; subst;
      [left | do 3 right; left | left | left | left];
      apply apery_w_spec; simpl.
    + split; try lia. split; [apply ns_zero | reflexivity].
    + split.
      * split; try reflexivity.
	destruct I as [I _].
	replace 17 with (10 + 7); try reflexivity.
	unfold Included, In in *.
	apply ns_closed; apply I; simpl; intuition.
      *
	-- unfold List.In.
Abort.


Theorem finite_gen A `{numerical_semigroup A} : exists B, Finite B /\ generator A B.
Proof.
   assert (exists n, A n /\ n <> 0) as [n [An n0]]. {
    destruct (cofinite_definitive A) as [m F];
      try apply ns_cofinite.
    exists (S m). split; [auto | lia].
  }
  exists (Add (apery A n) n).
  split.
  - apply Add_preserves_Finite. eapply cardinal_finite.
    apply apery_cardinality; assumption.
  - apply apery_generator; assumption.
Qed.
