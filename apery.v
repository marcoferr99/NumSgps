Require Export def.
From Coq Require Import Lia.
From stdpp Require Import numbers.
Require Import nat.

Generalizable No Variables.
Generalizable Variables C D M.


Section apery.
  Context {C} M `{numerical_semigroup C M} (n : nat).

  (** Apery set definition *)

  Definition apery :=
    filter (.∈ M) ((seq 0 n) ++ map (fun x => x + n) gaps).

  Theorem Sorted_lt_apery : Sorted lt apery.
  Proof.
    apply StronglySorted_Sorted, StronglySorted_filter.
    apply Sorted_StronglySorted; [intros ?; lia|].
    destruct (map (fun x => x + n) gaps) eqn : E.
    - rewrite app_nil_r. apply Sorted_lt_seq.
    - apply Sorted_middle.
      + destruct gaps; [easy|].
	simpl in E. injection E. intros _ <-.
	apply Sorted_snoc; [apply Sorted_lt_seq|].
	destruct n; [constructor|].
	rewrite seq_S. constructor. lia.
      + rewrite <- E.
	generalize (sorted_gaps).
	remember gaps as m. clear.
	intros Sm. induction m; [constructor|].
	simpl. inversion Sm as [|? ? ? Hd].
	constructor; [auto|].
	inversion Hd; constructor. lia.
  Qed.

  Definition apery_set :=
    {[x | x ∈ M /\ (n <= x -> x - n ∉ M)]}.

  Theorem apery_apery_set :
    forall x, x ∈ apery <-> x ∈ apery_set.
  Proof.
    unfold apery, apery_set. intros x.
    rewrite elem_of_list_filter. set_unfold.
    split; intros Hx.
    - destruct Hx as [Mx [Sx | [a [Ga Ha]]]];
	try (split; [assumption|]).
      + apply elem_of_seq in Sx. lia.
      + subst. intros.
	rewrite <- add_sub_assoc, sub_diag, add_0_r;
	  [|lia].
	now apply elem_of_gaps'.
    - destruct Hx as [Mx Hx]. split; [assumption|].
      destruct (le_gt_cases n x) as [L|L].
      + right. exists (x - n). split; [lia|].
	apply elem_of_gaps'. auto.
      + left. apply elem_of_seq. lia.
  Qed.

  Instance apery_set_Decision x : Decision (x ∈ apery_set).
  Proof.
    destruct (decide (x ∈ apery)).
    - left. now apply apery_apery_set.
    - right. intros N. now apply apery_apery_set in N.
  Qed.

  (** The apery set of [n] does not contain two
      different numbers that are congruent modulo [n] *)

  Theorem apery_congr_unique a b : n ∈ M ->
    a ∈ apery -> b ∈ apery -> a mod n = b mod n -> a = b.
  Proof.
    intros Mn.
    assert (T :
      forall a b, a ∈ apery -> b ∈ apery -> a <= b ->
      a mod n = b mod n -> a = b
    ). {
      clear a b. intros a b Aa Ab L N.
      apply apery_apery_set in Aa, Ab.
      destruct (le_gt_cases n b) as [Ln | Lb].
      - destruct Ab as [_ Hb]. apply Hb in Ln.
	apply congr_mod_divide in N. destruct N as [k Hk].
	destruct k; try lia. exfalso. apply Ln.
	replace (b - n) with (k * n + a); try lia.
	apply ns_closed; [now apply ns_mul_closed|].
	now destruct Aa.
      - destruct (le_gt_cases n a); try lia.
	do 2 rewrite mod_small in N; assumption.
    }
    intros. destruct (le_ge_cases a b); try auto.
    symmetry. auto with congr_mod.
  Qed.

  (** [w] is the minimum element of [A] that
      is congruent to [i] modulo [n] *)

  Definition apery_min i w :=
    set_min {[x | x ∈ M ∧ congr_mod n x i]} w.

  Theorem apery_min_exists : n <> 0 ->
    forall i, exists w, apery_min i w.
  Proof.
    intros n0 i. apply well_ordering_principle.
    - intros x.
      assert (D : Decision (x ∈ M ∧ congr_mod n x i)). {
	apply and_dec; [tc_solve | apply eq_dec].
      }
      destruct D; [left|right]; assumption.
    - set_unfold. exists (i + conductor * n). split.
      + apply conductor_le_in. destruct n; lia.
      + unfold congr_mod. apply Div0.mod_add.
  Qed.

  Theorem apery_min_all_classes (n0 : n <> 0) :
    forall x, exists2 i, i < n &
    forall w, apery_min i w -> congr_mod n x w.
  Proof.
    intros x. exists (x mod n).
    - apply mod_upper_bound. assumption.
    - intros w [Hw _]. set_unfold.
      unfold congr_mod in *.
      destruct Hw as [_ Hw]. rewrite Hw.
      symmetry. apply Div0.mod_mod.
  Qed.

  Definition apery_set_2 :=
    {[ x | exists2 i, i < n & apery_min i x]}.

  Inductive apery_l2_aux : nat -> list nat -> Prop :=
    | apery_l_nil : apery_l2_aux 0 []
    | apery_l_cons t i w : apery_min i w ->
	apery_l2_aux i t -> apery_l2_aux (S i) (w :: t).

  Theorem apery_l2_aux_spec m l : apery_l2_aux m l ->
    forall x, x ∈ l <-> exists2 i, i < m & apery_min i x.
  Proof.
    intros Hl. split.
    - intros Hx.
      induction Hl as [| ? ? ? ? ? IH]; [easy|].
      inversion Hx; subst.
      + exists i; [lia|assumption].
      + destruct IH; [assumption|].
	exists x0; [lia|assumption].
    - intros [i Hi Hx].
      induction Hl as [|? j ? AM ? IH]; [lia|].
      destruct (eq_dec i j).
      + replace x with w; [left|].
	eapply set_min_unique; [apply AM|].
	subst. apply Hx.
      + right. apply IH. lia.
  Qed.

  Theorem apery_l2_aux_NoDup m l :
    m <= n -> apery_l2_aux m l -> NoDup l.
  Proof.
    intros L A. induction A; constructor.
    - eapply apery_l2_aux_spec in A.
      intros N. apply A in N. destruct N.
      assert (E : x mod n = i mod n). {
	unfold apery_min, set_min in *. set_unfold.
	destruct H7 as [[_ CM] _]. rewrite <- CM.
	symmetry. apply H9.
      }
      apply congr_mod_divide in E. destruct E.
      destruct n; [lia|]. destruct n0; [lia|].
      induction x0; lia.
    - apply IHA. lia.
  Qed.

  Definition apery_l2 := apery_l2_aux n.

  Theorem apery_l2_apery_set_2 l : apery_l2 l ->
    forall x, x ∈ l <-> x ∈ apery_set_2.
  Proof. apply apery_l2_aux_spec. Qed.

  Theorem apery_l2_NoDup l : apery_l2 l -> NoDup l.
  Proof. apply apery_l2_aux_NoDup. lia. Qed.

  Theorem apery_l2_ex : n <> 0 -> exists l, apery_l2 l.
  Proof.
    intros n0. unfold apery_l2.
    assert (forall i, exists l, apery_l2_aux i l). {
      induction i as [| i [t Ht]].
      - exists []. constructor.
      - destruct (apery_min_exists n0 i) as [w Hw].
	exists (w :: t). now constructor.
    }
    auto.
  Qed.

  Theorem apery_equiv :
    n <> 0 -> n ∈ M -> apery_set ≡ apery_set_2.
  Proof.
    intros n0 Mn.
    assert (I : apery_set_2 ⊆ apery_set). {
      unfold apery_set, apery_set_2. set_unfold.
      intros x [i Li Hi].
      unfold apery_min, set_min in *. set_unfold.
      split; [intuition|].
      intros L N.
      assert (NL : ~(x <= x - n)); [lia|].
      apply NL. apply Hi. intuition.
      unfold congr_mod.
      rewrite <- Div0.mod_add with (b := 1).
      replace (x - n + 1 * n) with x; [|lia].
      assumption.
    }
    intros x. split; [|apply I]. intros Hx.
    destruct (apery_min_all_classes n0 x) as [i Li Hi].
    destruct (apery_min_exists n0 i) as [w Hw].
    exists i; [assumption|].
    replace x with w; [assumption|].
    apply apery_congr_unique; try assumption.
    + apply apery_apery_set.
      apply I. unfold apery_set_2. set_unfold. eauto.
    + now apply apery_apery_set.
    + symmetry. now apply Hi.
  Qed.

  (** Every element of [A] can be written as [k * n + w],
      where [w] is an element of [apery] *)
  Theorem apery_generates : n ∈ M -> n <> 0 ->
    forall a, a ∈ M ->
    exists ! k w, w ∈ apery_set /\ a = k * n + w.
  Proof.
    intros Mn n0 a Ma.
    destruct (decide (a ∈ apery_set)) as [Aa | Aa].
    - exists 0. split.
      + exists a. split; try auto. intuition.
      + intros x [w [[W1 W2] W3]].
	destruct x; try reflexivity.
	exfalso. apply Aa; try lia.
	replace (a - n) with (x * n + w); try lia.
	apply ns_closed; [|apply W1].
	clear W1 W2 W3. induction x; [apply ns_zero|].
	now apply ns_closed.
    - assert (
	exists k, a >= S k * n /\
	~ ((a - k * n) ∈ apery_set) /\ (a - S k * n) ∈ apery_set
      ) as [k [K1 [K2 K3]]]. {
	assert (
	  exists k, set_min {[k | n <= a - S k * n ->
	    ~ (a - S k * n - n) ∈ M]} k
	) as [k [M1 M2]]. {
	    apply well_ordering_principle.
	    - intros x.
	      assert (D : Decision (n ≤ a - S x * n → a - S x * n - n ∉ M)). {
		apply impl_dec.
		- apply Compare_dec.le_dec.
		- tc_solve.
	      }
	      destruct D; [left|right]; assumption.
	    - exists a. set_unfold.
	      induction n; lia.
	}
	exists k.
	assert (G : a >= S k * n). {
	  destruct k.
	  - unfold apery_set in Aa. set_unfold.
	    destruct (le_gt_cases n a); [lia|].
	    exfalso. apply Aa. split; [assumption|].
	    lia.
	  - specialize M2 with k. set_unfold. lia.
	}
	assert (Ak : a - S k * n ∈ M). {
	  destruct k.
	  - unfold apery_set in Aa. set_unfold.
	    rewrite add_0_r.
	    destruct (decide (a - n ∈ M)); [assumption|].
	    exfalso. apply Aa. split; intros; assumption.
	  - specialize M2 with k.
	    apply dec_stable. intros I.
	    assert (N : ~ S k <= k); try lia.
	    apply N. apply M2. set_unfold. intros.
	    replace (a - (n + k * n) - n) with (a - S (S k) * n); [assumption | lia].
	}
	split; try assumption.
	unfold apery_set. set_unfold. split; [|intuition].
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
	  apply apery_congr_unique; try assumption;
	    try (apply apery_apery_set; assumption).
	  symmetry.
	  rewrite <- Div0.mod_add with (b := S k).
	  replace (a - S k * n + S k * n) with a; try lia.
	  subst a. rewrite add_comm. apply Div0.mod_add.
	}
	assert (E1 : a = z + S k * n); try lia.
	subst a.
	apply (mul_cancel_r _ _ n); try assumption. lia.
  Qed.

  Theorem apery_generator : n ∈ M -> n <> 0 ->
    generator (apery_set ∪ {[n]}).
  Proof.
    intros An n0. split.
    - intros x Hx. set_unfold.
      destruct Hx as [Hx | Hx].
      + apply Hx.
      + subst. assumption.
    - intros a Aa.
      generalize (apery_generates An n0 a Aa).
      intros [k [[w [[Aw E] _]] _]].
      apply (generates_eq _ _
	2
	(fun y => match y with
			 | 0 => n
			 | S y => w
			 end)
	(fun y => match y with
			 | 0 => k
			 | S y => 1
			 end)
      ).
      + intros. set_unfold. destruct i; [now right|].
	now left.
      + simpl. lia.
  Qed.

End apery.


Theorem finite_gen `{numerical_semigroup C M} :
  exists A : propset nat, set_finite A /\ generator A.
Proof.
  assert (exists n, n ∈ M /\ n <> 0) as [n [Mn n0]]. {
    exists (S conductor). split; [|easy].
    apply conductor_le_in. lia.
  }
  exists (apery_set M n ∪ {[n]}).
  split; [|now apply apery_generator].
  exists (n :: apery M n).
  intros x Hx. destruct Hx.
  - right. now apply apery_apery_set.
  - set_unfold. intuition.
Qed.


(**********)
(** Apery *)
(**********)

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

Theorem mod_ge_congr n a x :
  congr_mod n a x -> mod_ge n a x = x.
Proof.
  intros I. unfold mod_ge. unfold congr_mod in I.
  destruct (leb_spec x (x - x mod n + a mod n)); [|lia].
  generalize (Div0.mod_le x n). intros D. lia.
Qed.


Fixpoint find_congr n a l := let an := a mod n in
  match l with
  | [] => 0
  | [e] => mod_ge n a e
  | h :: t => if h mod n =? an then h else find_congr n a t
  end.

Theorem find_congr_rewrite n a x y t :
  find_congr n a (x :: y :: t) =
  if x mod n =? a mod n then x else find_congr n a (y :: t).
Proof. reflexivity. Qed.

Theorem find_congr_congr n a l :
  l <> [] -> congr_mod n (find_congr n a l) a.
Proof.
  induction l; [easy|].
  simpl. destruct l; [intros; apply mod_ge_mod|].
  intros. destruct (eqb_spec (a0 mod n) (a mod n));
    [assumption|].
  auto.
Qed.

Theorem find_congr_min n a l x :
  Sorted lt l -> n <> 0 -> x ∈ l ->
  congr_mod n a x -> find_congr n a l <= x.
Proof.
  intros SS n0 Lx I. induction l; simpl; [lia|].
  destruct l.
  - set_unfold. destruct Lx; [|easy]. subst.
    rewrite mod_ge_congr; [lia|assumption].
  - destruct (eqb_spec (a0 mod n) (a mod n)).
    + destruct (eq_dec a0 x); [lia|].
      apply Sorted_StronglySorted in SS;
	[|intros ?; lia].
      inversion SS. assert (a0 < x); [|lia].
      eapply Forall_forall; try eassumption.
      inversion Lx; [|assumption].
      subst. contradiction.
    + destruct (eq_dec x a0).
      * subst. unfold congr_mod in I. symmetry in I.
	contradiction.
      * apply IHl; [now inversion SS|].
	inversion Lx; now subst.
Qed.

Theorem test n x y :
  n <> 0 -> x > y -> x >= y - y mod n + x mod n.
Proof.
  clear. intros n0 L.
  rewrite (Div0.div_mod x n) at 1.
  rewrite (Div0.div_mod y n) at 1.
  generalize (Div0.div_le_mono y x n). intros Lm.
  apply add_le_mono; [|lia].
  rewrite <- add_sub_assoc; [|lia].
  rewrite sub_diag.
  remember (y / n) as b eqn : E. clear E.
  remember (x / n) as a eqn : E. clear E.
  induction n; lia.
Qed.

Theorem test2 n x y :
  congr_mod n x y -> x > y -> exists q, x = q * n + y.
Proof.
  clear. intros H L.
  assert ((x - y) mod n = 0). {
    apply congr_mod_symm in H.
    apply congr_mod_divide in H.
    destruct H. rewrite H.
    apply Div0.mod_mul.
  }
  apply (Lcm0.mod_divide (x - y) n) in H0.
  destruct H0. exists x0. lia.
Qed.

Theorem find_congr_min_2 n a l x :
  Sorted lt l -> n <> 0 -> x > l !!! (length l - 1) ->
  congr_mod n a x -> find_congr n a l <= x.
Proof.
  clear.
  intros SS n0 Lx I. induction l; simpl; [lia|].
  destruct l.
  - set_unfold.
    unfold mod_ge.
    rewrite I.
    destruct (leb_spec a0 (a0 - a0 mod n + x mod n)).
    + apply test; [assumption|lia].
    + replace (a0 - a0 mod n + x mod n + n) with (a0 - a0 mod n + n + x mod n); [|lia].
      assert (x mod n < a0 mod n); [lia|].
      assert (a0 - a0 mod n + n <= x - x mod n); [|lia].
      destruct (test2 n (x - x mod n) (a0 - a0 mod n)).
      * unfold congr_mod.
	rewrite (div_mod_eq a0 n) at 1.
	rewrite <- add_sub_assoc, sub_diag, add_0_r; [|lia].
	rewrite mul_comm, Div0.mod_mul.
	rewrite (div_mod_eq x n) at 1.
	rewrite <- add_sub_assoc, sub_diag, add_0_r; [|lia].
	rewrite mul_comm, Div0.mod_mul.
	reflexivity.
      * lia.
      * destruct x0.
	-- simpl in *. lia.
	-- lia.
  - destruct (eqb_spec (a0 mod n) (a mod n)).
    + simpl in *.
      apply Sorted_StronglySorted in SS; [|intros ?; lia].
      inversion SS. subst.
      assert (a0 < (n1 :: l) !!! length l); [|lia].
      eapply Forall_forall; [eassumption|].
      apply elem_of_list_lookup_total_2.
      simpl. lia.
    + apply IHl; [now inversion SS|].
      simpl in *. now rewrite sub_0_r.
Qed.

Theorem find_congr_th n a l : n <> 0 -> l <> [] ->
  find_congr n a l ∈ l \/
  find_congr n a l > l !!! (length l - 1).
Proof.
  intros n0 ln. induction l as [ | h t IH]; try contradiction.
  destruct t as [ | k t].
  - simpl in *.
    destruct (eq_dec h (mod_ge n a h));
      [set_unfold; intuition|].
    right. apply (mod_ge_ge _ a h) in n0. lia.
  - rewrite find_congr_rewrite.
    destruct (eqb_spec (h mod n) (a mod n)).
    + simpl. set_unfold. intuition.
    + remember (find_congr n a (k :: t)) as l.
      destruct IH as [IH|IH]; try discriminate.
      * left. simpl in *. set_unfold. intuition.
      * right. simpl in *. now rewrite sub_0_r in IH.
Qed.

Fixpoint apery_alg_aux n m l :=
  match m with
  | 0 => []
  | S m => find_congr n m l :: apery_alg_aux n m l
  end.

Definition apery_alg l n :=
  apery_alg_aux n n l.

Theorem apery_alg_correct n i :
  term i -> n <> 0 -> n ∈ M ->
  forall x, x ∈ apery_alg n i <-> x ∈ apery_set M n.
Proof.
  intros T n0 Mn x.
  rewrite apery_equiv; try assumption; [|tc_solve].
  unfold apery_alg, apery_set_2. set_unfold.
  assert (forall m, x ∈ apery_alg_aux n m (small_elements i) <-> (exists2 i, i < m & apery_min M n i x)); [|auto].
  induction m.
  { simpl. split; [easy|]. intros []. lia. }
  assert (l0 : small_elements i <> []). {
    intros N. assert (0 ∈ []); [|easy].
    rewrite <- N.
    apply small_elements_small_elements_set; [assumption|].
    split; [apply ns_zero | lia].
  }
  assert (E : (small_elements i) !!! (length (small_elements i) - 1) = conductor). {
    edestruct (elem_of_list_split (small_elements i)) as (l1 & l2 & Hl).
    * apply small_elements_small_elements_set; [assumption|].
      split; [apply conductor_le_in|]; apply le_refl.
    * generalize (Sorted_lt_small_elements i). intros SS.
      rewrite Hl in SS.
      apply Sorted_app_r in SS.
      apply Sorted_StronglySorted in SS;
	[|intros ?; lia].
      destruct l2.
      -- rewrite Hl.
	 apply list_lookup_total_middle.
	 rewrite length_app. simpl. lia.
      -- inversion SS.
	 assert (conductor < l !!! (length l - 1)). {
	   eapply Forall_forall; [eassumption|].
	   subst.
	   apply elem_of_list_lookup_total_2.
	   simpl. lia.
	 }
	 assert (l !!! (length l - 1) <= conductor);
	   [|lia].
	 assert (l !!! (length l - 1) ∈ small_elements i). {
	   rewrite Hl. subst.
	   apply elem_of_app. right.
	   simpl. right.
	   apply elem_of_list_lookup_total_2.
	   simpl. lia.
	 }
	 apply small_elements_small_elements_set in H12; [|assumption].
	 unfold small_elements_set in H12. set_unfold.
	 apply H12.
  }
  split.
  - intros Hx. simpl in Hx.
    set_unfold. destruct Hx.
    + exists m; [lia|].
      unfold apery_min, set_min. set_unfold.
      split; [split|].
      * apply (find_congr_th n m (small_elements i)) in n0 as F;
	 [|assumption].
	destruct F.
	-- subst. eapply small_elements_in. eassumption.
	-- rewrite E in H8. subst.
	   apply conductor_le_in. lia.
      * subst. now apply find_congr_congr.
      * subst.
	intros x [Mx Hx].
	destruct (decide (x ∈ (small_elements i))).
	-- apply find_congr_min; try assumption.
	   ++ apply Sorted_lt_small_elements.
	   ++ auto with congr_mod.
	      -- assert (conductor < x). {
		 apply dec_stable. intros N. apply n1.
		 apply small_elements_small_elements_set; [assumption|].
		 split; [assumption|lia].
	      }
	      apply congr_mod_symm in Hx.
	      apply find_congr_min_2; try assumption.
	      ** apply Sorted_lt_small_elements.
	      ** lia.
    + apply IHm in H7. destruct H7. exists x0.
      * lia.
      * assumption.
  -
  simpl. constructor; [|assumption].
  unfold apery_min, set_min. set_unfold. split.
  - destruct (find_congr_th n m l); try assumption.
    + split; [now apply L|]. now apply find_congr_congr.
    + unfold small_elements_list in L.
      rewrite E in *. split.
      * apply conductor_le_in. lia.
      * now apply find_congr_congr.
  - intros x [Mx Hx].
    destruct (decide (x ∈ l)).
    + apply find_congr_min; try assumption.
      * apply L.
      * auto with congr_mod.
    + assert (conductor < x). {
	apply dec_stable. intros N. apply n1.
	apply L. split; [assumption|lia].
      }
      apply congr_mod_symm in Hx.
      apply find_congr_min_2; try assumption.
      * apply L.
      * lia.
Qed.

End generators.

Compute small_elements_opt [5;9;21] 100.
Compute match small_elements_opt [5;9;21] 100 with
      | None => None
      | Some l => Some (rev (apery_alg 6 l))
      end.




Theorem i_not_zero i : term i -> i <> 0.
Proof.
  unfold term. intros T ?. subst. simpl in T. lia.
Qed.

Theorem nth_limit_not_zero i :
  term i -> nth_limit i <> 0.
Proof.
  unfold nth_limit. intros T N.
  apply eq_mul_0_r in N; try contradiction.
  destruct i.
  - apply i_not_zero in T. contradiction.
  - intros D. apply length_zero_iff_nil in D.
    simpl in D. eapply next_not_nil. eassumption.
Qed.

Theorem small_list_limit_not_nil i :
  term i -> small_list_limit i <> [].
Proof.
  intros T D.
  generalize (small_list_all i 0). intros I.
  unfold small_list_limit in *.
  assert (N : 0 ∈ []); try inversion N.
  rewrite <- D. apply elem_of_list_filter.
  apply nth_limit_not_zero in T. split; [lia|].
  apply I; try apply ns_zero. lia.
Qed.

(** [small_elements] contains all the elements of [A] that are less then or
  equal to [cond]. *)

Theorem small_elements_le_all i : term i ->
  forall a, a ∈ M -> a <= cond i ->
  a ∈ small_elements i.
Proof.
  intros T a Aa L.
  assert (Is : a ∈ small_list_limit i). {
    eapply small_list_limit_all; try eassumption.
    apply Exists_exists. exists (cond i).
    split; try assumption. 
    now apply elem_of_list_lookup_total_2.
  }
  apply elem_of_list_lookup_total_1 in Is.
  destruct Is as [n [Hn1 Hn2]]. subst a.
  unfold cond in L.
  assert (n <= cond_pos i). {
    apply nlt_ge. intros ?.
    apply nlt_ge in L. apply L. clear L.
    apply StronglySorted_lookup; try assumption.
    apply Sorted_StronglySorted; [intros ?; lia|].
    apply small_list_limit_sorted.
  }
  unfold term in T.
  rewrite <- (firstn_skipn (S (cond_pos i)) (small_list_limit i)).
  rewrite lookup_total_app_l.
  - apply elem_of_list_lookup_total_2.
    unfold small_elements. rewrite length_take_le; lia.
  - rewrite length_take_le; lia.
Qed.
