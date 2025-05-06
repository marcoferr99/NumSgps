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
