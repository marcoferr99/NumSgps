Require Export generators.
From Coq Require Import Lia.
From stdpp Require Import numbers.
Require Import nat.

Generalizable No Variables.
Generalizable Variables C D M.


Section apery.
  Context {C} M `{numerical_semigroup C M} (n : nat).


  (****************************)
  (** * Apery list definition *)
  (****************************)

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

  Theorem apery_spec :
    forall x, x ∈ apery <-> x ∈ M /\ (n <= x -> x - n ∉ M).
  Proof.
    unfold apery. intros x.
    rewrite elem_of_list_filter. set_unfold.
    split; intros [Mx Hx]; (split; [assumption|]).
    - destruct Hx as [Sx | [a [Ga Ha]]].
      + apply elem_of_seq in Sx. lia.
      + subst. intros.
	replace (a + n - n) with a; [|lia].
	now apply elem_of_gaps'.
    - destruct (le_gt_cases n x) as [L|L].
      + right. exists (x - n). split; [lia|].
	apply elem_of_gaps'. auto.
      + left. apply elem_of_seq. lia.
  Qed.


  (*****************************)
  (** * Apery characterization *)
  (*****************************)

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
      apply apery_spec in Aa, Ab.
      destruct (le_gt_cases n b) as [Ln | Lb].
      - destruct Ab as [_ Hb]. apply Hb in Ln.
	apply mod_divide in N. destruct N as [k Hk].
	destruct k; try lia. exfalso. apply Ln.
	replace (b - n) with (k * n + a); try lia.
	apply ns_closed; [now apply ns_mul_closed|].
	now destruct Aa.
      - destruct (le_gt_cases n a); try lia.
	do 2 rewrite mod_small in N; assumption.
    }
    intros. destruct (le_ge_cases a b); try auto.
    symmetry. auto.
  Qed.

  (** [w] is the minimum element of [A] that
      is congruent to [i] modulo [n] *)

  Definition apery_min i w :=
    set_min {[x | x ∈ M ∧ x mod n = i mod n]} w.

  Theorem apery_min_exists : n <> 0 ->
    forall i, exists w, apery_min i w.
  Proof.
    intros n0 i. apply well_ordering_principle.
    - intros x.
      assert (D : Decision (x ∈ M ∧ x mod n = i mod n)). {
	apply and_dec; [tc_solve | apply eq_dec].
      }
      destruct D; [left|right]; assumption.
    - set_unfold. exists (i + conductor * n). split.
      + apply conductor_le_in. destruct n; lia.
      + apply Div0.mod_add.
  Qed.

  Theorem apery_min_all_classes (n0 : n <> 0) :
    forall x, exists2 i, i < n &
    forall w, apery_min i w -> x mod n = w mod n.
  Proof.
    intros x. exists (x mod n).
    - apply mod_upper_bound. assumption.
    - intros w [Hw _]. set_unfold.
      destruct Hw as [_ Hw]. rewrite Hw.
      symmetry. apply Div0.mod_mod.
  Qed.

  Theorem apery_spec_2 : n <> 0 -> n ∈ M ->
    forall x, x ∈ apery <->
    exists2 i, i < n & apery_min i x.
  Proof.
    intros n0 Mn.
    assert (I : forall x, (exists2 i, i < n & apery_min i x) -> x ∈ apery). {
      intros x [i Hi Hx]. apply apery_spec.
      unfold apery_min, set_min in *. set_unfold.
      split; [intuition|].
      intros L N.
      assert (NL : ~(x <= x - n)); [lia|].
      apply NL. apply Hx. intuition.
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
    + apply I. eauto.
    + symmetry. now apply Hi.
  Qed.


  (**************)
  (** ** Unused *)
  (**************)

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
      apply mod_divide in E. destruct E.
      destruct n; [lia|]. destruct n0; [lia|].
      induction x0; lia.
    - apply IHA. lia.
  Qed.

  Definition apery_l2 := apery_l2_aux n.

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


  (**************************)
  (** * Apery as generators *)
  (**************************)

  (** Every element of [A] can be written as [k * n + w],
      where [w] is an element of [apery] *)

  Theorem apery_generates : n ∈ M -> n <> 0 ->
    forall a, a ∈ M ->
    exists ! k w, w ∈ apery /\ a = k * n + w.
  Proof.
    intros Mn n0 a Ma.
    destruct (decide (a ∈ apery)) as [Aa | Aa].
    - exists 0. split.
      + exists a. split; try auto. intuition.
      + intros x [w [[W1 W2] W3]].
	destruct x; try reflexivity.
	apply apery_spec in Aa, W1; try assumption.
	exfalso. apply Aa; try lia.
	replace (a - n) with (x * n + w); try lia.
	apply ns_closed; [|apply W1].
	clear W1 W2 W3. induction x; [apply ns_zero|].
	now apply ns_closed.
    - assert (
	exists k, a >= S k * n /\
	~ ((a - k * n) ∈ apery) /\ (a - S k * n) ∈ apery
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
	  - rewrite apery_spec in Aa. set_unfold.
	    destruct (le_gt_cases n a); [lia|].
	    exfalso. apply Aa. split; [assumption|].
	    lia.
	  - specialize M2 with k. set_unfold. lia.
	}
	assert (Ak : a - S k * n ∈ M). {
	  destruct k.
	  - rewrite apery_spec in Aa. set_unfold.
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
	repeat rewrite apery_spec. set_unfold.
	split; [|intuition].
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

  Theorem generator_apery : n ∈ M -> n <> 0 ->
    generator M (n :: apery).
  Proof.
    intros An n0. split.
    - intros x Hx. set_unfold.
      destruct Hx as [Hx | Hx].
      + now subst.
      + now apply apery_spec.
    - intros a Aa.
      generalize (apery_generates An n0 a Aa).
      intros [k [[w [[Aw E] _]] _]].
      apply (lin_comb_eq _ _
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
      + intros. set_unfold. destruct i; [now left|].
	now right.
      + simpl. lia.
  Qed.


  (**********************************)
  (** Apery alternative computation *)
  (**********************************)

  Fixpoint apery_2_aux m l :=
    match m with
    | 0 => []
    | S m => find_mod n conductor m l :: apery_2_aux m l
    end.

  Definition apery_2 := apery_2_aux n small_elements.

  Theorem apery_2_correct :
    n <> 0 -> n ∈ M -> forall x, x ∈ apery_2 <-> x ∈ apery.
  Proof.
    intros n0 Mn x.
    rewrite apery_spec_2; try assumption.
    unfold apery_2.
    assert (forall m, x ∈ apery_2_aux m small_elements <-> (exists2 i, i < m & apery_min i x)); [|auto].
    induction m.
    { simpl. split; [easy|]. intros []. lia. }
    assert (l0 : small_elements <> []). {
      intros N. assert (0 ∈ []); [|easy].
      rewrite <- N.
      apply small_elements_spec.
      split; [apply ns_zero | lia].
    }
    assert (Ss : Sorted lt small_elements). {
      apply StronglySorted_Sorted.
      apply StronglySorted_filter.
      apply Sorted_StronglySorted; [intros ?; lia|].
      apply Sorted_lt_seq.
    }
    assert (AM : apery_min m (find_mod n conductor m small_elements)). {
      unfold apery_min, set_min. set_unfold.
      split; [split|].
      - apply (find_mod_in n conductor m small_elements) in n0 as F.
	destruct F as [F|F].
	+ subst. apply small_elements_spec in F. apply F.
	+ apply conductor_le_in. lia.
      - subst. now apply find_mod_mod.
      - subst. intros a [Mx Hx].
	destruct (decide (a ∈ small_elements)).
	+ apply find_mod_min; assumption.
	+ assert (conductor < a). {
	  apply dec_stable. intros N. apply n1.
	  apply small_elements_spec.
	  split; [assumption|lia].
	  }
	  apply find_mod_min_2; try assumption.
	  apply Forall_forall.
	  intros y Hy. apply elem_of_list_filter in Hy.
	  rewrite elem_of_seq in Hy. lia.
    }
    split; simpl.
    - intros Hx. set_unfold. destruct Hx.
      + exists m; [lia|]. subst. apply AM.
      + destruct IHm as [IHm _]. destruct IHm; eauto.
    - intros [i Li Hi].
      destruct (eq_dec i m).
      + subst. set_unfold. left.
	eapply set_min_unique; [eassumption|].
	apply AM.
      + right. apply IHm. exists i; [lia|]. assumption.
  Qed.

End apery.
