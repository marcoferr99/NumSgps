From Coq Require Import Euclid Lia.
Require Export def list_alg.
 
Generalizable No Variables.
Generalizable Variables C D M.


Section generators.
  Context `{ElemOf nat D} (A : D).

  Inductive lin_comb : nat -> Prop :=
    lin_comb_intro r x l
      (IA : (forall i, i < r -> x i ∈ A)) :
      lin_comb (sum_list_with (fun i => l i * x i) (seq 0 r)).

  Theorem lin_comb_eq a r x l :
    (forall i, i < r -> x i ∈ A) ->
    a = sum_list_with (fun i => l i * x i) (seq 0 r) ->
    lin_comb a.
  Proof. now intros ? ->. Qed.

  Theorem lin_comb_add x y :
    lin_comb x -> lin_comb y -> lin_comb (x + y).
  Proof.
    clear. intros Hx Hy.
    inversion Hx as [rx ax kx Hax].
    inversion Hy as [ry ay ky Hay].
    set (a i := if (i <? rx) then ax i else ay (i - rx)).
    set (k i := if (i <? rx) then kx i else ky (i - rx)).
    apply (lin_comb_eq _ (rx + ry) a k).
    - intros. unfold a. destruct (ltb_spec i rx); [auto|].
      apply Hay. lia.
    - rewrite seq_app, sum_list_with_app. f_equal.
      + apply sum_list_with_eq.
	intros z Hz. unfold k, a.
	apply elem_of_seq in Hz.
	destruct (ltb_spec z rx); lia.
      + unfold k, a. clear.
	induction ry; [reflexivity|].
	repeat rewrite seq_S, sum_list_with_app.
	rewrite IHry. f_equal.
	simpl. destruct (ltb_spec (rx + ry) rx); [lia|].
	replace (rx + ry - rx) with ry; lia.
  Qed.

  Definition generated := {[x | lin_comb x]}.

  Instance submonoid_generated : submonoid generated.
  Proof.
    clear. constructor; unfold generated; set_unfold.
    - apply (lin_comb_eq _ 0 id id); [lia|reflexivity].
    - intros x y Hx Hy. now apply lin_comb_add.
  Qed.

  Theorem lin_comb_in `{submonoid C M} :
    (forall x, x ∈ A -> x ∈ M) ->
    forall a, lin_comb a -> a ∈ M.
  Proof.
    intros I a G. inversion G. subst.
    clear G. induction r; [apply ns_zero|].
    rewrite seq_S. rewrite sum_list_with_app.
    apply ns_closed.
    - apply IHr. intros. apply IA. lia.
    - simpl. rewrite add_0_r.
      apply ns_mul_closed. apply I. apply IA. lia.
  Qed.

End generators.

Definition generator `{ElemOf nat C} (M : C) `{ElemOf nat D} (A : D) :=
  (forall x, x ∈ A -> x ∈ M) /\
  forall a, a ∈ M -> lin_comb A a.

Theorem generator_generated `{ElemOf nat D} (A : D) :
  generator (generated A) A.
Proof.
  unfold generator, generated. set_unfold.
  split; intros; [|assumption].
  apply (lin_comb_eq _ _ 1 (fun _ => x) (fun _ => 1));
    [auto|].
  simpl. lia.
Qed.


Section generators.
  Variables (gen : list nat).
  Local Notation M := (generated gen).
  Local Notation mlt := (list_min gen).
  Hypothesis (m0 : mlt <> 0).
  Local Notation nh := (nh (length gen - 1)).

  Theorem gen_neq : gen <> [].
  Proof. intros ?. subst. contradiction. Qed.

  Theorem length_gen_neq : length gen <> 0.
  Proof.
    intros ?. now apply gen_neq, length_zero_iff_nil.
  Qed.

  Theorem nh_Forall_gt n : Forall (gt (length gen)) (nh n).
  Proof.
    apply Forall_forall. intros x Hx.
    generalize (nh_Forall (length gen - 1) n). intros F.
    eapply Forall_forall in F; [|eassumption].
    generalize length_gen_neq. lia.
  Qed.

  Definition nhsum n := sum_list_with (gen !!!.) (nh n).

  Definition nth_limit n := length (nh n) * mlt.

  Theorem nhsum_le n : nhsum n >= nth_limit n.
  Proof.
    unfold nth_limit, nhsum.
    generalize (nh_Forall_gt n). intros F.
    remember (nh n) as h eqn : E. clear E.
    induction h; simpl; try lia.
    inversion F. subst. eapply le_trans.
    - apply add_le_mono_l. apply IHh. assumption.
    - apply add_le_mono_r. apply list_min_le.
      now apply elem_of_list_lookup_total_2.
  Qed.

  Theorem nhsum_in : forall n, nhsum n ∈ M.
  Proof.
    generalize (submonoid_generated gen). intros SM.
    intros. unfold nhsum.
    generalize (nh_Forall_gt n). intros F.
    remember (nh n) as ls eqn : E.
    remember (length ls) as ln eqn : En. clear E.
    generalize dependent ls.
    induction ln as [ | ln IH]; intros.
    + symmetry in En. apply length_zero_iff_nil in En.
      subst. simpl. apply ns_zero.
    + intros. destruct ls; try discriminate.
      inversion F. subst. simpl. apply ns_closed.
      * destruct (generator_generated gen) as [G _].
	apply G.
	apply elem_of_list_lookup_total_2. lia.
      * apply IH; auto.
  Qed.

  Theorem nhsum_all a : a ∈ M -> exists n, nhsum n = a.
  Proof.
    intros Aa. destruct (generator_generated gen) as [_ G].
    destruct (G a Aa) as [r x k Hr].
    set (l := flat_map (fun i => repeat (lookup_inv gen (x i)) (k i)) (seq 0 r)).
    set (ol := reverse (merge_sort le l)).
    destruct (nh_all (length gen - 1) ol) as [n Hn].
    - apply Forall_impl with (P := gt (length gen));
	[|intros; lia].
      subst ol. apply Forall_reverse.
      rewrite merge_sort_Permutation.
      unfold l. apply Forall_flat_map.
      apply Forall_forall. intros y Hy.
      rewrite repeat_replicate. apply Forall_replicate.
      apply lookup_inv_lt. apply Hr.
      apply elem_of_seq in Hy. lia.
    - subst ol. apply Sorted_reverse.
      apply Sorted_merge_sort. intros ?. lia.
    - exists n. unfold nhsum. rewrite Hn. clear n Hn.
      rewrite (Permutation_sum_list_with _ _ l).
      + subst l. rewrite sum_list_with_flat_map.
	clear Aa. induction r; try reflexivity.
	rewrite seq_S.
	repeat rewrite sum_list_with_app. f_equal.
	* apply IHr. clear IHr. intros. apply Hr. lia.
	* clear IHr. simpl.
	  remember (k r) as kr eqn : E. clear E.
	  generalize Hr. clear. intros.
	  induction kr; try reflexivity.
	  simpl. rewrite lookup_lookup_inv; [|auto].
	  do 2 f_equal.
	  repeat rewrite add_0_r in IHkr. assumption.
      + subst ol. eapply Permutation_trans.
	* apply reverse_Permutation.
	* apply merge_sort_Permutation.
  Qed.

  Theorem nhsum_all_limit m a : a ∈ M -> a < nth_limit m ->
    exists n, n < m /\ nhsum n = a.
  Proof.
    intros Aa L.
    destruct (nhsum_all a) as [n Hn]; try assumption.
    exists n. split; try assumption. subst.
    destruct (le_gt_cases m n); try assumption.
    apply Arith_base.lt_not_le_stt in L.
    exfalso. apply L.
    eapply le_trans; [|apply nhsum_le].
    apply mul_le_mono_r. now apply nh_le_length.
  Qed.

  Fixpoint small_list_aux n :=
    match n with
    | 0 => []
    | S n => nhsum n :: small_list_aux n
    end.

  Definition small_list n :=
    sorted_nodup (merge_sort le (small_list_aux n)).

  Theorem small_list_all n a :
    a ∈ M -> a < nth_limit n -> a ∈ small_list n.
  Proof.
    intros Aa L.
    destruct (nhsum_all_limit n a) as [m Hm];
      try assumption.
    destruct Hm as [Hm E]. subst.
    generalize Hm. clear. intros.
    unfold small_list. rewrite <- sorted_nodup_in.
    rewrite merge_sort_Permutation.
    generalize dependent m. intros.
    induction n; simpl; try lia.
    destruct (eq_dec m n); subst; [left|right].
    apply IHn; lia.
  Qed.

  Theorem small_list_in i a : a ∈ small_list i -> a ∈ M.
  Proof.
    unfold small_list.
    rewrite <- sorted_nodup_in, merge_sort_Permutation.
    intros Ha. induction i; [inversion Ha|].
    simpl in *. set_unfold in Ha. destruct Ha; [|auto].
    subst. apply nhsum_in.
  Qed.

  Theorem small_list_sorted i : Sorted lt (small_list i).
  Proof.
    unfold small_list.
    apply Sorted_lt_sorted_nodup.
    apply Sorted_merge_sort.
    intros ?. lia.
  Qed.

  Definition small_list_limit n :=
    filter (fun x => x <= nth_limit n) (small_list n).

  Theorem Sorted_lt_small_list_limit n :
    Sorted lt (small_list_limit n).
  Proof.
    apply StronglySorted_Sorted.
    apply StronglySorted_filter.
    apply Sorted_StronglySorted; [intros ?; lia|].
    apply small_list_sorted.
  Qed.

  Theorem small_list_limit_all n a :
    a ∈ M -> Exists (le a) (small_list_limit n) ->
    a ∈ small_list_limit n.
  Proof.
    intros Aa E. unfold small_list_limit in *.
    apply elem_of_list_filter. apply Exists_exists in E.
    destruct E as [x Hx]. destruct Hx as [I L].
    apply elem_of_list_filter in I. destruct I.
    split; [lia|].
    destruct (eq_dec x a); subst; [assumption|].
    apply small_list_all; [assumption|lia].
  Qed.

  Theorem small_list_limit_in n a :
    a ∈ small_list_limit n -> a ∈ M.
  Proof.
    unfold small_list_limit.
    rewrite elem_of_list_filter.
    intros Ha.
    eapply small_list_in. apply Ha.
  Qed.

  Definition cond_pos i :=
    find_seq (small_list_limit i) (list_min gen).

  Definition term i :=
    cond_pos i < length (small_list_limit i).

  Definition cond i := small_list_limit i !!! cond_pos i.

  Theorem cond_pred_notin i :
    term i -> cond i <> 0 -> (cond i - 1) ∉ M.
  Proof.
    generalize (submonoid_generated gen). intros SM.
    intros T N L.
    generalize (Sorted_lt_small_list_limit i). intros SS.
    apply Sorted_StronglySorted in SS; [|intros ?; lia].
    assert (cond_pos i <> 0). {
      intros D. unfold cond in *.
      rewrite D in *. clear D. apply N.
      inversion SS as [|? ? ? ? E]; try reflexivity. simpl.
      assert (I : 0 ∈ small_list_limit i). {
	apply small_list_limit_all.
	- apply ns_zero.
	- rewrite <- E. constructor. lia.
      }
      rewrite <- E in *. set_unfold.
      destruct I; [auto|].
      inversion SS. assert (a < 0); [|lia].
      eapply Forall_forall; eassumption.
    }
    eapply (find_seq_first (small_list_limit i) _ (cond_pos i - 1)).
    - apply T.
    - fold (cond_pos i). lia.
    - replace (S (cond_pos i - 1)) with (cond_pos i);
	[|lia].
      eapply small_list_limit_all in L.
      2:{
	apply Exists_exists. exists (cond i).
	split; [|lia].
	now apply elem_of_list_lookup_total_2.
      }
      apply elem_of_list_lookup_total_1 in L.
      destruct L as [n [Hn1 Hn2]].
      fold (cond i).
      replace (cond_pos i - 1) with n; [lia|].
      unfold cond in Hn2. unfold term in T.
      assert (Ln : n < cond_pos i). {
	assert (Ln : n <= cond_pos i). {
	  eapply StronglySorted_lookup_2;
	    try eassumption.
	  fold (cond i) in *.
	  rewrite Hn2. unfold cond. lia.
	}
	assert (n <> cond_pos i); [|lia].
	intros D. subst. fold (cond i) in *. lia.
      }
      assert (S n = cond_pos i); [|lia].
      assert (LSn : S n < length (small_list_limit i));
	[lia|].
      apply le_antisymm; [lia|].
      eapply StronglySorted_lookup_2; try eassumption.
      fold (cond i) in *.
      unfold lt. intros D.
      assert (nSn : n < S n); [lia|].
      eapply StronglySorted_lookup in nSn; try eassumption.
      unfold lt in *. rewrite Hn2 in *.
      replace (small_list_limit i !!! cond_pos i) with (cond i) in *; [|reflexivity].
      lia.
  Qed.

  (** All the elements greater than or equal to cond are in A. *)

  Theorem cond_ge_in i : term i ->
    forall a, cond i <= a -> a ∈ M.
  Proof.
    generalize (submonoid_generated gen). intros SM.
    intros T a L.
    replace a with (a - cond i + cond i); [|lia].
    rewrite (Div0.div_mod (a - cond i) (list_min gen)).
    rewrite <- add_assoc. apply ns_closed.
    + rewrite mul_comm. apply ns_mul_closed.
      destruct (generator_generated gen) as [G _]. apply G.
      apply list_min_in. apply gen_neq.
    + apply (find_seq_seq (small_list_limit i) (list_min gen)) in T.
      apply small_list_limit_in with (n := i);
	try assumption.
      rewrite <- (firstn_skipn (cond_pos i) (small_list_limit i)).
      apply elem_of_app. right.
      rewrite <- (firstn_skipn (list_min gen)).
      apply elem_of_app. left.
      fold (cond_pos i) in T. rewrite T.
      apply (mod_upper_bound (a - cond i) (list_min gen)) in m0.
      fold (cond i) in *.
      apply elem_of_seq. lia.
  Qed.

  Theorem cond_max i : term i ->
    (1 ∈ M ∧ cond i = 0) ∨ (set_max ({[x | x ∉ M]}) (cond i - 1)).
  Proof.
    intros T.
    destruct (cond i) eqn : E.
    - left. split; [|reflexivity].
      eapply cond_ge_in; [eassumption|]. lia.
    - right. unfold set_max. split.
      + rewrite elem_of_PropSet, <- E.
	apply cond_pred_notin; [assumption|lia].
      + intros m Hm. rewrite elem_of_PropSet in Hm.
	destruct (le_gt_cases m (S n - 1)); [assumption|].
	exfalso. apply Hm.
	eapply cond_ge_in; [eassumption|]. lia.
  Qed.

  Definition small_els i :=
    take (S (cond_pos i)) (small_list_limit i).

  Theorem small_els_alt i : term i ->
    small_els i =
    filter (fun x => x <= cond i) (small_list_limit i).
  Proof.
    intros T. unfold small_els. apply Sorted_lt_eq.
    - eapply Sorted_app_l.
      rewrite take_drop. apply Sorted_lt_small_list_limit.
    - apply StronglySorted_Sorted.
      apply StronglySorted_filter.
      apply Sorted_StronglySorted; [intros ?; lia|].
      apply Sorted_lt_small_list_limit.
    - intros x. rewrite elem_of_list_filter.
      split; intros Hx.
      + split.
	* destruct (eq_dec x (cond i)); [lia|].
	  assert (x < cond i); [|lia].
	  apply elem_of_take in Hx as [j [Sx Hx]].
	  unfold le, cond.
	  erewrite <- (list_lookup_total_correct _ j x);
	    [|eassumption].
	  eapply StronglySorted_lookup.
	  -- apply Sorted_StronglySorted; [intros ?; lia|].
	     apply Sorted_lt_small_list_limit.
	  -- apply lookup_lt_is_Some. now exists x.
	  -- assumption.
	  -- assert (j <> cond_pos i); [|lia].
	     intros N. apply n.
	     erewrite <- (list_lookup_total_correct _ j x);
		[|eassumption].
	     unfold cond. now f_equal.
	* eapply subseteq_take. eassumption.
      + apply elem_of_take.
	destruct Hx as [L Hx].
	apply elem_of_list_lookup_1 in Hx as [a Ha].
	exists a. split; [assumption|].
	apply le_n_S.
	eapply StronglySorted_lookup_2.
	* apply Sorted_StronglySorted;
	    [|apply Sorted_lt_small_list_limit].
	  intros ?. lia.
	* apply T.
	* apply lookup_lt_is_Some_1. now exists x.
	* unfold lt.
	  erewrite (list_lookup_total_correct _ a);
	    [|eassumption].
	  fold (cond i). lia.
  Qed.

  Theorem small_list_limit_small_els i :
    small_list_limit i =
    small_els i ++ drop (S (cond_pos i)) (small_list_limit i).
  Proof. symmetry. apply firstn_skipn. Qed.

  Theorem small_els_in i a :
    a ∈ small_els i -> a ∈ M.
  Proof.
    intros I. apply (small_list_limit_in i).
    rewrite small_list_limit_small_els.
    apply elem_of_app. left. assumption.
  Qed.

  Theorem Sorted_lt_small_els i :
    Sorted lt (small_els i).
  Proof.
    assert (SS := Sorted_lt_small_list_limit i).
    unfold small_els.
    rewrite <- (take_drop (S (cond_pos i))) in SS.
    eapply Sorted_app_l. eassumption.
  Qed.

  Theorem small_els_spec i : term i ->
    forall x, x ∈ small_els i <->
    x ∈ M ∧ x <= cond i.
  Proof.
    intros T x.
    rewrite small_els_alt; [|assumption].
    rewrite elem_of_list_filter.
    split; intros [X1 X2].
    - split; [eapply small_list_limit_in|]; eassumption.
    - split; [assumption|].
      apply small_list_limit_all; [assumption|].
      apply Exists_exists. exists (cond i).
      split; [|assumption].
      now apply elem_of_list_lookup_total_2.
  Qed.

  Definition small_els_opt i :=
    if decide (term i) then Some (small_els i) else None.

  Definition gaps_alg i :=
    filter (.∉ (small_els i)) (seq 0 (cond i)).

  Theorem gaps_alg_correct i : term i ->
    forall x, x ∉ gaps_alg i <-> x ∈ M.
  Proof.
    intros T x. unfold gaps_alg.
    rewrite elem_of_list_filter.
    split.
    - intros Hx.
      apply not_and_r in Hx. destruct Hx.
      + apply dec_stable in H.
	apply small_els_spec in H; intuition.
      + rewrite elem_of_seq in H.
	eapply cond_ge_in; [eassumption|lia].
    - intros Mx [Sm Sc]. rewrite elem_of_seq in Sc.
      rewrite small_els_spec in Sm; [|assumption].
      apply not_and_r in Sm. destruct Sm; [contradiction|].
      lia.
  Qed.

  Definition gen_numerical_semigroup i : term i ->
    numerical_semigroup M.
  Proof.
    generalize (submonoid_generated gen). intros SM.
    intros T.
    apply (numerical_semigroup_intro _ (gaps_alg i)).
    - apply StronglySorted_Sorted, StronglySorted_filter.
      apply Sorted_StronglySorted; [intros?; lia|].
      apply Sorted_lt_seq.
    - intros x. split; apply gaps_alg_correct; assumption.
  Qed.

  (*Definition term_n := nhinv (length gen - 1) (replicate ((lim gen / mlt) + 1) (lookup_inv gen mlt)).

  Theorem unfinished x :
    sum_list_with (gen !!!.) (replicate ((x / mlt) + 1) (lookup_inv gen mlt)) = ((x / mlt) + 1) * mlt.
  Proof.
    rewrite sum_list_with_map.
    rewrite fmap_replicate.
    rewrite sum_list_replicate.
    rewrite lookup_lookup_inv; [lia|].
    apply list_min_in. apply gen_neq.
  Qed.

  Definition small_elements_term := small_elements term_n.
  Definition gaps_alg_term := gaps_alg term_n.*)

End generators.


Compute term [5;9;21] 60.
Compute small_els [5;9;21] 60.
Compute gaps_alg [5;9;21] 60.
