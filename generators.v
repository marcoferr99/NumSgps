From Coq Require Import Euclid Lia.
Require Export def list_alg.
Require Import gcd.
 
Generalizable No Variables.
Generalizable Variables C M.


Section generators.
  Context `{numerical_semigroup C M}.
  Variables (gen : list nat).
  Hypothesis (G : generator gen).
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
      * destruct G as [G1 _]. apply G.
	apply elem_of_list_lookup_total_2. lia.
      * apply IH; auto.
  Qed.

  Theorem nhsum_all a : a ∈ M -> exists n, nhsum n = a.
  Proof.
    intros Aa. destruct G as [_ G2].
    destruct (G2 a Aa) as [r x k Hr].
    set (l := flat_map (fun i => repeat (lookup_inv gen (x i)) (k i)) (seq 0 r)).
    set (ol := reverse (merge_sort le l)).
    destruct (nh_all (length gen - 1) ol) as [n Hn].
    - apply Forall_impl with (P := gt (length gen));
	[|intros; lia].
      subst ol. apply Forall_reverse.
      rewrite merge_sort_Permutation.
      unfold l. apply Forall_flat_map.
      apply Forall_forall. intros y Hy.
      apply Forall_repeat. apply lookup_inv_lt. apply Hr.
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
    simpl in *. set_unfold. destruct Ha; [|auto].
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
    intros T a L.
    replace a with (a - cond i + cond i); [|lia].
    rewrite (Div0.div_mod (a - cond i) (list_min gen)).
    rewrite <- add_assoc. apply ns_closed.
    + rewrite mul_comm. apply ns_mul_closed.
      destruct G as [G1 _]. apply G1.
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

  Theorem cond_conductor i : term i -> cond i = conductor.
  Proof.
    intros T. unfold conductor.
    destruct gaps eqn : Eg.
    - destruct (eq_dec (cond i) 0) as [|N]; [assumption|].
      apply cond_pred_notin in N; [|assumption].
      exfalso. apply N. apply elem_of_gaps. now rewrite Eg.
    - rewrite <- Eg. destruct (cond i) as [|c] eqn : E.
      + absurd (n ∈ gaps).
	* apply elem_of_gaps.
	  eapply cond_ge_in; [eassumption|]. lia.
	* rewrite Eg. left.
      + f_equal.
	apply le_antisymm.
	* destruct (le_gt_cases c (list_max gaps));
	    [assumption|].
	  exfalso. eapply cond_pred_notin;
	    [eassumption|lia|].
	  apply conductor_le_in.
	  unfold conductor. rewrite Eg. rewrite <- Eg. lia.
	* apply list_max_le. apply Forall_forall.
	  intros x Hx.
	  apply dec_stable. intros N.
	  apply elem_of_gaps' in Hx. apply Hx.
	  eapply cond_ge_in; [eassumption|].
	  lia.
  Qed.

  Definition small_elements i :=
    take (S (cond_pos i)) (small_list_limit i).

  Theorem small_elements_alt i : term i ->
    small_elements i =
    filter (fun x => x <= cond i) (small_list_limit i).
  Proof.
    intros T. unfold small_elements. apply Sorted_lt_eq.
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

  Theorem small_list_limit_small_elements i :
    small_list_limit i =
    small_elements i ++ drop (S (cond_pos i)) (small_list_limit i).
  Proof. symmetry. apply firstn_skipn. Qed.

  Theorem small_elements_in i a :
    a ∈ small_elements i -> a ∈ M.
  Proof.
    intros I. apply (small_list_limit_in i).
    rewrite small_list_limit_small_elements.
    apply elem_of_app. left. assumption.
  Qed.

  Theorem Sorted_lt_small_elements i :
    Sorted lt (small_elements i).
  Proof.
    assert (SS := Sorted_lt_small_list_limit i).
    unfold small_elements.
    rewrite <- (take_drop (S (cond_pos i))) in SS.
    eapply Sorted_app_l. eassumption.
  Qed.

  Theorem small_elements_small_elements_set i : term i ->
    forall x, x ∈ small_elements i <->
    x ∈ small_elements_set.
  Proof.
    intros T x.
    rewrite small_elements_alt; [|assumption].
    rewrite elem_of_list_filter.
    split; intros [X1 X2].
    - split; [eapply small_list_limit_in; eassumption|].
      erewrite <- cond_conductor; eassumption.
    - rewrite cond_conductor; [|assumption].
      split; [assumption|].
      apply small_list_limit_all; [assumption|].
      apply Exists_exists. exists conductor.
      split; [|assumption].
      erewrite <- cond_conductor; [|eassumption].
      now apply elem_of_list_lookup_total_2.
  Qed.

  Definition small_elements_opt i :=
    if decide (term i) then Some (small_elements i) else None.

  Definition gaps_alg i :=
    filter (.∉ (small_elements i)) (seq 0 (cond i)).

  Theorem gaps_alg_correct i : term i -> gaps_alg i = gaps.
  Proof.
    intros T. apply Sorted_lt_eq.
    - apply StronglySorted_Sorted, StronglySorted_filter.
      apply Sorted_StronglySorted; [intros ?; lia|].
      apply Sorted_lt_seq.
    - apply sorted_gaps.
    - intros x. unfold gaps_alg.
      rewrite elem_of_list_filter, elem_of_gaps'.
      split.
      + intros [Sx Hx] N.
	destruct (le_gt_cases x conductor).
	* apply Sx.
	  apply small_elements_small_elements_set;
	    [assumption|].
	  unfold small_elements_set. set_unfold. auto.
	* apply elem_of_seq in Hx.
	  erewrite <- cond_conductor in H7; [|eassumption].
	  lia.
      + intros Hx. split.
	* intros N.
	  apply small_elements_small_elements_set in N;
	    [|assumption].
	  now destruct N.
	* apply elem_of_seq.
	  rewrite cond_conductor; [|assumption].
	  destruct (le_gt_cases conductor x); [|lia].
	  exfalso. apply Hx. now apply conductor_le_in.
  Qed.


  Definition term_n := nhinv (length gen - 1) (replicate ((lim gen / mlt) + 1) (lookup_inv gen mlt)).

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
  Definition gaps_alg_term := gaps_alg term_n.

End generators.


Compute term [5;9;21] (term_n [5;9;21]).
Compute small_elements_term [5;9;21].
Compute gaps_alg_term [5;9;21].
