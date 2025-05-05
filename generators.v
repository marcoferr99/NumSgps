From Coq Require Import Euclid Lia.
Require Export apery list_alg.
 
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
      + f_equal. Search list_max.
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

  Theorem small_elements_spec i :
    term i -> small_elements_list (small_elements i).
  Proof.
    intros T. split.
    - assert (SS := Sorted_lt_small_list_limit i).
      unfold small_elements.
      rewrite <- (take_drop (S (cond_pos i))) in SS.
      eapply Sorted_app_l. eassumption.
    - intros x.
      rewrite small_elements_alt; [|assumption].
      rewrite elem_of_list_filter.
      split; intros [X1 X2].
      + split; [eapply small_list_limit_in; eassumption|].
	erewrite <- cond_conductor; eassumption.
      + rewrite cond_conductor; [|assumption].
	split; [assumption|].
	apply small_list_limit_all; [assumption|].
	apply Exists_exists. exists conductor.
	split; [|assumption].
	erewrite <- cond_conductor; [|eassumption].
	now apply elem_of_list_lookup_total_2.
  Qed.

  Definition small_elements_opt i :=
    if decide (term i) then Some (small_elements i) else None.


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
    apply (div_le_mono y x n) in n0; [|lia].
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
      destruct H. rewrite H0.
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

  Definition apery_alg n l := apery_alg_aux n n l.

  Theorem apery_alg_correct n l : n <> 0 ->
    small_elements_list l -> apery_l M n (apery_alg n l).
  Proof.
    intros n0 L. unfold apery_alg, apery_l.
    assert (forall m, apery_l_aux M n m (apery_alg_aux n m l)); [|auto].
    induction m; [constructor|].
    assert (l0 : l <> []). {
      intros N. assert (0 ∈ []); [|easy].
      rewrite <- N. apply L. split; [apply ns_zero|lia].
    }
    assert (E : l !!! (length l - 1) = conductor). {
      destruct L as [SS L].
      edestruct (elem_of_list_split l) as (l1 & l2 & Hl).
      * apply L.
	split; [apply conductor_le_in|]; apply le_refl.
      * rewrite Hl in SS.
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
	     rewrite length_app. simpl.
	     rewrite lookup_total_app_r; [|lia].
	     rewrite lookup_total_cons_ne_0; [|lia].
	     apply elem_of_list_lookup_total_2.
	     simpl. lia.
	   }
	   assert (l !!! (length l - 1) <= conductor);
	     [|lia].
	     apply L.
	     apply elem_of_list_lookup_total_2.
	     destruct (nil_or_length_pos l);
	       [contradiction|lia].
    }
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

Theorem find_congr_apery_w A `{numerical_semigroup A}
  gen i n (n0 : n <> 0) :
  generator A (Inl gen) ->
  term gen i -> list_min gen <> 0 ->
  forall x, find_congr n (proj1_sig x) (small_elements gen i) = apery_w A n n0 x.
Proof.
  intros G T M0 x.
  destruct (apery_w_spec A n n0) as [_ P].
  apply P. clear P.
  assert (SN : small_elements gen i <> []). {
    unfold small_elements. intros C.
    remember (small_list_limit gen i) as sl.
    destruct sl.
    - eapply small_list_limit_not_nil; try eassumption.
      auto.
    - simpl in C. discriminate.
  }
  destruct x as [x px]. simpl. split.
  - split.
    + destruct (find_congr_th n x (small_elements gen i));
	try assumption.
      * eapply small_elements_In; eassumption.
      * eapply small_elements_ge_all; try eassumption.
	replace (length (small_elements gen i) - 1) with
	  (cond_pos gen i) in H0.
	-- unfold small_elements in H0 at 2.
	   rewrite nth_firstn in H0.
	   destruct (ltb_spec (cond_pos gen i) (S (cond_pos gen i))); try lia.
	   fold (cond gen i) in H0. lia.
	-- unfold small_elements.
	   rewrite firstn_length_le; try lia.
	   unfold term in T. lia.
    + remember (small_elements gen i) as l eqn : E.
      clear E. induction l; try contradiction.
      destruct l.
      * simpl. apply mod_ge_mod.
      * rewrite find_congr_rewrite.
	destruct (eqb_spec (a mod n) (x mod n));
	  try assumption.
	apply IHl. discriminate.
  - intros m [Am Cm].

End generators.

Compute small_elements_opt [4;7;10] 40.




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



Compute term [5;9;21] 60.
Compute small_elements [5;9;21] 60.
Compute find_congr 5 4 (small_elements [5;9;21] 100).
