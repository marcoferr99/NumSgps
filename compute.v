From Coq Require Import Lia.
Require Export def list_alg.
 
Generalizable No Variables.
Generalizable Variables M.

Section generators.
  Context `{numerical_semigroup M}.
  Variables (gen : list nat).
  Hypothesis (G : generator gen).
  Local Notation mlt := (list_min gen).
  Hypothesis (m0 : mlt <> 0).
  Local Notation nh := (nh (length gen - 1)).

  Theorem gen_neq : gen <> [].
  Proof. intros C. subst. contradiction. Qed.

  Theorem length_gen_neq : length gen <> 0.
  Proof.
    intros C.
    apply gen_neq, length_zero_iff_nil. assumption.
  Qed.

  Definition nhsum n := sum_list_with (gen !!!.) (nh n).

  Theorem nh_Forall_gt n : Forall (gt (length gen)) (nh n).
  Proof.
    apply List.Forall_nth. intros.
    generalize (nh_Forall (length gen - 1) n). intros F.
    eapply Forall_nth with (d := d) in F; try eassumption.
    generalize length_gen_neq. lia.
  Qed.

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

  Theorem list_lookup_total_nth l i :
    l !!! i = nth i l 0.
  Proof.
    destruct (l !! i) eqn : E.
    - apply list_lookup_total_correct.
      rewrite nth_lookup. unfold default. rewrite E.
      reflexivity.
    - rewrite list_lookup_total_alt. unfold default.
      rewrite E. rewrite nth_lookup.
      unfold inhabitant, inhabited. rewrite E.
      reflexivity.
  Qed.

  Theorem nhsum_all a : a ∈ M -> exists n, nhsum n = a.
  Proof.
    intros Aa. destruct G as [_ G2].
    destruct (G2 a Aa) as [r x k Hr].
    set (l := flat_map (fun i => repeat (lookup_inv gen (x i)) (k i)) (seq 0 r)).
    set (ol := reverse (merge_sort le l)).
    destruct (nh_all (length gen - 1) ol) as [n Hn].
    - apply Forall_impl with (P := gt (length gen));
	try (intros; lia).
      subst ol. apply Forall_reverse.
      rewrite merge_sort_Permutation.
      unfold l. apply Forall_flat_map.
      apply Forall_forall. intros.
      apply Forall_repeat.
      apply lookup_inv_lt.
      apply Hr.
      apply elem_of_seq in H0. lia.
    - subst ol. apply Sorted_reverse. clear.
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
      + subst ol. eapply Permutation_trans; symmetry.
	* symmetry. apply reverse_Permutation.
	* symmetry. apply merge_sort_Permutation.
  Qed.

  Theorem nhsum_all_limit m a :
    a ∈ M -> a < nth_limit m ->
    exists n, n < m /\ nhsum n = a.
  Proof.
    intros Aa L.
    destruct (nhsum_all a) as [n Hn]; try assumption.
    exists n. split; try assumption. subst.
    destruct (le_gt_cases m n); try assumption.
    apply Arith_base.lt_not_le_stt in L.
    exfalso. apply L.
    eapply le_trans. 2:{ apply nhsum_le. }
    apply mul_le_mono_r. apply nh_le_length. assumption.
  Qed.

  Fixpoint small_list_aux n :=
    match n with
    | 0 => []
    | S n => nhsum n :: small_list_aux n
    end.

  Definition small_list n :=
    sorted_nodup (merge_sort le (small_list_aux n)).

  Definition small_list_limit n :=
    filter (fun x => x <= nth_limit n) (small_list n).

  Theorem small_list_limit_sorted n :
    Sorted le (small_list_limit n).
  Proof.
    apply StronglySorted_Sorted.
    apply StronglySorted_filter.
    apply Sorted_StronglySorted; [intros ?; lia|].
    unfold small_list.
    apply Sorted_le_sorted_nodup.
    apply Sorted_merge_sort.
    intros ?. lia.
  Qed.

  Theorem small_list_limit_sorted_lt n :
    StronglySorted lt (small_list_limit n).
  Proof.
    apply Sorted_StronglySorted; [intros ?; lia|].
    apply Sorted_le_lt. split.
    - apply small_list_limit_sorted.
    - apply NoDup_filter. apply sorted_nodup_NoDup.
      apply Sorted_merge_sort. intros ?. lia.
  Qed.

  Definition last_element_pos i :=
    find_seq (small_list_limit i) (list_min gen).

  Definition term i :=
    last_element_pos i < length (small_list_limit i).

  Definition last_element i :=
    small_list_limit i !!! last_element_pos i.

  Definition small_elements i :=
    firstn (S (last_element_pos i)) (small_list_limit i).


  Theorem small_list_all n a : a ∈ M -> a < nth_limit n ->
    a ∈ small_list n.
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

  Theorem small_list_limit_In n a :
    a ∈ small_list_limit n -> a ∈ M.
  Proof.
    intros I.
    unfold small_list_limit in I.
    apply elem_of_list_filter in I.
    destruct I as [_ I]. unfold small_list in I.
    apply sorted_nodup_in in I.
    rewrite merge_sort_Permutation in I.
    induction n; simpl in I; [easy|].
    set_unfold. destruct I; auto.
    subst. eapply nhsum_in; assumption.
  Qed.

  Theorem small_list_limit_small_elements i :
    small_list_limit i = small_elements i ++ skipn (S (last_element_pos i)) (small_list_limit i).
  Proof. symmetry. apply firstn_skipn. Qed.

  Theorem small_elements_In i a :
    a ∈ small_elements i -> a ∈ M.
  Proof.
    intros I. apply (small_list_limit_In i).
    rewrite small_list_limit_small_elements.
    apply elem_of_app. left. assumption.
  Qed.

(** [small_elements] contains all the elements of [A] that are less then or
    equal to [last_element]. *)

  Theorem small_elements_le_all i : term i ->
    forall a, a ∈ M -> a <= last_element i ->
    a ∈ small_elements i.
  Proof.
    intros T a Aa L.
    assert (Is : a ∈ small_list_limit i). {
      eapply small_list_limit_all; try eassumption.
      apply Exists_exists. exists (last_element i).
      split; try assumption. 
      apply elem_of_list_lookup_total_2. assumption.
    }
    apply elem_of_list_lookup_total_1 in Is.
    destruct Is as [n [Hn1 Hn2]]. subst a.
    unfold last_element in L.
    assert (n <= last_element_pos i). {
      apply nlt_ge. intros C.
      apply nlt_ge in L. apply L. clear L.
      repeat rewrite lookup_total_nth.
      apply StronglySorted_nth; try assumption.
      apply small_list_limit_sorted_lt.
    }
    unfold term in T.
    rewrite <- (firstn_skipn (S (last_element_pos i)) (small_list_limit i)).
    rewrite lookup_total_nth. rewrite app_nth1.
    - apply nth_elem_of. unfold small_elements.
      rewrite firstn_length_le; lia.
    - rewrite firstn_length_le; lia.
  Qed.

(** All the elements greater than or equal to last_element are in A. *)

  Theorem small_elements_ge_all i : term i ->
    forall a, a >= last_element i -> a ∈ M.
  Proof.
    intros T a L.
    replace a with (a - last_element i + last_element i);
      try lia.
    erewrite (Div0.div_mod (a - last_element i) (list_min gen)); try lia.
    rewrite <- add_assoc. apply ns_closed.
    + rewrite mul_comm.
      apply ns_mul_closed.
      destruct G as [G1 _].
      apply G1. simpl.
      apply list_min_in. apply gen_neq.
    + apply (find_seq_seq 0 (small_list_limit i) (list_min gen)) in T.
      eapply small_list_limit_In with (n := i);
	try assumption.
      rewrite <- (firstn_skipn (last_element_pos i) (small_list_limit i)).
      apply elem_of_app. right.
      rewrite <- (firstn_skipn (list_min gen)).
      apply elem_of_app. left.
      fold (last_element_pos i) in T. rewrite T.
      apply elem_of_seq.
      unfold last_element in *.
      rewrite lookup_total_nth in *.
      replace inhabitant with 0; [|reflexivity].
      split; try lia.
      apply (mod_upper_bound (a - last_element i) (list_min gen)) in m0.
      unfold last_element in *.
      rewrite lookup_total_nth in *.
      replace inhabitant with 0 in *; [|reflexivity].
      lia.
  Qed.

(** [last_element] is [0] or its predecessor is not in [A]. *)

  Theorem last_element_pred_not_in i : term i ->
    last_element i <> 0 -> (last_element i - 1) ∉ M.
  Proof.
    intros T N C.
    apply (small_elements_le_all i) in C;
      try assumption; try lia.
    assert (SS := small_list_limit_sorted_lt i).
    assert (last_element_pos i <> 0). {
      intros D. unfold last_element in *.
      rewrite D in *. clear D. apply N.
      inversion SS; try reflexivity. simpl.
      assert (I : 0 ∈ small_list_limit i). {
	eapply small_list_limit_all; try eassumption.
	- apply ns_zero.
	- rewrite <- H0. constructor. lia.
      }
      apply elem_of_list_lookup_total_1 in I.
      destruct I as [n [Ln Hn]].
      rewrite <- H0 in *. destruct n; try assumption.
      simpl in *.
      assert (a < 0); [|lia].
      eapply Forall_forall; try eassumption.
      rewrite <- Hn.
      apply elem_of_list_lookup_total_2.
      lia.
    }
    eapply (find_seq_first 0 (small_list_limit i) _ (last_element_pos i - 1)).
    - apply T.
    - fold (last_element_pos i). lia.
    - replace (S (last_element_pos i - 1)) with (last_element_pos i); try lia.
      assert (I : (last_element i - 1) ∈ (small_list_limit i)). {
	unfold small_elements in C.
	rewrite <- (firstn_skipn (S (last_element_pos i))).
	apply elem_of_app. intuition.
      }
      apply elem_of_list_lookup_total_1 in I.
      destruct I as [n [Hn1 Hn2]].
      assert (E : 0 = inhabitant); [reflexivity|].
      rewrite E at 2 3.
      repeat rewrite <- lookup_total_nth in *.
      fold (last_element i).
      replace (last_element_pos i - 1) with n; try lia.
      unfold last_element in Hn2. unfold term in T.
      assert (Ln : n < last_element_pos i). {
	assert (Ln : n <= last_element_pos i). {
	  eapply (StronglySorted_nth_c 0);
	    try eassumption.
	    repeat rewrite lookup_total_nth in *.
	    replace inhabitant with 0 in *; try reflexivity.
	    lia.
	}
	assert (n <> last_element_pos i); try lia.
	intros D. subst. fold (last_element i) in *. lia.
      }
      assert (S n = last_element_pos i); try lia.
      assert (LSn : S n < length (small_list_limit i));
	try lia.
      apply le_antisymm; try lia.
      eapply (StronglySorted_nth_c 0); try eassumption.
      unfold lt. intros D.
      rewrite E in D.
      repeat rewrite <- lookup_total_nth in D.
      fold (last_element i) in *.
      assert (nSn : n < S n); try lia.
      eapply (StronglySorted_nth 0) in nSn;
	try eassumption.
      rewrite E in *.
      repeat rewrite <- lookup_total_nth in *.
      lia.
  Qed.

  Theorem i_not_zero i : term i -> i <> 0.
  Proof.
    unfold term. intros T C. subst.
    simpl in T. lia.
  Qed.

  Theorem nth_limit_not_zero i : term i ->
    nth_limit i <> 0.
  Proof.
    unfold nth_limit. intros T C.
    apply eq_mul_0_r in C; try contradiction.
    destruct i.
    - apply i_not_zero in T. contradiction.
    - intros D. apply length_zero_iff_nil in D.
      simpl in D. eapply next_not_nil. eassumption.
  Qed.

  Theorem small_list_limit_not_nil i : term i ->
    small_list_limit i <> [].
  Proof.
    intros T C.
    generalize (small_list_all i 0). intros I.
    unfold small_list_limit in *.
    assert (N : 0 ∈ []); try inversion N.
    rewrite <- C. apply elem_of_list_filter.
    apply nth_limit_not_zero in T. split.
    - lia.
    - apply I; try apply ns_zero. lia.
  Qed.

End generators.

Compute small_elements [4;7;10] 100.

Definition mod_ge n a x :=
  let r := x - x mod n + a mod n in
  if x <=? r then r else r + n.

Theorem mod_ge_mod n a x : (mod_ge n a x) mod n = a mod n.
Proof.
  unfold mod_ge.
  assert ((x - x mod n) mod n = 0). {
    generalize (Div0.div_mod x n). intros D.
    replace (x - x mod n) with (n * (x / n)); try lia.
    rewrite mul_comm. apply Div0.mod_mul.
  }
  destruct (leb_spec x (x - x mod n + a mod n)).
  - rewrite <- Div0.add_mod_idemp_l. rewrite H.
    simpl. apply Div0.mod_mod.
  - rewrite <- add_assoc. rewrite <- Div0.add_mod_idemp_l.
    rewrite H. simpl.
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

Theorem find_congr_th n a l : n <> 0 -> l <> [] ->
  In (find_congr n a l) l \/
  find_congr n a l > nth (length l - 1) l 0.
Proof.
  intros n0 ln. induction l as [ | h t IH]; try contradiction.
  destruct t as [ | k t].
  - simpl in *.
    destruct (eq_dec h (mod_ge n a h)); [intuition | ].
    right. apply (mod_ge_ge _ a h) in n0. lia.
  - rewrite find_congr_rewrite.
    destruct (eqb_spec (h mod n) (a mod n)).
    + simpl. intuition.
    + remember (find_congr n a (k :: t)) as l.
      destruct IH; try discriminate.
      * left. simpl in *. intuition.
      * right. simpl in *.
	rewrite sub_0_r in H. assumption.
Qed.


Compute term [5;9;21] 60.
Compute small_elements [5;9;21] 60.
Compute find_congr 5 4 (small_elements [5;9;21] 100).

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
	  (last_element_pos gen i) in H0.
	-- unfold small_elements in H0 at 2.
	   rewrite nth_firstn in H0.
	   destruct (ltb_spec (last_element_pos gen i) (S (last_element_pos gen i))); try lia.
	   fold (last_element gen i) in H0. lia.
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
