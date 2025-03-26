From Coq Require Import Lia Mergesort Permutation Sorted.
Require Export def.
 

Fixpoint olist_add max l :=
  match l with
  | [] => [0]
  | h :: t => if h <? max then S h :: t else
      match olist_add max t with
      | [] => []
      | h :: t => h :: h :: t
      end
  end.

Theorem olist_add_0 l : olist_add 0 l = 0 :: repeat 0 (length l).
Proof.
  induction l; try reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed.

Theorem olist_add_not_nil max l : olist_add max l <> [].
Proof.
  induction l.
  - simpl. intros. discriminate.
  - simpl. unfold "<?". destruct (leb_spec0 (S a) max).
    + intros. discriminate.
    + remember (olist_add max l) as h. destruct h.
      * assumption.
      * discriminate.
Qed.

Theorem olist_add_m m l n :
  olist_add (S m) (repeat (S m) n ++ m :: l) = repeat (S m) n ++ olist_add (S m) (m :: l).
Proof.
  intros. induction n; try reflexivity.
  remember (S m) as sm. remember (m :: l) as ml.
  simpl. unfold "<?".
  destruct (leb_spec0 (S sm) sm); try lia.
  rewrite IHn.
  remember (repeat sm n ++ olist_add sm ml) as h.
  destruct h.
  - exfalso. eapply olist_add_not_nil. apply IHn.
  - f_equal. destruct n.
    + simpl in *. subst. simpl in IHn. unfold "<?" in IHn.
      destruct (leb_spec0 (S m) (S m)); try lia.
      injection IHn. auto.
    + simpl in Heqh. injection Heqh. auto.
Qed.

Fixpoint olist max l n :=
  match n with
  | 0 => l
  | S n => olist_add max (olist max l n)
  end.

  (*Theorem t1 max l : forall n, n <= max ->
  exists m, olist max l m = n :: l.
Proof.
  intros.
  remember (length l) as ln.
  generalize dependent l. generalize dependent n. induction ln.
  - intros.
    symmetry in Heqln. apply length_zero_iff_nil in Heqln.
    subst. exists (S n). simpl.
    induction n; try reflexivity.
    simpl. rewrite IHn; try lia. simpl.
    replace (n <? max) with (true); try reflexivity.
    symmetry. apply Compare_dec.leb_correct. assumption.
  - intros.
  intros. destruct l.
  - exists (S n). induction n; try reflexivity.
    simpl in *. rewrite IHn; try lia.
    simpl. replace (n <? max) with (true); try reflexivity.
    symmetry. apply Compare_dec.leb_correct. assumption.
  - destruct (classic (n = n0)).
    + subst. exists 1. simpl.
      replace (n0 <? max) with false.*)

Theorem olist_add_le max l :
  Forall (fun x => x <= max) l ->
  Forall (fun x => x <= max) (olist_add max l).
Proof.
  intros F. induction l.
  - simpl. constructor; [lia | constructor].
  - destruct (le_gt_cases max a).
    + inversion F. subst.
      replace a with max; try lia. simpl.
      replace (max <? max) with false.
      * remember (olist_add max l) as ls.
	destruct ls; [constructor | ].
	constructor; auto.
	apply IHl in H3. inversion H3. assumption.
      * symmetry. apply Compare_dec.leb_correct_conv. lia.
    + simpl. apply ltb_lt in H as L. rewrite L.
      constructor; try lia. inversion F. assumption.
Qed.

Fixpoint olist_nth max n :=
  match n with
  | 0 => []
  | S n => olist_add max (olist_nth max n)
  end.

  (*set (mlength := fun m l ml => ml <= length l /\ forall k, k < length l -> nth k l 0 >= m <-> k < ml).
  assert (ML1 : forall l n m nl ml, mlength n l nl -> mlength m l ml -> n <= m -> ml <= nl). {
    intros. subst mlength. simpl in *. destruct H, H0.
    destruct ml; try lia. apply H2; try lia.
    eapply le_trans.
    - apply H1.
    - apply H3; lia.
  }
  assert (ML2 : forall l k1 k2 n, mlength n l (S k1) -> mlength (S n) l k2 -> nth k1 l 0 = n <-> k2 < S k1). {
    intros. split; intros.
    - unfold mlength in H, H0.
      destruct (eq_dec k1 (length l)).
      + subst. destruct H0. lia.
      + destruct (le_gt_cases (S k1) k2); try assumption.
        assert (nth k1 l 0 >= S n). {
	  apply H0; try lia.
	}
	subst. lia.
    - unfold mlength in H, H0.
      apply le_antisymm.
      + destruct (le_gt_cases (nth k1 l 0) n);
	  try assumption.
	  apply H0 in H2; lia.
      + apply H; lia.
  }
  assert (ML3 : forall l k, mlength 0 l k <-> k = length l). {
    intros. split; intros.
    - unfold mlength in H. apply le_antisymm; try apply H.
      destruct H. remember (length l) as ln.
      destruct ln; try lia. apply H0; lia.
    - subst. unfold mlength. split; auto.
      intros. split; lia.
  }
  assert (MLa : forall l1 l2 m k1 k2, StronglySorted ge (l1 ++ l2) -> mlength m l1 k1 -> mlength m l2 k2 -> mlength m (l1 ++ l2) (k1 + k2)). {
    intros. unfold mlength. split.
    - rewrite length_app. destruct H0, H1. lia.
    - intros. split; intros.
      + destruct H0, H1.
	destruct (le_gt_cases (length l1) k).
	* rewrite app_nth2 in H3; try lia.
	  rewrite length_app in H2.
	  assert (length l1 <= k1). {
	    remember (length l1) as n. destruct n; try lia.
	    apply H4; try lia.
	    eapply le_trans; try eassumption.
	    rewrite Heqn. rewrite <- app_nth2; try lia.
	    rewrite <- (app_nth1 l1 l2); try lia.
	    apply LS; try assumption;
	      try rewrite length_app; lia.
	  }
	  apply H5 in H3; lia.
	* rewrite app_nth1 in H3; try lia.
	  apply H4 in H3; lia.
      + destruct H0, H1.
	destruct (le_gt_cases (length l1) k).
	* rewrite app_nth2; try lia.
	  apply H5; lia.
	* destruct (le_gt_cases k1 k).
	  -- assert (nth k l1 0 < m). {
	      destruct (le_gt_cases m (nth k l1 0));
		try assumption.
		apply H4 in H8; lia.
	     }
	     replace k2 with 0 in *; try lia.
	     apply le_antisymm; try lia.
	     destruct (le_gt_cases k2 0); try assumption.
	     apply H5 in H9; try lia.
	     rewrite <- app_nth1 with (l' := l2) in H8; try lia.
	     replace 0 with (length l1 - length l1) in H9 at 1; try lia.
	     rewrite <- app_nth2 in H9; try lia.
	     assert (k <= length l1); try lia.
	     eapply LS in H10; try eassumption;
	      try rewrite length_app; lia.
	  -- rewrite app_nth1; try lia. apply H4; lia.
  }*)

Theorem t2 max : forall l, Forall (fun x => x <= max) l ->
  StronglySorted ge l -> exists n, olist_nth max n = l.
Proof.
  assert (IF : forall T (l : list T) k, incl (firstn k l) l). {
    intros. rewrite <- firstn_skipn with (n := k).
    apply incl_appl. apply incl_refl.
  }
  assert (IS : forall T (l : list T) k, incl (skipn k l) l). {
    intros. rewrite <- firstn_skipn with (n := k).
    apply incl_appr. apply incl_refl.
  }
  assert (SK : forall l n, n < length l -> skipn n l = nth n l 0 :: skipn (S n) l). {
    induction l; try (simpl; lia).
    intros. destruct n; try reflexivity.
    rewrite skipn_cons.
    simpl in H. rewrite IHl; try lia.
    rewrite skipn_cons. reflexivity.
  }
  assert (FS : forall l n, n < length l -> firstn (S n) l = firstn n l ++ [nth n l 0]). {
    intros. rewrite firstn_skipn_rev.
    rewrite <- rev_involutive. f_equal.
    rewrite rev_app_distr. simpl.
    rewrite SK; try (rewrite rev_length; lia).
    rewrite rev_nth; try lia.
    repeat f_equal; try lia.
    rewrite skipn_rev. repeat f_equal. lia.
  }
  assert (LSr : forall n m, LocallySorted ge (repeat n m)). {
    intros. induction m; try constructor.
    simpl. remember (repeat n m) as r. destruct r.
    - constructor.
    - constructor; try assumption.
      destruct m; try discriminate.
      injection Heqr. lia.
  }
  assert (LS : forall l a h, LocallySorted ge (l ++ [a]) -> LocallySorted ge (a :: h) -> LocallySorted ge (l ++ a :: h)). {
    induction l; intros; try assumption.
    simpl. destruct l.
    - simpl. constructor; try assumption.
      inversion H. assumption.
    - simpl. constructor.
      + apply IHl; try assumption. inversion H; assumption.
      + inversion H. assumption.
  }
  assert (LSl : forall l, LocallySorted ge l -> forall n1 n2, n1 < length l -> n2 < length l -> n1 <= n2 -> nth n2 l 0 <= nth n1 l 0). {
    intros l L.
    apply Sorted_LocallySorted_iff in L.
    apply Sorted_StronglySorted in L.
    2: { unfold Transitive. lia. }
    induction l; intros.
    - simpl in *. lia.
    - inversion L. subst. destruct n1, n2; simpl; try lia.
      + simpl in H0.
        eapply (Forall_nth (ge a) l) in H5;
	  try eassumption.
	lia.
      + apply IHl; simpl in *; try assumption; lia.
  }
  assert (LSp : forall l a, LocallySorted ge (l ++ [S a]) -> LocallySorted ge (l ++ [a])). {
    clear. induction l.
    - intros. constructor.
    - intros. simpl. destruct l.
      + constructor; try constructor.
	inversion H. lia.
      + simpl. inversion H. subst. apply IHl in H2.
	constructor; assumption.
  }
  assert (LSp2 : forall l b a, a <= b -> LocallySorted ge (l ++ [b]) -> LocallySorted ge (l ++ [a])). {
    induction b; intros.
    - replace a with 0; try lia. assumption.
    - destruct (eq_dec a (S b)).
      + subst. assumption.
      + apply IHb; try (apply LSp; assumption).
	lia.
  }
  assert (LSa : forall l h, LocallySorted ge (l ++ h) -> LocallySorted ge h). {
    intros. induction l; try assumption.
    inversion H.
    - simpl in *. apply IHl. inversion H; try constructor.
      assumption.
    - apply IHl. inversion H; try constructor. assumption.
  }
  assert (LSal : forall l h, LocallySorted ge (l ++ h) -> LocallySorted ge l). {
    clear. intros. induction l.
    - constructor.
    - destruct l; constructor.
      + apply IHl. simpl in H. inversion H. assumption.
      + inversion H. assumption.
  }
  set (
    ml := fix ml m l :=
      match l with
      | [] => 0
      | h :: t => let x := ml m t in
	  if m <=? h then S x else x
      end
  ).
  assert (ml_0 : forall l, ml 0 l = length l). {
    induction l; simpl; auto.
  }
  assert (M1 : forall l n m, n <= m -> ml m l <= ml n l). {
    intros. induction l; auto. simpl.
    destruct (leb_spec0 m a), (leb_spec0 n a); lia.
  }
  assert (ml_app : forall l h m, ml m (l ++ h) = ml m l + ml m h). {
    intros. induction l; try reflexivity.
    simpl. destruct (leb_spec0 m a); lia.
  }
  assert (M2 : forall l n a, LocallySorted ge (a :: l) -> a < n -> ml n (a :: l) = 0). {
    induction l; intros.
    - simpl. destruct (leb_spec0 n a); lia.
    - simpl. destruct (leb_spec0 n a0); try lia.
      apply IHl; inversion H;
	try constructor; try assumption; lia.
  }
  assert (M3 : forall l m n, LocallySorted ge l -> n < ml m l -> nth n l 0 >= m). {
    induction l; intros.
    - simpl in *. lia.
    - simpl. destruct n.
      + simpl in H0. destruct (leb_spec0 m a); try lia.
	eapply le_trans.
	* apply IHl.
	  -- inversion H; [constructor | assumption].
	  -- apply H0.
	* inversion H.
	  -- subst. simpl in *. lia.
	  -- subst. simpl. assumption.
      + apply IHl.
	* inversion H; [constructor | assumption].
	* simpl in H0. destruct (leb_spec0 m a); lia.
  }
  assert (M4 : forall l n m, LocallySorted ge l -> n < length l -> nth n l 0 < m -> ml m l = ml m (firstn n l)). {
    intros. rewrite <- (firstn_skipn n l) at 1.
    rewrite ml_app. rewrite <- add_0_r. f_equal.
    rewrite SK; try assumption.
    apply M2; try assumption.
    rewrite <- SK; try assumption.
    eapply LSa. rewrite firstn_skipn. assumption.
  }
  assert (M5 : forall l a h m, a < m -> ml m (l ++ a :: h) = ml m (l ++ h)). {
    intros. induction l.
    - simpl. destruct (leb_spec0 m a); lia.
    - simpl. destruct (leb_spec0 m a0); lia.
  }
  assert (M6 : forall l a h m, a >= m -> ml m (l ++ a :: h) = S (ml m (l ++ h))). {
    intros. induction l.
    - simpl. destruct (leb_spec0 m a); lia.
    - simpl. destruct (leb_spec0 m a0); lia.
  }
  assert (M7 : forall l m n, LocallySorted ge l -> n < length l -> n >= ml m l -> nth n l 0 < m). {
    induction l; intros.
    - simpl in *. lia.
    - simpl in *. destruct (leb_spec0 m a).
      + destruct n; try lia. apply IHl; try lia.
	inversion H; [constructor | assumption].
      + destruct n; try lia.
	assert (0 <= S n); try lia.
	eapply (LSl (a :: l) _ 0 (S n)) in H2.
	* simpl in H2. lia.
	* simpl. lia.
	* simpl. lia.
  }
  set (
    f m k :=
      forall l, LocallySorted ge l -> Forall (ge max) l ->
      (forall i, i <= m -> ml i l = k i) ->
      exists n, olist_nth max n = l
  ).
  set (
    P m := forall (k : nat -> nat), f (max - m) k ->
    f (max - m) (fun i => if i =? max - m then S (k i) else k i)
  ).

  assert (forall m, P m). {
    subst P f. simpl. intros m k H l L F Hl.
    set (p := k (max - m)).
    assert (Ep : S p = ml (max - m) l). {
      specialize Hl with (max - m).
      destruct (eqb_spec (max - m) (max - m)); lia.
    }
    assert (p_le : p < length l). {
      unfold "<". rewrite <- ml_0.
      rewrite Ep. apply M1. lia.
    }
    generalize (firstn_skipn p l). intros El.
    rewrite SK in El; try assumption.
    assert (fle : forall i, i <= max - m -> Forall (le i) (firstn p l)). {
      intros. apply Forall_nth. intros.
      rewrite (nth_indep _ _ 0); try assumption.
      rewrite firstn_length_le in H1; try lia.
      rewrite nth_firstn.
      unfold "<?". destruct (leb_spec0 (S i0) p); try lia.
      unfold le.
      apply M3; try assumption.
      eapply (M1 l) in H0. lia.
    }
    assert (FrS : Forall (gt (max - m)) (skipn (S p) l)). {
      apply Forall_nth. intros.
      rewrite (nth_indep _ _ 0); try assumption. clear d.
      rewrite nth_skipn. apply M7; try assumption; try lia.
      rewrite length_skipn in H0. lia.
    }
    set (pr := match max - m with 0 => [] | S n => [n] end).
    set (h := repeat max p ++ pr ++ skipn (S p) l).
    assert (eh : exists n, olist_nth max n = h). {
      assert (Lh : LocallySorted ge h). {
	subst h.
        remember (max - m) as mm. destruct mm.
	- subst pr. rewrite app_nil_l.
	  remember (skipn (S p) l) as s eqn : E. clear E.
	  destruct s.
	  + rewrite app_nil_r. apply LSr.
	  + inversion FrS. lia.
	- subst pr. apply LS.
	  + apply LSp2 with max; try lia.
	    replace [max] with (repeat max 1);
	      try reflexivity.
	      rewrite <- repeat_app. apply LSr.
	  + remember (skipn (S p) l) as s eqn : E.
	    destruct s; constructor.
	    * rewrite E.
	      rewrite <- (firstn_skipn (S p)) in L.
	      apply LSa in L. assumption.
	    * inversion FrS. lia.
      }
      apply H; try assumption.
      - subst h. apply Forall_app. split.
	+ clear.
	  induction p; simpl; constructor;
	    [lia | assumption].
	+ apply Forall_app. split.
	  * subst pr. remember (max - m) as mm.
	    destruct mm; constructor; [lia | constructor].
	  * rewrite <- (firstn_skipn (S p)) in F.
	    apply Forall_app in F. apply F.
      - intros i Hil. apply Hl in Hil as Hi.
	remember (max - m) as mm. destruct mm.
	+ subst p pr h.
	  destruct (eqb_spec i 0); try lia. subst.
	  remember (skipn (S (k 0)) l) as s eqn : E.
	  clear E.
	  destruct s.
	  -- repeat rewrite app_nil_r in *.
	     remember (k 0) as x. clear.
	     induction x; try reflexivity.
	     simpl. lia.
	  -- inversion FrS. lia.
	+ destruct (eqb_spec i (S mm)).
	  * subst. apply le_antisymm.
	    -- destruct (le_gt_cases (ml (S mm) h) (k (S mm))) as [C | C]; try assumption.
		apply M3 in C; try assumption.
		destruct (Compare_dec.gt_dec (S mm) (nth (k (S mm)) h 0)); try lia.
		exfalso. apply n. clear n C. unfold h.
		rewrite app_nth2; rewrite repeat_length;
		  try lia.
		subst p. rewrite sub_diag.
		subst pr. simpl. lia.
	    -- assert (length l = length h). {
		 rewrite <- El. subst h.
		 repeat rewrite length_app.
		 remember (skipn (S p) l) as s. simpl.
		 f_equal.
		 rewrite firstn_length_le; try lia.
		 symmetry. apply repeat_length.
	       }
	       destruct (le_gt_cases (k (S mm)) (ml (S mm) h)) as [C | C]; try assumption.
		unfold "<" in C. remember (k (S mm)) as ki.
		destruct ki; try (subst; lia).
		apply le_S_n in C.
		apply M7 in C; try assumption; try lia.
		unfold h in C. rewrite app_nth1 in C.
		++ rewrite nth_repeat_lt in C; lia.
		++ rewrite repeat_length. lia.
	  * subst pr. rewrite <- Hi, <- El. unfold h.
	    remember (skipn (S p) l) as s.
	    replace (nth p l 0 :: s) with ([nth p l 0] ++ s); try reflexivity.
	    repeat rewrite ml_app. f_equal.
	    -- replace (ml i (firstn p l)) with p.
	       ++ rewrite Heqmm in *.
		  generalize F Hil. clear. intros F Hil.
		  induction p; try reflexivity.
		  simpl. destruct (leb_spec0 i max); lia.
	       ++ subst p.
		  apply fle in Hil.
		  remember (firstn (k (S mm)) l) as f.
		  assert (length f = k (S mm)). {
		    subst f. apply firstn_length_le. lia.
		  }
		  generalize H0 Hil. clear. intros.
		  remember (k (S mm)) as n. clear Heqn.
		  generalize dependent n.
		  induction f; intros.
		  --- simpl in *. lia.
		  --- simpl. destruct (leb_spec0 i a).
		      +++ destruct n.
			  *** simpl in H0. lia.
			  *** f_equal. apply IHf.
			      ---- inversion Hil. assumption.
			      ---- simpl in H0. lia.
		      +++ inversion Hil. lia.
	    -- f_equal. simpl.
	       destruct (leb_spec0 i mm), (leb_spec0 i (nth p l 0)); try lia.
	       exfalso. apply n0. subst p.
	       apply M3; try assumption. rewrite Hi.
	       apply (M1 l) in Hil. lia.
    }
    assert (forall s, olist_add max (repeat max p ++ pr ++ s) = repeat (max - m) (S p) ++ s). {
      subst h. destruct max as [ | max].
      + simpl in pr. subst pr.
	remember (skipn (S p) l) as s eqn : E. clear E.
	destruct s.
	* repeat rewrite app_nil_r. rewrite olist_add_0.
	  rewrite repeat_length. rewrite <- El.
	  rewrite FR. Search repeat.
	  assert ([nth p l 0] = repeat 0 1). {
	    simpl. f_equal.
	    eapply Forall_nth in F; try eassumption.
	    - apply le_antisymm; [eassumption | lia].
	  }
	  rewrite H0. rewrite <- repeat_app.
	  rewrite add_comm. reflexivity.
	* inversion FrS. lia.
      + simpl in pr. subst pr.
	remember (skipn (S p) l) as s. simpl.
	rewrite olist_add_m. rewrite <- El. rewrite FR.
	f_equal. simpl. unfold "<?".
	destruct (leb_spec0 (S max) (S max)); try lia.
	f_equal. apply le_antisymm.
	* apply M3; try assumption. subst p.
	  rewrite sub_0_r in *. lia.
	* eapply Forall_nth in F; eassumption.
    }
    induction m.
    - destruct eh as [n Hn].
      exists (S n). simpl. rewrite Hn. clear Hn.
      assert (FR : firstn p l = repeat max p). {
	apply nth_ext with 0 0.
	- rewrite firstn_length_le; try lia.
	  symmetry. apply repeat_length.
	- intros. rewrite firstn_length_le in H0; try lia.
	  rewrite nth_repeat_lt; try lia.
	  rewrite <- El in F.
	  apply Forall_app in F as [F _].
	  + eapply Forall_nth in F.
	    * eapply Forall_nth in fle.
	      -- apply le_antisymm; eassumption.
	      -- lia.
	      -- rewrite firstn_length_le; lia.
	    * rewrite firstn_length_le; lia.
      }
      subst h. destruct max as [ | max].
      + simpl in pr. subst pr.
	remember (skipn (S p) l) as s eqn : E. clear E.
	destruct s.
	* repeat rewrite app_nil_r. rewrite olist_add_0.
	  rewrite repeat_length. rewrite <- El.
	  rewrite FR. Search repeat.
	  assert ([nth p l 0] = repeat 0 1). {
	    simpl. f_equal.
	    eapply Forall_nth in F; try eassumption.
	    - apply le_antisymm; [eassumption | lia].
	  }
	  rewrite H0. rewrite <- repeat_app.
	  rewrite add_comm. reflexivity.
	* inversion FrS. lia.
      + simpl in pr. subst pr.
	remember (skipn (S p) l) as s. simpl.
	rewrite olist_add_m. rewrite <- El. rewrite FR.
	f_equal. simpl. unfold "<?".
	destruct (leb_spec0 (S max) (S max)); try lia.
	f_equal. apply le_antisymm.
	* apply M3; try assumption. subst p.
	  rewrite sub_0_r in *. lia.
	* eapply Forall_nth in F; eassumption.
    - simpl in IHm.


      + set (j := repeat (max - S m) (S p) ++ skipn (S p) l).
	assert (exists n, olist_nth max n = j). {
	  clear IHm. destruct eh as [n Hn]. exists (S n).
	  simpl. rewrite Hn. subst h.
	}

	assert (nth (S p) l 0 = max - m). {
	  apply le_antisymm.
	  - assert (S p >= ml (max - m) l); try lia.
	    apply M7 in H0.
	  - assert (nth p l 0 < S (max - m)). {
	      apply M7; try assumption.
	    }
	  - assert (ml (max - m) l > p); try lia.
	    unfold ">", "<" in H0. rewrite Ep in H0.
	    apply M7 in H0.
	    + subst p. lia.
	}
	destruct (eq_dec max m).
	* subst. rewrite sub_diag in *.
	  specialize Hl with 0. simpl in Hl. subst p.
	  rewrite sub_diag in *. clear Hl.
	  rewrite ml_0 in Ep. clear p_le.
	  rewrite Ep in El. rewrite skipn_all in El.
	  assert (S m - m = 1); try lia.
	  rewrite H0 in IH. unfold f in IH. simpl in IH.
	assert (Forall (gt (nth p l 0)) 
	remember (nth p l 0) as x. destruct x.
	*
	assert (El : l = firstn p l ++ skipn
	Search firstn skipn.
  }
  2:{ specialize H with max. unfold P in H.
    rewrite sub_diag in H. unfold f in H.
    assert (H1 := H (fun i => 0)). simpl in H1.
    specialize H with (fun i => 0).
  assert (nat_ind P).
  P1 m := P (max - m).
  forall k k0 k1, l 2 k /\ l 1 k1 /\ l 0 k0 -> l 2 (S k) /\ l 1 k1 /\ l 0 k0
  forall k k0, l 1 k /\ l 0 k0 -> l 1 (S k) /\ l 0 k0
  forall k, l 0 k -> l 0 (S k)


  (forall m, P1 m -> P1 (S m))
  set (
    R k := forall l, (forall i, mlength i l = k i) ->
    exists n, olist_nth max n = l
  ).
  assert (
  (forall k, R 1 k -> R 1 (S k)) ->
    forall k, R 0 k -> R 0 (S k)
  (forall l, length l = k -> ex) -> (forall l, length l = S k -> ex)
    forall m, (forall m1, m1 > m -> forall k, 
    forall k, (forall m k1, k1 < k -> R m k1) -> 
  ).
  Compute mlength 2 [3;2;2;2;0;0;0].
  (
    (forall n, n > m -> R n k) -> R m (S k)
  )
  (forall m k, f h m = k -> (forall a, a > m -> P a)
  set (f := fun (h : list nat) m l => m + l).
  set (R m k := forall h, f h m 0 = k -> exists n, olist_nth max n = h).
  generalize (two_dim_induction R). subst R.
  assert (forall m k, m <= max -> (forall h, f h 0 = k -> exists n, olist_nth max n = h) -> forall h, f h 0 = S k -> exists n, olist_nth max n = h).
  intros l F L. remember (length l) as ln eqn : E.
  generalize dependent l. induction ln; intros.
  - symmetry in E. apply length_zero_iff_nil in E.
    subst. exists 0. reflexivity.
  - assert (exists n, olist_nth max n = repeat 0 (S ln)). {
      specialize IHln with (repeat max ln).
      destruct IHln; clear E;
	[ induction ln; try constructor; auto
	| induction ln; try constructor; auto
	| induction ln; try constructor; auto
	|
	].
      - simpl. destruct ln; constructor; auto.
      - simpl. auto.
      - exists (S x). simpl. rewrite H.
	clear H. induction ln; try reflexivity.
        simpl. unfold "<?".
	generalize (leb_spec0 (S max) max).
	intros B. destruct B; try lia.
	* destruct (olist_add max (repeat max ln)).
	  -- discriminate.
	  -- injection IHln. intros. subst. reflexivity.
    }
    clear IHln.
    set (f := fix f l n :=
      match l with
      | [] => n
      | h :: t => if h =? 0 then n else f t (S n)
      end
    ).
    assert (Hf0 : forall l n, f l (S n) = S (f l n)). {
      clear. induction l; simpl; try lia.
      destruct (eqb_spec a 0); try lia.
      intros m. apply IHl.
    }
    assert (Hf : forall l n, LocallySorted ge l -> nth n l 1 = 0 <-> n < length l /\ n >= f l 0). {
      clear max ln l F L E H.
      intros l n L. split; intros H.
      - clear L. split.
	+ destruct (le_gt_cases (length l) n) as [Hl | ];
	    try assumption.
	  eapply nth_overflow in Hl.
	  rewrite H in Hl. discriminate.
	+ generalize dependent n.
	  induction l; intros; simpl; try lia.
	  destruct (eqb_spec a 0); try lia.
	  replace (a :: l) with ([a] ++ l) in H;
	    try reflexivity.
	  destruct n; try contradiction.
	  rewrite app_nth2 in H; try (simpl; lia).
	  simpl in *. apply IHl in H.
	  specialize Hf0 with l 0. lia.
      - generalize dependent n.
        induction l; try (simpl in *; lia).
	+ intros. replace (a :: l) with ([a] ++ l);
	    try reflexivity.
	  destruct n.
	  * simpl in *.
	    destruct (eqb_spec a 0); try assumption.
	    rewrite Hf0 in H. lia.
	  * rewrite app_nth2; simpl; try lia.
	    apply IHl.
	    -- inversion L; [constructor | assumption].
	    -- simpl in *. split; try lia.
	       destruct H as [_ H].
	       destruct (eqb_spec a 0).
	       ++ destruct l.
		  ** simpl. lia.
		  ** inversion L. subst.
		     replace n0 with 0; simpl; lia.
	       ++ rewrite Hf0 in H. lia.
    }
    remember (f l 0) as k.
    generalize dependent l.
    induction k.
    + destruct H as [n Hn]. exists n. rewrite Hn.
      rewrite E.
      apply nth_ext with (d := 1) (d' := 1); try apply repeat_length.
      intros. rewrite repeat_length in H.
      destruct (Hf l n0); try assumption. rewrite H1.
      * apply  nth_repeat_lt. apply H.
      * intuition.
    + intros. rewrite E in *. clear ln E.
      assert (forall m, m >= S k -> skipn m l = repeat 0 (length l - m)). {
	intros.
        apply nth_ext with 1 1.
	- rewrite repeat_length. apply length_skipn.
	- intros. rewrite nth_skipn.
	  specialize Hf with l (m + n).
	  destruct Hf; try assumption.
	  rewrite H3.
	  + symmetry. apply nth_repeat_lt.
	    rewrite length_skipn in H1. assumption.
	  + split.
	    * rewrite length_skipn in H1. lia.
	    * lia.
      }
      assert (LA : forall T x (l : list T) k, k < length l -> length (firstn k l ++ [x] ++ skipn (S k) l) = length l). {
	clear. intros. repeat rewrite length_app.
	rewrite length_skipn.
	rewrite <- (firstn_skipn k l) at 3.
	rewrite length_app. f_equal. rewrite length_skipn.
	simpl. lia.
      }
      set (h := firstn k l ++ [0] ++ skipn (S k) l).
      assert (LocallySorted ge h). {
	subst h.
	assert (forall l n, LocallySorted ge l -> LocallySorted ge (l ++ repeat 0 n)). {
	  clear. intros. induction l.
	  - simpl. induction n.
	    + simpl. constructor.
	    + simpl. destruct n; simpl; try constructor.
	      * simpl in *. assumption.
	      * auto.
	  - simpl. destruct l.
	    + simpl. destruct n.
	      * simpl. constructor.
	      * simpl. constructor.
		-- apply IHl. constructor.
		-- lia.
	    + simpl. constructor.
	      * apply IHl. inversion H. assumption.
	      * inversion H. assumption.
	}
	replace ([0] ++ skipn (S k) l) with (repeat 0 (length l - S k + 1)).
	-- apply H1.
	   assert (forall l n, LocallySorted ge l -> LocallySorted ge (firstn n l)). {
	     clear. intros.
	     generalize dependent l. induction n.
	     - simpl. constructor.
	     - intros. simpl. destruct l; try constructor.
	       remember (firstn n l) as h.
	       destruct h; try constructor.
	       + rewrite Heqh. apply IHn.
		 inversion H; [constructor | assumption].
	       + inversion H; subst.
		 * rewrite firstn_nil in Heqh.
		   discriminate.
		 * destruct n; try discriminate.
		   rewrite firstn_cons in Heqh.
		   injection Heqh. lia.
	   }
	   auto.
	-- rewrite add_comm. rewrite repeat_app.
	   f_equal. symmetry. apply H0. lia.
      }
      assert (S k <= length l). {
	rewrite Heqk. clear IHk h H1 H k F L Heqk H0. induction l.
	- simpl. auto.
	- simpl. destruct (eqb_spec a 0); try lia.
	  rewrite Hf0. lia.
      }
      specialize IHk with h.
      destruct IHk; try assumption.
      * subst h. apply Forall_app. split.
	-- apply incl_Forall with (l1 := l).
	   ++ rewrite <- firstn_skipn with (n := k).
	      apply incl_appl. apply incl_refl.
	   ++ assumption.
	-- constructor; try lia.
	   apply incl_Forall with (l1 := l).
	   ++ rewrite <- firstn_skipn with (n := S k).
	      apply incl_appr. apply incl_refl.
	   ++ assumption.
      * subst h. symmetry. apply LA. lia.
      * assert (k < length h). {
	  subst h. rewrite length_app.
	  rewrite firstn_length_le; try lia.
	  rewrite length_app. simpl. lia.
	}
	symmetry. apply le_antisymm.
	-- apply Hf; try assumption.
	   unfold h. rewrite app_nth2.
	   ++ rewrite firstn_length_le.
	      ** rewrite sub_diag. simpl. reflexivity.
	      ** lia.
	   ++ rewrite firstn_length_le; lia.
	-- destruct (le_gt_cases k (f h 0));
	     try assumption.
	   destruct k; try lia.
	   assert (k >= f h 0); try lia.
	   destruct (Hf h k); try assumption.
	   assert (nth k h 1 = 0).
	   ++ intuition.
	   ++ unfold h in H8.
	      rewrite app_nth1 in H8.
	      ** rewrite nth_firstn in H8.
		 unfold "<?" in H8.
		 destruct (leb_spec0 (S k) (S k)); try lia.
		 apply Hf in H8; try assumption. lia.
	      ** rewrite firstn_length_le; lia.
      * unfold h in H3.
	clear H F L Heqk H0 H1.
	remember (nth k l 1) as y.
	generalize dependent l. induction y.
	-- exists x. rewrite H3.
	   rewrite <- (firstn_skipn k). f_equal.
	   assert (forall l k, k < length l -> skipn k l = nth k l 1 :: skipn (S k) l). {
	     clear. intros.
	     generalize dependent k. induction l.
	     - simpl in *. lia.
	     - intros. replace (a :: l) with ([a] ++ l); try reflexivity.
	       destruct k.
	       + simpl in *. reflexivity.
	       + simpl. rewrite IHl; try reflexivity.
		 simpl in H. lia.
	   }
	   rewrite (H l k).
	   ++ rewrite <- Heqy. reflexivity.
	   ++ lia.
	-- intros.
	   set (j := firstn k l ++ [y] ++ skipn (S k) l).
	   destruct (IHy j).
	   ++ unfold j. rewrite LA; lia.
	   ++ rewrite H3.
	      assert (firstn k l = firstn k j). {
		unfold j. Search firstn.
		replace k with (length (firstn k l) + 0) at 2.
		- rewrite firstn_app_2. simpl.
		  rewrite app_nil_r. reflexivity.
		- rewrite firstn_length_le; lia.
	      }
	      rewrite H. do 2 f_equal.
	      subst j.
	      rewrite app_assoc. rewrite skipn_app.
	      assert (S k = length (firstn k l ++ [y])). {
		rewrite length_app.
		rewrite firstn_length_le; simpl; lia.
	      }
	      rewrite H0 at 2.
	      rewrite skipn_all. rewrite <- H0.
	      rewrite sub_diag. reflexivity.
	   ++ subst j. rewrite app_nth2.
	      ** rewrite firstn_length_le; try lia.
		 rewrite sub_diag. reflexivity.
	      ** rewrite firstn_length_le; lia.
	   ++ specialize IHl with (repeat max k ++ [y] ++ repeat
	   ++ exists (S x0). simpl. rewrite H.
	      subst j.
	      unfold olist_add. simpl.

	   repeat rewrite H0.
	   generalize Heqk. clear.
	   intros. induction l.
	   ++ simpl in *. discriminate.
	   ++ simpl.
	   replace ([0]) with (skipn 0 [0]); try reflexivity.
	   replace (skipn k l) with (skipn (S k) (0 :: l)).
	   ++ replace (0 :: l) with ([0] ++ l); try reflexivity.
	      rewrite skipn_app.
	   rewrite <- skipn_cons with (a := 0).
	   Search skipn.
	   Search (_ ++ skipn _ _).
	   replace (S k) with (1 + k) in *; try lia.
	   rewrite <- skipn_skipn in *.
	   destruct (skipn k l).
	   ++ simpl in *.
	      assert (@length nat [] = length (repeat 0 (length l - S k))). { congruence. }
	      rewrite repeat_length in H4. simpl in H4.
	      lia.
	   ++ simpl.
	   rewrite H0. erewrite <- skipn_cons.

      * apply repeat_length.
    + remember (nth k l 1) as x. induction x.
      * assert (forall l k, f l 0 = S k -> nth k l 1 <> 0). {
	  clear. induction l.
	  - simpl in *. discriminate.
	  - intros. destruct (eq_dec a 0).
	    + subst. simpl in *. discriminate.
	    + specialize IHl with (S k).
	      simpl in H. replace (a =? 0) with false in H.
	      * simpl.
	}
	-- Search (_ =? _).
      * refle
      * simpl in *.
    induction max.
    + destruct H. exists x. rewrite H.
      rewrite E. clear L E x H. induction l.
      * reflexivity.
      * simpl. rewrite IHl.
	-- f_equal. inversion F. lia.
    induction k.
    +
    set (f := fix f l n :=
      match l with
      | [] => n
      | h :: t => if h =? 0 then n else f t (S n)
      end).
    assert (forall l n, f l n >= n). {
      clear. induction l.
      - simpl. lia.
      - simpl. destruct (a =? 0); try lia.
	intros n. specialize IHl with (S n). lia.
    }
    remember (f l 0) as k.
    generalize dependent l.
    induction k; intros.
    + destruct H. exists x.
      rewrite H, E. clear E H F.
      induction l; try reflexivity.
      simpl. rewrite IHl.
      * simpl in Heqk. destruct a; try reflexivity.
	replace (S a =? 0) with false in Heqk.
	-- specialize H0 with l 1. lia.
	-- symmetry. apply eqb_neq. lia.
      * inversion L; try constructor. assumption.
      * destruct (eq_dec a 0).
	-- subst. simpl in *. destruct l.
	   ++ reflexivity.
	   ++ inversion L. subst.
	      assert (n = 0); try lia. subst.
	      reflexivity.
	-- simpl in *. replace (a =? 0) with false in Heqk.
	   ++ specialize H0 with l 1. lia.
	   ++ symmetry. apply eqb_neq. assumption.
    + remember (nth k l 1) as x. induction x.
      * assert (forall l k, f l 0 = S k -> nth k l 1 <> 0). {
	  clear. induction l.
	  - simpl in *. discriminate.
	  - intros. destruct (eq_dec a 0).
	    + subst. simpl in *. discriminate.
	    + specialize IHl with (S k).
	      simpl in H. replace (a =? 0) with false in H.
	      * simpl.
	}
	-- Search (_ =? _).
      * refle
      * simpl in *.
    induction max.
    + destruct H. exists x. rewrite H.
      rewrite E. clear L E x H. induction l.
      * reflexivity.
      * simpl. rewrite IHl.
	-- f_equal. inversion F. lia.
	-- inversion F. assumption.
    + simpl.
    set (f := fix f max l n :=
      match l with
      | [] => n
      | h :: t => if h =? max then f max t (pred n) else n
      end).
      Compute f 2 [2;2;2;2;2] 5.

    remember (length (filter (fun x => 0 <? x) l)) as k.
    generalize dependent l. induction k; intros.
    + destruct H. exists x.
      rewrite H, E. clear E H F.
      induction l; try reflexivity.
      simpl in *. unfold "<?" in *.
      destruct (leb_spec0 1 a); try discriminate.
      rewrite IHl.
      * f_equal. lia.
      * inversion L; [constructor | assumption].
      * assumption.
    + assert (forall l k, LocallySorted (fun x y => x >= y) l -> length (filter (fun x => 0 <? x) l) = k ->
      forall n, n < length l -> nth n l 1 = 0 <-> n >= k). {
	clear. intros l k L F n. intros U. split; intros H.
	- clear U. generalize dependent n.
	  generalize dependent k.
	  induction l.
	  + simpl in *. destruct n; lia.
	  + intros.
	    replace (a :: l) with ([a] ++ l) in H;
	      try auto.
	    simpl in F. unfold "<?" in *.
	    destruct (leb_spec0 1 a).
	    * destruct k; try discriminate.
	      destruct n. { simpl in H. subst. lia. }
	      rewrite app_nth2 in H.
	      -- apply IHl with (k := k) in H.
		 ++ simpl in H. lia.
		 ++ inversion L; [constructor | assumption].
		 ++ auto.
	      -- simpl. lia.
	    * assert (a = 0); try lia. subst a.
	      assert (k = 0). {
		clear IHl n n0 H.
		induction l.
		- simpl in *. auto.
		- apply IHl.
		  + inversion L. subst.
		    replace a with 0 in H1; try lia.
		    assumption.
		  + inversion L. assert (a = 0); try lia.
		    subst. simpl. reflexivity.
	      }
	      lia.
	- generalize dependent k. induction l.
	  + simpl in *. lia.
	  + intros. replace (a :: l) with ([a] ++ l);
	      try reflexivity.
	    rewrite app_nth2.
	    * apply IHl.
	      -- inversion L; [constructor | assumption].
	      --
	      -- specialize IHl with (k := S k).
	      -- inversion L; [constructor | assumption].
	      -- assumption.
	      -- assert (a = 0); try lia.
		 subst. simpl in *. destruct n.
		 ++ lia.
	      -- inversion L
		    **
		 3:{ simpl in F.
	    * eapply IHl in H.
	      3:{
	    apply IHl.
	    * inversion L; [constructor | assumption].
	    *
	- destruct (le_gt_cases n k); try assumption.
      }
    + remember (nth k l 1) as x. induction x.
      * assert (forall l k, f l 0 = S k -> nth k l 1 <> 0). {
	  clear. induction l.
	  - simpl in *. discriminate.
	  - intros. destruct (eq_dec a 0).
	    + subst. simpl in *. discriminate.
	    + specialize IHl with (S k).
	      simpl in H. replace (a =? 0) with false in H.
	      * simpl.
	}
	-- Search (_ =? _).
      * refle
      * simpl in *.
    induction max.
    + destruct H. exists x. rewrite H.
      rewrite E. clear L E x H. induction l.
      * reflexivity.
      * simpl. rewrite IHl.
	-- f_equal. inversion F. lia.
    induction k.
    +
    set (f := fix f l n :=
      match l with
      | [] => n
      | h :: t => if h =? 0 then n else f t (S n)
      end).
    assert (forall l n, f l n >= n). {
      clear. induction l.
      - simpl. lia.
      - simpl. destruct (a =? 0); try lia.
	intros n. specialize IHl with (S n). lia.
    }
    remember (f l 0) as k.
    generalize dependent l.
    induction k; intros.
    + destruct H. exists x.
      rewrite H, E. clear E H F.
      induction l; try reflexivity.
      simpl. rewrite IHl.
      * simpl in Heqk. destruct a; try reflexivity.
	replace (S a =? 0) with false in Heqk.
	-- specialize H0 with l 1. lia.
	-- symmetry. apply eqb_neq. lia.
      * inversion L; try constructor. assumption.
      * destruct (eq_dec a 0).
	-- subst. simpl in *. destruct l.
	   ++ reflexivity.
	   ++ inversion L. subst.
	      assert (n = 0); try lia. subst.
	      reflexivity.
	-- simpl in *. replace (a =? 0) with false in Heqk.
	   ++ specialize H0 with l 1. lia.
	   ++ symmetry. apply eqb_neq. assumption.
    + remember (nth k l 1) as x. induction x.
      * assert (forall l k, f l 0 = S k -> nth k l 1 <> 0). {
	  clear. induction l.
	  - simpl in *. discriminate.
	  - intros. destruct (eq_dec a 0).
	    + subst. simpl in *. discriminate.
	    + specialize IHl with (S k).
	      simpl in H. replace (a =? 0) with false in H.
	      * simpl.
	}
	-- Search (_ =? _).
      * refle
      * simpl in *.
    induction max.
    + destruct H. exists x. rewrite H.
      rewrite E. clear L E x H. induction l.
      * reflexivity.
      * simpl. rewrite IHl.
	-- f_equal. inversion F. lia.
	-- inversion F. assumption.
    + simpl.
    set (f := fix f max l n :=
      match l with
      | [] => n
      | h :: t => if h =? max then f max t (pred n) else n
      end).
      Compute f 2 [2;2;2;2;2] 5.

  intros l F L. induction l.
  - exists 0. reflexivity.
  - destruct IHl as [m Hm].
    + inversion F. assumption.
    + inversion L; [constructor | assumption].
    + set (x := olist_add max l).
  intros. induction max.
  - exists (length l). induction l.
    + simpl. reflexivity.
    + simpl. rewrite IHl.
      * unfold olist_add. simpl.

Compute olist_nth 2 4150.
Definition n1 max min := max - min.

Fixpoint n2 max n min :=
  match n with
  | 0 => 0
  | S n => 

0 1 2 00 10 11 20 21 22 000 100 110 111 200 210 211 220 221 222

Theorem t1 max 
Compute olist_nth 2 6.
Compute olist_nth 2 12.

Theorem olist_all max :
  forall l, LocallySorted (fun x y => x >= y) l ->
  exists n, olist_nth max n = l.
Proof.
  induction l; intros.
  - exists 0. reflexivity.
  - destruct IHl as [m Hm].
    + inversion H; try constructor. assumption.
    + set (x := olist_nth max (S m)).
      simpl in x. unfold olist_add in x.
Admitted.

Theorem olist_nth_le max n :
  Forall (fun x => x <= max) (olist_nth max n).
Proof.
  induction n; [constructor | ].
  apply olist_add_le. assumption.
Qed.

Definition nth_sum l n :=
  sum (fun i => nth i l 0) (olist_nth (length l - 1) n).

Theorem nth_sum_in A `{numerical_semigroup A} l :
  generator A (fun x => List.In x l) ->
  forall n, A (nth_sum l n).
Proof.
  intros G n.
  destruct (eq_dec (length l) 0) as [l0 | l0].
  - apply length_zero_iff_nil in l0. subst.
    replace (nth_sum [] n) with 0; try apply ns_zero.
    unfold nth_sum. simpl.
    remember (olist_nth 0 n) as ls eqn : E.
    clear E. induction ls; try reflexivity.
    simpl. destruct a; rewrite add_0_l; assumption.
  - unfold nth_sum.
    generalize (olist_nth_le (length l - 1) n). intros F.
    remember (olist_nth (length l - 1) n) as ls eqn : E.
    remember (length ls) as ln eqn : En. clear E.
    generalize dependent ls. induction ln as [ | ln IH].
    + intros.
      symmetry in En. apply length_zero_iff_nil in En.
      subst. apply ns_zero.
    + intros. destruct ls; try discriminate.
      simpl. apply ns_closed.
      * destruct G as [G _]. unfold Included, In in G.
	apply G. apply nth_In. inversion F. subst. lia.
      * apply IH; auto. inversion F. assumption.
Qed.

Fixpoint list_min l :=
  match l with
  | [] => 0
  | [x] => x
  | h :: t => Nat.min h (list_min t)
  end.

Definition nth_sum_limit l n :=
  let ln := length (olist_nth (length l - 1) n) in
  ln * list_min l.

Theorem generates_list l a :
  generates_el (fun x => List.In x l) a ->
  exists ls, sum (fun i => nth i l 0) ls = a.
Proof.
  intros G. destruct G as [r x k G].
  induction r as [ | r IH].
  - exists []. reflexivity.
  - rewrite seq_S. simpl. rewrite sum_app.
    destruct IH as [h Hh]; auto.
    assert (exists n, nth n l 0 = x r) as [n Hn]. {
      destruct (In_nth l (x r) 0) as [n Hn]; auto.
      exists n. apply Hn.
    }
    exists (h ++ repeat n (k r)). simpl. rewrite add_0_r.
    rewrite sum_app. rewrite Hh. f_equal.
    remember (k r) as m eqn : E. clear E.
    induction m; simpl; auto.
Qed.

Theorem nth_sum_all A `{numerical_semigroup A} l n :
  generator A (fun x => List.In x l) ->
  forall a, A a /\ a <= nth_sum_limit l n ->
  exists m, m <= n /\ a = nth_sum l m.
Proof.
  intros [_ G] a [Aa L].
  generalize (G a Aa). clear G. intros G.
  apply generates_list in G. destruct G as [ls Hl].
  destruct (olist_all (length l - 1) ls) as [m Hm].
  exists m.
  assert (a = nth_sum l m). {
   unfold nth_sum.
   rewrite <- (sum_permutation _ _ _ Hm). auto.
  }
  split; try assumption.
  subst a. clear A H Aa Hm H0.
  unfold nth_sum_limit in L.
Abort.

Fixpoint first_congr l m a i n :=
  match i with
  | 0 => 0
  | S i => let x := fst (nth_sum l n) in
      if x mod m =? a mod m then x else first_congr l m a i (S n)
  end.
Compute first_congr [4;7;10] 4 1 100 0.

Compute nth_sum [] 9.

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
