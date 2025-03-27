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

Theorem olist_nth_all max : forall l, Forall (fun x => x <= max) l ->
  LocallySorted ge l -> exists n, olist_nth max n = l.
Proof.
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
    rewrite SK; try (rewrite length_rev; lia).
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

  set (Hld l m k := forall i, i <= max - m -> ml i l = if i =? max - m then S (k i) else k i).
  assert (Ep : forall l m k, Hld l m k -> S (k (max - m)) = ml (max - m) l). {
    intros l m k Hl. subst Hld. simpl in Hl.
    specialize Hl with (max - m).
    destruct (eqb_spec (max - m) (max - m)); lia.
  }
  assert (p_le : forall (l : list nat) m k, Hld l m k -> k (max - m) < length l). {
    intros. unfold "<". rewrite <- ml_0.
    specialize Ep with l m k. rewrite Ep; try assumption.
    apply M1. lia.
  }
  assert (fle : forall l m k, LocallySorted ge l -> Hld l m k -> forall i, i <= max - m -> Forall (le i) (firstn (k (max - m)) l)). {
    intros l m k L Hl i Hi. apply Forall_nth. intros j d Hj.
    rewrite (nth_indep _ _ 0); try assumption.
    specialize Ep with l m k. apply Ep in Hl as Epa.
    specialize p_le with l m k. apply p_le in Hl as le_pa.
    rewrite firstn_length_le in Hj; try lia.
    rewrite nth_firstn. unfold "<?".
    destruct (leb_spec0 (S j) (k (max - m))) as [HSj | ]; try lia.
    unfold le.
    apply M3; try assumption.
    eapply (M1 l) in Hi. lia.
  }
  assert (FrS : forall l m k, LocallySorted ge l -> Hld l m k -> Forall (gt (max - m)) (skipn (S (k (max - m))) l)). {
    intros l m k L Hl.
    apply Forall_nth. intros i d Hi.
    rewrite (nth_indep _ _ 0); try assumption.
    rewrite nth_skipn.
    apply Ep in Hl.
    apply M7; try assumption; try lia.
    rewrite length_skipn in Hi. lia.
  }
  assert (eh :
    forall l m k, LocallySorted ge l ->
    Forall (ge max) l ->
    f (max - m) k ->
    (forall i, i <= max - m -> ml i l = if i =? max - m then S (k i) else k i) ->
      let p := k (max - m) in
      let pr := match max - m with 0 => [] | S n => [n] end in
      let h := repeat max p ++ pr ++ skipn (S p) l in
      exists n, olist_nth max n = h
  ). {
    intros l m k L F H Hl. intros.
    generalize (firstn_skipn p l). intros El.
    generalize (fle _ _ _ L Hl). clear fle. intros fle.
    generalize (Ep _ _ _ Hl). clear Ep. intros Ep.
    apply p_le in Hl as p_lea.
    apply FrS in Hl as FrSa; try assumption.
    rewrite SK in El; try assumption.
    assert (Lh : LocallySorted ge h). {
      subst h. remember (max - m) as mm. destruct mm.
      - subst pr. rewrite app_nil_l. subst p.
	remember (skipn (S (k 0)) l) as s eqn : E. clear E.
	destruct s.
	+ rewrite app_nil_r. apply LSr.
	+ inversion FrSa. lia.
      - subst pr. apply LS.
	+ apply LSp2 with max; try lia.
	  replace [max] with (repeat max 1);
	    try reflexivity.
	    rewrite <- repeat_app. apply LSr.
	+ subst p. remember (skipn (S (k (S mm))) l) as s eqn : E.
	  destruct s; constructor.
	  * rewrite E.
	    rewrite <- (firstn_skipn (S (k (S mm)))) in L.
	    apply LSa in L. assumption.
	  * inversion FrSa. lia.
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
	-- inversion FrSa. lia.
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
		remember (firstn (k (S mm)) l) as fs.
		assert (length fs = k (S mm)). {
		  subst fs. apply firstn_length_le. lia.
		}
		generalize H0 Hil. clear. intros.
		remember (k (S mm)) as n. clear Heqn.
		generalize dependent n.
		induction fs; intros.
		--- simpl in *. lia.
		--- simpl. destruct (leb_spec0 i a).
		    +++ destruct n.
			*** simpl in H0. lia.
			*** f_equal. apply IHfs.
			    ---- inversion Hil. assumption.
			    ---- simpl in H0. lia.
		    +++ inversion Hil. lia.
	  -- f_equal. simpl.
	     destruct (leb_spec0 i mm), (leb_spec0 i (nth p l 0)); try lia.
	     exfalso. apply n0. subst p.
	     apply M3; try assumption. rewrite Hi.
	     apply (M1 l) in Hil. lia.
  }

  assert (R :
    forall l m k, LocallySorted ge l ->
    Forall (ge max) l ->
    f (max - m) k ->
    (forall i, i <= max - m -> ml i l = if i =? max - m then S (k i) else k i) ->
      let p := k (max - m) in
      let pr := match max - m with 0 => [] | S n => [n] end in
      let h := repeat max p ++ pr ++ skipn (S p) l in
    olist_add max (repeat max p ++ pr ++ (skipn (S p) l)) = repeat (max - m) (S p) ++ (skipn (S p) l)
  ). {
    intros l m k L F H Hl. intros.
    generalize (FrS _ _ _ L Hl). clear FrS. intros FrS.
    generalize (Ep _ _ _ Hl). clear Ep. intros Ep.
    remember (max - m) as mm. destruct mm.
    + simpl in pr. subst pr.
      rewrite app_nil_l. subst p.
      remember (skipn (S (k 0)) l) as s. destruct s.
      * repeat rewrite app_nil_r.
	clear. remember (k 0) as p eqn : E. clear E.
	induction p; try reflexivity.
	simpl. unfold "<?".
	destruct (leb_spec0 (S max) (max)); try lia.
	rewrite IHp. reflexivity.
      * inversion FrS. lia.
    + subst pr.
      remember (skipn (S p) l) as s. simpl.
      generalize Heqmm. clear. intros.
      induction p.
      * simpl. unfold "<?".
	destruct (leb_spec0 (S mm) max); try reflexivity. lia.
      * simpl. unfold "<?". destruct (leb_spec0 (S max) max); try lia.
	rewrite IHp. reflexivity.
  }
  assert (B :
    forall l m k, LocallySorted ge l ->
    Forall (ge max) l ->
    f (max - m) k -> ml (S (max - m)) l = 0 ->
    (forall i, i <= max - m -> ml i l = if i =? max - m then S (k i) else k i) -> exists n, olist_nth max n = l
  ). {
    subst P f. simpl. intros l m k L F H Hm Hl.
    generalize (p_le _ _ _ Hl). clear p_le. intros p_le.
    generalize (eh l m k). intros eha.
    generalize (fle _ _ _ L Hl). clear fle. intros fle.
    generalize (R l m k). clear R. intros R.
    generalize (Ep _ _ _ Hl). clear Ep. intros Ep.
    generalize (firstn_skipn (k (max - m)) l). intros El.
    rewrite SK in El; try assumption.
    destruct eha as [n Hn]; try assumption.
    exists (S n). simpl. rewrite Hn. clear Hn.
    assert (FR : firstn (k (max - m)) l = repeat (max - m) (k (max - m))). {
      apply nth_ext with 0 0.
      - rewrite firstn_length_le; try lia.
	symmetry. apply repeat_length.
      - intros. rewrite firstn_length_le in H0; try lia.
	rewrite nth_repeat_lt; try lia.
	rewrite <- El in F.
	apply Forall_app in F as [F _].
	+ eapply Forall_nth in fle.
	  * apply le_antisymm; try eassumption.
	    rewrite nth_firstn.
	    unfold "<?".
	    destruct (leb_spec0 (S n0) (k (max - m)));
	    try lia. unfold le in fle.
	    assert (nth n0 l 0 < S (max - m)); try lia.
	    apply M7; try assumption; try lia.
	  * lia.
	  * rewrite firstn_length_le; lia.
    }
    apply R in Hl as Ra; try assumption. clear R.
    rewrite <- El at 2. rewrite Ra, FR.
    replace (nth (k (max - m)) l 0 :: skipn (S (k (max - m))) l) with ([nth (k (max - m)) l 0] ++ skipn (S (k (max - m))) l); try reflexivity.
    rewrite app_assoc. f_equal.
    replace [nth (k (max - m)) l 0] with (repeat (max - m) 1).
    + rewrite <- repeat_app. rewrite add_comm.
      f_equal.
    + simpl. f_equal. apply le_antisymm.
      * apply M3; try assumption. lia.
      * assert (nth (k (max - m)) l 0 < S (max - m)); try lia.
	apply M7; try assumption. lia.
  }

  assert (forall m, P m). {
    induction m; intros.
    - subst P f. simpl. intros k H l L F Hl.
      eapply B; try eassumption.
      apply le_antisymm; try lia. rewrite sub_0_r.
      destruct (le_gt_cases (ml (S max) l) 0); try assumption.
      apply M3 in H0; try assumption.
      destruct l.
      + simpl in *. lia.
      + inversion F. subst. simpl in H0. lia.
    - subst P. simpl in IHm. simpl. intros k Hk.
      unfold f. intros l L F Hl.
      generalize (eh l (S m) k). intros eha.
      set (p := k (max - (S m))).
      set (j := repeat (max - S m) (S p) ++ skipn (S p) l).
      assert (exists n, olist_nth max n = j). {
	destruct eha as [n Hn]; try assumption.
	exists (S n).
	simpl. rewrite Hn. subst j.
	subst p. apply R; try assumption.
      }

      remember (ml (max - m) l) as mm. destruct mm.
      + destruct H. exists x. rewrite H. clear H x.
	generalize (p_le _ _ _ Hl). clear p_le. intros p_le.
	generalize (Ep _ _ _ Hl). clear Ep. intros Ep.
	generalize (firstn_skipn (k (max - S m)) l). intros El.
	rewrite SK in El; try assumption.
	rewrite <- El. clear IHm.
	fold p.
	subst j. remember (skipn (S p) l) as s.
	replace (nth p l 0 :: s) with ([nth p l 0] ++ s); try reflexivity.
	rewrite app_assoc. f_equal.
	apply nth_ext with 0 0.
	* rewrite repeat_length, length_app, firstn_length_le; try lia. simpl. lia.
	* intros. rewrite repeat_length in H.
	  rewrite nth_repeat_lt; try lia.
	  destruct (eq_dec n p).
	  -- subst. rewrite app_nth2; rewrite firstn_length_le; try lia.
	     rewrite sub_diag. simpl.
	     apply le_antisymm.
	     ++ apply M3; try assumption. lia.
	     ++ assert (p >= ml (max - m) l); try lia.
		apply M7 in H0; try assumption. lia.
	  -- rewrite app_nth1; try (rewrite firstn_length_le; lia).
	     rewrite nth_firstn. unfold "<?".
	     destruct (leb_spec0 (S n) p); try lia.
	     apply le_antisymm.
	     ++ apply M3; try assumption. lia.
	     ++ assert (n >= ml (max - m) l); try lia.
		apply M7 in H0; try assumption; lia.
      + destruct (eq_dec (max - m) 0) as [e | e]. {
	  assert (eS : max - S m = 0); try lia.
	  eapply IHm; try assumption.
	  - subst f. simpl.
	    intros. apply Hk; try assumption.
	    intros. apply H2. lia.
	  - intros. destruct (eqb_spec i (max - m)); try lia.
	    subst. rewrite e in *. rewrite Hl; try lia.
	    destruct (eqb_spec 0 (max - S m)); lia.
	}
	remember (max - S m) as a eqn : Ea.
	replace (max - m) with (S a) in *; try lia.
	destruct H as [n Hn].
	assert (forall x l, LocallySorted ge l -> Forall (ge max) l -> (forall i, i <= a -> ml i l = if i =? a then S (k i) else k i) -> ml (S a) l = x -> exists n, olist_nth max n = l). {
	  induction x; intros.
	  - clear j Hn.
	    set (j := repeat a (S (k a)) ++ skipn (S (k a)) l0).
	    assert (exists n, olist_nth max n = j). {
	      destruct (eh l0 (max - a) k) as [b Hb]; try assumption.
	      - replace (max - (max - a)) with a; try lia.
		assumption.
	      - replace (max - (max - a)) with a; try lia.
	        intros. destruct (eqb_spec i a).
		+ subst i. rewrite H1; try lia.
		  destruct (eqb_spec a a); lia.
		+ rewrite H1; try lia.
		  destruct (eqb_spec i a); lia.
	      - exists (S b). simpl. rewrite Hb. subst j.
		replace (max - (max - a)) with a; try lia.
		subst a. apply R; try assumption.
	    }
	    destruct H3.
	    eapply B with (max - a) k;
	      replace (max - (max - a)) with a; try lia;
	      try assumption.
	  - set (k1 i := if i =? S a then x else ml i l0).
	    apply IHm with k1; try assumption.
	    + subst f. simpl. intros.
	      destruct IHx with l1; try assumption.
	      * intros. rewrite H5; try lia.
		subst k1. simpl.
		destruct (eqb_spec i (S a)); try lia.
		rewrite H1; try lia.
	      * rewrite H5; try lia. subst k1. simpl.
		destruct (eqb_spec a a); lia.
	      * exists x0. assumption.
	    + intros. destruct (eqb_spec i (S a)).
	      * subst k1. simpl.
		destruct (eqb_spec i (S a)); try lia.
		subst. lia.
	      * subst k1. simpl.
		destruct (eqb_spec i (S a)); lia.
	}
	apply H with (ml (S a) l); try assumption.
	reflexivity.
  }
  intros.
  remember (length l) as ln.
  generalize dependent l. induction ln; intros.
  - exists 0.
    symmetry in Heqln. apply length_zero_iff_nil in Heqln.
    subst. reflexivity.
  - specialize H with max. subst P. simpl in H.
    rewrite sub_diag in H.
    set (k (i : nat) := ln). specialize H with k.
    subst f. simpl in H. apply H; try assumption.
    + intros. apply IHln; try assumption.
      rewrite <- ml_0. rewrite H4; try lia. reflexivity.
    + intros. destruct (eqb_spec i 0); try lia.
      subst. rewrite ml_0. rewrite <- Heqln. reflexivity.
      Unshelve. assumption.
Qed.

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
