(*From Coq Require Import Lia Mergesort Permutation Sorted.*)
From Coq Require Import Lia Sorted.
Require Export def.
 

Module ordered_list.

(** Increase the first number in the list [l] that is less than [max] and set
    all the previous elements to that same (increased) value. *)

Fixpoint next max l :=
  match l with
  | [] => [0]
  | h :: t => if h <? max then S h :: t else
      match next max t with
      | [] => []
      | h :: t => h :: h :: t
      end
  end.

Theorem next_0 l : next 0 l = repeat 0 (S (length l)).
Proof.
  induction l; try reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed.


Section ordered_list.
  Context (max : nat).
  Local Notation next := (next max).
  Local Notation Forall_max := (Forall (ge max)).
  Local Notation sorted := (LocallySorted ge).
  Local Notation nth n l := (nth n l 0).

  Theorem next_not_nil l : next l <> [].
  Proof.
    induction l; try discriminate.
    simpl. destruct (ltb_spec a max); try discriminate.
    destruct (next l); [assumption | discriminate].
  Qed.

  Theorem next_repeat l n m : m < max ->
    next (repeat max n ++ m :: l) =
    repeat (S m) n ++ next (m :: l).
  Proof.
    intros Hm. induction n as [ | n IH]; try reflexivity.
    remember (m :: l) as ml. simpl.
    destruct (ltb_spec max max); try lia. rewrite IH.
    remember (repeat (S m) n ++ next ml) as h eqn : Eh.
    destruct h.
    - exfalso. eapply next_not_nil. eassumption.
    - f_equal. destruct n; simpl in *.
      + subst. simpl in IH.
	destruct (ltb_spec m max); try lia.
	injection IH. auto.
      + injection Eh. auto.
  Qed.

  Theorem next_Forall l :
    Forall_max l -> Forall_max (next l).
  Proof.
    intros F. induction l as [ | h t IH].
    - simpl. constructor; [lia | constructor].
    - inversion F as [ | n l _ Ft].
      simpl. destruct (ltb_spec h max); subst.
      + constructor; assumption.
      + remember (next t) as nt.
	destruct nt; constructor; auto.
	apply IH in Ft. inversion Ft. assumption.
  Qed.

  Fixpoint nh n :=
    match n with
    | 0 => []
    | S n => next (nh n)
    end.

  Theorem nh_all : forall l, Forall_max l -> sorted l ->
    exists n, nh n = l.
  Proof.
    assert (skipn_nth : forall l n, n < length l ->
      skipn n l = nth n l :: skipn (S n) l
    ). {
      induction l as [ | h t IH]; try (simpl; lia).
      intros n Hn. destruct n; try reflexivity.
      rewrite skipn_cons.
      simpl in Hn. rewrite IH; try lia.
      rewrite skipn_cons. reflexivity.
    }
    assert (firstn_succ : forall l n, n < length l ->
      firstn (S n) l = firstn n l ++ [nth n l]
    ). {
      intros. rewrite firstn_skipn_rev.
      rewrite <- rev_involutive. f_equal.
      rewrite rev_app_distr. simpl.
      rewrite skipn_nth; try (rewrite length_rev; lia).
      rewrite rev_nth; try lia.
      repeat f_equal; try lia.
      rewrite skipn_rev. repeat f_equal. lia.
    }
    assert (repeat_sorted :
      forall n m, sorted (repeat n m)
    ). {
      intros. induction m; try constructor.
      simpl. remember (repeat n m) as r eqn : Er.
      destruct r; constructor; try assumption.
      destruct m; try discriminate.
      injection Er. lia.
    }
    assert (sorted_middle :
      forall l a h, sorted (l ++ [a]) -> sorted (a :: h) ->
      sorted (l ++ a :: h)
    ). {
      induction l; intros; try assumption.
      simpl. destruct l; simpl; constructor;
	try assumption; try (inversion H; assumption).
	apply IHl; try assumption. inversion H. assumption.
    }
    assert (sorted_nth : forall l, sorted l ->
      forall m n, m < length l -> n < length l -> m <= n ->
      nth n l <= nth m l
    ). {
      intros l L.
      apply Sorted_LocallySorted_iff in L.
      apply Sorted_StronglySorted in L.
      2: { unfold Transitive. lia. }
      induction l; intros; try (simpl in H; lia).
      inversion L. subst. destruct m, n; simpl; try lia.
      - simpl in H0.
	eapply (Forall_nth (ge a) l) in H5; try eassumption.
	lia.
      - apply IHl; simpl in *; try assumption; lia.
    }
    assert (sorted_app_le : forall l b a, a <= b ->
      sorted (l ++ [b]) -> sorted (l ++ [a])
    ). {
      induction b; intros.
      - replace a with 0; try lia. assumption.
      - destruct (eq_dec a (S b)); try (subst; assumption).
	apply IHb; try lia. generalize H0. clear.
	intros H. induction l; intros; [constructor | ].
	simpl. destruct l.
	+ constructor; try constructor.
	  inversion H. lia.
	+ simpl. inversion H. subst. apply IHl in H2.
	  constructor; assumption.
    }
    assert (sorted_app_r :
      forall l h, sorted (l ++ h) -> sorted h
    ). {
      intros. induction l; try assumption.
      inversion H; apply IHl;
	inversion H; try constructor; assumption.
    }
    assert (sorted_app_l :
      forall l h, sorted (l ++ h) -> sorted l
    ). {
      clear. intros. induction l; try constructor.
      destruct l; constructor.
      - apply IHl. simpl in H. inversion H. assumption.
      - inversion H. assumption.
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
    assert (ml_le :
      forall l n m, n <= m -> ml m l <= ml n l
    ). {
      intros. induction l; auto. simpl.
      destruct (leb_spec m a), (leb_spec n a); lia.
    }
    assert (ml_app :
      forall l h m, ml m (l ++ h) = ml m l + ml m h
    ). {
      intros. induction l; try reflexivity.
      simpl. destruct (leb_spec m a); lia.
    }
    assert (ml_lt_0 :
      forall l n a, sorted (a :: l) -> a < n -> ml n (a :: l) = 0
    ). {
      induction l as [ | h t IH]; intros; simpl.
      - destruct (leb_spec n a); lia.
      - destruct (leb_spec n a); try lia.
	apply IH; inversion H;
	  try constructor; try assumption; lia.
    }
    assert (ml_nth_ge : forall l m n, sorted l ->
      n < ml m l -> nth n l >= m
    ). {
      induction l; intros; simpl in H0; try lia.
      simpl. destruct n.
      - destruct (leb_spec m a); try lia.
	eapply le_trans.
	+ apply IHl; try eassumption.
	  inversion H; [constructor | assumption].
	+ inversion H; subst; simpl in *;
	    [lia | assumption].
      - apply IHl.
	+ inversion H; [constructor | assumption].
	+ destruct (leb_spec m a); lia.
    }
    assert (ml_nth_lt : forall l m n, sorted l ->
      n < length l -> n >= ml m l -> nth n l < m
    ). {
      induction l; intros; simpl in *; try lia.
      destruct (leb_spec m a); destruct n; try lia.
      - apply IHl; try lia.
	inversion H; [constructor | assumption].
      - assert (0 <= S n); try lia.
	eapply sorted_nth in H3; try eassumption;
	  simpl in *; lia.
    }

    set (mlk m k l := forall i, i <= m -> ml i l = k i).
    set (
      all m k :=
	forall l, sorted l -> Forall_max l -> mlk m k l ->
	exists n, nh n = l
    ).
    set (Sk m k i := if i =? m then S (k i) else k i).

    set (Hld l m k := forall i, i <= max - m -> ml i l = if i =? max - m then S (k i) else k i).
    assert (mlk_Sk :
      forall l m k, mlk m (Sk m k) l -> ml m l = S (k m)
    ). {
      intros l m k Hl. subst mlk Sk. simpl in Hl.
      specialize Hl with m.
      destruct (eqb_spec m m); lia.
    }
    assert (mlk_lt :
      forall l m k, mlk m (Sk m k) l -> k m < length l
    ). {
      intros. rewrite <- ml_0.
      unfold "<". erewrite <- mlk_Sk; try eassumption.
      apply ml_le. lia.
    }
    assert (Fle :
      forall l m k, sorted l -> mlk m (Sk m k) l ->
      forall i, i <= m -> Forall (le i) (firstn (k m) l)
    ). {
      intros l m k L Hl i Hi.
      apply Forall_nth. intros j d Hj.
      rewrite (nth_indep _ _ 0); try assumption.
      apply mlk_Sk in Hl as MS. apply mlk_lt in Hl as ML.
      rewrite firstn_length_le in Hj; try lia.
      rewrite nth_firstn.
      destruct (ltb_spec j (k m)); try lia.
      apply ml_nth_ge; try assumption.
      apply (ml_le l) in Hi. lia.
    }
    assert (FS :
      forall l m k, sorted l -> mlk m (Sk m k) l ->
      Forall (gt m) (skipn (S (k m)) l)
    ). {
      intros l m k L Hl.
      apply Forall_nth. intros i d Hi.
      rewrite (nth_indep _ _ 0); try assumption.
      rewrite nth_skipn. apply mlk_Sk in Hl.
      apply ml_nth_lt; try assumption; try lia.
      rewrite length_skipn in Hi. lia.
    }
    assert (GR :
      forall l m k, sorted l -> Forall_max l ->
      all m k -> mlk m (Sk m k) l -> m <= max ->
      let md := match m with 0 => [] | S n => [n] end in
      let h :=
	repeat max (k m) ++ md ++ skipn (S (k m)) l in
      exists n, nh n = h
    ). {
      intros l m k L F H Hl Lm md h.
      generalize (mlk_lt _ _ _ Hl). clear mlk_lt.
      intros mlk_lt.
      generalize (mlk_Sk _ _ _ Hl). clear mlk_Sk.
      intros mlk_Sk.
      generalize (FS _ _ _ L Hl). clear FS. intros FS.
      assert (Lh : LocallySorted ge h). {
	subst h. destruct m; subst md.
	- rewrite app_nil_l.
	  remember (skipn (S (k 0)) l) as s eqn : E.
	  clear E. destruct s.
	  + rewrite app_nil_r. apply repeat_sorted.
	  + inversion FS. lia.
	- apply sorted_middle.
	  + apply sorted_app_le with max; try lia.
	    replace [max] with (repeat max 1);
	      try reflexivity.
	      rewrite <- repeat_app. apply repeat_sorted.
	  + remember (skipn (S (k (S m))) l) as s eqn : E.
	    destruct s; constructor.
	    * rewrite E.
	      rewrite <- (firstn_skipn (S (k (S m)))) in L.
	      apply sorted_app_r in L. assumption.
	    * inversion FS. lia.
      }
      apply H; try assumption.
      - subst h. apply Forall_app. split.
	+ clear. induction (k m); simpl; constructor;
	    [lia | assumption].
	+ apply Forall_app. split.
	  * subst md.
	    destruct m; constructor; [lia | constructor].
	  * rewrite <- (firstn_skipn (S (k m))) in F.
	    apply Forall_app in F. apply F.
      - intros i Hil. apply Hl in Hil as Hi.
	destruct m.
	+ subst md h. destruct (eq_dec i 0); try lia. subst.
	  remember (skipn (S (k 0)) l) as s eqn : E.
	  clear E. destruct s.
	  -- repeat rewrite app_nil_r in *.
	     clear. induction (k 0); try reflexivity.
	     simpl. lia.
	  -- inversion FS. lia.
	+ generalize (firstn_skipn (k (S m)) l).
	  rewrite skipn_nth; try assumption.
	  intros El. symmetry in El.
	  subst Sk. simpl in Hi, Hl.
	  destruct (eqb_spec i (S m)).
	  * subst. apply le_antisymm.
	    -- destruct (le_gt_cases (ml (S m) h) (k (S m))) as [C | C]; try assumption.
		apply ml_nth_ge in C; try assumption.
		destruct (Compare_dec.gt_dec (S m) (nth (k (S m)) h)); try lia.
		exfalso. apply n. clear n C. unfold h.
		rewrite app_nth2; rewrite repeat_length;
		  try lia.
		rewrite sub_diag. subst md. simpl. lia.
	    -- assert (length l = length h). {
		 rewrite El.
		 subst h. repeat rewrite length_app.
		 remember (skipn (S (k (S m))) l) as s.
		 simpl. f_equal.
		 rewrite firstn_length_le; try lia.
		 symmetry. apply repeat_length.
	       }
	       destruct (le_gt_cases (k (S m)) (ml (S m) h)) as [C | C]; try assumption.
		unfold "<" in C.
		destruct (k (S m)); try (subst; lia).
		apply le_S_n in C.
		apply ml_nth_lt in C;
		  try assumption; try lia.
		unfold h in C. rewrite app_nth1 in C.
		++ rewrite nth_repeat_lt in C; lia.
		++ rewrite repeat_length. lia.
	  * subst md. rewrite <- Hi, El. unfold h.
	    remember (skipn (S (k (S m))) l) as s.
	    replace (nth (k (S m)) l :: s) with ([nth (k (S m)) l] ++ s); try reflexivity.
	    repeat rewrite ml_app. f_equal.
	    -- replace (ml i (firstn (k (S m)) l)) with (k (S m)).
	       ++ generalize F Hil Lm. clear.
		  intros F Hil Lm.
		  induction (k (S m)); try reflexivity.
		  simpl. destruct (leb_spec i max); lia.
	       ++ eapply Fle in Hl as Fl; try eassumption.
		  remember (firstn (k (S m)) l) as fs.
		  assert (length fs = k (S m)). {
		    subst fs. apply firstn_length_le. lia.
		  }
		  generalize H0 Fl. clear. intros.
		  remember (k (S m)) as x. clear Heqx.
		  generalize dependent x.
		  induction fs; intros; simpl in *; try lia.
		  destruct (leb_spec i a);
		    try (inversion Fl; lia).
		  destruct x; simpl in H0; try lia.
		  f_equal.
		  apply IHfs; simpl in H0; try lia.
		  inversion Fl. assumption.
	    -- f_equal. simpl.
	       destruct (leb_spec i m), (leb_spec0 i (nth (k (S m)) l)); try lia.
	       exfalso. apply n0.
	       apply ml_nth_ge; try assumption. rewrite Hi.
	       apply (ml_le l) in Hil. lia.
    }

    assert (NR :
      forall l m k, sorted l -> Forall_max l ->
      all m k -> mlk m (Sk m k) l -> m <= max ->
      let md := match m with 0 => [] | S n => [n] end in
      next (repeat max (k m) ++ md ++ (skipn (S (k m)) l)) = repeat m (S (k m)) ++ (skipn (S (k m)) l)
    ). {
      intros l m k L F H Hl Lm md.
      generalize (FS _ _ _ L Hl). clear FS. intros FS.
      generalize (mlk_Sk _ _ _ Hl). clear mlk_Sk.
      intros mlk_Sk.
      destruct m.
      + subst md. rewrite app_nil_l.
	remember (skipn (S (k 0)) l) as s.
	destruct s; try (inversion FS; lia).
	repeat rewrite app_nil_r.
	clear. induction (k 0); try reflexivity.
	simpl. destruct (ltb_spec max max); try lia.
	rewrite IHn. reflexivity.
      + subst md.
	remember (skipn (S (k (S m))) l) as s. simpl.
	generalize Lm. clear. intros.
	induction (k (S m)).
	* simpl.
	  destruct (ltb_spec m max); try reflexivity. lia.
	* simpl. destruct (ltb_spec max max); try lia.
	  rewrite IHn. reflexivity.
    }

    assert (B :
      forall l m k, sorted l -> Forall_max l ->
      all m k -> mlk m (Sk m k) l -> m <= max ->
      ml (S m) l = 0 ->
      exists n, nh n = l
    ). {
      intros l m k L F H Hl Lm Hm.
      generalize (mlk_lt _ _ _ Hl). clear mlk_lt.
      intros mlk_lt.
      generalize (firstn_skipn (k m) l).
      intros El. symmetry in El.
      rewrite skipn_nth in El; try assumption.
      generalize (mlk_Sk _ _ _ Hl). clear mlk_Sk.
      intros mlk_Sk.
      destruct (GR l m k) as [n Hn]; try assumption.
      exists (S n). simpl. rewrite Hn. clear Hn n.
      assert (FR : firstn (k m) l = repeat m (k m)). {
	apply nth_ext with 0 0.
	- rewrite firstn_length_le; try lia.
	  symmetry. apply repeat_length.
	- intros n Hn.
	  rewrite firstn_length_le in Hn; try lia.
	  rewrite nth_repeat_lt; try lia.
	  rewrite El in F.
	  apply Forall_app in F as [F _].
	  + eapply Forall_nth in Fle; try eassumption.
	    * apply le_antisymm; try eassumption.
	      rewrite nth_firstn.
	      destruct (ltb_spec n (k m)); try lia.
	      assert (nth n l < S m); try lia.
	      apply ml_nth_lt; try assumption; lia.
	    * lia.
	    * rewrite firstn_length_le; lia.
      }
      apply NR in Hl as R; try assumption. clear NR.
      rewrite El at 2. rewrite R, FR.
      replace (nth (k m) l :: skipn (S (k m)) l) with ([nth (k m) l] ++ skipn (S (k m)) l); try reflexivity.
      rewrite app_assoc. f_equal.
      replace [nth (k m) l] with (repeat m 1).
      + rewrite <- repeat_app. rewrite add_comm.
	reflexivity.
      + simpl. f_equal. apply le_antisymm.
	* apply ml_nth_ge; try assumption. lia.
	* assert (nth (k m) l < S m); try lia.
	  apply ml_nth_lt; try assumption. lia.
    }

    assert (forall m k, all (max - m) k ->
      all (max - m) (Sk (max - m) k)
    ). {
      induction m.
      - rewrite sub_0_r. subst all. simpl in *.
	intros k H l L F Hl.
	eapply B; try eassumption; try lia.
	apply le_antisymm; try lia.
	destruct (le_gt_cases (ml (S max) l) 0);
	  try assumption.
	apply ml_nth_ge in H0; try assumption.
	destruct l; simpl in *; try lia.
	inversion F. subst. lia.
      - intros k Hk. unfold all. intros l L F Hl.
	destruct (eq_dec (max - m) 0) as [e | e].
	+ rewrite e in *.
	  replace (max - S m) with 0 in *; try lia.
	  eapply IHm; eassumption.
	(*generalize (GR l a k). intros R.
	set (p := k a).
	set (j := repeat a (S p) ++ skipn (S p) l).
	assert (exists n, olist_nth max n = j). {
	  destruct eha as [n Hn]; try assumption.
	  exists (S n).
	  simpl. rewrite Hn. subst j.
	  subst p. apply R; try assumption.
	}*)

	(*remember (ml (max - m) l) as mm. destruct mm.
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
		  apply M7 in H0; try assumption; lia.*)
	+ remember (max - S m) as a eqn : Ea.
	  replace (max - m) with (S a) in *; try lia.
	  assert (
	    forall l, sorted l -> Forall_max l ->
	    mlk a (Sk a k) l -> exists n, nh n = l
	  ). {
	    clear dependent l. intros l.
	    remember (ml (S a) l) as x eqn : E.
	    generalize dependent l. induction x; intros.
	    - set (j := repeat a (S (k a)) ++ skipn (S (k a)) l).
	      assert (Hj : exists n, nh n = j). {
		destruct (GR l a k) as [n Hn];
		  try assumption; try lia.
		  exists (S n). simpl. rewrite Hn. subst j.
		  apply NR; try assumption. lia.
	      }
	      destruct Hj. apply B with a k; auto; lia.
	    - set (k1 i := if i =? S a then x else ml i l).
	      apply IHm with k1; try assumption.
	      + subst all. simpl. intros.
		destruct IHx with l0; try assumption.
		* intros. rewrite H4; try lia.
		  subst k1. simpl.
		  destruct (eqb_spec a a); try lia.
		* unfold mlk. intros.
		  rewrite H4; try lia. subst k1. simpl.
		  destruct (eqb_spec i (S a)); try lia.
		  rewrite H1; lia.
		* exists x0. assumption.
	      + unfold mlk. intros. unfold Sk.
		destruct (eqb_spec i (S a)).
		* subst k1. simpl.
		  destruct (eqb_spec i (S a)); try lia.
		  subst. lia.
		* subst k1. simpl.
		  destruct (eqb_spec i (S a)); lia.
	  }
	  apply H; assumption.
    }

    intros.
    remember (length l) as ln.
    generalize dependent l. induction ln; intros.
    - exists 0.
      symmetry in Heqln. apply length_zero_iff_nil in Heqln.
      subst. reflexivity.
    - set (k (i : nat) := ln). specialize H with max k.
      rewrite sub_diag in H.
      subst all. simpl in H. apply H; try assumption.
      + intros. apply IHln; try assumption.
	rewrite <- ml_0. rewrite H4; try lia. reflexivity.
      + unfold mlk, Sk. intros.
	destruct (eqb_spec i 0); try lia.
	subst. rewrite ml_0. rewrite <- Heqln. reflexivity.
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
    assert (M4 : forall l n m, sorted l -> n < length l -> nth n l 0 < m -> ml m l = ml m (firstn n l)). {
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
