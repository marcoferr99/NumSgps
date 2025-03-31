From Coq Require Import FunctionalExtensionality Lia Mergesort Permutation Sorted.
Require Export def.
 

Section max.
  Context (max : nat).
  Local Notation Forall_max := (Forall (ge max)).
  Local Notation sorted := (LocallySorted ge).
  Local Notation nth n l := (nth n l 0).

(** Increase the first number in the list [l] that is less than [max] and set
    all the previous elements to that same (increased) value. *)

  Fixpoint next l :=
    match l with
    | [] => [0]
    | h :: t => if h <? max then S h :: t else
	match next t with
	| [] => []
	| h :: t => h :: h :: t
	end
    end.

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

  Theorem next_sorted l :
    sorted l -> sorted (next l).
  Proof.
    intros L. induction l; simpl; [constructor | ].
    destruct (ltb_spec a max).
    - destruct l; constructor; inversion L; try assumption.
      lia.
    - remember (next l) as nl.
      destruct nl; constructor; try lia.
      apply IHl. inversion L; try constructor.
      assumption.
  Qed.

  Theorem next_length l : length (next l) = length l \/
    length (next l) = S (length l).
  Proof.
    intros. induction l; simpl; [intuition | ].
    destruct (ltb_spec a max); simpl; [intuition | ].
    remember (next l) as nl eqn : E. destruct nl.
    - exfalso. eapply next_not_nil. eauto.
    - rewrite E in *. simpl. intuition.
  Qed.

  Theorem next_length_le l : length l <= length (next l).
  Proof.
    generalize (next_length l). intros. intuition.
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

  Theorem nh_le_length m n :
    m <= n -> length (nh m) <= length (nh n).
  Proof.
    intros. induction n.
    - destruct m; lia.
    - destruct (eq_dec m (S n)).
      + subst. lia.
      + simpl. rewrite <- next_length_le. intuition lia.
  Qed.

  Theorem nh_Forall n : Forall_max (nh n).
  Proof.
    induction n; [constructor | ].
    apply next_Forall. assumption.
  Qed.

  Theorem nh_sorted n : sorted (nh n).
  Proof.
    induction n; [constructor | ].
    simpl. apply next_sorted. assumption.
  Qed.

End max.

Section generators.
  Context (gen : list nat).
  Local Notation nth n l := (nth n l 0).
  Local Notation nh := (nh (length gen - 1)).

  Definition nth_sum n := sum (fun i => nth i gen) (nh n).

  Theorem nth_sum_in A `{numerical_semigroup A} :
    generator A (fun x => List.In x gen) ->
    forall n, A (nth_sum n).
  Proof.
    intros G n.
    destruct (eq_dec (length gen) 0) as [l0 | l0].
    - replace (nth_sum n) with 0; try apply ns_zero.
      unfold nth_sum.
      apply length_zero_iff_nil in l0. subst. simpl.
      remember (compute.nh 0 n) as ls eqn : E. clear E.
      induction ls; try reflexivity.
      simpl. destruct a; rewrite add_0_l; assumption.
    - unfold nth_sum.
      generalize (nh_Forall (length gen - 1) n). intros F.
      remember (nh n) as ls eqn : E.
      remember (length ls) as ln eqn : En. clear E.
      generalize dependent ls.
      induction ln as [ | ln IH]; intros.
      + symmetry in En. apply length_zero_iff_nil in En.
	subst. apply ns_zero.
      + intros. destruct ls; try discriminate.
	simpl. apply ns_closed.
	* destruct G as [G _]. unfold Included, In in G.
	  apply G. apply nth_In. inversion F. subst. lia.
	* apply IH; auto. inversion F. assumption.
  Qed.

  Fixpoint nth_inv l x :=
    match l with
    | [] => 0
    | h :: t => if h =? x then 0 else S (nth_inv t x)
    end.

  Theorem nth_inv_lt l x : List.In x l ->
    nth_inv l x < length l.
  Proof.
    induction l; try contradiction.
    simpl. intros I. destruct (eqb_spec a x); try lia.
    apply Arith_base.lt_n_S_stt. intuition.
  Qed.
  
  Theorem nth_nth_inv l x : List.In x l ->
    nth (nth_inv l x) l = x.
  Proof.
    induction l; try contradiction.
    intros I. simpl.
    destruct (eqb_spec a x); try assumption.
    simpl in I. intuition.
  Qed.

  Theorem Forall_repeat {T} (P : T -> Prop) x n : P x ->
    Forall P (repeat x n).
  Proof. intros. induction n; constructor; assumption. Qed.

  Theorem LocallySorted_rev {T} (P : T -> T -> Prop) l :
    LocallySorted P l ->
    LocallySorted (fun x y => P y x) (rev l).
  Proof.
    assert (
      forall P (l : list T) a h,
      LocallySorted P (l ++ [a]) ->
      LocallySorted P (a :: h) ->
      LocallySorted P (l ++ a :: h)
    ). {
      clear. induction l; intros; try assumption.
      simpl. destruct l; simpl; constructor;
	try assumption; try (inversion H; assumption).
	apply IHl; try assumption. inversion H. assumption.
    }
    intros L. induction l; try constructor.
    destruct l as [ | h t]; [constructor | ]. simpl.
    rewrite <- app_assoc. apply H.
    - apply IHl. inversion L. assumption.
    - inversion L. subst.
      constructor; [constructor | assumption].
  Qed.

  Theorem nth_sum_all A `{numerical_semigroup A} :
    generator A (fun x => List.In x gen) ->
    forall a, A a -> exists n, nth_sum n = a.
  Proof.
    intros [_ G] a Aa.
    destruct (G a Aa) as [r x k Hr].
    set (l := flat_map (fun i => repeat (nth_inv gen (x i)) (k i)) (seq 0 r)).
    set (ol := rev (NatSort.sort l)).
    destruct (nh_all (length gen - 1) ol) as [n Hn].
    - subst ol. apply Forall_rev.
      generalize (NatSort.Permuted_sort l). intros P.
      assert (F : Forall (ge (length gen - 1)) l). {
	unfold l. apply Forall_flat_map.
	generalize dependent Hr. clear.
	remember (seq 0 r) as s eqn : Es.
	assert (Forall (gt r) s). {
	  subst s. induction r; [constructor | ].
	  rewrite seq_S. apply Forall_app. split.
	  - apply Forall_nth. intros.
	    eapply Forall_nth in IHr; try eassumption.
	    eapply le_trans; try eassumption. lia.
	  - constructor; try constructor.
	}
	clear Es. intros Hr. generalize dependent s.
	induction s; [constructor | ].
	constructor.
	- apply Forall_repeat.
	  assert (nth_inv gen (x a) < length gen); try lia.
	  apply nth_inv_lt. apply Hr.
	  inversion H. lia.
	- apply IHs. inversion H. assumption.
      }
      eapply Permutation_Forall in P.
      destruct P; try eassumption; constructor; assumption.
    - subst ol. apply LocallySorted_rev. clear.
      generalize (NatSort.LocallySorted_sort l). intros L.
      unfold is_true in L. fold leb in L.
      remember (NatSort.sort l) as h eqn : E. clear E.
      induction h; [constructor | ].
      destruct h; constructor.
      + apply IHh. inversion L. assumption.
      + inversion L. subst.
	destruct (leb_spec a n); lia.
    - exists n. unfold nth_sum. rewrite Hn. clear n Hn.
      rewrite (sum_Permutation _ _ l).
      + subst l. rewrite sum_flat_map.
	clear Aa. induction r; try reflexivity.
	rewrite seq_S. repeat rewrite sum_app. f_equal.
	* apply IHr. clear IHr. intros. apply Hr. lia.
	* clear IHr. simpl.
	remember (k r) as kr eqn : E. clear E.
	generalize Hr. clear. intros.
	induction kr; try reflexivity.
	simpl. rewrite nth_nth_inv; auto.
	f_equal. f_equal. repeat rewrite add_0_r in IHkr.
	assumption.
      + subst ol. eapply Permutation_trans.
	* symmetry. apply Permutation_rev.
	* symmetry. apply NatSort.Permuted_sort.
  Qed.

  Fixpoint list_min l :=
    match l with
    | [] => 0
    | [x] => x
    | h :: t => Nat.min h (list_min t)
    end.

  Theorem list_min_le l x : List.In x l ->
    list_min l <= x.
  Proof.
    intros. induction l.
    - simpl. lia.
    - simpl. destruct l.
      + simpl in *. intuition lia.
      + inversion H.
	* rewrite le_min_l. lia.
	* rewrite le_min_r. auto.
  Qed.

  Theorem nth_sum_le n :
    nth_sum n >= (length (nh n)) * list_min gen.
  Proof.
    destruct (eq_dec (length gen) 0) as [ | e]. {
      apply length_zero_iff_nil in e.
      rewrite e. simpl. lia.
    }
    unfold nth_sum. remember (nh n) as h eqn : E.
    generalize dependent n.
    induction h; intros; simpl; try lia.
    eapply le_trans.
    - apply add_le_mono_l.
      destruct (nh_all (length gen - 1) h).
      + destruct (nh_Forall (length gen - 1) n);
	  try discriminate.
	  injection E. intros. subst. assumption.
      + destruct (nh_sorted (length gen - 1) n);
	  try discriminate.
	* injection E. intros. subst. constructor.
	* injection E. intros. subst. assumption.
      + eapply IHh. eauto.
    - apply add_le_mono_r. apply list_min_le.
      apply nth_In.
      generalize (nh_Forall (length gen - 1) n). intros.
      rewrite <- E in H. inversion H. subst. lia.
  Qed.

  Theorem nth_sum_all_le A `{numerical_semigroup A} :
    generator A (fun x => List.In x gen) ->
    forall m a, A a -> a < (length (nh m)) * list_min gen ->
    exists n, n < m /\ nth_sum n = a.
  Proof.
    intros.
    destruct (nth_sum_all A H0 a); try assumption.
    exists x. split; try assumption. subst.
    destruct (ltb_spec x m); try assumption.
    apply Arith_base.lt_not_le_stt in H2.
    exfalso. apply H2.
    eapply le_trans. 2:{ apply nth_sum_le. }
    apply mul_le_mono_r. apply nh_le_length. lia.
  Qed.


  Fixpoint nth_sum_list_aux n :=
    match n with
    | 0 => []
    | S n => nth_sum n :: nth_sum_list_aux n
    end.

  Fixpoint sorted_nodup l :=
    match l with
    | [] => []
    | x :: t =>
	match t with
	| [] => [x]
	| y :: s => if x =? y then sorted_nodup t else
	   x :: sorted_nodup t
        end
    end.

  Theorem sorted_nodup_In l a : List.In a l ->
    List.In a (sorted_nodup l).
  Proof.
    intros L. induction l; [inversion L | ].
    simpl in *. destruct l.
    - constructor. intuition. inversion H.
    - destruct (eqb_spec a0 n).
      + subst. apply IHl. intuition.
	subst. constructor. reflexivity.
      + simpl. intuition.
  Qed.

  Definition nth_sum_list n :=
    sorted_nodup (NatSort.sort (nth_sum_list_aux n)).

  Definition nth_limit n := length (nh n) * list_min (gen).

  Theorem nth_sum_list_all A `{numerical_semigroup A} n :
    generator A (fun x => List.In x gen) ->
    forall a, A a -> a < nth_limit n ->
    List.In a (nth_sum_list n).
  Proof.
    intros.
    destruct (nth_sum_all_le _ H0 n a); try assumption.
    destruct H3. subst.
    generalize H3. clear. intros.
    unfold nth_sum_list. apply sorted_nodup_In.
    eapply Permutation_in; try apply NatSort.Permuted_sort.
    generalize dependent x. intros. induction n.
    - simpl. replace x with 0; try lia.
    - simpl. destruct (eq_dec x n).
      + subst. left. reflexivity.
      + right. apply IHn; try lia.
  Qed.

  Definition nth_sum_list2 n :=
    filter (fun x => x <? nth_limit n) (nth_sum_list n).

  Theorem nth_sum_list2_all A `{numerical_semigroup A} n :
    generator A (fun x => List.In x gen) ->
    forall a, A a -> Exists (le a) (nth_sum_list2 n) ->
    List.In a (nth_sum_list2 n).
  Proof.
    intros. unfold nth_sum_list2 in *.
    apply filter_In. apply Exists_exists in H2.
    destruct H2. destruct H2.
    apply filter_In in H2. destruct H2.
    destruct (ltb_spec x (nth_limit n)); try discriminate.
    clear H4. unfold le in H3.
    split.
    - eapply nth_sum_list_all; try eassumption. lia.
    - destruct (ltb_spec a (nth_limit n)); try reflexivity.
      lia.
  Qed.

  Fixpoint list_eq l m :=
    match l, m with
    | [], [] => true
    | hl :: tl, hm :: tm => if hl =? hm then list_eq tl tm else false
    | _, _ => false
    end.

  Theorem list_eq_iff l m : list_eq l m = true <-> l = m.
  Proof.
    split; intros.
    - generalize dependent m. induction l; simpl in *.
      + destruct m; [reflexivity | discriminate].
      + destruct m; try discriminate.
	intros. destruct (eqb_spec a n); try lia.
	subst. f_equal. apply IHl. assumption.
    - generalize dependent m. induction l; simpl; intros.
      + destruct m; try discriminate. reflexivity.
      + destruct m; try discriminate.
	destruct (eqb_spec a n).
	* apply IHl. injection H. auto.
	* injection H. intros. contradiction.
  Qed.

  Definition is_seq l n :=
    match n, l with
    | 0, [] => true
    | _, h :: t => list_eq l (seq h n)
    | S n, [] => false
    end.

  Theorem is_seq_th l n :
    is_seq l n = true <-> exists a, seq a n = l.
  Proof.
    split; intros.
    - destruct l, n; simpl in *; try discriminate.
      + exists 0. reflexivity.
      + destruct (eqb_spec n0 n0); try lia.
	apply list_eq_iff in H. exists n0.
	f_equal. auto.
    - destruct H.
      destruct l, n; simpl in *; try discriminate; try reflexivity.
      destruct (eqb_spec n0 n0); try lia.
      apply list_eq_iff. injection H. intros. subst.
      reflexivity.
  Qed.

  Fixpoint find_seq l n :=
    match l with
    | [] => None
    | h :: t => if list_eq l (seq h n) then Some h
	else find_seq t n
    end.

  Theorem find_seq_th l n p : find_seq l n = Some p ->
    exists h t, l = h ++ seq p n ++ t.
  Proof.
    intros. induction l.
    - simpl in *. discriminate.
    - simpl in H. remember (seq a n) as sq.
      destruct sq.
      + apply IHl in H. destruct H. destruct H.
	exists (a :: x), x0. simpl. f_equal. assumption.
      + destruct (eqb_spec a n0).
	* subst. remember (list_eq l sq) as b.
	  destruct b.
	  -- injection H as H. subst.
	     symmetry in Heqb. apply list_eq_iff in Heqb.
	     subst. exists [], []. simpl.
	     rewrite app_nil_r. assumption.
	  -- apply IHl in H. destruct H. destruct H.
	     exists (n0 :: x), x0. simpl. f_equal.
	     assumption.
	* apply IHl in H. do 2 destruct H.
	  exists (a :: x), x0. simpl. f_equal. assumption.
  Qed.

  Theorem find_seq_th2


  Compute test0 [1;2;3;7;8;10] 1 1.

  Fixpoint test l n p m c :=
    match m with
    | 0 => Some p
    | S m =>
	match l with
        | [] => None
        | x :: t => if x =? c then test t n p m (S c)
	    else test t n x n (S x)
        end
    end.

  Definition test2 l n :=
    match n, l with
    | 0, _ => None
    | _, [] => test l n 0 n 0
    | S n, x :: t => test t n x n (S x)
    end.

  Theorem test2_th l n m: test2 l n = Some m ->
    forall x, x < n -> List.In (x + m) l.
  Proof.
    intros. destruct l, n; simpl in *; try discriminate.
    induction l.
    - simpl in *. destruct n.
      + injection H. intros. lia.
      + discriminate.
    - simpl in *.
      destruct n.
      + injection H. intros. subst. lia.
      + destruct (eqb_spec a (S n0)).
	* subst.
    intros. generalize dependent l.
    induction n; try lia. intros.
    unfold test2 in *.
    simpl in H. destruct l.
    - destruct (eqb_spec n 0); try discriminate.
      subst. injection H. intros. subst.
      replace x with 0; try lia. simpl.
      left. reflexivity.
    - destruct n1.
      +

  Definition last l := test2 l (list_min gen).

  Theorem t A `{numerical_semigroup A} l n :
    generator A (fun x => List.In x gen) ->
    list_min gen <> 0 ->
    last l = Some n ->
    forall a, a >= n -> A a.
  Proof.
    intros.

End generators.

Compute test2 [72;73;74] 3.
Compute test [0;2;76;2;3;4] 3 0.
Compute nth_sum_list2 [4;7;10] 35.
Compute test2 (nth_sum_list2 [4;7;10] 35) 4.
Compute nth_sum_list_limit [4;7;10] 16.
Compute sorted_nodup (NatSort.sort (nth_sum_list [4;7;10] 21)).

  Fixpoint nh_limit l n :=
    if (length (nh n) =? l) then n
    else 
    match (nh n) with

    let 
    match (


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
