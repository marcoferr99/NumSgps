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
Compute olist_add 3 [0;2;0].

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

Theorem t2 max : forall l, Forall (fun x => x <= max) l ->
  LocallySorted ge l -> exists n, olist_nth max n = l.
Proof.
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
      * subst h. repeat rewrite length_app.
	rewrite length_skipn.
	rewrite <- (firstn_skipn k l) at 1.
	rewrite length_app. f_equal. rewrite length_skipn.
	simpl. lia.
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
	   rewrite (H4 l k).
	   ++ rewrite <- Heqy. reflexivity.
	   ++ lia.
	--
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
