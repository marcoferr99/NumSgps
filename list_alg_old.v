Require Export list_nat.
From Coq Require Import Lia.
From mathcomp Require Import binomial.

Global Set Bullet Behavior "Strict Subproofs".


Section lgen.
  Variable (max : nat).
  Local Notation ge_max := (Forall (ge max)).
  Local Notation sorted := (Sorted ge).

  Definition gelist l := sorted l ∧ ge_max l.


  (****************)
  (** * Next list *)
  (****************)

  (** Increase the first number in the list [l] that is less than [max] and set
      all the previous elements to that same (increased) value *)

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
    destruct (next l); [contradiction | discriminate].
  Qed.

  Theorem next_repeat l n m : m < max ->
    next (repeat max n ++ m :: l) =
    repeat (S m) (S n) ++ l.
  Proof.
    intros Hm.
    induction n.
    - simpl. destruct (ltb_spec m max); [reflexivity|lia].
    - simpl. destruct (ltb_spec max max); [lia|].
      rewrite IHn.
      destruct (repeat (S m) (S n) ++ l) eqn : E.
      + exfalso. eapply next_not_nil. eassumption.
      + rewrite <- E. f_equal.
	simpl in E. now injection E.
  Qed.

  Theorem ge_max_next l :
    ge_max l -> ge_max (next l).
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

  Theorem sorted_next l : sorted l -> sorted (next l).
  Proof.
    intros L.
    induction l as [ | h t IH]; simpl;
      [constructor; constructor|].
    inversion L as [|? ? ? Hd].
    destruct (ltb_spec h max).
    - constructor; [assumption|].
      inversion Hd; constructor. lia.
    - remember (next t) as nt.
      destruct nt; constructor; [auto|].
      constructor. lia.
  Qed.

  Theorem gelist_next l : gelist l -> gelist (next l).
  Proof.
    unfold gelist. intros []. split.
    - now apply sorted_next.
    - now apply ge_max_next.
  Qed.

  Theorem length_next l : length (next l) = length l \/
    length (next l) = S (length l).
  Proof.
    induction l; simpl; [intuition | ].
    destruct (ltb_spec a max); simpl; [intuition | ].
    remember (next l) as nl eqn : E. destruct nl.
    - exfalso. eapply next_not_nil. eauto.
    - simpl in *. intuition.
  Qed.

  Theorem length_next_le l : length l <= length (next l).
  Proof.
    generalize (length_next l). intros. intuition lia.
  Qed.


  (************************)
  (** ** Inverse for next *)
  (************************)

  (** This function is not used for now *)

  Fixpoint next_inv l :=
    match l with
    | [] => []
    | h :: t => match t with
       | [] => match h with 0 => [] | S h => [h] end
       | a :: s => if h =? a then max :: next_inv t else
	   match h with
	    | 0 => []
	    | S h => h :: t
	  end
       end
    end.

  Theorem next_inv_nil l : next_inv l <> [] -> l <> [].
  Proof.
    intros H N. apply H. subst. reflexivity.
  Qed.

  Theorem ge_max_next_inv l :
    ge_max l -> ge_max (next_inv l).
  Proof.
    intros F. induction l as [ | h t IH].
    - simpl. constructor.
    - inversion F as [ | n l _ Ft]. subst.
      simpl. destruct t.
      + destruct h; [constructor|].
	inversion F. constructor; [lia|constructor].
      + destruct (eqb_spec h n); [constructor; auto|].
	destruct h; [constructor|].
	inversion F. constructor; [lia|auto].
  Qed.

  Theorem sorted_next_inv l : ge_max l -> sorted l -> sorted (next_inv l).
  Proof.
    intros F L.
    induction l as [ | h t IH]; simpl;
      [constructor; constructor|].
    inversion L as [|? ? ? Hd]. inversion F.
    destruct t.
    - destruct h; constructor; constructor.
    - destruct (eqb_spec h n).
      + constructor; [auto|].
	simpl. destruct t0.
	* destruct n; constructor. lia.
	* subst. destruct (eqb_spec n n0).
	  -- constructor. lia.
	  -- destruct n; constructor. lia.
      + subst. destruct h; constructor; [assumption|].
	inversion Hd. constructor. lia.
  Qed.

  Theorem next_inv_next l :
    gelist l -> next_inv (next l) = l.
  Proof.
    intros [R F]. induction l; [reflexivity|].
    simpl. destruct (ltb_spec a max).
    - simpl. destruct l; [reflexivity|].
      destruct n; [reflexivity|].
      destruct (eqb_spec a n); [|reflexivity].
      subst.
      inversion R. subst. inversion H3. lia.
    - destruct (next l) eqn : E.
      + exfalso. eapply next_not_nil. eassumption.
      + rewrite <- IHl.
	* simpl. destruct (eqb_spec n n); [|lia].
	  replace a with max; [reflexivity|].
	  inversion F. lia.
	* now inversion R.
	* now inversion F.
  Qed.

  Theorem next_next_inv l : l <> [] ->
    gelist l -> next (next_inv l) = l.
  Proof.
    intros l0 [R F]. induction l; [easy|].
    simpl. destruct l.
    - destruct a; [reflexivity|].
      simpl. destruct (ltb_spec a max); [reflexivity|].
      inversion F. lia.
    - destruct (eqb_spec a n).
      + subst. unfold next.
	destruct (ltb_spec max max); [lia|].
	fold next. rewrite IHl; try easy.
	* now inversion R.
	* now inversion F.
      + destruct a; simpl.
	* inversion R. inversion H2. lia.
	* destruct (ltb_spec a max); [reflexivity|].
	  inversion F. lia.
  Qed.


  (**********************)
  (** * List generation *)
  (**********************)

  Fixpoint lgen n :=
    match n with
    | 0 => []
    | S n => next (lgen n)
    end.

  (** Gli elementi delle liste generate da
      [lgen] sono minori o uguali a [max] *)

  Theorem ge_max_lgen n : ge_max (lgen n).
  Proof.
    induction n; [constructor | ].
    simpl. apply ge_max_next. assumption.
  Qed.

  (** Le liste generate da [lgen] sono ordinate. *)

  Theorem sorted_lgen n : sorted (lgen n).
  Proof.
    induction n; [constructor | ].
    simpl. apply sorted_next. assumption.
  Qed.

  Theorem lgen_correct n : gelist (lgen n).
  Proof.
    split; [apply sorted_lgen | apply ge_max_lgen].
  Qed.

  (** [lgen] genera le liste in ordine
      crescente di lunghezza *)

  Theorem length_lgen_le m n :
    m <= n -> length (lgen m) <= length (lgen n).
  Proof.
    intros. induction n.
    - destruct m; lia.
    - destruct (eq_dec m (S n)); try (subst; lia).
      unfold lgen in *. simpl.
      rewrite <- length_next_le. intuition lia.
  Qed.

  Theorem lgen_complete :
    forall l, gelist l -> exists n, lgen n = l.
  Proof.
    assert (repeat_sorted :
      forall n m, sorted (repeat n m)
    ). {
      clear. intros.
      induction m; simpl; constructor; [assumption|].
      destruct m; simpl; constructor. auto.
    }
    assert (sorted_lookup : forall l, sorted l ->
      forall m n, m < length l -> n < length l -> m <= n ->
      l !!! n <= l !!! m
    ). {
      clear. intros l L.
      apply Sorted_StronglySorted in L; [|intros ?; lia].
      induction l; intros m n Lm Ln Le; [simpl in *; lia|].
      inversion L as [|? ? ? F]. subst.
      destruct m, n; simpl; try lia.
      - simpl in Ln.
	eapply Forall_lookup_total_1 in F; [eassumption|].
	lia.
      - apply IHl; simpl in *; try assumption; lia.
    }
    assert (sorted_app_le : forall l b a, a <= b ->
      sorted (l ++ [b]) -> sorted (l ++ [a])
    ). {
      clear. induction b; intros a L Sb.
      - replace a with 0; [assumption|lia].
      - destruct (eq_dec a (S b)); [subst; assumption|].
	apply IHb; [lia|].
	generalize Sb. clear. intros Sb.
	induction l; intros; [constructor;constructor|].
	simpl. destruct l.
	+ constructor; constructor; try constructor.
	  inversion Sb as [|? ? ? Hd]. inversion Hd. lia.
	+ simpl. inversion Sb as [|? ? ? Hd]. subst.
	  constructor; [auto|].
	  inversion Hd. constructor. assumption.
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
      clear. induction l; simpl; auto.
    }
    assert (ml_le :
      forall l n m, n <= m -> ml m l <= ml n l
    ). {
      clear. intros. induction l; [auto|]. simpl.
      destruct (leb_spec m a), (leb_spec n a); lia.
    }
    assert (ml_app :
      forall l h m, ml m (l ++ h) = ml m l + ml m h
    ). {
      clear. intros. induction l; try reflexivity.
      simpl. destruct (leb_spec m a); lia.
    }
    assert (ml_lookup_ge : forall l m n, sorted l ->
      n < ml m l -> l !!! n >= m
    ). {
      clear.
      induction l; intros m n SR L; simpl in L; [lia|].
      destruct n; simpl.
      - destruct (leb_spec m a); [assumption|].
	eapply le_trans.
	+ apply IHl; try eassumption.
	  now inversion SR.
	+ inversion SR as [|? ? ? Hd]; subst; simpl in *.
	  destruct l; simpl; [lia|]. now inversion Hd.
      - apply IHl.
	+ now inversion SR.
	+ destruct (leb_spec m a); lia.
    }
    assert (ml_lookup_lt : forall l m n, sorted l ->
      n < length l -> n >= ml m l -> l !!! n < m
    ). {
      generalize sorted_lookup. clear.
      intros sorted_lookup.
      induction l; intros m n SR LN L; simpl in *; [lia|].
      destruct (leb_spec m a); destruct n; simpl; try lia.
      - apply IHl; try lia. now inversion SR.
      - assert (Sn : 0 <= S n); [lia|].
	eapply sorted_lookup in Sn; try eassumption;
	  simpl in *; lia.
    }
    set (mlk m k l := forall i, i <= m -> ml i l = k i).
    set (
      all m k :=
	forall l, gelist l -> mlk m k l ->
	exists n, lgen n = l
    ).
    set (Sk m k i := if i =? m then S (k i) else k i).
    assert (mlk_Sk :
      forall l m k, mlk m (Sk m k) l -> ml m l = S (k m)
    ). {
      clear. intros l m k Hl. subst mlk Sk. simpl in Hl.
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
      eapply Forall_lookup_total_2.
      intros j Hj.
      apply mlk_Sk in Hl as MS. apply mlk_lt in Hl as ML.
      rewrite length_take_le in Hj; [|lia].
      rewrite lookup_total_take; [|assumption].
      apply ml_lookup_ge; try assumption.
      apply (ml_le l) in Hi. lia.
    }
    assert (FS :
      forall l m k, sorted l -> mlk m (Sk m k) l ->
      Forall (gt m) (drop (S (k m)) l)
    ). {
      intros l m k L Hl.
      eapply Forall_lookup_total_2. intros i Hi.
      rewrite lookup_total_drop.
      apply mlk_Sk in Hl. rewrite length_drop in Hi.
      apply ml_lookup_lt; try assumption; lia.
    }

    assert (GR :
      forall l m k, gelist l ->
      all m k -> mlk m (Sk m k) l -> m <= max ->
      let md := match m with 0 => [] | S n => [n] end in
      let h :=
	repeat max (k m) ++ md ++ skipn (S (k m)) l in
      exists n, lgen n = h
    ). {
      intros l m k [L F] H Hl Lm md h.
      generalize (mlk_lt _ _ _ Hl). clear mlk_lt.
      intros mlk_lt.
      generalize (mlk_Sk _ _ _ Hl). clear mlk_Sk.
      intros mlk_Sk.
      generalize (FS _ _ _ L Hl). clear FS. intros FS.
      assert (Lh : sorted h). {
	subst h. destruct m; subst md.
	- rewrite app_nil_l.
	  remember (drop (S (k 0)) l) as s eqn : E.
	  clear E. destruct s.
	  + rewrite app_nil_r. apply repeat_sorted.
	  + inversion FS. lia.
	- apply Sorted_middle.
	  + apply sorted_app_le with max; [lia|].
	    replace [max] with (repeat max 1);
	      try reflexivity.
	    rewrite <- repeat_app. apply repeat_sorted.
	  + remember (drop (S (k (S m))) l) as s eqn : E.
	    constructor.
	    * rewrite E.
	      rewrite <- (firstn_skipn (S (k (S m)))) in L.
	      apply Sorted_app_r in L. assumption.
	    * inversion FS; constructor. lia.
      }
      apply H; [split|]; try assumption.
      - subst h. apply Forall_app.
	rewrite repeat_replicate.
	split; [apply Forall_replicate; lia|].
	apply Forall_app. split.
	+ subst md.
	  destruct m; constructor; [lia | constructor].
	+ rewrite <- (firstn_skipn (S (k m))) in F.
	  apply Forall_app in F. apply F.
      - intros i Hil. apply Hl in Hil as Hi.
	destruct m.
	+ subst md h. assert (i = 0); [lia|]. subst.
	  destruct (skipn (S (k 0))).
	  * repeat rewrite app_nil_r in *.
	    rewrite ml_0. apply repeat_length.
	  * inversion FS. lia.
	+ generalize (firstn_skipn (k (S m)) l).
	  rewrite drop_lookup; try assumption.
	  intros El. symmetry in El.
	  subst Sk. simpl in Hi, Hl.
	  destruct (eqb_spec i (S m)).
	  * subst. apply le_antisymm.
	    -- destruct (le_gt_cases (ml (S m) h) (k (S m))) as [C | C]; try assumption.
		apply ml_lookup_ge in C; try assumption.
		unfold h in C.
		rewrite lookup_total_app_r in C;
		  rewrite repeat_length in *; [|lia].
		rewrite sub_diag in C.
		subst md. simpl in C. lia.
	    -- assert (length l = length h). {
		 rewrite El. subst h.
		 repeat rewrite length_app.
		 remember (drop (S (k (S m))) l) as s.
		 simpl. f_equal.
		 rewrite firstn_length_le; try lia.
		 symmetry. apply repeat_length.
	       }
	       destruct (le_gt_cases (k (S m)) (ml (S m) h)) as [C | C]; try assumption.
		unfold "<" in C.
		destruct (k (S m)); [subst; lia|].
		apply le_S_n in C.
		apply ml_lookup_lt in C; [|assumption|lia].
		unfold h in C.
		rewrite lookup_total_app_l in C;
		  [|rewrite repeat_length; lia].
		rewrite repeat_replicate in C.
		rewrite lookup_total_replicate_2 in C; lia.
	  * subst md. rewrite <- Hi, El. unfold h.
	    remember (drop (S (k (S m))) l) as s.
	    replace (l !!! (k (S m)) :: s) with ([l !!! (k (S m))] ++ s); try reflexivity.
	    repeat rewrite ml_app. f_equal.
	    -- replace (ml i (take (k (S m)) l)) with (k (S m)).
	       ++ generalize F Hil Lm. clear.
		  intros F Hil Lm.
		  induction (k (S m)); try reflexivity.
		  simpl. destruct (leb_spec i max); lia.
	       ++ eapply Fle in Hl as Fl; try eassumption.
		  remember (firstn (k (S m)) l) as fs.
		  assert (Lk : length fs = k (S m)). {
		    subst fs. apply firstn_length_le. lia.
		  }
		  generalize Lk Fl. clear. intros.
		  remember (k (S m)) as x eqn : E. clear E.
		  generalize dependent x.
		  induction fs;
		    intros; simpl in *; [auto|].
		  destruct (leb_spec i a);
		    [|inversion Fl; lia].
		  destruct x; simpl in Lk; [lia|].
		  f_equal.
		  apply IHfs; simpl in Lk; [|lia].
		  inversion Fl. assumption.
	    -- f_equal. simpl.
	       destruct (leb_spec i m), (leb_spec0 i (l !!! (k (S m)))); try lia.
	       exfalso. apply n0.
	       apply ml_lookup_ge; try assumption.
	       rewrite Hi. apply (ml_le l) in Hil. lia.
    }

    assert (NR :
      forall l m k, sorted l ->
      mlk m (Sk m k) l -> m <= max ->
      let md := match m with 0 => [] | S n => [n] end in
      next (repeat max (k m) ++ md ++ (skipn (S (k m)) l)) = repeat m (S (k m)) ++ (skipn (S (k m)) l)
    ). {
      intros l m k L Hl Lm md.
      generalize (FS _ _ _ L Hl); clear FS; intros FS.
      generalize (mlk_Sk _ _ _ Hl); clear mlk_Sk;
	intros mlk_Sk.
      destruct m.
      + subst md. rewrite app_nil_l.
	remember (skipn (S (k 0)) l) as s.
	destruct s; [|inversion FS; lia].
	repeat rewrite app_nil_r.
	clear. induction (k 0); try reflexivity.
	simpl. destruct (ltb_spec max max); [lia|].
	rewrite IHn. reflexivity.
      + subst md. apply next_repeat. lia.
    }

    assert (B :
    forall l m k, gelist l ->
      all m k -> mlk m (Sk m k) l -> m <= max ->
      ml (S m) l = 0 ->
      exists n, lgen n = l
    ). {
      intros l m k [L F] H Hl Lm Hm.
      generalize (mlk_lt _ _ _ Hl); clear mlk_lt;
	intros mlk_lt.
      generalize (firstn_skipn (k m) l).
      intros El. symmetry in El.
      rewrite drop_lookup in El; try assumption.
      generalize (mlk_Sk _ _ _ Hl); clear mlk_Sk;
	intros mlk_Sk.
      destruct (GR l m k) as [n Hn];
	[split| | | |]; try assumption.
      exists (S n). unfold lgen in *.
      simpl. rewrite Hn. clear Hn n.
      assert (FR : firstn (k m) l = repeat m (k m)). {
	apply list_eq. intros i.
	destruct (le_gt_cases (k m) i).
	- rewrite lookup_ge_None_2;
	    [|rewrite length_take_le; lia].
	  rewrite lookup_ge_None_2; [reflexivity|].
	  now rewrite repeat_length.
	- rewrite list_lookup_lookup_total;
	    [|apply lookup_lt_is_Some; rewrite length_take_le; lia].
	  rewrite list_lookup_lookup_total;
	    [|apply lookup_lt_is_Some; rewrite repeat_length; lia].
	  f_equal.
	  rewrite El in F.
	  apply Forall_app in F as [F _].
	  eapply Forall_lookup_total in Fle;
	    try eassumption.
	  + apply le_antisymm; try eassumption.
	    rewrite lookup_total_take; [|assumption].
	    rewrite repeat_replicate.
	    rewrite lookup_total_replicate_2;
	      [|assumption].
	    assert (l !!! i < S m); [|lia].
	    apply ml_lookup_lt; try assumption; lia.
	  + rewrite repeat_replicate.
	    rewrite lookup_total_replicate_2;
	      [lia|assumption].
	  + rewrite firstn_length_le; lia.
      }
      apply NR in Hl as R; try assumption. clear NR.
      rewrite El at 2. rewrite R, FR.
      replace (l !!! k m :: skipn (S (k m)) l) with ([l !!! k m] ++ skipn (S (k m)) l); try reflexivity.
      rewrite app_assoc. f_equal.
      replace [l !!! k m] with (repeat m 1).
      + rewrite <- repeat_app. now rewrite add_comm.
      + simpl. f_equal. apply le_antisymm.
	* apply ml_lookup_ge; try assumption. lia.
	* assert (l !!! k m < S m); [|lia].
	  apply ml_lookup_lt; try assumption. lia.
    }

    assert (forall m k, all (max - m) k ->
      all (max - m) (Sk (max - m) k)
    ). {
      induction m.
      - rewrite sub_0_r. subst all. simpl in *.
	intros k H l [L F] Hl.
	eapply B; try eassumption; try lia;
	  [split|]; try assumption.
	apply le_antisymm; try lia.
	destruct (le_gt_cases (ml (S max) l) 0);
	  try assumption.
	apply ml_lookup_ge in H0; try assumption.
	destruct l; simpl in *; try lia.
	inversion F. subst. lia.
      - intros k Hk. unfold all. intros l [L F] Hl.
	destruct (eq_dec (max - m) 0) as [e | e].
	+ rewrite e in *.
	  replace (max - S m) with 0 in *; try lia.
	  eapply IHm; try eassumption. now split.
	+ remember (max - S m) as a eqn : Ea.
	  replace (max - m) with (S a) in *; try lia.
	  assert (
	    forall l, sorted l -> ge_max l ->
	    mlk a (Sk a k) l -> exists n, lgen n = l
	  ). {
	    clear dependent l. intros l.
	    remember (ml (S a) l) as x eqn : E.
	    generalize dependent l. induction x; intros.
	    - apply B with a k; auto;
		[split; assumption|].
	      lia.
	    - set (k1 i := if i =? S a then x else ml i l).
	      apply IHm with k1; [|split|]; try assumption.
	      + subst all. simpl. intros. destruct H2.
		destruct IHx with l0; try assumption.
		* intros. rewrite H3; try lia.
		  subst k1. simpl.
		  destruct (eqb_spec a a); lia.
		* unfold mlk. intros.
		  rewrite H3; try lia. subst k1. simpl.
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
      symmetry in Heqln.
      apply length_zero_iff_nil in Heqln.
      subst. reflexivity.
    - set (k (i : nat) := ln). specialize H with max k.
      rewrite sub_diag in H.
      subst all. simpl in H. apply H; try assumption.
      + intros. apply IHln; try assumption.
	rewrite <- ml_0. rewrite H2; try lia. reflexivity.
      + unfold mlk, Sk. intros.
	destruct (eqb_spec i 0); try lia.
	subst. rewrite ml_0. rewrite <- Heqln. reflexivity.
  Qed.


  (************************)
  (** ** Inverse for lgen *)
  (************************)

  Fixpoint lgen_inv_aux n l :=
    match l with
    | [] => 0
    | h :: t =>
	binomial (n + max + 1) (n + 1) -
	binomial (n + max - h) (n + 1) +
	lgen_inv_aux (S n) t
    end.

  Theorem lgen_inv_aux_app n l m :
    lgen_inv_aux n (l ++ m) = lgen_inv_aux n l + lgen_inv_aux (n + length l) m.
  Proof.
    generalize dependent n.
    induction l; simpl; intros; [now rewrite add_0_r|].
    rewrite IHl. rewrite add_assoc. f_equal.
    f_equal. lia.
  Qed.

  Definition lgen_inv := lgen_inv_aux 0.

  Theorem lgen_inv_repeat_aux m n : m <= max ->
    lgen_inv (repeat m n) + binomial (n + max - m) (max - m) = binomial (n + max) (S max) + binomial (n + max) max.
  Proof.
    intros L.
    induction n.
    - unfold lgen_inv. simpl. repeat rewrite binn.
      rewrite bin_small; [lia|].
      apply ssrnat.ltnSn.
    - unfold lgen_inv.
      replace (S n) with (n + 1); [|lia].
      rewrite repeat_app, lgen_inv_aux_app.
      rewrite repeat_length. simpl.
      fold lgen_inv.
      rewrite add_0_r. rewrite add_comm, add_assoc.
      rewrite add_sub_assoc.
      + apply add_sub_eq_r.
	rewrite <- (@bin_sub (n + 1 + max - m)).
	* unfold ssrnat.subn.
	  replace (n + 1 + max - m - (max - m)) with (S n); [|lia].
	  replace (n + 1 + max - m) with (S (n + max - m)); [|lia].
	  rewrite binS. unfold ssrnat.addn.
	  rewrite <- (@bin_sub (n + max - m) n).
	  -- unfold ssrnat.subn.
	     replace (n + max - m - n) with (max - m); [|lia].
	     rewrite add_comm in IHn.
	     rewrite <- (add_assoc (binomial (n + max - m) (S n))).
	     rewrite IHn.
	     rewrite add_comm. repeat rewrite <- add_assoc.
	     f_equal.
	     ++ f_equal. lia.
	     ++ replace (n + (1 + max)) with (S (n + max)); [|lia].
		rewrite binS. unfold ssrnat.addn.
		repeat rewrite <- add_assoc. do 2 f_equal.
		rewrite <- bin_sub.
		** unfold ssrnat.subn. f_equal; lia.
		** destruct (@ssrnat.leP max (S (n + max))).
		   --- reflexivity.
		   --- lia.
	  -- destruct (@ssrnat.leP n (n + max - m)).
	     ++ reflexivity.
	     ++ lia.
	* destruct (@ssrnat.leP (max - m) (n + 1 + max - m)).
	  -- reflexivity.
	  -- lia.
      + generalize (@leq_bin2l (n + max - m) (n + max + 1) (n + 1)). intros M.
        destruct (@ssrnat.leP 'C(n + max - m, n + 1) 'C(n + max + 1, n + 1)).
	* assumption.
	* assert (N : is_true false); [|inversion N].
	  apply M.
	  destruct (@ssrnat.leP (n + max - m) (n + max + 1)).
	  -- reflexivity.
	  -- lia.
  Qed.

  Theorem lgen_inv_repeat m n : m <= max ->
    lgen_inv (repeat m n) = binomial (n + max) (S max) + binomial (n + max) max - binomial (n + max - m) (max - m).
  Proof.
    intros L. symmetry. apply add_sub_eq_r.
    now apply lgen_inv_repeat_aux.
  Qed.

  Theorem lgen_lgen_inv l n m : m < max ->
    lgen_inv (next (repeat max n ++ m :: l)) = S (lgen_inv(repeat max n ++ m :: l)).
  Proof.
    intros L.
    rewrite next_repeat; [|assumption].
    replace (m :: l) with ([m] ++ l); [|reflexivity].
    unfold lgen_inv. repeat rewrite lgen_inv_aux_app.
    rewrite <- add_succ_l, add_assoc.
    repeat rewrite repeat_length. f_equal.
    2:{ simpl. f_equal. lia. }
    fold lgen_inv.
    repeat rewrite lgen_inv_repeat; try lia.
    rewrite sub_diag. rewrite bin0.
    apply add_sub_eq_r.
    assert ('C(n + max, S max) + 'C(n + max, max) > 0). {
      assert ('C(n + max, max) >= 'C(max, max)). {
	generalize (@leq_bin2l max (n + max) max). intros M.
	destruct (@ssrnat.leP 'C(max, max) 'C(n + max, max)).
	- assumption.
	- assert (N : is_true false); [|inversion N].
	  apply M.
	  destruct (@ssrnat.leP max (n + max)).
	  + reflexivity.
	  + lia.
      }
      rewrite binn in H. lia.
    }
    replace (S ('C(n + max, S max) + 'C(n + max, max) - 1)) with ('C(n + max, S max) + 'C(n + max, max)); [|lia].
    rewrite <- add_assoc. rewrite (add_comm (lgen_inv_aux (0 + n) [m])).
    rewrite add_assoc. simpl.
    rewrite add_0_r. rewrite add_sub_assoc.
    - apply add_sub_eq_r.
      rewrite binS. unfold ssrnat.addn.
      repeat rewrite <- add_assoc. do 2 f_equal.
      rewrite <- bin_sub.
      + unfold ssrnat.subn.
	replace (S (n + max) - max) with (n + 1); [|lia].
	rewrite add_comm.
	f_equal.
	* rewrite <- bin_sub.
	  -- unfold ssrnat.subn. f_equal. lia.
	  -- destruct (@ssrnat.leP (n + 1) (n + max - m)).
	     ++ reflexivity.
	     ++ lia.
	* f_equal. lia.
      + destruct (@ssrnat.leP max (S (n + max))).
	* reflexivity.
	* lia.
    - generalize (@leq_bin2l (n + max - m) (n + max + 1) (n + 1)). intros M.
      destruct (@ssrnat.leP 'C(n + max - m, n + 1) 'C(n + max + 1, n + 1)).
      + assumption.
      + assert (N : is_true false); [|inversion N].
	apply M.
	destruct (@ssrnat.leP (n + max - m) (n + max + 1)).
	* reflexivity.
	* lia.
  Qed.

  Theorem lgen_lgen_inv_2 n :
    lgen_inv (next (repeat max n)) = S (lgen_inv(repeat max n)).
  Proof.
    replace (next (repeat max n)) with (repeat 0 (n + 1)).
    - repeat rewrite lgen_inv_repeat; try lia.
      rewrite sub_diag, bin0.
      repeat rewrite sub_0_r.
      rewrite <- add_sub_assoc; [|lia].
      rewrite sub_diag, add_0_r.
      replace (n + 1 + max) with (S (n + max)); [|lia].
      rewrite binS. unfold ssrnat.addn.
      assert ('C(n + max, S max) + 'C(n + max, max) > 0). {
	assert ('C(n + max, max) >= 'C(max, max)). {
	  generalize (@leq_bin2l max (n + max) max). intros M.
	  destruct (@ssrnat.leP 'C(max, max) 'C(n + max, max)).
	  - assumption.
	  - assert (N : is_true false); [|inversion N].
	    apply M.
	    destruct (@ssrnat.leP max (n + max)).
	    + reflexivity.
	    + lia.
	}
	rewrite binn in H. lia.
      }
      lia.
    - induction n; simpl; [reflexivity|].
      destruct (ltb_spec max max); [lia|].
      rewrite IHn. remember (next (repeat max n)) as r eqn : E.
      destruct r.
      + rewrite repeat_app in IHn. simpl in *.
	eapply app_eq_nil. eassumption.
      + f_equal. replace (n + 1) with (S n) in *; [|lia].
	simpl in *. now injection IHn.
  Qed.

  Theorem list_repeat l : gelist l ->
    match list_find (fun x => x < max) l with
    | None => l = repeat max (length l)
    | Some (p, e) => l = repeat max p ++ e :: drop (S p) l
    end.
  Proof.
    intros.
    destruct (list_find _ l) eqn : E.
    - destruct p as [p e].
      replace (repeat max p) with (take p l).
      + symmetry. apply take_drop_middle.
	apply list_find_Some in E. apply E.
      + apply list_find_Some in E.
  Admitted.

  Theorem lgen_inv_next l : gelist l ->
    lgen_inv (next l) = S (lgen_inv l).
  Proof.
    intros G.
    generalize (list_repeat l). intros R.
    destruct (list_find (fun x => x < max) l) eqn : E.
    - destruct p. rewrite R; [|assumption].
      apply lgen_lgen_inv. destruct G.
      apply list_find_Some in E. apply E.
    - rewrite R; [|assumption].
      apply lgen_lgen_inv_2.
  Qed.

  Theorem lgen_inv_lgen l : gelist l ->
    lgen (lgen_inv l) = l.
  Proof.
    intros L.
    destruct (lgen_complete l); [assumption|].
    rewrite <- H in *. clear dependent l.
    induction x; [reflexivity|].
    simpl. intros.
    rewrite lgen_inv_next; [|apply lgen_correct].
    simpl. rewrite IHx; [reflexivity|].
    apply lgen_correct.
  Qed.

End lgen.
