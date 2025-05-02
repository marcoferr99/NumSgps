From Coq Require Import Lia.
Require Export list_nat.


(**********************)
(** * List generation *)
(**********************)

Section nh.
  Variable (max : nat).
  Local Notation Forall_max := (Forall (ge max)).
  Local Notation sorted := (Sorted ge).


  (*****************)
  (** ** Next list *)
  (*****************)

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
    replace (repeat (S m) (S n) ++ l) with (repeat (S m) n ++ next (m :: l)). 2:{
      replace (S n) with (n + 1); try lia.
      rewrite repeat_app. simpl.
      destruct (ltb_spec m max); try lia.
      rewrite <- app_assoc. reflexivity.
    }
    induction n as [ | n IH]; try reflexivity.
    remember (m :: l) as ml. simpl.
    destruct (ltb_spec max max); try lia. rewrite IH.
    remember (repeat (S m) n ++ next ml) as t eqn : Eh.
    destruct t as [ | h t].
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

  Theorem next_sorted l : sorted l -> sorted (next l).
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

  Theorem next_length l : length (next l) = length l \/
    length (next l) = S (length l).
  Proof.
    induction l; simpl; [intuition | ].
    destruct (ltb_spec a max); simpl; [intuition | ].
    remember (next l) as nl eqn : E. destruct nl.
    - exfalso. eapply next_not_nil. eauto.
    - simpl in *. intuition.
  Qed.

  Theorem next_length_le l : length l <= length (next l).
  Proof.
    generalize (next_length l). intros. intuition lia.
  Qed.


  (****************)
  (** ** Nth list *)
  (****************)

  Fixpoint nh n :=
    match n with
    | 0 => []
    | S n => next (nh n)
    end.

  Theorem nh_all : forall l, Forall_max l -> sorted l ->
    exists n, nh n = l.
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
    assert (sorted_app_r :
      forall l h, sorted (l ++ h) -> sorted h
    ). {
      clear. intros. induction l; [assumption|].
      inversion H; now apply IHl.
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
	forall l, sorted l -> Forall_max l -> mlk m k l ->
	exists n, nh n = l
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
	      apply sorted_app_r in L. assumption.
	    * inversion FS; constructor. lia.
      }
      apply H; try assumption.
      - subst h. apply Forall_app.
	split; [apply Forall_repeat; lia|].
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
		Search lookup_total app.
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
      forall l m k, sorted l -> Forall_max l ->
      all m k -> mlk m (Sk m k) l -> m <= max ->
      ml (S m) l = 0 ->
      exists n, nh n = l
    ). {
      intros l m k L F H Hl Lm Hm.
      generalize (mlk_lt _ _ _ Hl); clear mlk_lt;
	intros mlk_lt.
      generalize (firstn_skipn (k m) l).
      intros El. symmetry in El.
      rewrite drop_lookup in El; try assumption.
      generalize (mlk_Sk _ _ _ Hl); clear mlk_Sk;
	intros mlk_Sk.
      destruct (GR l m k) as [n Hn]; try assumption.
      exists (S n). simpl. rewrite Hn. clear Hn n.
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
	intros k H l L F Hl.
	eapply B; try eassumption; try lia.
	apply le_antisymm; try lia.
	destruct (le_gt_cases (ml (S max) l) 0);
	  try assumption.
	apply ml_lookup_ge in H0; try assumption.
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
	    - apply B with a k; auto; lia.
	    - set (k1 i := if i =? S a then x else ml i l).
	      apply IHm with k1; try assumption.
	      + subst all. simpl. intros.
		destruct IHx with l0; try assumption.
		* intros. rewrite H4; try lia.
		  subst k1. simpl.
		  destruct (eqb_spec a a); lia.
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
      symmetry in Heqln.
      apply length_zero_iff_nil in Heqln.
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

  (** [nh] genera le liste in ordine
      crescente di lunghezza *)

  Theorem nh_le_length m n :
    m <= n -> length (nh m) <= length (nh n).
  Proof.
    intros. induction n.
    - destruct m; lia.
    - destruct (eq_dec m (S n)); try (subst; lia).
      simpl. rewrite <- next_length_le. intuition lia.
  Qed.

  (** Gli elementi delle liste generate da
      [nh] sono minori o uguali a [max] *)

  Theorem nh_Forall n : Forall_max (nh n).
  Proof.
    induction n; [constructor | ].
    simpl. apply next_Forall. assumption.
  Qed.

  (** Le liste generate da [nh] sono ordinate. *)

  Theorem nh_sorted n : sorted (nh n).
  Proof.
    induction n; [constructor | ].
    simpl. apply next_sorted. assumption.
  Qed.

End nh.
