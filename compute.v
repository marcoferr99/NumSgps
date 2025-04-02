From Coq Require Import FunctionalExtensionality Lia Mergesort Permutation Sorted.
Require Export def.
Require Import list.
 

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

  Fixpoint nh n :=
    match n with
    | 0 => []
    | S n => next (nh n)
    end.

(** Voglio dimostrare per induzione sulla lunghezza di [l].  Se è [0], allora
    [l] è la lista vuota e [nh 0 = l].  Devo dimostrare che se il teorema è vero
    per le liste di lunghezza [k] allora è vero per le liste di lunghezza [S k].

    Per ogni lista [l] e per ogni naturale [i] sia [ml i l], che chiamiamo
    [i]-lunghezza di [l], il numero di elementi di [l] che sono maggiori o
    uguali a [i].  In particolare, [ml 0 l] è la lunghezza di [l].

    Per ogni [m] naturale e per ogni [k] funzione dai naturali nei naturali sia
    [all m k] la proposizione: per ogni lista [l] ordinata e con elementi minori
    o uguali a [max], se per ogni [i] da [0] a [m] la [i]-lunghezza di [l] è [k
    i] allora [l] è generata dall'algoritmo.  In particolare, [all 0 k]
    corrisponde alla proposizione: tutte le liste ordinate e con elementi minori
    o uguali a [max] di lunghezza [k 0] sono generate.

    Per ogni [m] naturale e per ogni [k] funzione dai naturali nei naturali sia
    [Sk m k] la funzione che a [m] associa [S (k i)] e che applicata agli altri
    naturali è uguale a [k].  Vorrei dimostrare che per ogni [k] si ha che [all
    0 k] implica [all 0 (Sk 0 k)].  Infatti [all 0 (Sk 0 k)] corrisponde alla
    proposizione: tutte le liste ordinate e con elementi minori o uguali a [max]
    di lunghezza [S (k 0)] sono generate.

    Se dimostro che per ogni [m] naturale e [k] funzione dai naturali ai
    naturali si ha che [all (max - m) k -> all (max - m) (Sk (max - m) k)]
    allora in particolare è vero per [m = max], che è ciò che voglio dimostrare.
    Lo dimostro per induzione su [m].

    Siano [k] una funzione dai naturali ai naturali e sia [m] minore o uguale a
    [max].  Supponiamo che valga [all m k].  Sia [l] una lista ordinata e con
    elementi minori o uguali a [max] tale che per ogni [i] minore o uguale a [m]
    la [i]-lunghezza di [l] è [(Sk m k) i].  Sia [h] la lista [repeat max (k m)
    ++ md ++ skipn (S (k m)) l], dove [md] è la lista vuota se [m] è zero, ed è
    la lista con il solo elemento [m - 1] altrimenti.  Allora [h] è generata.
    Inoltre si ha che [next h] è uguale a [repeat m (S (k m)) ++ (skipn (S (k
    m)) l)].

    Siano [k] una funzione dai naturali ai naturali e sia [m] minore o uguale a
    [max].  Supponiamo che valga [all m k].  Sia [l] una lista ordinata e con
    elementi minori o uguali a [max] tale che per ogni [i] minore o uguale a [m]
    la [i]-lunghezza di [l] è [(Sk m k) i].  Se la [S m]-lunghezza di [l] è zero
    allora [l] è generata.

    Torniamo alla dimostrazione per induzione su [m].  Se [m] è zero, devo
    dimostrare che per ogni [k] si ha che [all max k -> all max (Sk max k)].
    Sia [l] una lista ordinata e con elementi minori o uguali a [max] tale che
    per ogni [i] minore o uguale a [max] la [i]-lunghezza di [l] è [(Sk max k)
    i].  La [S max]-lunghezza di [l] è zero, in quanto [l] non ha elementi
    maggiori di [max].  Quindi, per quanto sopra, [l] è generata.

    Supponiamo ora che per ogni [k] si abbia [all (max - m) k -> all (max - m)
    (Sk (max - m) k)] e dimostriamo che per ogni [k] si ha che [all (max - S m)
    k -> all (max - S m) (Sk (max - S m) k)].

    Sia [a := max - S m].  Allora [S a = max - m].  Sia [l] una lista ordinata e
    con elementi minori o uguali a [max] tale che per ogni [i] fra [0] e [a] la
    [i]-lunghezza di [l] è [Sk a k i].  Sia [x] = [ml (S a) l].  Dimostro per
    induzione su [x] che [l] è generata.  Se [x] è zero [l] è generata per
    quanto sopra.

    Supponiamo che tutte le liste come sopra con [ml (S a) l = x] siano
    generate, e dimostriamo che le liste come sopra e con [ml (S a) l = S x]
    sono generate.  Sia [k1] la funzione che a [S a] associa [x] e che agli
    altri naturali [i] associa [ml i l] Allora per ipotesi induttiva (su [x]),
    vale [all (S a) k1], e dato che per ipotesi induttiva su [m] vale [all (S a)
    k1 -> all (S a) (Sk (S a) k1)], abbiamo allora [all (S a) (Sk (S a) k1))].
    Dato che le [i]-lunghezze di [l] sono date dalla funzione [Sk (S a) k1], la
    lista [l] è generata. **)

  Theorem nh_all : forall l, Forall_max l -> sorted l ->
    exists n, nh n = l.
  Proof.
    assert (repeat_sorted :
      forall n m, sorted (repeat n m)
    ). {
      clear. intros. induction m; try constructor.
      simpl. remember (repeat n m) as r eqn : Er.
      destruct r; constructor; try assumption.
      destruct m; try discriminate. injection Er. lia.
    }
    assert (sorted_nth : forall l, sorted l ->
      forall m n, m < length l -> n < length l -> m <= n ->
      nth n l <= nth m l
    ). {
      clear. intros l L.
      apply Sorted_LocallySorted_iff in L.
      apply Sorted_StronglySorted in L.
      2: { unfold Transitive. lia. }
      induction l; intros m n Lm Ln Le;
	try (simpl in *; lia).
      inversion L. subst. destruct m, n; simpl; try lia.
      - simpl in Ln.
	eapply (Forall_nth (ge a) l) in H2;
	  try eassumption.
	lia.
      - apply IHl; simpl in *; try assumption; lia.
    }
    assert (sorted_app_le : forall l b a, a <= b ->
      sorted (l ++ [b]) -> sorted (l ++ [a])
    ). {
      clear. induction b; intros a L Sb.
      - replace a with 0; try lia. assumption.
      - destruct (eq_dec a (S b)); try (subst; assumption).
	apply IHb; try lia. generalize Sb. clear.
	intros Sb. induction l; intros; [constructor | ].
	simpl. destruct l.
	+ constructor; try constructor.
	  inversion Sb. lia.
	+ simpl. inversion Sb. subst.
	  constructor; try assumption.
	  apply IHl. assumption.
    }
    assert (sorted_app_r :
      forall l h, sorted (l ++ h) -> sorted h
    ). {
      clear. intros. induction l; try assumption.
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
      clear. induction l; simpl; auto.
    }
    assert (ml_le :
      forall l n m, n <= m -> ml m l <= ml n l
    ). {
      clear. intros. induction l; auto. simpl.
      destruct (leb_spec m a), (leb_spec n a); lia.
    }
    assert (ml_app :
      forall l h m, ml m (l ++ h) = ml m l + ml m h
    ). {
      clear. intros. induction l; try reflexivity.
      simpl. destruct (leb_spec m a); lia.
    }
    assert (ml_nth_ge : forall l m n, sorted l ->
      n < ml m l -> nth n l >= m
    ). {
      clear.
      induction l; intros m n SR L; simpl in L; try lia.
      simpl. destruct n.
      - destruct (leb_spec m a); try lia.
	eapply le_trans.
	+ apply IHl; try eassumption.
	  inversion SR; [constructor | assumption].
	+ inversion SR; subst; simpl in *;
	    [lia | assumption].
      - apply IHl.
	+ inversion SR; [constructor | assumption].
	+ destruct (leb_spec m a); lia.
    }
    assert (ml_nth_lt : forall l m n, sorted l ->
      n < length l -> n >= ml m l -> nth n l < m
    ). {
      generalize sorted_nth. clear. intros sorted_nth.
      induction l; intros m n SR LN L; simpl in *; try lia.
      destruct (leb_spec m a); destruct n; try lia.
      - apply IHl; try lia.
	inversion SR; [constructor | assumption].
      - assert (Sn : 0 <= S n); try lia.
	eapply sorted_nth in Sn; try eassumption;
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
      apply Forall_nth. intros j d Hj.
      rewrite (nth_indep _ _ 0); try assumption. clear d.
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
      rewrite (nth_indep _ _ 0); try assumption. clear d.
      rewrite nth_skipn. apply mlk_Sk in Hl.
      rewrite length_skipn in Hi.
      apply ml_nth_lt; try assumption; lia.
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
	  remember (skipn (S (k 0)) l) as s eqn : E.
	  clear E. destruct s.
	  + rewrite app_nil_r. apply repeat_sorted.
	  + inversion FS. lia.
	- apply LocallySorted_middle.
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
	+ subst md h. assert (i = 0); try lia. subst.
	  destruct (skipn (S (k 0))).
	  * repeat rewrite app_nil_r in *.
	    rewrite ml_0. apply repeat_length.
	  * inversion FS. lia.
	+ generalize (firstn_skipn (k (S m)) l).
	  rewrite (skipn_nth 0); try assumption.
	  intros El. symmetry in El.
	  subst Sk. simpl in Hi, Hl.
	  destruct (eqb_spec i (S m)).
	  * subst. apply le_antisymm.
	    -- destruct (le_gt_cases (ml (S m) h) (k (S m))) as [C | C]; try assumption.
		apply ml_nth_ge in C; try assumption.
		unfold h in C.
		rewrite app_nth2 in C;
		  rewrite repeat_length in *; try lia.
		rewrite sub_diag in C.
		subst md. simpl in C. lia.
	    -- assert (length l = length h). {
		 rewrite El. subst h.
		 repeat rewrite length_app.
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
		unfold h in C.
		rewrite app_nth1 in C;
		  try (rewrite repeat_length; lia).
		rewrite nth_repeat_lt in C; lia.
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
		  assert (Lk : length fs = k (S m)). {
		    subst fs. apply firstn_length_le. lia.
		  }
		  generalize Lk Fl. clear. intros.
		  remember (k (S m)) as x eqn : E. clear E.
		  generalize dependent x.
		  induction fs;
		    intros; simpl in *; try lia.
		  destruct (leb_spec i a);
		    try (inversion Fl; lia).
		  destruct x; simpl in Lk; try lia.
		  f_equal.
		  apply IHfs; simpl in Lk; try lia.
		  inversion Fl. assumption.
	    -- f_equal. simpl.
	       destruct (leb_spec i m), (leb_spec0 i (nth (k (S m)) l)); try lia.
	       exfalso. apply n0.
	       apply ml_nth_ge; try assumption. rewrite Hi.
	       apply (ml_le l) in Hil. lia.
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
	destruct s; try (inversion FS; lia).
	repeat rewrite app_nil_r.
	clear. induction (k 0); try reflexivity.
	simpl. destruct (ltb_spec max max); try lia.
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
      rewrite (skipn_nth 0) in El; try assumption.
      generalize (mlk_Sk _ _ _ Hl); clear mlk_Sk;
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

  Theorem nh_le_length m n :
    m <= n -> length (nh m) <= length (nh n).
  Proof.
    intros. induction n.
    - destruct m; lia.
    - destruct (eq_dec m (S n)); try (subst; lia).
      simpl. rewrite <- next_length_le. intuition lia.
  Qed.

  Theorem nh_Forall n : Forall_max (nh n).
  Proof.
    induction n; [constructor | ].
    simpl. apply next_Forall. assumption.
  Qed.

  Theorem nh_sorted n : sorted (nh n).
  Proof.
    induction n; [constructor | ].
    simpl. apply next_sorted. assumption.
  Qed.

End max.

Section generators.
  Context (gen : list nat) (G0 : gen <> []).
  Local Notation nth n l := (nth n l 0).
  Local Notation nh := (nh (length gen - 1)).

  Definition nth_sum n := sum (fun i => nth i gen) (nh n).

  Theorem nh_lt_length n : Forall (gt (length gen)) (nh n).
  Proof.
    assert (L : length gen <> 0). {
      intros C. apply G0.
      apply length_zero_iff_nil. assumption.
    }
    apply Forall_nth. intros.
    assert (List.nth i (nh n) d <= length gen - 1);
      try lia.
    generalize (nh_Forall (length gen - 1) n). intros F.
    eapply Forall_nth in F; try apply H. eassumption.
  Qed.

  Theorem nth_sum_in A `{numerical_semigroup A} :
    generator A (Inl gen) -> forall n, A (nth_sum n).
  Proof.
    intros G n. unfold nth_sum.
    generalize (nh_lt_length n). intros F.
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

  Theorem nth_sum_all A `{numerical_semigroup A} :
    generator A (Inl gen) ->
    forall a, A a -> exists n, nth_sum n = a.
  Proof.
    intros [_ G] a Aa.
    destruct (G a Aa) as [r x k Hr].
    set (l := flat_map (fun i => repeat (nth_inv 0 gen (x i)) (k i)) (seq 0 r)).
    set (ol := rev (NatSort.sort l)).
    destruct (nh_all (length gen - 1) ol) as [n Hn].
    - apply Forall_impl with (P := gt (length gen));
	try (intros; lia).
      subst ol. apply Forall_rev.
      generalize (NatSort.Permuted_sort l). intros P.
      eapply Permutation_Forall; try eassumption.
      unfold l. apply Forall_flat_map.
      apply Forall_nth. intros.
      rewrite (nth_indep _ _ 0); try lia.
      apply Forall_repeat. apply nth_inv_lt.
      apply Hr. rewrite length_seq in H0.
      rewrite seq_nth; lia.
    - subst ol. apply LocallySorted_rev. clear.
      generalize (NatSort.LocallySorted_sort l). intros L.
      eapply LocallySorted_iff; try eassumption.
      intros. unfold is_true. fold leb.
      destruct (leb_spec x0 y); lia.
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
	  simpl. unfold Inl in *.
	  rewrite nth_nth_inv; auto.
	  f_equal. f_equal. repeat rewrite add_0_r in IHkr.
	  assumption.
      + subst ol. eapply Permutation_trans; symmetry.
	* apply Permutation_rev.
	* apply NatSort.Permuted_sort.
  Qed.


  Definition nth_limit n := length (nh n) * list_min gen.

  Theorem nth_sum_le n : nth_sum n >= nth_limit n.
  Proof.
    unfold nth_limit, nth_sum.
    generalize (nh_lt_length n). intros F.
    remember (nh n) as h eqn : E. clear E.
    induction h; simpl; try lia.
    eapply le_trans.
    - apply add_le_mono_l. eapply IHh.
      inversion F. assumption.
    - apply add_le_mono_r. apply list_min_le.
      apply nth_In. inversion F. assumption.
  Qed.

  Theorem nth_sum_all_le A `{numerical_semigroup A} :
    generator A (fun x => In x gen) ->
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

  Theorem sorted_nodup_In l a : In a l ->
    In a (sorted_nodup l).
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
    generator A (fun x => In x gen) ->
    forall a, A a -> a < nth_limit n ->
    In a (nth_sum_list n).
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
    generator A (fun x => In x gen) ->
    forall a, A a -> Exists (le a) (nth_sum_list2 n) ->
    In a (nth_sum_list2 n).
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

  Fixpoint find_sub_aux p l s :=
    if list_eq (firstn (length s) l) s then p else
      match l with
      | [] => p
      | h :: t => find_sub_aux (S p) t s
      end.

  Theorem find_sub_aux_th p l s :
    find_sub_aux (S p) l s = S (find_sub_aux p l s).
  Proof.
    generalize dependent p. induction l.
    - simpl. destruct (list_eq (firstn (length s) []));
	reflexivity.
    - intros. simpl.
      destruct (list_eq (firstn (length s) (a :: l)) s);
	try reflexivity.
	apply IHl.
  Qed.

  Definition find_sub := find_sub_aux 0.

  Theorem find_sub_th l s : l <> [] ->
    let p := find_sub l s in
    p < length l <-> exists h t, l = h ++ s ++ t.
  Proof.
    intros N p. subst p. split; intros.
    - clear N. induction l; simpl in *; try lia.
      remember (list_eq (firstn (length s) l) s) as b.
      destruct b.
      + symmetry in Heqb. apply list_eq_iff in Heqb.
	exists [a], (skipn (length s) l).
	simpl. f_equal. rewrite <- Heqb at 1.
	symmetry. apply firstn_skipn.
      + unfold find_sub in *. simpl in *.
	remember (list_eq (firstn (length s) (a :: l)) s) as b.
	destruct b.
	* symmetry in Heqb0. apply list_eq_iff in Heqb0.
	  exists [], (skipn (length s) (a :: l)).
	  rewrite <- Heqb0 at 1. simpl.
	  symmetry. apply firstn_skipn.
	* rewrite find_sub_aux_th in H.
	  destruct IHl; try lia. destruct H0.
	  exists (a :: x), x0. simpl. subst l. reflexivity.
    - destruct H. destruct H. subst l. induction x.
      + simpl. unfold find_sub.
	remember (s ++ x0) as l. destruct l.
	* simpl in *. contradiction N. reflexivity.
	* simpl in *.
	  remember (list_eq (firstn (length s) (n :: l)) s) as b.
	  destruct b; try lia.
	  assert (firstn (length s) (n :: l) <> s). {
	    intros C. apply list_eq_iff in C.
	    rewrite C in Heqb. discriminate.
	  }
	  contradiction H. rewrite Heql.
	  rewrite firstn_app. rewrite sub_diag.
	  rewrite firstn_all. rewrite firstn_O.
	  rewrite app_nil_r. reflexivity.
      + simpl in *. destruct s. {
	  simpl in *. unfold find_sub. simpl. lia.
	}
	unfold find_sub. remember (n :: s) as s1.
	unfold find_sub_aux.
	remember (list_eq (firstn (length s1) (a :: x ++ s1 ++ x0)) s1) as b.
	destruct b; try lia.
	rewrite find_sub_aux_th.
	apply Arith_base.lt_n_S_stt. apply IHx.
	subst s1.
	replace ((n :: s) ++ x0) with (n :: (s ++ x0)); try reflexivity.
	symmetry. apply app_cons_not_nil.
  Qed.

  Fixpoint find_seq_aux p l n :=
    match l with
    | [] => p
    | h :: t => if list_eq (firstn n l) (seq h n) then p
	else find_seq_aux (S p) t n
    end.

  Theorem find_seq_aux_th p l n :
    find_seq_aux (S p) l n = S (find_seq_aux p l n).
  Proof.
    generalize dependent p. induction l; intros.
    - simpl. reflexivity.
    - simpl. remember (list_eq (firstn n (a :: l)) (seq a n)) as b.
      destruct b; try reflexivity.
      apply IHl.
  Qed.

  Definition find_seq := find_seq_aux 0.

  Theorem find_seq_th l n : find_seq l n < length l ->
    exists t, l = firstn (find_seq l n) l ++ seq (nth (find_seq l n) l) n ++ t.
  Proof.
    intros. induction l; try (simpl in *; lia).
    simpl. unfold find_seq in *. simpl in *.
    remember (seq a n) as sq.
    remember (list_eq (firstn n (a :: l)) sq) as b.
    destruct b.
    - symmetry in Heqb. apply list_eq_iff in Heqb.
      rewrite <- Heqb in *. rewrite <- Heqsq.
      exists (skipn n (a :: l)). simpl.
      symmetry. apply firstn_skipn.
    - destruct IHl.
      + rewrite find_seq_aux_th in H. lia.
      + rewrite find_seq_aux_th.
	exists x. simpl. rewrite H0 at 1.
	reflexivity.
  Qed.

  Theorem t1 a l n : find_seq (a :: l) n <> 0 ->
    firstn n (a :: l) <> seq a n.
  Proof.
    intros. unfold find_seq in H. simpl in H.
    remember (list_eq (firstn n (a :: l)) (seq a n)) as b.
    destruct b; try contradiction.
    intros C. apply list_eq_iff in C. rewrite C in Heqb.
    discriminate.
  Qed.

  Theorem t2 a l n h :
    find_seq (h ++ a :: l) n > length h ->
    firstn n (a :: l) <> seq a n.
  Proof.
    induction h; intros.
    - simpl in *. apply t1. lia.
    - simpl in *.
      unfold find_seq in H. simpl in H.
      remember (list_eq (firstn n (a0 :: h ++ a :: l)) (seq a0 n)) as b.
      destruct b; try lia.
      apply IHh. rewrite find_seq_aux_th in H.
      unfold find_seq. lia.
  Qed.

  Theorem find_seq_first l n m : find_seq l n < length l ->
    find_seq l n = S m -> S (nth m l) <> nth (S m) l.
  Proof.
    intros. intros C.
    apply find_seq_th in H as F. destruct F.
    rewrite H0 in H1.
    assert (exists h, firstn (S m) l = h ++ [nth m l]). {
      rewrite H0 in H. generalize H. clear. intros.
      remember (nth m l) as n eqn : E.
      rewrite <- (firstn_skipn m l). subst n.
      rewrite firstn_app.
      rewrite firstn_length_le; try lia.
      replace (S m - m) with 1; try lia.
      rewrite (skipn_nth 0); try lia.
      exists (firstn (S m) (firstn m l)). reflexivity.
    }
    destruct H2. rewrite H2 in H1.
    repeat rewrite app_assoc in H1.
    rewrite <- (app_assoc x0) in H1.
    simpl in H1. rewrite <- app_assoc in H1.
    assert (firstn n (nth m l :: seq (nth (S m) l) n) = seq (nth m l) n). {
      rewrite <- C. remember (nth m l) as a. clear.
      generalize dependent a. induction n; try reflexivity.
      intros. simpl. f_equal. apply IHn.
    }
    rewrite <- (firstn_skipn n (nth m l :: seq (nth (S m) l) n)) in H1.
    rewrite H3 in H1.
    repeat rewrite <- app_assoc in H1.
    remember (skipn n (nth m l :: seq (nth (S m) l) n) ++ x) as t eqn : E. clear E.
    clear H3.
    assert (length x0 = m). {
      apply (f_equal (@length nat)) in H2.
      rewrite firstn_length_le in H2; try lia.
      rewrite length_app in H2. simpl in H2. lia.
    }
    remember (seq (nth m l) n) as sq. destruct sq.
    - simpl in *. destruct n.
      + simpl in *. unfold find_seq in *. destruct l.
	* simpl in *. lia.
	* simpl in *. lia.
      + simpl in *. discriminate.
    - assert (find_seq l n > m); try lia.
      rewrite H1 in H4. simpl in H4.
      rewrite <- H3 in H4. apply t2 in H4.
      destruct n.
      + simpl in *. discriminate.
      + apply H4.
	replace (n0 :: sq ++ t) with ((n0 :: sq) ++ t); try reflexivity.
	rewrite firstn_app. rewrite Heqsq.
	replace (S n) with (length (seq (nth m l) (S n))) at 1 3.
	* rewrite firstn_all. rewrite sub_diag.
	  simpl.
	  replace n0 with (nth m l).
	  -- rewrite app_nil_r. reflexivity.
	  -- simpl in Heqsq. injection Heqsq. auto.
	* rewrite length_seq. reflexivity.
  Qed.

  Definition last i := let l := (nth_sum_list2 i) in
    nth_error l (find_seq l (list_min gen)).

  Theorem last_ge_all A `{numerical_semigroup A} i n :
    generator A (fun x => In x gen) ->
    last i = Some n -> forall a, n <= a -> A a.
  Proof.
    destruct (eq_dec (length gen) 0). {
      apply length_zero_iff_nil in e. rewrite e.
      intros. simpl in *. destruct H0.
      unfold Included, In in *. simpl in *.
      specialize H3 with 0.
      assert (A 0); try apply ns_zero.
      apply H3 in H4. inversion H4.
      exfalso. eapply H6. 
      -
    }
    assert (gen <> []). {
      intros C.
    }
    unfold last in *.
    assert (Some n <> None); try discriminate.
    rewrite <- H1 in H3. apply nth_error_Some in H3.
    apply find_seq_th in H3.
    rewrite Div0.div_mod with (b := list_min gen).
    apply ns_closed.
    - rewrite mul_comm. apply sub_mul_closed; try apply _.
      destruct H0. unfold Included in H0. apply H0.
      unfold In. apply list_min_in.
    Search div.
    generalize (find_seq_th (nth_sum_list2 i)).

End generators.

Compute last [4;7;10] 100.
Compute last [72;73;74] 3.
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
  generates_el (fun x => In x l) a ->
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
  generator A (fun x => In x l) ->
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
  generator A (fun x => In x [4;7;10]) ->
  apery A 4 = (fun x => In x [0;7;10;17]).
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
	-- unfold In.
Abort.

  Fixpoint n_seq_aux l n x m p c :=
    match m with
    | 0 => p
    | S m =>
	match l with
	| [] => c
        | h :: t => if h =? x then n_seq_aux t n (S x) m p (S c) else n_seq_aux t n (S h) n c (S c)
        end
    end.

  Definition n_seq l n :=
    match n with
    | 0 => length l
    | S n => n_seq_aux l n 0 (S n) 0 0
    end.

  Theorem t l n : n_seq (skipn (n_seq l n) l) n = 0.
  Proof.
    induction l.
    - destruct n; reflexivity.
    - destruct n.
      + simpl. rewrite length_skipn. lia.
      + simpl. destruct (eqb_spec a 0).
	* subst. simpl in *.
	  rewrite skipn_cons.

