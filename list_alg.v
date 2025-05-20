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


  (*********************)
  (** ** lgen_complete *)
  (*********************)

  Definition find_le m l :=
    match list_find (fun x => x < m) l with
    | None => length l
    | Some (p, _) => p
    end.

  Theorem find_le_length m l : find_le m l <= length l.
  Proof.
    unfold find_le in *.
    destruct (list_find (fun x => x < m) l) eqn : E.
    - destruct p as [p]. apply list_find_Some in E.
      assert (p < length l); [|lia].
      apply lookup_lt_is_Some_1.
      destruct E. eauto.
    - lia.
  Qed.

  Theorem find_le_take m l :
    Forall (fun x => m <= x) (take (find_le m l) l).
  Proof.
    apply Forall_forall. intros x Hx.
    unfold find_le in *.
    apply elem_of_take in Hx as [j Hj].
    destruct (list_find (fun x => x < m) l) eqn : E.
    - destruct p as [p]. apply list_find_Some in E.
      apply le_ngt. destruct E as (_ & _ & E).
      eapply E; apply Hj.
    - apply list_find_None in E.
      destruct Hj as [Hj].
      apply elem_of_list_lookup_2 in Hj.
      eapply Forall_forall in E; [|eassumption].
      lia.
  Qed.

  Theorem find_le_drop m l : sorted l ->
    Forall (fun x => x < m) (drop (find_le m l) l).
  Proof.
    intros SR.
    apply Forall_forall. intros x Hx.
    apply elem_of_drop in Hx as [i Hi].
    unfold find_le in *.
    destruct (list_find (fun x => x < m) l) eqn : E.
    - destruct p as [p]. apply list_find_Some in E.
      assert (L : p <= i); [lia|].
      assert (n >= x); [|lia].
      eapply (StronglySorted_lookup_refl _); try eassumption.
      + apply (Sorted_StronglySorted _). eassumption.
      + apply E.
      + apply Hi.
    - assert (N : ~ i < length l); [lia|].
      exfalso. apply N.
      apply lookup_lt_is_Some_1. exists x. apply Hi.
  Qed.

  Definition le_length m l := length (filter (fun x => m <= x) l).

  Theorem le_length_cons m h t :
    le_length m (h :: t) =
    if decide (m <= h) then S (le_length m t) else le_length m t.
  Proof.
    unfold le_length. rewrite filter_cons.
    now destruct (decide (m <= h)).
  Qed.

  Theorem find_le_le_length m l : sorted l ->
    find_le m l = le_length m l.
  Proof.
    intros SR.
    rewrite <- (take_drop (find_le m l)) at 2.
    unfold le_length. rewrite filter_app.
    rewrite filter_all; [|apply find_le_take].
    rewrite filter_none.
    - rewrite app_nil_r. symmetry. apply length_take_le.
      apply find_le_length.
    - apply Forall_forall.
      generalize (find_le_drop m l SR). intros F.
      intros x Hx.
      eapply Forall_forall in F; [|eassumption]. lia.
  Qed.

  Theorem take_le_length m l : sorted l ->
    Forall (fun x => m <= x) (take (le_length m l) l).
  Proof.
    intros SR.
    rewrite <- find_le_le_length; [|assumption].
    now apply find_le_take.
  Qed.

  Theorem drop_le_length m l : sorted l ->
    Forall (fun x => x < m) (drop (le_length m l) l).
  Proof.
    intros SR.
    rewrite <- find_le_le_length; [|assumption].
    now apply find_le_drop.
  Qed.

  Theorem le_length_app n l m :
    le_length n (l ++ m) = le_length n l + le_length n m.
  Proof.
    unfold le_length. rewrite filter_app. apply length_app.
  Qed.

  Theorem le_length_0 l : le_length 0 l = length l.
  Proof.
    induction l; [reflexivity|].
    unfold le_length in *. simpl.
    now rewrite IHl.
  Qed.

  Theorem le_length_le n m l :
    n <= m -> le_length m l <= le_length n l.
  Proof.
    intros L. induction l; [easy|].
    unfold le_length in *. repeat rewrite filter_cons.
    destruct (decide (n <= a)), (decide (m <= a)); simpl; lia.
  Qed.

  Theorem le_length_lookup_le m l : sorted l ->
    forall i x, l !! i = Some x ->
    i < le_length m l -> m <= x.
  Proof.
    intros SR i x Hx L.
    rewrite <- find_le_le_length in L; [|assumption].
    eapply Forall_forall.
    - apply find_le_take.
    - apply elem_of_take. eauto.
  Qed.

  Theorem le_length_lookup_lt m l : sorted l ->
    forall i x, l !! i = Some x ->
    le_length m l <= i -> x < m.
  Proof.
    intros SR i x Hx L.
    rewrite <- find_le_le_length in L; [|assumption].
    generalize (find_le_drop m l SR). intros F.
    eapply Forall_forall in F; [eassumption|].
    apply elem_of_drop. eauto.
  Qed.

  Theorem le_length_replicate m n x :
    le_length m (replicate n x) =
    if decide (m <= x) then n else 0.
  Proof.
    induction n; simpl.
    - destruct (decide (m <= x)); reflexivity.
    - unfold le_length in *. rewrite filter_cons.
      destruct (decide (m <= x)); simpl; now rewrite IHn.
  Qed.

  Definition le_length_eq m k l :=
    forall i, i < m -> le_length i l = k i.

  Definition le_length_eq_lgen m k :=
    forall l, gelist l -> le_length_eq m k l ->
    exists n, lgen n = l.

  Theorem list_replicate l n :
    Forall (eq n) l -> l = replicate (length l) n.
  Proof.
    intros F. remember (length l) as m eqn : E.
    generalize dependent l.
    induction m; simpl; intros;
      [now apply length_zero_iff_nil|].
    destruct l; simpl in *; [lia|].
    inversion F. f_equal; [easy|].
    apply IHm; [assumption|lia].
  Qed.

  Theorem take_le_length_replicate l m :
    sorted l -> Forall (fun x => x <= m) l ->
    take (le_length m l) l = replicate (le_length m l) m.
  Proof.
    intros SR F.
    replace (le_length m l) with (length (take (le_length m l) l)) at 2;
      [|apply length_take_le; apply length_filter].
    apply list_replicate. apply Forall_forall.
    intros a Ha. apply elem_of_take in Ha as [i Hi].
    apply le_antisymm.
    - eapply le_length_lookup_le;
	try eassumption; apply Hi.
    - eapply Forall_forall in F; [eassumption|].
      eapply elem_of_list_lookup_2. apply Hi.
  Qed.

  Theorem le_length_0_lgen m k l :
    m <= max -> gelist l -> le_length_eq_lgen (S m) k ->
    le_length_eq m k l -> le_length m l = S (k m) ->
    le_length (S m) l = 0 -> exists n, lgen n = l.
  Proof.
    unfold le_length_eq.
    intros Lm [SR M] A F Fm FS.
    generalize (lookup_lt_is_Some_2 l (k m)). intros IS.
    assert (Lk : k m < length l). {
      unfold "<". rewrite <- Fm. apply length_filter.
    }
    destruct IS as [x Hx]; [assumption|].
    replace x with m in *.
    2:{
      apply le_antisymm.
      - eapply Forall_forall; [apply find_le_take|].
	apply elem_of_take. exists (k m).
	split; [eassumption|].
	rewrite find_le_le_length; [|assumption].
	rewrite Fm. lia.
      - assert (x < S m); [|lia].
	generalize (find_le_drop (S m) l). intros FD.
	eapply Forall_forall in FD; [eassumption|assumption|].
	apply elem_of_drop. exists (k m).
	rewrite find_le_le_length; [|assumption].
	split; [assumption|]. lia.
    }
    generalize (take_drop_middle l (k m) m Hx). intros El.
    remember (drop (S (k m)) l) as d eqn : Ed.
    set (md := match m with 0 => [] | S m => [m] end).
    set (h := replicate (k m) max ++ md ++ d).
    assert (d0 : m = 0 -> d = []). {
      intros. subst. rewrite <- Fm.
      rewrite le_length_0. apply drop_all.
    }
    assert (Smd : sorted (md ++ d)). {
      subst md. destruct m.
      - rewrite d0; constructor.
      - simpl. constructor.
	+ subst d. eapply Sorted_app_r.
	  now rewrite take_drop.
	+ destruct d; constructor.
	  generalize (drop_le_length (S m) l SR).
	  intros FD. rewrite Forall_forall in FD.
	  assert (n < S m); [|lia]. apply FD.
	  rewrite Fm, <- Ed. left.
    }
    assert (Sh : sorted h). {
      subst h md. destruct m.
      - rewrite d0; [|reflexivity].
	repeat rewrite app_nil_r.
	apply (Sorted_replicate _).
      - remember (S (k (S m))) as y eqn : E.
	simpl. apply Sorted_middle; [|assumption].
	+ apply (Sorted_app _ _ max).
	  * lia.
	  * replace [max] with (replicate 1 max);
	      [|reflexivity].
	    rewrite <- replicate_add.
	    apply (Sorted_replicate _).
    }
    destruct (A h) as [n Hn]; [split| |].
    - apply Sh.
    - subst h. apply Forall_app.
      split; [|apply Forall_app; split].
      + now apply Forall_replicate.
      + destruct m; subst md;
	  constructor; [lia|constructor].
      + eapply Forall_app.
	subst d. now rewrite take_drop.
    - intros i Hi.
      destruct m. {
	subst h.
        rewrite d0 in *; try reflexivity.
	subst md.
	repeat rewrite app_nil_r in *.
	rewrite le_length_replicate.
	destruct (decide (i <= max)); [|lia].
	replace i with 0; lia.
      }
      subst md.
      assert (Lh : length h = length l). {
	subst h. rewrite <- El.
	repeat rewrite length_app. simpl.
	rewrite length_replicate.
	rewrite length_take_le; lia.
      }
      destruct (eq_dec i (S m)).
      + subst. apply le_antisymm.
	* apply le_ngt. intros N.
	  rewrite <- Lh in Lk.
	  apply lookup_lt_is_Some_2 in Lk as [y Hy].
	  apply le_length_lookup_le with (x := y) in N;
	    try assumption.
	  unfold h in Hy. simpl in Hy.
	  rewrite list_lookup_middle in Hy;
	    [|now rewrite length_replicate].
	  injection Hy as Hy. subst. lia.
	* apply le_ngt. intros N.
	  unfold "<" in N. destruct (k (S m)); [lia|].
	  assert (Ln : n < length l); [lia|].
	  rewrite <- Lh in Ln.
	  apply lookup_lt_is_Some_2 in Ln as [y Hy].
	  apply le_S_n, le_length_lookup_lt with (x := y) in N; try assumption.
	  subst h.
	  rewrite lookup_app_l in Hy;
	    [|rewrite length_replicate; lia].
	  apply lookup_replicate_1 in Hy. lia.
      + rewrite <- F, <- El; [|lia]. unfold h.
	repeat rewrite le_length_app.
	rewrite le_length_cons.
	destruct (decide (i <= m)); [|lia]. simpl.
	f_equal.
	* rewrite le_length_replicate.
	  destruct (decide (i <= max)); [|lia].
	  unfold le_length. rewrite filter_all.
	  -- rewrite length_take_le; lia.
	  -- apply Forall_forall. intros a Ha.
	     apply elem_of_take in Ha as [j Hj].
	     eapply le_length_lookup_le.
	     ++ apply SR.
	     ++ apply Hj.
	     ++ assert (Li : i <= S m); [lia|].
		apply (le_length_le i (S m) l) in Li.
		lia.
	* rewrite le_length_cons.
	  destruct (decide (i <= S m)); lia.
    - exists (S n). simpl. rewrite Hn.
      rewrite <- El.
      replace (take (k m) l) with (replicate (k m) m).
      2:{
	symmetry.
	replace (k m) with (length (take (k m) l)) at 2;
	  [|apply length_take_le; lia].
	apply list_replicate.
	apply Forall_forall.
	intros a Ha. unfold eq.
	apply elem_of_take in Ha as [i Hi].
	apply le_antisymm.
	- eapply le_length_lookup_le.
	  + apply SR.
	  + apply Hi.
	  + lia.
	- assert (a < S m); [|lia].
	  eapply le_length_lookup_lt.
	  + apply SR.
	  + apply Hi.
	  + lia.
      }
      subst h md. destruct m.
      + rewrite d0 in *; try reflexivity.
	repeat rewrite app_nil_r.
	clear. induction (k 0); [reflexivity|].
	simpl. destruct (ltb_spec max max); [lia|].
	rewrite IHn.
	destruct (replicate n 0 ++ [0]) eqn : E.
	* exfalso. eapply next_not_nil. eassumption.
	* f_equal. destruct n; injection E; auto.
      + simpl. repeat rewrite <- repeat_replicate.
	rewrite next_repeat; [|lia].
	replace (S (k (S m))) with (k (S m) + 1); [|lia].
	now rewrite repeat_app, <- app_assoc.
  Qed.

  Theorem le_length_eq_impl m k :
    le_length_eq_lgen (S (max - m)) k ->
    forall l, gelist l -> le_length_eq (max - m) k l ->
    le_length (max - m) l = S (k (max - m)) ->
    exists n, lgen n = l.
  Proof.
    generalize dependent k.
    induction m; intros k A l G Fl FS.
    - repeat rewrite sub_0_r in *.
      eapply le_length_0_lgen; try eassumption; try lia.
      apply le_antisymm; try lia.
      apply le_ngt. intros N.
      destruct G as [L F].
      destruct l. {
	unfold le_length in *. simpl in *. lia.
      }
      eapply le_length_lookup_le in N; try assumption;
	[|now simpl].
      inversion F. lia.
    - destruct (eq_dec (max - m) 0) as [E|E].
      + rewrite E in *.
	replace (max - S m) with 0 in *; [|lia].
	eapply IHm; eassumption.
      + remember (max - S m) as a eqn : Ea.
	replace (max - m) with (S a) in *; [|lia].
	assert (
	  forall l, gelist l -> le_length_eq a k l ->
	  le_length a l = S (k a) ->
	  exists n, lgen n = l
	). {
	  clear dependent l. intros l.
	  remember (le_length (S a) l) as x eqn : Ex.
	  generalize dependent l.
	  induction x; intros l La G Lk Ek.
	  - apply le_length_0_lgen with a k; auto; lia.
	  - apply (IHm (fun i => if i =? (S a) then x else le_length i l)); try assumption.
	    + intros v Gv Hv.
	      destruct IHx with v as [n Hn];
		try assumption.
	      * rewrite Hv; [|lia].
		destruct (eqb_spec (S a) (S a)); lia.
	      * intros i Hi.
		rewrite Hv; [|lia].
		destruct (eqb_spec i (S a)); [lia|].
		rewrite Lk; lia.
	      * rewrite Hv; [|lia].
		destruct (eqb_spec a (S a)); [lia|].
		assumption.
	      * eauto.
	    + intros i Hi. destruct (eqb_spec i (S a)).
	      * subst. lia.
	      * reflexivity.
	    + destruct (eqb_spec (S a) (S a)); [|lia].
	      auto.
	}
	auto.
  Qed.

  Theorem lgen_complete l :
    gelist l -> exists n, lgen n = l.
  Proof.
    intros G.
    remember (length l) as ln eqn : E.
    generalize dependent l. induction ln; intros.
    - exists 0.
      symmetry in E. apply length_zero_iff_nil in E.
      now subst.
    - set (k (i : nat) := ln).
      apply (le_length_eq_impl max k);
	try assumption; rewrite sub_diag.
      + intros m Gm L. apply IHln; [assumption|].
	rewrite <- le_length_0, L; [reflexivity|lia].
      + intros i Hi. lia.
      + now rewrite le_length_0.
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

  Theorem lgen_inv_next l : gelist l ->
    lgen_inv (next l) = S (lgen_inv l).
  Proof.
    intros G.
    generalize (take_drop (le_length max l) l). intros R.
    rewrite take_le_length_replicate in R; try apply G.
    remember (drop (le_length max l)) as d eqn : D.
    rewrite <- repeat_replicate in R.
    destruct d eqn : Ed.
    - rewrite <- R. rewrite app_nil_r.
      apply lgen_lgen_inv_2.
    - rewrite <- R. apply lgen_lgen_inv.
      generalize (drop_le_length max l). intros F.
      eapply Forall_forall in F; try eassumption.
      + apply G.
      + rewrite <- D, Ed. left.
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
