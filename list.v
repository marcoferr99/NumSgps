From Coq Require Export List Mergesort Sorted.
From Coq Require Import Arith Lia.
Export ListNotations Nat NatSort Relations_1.


(*************************)
(** * Generic list facts *)
(*************************)

Definition Inl {T} (l : list T) x := In x l.
Arguments Inl {T} l x /.

Theorem skipn_nth {T} (d : T) l n : n < length l ->
  skipn n l = nth n l d :: skipn (S n) l.
Proof.
  generalize dependent n.
  induction l as [ | h t IH]; try (simpl; lia).
  intros n Hn. destruct n; try reflexivity.
  rewrite skipn_cons.
  simpl in Hn. rewrite IH; try lia.
  rewrite skipn_cons. reflexivity.
Qed.

Theorem firstn_S {T} d (l : list T) n : n < length l ->
  firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  intros. rewrite <- (rev_involutive l) at 1.
  rewrite firstn_rev. rewrite length_rev.
  rewrite (skipn_nth d); try (rewrite length_rev; lia).
  replace (S (length l - S n)) with (length l - n);
    try lia.
  simpl. rewrite rev_nth; try lia. f_equal.
  - rewrite skipn_rev. rewrite rev_involutive. f_equal.
    lia.
  - repeat f_equal. lia.
Qed.

Theorem Forall_repeat {T} (P : T -> Prop) x n : P x ->
  Forall P (repeat x n).
Proof. intros. induction n; constructor; assumption. Qed.


(**************)
(** * Sorting *)
(**************)

Theorem LocallySorted_middle {T} P (l : list T) a h :
  LocallySorted P (l ++ [a]) -> LocallySorted P (a :: h) ->
  LocallySorted P (l ++ a :: h).
Proof.
  induction l; intros; try assumption.
  simpl. destruct l; simpl; constructor;
    try assumption; try (inversion H; assumption).
  apply IHl; try assumption. inversion H. assumption.
Qed.

Theorem LocallySorted_rev {T} (P : T -> T -> Prop) l :
  LocallySorted P l ->
  LocallySorted (fun x y => P y x) (rev l).
Proof.
  intros L. induction l; try constructor.
  destruct l as [ | h t]; [constructor | ]. simpl.
  rewrite <- app_assoc. apply LocallySorted_middle.
  - apply IHl. inversion L. assumption.
  - inversion L. subst.
    constructor; [constructor | assumption].
Qed.

Theorem LocallySorted_iff {T} P Q (l : list T) :
  (forall x y, P x y <-> Q x y) ->
  LocallySorted P l -> LocallySorted Q l.
Proof.
  intros. induction l; try constructor.
  destruct l; constructor.
  - apply IHl. inversion H0. assumption.
  - apply H. inversion H0. assumption.
Qed.

Theorem LocallySorted_StronglySorted {T} P (l : list T) :
  Transitive P -> LocallySorted P l -> StronglySorted P l.
Proof.
  intros.
  apply Sorted_StronglySorted; try assumption.
  apply Sorted_LocallySorted_iff. assumption.
Qed.

Theorem StronglySorted_LocallySorted {T} P (l : list T) :
  StronglySorted P l -> LocallySorted P l.
Proof.
  intros.
  apply Sorted_LocallySorted_iff.
  apply StronglySorted_Sorted. assumption.
Qed.

Theorem StronglySorted_nth {T} d P (l : list T) :
  StronglySorted P l ->
  forall n m, n < length l -> m < length l ->
  n < m -> P (nth n l d) (nth m l d).
Proof.
  induction l; intros SR n m Ln Lm L;
    try (simpl in Ln; lia).
  inversion SR. subst. destruct m, n; simpl; try lia.
  - apply Forall_nth; try assumption.
    simpl in Lm. lia.
  - simpl in Ln, Lm. apply IHl; try assumption; lia.
Qed.

Theorem StronglySorted_nth_c {T} d P (l : list T) :
  StronglySorted P l ->
  forall n m, n < length l -> m < length l ->
  ~ P (nth n l d) (nth m l d) -> m <= n.
Proof.
  intros SR n m Ln Lm C.
  destruct (le_gt_cases m n); try assumption.
  exfalso. apply C. apply StronglySorted_nth; assumption.
Qed.

Theorem StronglySorted_filter {T} P f (l : list T) :
  StronglySorted P l -> StronglySorted P (filter f l).
Proof.
  intros SS. induction l; simpl; try constructor.
  destruct (f a).
  - constructor.
    + inversion SS. auto.
    + inversion SS. eapply incl_Forall.
      * apply incl_filter.
      * assumption.
  - inversion SS. auto.
Qed.


(*******************************)
(** * Lists of natural numbers *)
(*******************************)


(**********************************)
(** ** Inverse function for [nth] *)
(**********************************)

Fixpoint nth_inv d l x :=
  match l with
  | [] => d
  | h :: t => if h =? x then 0 else S (nth_inv d t x)
  end.

Theorem nth_inv_lt d l x : In x l ->
  nth_inv d l x < length l.
Proof.
  induction l; try contradiction.
  simpl. intros I. destruct (eqb_spec a x); try lia.
  apply Arith_base.lt_n_S_stt. intuition.
Qed.

Theorem nth_nth_inv d e l x : In x l ->
  nth (nth_inv d l x) l e = x.
Proof.
  induction l; try contradiction.
  intros I. simpl.
  destruct (eqb_spec a x); try assumption.
  simpl in I. intuition.
Qed.


(********************)
(** ** List minimum *)
(********************)

Fixpoint list_min l :=
  match l with
  | [] => 0
  | [x] => x
  | h :: t => min h (list_min t)
  end.

Theorem list_min_In l : l <> [] ->
  In (list_min l) l.
Proof.
  intros. induction l; try contradiction.
  simpl in *. destruct l; [intuition | ].
  destruct (le_ge_cases a (list_min (n :: l))).
  - rewrite min_l; try assumption. intuition.
  - rewrite min_r; try assumption.
    right. apply IHl. discriminate.
Qed.

Theorem list_min_le l x : In x l ->
  list_min l <= x.
Proof.
  intros. induction l; simpl; try lia.
  destruct l.
  - simpl in *. intuition lia.
  - inversion H.
    + rewrite le_min_l. lia.
    + rewrite le_min_r. auto.
Qed.


(***************)
(** ** Sorting *)
(***************)

Theorem LocallySorted_sort l :
  LocallySorted le (sort l).
Proof.
  generalize (LocallySorted_sort l). intros L.
  eapply LocallySorted_iff; try eassumption.
  intros. unfold is_true. fold leb.
  destruct (leb_spec x y); lia.
Qed.

Theorem LocallySorted_le_NoDup_lt l :
  LocallySorted le l -> NoDup l ->
  LocallySorted lt l.
Proof.
  intros L N. induction l; try constructor.
  destruct l; constructor.
  - apply IHl.
    + inversion L. assumption.
    + inversion N. assumption.
  - inversion L. inversion N. subst. unfold In in H6.
    lia.
Qed.

Theorem LocallySorted_NoDup_nth_lt d l n m :
  LocallySorted le l -> NoDup l ->
  n < length l -> m < length l ->
  n < m -> nth n l d < nth m l d.
Proof.
  intros LS N Ln Lm L.
  eapply StronglySorted_nth; try assumption.
  apply LocallySorted_StronglySorted.
  - intros x. lia.
  - apply LocallySorted_le_NoDup_lt; assumption.
Qed.


(***************************)
(** ** Removing duplicates *)
(***************************)

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

Theorem sorted_nodup_In l a : In a l <->
  In a (sorted_nodup l).
Proof.
  induction l; simpl; [intuition | ].
  destruct l; [simpl; intuition | ].
  destruct (eqb_spec a0 n).
  - split; intuition. subst. apply H0.
    constructor. reflexivity.
  - split; intros.
    + destruct H.
      * subst. constructor. reflexivity.
      * simpl. right. apply IHl. assumption.
    + inversion H; intuition.
Qed.

Theorem sorted_nodup_head_eq h t a s :
  sorted_nodup (h :: t) = a :: s -> h = a.
Proof.
  generalize dependent h. induction t; intros.
  - simpl in H. injection H. auto.
  - simpl in H. destruct (eqb_spec h a0).
    + apply IHt. rewrite <- H. subst. reflexivity.
    + injection H. auto.
Qed.

Theorem sorted_nodup_NoDup l : LocallySorted le l ->
  NoDup (sorted_nodup l).
Proof.
  induction l; intros; simpl; try constructor.
  destruct l; try constructor; try constructor.
  - intros C. inversion C.
  - destruct (eqb_spec a n); try constructor.
    + apply IHl. inversion H. assumption.
    + intros C. apply sorted_nodup_In in C.
      apply n0. apply le_antisymm.
      * inversion H. assumption.
      * inversion C; try lia.
	apply LocallySorted_StronglySorted in H.
	2:{ intros x. apply le_trans. }
	inversion H. inversion H3. subst.
	eapply In_nth with (d := 0) in H0.
	destruct H0. destruct H0.
	rewrite <- H1.
	eapply Forall_nth in H8; eassumption.
    + inversion H. auto.
Qed.

Theorem LocallySorted_le_sorted_nodup l :
  LocallySorted le l ->
  LocallySorted le (sorted_nodup l).
Proof.
  intros L. induction l; simpl; try constructor.
  destruct l as [ | b l]; try constructor.
  destruct (eqb_spec a b).
  - inversion L. auto.
  - remember (sorted_nodup (b :: l)) as s.
    inversion L. destruct s; constructor.
    + subst. auto.
    + subst. symmetry in Heqs.
      apply sorted_nodup_head_eq in Heqs. lia.
Qed.


(*********************)
(** ** List equality *)
(*********************)

Fixpoint list_eq l m :=
  match l, m with
  | [], [] => true
  | hl :: tl, hm :: tm => if hl =? hm then list_eq tl tm else false
  | _, _ => false
  end.

Theorem list_eq_spec l m :
  Bool.reflect (l = m) (list_eq l m).
Proof.
  remember (list_eq l m) as b. destruct b; constructor.
  - generalize dependent m.
    induction l; simpl; intros; destruct m;
      try reflexivity; try discriminate.
      destruct (eqb_spec a n); try discriminate.
      subst. f_equal. apply IHl. assumption.
  - generalize dependent m.
    induction l; simpl; intros; destruct m;
      try discriminate.
    destruct (eqb_spec a n).
    + intros C. eapply IHl; try eassumption.
      injection C. auto.
    + intros C. injection C as N. contradiction.
Qed.


(***********************)
(** ** Find a sequence *)
(***********************)

Fixpoint find_seq_aux p l n :=
  match l with
  | [] => p
  | h :: t => if list_eq (firstn n l) (seq h n) then p
      else find_seq_aux (S p) t n
  end.

Theorem find_seq_aux_S p l n :
  find_seq_aux (S p) l n = S (find_seq_aux p l n).
Proof.
  generalize dependent p.
  induction l; intros; simpl; try reflexivity.
  destruct (list_eq_spec (firstn n (a :: l)) (seq a n));
    try reflexivity.
  apply IHl.
Qed.

Definition find_seq := find_seq_aux 0.

Theorem find_seq_seq d l n : find_seq l n < length l ->
  firstn n (skipn (find_seq l n) l) =
    seq (nth (find_seq l n) l d) n.
Proof.
  intros L. induction l; try (simpl in *; lia).
  unfold find_seq in *. simpl in *.
  destruct (list_eq_spec (firstn n (a :: l)) (seq a n)).
  - rewrite skipn_O. assumption.
  - rewrite find_seq_aux_S in *. apply IHl. lia.
Qed.

Theorem find_seq_neq a l n h :
  find_seq (h ++ a :: l) n > length h ->
  firstn n (a :: l) <> seq a n.
Proof.
  induction h as [ | x h IH];
    unfold find_seq; simpl; intros.
  - destruct (list_eq_spec (firstn n (a :: l)) (seq a n));
      [lia | assumption].
  - destruct (list_eq_spec (firstn n (x :: h ++ a :: l)) (seq x n));
      try lia.
    apply IH. rewrite find_seq_aux_S in H.
    fold find_seq in H. lia.
Qed.

Theorem find_seq_first d l n m : find_seq l n < length l ->
  find_seq l n = S m -> S (nth m l d) <> nth (S m) l d.
Proof.
  intros L E C.
  apply (find_seq_seq d) in L as F. rewrite E in *.
  assert (G : find_seq l n > length (firstn m l)). {
    rewrite firstn_length_le; lia.
  }
  rewrite <- (firstn_skipn m l) in G at 1.
  rewrite (skipn_nth d) in G; try lia.
  apply find_seq_neq in G. apply G. clear G.
  replace (nth m l d :: skipn (S m) l) with ([nth m l d] ++ skipn (S m) l); try reflexivity.
  rewrite firstn_app. destruct n; try reflexivity.
  remember (skipn (S m) l) as s.
  simpl. f_equal. rewrite firstn_nil, sub_0_r. simpl.
  generalize F. intros G.
  rewrite seq_S in G. rewrite C.
  eapply app_inv_tail. rewrite <- G. clear G.
  assert (n < length s). {
    apply (f_equal (@length nat)) in F.
    rewrite length_seq in F.
    rewrite length_firstn in F.
    unfold "<". rewrite <- F. apply le_min_r.
  }
  rewrite (firstn_S d); try assumption.
  repeat f_equal.
  rewrite <- E in L. apply (find_seq_seq d) in L as F1.
  replace (nth n s d) with (nth n (seq (nth (S m) l d) (S n)) d).
  - symmetry. apply seq_nth. lia.
  - rewrite E in F1. rewrite <- F1. rewrite nth_firstn.
    destruct (ltb_spec n (S n)); try lia.
    subst s. reflexivity.
Qed.
