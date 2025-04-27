From stdpp Require Export list_numbers sets sorting.
Require Export list.
Export Nat.


(*******************************)
(** * Lists of natural numbers *)
(*******************************)

Theorem list_max_notin l x : x > list_max l -> x ∉ l.
Proof.
  intros Hx. destruct l eqn : E; [easy|].
  rewrite <- E in *.
  apply list_max_lt in Hx; [|now rewrite E].
  intros N. eapply Forall_forall in Hx; try eassumption.
  lia.
Qed.

Theorem Sorted_le_lt l :
  Sorted lt l <-> Sorted le l /\ NoDup l.
Proof.
  induction l; split.
  - split; constructor.
  - constructor.
  - intros S. split.
    + apply Sorted_LocallySorted_iff.
      destruct l; constructor.
      * apply Sorted_LocallySorted_iff.
	apply IHl. inversion S. assumption.
      * inversion S as [|? ? ? L]. inversion L. lia.
    + constructor.
      * intros N.
	apply Sorted_StronglySorted in S; [|intros ?; lia].
	assert (a < a); [|lia].
	eapply Forall_forall; try eassumption.
	inversion S. assumption.
      * apply IHl. inversion S. assumption.
  - intros [S D].
    apply Sorted_LocallySorted_iff.
    destruct l; constructor.
    + apply Sorted_LocallySorted_iff.
      apply IHl. split.
      * inversion S. assumption.
      * inversion D. assumption.
    + inversion S as [|? ? ? L]. inversion L. subst.
      inversion D as [|? ? N]. subst.
      assert (a <> n); [|lia].
      intros C. apply N. subst. constructor.
Qed.


(**********************************)
(** ** Inverse function for [nth] *)
(**********************************)

Definition list_find_total {T} `{Inhabited T} (P : T -> Prop) `{forall x, Decision (P x)} l :=
  default inhabitant (list_find P l).

Definition lookup_inv l x :=
  fst (list_find_total (eq x) l).

Theorem lookup_inv_lt l x :
  x ∈ l -> lookup_inv l x < length l.
Proof.
  intros Hx.
  edestruct (list_find_elem_of (eq x) l) as [[p y] Hy];
    [eassumption|reflexivity|].
  apply list_find_Some in Hy as P.
  destruct P as (P1 & P2 & P3).
  unfold eq in P2. subst.
  apply lookup_lt_is_Some.
  econstructor. rewrite <- P1. f_equal.
  unfold lookup_inv, list_find_total.
  replace p with ((p, y).1); [|reflexivity].
  f_equal.
  apply Some_inj. rewrite <- Hy. unfold default.
  simpl. rewrite Hy. reflexivity.
Qed.

Theorem lookup_lookup_inv l x :
  x ∈ l -> l !!! lookup_inv l x = x.
Proof.
  intros Hx.
  edestruct (list_find_elem_of (eq x) l) as [[p y] Hy];
    [eassumption|reflexivity|].
  apply list_find_Some in Hy as P.
  apply list_lookup_total_correct.
  destruct P as (P1 & P2 & P3).
  unfold eq in P2. subst.
  rewrite <- P1. f_equal.
  replace p with ((p, y).1); [|reflexivity].
  unfold lookup_inv. f_equal.
  apply Some_inj. rewrite <- Hy.
  unfold list_find_total. unfold default.
  rewrite Hy. reflexivity.
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

Theorem list_min_in l : l <> [] -> list_min l ∈ l.
Proof.
  intros. induction l; try contradiction.
  simpl in *. destruct l; [constructor|].
  destruct (le_ge_cases a (list_min (n :: l))).
  - rewrite min_l; try assumption. constructor.
  - rewrite min_r; try assumption.
    right. apply IHl. discriminate.
Qed.

Theorem list_min_le l x : x ∈ l -> list_min l <= x.
Proof.
  intros. induction l; simpl; try lia.
  destruct l.
  - inversion H; [lia|]. easy.
  - inversion H.
    + rewrite le_min_l. lia.
    + rewrite le_min_r. auto.
Qed.


(***********)
(** ** Sum *)
(***********)

Instance Permutation_sum_list_with {T} (f : T -> nat) :
  Proper (Permutation ==> eq) (fun l => sum_list_with f l).
Proof.
  intros l1 l2 Hl. unfold eq.
  induction Hl using Permutation_ind_bis;
    simpl; try reflexivity; try rewrite IHHl; try reflexivity.
  - lia.
  - rewrite IHHl1. assumption.
Qed.

Theorem sum_list_with_flat_map {T} (f : T -> nat) g (l : list T) :
  sum_list_with f (flat_map g l) = sum_list_with (fun x => sum_list_with f (g x)) l.
Proof.
  induction l; try reflexivity.
  simpl. rewrite sum_list_with_app. auto.
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

Theorem sorted_nodup_in l a :
  a ∈ l <-> a ∈ (sorted_nodup l).
Proof.
  induction l; simpl; [easy|].
  destruct l; [simpl; intuition | ].
  destruct (eqb_spec a0 n).
  - split; [|set_unfold; intuition].
    subst. intros. apply IHl.
    set_unfold. intuition.
  - split; intros.
    + inversion H.
      * subst. constructor.
      * simpl. right. apply IHl. assumption.
    + inversion H; subst.
      * constructor.
      * right. apply IHl. auto.
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

Theorem sorted_nodup_NoDup l : Sorted le l ->
  NoDup (sorted_nodup l).
Proof.
  induction l; intros; simpl; try constructor.
  destruct l; try constructor; try constructor.
  - intros C. inversion C.
  - destruct (eqb_spec a n); try constructor.
    + apply IHl. inversion H. assumption.
    + intros C. apply sorted_nodup_in in C.
      apply n0. apply le_antisymm.
      * inversion H as [|? ? ? Hd].
	inversion Hd. assumption.
      * inversion C; [lia|].
	apply Sorted_StronglySorted in H; [|intros ?; lia].
	inversion H. inversion H6. subst.
	eapply Forall_forall; eassumption.
    + inversion H. auto.
Qed.

Theorem Sorted_le_sorted_nodup l :
  Sorted le l -> Sorted le (sorted_nodup l).
Proof.
  intros L. induction l; simpl; [constructor|].
  destruct l as [ | b l]; [assumption|].
  destruct (eqb_spec a b).
  - inversion L. auto.
  - remember (sorted_nodup (b :: l)) as s.
    inversion L. destruct s; constructor; subst; auto.
    subst. symmetry in Heqs.
    apply sorted_nodup_head_eq in Heqs.
    constructor. inversion H2. lia.
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

