From stdpp Require Export list_numbers sets sorting.
Require Export list nat.
Export Nat.


Definition list_max_lower_bound l : l <> [] ->
  lower_bound ge (list_max l) l.
Proof.
  intros l0 x Hx.
  destruct (le_gt_cases x (list_max l)) as [|L];
    [assumption|].
  apply list_max_lt in L; [|assumption].
  eapply Forall_forall in L; [|eassumption]. lia.
Qed.

Theorem list_max_notin l x : x > list_max l -> x ∉ l.
Proof.
  intros Hx.
  destruct (decide (l = [])); [subst; easy|].
  intros N. apply list_max_lower_bound in N; [|assumption].
  lia.
Qed.


(*****************)
(** * [find_gap] *)
(*****************)

(** Let [n] be the minimum natural number such that the list [l] begins with
    [[x, x+1, ..., x+(n-1), y]] and [y <> x+n].  Than the function [find_gap]
    returns [x+n]. *)

Fixpoint find_gap x l :=
  match l with
  | [] => x
  | h :: t =>
      if h =? x then find_gap (S x) t else x
  end.

Theorem find_gap_le x l : x <= find_gap x l.
Proof.
  generalize dependent x. induction l; simpl; [lia|].
  intros x. destruct (eqb_spec a x); [|lia].
  subst. eapply le_trans; [|apply IHl]. lia.
Qed.

Theorem find_gap_le_lt_in x l : Sorted lt l ->
  forall n, x <= n < find_gap x l -> n ∈ l.
Proof.
  intros L n [Le Lt]. generalize dependent x.
  induction l; simpl in *; [lia|].
  intros x Le Lt.
  destruct (eq_dec n a); subst; [constructor|]. right.
  assert (LS : Sorted lt l); [inversion L; assumption|].
  destruct (eqb_spec a x); [|lia].
  eapply IHl; [assumption| |eassumption]. lia.
Qed.

Theorem find_gap_notin x l : Sorted lt l ->
  Forall (le x) l -> find_gap x l ∉ l.
Proof.
  intros L. generalize dependent x. induction l; [easy|].
  simpl. intros x F.
  assert (Sorted lt l); [inversion L; assumption|].
  apply Sorted_StronglySorted in L; [|intros ?; lia].
  destruct (eqb_spec a x); intros C; inversion C; subst.
  - generalize (find_gap_le (S x) l). lia.
  - specialize IHl with (S x). apply IHl; try assumption.
    apply Forall_forall. intros a Ha.
    assert (x < a); [|lia].
    inversion L. eapply Forall_forall; eassumption.
  - contradiction.
  - assert (x <= a). {
      eapply Forall_forall; [eassumption|constructor].
    }
    assert (a < x); [|lia].
    inversion L. subst. eapply Forall_forall; eassumption.
Qed.

Theorem find_gap_notin_le x l n : Sorted lt l ->
  n ∉ l -> n >= x -> find_gap x l <= n.
Proof.
  intros L N G.
  destruct (le_gt_cases (find_gap x l) n);
    [assumption|].
  exfalso. apply N.
  eapply find_gap_le_lt_in; [assumption|].
  split; eassumption.
Qed.


(**************)
(** * Sorting *)
(**************)

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

Theorem Sorted_lt_unique l :
  Sorted lt l -> forall i j, i < length l ->
  j < length l -> l !! i = l !! j -> i = j.
Proof.
  intros S i j Li Lj E.
  apply (Sorted_StronglySorted _) in S.
  apply lookup_lt_is_Some_2 in Li, Lj.
  destruct Li, Lj.
  eapply (StronglySorted_unique_index lt _); try eassumption.
  congruence.
Qed.

Theorem Sorted_lt_eq l m : Sorted lt l -> Sorted lt m ->
  (forall x, x ∈ l <-> x ∈ m) -> l = m.
Proof.
  generalize dependent m. induction l; intros m Sl Sm H.
  - destruct m; [reflexivity|].
    assert (n ∈ []); [|easy]. apply H. left.
  - destruct m.
    + assert (a ∈ []); [|easy]. apply H. left.
    + destruct (eq_dec a n).
      * subst. f_equal.
	apply IHl; [now inversion Sl | now inversion Sm|].
	intros x. split; intros Hx.
	-- destruct (eq_dec n x).
	   ++ subst.
	      apply Sorted_StronglySorted in Sl;
		[|intros ?; lia].
	      inversion Sl. subst.
	      assert (x < x); [|lia].
	      eapply Forall_forall; eassumption.
	   ++ assert (x ∈ n :: l); [now right|].
	      apply H in H0.
	      inversion H0; [lia|assumption].
	-- destruct (eq_dec n x).
	   ++ subst.
	      apply Sorted_StronglySorted in Sm;
		[|intros ?; lia].
	      inversion Sm. subst.
	      assert (x < x); [|lia].
	      eapply Forall_forall; eassumption.
	   ++ assert (x ∈ n :: m); [now right|].
	      apply H in H0.
	      inversion H0; [lia|assumption].
      * apply Sorted_StronglySorted in Sl, Sm;
	  try (intros ?; lia).
	inversion Sl; inversion Sm. subst.
	assert (a < n). {
	  eapply Forall_forall; try eassumption.
	  assert (n ∈ n :: m); [left|].
	  apply H in H0. inversion H0; [lia|assumption].
	}
	assert (n < a). {
	  eapply Forall_forall; try eassumption.
	  assert (a ∈ a :: l); [left|].
	  apply H in H1. inversion H1; [lia|assumption].
	}
	lia.
Qed.

Theorem Sorted_lt_seq n m : Sorted lt (seq n m).
Proof.
  generalize dependent n.
  induction m; simpl; [constructor|].
  intros n. constructor; [easy|].
  destruct m; simpl; constructor. lia.
Qed.


(*************************************)
(** ** Inverse function for [lookup] *)
(*************************************)

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
(** * List minimum *)
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

Theorem sum_list_with_eq {A} f g (l : list A) :
  (forall x, x ∈ l -> f x = g x) ->
  sum_list_with f l = sum_list_with g l.
Proof.
  intros. induction l; [reflexivity|].
  simpl. rewrite IHl.
  - f_equal. apply H. left.
  - intros. apply H. now right.
Qed.


(***************************)
(** * Removing duplicates *)
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

Theorem NoDup_sorted_nodup l : Sorted le l ->
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

Theorem Sorted_lt_sorted_nodup l :
  Sorted le l -> Sorted lt (sorted_nodup l).
Proof.
  intros S. apply Sorted_le_lt.
  split; [now apply Sorted_le_sorted_nodup|].
  now apply NoDup_sorted_nodup.
Qed.


(***********************)
(** ** Find a sequence *)
(***********************)

Fixpoint find_seq_aux p l n :=
  match l with
  | [] => p
  | h :: t => if decide (take n l = seq h n) then p
      else find_seq_aux (S p) t n
  end.

Theorem find_seq_aux_S p l n :
  find_seq_aux (S p) l n = S (find_seq_aux p l n).
Proof.
  generalize dependent p.
  induction l; intros; simpl; try reflexivity.
  destruct (decide (take n (a :: l) = seq a n));
    try reflexivity.
  apply IHl.
Qed.

Definition find_seq := find_seq_aux 0.

Theorem find_seq_seq l n : find_seq l n < length l ->
  take n (drop (find_seq l n) l) =
    seq (l !!! find_seq l n) n.
Proof.
  intros L. induction l; [simpl in *; lia|].
  unfold find_seq in *. simpl in *.
  destruct (decide (firstn n (a :: l) = seq a n)).
  - rewrite skipn_O. assumption.
  - rewrite find_seq_aux_S in *. apply IHl. lia.
Qed.

Theorem find_seq_neq a l n h :
  find_seq (h ++ a :: l) n > length h ->
  take n (a :: l) <> seq a n.
Proof.
  induction h as [|x h IH]; unfold find_seq; simpl; intros.
  - destruct (decide (firstn n (a :: l) = seq a n));
      [lia | assumption].
  - destruct (decide (firstn n (x :: h ++ a :: l) = seq x n));
      [lia|].
    apply IH. rewrite find_seq_aux_S in H.
    fold find_seq in H. lia.
Qed.

Theorem find_seq_first l n m : find_seq l n < length l ->
  find_seq l n = S m -> S (l !!! m) <> l !!! S m.
Proof.
  intros L E C.
  apply find_seq_seq in L as F. rewrite E in *.
  assert (G : find_seq l n > length (take m l)). {
    rewrite firstn_length_le; lia.
  }
  rewrite <- (firstn_skipn m l) in G at 1.
  rewrite drop_lookup in G; [|lia].
  apply find_seq_neq in G. apply G. clear G.
  replace (l !!! m :: drop (S m) l) with ([l !!! m] ++ drop (S m) l); try reflexivity.
  rewrite firstn_app. destruct n; try reflexivity.
  remember (drop (S m) l) as s.
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
  rewrite take_S; try assumption.
  repeat f_equal.
  rewrite <- E in L. apply find_seq_seq in L as F1.
  replace (s !!! n) with ((seq (l !!! S m) (S n)) !!! n).
  - symmetry. apply lookup_total_seq_lt. lia.
  - rewrite E in F1. rewrite <- F1.
    rewrite lookup_total_take; [|lia].
    subst s. reflexivity.
Qed.


(******************)
(** * Find modulo *)
(******************)

Definition find_mod n c a l :=
  match list_find (fun x => x mod n = a mod n) l with
  | None => mod_ge n a c
  | Some (_, x) => x
  end.

Theorem find_mod_mod n c a l :
  (find_mod n c a l) mod n = a mod n.
Proof.
  unfold find_mod.
  destruct (list_find (λ x, x mod n = a mod n)) eqn : E.
  - destruct p as [p x].
    apply list_find_Some in E. intuition.
  - apply mod_ge_mod.
Qed.

Theorem find_mod_min n c a l x :
  Sorted lt l -> n <> 0 -> x ∈ l ->
  x mod n = a mod n -> find_mod n c a l <= x.
Proof.
  intros SS n0 Lx I.
  unfold find_mod.
  destruct (list_find (λ x, x mod n = a mod n)) eqn : E.
  - destruct p as [p y].
    apply list_find_Some in E.
    destruct (le_gt_cases y x); [assumption|].
    apply elem_of_list_lookup_1 in Lx as [i Hi].
    exfalso. destruct E as (Hy & _ & E). eapply E.
    + apply Hi.
    + assert (i <= p). {
	apply (Sorted_StronglySorted _) in SS.
	destruct (le_gt_cases i p) as [|L]; [assumption|].
	eapply (StronglySorted_lookup _ _ SS) in L;
	  try eassumption.
	lia.
      }
      destruct (eq_dec i p); [|lia].
      subst.
      assert (x = y); [|lia].
      rewrite Hi in Hy. now injection Hy.
    + assumption.
  - apply list_find_None in E.
    eapply Forall_forall in E; [|eassumption].
    contradiction.
Qed.

Theorem find_mod_min_2 n c a l x :
  Sorted lt l -> Forall (ge c) l ->
  n <> 0 -> x > c -> x mod n = a mod n ->
  find_mod n c a l <= x.
Proof.
  intros SS F n0 Lx I.
  unfold find_mod.
  destruct (list_find (λ x, x mod n = a mod n)) eqn : E.
  - destruct p as [p y].
    apply list_find_Some in E as [E _].
    apply elem_of_list_lookup_2 in E.
    eapply Forall_forall in F; [|eassumption].
    lia.
  - unfold mod_ge. rewrite <- I.
    destruct (leb_spec c (c - c mod n + x mod n)).
    + apply mod_mod_le; [assumption|lia].
    + replace (c - c mod n + x mod n + n) with (c - c mod n + n + x mod n); [|lia].
      assert (x mod n < c mod n); [lia|].
      assert (c - c mod n + n <= x - x mod n); [|lia].
      destruct (mod_divide_2 n (x - x mod n) (c - c mod n)).
      * lia.
      * rewrite (div_mod_eq c n) at 1.
	rewrite <- add_sub_assoc, sub_diag, add_0_r; [|lia].
	rewrite mul_comm, Div0.mod_mul.
	rewrite (div_mod_eq x n) at 1.
	rewrite <- add_sub_assoc, sub_diag, add_0_r; [|lia].
	rewrite mul_comm, Div0.mod_mul.
	reflexivity.
      * destruct x0; simpl in *; lia.
Qed.

Theorem find_mod_in n c a l : n <> 0 ->
  find_mod n c a l ∈ l \/ find_mod n c a l >= c.
Proof.
  intros n0.
  unfold find_mod.
  destruct (list_find (λ x, x mod n = a mod n)) eqn : E.
  - destruct p as [p y].
    apply list_find_Some in E as [E _].
    left. eapply elem_of_list_lookup_2. eassumption.
  - right. now apply mod_ge_ge.
Qed.
