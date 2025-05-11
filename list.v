From stdpp Require Export list sorting.


(*************************)
(** * Generic list facts *)
(*************************)

Theorem repeat_replicate {T} (x : T) n :
  repeat x n = replicate n x.
Proof.
  induction n; [reflexivity|]. simpl. now f_equal.
Qed.

Theorem lookup_total_nth {T} `{Inhabited T} (l : list T) n :
  l !!! n = nth n l inhabitant.
Proof.
  rewrite nth_lookup. apply list_lookup_total_alt.
Qed.

Theorem drop_lookup {T} `{Inhabited T} (l : list T) n :
  n < length l -> drop n l = l !!! n :: drop (S n) l.
Proof.
  generalize dependent n.
  induction l as [ | h t IH]; try (simpl; lia).
  intros n Hn. destruct n; [reflexivity|].
  rewrite skipn_cons.
  simpl in Hn. rewrite IH; [|lia].
  now rewrite skipn_cons.
Qed.

Theorem take_S {T} `{Inhabited T} (l : list T) n : n < length l ->
  firstn (S n) l = firstn n l ++ [l !!! n].
Proof.
  intros L.
  apply take_S_r. now apply list_lookup_lookup_total_lt.
Qed.


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

Theorem Sorted_middle {T} P (l : list T) a h :
  Sorted P (l ++ [a]) -> Sorted P (a :: h) ->
  Sorted P (l ++ a :: h).
Proof.
  repeat rewrite Sorted_LocallySorted_iff.
  apply LocallySorted_middle.
Qed.

Theorem StronglySorted_filter {T} P f `{forall x, Decision (f x)} (l : list T) :
  StronglySorted P l -> StronglySorted P (filter f l).
Proof.
  intros SS. induction l; simpl; [constructor|].
  unfold filter, list_filter.
  inversion SS. destruct (decide (f a)); [|auto].
  constructor; [auto|].
  apply Forall_forall. intros x Hx.
  eapply Forall_forall; [eassumption|].
  eapply list_filter_subseteq. eassumption.
Qed.

Theorem Sorted_app_l {T} P (l1 l2 : list T) :
  Sorted P (l1 ++ l2) -> Sorted P l1.
Proof.
  intros S. induction l1; [constructor|].
  inversion S as [|? ? ? Hd]. subst. constructor; [auto|].
  destruct l1; [constructor|].
  inversion Hd. now constructor.
Qed.

Theorem Sorted_app_r {T} P (l1 l2 : list T) :
  Sorted P (l1 ++ l2) -> Sorted P l2.
Proof.
  intros S. induction l1; [assumption|].
  inversion S. auto.
Qed.

Theorem Sorted_iff {T} P Q (l : list T) :
  (forall x y, P x y <-> Q x y) ->
  Sorted P l -> Sorted Q l.
Proof.
  intros E S. induction l; [constructor|].
  inversion S as [|? ? ? Hd]. constructor; [auto|].
  destruct l; constructor.
  apply E. now inversion Hd.
Qed.

Theorem StronglySorted_lookup {T} `{Inhabited T} P (l : list T) :
  StronglySorted P l ->
  forall n m, n < length l -> m < length l ->
  n < m -> P (l !!! n) (l !!! m).
Proof.
  induction l; intros SR n m Ln Lm L; [simpl in Ln; lia|].
  inversion SR. subst. destruct m, n; simpl; try lia.
  - apply Forall_lookup_total; [assumption|].
    simpl in Lm. lia.
  - simpl in Ln, Lm. apply IHl; try assumption; lia.
Qed.

Theorem StronglySorted_lookup_2 {T} `{Inhabited T} P (l : list T) :
  StronglySorted P l ->
  forall n m, n < length l -> m < length l ->
  ~ P (l !!! n) (l !!! m) -> m <= n.
Proof.
  intros SR n m Ln Lm C.
  destruct (Nat.le_gt_cases m n); try assumption.
  exfalso. apply C. now apply StronglySorted_lookup.
Qed.
