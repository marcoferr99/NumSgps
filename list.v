From stdpp Require Export list sorting.


(*************************)
(** * Generic list facts *)
(*************************)

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

Theorem Sorted_iff {T} P Q (l : list T) :
  (forall x y, P x y <-> Q x y) ->
  Sorted P l -> Sorted Q l.
Proof.
  intros E S. induction l; [constructor|].
  inversion S as [|? ? ? Hd]. constructor; [auto|].
  destruct l; constructor.
  apply E. now inversion Hd.
Qed.
