From Coq Require Export List.
From Coq Require Import Arith Lia Sorted.
Export ListNotations.
Import Nat.

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

Definition Inl {T} (l : list T) x := In x l.

Theorem Forall_repeat {T} (P : T -> Prop) x n : P x ->
  Forall P (repeat x n).
Proof. intros. induction n; constructor; assumption. Qed.

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

Theorem LocallySorted_iff {T} P Q (l : list T) :
  (forall x y, P x y <-> Q x y) ->
  LocallySorted P l -> LocallySorted Q l.
Proof.
  intros. induction l; try constructor.
  destruct l; constructor.
  - apply IHl. inversion H0. assumption.
  - apply H. inversion H0. assumption.
Qed.

Fixpoint list_min l :=
  match l with
  | [] => 0
  | [x] => x
  | h :: t => Nat.min h (list_min t)
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
