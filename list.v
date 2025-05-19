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

Theorem filter_all {A} P `{forall x, Decision (P x)} (l : list A) :
  Forall P l -> filter P l = l.
Proof.
  intros F. induction l; [reflexivity|].
  rewrite filter_cons. destruct (decide (P a)).
  - f_equal. apply IHl. now inversion F.
  - inversion F. contradiction.
Qed.

Theorem filter_none {A} P `{forall x, Decision (P x)} (l : list A) :
  Forall (fun x => ~ P x) l -> filter P l = [].
Proof.
  intros F. induction l; [reflexivity|].
  rewrite filter_cons. destruct (decide (P a)).
  - inversion F. contradiction.
  - apply IHl. now inversion F.
Qed.

Theorem elem_of_drop {A} (x : A) n l :
  x ∈ drop n l <-> exists i, l !! i = Some x ∧ n <= i.
Proof.
  split.
  - intros Hx.
    apply elem_of_list_lookup_1 in Hx as [i Hi].
    rewrite lookup_drop in Hi.
    exists (n + i). split; [assumption|]. lia.
  - intros [i [Si Hi]].
    eapply elem_of_list_lookup_2.
    rewrite lookup_drop.
    replace i with (n + (i - n)) in Si; [|lia].
    eassumption.
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

Theorem StronglySorted_lookup {T} P (l : list T) :
  StronglySorted P l ->
  forall i j x y, l !! i = Some x -> l !! j = Some y ->
  i < j -> P x y.
Proof.
  induction l; intros SR i j x y Hx Hy L.
  - rewrite lookup_nil in Hx. discriminate.
  - inversion SR. subst.
    destruct i, j; simpl in *; try lia.
    + injection Hx as Hx. subst.
      eapply Forall_lookup_1; eassumption.
    + eapply IHl; try eassumption. lia.
Qed.

Theorem StronglySorted_lookup_refl {T} P `{!Reflexive P} (l : list T) :
  StronglySorted P l ->
  forall i j x y, l !! i = Some x -> l !! j = Some y ->
  i <= j -> P x y.
Proof.
  intros SR i j x y Hx Hy L.
  destruct (decide (i = j)).
  - subst. rewrite Hx in Hy.
    injection Hy. intros ->. reflexivity.
  - eapply StronglySorted_lookup; try eassumption. lia.
Qed.

Theorem StronglySorted_unique_index {T} R `{!Irreflexive R} (l : list T) :
  StronglySorted R l ->
  forall i j x, l !! i = Some x -> l !! j = Some x ->
  i = j.
Proof.
  intros SS i j x Hi Hj.
  apply dec_stable. intros N.
  assert (O : i < j ∨ j < i); [lia|].
  destruct O as [O|O]; eapply StronglySorted_lookup in O; try eassumption; apply irreflexivity in O; assumption.
Qed.

Instance Sorted_equiv_proper {A} l :
  Proper (Normalizes A ==> iff) (fun R => Sorted R l).
Proof.
  intros P Q N.
  induction l; split; intros H; constructor; inversion H;
    try (now apply IHl); subst; destruct l; constructor.
  - apply N. now inversion H3.
  - apply N. now inversion H3.
Qed.

Theorem Sorted_app {T} R `{!Transitive R} (l : list T) x y :
  R x y -> Sorted R (l ++ [x]) -> Sorted R (l ++ [y]).
Proof.
  intros Rxy Sx.
  rewrite <- reverse_involutive.
  eapply Sorted_equiv_proper; [apply flip_atom|].
  apply Sorted_reverse. apply Sorted_reverse in Sx.
  rewrite reverse_app in *. simpl in *.
  inversion Sx. subst. constructor; [assumption|].
  destruct (reverse l); [constructor|].
  inversion H2. constructor. simpl in *.
  eapply transitivity; eassumption.
Qed.

Theorem Sorted_replicate {T} R `{!Reflexive R} n (x : T) :
  Sorted R (replicate n x).
Proof.
  induction n; simpl; constructor; [assumption|].
  destruct n; constructor. reflexivity.
Qed.
