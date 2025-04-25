Require Export def.
From Coq Require Import Lia.
From stdpp Require Import numbers propset.
Require Import nat.


Section apery.
  Context `{numerical_semigroup C M} (n : nat).

  (** Apery set definition *)

  Definition apery :=
    {[x | x ∈ M ∧ (n <= x -> x - n ∉ M)]}.

  (** The apery set of [n] does not contain two
      different numbers that are congruent modulo [n] *)

  Theorem apery_congr_unique a b : n ∈ M ->
    a ∈ apery -> b ∈ apery -> a mod n = b mod n -> a = b.
  Proof.
    intros Mn.
    assert (T :
      forall a b, a ∈ apery -> b ∈ apery -> a <= b ->
      a mod n = b mod n -> a = b
    ). {
      clear a b. intros a b Aa Ab L N.
      destruct (le_gt_cases n b) as [Ln | Lb].
      - destruct Ab as [_ Hb]. apply Hb in Ln.
	apply congr_mod_divide in N. destruct N as [k Hk].
	destruct k; try lia. exfalso. apply Ln.
	replace (b - n) with (k * n + a); try lia.
	apply ns_closed; [now apply ns_mul_closed|].
	now destruct Aa.
      - destruct (le_gt_cases n a); try lia.
	do 2 rewrite mod_small in N; assumption.
    }
    intros. destruct (le_ge_cases a b); try auto.
    symmetry. auto with congr_mod.
  Qed.

  (** [w] is the minimum element of [A] that
      is congruent to [i] modulo [n] *)

  Definition apery_min i w :=
    set_min {[x | x ∈ M ∧ congr_mod n x i]} w.

  Theorem apery_min_exists : n <> 0 ->
    forall i, exists w, apery_min i w.
  Proof.
    intros n0 i. apply well_ordering_principle.
    destruct (cofinite_definitive A) as [m Hm];
      try apply ns_cofinite.
    apply (Inhabited_intro (i + m * n)). split.
    + apply Hm. destruct n; lia.
    + unfold congr_mod. apply Div0.mod_add.
  Qed.


  (*************************)
  (** * [apery_w] function *)
  (*************************)

  Theorem apery_w_is_func : n <> 0 ->
    forall i : {x | x < n},
    exists ! w, apery_min (proj1_sig i) w.
  Proof.
    intros n0 i.
    destruct (apery_min_exists n0 (proj1_sig i)) as [w Hw].
    exists w. split; try assumption.
    eauto using minE_unique.
  Qed.

  Definition apery_w (n0 : n <> 0) :=
    proj1_sig (rel_func _ (apery_w_is_func n0)).

  Definition apery_w_spec (n0 : n <> 0) :
    (forall i, apery_min (proj1_sig i) (apery_w n0 i)) /\ forall i w, apery_min (proj1_sig i) w -> w = apery_w n0 i :=
    proj2_sig (rel_func _ (apery_w_is_func n0)).

  Theorem apery_w_injective (n0 : n <> 0) :
    injective (apery_w n0).
  Proof.
    intros x y I.
    apply proj1_sig_injective.
    destruct (apery_w_spec n0) as [Hw _].
    destruct (Hw x) as [[_ Hx] _].
    destruct (Hw y) as [[_ Hy] _].
    unfold congr_mod in *. rewrite I in Hx.
    rewrite Hx in Hy. clear Hx I n0 Hw.
    destruct x, y. simpl in *.
    now do 2 rewrite mod_small in Hy.
  Qed.

  Theorem apery_w_congr (n0 : n <> 0) :
    forall x, congr_mod n (apery_w n0 x) (proj1_sig x).
  Proof. apply apery_w_spec. Qed.

  (** [apery_alt] has a representative for every modulo class *)
  Theorem apery_w_all_classes (n0 : n <> 0) :
    forall x, exists i, congr_mod n x (apery_w n0 i).
  Proof.
    intros x.
    exists (exist (x mod n) (mod_upper_bound _ _ n0)).
    unfold congr_mod. rewrite apery_w_congr. simpl.
    symmetry. apply Div0.mod_mod.
  Qed.

  (** [apery] and [apery_alt] are the same set *)
  Theorem apery_w_eq (n0 : n <> 0) : A n ->
    Im (Full_set _) (apery_w n0) = apery.
  Proof.
    intros An.
    assert (I : Included (Im (Full_set _) (apery_w n0)) apery). {
      unfold Included, In. intros w Hw. 
      destruct Hw as [i _ w Hw]. subst w.
      destruct (apery_w_spec n0) as [W _].
      specialize W with i.
      split; try apply W.
      intros L AD.
      assert (N : ~(apery_w n0 i <= apery_w n0 i - n)); try lia.
      apply N. apply W. split; try assumption.
      unfold congr_mod.
      rewrite <- Div0.mod_add with (b := 1).
      replace (apery_w n0 i - n + 1 * n) with (apery_w n0 i); try lia.
      apply W.
    }
    apply Extensionality_Ensembles. split; try assumption.
    unfold Included, In. intros w Hw.
    destruct (apery_w_all_classes n0 w) as [x Hx].
    apply Im_intro with (x := x); try constructor.
    apply apery_congr_unique; try assumption.
    apply I. econstructor; constructor.
  Qed.

  Theorem apery_cardinality : A n -> n <> 0 ->
    cardinal apery n.
  Proof.
    intros An n0.
    rewrite <- (apery_w_eq n0); try assumption.
    apply injective_cardinal.
    - apply apery_w_injective.
    - apply sig_cardinal. apply cardinal_gt_n.
  Qed.

  (** Every element of [A] can be written as [k * n + w],
      where [w] is an element of [apery] *)
  Theorem apery_generates : A n -> n <> 0 ->
    forall a, A a ->
    exists ! k w, apery w /\ a = k * n + w.
  Proof.
    intros An n0 a Aa.
    destruct (classic (apery a)) as [Ap | Ap].
    - exists 0. split.
      + exists a. split; try auto. intuition.
      + intros x [w [[W1 W2] W3]].
	destruct x; try reflexivity.
	exfalso. apply Ap; try lia.
	replace (a - n) with (x * n + w); try lia.
	apply ns_closed; [|apply W1].
	clear W1 W2 W3. induction x; [apply ns_zero|].
	now apply ns_closed.
    - assert (
	exists k, a >= S k * n /\
	~ (apery (a - k * n)) /\ apery (a - S k * n)
      ) as [k [K1 [K2 K3]]]. {
	assert (
	  exists k, minE (fun k => n <= a - S k * n ->
	    ~ A (a - S k * n - n)) k
	) as [k [M1 M2]]. {
	    apply well_ordering_principle.
	    apply (Inhabited_intro a). unfold In.
	    induction n; lia.
	}
	exists k.
	assert (G : a >= S k * n). {
	  destruct k.
	  - apply not_and_or in Ap. intuition lia.
	  - specialize M2 with k. lia.
	}
	assert (Ak : A (a - S k * n)). {
	  destruct k.
	  - apply not_and_or in Ap.
	    replace (1 * n) with n in *; try lia.
	    destruct Ap; try contradiction.
	    apply NNPP. auto.
	  - specialize M2 with k. apply NNPP. intros C.
	    assert (N : ~ S k <= k); try lia.
	    apply N. apply M2. intros.
	    replace (a - S k * n - n) with (a - S (S k) * n); [assumption | lia].
	}
	split; try assumption.
	unfold apery. split; [|intuition].
	intros [C1 C2].
	apply C2; try lia.
	replace (a - k * n - n) with (a - S k * n);
	  [assumption | lia].
      }
      exists (S k). split.
      + exists (a - S k * n). split; try lia.
	split; [assumption | lia].
      + intros l [z [[Z1 Z2] Z3]].
	assert (E : z = a - S k * n). {
	  apply apery_congr_unique; try assumption.
	  symmetry.
	  rewrite <- Div0.mod_add with (b := S k).
	  replace (a - S k * n + S k * n) with a; try lia.
	  subst a. rewrite add_comm. apply Div0.mod_add.
	}
	assert (E1 : a = z + S k * n); try lia.
	subst a.
	apply (mul_cancel_r _ _ n); try assumption. lia.
  Qed.

  Theorem apery_generator : A n -> n <> 0 ->
    generator A (Add apery n).
  Proof.
    intros An n0. split.
    - intros x Hx. unfold In in *.
      destruct Hx as [x Hx | x Hx].
      + unfold apery, In in *. intuition.
      + destruct Hx. assumption.
    - intros a Aa.
      generalize (apery_generates An n0 a Aa).
      intros [k [[w [[Aw E] _]] _]].
      apply (generates_eq _ _
	2
	(fun y => match y with
			 | 0 => n
			 | S y => w
			 end)
	(fun y => match y with
			 | 0 => k
			 | S y => 1
			 end)
      ).
      + intros. destruct i.
	* apply Union_intror. constructor.
	* constructor. assumption.
      + simpl. lia.
  Qed.

End apery.


Theorem finite_gen A `{numerical_semigroup A} : exists B, Finite B /\ generator A B.
Proof.
   assert (exists n, A n /\ n <> 0) as [n [An n0]]. {
    destruct (cofinite_definitive A) as [m F];
      try apply ns_cofinite.
    exists (S m). split; [auto | lia].
  }
  exists (Add (apery A n) n).
  split.
  - apply Add_preserves_Finite. eapply cardinal_finite.
    apply apery_cardinality; assumption.
  - apply apery_generator; assumption.
Qed.
