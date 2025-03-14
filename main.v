From Coq Require Export Ensembles Finite_sets.
From Coq Require Import Arith Classical ClassicalChoice Image Lia List.
Require Export nat.
Import ListNotations.


(* submonoid of nat (with addition) *)
Class nat_submonoid (A : Ensemble nat) : Prop := {
  ns_zero : A 0;
  ns_closed : forall a b, A a -> A b -> A (a + b)
}.

(* numerical semigroup definition *)
Class numerical_semigroup (A : Ensemble nat) : Prop := {
  ns_submonoid :: nat_submonoid A;
  ns_cofinite : Finite (Complement A)
}.


Section numerical_semigroup.

  Context A `{numerical_semigroup A} (n : nat).

  (* apery set *)
  Definition apery x := A x /\ (n <= x -> ~ A (x - n)).

  Definition apery_min i w :=
    min (fun x => A x /\ congr_mod n x i) w.

  Theorem apery_min_exists : n <> 0 -> forall i,
    exists w, apery_min i w.
  Proof.
    intros n0 i. apply well_ordering_principle.
    destruct (nat_finite_definitive A) as [m Hm];
      try apply ns_cofinite.
    apply (Inhabited_intro (i + m * n)). split.
    + apply Hm. destruct n; lia.
    + unfold congr_mod. apply Div0.mod_add.
  Qed.

  Theorem apery_w_prop : n <> 0 -> forall i : {x | x < n},
    exists ! w, apery_min (proj1_sig i) w.
  Proof.
    intros n0 i.
    destruct (apery_min_exists n0 (proj1_sig i)) as [w Hw].
    exists w. split; try assumption.
    eauto using min_unique.
  Qed.

  Definition apery_w (n0 : n <> 0) :=
    proj1_sig (rel_to_func2 _ (apery_w_prop n0)).

  Definition apery_w_spec (n0 : n <> 0) :
    (forall i : {x | x < n}, apery_min (proj1_sig i) (apery_w n0 i)) /\ forall (i : {x | x < n}) w, apery_min (proj1_sig i) w -> w = apery_w n0 i :=
    proj2_sig (rel_to_func2 _ (apery_w_prop n0)).

  Theorem apery_w_inj (n0 : n <> 0) :
    injective (apery_w n0).
  Proof.
    intros x y I.
    apply proj1_sig_inj.
    destruct (apery_w_spec n0) as [Hw _].
    destruct (Hw x) as [[_ Hx] _].
    destruct (Hw y) as [[_ Hy] _].
    unfold congr_mod in *. rewrite I in Hx.
    rewrite Hx in Hy. clear Hx I n0 Hw.
    destruct x, y. simpl in *.
    rewrite mod_small, mod_small in Hy; assumption.
  Qed.

  (* equivalent definition for apery set *)
  Definition apery_alt w := exists i, apery_min i w.

  Theorem apery_alt_w (n0 : n <> 0) :
    Im (Full_set _) (apery_w n0) = apery_alt.
  Proof.
    ensemble_eq x Hx.
    - destruct Hx. subst. unfold apery_alt.
      destruct (apery_w_spec n0) as [SP _]. eauto.
    - set (y := exist (fun x => x < n) (x mod n) (mod_upper_bound _ _ n0)).
      apply Im_intro with (x := y); try constructor.
      apply (apery_w_spec n0). subst y. simpl in *.
      destruct Hx as [i Hi].
      unfold apery_min, congr_mod in *.
      replace ((x mod n) mod n) with (i mod n); try assumption.
      rewrite Div0.mod_mod. symmetry. apply Hi.
  Qed.

  (* apery_alt has a representative for every modulo class *)
  Theorem apery_alt_all_classes : n <> 0 ->
    forall x, exists w, apery_alt w /\ congr_mod n x w.
  Proof.
    intros n0 x.
    destruct (apery_alt_exists n0 x) as [w W].
    exists w. split.
    - unfold apery_alt. eauto.
    - unfold min in *. intuition auto with congr_mod.
  Qed.

  Print Union.
  Inductive rel {U} {E : Ensemble U} (i : sig E) : U -> sig E -> Prop :=
    | rel1 x (H : E x) : rel i x (exist _ x H)
    | rel2 x (H : ~ E x) : rel i x i.

  Theorem cardinal_same U (E : Ensemble U) m :
    cardinal E m -> cardinal (Full_set (sig E)) m.
  Proof.
    destruct (classic (inhabited (sig E))).
    - destruct H0 as [i].
      generalize (choice (@rel U E i)). intros [f Hf].
      + intros x. destruct (classic (E x)).
	* exists (exist _ x H0). apply rel1.
	* exists i. apply rel2. assumption.
      + intros C.
	destruct (cardinal_Im_intro _ _ _ f _ C).
	assert (Im E f = Full_set _). {
	  apply Extensionality_Ensembles.
	  split; try constructor.
	  unfold Included, In. intros.
	  destruct x0. exists x0; try assumption.
	  specialize Hf with x0. inversion Hf.
	  - subst. simpl in *. f_equal. apply proof_irrelevance.
	  - subst. contradiction.
	}
	rewrite H1 in H0.
	assert (m = x). {
	  eapply injective_preserves_cardinal.
	  - assert (injective (@proj1_sig _ E)).
	    + intros a b I. destruct a, b. simpl in *.
	      subst x0. f_equal. apply proof_irrelevance.
	    + apply H2.
	  - apply H0.
	  - assert ((Im (Full_set {x : U | E x}) (@proj1_sig _ E)) = E).
	    + apply Extensionality_Ensembles.
	      split; unfold Included, In; intros a.
	      * intros. inversion H2. subst. destruct x0.
		simpl. assumption.
	      * intros. exists (exist _ a H2).
		-- constructor.
		-- simpl. reflexivity.
	    + rewrite <- H2 in C. apply C.
	}
	subst m. assumption.
    - intros. assert (0 = m).
      + eapply cardinal_Empty. replace (Empty_set _) with E; try assumption.
	* apply Extensionality_Ensembles.
	  split; unfold Included, In; intros x Hx.
	  -- exfalso. apply H0. constructor.
	     apply (exist _ x Hx).
	  -- inversion Hx.
      + subst m. assert ((Full_set {x : U | E x}) = (Empty_set {x | E x})).
	* apply Extensionality_Ensembles.
	  split; intros x Hx; unfold In.
	  -- exfalso. apply H0. constructor. apply x.
	  -- constructor.
	* rewrite H2 at 1. constructor.
  Qed.

  Theorem apery_alt_card : n <> 0 -> cardinal apery_alt n.
  Proof.
    intros n0.
    generalize (apery_alt_f n0). intros [f [If Hf]].
    generalize (cardinal_lt_n n). intros C.
    apply cardinal_same in C.
    destruct (cardinal_Im_intro _ _ _ f _ C) as [p Hp].
    assert (p = n).
    - eapply injective_preserves_cardinal; eauto.
    - subst p. rewrite <- Hf. assumption.
Qed.

  (* the apery set of n does not contain two different numbers who are congruent
     modulo n *)
  Theorem apery_congr_unique : A n ->
    forall a b, apery a -> apery b -> congr_mod n a b -> a = b.
  Proof.
    intros An.
    assert (T : forall a b, apery a -> apery b -> a <= b -> congr_mod n a b -> a = b). {
      intros a b Aa Ab L C.
      destruct (le_ge_cases n b) as [Ln | Lb].
      - apply Ab in Ln.
	apply congr_mod_divide in C. destruct C as [k Hk].
	destruct k; try lia.
	exfalso. apply Ln.
	assert (Hb : b = S k * n + a); try lia.
	rewrite Hb.
	replace (S k * n + a - n) with (k * n + a);
	  try lia.
	apply ns_closed.
	+ clear Hk Ln Hb. induction k.
	  * apply ns_zero.
	  * apply ns_closed; assumption.
	+ apply Aa.
      - destruct (le_gt_cases n a); try lia.
        unfold congr_mod in C.
	rewrite mod_small in C; try assumption.
	rewrite mod_small in C; try assumption.
	unfold apery in Ab.
	destruct (le_gt_cases n b); try assumption.
	assert (b = n); try lia. subst.
	destruct Ab.
	exfalso. apply H3; try assumption.
	rewrite sub_diag. apply ns_zero.
    }
    intros. destruct (le_ge_cases a b); try auto.
    - symmetry. auto with congr_mod.
  Qed.

  (* apery and apery_alt are the same set *)
  Theorem apery_alt_eq : A n -> n <> 0 ->
    apery = apery_alt.
  Proof.
    intros An n0.
    assert (I : Included apery_alt apery). {
      unfold Included, In. unfold apery_alt, apery.
      intros w [i Hw]. unfold min in *.
      destruct Hw as [[Aw C] Hw].
      split; try assumption. intros L.
      specialize Hw with (w - n). intros AS.
      assert (N : ~(w <= w - n)); try lia.
      apply N. apply Hw. split; try assumption.
      unfold congr_mod.
      rewrite <- Div0.mod_add with (b := 1).
      rewrite <- C. f_equal. lia.
    }
    apply Extensionality_Ensembles.
    split; try assumption.
    unfold Included, In. intros w Hw.
    assert (AH := apery_alt_all_classes n0 w).
    destruct AH as [x [Hx1 Hx2]].
    destruct (classic (x = w)).
    + subst. assumption.
    + apply I in Hx1. exfalso. apply H0.
      generalize apery_congr_unique.
      auto with congr_mod.
  Qed.

  (* every element of A can be written as k * n + w, where w is an element
     of apery *)
  Theorem apery_generates : A n -> n <> 0 ->
    forall a, A a -> exists ! k w, apery w /\ a = k * n + w.
  Proof.
    intros An n0 a Aa.
    destruct (classic (apery a)) as [Ap | Ap].
    - exists 0. split.
      + exists a. split; try auto.
	intros. apply H0.
      + intros. repeat destruct H0.
	destruct x'; try reflexivity.
	exfalso. destruct (le_gt_cases n a).
	* apply Ap; try assumption.
	  rewrite H2. replace (S x' * n + x - n) with (x' * n + x); try lia.
	  apply ns_closed; try assumption. clear H0 H3 H2 H1 H4.
	  induction x'; try apply ns_zero.
	  apply ns_closed; assumption.
	* lia.
    - assert (Hk : exists k, a >= S k * n /\ ~ (apery (a - k * n)) /\ apery (a - S k * n)). {
	assert (M : exists k, min (fun k => n <= a - S k * n -> ~ A (a - S k * n - n)) k). {
	    apply well_ordering_principle.
	    apply (Inhabited_intro a). unfold In.
	    induction n; lia.
	}
	destruct M as [k [M1 M2]]. exists k.
	assert (G : a >= S k * n). {
	  destruct k.
	  - apply not_and_or in Ap. intuition.
	  - specialize M2 with k.
	    assert (~ S k <= k); lia.
	}
	assert (Ak : A (a - S k * n)). {
	  destruct k.
	  - unfold apery in Ap. apply not_and_or in Ap.
	    replace (1 * n) with n in *; try lia.
	    destruct Ap; try contradiction.
	    apply NNPP. auto.
	  - specialize M2 with k. apply NNPP. intros C.
	    assert (~ S k <= k); try lia.
	    apply H0. apply M2. intros.
	    replace (a - S k * n - n) with (a - S (S k) * n); try assumption.
	    lia.
	}
	split; try assumption.
	unfold apery. split.
	- intros C. destruct C as [C1 C2].
	  apply C2; try lia.
	  replace (a - k * n - n) with (a - S k * n).
	  + assumption.
	  + lia.
	- intuition.
      }
      destruct Hk as [k [K1 [K2 K3]]].
      exists (S k). split.
      + exists (a - S k * n). split.
	* split; try assumption. lia.
	* intros l [L1 L2]. lia.
      + intros l [z [[Z1 Z2] Z3]].
	assert (E : z = a - S k * n). {
	  apply apery_congr_unique; try assumption.
	  unfold congr_mod.
	  symmetry. rewrite <- Div0.mod_add with (b := S k).
	  replace (a - S k * n + S k * n) with a; try lia.
	  subst a. rewrite add_comm. apply Div0.mod_add.
	}
	assert (E1 : a = z + S k * n); try lia.
	subst a.
	apply (mul_cancel_r _ _ n); try assumption. lia.
  Qed.

  Definition generator B := forall a, A a ->
    exists r x l, (forall y, y < r -> B (x y)) /\
    a = fold_right (fun u v => v + l u * x u) 0 (seq 0 r).
End NumericalSemigroups.

Theorem finite_gen A `{numerical_semigroup A} : exists B, Finite B /\ generator A B.
Proof.
   assert (Hn : exists n, A n /\ n <> 0). {
    generalize (nat_finite_definitive A).
    intros [m F]; try apply ns_cofinite.
    exists (m + 1). split; try lia.
    apply F. lia.
  }
  destruct Hn as [n [An n0]].
  exists (Add (apery A n) n).
  split.
  - apply Add_preserves_Finite.
    apply (cardinal_finite _ _ n).
    rewrite apery_alt_eq; try assumption.
    apply apery_alt_card; try assumption.
  - intros a Aa.
    generalize (apery_generates A n An n0 a Aa).
    intros [k [[w [[Aw E] _]] _]].
    exists 2.
    exists (fun y => match y with
		     | 0 => n
		     | S y => w
		     end).
    exists (fun y => match y with
		     | 0 => k
		     | S y => 1
		     end).
    split.
    + intros. destruct y.
      * apply Union_intror. constructor.
      * constructor. assumption.
    + simpl. lia.
Qed.
