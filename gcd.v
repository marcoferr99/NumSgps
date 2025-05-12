From Coq Require Import ZArith.
Require Import def.
Import ZArith Znumtheory.


Definition gcd_l l := foldr Z.gcd 0 l.

Theorem gcd_l_divide l : Forall (Z.divide (gcd_l l)) l.
Proof.
  induction l; constructor; simpl.
  - apply Z.gcd_divide_l.
  - apply Forall_forall. intros x Hx.
    eapply Z.divide_trans.
    + apply Z.gcd_divide_r.
    + eapply Forall_forall; eassumption.
Qed.

Theorem gcd_l_greatest l :
  forall d, Forall (Z.divide d) l -> (d | gcd_l l).
Proof.
  induction l; intros d Hd; simpl.
  - apply Z.divide_0_r.
  - apply Z.gcd_greatest.
    + eapply Forall_forall; [apply Hd|]. now left.
    + apply IHl. now inversion Hd.
Qed.

Definition extgcd_l_aux a b :=
  match b with (d, l) =>
    match extgcd a d with (x, y, d) =>
      (d, x :: map (fun u => y * u) l)
    end
  end.

Definition extgcd_l := foldr extgcd_l_aux (0, []).

Theorem extgcd_l_correct l d c :
  extgcd_l l = (d, c) -> d = gcd_l l /\
  d = fold_right Z.add 0 (zip_with Z.mul c l).
Proof.
  intros E.
  replace d with (fst (extgcd_l l)); [|now rewrite E].
  replace c with (snd (extgcd_l l)); [|now rewrite E].
  clear d c E.
  split.
  - induction l; simpl; [reflexivity|].
    unfold extgcd_l_aux.
    destruct (extgcd_l l) as (d, c) eqn : E1.
    destruct (extgcd a d) as (p, d') eqn : E2.
    destruct p as (x, y) eqn : E3.
    rewrite <- IHl.
    simpl. eapply extgcd_correct. eassumption.
  - induction l; simpl; [reflexivity|].
    unfold extgcd_l_aux.
    destruct (extgcd_l l) as (d, c) eqn : E1.
    destruct (extgcd a d) as (p, d') eqn : E2.
    destruct p as (x, y) eqn : E3. simpl in *.
    apply extgcd_correct in E2 as [E4 E5].
    rewrite <- E4. f_equal.
    rewrite IHl. clear.
    generalize dependent c. induction l; intros c.
    + repeat rewrite zip_with_nil_r. simpl. ring.
    + destruct c; simpl; [ring|].
      rewrite <- IHl. ring.
Qed.

Definition l_pos l := List.filter (Z.ltb 0) l.

Theorem l_pos_pos l : Forall (Z.lt 0) (l_pos l).
Proof.
  induction l; [constructor|].
  simpl. destruct (Z.ltb_spec 0 a); [|assumption].
  now constructor.
Qed.

Definition l_neg l :=
  map (Z.opp) (List.filter (Z.gtb 0) l).

Theorem l_neg_pos l : Forall (Z.lt 0) (l_neg l).
Proof.
  induction l; [constructor|].
  unfold l_neg. simpl.
  destruct (Z.gtb_spec 0 a); [|assumption].
  simpl. constructor; [|assumption]. lia.
Qed.

Theorem l_pos_l_neg l :
  foldr Z.add 0 (l_pos l) - foldr Z.add 0 (l_neg l) =
  foldr Z.add 0 l.
Proof.
  induction l; simpl; [lia|]. unfold l_neg. simpl.
  destruct (Z.ltb_spec 0 a), (Z.gtb_spec 0 a).
  - lia.
  - simpl. rewrite <- IHl. symmetry. apply Z.add_assoc.
  - simpl. rewrite <- IHl. unfold l_neg. lia.
  - replace a with 0; [|lia]. rewrite <- IHl.
    unfold l_neg. lia.
Qed.

Definition bez_l l :=
  match extgcd_l l with (d, c) => zip_with Z.mul c l end.

Definition bez_neg l := foldr Z.add 0 (l_neg (bez_l l)).

Theorem gcd_l_bez_l l : gcd_l l = foldr Z.add 0 (bez_l l).
Proof.
  induction l; [reflexivity|].
  simpl. unfold bez_l.
  destruct (extgcd_l (a :: l)) as (d, c) eqn : E.
  apply extgcd_l_correct in E as [E1 E2].
  destruct c; simpl in *; [lia|].
  now rewrite <- E1, E2.
Qed.

Theorem gcd_l_bez_neg l :
  gcd_l l + bez_neg l = foldr Z.add 0 (l_pos (bez_l l)).
Proof.
  rewrite gcd_l_bez_l. rewrite <- l_pos_l_neg.
  unfold bez_neg. lia.
Qed.

Open Scope nat_scope.

Definition nat_gcd_l l := foldr gcd 0 l.

Definition lim l := Z.to_nat (bez_neg (map Z.of_nat l)).

Definition lim_ln l :=
  match extgcd_l (fmap Z.of_nat l) with (d, c) => intros x y Hx Hy.
  sum_list_with Z.to_nat c end.

Theorem Nat2Z_gcd_l l :
  nat_gcd_l l = Z.to_nat (gcd_l (map Z.of_nat l)).
Proof.
  assert (L : forall l, (0 <= gcd_l (map Z.of_nat l))%Z). {
    clear. induction l; simpl; [lia|].
    apply Z.gcd_nonneg.
  }
  induction l; simpl; [reflexivity|].
  apply gcd_unique.
  - rewrite <- (Nat2Z.id a) at 2.
    apply Z2Nat.divide.
    + apply (L (a :: l)).
    + apply Zle_0_nat.
    + apply Z.gcd_divide_l.
  - rewrite IHl. apply Z2Nat.divide.
    + apply (L (a :: l)).
    + apply L.
    + apply Z.gcd_divide_r.
  - intros q Hqa Hq. apply Nat2Z.divide.
    rewrite Z2Nat.id; [|apply (L (a :: l))].
    apply Z.gcd_greatest.
    + now apply Nat2Z.divide.
    + apply Z2Nat.divide.
      * apply Zle_0_nat.
      * apply L.
      * rewrite <- IHl. now rewrite Nat2Z.id.
Qed.

Theorem sum_list_with_foldr {T} (P : T -> nat) l :
  sum_list_with P l = foldr (fun a b => b + P a) 0 l.
Proof.
  induction l; simpl; [reflexivity|].
  rewrite IHl. lia.
Qed.

Theorem t l : lim l + nat_gcd_l l =
  sum_list (map Z.to_nat (l_pos (bez_l (map Z.of_nat l)))).
Proof.
  unfold lim, bez_neg.
  rewrite Nat2Z_gcd_l.
  rewrite <- Z2Nat.inj_add.
  - rewrite Z.add_comm. rewrite gcd_l_bez_neg.
    remember (l_pos (bez_l (map Z.of_nat l))) as s.
    generalize (l_pos_pos (bez_l (map Z.of_nat l))).
    rewrite <- Heqs. clear.
    induction s; simpl; [reflexivity|]. intros F.
    inversion F as [|? ? ? Fs].
    rewrite Z2Nat.inj_add.
    + rewrite IHs; [reflexivity|assumption].
    + lia.
    + generalize Fs. clear. induction s; simpl; [lia|].
      intros F. inversion F. apply IHs in H2. lia.
  - generalize (l_neg_pos (bez_l (map Z.of_nat l))).
    intros F.
    remember (l_neg (bez_l (map Z.of_nat l))) as s eqn : E. clear E.
    induction s; simpl; [reflexivity|].
    inversion F as [|? ? ? Fs]. apply IHs in Fs. lia.
  - remember (map Z.of_nat l) as s. clear.
    destruct s; simpl; [lia|].
    apply Z.gcd_nonneg.
Qed.

Theorem sum_list_with_map {A} l (f : A -> nat) :
  sum_list_with f l = sum_list (map f l).
Proof. induction l; simpl; auto. Qed.

Theorem map_fmap {A B} (f : A -> B) l : map f l = f <$> l.
Proof.
  induction l; [reflexivity|].
  simpl. rewrite IHl. reflexivity.
Qed.

Theorem extgcd_l_length l d c :
  extgcd_l l = (d, c) -> length c = length l.
Proof.
  generalize dependent c. generalize dependent d.
  induction l; destruct c; simpl in *; try easy; intros.
  - unfold extgcd_l_aux in H.
    destruct (extgcd_l l).
    destruct (extgcd a z).
    now destruct p.
  - f_equal.
    unfold extgcd_l_aux in H.
    destruct (extgcd_l l).
    destruct (extgcd a z0).
    destruct p. injection H. intros.
    rewrite <- H0.
    rewrite length_map. eapply IHl. reflexivity.
Qed.

Theorem t1 l : generates l (lim l + nat_gcd_l l).
Proof.
  rewrite t.
  rewrite <- sum_list_with_map.
  unfold bez_l.
  destruct (extgcd_l (map Z.of_nat l)) as (d, c) eqn : E.
  assert (Ln : length c = length l). {
    erewrite extgcd_l_length.
    - rewrite length_map. reflexivity.
    - eassumption.
  }
  clear E d.
  set (x i := l !!! i).
  set (y i := Z.to_nat (c !!! i)).
  apply (generates_eq _ _ (length l) x y).
  - intros i Hi. subst x. simpl.
    now apply elem_of_list_lookup_total_2.
  - assert (forall r, r <= length l -> sum_list_with (fun i => y i * x i) (seq 0 r) = sum_list (take r (zip_with mul (fmap y (seq 0 r)) (fmap x (seq 0 r))))). {
      induction r; [reflexivity|]. intros L.
      rewrite seq_S.
      repeat rewrite fmap_app. rewrite zip_with_app.
      - simpl. rewrite take_S.
	+ repeat rewrite sum_list_with_app. simpl.
	  rewrite IHr; [|lia].
	  f_equal.
	  * rewrite take_app_le; [reflexivity|].
	    rewrite length_zip_with_r_eq; repeat rewrite length_fmap, length_seq; lia.
	  * rewrite lookup_total_app_r;
	      rewrite length_zip_with_r_eq; repeat rewrite length_fmap, length_seq; try lia.
	      now rewrite sub_diag.
	+ rewrite length_app, length_zip_with_r_eq;
	    repeat rewrite length_fmap, length_seq; simpl; lia.
      - now repeat rewrite length_fmap, length_seq.
    }
    rewrite H; [|lia]. clear H.
    rewrite take_ge.
    2:{
      rewrite length_zip_with_r_eq; repeat rewrite length_fmap, length_seq; lia.
    }
    replace (y <$> seq 0 (length l)) with (map Z.to_nat c).
    + replace (x <$> seq 0 (length l)) with l.
      * clear. generalize dependent c.
	induction l; destruct c; simpl; try reflexivity.
	destruct (Z.ltb_spec 0 (z * Z.of_nat a)).
	-- simpl. rewrite IHl. f_equal.
	   destruct (Z.leb_spec 0 z).
	   ++ rewrite Z2Nat.inj_mul; lia.
	   ++ lia.
	-- rewrite IHl. lia.
      * subst x. apply list_eq.
	intros i.
	rewrite list_lookup_fmap.
	destruct (le_gt_cases (length l) i).
	-- rewrite lookup_seq_ge; [|assumption].
	   rewrite lookup_ge_None. assumption.
	-- rewrite lookup_seq_lt; [|assumption].
	   apply lookup_lt_is_Some_2 in H.
	   destruct H. rewrite H. simpl.
	   now rewrite (list_lookup_total_correct _ _ x).
    + subst y. apply list_eq. intros i.
      rewrite (list_lookup_fmap _ (seq 0 (length l))).
      destruct (le_gt_cases (length l) i).
      * rewrite lookup_seq_ge; [|assumption].
	rewrite lookup_ge_None.
	rewrite length_map. lia.
      * rewrite lookup_seq_lt; [|assumption].
	assert (L := H).
	rewrite <- Ln in H. erewrite <- length_map in H.
	eapply lookup_lt_is_Some_2 in H.
	destruct H. rewrite H. simpl.
	f_equal.
	erewrite <- (list_lookup_total_correct _ _ x0); [|eassumption].
	erewrite list_lookup_total_fmap; [|lia].
	reflexivity.
Qed.

Theorem Z2Nat_sum l :
  sum_list l = Z.to_nat (foldr Z.add 0%Z (map Z.of_nat l)).
Proof.
  induction l; [reflexivity|].
  simpl. rewrite IHl. rewrite Z2Nat.inj_add.
  - now rewrite Nat2Z.id.
  - lia.
  - clear. induction l; simpl; lia.
Qed.

Theorem Z2Nat_sum_2 l : Forall (Z.le 0) l ->
  sum_list (map Z.to_nat l) = Z.to_nat (foldr Z.add 0%Z l).
Proof.
  induction l; [reflexivity|].
  simpl. intros. inversion H. subst.
  rewrite IHl; [|assumption].
  rewrite Z2Nat.inj_add; try reflexivity; try assumption.
  - generalize H3. clear. induction l; simpl; [lia|].
    intros F. inversion F. apply IHl in H2. lia.
Qed.

Theorem t2 l : generates l (lim l).
Proof.
  unfold lim, bez_neg.
  rewrite <- Z2Nat_sum_2.
  2:{
    generalize l_neg_pos. intros.
    apply Forall_forall. intros.
    assert (0 < x)%Z; [|lia].
    eapply Forall_forall; try eassumption. apply H.
  }
  unfold bez_l.
  destruct (extgcd_l (map Z.of_nat l)) as (d, c) eqn : E.
  assert (Ln : length c = length l). {
    erewrite extgcd_l_length.
    - rewrite length_map. reflexivity.
    - eassumption.
  }
  clear E d.
  set (x i := l !!! i).
  set (y i := Z.to_nat (- c !!! i)).
  apply (generates_eq _ _ (length l) x y).
  - intros i Hi. subst x. simpl.
    now apply elem_of_list_lookup_total_2.
  - assert (forall r, r <= length l -> sum_list_with (fun i => y i * x i) (seq 0 r) = sum_list (take r (zip_with mul (fmap y (seq 0 r)) (fmap x (seq 0 r))))). {
      induction r; [reflexivity|]. intros L.
      rewrite seq_S.
      repeat rewrite fmap_app. rewrite zip_with_app.
      - simpl. rewrite take_S.
	+ repeat rewrite sum_list_with_app. simpl.
	  rewrite IHr; [|lia].
	  f_equal.
	  * rewrite take_app_le; [reflexivity|].
	    rewrite length_zip_with_r_eq; repeat rewrite length_fmap, length_seq; lia.
	  * rewrite lookup_total_app_r;
	      rewrite length_zip_with_r_eq; repeat rewrite length_fmap, length_seq; try lia.
	      now rewrite sub_diag.
	+ rewrite length_app, length_zip_with_r_eq;
	    repeat rewrite length_fmap, length_seq; simpl; lia.
      - now repeat rewrite length_fmap, length_seq.
    }
    rewrite H; [|lia]. clear H.
    rewrite take_ge.
    2:{
      rewrite length_zip_with_r_eq; repeat rewrite length_fmap, length_seq; lia.
    }
    replace (y <$> seq 0 (length l)) with (map (fun x => Z.to_nat (- x)) c).
    + replace (x <$> seq 0 (length l)) with l.
      * clear. generalize dependent c.
	induction l; destruct c; simpl; try reflexivity.
	unfold l_neg in *. simpl.
	destruct (Z.gtb_spec 0 (z * Z.of_nat a)).
	-- simpl. rewrite IHl. f_equal.
	   rewrite Zopp_mult_distr_l.
	   destruct (Z.leb_spec 0 z).
	   ++ rewrite Z2Nat.inj_mul; lia.
	   ++ lia.
	-- rewrite IHl. lia.
      * subst x. apply list_eq.
	intros i.
	rewrite list_lookup_fmap.
	destruct (le_gt_cases (length l) i).
	-- rewrite lookup_seq_ge; [|assumption].
	   rewrite lookup_ge_None. assumption.
	-- rewrite lookup_seq_lt; [|assumption].
	   apply lookup_lt_is_Some_2 in H.
	   destruct H. rewrite H. simpl.
	   now rewrite (list_lookup_total_correct _ _ x).
    + subst y. apply list_eq. intros i.
      rewrite (list_lookup_fmap _ (seq 0 (length l))).
      destruct (le_gt_cases (length l) i).
      * rewrite lookup_seq_ge; [|assumption].
	rewrite lookup_ge_None.
	rewrite length_map. lia.
      * rewrite lookup_seq_lt; [|assumption].
	assert (L := H).
	rewrite <- Ln in H. erewrite <- length_map in H.
	eapply lookup_lt_is_Some_2 in H.
	destruct H. rewrite H. simpl.
	f_equal.
	erewrite <- (list_lookup_total_correct _ _ x0); [|eassumption].
	erewrite list_lookup_total_fmap; [|lia].
	reflexivity.
Qed.

Theorem generates_mul `{ElemOf nat C} (l : C) x y :
  generates l x -> generates l (y * x).
Proof.
  intros. induction y.
  - rewrite mul_0_l.
    apply (generates_eq _ _ 0 (fun i => 0) (fun i => 0)).
    + intros. lia.
    + reflexivity.
  - simpl. now apply generates_add.
Qed.

Theorem generates_lim l x y :
  x <= y -> generates l (y * lim l + x * nat_gcd_l l).
Proof.
  intros L.
  replace y with (y - x + x); [|lia].
  rewrite mul_add_distr_r, <- add_assoc.
  apply generates_add.
  - apply generates_mul. apply t2.
  - rewrite <- mul_add_distr_l.
    apply generates_mul. apply t1.
Qed.

Theorem gen l x h k:
  generates l x -> generates (h :: l) (k * h + x).
Proof.
  intros [s a b G].
  apply (generates_eq _ _ (S s) (fun i => match i with 0 => h | S i => a i end) (fun i => match i with 0 => k | S i => b i end)).
  - intros i Hi. destruct i; [left|].
    right. apply G. lia.
  - clear. simpl. induction s; [reflexivity|].
    rewrite (seq_S _ 1). rewrite sum_list_with_app.
    rewrite seq_S. simpl in *.
    apply add_cancel_l in IHs. rewrite <- IHs.
    rewrite sum_list_with_app. simpl. reflexivity.
Qed.
