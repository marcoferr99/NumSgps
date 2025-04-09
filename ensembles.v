From Coq Require Export Ensembles Finite_sets Image.
From Coq Require Import ClassicalChoice Powerset_Classical_facts.

(** Set implicit arguments. *)

Arguments Add {U}.
Arguments Complement {U}.
Arguments exist {A P}.
Arguments Finite {U}.
Arguments Im {U V}.
Arguments In {U}.
Arguments Included {U}.
Arguments Inhabited {U}.
Arguments Inhabited_intro {U B}.
Arguments Intersection {U}.
Arguments Subtract {U}.
Arguments Union {U}.
Arguments cardinal {U}.
Arguments injective {U V}.

(** * Ensembles *)

(** Usual notation for union and intersection. *)

Infix "∪" := Union (at level 50).
Infix "∩" := Intersection (at level 40).

(** Tactic for splitting ensembles equality into the two inclusions. *)

Ltac ex_ensembles x Hx :=
  apply Extensionality_Ensembles; split; unfold Included, In; intros x Hx.

(** The morgan law (complement of union). *)

Theorem de_morgan_cu {U} (A B : Ensemble U) :
  Complement (A ∪ B) = Complement A ∩ Complement B.
Proof.
  ex_ensembles x Hx; unfold Complement in *.
  - constructor; unfold In; intros C; apply Hx;
      auto with sets.
  - inversion Hx. subst. unfold In in *.
    intros C. inversion C; subst; contradiction.
Qed.


(** * Sigma types *)

(** [proj1_sig] is injective. Requires proof irrelevance. *)

Theorem proj1_sig_injective {U} (P : U -> Prop) :
  injective (@proj1_sig _ P).
Proof.
  intros x y Hf. destruct x, y. simpl in *.
  subst. f_equal. apply proof_irrelevance.
Qed.

Theorem proj1_sig_Im {U} (P : U -> Prop) :
  Im (Full_set _) (@proj1_sig _ P) = P.
Proof.
  ex_ensembles x Hx.
  - destruct Hx. subst. destruct x. assumption.
  - apply Im_intro with (x := exist x Hx); constructor.
Qed.


(** * Cardinality *)

(** The image of an ensemble with cardinality [n] has cardinality [n].
    *)

Theorem injective_cardinal {U V} A (f : U -> V) n :
  injective f -> cardinal A n -> cardinal (Im A f) n.
Proof.
  intros I C.
  destruct (cardinal_Im_intro _ _ _ f _ C) as [p Cp].
  replace n with p; try assumption.
  eapply injective_preserves_cardinal; eassumption.
Qed.

(* [Full_set (sig E)] has the same cardinality as [E]. *)

Inductive sig_cardinal_aux {U} (E : Ensemble U) i :
  U -> sig E -> Prop :=
  | sig_cardinal_aux_intro x (H : E x) :
      sig_cardinal_aux E i x (exist x H)
  | sig_cardinal_aux_intro_i x (H : ~ E x) :
      sig_cardinal_aux E i x i.

Theorem sig_cardinal {U} (E : Ensemble U) n :
  cardinal E n -> cardinal (Full_set (sig E)) n.
Proof.
  intros C.
  assert (exists m, cardinal (Full_set (sig E)) m) as [m Hm]. {
    destruct (classic (inhabited (sig E))) as [I | I].
    - destruct I as [i].
      generalize (choice (sig_cardinal_aux E i)).
      intros [f Hf].
      + intros x. destruct (classic (E x)).
	* exists (exist x H). apply sig_cardinal_aux_intro.
	* exists i. apply sig_cardinal_aux_intro_i.
	  assumption.
      + destruct (cardinal_Im_intro _ _ _ f _ C).
	exists x.
	replace (Full_set _) with (Im E f); try assumption.
	ex_ensembles a Ha; try constructor.
	destruct a as [a Ea]. exists a; try assumption.
	specialize Hf with a.
	inversion Hf; subst; try contradiction.
	f_equal. apply proof_irrelevance.
    - exists 0.
      replace (Full_set _) with (Empty_set (sig E));
	try constructor.
      ex_ensembles x Hx; try constructor.
      exfalso. apply I. constructor. assumption.
  }
  replace -> n with m; try assumption.
  eapply injective_preserves_cardinal; try eassumption.
  - apply proj1_sig_injective.
  - rewrite proj1_sig_Im. assumption.
Qed.
