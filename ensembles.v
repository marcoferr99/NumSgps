From Coq Require Export Ensembles Finite_sets Image.
From Coq Require Import ClassicalChoice Powerset_Classical_facts.

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
Arguments Union {U}.
Arguments cardinal {U}.
Arguments injective {U V}.


Infix "∪" := Union (at level 50).
Infix "∩" := Intersection (at level 40).

Ltac ex_ensembles x Hx :=
  apply Extensionality_Ensembles; split; unfold Included, In; intros x Hx.

(* the morgan law *)
Theorem de_morgan_cu {U} (A B : Ensemble U) :
  Complement (A ∪ B) = Complement A ∩ Complement B.
Proof.
  ex_ensembles x Hx; unfold Complement in *.
  - constructor; unfold In; intros C; apply Hx;
      auto with sets.
  - inversion Hx. subst. unfold In in *.
    intros C. inversion C; subst; contradiction.
Qed.

Hint Resolve de_morgan_cu : sets.


Theorem proj1_sig_injective {U} (P : U -> Prop) :
  injective (@proj1_sig _ P).
Proof.
  intros x y Hf. destruct x, y. simpl in *.
  subst. f_equal. apply proof_irrelevance.
Qed.

Theorem proj1_sig_image {U} (P : U -> Prop) :
  Im (Full_set _) (@proj1_sig _ P) = P.
Proof.
  ex_ensembles x Hx.
  - destruct Hx. subst. destruct x. assumption.
  - apply Im_intro with (x := exist x Hx); constructor.
Qed.




Inductive rel {U} {E : Ensemble U} (i : sig E) : U -> sig E -> Prop :=
  | rel_intro1 x (H : E x) : rel i x (exist x H)
  | rel_intro2 x (H : ~ E x) : rel i x i.

Theorem sig_cardinal {U} (E : Ensemble U) m :
  cardinal E m -> exists n, cardinal (Full_set (sig E)) n.
Proof.
  destruct (classic (inhabited (sig E))) as [I | I].
  - destruct I as [i].
    generalize (choice (@rel U E i)). intros [f Hf].
    + intros x. destruct (classic (E x)).
      * exists (exist x H). apply rel_intro1.
      * exists i. apply rel_intro2. assumption.
    + intros C.
      destruct (cardinal_Im_intro _ _ _ f _ C).
      assert (Im E f = Full_set _). {
	ex_ensembles a Ha; try constructor.
	destruct a as [a Ea]. exists a; try assumption.
	specialize Hf with a. inversion Hf.
	- subst. f_equal. apply proof_irrelevance.
	- subst. contradiction.
      }
      rewrite <- H0. eauto.
  - assert (Full_set (sig E) = Empty_set _). {
      ex_ensembles a Ha; try constructor.
      apply inhabits in a as In. contradiction.
    }
    rewrite H. exists 0. constructor.
Qed.

Theorem sig_cardinal_same {U} (E : Ensemble U) m n :
  cardinal E m -> cardinal (Full_set (sig E)) n -> m = n.
Proof.
  intros Cm Cn.
  rewrite <- (proj1_sig_image E) in Cm.
  eapply injective_preserves_cardinal; try eassumption.
  apply (proj1_sig_injective E).
Qed.
