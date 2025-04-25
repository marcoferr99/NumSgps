From stdpp Require Export list sorting.
From Coq Require Import Lia.


(*******************************)
(** * Lists of natural numbers *)
(*******************************)

Theorem list_max_notin l x : x > list_max l -> x ∉ l.
Proof.
  intros Hx. destruct l eqn : E; [easy|].
  rewrite <- E in *.
  apply list_max_lt in Hx; [|now rewrite E].
  intros N. eapply Forall_forall in Hx; try eassumption.
  lia.
Qed.

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
