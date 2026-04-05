(** * Sorted lists and permutations

    Lemmas connecting [StronglySorted], [Permutation], and sorted insertion.
    All results are over [nat] with [Nat.le]. *)

From Stdlib Require Import Arith Lia List PeanoNat Sorting Permutation.
Import ListNotations.

(** ** Sorted insertion *)

Fixpoint insert (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => [x]
  | h :: t => if x <=? h then x :: h :: t else h :: insert x t
  end.

Lemma insert_perm : forall x l, Permutation (x :: l) (insert x l).
Proof.
  intros x l. induction l as [| h t IH]; simpl; [reflexivity |].
  destruct (x <=? h); [reflexivity |].
  eapply perm_trans; [apply perm_swap | constructor; exact IH].
Qed.

Lemma insert_Forall : forall (P : nat -> Prop) x l,
  P x -> Forall P l -> Forall P (insert x l).
Proof.
  intros P x l Hx Hl.
  apply (Permutation_Forall (insert_perm x l)).
  constructor; assumption.
Qed.

Lemma Forall_le_insert : forall x y l,
  y <= x -> Forall (Nat.le y) l -> Forall (Nat.le y) (insert x l).
Proof.
  intros. apply insert_Forall; [lia | assumption].
Qed.

Lemma insert_sorted :
  forall x l, StronglySorted Nat.le l -> StronglySorted Nat.le (insert x l).
Proof.
  intros x l. induction l as [| h t IH]; simpl; intro Hs.
  - constructor; constructor.
  - destruct (StronglySorted_inv Hs) as [Ht Hle].
    destruct (x <=? h) eqn:E.
    + apply Nat.leb_le in E.
      constructor; [exact Hs |].
      constructor; [exact E |]. eapply Forall_impl; [| exact Hle]. lia.
    + apply Nat.leb_gt in E.
      constructor; [exact (IH Ht) | exact (Forall_le_insert x h t ltac:(lia) Hle)].
Qed.

(** ** Removing one occurrence *)

Fixpoint remove_one (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => if Nat.eq_dec x h then t else h :: remove_one x t
  end.

Lemma remove_one_perm :
  forall x l, In x l -> Permutation l (x :: remove_one x l).
Proof.
  intros x l. induction l as [| h t IH]; simpl; [tauto |].
  intros [-> | Hin].
  - destruct (Nat.eq_dec x x); [reflexivity | contradiction].
  - destruct (Nat.eq_dec x h) as [-> | ?]; [reflexivity |].
    eapply perm_trans; [| apply perm_swap]. constructor. exact (IH Hin).
Qed.

(** ** Sorted permutations are equal *)

Lemma ssorted_perm_eq : forall l1 l2,
  StronglySorted Nat.le l1 -> StronglySorted Nat.le l2 ->
  Permutation l1 l2 -> l1 = l2.
Proof.
  intros l1. induction l1 as [| a l1 IH]; intros l2 Hs1 Hs2 Hp.
  - symmetry. exact (Permutation_nil Hp).
  - destruct l2 as [| b l2].
    { apply Permutation_sym, Permutation_nil in Hp. discriminate. }
    assert (a = b).
    { (* a is in b::l2 and b is in a::l1, so both heads bound each other *)
      assert (In b (a :: l1))
        by (apply (Permutation_in _ (Permutation_sym Hp)); now left).
      assert (In a (b :: l2))
        by (apply (Permutation_in _ Hp); now left).
      destruct H as [-> | Hb]; [reflexivity |].
      destruct H0 as [-> | Ha]; [reflexivity |].
      pose proof (proj2 (StronglySorted_inv Hs1)) as Hfa.
      pose proof (proj2 (StronglySorted_inv Hs2)) as Hfb.
      rewrite Forall_forall in Hfa, Hfb.
      specialize (Hfa b Hb). specialize (Hfb a Ha). lia. }
    subst b. f_equal. apply IH.
    + exact (proj1 (StronglySorted_inv Hs1)).
    + exact (proj1 (StronglySorted_inv Hs2)).
    + exact (Permutation_cons_inv Hp).
Qed.
