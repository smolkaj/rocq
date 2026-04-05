(** * The Fundamental Theorem of Arithmetic

    Every natural number ≥ 2 has a unique prime factorization.

    We represent factorizations as sorted lists of primes whose product
    equals [n].  Existence follows by strong induction (find the smallest
    prime factor, divide it out, recurse).  Uniqueness follows from
    Euclid's lemma — derived in [Primes] from Bézout via [Nat.gauss] —
    which lets us peel matching primes off two factorizations one at a time. *)

From Stdlib Require Import Arith Lia List PeanoNat Sorting Permutation.
From Roq Require Import Primes SortedPermutation.
Import ListNotations.

(** ** Definitions *)

Fixpoint product (l : list nat) : nat :=
  match l with
  | [] => 1
  | h :: t => h * product t
  end.

Definition factorization_of (n : nat) (l : list nat) : Prop :=
  Forall prime l /\ StronglySorted Nat.le l /\ product l = n.

Lemma insert_product : forall x l, product (insert x l) = x * product l.
Proof.
  intros x l. induction l as [| h t IH]; simpl; [lia |].
  destruct (x <=? h); simpl; [lia | rewrite IH; lia].
Qed.

(** ** Product lemmas *)

Lemma product_perm :
  forall l1 l2, Permutation l1 l2 -> product l1 = product l2.
Proof.
  intros l1 l2 H. induction H; simpl; lia.
Qed.

Lemma product_prime_ge_1 :
  forall l, Forall prime l -> 1 <= product l.
Proof.
  induction l as [| h t IH]; simpl; [lia |].
  intro Hpl. inversion Hpl; subst.
  destruct H1 as [Hh _]. specialize (IH H2). nia.
Qed.

Lemma product_cons_lt :
  forall p t, prime p -> Forall prime t -> product t < p * product t.
Proof.
  intros p t [Hp _] Ht. pose proof (product_prime_ge_1 t Ht). nia.
Qed.

(** ** Divisibility helpers *)

Lemma divide_lt :
  forall p n, 2 <= p -> 2 <= n -> Nat.divide p n -> n / p < n.
Proof.
  intros p n Hp Hn [q Hq]. rewrite Hq, Nat.div_mul; [| lia].
  destruct q; [lia |]. nia.
Qed.

Lemma divide_quotient_ge_2 :
  forall p n, 2 <= p -> p < n -> Nat.divide p n -> 2 <= n / p.
Proof.
  intros p n Hp Hpn [q Hq]. rewrite Hq, Nat.div_mul; [| lia].
  destruct q; [lia |]. destruct q; [nia |]. lia.
Qed.

Lemma divide_mul_cancel :
  forall p n, 2 <= p -> Nat.divide p n -> p * (n / p) = n.
Proof.
  intros p n Hp Hdiv.
  pose proof (Nat.Div0.div_mod n p) as Hdm.
  rewrite (proj2 (Nat.Lcm0.mod_divide n p) Hdiv) in Hdm. lia.
Qed.

(** ** Existence

    Every [n >= 2] has a prime factorization, by strong induction:
    if [n] is prime we are done; otherwise divide out the smallest
    prime factor and recurse on the quotient. *)

Theorem factorization_exists :
  forall n, 2 <= n -> exists l, factorization_of n l.
Proof.
  intros n. induction n as [n IH] using lt_wf_ind. intro Hn.
  destruct (prime_dec n) as [Hprime | Hnotprime].
  - exists [n]. split; [| split].
    + constructor; [exact Hprime | constructor].
    + constructor; constructor.
    + simpl. lia.
  - destruct (smallest_factor_spec n Hn) as [Hsf2 [Hsfn [Hdiv Hmin]]].
    set (sf := smallest_factor n) in *.
    assert (Hprime : prime sf) by (apply smallest_factor_prime; lia).
    assert (Hsf_lt : sf < n).
    { destruct (Nat.eq_dec sf n) as [Heq | ?]; [| lia].
      exfalso. apply Hnotprime. rewrite <- Heq. exact Hprime. }
    destruct (IH (n / sf)) as [l [Hpl [Hs Hprod]]].
    + apply divide_lt; [lia | lia | exact Hdiv].
    + apply divide_quotient_ge_2; assumption.
    + exists (insert sf l). split; [| split].
      * apply (Permutation_Forall (insert_perm sf l)).
        constructor; [exact Hprime | exact Hpl].
      * exact (insert_sorted sf l Hs).
      * rewrite insert_product, Hprod. exact (divide_mul_cancel sf n ltac:(lia) Hdiv).
Qed.

(** ** Uniqueness

    Two prime-lists with the same product are permutations of each other.
    The proof peels one prime at a time: the head of [l1] divides [product l2]
    (by Euclid's lemma it divides some element, which must be equal since both
    are prime), so we remove it from [l2] and recurse on the smaller product. *)

Lemma prime_divides_product :
  forall p l, prime p -> Nat.divide p (product l) ->
    exists x, In x l /\ Nat.divide p x.
Proof.
  intros p l Hp. induction l as [| h t IH]; simpl.
  - intros [q Hq]. destruct Hp as [Hp2 _]. destruct q; simpl in *; lia.
  - intro Hdiv.
    destruct (prime_divides_mul _ _ _ Hp Hdiv) as [Hh | Ht].
    + exists h. auto.
    + destruct (IH Ht) as [x [? ?]]. exists x. auto.
Qed.

Lemma factorization_perm : forall n l1 l2,
  Forall prime l1 -> Forall prime l2 ->
  product l1 = n -> product l2 = n ->
  Permutation l1 l2.
Proof.
  intro n. induction n as [n IH] using lt_wf_ind.
  intros l1 l2 Hpl1 Hpl2 Hp1 Hp2.
  destruct l1 as [| p t1].
  - destruct l2 as [| q t2]; [constructor |].
    exfalso. simpl in Hp1, Hp2. subst n.
    inversion Hpl2; subst.
    exact (Nat.lt_irrefl 1 ltac:(pose proof (product_cons_lt q t2 H1 H2); nia)).
  - assert (Hpp : prime p) by (inversion Hpl1; assumption).
    assert (Hpt1 : Forall prime t1) by (inversion Hpl1; assumption).
    simpl in Hp1.
    assert (Hpdiv : Nat.divide p (product l2))
      by (rewrite Hp2, <- Hp1; exists (product t1); lia).
    destruct (prime_divides_product _ _ Hpp Hpdiv) as [x [Hin Hxd]].
    replace x with p in * by (apply prime_divides_prime; auto;
      rewrite Forall_forall in Hpl2; auto).
    pose proof (remove_one_perm _ _ Hin) as Hperm2.
    assert (Hpt2 : Forall prime (remove_one p l2)).
    { pose proof (Permutation_Forall Hperm2 Hpl2) as H. inversion H; assumption. }
    assert (Hprod_eq : product t1 = product (remove_one p l2)).
    { assert (product l2 = p * product (remove_one p l2))
        by (rewrite (product_perm _ _ Hperm2); reflexivity).
      destruct Hpp as [Hp2' _].
      assert (p <> 0) by lia.
      rewrite Hp2 in H. rewrite <- Hp1 in H.
      exact (proj1 (Nat.mul_cancel_l _ _ _ H0) H). }
    assert (Hlt : product t1 < n)
      by (rewrite <- Hp1; exact (product_cons_lt p t1 Hpp Hpt1)).
    eapply perm_trans; [| exact (Permutation_sym Hperm2)].
    constructor. exact (IH _ Hlt _ _ Hpt1 Hpt2 eq_refl (eq_sym Hprod_eq)).
Qed.

(** ** Main results *)

Theorem factorization_unique : forall n l1 l2,
  factorization_of n l1 -> factorization_of n l2 -> l1 = l2.
Proof.
  intros n l1 l2 [Hpl1 [Hs1 Hp1]] [Hpl2 [Hs2 Hp2]].
  apply ssorted_perm_eq; [assumption | assumption |].
  exact (factorization_perm n l1 l2 Hpl1 Hpl2 Hp1 Hp2).
Qed.

Theorem fundamental_theorem_of_arithmetic :
  forall n, 2 <= n -> exists! l, factorization_of n l.
Proof.
  intros n Hn.
  destruct (factorization_exists n Hn) as [l Hl].
  exists l. split; [exact Hl |].
  intros l' Hl'. exact (factorization_unique n l l' Hl Hl').
Qed.

Print Assumptions fundamental_theorem_of_arithmetic.
