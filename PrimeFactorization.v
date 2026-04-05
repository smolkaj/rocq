(** * The Fundamental Theorem of Arithmetic

    Every natural number ≥ 2 has a unique prime factorization.

    We represent factorizations as sorted lists of primes whose product
    equals [n].  Existence follows by strong induction (find the smallest
    prime factor, divide it out, recurse).  Uniqueness follows from
    Euclid's lemma — derived here from Bézout via [Nat.gauss] — which
    lets us peel matching primes off two factorizations one at a time. *)

From Stdlib Require Import Arith Lia List PeanoNat Sorting Permutation.
Import ListNotations.

(* ========================================================================= *)
(** ** Primes *)
(* ========================================================================= *)

Definition prime (p : nat) : Prop :=
  2 <= p /\ forall d, Nat.divide d p -> d = 1 \/ d = p.

(** Trial division from [k] up to [n], with structural recursion on [fuel].
    When fuel runs out we return [n] itself (which always self-divides). *)
Fixpoint sdf (n k fuel : nat) : nat :=
  match fuel with
  | 0 => n
  | S f => if Nat.eq_dec (n mod k) 0 then k else sdf n (S k) f
  end.

Definition smallest_factor (n : nat) := sdf n 2 (n - 2).

Lemma sdf_spec : forall fuel n k,
  2 <= k -> k <= n -> 2 <= n -> n <= k + fuel ->
  let d := sdf n k fuel in
  k <= d /\ d <= n /\ n mod d = 0 /\
  forall j, k <= j -> j < d -> n mod j <> 0.
Proof.
  induction fuel as [| f IH]; intros n k Hk Hkn Hn Hb; simpl.
  - repeat split; [lia | lia | apply Nat.Div0.mod_same | intros; lia].
  - destruct (Nat.eq_dec (n mod k) 0) as [e | ne].
    + repeat split; [lia | lia | exact e | intros; lia].
    + destruct (Nat.eq_dec k n) as [-> | Hkn'].
      * exfalso. exact (ne (Nat.Div0.mod_same n)).
      * destruct (IH n (S k) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          as [H1 [H2 [H3 H4]]].
        repeat split; [lia | lia | exact H3 |].
        intros j Hj1 Hj2.
        destruct (Nat.eq_dec j k) as [-> | Hjk]; [exact ne | apply H4; lia].
Qed.

Lemma smallest_factor_spec : forall n, 2 <= n ->
  2 <= smallest_factor n /\ smallest_factor n <= n /\
  Nat.divide (smallest_factor n) n /\
  forall j, 2 <= j -> j < smallest_factor n -> ~ Nat.divide j n.
Proof.
  intros n Hn. unfold smallest_factor.
  destruct (sdf_spec (n-2) n 2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as [H1 [H2 [H3 H4]]].
  repeat split; [lia | lia | |].
  - apply Nat.Lcm0.mod_divide. exact H3.
  - intros j Hj1 Hj2 [q Hq].
    exact (H4 j ltac:(lia) Hj2 ltac:(rewrite Hq; apply Nat.Div0.mod_mul)).
Qed.

Lemma smallest_factor_prime : forall n, 2 <= n -> prime (smallest_factor n).
Proof.
  intros n Hn.
  destruct (smallest_factor_spec n Hn) as [Hsf2 [Hsfn [Hdiv Hmin]]].
  split; [lia |].
  intros d Hd_div.
  destruct (Nat.eq_dec d 0) as [-> | Hd0].
  { destruct Hd_div as [q Hq]. lia. }
  destruct (Nat.eq_dec d 1) as [-> | Hd1]; [now left |].
  right.
  assert (Hd2 : 2 <= d) by (destruct d; [lia |]; destruct d; lia).
  assert (Hdn : Nat.divide d n) by (eapply Nat.divide_trans; eassumption).
  destruct (lt_dec d (smallest_factor n)) as [Hlt | Hge].
  - exfalso. exact (Hmin d Hd2 Hlt Hdn).
  - destruct Hd_div as [q Hq]. destruct q; lia.
Qed.

Lemma prime_dec : forall n, {prime n} + {~ prime n}.
Proof.
  intro n.
  destruct (le_dec 2 n) as [Hn | Hn].
  2: { right; intros [H _]; lia. }
  destruct (Nat.eq_dec (smallest_factor n) n) as [Heq | Hne].
  - left. rewrite <- Heq. apply smallest_factor_prime. lia.
  - right. intro Hp.
    destruct (smallest_factor_spec n Hn) as [Hsf2 [_ [Hdiv _]]].
    destruct Hp as [_ Hirr]. destruct (Hirr _ Hdiv); lia.
Qed.

(** Euclid's lemma, derived from Bézout's identity via [Nat.gauss]:
    if [p] is prime and [gcd(p, a) = 1] then [p | ab] implies [p | b]. *)
Lemma prime_divides_mul :
  forall p a b, prime p -> Nat.divide p (a * b) ->
    Nat.divide p a \/ Nat.divide p b.
Proof.
  intros p a b [_ Hirr] Hdiv.
  destruct (Hirr (Nat.gcd p a) (Nat.gcd_divide_l p a)) as [Hco | Hgp].
  - right. exact (Nat.gauss p a b Hdiv Hco).
  - left. rewrite <- Hgp. apply Nat.gcd_divide_r.
Qed.

Lemma prime_divides_prime :
  forall p q, prime p -> prime q -> Nat.divide p q -> p = q.
Proof.
  intros p q [Hp _] [_ Hirr] Hdiv. destruct (Hirr p Hdiv); lia.
Qed.

(* ========================================================================= *)
(** ** Factorizations *)
(* ========================================================================= *)

Fixpoint product (l : list nat) : nat :=
  match l with
  | [] => 1
  | h :: t => h * product t
  end.

Definition factorization_of (n : nat) (l : list nat) : Prop :=
  Forall prime l /\ StronglySorted Nat.le l /\ product l = n.

(** *** Sorted insertion *)

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

Lemma insert_product : forall x l, product (insert x l) = x * product l.
Proof.
  intros x l. induction l as [| h t IH]; simpl; [lia |].
  destruct (x <=? h); simpl; [lia | rewrite IH; lia].
Qed.

Lemma Forall_le_insert : forall x y l,
  y <= x -> Forall (Nat.le y) l -> Forall (Nat.le y) (insert x l).
Proof.
  intros x y l Hyx Hl. induction l as [| h t IH]; simpl.
  - constructor; [lia | constructor].
  - destruct (x <=? h); constructor; inversion Hl; auto.
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

(** *** Product lemmas *)

Lemma product_perm :
  forall l1 l2, Permutation l1 l2 -> product l1 = product l2.
Proof.
  intros l1 l2 H. induction H; simpl; lia.
Qed.

Lemma product_prime_ge_1 :
  forall l, Forall prime l -> 1 <= product l.
Proof.
  induction l as [| h t IH]; simpl; [lia |].
  intros Hpl. inversion Hpl; subst.
  destruct H1 as [Hh _]. specialize (IH H2). nia.
Qed.

(** Consing a prime strictly increases the product. *)
Lemma product_cons_lt :
  forall p t, prime p -> Forall prime t -> product t < p * product t.
Proof.
  intros p t [Hp _] Ht. pose proof (product_prime_ge_1 t Ht). nia.
Qed.

(** *** Divisibility helpers *)

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

(* ========================================================================= *)
(** ** Existence *)
(* ========================================================================= *)

(** Every [n >= 2] has a prime factorization, by strong induction:
    if [n] is prime we are done; otherwise divide out the smallest
    prime factor and recurse on the quotient. *)

Theorem factorization_exists :
  forall n, 2 <= n -> exists l, factorization_of n l.
Proof.
  intros n. induction n as [n IH] using lt_wf_ind. intro Hn.
  destruct (prime_dec n) as [Hprime | Hnotprime].
  - (* n is prime *)
    exists [n]. split; [| split].
    + constructor; [exact Hprime | constructor].
    + constructor; constructor.
    + simpl. lia.
  - (* n is composite: divide out the smallest factor *)
    destruct (smallest_factor_spec n Hn) as [Hsf2 [Hsfn [Hdiv Hmin]]].
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

(* ========================================================================= *)
(** ** Uniqueness *)
(* ========================================================================= *)

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

(** Two prime-lists with the same product are permutations of each other.
    The proof peels one prime at a time: the head of [l1] divides [product l2]
    (by Euclid's lemma it divides some element, which must be equal since both
    are prime), so we remove it from [l2] and recurse on the smaller product. *)

Lemma factorization_perm : forall n l1 l2,
  Forall prime l1 -> Forall prime l2 ->
  product l1 = n -> product l2 = n ->
  Permutation l1 l2.
Proof.
  intro n. induction n as [n IH] using lt_wf_ind.
  intros l1 l2 Hpl1 Hpl2 Hp1 Hp2.
  destruct l1 as [| p t1].
  - (* l1 = [] means product = 1; l2 must also be empty *)
    destruct l2 as [| q t2]; [constructor |].
    exfalso. simpl in Hp1, Hp2. subst n.
    inversion Hpl2; subst. exact (Nat.lt_irrefl 1 ltac:(pose proof (product_cons_lt q t2 H1 H2); nia)).
  - (* l1 = p :: t1 *)
    assert (Hpp : prime p) by (inversion Hpl1; assumption).
    assert (Hpt1 : Forall prime t1) by (inversion Hpl1; assumption).
    simpl in Hp1.
    (* p divides product l2 *)
    assert (Hpdiv : Nat.divide p (product l2))
      by (rewrite Hp2, <- Hp1; exists (product t1); lia).
    destruct (prime_divides_product _ _ Hpp Hpdiv) as [x [Hin Hxd]].
    replace x with p in * by (apply prime_divides_prime; auto;
      rewrite Forall_forall in Hpl2; auto).
    (* Peel p from both sides and recurse *)
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

(** Two strongly sorted permutations of the same list are equal. *)
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

(* ========================================================================= *)
(** ** Main results *)
(* ========================================================================= *)

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
