(** * The Fundamental Theorem of Arithmetic

    Every natural number ≥ 2 admits a prime factorization,
    and that factorization is unique up to ordering. *)

From Stdlib Require Import Arith Lia List PeanoNat Sorting Permutation.
Import ListNotations.

(** ** Definitions *)

Definition prime (p : nat) : Prop :=
  2 <= p /\ forall d, Nat.divide d p -> d = 1 \/ d = p.

Fixpoint product (l : list nat) : nat :=
  match l with
  | [] => 1
  | h :: t => h * product t
  end.

Definition factorization_of (n : nat) (l : list nat) : Prop :=
  Forall prime l /\ StronglySorted Nat.le l /\ product l = n.

(** ** Smallest factor and primality *)

(** Trial division from [k] up to [n], with [fuel] bounding the search. *)
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
  (forall j, k <= j -> j < d -> n mod j <> 0).
Proof.
  induction fuel as [| f IH]; intros n k Hk Hkn Hn Hb; simpl.
  - repeat split; [lia | lia | apply Nat.Div0.mod_same | intros; lia].
  - destruct (Nat.eq_dec (n mod k) 0) as [e | ne].
    + repeat split; [lia | lia | exact e | intros; lia].
    + destruct (Nat.eq_dec k n) as [-> | Hkn'].
      * exfalso. apply ne. apply Nat.Div0.mod_same.
      * destruct (IH n (S k) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          as [H1 [H2 [H3 H4]]].
        repeat split; [lia | lia | exact H3 |].
        intros j Hj1 Hj2.
        destruct (Nat.eq_dec j k) as [-> | Hjk].
        -- exact ne.
        -- apply H4; lia.
Qed.

Lemma smallest_factor_spec : forall n, 2 <= n ->
  2 <= smallest_factor n /\ smallest_factor n <= n /\
  Nat.divide (smallest_factor n) n /\
  (forall j, 2 <= j -> j < smallest_factor n -> ~ Nat.divide j n).
Proof.
  intros n Hn. unfold smallest_factor.
  destruct (sdf_spec (n-2) n 2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as [H1 [H2 [H3 H4]]].
  repeat split; [lia | lia | |].
  - apply Nat.Lcm0.mod_divide. exact H3.
  - intros j Hj1 Hj2 Hdiv.
    assert (Hmod : n mod j = 0).
    { destruct Hdiv as [q Hq]. rewrite Hq. apply Nat.Div0.mod_mul. }
    exact (H4 j ltac:(lia) Hj2 Hmod).
Qed.

Lemma smallest_factor_prime : forall n, 2 <= n -> prime (smallest_factor n).
Proof.
  intros n Hn.
  destruct (smallest_factor_spec n Hn) as [Hsf2 [Hsfn [Hdiv Hmin]]].
  split; [lia |].
  intros d Hd_div.
  destruct (Nat.eq_dec d 0) as [-> | Hd0].
  { destruct Hd_div as [q Hq]. lia. }
  destruct (Nat.eq_dec d 1) as [-> | Hd1]; [left; reflexivity |].
  right.
  assert (Hd2 : 2 <= d).
  { destruct d; [lia |]. destruct d; [lia |]. lia. }
  assert (Hdn : Nat.divide d n) by (eapply Nat.divide_trans; eassumption).
  destruct (lt_dec d (smallest_factor n)) as [Hlt | Hge].
  - exfalso. exact (Hmin d Hd2 Hlt Hdn).
  - destruct Hd_div as [q Hq].
    assert (d <= smallest_factor n) by (destruct q; lia).
    lia.
Qed.

Lemma prime_dec : forall n, {prime n} + {~ prime n}.
Proof.
  intro n.
  destruct (le_dec 2 n) as [Hn | Hn].
  2: { right; intros [H _]; lia. }
  destruct (Nat.eq_dec (smallest_factor n) n) as [Heq | Hne].
  - left. rewrite <- Heq. apply smallest_factor_prime. lia.
  - right. intro Hp.
    destruct (smallest_factor_spec n Hn) as [Hsf2 [Hsfn [Hdiv _]]].
    destruct Hp as [_ Hirr]. destruct (Hirr _ Hdiv); lia.
Qed.

(** ** Euclid's lemma via GCD *)

Lemma prime_divides_mul :
  forall p a b, prime p -> Nat.divide p (a * b) ->
    Nat.divide p a \/ Nat.divide p b.
Proof.
  intros p a b [Hp2 Hirr] Hdiv.
  destruct (Hirr (Nat.gcd p a)) as [Hg1 | Hgp].
  - apply Nat.gcd_divide_l.
  - right. apply Nat.gauss with a; [exact Hdiv | exact Hg1].
  - left. rewrite <- Hgp. apply Nat.gcd_divide_r.
Qed.

(** ** Sorted insertion *)

Fixpoint insert (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => [x]
  | h :: t => if x <=? h then x :: h :: t else h :: insert x t
  end.

Lemma Forall_insert : forall x y l,
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
  - destruct (x <=? h) eqn:E.
    + apply Nat.leb_le in E.
      constructor; [exact Hs |].
      constructor; [exact E |].
      eapply Forall_impl; [| exact (proj2 (StronglySorted_inv Hs))]. lia.
    + apply Nat.leb_gt in E.
      destruct (StronglySorted_inv Hs) as [Ht Hrel].
      constructor; [exact (IH Ht) |].
      apply Forall_insert; [lia | exact Hrel].
Qed.

Lemma insert_perm :
  forall x l, Permutation (x :: l) (insert x l).
Proof.
  intros x l. induction l as [| h t IH]; simpl.
  - reflexivity.
  - destruct (x <=? h); [reflexivity |].
    eapply perm_trans; [apply perm_swap | constructor; exact IH].
Qed.

Lemma insert_product :
  forall x l, product (insert x l) = x * product l.
Proof.
  intros x l. induction l as [| h t IH]; simpl.
  - lia.
  - destruct (x <=? h); simpl; [lia | rewrite IH; lia].
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
  assert (Hmod : n mod p = 0)
    by (apply Nat.Lcm0.mod_divide; exact Hdiv).
  pose proof (Nat.Div0.div_mod n p) as Hdm.
  rewrite Hmod in Hdm. lia.
Qed.

(** ** Product of primes *)

Lemma product_perm :
  forall l1 l2, Permutation l1 l2 -> product l1 = product l2.
Proof.
  intros l1 l2 H. induction H; simpl; lia.
Qed.

Lemma product_ge_1 :
  forall l, Forall prime l -> 1 <= product l.
Proof.
  induction l as [| h t IH]; simpl; [lia |].
  intro Hpl. inversion Hpl; subst.
  destruct H1 as [Hh _]. specialize (IH H2). nia.
Qed.

(** If [p] is prime and [p :: t] is a list of primes, then
    [p * product t > product t]. *)
Lemma product_cons_lt :
  forall p t, prime p -> Forall prime t -> product t < p * product t.
Proof.
  intros p t [Hp _] Ht. pose proof (product_ge_1 t Ht). nia.
Qed.

(** ** Part I: Existence *)

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
    assert (Hprime : prime (smallest_factor n)) by (apply smallest_factor_prime; lia).
    assert (Hsfn' : smallest_factor n < n).
    { destruct (Nat.eq_dec (smallest_factor n) n); [| lia].
      exfalso. apply Hnotprime. rewrite <- e. exact Hprime. }
    assert (Hq2 : 2 <= n / smallest_factor n)
      by (apply divide_quotient_ge_2; assumption).
    assert (Hlt : n / smallest_factor n < n)
      by (apply divide_lt; [lia | lia | assumption]).
    destruct (IH _ Hlt Hq2) as [l [Hpl [Hs Hprod]]].
    exists (insert (smallest_factor n) l). split; [| split].
    + apply (Permutation_Forall (insert_perm _ l)).
      constructor; [exact Hprime | exact Hpl].
    + apply insert_sorted. exact Hs.
    + rewrite insert_product, Hprod. apply divide_mul_cancel; [lia | exact Hdiv].
Qed.

(** ** Part II: Uniqueness *)

Lemma prime_divides_product :
  forall p l, prime p -> Nat.divide p (product l) ->
    exists x, In x l /\ Nat.divide p x.
Proof.
  intros p l Hp. induction l as [| h t IH]; simpl.
  - intros [q Hq]. destruct Hp as [Hp2 _].
    destruct q; simpl in *; lia.
  - intro Hdiv.
    destruct (prime_divides_mul _ _ _ Hp Hdiv) as [Hh | Ht].
    + exists h. auto.
    + destruct (IH Ht) as [x [Hin Hxd]]. exists x. auto.
Qed.

Lemma prime_divides_prime :
  forall p q, prime p -> prime q -> Nat.divide p q -> p = q.
Proof.
  intros p q [Hp2 _] [_ Hirr] Hdiv.
  destruct (Hirr p Hdiv); lia.
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

(** Two prime lists with the same product are permutations of each other. *)
Lemma factorization_perm :
  forall n l1 l2,
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
    pose proof (product_cons_lt q t2 H1 H2). nia.
  - assert (Hpp : prime p) by (inversion Hpl1; assumption).
    assert (Hpt1 : Forall prime t1) by (inversion Hpl1; assumption).
    simpl in Hp1.
    (* p | product l2 because p * product t1 = product l2 *)
    assert (Hpdiv : Nat.divide p (product l2)).
    { rewrite Hp2, <- Hp1. exists (product t1). lia. }
    destruct (prime_divides_product _ _ Hpp Hpdiv) as [x [Hin Hxd]].
    assert (Hpx : p = x).
    { apply prime_divides_prime; [assumption | | assumption].
      rewrite Forall_forall in Hpl2. auto. }
    subst x.
    pose proof (remove_one_perm _ _ Hin) as Hperm2.
    assert (Hpt2 : Forall prime (remove_one p l2)).
    { assert (H : Forall prime (p :: remove_one p l2))
        by (eapply Permutation_Forall; eassumption).
      inversion H; assumption. }
    assert (Hprod_eq : product t1 = product (remove_one p l2)).
    { assert (product l2 = p * product (remove_one p l2))
        by (rewrite (product_perm _ _ Hperm2); reflexivity).
      destruct Hpp as [Hp2' _]. nia. }
    assert (Hlt : product t1 < n).
    { rewrite <- Hp1. exact (product_cons_lt p t1 Hpp Hpt1). }
    eapply perm_trans; [| apply Permutation_sym; exact Hperm2].
    constructor. apply (IH _ Hlt); [exact Hpt1 | exact Hpt2 | reflexivity | symmetry; exact Hprod_eq].
Qed.

(** Strongly sorted permutations are equal. *)
Lemma ssorted_perm_eq :
  forall l1 l2, StronglySorted Nat.le l1 -> StronglySorted Nat.le l2 ->
    Permutation l1 l2 -> l1 = l2.
Proof.
  intros l1. induction l1 as [| a l1 IH]; intros l2 Hs1 Hs2 Hp.
  - symmetry. apply Permutation_nil. assumption.
  - destruct l2 as [| b l2]; [apply Permutation_sym, Permutation_nil in Hp; discriminate |].
    assert (a = b).
    { assert (Hin_b : In b (a :: l1))
        by (apply (Permutation_in _ (Permutation_sym Hp)); left; reflexivity).
      assert (Hin_a : In a (b :: l2))
        by (apply (Permutation_in _ Hp); left; reflexivity).
      destruct Hin_b as [-> | Hin_b]; [reflexivity |].
      destruct Hin_a as [-> | Hin_a]; [reflexivity |].
      destruct (StronglySorted_inv Hs1) as [_ Ha].
      destruct (StronglySorted_inv Hs2) as [_ Hb].
      rewrite Forall_forall in Ha, Hb.
      specialize (Ha b Hin_b). specialize (Hb a Hin_a). lia. }
    subst b. f_equal. apply IH.
    + exact (proj1 (StronglySorted_inv Hs1)).
    + exact (proj1 (StronglySorted_inv Hs2)).
    + exact (Permutation_cons_inv Hp).
Qed.

(** ** The Fundamental Theorem of Arithmetic *)

Theorem factorization_unique :
  forall n l1 l2,
    factorization_of n l1 -> factorization_of n l2 -> l1 = l2.
Proof.
  intros n l1 l2 [Hpl1 [Hs1 Hp1]] [Hpl2 [Hs2 Hp2]].
  apply ssorted_perm_eq; [assumption | assumption |].
  apply (factorization_perm n); congruence.
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
