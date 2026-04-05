(** * The Fundamental Theorem of Arithmetic

    Every natural number ≥ 2 admits a prime factorization,
    and that factorization is unique up to ordering. *)

From Rocq Require Import Arith Lia List Permutation Sorting.
Import ListNotations.

(** ** Prime factorizations as sorted lists *)

(** A factorization of [n] is a sorted list of primes whose product is [n]. *)

Definition is_prime (p : nat) : Prop :=
  2 <= p /\ forall d, d >= 1 -> d < p -> ~ (p mod d = 0) \/ d = 1.

(** We use the stdlib's [prime] predicate instead, which is better supported. *)
From Rocq Require Import PeanoNat.

(** [Nat.Prime p] says [p >= 2] and its only divisors are 1 and [p]. *)

Definition prime_list (l : list nat) : Prop :=
  Forall Nat.Prime l.

Definition product (l : list nat) : nat :=
  fold_right Nat.mul 1 l.

Definition factorization_of (n : nat) (l : list nat) : Prop :=
  prime_list l /\ Sorted Nat.le l /\ product l = n.

(** ** Part I: Existence

    Every [n >= 2] has at least one prime factorization.
    We prove this by strong induction on [n]. *)

(** A helper: if [n >= 2], then [n] has a smallest divisor [>= 2],
    and that divisor is prime. *)

Lemma smallest_divisor_aux :
  forall n k,
    2 <= k -> k <= n -> 2 <= n ->
    (forall j, 2 <= j -> j < k -> ~ Nat.divide j n) ->
    exists p, 2 <= p /\ p <= n /\ Nat.divide p n /\ Nat.Prime p.
Proof.
  intros n k. revert n.
  induction k as [k IHk] using lt_wf_ind.
  intros n Hk Hkn Hn Hno.
  destruct (Nat.eq_dec (n mod k) 0) as [Hdiv | Hndiv].
  - (* k divides n *)
    (* Is k prime? If all numbers 2..k-1 don't divide k, it's prime. *)
    destruct (Nat.eq_dec k 2) as [-> | Hk2].
    + exists 2. repeat split; try lia.
      * apply Nat.mod_divide in Hdiv; [exact Hdiv | lia].
      * constructor; [lia |].
        intros [|[|[|m]]] Hm; lia.
    + (* k > 2: check if k is prime by looking for divisors *)
      assert (Hk3 : 2 < k) by lia.
      (* k divides n *)
      assert (Hkdiv : Nat.divide k n).
      { apply Nat.mod_divide; lia. }
      (* Does k have a divisor between 2 and k-1? *)
      destruct (Nat.Prime_dec k) as [Hprime | Hnotprime].
      * exists k. repeat split; try lia; assumption.
      * (* k is composite, so it has a divisor 2 <= d < k *)
        unfold Nat.Prime in Hnotprime.
        assert (Hk2' : 2 <= k) by lia.
        (* k is not prime and k >= 2, so there exists d with 1 < d < k and d | k *)
        destruct (Nat.not_prime_divide k) as [d [Hd1 Hdk]]; [lia | exact Hnotprime |].
        destruct Hd1 as [Hd2 Hdk'].
        (* d divides k and k divides n, so d divides n *)
        assert (Hdn : Nat.divide d n).
        { eapply Nat.divide_trans; eassumption. }
        (* But all j with 2 <= j < k don't divide n — contradiction *)
        exfalso. apply (Hno d); [lia | lia | exact Hdn].
  - (* k does not divide n *)
    destruct (Nat.eq_dec k n) as [-> | Hkn'].
    + (* k = n and n doesn't divide itself — impossible *)
      exfalso. apply Hndiv. apply Nat.mod_same. lia.
    + assert (Hk1 : k + 1 <= n) by lia.
      apply (IHk (k + 1)); try lia.
      intros j Hj1 Hj2.
      destruct (Nat.eq_dec j k) as [-> | Hjk].
      * intro Habs. apply Hndiv.
        apply Nat.mod_divide in Habs; [| lia].
        destruct Habs as [q Hq].
        rewrite Nat.mul_comm in Hq.
        rewrite Hq. apply Nat.mod_mul. lia.
      * apply Hno; lia.
Qed.

Lemma smallest_divisor :
  forall n, 2 <= n ->
    exists p, 2 <= p /\ p <= n /\ Nat.divide p n /\ Nat.Prime p.
Proof.
  intros n Hn.
  apply (smallest_divisor_aux n 2); try lia.
  intros j Hj1 Hj2. lia.
Qed.

(** Dividing out a factor produces a smaller number. *)
Lemma divide_smaller :
  forall p n, 2 <= p -> Nat.divide p n -> 2 <= n -> n / p < n.
Proof.
  intros p n Hp [q Hq] Hn.
  rewrite Hq. rewrite Nat.div_mul; [| lia].
  destruct q; [lia |]. simpl. lia.
Qed.

Lemma divide_quotient_ge_1 :
  forall p n, 2 <= p -> p <= n -> Nat.divide p n -> 1 <= n / p.
Proof.
  intros p n Hp Hpn [q Hq].
  rewrite Hq. rewrite Nat.div_mul; [| lia].
  lia.
Qed.

(** Insert into a sorted list, maintaining sortedness. *)
Fixpoint insert (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => [x]
  | h :: t => if x <=? h then x :: h :: t else h :: insert x t
  end.

Lemma insert_sorted :
  forall x l, Sorted Nat.le l -> Sorted Nat.le (insert x l).
Proof.
  intros x l. induction l as [| h t IH]; simpl; intro Hsorted.
  - constructor; constructor.
  - destruct (x <=? h) eqn:E.
    + apply Nat.leb_le in E.
      constructor; [assumption |].
      constructor. exact E.
    + apply Nat.leb_gt in E.
      inversion Hsorted; subst.
      * simpl. constructor; [constructor |].
        constructor. lia.
      * rename H1 into Hsorted'. rename H2 into Hrel.
        specialize (IH Hsorted').
        simpl in IH.
        destruct (x <=? b) eqn:E2.
        -- constructor; [exact IH |].
           constructor. lia.
        -- constructor; [exact IH |].
           inversion Hrel; subst. constructor. assumption.
Qed.

Lemma insert_perm :
  forall x l, Permutation (x :: l) (insert x l).
Proof.
  intros x l. induction l as [| h t IH]; simpl.
  - reflexivity.
  - destruct (x <=? h) eqn:E.
    + reflexivity.
    + apply perm_trans with (h :: x :: t).
      * apply perm_swap.
      * constructor. exact IH.
Qed.

Lemma insert_product :
  forall x l, product (insert x l) = x * product l.
Proof.
  intros x l. induction l as [| h t IH]; simpl.
  - lia.
  - destruct (x <=? h); simpl; [lia |].
    rewrite IH. lia.
Qed.

(** The main existence theorem, by strong induction. *)
Theorem factorization_exists :
  forall n, 2 <= n -> exists l, factorization_of n l.
Proof.
  intros n. induction n as [n IH] using lt_wf_ind.
  intro Hn.
  destruct (Nat.Prime_dec n) as [Hprime | Hnotprime].
  - (* n is prime: factorization is just [n] *)
    exists [n]. unfold factorization_of, prime_list, product. simpl.
    repeat split.
    + constructor; [exact Hprime | constructor].
    + constructor.
    + lia.
  - (* n is composite: find a prime factor, divide, recurse *)
    destruct (smallest_divisor n Hn) as [p [Hp2 [Hpn [Hdiv Hprime]]]].
    assert (Hq : n / p >= 2).
    { destruct (Nat.eq_dec p n) as [-> | Hne].
      - exfalso. apply Hnotprime. exact Hprime.
      - assert (n / p >= 1) by (apply divide_quotient_ge_1; [lia | lia | exact Hdiv]).
        destruct (Nat.eq_dec (n / p) 1) as [Heq1 | Hneq1].
        + (* n/p = 1 means n = p, contradiction *)
          exfalso. apply Hne.
          destruct Hdiv as [q Hq].
          rewrite Hq in Heq1.
          rewrite Nat.div_mul in Heq1; [| lia].
          lia.
        + lia.
    }
    assert (Hlt : n / p < n) by (apply divide_smaller; [lia | exact Hdiv | lia]).
    destruct (IH (n / p) Hlt Hq) as [l [Hpl [Hsorted Hprod]]].
    exists (insert p l).
    unfold factorization_of. repeat split.
    + (* all primes *)
      unfold prime_list.
      assert (Permutation (p :: l) (insert p l)) by apply insert_perm.
      apply Permutation_Forall with (p :: l); [exact H |].
      constructor; [exact Hprime |]. exact Hpl.
    + (* sorted *)
      apply insert_sorted. exact Hsorted.
    + (* product correct *)
      rewrite insert_product. rewrite Hprod.
      destruct Hdiv as [q Hq].
      rewrite Hq. rewrite Nat.div_mul; [| lia].
      lia.
Qed.

(** ** Part II: Uniqueness

    If two sorted lists of primes have the same product, they are equal.
    The key ingredient is Euclid's lemma: if [p] is prime and [p | a * b],
    then [p | a] or [p | b]. *)

(** Euclid's lemma is available as [Nat.Prime_divide] in the stdlib. *)
Check Nat.Prime_divide.
(* : forall p, Nat.Prime p -> forall n m, Nat.divide p (n * m) ->
     Nat.divide p n \/ Nat.divide p m *)

(** A prime dividing a product of a list must divide some element. *)
Lemma prime_divides_product :
  forall p l, Nat.Prime p -> Nat.divide p (product l) ->
    exists x, In x l /\ Nat.divide p x.
Proof.
  intros p l Hp. induction l as [| h t IH]; simpl.
  - unfold product. simpl. intros [q Hq].
    assert (Hp2 : 2 <= p) by (destruct Hp; lia).
    lia.
  - unfold product. simpl. fold (product t).
    intro Hdiv.
    apply Nat.Prime_divide in Hdiv; [| exact Hp].
    destruct Hdiv as [Hh | Ht].
    + exists h. split; [left; reflexivity | exact Hh].
    + destruct (IH Ht) as [x [Hin Hxdiv]].
      exists x. split; [right; exact Hin | exact Hxdiv].
Qed.

(** A prime dividing another prime must be equal to it. *)
Lemma prime_divides_prime :
  forall p q, Nat.Prime p -> Nat.Prime q -> Nat.divide p q -> p = q.
Proof.
  intros p q Hp Hq [k Hk].
  destruct Hp as [Hp2 Hpirr].
  destruct Hq as [Hq2 Hqirr].
  destruct (Hqirr p) as [Hp1 | Hpq].
  - exists k. lia.
  - lia.
  - exact Hpq.
Qed.

(** Removing one occurrence of [x] from a list. *)
Fixpoint remove_one (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => if Nat.eq_dec x h then t else h :: remove_one x t
  end.

Lemma remove_one_in :
  forall x l, In x l -> Permutation l (x :: remove_one x l).
Proof.
  intros x l. induction l as [| h t IH]; simpl.
  - intros [].
  - intros [-> | Hin].
    + destruct (Nat.eq_dec x x); [reflexivity | contradiction].
    + destruct (Nat.eq_dec x h) as [-> | Hne].
      * reflexivity.
      * specialize (IH Hin).
        apply perm_trans with (h :: x :: remove_one x t).
        -- constructor. exact IH.
        -- apply perm_swap.
Qed.

Lemma product_perm :
  forall l1 l2, Permutation l1 l2 -> product l1 = product l2.
Proof.
  intros l1 l2 H. induction H; simpl; unfold product in *; simpl in *; try lia.
  fold (product l) in *. fold (product l') in *. lia.
Qed.

Lemma prime_list_perm :
  forall l1 l2, Permutation l1 l2 -> prime_list l1 -> prime_list l2.
Proof.
  intros l1 l2 Hperm Hpl.
  unfold prime_list in *.
  eapply Permutation_Forall; eassumption.
Qed.

(** If two sorted lists of primes are permutations, they are equal. *)
Lemma sorted_perm_eq :
  forall l1 l2, Sorted Nat.le l1 -> Sorted Nat.le l2 ->
    Permutation l1 l2 -> l1 = l2.
Proof.
  intros l1 l2 Hs1 Hs2 Hperm.
  apply (Sorted_Sorted_eq Nat.eq Nat.le); try assumption.
  - apply Nat.eq_equiv.
  - exact Nat.le_antisymm.
Qed.

(** Product of a list of primes is >= 1. *)
Lemma product_ge_1 :
  forall l, prime_list l -> product l >= 1.
Proof.
  intros l Hpl. induction l as [| h t IH]; simpl.
  - unfold product. simpl. lia.
  - unfold product. simpl. fold (product t).
    inversion Hpl; subst.
    specialize (IH H2).
    assert (h >= 2) by (destruct H1; lia).
    nia.
Qed.

(** Now the uniqueness proof: two factorizations of the same number
    are permutations of each other. We prove this by induction on the product. *)
Lemma factorization_unique_perm :
  forall n l1 l2,
    prime_list l1 -> prime_list l2 ->
    product l1 = n -> product l2 = n ->
    Permutation l1 l2.
Proof.
  intro n. induction n as [n IH] using lt_wf_ind.
  intros l1 l2 Hpl1 Hpl2 Hprod1 Hprod2.
  destruct l1 as [| p1 t1].
  - (* l1 is empty, so product = 1 *)
    simpl in Hprod1. unfold product in Hprod1. simpl in Hprod1. subst.
    destruct l2 as [| p2 t2].
    + constructor.
    + (* product of l2 = 1, but l2 has a prime, contradiction *)
      exfalso. unfold product in Hprod2. simpl in Hprod2.
      fold (product t2) in Hprod2.
      inversion Hpl2; subst.
      assert (p2 >= 2) by (destruct H1; lia).
      assert (product t2 >= 1) by (apply product_ge_1; exact H2).
      lia.
  - (* l1 = p1 :: t1 *)
    unfold product in Hprod1. simpl in Hprod1. fold (product t1) in Hprod1.
    (* p1 divides n = product l2 *)
    assert (Hp1 : Nat.Prime p1) by (inversion Hpl1; assumption).
    assert (Hp1_div : Nat.divide p1 (product l2)).
    { rewrite Hprod2. rewrite <- Hprod1. exists (product t1). lia. }
    destruct (prime_divides_product p1 l2 Hp1 Hp1_div) as [x [Hin Hxdiv]].
    assert (Hx_prime : Nat.Prime x).
    { unfold prime_list in Hpl2. rewrite Forall_forall in Hpl2. auto. }
    assert (Hxp1 : x = p1) by (symmetry; apply prime_divides_prime; assumption).
    subst x.
    (* Remove p1 from l2 *)
    assert (Hperm2 : Permutation l2 (p1 :: remove_one p1 l2)).
    { apply remove_one_in. exact Hin. }
    assert (Hpl2' : prime_list (remove_one p1 l2)).
    { apply prime_list_perm with (p1 :: remove_one p1 l2).
      - symmetry. exact Hperm2.
      - apply prime_list_perm with l2; [exact Hperm2 | exact Hpl2]. }
    (* Ahh wait, need to reverse the logic *)
    assert (Hpl2'' : prime_list (remove_one p1 l2)).
    { clear Hpl2'.
      assert (Hpl2_perm : prime_list (p1 :: remove_one p1 l2)).
      { eapply prime_list_perm; [exact Hperm2 | exact Hpl2]. }
      inversion Hpl2_perm; assumption. }
    (* Products match after removing p1 *)
    assert (Hprod_rem : product (remove_one p1 l2) = product t1).
    { assert (Heq : product l2 = p1 * product (remove_one p1 l2)).
      { rewrite (product_perm _ _ Hperm2). simpl. unfold product. simpl.
        fold (product (remove_one p1 l2)). reflexivity. }
      rewrite <- Hprod1 in Hprod2. rewrite Heq in Hprod2.
      assert (p1 >= 2) by (destruct Hp1; lia).
      nia.
    }
    assert (Hpl1' : prime_list t1) by (inversion Hpl1; assumption).
    assert (Hlt : product t1 < n).
    { rewrite <- Hprod1.
      assert (p1 >= 2) by (destruct Hp1; lia).
      assert (product t1 >= 1) by (apply product_ge_1; exact Hpl1').
      nia.
    }
    assert (IHperm : Permutation t1 (remove_one p1 l2)).
    { apply (IH (product t1) Hlt t1 (remove_one p1 l2));
        [exact Hpl1' | exact Hpl2'' | reflexivity | symmetry; exact Hprod_rem].
    }
    apply perm_trans with (p1 :: remove_one p1 l2).
    + constructor. exact IHperm.
    + symmetry. exact Hperm2.
Qed.

(** The main uniqueness theorem: sorted factorizations are equal. *)
Theorem factorization_unique :
  forall n l1 l2,
    factorization_of n l1 -> factorization_of n l2 -> l1 = l2.
Proof.
  intros n l1 l2 [Hpl1 [Hs1 Hp1]] [Hpl2 [Hs2 Hp2]].
  apply sorted_perm_eq; try assumption.
  apply (factorization_unique_perm n); try assumption; lia.
Qed.

(** ** The Fundamental Theorem of Arithmetic *)

Theorem fundamental_theorem_of_arithmetic :
  forall n, 2 <= n ->
    exists! l, factorization_of n l.
Proof.
  intros n Hn.
  destruct (factorization_exists n Hn) as [l Hl].
  exists l. split; [exact Hl |].
  intros l' Hl'.
  symmetry. apply (factorization_unique n); assumption.
Qed.

Print Assumptions fundamental_theorem_of_arithmetic.
