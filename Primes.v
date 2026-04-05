(** * Prime numbers over [nat]

    Defines primality, a computable smallest-factor function via trial
    division, decidability of primality, and Euclid's lemma (derived
    from Bézout's identity via [Nat.gauss]). *)

From Stdlib Require Import Arith Lia PeanoNat.

Definition prime (p : nat) : Prop :=
  2 <= p /\ forall d, Nat.divide d p -> d = 1 \/ d = p.

(** ** Smallest factor *)

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

(** ** Decidability *)

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

(** ** Euclid's lemma

    Derived from Bézout's identity via [Nat.gauss]: if [p] is prime
    and [gcd(p, a) = 1] then [p | ab] implies [p | b]. *)

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
