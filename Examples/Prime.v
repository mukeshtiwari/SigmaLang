From Stdlib Require Import ZArith 
Znumtheory Psatz Utf8.


(** * Prime: primality testing by computation

    This file gives a primality test that is a program rather than a
    proof.  You hand it a number, it runs, and it answers true or
    false.  [is_prime_sqrt_correct] then says that a true answer can
    be trusted: the number really is prime.

    ** Why a test that runs is needed

    The concrete group used by the end-to-end example in
    Examples/ThresholdIns.v is built from two numbers that must be
    prime.  Nearly every algebraic fact about that group depends on
    those two primality facts, so they have to be available as real
    proofs of [Znumtheory.prime], not as assumptions.

    Writing such a proof by hand for a four digit number is tedious
    and teaches nothing.  Instead we write a boolean test once, prove
    once and for all that the test never lies, and then discharge
    each primality side condition by letting Rocq evaluate the test
    on the number at hand.  This style is called proof by reflection:
    a proof obligation is reflected into a computation, and the
    kernel carries the computation out.

    ** The test

    A number is prime exactly when it is greater than one and has no
    divisor strictly between one and itself.  A composite number
    always has such a divisor no larger than its own square root, so
    it is enough to examine the candidates from one up to the square
    root.  Rather than testing divisibility directly, the test asks
    that each candidate [k] be coprime to the number, that is, that
    [Z.gcd] of the two be one.  That is the same condition, and it is
    convenient because the standard library already knows a lot about
    [Z.gcd]. *)

(** Run a boolean test on every integer from [n] down to one.

    [iterate_fn f n] evaluates [f] at [Z.of_nat n], then at the
    predecessor, and so on, and returns true only when every one of
    those calls returned true.  The empty range, [n] equal to zero,
    gives true, because a conjunction over nothing is true.

    The value zero itself is never tested: the recursion stops at the
    base case without calling [f].  That is deliberate, since the
    candidate divisors we care about start at one. *)
Fixpoint iterate_fn (f : Z -> bool) (n : nat) : bool :=
  match n with
  | O => true 
  | S m => f (Z.of_nat n) && iterate_fn f m
  end.

(** What a successful run of [iterate_fn] tells you.

    The hypothesis is that [iterate_fn f n] returned true, that is,
    the test [f] succeeded everywhere on the range.  The conclusion
    is that [f k] is true for each individual integer [k] with
    [1 <= k <= Z.of_nat n].

    This is the step that turns a single boolean answer about a whole
    range into a fact about an arbitrary member of that range, which
    is what the correctness theorem below needs.

    Why it is true: induct on [n].  For zero the range is empty and
    there is nothing to prove.  For a successor the boolean
    conjunction splits into the test at the top point and a
    successful run on the shorter range, and the given [k] is either
    the top point itself, handled by the first half, or lies in the
    shorter range, handled by the induction hypothesis. *)
Lemma iterate_fn_spec_prime :
  ∀ (n : nat) (f : Z → bool), iterate_fn f n = true ->
  ∀ (k : Z), 1 <= k <= Z.of_nat n -> f k = true.
Proof.
  induction n as [|n ihn]. 
  +
    intros * ha * hb.
    nia.
  +
    intros * ha * hb.
    cbn in ha.
    eapply Bool.andb_true_iff in ha as [hal har].
    assert (hc : k = Z.of_nat (S n) ∨ 1 <= k <= Z.of_nat n) by nia.
    destruct hc as [hc | hc].
    ++
      subst. exact hal.
    ++
      eapply ihn; try assumption.
Qed.

(** The primality test itself.

    [is_prime_sqrt p] returns true when both of the following hold:

    - [p] is strictly greater than one, and
    - every candidate [k] with [1 <= k <= Z.sqrt p] is coprime to
      [p], meaning that [Z.gcd k p] is one.

    The second part is exactly one run of [iterate_fn] over the range
    up to [Z.to_nat (Z.sqrt p)].

    The test is used in one direction only.  A true answer is a
    guarantee of primality, and that guarantee is
    [is_prime_sqrt_correct] below.  Nothing is claimed here about a
    false answer, because the examples never need it. *)
Definition is_prime_sqrt (p : Z) : bool :=
  (1 <? p) && iterate_fn (fun k => Z.gcd k p =? 1)
  (Z.to_nat (Z.sqrt p)).


(** Every composite number has a small divisor.

    If [n] is greater than one and is not prime, then it has a
    divisor [d] with [1 < d <= Z.sqrt n].  This is the classical
    reason why trial division is allowed to stop at the square root,
    and it is what connects the bounded search performed by
    [is_prime_sqrt] to the unbounded statement [prime n].

    Why it is true: failing to be prime gives some divisor of [n]
    strictly between one and [n].  Call it [p] and write [n] as [p]
    times [v].  If [p] is already at most the square root of [n],
    it is the divisor we want.  Otherwise [p] is above the square
    root, and then its partner [v] must be at or below the square
    root, since two factors both above the square root would multiply
    to something larger than [n].  The partner is also greater than
    one, because [p] is smaller than [n].  So in that case the
    partner is the divisor we want. *)
Lemma composite_has_divisor_sqrt :
  ∀ n, 1 < n -> ~prime n -> 
  exists d, 1 < d <= Z.sqrt n /\ (d | n).
Proof.
  intros n Hn Hnp.
  destruct (not_prime_divide n Hn Hnp) as (p & hp & (v & hv)).
  destruct (Z.le_gt_cases p (Z.sqrt n)) as [ha | ha]. 
  +
    exists p; split; auto. split; [|assumption]. nia.
    eexists. exact hv.
  +
    exists (n/p); split.
    ++
      split.
      *
        rewrite hv in hp.
        assert (hb : n/p = v).
        rewrite hv. 
        rewrite Z.div_mul.
        reflexivity. nia.
        rewrite hb. nia.
      *
        subst n.
        rewrite Z.div_mul;[|try nia].   
        remember (Z.sqrt (v * p)) as s.
        assert (hb : s * s <= v * p < Z.succ s * Z.succ s).
        {
          split. 
          +
            pose proof Z.sqrt_mul_below (v * p) (v * p) as hb.
            rewrite <-Heqs in hb. rewrite Z.sqrt_square in hb;[|try nia].
            exact hb.
          +

  
            assert (hb : v * p = Z.sqrt (v * p * (v * p))).
            rewrite Z.sqrt_square. reflexivity. nia.
            rewrite hb.
            pose proof Z.sqrt_mul_above (v * p) (v * p) (ltac:(nia))
            (ltac:(nia)) as hc. rewrite Heqs.
            exact hc.
        }
        assert (hc : Z.succ s <= p) by nia.
        assert(hd : v * p <= Z.succ s * p). nia.
        nia.
    ++ 
      exists p. 
      rewrite !hv. rewrite Z.div_mul. 
      nia. nia.
Qed.

(** Correctness of the test: a true answer means prime.

    This is the only result of the file that other developments use.
    Given that [is_prime_sqrt n] evaluates to true, the number [n]
    really satisfies the standard library predicate [prime].  A
    primality side condition can therefore be discharged by applying
    this theorem and then asking Rocq to evaluate the test, which is
    exactly how Examples/ThresholdIns.v justifies its two primes.

    Why it is true: the two halves of the boolean answer say that [n]
    is greater than one and, through [iterate_fn_spec_prime], that
    every [k] in the range [1 <= k <= Z.sqrt n] is coprime to [n].
    Suppose [n] were not prime.  Then [composite_has_divisor_sqrt]
    produces a divisor [d] lying inside exactly that range.  A
    divisor of [n] has greatest common divisor with [n] equal to
    itself, so coprimality forces [d] to be one, contradicting
    [1 < d].  Hence [n] is prime. *)
Theorem is_prime_sqrt_correct :
  ∀ (n : Z), is_prime_sqrt n = true -> prime n.
Proof.
  intros * ha.
  unfold is_prime_sqrt in ha.
  apply Bool.andb_true_iff in ha; 
  destruct ha as [halt haiter].
  rewrite Z.ltb_lt in halt. 
  assert (hb : forall k, 1 <= k <= Z.sqrt n -> Z.gcd k n = 1).
  {
    intros k ha.
    eapply iterate_fn_spec_prime with (k := k), Z.eqb_eq  in haiter.
    exact haiter.
    rewrite Z2Nat.id.
    exact ha. nia.
  }
  (* Prove n is prime by contradiction *)
  destruct (prime_dec n) as [hp | hnp]; [assumption|].
  destruct (composite_has_divisor_sqrt n halt hnp) as [d [hc hd]].
  (* d satisfies gcd d n = d (since d divides n) *)
  assert (Hd_pos : 0 < d) by lia.
  assert (Hgcd : Z.gcd d n = d).
  {
    apply Z.gcd_unique; auto.
    - nia.
    - exists 1. nia.
  }
  assert (ha : 1 <= d <= Z.sqrt n). nia.
  specialize (hb _ ha).
  rewrite hb in Hgcd.
  nia.
Qed.

