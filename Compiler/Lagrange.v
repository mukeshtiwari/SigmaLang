From Stdlib Require Import Setoid
  setoid_ring.Field Lia List Utf8
  Psatz Bool.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.

Import ListNotations.

(** * Lagrange: interpolation over an abstract field

    Interpolation is the following problem.  You are handed a
    handful of points, each one a pair of an input and an output.
    You want a polynomial that passes through all of them.  If the
    inputs are pairwise different, there is exactly one such
    polynomial of low enough degree, and that polynomial is called
    the interpolant.  This file constructs it, proves that it really
    does pass through every given point, and proves that it is the
    only low-degree function that does.

    Some words used throughout, explained once here.

    - A field is a set with addition, subtraction, multiplication
      and division, in which division by anything other than [zero]
      is allowed and the usual algebraic laws hold.  The rational
      numbers form a field, and so does arithmetic modulo a prime.
      The whole file is parametric in such a field [F]: nothing
      below depends on which field it is.
    - A node is the input coordinate of one of the given points.  In
      the threshold protocol of Composition.v each child of a
      threshold node owns one public node of its own.
    - The degree of a polynomial is the highest power of the
      variable that occurs in it.  A polynomial written with [k]
      coefficients has degree less than [k].  The degree cap is the
      bound that the threshold protocol places on the degree of the
      prover's polynomial.
    - A root of a polynomial is an input at which the polynomial
      evaluates to [zero].

    ** Two halves, two representations

    The first half of the file works in evaluation form.  There is
    no datatype of polynomials at all.  The interpolant
    [lag_interp] is simply a function from [F] to [F], assembled as
    a weighted sum of the Lagrange basis factors [lag_basis].  That
    is all a verifier ever needs, because a verifier only ever
    evaluates.  Staying with functions keeps the construction short,
    and makes the main theorem [lag_interp_eval], which says that
    the interpolant passes through every given point, a direct
    computation.

    The second half needs more.  To show that the interpolant is the
    only low-degree function through those points, we have to count
    roots, and counting needs a representation that has a size.  So
    [poly] is introduced as a list of coefficients, [roots_bound]
    shows that a polynomial with more distinct roots than
    coefficients is [zero] everywhere, and [lag_poly] shows that the
    interpolant of the first half is exactly such a polynomial, of
    the expected size.  Uniqueness, [lag_interp_unique], follows.

    ** Where this is used

    [CThresh] in Composition.v is the Shamir threshold combinator.
    Its prover spreads one root challenge over all the children by
    interpolating, and its verifier reconstructs every child
    challenge with [lag_interp]; completeness, special soundness and
    zero knowledge of [CThresh] are all proven there.  Shamir.v then
    uses the uniqueness theorem proven here to show that two
    accepting threshold runs with different root challenges must
    disagree on at least [thr] children, which is exactly what the
    extractor of the threshold node needs. *)
Section Lagrange.

  (** ** Parameters

      Everything below is parametric in an arbitrary field.  The
      carrier type is [F], and the field structure is supplied as
      its operations together with a proof that they obey the field
      laws.

      - [zero] and [one] are the additive and multiplicative units;
      - [add], [mul], [sub] and [div] are the four binary
        operations;
      - [opp] is negation and [inv] is the multiplicative inverse;
      - [Fdec] decides equality of two field elements, which is what
        makes the case split in [mul_zero_factor] constructive;
      - [Hfield] is the proof that all of this really forms a
        field. *)
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hfield : @field F (@eq F) zero one opp add sub mul inv div}.

  (** Local infix notation for the three operations used most, so
      that the algebra below reads like ordinary arithmetic instead
      of nested function applications. *)
  #[local] Infix "*" := mul.
  #[local] Infix "+" := add.
  #[local] Infix "-" := sub.

  (** Register the field with the [field] tactic, so that routine
      algebraic identities can be discharged automatically, with the
      nonzero side conditions left as goals. *)
  Add Field field : (@field_theory_for_stdlib_tactic F
    eq zero one opp add mul sub inv div Hfield).

  (** ** Interpolation in evaluation form *)

  (** Pair each element of a list with all the remaining elements.

      Run on a list whose elements are [a], [b] and [c] in that
      order, [select] returns three pairs: [a] paired with the list
      of [b] and [c], then [b] paired with the list of [a] and [c],
      then [c] paired with the list of [a] and [b].  Every element
      appears once in a first component, and the second component
      always holds the others, in their original order.

      This is precisely the shape that a Lagrange basis factor
      needs.  The factor belonging to one node has to mention that
      node once, as the node it is centred on, and every other node
      once, as a place where it must vanish.  So [select] walks the
      point list and hands each step both pieces of information at
      the same time: the distinguished point, and all the rest. *)
  Fixpoint select {A : Type} (l : list A) : list (A * list A) :=
    match l with
    | [] => []
    | x :: xs =>
        (x, xs) :: List.map (fun p => (fst p, x :: snd p)) (select xs)
    end.

  (** The Lagrange basis factor belonging to the node [xi], taken
      with respect to the other nodes [xs], and evaluated at the
      point [x].  It is the product, over every other node [xj], of
      the ratio (x - xj) / (xi - xj), written here with [inv]
      because that is how a field divides.

      Two properties make this the right building block.  At
      [x = xi] every single ratio reads (xi - xj) / (xi - xj), which
      is [one], so the whole product is [one]: the factor is [one]
      at its own node, which is [lag_basis_self].  At [x = xj] for
      one of the other nodes, the numerator of that one ratio is
      [zero], so the whole product is [zero]: the factor vanishes at
      every other node, which is [lag_basis_zero].

      This is also where the nodes have to be pairwise distinct.  If
      [xi] were equal to one of the [xj] then the denominator
      (xi - xj) would be [zero], and there is no inverse of [zero],
      so the factor would be meaningless. *)
  Definition lag_basis (xi : F) (xs : list F) (x : F) : F :=
    List.fold_right
      (fun xj acc => ((x - xj) * inv (xi - xj)) * acc) one xs.

  (** The interpolant of a list of points, in evaluation form:
      given the points [pts] and an input [x], it returns the value
      at [x] of the low-degree polynomial through those points.

      It is the sum, over every point, of that point's output value
      multiplied by that point's basis factor.  [select] supplies,
      for each point, both the point itself and the list of all the
      others, and [List.map fst] keeps only the node of each of
      those others, since the values of the other points play no
      part in a basis factor.

      Why the sum passes through every given point: at the node of
      one particular point, that point's own basis factor is [one]
      and every other basis factor is [zero], so the whole sum
      collapses to that one point's output value.  That is the
      content of [lag_interp_eval].

      Note that there is no polynomial datatype in sight.  The
      interpolant is just a function, which is all that a verifier
      needs in order to evaluate. *)
  Definition lag_interp (pts : list (F * F)) (x : F) : F :=
    List.fold_right
      (fun p acc =>
        (snd (fst p)) *
        lag_basis (fst (fst p)) (List.map fst (snd p)) x + acc)
      zero (select pts).

  (** Two different field elements have a nonzero difference.

      If [a] and [b] are different then [a - b] cannot be [zero],
      because adding [b] back to [a - b] recovers [a], so a [zero]
      difference would force [a] and [b] to be equal.

      Small as it is, this fact is what licenses dividing by
      (xi - xj) in a basis factor: it converts the distinctness
      hypothesis on the nodes into exactly the nonzero side
      condition that the [field] tactic asks for. *)
  Lemma sub_neq_zero : ∀ (a b : F),
    a <> b -> a - b <> zero.
  Proof.
    intros * ha hb.
    eapply ha.
    assert (hc : a = (a - b) + b). field.
    rewrite hc, hb. field.
  Qed.

  (** A basis factor takes the value [one] at its own node.

      The hypothesis says that the node [xi] differs from every node
      in the list [xs] of other nodes.  Under that hypothesis every
      ratio in the product becomes (xi - xj) / (xi - xj), which is
      [one] because the denominator is nonzero by [sub_neq_zero],
      and a product of [one]s is [one].

      The proof is an induction on [xs]: peel off one other node,
      apply the induction hypothesis to the rest, and let the
      [field] tactic cancel the single remaining ratio. *)
  Lemma lag_basis_self : ∀ (xs : list F) (xi : F),
    (∀ xj, List.In xj xs -> xi <> xj) ->
    lag_basis xi xs xi = one.
  Proof.
    induction xs as [|xj xs ih]; intros xi ha.
    +
      reflexivity.
    +
      specialize (ih xi (fun xk hk => ha xk (or_intror hk))).
      unfold lag_basis in ih |- *; cbn.
      rewrite ih.
      field.
      eapply sub_neq_zero.
      eapply ha; left; reflexivity.
  Qed.

  (** A basis factor takes the value [zero] at every other node.

      The hypothesis says that [xz] is one of the other nodes listed
      in [xs].  The ratio of the product belonging to [xz] then has
      numerator (xz - xz), which is [zero], and a product with a
      [zero] factor is [zero].  No distinctness is needed for this
      direction, and the centre node [xi] plays no role at all.

      The proof is an induction on [xs], splitting on whether [xz]
      is the head of the list or lies somewhere in the tail. *)
  Lemma lag_basis_zero : ∀ (xs : list F) (xi xz : F),
    List.In xz xs ->
    lag_basis xi xs xz = zero.
  Proof.
    induction xs as [|xj xs ih]; intros xi xz ha.
    +
      destruct ha.
    +
      destruct ha as [ha | ha].
      ++
        subst.
        unfold lag_basis; cbn.
        assert (hb : xz - xz = zero). field.
        rewrite hb.
        assert (hc : ∀ q : F, zero * q = zero).
        intros; field.
        rewrite hc, hc.
        reflexivity.
      ++
        specialize (ih xi xz ha).
        unfold lag_basis in ih |- *; cbn.
        rewrite ih.
        assert (hc : ∀ q : F, q * zero = zero).
        intros; field.
        rewrite hc.
        reflexivity.
  Qed.

  (** Folding an addition over terms that are all [zero] leaves the
      starting value untouched.

      The function [f] assigns a field element to each element of
      the list [l], and the hypothesis says that every one of those
      elements is [zero].  Adding a pile of [zero]s to [init] gives
      back [init].

      This is the bookkeeping lemma behind [lag_interp_eval]: once
      we know that all the summands of the interpolant but one
      vanish, this lemma discards them in a single step instead of
      one at a time. *)
  Lemma fold_add_zero : ∀ {A : Type} (f : A -> F) (l : list A)
    (init : F),
    (∀ p, List.In p l -> f p = zero) ->
    List.fold_right (fun p acc => f p + acc) init l = init.
  Proof.
    intros A f.
    induction l as [|p l ih]; intros init ha.
    +
      reflexivity.
    +
      cbn.
      rewrite (ha p (or_introl eq_refl)).
      rewrite ih.
      field.
      intros q hq; eapply ha; right; exact hq.
  Qed.

  (** Splitting [select] at a distinguished element.

      Consider a list written as a prefix [l₁], then a distinguished
      element [p], then a suffix [l₂].  Applying [select] to it
      produces a list of pairs that can itself be cut into three
      pieces: a block [S₁], then the single entry that pairs [p]
      with all the other elements, then a block [S₂].  Moreover
      every entry in [S₁] and in [S₂] carries [p] somewhere inside
      its own list of others.

      Both halves of the statement are used by the main theorem.
      The middle entry is the summand that will survive, and the
      claim that all the other entries mention [p] is what makes
      their basis factors vanish at the node of [p], by
      [lag_basis_zero].

      The proof is an induction on the prefix [l₁], following the
      recursive shape of [select] itself. *)
  Lemma select_split : ∀ {A : Type} (l₁ l₂ : list A) (p : A),
    ∃ S₁ S₂,
      select (l₁ ++ p :: l₂) = S₁ ++ (p, l₁ ++ l₂) :: S₂ ∧
      (∀ q, List.In q (S₁ ++ S₂) -> List.In p (snd q)).
  Proof.
    induction l₁ as [|a l₁ ih]; intros l₂ p.
    +
      cbn.
      exists [], (List.map (fun q => (fst q, p :: snd q)) (select l₂)).
      split.
      ++
        reflexivity.
      ++
        intros q hq; cbn in hq.
        eapply List.in_map_iff in hq.
        destruct hq as (q' & hb & hc).
        rewrite <-hb; cbn.
        left; reflexivity.
    +
      destruct (ih l₂ p) as (S₁ & S₂ & hb & hc).
      exists ((a, l₁ ++ p :: l₂) ::
        List.map (fun q => (fst q, a :: snd q)) S₁),
        (List.map (fun q => (fst q, a :: snd q)) S₂).
      split.
      ++
        cbn.
        rewrite hb.
        rewrite List.map_app.
        cbn.
        reflexivity.
      ++
        intros q hq.
        cbn in hq.
        destruct hq as [hq | hq].
        +++
          rewrite <-hq; cbn.
          eapply List.in_or_app; right.
          left; reflexivity.
        +++
          rewrite <-List.map_app in hq.
          eapply List.in_map_iff in hq.
          destruct hq as (q' & hd & he).
          rewrite <-hd; cbn.
          right.
          eapply hc; exact he.
  Qed.

  (** Main theorem: the interpolant passes through every given
      point.

      [pts] is the list of points.  The hypothesis [List.NoDup] on
      the nodes says that the input coordinates are pairwise
      distinct; this both keeps every denominator of a basis factor
      away from [zero] and stops one input from being asked for two
      different outputs.  The hypothesis [List.In (xk, yk) pts] says
      that the pair of node [xk] and value [yk] is one of the given
      points.  The conclusion is that evaluating the interpolant at
      [xk] returns exactly [yk].

      The argument.  Split [pts] around the chosen point and use
      [select_split] to cut the sum defining the interpolant into
      three parts: the summands before the chosen point, the summand
      of the chosen point, and the summands after it.  Every summand
      other than the chosen one has a basis factor that mentions
      [xk] among its other nodes, so by [lag_basis_zero] that factor
      is [zero] at [xk] and the whole summand vanishes;
      [fold_add_zero] then wipes out each block in one go.  The
      surviving summand is [yk] multiplied by the basis factor of
      [xk], which by [lag_basis_self] is [one], using distinctness
      of the nodes.  What is left is [yk]. *)
  Theorem lag_interp_eval :
    ∀ (pts : list (F * F)) (xk yk : F),
    List.NoDup (List.map fst pts) ->
    List.In (xk, yk) pts ->
    lag_interp pts xk = yk.
  Proof.
    intros * hnd hin.
    destruct (List.in_split _ _ hin) as (l₁ & l₂ & hsplit); subst.
    destruct (@select_split (F * F) l₁ l₂ (xk, yk))
      as (S₁ & S₂ & hsel & hother).
    unfold lag_interp.
    rewrite hsel.
    rewrite List.fold_right_app.
    cbn [List.fold_right fst snd].
    (* the terms of S₂ vanish *)
    rewrite (fold_add_zero
      (fun p => (snd (fst p)) *
        lag_basis (fst (fst p)) (List.map fst (snd p)) xk) S₂ zero).
    +
      (* the distinguished term is yk · 1 *)
      rewrite List.map_app in hnd; cbn in hnd.
      pose proof (List.NoDup_remove_2 _ _ _ hnd) as hxk.
      rewrite lag_basis_self.
      ++
        assert (ha : yk * one + zero = yk). field.
        rewrite ha.
        (* the terms of S₁ vanish *)
        rewrite (fold_add_zero
          (fun p => (snd (fst p)) *
            lag_basis (fst (fst p)) (List.map fst (snd p)) xk) S₁ yk).
        reflexivity.
        intros p hp.
        rewrite lag_basis_zero.
        field.
        eapply List.in_map_iff.
        exists (xk, yk).
        split. reflexivity.
        eapply hother.
        eapply List.in_or_app; left; exact hp.
      ++
        intros xj hj heq; subst.
        eapply hxk.
        rewrite List.map_app in hj.
        exact hj.
    +
      intros p hp.
      rewrite lag_basis_zero.
      field.
      eapply List.in_map_iff.
      exists (xk, yk).
      split. reflexivity.
      eapply hother.
      eapply List.in_or_app; right; exact hp.
  Qed.

  (** ** Polynomials as coefficient lists

      The evaluation form above is enough to build an interpolant,
      but not enough to say that it is the only one.  Uniqueness is
      a counting statement about roots, and counting needs a
      representation that carries a size.  So this half of the file
      introduces polynomials as plain lists of coefficients, lowest
      degree first, and rebuilds the interpolant in that form.

      The chain of results is:

      - [quot_spec], division by a linear factor: the difference
        p(x) - p(a) equals (x - a) times the quotient evaluated
        at x;
      - [roots_bound]: a polynomial with more distinct roots than it
        has coefficients evaluates to [zero] everywhere;
      - [poly_unique]: two polynomials with at most as many
        coefficients as there are points, agreeing on that many
        distinct points, agree everywhere;
      - [lag_poly]: the interpolant of the first half really is such
        a polynomial, of the expected size, by [lag_poly_eval] and
        [lag_poly_length];
      - [lag_interp_unique] and [lag_interp_agree_at_zero]: the two
        uniqueness facts that threshold soundness consumes. *)

  (** A polynomial, represented as the list of its coefficients
      with the constant term first.  A list whose entries are [a],
      [b] and [c] stands for the polynomial a + b x + c x x.

      A polynomial written with [k] coefficients has degree less
      than [k], so the length of the list is the handle used for the
      degree cap.  Trailing [zero] coefficients are allowed, which
      means the length is an upper bound on the degree rather than
      the exact degree; every statement below is phrased as such an
      upper bound, so this costs nothing. *)
  Definition poly : Type := list F.

  (** Evaluate a polynomial at a point, by Horner's rule.

      The empty polynomial is the constant [zero].  A polynomial
      whose first coefficient is [c] and whose remaining
      coefficients form [p'] evaluates to [c] plus [x] times the
      value of [p'] at [x].  Unfolding the recursion gives the usual
      sum of coefficient times power, and it needs no exponentiation
      operator on the field. *)
  Fixpoint peval (p : poly) (x : F) : F :=
    match p with
    | [] => zero
    | c :: p' => c + x * peval p' x
    end.

  (** ** The root bound

      A field has no zero divisors, and that single fact is what
      limits how many roots a polynomial can have. *)

  (** If a product of two field elements is [zero], then one of the
      two factors is [zero].

      If the first factor [a] is [zero] we are done.  Otherwise [a]
      is invertible, and multiplying the equation through by the
      inverse of [a] leaves [b = zero].  The decidable equality
      [Fdec] is what makes that case split constructive.

      Put another way, a field is an integral domain.  This is the
      step where "the product of (r' - r) and the quotient is
      [zero]" turns into "either the two roots coincide or the
      quotient vanishes there", which is what drives the induction
      in [roots_bound]. *)
  Lemma mul_zero_factor : ∀ (a b : F),
    a * b = zero -> a = zero ∨ b = zero.
  Proof.
    intros * ha.
    destruct (Fdec a zero) as [hz | hnz].
    +
      left; exact hz.
    +
      right.
      assert (hb : b = inv a * (a * b)). field. exact hnz.
      rewrite hb, ha. field. exact hnz.
  Qed.

  (** Synthetic division by the linear factor (X - a): the call
      [quot a p] returns the quotient.  The remainder, which is
      always the value of [p] at [a], is left implicit; [quot_spec]
      below states the relation that pins both down.

      The recursion is ordinary synthetic division read from the
      top: each coefficient of the quotient is the value at [a] of
      the corresponding tail of [p].  A polynomial with one
      coefficient or none has an empty quotient, since dividing a
      constant by a linear factor yields nothing. *)
  Fixpoint quot (a : F) (p : poly) : poly :=
    match p with
    | [] => []
    | c :: p' =>
        match p' with
        | [] => []
        | _ :: _ => peval p' a :: quot a p'
        end
    end.

  (** Dividing by a linear factor removes exactly one coefficient.

      The quotient has one coefficient fewer than the dividend,
      except that the empty polynomial stays empty, which is what
      [Nat.pred] expresses.  This is the bookkeeping that makes the
      induction in [roots_bound] decrease: one root consumed, one
      coefficient fewer left. *)
  Lemma quot_length : ∀ (p : poly) (a : F),
    List.length (quot a p) = Nat.pred (List.length p).
  Proof.
    induction p as [|c p ih]; intros a.
    +
      reflexivity.
    +
      destruct p as [|c' p'].
      ++
        reflexivity.
      ++
        cbn.
        cbn in ih.
        rewrite (ih a).
        reflexivity.
  Qed.

  (** The defining property of synthetic division: for all [a] and
      [x], the difference of the value of [p] at [x] and its value
      at [a] equals (x - a) times the value of the quotient at [x].

      In particular, if [a] is a root of [p], then [p] factors as
      (x - a) times [quot a p].  This is the algebraic heart of the
      root bound: every root can be pulled out as a linear factor,
      and by [quot_length] each extraction costs one coefficient.

      The proof is an induction on the coefficient list.  The step
      is the identity (c + x Px) - (c + a Pa) = (x - a) (Pa + x B),
      valid whenever Px - Pa = (x - a) B, which the [field] tactic
      discharges once it has been stated. *)
  Lemma quot_spec : ∀ (p : poly) (a x : F),
    peval p x - peval p a = (x - a) * peval (quot a p) x.
  Proof.
    induction p as [|c p ih]; intros a x.
    +
      cbn. field.
    +
      destruct p as [|c' p'].
      ++
        cbn. field.
      ++
        specialize (ih a x).
        cbn in ih |- *.
        assert (hstep : ∀ (Px Pa B : F),
          Px - Pa = (x - a) * B ->
          (c + x * Px) - (c + a * Pa) = (x - a) * (Pa + x * B)).
        intros * hpq.
        assert (h₂ : (x - a) * (Pa + x * B) =
          (x - a) * Pa + x * ((x - a) * B)). field.
        rewrite h₂, <-hpq. field.
        eapply hstep. exact ih.
  Qed.

  (** A polynomial with more distinct roots than coefficients is
      the zero function.

      Read the hypotheses as follows.  [p] has at most [n]
      coefficients, so its degree is less than [n].  [roots] is a
      list of exactly [n] field elements, pairwise distinct by
      [List.NoDup], and [p] evaluates to [zero] at every one of
      them.  The conclusion is that [p] evaluates to [zero] at every
      input whatsoever, not only at the listed roots.

      Why it is true.  A nonzero polynomial of degree less than [n]
      cannot have [n] distinct roots.  Each root can be divided out
      by [quot_spec], and each division costs one coefficient by
      [quot_length], so [n] distinct roots would consume more
      coefficients than there are.

      The proof turns this into an induction on [n].  Take the first
      root [r] and factor [p] as (x - r) times the quotient.  Each
      of the remaining roots is still a root of the quotient: at
      such a root the product is [zero] and the first factor is not,
      because the roots are distinct, so by [mul_zero_factor] the
      quotient must vanish there.  The induction hypothesis then
      applies to the quotient, which has one coefficient fewer and
      one root fewer.  The base case is a polynomial with no
      coefficients at all, which is the zero function outright. *)
  Theorem roots_bound : ∀ (n : nat) (p : poly) (roots : list F),
    (List.length p <= n)%nat ->
    List.length roots = n ->
    List.NoDup roots ->
    (∀ r, List.In r roots -> peval p r = zero) ->
    ∀ x, peval p x = zero.
  Proof.
    induction n as [|n ih].
    +
      intros * hl hr hnd hz x.
      destruct p; [reflexivity | cbn in hl; lia].
    +
      intros * hl hr hnd hz x.
      destruct roots as [|r roots']; [cbn in hr; lia |].
      cbn in hr; injection hr as hr.
      inversion hnd as [| ? ? hnin hnd']; subst.
      pose proof (quot_spec p r x) as hq.
      rewrite (hz r (or_introl eq_refl)) in hq.
      assert (hpx : peval p x = (x - r) * peval (quot r p) x).
      rewrite <-hq. field.
      rewrite hpx.
      assert (hqz : peval (quot r p) x = zero).
      eapply (ih (quot r p) roots').
      rewrite quot_length. lia.
      reflexivity.
      exact hnd'.
      intros r' hr'.
      pose proof (quot_spec p r r') as hq'.
      rewrite (hz r' (or_intror hr')) in hq'.
      rewrite (hz r (or_introl eq_refl)) in hq'.
      assert (hq₂ : (r' - r) * peval (quot r p) r' = zero).
      rewrite <-hq'. field.
      destruct (mul_zero_factor _ _ hq₂) as [hz₁ | hz₂].
      exfalso.
      eapply hnin.
      assert (hrr : r' = r).
      assert (h₃ : r' = (r' - r) + r). field.
      rewrite h₃, hz₁. field.
      rewrite <-hrr. exact hr'.
      exact hz₂.
      rewrite hqz. field.
  Qed.

  (** ** Uniqueness of low-degree polynomials

      Subtraction is what connects the previous section to
      uniqueness.  It turns the question "do these two polynomials
      agree at many points?" into the question "does their
      difference have many roots?", and the second question is
      already answered by [roots_bound]. *)

  (** Negate a polynomial, coefficient by coefficient. *)
  Fixpoint pneg (p : poly) : poly :=
    match p with
    | [] => []
    | c :: p' => opp c :: pneg p'
    end.

  (** Subtract two polynomials, coefficient by coefficient.  When
      one of the two lists runs out, the rest of the other is taken
      over, negated if it was the second one.  The result has at
      most as many coefficients as the longer input, which is
      [psub_length]. *)
  Fixpoint psub (p q : poly) : poly :=
    match p, q with
    | [], q => pneg q
    | p, [] => p
    | a :: p', b :: q' => (a - b) :: psub p' q'
    end.

  (** Negating a polynomial negates its value at every point. *)
  Lemma pneg_eval : ∀ (q : poly) (x : F),
    peval (pneg q) x = opp (peval q x).
  Proof.
    induction q as [|c q ih]; intros x; cbn.
    field.
    rewrite ih. field.
  Qed.

  (** Negation does not change the number of coefficients, so it
      never affects a degree bound. *)
  Lemma pneg_length : ∀ (q : poly),
    List.length (pneg q) = List.length q.
  Proof.
    induction q; cbn; [reflexivity | rewrite IHq; reflexivity].
  Qed.

  (** The value of a difference is the difference of the values.

      This is the lemma that lets a statement about two polynomials
      agreeing at a point be restated as a statement about a single
      polynomial having a root there. *)
  Lemma psub_eval : ∀ (p q : poly) (x : F),
    peval (psub p q) x = peval p x - peval q x.
  Proof.
    induction p as [|a p ih]; intros q x.
    +
      cbn. rewrite pneg_eval. field.
    +
      destruct q as [|b q].
      ++
        cbn. field.
      ++
        cbn. rewrite ih. field.
  Qed.

  (** A difference has at most as many coefficients as the longer
      of its two inputs, so subtracting two polynomials never
      escapes their common degree cap. *)
  Lemma psub_length : ∀ (p q : poly),
    (List.length (psub p q) <=
      Nat.max (List.length p) (List.length q))%nat.
  Proof.
    induction p as [|a p ih]; intros q.
    +
      cbn. rewrite pneg_length. lia.
    +
      destruct q as [|b q]; cbn.
      lia.
      specialize (ih q). lia.
  Qed.

  (** Two low-degree polynomials that agree on enough distinct
      points are equal as functions.

      The hypotheses: [pts] is a list of pairwise distinct inputs;
      both [p] and [q] have at most as many coefficients as there
      are entries in [pts]; and the two polynomials take the same
      value at every entry of [pts].  The conclusion is that they
      take the same value at every input.

      Why it is true.  Look at the difference [psub p q].  By
      [psub_length] it has at most as many coefficients as [pts] has
      entries, and by [psub_eval] together with the agreement
      hypothesis it has a root at each of those entries.  That is
      more distinct roots than coefficients, so [roots_bound]
      applies and the difference is [zero] everywhere, which says
      exactly that [p] and [q] agree everywhere. *)
  Theorem poly_unique : ∀ (p q : poly) (pts : list F),
    List.NoDup pts ->
    (List.length p <= List.length pts)%nat ->
    (List.length q <= List.length pts)%nat ->
    (∀ r, List.In r pts -> peval p r = peval q r) ->
    ∀ x, peval p x = peval q x.
  Proof.
    intros * hnd hlp hlq hagree x.
    assert (hzz : peval (psub p q) x = zero).
    eapply (roots_bound (List.length pts) (psub p q) pts).
    pose proof (psub_length p q). lia.
    reflexivity.
    exact hnd.
    intros r hr. rewrite psub_eval. rewrite (hagree r hr). field.
    rewrite psub_eval in hzz.
    assert (h₂ : peval p x = (peval p x - peval q x) + peval q x).
    field.
    rewrite h₂, hzz. field.
  Qed.

  (** ** The interpolant as a coefficient polynomial

      To apply [poly_unique] to [lag_interp] we must exhibit the
      interpolant as an actual coefficient list, and bound its
      length.  This section therefore rebuilds the construction of
      the first half inside the [poly] representation, piece by
      piece: addition, scaling by a constant, multiplication by a
      linear factor, then the basis factors, then the interpolant
      itself.  Each piece comes with two lemmas, one saying that it
      evaluates the same way as its evaluation-form counterpart, and
      one bounding its number of coefficients. *)

  (** Add two polynomials coefficient by coefficient; when one list
      runs out, the remaining coefficients of the other are copied
      across unchanged. *)
  Fixpoint padd (p q : poly) : poly :=
    match p, q with
    | [], q => q
    | p, [] => p
    | a :: p', b :: q' => (a + b) :: padd p' q'
    end.

  (** The value of a sum is the sum of the values. *)
  Lemma padd_eval : ∀ (p q : poly) (x : F),
    peval (padd p q) x = peval p x + peval q x.
  Proof.
    induction p as [|a p ih]; intros q x.
    +
      cbn. field.
    +
      destruct q as [|b q]; cbn.
      field.
      rewrite ih. field.
  Qed.

  (** A sum has at most as many coefficients as the longer of its
      two inputs, so adding polynomials never exceeds the larger of
      their degree caps. *)
  Lemma padd_length : ∀ (p q : poly),
    (List.length (padd p q) <=
      Nat.max (List.length p) (List.length q))%nat.
  Proof.
    induction p as [|a p ih]; intros q.
    +
      cbn. lia.
    +
      destruct q as [|b q]; cbn.
      lia.
      specialize (ih q). lia.
  Qed.

  (** Multiply every coefficient by the constant [c], which is the
      same as multiplying the whole polynomial by [c].  This is how
      a basis factor gets weighted by its point's output value, and
      how the reciprocal of a node difference is applied. *)
  Definition pscale (c : F) (p : poly) : poly :=
    List.map (mul c) p.

  (** Scaling a polynomial by [c] scales its value at every point
      by [c]. *)
  Lemma pscale_eval : ∀ (p : poly) (c x : F),
    peval (pscale c p) x = c * peval p x.
  Proof.
    induction p as [|a p ih]; intros c x.
    +
      cbn. field.
    +
      specialize (ih c x).
      unfold pscale in ih |- *; cbn.
      rewrite ih. field.
  Qed.

  (** Scaling does not change the number of coefficients, since it
      is just a [List.map] over the list. *)
  Lemma pscale_length : ∀ (p : poly) (c : F),
    List.length (pscale c p) = List.length p.
  Proof.
    intros; eapply List.map_length.
  Qed.

  (** Multiply a polynomial by the linear factor (X - a).

      Multiplying by X shifts every coefficient one place up, which
      is what putting an extra [zero] in front of the list does, and
      multiplying by the negation of [a] is a [pscale].  Adding the
      two results gives the product.  This is the operation that
      builds a basis factor one node at a time. *)
  Definition lin_mul (a : F) (p : poly) : poly :=
    padd (pscale (opp a) p) (zero :: p).

  (** Multiplying by the linear factor multiplies the value at [x]
      by (x - a), which is the whole point of the definition.  Note
      in passing that the product vanishes at [a], whatever [p] is:
      that is how a basis factor acquires its roots. *)
  Lemma lin_mul_eval : ∀ (p : poly) (a x : F),
    peval (lin_mul a p) x = (x - a) * peval p x.
  Proof.
    intros *.
    unfold lin_mul.
    rewrite padd_eval, pscale_eval; cbn.
    field.
  Qed.

  (** Multiplying by a linear factor adds at most one coefficient,
      that is, it raises the degree by at most one. *)
  Lemma lin_mul_length : ∀ (p : poly) (a : F),
    (List.length (lin_mul a p) <= S (List.length p))%nat.
  Proof.
    intros *.
    unfold lin_mul.
    pose proof (padd_length (pscale (opp a) p) (zero :: p)) as ha.
    rewrite pscale_length in ha.
    cbn in ha. lia.
  Qed.

  (** The Lagrange basis factor of the node [xi] with respect to
      the other nodes [xs], now as an actual coefficient list.

      It is built by folding over the other nodes: start from the
      constant polynomial [one], and for each other node [xj]
      multiply by the linear factor (X - xj) with [lin_mul], then
      scale by the inverse of (xi - xj) with [pscale].  This is the
      same product as [lag_basis], only assembled as coefficients
      instead of being evaluated on the fly. *)
  Definition basis_poly (xi : F) (xs : list F) : poly :=
    List.fold_right
      (fun xj acc => pscale (inv (xi - xj)) (lin_mul xj acc))
      [one] xs.

  (** The coefficient form and the evaluation form of a basis
      factor agree at every point.

      This is the bridge lemma of the section: everything already
      proven about [lag_basis], such as being [one] at its own node
      and [zero] at the others, transfers to [basis_poly] and back
      without being reproved. *)
  Lemma basis_poly_eval : ∀ (xs : list F) (xi x : F),
    peval (basis_poly xi xs) x = lag_basis xi xs x.
  Proof.
    induction xs as [|xj xs ih]; intros xi x.
    +
      cbn. field.
    +
      specialize (ih xi x).
      unfold basis_poly, lag_basis in ih |- *.
      cbn [List.fold_right].
      rewrite pscale_eval, lin_mul_eval, ih.
      set (k := inv (xi - xj)).
      field.
  Qed.

  (** A basis factor built from [k] other nodes has at most [k + 1]
      coefficients, that is, degree at most [k].

      Each step of the fold multiplies by one linear factor, which
      adds at most one coefficient by [lin_mul_length], and the
      scaling adds none by [pscale_length].  The fold starts from
      the single coefficient [one]. *)
  Lemma basis_poly_length : ∀ (xs : list F) (xi : F),
    (List.length (basis_poly xi xs) <= S (List.length xs))%nat.
  Proof.
    induction xs as [|xj xs ih]; intros xi.
    +
      cbn. lia.
    +
      specialize (ih xi).
      unfold basis_poly in ih |- *.
      cbn [List.fold_right].
      rewrite pscale_length.
      pose proof (lin_mul_length
        (List.fold_right
          (fun xj' acc => pscale (inv (xi - xj')) (lin_mul xj' acc))
          [one] xs) xj) as ha.
      cbn [List.length].
      lia.
  Qed.

  (** The interpolant of the points [pts], as a coefficient list.

      It is the same weighted sum as [lag_interp]: [select] hands
      over each point together with all the others, each point
      contributes its basis polynomial scaled by its own output
      value, and the contributions are added up with [padd]. *)
  Definition lag_poly (pts : list (F * F)) : poly :=
    List.fold_right
      (fun p acc =>
        padd (pscale (snd (fst p))
          (basis_poly (fst (fst p)) (List.map fst (snd p)))) acc)
      [] (select pts).

  (** The coefficient form and the evaluation form of the
      interpolant agree at every point.

      Together with [lag_poly_length] this is what makes
      [poly_unique], a statement about coefficient lists, applicable
      to [lag_interp], which is only a function. *)
  Lemma lag_poly_eval : ∀ (pts : list (F * F)) (x : F),
    peval (lag_poly pts) x = lag_interp pts x.
  Proof.
    intros *.
    unfold lag_poly, lag_interp.
    induction (select pts) as [|e sel ih]; cbn.
    +
      reflexivity.
    +
      rewrite padd_eval, pscale_eval, basis_poly_eval, ih.
      reflexivity.
  Qed.

  (** Every entry produced by [select] accounts for the whole list.

      If the pair of [p] and [others] occurs in [select l], then
      [others] has exactly one element fewer than [l], because
      [others] is [l] with the single occurrence of [p] removed.

      This is the counting fact needed to bound the size of
      [lag_poly]: each summand is a basis polynomial built from the
      other nodes, and there is one fewer of those than there are
      points. *)
  Lemma select_entry_length : ∀ (A : Type) (l : list A)
    (p : A) (others : list A),
    List.In (p, others) (select l) ->
    S (List.length others) = List.length l.
  Proof.
    induction l as [|x xs ih]; intros * ha.
    +
      destruct ha.
    +
      cbn in ha.
      destruct ha as [ha | ha].
      ++
        injection ha as h₁ h₂; subst.
        reflexivity.
      ++
        eapply List.in_map_iff in ha.
        destruct ha as ((p' & others') & hb & hc).
        injection hb as h₁ h₂; subst.
        cbn.
        rewrite (ih _ _ hc).
        reflexivity.
  Qed.

  (** The interpolant of [n] points has at most [n] coefficients,
      that is, degree less than [n].

      Each summand is a basis polynomial built from the other
      nodes, of which there is one fewer than there are points by
      [select_entry_length], so each summand has at most [n]
      coefficients by [basis_poly_length].  Scaling preserves that
      by [pscale_length], and adding the summands preserves the
      maximum by [padd_length].

      This bound is exactly the degree cap that the threshold
      protocol relies on: the number of points the prover may choose
      controls the degree, and the degree controls how many child
      challenges the prover can pick by hand. *)
  Lemma lag_poly_length : ∀ (pts : list (F * F)),
    (List.length (lag_poly pts) <= List.length pts)%nat.
  Proof.
    intros *.
    unfold lag_poly.
    assert (ha : ∀ e, List.In e (select pts) ->
      S (List.length (snd e)) = List.length pts).
    intros (pe & others) he.
    eapply select_entry_length; exact he.
    induction (select pts) as [|e sel ih]; cbn.
    +
      lia.
    +
      pose proof (padd_length
        (pscale (snd (fst e))
          (basis_poly (fst (fst e)) (List.map fst (snd e))))
        (List.fold_right
          (fun p acc =>
            padd (pscale (snd (fst p))
              (basis_poly (fst (fst p)) (List.map fst (snd p)))) acc)
          [] sel)) as hb.
      rewrite pscale_length in hb.
      pose proof (basis_poly_length
        (List.map fst (snd e)) (fst (fst e))) as hc.
      rewrite List.map_length in hc.
      pose proof (ha e (or_introl eq_refl)) as hd.
      cbn in hd.
      assert (he : ∀ e', List.In e' sel ->
        S (List.length (snd e')) = List.length pts).
      intros e' he'.
      eapply ha; right; exact he'.
      specialize (ih he).
      lia.
  Qed.

  (** ** Uniqueness of Lagrange interpolants

      The payoff of the second half, stated back in evaluation form
      so that callers never have to mention [poly] at all. *)

  (** Two interpolants that agree on enough distinct nodes are the
      same function.

      The hypotheses: [nodes] is a list of pairwise distinct field
      elements; each of the two point lists [pts₁] and [pts₂] has at
      most as many points as there are nodes, which is the degree
      cap; and the two interpolants take the same value at every one
      of those nodes.  The conclusion is that they take the same
      value at every input at all, including inputs nowhere near the
      nodes.

      Why it is true.  By [lag_poly_eval] and [lag_poly_length],
      each interpolant is a coefficient polynomial with at most as
      many coefficients as there are nodes, so [poly_unique] applies
      directly.  Underneath, this is the root count of
      [roots_bound]: the difference of the two interpolants is a
      polynomial of degree less than the number of nodes which
      vanishes at every one of those nodes, and only the zero
      polynomial can do that. *)
  Theorem lag_interp_unique :
    ∀ (pts₁ pts₂ : list (F * F)) (nodes : list F),
    List.NoDup nodes ->
    (List.length pts₁ <= List.length nodes)%nat ->
    (List.length pts₂ <= List.length nodes)%nat ->
    (∀ a, List.In a nodes ->
      lag_interp pts₁ a = lag_interp pts₂ a) ->
    ∀ x, lag_interp pts₁ x = lag_interp pts₂ x.
  Proof.
    intros * hnd hl₁ hl₂ hagree x.
    rewrite <-!lag_poly_eval.
    eapply (poly_unique (lag_poly pts₁) (lag_poly pts₂) nodes).
    exact hnd.
    pose proof (lag_poly_length pts₁). lia.
    pose proof (lag_poly_length pts₂). lia.
    intros r hr.
    rewrite !lag_poly_eval.
    eapply hagree; exact hr.
  Qed.

  (** The special case that threshold soundness actually consumes:
      agreement on enough distinct nodes forces agreement at the
      input [zero].

      The hypotheses are those of [lag_interp_unique], and the
      conclusion is just that theorem instantiated at [zero].

      Why [zero] is the interesting input.  In the threshold
      protocol of Composition.v the value of the interpolant at
      [zero] is the root challenge, and its values at the public
      nodes are the child challenges.  Read contrapositively, this
      corollary says that two runs with different root challenges
      cannot agree on that many child challenges.  The number of
      children they may agree on is capped by the degree cap, so the
      remaining children, at least [thr] of them, must have received
      different challenges, and each of those is a child the
      extractor can open.  That is the counting argument carried out
      in Shamir.v as [threshold_extraction]. *)
  Corollary lag_interp_agree_at_zero :
    ∀ (pts₁ pts₂ : list (F * F)) (nodes : list F),
    List.NoDup nodes ->
    (List.length pts₁ <= List.length nodes)%nat ->
    (List.length pts₂ <= List.length nodes)%nat ->
    (∀ a, List.In a nodes ->
      lag_interp pts₁ a = lag_interp pts₂ a) ->
    lag_interp pts₁ zero = lag_interp pts₂ zero.
  Proof.
    intros * hnd hl₁ hl₂ hagree.
    eapply lag_interp_unique.
    exact hnd. exact hl₁. exact hl₂. exact hagree.
  Qed.

End Lagrange.
