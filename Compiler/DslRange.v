From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool List PeanoNat.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import
  Util.
From Compiler Require Import
  LinearRelation Composition Dsl DslRename DslRepair.

Import VectorNotations.

(** * DslRange: proving that a secret lies in an interval

    This file builds the "range" gadget of the compiler: the block of
    equations a prover must satisfy in order to convince a verifier
    that a secret value [x] lies between [0] and a public bound [u],
    without revealing [x] itself.

    ** Why a range proof needs a gadget at all

    Everything in this development happens over an abstract field [F].
    A field has addition and multiplication, but it has no order:
    there is no "less than" relation on [F], so the sentence "[x] is
    between [0] and [u]" is not even expressible directly.

    What can be said is this.  The natural numbers are embedded into
    the field by [fnat], which sends [0] to [zero] and [S k] to
    [one + fnat k].  A field element counts as small when it is the
    image under [fnat] of a natural number below [u].  So the property
    the gadget establishes is

    - there is a natural number [k] with [k < u] and [wenv x = fnat k].

    That is the only faithful reading of "in range" over an abstract
    field, and it is exactly what [range_sound] below delivers.

    ** The idea: decompose the secret into bits

    A number below [u] can be written as a weighted sum of bits.  So
    the prover publishes one commitment per bit, proves that each
    committed value really is a bit, that is, only [0] or [1], and
    proves one further equation saying that the weighted sum of those
    bits is [x].  If every bit is genuinely [0] or [1], the weighted
    sum cannot exceed the sum of the weights, and the weights are
    chosen so that this total is exactly [u - 1].  Hence [x] is the
    image of a natural number below [u].

    ** The equations

    Write [A] and [B] for two public group elements, the Pedersen
    bases, and [b] for a bit.  A Pedersen commitment to [b] with
    randomness [r] is the group element [gop (gpow A b) (gpow B r)],
    that is, [A] raised to [b] times [B] raised to [r].  An opening of
    a commitment is a pair of scalars that produce it in this way.
    For each bit index the gadget asks for two equations:

    - the first, [commit_eq], says the published point is a commitment
      to the bit with some randomness;
    - the second says the same point is also a commitment whose base
      is the point itself, raised to the bit.

    Read together, the second equation forces the committed value to
    equal its own square, and the only field elements equal to their
    own square are [zero] and [one].  That is what pins a bit down;
    see [bit_dichotomy].

    A final equation, [range_link], ties the bits back to [x].

    Every equation is linear in the secrets, so the whole gadget is an
    ordinary block of core equations and needs nothing new from the
    composition layer.

    ** What is proven

    - [range_sound]: any witness satisfying the gadget either places
      [x] in the interval, or reveals that the public setup was
      broken.  The comment on that theorem spells out the dichotomy.
    - [range_complete]: an honest prover who really holds a small [x]
      can publish the bit commitments and satisfy the gadget.

    The names of the per-bit variables and of the per-bit commitment
    points are not fixed here.  They are supplied by the caller as
    functions of the bit index, so that the surface language can
    generate fresh names; see [bb], [br], [bs] and [bC].

    The user-facing constructor [TRange] of Compiler/Surface.v lowers
    to [range_stmt] and inherits both theorems. *)

Section DslRange.

  (** ** Parameters of the gadget

      Everything below is parametric in three structures.

      - A field [F], with constants [zero] and [one], operations
        [add], [mul], [sub] and [div], negation [opp], inverse [inv],
        and a procedure [Fdec] deciding equality of two field
        elements.  Field elements are the secret scalars.
      - A group [G], written multiplicatively, with identity [gid],
        inverse [ginv], product [gop] and exponentiation [gpow], where
        [gpow g x] is [g] raised to the power [x].  Group elements are
        the public points: the Pedersen bases and the bit
        commitments.
      - A type [V] of variable names with decidable equality [vdec].
        A statement never mentions concrete field or group values,
        only names; an environment is what maps a name to a value. *)
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}.

  Context
    {G : Type}
    {gid : G}
    {ginv : G -> G}
    {gop : G -> G -> G}
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}.

  Context
    {V : Type}
    {vdec : forall x y : V, {x = y} + {x <> y}}.

  (** Local notations: [^] is group exponentiation, [*] and [+] are
      the field product and sum.  They are local to this section and
      do not leak into other files. *)
  #[local] Infix "^" := gpow.
  #[local] Infix "*" := mul.
  #[local] Infix "+" := add.

  (** Abbreviations for the syntax of Compiler/Dsl.v, already applied
      to this section's field, group and name types: public scalar
      expressions, equations and statements, the Pedersen commitment
      equation [commit_eq] borrowed from Compiler/DslRepair.v, and the
      boolean equality test on names. *)
  #[local] Notation pexprC := (@pexpr F V).
  #[local] Notation equationC := (@equation F V).
  #[local] Notation stmtC := (@stmt F V).
  #[local] Notation commit_eqC := (@commit_eq F one V).
  #[local] Notation veqb := (@veqb V vdec).

  (** The embedding of the natural numbers into the field: [fnat 0] is
      [zero] and [fnat (S k)] is [one + fnat k], so [fnat k] is [one]
      added to itself [k] times.  This is how a statement about
      counting becomes a statement about field elements.  It is not
      injective in general, since in a prime field it eventually wraps
      around, which is why a real deployment keeps the bound [u] far
      below the size of the field; that is a parameter choice, not a
      concern of these proofs. *)
  Fixpoint fnat (k : nat) : F :=
    match k with
    | 0 => zero
    | S k' => one + fnat k'
    end.

  (** The projection from a field element back to a bit, used only by
      the extractor in the soundness proof.  [bitof v] is [0] when [v]
      is [zero] and [1] otherwise.  It is a genuine inverse of [fnat]
      only on values already known to be [zero] or [one], which is
      exactly the situation it is used in; see [bitof_fnat]. *)
  Definition bitof (v : F) : nat :=
    match Fdec v zero with
    | left _ => 0
    | right _ => 1
    end.

  (** The names the gadget uses, given as functions of the bit index
      [i].

      - [bb i] names the [i]-th bit itself;
      - [br i] names the randomness of the commitment to that bit;
      - [bs i] names the extra scalar used by the second, squaring
        equation for that bit;
      - [bC i] names the published commitment point of that bit.

      Leaving these as parameters puts the caller in charge of picking
      names that clash with nothing else.  The resulting freshness
      conditions reappear as hypotheses of [range_complete]. *)
  Variable bb br bs bC : nat -> V.

  (** The weights used to decompose a value below [u].

      The list holds the powers of two [1], [2], [4] and so on, up to
      but not including [Nat.pow 2 (Nat.log2 u)], followed by one
      final weight: the remainder [u - Nat.pow 2 (Nat.log2 u)].

      Why is the last weight a remainder rather than the next power of
      two?  Because the representable values have to be exactly [0] up
      to [u - 1], with nothing above.  With every bit equal to [0] or
      [1], the largest representable value is the sum of all the
      weights.  The powers of two below the top one add up to
      [Nat.pow 2 (Nat.log2 u) - 1], and adding the remainder gives
      [u - 1] exactly; this is [weights_sum].  Putting a plain power
      of two in the last slot would let a prover reach values at or
      above [u], and then the gadget would prove nothing about the
      bound.  Nothing below [u] is lost either: [range_bits_exist]
      shows every such value still has a bit vector, using the last
      bit as a flag meaning "at least the remainder". *)
  Definition range_weights (u : nat) : list nat :=
    List.app
      (List.map (fun i => Nat.pow 2 i) (List.seq 0 (Nat.log2 u)))
      (List.cons (u - Nat.pow 2 (Nat.log2 u))%nat List.nil).

  (** The same weights paired with their positions: [indexed_weights u]
      is the list of pairs [(i, w)] where [w] is the [i]-th element of
      [range_weights u].

      The index has to be carried around explicitly because it is what
      selects the variable names: the pair [(i, w)] contributes the
      bit named [bb i] with weight [w].  Keeping index and weight
      together lets the link equation and the bit equations both be
      generated by a single traversal of one list. *)
  Definition indexed_weights (u : nat) : list (nat * nat) :=
    List.combine
      (List.seq 0 (List.length (range_weights u)))
      (range_weights u).

  (** Every pair produced by [indexed_weights u] carries a legal bit
      position, that is, an index strictly below the number of
      weights.  True because the indices come from
      [List.seq 0 (List.length (range_weights u))] and [List.combine]
      can only shorten a list.  It is needed wherever a bit index is
      used to look up an entry of a list of that length. *)
  Lemma indexed_weights_idx :
    ∀ (u : nat) (iw : nat * nat),
    List.In iw (indexed_weights u) -> (fst iw < List.length (range_weights u))%nat.
  Proof.
    intros u [i w] hin; cbn [fst].
    unfold indexed_weights in hin.
    eapply List.in_combine_l in hin.
    eapply List.in_seq in hin. lia.
  Qed.

  (** The two equations constraining bit number [i], where [An] and
      [Bn] name the two Pedersen bases.

      The first is [commit_eq], reused from Compiler/DslRepair.v: the
      published point [bC i] equals [An] raised to the bit [bb i],
      times [Bn] raised to the randomness [br i].

      The second says that the very same point [bC i] also equals
      itself raised to the bit, times [Bn] raised to the auxiliary
      scalar [bs i].  Substituting the first equation into the second
      writes one point as a commitment in two ways, once with the bit
      as exponent and once with the bit squared as exponent.  Either
      those exponents agree, which forces the bit to be [zero] or
      [one], or the two openings genuinely differ and a discrete
      logarithm of [An] to the base [Bn] falls out.  That case
      analysis is [bit_dichotomy].

      Both equations are linear in the secrets, so both are ordinary
      core equations. *)
  Definition bit_eqs (An Bn : V) (i : nat) : list equationC :=
    List.cons (commit_eqC (bC i) An Bn (bb i) (br i))
    (List.cons (simple_eq (one := one) (bC i)
      (List.cons (mkterm (PConst one) (bb i) (bC i))
        (List.cons (mkterm (PConst one) (bs i) Bn) List.nil)))
      List.nil).

  (** The equation linking the bits back to the secret.

      Given the base name [An], the name [x] of the secret and the
      indexed weights [iws], this is the equation whose terms are [An]
      raised to [x] and then, for every pair [(i, w)] in [iws], [An]
      raised to minus [fnat w] times the bit [bb i].  Reading off the
      exponents, it says that [x] minus the weighted sum of the bits
      is zero, which is to say that [x] is that weighted sum.

      It carries no public offset terms, so it is homogeneous: the
      whole product is required to be the group identity.  Since every
      term shares the base [An], the equation says nothing at all when
      [An] is itself the identity, which is why a degenerate branch
      appears in the soundness statement. *)
  Definition range_link (An x : V) (iws : list (nat * nat)) : equationC :=
    mkeq (List.cons (mkterm (PConst one) x An)
      (List.map (fun iw =>
        mkterm (PConst (opp (fnat (snd iw)))) (bb (fst iw)) An) iws))
      List.nil.

  (** The complete lowered statement for "[x] lies below [u]".

      It is a single block of core equations: first the link equation
      over all the indexed weights, then, for each indexed weight, the
      two equations constraining that bit.  [An] and [Bn] name the two
      Pedersen bases, [x] names the secret and [u] is the public
      bound.  This is what the surface constructor [TRange] compiles
      to. *)
  Definition range_stmt (An Bn x : V) (u : nat) : stmtC :=
    SEqs (List.cons (range_link An x (indexed_weights u))
      (List.flat_map (fun iw => bit_eqs An Bn (fst iw))
        (indexed_weights u))).

  (** Search for the first bit position whose committed value is not a
      bit at all.

      [find_nonbit wenv l] walks the indexed weights [l] and returns
      the first pair whose bit variable takes, in the environment
      [wenv], a value that is neither [zero] nor [one].  It returns
      [None] when every value is one of the two.

      This is the pivot of the soundness proof.  If the search fails,
      all the bits are genuine and the counting argument applies.  If
      it succeeds, the two equations of that one bit are
      contradictory unless the setup is degenerate, and a discrete
      logarithm can be extracted.  Writing the search as a function,
      rather than appealing to classical choice, keeps the whole
      development constructive. *)
  Fixpoint find_nonbit (wenv : V -> F) (l : list (nat * nat)) :
    option (nat * nat) :=
    match l with
    | List.nil => None
    | List.cons iw l' =>
        match Fdec (wenv (bb (fst iw))) zero with
        | left _ => find_nonbit wenv l'
        | right _ =>
            match Fdec (wenv (bb (fst iw))) one with
            | left _ => find_nonbit wenv l'
            | right _ => Some iw
            end
        end
    end.

  (** ** Semantics: what it means to satisfy the gadget

      From here on statements are read against environments.  [genv]
      maps a name to the public group element it stands for, so it
      records which points [An], [Bn] and each [bC i] actually are.
      [penv] maps a name to a public field element and is used by
      public coefficient expressions.  A third environment, always
      called [wenv] below, maps a name to a secret field element; it
      is the witness, the private data the prover claims to know. *)
  Section Spec.

    Variable genv : V -> G.
    Variable penv : V -> F.

    (** Abbreviations for the denotation functions of Compiler/Dsl.v at
        these environments: [eq_denoteC wenv e] says the single
        equation [e] holds, [stmt_denoteC wenv s] says the statement
        [s] holds, and [terms_foldC wenv ts] is the group element
        obtained by multiplying out the list of terms [ts]. *)
    #[local] Notation eq_denoteC :=
      (@eq_denote F add mul opp G gid gop gpow V genv penv).
    #[local] Notation stmt_denoteC :=
      (@stmt_denote F add mul opp G gid gop gpow V genv penv).
    #[local] Notation terms_foldC :=
      (@terms_fold F add mul opp G gid gop gpow V genv penv).

    (** ** Soundness

        The proofs need more than bare syntax: they need the group and
        the field to fit together, which is what the vector space
        structure [Hvec] provides.  It supplies the laws relating
        exponents to products of points, for instance that a base
        raised to a sum of exponents is the product of the base raised
        to each.  The [Add Field] declaration arms the [field] tactic
        so that routine identities in [F] can be discharged
        automatically. *)
    Section Proofs.

      Context
        {Hvec : @vector_space F (@eq F) zero one add mul sub
          div opp inv G (@eq G) gid ginv gop gpow}.
      Add Field field : (@field_theory_for_stdlib_tactic F
        eq zero one opp add mul sub inv div vector_space_field).

      (** *** Arithmetic of the embedding

          Three small facts saying that [fnat] respects sums and
          products as far as we need, plus the fact that a field has
          no zero divisors. *)

      (** The embedding turns addition of naturals into addition in the
          field.  Proved by induction on the first argument: the base
          case is [fnat 0 = zero] and the step unfolds one [S] on each
          side.  This is what allows a counting argument carried out
          on natural numbers to be transported to the field side. *)
      Lemma fnat_add : ∀ (a b : nat), fnat (a + b)%nat = fnat a + fnat b.
      Proof.
        induction a as [|a ih]; intros *; cbn.
        field.
        rewrite ih. field.
      Qed.

      (** The embedding turns multiplication of naturals into
          multiplication in the field.  Induction on the first
          argument, using [fnat_add] in the step, since [S a] times [b]
          is [b] plus [a] times [b].  It is used to rewrite a weight
          times a bit, which is precisely where the nat-side weighted
          sum meets the field-side one. *)
      Lemma fnat_mul : ∀ (a b : nat), fnat (a * b)%nat = fnat a * fnat b.
      Proof.
        induction a as [|a ih]; intros *; cbn.
        field.
        rewrite fnat_add, ih. field.
      Qed.

      (** A field has no zero divisors: if a product is [zero] then one
          of its two factors is [zero].  The argument is the usual one.
          If the first factor is not [zero] it has a multiplicative
          inverse, and multiplying the hypothesis through by that
          inverse leaves the second factor equal to [zero].  The
          decision procedure [Fdec] supplies the case split
          constructively. *)
      Lemma fmul_zero_factor : ∀ (a b : F),
        a * b = zero -> a = zero ∨ b = zero.
      Proof.
        intros * ha.
        destruct (Fdec a zero) as [hz | hnz].
        left; exact hz.
        right.
        assert (hb : b = inv a * (a * b)). field. exact hnz.
        rewrite hb, ha. field. exact hnz.
      Qed.

      (** For a value already known to be [zero] or [one], projecting it
          to a bit with [bitof] and embedding the result back with
          [fnat] returns the original value.  So [bitof] really does
          invert [fnat] on the two-element set of bits.  This is the
          bridge the soundness proof crosses when it replaces
          field-side bit values by nat-side ones. *)
      Lemma bitof_fnat : ∀ (v : F),
        v = zero ∨ v = one -> fnat (bitof v) = v.
      Proof.
        intros * ha.
        unfold bitof.
        destruct (Fdec v zero) as [hz | hnz].
        + cbn. rewrite hz. reflexivity.
        + destruct ha as [ha | ha]; [congruence |].
          cbn. rewrite ha. field.
      Qed.

      (** *** One bit is really a bit, or the setup is broken *)

      (** The key fact about the per-bit gadget.

          The two hypotheses are the two equations of [bit_eqs] for a
          single bit, read in the environment [wenv]: the point [Cb] is
          the commitment to the value of [b] with randomness [r], and
          the same point [Cb] also equals [Cb] raised to that value,
          times [Bn] raised to the value of [sn].

          Substituting the first into the second writes one point as a
          commitment in two ways: once with the bit value as exponent,
          once with the bit value squared.  If the two exponents are
          equal, then the value [v] satisfies [v = v * v], hence
          [v * (one + opp v) = zero], and since a field has no zero
          divisors ([fmul_zero_factor]) the value must be [zero] or
          [one].  If the two exponents differ, we hold two different
          openings of one commitment, and [two_openings_dlog] of
          Compiler/DslRepair.v turns them into a discrete logarithm
          [d], that is, an exponent with [genv An] equal to [genv Bn]
          raised to [d].

          A discrete logarithm is the exponent carrying one public
          point to another.  The security of the commitment scheme
          rests on nobody being able to produce one, so this branch of
          the conclusion is a break of the setup rather than a useful
          proof about the secret. *)
      Lemma bit_dichotomy :
        ∀ (Cb An Bn b r sn : V) (wenv : V -> F),
        eq_denoteC wenv (commit_eqC Cb An Bn b r) ->
        eq_denoteC wenv (simple_eq (one := one) Cb
          (List.cons (mkterm (PConst one) b Cb)
            (List.cons (mkterm (PConst one) sn Bn) List.nil))) ->
        (wenv b = zero ∨ wenv b = one) ∨
        (∃ d : F, genv An = (genv Bn) ^ d).
      Proof.
        intros * h₁ h₂.
        eapply (commit_eq_denote genv penv (Hvec := Hvec)) in h₁.
        eapply (simple_eq_denote genv penv (Hvec := Hvec)) in h₂.
        unfold terms_fold, term_denote in h₂; cbn in h₂.
        rewrite right_identity in h₂.
        rewrite h₁ in h₂.
        rewrite smul_distributive_vadd, !smul_pow_up in h₂.
        rewrite <-associative in h₂.
        rewrite <-smul_distributive_fadd in h₂.
        assert (ha : wenv b * (one * wenv b) = wenv b * wenv b). { field. }
        rewrite ha in h₂.
        destruct (Fdec (wenv b) (wenv b * wenv b)) as [heq | hne].
        +
          left.
          assert (hz : wenv b * (one + opp (wenv b)) = zero).
          { assert (hh : wenv b * (one + opp (wenv b)) =
              wenv b + opp (wenv b * wenv b)). { field. }
            rewrite hh, <-heq. field. }
          destruct (fmul_zero_factor _ _ hz) as [h0 | h1].
          left; exact h0.
          right.
          assert (hh : wenv b = one + opp (one + opp (wenv b))). { field. }
          rewrite hh, h1. field.
        +
          right.
          eapply (two_openings_dlog (Hvec := Hvec)
            (genv An) (genv Bn) (wenv b) (wenv r)
            (wenv b * wenv b) (wenv r * (one * wenv b) + one * wenv sn));
          [exact h₂ | exact hne].
      Qed.

      (** *** The linking equation *)

      (** Multiplying out the bit terms of the link equation.

          The link equation contains one term per indexed weight, and
          all of them share the base [An].  Multiplying them out
          therefore yields [An] raised to a single exponent, namely the
          sum over the list of minus the embedded weight times the bit
          value.  Induction on the list, using the vector space law
          that a product of powers of one base is that base raised to
          the sum of the exponents.

          This lemma is what turns a product of group elements into a
          statement about one field element, so that the rest of the
          argument can stay inside the field. *)
      Lemma range_terms_fold :
        ∀ (An : V) (iws : list (nat * nat)) (wenv : V -> F),
        terms_foldC wenv
          (List.map (fun iw =>
            mkterm (PConst (opp (fnat (snd iw)))) (bb (fst iw)) An) iws) =
        (genv An) ^
          (List.fold_right (fun iw acc =>
            opp (fnat (snd iw)) * wenv (bb (fst iw)) + acc) zero iws).
      Proof.
        induction iws as [|iw iws ih]; intros *;
        unfold terms_fold in *; cbn.
        + rewrite field_zero; reflexivity.
        + rewrite ih.
          rewrite smul_distributive_fadd.
          unfold term_denote; cbn.
          reflexivity.
      Qed.

      (** Negation can be pulled out of the weighted sum: summing minus
          each weighted bit gives minus the sum.  A one-line induction,
          but worth a name of its own, because both the soundness and
          the completeness proof want the sum in its positive form
          while the equation hands it over negated. *)
      Lemma fold_opp_coeff :
        ∀ (iws : list (nat * nat)) (wenv : V -> F),
        List.fold_right (fun iw acc =>
          opp (fnat (snd iw)) * wenv (bb (fst iw)) + acc) zero iws =
        opp (List.fold_right (fun iw acc =>
          fnat (snd iw) * wenv (bb (fst iw)) + acc) zero iws).
      Proof.
        induction iws as [|iw iws ih]; intros *; cbn.
        field.
        rewrite ih. field.
      Qed.

      (** What the link equation tells us about the secret.

          The hypothesis is that the link equation holds in the
          environment [wenv].  By [range_terms_fold] the equation says
          that [An], raised to the value of [x] minus the weighted sum
          of the bits, is the identity.  A power of a point is the
          identity in exactly two ways ([gid_power_zero] of
          Algebra/Vector_space.v): either the point itself is the
          identity, or the exponent is [zero].

          So either [genv An] is [gid], meaning the public base was
          degenerate and the equation was vacuous, or the value of [x]
          really is the weighted sum of the bit values.  The degenerate
          case cannot be excluded here, since nothing in this file
          constrains [genv]; it is passed on to the caller as one
          branch of [range_sound]. *)
      Lemma range_link_sound :
        ∀ (An x : V) (iws : list (nat * nat)) (wenv : V -> F),
        eq_denoteC wenv (range_link An x iws) ->
        (genv An = gid) ∨
        (wenv x = List.fold_right (fun iw acc =>
          fnat (snd iw) * wenv (bb (fst iw)) + acc) zero iws).
      Proof.
        intros * hd.
        unfold eq_denote, range_link in hd; cbn in hd.
        rewrite right_identity in hd.
        pose proof (range_terms_fold An iws wenv) as hf.
        unfold terms_fold in hf; cbn in hf.
        rewrite hf in hd.
        unfold term_denote in hd; cbn in hd.
        rewrite <-smul_distributive_fadd in hd.
        destruct (@gid_power_zero F (@eq F) zero one add mul sub div
          opp inv G (@eq G) gid ginv gop gpow Hvec Fdec _ _ hd) as [hg | hz].
        left; exact hg.
        right.
        rewrite fold_opp_coeff in hz.
        assert (hh : wenv x =
          one * wenv x +
          opp (List.fold_right (fun iw acc =>
            fnat (snd iw) * wenv (bb (fst iw)) + acc) zero iws) +
          List.fold_right (fun iw acc =>
            fnat (snd iw) * wenv (bb (fst iw)) + acc) zero iws).
        { field. }
        rewrite hh, hz. field.
      Qed.

      (** With all the bits genuine, the field-side sum is the image of
          the nat-side sum.

          The hypothesis says that every bit variable mentioned in the
          list takes the value [zero] or [one].  Under that assumption
          each field-side summand, an embedded weight times a bit
          value, equals the embedding of the nat-side product of the
          weight with [bitof] of that value, by [bitof_fnat] and
          [fnat_mul]; and [fnat_add] turns the two sums into one
          another.  Induction on the list does the rest.

          This is the step that moves the argument out of the field,
          where there is no order, into the natural numbers, where a
          bound can actually be proved. *)
      Lemma range_bits_value :
        ∀ (iws : list (nat * nat)) (wenv : V -> F),
        (∀ iw, List.In iw iws ->
          wenv (bb (fst iw)) = zero ∨ wenv (bb (fst iw)) = one) ->
        List.fold_right (fun iw acc =>
          fnat (snd iw) * wenv (bb (fst iw)) + acc) zero iws =
        fnat (List.fold_right (fun iw acc =>
          (snd iw * bitof (wenv (bb (fst iw)))) + acc)%nat 0%nat iws).
      Proof.
        induction iws as [|iw iws ih]; intros * hb; cbn.
        reflexivity.
        rewrite fnat_add, fnat_mul.
        rewrite (bitof_fnat _ (hb iw (or_introl eq_refl))).
        rewrite ih.
        reflexivity.
        intros iw' hin; eapply hb; right; exact hin.
      Qed.

      (** *** Counting on the natural number side

          Five small arithmetic facts adding up to a single statement:
          a weighted sum of genuine bits over [range_weights u] is at
          most [u - 1]. *)

      (** Folding addition over a list starting from a value [b] gives
          the same result as folding from [0] and adding [b] at the
          end.  Plain associativity and commutativity of addition,
          stated on its own so that later proofs can split a fold over
          an appended list. *)
      Lemma fold_add_base : ∀ (l : list nat) (b : nat),
        (List.fold_right Nat.add b l = List.fold_right Nat.add 0 l + b)%nat.
      Proof.
        induction l as [|a l ih]; intros *; cbn.
        lia.
        rewrite ih; lia.
      Qed.

      (** The powers of two indexed by [0] up to [m - 1] add up to
          [Nat.pow 2 m - 1].  The familiar identity, by induction on
          [m] with the list built by [List.seq].  It is what makes the
          last weight of [range_weights] come out right: the powers
          already cover every value strictly below
          [Nat.pow 2 (Nat.log2 u)]. *)
      Lemma pow2_sum : ∀ (m : nat),
        (List.fold_right Nat.add 0
          (List.map (fun i => Nat.pow 2 i) (List.seq 0 m)) = Nat.pow 2 m - 1)%nat.
      Proof.
        induction m as [|m ih].
        reflexivity.
        rewrite List.seq_S, List.map_app, List.fold_right_app.
        cbn.
        rewrite fold_add_base, ih.
        assert (hp : Nat.pow 2 m <> 0%nat).
        eapply PeanoNat.Nat.pow_nonzero; lia.
        cbn [Nat.pow].
        lia.
      Qed.

      (** A weighted sum of bits never exceeds the sum of the weights,
          because every [bitof] value is at most [1].  Induction on the
          list, with the per-element bound obtained by case analysis on
          the decidable test inside [bitof].  This is the inequality
          that actually bounds the secret. *)
      Lemma sum_mono :
        ∀ (iws : list (nat * nat)) (wenv : V -> F),
        (List.fold_right (fun iw acc =>
          (snd iw * bitof (wenv (bb (fst iw)))) + acc)%nat 0%nat iws <=
        List.fold_right (fun iw acc => (snd iw + acc)%nat) 0%nat iws)%nat.
      Proof.
        induction iws as [|iw iws ih]; intros *; cbn.
        lia.
        pose proof (ih wenv).
        assert (hb : (bitof (wenv (bb (fst iw))) <= 1)%nat).
        unfold bitof; destruct (Fdec (wenv (bb (fst iw))) zero); lia.
        nia.
      Qed.

      (** Pairing a list of weights with consecutive indices and then
          adding up the second components gives back the plain sum of
          the weights.  Bookkeeping: it says [indexed_weights] carries
          the same total as [range_weights], so a bound proved for one
          applies to the other. *)
      Lemma snd_fold_combine :
        ∀ (ws : list nat) (a : nat),
        (List.fold_right (fun iw acc => (snd iw + acc)%nat) 0%nat
          (List.combine (List.seq a (List.length ws)) ws) =
        List.fold_right Nat.add 0%nat ws)%nat.
      Proof.
        induction ws as [|w ws ih]; intros *; cbn.
        reflexivity.
        rewrite ih.
        reflexivity.
      Qed.

      (** The weights add up to exactly [u - 1], provided the bound [u]
          is at least [2].

          By [pow2_sum] the powers of two contribute
          [Nat.pow 2 (Nat.log2 u) - 1], and the final remainder weight
          contributes [u - Nat.pow 2 (Nat.log2 u)]; the two add to
          [u - 1].  The specification of [Nat.log2] is what guarantees
          the remainder does not underflow, that is, that
          [Nat.pow 2 (Nat.log2 u)] is at most [u].

          Together with [sum_mono] this is the arithmetic heart of
          soundness: genuine bits can represent every value from [0] to
          [u - 1], and nothing beyond. *)
      Lemma weights_sum : ∀ (u : nat),
        (2 <= u)%nat ->
        (List.fold_right Nat.add 0 (range_weights u) = u - 1)%nat.
      Proof.
        intros * hu.
        unfold range_weights.
        rewrite List.fold_right_app.
        cbn.
        rewrite fold_add_base, pow2_sum.
        destruct (PeanoNat.Nat.log2_spec u) as (hl & hr); [lia |].
        assert (hp : Nat.pow 2 (Nat.log2 u) <> 0%nat).
        eapply PeanoNat.Nat.pow_nonzero; lia.
        lia.
      Qed.

      (** *** Assembling soundness *)

      (** If a property holds of every element produced by a
          [List.flat_map], then it holds of every element of the block
          produced by any one input.  It is used to pull the two
          equations belonging to a single bit out of the flat list of
          all the bit equations of the statement. *)
      Lemma forall_flat_map_in :
        ∀ (A B : Type) (P : B -> Prop) (f : A -> list B) (l : list A) (a : A),
        List.Forall P (List.flat_map f l) ->
        List.In a l ->
        List.Forall P (f a).
      Proof.
        intros * hf hin.
        rewrite List.Forall_forall in hf.
        rewrite List.Forall_forall.
        intros b hb.
        eapply hf.
        eapply List.in_flat_map.
        exists a; exact (conj hin hb).
      Qed.

      (** When the search finds no bad bit, every bit is genuine: for
          every indexed weight in the list, the bit variable takes the
          value [zero] or [one].  Induction on the list, following the
          two decidable tests inside [find_nonbit]. *)
      Lemma find_nonbit_none :
        ∀ (l : list (nat * nat)) (wenv : V -> F),
        find_nonbit wenv l = None ->
        ∀ iw, List.In iw l ->
        wenv (bb (fst iw)) = zero ∨ wenv (bb (fst iw)) = one.
      Proof.
        induction l as [|iw l ih]; intros * hf iw' hin.
        destruct hin.
        cbn in hf.
        destruct (Fdec (wenv (bb (fst iw))) zero) as [h0 | h0].
        +
          destruct hin as [hin | hin].
          subst; left; exact h0.
          eapply ih; eauto.
        +
          destruct (Fdec (wenv (bb (fst iw))) one) as [h1 | h1];
          [| congruence].
          destruct hin as [hin | hin].
          subst; right; exact h1.
          eapply ih; eauto.
      Qed.

      (** When the search does return a pair, that pair really occurs in
          the list, and its bit variable really takes a value that is
          neither [zero] nor [one].  Induction on the list again.
          Together with [find_nonbit_none] this pair of lemmas is a
          complete specification of the search, so no proof below ever
          has to unfold it. *)
      Lemma find_nonbit_some :
        ∀ (l : list (nat * nat)) (wenv : V -> F) (iw : nat * nat),
        find_nonbit wenv l = Some iw ->
        List.In iw l ∧
        wenv (bb (fst iw)) <> zero ∧
        wenv (bb (fst iw)) <> one.
      Proof.
        induction l as [|iw₀ l ih]; intros * hf; cbn in hf.
        congruence.
        destruct (Fdec (wenv (bb (fst iw₀))) zero).
        +
          destruct (ih _ _ hf) as (ha & hb & hc).
          split; [right; exact ha | exact (conj hb hc)].
        +
          destruct (Fdec (wenv (bb (fst iw₀))) one).
          ++
            destruct (ih _ _ hf) as (ha & hb & hc).
            split; [right; exact ha | exact (conj hb hc)].
          ++
            injection hf as hf; subst.
            split; [left; reflexivity | eauto].
      Qed.

      (** ** Soundness of the range gadget

          Soundness is the promise made to the verifier: if the
          equations hold, then something real has been proved.  Here
          that promise takes the form of a three-way dichotomy.

          The hypotheses are that the bound [u] is at least [2], so
          that the interval is not trivial and [Nat.log2 u] behaves,
          and that the witness environment [wenv] satisfies the whole
          lowered statement [range_stmt An Bn x u] under the public
          environments [genv] and [penv].

          The conclusion is that one of three things holds.

          - There is a natural number [k] below [u] with
            [wenv x = fnat k].  This is the good case, and the only
            faithful way to say that [x] is in range over a field with
            no order.
          - [genv An] is [gid].  The public base [An] is the group
            identity, so every equation over that base holds
            vacuously.  This means the setup was broken, not that the
            prover cheated; a verifier rules it out once, in advance,
            when it checks the bases.
          - There is a [d] with [genv An] equal to [genv Bn] raised to
            [d].  This is a discrete logarithm relating the two
            Pedersen bases, and producing one is assumed to be
            infeasible.  It shows up because a cheating prover who
            opens one commitment in two different ways hands it over.

          Why the theorem is true.  Run [find_nonbit] over the indexed
          weights.  If it returns a pair, the two equations of that bit
          give, by [bit_dichotomy], either that its value is [zero] or
          [one], contradicting what the search reported, or a discrete
          logarithm: the third branch.  If it returns nothing, every
          bit is genuine, so [range_link_sound] gives either the
          degenerate base, the second branch, or that [wenv x] is the
          weighted bit sum.  In that last case [range_bits_value]
          rewrites the sum as [fnat] of a nat-side sum, and [sum_mono]
          together with [weights_sum] bounds that sum by [u - 1]: the
          first branch. *)
      Theorem range_sound :
        ∀ (An Bn x : V) (u : nat) (wenv : V -> F),
        (2 <= u)%nat ->
        stmt_denoteC wenv (range_stmt An Bn x u) ->
        (∃ k : nat, (k < u)%nat ∧ wenv x = fnat k) ∨
        (genv An = gid) ∨
        (∃ d : F, genv An = (genv Bn) ^ d).
      Proof.
        intros * hu hd.
        cbn in hd.
        inversion hd as [| ? ? hlink hbits]; subst.
        destruct (find_nonbit wenv (indexed_weights u)) eqn:hf.
        +
          destruct (find_nonbit_some _ _ _ hf) as (hin & hnz & hno).
          pose proof (forall_flat_map_in _ _ _ _ _ _ hbits hin) as hbe.
          inversion hbe as [| ? ? he₁ hbe']; subst.
          inversion hbe' as [| ? ? he₂ hnil]; subst.
          destruct (bit_dichotomy _ _ _ _ _ _ wenv he₁ he₂)
            as [[h0 | h1] | hdlog].
          exfalso; eapply hnz; exact h0.
          exfalso; eapply hno; exact h1.
          right; right; exact hdlog.
        +
          destruct (range_link_sound _ _ _ _ hlink) as [hg | hv].
          right; left; exact hg.
          left.
          pose proof (find_nonbit_none _ _ hf) as hgood.
          rewrite (range_bits_value _ _ hgood) in hv.
          eexists; split; [| exact hv].
          pose proof (sum_mono (indexed_weights u) wenv) as hm.
          pose proof (snd_fold_combine (range_weights u) 0) as hsf.
          pose proof (weights_sum u hu) as hws.
          unfold indexed_weights in *.
          lia.
      Qed.

    End Proofs.

  End Spec.

  (** ** Completeness

      The completeness argument has to instantiate the lemmas of the
      soundness section at a different point environment, an extended
      one in which the freshly published bit commitments have values.
      A section variable cannot be changed once it is fixed, so the
      section above is closed first and completeness is given a
      section of its own. *)
  Section Completeness.

    (** The public environments the honest prover starts from: [genv]
        for points and [penv] for public scalars.  The proof below
        builds an extended [genv'] that agrees with [genv] everywhere
        except at the new commitment points. *)
    Variable genv : V -> G.
    Variable penv : V -> F.

    (** As in the soundness section, the group and the field must fit
        together as a vector space, and the [field] tactic is armed for
        routine identities. *)
    Context
      {Hvec : @vector_space F (@eq F) zero one add mul sub
        div opp inv G (@eq G) gid ginv gop gpow}.
    Add Field field : (@field_theory_for_stdlib_tactic F
      eq zero one opp add mul sub inv div vector_space_field).

    (** The plan.  First show that every natural number below [u] has a
        bit vector for the weights of [range_weights u].  Then define
        the extended environments that assign those bits, the zero
        randomness and the commitment points to the gadget's names.
        Then check each equation of [range_stmt] by hand. *)

    (** *** Every value below the bound has a bit vector *)

    (** The little-endian binary digits of [m], exactly [n] of them:
        the head is [1] when [m] is odd and [0] otherwise, and the tail
        holds the digits of [m] halved.  Digits beyond the size of [m]
        come out as [0], and digits of [m] above position [n] are
        simply dropped, which is why a bound on [m] is needed in
        [nbits_value]. *)
    Fixpoint nbits (n m : nat) : list nat :=
      match n with
      | 0 => List.nil
      | S n' => List.cons (if Nat.odd m then 1 else 0) (nbits n' (Nat.div2 m))
      end.

    (** The nat-side weighted sum.  Given a list of bits [bs] and a
        list of indexed weights [iws], add up, for each pair [(i, w)]
        in [iws], the weight [w] times the [i]-th entry of [bs].  Bits
        are looked up by index rather than consumed in order, which
        mirrors the way the gadget reads the bit [bb i] out of the
        environment.  A missing entry counts as [0]. *)
    Definition iwsum (bs : list nat) (iws : list (nat * nat)) : nat :=
      List.fold_right (fun iw acc => (snd iw * List.nth (fst iw) bs 0 + acc)%nat)
        0%nat iws.

    (** [nbits n m] has exactly [n] entries, by construction.  Needed
        because the list of bits has to line up with the list of
        weights. *)
    Lemma nbits_length : ∀ n m, List.length (nbits n m) = n.
    Proof.
      induction n as [|n ih]; intro m; cbn; [reflexivity | rewrite ih; reflexivity].
    Qed.

    (** Every entry of [nbits n m] is at most [1], that is, really a
        bit.  Immediate from the shape of the definition, but it is one
        of the three things [range_bits_exist] has to deliver. *)
    Lemma nbits_le1 : ∀ n m, List.Forall (fun b => (b <= 1)%nat) (nbits n m).
    Proof.
      induction n as [|n ih]; intro m; cbn; [constructor |].
      constructor; [destruct (Nat.odd m); lia | eapply ih].
    Qed.

    (** Shifting every index up by one and doubling every weight
        doubles the sum, once a new bit is pushed onto the front of the
        bit list.  Pushing a bit renumbers all the old bits, and
        doubling the weights is the other half of moving one binary
        place; the new head bit contributes nothing here because no
        pair in the shifted list refers to index [0].  This is the
        induction step of [nbits_value]. *)
    Lemma iwsum_shift :
      ∀ (b : nat) (bl : list nat) (is ws : list nat),
      iwsum (List.cons b bl)
        (List.combine (List.map S is) (List.map (fun w => 2 * w)%nat ws)) =
      (2 * iwsum bl (List.combine is ws))%nat.
    Proof.
      intros b bl is.
      induction is as [|i is ih]; intros [|w ws]; cbn; try lia.
      unfold iwsum in ih |- *; cbn.
      rewrite ih. lia.
    Qed.

    (** The binary digits really represent the number: for [m] below
        [Nat.pow 2 n], the weighted sum of [nbits n m] against the
        weights [1], [2], [4] and so on, each paired with its own
        index, is [m] itself.

        Induction on [n].  The head digit contributes the parity of
        [m]; the tail is the representation of [m] halved against the
        same weights doubled and shifted, which is [iwsum_shift]; and
        [Nat.div2_odd] puts the two halves back together.  The bound on
        [m] is what guarantees that nothing is dropped off the top. *)
    Lemma nbits_value :
      ∀ (n m : nat), (m < Nat.pow 2 n)%nat ->
      iwsum (nbits n m)
        (List.combine (List.seq 0 n) (List.map (fun i => Nat.pow 2 i) (List.seq 0 n)))
      = m.
    Proof.
      induction n as [|n ih]; intros m hm.
      +
        cbn in hm. assert (m = 0)%nat by lia. subst. reflexivity.
      +
        cbn [nbits].
        change (List.seq 0 (S n)) with (List.cons 0 (List.seq 1 n)).
        rewrite <-List.seq_shift.
        assert (hmap : List.map (fun i => Nat.pow 2 i) (List.map S (List.seq 0 n)) =
          List.map (fun w => 2 * w)%nat (List.map (fun i => Nat.pow 2 i) (List.seq 0 n))).
        { rewrite !List.map_map. eapply List.map_ext. intro i. cbn [Nat.pow]. lia. }
        cbn [List.map] in hmap |- *.
        rewrite hmap.
        assert (hcons : ∀ bl i w iws,
          iwsum bl (List.cons (i, w) iws) = (w * List.nth i bl 0 + iwsum bl iws)%nat).
        { intros; reflexivity. }
        cbn [List.combine].
        rewrite hcons.
        rewrite iwsum_shift.
        assert (hd : (Nat.div2 m < Nat.pow 2 n)%nat).
        { pose proof (Nat.div2_odd m) as hs; cbn [Nat.pow] in hm.
          destruct (Nat.odd m); cbn [Nat.b2n] in hs; lia. }
        rewrite (ih _ hd).
        pose proof (Nat.div2_odd m) as hs.
        cbn [List.nth Nat.pow].
        destruct (Nat.odd m); cbn [Nat.b2n] in hs; lia.
    Qed.

    (** The weighted sum over an appended list of indexed weights splits
        as the sum over the two parts.  The bit list is shared between
        the two halves, which is exactly why the sum is defined by
        index lookup rather than by consuming bits one at a time. *)
    Lemma iwsum_app :
      ∀ (bl : list nat) (l₁ l₂ : list (nat * nat)),
      iwsum bl (List.app l₁ l₂) = (iwsum bl l₁ + iwsum bl l₂)%nat.
    Proof.
      intros; unfold iwsum; rewrite List.fold_right_app.
      induction l₁ as [|iw l₁ ih]; cbn; [reflexivity | rewrite ih; lia].
    Qed.

    (** The weighted sum looks at the bit list only through the indices
        mentioned in [iws]: two bit lists agreeing at all those
        positions give the same sum.  It is used to ignore a bit
        appended at the end while summing over the earlier
        positions. *)
    Lemma iwsum_ext :
      ∀ (bl₁ bl₂ : list nat) (iws : list (nat * nat)),
      (∀ iw, List.In iw iws -> List.nth (fst iw) bl₁ 0 = List.nth (fst iw) bl₂ 0) ->
      iwsum bl₁ iws = iwsum bl₂ iws.
    Proof.
      intros bl₁ bl₂ iws h.
      induction iws as [|iw iws ih]; cbn; [reflexivity |].
      unfold iwsum in ih |- *; cbn.
      rewrite (h iw (or_introl eq_refl)), ih; [reflexivity |].
      intros iw' hin; eapply h; right; exact hin.
    Qed.

    (** Zipping two equally long lists, each with one extra element
        appended, is the same as zipping them and appending the extra
        pair.  Pure list bookkeeping, needed because [range_weights]
        is built with the remainder weight appended at the end. *)
    Lemma combine_app_last :
      ∀ (l₁ ws : list nat) (a w : nat),
      List.length l₁ = List.length ws ->
      List.combine (List.app l₁ (List.cons a List.nil)) (List.app ws (List.cons w List.nil)) =
      List.app (List.combine l₁ ws) (List.cons (a, w) List.nil).
    Proof.
      induction l₁ as [|i l₁ ih]; intros [|w' ws] a w hl; cbn in hl |- *; try lia.
      + reflexivity.
      + rewrite ih; [reflexivity | lia].
    Qed.

    (** Peeling off the last weight.  If the weight list and the bit
        list both have length [m], then summing over the [m + 1]
        indexed weights obtained by appending a last weight [r] and a
        last bit [b] gives the sum over the first [m], plus [r] times
        [b].  It follows from [combine_app_last], [iwsum_app] and
        [iwsum_ext]: the earlier pairs mention only indices below [m],
        where the extended bit list still agrees with the original.

        This is where the special last weight of [range_weights] is
        handled on the completeness side. *)
    Lemma iwsum_app_last :
      ∀ (bl ws : list nat) (b r m : nat),
      List.length ws = m -> List.length bl = m ->
      iwsum (List.app bl (List.cons b List.nil))
        (List.combine (List.seq 0 (S m)) (List.app ws (List.cons r List.nil))) =
      (iwsum bl (List.combine (List.seq 0 m) ws) + r * b)%nat.
    Proof.
      intros bl ws b r m hws hbl.
      rewrite List.seq_S; cbn [Nat.add].
      rewrite combine_app_last; [| rewrite List.length_seq; lia].
      rewrite iwsum_app.
      unfold iwsum at 2; cbn.
      rewrite List.app_nth2; [| lia].
      rewrite hbl, Nat.sub_diag; cbn.
      f_equal; [| lia].
      eapply iwsum_ext.
      intros iw hin.
      destruct iw as (i & w'); cbn.
      eapply List.in_combine_l in hin.
      eapply List.in_seq in hin.
      rewrite List.app_nth1; [reflexivity | lia].
    Qed.

    (** Every value below the bound is representable.

        For [2 <= u] and [k < u] there is a bit list [bl] with one
        entry per weight, every entry at most [1], whose weighted sum
        over [indexed_weights u] is exactly [k].

        The construction splits on whether [k] is below
        [Nat.pow 2 (Nat.log2 u)].  If it is, take the ordinary binary
        digits of [k] and set the last bit, the one carrying the
        remainder weight, to [0].  If it is not, set that last bit to
        [1], which accounts for the remainder
        [u - Nat.pow 2 (Nat.log2 u)], and take the binary digits of
        what is left over, which the specification of [Nat.log2] shows
        is still below [Nat.pow 2 (Nat.log2 u)].  In both cases
        [nbits_value] evaluates the leading part and [iwsum_app_last]
        adds the final contribution.

        This lemma is the exact converse of the counting argument used
        for soundness.  Together the two say that the representable
        values are precisely [0] up to [u - 1]. *)
    Lemma range_bits_exist :
      ∀ (u k : nat), (2 <= u)%nat -> (k < u)%nat ->
      ∃ bl : list nat,
        List.length bl = List.length (range_weights u) ∧
        List.Forall (fun b => (b <= 1)%nat) bl ∧
        iwsum bl (indexed_weights u) = k.
    Proof.
      intros u k hu hk.
      set (ml := Nat.log2 u).
      set (r := (u - Nat.pow 2 ml)%nat).
      destruct (PeanoNat.Nat.log2_spec u) as (hl & hr); [lia |].
      fold ml in hl, hr.
      assert (hlen : List.length (range_weights u) = S ml).
      { unfold range_weights.
        rewrite List.length_app, List.length_map, List.length_seq. cbn. lia. }
      unfold indexed_weights. rewrite hlen.
      destruct (Nat.lt_ge_cases k (Nat.pow 2 ml)) as [hsmall | hbig].
      +
        exists (List.app (nbits ml k) (List.cons 0 List.nil)).
        split; [rewrite List.length_app, nbits_length; cbn; lia |].
        split; [eapply List.Forall_app; split;
                [eapply nbits_le1 | constructor; [lia | constructor]] |].
        unfold range_weights. fold ml. fold r.
        rewrite iwsum_app_last;
        [| rewrite List.length_map, List.length_seq; reflexivity | eapply nbits_length].
        rewrite nbits_value; [lia | exact hsmall].
      +
        assert (hkr : (k - r < Nat.pow 2 ml)%nat). { unfold r. cbn [Nat.pow] in hr. lia. }
        exists (List.app (nbits ml (k - r)) (List.cons 1 List.nil)).
        split; [rewrite List.length_app, nbits_length; cbn; lia |].
        split; [eapply List.Forall_app; split;
                [eapply nbits_le1 | constructor; [lia | constructor]] |].
        unfold range_weights. fold ml. fold r.
        rewrite iwsum_app_last;
        [| rewrite List.length_map, List.length_seq; reflexivity | eapply nbits_length].
        rewrite nbits_value; [| exact hkr].
        unfold r. cbn [Nat.pow] in hr. lia.
    Qed.

    (** *** Extending the environments at the new names

        An environment is a total function from names to values, so
        publishing the bit commitments means building a new function
        that agrees with the old one except at finitely many names. *)

    (** [upd w kvs] is the environment [w] updated at the names listed
        in [kvs]: looking up a name returns the value paired with it in
        [kvs] when there is one, and [w] of that name otherwise.  It is
        generic in the value type [T] so that one definition serves
        both the scalar environment and the point environment.  Earlier
        pairs shadow later ones, which is harmless here because the key
        lists are duplicate free. *)
    Definition upd {T : Type} (w : V -> T) (kvs : list (V * T)) : V -> T :=
      List.fold_right (fun kv w' => fun z => if veqb z (fst kv) then snd kv else w' z)
        w kvs.

    (** An update changes nothing at a name that is not among its keys.
        This is what makes the "agrees with the old environment outside
        the new names" clauses of [range_complete] true, and it is also
        how the proof knows that the bases [An] and [Bn] and the secret
        [x] keep the values they already had. *)
    Lemma upd_notin :
      ∀ {T : Type} (w : V -> T) (kvs : list (V * T)) (v : V),
      ~ List.In v (List.map fst kvs) -> upd w kvs v = w v.
    Proof.
      intros T w kvs v.
      induction kvs as [|kv kvs ih]; intro hnin; cbn.
      + reflexivity.
      + unfold Dsl.veqb.
        destruct (vdec v (fst kv)) as [heq | hne].
        - exfalso; eapply hnin; left; symmetry; exact heq.
        - eapply ih; intro hin; eapply hnin; right; exact hin.
    Qed.

    (** An update returns the listed value at a listed name, provided
        the keys are duplicate free so that no earlier pair shadows the
        one we are after.  This is how the proof reads back the values
        it has just installed. *)
    Lemma upd_in :
      ∀ {T : Type} (w : V -> T) (kvs : list (V * T)) (k : V) (val : T),
      List.NoDup (List.map fst kvs) -> List.In (k, val) kvs -> upd w kvs k = val.
    Proof.
      intros T w kvs k val.
      induction kvs as [|kv kvs ih]; intros hnd hin; cbn in hin |- *.
      + contradiction.
      + inversion hnd as [| ? ? hnin hnd']; subst.
        unfold Dsl.veqb.
        destruct hin as [hin | hin].
        - subst kv; cbn. destruct (vdec k k); [reflexivity | congruence].
        - destruct (vdec k (fst kv)) as [heq | hne].
          * exfalso; eapply hnin. rewrite <-heq.
            eapply List.in_map with (f := fst) in hin. exact hin.
          * eapply ih; assumption.
    Qed.

    (** All the secret-side names the gadget introduces for the first
        [n] bits: for each index, the bit itself, its commitment
        randomness and its squaring scalar.  They are collected into
        one list so that freshness can be stated once, as a single
        [List.NoDup] hypothesis of [range_complete]. *)
    Definition bit_names (n : nat) : list V :=
      List.flat_map (fun i => List.cons (bb i) (List.cons (br i) (List.cons (bs i) List.nil)))
        (List.seq 0 n).

    (** Membership in [bit_names n] spelled out: a name belongs to the
        list exactly when it is [bb i], [br i] or [bs i] for some index
        [i] below [n].  A convenience, so that later proofs never have
        to unfold the [List.flat_map]. *)
    Lemma in_bit_names :
      ∀ (n : nat) (v : V),
      List.In v (bit_names n) <->
      ∃ i, (i < n)%nat ∧ (v = bb i ∨ v = br i ∨ v = bs i).
    Proof.
      intros n v; unfold bit_names.
      rewrite List.in_flat_map.
      split.
      + intros (i & hi & hv). eapply List.in_seq in hi.
        exists i; split; [lia |].
        destruct hv as [hv | [hv | [hv | []]]]; subst; auto.
      + intros (i & hi & hv).
        exists i; split; [eapply List.in_seq; lia |].
        destruct hv as [hv | [hv | hv]]; subst; cbn; auto.
    Qed.

    (** The values the honest prover assigns to those names: bit number
        [i] is set to the embedding of the [i]-th entry of [bs0], and
        both its randomness and its squaring scalar are set to [zero].

        Randomness [zero] is acceptable here because this file proves
        completeness, not zero knowledge; hiding the committed value is
        the concern of the protocol layer, which supplies real
        randomness.  The squaring scalar is [zero] because with a
        genuine bit the second equation already balances without
        it. *)
    Definition bit_values (bs0 : list nat) (n : nat) : list (V * F) :=
      List.flat_map (fun i =>
        List.cons (bb i, fnat (List.nth i bs0 0))
          (List.cons (br i, zero) (List.cons (bs i, zero) List.nil)))
        (List.seq 0 n).

    (** The commitment points the honest prover publishes: for each
        index [i], the name [bC i] is mapped to [An] raised to the
        embedded bit, times [Bn] raised to [zero].  These are exactly
        the values the first equation of [bit_eqs] demands, so that
        equation then holds by construction. *)
    Definition bit_points (An Bn : V) (bs0 : list nat) (n : nat) : list (V * G) :=
      List.map (fun i => (bC i, gop ((genv An) ^ (fnat (List.nth i bs0 0))) ((genv Bn) ^ zero)))
        (List.seq 0 n).

    (** The keys of [bit_values] are precisely [bit_names], since the
        two lists are built by the same traversal.  This is what lets
        the single freshness hypothesis about [bit_names] discharge the
        duplicate-freeness side condition of [upd_in]. *)
    Lemma bit_values_fst :
      ∀ (bl : list nat) (n : nat), List.map fst (bit_values bl n) = bit_names n.
    Proof.
      intros bl n; unfold bit_values, bit_names.
      induction (List.seq 0 n) as [|i l ih]; cbn; [reflexivity | rewrite ih; reflexivity].
    Qed.

    (** For an index below [n], all three of its pairs really occur in
        [bit_values]: the bit with its embedded value, the randomness
        with [zero], and the squaring scalar with [zero].  These are
        fed to [upd_in] to read the values back out. *)
    Lemma in_bit_values :
      ∀ (bl : list nat) (n i : nat), (i < n)%nat ->
      List.In (bb i, fnat (List.nth i bl 0)) (bit_values bl n) ∧
      List.In (br i, zero) (bit_values bl n) ∧
      List.In (bs i, zero) (bit_values bl n).
    Proof.
      intros bl n i hi.
      assert (hin : List.In i (List.seq 0 n)). { eapply List.in_seq; lia. }
      unfold bit_values.
      repeat split; eapply List.in_flat_map; exists i; split; try exact hin.
      + left; reflexivity.
      + right; left; reflexivity.
      + right; right; left; reflexivity.
    Qed.

    (** The keys of [bit_points] are the commitment names [bC i] for
        [i] below [n].  Stated so that the caller's duplicate-freeness
        hypothesis about those names transfers to the key list. *)
    Lemma bit_points_fst :
      ∀ (An Bn : V) (bl : list nat) (n : nat),
      List.map fst (bit_points An Bn bl n) = List.map bC (List.seq 0 n).
    Proof.
      intros; unfold bit_points; rewrite List.map_map; reflexivity.
    Qed.

    (** For an index below [n], the pair naming that bit's commitment
        point really occurs in [bit_points].  The counterpart of
        [in_bit_values] on the group side. *)
    Lemma in_bit_points :
      ∀ (An Bn : V) (bl : list nat) (n i : nat), (i < n)%nat ->
      List.In (bC i, gop ((genv An) ^ (fnat (List.nth i bl 0))) ((genv Bn) ^ zero))
        (bit_points An Bn bl n).
    Proof.
      intros An Bn bl n i hi.
      unfold bit_points.
      eapply List.in_map_iff.
      exists i; split; [reflexivity |].
      eapply List.in_seq; lia.
    Qed.

    (** The field-side weighted sum computes the embedding of the
        nat-side one, as long as the environment assigns to each bit
        variable the embedding of the corresponding entry of the bit
        list.  Induction on the list of indexed weights, using
        [fnat_add] and [fnat_mul] at each step.

        It plays for completeness the role that [range_bits_value]
        plays for soundness, but under a stronger hypothesis: here we
        know the exact value of every bit, not merely that it is [zero]
        or [one]. *)
    Lemma fold_fnat_iwsum :
      ∀ (w : V -> F) (bl : list nat) (iws : list (nat * nat)),
      (∀ iw, List.In iw iws -> w (bb (fst iw)) = fnat (List.nth (fst iw) bl 0)) ->
      List.fold_right (fun iw acc => fnat (snd iw) * w (bb (fst iw)) + acc) zero iws =
      fnat (iwsum bl iws).
    Proof.
      intros w bl iws h.
      induction iws as [|iw iws ih]; cbn; [reflexivity |].
      unfold iwsum in ih |- *; cbn.
      rewrite fnat_add, fnat_mul, (h iw (or_introl eq_refl)), ih; [reflexivity |].
      intros iw' hin; eapply h; right; exact hin.
    Qed.

    (** Multiplying out a non-empty list of terms peels off the head: it
        is the head term's value times the product of the rest.  True
        by definition; it is stated as a lemma only so that it can be
        used as a rewriting step with the environments spelled out
        explicitly. *)
    Lemma terms_fold_cons :
      ∀ (g : V -> G) (w : V -> F) (t : @term F V) (ts : list (@term F V)),
      @terms_fold F add mul opp G gid gop gpow V g penv w (List.cons t ts) =
      gop (@term_denote F add mul opp G gpow V g penv w t)
          (@terms_fold F add mul opp G gid gop gpow V g penv w ts).
    Proof. reflexivity. Qed.

    (** ** Completeness of the range gadget

        Completeness is the promise made to the prover: someone who
        really knows a small secret can satisfy the equations.

        The hypotheses are that the bound [u] is at least [2], that
        there is a natural number [k] below [u] with [wenv x = fnat k],
        and three freshness conditions: the secret name [x] together
        with all the per-bit secret names are pairwise different, the
        commitment names [bC i] are pairwise different, and no
        commitment name collides with either Pedersen base.  Together
        they say that publishing the gadget's names disturbs nothing
        that was already there.

        The conclusion produces an extended point environment [genv']
        and an extended witness environment [wenv'] such that

        - [genv'] agrees with [genv] away from the commitment names, so
          only the freshly published points are new;
        - [wenv'] agrees with [wenv] away from the per-bit names, so in
          particular the secret [x] keeps its value;
        - the whole lowered statement holds under [genv'] and [wenv'].

        Why it is true.  By [range_bits_exist] the number [k] has a bit
        list for the range weights.  Set each bit variable to the
        embedding of its bit, each randomness and squaring scalar to
        [zero], and each commitment point to [An] raised to the bit
        times [Bn] raised to [zero].  The link equation then reduces,
        by [range_terms_fold] and [fold_fnat_iwsum], to [An] raised to
        [fnat k] minus [fnat k], which is the identity.  The first
        equation of each bit holds because the point was defined to be
        exactly that commitment.  The second holds by a two-case
        computation: with the bit [zero] both sides collapse to the
        identity, and with the bit [one] the point raised to [one] is
        the point itself. *)
    Theorem range_complete :
      ∀ (An Bn x : V) (u k : nat) (wenv : V -> F),
      (2 <= u)%nat -> (k < u)%nat -> wenv x = fnat k ->
      List.NoDup (List.cons x (bit_names (List.length (range_weights u)))) ->
      List.NoDup (List.map bC (List.seq 0 (List.length (range_weights u)))) ->
      (∀ i, (i < List.length (range_weights u))%nat -> bC i <> An ∧ bC i <> Bn) ->
      ∃ (genv' : V -> G) (wenv' : V -> F),
        (∀ P, ~ List.In P (List.map bC (List.seq 0 (List.length (range_weights u)))) ->
           genv' P = genv P) ∧
        (∀ v, ~ List.In v (bit_names (List.length (range_weights u))) ->
           wenv' v = wenv v) ∧
        @stmt_denote F add mul opp G gid gop gpow V genv' penv wenv'
          (range_stmt An Bn x u).
    Proof.
      intros An Bn x u k wenv hu hk hx hnd hndC hAB.
      set (n := List.length (range_weights u)) in *.
      destruct (range_bits_exist u k hu hk) as (bl & hlen & hbits & hsum).
      fold n in hlen.
      set (genv' := upd genv (bit_points An Bn bl n)).
      set (wenv' := upd wenv (bit_values bl n)).
      assert (hndv : List.NoDup (List.map fst (bit_values bl n))).
      { rewrite bit_values_fst. inversion hnd; assumption. }
      assert (hndp : List.NoDup (List.map fst (bit_points An Bn bl n))).
      { rewrite bit_points_fst; exact hndC. }
      assert (hxnew : ~ List.In x (bit_names n)).
      { inversion hnd; assumption. }
      assert (hwx : wenv' x = fnat k).
      { unfold wenv'. rewrite upd_notin; [exact hx | rewrite bit_values_fst; exact hxnew]. }
      (* A and B are not among the freshly published points *)
      assert (hgA : genv' An = genv An).
      { unfold genv'. eapply upd_notin. rewrite bit_points_fst.
        intro hin. eapply List.in_map_iff in hin.
        destruct hin as (i & heq & hi). eapply List.in_seq in hi.
        destruct (hAB i ltac:(lia)) as (h1 & _). eapply h1; exact heq. }
      assert (hgB : genv' Bn = genv Bn).
      { unfold genv'. eapply upd_notin. rewrite bit_points_fst.
        intro hin. eapply List.in_map_iff in hin.
        destruct hin as (i & heq & hi). eapply List.in_seq in hi.
        destruct (hAB i ltac:(lia)) as (_ & h2). eapply h2; exact heq. }
      (* the value of every bit variable and point in the new environments *)
      assert (hbit : ∀ i, (i < n)%nat ->
        wenv' (bb i) = fnat (List.nth i bl 0) ∧ wenv' (br i) = zero ∧ wenv' (bs i) = zero ∧
        genv' (bC i) = gop ((genv An) ^ (fnat (List.nth i bl 0))) ((genv Bn) ^ zero)).
      { intros i hi.
        destruct (in_bit_values bl n i hi) as (h1 & h2 & h3).
        unfold wenv', genv'.
        repeat split.
        - eapply upd_in; assumption.
        - eapply upd_in; assumption.
        - eapply upd_in; assumption.
        - eapply upd_in; [exact hndp | eapply in_bit_points; exact hi]. }
      assert (hidx : ∀ iw, List.In iw (indexed_weights u) -> (fst iw < n)%nat).
      { intros iw hin. unfold indexed_weights in hin.
        destruct iw as [i w]; cbn [fst].
        eapply List.in_combine_l in hin.
        eapply List.in_seq in hin. lia. }
      exists genv', wenv'.
      split; [| split].
      + intros P hP. unfold genv'. eapply upd_notin. rewrite bit_points_fst. exact hP.
      + intros v hv. unfold wenv'. eapply upd_notin. rewrite bit_values_fst. exact hv.
      + cbn [range_stmt stmt_denote].
        constructor.
        - (* the link equation: A^x · Π A^{-wᵢ bᵢ} = 1 *)
          unfold eq_denote, range_link; cbn [eq_rhs eq_off].
          unfold off_fold; cbn [List.fold_right]. rewrite right_identity.
          rewrite terms_fold_cons, (range_terms_fold genv' penv (Hvec := Hvec)),
            fold_opp_coeff.
          rewrite (fold_fnat_iwsum wenv' bl).
          2: { intros iw hin. eapply hbit; eapply hidx; exact hin. }
          rewrite hsum.
          unfold term_denote; cbn [peval t_coeff t_var t_base].
          rewrite hwx, hgA.
          rewrite <-smul_distributive_fadd.
          assert (hz : one * fnat k + opp (fnat k) = zero). { field. }
          rewrite hz, field_zero. reflexivity.
        - (* the bit equations *)
          eapply List.Forall_forall. intros e he.
          eapply List.in_flat_map in he. destruct he as (iw & hiw & he).
          pose proof (hidx iw hiw) as hi.
          destruct (hbit (fst iw) hi) as (h1 & h2 & h3 & h4).
          cbn [bit_eqs List.In] in he.
          destruct he as [he | [he | he]]; [| | contradiction]; subst e.
          * (* Cb = A^b · B^r *)
            eapply (commit_eq_denote genv' penv (Hvec := Hvec)).
            rewrite h4, h1, h2, hgA, hgB. reflexivity.
          * (* Cb = Cb^b · B^s, with b ∈ {0,1} and s = 0 *)
            eapply (simple_eq_denote genv' penv (Hvec := Hvec)).
            rewrite !terms_fold_cons. unfold terms_fold; cbn [List.fold_right].
            unfold term_denote; cbn [peval t_coeff t_var t_base].
            rewrite h1, h3, h4, hgB.
            assert (hb : List.nth (fst iw) bl 0 = 0%nat ∨ List.nth (fst iw) bl 0 = 1%nat).
            { rewrite List.Forall_forall in hbits.
              pose proof (hbits (List.nth (fst iw) bl 0)
                (List.nth_In bl 0 (ltac:(lia) : (fst iw < List.length bl)%nat))).
              lia. }
            assert (hz1 : one * zero = zero). { field. }
            rewrite hz1, !field_zero, !right_identity.
            destruct hb as [hb | hb]; rewrite hb; cbn [fnat].
            { rewrite hz1, !field_zero. reflexivity. }
            { assert (ho : one * (one + zero) = one). { field. }
              rewrite ho, field_one. reflexivity. }
    Qed.

  End Completeness.

End DslRange.
