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
  LinearRelation Composition Dsl DslRename.

Import VectorNotations.

(** * DslNeq: the not-equals gadget

    The statement language of Dsl.v can only say that things are
    equal.  Every equation it offers is a product of group elements
    raised to powers, and the equation asserts that this product is
    the identity of the group.  Such an equation can say "this point
    is that product"; it can never say "this scalar is different
    from that scalar".  Yet protocols regularly need exactly that: a
    bid that is not zero, two identifiers that are not the same, a
    value that avoids a forbidden one.  This file shows how to say
    one such thing inside the language, without extending the
    language at all.

    ** What is proven, and why it is hard

    The gadget proves that a public linear function of one private
    scalar is nonzero.  The private scalar is called [x], the public
    data are two scalar expressions [coeff] and [off], and the
    quantity in question is [coeff] times [x] plus [off].  Call that
    quantity the committed value.

    Being nonzero is a negative statement.  There is no linear
    equation whose solution set is "everything except zero", so the
    property cannot be written down directly.

    The way out uses one fact about fields: a value is nonzero
    exactly when it has a multiplicative inverse.  So instead of the
    negative statement, the prover proves a positive one: "I know a
    scalar [j] such that the committed value times [j] is [one]".  A
    prover whose committed value is [zero] can never produce such a
    [j], because zero times anything is zero.

    ** Moving the multiplication into the exponent

    A product of two unknown scalars is still not a linear equation.
    It becomes one by working in the exponent of a group.  The
    prover first commits to the value with a Pedersen commitment.  A
    Pedersen commitment uses two fixed public group points, here
    named [An] and [Bn].  To commit to a value the prover picks a
    random scalar [r], called the blinding factor, and publishes the
    point [An] raised to the value, times [Bn] raised to [r].  The
    random [r] hides the value.  The commitment binds the prover to
    a single value as long as nobody knows a scalar [d] with [An]
    equal to [Bn] raised to [d].  Such a [d] is called the discrete
    logarithm of [An] to the base [Bn]: the exponent that carries
    one group element to another.  An honest setup picks the two
    bases so that no one knows it.

    With the commitment in hand, the second equation says that [An]
    equals the commitment raised to [j], times [Bn] raised to a
    further scalar [s].  Both equations are linear in the unknown
    exponents [x], [r], [j] and [s], so both are ordinary equations
    of the language.  The gadget is therefore an ordinary core
    block: it asks nothing new of the compiler and composes with
    AND, OR and threshold like any other statement.

    An honest prover takes [j] to be the inverse of the committed
    value and [s] to be minus [r] times [j].  Raising the commitment
    to [j] contributes [An] to the first power, plus a leftover
    power of [Bn]; the term [Bn] raised to [s] is exactly the
    leftover, with the opposite sign, so the two cancel and the
    equation closes.

    ** The names used

    - [Cn] names the point holding the commitment;
    - [An] and [Bn] name the two public bases;
    - [x] names the private scalar being constrained;
    - [r] names the blinding scalar of the commitment;
    - [j] names the claimed inverse of the committed value;
    - [s] names the blinding correction that makes the second
      equation close.

    Of these, [x] and [r] belong to the prover already; [j] and [s]
    are auxiliary names that the gadget introduces, and they must be
    fresh, which is why the completeness theorem asks for them to
    differ from everything else.

    ** Soundness and completeness

    Soundness is the guarantee that a cheating prover cannot get
    away with a false claim.  Here it takes the form of a
    dichotomy ([neq_sound]): from any assignment satisfying the two
    equations, either the committed value really is nonzero, or one
    can write down an explicit discrete logarithm of [An] to the
    base [Bn].  The second branch is not a hole in the argument; it
    is a statement about the setup.  If the two bases were generated
    honestly, nobody knows that discrete logarithm, so the second
    branch cannot be reached and the first one must hold.

    Completeness is the opposite guarantee: an honest prover always
    succeeds ([neq_complete]).  Given a genuinely nonzero committed
    value and a correctly formed commitment, the honest prover
    computes the inverse and the matching blinding correction, and
    the extended assignment satisfies both equations.

    ** Limitation

    The gadget as written handles one private variable per
    inequality.  The committed value is [coeff] times [x] plus
    [off], a linear form in a single unknown.  An inequality
    involving two or more private scalars at once is not expressible
    by this definition and would need a wider linear form. *)

Section DslNeq.

  (** ** Parameters

      The development is parametric in the scalar field and in the
      group, so nothing below depends on a particular curve or a
      particular prime.

      This first block is the field of scalars: [F] is the carrier,
      [zero] and [one] the constants, [add], [mul], [sub] and [div]
      the four operations, [opp] negation and [inv] the
      multiplicative inverse.  [Fdec] decides equality of two
      scalars, which is what lets the soundness proof split into its
      two cases. *)
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}.

  (** The group in whose exponents the arithmetic happens: [G] is
      the carrier, [gid] the identity, [ginv] inversion, [gop] the
      group operation, and [gpow] raises a group element to a scalar
      power.  [Gdec] decides equality of group elements. *)
  Context
    {G : Type}
    {gid : G}
    {ginv : G -> G}
    {gop : G -> G -> G}
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}.

  (** Variable names are abstract.  All that is needed of them is
      that equality of two names can be decided, which [vdec]
      provides; that is enough to update one entry of an
      environment. *)
  Context
    {V : Type}
    {vdec : forall x y : V, {x = y} + {x <> y}}.

  (** Local notation so that the equations below read the way they
      would be written on paper: a caret for raising a group element
      to a power, and the usual signs for the field operations. *)
  #[local] Infix "^" := gpow.
  #[local] Infix "*" := mul.
  #[local] Infix "+" := add.

  (** Abbreviations for the syntax of Dsl.v and the environment
      update of DslRename.v, already applied to this section's
      parameters: [pexprC] is a public scalar expression, [equationC]
      one linear equation, [stmtC] a statement tree, and [overrideC]
      changes the value that an environment gives to one name. *)
  #[local] Notation pexprC := (@pexpr F V).
  #[local] Notation equationC := (@equation F V).
  #[local] Notation stmtC := (@stmt F V).
  #[local] Notation overrideC := (@override F V vdec).

  (** ** The two equations of the gadget *)

  (** The commitment equation.

      [neq_commit Cn An Bn x r coeff off] is the equation stating
      that the point named [Cn] is the Pedersen commitment to the
      committed value under the bases named [An] and [Bn], with
      blinding scalar named [r].  Read on paper it says: [Cn] equals
      [An] raised to [coeff] times [x] plus [off], times [Bn] raised
      to [r].

      The definition looks different because the language stores
      equations in homogeneous form, with everything moved to one
      side and the whole product asserted to be the identity.  So
      the two private terms are [An] raised to [coeff] times [x] and
      [Bn] raised to one times [r], while the public offsets are
      [An] raised to [off] and [Cn] raised to minus one.  The lemma
      [neq_commit_denote] below turns this back into the readable
      form, and the rest of the file only ever uses that lemma. *)
  Definition neq_commit (Cn An Bn x r : V) (coeff off : pexprC) : equationC :=
    mkeq (List.cons (mkterm coeff x An)
      (List.cons (mkterm (PConst one) r Bn) List.nil))
      (List.cons (off, An)
        (List.cons (POpp (PConst one), Cn) List.nil)).

  (** The whole gadget: the statement that the committed value is
      nonzero.

      [neq_stmt Cn An Bn x j s r coeff off] is a conjunction of two
      equations.  The first is the commitment equation above.  The
      second says that [An] equals the commitment [Cn] raised to [j],
      times [Bn] raised to [s]; it is written with [simple_eq], the
      readable form in which one named point equals a product of
      terms.

      The two equations are packed into a single [SEqs] node rather
      than joined with [SAnd].  That matters: an AND-tree of
      equations compiles into one leaf with a single shared witness
      vector, so the names [x], [r], [j] and [s] denote the same
      scalars in both equations.  Splitting them across an [SAnd]
      would give the two halves independent witnesses and the link
      between the commitment and its inverse would be lost. *)
  Definition neq_stmt (Cn An Bn x j s r : V) (coeff off : pexprC) : stmtC :=
    SEqs (List.cons (neq_commit Cn An Bn x r coeff off)
      (List.cons (simple_eq (one := one) An
        (List.cons (mkterm (PConst one) j Cn)
          (List.cons (mkterm (PConst one) s Bn) List.nil)))
        List.nil)).

  (** ** Semantics

      A statement is only syntax; it says nothing until names are
      given values.  The assignments that do this are called
      environments.  There are three of them, and they play
      different roles.

      - [genv] sends a point name to an actual group element.  It
        holds the public instance: the two bases and the commitment.
      - [penv] sends a name to a public scalar, which is what the
        public expressions [coeff] and [off] may mention.
      - The third environment, written [wenv] below, sends a name to
        a private scalar.  It is the witness: the secret data that
        the prover knows and the verifier does not.  It is not a
        section variable because both theorems quantify over it. *)
  Section Spec.

    Variable genv : V -> G.
    Variable penv : V -> F.

    (** [pevalC] evaluates a public scalar expression under [penv],
        [eq_denoteC] says when one equation holds, and
        [stmt_denoteC] says when a whole statement holds. *)
    #[local] Notation pevalC := (@peval F add mul opp V penv).
    #[local] Notation eq_denoteC :=
      (@eq_denote F add mul opp G gid gop gpow V genv penv).
    #[local] Notation stmt_denoteC :=
      (@stmt_denote F add mul opp G gid gop gpow V genv penv).

    (** ** The two theorems

        Everything proved below needs the algebra to behave, which
        the syntax alone does not guarantee.  [Hvec] is the
        assumption that the scalars and the group really form a
        vector space over a field: powers add when exponents add,
        the identity is the zero power, and so on.  Only inside this
        section can the equations be manipulated. *)
    Section Proofs.

      Context
        {Hvec : @vector_space F (@eq F) zero one add mul sub
          div opp inv G (@eq G) gid ginv gop gpow}.
      (** Register the field with the [field] tactic, so that
          routine scalar identities, in particular the ones about
          the inverse of the committed value, are discharged
          automatically. *)
      Add Field field : (@field_theory_for_stdlib_tactic F
        eq zero one opp add mul sub inv div vector_space_field).

      (** The commitment equation means what it is supposed to mean.

          The equation [neq_commit] is stored in homogeneous form,
          as a product asserted to be the group identity.  This
          lemma says that holding, under a witness [wenv], is the
          same as the readable statement that the point [genv Cn] is
          the base [genv An] raised to the committed value, times
          the base [genv Bn] raised to the blinding scalar.

          It is true by the vector-space laws alone.  The factor
          [Cn] raised to minus one is the inverse of the commitment,
          so moving it to the other side turns the identity into an
          equality of two points; the two powers of [An], one
          carrying [coeff] times [x] and one carrying [off], merge
          into a single power because powers add when exponents add.

          The lemma exists so that the soundness and completeness
          proofs never have to look at the homogeneous encoding
          again. *)
      Lemma neq_commit_denote :
        ∀ (Cn An Bn x r : V) (coeff off : pexprC) (wenv : V -> F),
        eq_denoteC wenv (neq_commit Cn An Bn x r coeff off) <->
        genv Cn =
          gop ((genv An) ^ (pevalC coeff * wenv x + pevalC off))
              ((genv Bn) ^ (wenv r)).
      Proof.
        intros *.
        unfold eq_denote, neq_commit, terms_fold, off_fold, term_denote, off_denote;
        cbn.
        rewrite !right_identity.
        assert (ha : one * wenv r = wenv r). { field. }
        rewrite ha.
        assert (hb : (genv Cn) ^ (opp one) = ginv (genv Cn)).
        { rewrite <-connection_between_vopp_and_fopp. rewrite field_one. reflexivity. }
        rewrite hb.
        rewrite gop_simp.
        rewrite <-smul_distributive_fadd.
        rewrite associative.
        rewrite gop_eq_gid_iff.
        rewrite group_inv_inv.
        split; intro hc; symmetry; exact hc.
      Qed.

      (** Soundness: the gadget cannot be satisfied by a cheat,
          unless the setup was rigged.

          The hypothesis is that some witness [wenv] satisfies the
          whole statement, that is, both equations at once.  The
          conclusion is a dichotomy.  Either the committed value,
          [coeff] times [x] plus [off], is genuinely different from
          [zero], which is what the gadget set out to prove; or
          there is an explicit scalar [d] with [genv An] equal to
          [genv Bn] raised to [d], the discrete logarithm of one
          base to the other.

          Why the dichotomy holds.  Suppose the committed value were
          [zero].  Then the first equation degenerates: the base
          [genv An] is raised to the zero power, which is the group
          identity, so the commitment is nothing but [genv Bn]
          raised to the blinding scalar.  Substituting that into the
          second equation gives [genv An] as a power of [genv Bn]
          alone, with exponent [r] times [j] plus [s].  That exponent
          is the required [d], and the proof exhibits it literally.
          If instead the committed value is not [zero], the left
          branch holds with nothing to do.

          What this buys.  In a deployment the two bases are
          generated so that their relative discrete logarithm is
          unknown; finding one is exactly the hard problem the whole
          protocol rests on.  Under that assumption the right branch
          is unreachable, so any satisfying witness really does
          certify that the value is nonzero. *)
      Theorem neq_sound :
        ∀ (Cn An Bn x j s r : V) (coeff off : pexprC) (wenv : V -> F),
        stmt_denoteC wenv (neq_stmt Cn An Bn x j s r coeff off) ->
        (pevalC coeff * wenv x + pevalC off <> zero) \/
        (∃ d : F, genv An = (genv Bn) ^ d).
      Proof.
        intros * hd.
        cbn in hd.
        inversion hd as [| ? ? h₁ hrest]; subst.
        inversion hrest as [| ? ? h₂ hnil]; subst.
        eapply neq_commit_denote in h₁.
        eapply (simple_eq_denote genv penv (Hvec := Hvec)) in h₂.
        unfold terms_fold, term_denote in h₂; cbn in h₂.
        destruct (Fdec (pevalC coeff * wenv x + pevalC off) zero) as [hz | hnz];
        [right | left; exact hnz].
        rewrite hz in h₁.
        rewrite field_zero, left_identity in h₁.
        rewrite h₁ in h₂.
        rewrite right_identity in h₂.
        rewrite smul_pow_up in h₂.
        rewrite <-smul_distributive_fadd in h₂.
        exists (wenv r * (one * wenv j) + one * wenv s).
        exact h₂.
      Qed.

      (** Completeness: an honest prover can always satisfy the
          gadget.

          Reading the hypotheses one by one:

          - the five inequalities between names say that [j] and [s]
            are fresh: each differs from [x], from [r], and from the
            other.  They are needed because the proof builds the new
            witness by overwriting the entries of [j] and [s], and
            overwriting must not disturb the values already fixed
            for [x] and [r].  A generator such as the one in
            VarType.v supplies names with this property.
          - the committed value is different from [zero].  This is
            the fact the prover actually knows and wants to show.
          - the last hypothesis says the commitment was formed
            correctly: the point [genv Cn] is [genv An] raised to
            the committed value, times [genv Bn] raised to the
            blinding scalar.

          The conclusion produces an extended witness.  It agrees
          with the original one on every name other than [j] and
          [s], so nothing the prover already committed to is
          changed, and it satisfies the whole statement.

          Why it works.  Because the committed value is nonzero it
          has an inverse; take [j] to be that inverse.  Then raising
          the commitment to [j] gives [genv An] to the first power,
          together with a leftover power of [genv Bn] whose exponent
          is the blinding scalar times the inverse.  Choosing [s] to
          be minus that exponent makes the leftover cancel, and the
          second equation reduces to [genv An] equals [genv An].
          The first equation still holds because the values of [x]
          and [r] were not touched. *)
      Theorem neq_complete :
        ∀ (Cn An Bn x j s r : V) (coeff off : pexprC) (wenv : V -> F),
        j <> x -> j <> r -> s <> x -> s <> r -> s <> j ->
        pevalC coeff * wenv x + pevalC off <> zero ->
        genv Cn =
          gop ((genv An) ^ (pevalC coeff * wenv x + pevalC off))
              ((genv Bn) ^ (wenv r)) ->
        ∃ (wenv' : V -> F),
          (∀ v, v <> j -> v <> s -> wenv' v = wenv v) ∧
          stmt_denoteC wenv' (neq_stmt Cn An Bn x j s r coeff off).
      Proof.
        intros * hjx hjr hsx hsr hsj hnz hcm.
        set (L := pevalC coeff * wenv x + pevalC off) in *.
        exists (overrideC (overrideC wenv j (inv L)) s (opp (wenv r) * inv L)).
        split.
        +
          intros v hvj hvs.
          rewrite override_other; [| exact hvs].
          rewrite override_other; [| exact hvj].
          reflexivity.
        +
          cbn.
          constructor; [| constructor; [| constructor]].
          -
            eapply neq_commit_denote.
            rewrite !override_other; try assumption;
            try (intro; subst; contradiction).
          -
            eapply (simple_eq_denote genv penv (Hvec := Hvec)).
            unfold terms_fold, term_denote; cbn.
            rewrite override_same.
            rewrite (override_other _ s j); [| intro h; eapply hsj; symmetry; exact h].
            rewrite override_same.
            rewrite right_identity.
            rewrite hcm.
            rewrite smul_distributive_vadd.
            rewrite !smul_pow_up.
            rewrite <-associative.
            rewrite <-smul_distributive_fadd.
            assert (ha : L * (one * inv L) = one). { field. exact hnz. }
            assert (hb2 : wenv r * (one * inv L) + one * (opp (wenv r) * inv L) = zero).
            { field. exact hnz. }
            rewrite ha, hb2, field_one, field_zero, right_identity.
            reflexivity.
      Qed.

    End Proofs.

  End Spec.

End DslNeq.
