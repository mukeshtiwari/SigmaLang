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
  LinearRelation Composition Dsl.

Import VectorNotations.

(** * DslSubst: eliminating a private variable defined by a linear form

    ** What this file is for

    The surface language of Surface.v lets a user write a local
    definition, a "let": a new private variable whose value is fixed
    by an expression built from the variables already in scope.  The
    core statement language of Dsl.v has no such construct.  This
    file bridges the gap.  It removes the defined variable by
    replacing every use of it by its definition, and it proves that
    doing so does not change what the statement means.

    ** Vocabulary

    A statement is a tree of group equations joined by AND, OR and
    threshold nodes.  An equation is a product of powers that must
    equal the identity element of the group.  Each factor of such a
    product is one of two things:

    - a term, a point raised to the power "public coefficient times
      private variable", or
    - an offset, a point raised to a purely public power, with no
      private variable in it.

    A point is a group element, named by the environment [genv].  A
    public scalar is a field element everybody knows, named by
    [penv].  A private scalar is a secret known only to the prover;
    the function naming those is the witness environment, written
    [wenv] below, and the secrets themselves are the witness.

    ** Linear forms

    A linear form, the type [lin] below, is what a defined variable
    may be defined by: a public constant plus a sum of public
    multiples of private variables.  Writing the constant [c0] and
    the summands [ci] times [yi], each [ci] is a public scalar
    expression and each [yi] is the name of a private variable.

    Nothing more general is allowed.  Anything more general would
    stop the equations from being linear in the private variables,
    and that linearity is what the whole compiler rests on.

    ** What substitution does to a term

    Take a term whose private variable is the [x] being eliminated,
    say the point [B] raised to the power [c] times [x].  Replace [x]
    by its definition and expand.  The power then splits into one
    factor for the constant part of the form and one factor for each
    summand: the factor [B] to the power [c] times [c0], and the
    factors [B] to the power [c] times [ci] times [yi].

    Every factor of the second kind is again an ordinary term: the
    same point, the public coefficient [c] times [ci], and the
    private variable [yi].  The first factor mentions no private
    variable at all, so it is an offset.  This is why [subst_term]
    returns a pair: a list of new terms, and a list of new offsets.
    A term whose variable is not [x] is returned untouched, as a
    one-element term list and no offsets.

    So one term becomes several terms plus a public offset, and the
    rewritten equation still has exactly the shape the core language
    demands, a list of terms and a list of offsets.  Nothing outside
    the core language is ever built, so the rewritten statement
    compiles just like any other.

    ** The main theorem

    [subst_stmt_denote] says the rewritten statement and the original
    have the same meaning, under one hypothesis: that the environment
    really does give [x] the value the linear form computes.

    That hypothesis is exactly the right one.  With it, the expansion
    above is an identity in the group, factor by factor, so the two
    products are equal and the two equations hold together or fail
    together.  Without it the two statements genuinely differ, since
    the rewritten one has forgotten [x] altogether and speaks only of
    the other private variables. *)

Section DslSubst.

  (** ** Parameters

      Nothing here depends on a particular field, group or type of
      names, so all three are taken as parameters.

      [F] is the field of scalars: [zero] and [one] are its
      constants, [add], [mul], [sub] and [div] its four binary
      operations, [opp] is negation, [inv] the multiplicative
      inverse, and [Fdec] decides whether two scalars are equal. *)
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}.

  (** [G] is the group in which the equations live.  [gid] is its
      identity element, [gop] its operation, [ginv] the inverse,
      [gpow] raises a group element to a scalar power, and [Gdec]
      decides whether two group elements are equal. *)
  Context
    {G : Type}
    {gid : G}
    {ginv : G -> G}
    {gop : G -> G -> G}
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}.

  (** [V] is the type of names.  Names are abstract: all that is
      asked of them is [vdec], a way to decide whether two names are
      equal.  The same type serves for private names, public scalar
      names and point names; which one is meant is decided by the
      environment the name is looked up in. *)
  Context
    {V : Type}
    {vdec : forall x y : V, {x = y} + {x <> y}}.

  (** Infix notations for the operations used below, so that the
      algebra reads the usual way: the caret is [gpow], raising a
      group element to a scalar power, and the star and the plus are
      [mul] and [add] on scalars.  They shorten the displayed
      statements and change nothing else. *)
  #[local] Infix "^" := gpow.
  #[local] Infix "*" := mul.
  #[local] Infix "+" := add.

  (** Local shorthands.  [veqb] is the boolean equality test on
      names derived from [vdec].  [pexprC] is the type of public
      scalar expressions, [termC] of single terms, [equationC] of
      equations and [stmtC] of whole statements, each of them the
      corresponding type of Dsl.v already applied to this section's
      field and name type. *)
  #[local] Notation veqb := (@veqb V vdec).
  #[local] Notation pexprC := (@pexpr F V).
  #[local] Notation termC := (@term F V).
  #[local] Notation equationC := (@equation F V).
  #[local] Notation stmtC := (@stmt F V).

  (** ** Linear forms and the substitution itself *)

  (** A linear form: a public constant together with a list of public
      multiples of private variables.

      The first component is the constant [c0], a public scalar
      expression.  The second is a list of pairs; a pair holds a
      public scalar expression [ci] and the name [yi] of a private
      variable, and stands for the summand [ci] times [yi].

      The value such a form takes in a given environment is computed
      by [lin_denote] below.  This is the only shape of definition
      the pass supports, and it is precisely the shape that keeps
      equations linear in the private variables. *)
  Definition lin : Type := (pexprC * list (pexprC * V))%type.

  (** Substitute the linear form [l] for the private variable [x] in
      a single term.  The result is a pair: the new terms, and the
      new offsets.

      A term is the point [t_base] raised to the power [t_coeff]
      times the variable [t_var].  There are two cases.

      - [t_var] is [x].  Then [x] must be replaced by the form.
        Multiplying the coefficient into the form and expanding gives
        one new term per summand of the form: the same point, the
        coefficient [PMul (t_coeff t) ci], and the variable [yi].
        The constant part of the form carries no private variable, so
        it becomes a single offset instead: the same point raised to
        the public power [PMul (t_coeff t) c0].
      - [t_var] is any other variable.  The term is left alone, and
        the result is that one term together with no offsets.

      The multiplications are kept symbolic, as uses of the
      expression constructor [PMul], so the output is still a piece
      of syntax and no field arithmetic is performed here. *)
  Definition subst_term (x : V) (l : lin) (t : termC) :
    list termC * list (pexprC * V) :=
    if veqb (t_var t) x
    then (List.map (fun cy => mkterm (PMul (t_coeff t) (fst cy)) (snd cy) (t_base t))
            (snd l),
          List.cons (PMul (t_coeff t) (fst l), t_base t) List.nil)
    else (List.cons t List.nil, List.nil).

  (** Substitute inside a whole equation.

      Every term of [eq_rhs] is substituted.  The term lists so
      produced are concatenated and become the new [eq_rhs]; the
      offset lists so produced are concatenated and placed in front
      of the equation's original offsets in [eq_off].

      The result is again an ordinary equation of the core language,
      a list of terms and a list of offsets, which is exactly why
      [subst_term] splits its output in two.  The order of the
      factors of the product does change, but a product in a
      commutative group does not depend on the order. *)
  Definition subst_eq (x : V) (l : lin) (e : equationC) : equationC :=
    mkeq (List.flat_map (fun t => fst (subst_term x l t)) (eq_rhs e))
         (List.app (List.flat_map (fun t => snd (subst_term x l t)) (eq_rhs e))
                   (eq_off e)).

  (** Substitute the linear form [l] for the private variable [x]
      throughout a statement.

      The recursion walks the tree and substitutes in every equation
      it meets: AND and OR nodes substitute in both children, and a
      threshold node substitutes in each child while keeping its
      threshold [t].  The shape of the tree is untouched, so the
      rewritten statement is accepted by the compiler wherever the
      original was.

      As in DslRename.v, the children of a threshold are traversed by
      a hand-written inner loop rather than by [List.map], because
      the guardedness checker does not accept the [List.map] form
      here.  [subst_stmt_thresh] below shows the two agree, so no
      later proof has to look inside the loop. *)
  Fixpoint subst_stmt (x : V) (l : lin) (s : stmtC) : stmtC :=
    match s with
    | SEqs eqs => SEqs (List.map (subst_eq x l) eqs)
    | SAnd a b => SAnd (subst_stmt x l a) (subst_stmt x l b)
    | SOr a b => SOr (subst_stmt x l a) (subst_stmt x l b)
    | SThresh t ss =>
        SThresh t
          ((fix go (ss : list stmtC) : list stmtC :=
              match ss with
              | List.nil => List.nil
              | List.cons s' ss' => List.cons (subst_stmt x l s') (go ss')
              end) ss)
    end.

  Section Spec.

    (** ** Semantics

        Everything below is stated for one fixed pair of public
        environments: [genv], which gives each point name its group
        element, and [penv], which gives each public scalar name its
        field element.  The witness environment, holding the private
        scalars, stays universally quantified in every lemma, since
        the hypotheses of those lemmas are conditions on it. *)
    Variable genv : V -> G.
    Variable penv : V -> F.

    (** Local shorthands for the evaluation functions of Dsl.v,
        already applied to this section's parameters.  [pevalC]
        evaluates a public scalar expression to a field element.
        [term_denoteC] gives the group element of one term.
        [terms_foldC] and [off_foldC] multiply together a list of
        terms and a list of offsets respectively.  [eq_denoteC] says
        when one equation holds, and [stmt_denoteC] when a whole
        statement holds. *)
    #[local] Notation pevalC := (@peval F add mul opp V penv).
    #[local] Notation term_denoteC := (@term_denote F add mul opp G gpow V genv penv).
    #[local] Notation terms_foldC := (@terms_fold F add mul opp G gid gop gpow V genv penv).
    #[local] Notation off_foldC := (@off_fold F add mul opp G gid gop gpow V genv penv).
    #[local] Notation eq_denoteC := (@eq_denote F add mul opp G gid gop gpow V genv penv).
    #[local] Notation stmt_denoteC := (@stmt_denote F add mul opp G gid gop gpow V genv penv).

    (** The value a linear form takes in a given witness
        environment.

        It evaluates the public constant with [pevalC], evaluates
        each public coefficient the same way, multiplies each one by
        the current value of its private variable, and adds
        everything together.  So this is the scalar that the defined
        variable is supposed to be equal to.

        It appears throughout the file as the hypothesis
        [wenv x = lin_denote wenv l].  That hypothesis says the
        environment respects the definition of [x], and it is exactly
        what the substituted statement needs in order to agree with
        the original. *)
    Definition lin_denote (wenv : V -> F) (l : lin) : F :=
      pevalC (fst l) +
      List.fold_right (fun cy acc => pevalC (fst cy) * wenv (snd cy) + acc)
        zero (snd l).

    Section Proofs.

      (** The proofs assume that the scalars and the group really
          form a vector space: [F] is a field, [G] is a commutative
          group, and [gpow] behaves like scalar multiplication.  The
          law that matters most is that a power whose exponent is a
          sum splits into a product of powers; that splitting is the
          heart of every calculation below. *)
      Context
        {Hvec : @vector_space F (@eq F) zero one add mul sub
          div opp inv G (@eq G) gid ginv gop gpow}.

      (** Register the field structure so that routine scalar
          identities, such as distributing a coefficient over a sum,
          are discharged automatically. *)
      Add Field field : (@field_theory_for_stdlib_tactic F
        eq zero one opp add mul sub inv div vector_space_field).

      (** The product over a concatenation of two term lists is the
          product over the first times the product over the second.

          [terms_foldC] folds a list with the group operation
          starting from the identity, so this is nothing but
          associativity of that operation together with the identity
          being neutral.  It is needed because substitution
          concatenates the term lists produced by the individual
          terms. *)
      Lemma terms_fold_app :
        ∀ (wenv : V -> F) (l₁ l₂ : list termC),
        terms_foldC wenv (List.app l₁ l₂) =
        gop (terms_foldC wenv l₁) (terms_foldC wenv l₂).
      Proof.
        induction l₁ as [|t l₁ ih]; intros l₂; cbn.
        + rewrite left_identity; reflexivity.
        + unfold terms_fold in ih |- *; cbn.
          rewrite ih, associative. reflexivity.
      Qed.

      (** The same fact for offsets: the product over a
          concatenation of two offset lists splits into the two
          products.  Substitution also concatenates offset lists, so
          both versions are used. *)
      Lemma off_fold_app :
        ∀ (l₁ l₂ : list (pexprC * V)),
        off_foldC (List.app l₁ l₂) = gop (off_foldC l₁) (off_foldC l₂).
      Proof.
        induction l₁ as [|o l₁ ih]; intros l₂; cbn.
        + rewrite left_identity; reflexivity.
        + unfold off_fold in ih |- *; cbn.
          rewrite ih, associative. reflexivity.
      Qed.

      (** A point raised to a coefficient times a sum of multiples
          equals the product of the individual powers.

          On the left, the point [genv B] is raised to [c] times the
          value of the list [cys] of public-multiple pairs, that is,
          the sum over the pairs of the coefficient times the value
          of the variable.  On the right, the same list is turned
          into one term per pair, with coefficient [PMul c] applied
          to that pair's coefficient and with that pair's variable,
          and the resulting terms are multiplied together.

          This is the identity that makes substitution legal.  It
          holds for two vector space reasons: a power whose exponent
          is a sum is the product of the powers, and a power whose
          exponent is a product is the repeated power.  The argument
          is an induction on [cys]; the empty case uses that raising
          to [zero] gives the identity element. *)
      Lemma pow_lin_sum :
        ∀ (wenv : V -> F) (B : V) (c : pexprC) (cys : list (pexprC * V)),
        (genv B) ^ (pevalC c *
          List.fold_right (fun cy acc => pevalC (fst cy) * wenv (snd cy) + acc)
            zero cys) =
        terms_foldC wenv
          (List.map (fun cy => mkterm (PMul c (fst cy)) (snd cy) B) cys).
      Proof.
        induction cys as [|cy cys ih]; cbn.
        +
          assert (h : pevalC c * zero = zero). { field. }
          rewrite h, field_zero. reflexivity.
        +
          assert (h : pevalC c * (pevalC (fst cy) * wenv (snd cy) +
            List.fold_right
              (fun cy acc => pevalC (fst cy) * wenv (snd cy) + acc) zero cys) =
            (pevalC c * pevalC (fst cy)) * wenv (snd cy) +
            pevalC c * List.fold_right
              (fun cy acc => pevalC (fst cy) * wenv (snd cy) + acc) zero cys).
          { field. }
          rewrite h, smul_distributive_fadd, ih.
          unfold terms_fold; cbn. unfold term_denote; cbn.
          reflexivity.
      Qed.

      (** Substituting one term preserves its contribution to the
          equation.

          The hypothesis [wenv x = lin_denote wenv l] says the
          environment really satisfies the definition of [x].  The
          conclusion says that the product of the terms returned by
          [subst_term], multiplied by the product of the offsets it
          returned, is the group element of the original term.

          If the term does not mention [x] there is nothing to prove,
          since the outputs are that term itself and no offsets.  If
          it does mention [x], the hypothesis lets the value of [x]
          be replaced by the value of the form; distributing the
          coefficient over the constant part and over the sum splits
          the power into the new offset and, by [pow_lin_sum], the
          product of the new terms. *)
      Lemma subst_term_denote :
        ∀ (wenv : V -> F) (x : V) (l : lin) (t : termC),
        wenv x = lin_denote wenv l ->
        gop (terms_foldC wenv (fst (subst_term x l t)))
            (off_foldC (snd (subst_term x l t))) =
        term_denoteC wenv t.
      Proof.
        intros * hx.
        unfold subst_term.
        destruct (veqb (t_var t) x) eqn:hv; cbn [fst snd].
        +
          eapply veqb_eq in hv.
          rewrite <-pow_lin_sum.
          unfold off_fold; cbn. unfold off_denote; cbn.
          rewrite right_identity.
          unfold term_denote. rewrite hv, hx. unfold lin_denote.
          assert (h : pevalC (t_coeff t) * (pevalC (fst l) +
            List.fold_right
              (fun cy acc => pevalC (fst cy) * wenv (snd cy) + acc) zero (snd l)) =
            pevalC (t_coeff t) * pevalC (fst l) +
            pevalC (t_coeff t) * List.fold_right
              (fun cy acc => pevalC (fst cy) * wenv (snd cy) + acc) zero (snd l)).
          { field. }
          rewrite h, smul_distributive_fadd, commutative.
          reflexivity.
        +
          unfold terms_fold, off_fold; cbn.
          rewrite !right_identity. reflexivity.
      Qed.

      (** The same statement for a whole list of terms.

          Substituting each term of [ts] and gathering all the
          results gives a term list and an offset list whose combined
          product is the product over the original [ts].  The
          argument is an induction on [ts]: [terms_fold_app] and
          [off_fold_app] split the concatenations, [subst_term_denote]
          handles the head, and the regrouping of the four partial
          products into two uses that the group is commutative.

          This is the form the equation-level lemma needs, since an
          equation carries a whole list of terms. *)
      Lemma subst_terms_denote :
        ∀ (wenv : V -> F) (x : V) (l : lin) (ts : list termC),
        wenv x = lin_denote wenv l ->
        gop (terms_foldC wenv (List.flat_map (fun t => fst (subst_term x l t)) ts))
            (off_foldC (List.flat_map (fun t => snd (subst_term x l t)) ts)) =
        terms_foldC wenv ts.
      Proof.
        intros * hx.
        induction ts as [|t ts ih]; cbn [List.flat_map].
        + unfold terms_fold, off_fold; cbn. rewrite right_identity. reflexivity.
        + rewrite terms_fold_app, off_fold_app, gop_simp.
          rewrite (subst_term_denote wenv x l t hx), ih.
          reflexivity.
      Qed.

      (** One equation means the same after substitution, provided
          the environment satisfies the definition of [x].

          An equation holds when the product of its terms times the
          product of its offsets is the identity of the group.  After
          substitution the offsets are the newly created ones
          followed by the original ones; regrouping that product and
          applying [subst_terms_denote] turns the whole left hand
          side into exactly the left hand side of the original
          equation.  The two being equal group elements, one is the
          identity precisely when the other is. *)
      Lemma subst_eq_denote :
        ∀ (wenv : V -> F) (x : V) (l : lin) (e : equationC),
        wenv x = lin_denote wenv l ->
        (eq_denoteC wenv (subst_eq x l e) <-> eq_denoteC wenv e).
      Proof.
        intros * hx.
        unfold eq_denote, subst_eq; cbn [eq_rhs eq_off].
        rewrite off_fold_app, associative, (subst_terms_denote wenv x l _ hx).
        reflexivity.
      Qed.

      (** Substituting in a threshold node is the same as
          substituting in each of its children.

          This replaces the hand-written loop inside [subst_stmt] by
          an ordinary [List.map], which is the form the later proofs
          want.  Proving it once keeps the internal loop out of every
          proof that follows. *)
      Lemma subst_stmt_thresh :
        ∀ (x : V) (l : lin) (t : nat) (ss : list stmtC),
        subst_stmt x l (SThresh t ss) = SThresh t (List.map (subst_stmt x l) ss).
      Proof.
        intros; cbn. f_equal.
      Qed.

      (** Substitution does not change which children of a threshold
          node hold.

          [flagged_denote] takes a list of children and a list of
          booleans, one flag per child, and asserts that every child
          whose flag is set holds.  The hypothesis here is that each
          child individually means the same before and after
          substitution.  The conclusion lifts that to the whole
          flagged conjunction, for any list of flags whatsoever.

          It is stated separately so that the threshold case of the
          main theorem can reuse the very same list of flags on both
          sides: substitution changes neither the number of children
          nor the number of flags that are set, so only the
          conjunction itself needs an argument. *)
      Lemma flagged_denote_map :
        ∀ (wenv : V -> F) (x : V) (l : lin) (ss : list stmtC) (bs : list bool),
        List.Forall (fun s =>
          stmt_denoteC wenv (subst_stmt x l s) <-> stmt_denoteC wenv s) ss ->
        (@flagged_denote F add mul opp G gid gop gpow V genv penv wenv
           (List.map (subst_stmt x l) ss) bs <->
         @flagged_denote F add mul opp G gid gop gpow V genv penv wenv ss bs).
      Proof.
        intros wenv x l ss.
        induction ss as [|s ss ih]; intros [|b bs] hall; cbn; try reflexivity.
        inversion hall as [| ? ? hs hall']; subst.
        rewrite (ih bs hall').
        destruct b; [rewrite hs |]; reflexivity.
      Qed.

      (** ** The main theorem *)

      (** Eliminating [x] does not change the meaning of a statement,
          provided the environment respects the definition of [x].

          The hypothesis [wenv x = lin_denote wenv l] says that the
          private scalar stored under the name [x] really is the
          value that the linear form [l] computes from the other
          private scalars.  Under that hypothesis the substituted
          statement holds precisely when the original does.

          Why it is true: the meaning of a statement is built up from
          the meanings of its equations by conjunction, disjunction
          and counting, and none of those connectives inspects an
          equation any further.  So it is enough that every single
          equation is preserved, which is [subst_eq_denote], and the
          rest is a structural induction over the tree.  The
          threshold case reuses the same flags on both sides through
          [flagged_denote_map].

          The hypothesis cannot be dropped.  The substituted
          statement no longer mentions [x] at all, so for an
          environment that gives [x] some unrelated value the two
          statements really do say different things.

          This is the correctness statement Surface.v relies on when
          it compiles a local definition.  There the body is
          elaborated with the defined variable still in it, and the
          variable is then substituted away with [subst_stmt].  The
          witness the honest prover uses assigns the defined variable
          exactly the value of its definition, which is precisely the
          hypothesis of this theorem, so the compiled statement means
          what the user wrote. *)
      Theorem subst_stmt_denote :
        ∀ (wenv : V -> F) (x : V) (l : lin) (s : stmtC),
        wenv x = lin_denote wenv l ->
        (stmt_denoteC wenv (subst_stmt x l s) <-> stmt_denoteC wenv s).
      Proof.
        intros wenv x l s hx.
        induction s as [eqs | a b iha ihb | a b iha ihb | t ss ihl]
          using stmt_ind'.
        +
          cbn.
          induction eqs as [|e eqs ih]; cbn.
          - split; intro; constructor.
          - split; intro h; inversion h as [| ? ? h1 h2]; subst; constructor.
            * eapply subst_eq_denote; eassumption.
            * eapply ih; exact h2.
            * eapply subst_eq_denote; eassumption.
            * eapply ih; exact h2.
        + cbn. rewrite iha, ihb. reflexivity.
        + cbn. rewrite iha, ihb. reflexivity.
        +
          rewrite subst_stmt_thresh.
          rewrite !(stmt_denote_thresh genv penv).
          split; intros (bs & hlen & hcnt & hfl); exists bs.
          - rewrite List.length_map in hlen.
            split; [exact hlen | split; [exact hcnt |]].
            eapply flagged_denote_map; eassumption.
          - split; [rewrite List.length_map; exact hlen | split; [exact hcnt |]].
            eapply flagged_denote_map; eassumption.
      Qed.

    End Proofs.

  End Spec.

End DslSubst.
