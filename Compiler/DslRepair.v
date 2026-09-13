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
  LinearRelation Composition Dsl DslDistrib DslRename.

Import VectorNotations.

(** * DslRepair: repairing a shared private variable with a Pedersen commitment

    ** Background: statements, witnesses, environments

    A statement of the DSL (Dsl.v) is a monotone formula built from
    linear group equations with [SAnd] (and), [SOr] (or) and
    [SThresh] (at least [t] of these children hold).  The secret data
    that makes a statement true is called the witness.  Here a witness
    is a witness environment [wenv], a function sending every private
    variable name to a scalar.  The public data lives in two further
    environments: [genv] sends a point name to a group element, and
    [penv] sends a public scalar name to a scalar.  The group is
    written multiplicatively, and [gpow g a], written [g ^ a], is [g]
    raised to the power [a].

    ** The problem this pass solves

    The compiler turns a statement into a sigma protocol.  An [SAnd]
    of two pure equation blocks compiles to a single node with one
    witness vector, so those two sides may share private variables
    freely.  But as soon as a side is an [SOr] or an [SThresh], the
    two sides become independent sub-protocols with independent
    witnesses, and nothing forces a variable occurring on both sides
    to take one and the same value.  The same holds between the
    children of one threshold.

    The checker [disj_inv] of Dsl.v is what guards this.  At such an
    [SAnd] it demands that the two sides share no private variable,
    and at an [SThresh] it demands that the children be pairwise
    disjoint.  A statement of the shape

    - [SAnd R (SThresh t l)] where the private variable [x] occurs
      both in [R] and inside the children [l]

    is therefore rejected, even though it is a perfectly reasonable
    thing to want to prove.  A prover could otherwise satisfy [R]
    with one value of [x] and satisfy a child with another, and the
    verifier would believe something weaker than what was written
    down.

    DslDistrib.v repairs the [SOr] case cheaply: distributing the
    conjunct into each branch puts the shared variable inside a
    single merged pure block, where sharing is safe again.  That
    trick does not survive a threshold, because writing "at least [t]
    of [k]" as an explicit disjunction costs a number of branches
    that grows like the number of subsets.  This file is the
    alternative.

    ** Pedersen commitments

    Fix two public group elements [A] and [B].  A Pedersen commitment
    to a value [v] is the single group element [gop (A ^ v) (B ^ w)],
    where the extra scalar [w] is called the randomness.  Publishing
    that element commits its author to [v]; exhibiting a pair
    [(v, w)] that reproduces it is called opening the commitment.

    A Pedersen commitment is binding: nobody can open one element
    with two different values.  The reason is plain arithmetic.  If
    [gop (A ^ x) (B ^ r)] and [gop (A ^ x') (B ^ r')] are the same
    element while [x] and [x'] differ, then dividing one by the other
    gives [A ^ (x - x') = B ^ (r' - r)], and raising both sides to
    the power [inv (x - x')] produces a scalar [d] with [A = B ^ d].
    Such a [d] is the discrete logarithm of [A] to the base [B].
    Computing discrete logarithms is believed infeasible in the
    groups used here, so producing two different openings is believed
    infeasible too.  The arithmetic half of that argument is
    [two_openings_dlog] below, and it is proven rather than assumed;
    only the last step, "such a [d] cannot be found", is a
    cryptographic assumption, and it is never used inside this file.

    ** The repair

    The input is a statement [SAnd R (SThresh t l)] in which the
    private variable [x] is shared between [R] and the children.  The
    output is [repair_thresh], which

    - commits once to the value of [x], at a fresh point name [Cn],
      using a fresh randomness variable [r], and adds to the conjunct
      [R] the equation saying that [Cn] holds that commitment;
    - gives child number [i] a private copy of [x] and a randomness
      of its own, both fresh, and rewrites the child so that it
      speaks about its copy instead of [x] (this is [rename_stmt] of
      DslRename.v);
    - adds to that child the equation saying that its own copy opens
      the very same commitment [Cn].

    Every branch now has a variable of its own, so the checker is
    satisfied.  The branches are tied back together by the
    commitment: they all open the one group element stored at [Cn],
    so by binding they all carry the same value.  The fresh names
    come from VarType.v.

    The bind equation is joined to each child with [and_distrib] of
    DslDistrib.v rather than a plain [SAnd].  That pushes the
    equation inside every disjunct, so a child that was a disjunction
    of pure equation blocks stays one, which is the shape the checker
    likes.

    ** What is proven

    - [repair_sound]: any environment satisfying the repaired
      statement either satisfies the original statement as well, or
      yields an explicit discrete logarithm of [genv An] to the base
      [genv Bn].  Soundness is the direction that protects the
      verifier.  This is an unconditional theorem with an explicit
      reduction; no hardness assumption is used in its proof.  The
      assumption enters only when the result is read: after an honest
      setup nobody knows such a discrete logarithm, so the second
      case never occurs in practice and the repaired statement really
      does imply the original one.
    - [repair_complete]: completeness, the direction that protects
      the prover.  An environment satisfying the original statement
      extends to one satisfying the repaired statement, so nothing
      that could be proven before is lost.  The point environment
      gains exactly one entry, the commitment at the fresh name
      [Cn]; every other point name keeps its value.
    - [repair_disj_inv]: the output passes the checker [disj_inv],
      which is the whole purpose of the pass.

    The pass is meant to run after distribution (DslDistrib.v), which
    already removes sharing across [SOr]; thresholds are what
    remain. *)

Section DslRepair.

  (** ** Parameters

      The file is parametric in its algebraic setting, exactly like
      the rest of the compiler.

      [F] is the type of scalars with its field structure: the
      constants [zero] and [one], the four binary operations [add],
      [mul], [sub] and [div], negation [opp] and multiplicative
      inverse [inv].  [Fdec] decides equality of scalars; it is what
      lets the soundness proof ask "does this copy carry the same
      value as the original?" and branch on the answer. *)
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}.

  (** [G] is the type of points, forming a group written
      multiplicatively: [gid] is the neutral element, [ginv] the
      inverse, [gop] the product, and [gpow g a] is [g] raised to the
      power [a].  [Gdec] decides equality of points. *)
  Context
    {G : Type}
    {gid : G}
    {ginv : G -> G}
    {gop : G -> G -> G}
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}.

  (** [V] is the type of names, kept abstract: private variables,
      point names and public scalar names are all drawn from it.  All
      that is needed of it here is that names can be compared, which
      is [vdec].  VarType.v provides concrete instances together with
      a generator of fresh names, which is what a caller of this pass
      uses to obtain the new names it must supply. *)
  Context
    {V : Type}
    {vdec : forall x y : V, {x = y} + {x <> y}}.

  (** Local notation.  The infix symbols abbreviate exponentiation
      and the field operations, while the abbreviations whose names
      end in the letter C are constructions of Dsl.v, DslDistrib.v
      and DslRename.v already applied to this section's parameters:
      [equationC] and [stmtC]
      are equations and statements over this [F] and [V],
      [and_distribC] is the conjunction that distributes over
      disjunctions, [rename_stmtC] renames one variable throughout a
      statement, [overrideC] changes one entry of an environment, and
      [rename_varC] renames a single name. *)
  #[local] Infix "^" := gpow.
  #[local] Infix "*" := mul.
  #[local] Infix "+" := add.
  #[local] Infix "-" := sub.

  #[local] Notation veqb := (@veqb V vdec).
  #[local] Notation equationC := (@equation F V).
  #[local] Notation stmtC := (@stmt F V).
  #[local] Notation and_distribC := (@and_distrib F V).
  #[local] Notation rename_stmtC := (@rename_stmt F V vdec).
  #[local] Notation overrideC := (@override F V vdec).
  #[local] Notation rename_varC := (@rename_var V vdec).

  (** ** The repaired statement

      The commitment equation, that is [C = A ^ v * B ^ w] written as
      a DSL equation.

      All five arguments are names.  [Cn] names the point that holds
      the commitment, [An] and [Bn] name the two public bases, [v]
      names the private scalar that is committed to and [w] names the
      randomness.  The equation is built with [simple_eq], the
      readable "this point equals this product of terms" form, and
      both terms carry the coefficient [PConst one], so they are
      plainly [A ^ v] and [B ^ w] with no public multiplier in front. *)
  Definition commit_eq (Cn An Bn v w : V) : equationC :=
    simple_eq (one := one) Cn
      (List.cons (mkterm (PConst one) v An)
        (List.cons (mkterm (PConst one) w Bn) List.nil)).

  (** The same commitment equation packaged as a statement, so that
      it can be conjoined with other statements.  It is an [SEqs]
      node holding the single equation [commit_eq]. *)
  Definition bind_stmt (Cn An Bn v w : V) : stmtC :=
    SEqs (List.cons (commit_eq Cn An Bn v w) List.nil).

  (** Repair one child of the threshold.

      [nm] is the pair of fresh names reserved for this child:
      [fst nm] is the child's private copy of the shared variable
      [x], and [snd nm] is the child's own randomness.  The child
      statement [s] is rewritten so that every occurrence of [x]
      speaks about [fst nm] instead, and the equation saying that
      this copy opens the commitment stored at [Cn] is conjoined to
      it.

      The conjunction used is [and_distribC], not a plain [SAnd].
      That matters for the checker: when [s] is a disjunction of pure
      equation blocks, distributing the bind equation into each
      disjunct keeps the result a disjunction of pure blocks, whereas
      a plain [SAnd] would leave a node that the checker treats as
      impure and then subjects to a disjointness test. *)
  Definition repair_child (Cn An Bn x : V) (nm : V * V) (s : stmtC) : stmtC :=
    and_distribC (bind_stmt Cn An Bn (fst nm) (snd nm))
      (rename_stmtC x (fst nm) s).

  (** Repair a whole list of children, walking the list of fresh
      name pairs and the list of children side by side, one pair per
      child.

      The recursion stops as soon as either list runs out.  That is
      why every lemma about this function carries the hypothesis that
      the two lists have the same length: without it the function
      would silently drop children. *)
  Fixpoint repair_children (Cn An Bn x : V) (names : list (V * V))
    (l : list stmtC) : list stmtC :=
    match names, l with
    | List.cons nm names', List.cons s l' =>
        List.cons (repair_child Cn An Bn x nm s)
          (repair_children Cn An Bn x names' l')
    | _, _ => List.nil
    end.

  (** The repaired statement.

      Starting from [SAnd R (SThresh t l)] with the private variable
      [x] shared between the conjunct [R] and the children [l], this
      builds

      - on the left, [R] conjoined with the equation saying that the
        point [Cn] is the commitment to [x] with randomness [r];
      - on the right, the same threshold over the repaired children,
        each carrying its own copy of [x] bound to that same
        commitment.

      [names] supplies one fresh pair of names per child, [Cn] is the
      fresh point name for the commitment, [r] the fresh root
      randomness, and [An], [Bn] name the two public bases.  Nothing
      here checks that the new names really are fresh; the lemmas
      below state precisely which freshness conditions they need. *)
  Definition repair_thresh (Cn An Bn x r : V) (names : list (V * V))
    (R : stmtC) (t : nat) (l : list stmtC) : stmtC :=
    SAnd (and_distribC R (bind_stmt Cn An Bn x r))
      (SThresh t (repair_children Cn An Bn x names l)).

  (** Update an environment at several names at once: [kvs] is a
      list of name and value pairs, and [override_list w kvs] behaves
      like [w] everywhere except at those names, where it returns the
      stored value.

      The head of the list is applied last and therefore wins if a
      name were to occur twice.  That situation never arises below,
      because the names being added are fresh and pairwise distinct,
      but it is the reason the lemma [override_list_in] asks for
      distinct keys. *)
  Fixpoint override_list (w : V -> F) (kvs : list (V * F)) : V -> F :=
    match kvs with
    | List.nil => w
    | List.cons kv kvs' => overrideC (override_list w kvs') (fst kv) (snd kv)
    end.

  (** ** Semantics

      Everything from here on is stated against one fixed pair of
      public environments: [genv], giving a group element to every
      point name, and [penv], giving a scalar to every public scalar
      name.  The notations abbreviate the denotations of Dsl.v:
      [stmt_denoteC wenv s] is the proposition "the statement [s]
      holds for the witness environment [wenv]", [eq_denoteC] is the
      same for a single equation, and [flagged_denoteC wenv l bs]
      says that every child of [l] whose flag in [bs] is set holds,
      which is how a threshold node is unfolded. *)
  Section Spec.

    Variable genv : V -> G.
    Variable penv : V -> F.

    #[local] Notation stmt_denoteC :=
      (@stmt_denote F add mul opp G gid gop gpow V genv penv).
    #[local] Notation eq_denoteC :=
      (@eq_denote F add mul opp G gid gop gpow V genv penv).
    #[local] Notation flagged_denoteC :=
      (@flagged_denote F add mul opp G gid gop gpow V genv penv).

    (** ** Proofs

        The proofs need the algebraic laws, collected in [Hvec]: the
        scalars form a field, the points form a commutative group,
        and exponentiation makes the points a vector space over the
        scalars.  Registering the field with the [field] tactic lets
        routine scalar identities be discharged automatically. *)
    Section Proofs.

      Context
        {Hvec : @vector_space F (@eq F) zero one add mul sub
          div opp inv G (@eq G) gid ginv gop gpow}.
      Add Field field : (@field_theory_for_stdlib_tactic F
        eq zero one opp add mul sub inv div vector_space_field).

      (** Reading the commitment equation back.

          The generic equation semantics of Dsl.v puts every equation
          in the homogeneous form "this product of powers equals the
          neutral element".  This lemma says that for [commit_eq]
          that unfolds to what one expects: the point [Cn] is equal
          to the product of [An] raised to the value of [v] and [Bn]
          raised to the value of [w], the two values being read out
          of the witness environment [wenv].

          It holds because [simple_eq] already isolates [Cn] on one
          side, and the two coefficients are [one], so multiplying by
          them changes nothing. *)
      Lemma commit_eq_denote :
        ∀ (wenv : V -> F) (Cn An Bn v w : V),
        eq_denoteC wenv (commit_eq Cn An Bn v w) <->
        genv Cn = gop ((genv An) ^ (wenv v)) ((genv Bn) ^ (wenv w)).
      Proof.
        intros *.
        unfold commit_eq.
        rewrite (simple_eq_denote genv penv (Hvec := Hvec)).
        unfold terms_fold, term_denote; cbn.
        assert (h1 : ∀ c : F, one * c = c). { intro; field. }
        rewrite !h1, right_identity.
        reflexivity.
      Qed.

      (** The same reading one level up: the statement built from
          the single commitment equation holds exactly when that
          equation holds.  An [SEqs] node denotes a [List.Forall]
          over its list of equations, and here the list has one
          element. *)
      Lemma bind_stmt_denote :
        ∀ (wenv : V -> F) (Cn An Bn v w : V),
        stmt_denoteC wenv (bind_stmt Cn An Bn v w) <->
        genv Cn = gop ((genv An) ^ (wenv v)) ((genv Bn) ^ (wenv w)).
      Proof.
        intros *; cbn.
        rewrite <-commit_eq_denote.
        split; intro h.
        + inversion h; assumption.
        + constructor; [exact h | constructor].
      Qed.

      (** Binding: two openings of one commitment give a discrete
          logarithm.

          Suppose one group element is written both as
          [gop (A ^ x) (B ^ r)] and as [gop (A ^ x') (B ^ r')], and
          suppose the two committed values [x] and [x'] are
          different.  Then one can exhibit a scalar [d] with
          [A = B ^ d], the discrete logarithm of [A] to the base [B].

          The witness is [d = (r' - r) * inv (x - x')].  Dividing the
          two readings of the element by each other gives
          [A ^ (x - x') = B ^ (r' - r)].  Because [x] and [x']
          differ, the scalar [x - x'] is nonzero and so has an
          inverse; raising both sides to that inverse power leaves
          [A] alone on the left and exactly [B ^ d] on the right.

          This lemma carries the cryptographic content of the whole
          pass, and it is worth being precise about what it does and
          does not assume.  It assumes nothing: it computes [d].
          What the hardness of discrete logarithms buys is that its
          hypothesis is unsatisfiable in practice for an honestly
          generated pair of bases, and that is exactly what it means
          for a Pedersen commitment to be binding. *)
      Lemma two_openings_dlog :
        ∀ (A B : G) (x r x' r' : F),
        gop (A ^ x) (B ^ r) = gop (A ^ x') (B ^ r') ->
        x <> x' ->
        ∃ d : F, A = B ^ d.
      Proof.
        intros A B x r x' r' heq hne.
        exists ((r' - r) * inv (x - x')).
        assert (hsub : ∀ (g : G) (a b : F),
          g ^ (a - b) = gop (g ^ a) (ginv (g ^ b))).
        { intros g a b.
          rewrite ring_sub_definition, smul_distributive_fadd.
          rewrite <-connection_between_vopp_and_fopp. reflexivity. }
        (* A^(x - x') = B^(r' - r) *)
        assert (hAB : A ^ (x - x') = B ^ (r' - r)).
        { rewrite !hsub.
          eapply f_equal with (f := fun z => gop z (ginv (B ^ r))) in heq.
          eapply f_equal with (f := fun z => gop (ginv (A ^ x')) z) in heq.
          rewrite <-associative, right_inverse, right_identity in heq.
          rewrite (commutative (ginv (A ^ x'))) in heq.
          rewrite <-!associative in heq.
          rewrite associative, left_inverse, left_identity in heq.
          exact heq. }
        assert (hinv : (x - x') * inv (x - x') = one).
        { field. intro h. eapply hne.
          eapply f_equal with (f := fun z => z + x') in h.
          assert (hz : ∀ a : F, a - x' + x' = a). { intro; field. }
          rewrite hz in h.
          assert (h0 : zero + x' = x'). { field. }
          rewrite h0 in h. exact h. }
        rewrite <-(field_one A).
        rewrite <-hinv, smul_associative_fmul, hAB, <-smul_associative_fmul.
        reflexivity.
      Qed.

      (** One repaired child either gives back the original child,
          or gives a discrete logarithm.

          The hypotheses are: the root commitment equation holds,
          that is, the point [Cn] holds the commitment to the value
          [wenv] gives to [x] with randomness [wenv r]; and the
          repaired child holds under that same [wenv].

          The repaired child asserts two things: the child's copy
          [fst nm] opens the commitment at [Cn], and the renamed
          child statement holds.  Compare the value of the copy with
          the value of [x].  If the two agree, the renamed statement
          means the original statement read in an environment that
          differs from [wenv] only at [x], where the values agree
          anyway, so the original child holds by [stmt_denote_ext].
          If they differ, then [Cn] has been opened twice with two
          different values, and [two_openings_dlog] converts that
          into a discrete logarithm of [genv An] to the base
          [genv Bn]. *)
      Lemma repair_child_sound :
        ∀ (wenv : V -> F) (Cn An Bn x r : V) (nm : V * V) (s : stmtC),
        genv Cn = gop ((genv An) ^ (wenv x)) ((genv Bn) ^ (wenv r)) ->
        stmt_denoteC wenv (repair_child Cn An Bn x nm s) ->
        stmt_denoteC wenv s \/
        (∃ d : F, genv An = (genv Bn) ^ d).
      Proof.
        intros wenv Cn An Bn x r nm s hroot hc.
        unfold repair_child in hc.
        eapply and_distrib_denote in hc.
        destruct hc as (hbind & hren).
        eapply bind_stmt_denote in hbind.
        eapply rename_stmt_denote in hren.
        destruct (Fdec (wenv (fst nm)) (wenv x)) as [heq | hne].
        +
          left.
          eapply stmt_denote_ext; [| exact hren].
          intros y hy. unfold override, Dsl.veqb.
          destruct (vdec y x) as [-> | hyx]; [exact heq | reflexivity].
        +
          right.
          eapply (two_openings_dlog (genv An) (genv Bn) (wenv x) (wenv r)
            (wenv (fst nm)) (wenv (snd nm))).
          - rewrite <-hroot, <-hbind. reflexivity.
          - intro h; eapply hne; symmetry; exact h.
      Qed.

      (** Repairing preserves the number of children, provided one
          pair of fresh names was supplied per child.  This is needed
          because a threshold node carries a list of flags, one per
          child, and its semantics insists that the flag list and the
          child list have the same length. *)
      Lemma repair_children_length :
        ∀ (Cn An Bn x : V) (names : list (V * V)) (l : list stmtC),
        List.length names = List.length l ->
        List.length (repair_children Cn An Bn x names l) = List.length l.
      Proof.
        intros Cn An Bn x names.
        induction names as [|nm names ih]; intros [|s l] hl;
        cbn in hl |- *; try lia.
        rewrite ih; [reflexivity | lia].
      Qed.

      (** The list version of [repair_child_sound].

          [bs] is the flag list of the threshold: the prover claims
          the children whose flag is set.  If the root commitment
          equation holds and every claimed repaired child holds, then
          either every claimed original child holds, or some child
          hands over a discrete logarithm.

          The proof walks the three lists together.  A child whose
          flag is unset asserts nothing and is passed over; a flagged
          child is handled by [repair_child_sound], and whichever of
          the two outcomes it yields is propagated to the whole
          list. *)
      Lemma repair_children_sound :
        ∀ (wenv : V -> F) (Cn An Bn x r : V) (names : list (V * V))
          (l : list stmtC) (bs : list bool),
        genv Cn = gop ((genv An) ^ (wenv x)) ((genv Bn) ^ (wenv r)) ->
        List.length names = List.length l ->
        flagged_denoteC wenv (repair_children Cn An Bn x names l) bs ->
        flagged_denoteC wenv l bs \/
        (∃ d : F, genv An = (genv Bn) ^ d).
      Proof.
        intros wenv Cn An Bn x r names.
        induction names as [|nm names ih]; intros [|s l] [|b bs] hroot hl hf;
        cbn in hl, hf |- *; try (left; exact I); try lia.
        destruct hf as (hs & hf).
        destruct (ih l bs hroot ltac:(lia) hf) as [hrest | hd];
        [| right; exact hd].
        destruct b.
        +
          destruct (repair_child_sound wenv Cn An Bn x r nm s hroot hs)
            as [hs' | hd]; [| right; exact hd].
          left; split; [exact hs' | exact hrest].
        +
          left; split; [exact I | exact hrest].
      Qed.

      (** ** Soundness

          Soundness is the direction that protects the verifier: what
          has been proven about the repaired statement must say
          something about the original one.

          The theorem is a dichotomy.  Given one pair of fresh names
          per child, and given any witness environment [wenv]
          satisfying the repaired statement, either

          - [wenv] satisfies the original statement
            [SAnd R (SThresh t l)] as well, or
          - there is a scalar [d] with [genv An = (genv Bn) ^ d].

          Why it holds: the left conjunct of the repaired statement
          yields both [R] and the root commitment equation, so [Cn]
          really does hold a commitment to the value of [x].  The
          threshold yields a flag list together with the repaired
          children, and [repair_children_sound] says the claimed
          children either hold in their original form or produce the
          discrete logarithm.  The same flag list is handed back
          unchanged, and its length still matches because repairing
          preserves the number of children.

          Note what is not assumed.  No hardness assumption appears
          anywhere in this proof; the second case is a value the
          proof actually computes.  The cryptography enters only in
          the reading of the statement: after an honest setup of the
          two bases nobody knows a discrete logarithm of [genv An] to
          the base [genv Bn], so the second case cannot be produced,
          and a prover who convinces a verifier of the repaired
          statement has really proven the original one. *)
      Theorem repair_sound :
        ∀ (wenv : V -> F) (Cn An Bn x r : V) (names : list (V * V))
          (R : stmtC) (t : nat) (l : list stmtC),
        List.length names = List.length l ->
        stmt_denoteC wenv (repair_thresh Cn An Bn x r names R t l) ->
        stmt_denoteC wenv (SAnd R (SThresh t l)) \/
        (∃ d : F, genv An = (genv Bn) ^ d).
      Proof.
        intros wenv Cn An Bn x r names R t l hl hrep.
        unfold repair_thresh in hrep.
        cbn [stmt_denote] in hrep.
        destruct hrep as (hR & hth).
        eapply and_distrib_denote in hR. destruct hR as (hR & hroot).
        eapply bind_stmt_denote in hroot.
        eapply (stmt_denote_thresh genv penv) in hth.
        destruct hth as (bs & hlen & hcnt & hf).
        destruct (repair_children_sound wenv Cn An Bn x r names l bs hroot hl hf)
          as [hf' | hd]; [| right; exact hd].
        left. cbn [stmt_denote]. split; [exact hR |].
        eapply (stmt_denote_thresh genv penv).
        exists bs. split; [| split; [exact hcnt | exact hf']].
        rewrite hlen. eapply repair_children_length; exact hl.
      Qed.

      (** ** Completeness

          Completeness is the direction that protects the prover:
          everything that could be proven before the rewrite can
          still be proven after it.  The work is bookkeeping about
          the new names.  One has to exhibit values for them and
          check that adding those values disturbs nothing that was
          already there. *)

      (** A name that is not among the updated keys keeps its old
          value.  This is the frame property of [override_list], and
          it is what lets the original variables of a statement be
          read unchanged after all the fresh names have been added to
          the environment. *)
      Lemma override_list_notin :
        ∀ (w : V -> F) (kvs : list (V * F)) (v : V),
        ~ List.In v (List.map fst kvs) -> override_list w kvs v = w v.
      Proof.
        intros w kvs v.
        induction kvs as [|kv kvs ih]; intro hnin; cbn.
        + reflexivity.
        + unfold override, Dsl.veqb.
          destruct (vdec v (fst kv)) as [heq | hne].
          - exfalso; eapply hnin; left; symmetry; exact heq.
          - eapply ih; intro hin; eapply hnin; right; exact hin.
      Qed.

      (** A name that is among the updated keys reads back the value
          stored with it, provided the keys are pairwise distinct.
          Distinctness is needed because [override_list] applies the
          head of the list last: without it, one pair could shadow
          another pair carrying the same key. *)
      Lemma override_list_in :
        ∀ (w : V -> F) (kvs : list (V * F)) (k : V) (val : F),
        List.NoDup (List.map fst kvs) -> List.In (k, val) kvs ->
        override_list w kvs k = val.
      Proof.
        intros w kvs k val.
        induction kvs as [|kv kvs ih]; intros hnd hin; cbn in hin |- *.
        + contradiction.
        + inversion hnd as [| ? ? hnin hnd']; subst.
          unfold override, Dsl.veqb.
          destruct hin as [hin | hin].
          - subst kv; cbn. destruct (vdec k k); [reflexivity | congruence].
          - destruct (vdec k (fst kv)) as [heq | hne].
            * exfalso; eapply hnin. rewrite <-heq.
              eapply List.in_map with (f := fst) in hin. exact hin.
            * eapply ih; assumption.
      Qed.

      (** The names the repair introduces: the root randomness [r],
          and for every child its copy of the shared variable
          followed by its own randomness.

          Collecting them in one list is convenient, because
          freshness then becomes a single statement: this list has no
          repetition, and it meets none of the names already used by
          the input statement. *)
      Definition new_names (r : V) (names : list (V * V)) : list V :=
        List.cons r
          (List.flat_map (fun nm => List.cons (fst nm) (List.cons (snd nm) List.nil))
            names).

      (** The values those new names take in the repaired witness
          environment, as a list of name and value pairs whose keys
          are exactly [new_names], see [new_values_fst].

          Every copy of the shared variable receives the value that
          [wenv] gives to [x].  That is what makes all the children
          open one and the same commitment.  The root randomness and
          every child randomness receive [zero].

          As far as this file is concerned any randomness would do,
          and [zero] is the simplest choice that makes the equations
          come out right.  Randomness is what hides the committed
          value, and hiding is not among the properties proven
          here. *)
      Definition new_values (wenv : V -> F) (x r : V) (names : list (V * V))
        : list (V * F) :=
        List.cons (r, zero)
          (List.flat_map (fun nm =>
             List.cons (fst nm, wenv x) (List.cons (snd nm, zero) List.nil))
            names).

      (** The repaired point environment: the same as [genv]
          everywhere except at the fresh name [Cn], which now holds
          the commitment to the value of [x] with randomness [zero].

          This is the only public data the pass adds.  In a
          deployment it is the group element the prover publishes
          alongside the proof. *)
      Definition repaired_genv (wenv : V -> F) (Cn An Bn x : V) : V -> G :=
        fun P => if veqb P Cn
                 then gop ((genv An) ^ (wenv x)) ((genv Bn) ^ zero)
                 else genv P.

      (** The keys of [new_values] are exactly [new_names].  This is
          the bridge that turns a freshness hypothesis stated about
          [new_names] into the pairwise distinctness of keys that the
          [override_list] lemmas ask for. *)
      Lemma new_values_fst :
        ∀ (wenv : V -> F) (x r : V) (names : list (V * V)),
        List.map fst (new_values wenv x r names) = new_names r names.
      Proof.
        intros; unfold new_values, new_names; cbn; f_equal.
        induction names as [|nm names ih]; cbn; [reflexivity |].
        rewrite ih; reflexivity.
      Qed.

      (** Each child's pair of new names contributes its two entries
          to [new_values]: the copy paired with the value of [x], the
          randomness paired with [zero].  This is how one computes
          what the repaired environment gives to a particular
          child. *)
      Lemma in_new_values :
        ∀ (wenv : V -> F) (x r : V) (names : list (V * V)) (nm : V * V),
        List.In nm names ->
        List.In (fst nm, wenv x) (new_values wenv x r names) ∧
        List.In (snd nm, zero) (new_values wenv x r names).
      Proof.
        intros wenv x r names nm hin.
        unfold new_values; split; right; eapply List.in_flat_map;
        exists nm; split; try exact hin.
        + left; reflexivity.
        + right; left; reflexivity.
      Qed.

      (** [bind_stmt_denote] again, but for an arbitrary point
          environment [g] in place of the fixed [genv].

          Completeness has to evaluate the commitment equation in the
          repaired point environment, which differs from [genv]
          precisely at [Cn], so the fixed-environment version of the
          lemma cannot be used there.  The statement and the reason
          are otherwise identical. *)
      Lemma bind_stmt_denote_gen :
        ∀ (g : V -> G) (wenv : V -> F) (Cn An Bn v w : V),
        @stmt_denote F add mul opp G gid gop gpow V g penv wenv
          (bind_stmt Cn An Bn v w) <->
        g Cn = gop ((g An) ^ (wenv v)) ((g Bn) ^ (wenv w)).
      Proof.
        intros g wenv Cn An Bn v w; cbn.
        unfold commit_eq.
        assert (h := simple_eq_denote g penv (Hvec := Hvec) Cn
          (List.cons (mkterm (PConst one) v An)
            (List.cons (mkterm (PConst one) w Bn) List.nil)) wenv).
        unfold terms_fold, term_denote in h; cbn in h.
        assert (h1 : ∀ c : F, one * c = c). { intro; field. }
        rewrite !h1, right_identity in h.
        rewrite <-h.
        split; intro hh.
        + inversion hh; assumption.
        + constructor; [exact hh | constructor].
      Qed.

      (** Every claimed child still holds after the repair.

          The list [names] being repaired is a sublist of the full
          list [names0] that determines the environment; that is what
          the inclusion hypothesis expresses, and it is what lets the
          induction peel off one child at a time while the two
          environments stay fixed.

          The other hypotheses are the freshness conditions.  The
          names in [new_names] have no repetition and none of them
          occurs in [used], while every variable of the children does
          occur in [used], so the new names are genuinely new.  The
          commitment name [Cn] is not a point name of the children
          and differs from the two bases [An] and [Bn], so
          overwriting the point environment at [Cn] cannot change the
          meaning of anything that was already written.

          Given that the flagged original children hold, the flagged
          repaired children hold in the repaired environments.  There
          are two things to check per child.  The bind equation holds
          by the very definition of [repaired_genv], once one knows
          that the child's copy carries the value of [x] and its
          randomness carries [zero].  The renamed child holds because
          its copy carries the value of [x], so reading the copy is
          the same as reading [x], and because freshness lets the
          original child be transported across both environment
          changes. *)
      Lemma repair_children_complete :
        ∀ (wenv : V -> F) (Cn An Bn x r : V) (names0 names : list (V * V))
          (l : list stmtC) (bs : list bool) (used : list V),
        List.incl names names0 ->
        List.length names = List.length l ->
        List.NoDup (new_names r names0) ->
        (∀ v, List.In v (new_names r names0) -> ~ List.In v used) ->
        List.incl (vars_of_list l) used ->
        ~ List.In Cn (stmt_points (SThresh 0 l)) ->
        Cn <> An -> Cn <> Bn ->
        flagged_denoteC wenv l bs ->
        @flagged_denote F add mul opp G gid gop gpow V
          (repaired_genv wenv Cn An Bn x) penv
          (override_list wenv (new_values wenv x r names0))
          (repair_children Cn An Bn x names l) bs.
      Proof.
        intros wenv Cn An Bn x r names0 names.
        induction names as [|nm names ih];
        intros [|s l] [|b bs] used hincl hl hnd hfresh hused hCn hCA hCB hf;
        cbn [List.length] in hl; cbn [repair_children flagged_denote] in hf |- *;
        try exact I; try lia.
        destruct hf as (hs & hf).
        assert (hnm : List.In nm names0). { eapply hincl; left; reflexivity. }
        destruct (in_new_values wenv x r names0 nm hnm) as (hx' & hr').
        assert (hndf : List.NoDup (List.map fst (new_values wenv x r names0))).
        { rewrite new_values_fst; exact hnd. }
        split.
        +
          destruct b; [| exact I].
          unfold repair_child.
          refine (proj2 (and_distrib_denote (repaired_genv wenv Cn An Bn x) penv _
            (bind_stmt Cn An Bn (fst nm) (snd nm)) (rename_stmtC x (fst nm) s)) _).
          split.
          -
            eapply bind_stmt_denote_gen.
            unfold repaired_genv.
            rewrite veqb_refl.
            assert (hA : veqb An Cn = false).
            { unfold Dsl.veqb; destruct (vdec An Cn); [congruence | reflexivity]. }
            assert (hB : veqb Bn Cn = false).
            { unfold Dsl.veqb; destruct (vdec Bn Cn); [congruence | reflexivity]. }
            rewrite hA, hB.
            rewrite (override_list_in _ _ _ _ hndf hx').
            rewrite (override_list_in _ _ _ _ hndf hr').
            reflexivity.
          -
            eapply rename_stmt_denote.
            rewrite (override_list_in _ _ _ _ hndf hx').
            eapply (stmt_denote_genv_ext penv genv).
            { intros P hP. unfold repaired_genv, Dsl.veqb.
              destruct (vdec P Cn) as [-> | hne]; [| reflexivity].
              exfalso; eapply hCn; cbn; eapply List.in_or_app; left; exact hP. }
            eapply stmt_denote_ext; [| exact hs].
            intros y hy.
            unfold override, Dsl.veqb.
            destruct (vdec y x) as [-> | hyx]; [reflexivity |].
            symmetry; eapply override_list_notin.
            rewrite new_values_fst. intro hin.
            eapply (hfresh y hin). eapply hused. unfold vars_of_list; cbn.
            eapply List.in_or_app; left; exact hy.
        +
          eapply (ih l bs used); try assumption.
          - intros nm' hin; eapply hincl; right; exact hin.
          - lia.
          - intros v hv; eapply hused. unfold vars_of_list in hv |- *; cbn.
            eapply List.in_or_app; right; exact hv.
          - intro hin; eapply hCn; cbn in hin |- *.
            eapply List.in_or_app; right; exact hin.
      Qed.

      (** Completeness of the repair.

          The hypotheses are the freshness contract the caller must
          honour: one pair of names per child; the introduced names
          [new_names] are pairwise distinct; none of them is [x] or
          occurs in [R] or in the children; and the commitment name
          [Cn] is not a point name of [R] or of the threshold and is
          neither of the two bases.

          The conclusion says that from a witness environment [wenv]
          satisfying the original statement one can build a point
          environment [genv'] and a witness environment [wenv']
          satisfying the repaired statement, and that [genv'] agrees
          with [genv] at every point name other than [Cn].  In other
          words the only public data that changes is the one new
          commitment, which is precisely the extra message an honest
          prover has to publish.

          The construction is the expected one: [genv'] is
          [repaired_genv] and [wenv'] extends [wenv] with
          [new_values].  The left conjunct holds because [R] is
          untouched by the new names and by the new point, and
          because the root commitment equation holds by construction.
          The threshold reuses the very same flag list as the
          original proof, so the same children are claimed, and
          [repair_children_complete] discharges them. *)
      Theorem repair_complete :
        ∀ (wenv : V -> F) (Cn An Bn x r : V) (names : list (V * V))
          (R : stmtC) (t : nat) (l : list stmtC),
        List.length names = List.length l ->
        List.NoDup (new_names r names) ->
        (∀ v, List.In v (new_names r names) ->
           ~ List.In v (List.cons x (List.app (stmt_vars R) (vars_of_list l)))) ->
        ~ List.In Cn (List.app (stmt_points R) (stmt_points (SThresh t l))) ->
        Cn <> An -> Cn <> Bn ->
        stmt_denoteC wenv (SAnd R (SThresh t l)) ->
        ∃ (genv' : V -> G) (wenv' : V -> F),
          (∀ P, P <> Cn -> genv' P = genv P) ∧
          @stmt_denote F add mul opp G gid gop gpow V genv' penv wenv'
            (repair_thresh Cn An Bn x r names R t l).
      Proof.
        intros wenv Cn An Bn x r names R t l hl hnd hfresh hCn hCA hCB hd.
        cbn [stmt_denote] in hd. destruct hd as (hR & hth).
        eapply (stmt_denote_thresh genv penv) in hth.
        destruct hth as (bs & hlen & hcnt & hf).
        assert (hndf : List.NoDup (List.map fst (new_values wenv x r names))).
        { rewrite new_values_fst; exact hnd. }
        assert (hxnew : ~ List.In x (new_names r names)).
        { intro hin; eapply (hfresh x hin); left; reflexivity. }
        exists (repaired_genv wenv Cn An Bn x),
          (override_list wenv (new_values wenv x r names)).
        split.
        +
          intros P hP. unfold repaired_genv, Dsl.veqb.
          destruct (vdec P Cn); [congruence | reflexivity].
        +
          unfold repair_thresh. cbn [stmt_denote]. split.
          -
            refine (proj2 (and_distrib_denote (repaired_genv wenv Cn An Bn x) penv _
              R (bind_stmt Cn An Bn x r)) _).
            split.
            *
              eapply (stmt_denote_genv_ext penv genv).
              { intros P hP. unfold repaired_genv, Dsl.veqb.
                destruct (vdec P Cn) as [-> | hne]; [| reflexivity].
                exfalso; eapply hCn; eapply List.in_or_app; left; exact hP. }
              eapply stmt_denote_ext; [| exact hR].
              intros y hy. symmetry; eapply override_list_notin.
              rewrite new_values_fst. intro hin.
              eapply (hfresh y hin). right; eapply List.in_or_app; left; exact hy.
            *
              eapply bind_stmt_denote_gen.
              unfold repaired_genv. rewrite veqb_refl.
              assert (hA : veqb An Cn = false).
              { unfold Dsl.veqb; destruct (vdec An Cn); [congruence | reflexivity]. }
              assert (hB : veqb Bn Cn = false).
              { unfold Dsl.veqb; destruct (vdec Bn Cn); [congruence | reflexivity]. }
              rewrite hA, hB.
              rewrite (override_list_notin _ _ x); [| rewrite new_values_fst; exact hxnew].
              rewrite (override_list_in _ _ r zero hndf); [reflexivity | left; reflexivity].
          -
            eapply (stmt_denote_thresh _ penv).
            exists bs.
            split; [rewrite hlen; symmetry; eapply repair_children_length; exact hl |
                    split; [exact hcnt |]].
            eapply (repair_children_complete wenv Cn An Bn x r names names l bs
              (List.cons x (List.app (stmt_vars R) (vars_of_list l)))); try assumption.
            * eapply List.incl_refl.
            * intros v hv; right; eapply List.in_or_app; right; exact hv.
            * intro hin; eapply hCn; eapply List.in_or_app; right; exact hin.
      Qed.

      (** ** The output passes the checker

          The purpose of the pass is that [disj_inv] accepts what it
          produces.  The lemmas below compute the variable sets of
          the repaired statement and establish the disjointness
          conditions that the checker tests. *)

      (** The boolean test [disjointb] returns [true] whenever the
          two lists really do share no name.  This is the bridge from
          the set-theoretic reasoning carried out in the proofs to
          the boolean that the checker computes. *)
      Lemma disjointb_intro :
        ∀ (l₁ l₂ : list V),
        (∀ v, List.In v l₁ -> ~ List.In v l₂) ->
        @disjointb V vdec l₁ l₂ = true.
      Proof.
        intros l₁ l₂ h.
        unfold disjointb.
        eapply List.forallb_forall.
        intros v hv.
        eapply negb_true_iff.
        destruct (List.existsb (veqb v) l₂) eqn:he; [| reflexivity].
        exfalso.
        eapply List.existsb_exists in he.
        destruct he as (u & hu & hvu).
        eapply veqb_eq in hvu; subst.
        eapply (h u hv hu).
      Qed.

      (** Renaming a variable does not change the shape of a
          statement, so a disjunction of pure equation blocks stays
          one.  [dnf] is the boolean test for that shape.

          It matters here because each repaired child is built by
          distributing an equation into a renamed child, and
          distribution only preserves the good shape when what it
          distributes into already has it. *)
      Lemma dnf_rename :
        ∀ (x y : V) (s : stmtC), dnf s = true -> dnf (rename_stmtC x y s) = true.
      Proof.
        intros x y s.
        induction s as [eqs | a b iha ihb | a b iha ihb | t l ihl]
          using stmt_ind'; intro h; cbn in h |- *; try discriminate.
        + reflexivity.
        + eapply andb_true_iff in h; destruct h as (ha & hb).
          rewrite (iha ha), (ihb hb). reflexivity.
      Qed.

      (** Where the variables of a repaired child can come from:
          either they are variables of the original child with [x]
          renamed to that child's copy, or they are one of the
          child's two new names.

          Nothing else appears, because the bind equation mentions
          only the copy and the randomness as private variables; the
          commitment and the two bases are point names, and point
          names are not private variables. *)
      Lemma repair_child_vars_incl :
        ∀ (Cn An Bn x : V) (nm : V * V) (s : stmtC),
        List.incl (stmt_vars (repair_child Cn An Bn x nm s))
          (List.app (List.map (rename_varC x (fst nm)) (stmt_vars s))
            (List.cons (fst nm) (List.cons (snd nm) List.nil))).
      Proof.
        intros Cn An Bn x nm s v hv.
        unfold repair_child in hv.
        eapply and_distrib_vars_incl in hv.
        eapply List.in_app_or in hv.
        destruct hv as [hv | hv].
        +
          cbn in hv.
          destruct hv as [hv | [hv | hv]]; try contradiction; subst;
          eapply List.in_or_app; right;
          [left; reflexivity | right; left; reflexivity].
        +
          rewrite stmt_vars_rename in hv.
          eapply List.in_or_app; left; exact hv.
      Qed.

      (** Every variable of the repaired child list belongs to one
          particular child.  The lemma returns that child together
          with its pair of new names, as an element of
          [List.combine names l], and places the variable in the set
          described by [repair_child_vars_incl]. *)
      Lemma repair_children_vars :
        ∀ (Cn An Bn x : V) (names : list (V * V)) (l : list stmtC) (v : V),
        List.In v (vars_of_list (repair_children Cn An Bn x names l)) ->
        ∃ (nm : V * V) (s : stmtC),
          List.In (nm, s) (List.combine names l) ∧
          List.In v (List.app (List.map (rename_varC x (fst nm)) (stmt_vars s))
            (List.cons (fst nm) (List.cons (snd nm) List.nil))).
      Proof.
        intros Cn An Bn x names.
        induction names as [|nm names ih]; intros [|s l] v hv; cbn in hv;
        try contradiction.
        unfold vars_of_list in hv; cbn in hv.
        eapply List.in_app_or in hv.
        destruct hv as [hv | hv].
        +
          exists nm, s. split; [left; reflexivity |].
          eapply repair_child_vars_incl; exact hv.
        +
          destruct (ih l v hv) as (nm' & s' & hin & hv').
          exists nm', s'. split; [right; exact hin | exact hv'].
      Qed.

      (** The case analysis on such a variable: it is one of the
          child's two new names, or it is a variable of the original
          child that is different from [x].

          It cannot be [x] itself, because every occurrence of [x]
          was renamed away.  This is the fact that makes the repaired
          children pairwise disjoint: the one name they used to share
          is gone from all of them. *)
      Lemma repair_child_var_cases :
        ∀ (x : V) (nm : V * V) (s : stmtC) (v : V),
        List.In v (List.app (List.map (rename_varC x (fst nm)) (stmt_vars s))
          (List.cons (fst nm) (List.cons (snd nm) List.nil))) ->
        (v = fst nm \/ v = snd nm) \/ (v <> x ∧ List.In v (stmt_vars s)).
      Proof.
        intros x nm s v hv.
        eapply List.in_app_or in hv.
        destruct hv as [hv | hv].
        +
          eapply List.in_map_iff in hv.
          destruct hv as (u & hu & hin).
          unfold rename_var, Dsl.veqb in hu.
          destruct (vdec u x) as [-> | hne].
          - left; left; symmetry; exact hu.
          - right; subst; split; assumption.
        +
          destruct hv as [hv | [hv | hv]]; try contradiction;
          left; [left | right]; symmetry; exact hv.
      Qed.

      (** ** Bookkeeping on the new names

          Small list facts about [new_names] and [List.combine],
          pulled out so that the two checker proofs below read as
          arguments rather than as list manipulation. *)

      (** Peeling one child off the list of new names.  If all the
          introduced names are pairwise distinct, then so are those
          of the remaining children, the two names of the child just
          removed occur nowhere in the rest, and those two names
          differ from each other. *)
      Lemma new_names_cons :
        ∀ (r : V) (nm : V * V) (names : list (V * V)),
        List.NoDup (new_names r (List.cons nm names)) ->
        List.NoDup (new_names r names) ∧
        ~ List.In (fst nm) (new_names r names) ∧
        ~ List.In (snd nm) (new_names r names) ∧
        fst nm <> snd nm.
      Proof.
        intros r nm names h.
        unfold new_names in h |- *; cbn in h.
        inversion h as [| ? ? hr hrest]; subst.
        inversion hrest as [| ? ? hf hrest']; subst.
        inversion hrest' as [| ? ? hs hrest'']; subst.
        cbn in hr, hf, hs.
        repeat split.
        + constructor; [| exact hrest''].
          intro hin; eapply hr; right; right; exact hin.
        + intros [hin | hin].
          - eapply hr; left; symmetry; exact hin.
          - eapply hf; right; exact hin.
        + intros [hin | hin].
          - eapply hr; right; left; symmetry; exact hin.
          - eapply hs; exact hin.
        + intro heq; eapply hf; left; symmetry; exact heq.
      Qed.

      (** Adding a child only adds names: every new name of the
          remaining children is still a new name of the whole list.
          This is what lets a freshness hypothesis be handed down to
          the recursive call. *)
      Lemma new_names_incl_tail :
        ∀ (r : V) (nm : V * V) (names : list (V * V)),
        List.incl (new_names r names) (new_names r (List.cons nm names)).
      Proof.
        intros r nm names v hv.
        unfold new_names in hv |- *; cbn.
        destruct hv as [hv | hv]; [left; exact hv | right; right; right; exact hv].
      Qed.

      (** If a child is paired with a name pair in
          [List.combine names l], then both names of that pair are
          among the introduced names [new_names]. *)
      Lemma in_combine_new_names :
        ∀ (r : V) (names : list (V * V)) (l : list stmtC) (nm : V * V) (s : stmtC),
        List.In (nm, s) (List.combine names l) ->
        List.In (fst nm) (new_names r names) ∧ List.In (snd nm) (new_names r names).
      Proof.
        intros r names l nm s hin.
        eapply List.in_combine_l in hin.
        unfold new_names; split; right; eapply List.in_flat_map;
        exists nm; split; try exact hin.
        + left; reflexivity.
        + right; left; reflexivity.
      Qed.

      (** The same fact stated about the flattened tail of
          [new_names], that is about the copies and the child
          randomnesses alone, without the root randomness.  The
          top-level checker proof needs this sharper form, because it
          has to keep the root randomness apart from the per-child
          names. *)
      Lemma in_combine_new_names_tail :
        ∀ (names : list (V * V)) (l : list stmtC) (nm : V * V) (s : stmtC),
        List.In (nm, s) (List.combine names l) ->
        List.In (fst nm)
          (List.flat_map (fun nm => List.cons (fst nm) (List.cons (snd nm) List.nil)) names) ∧
        List.In (snd nm)
          (List.flat_map (fun nm => List.cons (fst nm) (List.cons (snd nm) List.nil)) names).
      Proof.
        intros names l nm s hin.
        eapply List.in_combine_l in hin.
        split; eapply List.in_flat_map; exists nm; split; try exact hin.
        + left; reflexivity.
        + right; left; reflexivity.
      Qed.

      (** A variable of a child occurring in [List.combine names l]
          is a variable of the whole child list.  [vars_of_list] is
          the union of the children's variables. *)
      Lemma in_combine_vars :
        ∀ (names : list (V * V)) (l : list stmtC) (nm : V * V) (s : stmtC) (v : V),
        List.In (nm, s) (List.combine names l) ->
        List.In v (stmt_vars s) -> List.In v (vars_of_list l).
      Proof.
        intros names l nm s v hin hv.
        eapply List.in_combine_r in hin.
        unfold vars_of_list. eapply List.in_flat_map. exists s; split; assumption.
      Qed.

      (** The precondition saying that [x] is the only culprit: no
          two distinct children of the list share any variable other
          than [x].

          Read the definition child by child: any variable the head
          shares with the rest of the list must be [x], and the same
          holds recursively down the list.  This is what remains to
          be repaired once distribution has dealt with the
          disjunctions, and it is the hypothesis under which the
          repair restores the invariant. *)
      Fixpoint pairwise_except (x : V) (l : list stmtC) : Prop :=
        match l with
        | List.nil => True
        | List.cons s l' =>
            (∀ v, List.In v (stmt_vars s) -> List.In v (vars_of_list l') -> v = x) ∧
            pairwise_except x l'
        end.

      (** The repaired threshold node passes the checker.

          The hypotheses are: every child is a disjunction of pure
          blocks; one name pair per child; the introduced names are
          pairwise distinct and are neither [x] nor variables of the
          children; and [x] is the only variable that two distinct
          children share.

          The checker asks two things of a threshold node: that each
          child pass on its own, and that the children have pairwise
          disjoint variable sets.  The first holds because a repaired
          child is again a disjunction of pure blocks, and any such
          statement passes, by [dnf_disj_inv].  For the second, take
          a variable of one repaired child and a variable of a later
          one, and apply [repair_child_var_cases] to both.  A new
          name of one child is neither a new name of another, by
          distinctness, nor an original variable, by freshness.  Two
          original variables would have to be shared between distinct
          children, so by [pairwise_except] the shared variable would
          be [x], which no longer occurs anywhere after renaming. *)
      Lemma repair_children_disj_inv :
        ∀ (Cn An Bn x r : V) (names : list (V * V)) (l : list stmtC) (t : nat),
        List.Forall (fun s => dnf s = true) l ->
        List.length names = List.length l ->
        List.NoDup (new_names r names) ->
        (∀ v, List.In v (new_names r names) ->
           ~ List.In v (List.cons x (vars_of_list l))) ->
        pairwise_except x l ->
        @disj_inv F V vdec (SThresh t (repair_children Cn An Bn x names l)) = true.
      Proof.
        intros Cn An Bn x r names.
        induction names as [|nm names ih]; intros [|s l] t hdnf hl hnd hfresh hpw;
        cbn [List.length] in hl; try lia; try reflexivity.
        destruct (new_names_cons r nm names hnd) as (hnd' & hf & hs & hfs).
        inversion hdnf as [| ? ? hds hdl]; subst.
        destruct hpw as (hpw & hpw').
        assert (hfresh' : ∀ v, List.In v (new_names r names) ->
          ~ List.In v (List.cons x (vars_of_list l))).
        { intros v hv hin. eapply (hfresh v (new_names_incl_tail r nm names v hv)).
          destruct hin as [hin | hin]; [left; exact hin | right].
          unfold vars_of_list in hin |- *; cbn. eapply List.in_or_app; right; exact hin. }
        specialize (ih l t hdl ltac:(lia) hnd' hfresh' hpw').
        cbn [disj_inv] in ih |- *.
        cbn [repair_children pairwise_disjointb].
        eapply andb_true_iff in ih; destruct ih as (ihp & ihg).
        rewrite ihp, ihg.
        assert (hchild : @disj_inv F V vdec (repair_child Cn An Bn x nm s) = true).
        { eapply dnf_disj_inv. unfold repair_child.
          eapply and_distrib_dnf; [reflexivity |].
          eapply dnf_rename; exact hds. }
        rewrite hchild.
        rewrite disjointb_intro; [reflexivity |].
        intros v hv1 hv2.
        eapply repair_child_vars_incl in hv1.
        eapply repair_child_var_cases in hv1.
        eapply repair_children_vars in hv2.
        destruct hv2 as (nm' & s' & hin' & hv2).
        destruct (in_combine_new_names r names l nm' s' hin') as (hf' & hs').
        eapply repair_child_var_cases in hv2.
        destruct hv1 as [hv1 | (hvx & hvs)].
        +
          (* v is one of the head child's fresh names *)
          assert (hvnew : List.In v (new_names r (List.cons nm names))).
          { unfold new_names; cbn.
            destruct hv1 as [-> | ->]; [right; left | right; right; left]; reflexivity. }
          destruct hv2 as [hv2 | (hvx' & hvs')].
          -
            destruct hv1 as [hv1 | hv1]; destruct hv2 as [hv2 | hv2]; rewrite hv1 in hv2.
            * eapply hf; rewrite hv2; exact hf'.
            * eapply hf; rewrite hv2; exact hs'.
            * eapply hs; rewrite hv2; exact hf'.
            * eapply hs; rewrite hv2; exact hs'.
          -
            eapply (hfresh v hvnew). right.
            unfold vars_of_list; cbn. eapply List.in_or_app; right.
            eapply in_combine_vars; eassumption.
        +
          (* v is an original variable of s, v ≠ x *)
          destruct hv2 as [hv2 | (hvx' & hvs')].
          -
            assert (hvnew : List.In v (new_names r (List.cons nm names))).
            { eapply new_names_incl_tail. destruct hv2 as [-> | ->]; assumption. }
            eapply (hfresh v hvnew). right.
            unfold vars_of_list; cbn. eapply List.in_or_app; left; exact hvs.
          -
            eapply hvx. eapply hpw; [exact hvs |].
            eapply in_combine_vars; eassumption.
      Qed.

      (** The repaired statement passes the disjunction-invariant
          checker.  This is the theorem that says the pass has done
          its job.

          Besides the freshness contract on the introduced names, the
          theorem asks that [R] and every child be disjunctions of
          pure equation blocks, that [x] be the only variable [R]
          shares with the children, and that [x] be the only variable
          two distinct children share.

          The output is an [SAnd] whose right side is a threshold and
          therefore not a pure block, so the checker takes its second
          route: it demands that the two sides have disjoint variable
          sets and that each side pass on its own.

          - Disjointness.  The left side contributes the variables of
            [R], plus [x] and the root randomness [r].  The right
            side contributes, for each child, that child's pair of
            new names and its original variables other than [x].  A
            new name on one side cannot meet the other side, by
            freshness; [x] itself no longer occurs on the right,
            having been renamed away in every child; and an original
            variable of [R] meeting an original variable of a child
            would have to be [x] by hypothesis, which is the case
            just excluded.
          - The left side is a distributed conjunction of two
            disjunctions of pure blocks, hence is one itself, and so
            passes.
          - The right side is [repair_children_disj_inv].

          Together with [repair_sound] and [repair_complete] this
          completes the story: the output means the same as the input
          up to an explicit discrete-logarithm escape, an honest
          prover can still prove it, and the compiler now accepts
          it. *)
      Theorem repair_disj_inv :
        ∀ (Cn An Bn x r : V) (names : list (V * V))
          (R : stmtC) (t : nat) (l : list stmtC),
        dnf R = true ->
        List.Forall (fun s => dnf s = true) l ->
        List.length names = List.length l ->
        List.NoDup (new_names r names) ->
        (∀ v, List.In v (new_names r names) ->
           ~ List.In v (List.cons x (List.app (stmt_vars R) (vars_of_list l)))) ->
        (∀ v, List.In v (stmt_vars R) -> List.In v (vars_of_list l) -> v = x) ->
        pairwise_except x l ->
        @disj_inv F V vdec (repair_thresh Cn An Bn x r names R t l) = true.
      Proof.
        intros Cn An Bn x r names R t l hR hdnf hl hnd hfresh hshared hpw.
        unfold repair_thresh.
        assert (hpure : @pureb F V (SThresh t (repair_children Cn An Bn x names l)) = false).
        { reflexivity. }
        cbn [disj_inv].
        rewrite hpure, Bool.andb_false_r; cbn [orb].
        assert (hrnew : ~ List.In r
          (List.flat_map (fun nm => List.cons (fst nm) (List.cons (snd nm) List.nil)) names)).
        { unfold new_names in hnd. inversion hnd; assumption. }
        eapply andb_true_iff; split; [eapply andb_true_iff; split |].
        +
          eapply disjointb_intro.
          intros v hv1 hv2.
          eapply and_distrib_vars_incl in hv1.
          rewrite stmt_vars_thresh in hv2.
          eapply repair_children_vars in hv2.
          destruct hv2 as (nm' & s' & hin' & hv2).
          destruct (in_combine_new_names_tail names l nm' s' hin') as (hf' & hs').
          assert (hnew' : ∀ u, u = fst nm' \/ u = snd nm' -> List.In u (new_names r names)).
          { intros u [-> | ->]; unfold new_names; right; assumption. }
          eapply repair_child_var_cases in hv2.
          eapply List.in_app_or in hv1.
          destruct hv1 as [hv1 | hv1].
          -
            (* v ∈ vars R *)
            destruct hv2 as [hv2 | (hvx & hvs)].
            * eapply (hfresh v (hnew' v hv2)). right; eapply List.in_or_app; left; exact hv1.
            * eapply hvx. eapply hshared; [exact hv1 | eapply in_combine_vars; eassumption].
          -
            cbn in hv1.
            destruct hv1 as [hv1 | [hv1 | hv1]]; try contradiction; subst v.
            *
              (* v = x *)
              destruct hv2 as [hv2 | (hvx & hvs)].
              { eapply (hfresh x (hnew' x hv2)). left; reflexivity. }
              { eapply hvx; reflexivity. }
            *
              (* v = r *)
              destruct hv2 as [hv2 | (hvx & hvs)].
              { eapply hrnew. destruct hv2 as [-> | ->]; assumption. }
              { eapply (hfresh r); [left; reflexivity | right; eapply List.in_or_app; right].
                eapply in_combine_vars; eassumption. }
        +
          eapply dnf_disj_inv. eapply and_distrib_dnf; [exact hR | reflexivity].
        +
          eapply (repair_children_disj_inv Cn An Bn x r names l t hdnf hl hnd); [| exact hpw].
          intros v hv hin. eapply (hfresh v hv).
          destruct hin as [hin | hin];
          [left; exact hin | right; eapply List.in_or_app; right; exact hin].
      Qed.

    End Proofs.

  End Spec.

End DslRepair.
