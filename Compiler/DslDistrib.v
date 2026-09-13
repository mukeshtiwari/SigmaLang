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

(** * DslDistrib: distributing AND over OR

    The surface language of Dsl.v lets a user build a statement out
    of blocks of linear equations ([SEqs]) combined with AND
    ([SAnd]), OR ([SOr]) and threshold ([SThresh]) nodes.  Before
    such a statement can be compiled into a sigma protocol it has to
    pass the disjunction-invariant checker [disj_inv] of Dsl.v.
    This file contains one of the two repairs for statements that
    the checker rejects.  The other repair, which uses a Pedersen
    commitment and also works under a threshold, is in DslRepair.v.

    ** Vocabulary

    A few words are used throughout and are worth fixing first.

    - A private variable is one of the secret numbers the prover
      claims to know.  The vector [privs] declares them.
    - A witness is a concrete assignment of field elements to those
      private variables.  It is what the prover keeps to itself, and
      what a proof convinces the verifier exists.
    - A leaf is a single block of linear equations.  The compiler
      turns it into one [Leaf] node of the statement tree
      [comp_rel], and that node carries exactly one witness vector.
      The function [leaves_only] of Dsl.v recognises the statements
      that become one leaf, namely the AND-trees whose own leaves
      are all equation blocks, and returns the flat list of their
      equations.  Such a statement is called pure here.

    ** Why a shared private variable is a problem

    Every leaf of the compiled tree gets a witness vector of its
    own.  Suppose a private variable [x] occurs in the left child of
    an AND and again in the right child, and suppose the two
    children compile to two separate leaves.  Then nothing ties the
    two leaves together: the left leaf may use one value for [x] and
    the right leaf another.  The protocol would prove something
    weaker than what the user wrote.  Rather than accept that,
    [disj_inv] rejects the statement.

    An OR is harmless in comparison.  Only one branch of an OR is
    ever used by a proof, so a variable shared between the branches
    costs nothing: knowing some [x] with [P x], or knowing some [x]
    with [Q x], is the same as knowing some [x] with [P x] or with
    [Q x].

    So the cure is to arrange that the two occurrences of the shared
    variable end up inside one and the same leaf.  One leaf means
    one witness vector, and one witness vector means one value.

    ** What this pass does

    It pushes ANDs inward past ORs, using the ordinary distribution
    law of logic:

    - [SAnd (SOr a₁ a₂) b] becomes [SOr (SAnd a₁ b) (SAnd a₂ b)]
    - [SAnd a (SOr b₁ b₂)] becomes [SOr (SAnd a b₁) (SAnd a b₂)]

    It repeats this until no AND has an OR below it.  Every AND left
    over then has two pure children, and those two blocks of
    equations are concatenated into a single block.  A variable that
    was shared between a conjunct and a disjunct is now inside that
    single merged block, that is, inside one leaf, which is exactly
    what was wanted.

    The result is in disjunctive normal form.  Disjunctive normal
    form means a disjunction of conjunctions, with no disjunction
    left inside any conjunction.  Here the conjunctions have already
    been merged away into single blocks, so what is left is
    literally an OR-tree of [SEqs] nodes.  That is what the boolean
    test [dnf] recognises.

    ** Cost

    Distribution copies the other side of the AND once per branch of
    the OR.  An AND over a two-way OR duplicates its partner twice,
    an AND over two nested ORs duplicates it four times, and so on.
    The size of the output is therefore exponential in how deeply
    ORs are nested underneath ANDs.  That is the price of the
    approach, and it is why DslRepair.v exists as an alternative.

    ** Thresholds are left alone

    The pass deliberately does not distribute an AND over a
    threshold node.  A threshold is not a two-way branch that can be
    duplicated cheaply: it says that at least [t] of these [k]
    children hold, so turning it into a disjunction would mean
    writing out every one of the many subsets of size [t], which is
    far worse than the already exponential OR case.  So [and_merge]
    treats a threshold as an opaque, non-pure child and simply keeps
    the AND above it.  The pass still recurses into the children of
    a threshold, so everything below it is normalised, but the
    threshold node itself stays where it is.  This is why the
    disjunctive-normal-form result is stated only for
    threshold-free statements, and why DslRepair.v is needed for the
    rest.

    ** The two main results

    - [distrib_denote] says the pass changes nothing about what the
      statement means.  It is an if and only if, so nothing is lost
      and nothing is gained: the rewritten statement holds for
      exactly the same witness assignments as the original.
    - [distrib_disj_inv] says that on threshold-free input the
      rewritten statement passes [disj_inv].  So the pass really
      does repair the statement, and it does so with no side
      condition at all. *)
Section DslDistrib.

  (** ** Parameters

      The file is parametric in everything it talks about, so
      nothing below depends on a particular group or prime.

      - [F] is the field of scalars, with its constants [zero] and
        [one], its operations [add], [mul], [sub], [div], [opp] and
        [inv], and a procedure [Fdec] deciding equality on it.
      - [G] is the group the protocol lives in, with identity [gid],
        inverse [ginv], group operation [gop], exponentiation
        [gpow], and a procedure [Gdec] deciding equality.
      - [V] is the type of variable names, with a procedure [vdec]
        deciding equality; this is what lets the checker compare
        variables and compute variable sets. *)
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

  (** Shorthands for the statement type of Dsl.v and for its purity
      test, both already applied to this section's types.  [stmtC]
      is a statement tree.  [leaves_onlyC s] returns [Some eqs] when
      [s] is pure, that is when it is an AND-tree of equation blocks
      that compiles into a single leaf, and [None] otherwise. *)
  #[local] Notation stmtC := (@stmt F V).
  #[local] Notation leaves_onlyC := (@leaves_only F V).

  (** ** The pass

      [and_merge a b] builds the conjunction of [a] and [b], on the
      assumption that [a] and [b] have already been normalised.

      If both are pure, their equation lists are concatenated with
      [List.app] into one block [SEqs].  That is the step that
      matters: one block is one leaf, one leaf is one witness
      vector, and a private variable occurring in both [a] and [b]
      now has a single value.

      If either side is not pure, for instance because it is an OR
      that could not be distributed away, or a threshold node, then
      there is nothing to merge and the node [SAnd a b] is kept as
      it is. *)
  Definition and_merge (a b : stmtC) : stmtC :=
    match leaves_onlyC a, leaves_onlyC b with
    | Some la, Some lb => SEqs (List.app la lb)
    | _, _ => SAnd a b
    end.

  (** [and_distrib_r a b] conjoins [a] with [b] while pushing the
      conjunction through every OR at the top of [b].

      Here [a] is a side that is already free of top-level ORs.  The
      recursion walks down the OR spine of [b]: an [SOr b₁ b₂]
      becomes the OR of [a] with [b₁] and of [a] with [b₂], so [a]
      is duplicated once per branch.  Anything that is not an OR,
      that is an equation block, an AND or a threshold, is a place
      where the recursion stops and [and_merge] takes over.

      The recursion is structural in [b], which is why Rocq accepts
      it as a [Fixpoint] with no termination argument. *)
  Fixpoint and_distrib_r (a b : stmtC) {struct b} : stmtC :=
    match b with
    | SOr b₁ b₂ => SOr (and_distrib_r a b₁) (and_distrib_r a b₂)
    | _ => and_merge a b
    end.

  (** [and_distrib a b] conjoins [a] and [b], pushing the
      conjunction through the ORs of both sides.

      It first walks down the OR spine of [a], duplicating [b] once
      per branch, and then hands each OR-free piece of [a] to
      [and_distrib_r], which does the same for [b].  Splitting the
      job in two like this is what keeps both definitions
      structurally recursive.

      This is the function other passes call: DslRepair.v builds its
      repaired statements with it, and reasons about them with
      [and_distrib_denote] and [and_distrib_vars_incl] below. *)
  Fixpoint and_distrib (a b : stmtC) {struct a} : stmtC :=
    match a with
    | SOr a₁ a₂ => SOr (and_distrib a₁ b) (and_distrib a₂ b)
    | _ => and_distrib_r a b
    end.

  (** [distrib s] normalises a whole statement.

      It rebuilds [s] from the bottom up.  An equation block is
      already normal.  An OR keeps its shape and both children are
      normalised.  An AND normalises both children first and then
      calls [and_distrib], which is where the distribution law is
      applied and where two pure children get merged into one block.

      At a threshold node the node itself is left in place and only
      its children are normalised.  The inner [fix go] is that
      recursion over the list of children, written out by hand
      because [SThresh] nests a list of statements inside the
      statement type and the guard checker of Rocq needs to see the
      recursion on that list.  [distrib_thresh] below restates this
      case with [List.map], which is easier to reason with.

      Because [and_distrib] duplicates one side of each AND once per
      OR branch below it, the output can be exponentially larger
      than the input in the depth of OR nesting. *)
  Fixpoint distrib (s : stmtC) : stmtC :=
    match s with
    | SEqs eqs => SEqs eqs
    | SAnd a b => and_distrib (distrib a) (distrib b)
    | SOr a b => SOr (distrib a) (distrib b)
    | SThresh t l =>
        SThresh t
          ((fix go (l : list stmtC) : list stmtC :=
              match l with
              | List.nil => List.nil
              | List.cons s' l' => List.cons (distrib s') (go l')
              end) l)
    end.

  (** [thresh_free s] tests whether [s] contains no threshold node
      anywhere.

      It is the side condition of the normal-form results.  The pass
      does not distribute over a threshold, so only on a
      threshold-free statement can the output be guaranteed to be a
      plain OR-tree of equation blocks. *)
  Fixpoint thresh_free (s : stmtC) : bool :=
    match s with
    | SEqs _ => true
    | SAnd a b => thresh_free a && thresh_free b
    | SOr a b => thresh_free a && thresh_free b
    | SThresh _ _ => false
    end.

  (** [dnf s] tests whether [s] is already in disjunctive normal
      form, in the strong sense used here: [s] is an OR-tree all of
      whose leaves are equation blocks, with no AND and no threshold
      anywhere inside.

      Any AND has by then been merged into a single block, so a
      statement passing [dnf] is a disjunction of single leaves.
      That is the shape which makes the disjunction invariant hold
      for free, which is [dnf_disj_inv] below. *)
  Fixpoint dnf (s : stmtC) : bool :=
    match s with
    | SEqs _ => true
    | SOr a b => dnf a && dnf b
    | _ => false
    end.

  (** ** Semantics and invariants

      Everything above is pure syntax.  To say what the pass
      preserves we need an interpretation of statements, and that is
      what this section fixes. *)
  Section Spec.

    (** The data needed to read a statement:

        - [privs] is the vector of the [n] declared private
          variables; a statement is well formed only when every
          variable it uses is one of these;
        - [genv] maps a variable name to the group element it names,
          which is how the base of an exponentiation is resolved;
        - [penv] maps a variable name to the public scalar it names,
          which is how a public coefficient is evaluated. *)
    Context {n : nat}.
    Variable privs : Vector.t V n.
    Variable genv : V -> G.
    Variable penv : V -> F.

    (** Shorthands, all applied to the parameters just fixed.

        - [stmt_denoteC wenv s] is the meaning of [s] under the
          witness assignment [wenv], a proposition saying that the
          equations of [s] really hold at those secret values.
        - [wf_stmtC s] is the boolean well-formedness test: every
          private variable mentioned by [s] is declared in [privs].
        - [disj_invC s] is the disjunction-invariant checker of
          Dsl.v. *)
    #[local] Notation stmt_denoteC :=
      (@stmt_denote F add mul opp G gid gop gpow V genv penv).
    #[local] Notation wf_stmtC := (@wf_stmt F V vdec n privs).
    #[local] Notation disj_invC := (@disj_inv F V vdec).

    (** ** Proofs

        The definitions above are syntactic and need no algebra, but
        the meaning of a statement is written with group
        exponentiation, so the proofs about meaning need the group
        and the field to fit together.  [Hvec] is that assumption:
        the group [G] is a vector space over the field [F], with
        [gpow] as the scalar action. *)
    Section Proofs.

      Context
        {Hvec : @vector_space F (@eq F) zero one add mul sub
          div opp inv G (@eq G) gid ginv gop gpow}.

      (** ** The pass preserves meaning

          Merging two statements means conjunction: [and_merge a b]
          holds under a witness assignment [wenv] exactly when [a]
          and [b] both hold under it.

          In the interesting case both sides are pure, so
          [and_merge] has concatenated their equation lists, and the
          proof only has to know that all equations of an appended
          list hold exactly when all equations of each part hold;
          that is [List.Forall_app], together with
          [leaves_only_denote] of Dsl.v, which says that a pure
          statement means exactly that its extracted equations hold.
          In the other cases [and_merge] returns [SAnd a b] and the
          claim holds by definition. *)
      Lemma and_merge_denote :
        ∀ (wenv : V -> F) (a b : stmtC),
        stmt_denoteC wenv (and_merge a b) <->
        stmt_denoteC wenv a ∧ stmt_denoteC wenv b.
      Proof.
        intros wenv a b.
        unfold and_merge.
        destruct (leaves_onlyC a) as [la |] eqn:ha;
        [destruct (leaves_onlyC b) as [lb |] eqn:hb |].
        +
          cbn.
          rewrite (leaves_only_denote genv penv a la wenv ha),
            (leaves_only_denote genv penv b lb wenv hb).
          rewrite List.Forall_app. reflexivity.
        + cbn. reflexivity.
        + cbn. reflexivity.
      Qed.

      (** Distributing over the ORs of [b] does not change the
          meaning: [and_distrib_r a b] holds exactly when [a] and
          [b] both hold.

          The proof is induction on [b].  When [b] is an [SOr], the
          goal is that [a] together with one of [b₁], [b₂] is the
          same as [a] together with the disjunction of [b₁] and
          [b₂]; that is the distribution law of conjunction over
          disjunction, which [tauto] settles once the two induction
          hypotheses have been rewritten in.  Every other shape of
          [b] is a use of [and_merge_denote]. *)
      Lemma and_distrib_r_denote :
        ∀ (wenv : V -> F) (a b : stmtC),
        stmt_denoteC wenv (and_distrib_r a b) <->
        stmt_denoteC wenv a ∧ stmt_denoteC wenv b.
      Proof.
        intros wenv a b.
        induction b as [eqs | b₁ b₂ ih₁ ih₂ | b₁ b₂ ih₁ ih₂ | t l ihl]
          using stmt_ind';
        try (cbn [and_distrib_r]; eapply and_merge_denote).
        cbn [and_distrib_r stmt_denote].
        rewrite ih₁, ih₂.
        tauto.
      Qed.

      (** Distributing over the ORs of both sides does not change the
          meaning either.

          The same argument, now by induction on [a], with
          [and_distrib_r_denote] doing the work in the non-OR cases.
          This is the reusable form, applied directly by
          DslRepair.v. *)
      Lemma and_distrib_denote :
        ∀ (wenv : V -> F) (a b : stmtC),
        stmt_denoteC wenv (and_distrib a b) <->
        stmt_denoteC wenv a ∧ stmt_denoteC wenv b.
      Proof.
        intros wenv a b.
        induction a as [eqs | a₁ a₂ ih₁ ih₂ | a₁ a₂ ih₁ ih₂ | t l ihl]
          using stmt_ind';
        try (cbn [and_distrib]; eapply and_distrib_r_denote).
        cbn [and_distrib stmt_denote].
        rewrite ih₁, ih₂.
        tauto.
      Qed.

      (** [distrib] at a threshold node is exactly [List.map] over
          the children.

          The definition of [distrib] writes that recursion out by
          hand to satisfy the guard checker.  This lemma says the
          hand-written version and [List.map distrib] are the same
          term, so later proofs can work with [List.map] and use the
          ordinary library lemmas about it.  It holds by
          computation. *)
      Lemma distrib_thresh :
        ∀ (t : nat) (l : list stmtC),
        distrib (SThresh t l) = SThresh t (List.map distrib l).
      Proof.
        intros; cbn; f_equal.
      Qed.

      (** The pass is exact: a normalised statement holds under a
          witness assignment exactly when the original does.

          Nothing is lost and nothing is gained, which is what the
          if and only if buys.  Any witness for the original is a
          witness for the output and the other way round, so a
          verifier convinced by a proof about the output is
          convinced of the statement the user actually wrote.

          The proof is structural induction on [s].  The equation
          and OR cases are immediate.  The AND case is
          [and_distrib_denote] followed by the two induction
          hypotheses.  The threshold case is the only laborious one.
          By [stmt_denote_thresh] the meaning of a threshold node is
          the existence of a list of boolean flags [bs] marking
          which children are claimed, of the right length and with
          at least [t] flags set.  Mapping [distrib] over the
          children changes neither that length nor that count, and
          by the induction hypotheses it changes no child's meaning,
          so the very same [bs] works on both sides. *)
      Theorem distrib_denote :
        ∀ (wenv : V -> F) (s : stmtC),
        stmt_denoteC wenv (distrib s) <-> stmt_denoteC wenv s.
      Proof.
        intros wenv s.
        induction s as [eqs | a b iha ihb | a b iha ihb | t l ihl]
          using stmt_ind'.
        + reflexivity.
        + cbn [distrib]. rewrite and_distrib_denote, iha, ihb. reflexivity.
        + cbn [distrib stmt_denote]. rewrite iha, ihb. reflexivity.
        +
          rewrite distrib_thresh.
          rewrite !(stmt_denote_thresh genv penv).
          assert (hfl : ∀ bs,
            @flagged_denote F add mul opp G gid gop gpow V genv penv wenv
              (List.map distrib l) bs <->
            @flagged_denote F add mul opp G gid gop gpow V genv penv wenv l bs).
          { induction l as [|s l ih]; intros [|b bs]; cbn; try reflexivity.
            inversion ihl as [| ? ? hs hl]; subst.
            rewrite (ih hl bs).
            destruct b; [rewrite hs |]; reflexivity. }
          split; intros (bs & hlen & hcnt & hf); exists bs.
          - rewrite List.length_map in hlen.
            split; [exact hlen | split; [exact hcnt | eapply hfl; exact hf]].
          - split; [rewrite List.length_map; exact hlen |
                    split; [exact hcnt | eapply hfl; exact hf]].
      Qed.

      (** ** The pass preserves well-formedness

          A statement is well formed when every private variable it
          mentions is one of the variables declared in [privs].  The
          pass only rearranges and copies equations that were
          already there, so it cannot introduce an undeclared
          variable.  This matters because compilation is defined,
          and proved correct, only for well-formed statements.

          For [and_merge]: if [a] and [b] are well formed then so is
          the merge.  When both are pure their equation lists are
          appended, and [List.forallb] over an append is the
          conjunction of the two halves; [leaves_only_wf] of Dsl.v
          supplies the missing step, that the equations extracted
          from a well-formed pure statement are themselves well
          formed. *)
      Lemma and_merge_wf :
        ∀ (a b : stmtC),
        wf_stmtC a = true -> wf_stmtC b = true -> wf_stmtC (and_merge a b) = true.
      Proof.
        intros a b ha hb.
        unfold and_merge.
        destruct (leaves_onlyC a) as [la |] eqn:hla;
        [destruct (leaves_onlyC b) as [lb |] eqn:hlb |].
        +
          cbn. rewrite List.forallb_app. eapply andb_true_iff; split.
          - eapply (leaves_only_wf privs a la hla ha).
          - eapply (leaves_only_wf privs b lb hlb hb).
        + cbn. rewrite ha, hb. reflexivity.
        + cbn. rewrite ha, hb. reflexivity.
      Qed.

      (** Distributing over the ORs of [b] preserves well
          formedness.  Induction on [b]: at an [SOr] node each copy
          of [a] is combined with a well-formed branch, and
          everywhere else [and_merge_wf] applies. *)
      Lemma and_distrib_r_wf :
        ∀ (a b : stmtC),
        wf_stmtC a = true -> wf_stmtC b = true -> wf_stmtC (and_distrib_r a b) = true.
      Proof.
        intros a b ha hb.
        induction b as [eqs | b₁ b₂ ih₁ ih₂ | b₁ b₂ ih₁ ih₂ | t l ihl]
          using stmt_ind';
        try (cbn [and_distrib_r]; eapply and_merge_wf; assumption).
        cbn [and_distrib_r wf_stmt] in *.
        eapply andb_true_iff in hb; destruct hb as (hb₁ & hb₂).
        rewrite (ih₁ hb₁), (ih₂ hb₂). reflexivity.
      Qed.

      (** Distributing over the ORs of both sides preserves well
          formedness.  Induction on [a], with [and_distrib_r_wf] in
          the non-OR cases. *)
      Lemma and_distrib_wf :
        ∀ (a b : stmtC),
        wf_stmtC a = true -> wf_stmtC b = true -> wf_stmtC (and_distrib a b) = true.
      Proof.
        intros a b ha hb.
        induction a as [eqs | a₁ a₂ ih₁ ih₂ | a₁ a₂ ih₁ ih₂ | t l ihl]
          using stmt_ind';
        try (cbn [and_distrib]; eapply and_distrib_r_wf; assumption).
        cbn [and_distrib wf_stmt] in *.
        eapply andb_true_iff in ha; destruct ha as (ha₁ & ha₂).
        rewrite (ih₁ ha₁), (ih₂ ha₂). reflexivity.
      Qed.

      (** The whole pass preserves well formedness.

          Structural induction on [s], using [and_distrib_wf] at an
          AND node and, at a threshold node, a second induction over
          the list of children after rewriting with
          [distrib_thresh]. *)
      Theorem distrib_wf :
        ∀ (s : stmtC), wf_stmtC s = true -> wf_stmtC (distrib s) = true.
      Proof.
        intro s.
        induction s as [eqs | a b iha ihb | a b iha ihb | t l ihl]
          using stmt_ind'; intro h.
        + exact h.
        +
          cbn [wf_stmt distrib] in *.
          eapply andb_true_iff in h; destruct h as (ha & hb).
          eapply and_distrib_wf; [eapply iha; exact ha | eapply ihb; exact hb].
        +
          cbn [wf_stmt distrib] in *.
          eapply andb_true_iff in h; destruct h as (ha & hb).
          rewrite (iha ha), (ihb hb). reflexivity.
        +
          rewrite distrib_thresh.
          cbn in h |- *.
          induction l as [|s l ih]; cbn in h |- *; [reflexivity |].
          inversion ihl as [| ? ? hs hl]; subst.
          eapply andb_true_iff in h; destruct h as (h₁ & h₂).
          rewrite (hs h₁), (ih hl h₂). reflexivity.
      Qed.

      (** ** The output is in disjunctive normal form

          On threshold-free input the pass returns an OR-tree of
          single equation blocks, which is the shape the checker
          accepts with no disjointness condition to verify.

          The first step: if [a] is pure, so that [leaves_onlyC a]
          is not [None], and [b] is already in disjunctive normal
          form, then so is [and_distrib_r a b].  The reason is that
          every leaf of the OR-tree of [b] is an equation block,
          hence pure, so at every leaf [and_merge] finds two pure
          sides and produces a single block instead of an [SAnd].
          The hypothesis on [a] is exactly what rules out that
          [SAnd] case. *)
      Lemma and_distrib_r_dnf :
        ∀ (a b : stmtC),
        leaves_onlyC a <> None -> dnf b = true -> dnf (and_distrib_r a b) = true.
      Proof.
        intros a b ha hb.
        induction b as [eqs | b₁ b₂ ih₁ ih₂ | b₁ b₂ ih₁ ih₂ | t l ihl]
          using stmt_ind'; cbn in hb; try discriminate.
        +
          cbn [and_distrib_r]. unfold and_merge.
          destruct (leaves_onlyC a) as [la |]; [reflexivity | congruence].
        +
          cbn [and_distrib_r dnf].
          eapply andb_true_iff in hb; destruct hb as (hb₁ & hb₂).
          rewrite (ih₁ hb₁), (ih₂ hb₂). reflexivity.
      Qed.

      (** If both sides are in disjunctive normal form then so is
          their distributed conjunction.

          Induction on [a].  If [a] is an equation block it is pure,
          so [and_distrib_r_dnf] applies directly.  If [a] is an OR,
          the two branches are handled by the induction hypotheses.
          No other shape of [a] can satisfy [dnf a = true]. *)
      Lemma and_distrib_dnf :
        ∀ (a b : stmtC),
        dnf a = true -> dnf b = true -> dnf (and_distrib a b) = true.
      Proof.
        intros a b ha hb.
        induction a as [eqs | a₁ a₂ ih₁ ih₂ | a₁ a₂ ih₁ ih₂ | t l ihl]
          using stmt_ind'; cbn in ha; try discriminate.
        +
          cbn [and_distrib].
          eapply and_distrib_r_dnf; [cbn; congruence | exact hb].
        +
          cbn [and_distrib dnf].
          eapply andb_true_iff in ha; destruct ha as (ha₁ & ha₂).
          rewrite (ih₁ ha₁), (ih₂ ha₂). reflexivity.
      Qed.

      (** On a threshold-free statement the pass produces
          disjunctive normal form.

          Structural induction on [s]: an equation block is already
          normal, an OR is normal when both children are, and an AND
          is handled by [and_distrib_dnf] applied to the two
          normalised children.  The hypothesis [thresh_free s = true]
          rules out the one remaining case, the one the pass cannot
          normalise, and it passes down to the children, since a
          statement is threshold free exactly when all of its parts
          are. *)
      Theorem distrib_dnf :
        ∀ (s : stmtC), thresh_free s = true -> dnf (distrib s) = true.
      Proof.
        intro s.
        induction s as [eqs | a b iha ihb | a b iha ihb | t l ihl]
          using stmt_ind'; intro h; cbn in h; try discriminate.
        + reflexivity.
        +
          eapply andb_true_iff in h; destruct h as (ha & hb).
          cbn [distrib].
          eapply and_distrib_dnf; [eapply iha; exact ha | eapply ihb; exact hb].
        +
          eapply andb_true_iff in h; destruct h as (ha & hb).
          cbn [distrib dnf]. rewrite (iha ha), (ihb hb). reflexivity.
      Qed.

      (** A statement in disjunctive normal form always satisfies the
          disjunction invariant.

          This is where the work pays off.  [disj_inv] demands
          something only at an AND node, where it wants the two
          sides to be pure or their variable sets to be disjoint,
          and at a threshold node, where it wants the children to
          have pairwise disjoint variable sets.  A statement passing
          [dnf] has neither kind of node: it is an OR-tree of
          equation blocks, and [disj_inv] holds unconditionally on
          an equation block and asks only that both children pass at
          an OR.  So the induction goes through with nothing left to
          check. *)
      Lemma dnf_disj_inv :
        ∀ (s : stmtC), dnf s = true -> disj_invC s = true.
      Proof.
        intro s.
        induction s as [eqs | a b iha ihb | a b iha ihb | t l ihl]
          using stmt_ind'; intro h; cbn in h; try discriminate.
        + reflexivity.
        +
          eapply andb_true_iff in h; destruct h as (ha & hb).
          cbn. rewrite (iha ha), (ihb hb). reflexivity.
      Qed.

      (** ** Variable sets

          [stmt_vars s] is the list of all occurrences of private
          variables in [s].  The lemmas below record that the pass
          never invents a variable: whatever [and_merge],
          [and_distrib_r] or [and_distrib] produce, its variables
          all come from the two inputs.

          They are not needed for [distrib_disj_inv], which takes
          the shorter route through [dnf].  They exist because any
          argument about disjointness after distribution has to
          start from them, and DslRepair.v does exactly that: it
          uses [and_distrib_vars_incl] to keep the variables of its
          own repaired statements under control. *)

      (** Flattening a pure statement into one equation block keeps
          exactly the same variable occurrences.

          If [leaves_onlyC s] returns [Some eqs], then the variables
          of [SEqs eqs] are literally the variables of [s], as
          lists.  The reason is that [leaves_only] on an AND appends
          the two equation lists while [stmt_vars] on an AND appends
          the two variable lists, and collecting variables commutes
          with appending ([List.flat_map_app]). *)
      Lemma leaves_only_vars :
        ∀ (s : stmtC) (eqs : list (@equation F V)),
        leaves_onlyC s = Some eqs -> stmt_vars (SEqs eqs) = stmt_vars s.
      Proof.
        intro s.
        induction s as [eqs0 | a b iha ihb | a b iha ihb | t l ihl]
          using stmt_ind'; intros eqs h; cbn in h.
        + injection h as h; subst; reflexivity.
        +
          destruct (leaves_onlyC a) as [la |] eqn:ha; [| congruence].
          destruct (leaves_onlyC b) as [lb |] eqn:hb; [| congruence].
          injection h as h; subst.
          cbn. rewrite List.flat_map_app.
          rewrite <-(iha la eq_refl), <-(ihb lb eq_refl). reflexivity.
        + congruence.
        + congruence.
      Qed.

      (** The variables of a merge are among the variables of the two
          sides.

          [List.incl] means that every element of the first list
          occurs in the second.  In the pure case the merge is a
          single block whose variables, by [leaves_only_vars], are
          those of [a] followed by those of [b], so the inclusion is
          reflexivity.  In the other cases [and_merge] returns
          [SAnd a b], whose variables are that very same append. *)
      Lemma and_merge_vars_incl :
        ∀ (a b : stmtC),
        List.incl (stmt_vars (and_merge a b)) (List.app (stmt_vars a) (stmt_vars b)).
      Proof.
        intros a b.
        unfold and_merge.
        destruct (leaves_onlyC a) as [la |] eqn:ha;
        [destruct (leaves_onlyC b) as [lb |] eqn:hb |].
        +
          cbn. rewrite List.flat_map_app.
          change (List.flat_map (fun e => List.map t_var (eq_rhs e)) la)
            with (stmt_vars (SEqs la)).
          change (List.flat_map (fun e => List.map t_var (eq_rhs e)) lb)
            with (stmt_vars (SEqs lb)).
          rewrite (leaves_only_vars a la ha), (leaves_only_vars b lb hb).
          eapply List.incl_refl.
        + cbn. eapply List.incl_refl.
        + cbn. eapply List.incl_refl.
      Qed.

      (** The variables of [and_distrib_r a b] are among those of [a]
          and [b].

          Induction on [b].  At an [SOr] node the copies of [a] in
          the two branches contribute only variables of [a], and
          each branch contributes only its own, so every variable of
          the result comes from [a] or from [b].  The proof body is
          the bookkeeping that turns that sentence into memberships
          in appended lists. *)
      Lemma and_distrib_r_vars_incl :
        ∀ (a b : stmtC),
        List.incl (stmt_vars (and_distrib_r a b)) (List.app (stmt_vars a) (stmt_vars b)).
      Proof.
        intros a b.
        induction b as [eqs | b₁ b₂ ih₁ ih₂ | b₁ b₂ ih₁ ih₂ | t l ihl]
          using stmt_ind';
        try (cbn [and_distrib_r]; eapply and_merge_vars_incl).
        cbn [and_distrib_r stmt_vars].
        intros v hv.
        eapply List.in_app_or in hv.
        destruct hv as [hv | hv].
        + eapply ih₁ in hv. eapply List.in_app_or in hv. destruct hv as [hv | hv];
          eapply List.in_or_app;
          [left; exact hv | right; eapply List.in_or_app; left; exact hv].
        + eapply ih₂ in hv. eapply List.in_app_or in hv. destruct hv as [hv | hv];
          eapply List.in_or_app;
          [left; exact hv | right; eapply List.in_or_app; right; exact hv].
      Qed.

      (** The variables of [and_distrib a b] are among those of [a]
          and [b].  The same argument, now by induction on [a], with
          [and_distrib_r_vars_incl] at the leaves.  This is the form
          DslRepair.v reuses. *)
      Lemma and_distrib_vars_incl :
        ∀ (a b : stmtC),
        List.incl (stmt_vars (and_distrib a b)) (List.app (stmt_vars a) (stmt_vars b)).
      Proof.
        intros a b.
        induction a as [eqs | a₁ a₂ ih₁ ih₂ | a₁ a₂ ih₁ ih₂ | t l ihl]
          using stmt_ind';
        try (cbn [and_distrib]; eapply and_distrib_r_vars_incl).
        cbn [and_distrib stmt_vars].
        intros v hv.
        eapply List.in_app_or in hv.
        destruct hv as [hv | hv].
        + eapply ih₁ in hv. eapply List.in_app_or in hv. destruct hv as [hv | hv];
          eapply List.in_or_app;
          [left; eapply List.in_or_app; left; exact hv | right; exact hv].
        + eapply ih₂ in hv. eapply List.in_app_or in hv. destruct hv as [hv | hv];
          eapply List.in_or_app;
          [left; eapply List.in_or_app; right; exact hv | right; exact hv].
      Qed.

      (** ** The output passes the checker

          On a threshold-free statement the pass produces something
          [disj_inv] accepts.

          This is the second main result of the file, and the reason
          the pass exists.  Read together with [distrib_denote] it
          says: take a threshold-free statement the checker refused,
          normalise it, and you get a statement with the very same
          meaning which the checker now accepts, so it can be
          compiled.  No assumption is needed; the only cost is the
          size of the output.

          The proof is two steps: [distrib_dnf] puts the output into
          disjunctive normal form, and [dnf_disj_inv] observes that
          such statements satisfy the invariant. *)
      Corollary distrib_disj_inv :
        ∀ (s : stmtC), thresh_free s = true -> disj_invC (distrib s) = true.
      Proof.
        intros s h.
        eapply dnf_disj_inv, distrib_dnf; exact h.
      Qed.

    End Proofs.

  End Spec.

End DslDistrib.
