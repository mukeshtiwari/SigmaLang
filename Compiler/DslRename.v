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

(** * DslRename: renaming a private variable, and frame lemmas

    This file does two small jobs that the later passes of the
    compiler need: it renames one private variable throughout a
    statement, and it proves that the meaning of a statement depends
    only on the names the statement actually mentions.

    ** Vocabulary

    A statement of the DSL (see Dsl.v) is a tree of group equations
    combined with AND, OR and threshold nodes.  Each equation is a
    product of powers that has to equal the identity element of the
    group.  To give a statement a meaning one needs three
    environments, that is, three functions from names to values:

    - [genv] sends a name to a group element.  Such a group element
      is called a point, and such a name a point name.  Points are
      public: everybody knows them.
    - [penv] sends a name to a public scalar, a field element that
      everybody knows.
    - a witness environment, written [wenv] below, sends a name to a
      private scalar.  These are the secrets that only the prover
      knows.  The collection of them is called the witness.

    A term is one factor of an equation, of the shape "point raised
    to the power public coefficient times private variable".  An
    offset is a factor with no private variable in it, that is, a
    point raised to a purely public power.

    ** Why renaming is needed

    The compiler turns an OR node into a real disjunction proof, and
    that construction requires the two branches to use disjoint sets
    of private variables.  A user, however, happily writes the same
    private variable on both sides of an OR, and the same happens
    between the children of a threshold.  The repair pass of
    DslRepair.v fixes this by giving each branch its own private copy
    of the shared variable, and then adding equations that tie the
    copies back together: each copy has to open one and the same
    Pedersen commitment, which by the binding property of that
    commitment means they all carry the same value.  Making such a
    copy is exactly what [rename_stmt] does: it rewrites every
    occurrence of the private name [x] into the private name [y].

    The meaning of a renamed statement is described by
    [rename_stmt_denote]: the renamed statement holds in an
    environment [wenv] exactly when the original statement holds in
    the environment [override wenv x (wenv y)], which is [wenv]
    changed so that [x] now carries the value of [y].  In words,
    renaming a variable is the same as leaving the statement alone
    and correcting the environment at that one variable.  No
    freshness assumption is needed for this; freshness matters only
    for the syntactic variable-set computations that the checker
    performs.

    ** Why the frame lemmas are needed

    A compiler pass usually adds new names.  The repair pass, for
    instance, introduces fresh commitment points.  We must know that
    adding them cannot change the meaning of the part of the
    statement that was already there.  That is what a frame lemma
    says: the meaning of a statement depends only on the names it
    mentions.

    There are two such families, because two kinds of name are in
    play.

    - Private names.  [stmt_denote_ext] in Dsl.v says that two
      witness environments which agree on [stmt_vars s] give the
      statement [s] the same meaning; [stmt_vars] collects the
      private names of [s].  In this file, [stmt_vars_rename]
      computes the private names of a renamed statement, which is
      what lets a caller check that its chosen new name really was
      fresh.
    - Point names.  [stmt_denote_genv_ext] below says that two point
      environments which agree on [stmt_points s] give [s] the same
      meaning; [stmt_points], defined here, collects the point names
      of [s].

    Both families are needed.  A pass that introduces a fresh private
    variable uses the first; a pass that introduces a fresh point
    uses the second.  The repair pass does both at once. *)

Section DslRename.

  (** ** Parameters

      Nothing in this file depends on a particular field, group or
      type of names, so everything is taken as a parameter.

      [F] is the field of scalars: [zero] and [one] are its
      constants, [add], [mul], [sub] and [div] its four binary
      operations, [opp] is negation, [inv] is the multiplicative
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
      environment a name is looked up in. *)
  Context
    {V : Type}
    {vdec : forall x y : V, {x = y} + {x <> y}}.

  (** Local shorthands.  [veqb] is the boolean equality test on
      names derived from [vdec].  [termC], [equationC] and [stmtC]
      are the syntax types of Dsl.v already applied to this section's
      field and name type, so that the statements below stay
      readable. *)
  #[local] Notation veqb := (@veqb V vdec).
  #[local] Notation termC := (@term F V).
  #[local] Notation equationC := (@equation F V).
  #[local] Notation stmtC := (@stmt F V).

  (** ** Renaming a private variable *)

  (** Rename a single name.  [rename_var x y v] returns [y] when [v]
      is the name [x], and returns [v] unchanged otherwise.

      This is the whole of renaming.  Everything that follows only
      pushes this one operation through the syntax. *)
  Definition rename_var (x y v : V) : V := if veqb v x then y else v.

  (** Rename inside a single term.

      A term is the point [t_base] raised to the power [t_coeff]
      times the private variable [t_var].  Of these three fields only
      [t_var] is a private name, so only it is touched: the public
      coefficient and the point name are copied over unchanged.  In
      particular renaming never disturbs a point name that happens to
      be spelled the same way as the renamed variable. *)
  Definition rename_term (x y : V) (t : termC) : termC :=
    mkterm (t_coeff t) (rename_var x y (t_var t)) (t_base t).

  (** Rename inside a single equation.

      An equation has two parts: [eq_rhs], the list of terms that
      carry private variables, and [eq_off], the list of purely
      public offsets.  A private variable can only occur in the first
      part, so the terms are renamed one by one and the offsets are
      kept exactly as they are. *)
  Definition rename_eq (x y : V) (e : equationC) : equationC :=
    mkeq (List.map (rename_term x y) (eq_rhs e)) (eq_off e).

  (** Rename a private variable throughout a whole statement.

      [rename_stmt x y s] is [s] with every occurrence of the private
      name [x] replaced by [y].  The recursion simply walks the tree:
      equations are renamed one by one, AND and OR nodes rename both
      children, and a threshold node renames each of its children
      while keeping its threshold [t].  The shape of the tree never
      changes.

      The children of a threshold are traversed by a hand-written
      inner loop rather than by [List.map], because the guardedness
      checker does not accept the [List.map] form here.  The loop
      computes the same list, and [rename_stmt_thresh] below records
      that once and for all, so no later proof has to look inside
      it. *)
  Fixpoint rename_stmt (x y : V) (s : stmtC) : stmtC :=
    match s with
    | SEqs eqs => SEqs (List.map (rename_eq x y) eqs)
    | SAnd a b => SAnd (rename_stmt x y a) (rename_stmt x y b)
    | SOr a b => SOr (rename_stmt x y a) (rename_stmt x y b)
    | SThresh t l =>
        SThresh t
          ((fix go (l : list stmtC) : list stmtC :=
              match l with
              | List.nil => List.nil
              | List.cons s' l' => List.cons (rename_stmt x y s') (go l')
              end) l)
    end.

  (** ** Changing one entry of an environment *)

  (** [override w x v] is the environment that behaves exactly like
      [w] except at the name [x], where it returns [v].  Read it as
      "the same environment, except at one name".

      This is what lets the renaming theorem be stated with no side
      condition at all.  The renamed statement reads [y] wherever the
      original read [x]; saying that is the same as saying that the
      original statement is read in an environment whose entry for
      [x] has been set to the value of [y].

      Its behaviour is fixed completely by the two lemmas
      [override_same] and [override_other] below, so later proofs
      never need to unfold it. *)
  Definition override (w : V -> F) (x : V) (v : F) : V -> F :=
    fun z => if veqb z x then v else w z.

  (** ** The point names of a statement *)

  (** The point names mentioned by one equation.

      Two kinds of point name occur in an equation: the base of each
      term in [eq_rhs], and the point attached to each public offset
      in [eq_off].  Both are collected and the two lists are
      appended.

      Public scalar names occurring inside the coefficients are
      deliberately not collected here: those are read out of [penv],
      not out of the point environment [genv]. *)
  Definition eq_points (e : equationC) : list V :=
    List.app (List.map t_base (eq_rhs e)) (List.map snd (eq_off e)).

  (** The point names mentioned anywhere in a statement.

      This is the point-environment counterpart of [stmt_vars] from
      Dsl.v, which collects the private names.  It walks the tree and
      concatenates the point names of every equation it meets.
      Duplicates are not removed: the list is only ever used through
      membership questions, where duplicates make no difference.

      Its purpose is to state the frame lemma
      [stmt_denote_genv_ext].  A name that does not appear in this
      list is a point the statement never looks at, so a pass is free
      to give such a name a value of its own choosing. *)
  Fixpoint stmt_points (s : stmtC) : list V :=
    match s with
    | SEqs eqs => List.flat_map eq_points eqs
    | SAnd a b => List.app (stmt_points a) (stmt_points b)
    | SOr a b => List.app (stmt_points a) (stmt_points b)
    | SThresh _ l =>
        (fix go (l : list stmtC) : list V :=
           match l with
           | List.nil => List.nil
           | List.cons s' l' => List.app (stmt_points s') (go l')
           end) l
    end.

  Section Spec.

    (** ** Semantics

        The lemmas below are stated for one fixed pair of public
        environments: [genv], which gives each point name its group
        element, and [penv], which gives each public scalar name its
        field element.  Only the witness environment, which holds the
        private scalars, varies from lemma to lemma, except in the
        frame lemmas at the end of the file, which vary [genv] on
        purpose. *)
    Variable genv : V -> G.
    Variable penv : V -> F.

    (** Local shorthands for the three denotation functions of
        Dsl.v, already applied to this section's field, group and
        environments.  [term_denoteC] gives the group element of one
        term, [eq_denoteC] says when one equation holds, and
        [stmt_denoteC] says when a whole statement holds. *)
    #[local] Notation term_denoteC :=
      (@term_denote F add mul opp G gpow V genv penv).
    #[local] Notation eq_denoteC :=
      (@eq_denote F add mul opp G gid gop gpow V genv penv).
    #[local] Notation stmt_denoteC :=
      (@stmt_denote F add mul opp G gid gop gpow V genv penv).

    Section Proofs.

      (** The proofs assume that the scalars and the group really
          form a vector space: [F] is a field, [G] is a commutative
          group, and [gpow] behaves like scalar multiplication.  This
          is what makes the algebraic steps in the proofs legal. *)
      Context
        {Hvec : @vector_space F (@eq F) zero one add mul sub
          div opp inv G (@eq G) gid ginv gop gpow}.

      (** Reading an overridden environment at the overridden name
          gives the new value.  This is one half of the description
          of [override]. *)
      Lemma override_same : ∀ (w : V -> F) (x : V) (v : F),
        override w x v x = v.
      Proof.
        intros; unfold override; rewrite veqb_refl; reflexivity.
      Qed.

      (** Reading an overridden environment at any other name gives
          the old value.  The hypothesis [z <> x] says that the name
          being read is not the one that was changed.

          Together with [override_same] this pins [override] down
          completely, which is why no proof below ever unfolds it. *)
      Lemma override_other : ∀ (w : V -> F) (x z : V) (v : F),
        z <> x -> override w x v z = w z.
      Proof.
        intros * h; unfold override, Dsl.veqb.
        destruct (vdec z x); [congruence | reflexivity].
      Qed.

      (** Renaming a term does not change its value, provided the
          environment is corrected to match.

          The left hand side evaluates the renamed term in [wenv];
          the right hand side evaluates the original term in [wenv]
          corrected at [x] to the value [wenv y].  The two agree
          because a term reads a private variable in exactly one
          place.  If that variable is [x], the left hand side reads
          [y] while the right hand side reads the corrected entry,
          which holds precisely [wenv y].  If it is any other
          variable, both sides read the same untouched entry.  The
          point and the public coefficient are identical on the two
          sides either way. *)
      Lemma rename_term_denote :
        ∀ (wenv : V -> F) (x y : V) (t : termC),
        term_denoteC wenv (rename_term x y t) =
        term_denoteC (override wenv x (wenv y)) t.
      Proof.
        intros wenv x y t.
        unfold term_denote, rename_term, rename_var, override; cbn.
        destruct (veqb (t_var t) x); reflexivity.
      Qed.

      (** The same fact for a whole equation, phrased as an
          equivalence.

          An equation holds when the product of its terms and its
          offsets is the identity of the group.  The offsets mention
          no private variable, so they contribute the very same group
          element on both sides, and the product over the terms
          matches factor by factor by [rename_term_denote].  The two
          products being equal, one is the identity exactly when the
          other is. *)
      Lemma rename_eq_denote :
        ∀ (wenv : V -> F) (x y : V) (e : equationC),
        eq_denoteC wenv (rename_eq x y e) <->
        eq_denoteC (override wenv x (wenv y)) e.
      Proof.
        intros wenv x y e.
        unfold eq_denote, rename_eq; cbn [eq_rhs eq_off].
        assert (h : ∀ ts,
          @terms_fold F add mul opp G gid gop gpow V genv penv wenv
            (List.map (rename_term x y) ts) =
          @terms_fold F add mul opp G gid gop gpow V genv penv
            (override wenv x (wenv y)) ts).
        { induction ts as [|t ts ih]; cbn; [reflexivity |].
          unfold terms_fold in ih |- *; cbn.
          rewrite ih, rename_term_denote. reflexivity. }
        rewrite h. reflexivity.
      Qed.

      (** Renaming a threshold node is the same as renaming each of
          its children.

          This replaces the hand-written loop inside [rename_stmt] by
          an ordinary [List.map], which is the form every later proof
          about threshold nodes wants to work with.  Proving it once
          keeps that internal loop out of all the proofs below. *)
      Lemma rename_stmt_thresh :
        ∀ (x y : V) (t : nat) (l : list stmtC),
        rename_stmt x y (SThresh t l) = SThresh t (List.map (rename_stmt x y) l).
      Proof.
        intros; cbn; f_equal.
      Qed.

      (** The main renaming theorem: renaming a private variable is
          the same as correcting the environment at that variable.

          The renamed statement holds in [wenv] exactly when the
          original statement holds in [override wenv x (wenv y)],
          that is, in the environment that agrees with [wenv]
          everywhere except that the entry for [x] now carries the
          value of [y].

          Why it is true: the meaning of a statement is built up from
          the meanings of its equations by conjunction, disjunction
          and counting, and none of those connectives looks any
          deeper into an equation.  So it is enough that each single
          equation is preserved, which is [rename_eq_denote], and the
          rest is a structural induction over the tree.  In the
          threshold case the very same list of flags works on both
          sides, because renaming changes neither the number of
          children nor which of them hold.

          There is no freshness hypothesis.  Even when [y] already
          occurs in the statement the equivalence still holds; it
          then simply describes the merging of two variables into
          one.  A caller who wants renaming to produce a genuinely
          separate copy has to choose a fresh [y] itself, and
          [stmt_vars_rename] below is what lets it check that.

          This is the fact the repair pass of DslRepair.v uses when
          it gives each branch of an OR, and each child of a
          threshold, its own private copy of a shared variable. *)
      Theorem rename_stmt_denote :
        ∀ (wenv : V -> F) (x y : V) (s : stmtC),
        stmt_denoteC wenv (rename_stmt x y s) <->
        stmt_denoteC (override wenv x (wenv y)) s.
      Proof.
        intros wenv x y s.
        induction s as [eqs | a b iha ihb | a b iha ihb | t l ihl]
          using stmt_ind'.
        +
          cbn.
          induction eqs as [|e eqs ih]; cbn.
          - split; intro; constructor.
          - split; intro h; inversion h as [| ? ? h1 h2]; subst; constructor.
            * eapply rename_eq_denote; exact h1.
            * eapply ih; exact h2.
            * eapply rename_eq_denote; exact h1.
            * eapply ih; exact h2.
        + cbn. rewrite iha, ihb. reflexivity.
        + cbn. rewrite iha, ihb. reflexivity.
        +
          rewrite rename_stmt_thresh.
          rewrite !(stmt_denote_thresh genv penv).
          assert (hfl : ∀ bs,
            @flagged_denote F add mul opp G gid gop gpow V genv penv wenv
              (List.map (rename_stmt x y) l) bs <->
            @flagged_denote F add mul opp G gid gop gpow V genv penv
              (override wenv x (wenv y)) l bs).
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

      (** The private names of a renamed statement are the renamed
          private names.

          [stmt_vars] collects, in order and with duplicates, every
          private name occurring in a statement.  Renaming acts on
          each occurrence independently, so the resulting list is the
          old list with [rename_var x y] applied to each entry.

          This is the syntactic counterpart of
          [rename_stmt_denote], and it is what the disjointness
          checks of the repair pass are proven with.  From it one
          reads off that [x] no longer occurs after renaming, as long
          as [x] and [y] are different names, and that [y] now occurs
          wherever [x] used to. *)
      Lemma stmt_vars_rename :
        ∀ (x y : V) (s : stmtC),
        stmt_vars (rename_stmt x y s) = List.map (rename_var x y) (stmt_vars s).
      Proof.
        intros x y s.
        induction s as [eqs | a b iha ihb | a b iha ihb | t l ihl]
          using stmt_ind'.
        +
          cbn.
          induction eqs as [|e eqs ih]; cbn; [reflexivity |].
          rewrite List.map_app, ih. f_equal.
          unfold rename_eq; cbn. rewrite !List.map_map. reflexivity.
        + cbn. rewrite iha, ihb, List.map_app. reflexivity.
        + cbn. rewrite iha, ihb, List.map_app. reflexivity.
        +
          rewrite rename_stmt_thresh, !stmt_vars_thresh.
          unfold vars_of_list.
          induction l as [|s l ih]; cbn; [reflexivity |].
          inversion ihl as [| ? ? hs hl]; subst.
          rewrite List.map_app, hs, (ih hl). reflexivity.
      Qed.

      (** ** Frame lemmas for the point environment

          The four lemmas that follow build up, from terms to
          offsets to equations to whole statements, the single fact
          that the meaning of a statement depends on the point
          environment only at the point names the statement mentions.
          The private-variable counterpart of this fact is
          [stmt_denote_ext] in Dsl.v. *)

      (** A product of terms depends on the point environment only at
          the points those terms use.

          [terms_fold] multiplies together the group elements of a
          list of terms.  The hypothesis says that the two candidate
          point environments [g] and [g'] agree on the base of every
          term in [ts].  Each factor then comes out the same, so the
          whole product does.  The witness environment and the public
          scalar environment are shared by the two sides and play no
          role. *)
      Lemma terms_fold_genv_ext :
        ∀ (g g' : V -> G) (wenv : V -> F) (ts : list termC),
        (∀ P, List.In P (List.map t_base ts) -> g P = g' P) ->
        @terms_fold F add mul opp G gid gop gpow V g penv wenv ts =
        @terms_fold F add mul opp G gid gop gpow V g' penv wenv ts.
      Proof.
        intros g g' wenv ts.
        induction ts as [|t ts ih]; intro hp; [reflexivity |].
        unfold terms_fold in ih |- *; cbn.
        rewrite ih; [| intros P hP; eapply hp; right; exact hP].
        unfold term_denote. rewrite (hp (t_base t) (or_introl eq_refl)).
        reflexivity.
      Qed.

      (** The same fact for the public offsets of an equation.

          [off_fold] multiplies together the group elements of a list
          of offsets, each of which is a point raised to a purely
          public power.  If [g] and [g'] agree on every point named
          by those offsets, the two products are equal. *)
      Lemma off_fold_genv_ext :
        ∀ (g g' : V -> G) (os : list (@pexpr F V * V)),
        (∀ P, List.In P (List.map snd os) -> g P = g' P) ->
        @off_fold F add mul opp G gid gop gpow V g penv os =
        @off_fold F add mul opp G gid gop gpow V g' penv os.
      Proof.
        intros g g' os.
        induction os as [|o os ih]; intro hp; [reflexivity |].
        unfold off_fold in ih |- *; cbn.
        rewrite ih; [| intros P hP; eapply hp; right; exact hP].
        unfold off_denote. rewrite (hp (snd o) (or_introl eq_refl)).
        reflexivity.
      Qed.

      (** One equation means the same thing under two point
          environments that agree on its points.

          [eq_points e] is exactly the bases of the terms together
          with the points of the offsets, so the hypothesis feeds the
          two previous lemmas, one for each half of the equation.
          Both halves being equal group elements, their product is
          the identity under [g] exactly when it is under [g']. *)
      Lemma eq_denote_genv_ext :
        ∀ (g g' : V -> G) (wenv : V -> F) (e : equationC),
        (∀ P, List.In P (eq_points e) -> g P = g' P) ->
        (@eq_denote F add mul opp G gid gop gpow V g penv wenv e <->
         @eq_denote F add mul opp G gid gop gpow V g' penv wenv e).
      Proof.
        intros g g' wenv e hp.
        unfold eq_denote.
        rewrite (terms_fold_genv_ext g g'), (off_fold_genv_ext g g');
        [reflexivity | |].
        + intros P hP; eapply hp; unfold eq_points;
          eapply List.in_or_app; right; exact hP.
        + intros P hP; eapply hp; unfold eq_points;
          eapply List.in_or_app; left; exact hP.
      Qed.

      (** The frame lemma itself: the meaning of a statement depends
          on the point environment only at the points occurring in
          the statement.

          If [g] and [g'] agree on every name in [stmt_points s],
          then [s] holds under [g] exactly when it holds under [g'].

          The proof is a structural induction.  The equation case is
          [eq_denote_genv_ext]; the AND, OR and threshold cases only
          have to split the hypothesis between the children, since
          the points of a node are the points of its children
          concatenated.  The threshold case keeps the same list of
          flags on both sides.

          This is the lemma a pass reaches for when it introduces new
          points.  The repair pass of DslRepair.v adds fresh
          commitment points to [genv]; because those names do not
          occur in the statement that was already there, this lemma
          says that statement still means what it meant before. *)
      Lemma stmt_denote_genv_ext :
        ∀ (g g' : V -> G) (wenv : V -> F) (s : stmtC),
        (∀ P, List.In P (stmt_points s) -> g P = g' P) ->
        (@stmt_denote F add mul opp G gid gop gpow V g penv wenv s <->
         @stmt_denote F add mul opp G gid gop gpow V g' penv wenv s).
      Proof.
        intros g g' wenv s.
        induction s as [eqs | a b iha ihb | a b iha ihb | t l ihl]
          using stmt_ind'; intro hp.
        +
          cbn in hp |- *.
          induction eqs as [|e eqs ih]; cbn.
          - split; intro; constructor.
          - assert (hpe : ∀ P, List.In P (eq_points e) -> g P = g' P).
            { intros P hP; eapply hp; cbn; eapply List.in_or_app; left; exact hP. }
            assert (hpr : ∀ P, List.In P (List.flat_map eq_points eqs) -> g P = g' P).
            { intros P hP; eapply hp; cbn; eapply List.in_or_app; right; exact hP. }
            split; intro h; inversion h as [| ? ? h1 h2]; subst; constructor.
            * eapply (proj1 (eq_denote_genv_ext g g' wenv e hpe)); exact h1.
            * eapply (proj1 (ih hpr)); exact h2.
            * eapply (proj2 (eq_denote_genv_ext g g' wenv e hpe)); exact h1.
            * eapply (proj2 (ih hpr)); exact h2.
        +
          cbn in hp |- *.
          rewrite iha, ihb; [reflexivity | |].
          - intros P hP; eapply hp, List.in_or_app; right; exact hP.
          - intros P hP; eapply hp, List.in_or_app; left; exact hP.
        +
          cbn in hp |- *.
          rewrite iha, ihb; [reflexivity | |].
          - intros P hP; eapply hp, List.in_or_app; right; exact hP.
          - intros P hP; eapply hp, List.in_or_app; left; exact hP.
        +
          rewrite !(stmt_denote_thresh _ penv).
          cbn in hp.
          assert (hfl : ∀ bs,
            @flagged_denote F add mul opp G gid gop gpow V g penv wenv l bs <->
            @flagged_denote F add mul opp G gid gop gpow V g' penv wenv l bs).
          { induction l as [|s l ih]; intros [|b bs]; cbn; try reflexivity.
            inversion ihl as [| ? ? hs hl]; subst.
            rewrite (ih hl); [| intros P hP; eapply hp, List.in_or_app; right; exact hP].
            destruct b; [rewrite hs; [reflexivity |] | reflexivity].
            intros P hP; eapply hp, List.in_or_app; left; exact hP. }
          split; intros (bs & hlen & hcnt & hf); exists bs;
          (split; [exact hlen | split; [exact hcnt | eapply hfl; exact hf]]).
      Qed.

    End Proofs.

  End Spec.

End DslRename.
