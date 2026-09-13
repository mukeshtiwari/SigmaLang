From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef
  BinPos List PeanoNat Permutation Arith.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Probability Require Import
  Prob Distr.
From Utility Require Import
  Util.
From ExtLib.Structures Require Import
  Monad.
From Crypto Require Import
  Sigma.
From Compiler Require Import
  LinearRelation Composition.

Import VectorNotations.

(** * Dsl: the core statement language and its compiler

    This file has two halves.  The first defines a small language in
    which one writes down what is to be proven.  The second is a
    compiler that translates a statement of that language into the
    composed protocol of Composition.v, together with the two
    theorems saying that the translation is faithful.

    ** Sigma protocols in one paragraph

    A sigma protocol is a three-message conversation.  The prover
    holds a secret, called the witness, and wants to convince the
    verifier that it holds one without revealing it.  The prover
    speaks first with an announcement, a commitment computed from
    fresh randomness; the verifier replies with a random challenge;
    the prover closes with a response.  The three messages together
    are a transcript, and the verifier accepts or rejects it.  Three
    properties matter.  Completeness: an honest prover that really
    knows a witness is always accepted.  Special soundness: from two
    accepting transcripts that share the announcement but answer
    different challenges one can compute a witness, so a prover able
    to answer two challenges cannot be bluffing.  Zero knowledge: a
    simulator, given only the statement and the challenge and no
    witness at all, produces transcripts distributed exactly like
    the real ones, so a transcript leaks nothing.

    ** What a statement looks like

    A statement is a formula built from equations by conjunction,
    disjunction and threshold.  There is no negation: every
    connective is monotone, so making more leaves true can never
    make the whole statement false.  In the syntax of this file:

    - [SEqs eqs] is a list of equations, all of which must hold;
    - [SAnd a b] and [SOr a b] are the two binary connectives;
    - [SThresh t l] holds when at least [t] of the statements in the
      list [l] hold, without saying which ones.

    ** What one equation means

    The group is written multiplicatively, and [gpow g x], written
    [g ^ x] inside this file, is the point [g] raised to the scalar
    power [x].  An equation is a product of such powers that is
    required to equal the group identity [gid]:

    - each private term contributes [genv b ^ (c * wenv x)], a
      public point named [b] raised to a public coefficient [c]
      times the private scalar named [x];
    - each public offset contributes [genv b ^ c], a public point
      raised to a public scalar, with no secret in it at all.

    Everything is pushed to one side of the equality, so an equation
    reads "this product equals the identity" rather than "this
    product equals that point".  That homogeneous form is chosen for
    three reasons.  It is closed under what the compiler does to
    equations: taking the conjunction of two lists of equations is
    plain list concatenation, and there is no distinguished
    right-hand side to keep track of.  It separates cleanly into a
    private part and a public part, which is exactly the split a
    compiled leaf needs: the private part becomes a row of the
    matrix, and the public part, inverted, becomes the target point.
    And it makes the familiar form a derived notion: [simple_eq]
    builds the equation whose only public offset is a point raised
    to [opp one], and [simple_eq_denote] proves that this equation
    says the point equals the product of the terms.

    ** Three environments, and why the formula carries none of them

    Variable names are abstract: any type [V] with decidable
    equality will do.  A formula therefore mentions names only, and
    an instance of the problem is supplied separately by three
    environments.  An environment is simply a function from names to
    values.

    - [genv], from names to group elements, gives the points: the
      bases the powers are taken of, and the public targets.
    - [penv], from names to scalars, gives the public numbers.
      Coefficients in an equation are not bare constants but little
      expressions ([pexpr]) evaluated against [penv], so that the
      same formula can be reused with different public data.
    - [wenv], from names to scalars, gives the private numbers.
      This is the witness: what the prover knows and does not
      reveal.

    Keeping the instance out of the formula means one formula can be
    compiled against many instances, and it turns
    [stmt_denote wenv s] into a statement about the witness alone
    once [genv] and [penv] are fixed.

    ** What compilation produces

    [compile] turns a statement into a [comp_rel] of Composition.v,
    which is a tree of the same shape built from [Leaf], [CAnd],
    [COr] and [CThresh] nodes.  A leaf of that tree is the protocol
    of LinearRelation.v: it proves knowledge of a vector of scalars
    [x] with [M x = P], for a public matrix [M] of group elements
    and a public vector [P] of group elements.

    The one step worth explaining is that an AND-tree of equations
    is not compiled into [CAnd] nodes but merged into a single
    [Leaf].  The reason is sharing.  A [CAnd] node gives its two
    children independent witness vectors, so a private variable
    occurring on both sides would be answered by two unrelated
    values, and the compiled relation would be strictly weaker than
    the statement.  Merging the equations into one leaf gives them
    one witness vector, whose columns are the declared private
    variables [privs], so every occurrence of a variable reads the
    same entry of the same vector.

    Where merging is impossible, the compiler keeps a [CAnd] node
    and the checker [disj_inv] demands that the two branches share
    no private variable at all.  [SOr] becomes [COr] and [SThresh]
    becomes [CThresh], with the threshold interpolation points taken
    from the parameter [node] and checked pairwise distinct at
    compile time.  Nothing is expanded into subsets, so a threshold
    over [k] children stays linear in [k].

    ** The two main theorems

    [compile_stmt_sound] is the forward direction: if the statement
    holds of some witness environment, then the compiled relation
    has a witness.  It is what makes the compiled protocol usable,
    and it yields completeness and zero knowledge as corollaries.

    [compile_stmt_reflect] is the backward direction: any witness
    for the compiled relation can be read back as a witness
    environment satisfying the source statement.  Combined with
    special soundness of the composed protocol, it says that a
    prover who convinces the verifier really knows a witness for the
    statement as written, not merely for the matrix the compiler
    produced.  This direction needs [disj_inv]; DslNecessity.v
    exhibits a statement for which dropping the checker makes it
    false. *)

Section Dsl.

  (** ** Parameters

      The whole development is parametric in the algebraic structure
      it runs over, so nothing below depends on a particular curve
      or prime field.

      The scalars form a field [F]: [zero] and [one] are the two
      constants, [add], [mul], [sub] and [div] the four binary
      operations, [opp] is negation and [inv] the multiplicative
      inverse.  [Fdec] decides whether two scalars are equal, which
      is what lets the compiler run boolean tests such as
      [nodupb_F] on them.  The field laws themselves are not assumed
      here but in the [Proofs] section below, since the definitions
      need only the operations. *)
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}.

  (** The group [G] in which the equations live, written
      multiplicatively: [gid] is the identity, [gop] the group
      operation, [ginv] the inverse, and [gpow g x] raises the point
      [g] to the scalar power [x].  [Gdec] decides equality of two
      points, which the verifier needs in order to compare a
      recomputed announcement with the one it received. *)
  Context
    {G : Type}
    {gid : G}
    {ginv : G -> G}
    {gop : G -> G -> G}
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}.

  (** Variable names.  [V] is an arbitrary type with decidable
      equality [vdec]; the language never inspects a name beyond
      comparing it with another one.  Leaving the type abstract lets
      the surface language of Surface.v pick whatever names are
      convenient, for instance strings or numbers. *)
  Context
    {V : Type}
    {vdec : forall x y : V, {x = y} + {x <> y}}.

  (** Local notation, in force in this file only: [^] is [gpow],
      and [*] and [+] are the field operations rather than those of
      [nat]. *)
  #[local] Infix "^" := gpow.
  #[local] Infix "*" := mul.
  #[local] Infix "+" := add.

  (** Boolean equality of variable names, obtained by collapsing
      the decision procedure [vdec] to a [bool].  The compiler's
      checks are run with [List.forallb] and [List.existsb], which
      want a boolean, and a boolean test can be discharged by
      computation when the names are concrete. *)
  Definition veqb (x y : V) : bool :=
    if vdec x y then true else false.

  (** Boolean equality of scalars, the same collapse applied to
      [Fdec].  Used on the threshold interpolation points. *)
  Definition feqb (x y : F) : bool :=
    if Fdec x y then true else false.

  (** The definitions of LinearRelation.v and Composition.v take
      the field and the group structure as arguments.  The notations
      below fix those arguments once and for all to this section's
      structure, so that the rest of the file can write [comp_relC]
      instead of repeating the whole parameter list.  The trailing
      letter stands for "closed".

      - [row_evalC row xs] is the product of the entries of [row]
        raised to the matching entries of [xs]: one row of a linear
        relation, evaluated at a candidate witness.
      - [comp_relC] is the statement tree of Composition.v, with
        nodes [Leaf], [CAnd], [COr] and [CThresh].
      - [comp_witnessC r] is the type of witnesses of [r], computed
        from the shape of the tree, and [comp_rel_holdsC r w] says
        that the witness [w] satisfies [r].
      - [wlist] and [wholds] walk the children of a threshold node:
        a threshold witness is an optional witness per child, and
        [wholds] says each one present is correct.
      - [comp_randC] is the prover's randomness, [comp_proveC] the
        prover and [comp_verifyC] the verifier.
      - [comp_real_distributionC] and
        [comp_simulator_distributionC] are the distribution of real
        transcripts and the distribution the simulator produces;
        zero knowledge is the statement that the two agree. *)
  #[local] Notation row_evalC :=
    (@row_eval F G gid gop gpow _).
  #[local] Notation comp_relC := (@comp_rel F zero G).
  #[local] Notation comp_rel_holdsC :=
    (@comp_rel_holds F zero G gid gop gpow).
  #[local] Notation comp_witnessC :=
    (@comp_witness F zero G).
  #[local] Notation wlist := (wlist_gen comp_witnessC).
  #[local] Notation wholds := (wholds_gen comp_rel_holdsC).
  #[local] Notation comp_randC := (@comp_rand F zero G).
  #[local] Notation comp_verifyC :=
    (@comp_verify F zero one add mul sub inv G gid gop gpow Gdec).
  #[local] Notation comp_proveC :=
    (@comp_prove F zero one add mul sub opp inv G gid gop gpow).
  #[local] Notation comp_real_distributionC :=
    (@comp_real_distribution F zero one add mul sub opp inv G gid gop gpow).
  #[local] Notation comp_simulator_distributionC :=
    (@comp_simulator_distribution F zero one add mul sub opp inv G gid gop gpow).

  (** ** Syntax

      Three layers: public scalar expressions, then equations built
      out of terms, then the statement tree over equations. *)

  (** Public scalar expressions.  A coefficient inside an equation
      is not a bare field element but a small arithmetic expression
      over public data, so that one formula can be instantiated with
      many different public inputs.

      - [PConst c] is a literal scalar;
      - [PVar x] reads the public scalar bound to the name [x];
      - [PAdd], [PMul] and [POpp] are addition, multiplication and
        negation.

      There is no division and no way to mention private data: an
      expression is evaluated by [peval] against [penv] alone. *)
  Inductive pexpr : Type :=
  | PConst (c : F)
  | PVar (x : V)
  | PAdd (a b : pexpr)
  | PMul (a b : pexpr)
  | POpp (a : pexpr).

  (** One term of an equation, denoting the group element
      [genv t_base ^ (peval penv t_coeff * wenv t_var)].

      - [t_coeff] is the public coefficient, an expression;
      - [t_var] is the name of the private scalar the base is
        raised to;
      - [t_base] is the name of the public point being raised.

      So a term is "a public point, raised to a public number times
      one secret number".  This is the only place where a secret
      enters an equation. *)
  Record term : Type := mkterm
    { t_coeff : pexpr;
      t_var : V;
      t_base : V }.

  (** One equation, in homogeneous form: the product of all its
      private terms, times the product of all its public offsets, is
      required to be the group identity.

      - [eq_rhs] is the list of private terms, each of the shape
        described at [term];
      - [eq_off] is the list of public offsets, each a pair of a
        public coefficient and the name of a point, denoting that
        point raised to that coefficient and containing no secret.

      Everything sits on one side of the equality.  The file header
      explains why; in short, conjunction of equations becomes plain
      list concatenation, and the split into private and public
      parts is exactly the split a compiled leaf needs, where the
      private part becomes a matrix row and the public part,
      inverted, becomes the target point. *)
  Record equation : Type := mkeq
    { eq_rhs : list term;
      eq_off : list (pexpr * V) }.

  (** The readable form of an equation: the point named [Pn] is
      equal to the product of the terms [ts].

      It is built as the homogeneous equation whose single public
      offset is [Pn] raised to [opp one], that is, the inverse of
      [genv Pn].  Multiplying by an inverse is how "move it to the
      other side" is spelled in a group.  [simple_eq_denote] below
      proves that this equation really has the readable reading, so
      a user can write the familiar form while the compiler works
      with the homogeneous one. *)
  Definition simple_eq (Pn : V) (ts : list term) : equation :=
    mkeq ts (List.cons (POpp (PConst one), Pn) List.nil).

  (** The statement tree.

      - [SEqs eqs] holds when every equation in the list [eqs]
        holds;
      - [SAnd a b] and [SOr a b] are conjunction and disjunction;
      - [SThresh t l] holds when at least [t] of the statements in
        the list [l] hold, without saying which ones.

      There is no negation, so the language is monotone. *)
  Inductive stmt : Type :=
  | SEqs (eqs : list equation)
  | SAnd (a b : stmt)
  | SOr (a b : stmt)
  | SThresh (t : nat) (l : list stmt).

  (** Rocq's automatically generated induction principle for [stmt]
      is too weak to use: a [SThresh] node holds a [list stmt], and
      the generated principle offers no hypothesis at all about the
      statements inside that list.  [stmt_ind'] repairs this by
      asking, in the threshold case, for a [List.Forall] hypothesis,
      that is, for the property to hold of every child.  It is built
      by an inner fixpoint that walks the child list and calls the
      main recursion on each element.  Every induction over
      statements in this file uses it. *)
  Section StmtInduction.
    Variable P : stmt -> Prop.
    Hypothesis HEqs : ∀ eqs, P (SEqs eqs).
    Hypothesis HAnd : ∀ a b, P a -> P b -> P (SAnd a b).
    Hypothesis HOr : ∀ a b, P a -> P b -> P (SOr a b).
    Hypothesis HThresh : ∀ t l, List.Forall P l -> P (SThresh t l).

    (** The principle itself: to prove [P] of every statement, it
        suffices to prove it of a list of equations, of an [SAnd]
        and of an [SOr] given both children, and of an [SThresh]
        given all of its children. *)
    Fixpoint stmt_ind' (s : stmt) : P s :=
      match s with
      | SEqs eqs => HEqs eqs
      | SAnd a b => HAnd a b (stmt_ind' a) (stmt_ind' b)
      | SOr a b => HOr a b (stmt_ind' a) (stmt_ind' b)
      | SThresh t l =>
          HThresh t l
            ((fix go (l : list stmt) : List.Forall P l :=
                match l with
                | List.nil => @List.Forall_nil _ P
                | List.cons s' l' =>
                    @List.Forall_cons _ P s' l' (stmt_ind' s') (go l')
                end) l)
      end.
  End StmtInduction.

  (** Evaluate a public expression against the public environment
      [penv], giving a scalar.  A plain fold over the expression
      tree; no private data is involved, so both the prover and the
      verifier can carry it out. *)
  Fixpoint peval (penv : V -> F) (e : pexpr) : F :=
    match e with
    | PConst c => c
    | PVar x => penv x
    | PAdd a b => peval penv a + peval penv b
    | PMul a b => peval penv a * peval penv b
    | POpp a => opp (peval penv a)
    end.

  (** Decide whether a list of variable names is free of
      repetitions, by checking at each step that the head does not
      occur again in the tail.

      The compiler needs this for the declared private variables
      [privs].  If a name were declared twice it would own two
      matrix columns, and the correspondence between columns and
      variables, on which the whole compilation rests, would break.
      Being a boolean test, it appears in later statements as a
      hypothesis [nodupb l = true] that a caller discharges by
      computation. *)
  Fixpoint nodupb (l : list V) : bool :=
    match l with
    | List.nil => true
    | List.cons x r => negb (List.existsb (veqb x) r) && nodupb r
    end.

  (** The same repetition test for a list of scalars, used on the
      threshold interpolation points.  It is a separate function
      because it compares with [feqb] instead of [veqb];
      [nodupb_F_sound] below turns a successful test into the
      [List.NoDup] proof that a [CThresh] node stores. *)
  Fixpoint nodupb_F (l : list F) : bool :=
    match l with
    | List.nil => true
    | List.cons x r => negb (List.existsb (feqb x) r) && nodupb_F r
    end.

  (** Count how many flags of a list of booleans are set.

      A threshold statement is made precise by choosing, for every
      child, a flag saying whether that child is claimed to hold.
      The statement then holds when at least [t] flags are set and
      every flagged child really does hold.  [count_true] is how
      "at least [t] of them" is counted. *)
  Fixpoint count_true (bs : list bool) : nat :=
    match bs with
    | List.nil => 0
    | List.cons b bs' => ((if b then 1 else 0) + count_true bs')%nat
    end.

  Section Spec.

    (** The declarations and the instance data.

        - [n] is the number of declared private scalars and [privs]
          their names, in order.  This vector is the interface
          between the source language and the compiled one: column
          number [i] of every compiled matrix belongs to the
          variable sitting at position [i] of [privs].  The proofs
          require [privs] to be free of repetitions.
        - [genv] gives the group element of every point name: the
          bases of the powers and the public targets.
        - [penv] gives the value of every public scalar name; it is
          what [peval] reads.
        - [node] supplies the interpolation points used by threshold
          nodes.  A threshold node shares one verifier challenge
          among its children by evaluating a polynomial at fixed
          public points, and [node i] is the point belonging to
          child number [i].  Those points must be pairwise distinct
          and different from [zero], which the compiler checks; see
          Shamir.v for the counting argument that needs it.

        The private environment is deliberately not a section
        variable: it is the witness, and it is quantified afresh
        inside each statement about the semantics. *)
    Context {n : nat}.
    Variable privs : Vector.t V n.  (* private scalar names *)
    Variable genv : V -> G.         (* point environment *)
    Variable penv : V -> F.         (* public scalar environment *)
    Variable node : nat -> F.       (* threshold interpolation nodes *)

    (** ** Semantics

        What a statement means, given a witness environment.  These
        definitions are the specification: the compiler is correct
        exactly when the compiled relation agrees with them. *)

    (** The group element denoted by one term: its base point,
        raised to the public coefficient times the private scalar.
        All three environments meet here, and only here. *)
    Definition term_denote (wenv : V -> F) (t : term) : G :=
      (genv (t_base t)) ^ (peval penv (t_coeff t) * wenv (t_var t)).

    (** The product of the denotations of a list of terms, folded
        from the right starting at the identity [gid].  An empty
        list denotes [gid], which is why an equation with no private
        term behaves as expected. *)
    Definition terms_fold (wenv : V -> F) (ts : list term) : G :=
      List.fold_right (fun t acc => gop (term_denote wenv t) acc)
        gid ts.

    (** The group element denoted by one public offset: the point
        named in the pair, raised to the value of the public
        expression.  No witness is involved, so the verifier can
        compute it on its own. *)
    Definition off_denote (o : pexpr * V) : G :=
      (genv (snd o)) ^ (peval penv (fst o)).

    (** The product of the denotations of a list of public offsets.
        This product is the entire public part of an equation; the
        compiler inverts it to obtain the target point of the
        corresponding row of the leaf. *)
    Definition off_fold (os : list (pexpr * V)) : G :=
      List.fold_right (fun o acc => gop (off_denote o) acc) gid os.

    (** An equation holds under the witness environment [wenv] when
        the product of its private terms times the product of its
        public offsets is the group identity.  This is the
        homogeneous form announced in the file header. *)
    Definition eq_denote (wenv : V -> F) (e : equation) : Prop :=
      gop (terms_fold wenv (eq_rhs e)) (off_fold (eq_off e)) = gid.

    (** What a statement means under the witness environment
        [wenv].

        Lists of equations, conjunction and disjunction read as one
        would expect.  The threshold case is the only one worth
        reading twice: [SThresh t l] holds when there exists a list
        of flags [bs], one per child, with at least [t] flags set,
        such that every flagged child holds.  Unflagged children are
        not required to hold, and nothing records which children are
        flagged, which is exactly the "at least [t] of them"
        reading.

        The conjunction over flagged children is written as an
        inline fixpoint because [stmt_denote] is still being
        defined; [flagged_denote] just below is the same function,
        standing on its own. *)
    Fixpoint stmt_denote (wenv : V -> F) (s : stmt) : Prop :=
      match s with
      | SEqs eqs => List.Forall (eq_denote wenv) eqs
      | SAnd a b => stmt_denote wenv a ∧ stmt_denote wenv b
      | SOr a b => stmt_denote wenv a ∨ stmt_denote wenv b
      | SThresh t l =>
          ∃ bs : list bool,
            List.length bs = List.length l ∧
            (t <= count_true bs)%nat ∧
            (fix flagged (l : list stmt) (bs : list bool) : Prop :=
               match l, bs with
               | List.cons s' l', List.cons b bs' =>
                   (if b then stmt_denote wenv s' else True) ∧
                   flagged l' bs'
               | _, _ => True
               end) l bs
      end.

    (** The flagged-children conjunction of the threshold case, as a
        function that can be named and reasoned about: walking the
        children and the flags together, a flagged child must hold
        and an unflagged one need not.  It is the same proposition
        as the fixpoint inlined in [stmt_denote], which is what
        [stmt_denote_thresh] states. *)
    Fixpoint flagged_denote (wenv : V -> F) (l : list stmt) (bs : list bool)
      : Prop :=
      match l, bs with
      | List.cons s' l', List.cons b bs' =>
          (if b then stmt_denote wenv s' else True) ∧
          flagged_denote wenv l' bs'
      | _, _ => True
      end.

    (** Unfolding a threshold statement.  The two sides are the same
        proposition, but the right-hand one mentions
        [flagged_denote] instead of an anonymous fixpoint, which is
        what lets later proofs rewrite with it and apply the lemmas
        proved about [flagged_denote].  The proof is a routine
        induction over the child list, translating one form of the
        conjunction into the other. *)
    Lemma stmt_denote_thresh :
      ∀ (wenv : V -> F) (t : nat) (l : list stmt),
      stmt_denote wenv (SThresh t l) <->
      ∃ bs : list bool,
        List.length bs = List.length l ∧
        (t <= count_true bs)%nat ∧ flagged_denote wenv l bs.
    Proof.
      intros *; cbn.
      split; intros (bs & ha & hb & hc); exists bs; repeat split; try assumption.
      + clear ha hb. revert bs hc.
        induction l as [|s l ih]; intros [|b bs] hc; cbn in hc |- *; try exact I.
        destruct hc as (hc & hd); split; [exact hc | eapply ih; exact hd].
      + clear ha hb. revert bs hc.
        induction l as [|s l ih]; intros [|b bs] hc; cbn in hc |- *; try exact I.
        destruct hc as (hc & hd); split; [exact hc | eapply ih; exact hd].
    Qed.

    (** ** Well-formedness

        A statement is well formed when every private variable it
        mentions has been declared in [privs].  An undeclared
        variable would have no column in the compiled matrix, so its
        term would silently disappear and the compiled relation
        would be weaker than the statement; the check rules that
        out. *)

    (** A term is well formed when its private variable occurs among
        the declared names [privs]. *)
    Definition wf_term (t : term) : bool :=
      List.existsb (veqb (t_var t)) (Vector.to_list privs).

    (** An equation is well formed when all of its private terms
        are.  The public offsets need no check: they mention no
        private variable. *)
    Definition wf_eq (e : equation) : bool :=
      List.forallb wf_term (eq_rhs e).

    (** A statement is well formed when every equation occurring in
        it is.  The threshold case uses an inline fixpoint over the
        child list for the same reason as [stmt_denote];
        [wf_stmt_thresh] below restates it as a [List.Forall]. *)
    Fixpoint wf_stmt (s : stmt) : bool :=
      match s with
      | SEqs eqs => List.forallb wf_eq eqs
      | SAnd a b => wf_stmt a && wf_stmt b
      | SOr a b => wf_stmt a && wf_stmt b
      | SThresh t l =>
          (fix go (l : list stmt) : bool :=
             match l with
             | List.nil => true
             | List.cons s' l' => wf_stmt s' && go l'
             end) l
      end.

    (** ** Compilation

        How a statement becomes a [comp_relC].  The heart of it is
        the leaf case: a list of equations over the declared
        variables [privs] is turned into a matrix of group elements,
        with one row per equation and one column per declared
        variable, together with a vector of public target points. *)

    (** The contribution of one term to the column of the declared
        variable [x].

        When the term's private variable is [x], the contribution is
        the base point already raised to the public coefficient.
        Folding the coefficient into the base is what turns
        [genv b ^ (c * wenv x)] into a column entry that only has to
        be raised to [wenv x], which is the shape a linear relation
        over a witness vector requires.  When the term concerns
        another variable it contributes the identity [gid], which is
        neutral for the product taken along the column. *)
    Definition term_col (t : term) (x : V) : G :=
      if veqb (t_var t) x
      then (genv (t_base t)) ^ (peval penv (t_coeff t))
      else gid.

    (** The matrix row of one equation, as a vector indexed by the
        declared variables.

        Column [x] holds the product of [term_col t x] over all
        terms [t] of the list, that is, the product of the folded
        bases of exactly those terms whose private variable is [x];
        every other term contributes [gid] there.  Evaluating this
        row at the compiled witness therefore reproduces the product
        of the term denotations, which is what
        [row_of_terms_correct] proves.

        The correspondence between columns and variables is the
        whole point of the construction.  Because the row is built
        by mapping over [privs], column number [i] belongs to the
        same variable in every row of every equation, so two
        equations mentioning the same variable read the same entry
        of the witness vector. *)
    Definition row_of_terms (ts : list term) : Vector.t G n :=
      Vector.map (fun x =>
        List.fold_right (fun t acc => gop (term_col t x) acc) gid ts)
        privs.

    (** The compiled row of an equation is the row of its private
        terms.  The public offsets do not appear in the matrix at
        all; they become the target point in [compile_leaf]. *)
    Definition compile_eq_row (e : equation) : Vector.t G n :=
      row_of_terms (eq_rhs e).

    (** Compile a list of equations into a single [Leaf].

        The leaf has one row per equation and [n] columns, one per
        declared private variable.  Its public vector holds, for
        each equation, the inverse of the product of that equation's
        public offsets.

        Inverting is what moves the public part across the equality.
        The leaf relation says "the row evaluated at the witness
        equals the public point", while an equation says "the
        private product times the public product is the identity";
        the two are the same statement, by [gop_eq_gid_iff].

        Because all the equations live in one leaf they share one
        witness vector, and that is what binds a variable occurring
        in several equations to a single value. *)
    Definition compile_leaf (eqs : list equation) : comp_relC :=
      Leaf (List.length eqs) n
        (Vector.map compile_eq_row (Vector.of_list eqs))
        (Vector.map (fun e => ginv (off_fold (eq_off e)))
          (Vector.of_list eqs)).

    (** Try to read a statement as a plain conjunction of equations.

        [leaves_only s] returns [Some eqs] when [s] is built out of
        [SEqs] and [SAnd] only, with [eqs] the concatenation of all
        the equations it contains, and [None] as soon as a
        disjunction or a threshold is met.  Such a statement is
        called pure.

        A pure statement is compiled into one merged [Leaf], and
        this matters for soundness.  A [CAnd] node hands its two
        children independent witness vectors, so a private variable
        used on both sides would be answered twice, by two possibly
        different values.  Inside a single leaf there is only one
        witness vector, so shared variables really are shared. *)
    Fixpoint leaves_only (s : stmt) : option (list equation) :=
      match s with
      | SEqs eqs => Some eqs
      | SAnd a b =>
          match leaves_only a, leaves_only b with
          | Some la, Some lb => Some (List.app la lb)
          | _, _ => None
          end
      | SOr _ _ => None
      | SThresh _ _ => None
      end.

    (** The vector of the [k] interpolation points starting at index
        [i], namely [node i], [node (S i)] and so on.  A [CThresh]
        node stores its children's public points as a vector of the
        right length, and this builds that vector. *)
    Fixpoint node_vec (k i : nat) : Vector.t F k :=
      match k with
      | 0 => []
      | S k' => node i :: node_vec k' (S i)
      end.

    (** Are the interpolation points of a threshold over [k]
        children usable?

        The test is that [zero] together with the [k] points are
        pairwise distinct.  Distinctness of the points is what makes
        the counting argument of Shamir.v work: two polynomials of
        low degree agreeing on too many distinct points must be the
        same polynomial.  The point [zero] must also differ from all
        of them because it is where the root challenge is read off.

        The test is a boolean and is run at compile time, so a
        malformed threshold is rejected outright rather than
        producing a protocol that could not be proven sound. *)
    Definition nodes_ok (k : nat) : bool :=
      nodupb_F (List.cons zero (Vector.to_list (node_vec k 0))).

    (** The boolean repetition test implies the propositional one.
        A [CThresh] node stores a [List.NoDup] proof about its
        points, while the compiler can only compute a boolean, so
        this lemma is the bridge between the two.  It is a direct
        induction: the head does not occur in the tail because
        [List.existsb] said so, and the tail is repetition-free by
        the induction hypothesis. *)
    Lemma nodupb_F_sound :
      ∀ l : list F, nodupb_F l = true -> List.NoDup l.
    Proof.
      induction l as [|x l ih]; intro ha; cbn in ha.
      + constructor.
      + eapply andb_true_iff in ha.
        destruct ha as (ha & hb).
        constructor.
        ++ intro hin; eapply negb_true_iff in ha.
           assert (hc : List.existsb (feqb x) l = true).
           { eapply List.existsb_exists. exists x; split; [exact hin |].
             unfold feqb; destruct (Fdec x x); congruence. }
           congruence.
        ++ eapply ih; exact hb.
    Qed.

    (** The compiler: [compile s] is [Some r] with [r] the compiled
        relation, or [None] when the statement cannot be compiled.

        - [SEqs eqs] becomes a single merged leaf.
        - [SAnd a b] first tries to read both sides as pure
          conjunctions of equations.  If it can, their equations are
          appended and compiled into one leaf, so that the two sides
          share a single witness vector.  Otherwise a [CAnd] node is
          kept and the two sides receive independent witnesses.
        - [SOr a b] becomes [COr].
        - [SThresh t l] compiles every child and then builds a
          [CThresh] node holding as many interpolation points as
          there are children.  Two side conditions have to be
          decided here, and their proofs are stored inside the node:
          the threshold may not exceed the number of children, and
          the interpolation points must be usable in the sense of
          [nodes_ok].

        Failure is only ever caused by a malformed threshold.  Note
        that a threshold over [k] children compiles to a node of
        size linear in [k]: there is no expansion into the subsets
        of size [t].

        The recursion over the child list is inlined because
        [compile] is still being defined; [compile_thresh] below
        rewrites it into [compile_list]. *)
    Fixpoint compile (s : stmt) : option comp_relC :=
      match s with
      | SEqs eqs => Some (compile_leaf eqs)
      | SAnd a b =>
          match leaves_only a, leaves_only b with
          | Some la, Some lb => Some (compile_leaf (List.app la lb))
          | _, _ =>
              match compile a, compile b with
              | Some ra, Some rb => Some (CAnd ra rb)
              | _, _ => None
              end
          end
      | SOr a b =>
          match compile a, compile b with
          | Some ra, Some rb => Some (COr ra rb)
          | _, _ => None
          end
      | SThresh t l =>
          match
            (fix go (l : list stmt) : option (list comp_relC) :=
               match l with
               | List.nil => Some List.nil
               | List.cons s' l' =>
                   match compile s', go l' with
                   | Some r, Some rs => Some (List.cons r rs)
                   | _, _ => None
                   end
               end) l
          with
          | None => None
          | Some rs =>
              match le_dec t (List.length rs),
                    Sumbool.sumbool_of_bool (nodes_ok (List.length rs))
              with
              | left Ht, left Hok =>
                  Some (CThresh t (List.length rs)
                    (node_vec (List.length rs) 0) (Vector.of_list rs)
                    (nodupb_F_sound _ Hok) Ht)
              | _, _ => None
              end
          end
      end.

    (** Compiling a list of statements, as a function standing on
        its own: [Some] of the list of compiled children when every
        child compiles, and [None] otherwise.  It is the same
        function as the fixpoint inlined in [compile]; see
        [compile_thresh]. *)
    Fixpoint compile_list (l : list stmt) : option (list comp_relC) :=
      match l with
      | List.nil => Some List.nil
      | List.cons s' l' =>
          match compile s', compile_list l' with
          | Some r, Some rs => Some (List.cons r rs)
          | _, _ => None
          end
      end.

    (** The witness vector that a source witness environment
        compiles to: read [wenv] at each declared name, in the order
        of [privs].

        This is the translation of a secret from the source
        language, where it is a function from names to scalars, into
        the compiled language, where it is a vector of scalars.
        [lookup] below travels in the opposite direction. *)
    Definition compile_witness (wenv : V -> F) : Vector.t F n :=
      Vector.map wenv privs.


    (** ** The disjunction invariant

        The checker that makes the backward direction of correctness
        true, together with the machinery it needs: collecting the
        variables of a statement, testing two sets of variables for
        disjointness, rebuilding an environment from a witness
        vector, and merging two environments. *)

    (** Every private variable occurring in a statement, collected
        into a list, with repetitions.  Only the variables of terms
        are collected, since public offsets contain none.  The list
        is only ever used to ask whether two statements share a
        variable, so repetitions in it do no harm. *)
    Fixpoint stmt_vars (s : stmt) : list V :=
      match s with
      | SEqs eqs =>
          List.flat_map (fun e => List.map t_var (eq_rhs e)) eqs
      | SAnd a b => List.app (stmt_vars a) (stmt_vars b)
      | SOr a b => List.app (stmt_vars a) (stmt_vars b)
      | SThresh _ l =>
          (fix go (l : list stmt) : list V :=
             match l with
             | List.nil => List.nil
             | List.cons s' l' => List.app (stmt_vars s') (go l')
             end) l
      end.

    (** The private variables of a list of statements, concatenated.
        Used for the children of a threshold node. *)
    Definition vars_of_list (l : list stmt) : list V :=
      List.flat_map stmt_vars l.

    (** Do two lists of names share nothing?  [disjointb l₁ l₂] is
        true when no element of [l₁] occurs in [l₂].  This is the
        concrete form the invariant takes at a conjunction the
        compiler could not merge, and at the children of a
        threshold. *)
    Definition disjointb (l₁ l₂ : list V) : bool :=
      List.forallb (fun x => negb (List.existsb (veqb x) l₂)) l₁.

    (** Is the statement pure, that is, a conjunction of equations
        that [leaves_only] accepts and the compiler merges into a
        single leaf?  A boolean reading of "[leaves_only] returned
        [Some]". *)
    Definition pureb (s : stmt) : bool :=
      match leaves_only s with
      | Some _ => true
      | None => false
      end.

    (** Do the statements in a list have pairwise disjoint variable
        sets?  Each statement is tested against the concatenation of
        all the statements after it, which covers every pair exactly
        once.  This is the condition imposed on the children of a
        threshold node, whose witnesses are independent of one
        another. *)
    Fixpoint pairwise_disjointb (l : list stmt) : bool :=
      match l with
      | List.nil => true
      | List.cons s' l' =>
          disjointb (stmt_vars s') (vars_of_list l') && pairwise_disjointb l'
      end.

    (** The disjunction-invariant checker.

        The compiled relation can be strictly weaker than the source
        statement when a private variable is shared between two
        places that end up with independent witnesses.  This checker
        rejects exactly the statements where that can happen.

        A shared variable is bound to one single value only when
        both of its occurrences land inside the same merged leaf,
        reading the same witness vector.  So:

        - at [SAnd a b] the statement is accepted either when both
          sides are pure, in which case the compiler merges them
          into one leaf and sharing is safe, or when the two sides
          have disjoint variable sets and each satisfies the
          invariant on its own;
        - at [SThresh] the children receive independent witnesses,
          so their variable sets must be pairwise disjoint and each
          child must satisfy the invariant;
        - at [SOr a b] nothing more is required than the invariant
          for each branch.  Only one branch's witness is ever used,
          so a variable shared between the two branches is harmless:
          saying there exists a value of [x] making [a] hold or [b]
          hold is the same as saying there exists one making [a]
          hold, or there exists one making [b] hold.

        Dropping the checker really does break the backward
        direction.  DslNecessity.v exhibits a statement that shares
        a variable across an unmerged conjunction, for which the
        compiled relation has a witness although no single source
        environment satisfies the statement. *)
    Fixpoint disj_inv (s : stmt) : bool :=
      match s with
      | SEqs _ => true
      | SAnd a b =>
          (pureb a && pureb b) ||
          (disjointb (stmt_vars a) (stmt_vars b) &&
           disj_inv a && disj_inv b)
      | SOr a b => disj_inv a && disj_inv b
      | SThresh _ l =>
          pairwise_disjointb l &&
          (fix go (l : list stmt) : bool :=
             match l with
             | List.nil => true
             | List.cons s' l' => disj_inv s' && go l'
             end) l
      end.

    (** Turn a compiled witness vector back into a witness
        environment.

        [lookup names vals x] walks the two lists in step and
        returns the value paired with the first occurrence of [x]
        among [names]; a name that does not occur there gets [zero].
        Applied with [names] the declared variables and [vals] the
        witness vector, it inverts [compile_witness] on the declared
        names, which is what [map_lookup_gen] proves.  This is how
        the backward direction manufactures a source witness out of
        a compiled one. *)
    Fixpoint lookup (names : list V) (vals : list F) (x : V) : F :=
      match names, vals with
      | List.cons nm names', List.cons v vals' =>
          if veqb nm x then v else lookup names' vals' x
      | _, _ => zero
      end.

    (** Merge two witness environments, given the list [va] of the
        variables of the left one: a name occurring in [va] is read
        from [w₁], every other name from [w₂].

        When the backward direction meets a conjunction the compiler
        did not merge, it obtains one environment per branch and has
        to produce a single environment satisfying both.  Because
        the checker has guaranteed that the branches share no
        variable, merging in this way changes neither branch's
        reading, which is what [combine_env_denote] proves. *)
    Definition combine_env (va : list V) (w₁ w₂ : V -> F) : V -> F :=
      fun x => if List.existsb (veqb x) va then w₁ x else w₂ x.

    (** Read the flags off a threshold witness: one boolean per
        child, true exactly when that child carries a witness.

        In the compiled world a threshold witness is an optional
        witness per child; in the source world a threshold statement
        is made true by a list of flags.  [wflags] converts the
        former into the latter, so that the backward direction can
        hand [stmt_denote] the flag list it asks for.
        [wflags_count] and [wflags_length] say that the conversion
        preserves the number of witnesses present and the number of
        children. *)
    Fixpoint wflags {m : nat} (v : Vector.t comp_relC m) :
      wlist v -> list bool :=
      match v as v' return wlist v' -> list bool with
      | [] => fun _ => List.nil
      | r :: v' => fun w =>
          List.cons (match fst w with Some _ => true | None => false end)
            (wflags v' (snd w))
      end.

    (** ** Correctness

        Everything above is definitions, and could be written down
        for any group whatsoever.  The proofs need more: the scalars
        must form a field and the points a vector space over it, so
        that exponents can be added and multiplied in the usual
        way. *)

    Section Proofs.

      (** [Hvec] is the assumption that the points [G] with [gpow]
          form a vector space over the field [F].  It provides the
          laws used throughout the algebra below, in particular that
          raising a point to a product of scalars is the same as
          raising it twice in succession, and that raising to a sum
          multiplies the results.  The [Add Field] declaration that
          follows registers the field with the [field] tactic so
          that routine scalar identities are discharged
          automatically. *)
      Context
        {Hvec : @vector_space F (@eq F) zero one add mul sub
          div opp inv G (@eq G) gid ginv gop gpow}.
      Add Field field : (@field_theory_for_stdlib_tactic F
        eq zero one opp add mul sub inv div vector_space_field).

      (** A name is boolean-equal to itself. *)
      Lemma veqb_refl : ∀ x : V, veqb x x = true.
      Proof.
        intro x; unfold veqb; destruct (vdec x x); congruence.
      Qed.

      (** Boolean equality of names implies real equality, so
          [veqb] is faithful and not merely a heuristic.  Together
          with [veqb_refl] this is all the proofs ever need to know
          about it. *)
      Lemma veqb_eq : ∀ x y : V, veqb x y = true -> x = y.
      Proof.
        intros x y; unfold veqb; destruct (vdec x y); congruence.
      Qed.

      (** *** Leaf algebra

          A handful of small facts about evaluating a row of the
          compiled matrix.  Together they show that the matrix built
          by [row_of_terms] evaluates, at the compiled witness, to
          the product of the term denotations, which is the content
          of [row_of_terms_correct]. *)

      (** A row all of whose entries are the identity evaluates to
          the identity, whatever the witness is.  This is what makes
          a term contribute nothing to the columns of the variables
          other than its own. *)
      Lemma row_eval_map_gid :
        ∀ (m : nat) (sv : Vector.t V m) (ws : Vector.t F m),
        row_evalC (Vector.map (fun _ => gid) sv) ws = gid.
      Proof.
        induction m as [|m ihm].
        +
          intros *.
          rewrite (vector_inv_0 sv), (vector_inv_0 ws).
          reflexivity.
        +
          intros *.
          destruct (vector_inv_S sv) as (svh & svt & ha).
          destruct (vector_inv_S ws) as (wsh & wst & hb).
          subst.
          specialize (ihm svt wst).
          unfold row_eval in ihm |- *; cbn.
          rewrite vid_identity, left_identity.
          exact ihm.
      Qed.

      (** Evaluating the pointwise product of two rows at one
          witness gives the product of the two evaluations: row
          evaluation is a homomorphism in the row.  This is what
          lets the row of a list of terms be assembled one term at a
          time, since the row of a cons is the pointwise product of
          the head's row and the tail's row. *)
      Lemma row_eval_zip_gop :
        ∀ (m : nat) (r₁ r₂ : Vector.t G m) (ws : Vector.t F m),
        row_evalC (zip_with gop r₁ r₂) ws =
        gop (row_evalC r₁ ws) (row_evalC r₂ ws).
      Proof.
        induction m as [|m ihm].
        +
          intros *.
          rewrite (vector_inv_0 r₁), (vector_inv_0 r₂),
            (vector_inv_0 ws).
          unfold row_eval; cbn.
          rewrite left_identity.
          reflexivity.
        +
          intros *.
          destruct (vector_inv_S r₁) as (rh₁ & rt₁ & ha).
          destruct (vector_inv_S r₂) as (rh₂ & rt₂ & hb).
          destruct (vector_inv_S ws) as (wh & wt & hc).
          subst.
          specialize (ihm rt₁ rt₂ wt).
          unfold row_eval in ihm |- *; cbn.
          rewrite ihm, smul_distributive_vadd, gop_simp.
          reflexivity.
      Qed.

      (** Mapping a pointwise product over a vector is the same as
          mapping each factor separately and then multiplying
          pointwise.  Pure bookkeeping, needed to put
          [row_of_terms] of a cons into the shape that
          [row_eval_zip_gop] expects. *)
      Lemma map_pointwise_zip :
        ∀ (A : Type) (m : nat) (v : Vector.t A m) (f g : A -> G),
        Vector.map (fun x => gop (f x) (g x)) v =
        zip_with gop (Vector.map f v) (Vector.map g v).
      Proof.
        induction m as [|m ihm].
        +
          intros *.
          rewrite (vector_inv_0 v).
          reflexivity.
        +
          intros *.
          destruct (vector_inv_S v) as (vh & vt & ha); subst.
          cbn.
          rewrite ihm.
          reflexivity.
      Qed.

      (** A term whose private variable was not declared contributes
          nothing: every column entry of its row is the identity, so
          the row evaluates to the identity.  This is one reason
          well-formedness matters, and it is also the key step
          inside [term_col_one_hot]: once the declared name has been
          found, the remaining declarations contribute nothing
          more. *)
      Lemma term_col_absent :
        ∀ (m : nat) (sv : Vector.t V m) (ws : Vector.t F m)
          (t : term),
        List.existsb (veqb (t_var t)) (Vector.to_list sv) = false ->
        row_evalC (Vector.map (term_col t) sv) ws = gid.
      Proof.
        induction m as [|m ihm].
        +
          intros * ha.
          rewrite (vector_inv_0 sv), (vector_inv_0 ws).
          reflexivity.
        +
          intros * ha.
          destruct (vector_inv_S sv) as (svh & svt & hb).
          destruct (vector_inv_S ws) as (wsh & wst & hc).
          subst; cbn in ha.
          eapply orb_false_iff in ha.
          destruct ha as (hal & har).
          specialize (ihm svt wst t har).
          unfold term_col in ihm |- *.
          unfold row_eval in ihm |- *; cbn.
          rewrite hal.
          rewrite vid_identity, left_identity.
          exact ihm.
      Qed.

      (** The row of a single term, evaluated at the compiled
          witness, is exactly that term's denotation.

          The hypotheses are that the term's variable occurs among
          the declared names, and that the declared names have no
          repetition.  Repetition-freeness is what makes the row
          one-hot: the variable owns exactly one column, holding the
          base raised to the public coefficient.  Evaluation raises
          that entry further to the witness value stored in the same
          column, and the two exponents multiply, giving precisely
          the term's denotation.  Every other column holds the
          identity, by [term_col_absent]. *)
      Lemma term_col_one_hot :
        ∀ (m : nat) (sv : Vector.t V m) (wenv : V -> F)
          (t : term),
        List.existsb (veqb (t_var t)) (Vector.to_list sv) = true ->
        nodupb (Vector.to_list sv) = true ->
        row_evalC (Vector.map (term_col t) sv) (Vector.map wenv sv) =
        (genv (t_base t)) ^ (peval penv (t_coeff t) * wenv (t_var t)).
      Proof.
        induction m as [|m ihm].
        +
          intros * ha hb.
          rewrite (vector_inv_0 sv) in ha.
          cbn in ha; congruence.
        +
          intros * ha hb.
          destruct (vector_inv_S sv) as (svh & svt & hc); subst.
          cbn in ha, hb.
          eapply andb_true_iff in hb.
          destruct hb as (hbl & hbr).
          destruct (veqb (t_var t) svh) eqn:hd.
          ++
            eapply veqb_eq in hd.
            assert (he :
              List.existsb (veqb (t_var t)) (Vector.to_list svt) = false).
            rewrite hd.
            eapply negb_true_iff in hbl.
            exact hbl.
            unfold row_eval; cbn.
            unfold term_col at 1.
            rewrite hd, veqb_refl.
            pose proof (term_col_absent m svt
              (Vector.map wenv svt) t he) as hf.
            unfold row_eval in hf; cbn in hf.
            rewrite hf, right_identity.
            rewrite smul_associative_fmul.
            reflexivity.
          ++
            cbn in ha.
            specialize (ihm svt wenv t ha hbr).
            unfold row_eval in ihm |- *; cbn.
            unfold term_col at 1.
            rewrite hd.
            rewrite vid_identity, left_identity.
            exact ihm.
      Qed.

      (** The per-equation correctness lemma: the compiled row of a
          list of terms, evaluated at the compiled witness, is the
          product of the denotations of those terms.

          The hypotheses ask that every term be well formed, so that
          no term is silently dropped, and that the declared names
          have no repetition, so that each variable owns exactly one
          column.  The proof is an induction on the list of terms:
          [map_pointwise_zip] and [row_eval_zip_gop] split the row
          of a cons into the head's row times the tail's row, and
          [term_col_one_hot] evaluates the head. *)
      Lemma row_of_terms_correct :
        ∀ (ts : list term) (wenv : V -> F),
        List.forallb wf_term ts = true ->
        nodupb (Vector.to_list privs) = true ->
        row_evalC (row_of_terms ts) (compile_witness wenv) =
        terms_fold wenv ts.
      Proof.
        induction ts as [|t ts iht].
        +
          intros * ha hb.
          unfold row_of_terms; cbn.
          eapply row_eval_map_gid.
        +
          intros * ha hb.
          cbn in ha.
          eapply andb_true_iff in ha.
          destruct ha as (hal & har).
          unfold row_of_terms; cbn.
          rewrite map_pointwise_zip.
          rewrite row_eval_zip_gop.
          unfold compile_witness.
          rewrite term_col_one_hot;
          [| exact hal | exact hb].
          unfold row_of_terms, terms_fold in iht.
          unfold compile_witness in iht.
          unfold terms_fold; cbn.
          rewrite iht; [| exact har | exact hb].
          reflexivity.
      Qed.


      (** In a group, a product is the identity exactly when one
          factor is the inverse of the other.  This is the algebraic
          content of moving a term to the other side of an equation,
          and it is what connects the homogeneous form used by the
          language with the form a compiled leaf uses. *)
      Lemma gop_eq_gid_iff : ∀ (a b : G),
        gop a b = gid <-> a = ginv b.
      Proof.
        intros *; split; intro ha.
        +
          eapply f_equal with (f := fun z => gop z (ginv b)) in ha.
          rewrite <-associative, right_inverse, right_identity,
            left_identity in ha.
          exact ha.
        +
          rewrite ha.
          rewrite commutative, right_inverse.
          reflexivity.
      Qed.

      (** The equation built by [simple_eq Pn ts] says precisely
          that the point [genv Pn] is the product of the denotations
          of the terms [ts].

          It is true because the single public offset denotes
          [genv Pn] raised to [opp one], which is the inverse of
          [genv Pn], and a product with an inverse is the identity
          exactly when the two elements are equal.  The lemma exists
          so that a user of the language may write and read the
          familiar form while every proof below works with the
          homogeneous one. *)
      Lemma simple_eq_denote :
        ∀ (Pn : V) (ts : list term) (wenv : V -> F),
        eq_denote wenv (simple_eq Pn ts) <->
        genv Pn = terms_fold wenv ts.
      Proof.
        intros *.
        unfold eq_denote, simple_eq; cbn.
        unfold off_fold, off_denote; cbn.
        rewrite right_identity.
        assert (ha : (genv Pn) ^ (opp one) = ginv (genv Pn)).
        rewrite <-connection_between_vopp_and_fopp.
        rewrite field_one. reflexivity.
        rewrite ha.
        rewrite gop_eq_gid_iff.
        rewrite group_inv_inv.
        split; intro hb; symmetry; exact hb.
      Qed.

      (** The compiled leaf is equivalent to the list of equations
          it came from: the leaf relation holds of the compiled
          witness if and only if every equation holds under the
          witness environment.

          The hypotheses are well-formedness of the equations and
          repetition-freeness of the declared names, the same two
          conditions as [row_of_terms_correct].  The proof is an
          induction on the equations.  For each one, the leaf
          relation demands that the row evaluate to the inverted
          public part, which by [gop_eq_gid_iff] is exactly the
          homogeneous equation, and by [row_of_terms_correct] the
          row evaluation is the product of the term denotations.

          This single lemma carries both directions of correctness
          at the leaves, so the two main theorems only have to
          propagate it through the tree. *)
      Lemma compile_leaf_correct :
        ∀ (eqs : list equation) (wenv : V -> F),
        List.forallb wf_eq eqs = true ->
        nodupb (Vector.to_list privs) = true ->
        (comp_rel_holdsC (compile_leaf eqs) (compile_witness wenv) <->
         List.Forall (eq_denote wenv) eqs).
      Proof.
        induction eqs as [|e eqs ihe].
        +
          intros * ha hb.
          split; intro hc.
          constructor.
          reflexivity.
        +
          intros * ha hb.
          cbn in ha.
          eapply andb_true_iff in ha.
          destruct ha as (hae & har).
          specialize (ihe wenv har hb).
          split; intro hc.
          ++
            cbn in hc.
            pose proof (f_equal (@Vector.hd G _) hc) as hh;
            cbn in hh.
            pose proof (f_equal (@Vector.tl G _) hc) as ht;
            cbn in ht.
            constructor.
            +++
              unfold eq_denote.
              eapply gop_eq_gid_iff.
              rewrite <-(row_of_terms_correct (eq_rhs e) wenv hae hb).
              exact hh.
            +++
              eapply ihe.
              exact ht.
          ++
            inversion hc as [| ? ? hde hrest]; subst.
            cbn.
            f_equal.
            +++
              unfold compile_eq_row.
              rewrite row_of_terms_correct;
              [| exact hae | exact hb].
              eapply gop_eq_gid_iff.
              exact hde.
            +++
              eapply ihe.
              exact hrest.
      Qed.

      (** A pure statement means exactly the conjunction of the
          equations that [leaves_only] collects from it.

          Flattening a conjunction into a list loses nothing,
          because conjunction is associative and [List.Forall] over
          an appended list splits into the two halves.  This is what
          lets the compiler forget the shape of a pure AND-tree and
          keep only its equations. *)
      Lemma leaves_only_denote :
        ∀ (s : stmt) (eqs : list equation) (wenv : V -> F),
        leaves_only s = Some eqs ->
        (stmt_denote wenv s <-> List.Forall (eq_denote wenv) eqs).
      Proof.
        induction s as [leqs | a b iha ihb | a b iha ihb | t l ihl]
          using stmt_ind'.
        +
          intros * ha; cbn in ha.
          injection ha as ha; subst.
          cbn; reflexivity.
        +
          intros * ha; cbn in ha.
          destruct (leaves_only a) as [la|] eqn:hb;
          [| congruence].
          destruct (leaves_only b) as [lb|] eqn:hc;
          [| congruence].
          injection ha as ha; subst.
          cbn.
          rewrite (iha la wenv eq_refl), (ihb lb wenv eq_refl).
          rewrite List.Forall_app.
          reflexivity.
        +
          intros * ha; cbn in ha; congruence.
        +
          intros * ha; cbn in ha; congruence.
      Qed.

      (** Collecting the equations of a pure statement preserves
          well-formedness: if the statement is well formed then so
          is every equation collected from it.  Needed because the
          merged leaf is built from the collected list, and
          [compile_leaf_correct] demands that list be well
          formed. *)
      Lemma leaves_only_wf :
        ∀ (s : stmt) (eqs : list equation),
        leaves_only s = Some eqs ->
        wf_stmt s = true ->
        List.forallb wf_eq eqs = true.
      Proof.
        induction s as [leqs | a b iha ihb | a b iha ihb | t l ihl]
          using stmt_ind'.
        +
          intros * ha hb; cbn in ha, hb.
          injection ha as ha; subst.
          exact hb.
        +
          intros * ha hb; cbn in ha, hb.
          eapply andb_true_iff in hb.
          destruct hb as (hbl & hbr).
          destruct (leaves_only a) as [la|] eqn:hc;
          [| congruence].
          destruct (leaves_only b) as [lb|] eqn:hd;
          [| congruence].
          injection ha as ha; subst.
          rewrite List.forallb_app.
          eapply andb_true_iff; split.
          eapply iha; [reflexivity | exact hbl].
          eapply ihb; [reflexivity | exact hbr].
        +
          intros * ha; cbn in ha; congruence.
        +
          intros * ha; cbn in ha; congruence.
      Qed.

      (** The recursion inlined in the threshold case of [compile]
          is [compile_list].  A purely syntactic fact, proved by
          induction on the child list, which lets the proofs below
          reason about the threshold case using a named function
          instead of an anonymous fixpoint. *)
      Lemma compile_thresh :
        ∀ (t : nat) (l : list stmt),
        compile (SThresh t l) =
        match compile_list l with
        | None => None
        | Some rs =>
            match le_dec t (List.length rs),
                  Sumbool.sumbool_of_bool (nodes_ok (List.length rs))
            with
            | left Ht, left Hok =>
                Some (CThresh t (List.length rs)
                  (node_vec (List.length rs) 0) (Vector.of_list rs)
                  (nodupb_F_sound _ Hok) Ht)
            | _, _ => None
            end
        end.
      Proof.
        intros *; cbn.
        assert (ha : ∀ l', (fix go (l : list stmt) : option (list comp_relC) :=
            match l with
            | List.nil => Some List.nil
            | List.cons s' l' =>
                match compile s', go l' with
                | Some r, Some rs => Some (List.cons r rs)
                | _, _ => None
                end
            end) l' = compile_list l').
        { induction l' as [|s' l' ih]; cbn; [reflexivity |].
          rewrite ih; reflexivity. }
        rewrite ha; reflexivity.
      Qed.

      (** Well-formedness of a threshold statement, restated as a
          [List.Forall] over its children.  The same remark as for
          [compile_thresh]: it replaces an inline fixpoint by a
          standard list predicate. *)
      Lemma wf_stmt_thresh :
        ∀ (t : nat) (l : list stmt),
        wf_stmt (SThresh t l) = true -> List.Forall (fun s => wf_stmt s = true) l.
      Proof.
        intros t l; cbn.
        induction l as [|s l ih]; intro ha; cbn in ha.
        + constructor.
        + eapply andb_true_iff in ha; destruct ha as (ha & hb).
          constructor; [exact ha | eapply ih; exact hb].
      Qed.

      (** Build a compiled witness for the children of a threshold
          out of a source proof that the flagged children hold.

          The first hypothesis is the induction hypothesis of the
          main theorem, assumed for every child: a child whose
          denotation holds yields a witness for its compiled
          relation.  The others say that the children are well
          formed, that they all compile, that there is exactly one
          flag per child, and that every flagged child holds.

          The result is a list of optional witnesses carrying a
          witness at exactly the flagged positions, together with
          the fact that the number of witnesses present equals the
          number of flags set.  That count is what a [CThresh]
          relation compares against the threshold, so it is what
          turns "at least [t] flags" into "at least [t]
          witnesses". *)
      Lemma thresh_witness :
        ∀ (l : list stmt) (rs : list comp_relC) (bs : list bool) (wenv : V -> F),
        List.Forall (fun s => ∀ r, wf_stmt s = true -> compile s = Some r ->
          stmt_denote wenv s -> ∃ w, comp_rel_holdsC r w) l ->
        List.Forall (fun s => wf_stmt s = true) l ->
        compile_list l = Some rs ->
        List.length bs = List.length l ->
        flagged_denote wenv l bs ->
        ∃ w : wlist (Vector.of_list rs),
          count_true bs = wcount (Vector.of_list rs) w ∧
          wholds (Vector.of_list rs) w.
      Proof.
        induction l as [|s l ih]; intros rs bs wenv hall hwf hc hlen hfl.
        +
          cbn in hc.
          injection hc as hc; subst.
          destruct bs; [| cbn in hlen; lia].
          exists tt; cbn; split; [reflexivity | exact I].
        +
          cbn in hc.
          destruct (compile s) as [r |] eqn:hr; [| congruence].
          destruct (compile_list l) as [rs' |] eqn:hrs; [| congruence].
          injection hc as hc; subst.
          destruct bs as [| b bs]; [cbn in hlen; lia |].
          cbn in hlen, hfl.
          destruct hfl as (hs & hfl).
          inversion hall as [| ? ? hs' hall']; subst.
          inversion hwf as [| ? ? hwfs hwf']; subst.
          destruct (ih rs' bs wenv hall' hwf' eq_refl ltac:(lia) hfl)
            as (w' & hcount & hw').
          destruct b.
          ++
            destruct (hs' r hwfs hr hs) as (x & hx).
            exists (Some x, w'); cbn.
            split; [rewrite hcount; reflexivity | split; [exact hx | exact hw']].
          ++
            exists (None, w'); cbn.
            split; [rewrite hcount; reflexivity | split; [exact I | exact hw']].
      Qed.

      (** First main theorem: if the statement holds, the compiled
          relation has a witness.

          The hypotheses are that the statement is well formed, that
          the declared names have no repetition, and that the
          statement compiles to [r].  From a proof that the
          statement holds under some witness environment [wenv], the
          conclusion produces a witness of the compiled relation.

          Why it is true, case by case.  At a leaf, the compiled
          witness [compile_witness wenv] works, by
          [compile_leaf_correct].  At a conjunction the compiler
          merged, the very same vector works for both sides at once,
          which is the point of merging.  At a conjunction it did
          not merge, the two branch witnesses are simply paired.  At
          a disjunction, the witness of whichever branch holds is
          injected into the sum.  At a threshold, the flags supplied
          by the semantics say which children to build witnesses
          for, and [thresh_witness] assembles them, with enough of
          them present to meet the threshold.

          No disjunction invariant is needed here.  In this
          direction one source environment is being turned into
          witnesses, so every occurrence of a shared variable
          automatically receives the same value. *)
      Theorem compile_stmt_sound :
        ∀ (s : stmt) (r : comp_relC) (wenv : V -> F),
        wf_stmt s = true ->
        nodupb (Vector.to_list privs) = true ->
        compile s = Some r ->
        stmt_denote wenv s ->
        ∃ (w : comp_witnessC r), comp_rel_holdsC r w.
      Proof.
        induction s as [leqs | a b iha ihb | a b iha ihb | t l ihl]
          using stmt_ind'.
        +
          intros * ha hb hc hd; cbn in ha, hc, hd.
          injection hc as hc; subst.
          exists (compile_witness wenv).
          eapply compile_leaf_correct; assumption.
        +
          intros * ha hb hc hd; cbn in ha, hc, hd.
          eapply andb_true_iff in ha; destruct ha as (hwa & hwb).
          destruct hd as (hda & hdb).
          destruct (leaves_only a) as [la |] eqn:hla;
          [destruct (leaves_only b) as [lb |] eqn:hlb |].
          ++
            injection hc as hc; subst.
            exists (compile_witness wenv).
            eapply compile_leaf_correct.
            +++
              rewrite List.forallb_app; eapply andb_true_iff; split;
              eapply leaves_only_wf; eassumption.
            +++
              exact hb.
            +++
              eapply List.Forall_app; split;
              eapply leaves_only_denote; eassumption.
          ++
            destruct (compile a) as [ra |] eqn:hra; [| congruence].
            destruct (compile b) as [rb |] eqn:hrb; [| congruence].
            injection hc as hc; subst.
            destruct (iha ra wenv hwa hb eq_refl hda) as (wa & hwa').
            destruct (ihb rb wenv hwb hb eq_refl hdb) as (wb & hwb').
            exists (wa, wb); cbn; split; assumption.
          ++
            destruct (compile a) as [ra |] eqn:hra; [| congruence].
            destruct (compile b) as [rb |] eqn:hrb; [| congruence].
            injection hc as hc; subst.
            destruct (iha ra wenv hwa hb eq_refl hda) as (wa & hwa').
            destruct (ihb rb wenv hwb hb eq_refl hdb) as (wb & hwb').
            exists (wa, wb); cbn; split; assumption.
        +
          intros * ha hb hc hd; cbn in ha, hc, hd.
          eapply andb_true_iff in ha; destruct ha as (hwa & hwb).
          destruct (compile a) as [ra |] eqn:hra; [| congruence].
          destruct (compile b) as [rb |] eqn:hrb; [| congruence].
          injection hc as hc; subst.
          destruct hd as [hda | hdb].
          ++
            destruct (iha ra wenv hwa hb eq_refl hda) as (wa & hwa').
            exists (inl wa); cbn; exact hwa'.
          ++
            destruct (ihb rb wenv hwb hb eq_refl hdb) as (wb & hwb').
            exists (inr wb); cbn; exact hwb'.
        +
          intros * ha hb hc hd.
          rewrite compile_thresh in hc.
          eapply wf_stmt_thresh in ha.
          eapply stmt_denote_thresh in hd.
          destruct hd as (bs & hlen & hcnt & hfl).
          destruct (compile_list l) as [rs |] eqn:hrs; [| congruence].
          destruct (le_dec t (List.length rs)) as [Ht |]; [| congruence].
          destruct (Sumbool.sumbool_of_bool (nodes_ok (List.length rs)))
            as [Hok |]; [| congruence].
          injection hc as hc; subst.
          destruct (thresh_witness l rs bs wenv) as (w & hw & hw');
          try assumption.
          ++
            eapply List.Forall_impl; [| exact ihl].
            intros s hs r hwf hcs hds; eapply hs; eassumption.
          ++
            exists w; cbn; split; [lia | exact hw'].
      Qed.

      (** *** From relations to protocols

          The theorem above speaks of relations and witnesses.  The
          two corollaries below lift it to the protocol itself, that
          is, to what the prover, the verifier and the simulator
          actually do.  Each one takes the witness just obtained and
          feeds it to the corresponding theorem of
          Composition.v. *)

      (** Completeness of the compiled protocol: if the statement
          holds, then there is a witness with which the verifier
          accepts the prover's transcript, for every choice of the
          prover's randomness [rnd] and every challenge [c].

          In words, an honest prover that knows a witness is never
          rejected, whatever the verifier asks.  The proof obtains a
          witness from [compile_stmt_sound] and hands it to the
          completeness theorem of the composed protocol. *)
      Corollary compile_protocol_completeness :
        ∀ (s : stmt) (r : comp_relC) (wenv : V -> F),
        wf_stmt s = true ->
        nodupb (Vector.to_list privs) = true ->
        compile s = Some r ->
        stmt_denote wenv s ->
        ∃ (w : comp_witnessC r),
          ∀ (rnd : comp_randC r) (c : F),
          comp_verifyC r c (comp_proveC r w rnd c) = true.
      Proof.
        intros * ha hb hc hd.
        destruct (compile_stmt_sound s r wenv ha hb hc hd) as (w & hw).
        exists w; intros *.
        exact (@comp_completeness F zero one add mul sub div opp inv Fdec
          G gid ginv gop gpow Gdec Hvec r w rnd c hw).
      Qed.

      (** Zero knowledge of the compiled protocol: for a statement
          that holds, the distribution of real transcripts and the
          distribution produced by the simulator are permutations of
          one another, hence the same distribution.

          The simulator is given the statement and the challenge but
          no witness at all, and still produces transcripts.  If its
          output is distributed exactly like the real one, then a
          transcript cannot carry any information about the witness,
          since it could have been produced without knowing one.

          The extra hypotheses concern [lf]: it is non-empty
          ([Hlfn]), has no repetition, and contains every scalar.
          In other words [lf] enumerates the field, which is how a
          uniformly random choice is represented here. *)
      Corollary compile_protocol_zkp :
        ∀ (s : stmt) (r : comp_relC) (wenv : V -> F)
          (lf : list F) (Hlfn : lf <> List.nil) (c : F),
        wf_stmt s = true ->
        nodupb (Vector.to_list privs) = true ->
        compile s = Some r ->
        stmt_denote wenv s ->
        List.NoDup lf -> (∀ x : F, List.In x lf) ->
        ∃ (w : comp_witnessC r),
          Permutation (comp_real_distributionC lf Hlfn r w c)
                      (comp_simulator_distributionC lf Hlfn r c).
      Proof.
        intros * ha hb hc hd hnd hin.
        destruct (compile_stmt_sound s r wenv ha hb hc hd) as (w & hw).
        exists w.
        exact (@comp_distribution_perm F zero one add mul sub div opp inv Fdec
          G gid ginv gop gpow Hvec r lf Hlfn w c hnd hin hw).
      Qed.


      (** *** Reading a compiled witness back

          The backward direction.  Given a witness for the compiled
          relation, reconstruct a witness environment for the source
          statement.  Most of the work is plumbing: rebuilding an
          environment from a vector, and merging the environments
          coming from different branches without disturbing one
          another, which is where the disjunction invariant earns
          its keep. *)

      (** Membership in a list of names makes the boolean test
          [List.existsb] with [veqb] succeed: the bridge from the
          propositional side to the boolean side. *)
      Lemma in_vars_existsb :
        ∀ (l : list V) (x : V),
        List.In x l -> List.existsb (veqb x) l = true.
      Proof.
        intros * ha.
        eapply List.existsb_exists.
        exists x.
        split. exact ha. eapply veqb_refl.
      Qed.

      (** If two lists of names are disjoint according to
          [disjointb], then a name taken from the second is not
          found in the first.  This is the shape in which
          disjointness is used by [combine_env]: a variable of the
          right-hand branch is absent from the left branch's list,
          so the merged environment reads it from the right. *)
      Lemma disjointb_existsb :
        ∀ (l₁ l₂ : list V) (x : V),
        disjointb l₁ l₂ = true ->
        List.In x l₂ ->
        List.existsb (veqb x) l₁ = false.
      Proof.
        intros * ha hb.
        destruct (List.existsb (veqb x) l₁) eqn:hc;
        [| reflexivity].
        eapply List.existsb_exists in hc.
        destruct hc as (y & hy & hxy).
        eapply veqb_eq in hxy; subst.
        unfold disjointb in ha.
        pose proof (proj1 (List.forallb_forall _ _) ha y hy) as hd.
        eapply negb_true_iff in hd.
        pose proof (in_vars_existsb _ _ hb) as he.
        congruence.
      Qed.

      (** Extending a lookup with a name that does not occur among
          the declarations [sv] changes nothing, once the lookup is
          mapped over [sv].  This is the step lemma inside
          [map_lookup_gen]: after the head declaration has been
          consumed, it cannot reappear in the tail, so the extra
          case of the lookup is never taken. *)
      Lemma lookup_skip :
        ∀ (m : nat) (sv : Vector.t V m) (names : list V)
          (vals : list F) (nm : V) (v : F),
        List.existsb (veqb nm) (Vector.to_list sv) = false ->
        Vector.map
          (fun x => if veqb nm x then v else lookup names vals x) sv =
        Vector.map (lookup names vals) sv.
      Proof.
        induction m as [|m ihm].
        +
          intros * ha.
          rewrite (vector_inv_0 sv).
          reflexivity.
        +
          intros * ha.
          destruct (vector_inv_S sv) as (svh & svt & hb); subst.
          cbn in ha.
          eapply orb_false_iff in ha.
          destruct ha as (hal & har).
          cbn.
          rewrite hal.
          f_equal.
          eapply ihm.
          exact har.
      Qed.

      (** The round trip: reconstructing an environment from a
          witness vector with [lookup], and then compiling it back,
          returns the original vector, provided the declared names
          have no repetition.

          Repetition-freeness is essential here.  If a name were
          declared twice, [lookup] would always return the value of
          its first occurrence and the second entry of the vector
          would be lost.  This lemma is what lets the backward
          direction at a leaf hand back a genuine source witness. *)
      Lemma map_lookup_gen :
        ∀ (m : nat) (sv : Vector.t V m) (ws : Vector.t F m),
        nodupb (Vector.to_list sv) = true ->
        Vector.map (lookup (Vector.to_list sv) (Vector.to_list ws)) sv
          = ws.
      Proof.
        induction m as [|m ihm].
        +
          intros * ha.
          rewrite (vector_inv_0 sv), (vector_inv_0 ws).
          reflexivity.
        +
          intros * ha.
          destruct (vector_inv_S sv) as (svh & svt & hb).
          destruct (vector_inv_S ws) as (wh & wt & hc).
          subst.
          cbn in ha.
          eapply andb_true_iff in ha.
          destruct ha as (hal & har).
          eapply negb_true_iff in hal.
          cbn.
          rewrite veqb_refl.
          f_equal.
          rewrite lookup_skip.
          eapply ihm.
          exact har.
          exact hal.
      Qed.

      (** *** Frame lemmas

          A denotation looks only at the variables that actually
          occur in it, so two environments agreeing on those
          variables give the same reading.  These lemmas are what
          make merging environments safe, and each is a
          straightforward induction.

          This first one is the fold over a list of terms: two
          environments agreeing on the variables of the terms give
          the same product of term denotations. *)
      Lemma term_fold_ext :
        ∀ (ts : list term) (w₁ w₂ : V -> F),
        (∀ x, List.In x (List.map t_var ts) -> w₁ x = w₂ x) ->
        List.fold_right (fun t acc => gop (term_denote w₁ t) acc)
          gid ts =
        List.fold_right (fun t acc => gop (term_denote w₂ t) acc)
          gid ts.
      Proof.
        induction ts as [|t ts iht].
        +
          intros; reflexivity.
        +
          intros * ha.
          cbn.
          f_equal.
          ++
            unfold term_denote.
            rewrite (ha (t_var t) (or_introl eq_refl)).
            reflexivity.
          ++
            eapply iht.
            intros x hx.
            eapply ha.
            right; exact hx.
      Qed.

      (** The same for a single equation: one that holds under [w₁]
          holds under [w₂] whenever the two environments agree on
          the variables occurring in its terms.  The public offsets
          are untouched, since they mention no private variable. *)
      Lemma eq_denote_ext :
        ∀ (e : equation) (w₁ w₂ : V -> F),
        (∀ x, List.In x (List.map t_var (eq_rhs e)) -> w₁ x = w₂ x) ->
        eq_denote w₁ e -> eq_denote w₂ e.
      Proof.
        intros * ha hb.
        unfold eq_denote, terms_fold in hb |- *.
        rewrite <-(term_fold_ext (eq_rhs e) w₁ w₂ ha).
        exact hb.
      Qed.

      (** The same for a list of equations, with the variables
          collected from all of them. *)
      Lemma eqs_denote_ext :
        ∀ (eqs : list equation) (w₁ w₂ : V -> F),
        (∀ x, List.In x (List.flat_map
          (fun e => List.map t_var (eq_rhs e)) eqs) -> w₁ x = w₂ x) ->
        List.Forall (eq_denote w₁) eqs ->
        List.Forall (eq_denote w₂) eqs.
      Proof.
        induction eqs as [|e eqs ihe].
        +
          intros; constructor.
        +
          intros * ha hb.
          inversion hb as [| ? ? hbe hbr]; subst.
          constructor.
          ++
            eapply eq_denote_ext; [| exact hbe].
            intros x hx.
            eapply ha; cbn.
            eapply List.in_or_app.
            left; exact hx.
          ++
            eapply ihe; [| exact hbr].
            intros x hx.
            eapply ha; cbn.
            eapply List.in_or_app.
            right; exact hx.
      Qed.

      (** The variables of a threshold statement are the variables
          of its children, concatenated.  Once again a restatement
          of an inline fixpoint in terms of a named function. *)
      Lemma stmt_vars_thresh :
        ∀ (t : nat) (l : list stmt), stmt_vars (SThresh t l) = vars_of_list l.
      Proof.
        intros t l; cbn; unfold vars_of_list.
        induction l as [|s l ih]; cbn; [reflexivity |].
        rewrite ih; reflexivity.
      Qed.

      (** The invariant at a threshold statement, unpacked into its
          two halves: the children have pairwise disjoint variables,
          and each child satisfies the invariant itself. *)
      Lemma disj_inv_thresh :
        ∀ (t : nat) (l : list stmt),
        disj_inv (SThresh t l) = true ->
        pairwise_disjointb l = true ∧ List.Forall (fun s => disj_inv s = true) l.
      Proof.
        intros t l ha; cbn in ha.
        eapply andb_true_iff in ha; destruct ha as (ha & hb).
        split; [exact ha |].
        clear ha.
        induction l as [|s l ih]; cbn in hb.
        + constructor.
        + eapply andb_true_iff in hb; destruct hb as (hb & hc).
          constructor; [exact hb | eapply ih; exact hc].
      Qed.

      (** The frame lemma for a whole statement: if two environments
          agree on every variable occurring in [s], then [s] holds
          under one exactly when it holds under the other.

          It is proved by induction over statements with
          [stmt_ind'], pushing the agreement hypothesis into each
          subtree, and it rests on the frame lemmas for equations.
          This is the lemma that makes an environment built for one
          branch usable in a context where the other branches have
          been given values of their own. *)
      Lemma stmt_denote_ext :
        ∀ (s : stmt) (w₁ w₂ : V -> F),
        (∀ x, List.In x (stmt_vars s) -> w₁ x = w₂ x) ->
        stmt_denote w₁ s -> stmt_denote w₂ s.
      Proof.
        induction s as [eqs | a b iha ihb | a b iha ihb | t l ihl]
          using stmt_ind'.
        +
          intros * ha hb; cbn in *.
          eapply eqs_denote_ext; [exact ha | exact hb].
        +
          intros * ha hb; cbn in *.
          destruct hb as (hbl & hbr).
          split.
          ++
            eapply iha; [| exact hbl].
            intros x hx. eapply ha, List.in_or_app. left; exact hx.
          ++
            eapply ihb; [| exact hbr].
            intros x hx. eapply ha, List.in_or_app. right; exact hx.
        +
          intros * ha hb; cbn in *.
          destruct hb as [hb | hb].
          ++
            left. eapply iha; [| exact hb].
            intros x hx. eapply ha, List.in_or_app. left; exact hx.
          ++
            right. eapply ihb; [| exact hb].
            intros x hx. eapply ha, List.in_or_app. right; exact hx.
        +
          intros * ha hb.
          rewrite stmt_vars_thresh in ha.
          eapply stmt_denote_thresh in hb.
          eapply stmt_denote_thresh.
          destruct hb as (bs & hlen & hcnt & hfl).
          exists bs; split; [exact hlen | split; [exact hcnt |]].
          clear hlen hcnt.
          revert bs hfl.
          induction l as [|s l ih]; intros [|b bs] hfl; cbn in hfl |- *;
          try exact I.
          inversion ihl as [| ? ? hs hl]; subst.
          destruct hfl as (hfs & hfl).
          split.
          ++
            destruct b; [| exact I].
            eapply hs; [| exact hfs].
            intros x hx. eapply ha. unfold vars_of_list; cbn.
            eapply List.in_or_app; left; exact hx.
          ++
            eapply ih; [exact hl | | exact hfl].
            intros x hx. eapply ha. unfold vars_of_list in hx |- *; cbn.
            eapply List.in_or_app; right; exact hx.
      Qed.

      (** The same frame property for the flagged conjunction over
          the children of a threshold node. *)
      Lemma flagged_denote_ext :
        ∀ (l : list stmt) (bs : list bool) (w₁ w₂ : V -> F),
        (∀ x, List.In x (vars_of_list l) -> w₁ x = w₂ x) ->
        flagged_denote w₁ l bs -> flagged_denote w₂ l bs.
      Proof.
        induction l as [|s l ih]; intros [|b bs] w₁ w₂ ha hfl;
        cbn in hfl |- *; try exact I.
        destruct hfl as (hfs & hfl).
        split.
        +
          destruct b; [| exact I].
          eapply stmt_denote_ext; [| exact hfs].
          intros x hx. eapply ha. unfold vars_of_list; cbn.
          eapply List.in_or_app; left; exact hx.
        +
          eapply ih; [| exact hfl].
          intros x hx. eapply ha. unfold vars_of_list in hx |- *; cbn.
          eapply List.in_or_app; right; exact hx.
      Qed.

      (** Merging is sound when the two statements share no
          variable: if [a] holds under [wa] and [b] holds under
          [wb], and their variable sets are disjoint, then both hold
          under the merged environment built by [combine_env].

          The reason is exactly the frame lemma.  On the variables
          of [a] the merged environment agrees with [wa] by
          construction, and on the variables of [b] it agrees with
          [wb], because disjointness guarantees that none of them
          appears in [a]'s list.  This is the single place where the
          disjointness demanded by [disj_inv] pays off. *)
      Lemma combine_env_denote :
        ∀ (a b : stmt) (wa wb : V -> F),
        disjointb (stmt_vars a) (stmt_vars b) = true ->
        stmt_denote wa a -> stmt_denote wb b ->
        stmt_denote (combine_env (stmt_vars a) wa wb) a ∧
        stmt_denote (combine_env (stmt_vars a) wa wb) b.
      Proof.
        intros * hdisj ha hb.
        split.
        +
          eapply stmt_denote_ext; [| exact ha].
          intros x hx.
          unfold combine_env.
          rewrite (in_vars_existsb _ _ hx).
          reflexivity.
        +
          eapply stmt_denote_ext; [| exact hb].
          intros x hx.
          unfold combine_env.
          rewrite (disjointb_existsb _ _ _ hdisj hx).
          reflexivity.
      Qed.

      (** Converting a threshold witness into flags preserves the
          count: the number of flags set equals the number of
          children carrying a witness.  This is how the compiled
          threshold condition turns into the source one. *)
      Lemma wflags_count :
        ∀ (m : nat) (v : Vector.t comp_relC m) (w : wlist v),
        count_true (wflags v w) = wcount v w.
      Proof.
        induction v as [|r m v ih]; intros w; cbn.
        + reflexivity.
        + destruct (fst w); cbn; rewrite ih; reflexivity.
      Qed.

      (** Converting a threshold witness into flags produces exactly
          one flag per child. *)
      Lemma wflags_length :
        ∀ (m : nat) (v : Vector.t comp_relC m) (w : wlist v),
        List.length (wflags v w) = m.
      Proof.
        induction v as [|r m v ih]; intros w; cbn.
        + reflexivity.
        + rewrite ih; reflexivity.
      Qed.

      (** The backward direction for the children of a threshold:
          one single environment under which every child carrying a
          witness holds.

          The hypotheses are the induction hypothesis of the main
          theorem for each child, well-formedness of the children,
          the invariant for each child, pairwise disjointness of the
          children's variables, that the children all compile, and
          that the compiled witness list satisfies them.

          The environments produced by the individual children are
          merged one at a time with [combine_env], walking the list
          from the left.  Pairwise disjointness is what makes each
          merge harmless: the head's variables occur in no later
          child, so extending the tail's environment with the head's
          values disturbs nothing already established. *)
      Lemma thresh_reflect :
        ∀ (l : list stmt) (rs : list comp_relC) (w : wlist (Vector.of_list rs)),
        List.Forall (fun s => ∀ r, wf_stmt s = true -> disj_inv s = true ->
          compile s = Some r ->
          ∀ w : comp_witnessC r, comp_rel_holdsC r w ->
          ∃ wenv, stmt_denote wenv s) l ->
        List.Forall (fun s => wf_stmt s = true) l ->
        List.Forall (fun s => disj_inv s = true) l ->
        pairwise_disjointb l = true ->
        compile_list l = Some rs ->
        wholds (Vector.of_list rs) w ->
        ∃ wenv, flagged_denote wenv l (wflags (Vector.of_list rs) w).
      Proof.
        induction l as [|s l ih]; intros rs w hall hwf hinv hpair hc hw.
        +
          cbn in hc.
          injection hc as hc; subst.
          exists (fun _ => zero); cbn; exact I.
        +
          cbn in hc.
          destruct (compile s) as [r |] eqn:hr; [| congruence].
          destruct (compile_list l) as [rs' |] eqn:hrs; [| congruence].
          injection hc as hc; subst.
          cbn in hpair.
          eapply andb_true_iff in hpair; destruct hpair as (hdisj & hpair).
          inversion hall as [| ? ? hs hall']; subst.
          inversion hwf as [| ? ? hwfs hwf']; subst.
          inversion hinv as [| ? ? hinvs hinv']; subst.
          destruct w as (ow & w'); cbn in hw.
          destruct hw as (hws & hw').
          destruct (ih rs' w' hall' hwf' hinv' hpair eq_refl hw')
            as (wenv' & hfl).
          destruct ow as [x |].
          ++
            destruct (hs r hwfs hinvs hr x hws) as (wenv_s & hd).
            exists (combine_env (stmt_vars s) wenv_s wenv'); cbn.
            split.
            +++
              eapply stmt_denote_ext; [| exact hd].
              intros y hy. unfold combine_env.
              rewrite (in_vars_existsb _ _ hy). reflexivity.
            +++
              eapply flagged_denote_ext; [| exact hfl].
              intros y hy. unfold combine_env.
              rewrite (disjointb_existsb _ _ _ hdisj hy). reflexivity.
          ++
            exists wenv'; cbn.
            split; [exact I | exact hfl].
      Qed.

      (** Compiling a list of statements preserves its length, so a
          threshold node has as many children after compilation as
          before.  Needed in order to match the flag list, which has
          one entry per source child, against the compiled
          children. *)
      Lemma compile_list_length :
        ∀ (l : list stmt) (rs : list comp_relC),
        compile_list l = Some rs -> List.length rs = List.length l.
      Proof.
        induction l as [|s l ih]; intros rs hc; cbn in hc.
        + injection hc as hc; subst; reflexivity.
        + destruct (compile s); [| congruence].
          destruct (compile_list l) as [rs' |] eqn:hrs; [| congruence].
          injection hc as hc; subst; cbn.
          rewrite (ih rs' eq_refl); reflexivity.
      Qed.

      (** The backward direction at a conjunction the compiler did
          not merge.

          The two branches were compiled separately, so the witness
          of a [CAnd] node is a pair of independent witnesses.  Each
          of them yields an environment for its own branch, and
          because the invariant guarantees that the branches share
          no variable, [combine_env_denote] merges the two
          environments into one under which the conjunction holds.

          Without disjointness this step would simply be false: the
          two branch environments could disagree on a shared
          variable, and then no merge of them would satisfy both
          branches. *)
      Lemma and_reflect_unmerged :
        ∀ (a b : stmt) (ra rb : comp_relC),
        (∀ w : comp_witnessC ra, comp_rel_holdsC ra w ->
          ∃ wenv, stmt_denote wenv a) ->
        (∀ w : comp_witnessC rb, comp_rel_holdsC rb w ->
          ∃ wenv, stmt_denote wenv b) ->
        disjointb (stmt_vars a) (stmt_vars b) = true ->
        ∀ (w : comp_witnessC (CAnd ra rb)), comp_rel_holdsC (CAnd ra rb) w ->
        ∃ wenv, stmt_denote wenv (SAnd a b).
      Proof.
        intros * iha ihb hdisj w hw.
        destruct w as (wa & wb); cbn in hw.
        destruct hw as (hwa & hwb).
        destruct (iha wa hwa) as (wea & hwea).
        destruct (ihb wb hwb) as (web & hweb).
        exists (combine_env (stmt_vars a) wea web); cbn.
        eapply combine_env_denote; assumption.
      Qed.

      (** Second main theorem: any witness for the compiled relation
          can be read back as a witness environment for the source
          statement.

          The hypotheses are well-formedness, repetition-freeness of
          the declared names, the disjunction invariant, and that
          the statement compiles to [r].  Given any witness [w] of
          [r], the conclusion produces an environment [wenv] under
          which the statement holds.

          Why it is true, case by case.  At a leaf the witness is a
          vector; [lookup] turns it into an environment, and
          [map_lookup_gen] shows that compiling that environment
          gives the vector back, so [compile_leaf_correct] applies.
          At a conjunction the compiler merged, there is one leaf
          and one vector, so the single reconstructed environment
          satisfies both sides at once, and this is where sharing a
          variable is genuinely sound.  At a conjunction it did not
          merge, the two branch environments are combined by
          [and_reflect_unmerged], using the disjointness the
          invariant provides.  At a disjunction, whichever branch
          the witness names is reflected and its environment
          returned.  At a threshold, [thresh_reflect] merges the
          children's environments while [wflags] turns the compiled
          witness into the flag list the semantics asks for, with
          [wflags_count] and [compile_list_length] supplying the
          count and the length that the semantics demands.

          This is the direction that needs the invariant, and
          DslNecessity.v shows that the need is real. *)
      Theorem compile_stmt_reflect :
        ∀ (s : stmt) (r : comp_relC),
        wf_stmt s = true ->
        nodupb (Vector.to_list privs) = true ->
        disj_inv s = true ->
        compile s = Some r ->
        ∀ (w : comp_witnessC r),
        comp_rel_holdsC r w ->
        ∃ (wenv : V -> F), stmt_denote wenv s.
      Proof.
        induction s as [eqs | a b iha ihb | a b iha ihb | t l ihl]
          using stmt_ind'.
        +
          intros r ha hb hinv hc w hw; cbn in ha, hc.
          injection hc as hc; subst.
          exists (lookup (Vector.to_list privs) (Vector.to_list w)); cbn.
          eapply compile_leaf_correct; [exact ha | exact hb |].
          unfold compile_witness.
          rewrite map_lookup_gen; [exact hw | exact hb].
        +
          intros r ha hb hinv hc; cbn in ha, hc, hinv.
          eapply andb_true_iff in ha; destruct ha as (hal & har).
          unfold pureb in hinv.
          destruct (leaves_only a) as [la |] eqn:hd;
          destruct (leaves_only b) as [lb |] eqn:he.
          ++
            (* both pure: one merged Leaf, shared witness vector *)
            injection hc as hc; subst.
            intros w hw.
            exists (lookup (Vector.to_list privs) (Vector.to_list w)).
            assert (hf : List.Forall
              (eq_denote (lookup (Vector.to_list privs) (Vector.to_list w)))
              (List.app la lb)).
            { eapply compile_leaf_correct; [| exact hb |].
              - rewrite List.forallb_app; eapply andb_true_iff; split;
                eapply leaves_only_wf; eassumption.
              - unfold compile_witness.
                rewrite map_lookup_gen; [exact hw | exact hb]. }
            eapply List.Forall_app in hf; destruct hf as (hfl & hfr).
            cbn; split.
            - eapply (leaves_only_denote a la _ hd); exact hfl.
            - eapply (leaves_only_denote b lb _ he); exact hfr.
          ++
            (* unmerged: independent witnesses, disjointness *)
            cbn in hinv.
            eapply andb_true_iff in hinv; destruct hinv as (hinv & hinvb).
            eapply andb_true_iff in hinv; destruct hinv as (hdisj & hinva).
            destruct (compile a) as [ra |] eqn:hra; [| congruence].
            destruct (compile b) as [rb |] eqn:hrb; [| congruence].
            injection hc as hc; subst.
            eapply and_reflect_unmerged; [| | exact hdisj].
            - intros wa hwa; eapply (iha ra hal hb hinva eq_refl wa hwa).
            - intros wb hwb; eapply (ihb rb har hb hinvb eq_refl wb hwb).
          ++
            cbn in hinv.
            eapply andb_true_iff in hinv; destruct hinv as (hinv & hinvb).
            eapply andb_true_iff in hinv; destruct hinv as (hdisj & hinva).
            destruct (compile a) as [ra |] eqn:hra; [| congruence].
            destruct (compile b) as [rb |] eqn:hrb; [| congruence].
            injection hc as hc; subst.
            eapply and_reflect_unmerged; [| | exact hdisj].
            - intros wa hwa; eapply (iha ra hal hb hinva eq_refl wa hwa).
            - intros wb hwb; eapply (ihb rb har hb hinvb eq_refl wb hwb).
          ++
            cbn in hinv.
            eapply andb_true_iff in hinv; destruct hinv as (hinv & hinvb).
            eapply andb_true_iff in hinv; destruct hinv as (hdisj & hinva).
            destruct (compile a) as [ra |] eqn:hra; [| congruence].
            destruct (compile b) as [rb |] eqn:hrb; [| congruence].
            injection hc as hc; subst.
            eapply and_reflect_unmerged; [| | exact hdisj].
            - intros wa hwa; eapply (iha ra hal hb hinva eq_refl wa hwa).
            - intros wb hwb; eapply (ihb rb har hb hinvb eq_refl wb hwb).
        +
          intros r ha hb hinv hc; cbn in ha, hc, hinv.
          eapply andb_true_iff in ha; destruct ha as (hal & har).
          eapply andb_true_iff in hinv; destruct hinv as (hinva & hinvb).
          destruct (compile a) as [ra |] eqn:hra; [| congruence].
          destruct (compile b) as [rb |] eqn:hrb; [| congruence].
          injection hc as hc; subst.
          intros w hw.
          destruct w as [wa | wb].
          ++
            destruct (iha ra hal hb hinva eq_refl wa hw) as (wea & hwea).
            exists wea; left; exact hwea.
          ++
            destruct (ihb rb har hb hinvb eq_refl wb hw) as (web & hweb).
            exists web; right; exact hweb.
        +
          intros r ha hb hinv hc.
          rewrite compile_thresh in hc.
          eapply wf_stmt_thresh in ha.
          eapply disj_inv_thresh in hinv; destruct hinv as (hpair & hinvl).
          destruct (compile_list l) as [rs |] eqn:hrs; [| congruence].
          destruct (le_dec t (List.length rs)) as [Ht |]; [| congruence].
          destruct (Sumbool.sumbool_of_bool (nodes_ok (List.length rs)))
            as [Hok |]; [| congruence].
          injection hc as hc; subst.
          intros w hw; cbn in hw.
          destruct hw as (hcount & hholds).
          destruct (thresh_reflect l rs w) as (wenv & hfl); try assumption.
          ++
            eapply List.Forall_impl; [| exact ihl].
            intros s hs r hwf hinvs hcs; eapply hs; eassumption.
          ++
            exists wenv.
            eapply stmt_denote_thresh.
            exists (wflags (Vector.of_list rs) w).
            split; [| split].
            - rewrite wflags_length. eapply compile_list_length; exact hrs.
            - rewrite wflags_count; exact hcount.
            - exact hfl.
      Qed.

      (** Special soundness, stated at the level of the source
          language.

          Suppose a prover produced two accepting transcripts [tr]
          and [tr'] that begin with the same announcement but answer
          two different challenges [c] and [c'].  Then the statement
          itself is satisfiable: there is a witness environment
          under which it holds.

          This is the guarantee a proof system is really wanted for.
          A prover able to answer two different challenges after
          committing to a single announcement cannot be guessing,
          and rewinding it extracts a witness.  Special soundness of
          the composed protocol produces a witness of the compiled
          relation, and [compile_stmt_reflect] translates that
          witness back into the source language, so the guarantee is
          about the statement the user wrote and not about the
          matrix the compiler built.

          The hypotheses are the three static checks
          ([wf_stmt], repetition-freeness of [privs], and
          [disj_inv]), that [s] compiles to [r], that the two
          challenges differ, that the two transcripts share their
          announcement, and that the verifier accepts both. *)
      Corollary compile_protocol_soundness :
        ∀ (s : stmt) (r : comp_relC) (c c' : F)
          (tr tr' : @comp_transcript F zero G r),
        wf_stmt s = true ->
        nodupb (Vector.to_list privs) = true ->
        disj_inv s = true ->
        compile s = Some r ->
        c <> c' ->
        @comp_same_announcement F zero G r tr tr' ->
        comp_verifyC r c tr = true ->
        comp_verifyC r c' tr' = true ->
        ∃ (wenv : V -> F), stmt_denote wenv s.
      Proof.
        intros * ha hb hc hr hd he hf hg.
        destruct (@comp_special_soundness F zero one add mul sub div
          opp inv Fdec G gid ginv gop gpow Gdec Hvec
          r c c' tr tr' hd he hf hg) as (w & hw).
        eapply compile_stmt_reflect; eassumption.
      Qed.

    End Proofs.

  End Spec.

End Dsl.
