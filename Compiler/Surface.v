From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool List PeanoNat Permutation.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import
  Util.
From Compiler Require Import
  LinearRelation Composition Dsl DslSubst DslRename
  DslRepair DslNeq DslRange VarType.

Import VectorNotations.

(** * Surface: the language people write, and how it becomes the core

    ** What a surface language is

    A compiler usually holds two languages at once.  The core
    language is small: few constructs, each with a simple meaning,
    chosen so that the hard theorems about it stay short.  The
    surface language is the one a human actually writes.  It has the
    conveniences: named definitions, comparisons, ranges, arithmetic
    written the way one would write it on paper.  Elaboration is the
    pass that translates the second into the first.

    The core language of Dsl.v is deliberately austere.  A core
    statement is a tree whose leaves are lists of homogeneous linear
    equations, combined by AND, OR, and "at least [t] of these".
    Homogeneous means every equation is written as "this product of
    powers equals the group identity", with nothing on the other
    side.  Linear means every exponent is a public coefficient times
    a single private scalar.  That is exactly the shape a sigma
    protocol can prove, and nothing more, which is why the core
    refuses to be any richer.

    ** The surface language

    This file defines the language a user writes, after the
    sigma-compiler front end, in three syntactic classes:

    - scalar expressions [sexpr]: constants, public scalars, private
      scalars, sums, products and negation;
    - point expressions [gexpr]: the group identity, named points,
      products, inverses, and a named point raised to a scalar
      expression;
    - statements [sstmt]: equality of two point expressions, a
      scalar expression being nonzero, a private scalar lying below
      a bound, a local definition of a private scalar, and the AND,
      OR and t-of-n combinators.

    A witness is the secret data the prover claims to know.  Here it
    is an environment: a function from names to field elements.  A
    private variable is one whose value lives in the witness; a
    public variable is one whose value both parties already know.

    ** What elaboration does

    [elab] turns a surface statement into a core statement.  It

    - flattens each side of a point equation into a list of private
      terms and a list of public offsets, which requires that every
      exponent be linear in the private scalars and that every
      exponent sit directly on a named point;
    - lowers the nonzero test and the range test to the gadgets of
      DslNeq.v and DslRange.v, whose auxiliary variables and
      commitment points are drawn from the fresh-name generator of
      VarType.v;
    - eliminates a local definition by the substitution pass of
      DslSubst.v;
    - threads a list of already-used names through the whole walk,
      so that no two gadgets ever pick the same auxiliary name.

    Elaboration may fail, which is why [elab] returns an option.  It
    fails exactly when the user wrote something the protocol cannot
    prove, such as a product of two private scalars.

    ** The two theorems

    [elab_sound] is a dichotomy.  From a witness of the elaborated
    core statement one gets either a witness of the surface
    statement, or a proof that the commitment setup itself was
    broken.  A Pedersen commitment to a value [v] with randomness
    [r] is the group element
    [gop (gpow A v) (gpow B r)], for two public base points [A] and
    [B].  It hides [v], and binds the committer to [v], only as long
    as nobody knows how [A] and [B] relate.  Broken means either [A]
    is the group identity, or someone exhibits a scalar [d] with
    [A = gpow B d].  Neither can be produced when the bases were
    generated honestly, so in practice the dichotomy collapses to
    the first alternative, which is what soundness should say.

    [elab_complete] is the other direction.  An honest prover who
    satisfies the surface statement can satisfy the core statement
    too.  Doing so means publishing the gadgets' commitment points
    and filling in the gadgets' auxiliary scalars, so the
    environments do grow.  They grow only at names that were fresh:
    everything the user named keeps exactly the value it had. *)

(** ** Generic list facts

    Two pieces of ordinary list bookkeeping, needed below but saying
    nothing about the language itself.  They sit at the top level,
    outside every section, because they are reusable anywhere. *)

(** Reading a list back at each of its own positions rebuilds it.

    If [l] has length [n] then mapping "read position [i] of [l]"
    over the list [0, 1, ..., n - 1] returns [l] again.  The default
    value [d] is never actually used, since every index is a legal
    position.

    It is needed because the gadgets below take their variable names
    as a function of a bit index, while the fresh-name generator
    hands out a plain list.  This lemma says that wrapping a list
    into such a function and unrolling it again loses nothing. *)
Lemma map_nth_seq :
  ∀ (A : Type) (l : list A) (d : A),
  List.map (fun i => List.nth i l d) (List.seq 0 (List.length l)) = l.
Proof.
  intros A l d.
  induction l as [| a l ih]; cbn [List.length List.seq List.map List.nth];
  [reflexivity |].
  f_equal.
  rewrite <-List.seq_shift, List.map_map. cbn [List.nth]. exact ih.
Qed.

(** The same fact with the length supplied separately.

    Convenient at the use sites, where the length [n] is already
    fixed by the surrounding code and is known to be the length of
    [l] only through a hypothesis. *)
Lemma map_nth_seq_len :
  ∀ (A : Type) (l : list A) (d : A) (n : nat),
  List.length l = n ->
  List.map (fun i => List.nth i l d) (List.seq 0 n) = l.
Proof.
  intros A l d n hn; subst n; eapply map_nth_seq.
Qed.

(** Emitting three values per element, or concatenating three
    mapped lists, produces the same multiset.

    Walking a list [l] and emitting the triple [f i], [g i], [h i]
    for each element yields the elements of [List.map f l],
    [List.map g l] and [List.map h l] interleaved.  Sorting them
    back into three blocks is a permutation: the same elements in a
    different order.

    The range gadget names its per-bit variables three at a time,
    while the fresh-name generator produces three separate lists.
    Only membership matters for freshness, and membership survives a
    permutation, so this lemma is the bridge between the two
    views. *)
Lemma flat_map3_perm :
  ∀ (A B : Type) (f g h : A -> B) (l : list A),
  Permutation
    (List.flat_map (fun i => List.cons (f i) (List.cons (g i) (List.cons (h i) List.nil))) l)
    (List.app (List.map f l) (List.app (List.map g l) (List.map h l))).
Proof.
  intros A B f g h l.
  induction l as [| a l ih]; cbn [List.flat_map List.map List.app]; [constructor |].
  eapply perm_skip.
  eapply Permutation_trans; [eapply perm_skip; eapply perm_skip; exact ih |].
  eapply Permutation_trans; [eapply perm_skip; eapply Permutation_middle |].
  eapply Permutation_trans; [eapply Permutation_middle |].
  eapply Permutation_app_head. eapply perm_skip. eapply Permutation_middle.
Qed.

Section Surface.

  (** ** Parameters

      Everything below is parametric in the algebraic setting, so no
      particular curve or prime is baked in.

      - [F] is the field of scalars: the constants [zero] and [one],
        the four operations [add], [mul], [sub] and [div], negation
        [opp], multiplicative inverse [inv], and a procedure [Fdec]
        deciding equality of two scalars.
      - [G] is the group of points, written multiplicatively:
        identity [gid], inverse [ginv], product [gop], and
        exponentiation [gpow], where [gpow g x] is the point [g]
        raised to the scalar power [x].  [Gdec] decides equality of
        points.
      - [V] is the type of variable names, with a [VarType] instance
        [HV] supplying decidable equality and, more importantly, a
        generator of names guaranteed to be fresh.  Names stay
        abstract here; a real front end uses strings, and no proof
        below ever looks inside one. *)

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
    {HV : VarType V}.

  (** Shorthands for the name type: [vdecV] is decidable equality
      on names, taken from the [VarType] instance, and [veqb] is its
      boolean form.  The three infix symbols let exponentiation,
      multiplication and addition be written the usual way inside
      this section. *)
  #[local] Notation vdecV := (@VarType.vdec V HV).
  #[local] Notation veqb := (@veqb V vdecV).

  #[local] Infix "^" := gpow.
  #[local] Infix "*" := mul.
  #[local] Infix "+" := add.

  (** Shorthands for the core language of Dsl.v, already applied to
      this section's field and name types.  [pexprC] is a public
      scalar expression, [termC] one term of a linear equation,
      [equationC] one homogeneous equation, [stmtC] a whole core
      statement tree, [linC] a linear form in the sense of DslSubst.v
      (a public constant plus public multiples of private scalars),
      [fnatC] the embedding of the natural numbers into [F], and
      [overrideC] the update of a scalar environment at one name. *)
  #[local] Notation pexprC := (@pexpr F V).
  #[local] Notation termC := (@term F V).
  #[local] Notation equationC := (@equation F V).
  #[local] Notation stmtC := (@stmt F V).
  #[local] Notation linC := (@lin F V).
  #[local] Notation fnatC := (@fnat F zero one add).
  #[local] Notation overrideC := (@override F V vdecV).

  (** ** Syntax of the surface language

      Three syntactic classes: scalar expressions, point expressions
      and statements.  The grammar imposes nothing beyond this
      separation.  In particular it happily allows expressions the
      protocol cannot prove anything about; those are rejected later,
      by elaboration, rather than ruled out here. *)

  (** Scalar expressions: arithmetic over field elements.

      A scalar expression denotes one element of [F].  There are two
      kinds of variable and the difference matters everywhere below.

      - [XConst c] is a literal field element.
      - [XPub x] is a public scalar: a value the verifier knows too,
        read from the public environment.
      - [XPriv x] is a private scalar: part of the secret the prover
        claims to know, read from the witness.
      - [XAdd a b], [XMul a b] and [XNeg a] are sum, product and
        negation.

      Nothing here forbids multiplying two private scalars.  Such an
      expression has a perfectly good mathematical meaning;
      elaboration will simply refuse it, because a sigma protocol can
      prove linear relations between secrets and no more. *)
  Inductive sexpr : Type :=
  | XConst (c : F)
  | XPub (x : V)
  | XPriv (x : V)
  | XAdd (a b : sexpr)
  | XMul (a b : sexpr)
  | XNeg (a : sexpr).

  (** Point expressions: arithmetic in the group.

      A point expression denotes one element of [G].

      - [YOne] is the group identity.
      - [YPt P] is the point published under the name [P].
      - [YMul a b] is the group product, [YInv a] the group inverse.
      - [YPow P e] is the point named [P] raised to the power given
        by the scalar expression [e].

      An exponent may sit only on a named point, never on a compound
      point expression.  This costs nothing in practice, since any
      exponentiation the protocol can handle can be pushed down onto
      the bases, and it keeps flattening simple: all the terms coming
      from one [YPow] share a single base. *)
  Inductive gexpr : Type :=
  | YOne
  | YPt (P : V)
  | YMul (a b : gexpr)
  | YInv (a : gexpr)
  | YPow (P : V) (e : sexpr).

  (** Statements: what the prover claims.

      - [TEq a b] says the two point expressions denote the same
        group element.  This is the workhorse: a discrete-logarithm
        claim, the opening of a commitment, and a linear relation
        between secrets are all written this way.
      - [TNeq e] says the scalar expression [e] is not zero.
      - [TRange x u] says the private scalar [x] is the image in the
        field of one of the natural numbers below [u].
      - [TLet x e body] introduces a local name: throughout [body],
        the private scalar [x] stands for the value of [e].  It is a
        convenience for the writer, and elaboration removes it
        completely.
      - [TAnd a b] and [TOr a b] are conjunction and disjunction.
        Disjunction is the interesting one: the verifier learns that
        one side holds, never which.
      - [TThresh t l] says at least [t] of the statements in the list
        [l] hold, again without revealing which ones. *)
  Inductive sstmt : Type :=
  | TEq (a b : gexpr)
  | TNeq (e : sexpr)
  | TRange (x : V) (u : nat)
  | TLet (x : V) (e : sexpr) (body : sstmt)
  | TAnd (a b : sstmt)
  | TOr (a b : sstmt)
  | TThresh (t : nat) (l : list sstmt).

  (** ** Induction over statements

      The induction principle Rocq generates for [sstmt] is too weak.
      In the case for [TThresh t l] it offers no hypothesis at all
      about the statements inside [l], because they occur under the
      list type constructor.  [sstmt_ind'] is the strengthened
      principle: its threshold case receives [List.Forall P l], that
      is, the property [P] for every child.

      It is written by hand as a [Fixpoint] with an inner recursion
      walking the list, which is how Rocq is convinced that the
      recursive calls are on structurally smaller statements.  Every
      induction over [sstmt] in this file uses it. *)

  Section SstmtInduction.
    Variable P : sstmt -> Prop.
    Hypothesis HEq : ∀ a b, P (TEq a b).
    Hypothesis HNeq : ∀ e, P (TNeq e).
    Hypothesis HRange : ∀ x u, P (TRange x u).
    Hypothesis HLet : ∀ x e body, P body -> P (TLet x e body).
    Hypothesis HAnd : ∀ a b, P a -> P b -> P (TAnd a b).
    Hypothesis HOr : ∀ a b, P a -> P b -> P (TOr a b).
    Hypothesis HThresh : ∀ t l, List.Forall P l -> P (TThresh t l).

    Fixpoint sstmt_ind' (s : sstmt) : P s :=
      match s with
      | TEq a b => HEq a b
      | TNeq e => HNeq e
      | TRange x u => HRange x u
      | TLet x e body => HLet x e body (sstmt_ind' body)
      | TAnd a b => HAnd a b (sstmt_ind' a) (sstmt_ind' b)
      | TOr a b => HOr a b (sstmt_ind' a) (sstmt_ind' b)
      | TThresh t l =>
          HThresh t l
            ((fix go (l : list sstmt) : List.Forall P l :=
                match l with
                | List.nil => @List.Forall_nil _ P
                | List.cons s' l' =>
                    @List.Forall_cons _ P s' l' (sstmt_ind' s') (go l')
                end) l)
      end.
  End SstmtInduction.

  (** ** The names a piece of syntax mentions

      One collection function per syntactic class.  Each returns the
      list of every name occurring anywhere inside its argument, with
      duplicates, and without distinguishing point names from public
      or private scalars: only membership is ever used.

      They serve two purposes.  First they say what a piece of syntax
      depends on, which gives the locality lemmas further down:
      changing an environment away from these names cannot change a
      meaning.  Second, such a list is what a caller hands to [elab]
      as the initial set of used names, so that generated names avoid
      everything the user wrote. *)

  (** Every name occurring in a scalar expression, public and
      private alike. *)
  Fixpoint xnames (e : sexpr) : list V :=
    match e with
    | XConst _ => List.nil
    | XPub x => List.cons x List.nil
    | XPriv x => List.cons x List.nil
    | XAdd a b => List.app (xnames a) (xnames b)
    | XMul a b => List.app (xnames a) (xnames b)
    | XNeg a => xnames a
    end.

  (** Every name occurring in a point expression: the point names,
      together with the names inside any exponent. *)
  Fixpoint gnames (g : gexpr) : list V :=
    match g with
    | YOne => List.nil
    | YPt P => List.cons P List.nil
    | YMul a b => List.app (gnames a) (gnames b)
    | YInv a => gnames a
    | YPow P e => List.cons P (xnames e)
    end.

  (** Every name occurring in a statement.

      For [TLet x e body] the bound name [x] is included, even though
      it is local and will disappear.  That is the conservative
      choice: a generated name then avoids [x] as well, so no capture
      is possible.  The threshold case is an inlined recursion over
      the list, for the same termination reason that [sstmt_ind'] is
      written by hand. *)
  Fixpoint snames (s : sstmt) : list V :=
    match s with
    | TEq a b => List.app (gnames a) (gnames b)
    | TNeq e => xnames e
    | TRange x _ => List.cons x List.nil
    | TLet x e body => List.cons x (List.app (xnames e) (snames body))
    | TAnd a b => List.app (snames a) (snames b)
    | TOr a b => List.app (snames a) (snames b)
    | TThresh _ l =>
        (fix go (l : list sstmt) : list V :=
           match l with
           | List.nil => List.nil
           | List.cons s' l' => List.app (snames s') (go l')
           end) l
    end.

  (** The names of every statement in a list, concatenated.  This
      is the threshold case of [snames], packaged as a function in
      its own right so that lemmas can be stated about it. *)
  Definition snames_of_list (l : list sstmt) : list V :=
    List.flat_map snames l.

  (** The inlined recursion inside [snames] really is
      [snames_of_list].

      A statement of the obvious, proved once by induction on the
      list, so that later proofs can rewrite with it instead of
      unfolding a fixpoint sitting under a constructor. *)
  Lemma snames_thresh :
    ∀ (t : nat) (l : list sstmt), snames (TThresh t l) = snames_of_list l.
  Proof.
    intros t l; unfold snames_of_list.
    induction l as [| s l ih]; [reflexivity |].
    cbn in ih |- *. rewrite ih. reflexivity.
  Qed.

  (** ** What the surface language means

      The meaning of a piece of syntax is fixed by three
      environments, an environment being nothing more than a function
      from names to values.

      - [penv] maps names to public scalars.  It is fixed for the
        whole section, since the public data is the same for prover
        and verifier.
      - [genv] maps names to group elements: the published points.
      - [wenv] maps names to private scalars.  This is the witness,
        the secret the prover claims to know.

      A witness satisfies a statement when the statement's
      denotation, a proposition built from these environments,
      holds. *)

  Section Sem.

    (** The public scalar environment, fixed throughout. *)
    Variable penv : V -> F.

    (** Evaluation of a core public scalar expression under [penv],
        from Dsl.v. *)
    #[local] Notation pevalC := (@peval F add mul opp V penv).

    (** The value of a scalar expression.

        [sdenote wenv e] reads public names from [penv], which the
        section fixes, and private names from the witness [wenv].
        Everything else is plain field arithmetic. *)
    Fixpoint sdenote (wenv : V -> F) (e : sexpr) : F :=
      match e with
      | XConst c => c
      | XPub x => penv x
      | XPriv x => wenv x
      | XAdd a b => sdenote wenv a + sdenote wenv b
      | XMul a b => sdenote wenv a * sdenote wenv b
      | XNeg a => opp (sdenote wenv a)
      end.

    (** The value of a point expression.

        [gdenote genv wenv g] reads point names from [genv].  The
        witness is consulted only at [YPow], whose exponent is a
        scalar expression and may mention private scalars. *)
    Fixpoint gdenote (genv : V -> G) (wenv : V -> F) (g : gexpr) : G :=
      match g with
      | YOne => gid
      | YPt P => genv P
      | YMul a b => gop (gdenote genv wenv a) (gdenote genv wenv b)
      | YInv a => ginv (gdenote genv wenv a)
      | YPow P e => (genv P) ^ (sdenote wenv e)
      end.

    (** What it means for a witness to satisfy a statement.

        Most cases can be read straight off the syntax.  Three
        deserve a word.

        [TRange x u] holds when the witness value of [x] is [fnatC k]
        for some natural number [k] below [u], that is, when it is
        the image in the field of an integer in the intended range.

        [TLet x e body] holds when [body] holds under the witness
        updated at [x] to the value of [e].  Any earlier value of [x]
        is shadowed, inside [body] only.

        [TThresh t l] holds when there is a list of booleans [bs],
        one flag per child, with at least [t] flags set, such that
        every flagged child holds.  Unflagged children are required
        to hold nothing.  The inner recursion is inlined for
        termination; [sflagged] just below is the same thing written
        as a standalone function. *)
    Fixpoint sstmt_denote (genv : V -> G) (wenv : V -> F) (s : sstmt) : Prop :=
      match s with
      | TEq a b => gdenote genv wenv a = gdenote genv wenv b
      | TNeq e => sdenote wenv e <> zero
      | TRange x u => ∃ k : nat, (k < u)%nat ∧ wenv x = fnatC k
      | TLet x e body =>
          sstmt_denote genv (overrideC wenv x (sdenote wenv e)) body
      | TAnd a b => sstmt_denote genv wenv a ∧ sstmt_denote genv wenv b
      | TOr a b => sstmt_denote genv wenv a ∨ sstmt_denote genv wenv b
      | TThresh t l =>
          ∃ bs : list bool,
            List.length bs = List.length l ∧
            (t <= count_true bs)%nat ∧
            (fix flagged (l : list sstmt) (bs : list bool) : Prop :=
               match l, bs with
               | List.cons s' l', List.cons b bs' =>
                   (if b then sstmt_denote genv wenv s' else True) ∧
                   flagged l' bs'
               | _, _ => True
               end) l bs
      end.

    (** "Every flagged statement of [l] holds", as a function.

        [sflagged genv wenv l bs] pairs each statement of [l] with
        the flag at the same position of [bs] and demands the
        statement only where the flag is [true].  If the two lists
        have different lengths the surplus is ignored; wherever it is
        used the lengths agree. *)
    Fixpoint sflagged (genv : V -> G) (wenv : V -> F) (l : list sstmt) (bs : list bool)
      : Prop :=
      match l, bs with
      | List.cons s' l', List.cons b bs' =>
          (if b then sstmt_denote genv wenv s' else True) ∧ sflagged genv wenv l' bs'
      | _, _ => True
      end.

    (** The threshold case of [sstmt_denote] is exactly the
        [sflagged] formulation.

        The two sides say the same thing; the proof merely
        re-associates the inlined fixpoint into calls of [sflagged],
        by induction on the two lists in step.  Having the
        equivalence available lets later proofs about thresholds work
        with a named function instead of a fixpoint frozen under a
        constructor. *)
    Lemma sstmt_denote_thresh :
      ∀ (genv : V -> G) (wenv : V -> F) (t : nat) (l : list sstmt),
      sstmt_denote genv wenv (TThresh t l) <->
      ∃ bs : list bool,
        List.length bs = List.length l ∧
        (t <= count_true bs)%nat ∧ sflagged genv wenv l bs.
    Proof.
      intros genv wenv t l; cbn.
      split; intros (bs & ha & hb & hc); exists bs; repeat split; try assumption.
      + clear ha hb. revert bs hc.
        induction l as [|s l ih]; intros [|b bs] hc; cbn in hc |- *; try exact I.
        destruct hc as (hc & hd); split; [exact hc | eapply ih; exact hd].
      + clear ha hb. revert bs hc.
        induction l as [|s l ih]; intros [|b bs] hc; cbn in hc |- *; try exact I.
        destruct hc as (hc & hd); split; [exact hc | eapply ih; exact hd].
    Qed.

    (** ** Linear forms

        A linear form, the type [linC] of DslSubst.v, is a pair: a
        public constant term, and a list of pairs "public
        coefficient, private name".  It denotes the constant plus the
        sum of each coefficient times the witness value of its name.

        Linear forms are the normal form of everything the protocol
        can prove about private scalars.  The five constructions
        below build them, and [lin_of] tries to read a whole scalar
        expression as one. *)

    (** The constant form: one public scalar expression, no private
        part at all. *)
    Definition lin_const (c : pexprC) : linC := (c, List.nil).
    (** A bare private scalar [x], as the form with constant zero and
        the single coefficient one on [x]. *)
    Definition lin_var (x : V) : linC :=
      (PConst zero, List.cons (PConst one, x) List.nil).
    (** The sum of two forms: add the constants, concatenate the
        private parts.  Repeated names are not collected, and need
        not be: the denotation is the same sum either way. *)
    Definition lin_add (a b : linC) : linC :=
      (PAdd (fst a) (fst b), List.app (snd a) (snd b)).
    (** The negation of a form: negate the constant and every
        coefficient. *)
    Definition lin_neg (a : linC) : linC :=
      (POpp (fst a), List.map (fun cy => (POpp (fst cy), snd cy)) (snd a)).
    (** A form multiplied by the public scalar expression [k]:
        multiply the constant and every coefficient by [k].  The
        result is still linear in the private scalars, which is
        precisely why scaling by a public value is allowed while
        scaling by a private one is not. *)
    Definition lin_scale (k : pexprC) (a : linC) : linC :=
      (PMul k (fst a), List.map (fun cy => (PMul k (fst cy), snd cy)) (snd a)).

    (** A scalar expression read as a linear form in the private
        scalars, or [None] when it is not linear.

        Constants and public variables become constant forms, a
        private variable becomes the single-variable form, and sums
        and negations map onto [lin_add] and [lin_neg].

        The product is the only case that can fail.  A product is
        linear only when at least one factor has an empty private
        part, that is, is a purely public quantity; the other factor
        is then scaled by it.  If both factors genuinely depend on
        private scalars their product is quadratic, and the function
        returns [None].

        This is where the austerity of the core reaches the user.  A
        sigma protocol proves knowledge of exponents satisfying
        linear relations, so an exponent multiplying two secrets
        cannot be compiled at all. *)
    Fixpoint lin_of (e : sexpr) : option linC :=
      match e with
      | XConst c => Some (lin_const (PConst c))
      | XPub x => Some (lin_const (PVar x))
      | XPriv x => Some (lin_var x)
      | XAdd a b =>
          match lin_of a, lin_of b with
          | Some la, Some lb => Some (lin_add la lb)
          | _, _ => None
          end
      | XNeg a => option_map lin_neg (lin_of a)
      | XMul a b =>
          match lin_of a, lin_of b with
          | Some la, Some lb =>
              match snd la with
              | List.nil => Some (lin_scale (fst la) lb)
              | _ =>
                  match snd lb with
                  | List.nil => Some (lin_scale (fst lb) la)
                  | _ => None
                  end
              end
          | _, _ => None
          end
      end.

    (** The value of a linear form under a witness, from DslSubst.v:
        the constant, plus the sum of each coefficient times the
        witness value of its name. *)
    #[local] Notation lin_denoteC := (@lin_denote F zero add mul opp V penv).

    (** The private names a linear form mentions. *)
    Definition lin_vars (l : linC) : list V := List.map snd (snd l).

    (** ** Flattening a point expression

        A core equation carries two lists.  [eq_rhs] holds the
        private terms, each of the shape "base raised to a public
        coefficient times a private scalar".  [eq_off] holds the
        public offsets, each of the shape "base raised to a public
        scalar expression".  The equation asserts that the product of
        all of them is the group identity.

        Flattening a point expression means producing exactly those
        two lists.  The functions below do it constructor by
        constructor. *)

    (** Invert a list of private terms by negating every
        coefficient.

        Negating an exponent is the same as inverting the resulting
        group element, so this is how a [YInv] is pushed inwards. *)
    Definition neg_terms (ts : list termC) : list termC :=
      List.map (fun t => mkterm (POpp (t_coeff t)) (t_var t) (t_base t)) ts.

    (** The same for a list of public offsets: negate each public
        exponent. *)
    Definition neg_offs (os : list (pexprC * V)) : list (pexprC * V) :=
      List.map (fun o => (POpp (fst o), snd o)) os.

    (** The private part of a linear form [l] as terms that all
        share the base [P].

        Each pair "coefficient, name" of [l] becomes the term [P]
        raised to that coefficient times that name.  The constant
        part of [l] is deliberately left out here: it is a public
        offset, and [elab_g] adds it separately. *)
    Definition lin_terms (P : V) (l : linC) : list termC :=
      List.map (fun cy => mkterm (fst cy) (snd cy) P) (snd l).

    (** The flattened form of a point expression: a list of private
        terms paired with a list of public offsets.  To read it as a
        group element, multiply everything together. *)
    Definition gflat : Type := (list termC * list (pexprC * V))%type.

    (** Flatten a point expression, or fail.

        - [YOne] flattens to nothing at all, since the empty product
          is the identity.
        - [YPt P] gives one public offset, namely [P] to the power
          one.
        - [YMul a b] concatenates the two flattenings, because the
          denotation is a product either way.
        - [YInv a] negates every exponent in both lists.
        - [YPow P e] asks [lin_of] to read the exponent [e] as a
          linear form.  The private part of that form becomes terms
          over the base [P], and its constant part becomes the single
          public offset [P] raised to that constant.

        The only source of failure is an exponent that is not
        linear. *)
    Fixpoint elab_g (g : gexpr) : option gflat :=
      match g with
      | YOne => Some (List.nil, List.nil)
      | YPt P => Some (List.nil, List.cons (PConst one, P) List.nil)
      | YMul a b =>
          match elab_g a, elab_g b with
          | Some pa, Some pb =>
              Some (List.app (fst pa) (fst pb), List.app (snd pa) (snd pb))
          | _, _ => None
          end
      | YInv a =>
          option_map (fun p => (neg_terms (fst p), neg_offs (snd p))) (elab_g a)
      | YPow P e =>
          option_map (fun l => (lin_terms P l, List.cons (fst l, P) List.nil))
            (lin_of e)
      end.

    (** Turn an equality of two flattened point expressions into one
        homogeneous core equation.

        The core has no notion of an equation with two sides.  Every
        equation reads "this product of powers equals the group
        identity".  So both sides are brought together: the left side
        is kept as it is, the right side is inverted by negating its
        exponents, and the two are concatenated.  Since the group is
        commutative, the left side times the inverse of the right
        side is the identity exactly when the two sides are equal.
        That equivalence is [elab_eq_denote] below. *)
    Definition elab_eq (pa pb : gflat) : equationC :=
      mkeq (List.app (fst pa) (neg_terms (fst pb)))
           (List.app (snd pa) (neg_offs (snd pb))).

    (** ** Elaborating statements into the core *)

    (** The two base points of the Pedersen commitments the gadgets
        use.

        A Pedersen commitment to a value [v] with randomness [r] is
        the group element
        [gop (gpow (genv An) v) (gpow (genv Bn) r)].  It hides [v],
        and binds the committer to [v], as long as nobody knows a
        scalar [d] with [genv An = gpow (genv Bn) d].  The two names
        are fixed here for the whole elaboration, so every gadget
        commits against the same pair.  Nothing in this file assumes
        the pair is honest; instead, the soundness theorem carries
        the possibility that it is not. *)
    Variable An Bn : V.

    (** A name used only as the default value of a list lookup that
        never actually runs off the end.  The gadgets take their
        per-bit names as functions of an index; wrapping a list into
        such a function needs some value for out-of-range indices,
        and this is it. *)
    Definition default_name : V := vfresh List.nil.

    (** The range gadget, with all its auxiliary names taken fresh.

        Proving that a private scalar [x] lies below [u] is done by
        decomposing [x] into bits.  The gadget of DslRange.v needs
        four families of names, one member of each per bit: the bit
        itself, the randomness of the bit's commitment, an auxiliary
        scalar that forces the bit to equal its own square, and the
        name under which the bit's commitment point is published.

        [elab_range used x u] asks the generator of VarType.v for
        four blocks of fresh names, each block avoiding [used]
        together with every block drawn before it, so the four
        families are fresh and pairwise disjoint.  It returns the
        core statement along with the extended used-name list. *)
    Definition elab_range (used : list V) (x : V) (u : nat) : stmtC * list V :=
      let n := List.length (range_weights u) in
      let fb := fresh_list used n in
      let fr := fresh_list (List.app used fb) n in
      let fs := fresh_list (List.app used (List.app fb fr)) n in
      let fC := fresh_list (List.app used (List.app fb (List.app fr fs))) n in
      (@range_stmt F zero one add opp V
         (fun i => List.nth i fb default_name)
         (fun i => List.nth i fr default_name)
         (fun i => List.nth i fs default_name)
         (fun i => List.nth i fC default_name) An Bn x u,
       List.app used (List.app fb (List.app fr (List.app fs fC)))).

    (** Elaboration: a surface statement becomes a core statement.

        [elab used s] returns the core statement together with the
        new list of used names, or [None] when [s] cannot be
        compiled.  The argument [used] is the list of names already
        spoken for: everything the user wrote, the two Pedersen
        bases, and every name generated earlier in the walk.
        Threading it through the recursion is what guarantees that no
        two gadgets ever choose the same auxiliary name.  Were that
        to happen, two unrelated secrets would silently be identified
        and both theorems below would fail.

        Case by case:

        - [TEq a b] flattens both sides and emits the single
          homogeneous equation built by [elab_eq].  No new name is
          needed, so [used] comes back unchanged.
        - [TNeq e] reads [e] as a linear form and additionally
          insists that the form mention exactly one private scalar,
          since the gadget of DslNeq.v is stated for "coefficient
          times [x] plus offset".  Four fresh names are drawn: the
          commitment point, and the gadget's three auxiliary scalars.
        - [TRange x u] is rejected for [u] below two, where the claim
          degenerates, and otherwise handed to [elab_range].
        - [TLet x e body] elaborates the body first and then
          substitutes the linear form of [e] for [x] throughout,
          using DslSubst.v.  The definition must not be circular,
          which is what the [List.existsb] test rules out: if [x]
          occurred inside its own defining form, substituting would
          not remove it.
        - [TAnd] and [TOr] elaborate the two sides in sequence,
          feeding the used-name list of the first into the second.
        - [TThresh t l] does the same along the list.  Its recursion
          is inlined for termination; [elab_list] below is the same
          function written separately. *)
    Fixpoint elab (used : list V) (s : sstmt) : option (stmtC * list V) :=
      match s with
      | TEq a b =>
          match elab_g a, elab_g b with
          | Some pa, Some pb =>
              Some (SEqs (List.cons (elab_eq pa pb) List.nil), used)
          | _, _ => None
          end
      | TNeq e =>
          match lin_of e with
          | Some (off, List.cons (coeff, x) List.nil) =>
              match fresh_list used 4 with
              | List.cons Cn (List.cons j (List.cons sn (List.cons r List.nil))) =>
                  Some (@neq_stmt F one V Cn An Bn x j sn r coeff off,
                        List.app used
                          (List.cons Cn (List.cons j (List.cons sn (List.cons r List.nil)))))
              | _ => None
              end
          | _ => None
          end
      | TRange x u =>
          if (2 <=? u)%nat then Some (elab_range used x u) else None
      | TLet x e body =>
          match lin_of e, elab used body with
          | Some l, Some (c, used') =>
              if List.existsb (veqb x) (lin_vars l) then None
              else Some (@subst_stmt F V vdecV x l c, used')
          | _, _ => None
          end
      | TAnd a b =>
          match elab used a with
          | Some (ca, u1) =>
              match elab u1 b with
              | Some (cb, u2) => Some (SAnd ca cb, u2)
              | None => None
              end
          | None => None
          end
      | TOr a b =>
          match elab used a with
          | Some (ca, u1) =>
              match elab u1 b with
              | Some (cb, u2) => Some (SOr ca cb, u2)
              | None => None
              end
          | None => None
          end
      | TThresh t l =>
          match
            (fix go (used : list V) (l : list sstmt) : option (list stmtC * list V) :=
               match l with
               | List.nil => Some (List.nil, used)
               | List.cons s' l' =>
                   match elab used s' with
                   | Some (c, u1) =>
                       match go u1 l' with
                       | Some (cs, u2) => Some (List.cons c cs, u2)
                       | None => None
                       end
                   | None => None
                   end
               end) used l
          with
          | Some (cs, used') => Some (SThresh t cs, used')
          | None => None
          end
      end.

    (** Elaborate a list of statements in sequence, threading the
        used-name list from each one into the next.

        This is literally the inner recursion of the [TThresh] case
        of [elab], written as a top-level fixpoint so that lemmas can
        be stated and proved about it. *)
    Fixpoint elab_list (used : list V) (l : list sstmt) : option (list stmtC * list V) :=
      match l with
      | List.nil => Some (List.nil, used)
      | List.cons s' l' =>
          match elab used s' with
          | Some (c, u1) =>
              match elab_list u1 l' with
              | Some (cs, u2) => Some (List.cons c cs, u2)
              | None => None
              end
          | None => None
          end
      end.

    (** The threshold case of [elab] is exactly [elab_list].

        True by computation, which is why the proof is
        [reflexivity].  It is stated as a lemma so that proofs can
        rewrite with it rather than unfold [elab] underneath a
        constructor. *)
    Lemma elab_thresh :
      ∀ (used : list V) (t : nat) (l : list sstmt),
      elab used (TThresh t l) =
      match elab_list used l with
      | Some (cs, used') => Some (SThresh t cs, used')
      | None => None
      end.
    Proof.
      intros; cbn; reflexivity.
    Qed.

    (** The commitment setup is broken.

        This asserts one of two things about the published points:
        the first base is the group identity, or someone can exhibit
        a scalar [d] with [genv An = gpow (genv Bn) d], that is, a
        discrete logarithm of the first base to the second.

        Either destroys the commitment scheme, and neither can be
        produced efficiently when the bases were generated honestly.
        It appears here because it is the escape clause of both
        gadgets: extracting from a prover yields either the claimed
        secret or exactly this.  That is the usual shape of
        sigma-protocol soundness, and [elab_sound] propagates it
        unchanged to the surface language. *)
    Definition degenerate (genv : V -> G) : Prop :=
      genv An = gid ∨ ∃ d : F, genv An = (genv Bn) ^ d.

    Section Proofs.

      (** The proofs need more than the bare operations, they need the
          axioms.  [Hvec] states that [F] is a field, that [G] is a
          commutative group, and that [gpow] is a scalar
          multiplication connecting the two, which makes identities
          such as "exponents add when powers of one base are
          multiplied" available.  The [Add Field] declaration lets
          the [field] tactic discharge routine identities in [F]. *)
      Context
        {Hvec : @vector_space F (@eq F) zero one add mul sub
          div opp inv G (@eq G) gid ginv gop gpow}.
      Add Field field : (@field_theory_for_stdlib_tactic F
        eq zero one opp add mul sub inv div vector_space_field).

      (** Shorthands for the core semantics of Dsl.v.
          [terms_foldC] multiplies out a list of private terms,
          [off_foldC] a list of public offsets, [eq_denoteC] states
          that one homogeneous equation holds, and [stmt_denoteC]
          that a whole core statement holds. *)
      #[local] Notation terms_foldC := (@terms_fold F add mul opp G gid gop gpow V).
      #[local] Notation off_foldC := (@off_fold F add mul opp G gid gop gpow V).
      #[local] Notation eq_denoteC := (@eq_denote F add mul opp G gid gop gpow V).
      #[local] Notation stmt_denoteC := (@stmt_denote F add mul opp G gid gop gpow V).

      (** ** Linear forms compute what they should

          The five constructions of linear forms were defined
          syntactically.  The lemmas here say that each denotes the
          operation it is named after, and together they yield
          [lin_of_denote]: a linear form extracted from a scalar
          expression has the same value as that expression. *)

      (** The private part of a linear form is summed by a fold, and
          that fold distributes over concatenation.

          This is the arithmetic behind [lin_add]: laying two lists
          of "coefficient times variable" side by side adds their
          sums. *)
      Lemma lin_fold_app :
        ∀ (wenv : V -> F) (l₁ l₂ : list (pexprC * V)),
        List.fold_right (fun cy acc => pevalC (fst cy) * wenv (snd cy) + acc)
          zero (List.app l₁ l₂) =
        List.fold_right (fun cy acc => pevalC (fst cy) * wenv (snd cy) + acc) zero l₁ +
        List.fold_right (fun cy acc => pevalC (fst cy) * wenv (snd cy) + acc) zero l₂.
      Proof.
        intros wenv l₁ l₂.
        induction l₁ as [| cy l₁ ih]; cbn [List.app List.fold_right].
        + field.
        + rewrite ih. field.
      Qed.

      (** [lin_add] denotes addition. *)
      Lemma lin_add_denote :
        ∀ (wenv : V -> F) (a b : linC),
        lin_denoteC wenv (lin_add a b) = lin_denoteC wenv a + lin_denoteC wenv b.
      Proof.
        intros wenv [ca la] [cb lb].
        unfold lin_denote, lin_add; cbn [fst snd peval].
        rewrite lin_fold_app. field.
      Qed.

      (** [lin_neg] denotes negation.  The inner induction shows that
          negating every coefficient negates the whole sum. *)
      Lemma lin_neg_denote :
        ∀ (wenv : V -> F) (a : linC),
        lin_denoteC wenv (lin_neg a) = opp (lin_denoteC wenv a).
      Proof.
        intros wenv [ca la].
        unfold lin_denote, lin_neg; cbn [fst snd peval].
        assert (hf : List.fold_right (fun cy acc => pevalC (fst cy) * wenv (snd cy) + acc) zero
            (List.map (fun cy => (POpp (fst cy), snd cy)) la) =
          opp (List.fold_right (fun cy acc => pevalC (fst cy) * wenv (snd cy) + acc) zero la)).
        { induction la as [| cy la ih]; cbn [List.map List.fold_right fst snd peval].
          + field.
          + rewrite ih. field. }
        rewrite hf. field.
      Qed.

      (** [lin_scale k a] denotes the public value of [k] times the
          value of [a].  The inner induction is distributivity of
          multiplication over the sum. *)
      Lemma lin_scale_denote :
        ∀ (wenv : V -> F) (k : pexprC) (a : linC),
        lin_denoteC wenv (lin_scale k a) = pevalC k * lin_denoteC wenv a.
      Proof.
        intros wenv k [ca la].
        unfold lin_denote, lin_scale; cbn [fst snd peval].
        assert (hf : List.fold_right (fun cy acc => pevalC (fst cy) * wenv (snd cy) + acc) zero
            (List.map (fun cy => (PMul k (fst cy), snd cy)) la) =
          pevalC k * (List.fold_right (fun cy acc => pevalC (fst cy) * wenv (snd cy) + acc) zero la)).
        { induction la as [| cy la ih]; cbn [List.map List.fold_right fst snd peval].
          + field.
          + rewrite ih. field. }
        rewrite hf. field.
      Qed.

      (** A scalar expression and the linear form extracted from it
          have the same value.

          Proved by induction on the expression, each case closed by
          the matching lemma above.  The product case splits on which
          factor turned out to be purely public, and the scaling
          lemma applies in both branches.

          This is the correctness statement for [lin_of], and it is
          what makes flattening meaning-preserving. *)
      Lemma lin_of_denote :
        ∀ (wenv : V -> F) (e : sexpr) (l : linC),
        lin_of e = Some l -> lin_denoteC wenv l = sdenote wenv e.
      Proof.
        intros wenv e.
        induction e as [c | x | x | a iha b ihb | a iha b ihb | a iha]; intros l he;
        cbn [lin_of] in he; cbn [sdenote].
        + inversion he; subst. unfold lin_denote, lin_const; cbn. field.
        + inversion he; subst. unfold lin_denote, lin_const; cbn. field.
        + inversion he; subst. unfold lin_denote, lin_var; cbn. field.
        + destruct (lin_of a) as [la |]; [| congruence].
          destruct (lin_of b) as [lb |]; [| congruence].
          inversion he; subst.
          rewrite lin_add_denote, (iha _ eq_refl), (ihb _ eq_refl). reflexivity.
        + destruct (lin_of a) as [[ca la] |]; [| congruence].
          destruct (lin_of b) as [[cb lb] |]; [| congruence].
          cbn [fst snd] in he.
          destruct la as [| ? ?].
          - inversion he; subst. rewrite lin_scale_denote, (ihb _ eq_refl).
            rewrite <-(iha _ eq_refl). unfold lin_denote; cbn. field.
          - destruct lb as [| ? ?]; [| congruence].
            inversion he; subst. rewrite lin_scale_denote, (iha _ eq_refl).
            rewrite <-(ihb _ eq_refl). unfold lin_denote; cbn. field.
        + destruct (lin_of a) as [la |]; cbn [option_map] in he; [| congruence].
          inversion he; subst. rewrite lin_neg_denote, (iha _ eq_refl). reflexivity.
      Qed.

      (** [lin_of] invents no names.

          Every private name appearing in the extracted form already
          appears in the expression.  This matters for freshness: a
          name chosen to avoid everything in [xnames e] thereby
          avoids everything the form mentions. *)
      Lemma lin_of_vars :
        ∀ (e : sexpr) (l : linC),
        lin_of e = Some l -> List.incl (lin_vars l) (xnames e).
      Proof.
        intros e.
        induction e as [c | x | x | a iha b ihb | a iha b ihb | a iha]; intros l he;
        cbn [lin_of] in he.
        + inversion he; subst. unfold lin_vars, lin_const; cbn. eapply List.incl_nil_l.
        + inversion he; subst. unfold lin_vars, lin_const; cbn. eapply List.incl_nil_l.
        + inversion he; subst. unfold lin_vars, lin_var; cbn. eapply List.incl_refl.
        + destruct (lin_of a) as [la |]; [| congruence].
          destruct (lin_of b) as [lb |]; [| congruence].
          inversion he; subst. unfold lin_vars, lin_add; cbn [fst snd xnames].
          rewrite List.map_app.
          eapply List.incl_app_app; [eapply iha | eapply ihb]; reflexivity.
        + destruct (lin_of a) as [[ca la] |]; [| congruence].
          destruct (lin_of b) as [[cb lb] |]; [| congruence].
          cbn [fst snd] in he.
          destruct la as [| ? ?].
          - inversion he; subst. unfold lin_vars, lin_scale; cbn [fst snd xnames].
            rewrite List.map_map; cbn [snd]. eapply List.incl_appr. eapply (ihb _ eq_refl).
          - destruct lb as [| ? ?]; [| congruence].
            inversion he; subst. unfold lin_vars, lin_scale; cbn [fst snd xnames].
            rewrite List.map_map; cbn [snd]. eapply List.incl_appl. eapply (iha _ eq_refl).
        + destruct (lin_of a) as [[ca la] |]; cbn [option_map] in he; [| congruence].
          inversion he; subst. unfold lin_vars, lin_neg; cbn [fst snd xnames].
          rewrite List.map_map; cbn [snd]. eapply (iha _ eq_refl).
      Qed.

      (** The value of a linear form depends on the witness only at
          the names the form mentions.

          Two witnesses agreeing on [lin_vars l] give [l] the same
          value.  Used whenever an environment is extended at fresh
          names and one must argue that old values did not move. *)
      Lemma lin_denote_ext :
        ∀ (w₁ w₂ : V -> F) (l : linC),
        (∀ x, List.In x (lin_vars l) -> w₁ x = w₂ x) ->
        lin_denoteC w₁ l = lin_denoteC w₂ l.
      Proof.
        intros w₁ w₂ [c l] h.
        unfold lin_denote, lin_vars in h |- *; cbn [fst snd] in h |- *.
        f_equal.
        induction l as [| cy l ih]; cbn [List.fold_right List.map] in h |- *; [reflexivity |].
        rewrite ih, (h (snd cy)); [reflexivity | left; reflexivity |].
        intros x hx; eapply h; right; exact hx.
      Qed.

      (** ** Flattening preserves meaning

          These lemmas build up to [elab_g_denote], which says that
          multiplying out a flattened point expression gives back the
          point the expression denoted, and to [elab_eq_denote],
          which says that the single homogeneous equation produced by
          [elab_eq] holds exactly when the two original sides are
          equal. *)

      (** Raising to a negated exponent is the same as inverting the
          power.  The group law read backwards, from the
          vector-space axioms. *)
      Lemma gpow_opp :
        ∀ (g : G) (x : F), g ^ (opp x) = ginv (g ^ x).
      Proof.
        intros g x.
        rewrite connection_between_vopp_and_fopp. reflexivity.
      Qed.

      (** The inverse of a product is the product of the inverses.
          True because the group is commutative; in a general group
          the order of the factors would flip. *)
      Lemma ginv_gop :
        ∀ (a b : G), ginv (gop a b) = gop (ginv a) (ginv b).
      Proof.
        intros a b.
        rewrite group_inv_flip, commutative. reflexivity.
      Qed.

      (** Negating every coefficient of a list of terms inverts the
          group element that list multiplies out to. *)
      Lemma terms_fold_neg :
        ∀ (genv : V -> G) (wenv : V -> F) (ts : list termC),
        terms_foldC genv penv wenv (neg_terms ts) = ginv (terms_foldC genv penv wenv ts).
      Proof.
        intros genv wenv ts.
        induction ts as [| t ts ih]; unfold neg_terms; cbn [List.map];
        unfold terms_fold; cbn [List.fold_right].
        + rewrite group_inv_id. reflexivity.
        + unfold neg_terms, terms_fold in ih. rewrite ih, ginv_gop.
          unfold term_denote; cbn [t_coeff t_var t_base peval].
          rewrite <-gpow_opp.
          assert (h : opp (pevalC (t_coeff t)) * wenv (t_var t) =
            opp (pevalC (t_coeff t) * wenv (t_var t))). { field. }
          rewrite h. reflexivity.
      Qed.

      (** The same for a list of public offsets. *)
      Lemma off_fold_neg :
        ∀ (genv : V -> G) (os : list (pexprC * V)),
        off_foldC genv penv (neg_offs os) = ginv (off_foldC genv penv os).
      Proof.
        intros genv os.
        induction os as [| o os ih]; unfold neg_offs; cbn [List.map];
        unfold off_fold; cbn [List.fold_right].
        + rewrite group_inv_id. reflexivity.
        + unfold neg_offs, off_fold in ih. rewrite ih, ginv_gop.
          unfold off_denote; cbn [fst snd peval].
          rewrite <-gpow_opp. reflexivity.
      Qed.

      (** A linear form over a single base multiplies out correctly.

          The terms built by [lin_terms P l] carry the private part
          of [l] as exponents on [P]; multiplying in [P] raised to
          the constant part of [l] gives [P] raised to the whole
          value of [l].  The reason is just that exponents add when
          powers of the same base are multiplied. *)
      Lemma lin_terms_denote :
        ∀ (genv : V -> G) (wenv : V -> F) (P : V) (l : linC),
        gop (terms_foldC genv penv wenv (lin_terms P l)) ((genv P) ^ (pevalC (fst l))) =
        (genv P) ^ (lin_denoteC wenv l).
      Proof.
        intros genv wenv P [c l].
        unfold lin_denote, lin_terms; cbn [fst snd].
        rewrite smul_distributive_fadd, commutative. f_equal.
        induction l as [| cy l ih]; cbn [List.map List.fold_right];
        unfold terms_fold; cbn [List.fold_right].
        + rewrite field_zero. reflexivity.
        + unfold terms_fold in ih. rewrite ih, smul_distributive_fadd.
          unfold term_denote; cbn [t_coeff t_var t_base]. reflexivity.
      Qed.

      (** Flattening a point expression preserves its value.

          If [elab_g g] succeeds with the pair [p], then multiplying
          the private terms of [p] by the public offsets of [p] gives
          exactly [gdenote genv wenv g].

          By induction on [g].  The identity case is the empty
          product; the product case regroups four folded blocks into
          two, which the commutativity of the group permits; the
          inverse case is the two negation lemmas; the power case is
          [lin_terms_denote] together with [lin_of_denote]. *)
      Lemma elab_g_denote :
        ∀ (genv : V -> G) (wenv : V -> F) (g : gexpr) (p : gflat),
        elab_g g = Some p ->
        gop (terms_foldC genv penv wenv (fst p)) (off_foldC genv penv (snd p)) =
        gdenote genv wenv g.
      Proof.
        intros genv wenv g.
        induction g as [| P | a iha b ihb | a iha | P e]; intros p hp;
        cbn [elab_g] in hp; cbn [gdenote].
        + inversion hp; subst; cbn [fst snd]. unfold terms_fold, off_fold; cbn.
          rewrite left_identity. reflexivity.
        + inversion hp; subst; cbn [fst snd]. unfold terms_fold, off_fold; cbn.
          unfold off_denote; cbn.
          rewrite left_identity, right_identity, field_one. reflexivity.
        + destruct (elab_g a) as [pa |]; [| congruence].
          destruct (elab_g b) as [pb |]; [| congruence].
          inversion hp; subst; cbn [fst snd].
          rewrite (terms_fold_app genv penv (Hvec := Hvec)),
            (off_fold_app genv penv (Hvec := Hvec)).
          rewrite <-(iha pa eq_refl), <-(ihb pb eq_refl).
          rewrite <-!associative. f_equal.
          rewrite !associative. f_equal. eapply commutative.
        + destruct (elab_g a) as [pa |]; cbn [option_map] in hp; [| congruence].
          inversion hp; subst; cbn [fst snd].
          rewrite terms_fold_neg, off_fold_neg, <-ginv_gop, (iha pa eq_refl). reflexivity.
        + destruct (lin_of e) as [l |] eqn:hl; cbn [option_map] in hp; [| congruence].
          inversion hp; subst; cbn [fst snd].
          unfold off_fold; cbn [List.fold_right]. unfold off_denote; cbn [fst snd].
          rewrite right_identity, lin_terms_denote, (lin_of_denote wenv e l hl). reflexivity.
      Qed.

      (** One homogeneous equation says exactly what the original
          point equation said.

          [elab_eq pa pb] holds, in the sense of the core semantics,
          if and only if the two point expressions denote the same
          group element.

          The reason is short.  The core equation asserts that the
          left side times the inverse of the right side is the
          identity, and in a group that happens exactly when the two
          are equal.  The length of the proof is entirely the
          rearrangement of four folded blocks into two, which
          commutativity permits. *)
      Lemma elab_eq_denote :
        ∀ (genv : V -> G) (wenv : V -> F) (a b : gexpr) (pa pb : gflat),
        elab_g a = Some pa -> elab_g b = Some pb ->
        (eq_denoteC genv penv wenv (elab_eq pa pb) <->
         gdenote genv wenv a = gdenote genv wenv b).
      Proof.
        intros genv wenv a b pa pb ha hb.
        unfold eq_denote, elab_eq; cbn [eq_rhs eq_off].
        rewrite (terms_fold_app genv penv (Hvec := Hvec)),
          (off_fold_app genv penv (Hvec := Hvec)).
        rewrite terms_fold_neg, off_fold_neg.
        set (Ta := terms_foldC genv penv wenv (fst pa)).
        set (Tb := terms_foldC genv penv wenv (fst pb)).
        set (Oa := off_foldC genv penv (snd pa)).
        set (Ob := off_foldC genv penv (snd pb)).
        assert (hre : gop (gop Ta (ginv Tb)) (gop Oa (ginv Ob)) =
          gop (gop Ta Oa) (ginv (gop Tb Ob))).
        { rewrite ginv_gop. rewrite <-!associative. f_equal.
          rewrite !associative. f_equal. eapply commutative. }
        rewrite hre.
        rewrite <-(elab_g_denote genv wenv a pa ha), <-(elab_g_denote genv wenv b pb hb).
        fold Ta Tb Oa Ob.
        split; intro h.
        + eapply (gop_eq_gid_iff (Hvec := Hvec)) in h. rewrite group_inv_inv in h. exact h.
        + eapply (gop_eq_gid_iff (Hvec := Hvec)). rewrite group_inv_inv. exact h.
      Qed.

      (** Flattening invents no names.

          Every private name of the produced terms, and every base
          name of the produced terms and offsets, already occurs in
          [gnames g].  Together with [lin_of_vars] this is what lets
          the freshness argument speak about the source syntax alone,
          never inspecting the flattened output. *)
      Lemma elab_g_names :
        ∀ (g : gexpr) (p : gflat),
        elab_g g = Some p ->
        List.incl (List.map t_var (fst p)) (gnames g) ∧
        List.incl (List.app (List.map t_base (fst p)) (List.map snd (snd p))) (gnames g).
      Proof.
        intros g.
        induction g as [| P | a iha b ihb | a iha | P e]; intros p hp;
        cbn [elab_g] in hp; cbn [gnames].
        + inversion hp; subst; cbn. split; eapply List.incl_nil_l.
        + inversion hp; subst; cbn. split; [eapply List.incl_nil_l | eapply List.incl_refl].
        + destruct (elab_g a) as [pa |]; [| congruence].
          destruct (elab_g b) as [pb |]; [| congruence].
          inversion hp; subst; cbn [fst snd].
          destruct (iha pa eq_refl) as (ha1 & ha2). destruct (ihb pb eq_refl) as (hb1 & hb2).
          split.
          - rewrite List.map_app. eapply List.incl_app_app; assumption.
          - rewrite !List.map_app.
            intros v hv. eapply List.in_or_app.
            eapply List.in_app_or in hv. destruct hv as [hv | hv];
            eapply List.in_app_or in hv; destruct hv as [hv | hv].
            * left. eapply ha2, List.in_or_app; left; exact hv.
            * right. eapply hb2, List.in_or_app; left; exact hv.
            * left. eapply ha2, List.in_or_app; right; exact hv.
            * right. eapply hb2, List.in_or_app; right; exact hv.
        + destruct (elab_g a) as [pa |]; cbn [option_map] in hp; [| congruence].
          inversion hp; subst; cbn [fst snd].
          destruct (iha pa eq_refl) as (ha1 & ha2).
          unfold neg_terms, neg_offs. rewrite !List.map_map. cbn [t_var t_base snd].
          split; assumption.
        + destruct (lin_of e) as [l |] eqn:hl; cbn [option_map] in hp; [| congruence].
          inversion hp; subst; cbn [fst snd].
          unfold lin_terms. rewrite !List.map_map. cbn [t_var t_base snd].
          split.
          - intros v hv. right. eapply (lin_of_vars e l hl). exact hv.
          - intros v hv. eapply List.in_app_or in hv. destruct hv as [hv | hv].
            * eapply List.in_map_iff in hv. destruct hv as (cy & heq & _). subst v.
              left; reflexivity.
            * destruct hv as [hv | []]. subst v. left; reflexivity.
      Qed.

      (** ** The meaning of a statement is local

          Three extensionality lemmas, one per syntactic class: a
          denotation looks at the environments only at the names its
          syntax mentions.

          These are the workhorses of the completeness proof.  There,
          environments are extended over and over with the auxiliary
          data of one gadget after another, and each time one must
          argue that everything already established still holds.  It
          does, because each extension touches only fresh names,
          which by construction are not among the names of anything
          proved so far. *)

      (** Two witnesses agreeing on [xnames e] give the scalar
          expression [e] the same value. *)
      Lemma sdenote_ext :
        ∀ (w₁ w₂ : V -> F) (e : sexpr),
        (∀ x, List.In x (xnames e) -> w₁ x = w₂ x) ->
        sdenote w₁ e = sdenote w₂ e.
      Proof.
        intros w₁ w₂ e h.
        induction e as [c | x | x | a iha b ihb | a iha b ihb | a iha]; cbn in h |- *.
        + reflexivity.
        + reflexivity.
        + eapply h; left; reflexivity.
        + rewrite iha, ihb; [reflexivity | |];
          intros x hx; eapply h, List.in_or_app; [right | left]; exact hx.
        + rewrite iha, ihb; [reflexivity | |];
          intros x hx; eapply h, List.in_or_app; [right | left]; exact hx.
        + rewrite iha; [reflexivity | exact h].
      Qed.

      (** Two point environments and two witnesses agreeing on
          [gnames e] give the point expression [e] the same value. *)
      Lemma gdenote_ext :
        ∀ (g₁ g₂ : V -> G) (w₁ w₂ : V -> F) (e : gexpr),
        (∀ x, List.In x (gnames e) -> g₁ x = g₂ x) ->
        (∀ x, List.In x (gnames e) -> w₁ x = w₂ x) ->
        gdenote g₁ w₁ e = gdenote g₂ w₂ e.
      Proof.
        intros g₁ g₂ w₁ w₂ e hg hw.
        induction e as [| P | a iha b ihb | a iha | P e]; cbn in hg, hw |- *.
        + reflexivity.
        + eapply hg; left; reflexivity.
        + rewrite iha, ihb; [reflexivity | | | |]; intros x hx;
          first [eapply hg | eapply hw]; eapply List.in_or_app;
          first [left; exact hx | right; exact hx].
        + rewrite iha; [reflexivity | exact hg | exact hw].
        + rewrite (hg P), (sdenote_ext w₁ w₂ e); [reflexivity | | left; reflexivity].
          intros x hx; eapply hw; right; exact hx.
      Qed.

      (** Two pairs of environments agreeing on [snames s] make the
          statement [s] equivalent.

          Proved by the strengthened induction [sstmt_ind'].  The
          [TLet] case is the only delicate one: inside the body the
          witness has been overridden at the bound name, so one shows
          that the two overridden witnesses still agree, splitting on
          whether the name being looked up is the bound one.  The
          threshold case reduces to the same statement for
          [sflagged] at an arbitrary flag list. *)
      Lemma sstmt_denote_ext :
        ∀ (s : sstmt) (g₁ g₂ : V -> G) (w₁ w₂ : V -> F),
        (∀ x, List.In x (snames s) -> g₁ x = g₂ x) ->
        (∀ x, List.In x (snames s) -> w₁ x = w₂ x) ->
        (sstmt_denote g₁ w₁ s <-> sstmt_denote g₂ w₂ s).
      Proof.
        intros s.
        induction s as [a b | e | x u | x e body ih | a b iha ihb | a b iha ihb | t l ihl]
          using sstmt_ind'; intros g₁ g₂ w₁ w₂ hg hw; cbn [snames] in hg, hw.
        + cbn [sstmt_denote].
          rewrite (gdenote_ext g₁ g₂ w₁ w₂ a), (gdenote_ext g₁ g₂ w₁ w₂ b);
          [reflexivity | | | |];
          intros x hx; first [eapply hg | eapply hw]; eapply List.in_or_app;
          first [left; exact hx | right; exact hx].
        + cbn [sstmt_denote]. rewrite (sdenote_ext w₁ w₂ e hw). reflexivity.
        + cbn [sstmt_denote]. rewrite (hw x); [reflexivity | left; reflexivity].
        + cbn [sstmt_denote]. eapply ih.
          - intros y hy. eapply hg. right. eapply List.in_or_app; right; exact hy.
          - intros y hy. unfold override.
            destruct (vdecV y x) as [heq | hne].
            * subst y. rewrite veqb_refl. eapply sdenote_ext.
              intros z hz. eapply hw. right. eapply List.in_or_app; left; exact hz.
            * destruct (veqb y x) eqn:hyx; [eapply veqb_eq in hyx; contradiction |].
              eapply hw. right. eapply List.in_or_app; right; exact hy.
        + cbn [sstmt_denote].
          rewrite (iha g₁ g₂ w₁ w₂), (ihb g₁ g₂ w₁ w₂); [reflexivity | | | |];
          intros x hx; first [eapply hg | eapply hw]; eapply List.in_or_app;
          first [left; exact hx | right; exact hx].
        + cbn [sstmt_denote].
          rewrite (iha g₁ g₂ w₁ w₂), (ihb g₁ g₂ w₁ w₂); [reflexivity | | | |];
          intros x hx; first [eapply hg | eapply hw]; eapply List.in_or_app;
          first [left; exact hx | right; exact hx].
        + rewrite !sstmt_denote_thresh.
          assert (hfl : ∀ bs, sflagged g₁ w₁ l bs <-> sflagged g₂ w₂ l bs).
          { induction ihl as [| s l hs hl ih]; intros [| b bs]; cbn [sflagged];
            try reflexivity.
            rewrite ih.
            - destruct b; [| reflexivity].
              rewrite (hs g₁ g₂ w₁ w₂); [reflexivity | |];
              intros x hx; first [eapply hg | eapply hw]; eapply List.in_or_app;
              left; exact hx.
            - intros x hx; eapply hg; eapply List.in_or_app; right; exact hx.
            - intros x hx; eapply hw; eapply List.in_or_app; right; exact hx. }
          split; intros (bs & h1 & h2 & h3); exists bs; repeat split; try assumption;
          eapply hfl; exact h3.
      Qed.

      (** ** Where the names of an elaborated statement come from

          A core statement has two kinds of name: its private
          variables, collected by [stmt_vars], and the points it
          mentions, collected by [stmt_points].  This group of lemmas
          builds up to [elab_names]: every such name is either a name
          from the source statement or a name generated along the
          way, and in both cases it lies in the used-name list [elab]
          returns.

          That is exactly the invariant the completeness proof needs
          in order to extend environments safely. *)

      (** Elaboration only ever adds to the used-name list.

          Whatever was in [used] is still in the list [elab used s]
          returns.  Names are never dropped, so a name reserved at
          any point stays reserved for the rest of the walk.  This is
          what makes the sequential threading in [TAnd], [TOr] and
          [TThresh] correct. *)
      Lemma elab_used_incl :
        ∀ (s : sstmt) (used used' : list V) (c : stmtC),
        elab used s = Some (c, used') -> List.incl used used'.
      Proof.
        intros s.
        induction s as [a b | e | x u | x e body ih | a b iha ihb | a b iha ihb | t l ihl]
          using sstmt_ind'; intros used used' c he.
        + cbn [elab] in he.
          destruct (elab_g a); [| congruence]. destruct (elab_g b); [| congruence].
          inversion he; subst. eapply List.incl_refl.
        + cbn [elab] in he.
          destruct (lin_of e) as [[off cys] |]; [| congruence].
          destruct cys as [| [coeff x] [| ? ?]]; try congruence.
          destruct (fresh_list used 4) as [| Cn [| j [| sn [| r [| ? ?]]]]]; try congruence.
          inversion he; subst. eapply List.incl_appl, List.incl_refl.
        + cbn [elab] in he.
          destruct (2 <=? u)%nat; [| congruence].
          inversion he; subst. eapply List.incl_appl, List.incl_refl.
        + cbn [elab] in he.
          destruct (lin_of e) as [l |]; [| congruence].
          destruct (elab used body) as [[cb u1] |] eqn:hb; [| congruence].
          destruct (List.existsb (veqb x) (lin_vars l)); [congruence |].
          inversion he; subst. eapply ih; exact hb.
        + cbn [elab] in he.
          destruct (elab used a) as [[ca u1] |] eqn:ha; [| congruence].
          destruct (elab u1 b) as [[cb u2] |] eqn:hb; [| congruence].
          inversion he; subst.
          eapply List.incl_tran; [eapply iha; exact ha | eapply ihb; exact hb].
        + cbn [elab] in he.
          destruct (elab used a) as [[ca u1] |] eqn:ha; [| congruence].
          destruct (elab u1 b) as [[cb u2] |] eqn:hb; [| congruence].
          inversion he; subst.
          eapply List.incl_tran; [eapply iha; exact ha | eapply ihb; exact hb].
        + rewrite elab_thresh in he.
          destruct (elab_list used l) as [[cs u'] |] eqn:hl; [| congruence].
          inversion he; subst. clear he.
          revert used used' cs hl.
          induction ihl as [| s l hs hl ih]; intros used used' cs hl';
          cbn [elab_list] in hl'.
          - inversion hl'; subst. eapply List.incl_refl.
          - destruct (elab used s) as [[c1 u1] |] eqn:h1; [| congruence].
            destruct (elab_list u1 l) as [[cs2 u2] |] eqn:h2; [| congruence].
            inversion hl'; subst.
            eapply List.incl_tran; [eapply hs; exact h1 | eapply ih; exact h2].
      Qed.

      (** Substitution introduces only the names of the substituted
          form, and removes the substituted name.

          If [v] is a private variable of the statement obtained by
          replacing [x] with the linear form [l], then either [v] is
          one of the variables of [l], or [v] was already a variable
          of the original statement and is different from [x].

          The second half is the important one.  After substituting,
          the name [x] is genuinely gone, which is why a [TLet] can
          be compiled away without leaving any trace. *)
      Lemma subst_stmt_vars :
        ∀ (x : V) (l : linC) (s : stmtC) (v : V),
        List.In v (stmt_vars (@subst_stmt F V vdecV x l s)) ->
        List.In v (lin_vars l) ∨ (List.In v (stmt_vars s) ∧ v <> x).
      Proof.
        intros x l s v.
        induction s as [eqs | a b iha ihb | a b iha ihb | t ss ihl] using stmt_ind';
        intros hv.
        + cbn [subst_stmt stmt_vars] in hv |- *.
          induction eqs as [| e eqs ih]; cbn [List.map List.flat_map] in hv |- *;
          [contradiction |].
          eapply List.in_app_or in hv. destruct hv as [hv | hv].
          - unfold subst_eq in hv; cbn [eq_rhs] in hv.
            eapply List.in_map_iff in hv. destruct hv as (t' & heq & hin).
            eapply List.in_flat_map in hin. destruct hin as (t & ht & hin').
            unfold subst_term in hin'.
            destruct (Dsl.veqb (t_var t) x) eqn:hvx; cbn [fst] in hin'.
            * eapply List.in_map_iff in hin'. destruct hin' as (cy & heq' & hcy).
              subst t'. cbn in heq.
              left. unfold lin_vars. rewrite <-heq. eapply List.in_map. exact hcy.
            * destruct hin' as [hin' | []]. subst t'.
              right. split.
              { eapply List.in_or_app; left. rewrite <-heq. eapply List.in_map. exact ht. }
              { intro hvx'. rewrite <-heq in hvx'. subst x.
                rewrite veqb_refl in hvx. congruence. }
          - destruct (ih hv) as [h | (h1 & h2)];
            [left; exact h | right; split; [eapply List.in_or_app; right; exact h1 | exact h2]].
        + cbn [subst_stmt stmt_vars] in hv |- *.
          eapply List.in_app_or in hv. destruct hv as [hv | hv].
          - destruct (iha hv) as [h | (h1 & h2)];
            [left; exact h | right; split; [eapply List.in_or_app; left; exact h1 | exact h2]].
          - destruct (ihb hv) as [h | (h1 & h2)];
            [left; exact h | right; split; [eapply List.in_or_app; right; exact h1 | exact h2]].
        + cbn [subst_stmt stmt_vars] in hv |- *.
          eapply List.in_app_or in hv. destruct hv as [hv | hv].
          - destruct (iha hv) as [h | (h1 & h2)];
            [left; exact h | right; split; [eapply List.in_or_app; left; exact h1 | exact h2]].
          - destruct (ihb hv) as [h | (h1 & h2)];
            [left; exact h | right; split; [eapply List.in_or_app; right; exact h1 | exact h2]].
        + cbn [subst_stmt stmt_vars] in hv |- *.
          induction ihl as [| s ss hs hss ih]; cbn in hv |- *; [contradiction |].
          eapply List.in_app_or in hv. destruct hv as [hv | hv].
          - destruct (hs hv) as [h | (h1 & h2)];
            [left; exact h | right; split; [eapply List.in_or_app; left; exact h1 | exact h2]].
          - destruct (ih hv) as [h | (h1 & h2)];
            [left; exact h | right; split; [eapply List.in_or_app; right; exact h1 | exact h2]].
      Qed.

      (** Substitution introduces no new point names.

          Replacing a private variable by a linear form rewrites
          exponents but never changes the base a term sits on, so the
          collection of points can only shrink.  The assertion inside
          the proof states precisely that: a substituted term keeps
          its base. *)
      Lemma subst_stmt_points :
        ∀ (x : V) (l : linC) (s : stmtC),
        List.incl (stmt_points (@subst_stmt F V vdecV x l s)) (stmt_points s).
      Proof.
        intros x l s.
        induction s as [eqs | a b iha ihb | a b iha ihb | t ss ihl] using stmt_ind'.
        + cbn [subst_stmt stmt_points].
          induction eqs as [| e eqs ih]; cbn [List.map List.flat_map];
          [eapply List.incl_refl |].
          eapply List.incl_app_app; [| exact ih].
          unfold eq_points, subst_eq; cbn [eq_rhs eq_off].
          (* a substituted term keeps its base *)
          assert (hterm : ∀ (t : termC) (v : V),
            (List.In v (List.map t_base (fst (@subst_term F V vdecV x l t))) ∨
             List.In v (List.map snd (snd (@subst_term F V vdecV x l t)))) -> v = t_base t).
          { intros t v hv. unfold subst_term in hv.
            destruct (Dsl.veqb (t_var t) x); cbn [fst snd] in hv.
            - destruct hv as [hv | hv].
              + rewrite List.map_map in hv. eapply List.in_map_iff in hv.
                destruct hv as (cy & heq & _). cbn in heq. symmetry; exact heq.
              + cbn in hv. destruct hv as [hv | []]. symmetry; exact hv.
            - destruct hv as [hv | hv]; cbn in hv;
              [destruct hv as [hv | []]; symmetry; exact hv | contradiction]. }
          intros v hv. eapply List.in_app_or in hv. destruct hv as [hv | hv].
          - eapply List.in_map_iff in hv. destruct hv as (t' & heq & hin).
            eapply List.in_flat_map in hin. destruct hin as (t & ht & hin').
            eapply List.in_or_app; left. eapply List.in_map_iff.
            exists t; split; [| exact ht].
            rewrite <-heq. symmetry. eapply hterm. left. eapply List.in_map_iff.
            exists t'; split; [reflexivity | exact hin'].
          - rewrite List.map_app in hv. eapply List.in_app_or in hv.
            destruct hv as [hv | hv].
            * eapply List.in_map_iff in hv. destruct hv as (o & heq & hin).
              eapply List.in_flat_map in hin. destruct hin as (t & ht & hin').
              eapply List.in_or_app; left. eapply List.in_map_iff.
              exists t; split; [| exact ht].
              rewrite <-heq. symmetry. eapply hterm. right. eapply List.in_map_iff.
              exists o; split; [reflexivity | exact hin'].
            * eapply List.in_or_app; right. exact hv.
        + cbn [subst_stmt stmt_points]. eapply List.incl_app_app; assumption.
        + cbn [subst_stmt stmt_points]. eapply List.incl_app_app; assumption.
        + cbn [subst_stmt stmt_points].
          induction ihl as [| s ss hs hss ih]; cbn; [eapply List.incl_refl |].
          eapply List.incl_app_app; [exact hs | exact ih].
      Qed.

      (** ** Which names the gadgets use

          Four inclusion lemmas, read straight off the definitions in
          DslNeq.v and DslRange.v, listing the private variables and
          the points each gadget mentions.  They are dull to prove
          and indispensable: without them there is no way to show
          that the names a gadget introduces stay inside the
          used-name list. *)

      (** The nonzero gadget mentions only the scalar under test and
          its three auxiliary scalars. *)
      Lemma neq_stmt_vars :
        ∀ (Cn A B x j sn r : V) (coeff off : pexprC),
        List.incl (stmt_vars (@neq_stmt F one V Cn A B x j sn r coeff off))
          (List.cons x (List.cons j (List.cons sn (List.cons r List.nil)))).
      Proof.
        intros *; cbn. intros v hv.
        repeat (destruct hv as [hv | hv]; [subst; cbn; tauto |]). contradiction.
      Qed.

      (** The nonzero gadget mentions only the two Pedersen bases and
          its own commitment point. *)
      Lemma neq_stmt_points :
        ∀ (Cn A B x j sn r : V) (coeff off : pexprC),
        List.incl (stmt_points (@neq_stmt F one V Cn A B x j sn r coeff off))
          (List.cons A (List.cons B (List.cons Cn List.nil))).
      Proof.
        intros *; cbn. intros v hv.
        repeat (destruct hv as [hv | hv]; [subst; cbn; tauto |]). contradiction.
      Qed.

      (** The range gadget mentions only the scalar under test and
          the per-bit variables collected by [bit_names], which are,
          for each bit index, the bit itself, the randomness of its
          commitment, and its square witness. *)
      Lemma range_stmt_vars :
        ∀ (bb br bs bC : nat -> V) (A B x : V) (u : nat),
        List.incl (stmt_vars (@range_stmt F zero one add opp V bb br bs bC A B x u))
          (List.cons x (bit_names bb br bs (List.length (range_weights u)))).
      Proof.
        intros *. unfold range_stmt. cbn [stmt_vars].
        intros v hv. cbn [List.flat_map] in hv.
        eapply List.in_app_or in hv. destruct hv as [hv | hv].
        + unfold range_link in hv; cbn [eq_rhs List.map t_var] in hv.
          destruct hv as [hv | hv]; [left; exact hv |].
          rewrite List.map_map in hv. eapply List.in_map_iff in hv.
          destruct hv as (iw & heq & hin). cbn [t_var] in heq. subst v.
          right. eapply in_bit_names. exists (fst iw).
          split; [eapply indexed_weights_idx; exact hin | left; reflexivity].
        + eapply List.in_flat_map in hv. destruct hv as (e & he & hv).
          eapply List.in_flat_map in he. destruct he as (iw & hin & he).
          pose proof (indexed_weights_idx u iw hin) as hi.
          unfold bit_eqs in he. cbn [List.In] in he.
          destruct he as [he | [he | []]]; subst e; cbn in hv.
          - destruct hv as [hv | [hv | []]]; subst v; right; eapply in_bit_names;
            exists (fst iw); split; auto.
          - destruct hv as [hv | [hv | []]]; subst v; right; eapply in_bit_names;
            exists (fst iw); split; auto.
      Qed.

      (** The range gadget mentions only the two Pedersen bases and
          the one commitment point published per bit. *)
      Lemma range_stmt_points :
        ∀ (bb br bs bC : nat -> V) (A B x : V) (u : nat),
        List.incl (stmt_points (@range_stmt F zero one add opp V bb br bs bC A B x u))
          (List.cons A (List.cons B (List.map bC (List.seq 0 (List.length (range_weights u)))))).
      Proof.
        intros *. unfold range_stmt. cbn [stmt_points].
        intros v hv. cbn [List.flat_map] in hv.
        eapply List.in_app_or in hv. destruct hv as [hv | hv].
        + unfold range_link, eq_points in hv;
          cbn [eq_rhs eq_off List.map t_base List.app] in hv.
          destruct hv as [hv | hv]; [left; exact hv |].
          rewrite List.app_nil_r, List.map_map in hv. eapply List.in_map_iff in hv.
          destruct hv as (iw & heq & hin). cbn [t_base] in heq. subst v. left; reflexivity.
        + eapply List.in_flat_map in hv. destruct hv as (e & he & hv).
          eapply List.in_flat_map in he. destruct he as (iw & hin & he).
          pose proof (indexed_weights_idx u iw hin) as hi.
          unfold bit_eqs in he. cbn [List.In] in he.
          destruct he as [he | [he | []]]; subst e; unfold eq_points in hv; cbn in hv.
          - destruct hv as [hv | [hv | [hv | []]]]; subst v;
            [left | right; left | right; right]; try reflexivity.
            eapply List.in_map_iff. exists (fst iw).
            split; [reflexivity | eapply List.in_seq; lia].
          - destruct hv as [hv | [hv | [hv | []]]]; subst v.
            * right; right. eapply List.in_map_iff. exists (fst iw).
              split; [reflexivity | eapply List.in_seq; lia].
            * right; left; reflexivity.
            * right; right. eapply List.in_map_iff. exists (fst iw).
              split; [reflexivity | eapply List.in_seq; lia].
      Qed.

      (** The per-bit names, viewed two ways, are the same names.

          [bit_names] emits three names per bit index, interleaved,
          whereas [elab_range] supplies three separate lists of fresh
          names.  When each list holds one entry per bit, the
          interleaved collection is a permutation of the three lists
          concatenated.  Since only membership is ever used, that is
          enough to carry freshness from the generator's lists over
          to the gadget's names.  The proof is [flat_map3_perm]
          followed by [map_nth_seq_len], which undoes the
          list-to-function wrapping. *)
      Lemma bit_names_perm :
        ∀ (fb fr fs : list V) (n : nat),
        List.length fb = n -> List.length fr = n -> List.length fs = n ->
        Permutation
          (bit_names (fun i => List.nth i fb default_name)
             (fun i => List.nth i fr default_name)
             (fun i => List.nth i fs default_name) n)
          (List.app fb (List.app fr fs)).
      Proof.
        intros fb fr fs n hb hr hs.
        unfold bit_names.
        eapply Permutation_trans; [eapply flat_map3_perm |].
        rewrite (map_nth_seq_len V fb default_name n hb),
          (map_nth_seq_len V fr default_name n hr),
          (map_nth_seq_len V fs default_name n hs).
        reflexivity.
      Qed.

      (** Every name of an elaborated range gadget lies in the
          extended used-name list.

          The hypotheses say that the scalar under test and the two
          bases were already reserved.  The gadget's variables are
          then either that scalar or one of the freshly generated
          per-bit names, and its points are either a base or one of
          the freshly generated commitment names.  [elab_range]
          appended all of those to [used], so the conclusion
          follows. *)
      Lemma elab_range_names :
        ∀ (used used' : list V) (x : V) (u : nat) (c : stmtC),
        elab_range used x u = (c, used') ->
        List.In x used -> List.In An used -> List.In Bn used ->
        List.incl (stmt_vars c) used' ∧ List.incl (stmt_points c) used'.
      Proof.
        intros used used' x u c hel hx hA hB.
        unfold elab_range in hel. inversion hel; subst; clear hel.
        set (n := List.length (range_weights u)) in *.
        set (fb := fresh_list used n) in *.
        set (fr := fresh_list (used ++ fb) n) in *.
        set (fs := fresh_list (used ++ fb ++ fr) n) in *.
        set (fC := fresh_list (used ++ fb ++ fr ++ fs) n) in *.
        split.
        + intros v hv. eapply range_stmt_vars in hv.
          destruct hv as [hv | hv].
          - subst v. eapply List.in_or_app; left; exact hx.
          - eapply (Permutation_in _ (bit_names_perm fb fr fs n
              (fresh_list_length V HV _ n) (fresh_list_length V HV _ n)
              (fresh_list_length V HV _ n))) in hv.
            eapply List.in_or_app; right.
            eapply List.in_app_or in hv.
            destruct hv as [hv | hv]; [eapply List.in_or_app; left; exact hv |].
            eapply List.in_or_app; right.
            eapply List.in_app_or in hv.
            destruct hv as [hv | hv]; [eapply List.in_or_app; left; exact hv |].
            eapply List.in_or_app; right. eapply List.in_or_app; left; exact hv.
        + intros v hv. eapply range_stmt_points in hv.
          destruct hv as [hv | [hv | hv]].
          - subst v. eapply List.in_or_app; left; exact hA.
          - subst v. eapply List.in_or_app; left; exact hB.
          - fold n in hv.
            rewrite (map_nth_seq_len V fC default_name n (fresh_list_length V HV _ n)) in hv.
            eapply List.in_or_app; right. eapply List.in_or_app; right.
            eapply List.in_or_app; right. eapply List.in_or_app; right. exact hv.
      Qed.

      (** Elaborating a list of statements yields a list of the same
          length.  Needed because the threshold count [t] is compared
          against the number of children on both the surface and the
          core side. *)
      Lemma elab_list_length :
        ∀ (l : list sstmt) (used used' : list V) (cs : list stmtC),
        elab_list used l = Some (cs, used') -> List.length cs = List.length l.
      Proof.
        intros l.
        induction l as [| s l ih]; intros used used' cs hl; cbn [elab_list] in hl.
        + inversion hl; subst. reflexivity.
        + destruct (elab used s) as [[c u1] |]; [| congruence].
          destruct (elab_list u1 l) as [[cs2 u2] |] eqn:h2; [| congruence].
          inversion hl; subst. cbn [List.length]. rewrite (ih _ _ _ h2). reflexivity.
      Qed.

      (** The list version of [elab_used_incl]: names are only ever
          added. *)
      Lemma elab_list_used_incl :
        ∀ (l : list sstmt) (used used' : list V) (cs : list stmtC),
        elab_list used l = Some (cs, used') -> List.incl used used'.
      Proof.
        intros l.
        induction l as [| s l ih]; intros used used' cs hl; cbn [elab_list] in hl.
        + inversion hl; subst; eapply List.incl_refl.
        + destruct (elab used s) as [[c u1] |] eqn:h1; [| congruence].
          destruct (elab_list u1 l) as [[cs2 u2] |] eqn:h2; [| congruence].
          inversion hl; subst.
          eapply List.incl_tran; [eapply (elab_used_incl s used u1 c h1) | eapply ih; exact h2].
      Qed.

      (** Every name of the elaborated statement lies in the returned
          used-name list.

          The hypotheses are that all source names of [s] were
          reserved to begin with, as were the two Pedersen bases.
          The conclusion covers both the private variables and the
          points of the core statement.

          The proof is an induction on [s] with [sstmt_ind'].  The
          leaf cases appeal to the name lemmas of the flattening and
          of the two gadgets.  The [TLet] case uses [subst_stmt_vars]
          to see that substitution adds only the names of the
          defining form, which are source names.  The composite cases
          chain the inclusions through [elab_used_incl], since a name
          reserved while elaborating the left child is still reserved
          when the right one is elaborated. *)
      Lemma elab_names :
        ∀ (s : sstmt) (used used' : list V) (c : stmtC),
        elab used s = Some (c, used') ->
        List.incl (snames s) used ->
        List.In An used -> List.In Bn used ->
        List.incl (stmt_vars c) used' ∧ List.incl (stmt_points c) used'.
      Proof.
        intros s.
        induction s as [a b | e | x u | x e body ih | a b iha ihb | a b iha ihb | t l ihl]
          using sstmt_ind'; intros used used' c he hsn hA hB.
        + cbn [elab] in he.
          destruct (elab_g a) as [pa |] eqn:ha; [| congruence].
          destruct (elab_g b) as [pb |] eqn:hb; [| congruence].
          inversion he; subst; clear he.
          cbn [snames] in hsn.
          destruct (elab_g_names a pa ha) as (ha1 & ha2).
          destruct (elab_g_names b pb hb) as (hb1 & hb2).
          cbn [stmt_vars stmt_points List.flat_map]. rewrite !List.app_nil_r.
          unfold elab_eq, eq_points; cbn [eq_rhs eq_off].
          rewrite !List.map_app. unfold neg_terms, neg_offs. rewrite !List.map_map.
          cbn [t_var t_base snd].
          split.
          - intros v hv. eapply hsn. eapply List.in_app_or in hv.
            destruct hv as [hv | hv]; eapply List.in_or_app;
            [left; eapply ha1; exact hv | right; eapply hb1; exact hv].
          - intros v hv. eapply hsn.
            rewrite <-List.app_assoc in hv.
            eapply List.in_app_or in hv. destruct hv as [hv | hv].
            * eapply List.in_or_app; left. eapply ha2. eapply List.in_or_app; left; exact hv.
            * eapply List.in_app_or in hv. destruct hv as [hv | hv].
              { eapply List.in_or_app; right. eapply hb2. eapply List.in_or_app; left; exact hv. }
              { eapply List.in_app_or in hv. destruct hv as [hv | hv].
                - eapply List.in_or_app; left. eapply ha2. eapply List.in_or_app; right; exact hv.
                - eapply List.in_or_app; right. eapply hb2. eapply List.in_or_app; right; exact hv. }
        + cbn [elab] in he.
          destruct (lin_of e) as [[off cys] |] eqn:hl; [| congruence].
          destruct cys as [| [coeff x] [| ? ?]]; try congruence.
          destruct (fresh_list used 4) as [| Cn [| j [| sn [| r [| ? ?]]]]] eqn:hfl; try congruence.
          inversion he; subst; clear he.
          cbn [snames] in hsn.
          assert (hx : List.In x used).
          { eapply hsn. eapply (lin_of_vars e _ hl). unfold lin_vars; cbn. left; reflexivity. }
          split.
          - intros v hv. eapply neq_stmt_vars in hv.
            destruct hv as [hv | [hv | [hv | [hv | []]]]]; subst v; eapply List.in_or_app.
            * left; exact hx.
            * right; right; left; reflexivity.
            * right; right; right; left; reflexivity.
            * right; right; right; right; left; reflexivity.
          - intros v hv. eapply neq_stmt_points in hv.
            destruct hv as [hv | [hv | [hv | []]]]; subst v; eapply List.in_or_app.
            * left; exact hA.
            * left; exact hB.
            * right; left; reflexivity.
        + cbn [elab] in he.
          destruct (2 <=? u)%nat eqn:hu; [| congruence].
          destruct (elab_range used x u) as [cr ur] eqn:hr.
          inversion he; subst; clear he.
          cbn [snames] in hsn.
          eapply elab_range_names; [exact hr | eapply hsn; left; reflexivity | exact hA | exact hB].
        + cbn [elab] in he.
          destruct (lin_of e) as [l |] eqn:hl; [| congruence].
          destruct (elab used body) as [[cb u1] |] eqn:hb; [| congruence].
          destruct (List.existsb (veqb x) (lin_vars l)) eqn:hex; [congruence |].
          inversion he; subst; clear he.
          cbn [snames] in hsn.
          pose proof (elab_used_incl body used used' cb hb) as hinc.
          destruct (ih used used' cb hb
            (ltac:(intros v hv; eapply hsn; right; eapply List.in_or_app; right; exact hv)) hA hB)
            as (hv1 & hp1).
          split.
          - intros v hv. eapply subst_stmt_vars in hv.
            destruct hv as [hv | (hv & _)].
            * eapply hinc, hsn. right. eapply List.in_or_app; left.
              eapply (lin_of_vars e l hl). exact hv.
            * eapply hv1; exact hv.
          - intros v hv. eapply hp1. eapply subst_stmt_points. exact hv.
        + cbn [elab] in he.
          destruct (elab used a) as [[ca u1] |] eqn:ha; [| congruence].
          destruct (elab u1 b) as [[cb u2] |] eqn:hb; [| congruence].
          inversion he; subst; clear he.
          cbn [snames] in hsn.
          pose proof (elab_used_incl a used u1 ca ha) as hinc1.
          pose proof (elab_used_incl b u1 used' cb hb) as hinc2.
          destruct (iha used u1 ca ha
            (ltac:(intros v hv; eapply hsn; eapply List.in_or_app; left; exact hv)) hA hB)
            as (hva & hpa).
          destruct (ihb u1 used' cb hb
            (ltac:(intros v hv; eapply hinc1, hsn; eapply List.in_or_app; right; exact hv))
            (hinc1 _ hA) (hinc1 _ hB)) as (hvb & hpb).
          cbn [stmt_vars stmt_points].
          split; eapply List.incl_app; try assumption; eapply List.incl_tran;
          [exact hva | exact hinc2 | exact hpa | exact hinc2].
        + cbn [elab] in he.
          destruct (elab used a) as [[ca u1] |] eqn:ha; [| congruence].
          destruct (elab u1 b) as [[cb u2] |] eqn:hb; [| congruence].
          inversion he; subst; clear he.
          cbn [snames] in hsn.
          pose proof (elab_used_incl a used u1 ca ha) as hinc1.
          pose proof (elab_used_incl b u1 used' cb hb) as hinc2.
          destruct (iha used u1 ca ha
            (ltac:(intros v hv; eapply hsn; eapply List.in_or_app; left; exact hv)) hA hB)
            as (hva & hpa).
          destruct (ihb u1 used' cb hb
            (ltac:(intros v hv; eapply hinc1, hsn; eapply List.in_or_app; right; exact hv))
            (hinc1 _ hA) (hinc1 _ hB)) as (hvb & hpb).
          cbn [stmt_vars stmt_points].
          split; eapply List.incl_app; try assumption; eapply List.incl_tran;
          [exact hva | exact hinc2 | exact hpa | exact hinc2].
        + rewrite elab_thresh in he.
          destruct (elab_list used l) as [[cs u'] |] eqn:hl; [| congruence].
          inversion he; subst; clear he.
          cbn [snames] in hsn.
          cbn [stmt_vars stmt_points].
          revert used used' cs hl hsn hA hB.
          induction ihl as [| s l hs hl ih]; intros used used' cs hl' hsn hA hB;
          cbn [elab_list] in hl'.
          - inversion hl'; subst. split; eapply List.incl_nil_l.
          - destruct (elab used s) as [[c1 u1] |] eqn:h1; [| congruence].
            destruct (elab_list u1 l) as [[cs2 u2] |] eqn:h2; [| congruence].
            inversion hl'; subst; clear hl'.
            pose proof (elab_used_incl s used u1 c1 h1) as hinc1.
            pose proof (elab_list_used_incl l u1 used' cs2 h2) as hinc2.
            destruct (hs used u1 c1 h1
              (ltac:(intros v hv; eapply hsn; eapply List.in_or_app; left; exact hv)) hA hB)
              as (hv1 & hp1).
            destruct (ih u1 used' cs2 h2
              (ltac:(intros v hv; eapply hinc1, hsn; eapply List.in_or_app; right; exact hv))
              (hinc1 _ hA) (hinc1 _ hB)) as (hv2 & hp2).
            split; eapply List.incl_app; try assumption; eapply List.incl_tran;
            [exact hv1 | exact hinc2 | exact hp1 | exact hinc2].
      Qed.

      (** ** Soundness

          Soundness is the direction that protects the verifier.
          Read it as: if someone produced a witness of the compiled
          statement, then either the user's statement really is true
          of that witness, or the setup was broken to begin with. *)

      (** The list version of soundness, for the children of a
          threshold.

          The [List.Forall] hypothesis is the induction hypothesis of
          the main proof: one soundness statement per child.  Given
          flags [bs] and a core witness satisfying every flagged
          compiled child, the same flags satisfy every flagged
          surface child, unless a broken setup turns up somewhere
          along the list.

          The proof walks the two lists together.  An unflagged child
          demands nothing and is free; a flagged one is handed to its
          own soundness statement. *)
      Lemma elab_list_sound :
        ∀ (l : list sstmt) (genv : V -> G),
        List.Forall (fun s => ∀ (used used' : list V) (c : stmtC) (wenv : V -> F),
          elab used s = Some (c, used') ->
          stmt_denoteC genv penv wenv c ->
          sstmt_denote genv wenv s ∨ degenerate genv) l ->
        ∀ (used used' : list V) (cs : list stmtC) (bs : list bool) (wenv : V -> F),
        elab_list used l = Some (cs, used') ->
        @flagged_denote F add mul opp G gid gop gpow V genv penv wenv cs bs ->
        sflagged genv wenv l bs ∨ degenerate genv.
      Proof.
        intros l genv hall.
        induction hall as [| s l hs hl ih]; intros used used' cs bs wenv hel hfl;
        cbn [elab_list] in hel.
        + inversion hel; subst. left. destruct bs; exact I.
        + destruct (elab used s) as [[c u1] |] eqn:h1; [| congruence].
          destruct (elab_list u1 l) as [[cs2 u2] |] eqn:h2; [| congruence].
          inversion hel; subst. clear hel.
          destruct bs as [| b bs]; [left; exact I |].
          cbn [flagged_denote] in hfl. destruct hfl as (hc & hrest).
          destruct (ih u1 used' cs2 bs wenv h2 hrest) as [hsf | hdeg]; [| right; exact hdeg].
          destruct b.
          - destruct (hs used u1 c wenv h1 hc) as [hss | hdeg]; [| right; exact hdeg].
            left. cbn [sflagged]. split; assumption.
          - left. cbn [sflagged]. split; [exact I | exact hsf].
      Qed.

      (** Soundness of elaboration: the dichotomy.

          If [elab used s] produced the core statement [c], and the
          environments satisfy [c], then either they satisfy the
          surface statement [s], or [degenerate genv] holds, meaning
          the two Pedersen bases are not independent and the setup
          itself was broken.

          Why two alternatives rather than one?  Because the gadgets
          are only as sound as their commitments.  The nonzero gadget
          proves that a committed value has an inverse; a prover who
          knew a discrete logarithm between the bases could open the
          commitment two different ways and pass the test with a zero
          value.  The range gadget tells the same story.  Nothing in
          this file can rule that out, so it is carried along
          honestly as the second alternative.  With honestly
          generated bases the second alternative is unreachable, and
          the theorem says what one wants it to say.

          The proof is an induction on [s] with [sstmt_ind'].
          Equations go through [elab_eq_denote] and never produce a
          degenerate case at all.  The nonzero and range cases are
          the gadget soundness theorems of DslNeq.v and DslRange.v,
          whose own escape clauses are precisely the two disjuncts of
          [degenerate].  The [TLet] case rebuilds the witness with
          the bound name set to the value of its defining form, uses
          [subst_stmt_denote] to pass between the substituted and the
          unsubstituted body, and then appeals to the induction
          hypothesis.  [TAnd], [TOr] and [TThresh] merely propagate:
          a broken setup found in any child is a broken setup for the
          whole statement. *)
      Theorem elab_sound :
        ∀ (s : sstmt) (used used' : list V) (c : stmtC)
          (genv : V -> G) (wenv : V -> F),
        elab used s = Some (c, used') ->
        stmt_denoteC genv penv wenv c ->
        sstmt_denote genv wenv s ∨ degenerate genv.
      Proof.
        intros s.
        induction s as [a b | e | x u | x e body ih | a b iha ihb | a b iha ihb | t l ihl]
          using sstmt_ind'; intros used used' c genv wenv he hd.
        + cbn [elab] in he.
          destruct (elab_g a) as [pa |] eqn:ha; [| congruence].
          destruct (elab_g b) as [pb |] eqn:hb; [| congruence].
          inversion he; subst; clear he.
          cbn [stmt_denote] in hd. inversion hd as [| ? ? heq _]; subst.
          left. cbn [sstmt_denote]. eapply (elab_eq_denote genv wenv a b pa pb ha hb). exact heq.
        + cbn [elab] in he.
          destruct (lin_of e) as [[off cys] |] eqn:hl; [| congruence].
          destruct cys as [| [coeff x] [| ? ?]]; try congruence.
          destruct (fresh_list used 4) as [| Cn [| j [| sn [| r [| ? ?]]]]] eqn:hfl; try congruence.
          inversion he; subst; clear he.
          destruct (neq_sound (Fdec := Fdec) genv penv (Hvec := Hvec)
            Cn An Bn x j sn r coeff off wenv hd) as [hnz | hdeg].
          - left. cbn [sstmt_denote]. rewrite <-(lin_of_denote wenv e _ hl).
            unfold lin_denote; cbn [fst snd List.fold_right].
            intro h; eapply hnz. rewrite <-h. field.
          - right. right. exact hdeg.
        + cbn [elab] in he.
          destruct (2 <=? u)%nat eqn:hu; [| congruence].
          destruct (elab_range used x u) as [cr ur] eqn:hr.
          inversion he; subst; clear he.
          unfold elab_range in hr. inversion hr; subst; clear hr.
          eapply Nat.leb_le in hu.
          destruct (range_sound (Fdec := Fdec) _ _ _ _ genv penv (Hvec := Hvec)
            An Bn x u wenv hu hd) as [hk | [h1 | h2]].
          - left. cbn [sstmt_denote]. exact hk.
          - right; left; exact h1.
          - right; right; exact h2.
        + cbn [elab] in he.
          destruct (lin_of e) as [l |] eqn:hl; [| congruence].
          destruct (elab used body) as [[cb u1] |] eqn:hb; [| congruence].
          destruct (List.existsb (veqb x) (lin_vars l)) eqn:hex; [congruence |].
          inversion he; subst; clear he.
          (* x is not a variable of the defining form *)
          assert (hxl : ∀ v, List.In v (lin_vars l) -> v <> x).
          { intros v hv heq. subst v.
            assert (h : List.existsb (veqb x) (lin_vars l) = true).
            { eapply List.existsb_exists. exists x. split; [exact hv | eapply veqb_refl]. }
            congruence. }
          (* evaluate the substituted body at x := value of the form *)
          set (w := overrideC wenv x (lin_denoteC wenv l)).
          assert (hwl : lin_denoteC w l = lin_denoteC wenv l).
          { eapply lin_denote_ext. intros v hv. unfold w. eapply override_other.
            eapply hxl; exact hv. }
          assert (hwx : w x = lin_denoteC w l).
          { rewrite hwl. unfold w. eapply override_same. }
          assert (hd' : stmt_denoteC genv penv w (@subst_stmt F V vdecV x l cb)).
          { eapply (stmt_denote_ext genv penv _ wenv w); [| exact hd].
            intros v hv. eapply subst_stmt_vars in hv.
            destruct hv as [hv | (_ & hv)]; unfold w; symmetry; eapply override_other;
            [eapply hxl; exact hv | exact hv]. }
          rewrite (subst_stmt_denote (vdec := vdecV) genv penv (Hvec := Hvec) w x l cb hwx) in hd'.
          destruct (ih used used' cb genv w hb hd') as [hs | hdeg]; [| right; exact hdeg].
          left. cbn [sstmt_denote]. rewrite <-(lin_of_denote wenv e l hl). exact hs.
        + cbn [elab] in he.
          destruct (elab used a) as [[ca u1] |] eqn:ha; [| congruence].
          destruct (elab u1 b) as [[cb u2] |] eqn:hb; [| congruence].
          inversion he; subst; clear he.
          cbn [stmt_denote] in hd. destruct hd as (hda & hdb).
          destruct (iha used u1 ca genv wenv ha hda) as [hsa | hdeg]; [| right; exact hdeg].
          destruct (ihb u1 used' cb genv wenv hb hdb) as [hsb | hdeg]; [| right; exact hdeg].
          left. cbn [sstmt_denote]. split; assumption.
        + cbn [elab] in he.
          destruct (elab used a) as [[ca u1] |] eqn:ha; [| congruence].
          destruct (elab u1 b) as [[cb u2] |] eqn:hb; [| congruence].
          inversion he; subst; clear he.
          cbn [stmt_denote] in hd. destruct hd as [hda | hdb].
          - destruct (iha used u1 ca genv wenv ha hda) as [hsa | hdeg]; [| right; exact hdeg].
            left. cbn [sstmt_denote]. left; exact hsa.
          - destruct (ihb u1 used' cb genv wenv hb hdb) as [hsb | hdeg]; [| right; exact hdeg].
            left. cbn [sstmt_denote]. right; exact hsb.
        + rewrite elab_thresh in he.
          destruct (elab_list used l) as [[cs u'] |] eqn:hl; [| congruence].
          inversion he; subst; clear he.
          eapply stmt_denote_thresh in hd. destruct hd as (bs & hlen & hcnt & hfl).
          assert (ihl' : List.Forall (fun s => ∀ (used used' : list V) (c : stmtC) (wenv : V -> F),
            elab used s = Some (c, used') -> stmt_denoteC genv penv wenv c ->
            sstmt_denote genv wenv s ∨ degenerate genv) l).
          { eapply List.Forall_impl; [| exact ihl]. intros s hs used0 used'0 c0 wenv0 he0 hd0.
            eapply hs; eassumption. }
          destruct (elab_list_sound l genv ihl' used used' cs bs wenv hl hfl) as [hsf | hdeg];
          [| right; exact hdeg].
          left. eapply sstmt_denote_thresh. exists bs.
          rewrite <-(elab_list_length l used used' cs hl).
          split; [exact hlen | split; [exact hcnt | exact hsf]].
      Qed.

      (** ** Completeness

          Completeness is the direction that protects the honest
          prover.  Read it as: if the user's statement really is true
          of some witness, then the compiled statement can be
          satisfied too, once the gadgets' points have been published
          and their auxiliary scalars filled in.

          Those points and scalars are new data, so completeness
          cannot claim that the very same environments work.  It
          claims something almost as good: the new environments agree
          with the old ones everywhere in [used].  Since [used]
          contains every name the user wrote, nothing visible
          changes, and only fresh names acquire values. *)

      (** [sflagged] depends on the environments only at the names of
          the statements in the list.  The list version of
          [sstmt_denote_ext]. *)
      Lemma sflagged_ext :
        ∀ (l : list sstmt) (bs : list bool) (g₁ g₂ : V -> G) (w₁ w₂ : V -> F),
        (∀ x, List.In x (snames_of_list l) -> g₁ x = g₂ x) ->
        (∀ x, List.In x (snames_of_list l) -> w₁ x = w₂ x) ->
        (sflagged g₁ w₁ l bs <-> sflagged g₂ w₂ l bs).
      Proof.
        intros l.
        induction l as [| s l ih]; intros [| b bs] g₁ g₂ w₁ w₂ hg hw; cbn [sflagged];
        try reflexivity.
        unfold snames_of_list in hg, hw; cbn [List.flat_map] in hg, hw.
        rewrite (ih bs g₁ g₂ w₁ w₂).
        + destruct b; [| reflexivity].
          rewrite (sstmt_denote_ext s g₁ g₂ w₁ w₂); [reflexivity | |];
          intros x hx; first [eapply hg | eapply hw]; eapply List.in_or_app; left; exact hx.
        + intros x hx; eapply hg; eapply List.in_or_app; right; exact hx.
        + intros x hx; eapply hw; eapply List.in_or_app; right; exact hx.
      Qed.

      (** Completeness for the nonzero gadget.

          The hypotheses are that the four names came fresh from the
          generator, that the scalar under test and the two bases
          were already reserved, and that the linear value
          "coefficient times the witness at [x], plus the offset" is
          really nonzero.

          The honest prover then commits to that value with
          randomness zero, publishing the commitment point under the
          fresh name, and sets the gadget's auxiliary scalars: the
          inverse of the committed value, and the value that makes
          the second equation balance.  Using zero as the randomness
          is harmless here, because this lemma is about the relation
          being satisfiable at all; hiding the committed value is the
          protocol's concern, not this statement's.

          The bulk of the proof is disjointness bookkeeping: the four
          fresh names are pairwise distinct and differ from the two
          bases and from [x], which is what the gadget's own
          completeness theorem in DslNeq.v demands. *)
      Lemma elab_neq_complete :
        ∀ (used : list V) (x Cn j sn r : V) (coeff off : pexprC)
          (genv : V -> G) (wenv : V -> F),
        fresh_list used 4 = List.cons Cn (List.cons j (List.cons sn (List.cons r List.nil))) ->
        List.In x used -> List.In An used -> List.In Bn used ->
        pevalC coeff * wenv x + pevalC off <> zero ->
        ∃ (genv' : V -> G) (wenv' : V -> F),
          (∀ P, List.In P used -> genv' P = genv P) ∧
          (∀ v, List.In v used -> wenv' v = wenv v) ∧
          stmt_denoteC genv' penv wenv' (@neq_stmt F one V Cn An Bn x j sn r coeff off).
      Proof.
        intros used x Cn j sn r coeff off genv wenv hfl hx hA hB hnz.
        pose proof (fresh_list_nodup V HV used 4) as hnd; rewrite hfl in hnd.
        pose proof (fresh_list_not_in V HV used 4) as hnin; rewrite hfl in hnin.
        assert (hCn : ~ List.In Cn used). { eapply hnin; left; reflexivity. }
        assert (hj : ~ List.In j used). { eapply hnin; right; left; reflexivity. }
        assert (hsn : ~ List.In sn used). { eapply hnin; right; right; left; reflexivity. }
        assert (hr : ~ List.In r used). { eapply hnin; right; right; right; left; reflexivity. }
        inversion hnd as [| ? ? hCn' hnd1]; subst. inversion hnd1 as [| ? ? hj' hnd2]; subst.
        inversion hnd2 as [| ? ? hsn' hnd3]; subst.
        (* commitment randomness 0, commitment point published at Cn *)
        set (L := pevalC coeff * wenv x + pevalC off).
        set (wenv0 := overrideC wenv r zero).
        set (genv' := @upd V vdecV G genv
          (List.cons (Cn, gop ((genv An) ^ L) ((genv Bn) ^ zero)) List.nil)).
        assert (hg : ∀ P, P <> Cn -> genv' P = genv P).
        { intros P hP; unfold genv'; eapply upd_notin; cbn. intros [h | []]; congruence. }
        assert (hgCn : genv' Cn = gop ((genv An) ^ L) ((genv Bn) ^ zero)).
        { unfold genv'; eapply upd_in;
          [cbn; constructor; [intros [] | constructor] | left; reflexivity]. }
        assert (hw0x : wenv0 x = wenv x).
        { unfold wenv0; eapply override_other; intro h; subst; contradiction. }
        assert (hw0r : wenv0 r = zero). { unfold wenv0; eapply override_same. }
        assert (hjx : j <> x). { intro h; eapply hj; rewrite h; exact hx. }
        assert (hjr : j <> r). { intro h; eapply hj'; rewrite h; right; left; reflexivity. }
        assert (hsx : sn <> x). { intro h; eapply hsn; rewrite h; exact hx. }
        assert (hsr : sn <> r). { intro h; eapply hsn'; rewrite h; left; reflexivity. }
        assert (hsj : sn <> j). { intro h; eapply hj'; rewrite h; left; reflexivity. }
        assert (hAC : An <> Cn). { intro h; eapply hCn; rewrite <-h; exact hA. }
        assert (hBC : Bn <> Cn). { intro h; eapply hCn; rewrite <-h; exact hB. }
        destruct (neq_complete (vdec := vdecV) genv' penv (Hvec := Hvec)
          Cn An Bn x j sn r coeff off wenv0 hjx hjr hsx hsr hsj) as (wenv' & hw' & hd).
        { rewrite hw0x. exact hnz. }
        { rewrite hgCn, hw0x, hw0r, (hg An hAC), (hg Bn hBC). reflexivity. }
        exists genv', wenv'. split; [| split].
        + intros P hP. eapply hg. intro h; eapply hCn; rewrite <-h; exact hP.
        + intros v hv.
          rewrite hw'; [| intro h; eapply hj; rewrite <-h; exact hv
                        | intro h; eapply hsn; rewrite <-h; exact hv].
          unfold wenv0; eapply override_other; intro h; eapply hr; rewrite <-h; exact hv.
        + exact hd.
      Qed.

      (** Completeness for the range gadget.

          Given that the witness value of [x] really is the field
          image of a natural number [k] below [u], the honest prover
          decomposes [k] into bits, publishes one commitment per bit
          under the fresh commitment names, and sets the per-bit
          variables accordingly.

          Once again most of the work is freshness.  The four blocks
          of names produced by [elab_range] must be pairwise disjoint
          and disjoint from [used].  That follows from the generator
          of VarType.v, since each block was drawn against all the
          previous ones, and [bit_names_perm] transports it to the
          gadget's own view of the names. *)
      Lemma elab_range_complete :
        ∀ (used used' : list V) (x : V) (u : nat) (c : stmtC)
          (genv : V -> G) (wenv : V -> F),
        elab_range used x u = (c, used') ->
        (2 <= u)%nat ->
        List.In x used -> List.In An used -> List.In Bn used ->
        (∃ k : nat, (k < u)%nat ∧ wenv x = fnatC k) ->
        ∃ (genv' : V -> G) (wenv' : V -> F),
          (∀ P, List.In P used -> genv' P = genv P) ∧
          (∀ v, List.In v used -> wenv' v = wenv v) ∧
          stmt_denoteC genv' penv wenv' c.
      Proof.
        intros used used' x u c genv wenv hel hu hx hA hB (k & hk & hwx).
        unfold elab_range in hel. inversion hel; subst; clear hel.
        set (n := List.length (range_weights u)) in *.
        set (fb := fresh_list used n) in *.
        set (fr := fresh_list (used ++ fb) n) in *.
        set (fs := fresh_list (used ++ fb ++ fr) n) in *.
        set (fC := fresh_list (used ++ fb ++ fr ++ fs) n) in *.
        pose proof (bit_names_perm fb fr fs n (fresh_list_length V HV _ n)
          (fresh_list_length V HV _ n) (fresh_list_length V HV _ n)) as hperm.
        (* the four name lists are fresh and pairwise disjoint *)
        assert (hfb : ∀ v, List.In v fb -> ~ List.In v used).
        { intros v hv; eapply (fresh_list_not_in V HV used n v hv). }
        assert (hfr : ∀ v, List.In v fr -> ~ List.In v (used ++ fb)).
        { intros v hv; eapply (fresh_list_not_in V HV _ n v hv). }
        assert (hfs : ∀ v, List.In v fs -> ~ List.In v (used ++ fb ++ fr)).
        { intros v hv; eapply (fresh_list_not_in V HV _ n v hv). }
        assert (hfC : ∀ v, List.In v fC -> ~ List.In v (used ++ fb ++ fr ++ fs)).
        { intros v hv; eapply (fresh_list_not_in V HV _ n v hv). }
        assert (hnd3 : List.NoDup (fb ++ fr ++ fs)).
        { eapply NoDup_app; [eapply fresh_list_nodup | |].
          - eapply NoDup_app; [eapply fresh_list_nodup | eapply fresh_list_nodup |].
            intros a ha hb. eapply (hfs a hb).
            eapply List.in_or_app; right. eapply List.in_or_app; right. exact ha.
          - intros a ha hb. eapply List.in_app_or in hb. destruct hb as [hb | hb].
            + eapply (hfr a hb). eapply List.in_or_app; right. exact ha.
            + eapply (hfs a hb). eapply List.in_or_app; right.
              eapply List.in_or_app; left. exact ha. }
        assert (hbn : ∀ v, List.In v (bit_names (fun i => List.nth i fb default_name)
            (fun i => List.nth i fr default_name) (fun i => List.nth i fs default_name) n) ->
            ~ List.In v used).
        { intros v hv. eapply (Permutation_in _ hperm) in hv.
          eapply List.in_app_or in hv. destruct hv as [hv | hv]; [eapply hfb; exact hv |].
          eapply List.in_app_or in hv. destruct hv as [hv | hv].
          - intro hu'. eapply (hfr v hv). eapply List.in_or_app; left; exact hu'.
          - intro hu'. eapply (hfs v hv). eapply List.in_or_app; left; exact hu'. }
        assert (hCmap : List.map (fun i => List.nth i fC default_name) (List.seq 0 n) = fC).
        { eapply map_nth_seq_len. eapply fresh_list_length. }
        destruct (range_complete (vdec := vdecV)
          (fun i => List.nth i fb default_name) (fun i => List.nth i fr default_name)
          (fun i => List.nth i fs default_name) (fun i => List.nth i fC default_name)
          genv penv (Hvec := Hvec) An Bn x u k wenv hu hk hwx) as (genv' & wenv' & hg & hw & hd).
        { fold n. constructor; [intro h; eapply (hbn x h); exact hx |].
          eapply Permutation_NoDup; [eapply Permutation_sym; exact hperm | exact hnd3]. }
        { fold n. rewrite hCmap. eapply fresh_list_nodup. }
        { fold n. intros i hi.
          assert (hin : List.In (List.nth i fC default_name) fC).
          { eapply List.nth_In. unfold fC. rewrite (fresh_list_length V HV _ n). exact hi. }
          split; intro h; eapply (hfC _ hin); eapply List.in_or_app; left;
          rewrite h; assumption. }
        exists genv', wenv'. split; [| split].
        + intros P hP. eapply hg. fold n. rewrite hCmap. intro h. eapply (hfC P h).
          eapply List.in_or_app; left; exact hP.
        + intros v hv. eapply hw. fold n. intro h. eapply (hbn v h). exact hv.
        + exact hd.
      Qed.

      (** The list version of completeness, for the children of a
          threshold.

          The [List.Forall] hypothesis supplies one completeness
          statement per child.  The children are elaborated in
          sequence, so the environments are extended in sequence too:
          first for the head, then for the tail on top of that.  When
          the tail extends the environments again, the head's core
          statement must still hold, and it does, because the tail
          touches only names that were fresh at that point while
          [elab_names] bounds the head's names by the used-name list
          the tail started from.  That is exactly where the name
          lemmas earn their keep.

          Unflagged children require nothing and are passed over. *)
      Lemma elab_list_complete :
        ∀ (l : list sstmt),
        List.Forall (fun s => ∀ (used used' : list V) (c : stmtC)
            (genv : V -> G) (wenv : V -> F),
          elab used s = Some (c, used') ->
          List.incl (snames s) used ->
          List.In An used -> List.In Bn used ->
          sstmt_denote genv wenv s ->
          ∃ (genv' : V -> G) (wenv' : V -> F),
            (∀ P, List.In P used -> genv' P = genv P) ∧
            (∀ v, List.In v used -> wenv' v = wenv v) ∧
            stmt_denoteC genv' penv wenv' c) l ->
        ∀ (used used' : list V) (cs : list stmtC) (bs : list bool)
          (genv : V -> G) (wenv : V -> F),
        elab_list used l = Some (cs, used') ->
        List.incl (snames_of_list l) used ->
        List.In An used -> List.In Bn used ->
        sflagged genv wenv l bs ->
        ∃ (genv' : V -> G) (wenv' : V -> F),
          (∀ P, List.In P used -> genv' P = genv P) ∧
          (∀ v, List.In v used -> wenv' v = wenv v) ∧
          @flagged_denote F add mul opp G gid gop gpow V genv' penv wenv' cs bs.
      Proof.
        intros l hall.
        induction hall as [| s l hs hl ih]; intros used used' cs bs genv wenv hel hsn hA hB hsf;
        cbn [elab_list] in hel.
        + inversion hel; subst. exists genv, wenv.
          split; [reflexivity | split; [reflexivity |]]. destruct bs; exact I.
        + destruct (elab used s) as [[c u1] |] eqn:h1; [| congruence].
          destruct (elab_list u1 l) as [[cs2 u2] |] eqn:h2; [| congruence].
          inversion hel; subst; clear hel.
          unfold snames_of_list in hsn; cbn [List.flat_map] in hsn.
          pose proof (elab_used_incl s used u1 c h1) as hinc1.
          assert (hsn_s : List.incl (snames s) used).
          { intros v hv; eapply hsn; eapply List.in_or_app; left; exact hv. }
          assert (hsn_l : List.incl (snames_of_list l) used).
          { intros v hv; eapply hsn; eapply List.in_or_app; right; exact hv. }
          destruct bs as [| b bs].
          - exists genv, wenv. split; [reflexivity | split; [reflexivity | exact I]].
          - cbn [sflagged] in hsf. destruct hsf as (hb & hrest).
            destruct b.
            * (* the child holds: elaborate it first, then the rest on top of it *)
              destruct (hs used u1 c genv wenv h1 hsn_s hA hB hb) as (g1 & w1 & hg1 & hw1 & hd1).
              assert (hrest1 : sflagged g1 w1 l bs).
              { eapply (sflagged_ext l bs genv g1 wenv w1); [| | exact hrest];
                intros v hv; symmetry; [eapply hg1 | eapply hw1]; eapply hsn_l; exact hv. }
              destruct (ih u1 used' cs2 bs g1 w1 h2 (List.incl_tran hsn_l hinc1)
                (hinc1 _ hA) (hinc1 _ hB) hrest1) as (g2 & w2 & hg2 & hw2 & hf2).
              destruct (elab_names s used u1 c h1 hsn_s hA hB) as (hvc & hpc).
              exists g2, w2. split; [| split].
              { intros P hP. rewrite (hg2 P (hinc1 _ hP)). eapply hg1; exact hP. }
              { intros v hv. rewrite (hw2 v (hinc1 _ hv)). eapply hw1; exact hv. }
              { cbn [flagged_denote]. split; [| exact hf2].
                eapply (stmt_denote_genv_ext penv g1 g2 w2 c).
                { intros P hP. symmetry. eapply hg2. eapply hpc; exact hP. }
                eapply (stmt_denote_ext g1 penv c w1 w2); [| exact hd1].
                intros v hv. symmetry. eapply hw2. eapply hvc; exact hv. }
            * destruct (ih u1 used' cs2 bs genv wenv h2 (List.incl_tran hsn_l hinc1)
                (hinc1 _ hA) (hinc1 _ hB) hrest) as (g2 & w2 & hg2 & hw2 & hf2).
              exists g2, w2. split; [| split].
              { intros P hP. eapply hg2, hinc1, hP. }
              { intros v hv. eapply hw2, hinc1, hv. }
              { cbn [flagged_denote]. split; [exact I | exact hf2]. }
      Qed.

      (** Completeness of elaboration.

          If the source names of [s] and the two Pedersen bases all
          lie in [used], and the environments satisfy the surface
          statement [s], then there are environments satisfying the
          compiled statement that agree with the original ones
          throughout [used].

          The two agreement conditions are the precise sense in which
          elaboration changes nothing the user can see: every point
          the user named keeps its value, every private scalar the
          user named keeps its value, and only names that were fresh
          receive new ones.

          The proof is an induction on [s] with [sstmt_ind'].
          Equations need no extension at all.  The nonzero and range
          cases are the two lemmas just above.  The [TLet] case is
          the subtle one: the induction hypothesis is applied to the
          body under the witness in which the bound name holds the
          value of its defining form, and the resulting witness is
          then patched to restore that name's original value.  That
          is legitimate because [subst_stmt_vars] says the bound name
          no longer occurs in the substituted body.  [TAnd] extends
          twice and repairs the first half with [stmt_denote_ext] and
          [stmt_denote_genv_ext] together with [elab_names]; [TOr]
          needs only one side; [TThresh] defers to
          [elab_list_complete]. *)
      Theorem elab_complete :
        ∀ (s : sstmt) (used used' : list V) (c : stmtC)
          (genv : V -> G) (wenv : V -> F),
        elab used s = Some (c, used') ->
        List.incl (snames s) used ->
        List.In An used -> List.In Bn used ->
        sstmt_denote genv wenv s ->
        ∃ (genv' : V -> G) (wenv' : V -> F),
          (∀ P, List.In P used -> genv' P = genv P) ∧
          (∀ v, List.In v used -> wenv' v = wenv v) ∧
          stmt_denoteC genv' penv wenv' c.
      Proof.
        intros s.
        induction s as [a b | e | x u | x e body ih | a b iha ihb | a b iha ihb | t l ihl]
          using sstmt_ind'; intros used used' c genv wenv he hsn hA hB hd.
        + cbn [elab] in he.
          destruct (elab_g a) as [pa |] eqn:ha; [| congruence].
          destruct (elab_g b) as [pb |] eqn:hb; [| congruence].
          inversion he; subst; clear he.
          exists genv, wenv. split; [reflexivity | split; [reflexivity |]].
          cbn [stmt_denote]. constructor; [| constructor].
          eapply (elab_eq_denote genv wenv a b pa pb ha hb). exact hd.
        + cbn [elab] in he.
          destruct (lin_of e) as [[off cys] |] eqn:hl; [| congruence].
          destruct cys as [| [coeff x] [| ? ?]]; try congruence.
          destruct (fresh_list used 4) as [| Cn [| j [| sn [| r [| ? ?]]]]] eqn:hfl; try congruence.
          inversion he; subst; clear he.
          cbn [snames] in hsn.
          assert (hx : List.In x used).
          { eapply hsn. eapply (lin_of_vars e _ hl). unfold lin_vars; cbn. left; reflexivity. }
          eapply (elab_neq_complete used x Cn j sn r coeff off genv wenv hfl hx hA hB).
          cbn [sstmt_denote] in hd. rewrite <-(lin_of_denote wenv e _ hl) in hd.
          unfold lin_denote in hd; cbn [fst snd List.fold_right] in hd.
          assert (heq : pevalC off + (pevalC coeff * wenv x + zero) =
            pevalC coeff * wenv x + pevalC off). { field. }
          rewrite heq in hd. exact hd.
        + cbn [elab] in he.
          destruct (2 <=? u)%nat eqn:hu; [| congruence].
          destruct (elab_range used x u) as [cr ur] eqn:hr.
          inversion he; subst; clear he.
          cbn [snames] in hsn.
          eapply Nat.leb_le in hu.
          eapply (elab_range_complete used used' x u c genv wenv hr hu);
          [eapply hsn; left; reflexivity | exact hA | exact hB | exact hd].
        + cbn [elab] in he.
          destruct (lin_of e) as [l |] eqn:hl; [| congruence].
          destruct (elab used body) as [[cb u1] |] eqn:hb; [| congruence].
          destruct (List.existsb (veqb x) (lin_vars l)) eqn:hex; [congruence |].
          inversion he; subst; clear he.
          cbn [snames] in hsn. cbn [sstmt_denote] in hd.
          assert (hxl : ∀ v, List.In v (lin_vars l) -> v <> x).
          { intros v hv heq. subst v.
            assert (h : List.existsb (veqb x) (lin_vars l) = true).
            { eapply List.existsb_exists. exists x. split; [exact hv | eapply veqb_refl]. }
            congruence. }
          assert (hxu : List.In x used). { eapply hsn; left; reflexivity. }
          (* the body's witness, built over x := value of the form *)
          set (w0 := overrideC wenv x (sdenote wenv e)) in hd.
          destruct (ih used used' cb genv w0 hb
            (ltac:(intros v hv; eapply hsn; right; eapply List.in_or_app; right; exact hv))
            hA hB hd) as (g1 & w1 & hg1 & hw1 & hd1).
          assert (hlin : lin_denoteC w1 l = sdenote wenv e).
          { rewrite <-(lin_of_denote wenv e l hl). eapply lin_denote_ext.
            intros v hv.
            rewrite hw1; [| eapply hsn; right; eapply List.in_or_app; left;
                            eapply (lin_of_vars e l hl); exact hv].
            unfold w0. eapply override_other. eapply hxl; exact hv. }
          assert (hwx : w1 x = lin_denoteC w1 l).
          { rewrite hlin, (hw1 x hxu). unfold w0. eapply override_same. }
          rewrite <-(subst_stmt_denote (vdec := vdecV) g1 penv (Hvec := Hvec) w1 x l cb hwx) in hd1.
          (* x itself is gone from the substituted body: restore its old value *)
          exists g1, (overrideC w1 x (wenv x)). split; [| split].
          - exact hg1.
          - intros v hv. destruct (vdecV v x) as [heq | hne].
            * subst v. eapply override_same.
            * rewrite override_other; [| exact hne]. rewrite (hw1 v hv).
              unfold w0. eapply override_other; exact hne.
          - eapply (stmt_denote_ext g1 penv _ w1); [| exact hd1].
            intros v hv. eapply subst_stmt_vars in hv. symmetry. eapply override_other.
            destruct hv as [hv | (_ & hv)]; [eapply hxl; exact hv | exact hv].
        + cbn [elab] in he.
          destruct (elab used a) as [[ca u1] |] eqn:ha; [| congruence].
          destruct (elab u1 b) as [[cb u2] |] eqn:hb; [| congruence].
          inversion he; subst; clear he.
          cbn [snames] in hsn. cbn [sstmt_denote] in hd. destruct hd as (hda & hdb).
          assert (hsa : List.incl (snames a) used).
          { intros v hv; eapply hsn; eapply List.in_or_app; left; exact hv. }
          assert (hsb : List.incl (snames b) used).
          { intros v hv; eapply hsn; eapply List.in_or_app; right; exact hv. }
          pose proof (elab_used_incl a used u1 ca ha) as hinc1.
          destruct (iha used u1 ca genv wenv ha hsa hA hB hda) as (g1 & w1 & hg1 & hw1 & hd1).
          assert (hdb1 : sstmt_denote g1 w1 b).
          { eapply (sstmt_denote_ext b genv g1 wenv w1); [| | exact hdb];
            intros v hv; symmetry; [eapply hg1 | eapply hw1]; eapply hsb; exact hv. }
          destruct (ihb u1 used' cb g1 w1 hb (List.incl_tran hsb hinc1)
            (hinc1 _ hA) (hinc1 _ hB) hdb1) as (g2 & w2 & hg2 & hw2 & hd2).
          destruct (elab_names a used u1 ca ha hsa hA hB) as (hva & hpa).
          exists g2, w2. split; [| split].
          - intros P hP. rewrite (hg2 P (hinc1 _ hP)). eapply hg1; exact hP.
          - intros v hv. rewrite (hw2 v (hinc1 _ hv)). eapply hw1; exact hv.
          - cbn [stmt_denote]. split; [| exact hd2].
            eapply (stmt_denote_genv_ext penv g1 g2 w2 ca).
            { intros P hP. symmetry. eapply hg2. eapply hpa; exact hP. }
            eapply (stmt_denote_ext g1 penv ca w1 w2); [| exact hd1].
            intros v hv. symmetry. eapply hw2. eapply hva; exact hv.
        + cbn [elab] in he.
          destruct (elab used a) as [[ca u1] |] eqn:ha; [| congruence].
          destruct (elab u1 b) as [[cb u2] |] eqn:hb; [| congruence].
          inversion he; subst; clear he.
          cbn [snames] in hsn. cbn [sstmt_denote] in hd.
          assert (hsa : List.incl (snames a) used).
          { intros v hv; eapply hsn; eapply List.in_or_app; left; exact hv. }
          assert (hsb : List.incl (snames b) used).
          { intros v hv; eapply hsn; eapply List.in_or_app; right; exact hv. }
          pose proof (elab_used_incl a used u1 ca ha) as hinc1.
          destruct hd as [hda | hdb].
          - destruct (iha used u1 ca genv wenv ha hsa hA hB hda) as (g1 & w1 & hg1 & hw1 & hd1).
            exists g1, w1. split; [exact hg1 | split; [exact hw1 |]].
            cbn [stmt_denote]. left; exact hd1.
          - destruct (ihb u1 used' cb genv wenv hb (List.incl_tran hsb hinc1)
              (hinc1 _ hA) (hinc1 _ hB) hdb) as (g2 & w2 & hg2 & hw2 & hd2).
            exists g2, w2. split; [| split].
            * intros P hP; eapply hg2, hinc1, hP.
            * intros v hv; eapply hw2, hinc1, hv.
            * cbn [stmt_denote]. right; exact hd2.
        + rewrite elab_thresh in he.
          destruct (elab_list used l) as [[cs u'] |] eqn:hl; [| congruence].
          inversion he; subst; clear he.
          rewrite snames_thresh in hsn.
          eapply sstmt_denote_thresh in hd. destruct hd as (bs & hlen & hcnt & hsf).
          destruct (elab_list_complete l ihl used used' cs bs genv wenv hl hsn hA hB hsf)
            as (g' & w' & hg & hw & hf).
          exists g', w'. split; [exact hg | split; [exact hw |]].
          eapply stmt_denote_thresh. exists bs.
          rewrite (elab_list_length l used used' cs hl).
          split; [exact hlen | split; [exact hcnt | exact hf]].
      Qed.

    End Proofs.

  End Sem.

End Surface.
