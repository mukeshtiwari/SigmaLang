From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef
  BinPos.
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

Import MonadNotation
  VectorNotations.

#[local] Open Scope monad_scope.

(** * LinearRelation: one proof for a whole system of linear group equations

    This file is the leaf of the compiler.  Every statement the
    compiler DSL can express is eventually reduced to the single
    protocol defined and proven here, which is due to Maurer.  The
    file Composition.v builds AND, OR and threshold statements on top
    of this leaf, and the file Crypto/Sigma.v contains the
    one-equation special case, the classical Schnorr protocol, that
    this file generalises.

    ** The statement being proven

    Two objects are public.  The first is a matrix [mat] of group
    elements, with [m] rows and [n] columns.  The second is a vector
    [pub] of [m] group elements, one per row.  The prover claims to
    know a vector [xs] of [n] field elements that solves the whole
    system at once, which in Rocq is written [mat_eval mat xs = pub].

    That secret vector is the witness.  A witness is the piece of
    information the prover has and the verifier does not, and the
    point of the protocol is to convince the verifier that the prover
    has one, without revealing anything about it.

    The group is written multiplicatively: [gop] is the group product,
    [gid] the neutral element, and [gpow g x] is [g] raised to the
    power [x], where the exponent [x] comes from the field [F].
    Reading [mat_eval] as "matrix times vector" is the right
    intuition, but every operation moves up one level.  In ordinary
    linear algebra an entry of a matrix-vector product is a sum of
    products of scalars; here it is a product of powers of group
    elements.  Sums become products, and products become
    exponentiations.

    ** The three moves of the protocol

    A sigma protocol is a three-message conversation between a prover
    and a verifier.

    - The announcement, also called the commitment, comes first.  The
      prover draws a fresh random vector [us] and sends
      [mat_eval mat us], the left-hand side of the system evaluated at
      that random vector instead of at the witness.  It pins the
      prover down to one particular [us] before any challenge is seen.
    - The challenge [c] comes second.  It is a single field element
      picked by the verifier.  The prover cannot predict it, and that
      unpredictability is what makes cheating hard.
    - The response comes third.  The prover sends [us + c * xs],
      computed entry by entry.  The random [us] hides the witness the
      way a one-time pad hides a message, so the response on its own
      says nothing about [xs].

    The verifier accepts when, for every row, that row evaluated at
    the response equals the announcement entry for the row multiplied
    by the public target of the row raised to the power [c].  This
    test is [verify_linear_relation_proof].  A transcript is the
    triple of announcement, challenge and response, that is, the
    written record of one run.

    ** What is proven about it

    - Completeness ([linear_relation_completeness]): an honest prover
      who really knows a witness always convinces the verifier.
      Nothing the verifier does can make an honest run fail.
    - Special soundness ([linear_relation_special_soundness]): from
      two accepting transcripts that share the same announcement but
      use two different challenges, one can compute an actual witness.
      A prover without a witness therefore cannot answer two different
      challenges, so a single accepting run is already strong
      evidence.
    - Special honest-verifier zero knowledge
      ([linear_relation_special_honest_verifier_zkp]): there is a
      simulator, a machine that gets no witness at all, whose output
      distribution is the same as the distribution of real
      transcripts.  Since transcripts produced without the witness
      look exactly like real ones, a real transcript cannot be leaking
      anything about the witness.

    ** Why this single leaf is enough

    Choosing [m] and [n] and filling in the matrix recovers all the
    usual protocols: Schnorr is [m = 1] with [n = 1], Okamoto is
    [m = 1], Chaum-Pedersen and equality of discrete logarithms are
    [n = 1], and Pedersen commitment openings, Diffie-Hellman tuples
    and public linear constraints on committed values are all specific
    matrices.  The section [Instances] at the end of the file proves
    each of these correspondences, so the compiler can emit a matrix
    and rely on the proofs here. *)
Section LinearRelation.

  (** ** Parameters

      The whole file is parametric in an abstract field and an
      abstract group, so nothing below depends on a particular curve
      or a particular prime.

      The field [F] supplies the exponents.  It is given as its
      carrier together with its operations: the constants [zero] and
      [one], the four binary operations [add], [mul], [sub] and [div],
      negation [opp], multiplicative inverse [inv], and [Fdec], which
      decides whether two field elements are equal. *)
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}.

  (** The group [G] supplies the public values.  It is written
      multiplicatively: [gid] is the neutral element, [gop] the
      product, [ginv] the inverse, and [gpow g x] is [g] raised to the
      power [x], with [x] taken from the field.  [Gdec] decides
      equality of group elements, which is what lets the verifier be a
      boolean-valued function that can actually be run. *)
  Context
    {G : Type}
    {gid : G}
    {ginv : G -> G}
    {gop : G -> G -> G}
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}.

  (** Infix shorthands used throughout the file.  The caret is
      exponentiation of a group element by a field element, that is
      [gpow], and the four arithmetic symbols denote the field
      operations [mul], [div], [add] and [sub], never the operations
      of [nat]. *)
  #[local] Infix "^" := gpow.
  #[local] Infix "*" := mul.
  #[local] Infix "/" := div.
  #[local] Infix "+" := add.
  #[local] Infix "-" := sub.

  (** Shorthand for building a transcript from its three parts, in
      the order announcement, challenge, response.  [mk_sigma] is the
      record of Crypto/Sigma.v that holds the three messages of a
      run. *)
  #[local] Notation "( a ; c ; r )" := (mk_sigma _ _ _ a c r).

  (** ** The protocol

      Definitions only: how a statement is evaluated, how an honest
      prover builds a transcript, how the simulator builds one without
      a witness, what the verifier checks, and the two probability
      distributions that the zero-knowledge statement compares. *)
  Section Def.

    (** Evaluate a single linear equation.

        A row of the matrix is a vector of [n] group elements, the
        bases of that equation, and [xs] is a vector of [n] field
        elements, the unknowns.  [row_eval row xs] raises each base to
        the exponent sitting in the matching position of [xs] and
        multiplies all the results together, starting from the neutral
        element [gid].

        This is one entry of a matrix-vector product carried over to a
        multiplicative group.  Where linear algebra would add the
        products of coefficients and unknowns, here we multiply the
        powers of bases and unknowns.  A row of width zero evaluates
        to [gid], the group analogue of an empty sum being zero. *)
    Definition row_eval {n : nat}
      (row : Vector.t G n) (xs : Vector.t F n) : G :=
      Vector.fold_right gop (zip_with gpow row xs) gid.

    (** Evaluate the whole system of equations.

        [mat] has [m] rows, each of width [n].  [mat_eval mat xs]
        applies [row_eval] to every row with the same vector [xs] of
        unknowns, producing a vector of [m] group elements.  The
        statement of the protocol is that this vector equals the
        public vector [pub], so one shared witness has to satisfy all
        [m] equations simultaneously. *)
    Definition mat_eval {m n : nat}
      (mat : Vector.t (Vector.t G n) m) (xs : Vector.t F n) :
      Vector.t G m :=
      Vector.map (fun row => row_eval row xs) mat.

    (** The identity-shaped matrix built from a single base [g].

        [diag_mat n g] is the square matrix of size [n] whose row [i]
        holds [g] in column [i] and the neutral element [gid]
        everywhere else.  Since [gid] raised to any power is still
        [gid], the off-diagonal entries contribute nothing, so row [i]
        evaluates to [g] raised to the [i]-th unknown.  That is the
        content of [mat_eval_diag].

        It exists so that a family of [n] independent equations that
        all use the same base, such as one commitment per secret
        value, can be written as one block of a single matrix instead
        of [n] separate statements. *)
    Fixpoint diag_mat (n : nat) (g : G) :
      Vector.t (Vector.t G n) n.
    Proof. 
      refine 
        match n with
        | 0 => []
        | S n' =>
          (g :: Vector.const gid n') ::
          Vector.map (fun row => gid :: row) (diag_mat n' g)
        end.
    Defined.

    (** The transcript an honest prover produces.

        The arguments are the public matrix [mat], the witness [xs],
        the prover's fresh randomness [us], and the verifier's
        challenge [c].  The three parts of the result are the three
        messages of the run:

        - the announcement is [mat_eval mat us], the system evaluated
          at the randomness rather than at the witness;
        - the challenge part is the one-element vector holding [c];
        - the response is [us + c * xs], taken position by position.

        Each entry of [us] is used once and never reused, so it hides
        the matching entry of the witness completely: for a fixed
        challenge, a uniformly random [us] makes the response
        uniformly random too. *)
    Definition construct_linear_relation_real_proof {m n : nat}
      (mat : Vector.t (Vector.t G n) m)
      (xs us : Vector.t F n) (c : F) : @sigma_proto F G m 1 n :=
      (mat_eval mat us; [c];
        zip_with (fun u x => u + c * x) us xs).

    (** The transcript the simulator produces, using no witness.

        The simulator is the object that makes zero knowledge precise.
        It is given only public data, here the matrix [mat], the
        public targets [pub] and the challenge [c], and it must output
        a transcript the verifier would accept.

        It works by running the protocol backwards.  Instead of
        picking the randomness first and deriving the response, it
        picks the response [zs] first, at random, and then solves the
        verification equation for the announcement: row [j] of the
        announcement is set to row [j] evaluated at [zs], multiplied
        by the public target of row [j] raised to the power [opp c].
        That extra factor cancels exactly the factor the verifier will
        introduce, so the check succeeds by construction.  This is
        [linear_relation_simulator_completeness].

        This is not a break of the protocol, because the simulator is
        handed the challenge in advance.  A real verifier picks the
        challenge only after seeing the announcement, and then the
        trick is unavailable. *)
    Definition construct_linear_relation_simulator_proof {m n : nat}
      (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m)
      (zs : Vector.t F n) (c : F) : @sigma_proto F G m 1 n :=
      (zip_with (fun row p => gop (row_eval row zs) (p ^ (opp c)))
        mat pub; [c]; zs).

    (** The verifier's test, written as a boolean function.

        Given the public matrix [mat], the public targets [pub] and a
        transcript [pf] made of an announcement, a challenge and a
        response, the verifier checks one equation per row: that row
        evaluated at the response must equal the announcement entry
        for the row, multiplied by the public target of the row raised
        to the challenge.

        The three vectors are zipped together so that row [j], target
        [j] and announcement entry [j] are checked as one triple, and
        [vector_forallb] demands that every row passes.  Equality of
        group elements is decided by [Gdec], which is why the answer
        is a plain boolean and the verifier is executable.

        Why this is the right test: the honest response is
        [us + c * xs], and a row evaluated at it splits into the row
        evaluated at [us], which is exactly the announcement, times
        the row evaluated at [xs] raised to [c], which is the public
        target raised to [c] precisely when the statement is true.
        That splitting is [row_eval_response]. *)
    Definition verify_linear_relation_proof {m n : nat}
      (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m)
      (pf : @sigma_proto F G m 1 n) : bool :=
      match pf with
      | (comm; cha; res) =>
        vector_forallb (fun '(row, (p, cm)) =>
          match Gdec (row_eval row res) (gop cm (p ^ (hd cha))) with
          | left _ => true
          | right _ => false
          end)
        (zip_with pair mat (zip_with pair pub comm))
      end.

    (** The distribution of real transcripts.

        Zero knowledge compares distributions rather than single runs,
        so the prover's randomness has to be modelled explicitly.  The
        list [lf] enumerates the field elements that may be drawn, and
        [Hlfn] records that it is not empty.  The vector [us] is
        obtained by taking [n] independent uniform samples from [lf];
        uniform means every element of [lf] is equally likely, so all
        possible vectors carry the same probability.  The transcript
        returned is the honest one built by
        [construct_linear_relation_real_proof]. *)
    Definition linear_relation_real_distribution {m n : nat}
      (lf : list F) (Hlfn : lf <> List.nil)
      (mat : Vector.t (Vector.t G n) m)
      (xs : Vector.t F n) (c : F) :
      dist (@sigma_proto F G m 1 n) :=
      us <- repeat_dist_ntimes_vector
        (uniform_with_replacement lf Hlfn) n ;;
      Ret (construct_linear_relation_real_proof mat xs us c).

    (** The distribution of simulated transcripts.

        The same random experiment as
        [linear_relation_real_distribution], except that the [n]
        uniform samples are used as the response [zs] and the
        transcript is assembled by the simulator.  Crucially, this
        definition never mentions a witness. *)
    Definition linear_relation_simulator_distribution {m n : nat}
      (lf : list F) (Hlfn : lf <> List.nil)
      (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m)
      (c : F) : dist (@sigma_proto F G m 1 n) :=
      zs <- repeat_dist_ntimes_vector
        (uniform_with_replacement lf Hlfn) n ;;
      Ret (construct_linear_relation_simulator_proof mat pub zs c).

  End Def.

  (** ** Properties of the protocol

      First two bookkeeping lemmas that translate the boolean verifier
      into a family of group equations and back; then the algebraic
      lemmas about [row_eval] and [mat_eval]; then completeness,
      special soundness and zero knowledge; and finally the instances
      that show which classical protocols this one subsumes. *)
  Section Proofs.

    (** The verifier accepted, therefore every row equation holds.

        This unpacks the boolean test into usable mathematics.  If
        [verify_linear_relation_proof] returned [true] on the
        transcript made of announcement [comm], challenge [c] and
        response [res], then for every row index [i] the group
        equation of that row holds exactly: the row evaluated at the
        response equals the announcement entry times the public target
        raised to [c].

        It is true because the boolean test is literally a conjunction
        over all rows of those equalities, decided by [Gdec]; the
        proof only has to see through [vector_forallb] and the
        zipping.  Every later proof that starts from an accepting run
        passes through this lemma. *)
    Theorem verify_linear_relation_forward :
      ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m)
        (pub comm : Vector.t G m) (c : F) (res : Vector.t F n),
      verify_linear_relation_proof mat pub (comm; [c]; res) = true ->
      ∀ (i : Fin.t m),
        row_eval (nth mat i) res = gop (nth comm i) ((nth pub i) ^ c).
    Proof.
      intros * ha i.
      unfold verify_linear_relation_proof in ha.
      rewrite vector_forallb_correct in ha.
      specialize (ha i).
      rewrite !nth_zip_with in ha.
      rewrite dec_true in ha.
      exact ha.
    Qed.

    (** The converse direction: if every row equation holds, the
        verifier accepts.

        This is the direction used by completeness and by simulator
        correctness.  To show that a transcript is accepted it is then
        enough to check one group identity per row, which is ordinary
        algebra, instead of reasoning about a boolean function. *)
    Theorem verify_linear_relation_backward :
      ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m)
        (pub comm : Vector.t G m) (c : F) (res : Vector.t F n),
      (∀ (i : Fin.t m),
        row_eval (nth mat i) res = gop (nth comm i) ((nth pub i) ^ c)) ->
      verify_linear_relation_proof mat pub (comm; [c]; res) = true.
    Proof.
      intros * ha.
      unfold verify_linear_relation_proof.
      rewrite vector_forallb_correct.
      intro i.
      rewrite !nth_zip_with, dec_true.
      exact (ha i).
    Qed.

    (** From here on the field and the group are assumed to form a
        vector space.  That assumption is what makes exponent
        arithmetic behave: the group is commutative, raising a base to
        a sum of exponents multiplies the two powers, raising a power
        to a power multiplies the exponents, and the neutral element
        absorbs every exponent.  All the algebraic lemmas below rest
        on it. *)
    Context
      {Hvec : @vector_space F (@eq F) zero one add mul sub
        div opp inv G (@eq G) gid ginv gop gpow}.
    (** Register the field with the [field] tactic, so that routine
        identities about exponents can be discharged automatically. *)
    Add Field field : (@field_theory_for_stdlib_tactic F
      eq zero one opp add mul sub inv div vector_space_field).

    (** Rearranging a product of four group elements.

        In a commutative group the two middle factors of
        [gop (gop a b) (gop c d)] may be exchanged, turning it into
        [gop (gop a c) (gop b d)].  This small fact is used again and
        again below, whenever two parallel products have to be matched
        up factor by factor.

        The same lemma appears in Okamoto.v and PedLinearRel.v; it is
        repeated here so that this file need not import those
        developments for a single rearrangement. *)
    Theorem gop_simp : ∀ (a b c d : G),
      gop (gop a b) (gop c d) = gop (gop a c) (gop b d).
    Proof.
      intros *.
      rewrite <-!associative.
      setoid_rewrite commutative at 2.
      rewrite <-!associative.
      setoid_rewrite commutative at 3.
      reflexivity.
    Qed.

    (** Evaluating a row one entry at a time.

        Putting a new base [g] at the front of a row and a new
        exponent [x] at the front of the unknowns multiplies the old
        value by [g] raised to [x].  This is the computation rule that
        every induction on the width of a row relies on. *)
    Lemma row_eval_cons : ∀ (n : nat) (g : G) (row : Vector.t G n)
      (x : F) (xs : Vector.t F n),
      row_eval (g :: row) (x :: xs) = gop (g ^ x) (row_eval row xs).
    Proof.
      intros *.
      unfold row_eval; cbn.
      reflexivity.
    Qed.

    (** A row of width zero evaluates to the neutral element [gid],
        the empty product.  This is the base case of the same
        inductions. *)
    Lemma row_eval_nil : ∀ (row : Vector.t G 0) (xs : Vector.t F 0),
      row_eval row xs = gid.
    Proof.
      intros *.
      rewrite (vector_inv_0 row), (vector_inv_0 xs).
      reflexivity.
    Qed.

    (** The key algebraic fact behind completeness.

        Evaluating a row at the honest response [us + c * xs] gives
        the row evaluated at [us], multiplied by the row evaluated at
        [xs] and then raised to the power [c].

        The reason is that each factor splits on its own: a base
        raised to [u + c * x] is the base raised to [u], times the
        base raised to [x] and then raised to [c].  In a commutative
        group all the left halves can then be collected on one side
        and all the right halves on the other.  The proof is an
        induction on the width of the row, with [gop_simp] doing that
        regrouping at each step.

        Read inside the protocol this says: the row evaluated at the
        response equals the announcement times the public target
        raised to the challenge, which is precisely the equation the
        verifier checks. *)
    Lemma row_eval_response :
      ∀ (n : nat) (row : Vector.t G n) (us xs : Vector.t F n) (c : F),
      row_eval row (zip_with (fun u x => u + c * x) us xs) =
      gop (row_eval row us) ((row_eval row xs) ^ c).
    Proof.
      induction n as [|n ihn].
      +
        intros *.
        rewrite (vector_inv_0 row), (vector_inv_0 us), (vector_inv_0 xs).
        unfold row_eval; cbn.
        rewrite vid_identity, left_identity.
        reflexivity.
      +
        intros *.
        destruct (vector_inv_S row) as (rh & rt & ha).
        destruct (vector_inv_S us) as (uh & ut & hb).
        destruct (vector_inv_S xs) as (xh & xt & hc).
        subst.
        specialize (ihn rt ut xt c).
        unfold row_eval in ihn |- *; cbn.
        rewrite ihn.
        assert (hd : uh + c * xh = uh + xh * c). field.
        rewrite hd; clear hd.
        rewrite smul_distributive_fadd,
          smul_associative_fmul,
          smul_distributive_vadd, gop_simp.
        reflexivity.
    Qed.

    (** The key algebraic fact behind special soundness.

        Take two response vectors [zs₁] and [zs₂] and a scalar [k],
        and form the vector whose entries are the differences of the
        two responses, each multiplied by [k].  Evaluating a row at
        that vector gives the quotient of the two separate
        evaluations, raised to the power [k].  Quotient here means the
        group product with the inverse, since the group is written
        multiplicatively.

        In other words, subtraction in the exponent becomes division
        in the group, and multiplication in the exponent becomes
        raising to a power.  The proof is again an induction on the
        width of the row, with [gop_simp] regrouping the factors.

        This is the lemma that turns the informal step "divide the two
        verification equations" into a statement about a concrete
        candidate witness. *)
    Lemma row_eval_sub_scale :
      ∀ (n : nat) (row : Vector.t G n) (zs₁ zs₂ : Vector.t F n) (k : F),
      row_eval row (zip_with (fun z₁ z₂ => (z₁ - z₂) * k) zs₁ zs₂) =
      (gop (row_eval row zs₁) (ginv (row_eval row zs₂))) ^ k.
    Proof.
      induction n as [|n ihn].
      +
        intros *.
        rewrite (vector_inv_0 row), (vector_inv_0 zs₁), (vector_inv_0 zs₂).
        unfold row_eval; cbn.
        rewrite group_inv_id, left_identity, vid_identity.
        reflexivity.
      +
        intros *.
        destruct (vector_inv_S row) as (rh & rt & ha).
        destruct (vector_inv_S zs₁) as (zh₁ & zt₁ & hb).
        destruct (vector_inv_S zs₂) as (zh₂ & zt₂ & hc).
        subst.
        specialize (ihn rt zt₁ zt₂ k).
        unfold row_eval in ihn |- *; cbn.
        rewrite ihn.
        rewrite smul_associative_fmul.
        rewrite ring_sub_definition.
        rewrite smul_distributive_fadd.
        rewrite <-connection_between_vopp_and_fopp.
        rewrite <-smul_distributive_vadd.
        rewrite group_inv_flip.
        rewrite gop_simp.
        f_equal.
        f_equal.
        rewrite commutative.
        reflexivity.
    Qed.

    (** ** Building matrices out of blocks

        The compiler does not write matrices by hand; it assembles
        them from pieces.  The lemmas in this group say how
        [row_eval] and [mat_eval] behave when rows are concatenated,
        when matrices are stacked, when a column of neutral elements
        is inserted, and when a public coefficient is folded into a
        base.  Together they let a structured statement, such as a
        list of commitments together with a linear constraint on the
        committed values, be rewritten as one flat matrix
        equation. *)

    (** A row made entirely of the neutral element evaluates to the
        neutral element, whatever the exponents are.  Such a row
        carries no information, and this is how an unknown that does
        not occur in an equation is encoded: its column in that row is
        [gid]. *)
    Lemma row_eval_const_gid :
      ∀ (n : nat) (xs : Vector.t F n),
      row_eval (Vector.const gid n) xs = gid.
    Proof.
      induction n as [|n ihn].
      +
        intros *.
        rewrite (vector_inv_0 xs).
        reflexivity.
      +
        intros *.
        destruct (vector_inv_S xs) as (xh & xt & ha); subst.
        specialize (ihn xt).
        unfold row_eval in ihn |- *; cbn.
        rewrite vid_identity, left_identity.
        exact ihn.
    Qed.

    (** Splitting a row into two halves.

        If a row is the concatenation of [r₁] and [r₂], and the
        unknowns are correspondingly the concatenation of [x₁] and
        [x₂], then the row evaluates to the product of the two halves
        evaluated separately.  A product over a disjoint union of
        positions is the product of the two partial products.  This is
        what lets one equation mention two independent blocks of
        witnesses. *)
    Lemma row_eval_app :
      ∀ (n₁ n₂ : nat) (r₁ : Vector.t G n₁) (r₂ : Vector.t G n₂)
        (x₁ : Vector.t F n₁) (x₂ : Vector.t F n₂),
      row_eval (r₁ ++ r₂) (x₁ ++ x₂) =
      gop (row_eval r₁ x₁) (row_eval r₂ x₂).
    Proof.
      induction n₁ as [|n₁ ihn].
      +
        intros *.
        rewrite (vector_inv_0 r₁), (vector_inv_0 x₁).
        unfold row_eval; cbn.
        rewrite left_identity.
        reflexivity.
      +
        intros *.
        destruct (vector_inv_S r₁) as (rh & rt & ha).
        destruct (vector_inv_S x₁) as (xh & xt & hb).
        subst.
        specialize (ihn n₂ rt r₂ xt x₂).
        unfold row_eval in ihn |- *; cbn.
        rewrite ihn, associative.
        reflexivity.
    Qed.

    (** Adding a dead column changes nothing.

        Prefixing every row of a matrix with the neutral element, and
        prefixing the unknowns with a new value [x], leaves the result
        of [mat_eval] unchanged.  The new column contributes [gid] to
        each row, so the new unknown is simply not constrained by this
        matrix.  This is the step that lets [diag_mat] be built by
        recursion, one column at a time. *)
    Lemma mat_eval_cons_col_gid :
      ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m)
        (x : F) (xs : Vector.t F n),
      mat_eval (Vector.map (fun row => gid :: row) mat) (x :: xs) =
      mat_eval mat xs.
    Proof.
      induction m as [|m ihm].
      +
        intros *.
        rewrite (vector_inv_0 mat).
        reflexivity.
      +
        intros *.
        destruct (vector_inv_S mat) as (rh & rt & ha); subst.
        specialize (ihm n rt x xs).
        unfold mat_eval in ihm |- *; cbn.
        f_equal.
        ++
          unfold row_eval; cbn.
          rewrite vid_identity, left_identity.
          reflexivity.
        ++
          exact ihm.
    Qed.

    (** What the identity-shaped matrix computes.

        [mat_eval (diag_mat n g) xs] is the vector of powers of [g],
        one per unknown: row [i] yields [g] raised to the [i]-th entry
        of [xs].  The off-diagonal entries are [gid] and drop out, by
        [row_eval_const_gid] and [mat_eval_cons_col_gid].

        So a family of [n] unrelated equations, each saying that some
        public element is [g] raised to some secret, is exactly one
        [diag_mat] block. *)
    Lemma mat_eval_diag :
      ∀ (n : nat) (g : G) (xs : Vector.t F n),
      mat_eval (diag_mat n g) xs = Vector.map (gpow g) xs.
    Proof.
      induction n as [|n ihn].
      +
        intros *.
        rewrite (vector_inv_0 xs).
        reflexivity.
      +
        intros *.
        destruct (vector_inv_S xs) as (xh & xt & ha); subst.
        cbn; f_equal.
        ++
          pose proof (row_eval_const_gid n xt) as hb.
          unfold row_eval in hb |- *; cbn.
          rewrite hb, right_identity.
          reflexivity.
        ++
          pose proof (mat_eval_cons_col_gid n n (diag_mat n g) xh xt) as hb.
          specialize (ihn g xt).
          unfold mat_eval in hb, ihn |- *.
          rewrite hb, ihn.
          reflexivity.
    Qed.

    (** How a linear constraint on the secrets becomes a single row.

        Suppose the statement contains a constraint with public
        coefficients [αs] on the secret values [vs], of the form "the
        sum of each coefficient times the matching value equals some
        public target".  Build the row whose [i]-th base is [g] raised
        to the [i]-th public coefficient.  Then evaluating that row at
        [vs] gives [g] raised to that whole weighted sum.

        The reason is the two exponent laws: raising [g] to a
        coefficient and then to a value is the same as raising [g] to
        their product, and multiplying powers of one and the same [g]
        adds the exponents.  So a constraint about field arithmetic
        becomes one group equation, whose right-hand side is [g]
        raised to the public target.  The compiler applies this
        transformation to every public scalar that appears in a
        statement. *)
    Lemma row_eval_pow_row :
      ∀ (n : nat) (g : G) (αs vs : Vector.t F n),
      row_eval (Vector.map (gpow g) αs) vs =
      g ^ (fold_right (fun '(α, v) acc => α * v + acc)
        (zip_with pair αs vs) zero).
    Proof.
      induction n as [|n ihn].
      +
        intros *.
        rewrite (vector_inv_0 αs), (vector_inv_0 vs).
        unfold row_eval; cbn.
        rewrite field_zero.
        reflexivity.
      +
        intros *.
        destruct (vector_inv_S αs) as (αh & αt & ha).
        destruct (vector_inv_S vs) as (vh & vt & hb).
        subst.
        specialize (ihn g αt vt).
        unfold row_eval in ihn |- *; cbn.
        rewrite smul_distributive_fadd, ihn.
        f_equal.
        rewrite <-smul_associative_fmul.
        reflexivity.
    Qed.

    (** Stacking two matrices stacks their results.

        Two systems over the same unknowns can be written one above
        the other, and evaluating the tall matrix is the same as
        evaluating each block and concatenating the answers.  This is
        how a conjunction of two statements over one witness vector
        becomes a single matrix. *)
    Lemma mat_eval_app_rows :
      ∀ (m₁ m₂ n : nat) (M₁ : Vector.t (Vector.t G n) m₁)
        (M₂ : Vector.t (Vector.t G n) m₂) (xs : Vector.t F n),
      mat_eval (M₁ ++ M₂) xs = mat_eval M₁ xs ++ mat_eval M₂ xs.
    Proof.
      induction m₁ as [|m₁ ihm].
      +
        intros *.
        rewrite (vector_inv_0 M₁).
        reflexivity.
      +
        intros *.
        destruct (vector_inv_S M₁) as (rh & rt & ha); subst.
        specialize (ihm m₂ n rt M₂ xs).
        unfold mat_eval in ihm |- *; cbn.
        rewrite ihm.
        reflexivity.
    Qed.

    (** Placing two matrices side by side multiplies their results.

        Here the two matrices have the same number of rows but
        possibly different widths.  Each row of the combined matrix is
        a row of [M₁] followed by a row of [M₂], and the unknowns are
        concatenated in the same way, so every row evaluates to the
        product of its two halves by [row_eval_app].

        This is how a statement over two groups of secrets, such as
        the committed values and their blinding randomnesses, is
        written as one wide matrix. *)
    Lemma mat_eval_zip_app :
      ∀ (m n₁ n₂ : nat) (M₁ : Vector.t (Vector.t G n₁) m)
        (M₂ : Vector.t (Vector.t G n₂) m)
        (x₁ : Vector.t F n₁) (x₂ : Vector.t F n₂),
      mat_eval (zip_with (fun r₁ r₂ => r₁ ++ r₂) M₁ M₂) (x₁ ++ x₂) =
      zip_with gop (mat_eval M₁ x₁) (mat_eval M₂ x₂).
    Proof.
      induction m as [|m ihm].
      +
        intros *.
        rewrite (vector_inv_0 M₁), (vector_inv_0 M₂).
        reflexivity.
      +
        intros *.
        destruct (vector_inv_S M₁) as (r₁h & r₁t & ha).
        destruct (vector_inv_S M₂) as (r₂h & r₂t & hb).
        subst.
        specialize (ihm n₁ n₂ r₁t r₂t x₁ x₂).
        unfold mat_eval in ihm |- *; cbn.
        rewrite ihm.
        f_equal.
        eapply row_eval_app.
    Qed.

    (** ** Completeness

        An honest prover always convinces the verifier. *)

    (** If the public vector really is the system evaluated at the
        witness, then the honest transcript is accepted, for every
        choice of randomness [us] and every challenge [c].

        The argument is one rewriting step with [row_eval_response]:
        a row evaluated at the response equals that row evaluated at
        [us], which is the announcement the prover sent, times the row
        evaluated at [xs] raised to [c], and the row evaluated at [xs]
        is the public target by the hypothesis.  That is literally the
        verifier's equation for the row, so
        [verify_linear_relation_backward] finishes the proof.

        Completeness is the promise that the protocol is usable at
        all.  It holds for every challenge, so no choice by the
        verifier can make an honest run fail. *)
    Theorem linear_relation_completeness :
      ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m)
        (pub : Vector.t G m) (xs us : Vector.t F n) (c : F),
      pub = mat_eval mat xs ->
      verify_linear_relation_proof mat pub
        (construct_linear_relation_real_proof mat xs us c) = true.
    Proof.
      intros * ha.
      unfold construct_linear_relation_real_proof.
      eapply verify_linear_relation_backward.
      intro i.
      rewrite row_eval_response.
      subst; unfold mat_eval.
      rewrite !(nth_map _ _ i i eq_refl).
      reflexivity.
    Qed.

    (** ** The simulator produces accepting transcripts *)

    (** The simulated transcript passes the verifier for any matrix,
        any public vector, any response [zs] and any challenge [c],
        with no assumption that the statement is true.

        The announcement was defined as the row evaluated at [zs],
        times the public target raised to [opp c].  The verifier
        recomputes the announcement times the target raised to [c], so
        the two opposite powers of the target meet and cancel, leaving
        the row evaluated at [zs] on both sides of the equation.

        Notice what this does not say.  It does not say the statement
        holds: a fake transcript for a false statement passes too.
        What stops a cheating prover is that the simulator needed the
        challenge before it could choose the announcement, and a real
        verifier never hands the challenge over that early. *)
    Theorem linear_relation_simulator_completeness :
      ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m)
        (pub : Vector.t G m) (zs : Vector.t F n) (c : F),
      verify_linear_relation_proof mat pub
        (construct_linear_relation_simulator_proof mat pub zs c) = true.
    Proof.
      intros *.
      unfold construct_linear_relation_simulator_proof.
      eapply verify_linear_relation_backward.
      intro i.
      rewrite !nth_zip_with.
      rewrite <-associative.
      rewrite <-smul_distributive_fadd.
      assert (ha : opp c + c = zero). field.
      rewrite ha, field_zero, right_identity.
      reflexivity.
    Qed.

    (** ** Special soundness

        Two accepting runs that share an announcement but differ in
        the challenge yield an actual witness. *)

    (** From two accepting transcripts with the same announcement
        [comm] and two different challenges [c₁] and [c₂], a witness
        can be computed.  So such a pair can only exist when the
        statement is in fact true.

        The mathematical idea is division.  Each accepting run gives,
        for every row, that the row evaluated at its own response
        equals the announcement entry times the public target raised
        to that run's challenge.  The announcements are the same in
        both runs, so dividing the first equation by the second makes
        them disappear and leaves: the quotient of the two row
        evaluations equals the target raised to [c₁ - c₂].  The two
        challenges differ, so [c₁ - c₂] is a nonzero field element and
        has an inverse.

        The extracted witness is therefore the vector whose [i]-th
        entry is the difference of the two responses at position [i],
        divided by [c₁ - c₂].  By [row_eval_sub_scale], evaluating a
        row at that vector is the quotient of the two evaluations
        raised to that inverse, which by the previous paragraph is the
        target raised to [(c₁ - c₂) * inv (c₁ - c₂)], that is, the
        target itself.  Every row is then satisfied, which is exactly
        [mat_eval mat xs = pub].

        This is why a single accepting run is convincing in practice.
        A prover able to answer two different challenges on the same
        announcement would, by this very construction, know a witness.
        It is also the shape that the rewinding arguments of
        Composition.v consume at each leaf. *)
    Theorem linear_relation_special_soundness :
      ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m)
        (pub comm : Vector.t G m) (c₁ c₂ : F)
        (res₁ res₂ : Vector.t F n),
      c₁ <> c₂ ->
      verify_linear_relation_proof mat pub (comm; [c₁]; res₁) = true ->
      verify_linear_relation_proof mat pub (comm; [c₂]; res₂) = true ->
      ∃ (xs : Vector.t F n), mat_eval mat xs = pub.
    Proof.
      intros * ha hb hc.
      pose proof (verify_linear_relation_forward _ _ _ _ _ _ _ hb) as hd.
      pose proof (verify_linear_relation_forward _ _ _ _ _ _ _ hc) as he.
      exists (zip_with (fun z₁ z₂ => (z₁ - z₂) * inv (c₁ - c₂))
        res₁ res₂).
      eapply eq_nth_iff.
      intros i j hij; subst.
      unfold mat_eval.
      rewrite !(nth_map _ _ j j eq_refl).
      rewrite row_eval_sub_scale.
      rewrite (hd j), (he j).
      rewrite group_inv_flip.
      rewrite gop_simp.
      setoid_rewrite commutative at 2;
      rewrite gop_simp, right_inverse, right_identity.
      rewrite commutative.
      rewrite connection_between_vopp_and_fopp.
      rewrite <-smul_distributive_fadd.
      rewrite <-smul_associative_fmul.
      assert (hf : (c₁ + opp c₂) * inv (c₁ - c₂) = one).
      field. intro hf. eapply ha.
      eapply f_equal with (f := fun x => x + c₂) in hf.
      rewrite left_identity in hf.
      rewrite <-hf. field.
      rewrite hf, field_one.
      reflexivity.
    Qed.

    (** ** Special honest-verifier zero knowledge

        A verifier who follows the protocol learns nothing from a run
        beyond the truth of the statement.  This is made precise by
        comparing two probability distributions: the transcripts of
        real runs, which use the witness, and the transcripts produced
        by the simulator, which has no witness.  If the two
        distributions are the same, a real transcript cannot be
        carrying information about the witness, because a machine
        without the witness produces the very same thing with the very
        same probabilities.

        Honest-verifier means the challenge is fixed in advance rather
        than chosen adversarially after seeing the announcement. *)

    (** Every outcome of the real experiment is an accepting
        transcript, and all outcomes carry the same probability.

        If the pair of a transcript [a] and a probability [b] occurs
        in [linear_relation_real_distribution], then [a] is accepted
        by the verifier, and [b] is one divided by the number of
        possible randomness vectors, which is the length of [lf]
        raised to the power [n].

        The first half is completeness, applied to whichever
        randomness produced [a].  The second half is the fact that [n]
        independent uniform draws from [lf] give a uniform
        distribution on vectors of length [n]. *)
    Lemma linear_relation_real_distribution_transcript_generic :
      ∀ (m n : nat) (lf : list F) (Hlf : lf <> List.nil)
        (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m)
        (xs : Vector.t F n) (a : sigma_proto) (b : prob) (c : F),
      pub = mat_eval mat xs ->
      List.In (a, b)
        (linear_relation_real_distribution lf Hlf mat xs c) ->
      verify_linear_relation_proof mat pub a = true ∧
      b = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) n)).
    Proof.
      intros * ha hb.
      unfold linear_relation_real_distribution in hb.
      refine (conj _ _).
      +
        destruct (bind_ret_in _ _ _ _ hb) as (us & q & hc & hd & he).
        rewrite hd.
        eapply linear_relation_completeness.
        exact ha.
      +
        eapply bind_ret_prob.
        intros * hc.
        eapply uniform_probability_multidraw_prob.
        exact hc.
        exact hb.
    Qed.

    (** The same two facts for the simulated experiment: every
        outcome is accepted, by
        [linear_relation_simulator_completeness], and every outcome
        carries the same probability, one divided by the length of
        [lf] raised to the power [n].  No hypothesis relating [pub] to
        a witness is needed here, since the simulator never uses
        one. *)
    Lemma linear_relation_simulator_distribution_transcript_generic :
      ∀ (m n : nat) (lf : list F) (Hlf : lf <> List.nil)
        (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m)
        (a : sigma_proto) (b : prob) (c : F),
      List.In (a, b)
        (linear_relation_simulator_distribution lf Hlf mat pub c) ->
      verify_linear_relation_proof mat pub a = true ∧
      b = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) n)).
    Proof.
      intros * ha.
      unfold linear_relation_simulator_distribution in ha.
      refine (conj _ _).
      +
        destruct (bind_ret_in _ _ _ _ ha) as (zs & q & hb & hc & hd).
        rewrite hc.
        eapply linear_relation_simulator_completeness.
      +
        eapply bind_ret_prob.
        intros * hb.
        eapply uniform_probability_multidraw_prob.
        exact hb.
        exact ha.
    Qed.

    (** Zero knowledge, in its accept-bit form.

        Tag every outcome of the real distribution with the verifier's
        answer on it, keeping the probability, and do the same for the
        simulated distribution.  The theorem says the two resulting
        lists are equal.

        The proof combines three facts.  The two distributions have
        the same length, because both are [n] uniform draws from the
        same list [lf].  Every real outcome is accepted and carries
        probability one over the length of [lf] raised to [n].  And
        the same holds of every simulated outcome.  So both lists are
        the same pair repeated the same number of times.

        The consequence is the zero-knowledge guarantee: an honest
        verifier sees accepting transcripts drawn uniformly, whether
        or not a witness was used, so a real run reveals nothing about
        [xs] beyond the truth of [mat_eval mat xs = pub]. *)
    Theorem linear_relation_special_honest_verifier_zkp :
      ∀ (m n : nat) (lf : list F) (Hlfn : lf <> List.nil)
        (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m)
        (xs : Vector.t F n) (c : F),
      pub = mat_eval mat xs ->
      List.map (fun '(a, p) =>
        (verify_linear_relation_proof mat pub a, p))
        (linear_relation_real_distribution lf Hlfn mat xs c) =
      List.map (fun '(a, p) =>
        (verify_linear_relation_proof mat pub a, p))
        (linear_relation_simulator_distribution lf Hlfn mat pub c).
    Proof.
      intros * ha.
      eapply map_ext_eq.
      +
        unfold linear_relation_real_distribution,
        linear_relation_simulator_distribution; cbn.
        repeat rewrite distribution_length.
        reflexivity.
      +
        intros (aa, cc, rr) y hb.
        eapply linear_relation_real_distribution_transcript_generic.
        exact ha.
        exact hb.
      +
        intros (aa, cc, rr) y hb.
        eapply linear_relation_simulator_distribution_transcript_generic.
        exact hb.
    Qed.

    (** ** Instances

        Each lemma below fixes a shape of matrix and shows that the
        relation [mat_eval mat xs = pub] then says exactly what the
        corresponding classical protocol says.  None of this is needed
        for the protocol itself.  The point is to check that this
        single leaf really does cover the statements the compiler must
        handle, and to record the exact matrix the compiler should
        emit in each case.

        One encoding trick recurs: an unknown that does not occur in
        an equation is given the neutral element [gid] in its column
        of that row, which contributes nothing to the product. *)
    Section Instances.

      (** Schnorr, the one-by-one case: a single base and a single
          unknown.  The relation says that the public [h] is [g]
          raised to the secret [x], so the witness is a discrete
          logarithm.  This is the protocol of Crypto/Sigma.v.  The
          proof is pure bookkeeping: a row of width one evaluates to
          [g ^ x] multiplied by the neutral element. *)
      Lemma schnorr_instance : ∀ (g h : G) (x : F),
        mat_eval [[g]] [x] = [h] <-> h = g ^ x.
      Proof.
        intros *; split; intro ha.
        +
          eapply f_equal with (f := Vector.hd) in ha; cbn in ha.
          rewrite right_identity in ha.
          subst; reflexivity.
        +
          subst; unfold mat_eval, row_eval; cbn.
          f_equal; rewrite right_identity;
          reflexivity.
      Qed.

      (** Okamoto: one equation in two unknowns.  The public [h] is a
          product of two powers with two different bases, and the
          witness is one representation of [h] in the bases [g₁] and
          [g₂].  The matrix is a single row of width two. *)
      Lemma okamoto_instance : ∀ (g₁ g₂ h : G) (x₁ x₂ : F),
        mat_eval [[g₁; g₂]] [x₁; x₂] = [h] <->
        h = gop (g₁ ^ x₁) (g₂ ^ x₂).
      Proof.
        intros *; split; intro ha.
        +
          eapply f_equal with (f := Vector.hd) in ha; cbn in ha.
          rewrite right_identity in ha.
          subst; reflexivity.
        +
          subst; unfold mat_eval, row_eval; cbn.
          f_equal; rewrite right_identity;
          reflexivity.
      Qed.

      (** Chaum-Pedersen: two equations in one unknown.  The same
          secret [x] is the exponent in both, so the statement is that
          [h₁] and [h₂] have the same discrete logarithm with respect
          to [g₁] and to [g₂] respectively.  The matrix is a column of
          two rows of width one, and sharing the single column is
          precisely what forces the same secret into both
          equations. *)
      Lemma chaum_pedersen_instance : ∀ (g₁ g₂ h₁ h₂ : G) (x : F),
        mat_eval [[g₁]; [g₂]] [x] = [h₁; h₂] <->
        (h₁ = g₁ ^ x ∧ h₂ = g₂ ^ x).
      Proof.
        intros *; split; intro ha.
        +
          pose proof (f_equal Vector.hd ha) as hb; cbn in hb.
          eapply f_equal with (f := fun v => Vector.hd (Vector.tl v))
            in ha; cbn in ha.
          rewrite right_identity in ha, hb.
          subst; split; reflexivity.
        +
          destruct ha as (ha & hb).
          subst; unfold mat_eval, row_eval; cbn.
          repeat f_equal;
          try (rewrite right_identity; reflexivity).
      Qed.

      (** Opening a Pedersen commitment: knowing a value [v] and a
          blinding randomness [r] such that the public commitment [C]
          is [g ^ v] times [h ^ r].  Structurally this is Okamoto with
          the bases and unknowns renamed, so the proof simply reuses
          [okamoto_instance]. *)
      Lemma pedersen_opening_instance : ∀ (g h C : G) (v r : F),
        mat_eval [[g; h]] [v; r] = [C] <-> C = gop (g ^ v) (h ^ r).
      Proof.
        intros *; exact (okamoto_instance g h C v r).
      Qed.

      (** The conjunction of two unrelated Schnorr statements, as a
          two-by-two matrix.  Each row constrains one unknown and
          ignores the other, which is expressed by the [gid] entry in
          the other column.  This shows that a plain AND of leaves
          needs no composition layer at all: it is already a single
          linear system, proven in one run. *)
      Lemma and_schnorr_instance : ∀ (g₁ g₂ h₁ h₂ : G) (x₁ x₂ : F),
        mat_eval [[g₁; gid]; [gid; g₂]] [x₁; x₂] = [h₁; h₂] <->
        (h₁ = g₁ ^ x₁ ∧ h₂ = g₂ ^ x₂).
      Proof.
        intros *; split; intro ha.
        +
          pose proof (f_equal Vector.hd ha) as hb; cbn in hb.
          eapply f_equal with (f := fun v => Vector.hd (Vector.tl v))
            in ha; cbn in ha.
          rewrite !vid_identity, !left_identity, !right_identity in ha, hb.
          subst; split; reflexivity.
        +
          destruct ha as (ha & hb).
          subst; unfold mat_eval, row_eval; cbn.
          repeat f_equal;
          rewrite ?vid_identity, ?left_identity, ?right_identity;
          reflexivity.
      Qed.

      (** Two Pedersen commitments hide one and the same value.
          There are three unknowns, the common value [v] and the two
          blinding randomnesses, and two equations.  The column of [v]
          is used by both rows, and that is what states the equality,
          while each randomness gets a private column with [gid] in
          the row that must not see it.  The protocol proves the two
          commitments agree without revealing [v]. *)
      Lemma pedersen_equality_instance :
        ∀ (g h C₁ C₂ : G) (v r₁ r₂ : F),
        mat_eval [[g; h; gid]; [g; gid; h]] [v; r₁; r₂] = [C₁; C₂] <->
        (C₁ = gop (g ^ v) (h ^ r₁) ∧ C₂ = gop (g ^ v) (h ^ r₂)).
      Proof.
        intros *; split; intro ha.
        +
          pose proof (f_equal Vector.hd ha) as hb; cbn in hb.
          eapply f_equal with (f := fun v => Vector.hd (Vector.tl v))
            in ha; cbn in ha.
          rewrite !vid_identity, !left_identity, !right_identity in ha, hb.
          subst; split; reflexivity.
        +
          destruct ha as (ha & hb).
          subst; unfold mat_eval, row_eval; cbn.
          repeat f_equal;
          rewrite ?vid_identity, ?left_identity, ?right_identity;
          reflexivity.
      Qed.

      (** A Diffie-Hellman tuple: the public elements are [g], [g]
          raised to [a], [g] raised to [b], and [g] raised to the
          product of [a] and [b].  The last equation is expressed by
          using the public element [h₁] itself as a base, with [b] as
          the exponent.  That is legitimate because bases only have to
          be public, not independent, and it is the standard way in
          which a product of secrets in the exponent is still a linear
          statement. *)
      Lemma dh_tuple_instance : ∀ (g h₁ h₂ h₃ : G) (a b : F),
        mat_eval [[g; gid]; [gid; g]; [gid; h₁]] [a; b] = [h₁; h₂; h₃] <->
        (h₁ = g ^ a ∧ h₂ = g ^ b ∧ h₃ = h₁ ^ b).
      Proof.
        intros *; split; intro ha.
        +
          pose proof (f_equal Vector.hd ha) as hb; cbn in hb.
          pose proof (f_equal (fun v => Vector.hd (Vector.tl v)) ha)
            as hc; cbn in hc.
          eapply f_equal with
            (f := fun v => Vector.hd (Vector.tl (Vector.tl v)))
            in ha; cbn in ha.
          rewrite !vid_identity, !left_identity, !right_identity
            in ha, hb, hc.
          subst; repeat split; reflexivity.
        +
          destruct ha as (ha & hb & hc).
          subst; unfold mat_eval, row_eval; cbn.
          repeat f_equal;
          rewrite ?vid_identity, ?left_identity, ?right_identity;
          reflexivity.
      Qed.

      (** Equality of discrete logarithms across arbitrarily many
          pairs: one secret [x], and for every index [i] the public
          element [hs] at [i] is the base [gs] at [i] raised to [x].
          The matrix is just the column of bases.  This generalises
          [chaum_pedersen_instance] from two equations to [m] of them
          at no extra cost in the protocol. *)
      Lemma dleq_instance : ∀ (m : nat) (gs hs : Vector.t G m) (x : F),
        mat_eval (Vector.map (fun g => [g]) gs) [x] = hs <->
        (∀ i : Fin.t m, nth hs i = nth gs i ^ x).
      Proof.
        intros *; split; intro ha.
        +
          intro i.
          rewrite <- ha.
          unfold mat_eval.
          rewrite !(nth_map _ _ i i eq_refl).
          unfold row_eval; cbn.
          rewrite right_identity.
          reflexivity.
        +
          eapply eq_nth_iff.
          intros i j hij; subst.
          unfold mat_eval.
          rewrite !(nth_map _ _ j j eq_refl), ha.
          unfold row_eval; cbn.
          rewrite right_identity.
          reflexivity.
      Qed.


      (** A full worked example: several Pedersen commitments
          together with a public linear constraint on the values they
          hide.

          The statement is that there are values [vs] and blinding
          randomnesses [rs] such that each commitment is [g] raised to
          its value times [h] raised to its randomness, and moreover
          the weighted sum of the values with the public coefficients
          [αs] equals a public target.  Written as one linear system
          over the concatenated witness [vs ++ rs], the matrix has two
          parts:

          - a block of rows for the commitment equations, made of two
            identity-shaped blocks placed side by side, the [g] block
            acting on [vs] and the [h] block acting on [rs];
          - one final row for the linear constraint, whose bases are
            the public coefficients folded into [g], each base being
            [g] raised to one coefficient, and whose right-hand side
            is [g] raised to the weighted sum.  The second half of
            that row is all [gid], because the constraint says nothing
            about the randomnesses.

          The theorem computes what this matrix evaluates to and shows
          the answer is exactly the intended right-hand side.  It is
          proven by peeling the construction apart with
          [mat_eval_app_rows], [mat_eval_zip_app], [mat_eval_diag],
          [row_eval_app], [row_eval_pow_row] and
          [row_eval_const_gid].

          The first component of the right-hand side is definitionally
          the commitment vector of PedLinearRel.v.  This instance is
          the template for how the compiler treats any public scalar
          occurring in a statement. *)
      Theorem pedersen_linear_relation_as_instance :
        ∀ (n : nat) (g h : G) (αs vs rs : Vector.t F n),
        mat_eval
          (zip_with (fun r₁ r₂ => r₁ ++ r₂) (diag_mat n g) (diag_mat n h) ++
            [Vector.map (gpow g) αs ++ Vector.const gid n])
          (vs ++ rs) =
        zip_with (fun v r => gop (g ^ v) (h ^ r)) vs rs ++
        [g ^ (fold_right (fun '(α, v) acc => α * v + acc)
          (zip_with pair αs vs) zero)].
      Proof.
        intros *.
        rewrite mat_eval_app_rows, mat_eval_zip_app.
        f_equal.
        +
          rewrite !mat_eval_diag.
          eapply eq_nth_iff.
          intros i j hij; subst.
          rewrite !nth_zip_with, !(nth_map _ _ j j eq_refl).
          reflexivity.
        +
          unfold mat_eval; cbn.
          f_equal.
          rewrite row_eval_app, row_eval_pow_row,
            row_eval_const_gid, right_identity.
          reflexivity.
      Qed.

    End Instances.
  End Proofs.
End LinearRelation.
