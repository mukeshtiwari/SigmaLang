From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool List PeanoNat.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import
  Util.
From Crypto Require Import
  Sigma.
From Compiler Require Import
  LinearRelation Composition Dsl.

Import VectorNotations.

(** * Nizk: making the composed protocol non-interactive

    ** The interactive protocol, recalled

    Composition.v builds an interactive proof out of a statement
    tree [comp_rel].  Such a proof is a conversation in three moves.
    First the prover sends an announcement, sometimes called the
    commitment: a collection of group elements computed from fresh
    random numbers.  Then the verifier sends back a challenge: a
    single field element, drawn at random.  Finally the prover sends
    a response, computed from the random numbers, the challenge, and
    the secret it knows.  The three pieces together are called a
    transcript, and the verifier accepts or rejects it.

    The secret the prover knows is the witness.  A protocol of this
    shape has three properties of interest.  Completeness: an honest
    prover who really knows a witness is always accepted.
    Soundness: a prover who does not know a witness is almost
    certainly rejected.  Zero knowledge: the verifier learns nothing
    beyond the fact that the statement is true, which is shown by
    exhibiting a simulator, a program that produces accepting
    transcripts out of thin air, without any witness, and whose
    output is distributed exactly like a real conversation.

    ** What Fiat-Shamir does

    The conversation needs both parties to be online at the same
    time.  Fiat-Shamir removes the verifier from the loop.  Instead
    of waiting for a random challenge, the prover computes the
    challenge itself, as the hash of its own first message.  A hash
    function is a fixed, public, deterministic function that maps
    its input to something that looks random; here it maps to a
    field element.  The prover then publishes announcement,
    challenge and response as a single file.  Anyone can check it
    later, with nobody online: the verifier recomputes the hash from
    the announcement it was given and checks the transcript against
    the challenge that comes out.

    The result is a non-interactive zero-knowledge proof, a NIZK.

    ** Weak versus strong Fiat-Shamir

    Everything depends on what goes into the hash.  The naive
    version, called weak Fiat-Shamir, hashes only the announcement.
    That is not enough.  An attacker who is free to choose the
    statement afterwards can first pick random data, hash it to get
    a challenge, and only then cook up a statement for which that
    announcement and challenge happen to be answerable.  The proof
    then verifies against a statement the attacker chose, which is
    worthless.

    The fix, called strong Fiat-Shamir (Bernhard, Pereira and
    Warinschi, ePrint 2016/771), is to hash the whole instance as
    well: the statement tree, the matrices of bases at every leaf,
    and the public points those equations are asserted to equal.
    Then the hash pins the statement down before the challenge
    exists, and the attacker has nothing left to choose.

    In this file the hash is an abstract parameter, a function
    [hash] of type [comp_ann_t r -> F] supplied by the caller.  The
    file does not, and cannot, force the caller to bind the
    instance: that responsibility sits with whoever instantiates it.
    The caller discharges it by baking the instance into the hash
    function it passes, which is exactly what
    Examples/ThresholdIns.v does, prefixing the generator and the
    public points to the hashed data.

    ** Why the transform is well defined at all

    The prover is supposed to hash its first message and then answer
    the resulting challenge.  That only makes sense if the first
    message does not itself depend on the challenge.  Otherwise the
    definition would be circular.

    For a leaf this is obvious, and for AND and OR nodes it is easy.
    For a threshold node it is a real statement, and it needs a real
    witness.  The reason is that a threshold prover simulates some
    of its children, and a simulated child is given a challenge that
    was committed to in advance, drawn from the prover's randomness.
    Those pre-committed values are recovered from the interpolating
    polynomial, and the interpolant takes them at the simulated
    children's own nodes no matter what the root challenge is.  That
    is [expand_chal_nodes] from Composition.v, and it only applies
    when the prover really does have at least [t] witnesses, so that
    the set of simulated children is the expected size.  The
    conclusion is [prove_ann_independent], and completeness assumes
    a valid witness anyway.

    ** What is proven here, and what is not

    Proven, and unconditionally:

    - [prove_ann_independent]: the announcement part of an honest
      transcript does not depend on the challenge, which is what
      makes the transformation well defined;
    - [nizk_completeness]: an honestly generated non-interactive
      proof always verifies.  This holds for every hash function
      whatsoever, good or bad;
    - [ann_to_list_inj]: flattening the announcement tree into a
      list of group elements loses nothing;
    - [comp_compact_recover]: the compact wire format at the end of
      the file can be expanded back into the transcript it came
      from.

    Not proven, deliberately: soundness and zero knowledge of the
    non-interactive protocol.  These do hold, by the standard
    argument built on [comp_special_soundness] and
    [comp_distribution_perm] from Composition.v, but only in the
    random-oracle model.  The random-oracle model is an idealisation
    in which the hash function is replaced by a truly random
    function that everybody, including the attacker, may only query
    like an oracle.  Real hash functions are not random oracles, and
    the idealisation is an assumption, not a theorem.  Adding it
    here would mean introducing an axiom.  That step is left out on
    purpose, so this development remains free of axioms and every
    theorem in it is unconditionally true.

    ** The compact wire format

    The last section shrinks what has to be transmitted.  The
    announcements are the bulkiest part of a transcript and they are
    also redundant: the verification equation determines each leaf
    announcement from that leaf's challenge and response.  So the
    wire format drops them, and the verifier recomputes them.
    [comp_compact_recover] proves that for any transcript the
    verifier would have accepted, the recomputation gives back
    exactly the announcements that were dropped. *)
Section Nizk.

  (** ** Parameters

      Like the rest of the compiler, the file is parametric in a
      field [F] and a group [G].  Nothing below depends on a
      particular choice, so the results apply to whatever prime
      group a deployment uses.

      - [zero], [one] are the two field constants;
      - [add], [mul], [sub], [div] the four field operations;
      - [opp] is field negation and [inv] the multiplicative
        inverse;
      - [Fdec] decides equality of two field elements. *)
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}.

  (** The group the statements live in.

      - [gid] is the identity and [ginv] inversion;
      - [gop] is the group operation;
      - [gpow] raises a group element to a field exponent, written
        with the infix notation below;
      - [Gdec] decides equality of two group elements, which is what
        the verifier needs in order to compare the two sides of an
        equation. *)
  Context
    {G : Type}
    {gid : G}
    {ginv : G -> G}
    {gop : G -> G -> G}
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}.

  (** Infix notation: [g ^ c] raises a group element to a field
      exponent, and [a - b] is field subtraction. *)
  #[local] Infix "^" := gpow.
  #[local] Infix "-" := sub.

  (** ** Shorthands

      The constants of Composition.v are defined inside a section of
      their own, so each of them takes this section's field and
      group operations as explicit arguments.  The notations below
      apply them once and for all, so the definitions that follow
      read the way they would on paper.

      - [comp_relC] is the statement tree;
      - [comp_witnessC], [comp_randC] and [comp_transcriptC] are the
        types of witness, prover randomness and transcript computed
        from a tree;
      - [comp_rel_holdsC] says a witness satisfies a tree;
      - [comp_proveC], [comp_simulateC] and [comp_verifyC] are the
        honest prover, the simulator and the verifier of the
        interactive protocol;
      - [row_evalC] evaluates one linear equation;
      - [expand_chalC] is the interpolating polynomial that spreads
        one root challenge over the children of a threshold node;
      - [wlist], [tlist], [rlist], [wholds], [provelist] and
        [verlist] are the generic walkers over the children of a
        threshold node, instantiated at the relevant types. *)
  #[local] Notation comp_relC := (@comp_rel F zero G).
  #[local] Notation comp_witnessC := (@comp_witness F zero G).
  #[local] Notation comp_randC := (@comp_rand F zero G).
  #[local] Notation comp_transcriptC := (@comp_transcript F zero G).
  #[local] Notation comp_rel_holdsC := (@comp_rel_holds F zero G gid gop gpow).
  #[local] Notation comp_proveC :=
    (@comp_prove F zero one add mul sub opp inv G gid gop gpow).
  #[local] Notation comp_simulateC :=
    (@comp_simulate F zero one add mul sub opp inv G gid gop gpow).
  #[local] Notation comp_verifyC :=
    (@comp_verify F zero one add mul sub inv G gid gop gpow Gdec).
  #[local] Notation row_evalC := (@row_eval F G gid gop gpow _).
  #[local] Notation expand_chalC :=
    (@expand_chal F zero one add mul sub inv).
  #[local] Notation wlist := (wlist_gen comp_witnessC).
  #[local] Notation tlist := (tlist_gen comp_transcriptC).
  #[local] Notation rlist := (tlist_gen comp_randC).
  #[local] Notation wholds := (wholds_gen comp_rel_holdsC).
  #[local] Notation provelist := (provelist_gen comp_proveC comp_simulateC).
  #[local] Notation verlist := (verlist_gen comp_verifyC).

  (** ** Definitions: the announcement, the hash input, and the
      non-interactive prover and verifier *)
  Section Def.

    (** The type of the announcement part of a transcript, computed
        from the statement tree.

        This is the data that gets hashed.  A transcript carries
        three kinds of thing: the announcements, which are first
        move data; the sub-challenges that OR and threshold nodes
        store so the verifier can reconstruct how the root challenge
        was split; and the responses.  The last two are third move
        data, computed after the challenge is known, and hashing
        them would be circular.  So [comp_ann_t] keeps only the
        announcements.

        Node by node: a [Leaf] with [m] equations announces [m]
        group elements, one per equation.  An [CAnd] or [COr] node
        announces the pair of its children's announcements.  A
        [CThresh] node announces the announcements of all its
        children, held in the same nested-product shape
        [tlist_gen] uses elsewhere. *)
    Fixpoint comp_ann_t (r : comp_relC) : Type :=
      match r with
      | Leaf m _ _ _ => Vector.t G m
      | CAnd rl rr => (comp_ann_t rl * comp_ann_t rr)%type
      | COr rl rr => (comp_ann_t rl * comp_ann_t rr)%type
      | CThresh _ _ _ rs _ _ => tlist_gen comp_ann_t rs
      end.

    (** Extracting the announcement from each child of a threshold
        node.

        A threshold node stores its children in a vector, which
        makes [comp_rel] a nested inductive type; Rocq does not
        accept a direct recursive call under such a vector.  The
        recursion over the children is therefore factored into a
        generic walker taking the function being defined as its
        argument [ca].  This is the same pattern Composition.v uses
        for [provelist_gen] and [verlist_gen].

        [v] is the vector of children and the argument of the
        returned function is their transcripts; the result is their
        announcements, in the same order. *)
    Fixpoint annlist_gen
      (ca : ∀ r : comp_relC, comp_transcriptC r -> comp_ann_t r)
      {n : nat} (v : Vector.t comp_relC n) {struct v} :
      tlist v -> tlist_gen comp_ann_t v :=
      match v as v' return tlist v' -> tlist_gen comp_ann_t v' with
      | [] => fun _ => tt
      | r :: v' => fun t => (ca r (fst t), annlist_gen ca v' (snd t))
      end.

    (** Reading the announcement out of a transcript.

        [transcript_ann r t] keeps the first move data of the
        transcript [t] and discards the rest.  It is the projection
        that produces the hash input.

        At a [Leaf] the transcript is a pair of announcement and
        response, so the announcement is its first component.  At an
        [CAnd] node the transcript is a pair of child transcripts,
        and the announcement is the pair of their announcements.  At
        a [COr] node the transcript is a pair of child transcripts
        together with the stored sub-challenge; the sub-challenge is
        dropped and the two children are projected.  At a [CThresh]
        node the transcript is the children's transcripts together
        with the compressed challenges; again the challenges are
        dropped and the children are projected with
        [annlist_gen]. *)
    Fixpoint transcript_ann (r : comp_relC) :
      comp_transcriptC r -> comp_ann_t r :=
      match r return comp_transcriptC r -> comp_ann_t r with
      | Leaf _ _ _ _ => fun t => fst t
      | CAnd rl rr => fun t =>
          (transcript_ann rl (fst t), transcript_ann rr (snd t))
      | COr rl rr => fun t =>
          (transcript_ann rl (fst (fst t)),
           transcript_ann rr (snd (fst t)))
      | CThresh _ _ _ rs _ _ => fun t =>
          annlist_gen transcript_ann rs (fst t)
      end.

    (** ** Flattening the announcement tree

        The announcement is a tree of vectors of group elements, but
        a hash function eats a flat sequence of bytes.  Somebody has
        to flatten it, and doing that by hand is where things go
        wrong.  Reaching into the tree ad hoc, taking [Vector.hd] of
        a leaf for instance, silently throws away group elements as
        soon as a leaf carries more than one equation.  The hash
        then fails to bind part of the announcement, and that is
        precisely the weak Fiat-Shamir failure the strong transform
        is meant to rule out: what the hash does not cover, an
        attacker is free to change afterwards.

        So the flattening is provided here, once, and proved
        faithful.  [ann_to_list] collects every group element of
        every leaf, from left to right.  [ann_to_list_inj], further
        down, proves that this loses nothing: two announcements with
        the same flattening are the same announcement.  An
        instantiation that hashes [ann_to_list] of the announcement,
        together with the instance, therefore really does bind the
        whole first message. *)

    (** How many group elements an announcement for [r] contains.

        This is a static count, read off the statement tree alone: a
        leaf with [m] equations contributes [m], an [CAnd] or [COr]
        node the sum of its children, and a [CThresh] node the sum
        over all its children.  Knowing the length in advance is
        what makes the injectivity proof work, since it tells the
        proof where to cut a concatenated list back into the pieces
        it was built from. *)
    Fixpoint ann_size (r : comp_relC) : nat :=
      match r with
      | Leaf m _ _ _ => m
      | CAnd rl rr => (ann_size rl + ann_size rr)%nat
      | COr rl rr => (ann_size rl + ann_size rr)%nat
      | CThresh _ _ _ rs _ _ => slist_gen ann_size rs
      end.

    (** Flattening the announcements of the children of a threshold
        node, in order.

        Again a generic walker over the vector of children, taking
        the flattening function [cl] as an argument for the same
        reason as [annlist_gen] above.  Each child is flattened and
        the results are concatenated, left to right. *)
    Fixpoint annl_gen (cl : ∀ r : comp_relC, comp_ann_t r -> list G)
      {n : nat} (v : Vector.t comp_relC n) {struct v} :
      tlist_gen comp_ann_t v -> list G :=
      match v as v' return tlist_gen comp_ann_t v' -> list G with
      | [] => fun _ => List.nil
      | r :: v' => fun a => List.app (cl r (fst a)) (annl_gen cl v' (snd a))
      end.

    (** The announcement, flattened into one list of group elements.

        [ann_to_list r a] walks the announcement [a] of statement
        tree [r] and returns all of its group elements in a single
        list, in left-to-right order.  A leaf contributes its vector
        turned into a list; an [CAnd] or [COr] node contributes the
        left child's list followed by the right child's; a
        [CThresh] node contributes its children's lists in order.

        This is the function an instantiation should feed to its
        hash, after the encoding of the instance.  Its faithfulness
        is [ann_to_list_inj] below. *)
    Fixpoint ann_to_list (r : comp_relC) : comp_ann_t r -> list G :=
      match r return comp_ann_t r -> list G with
      | Leaf _ _ _ _ => fun a => Vector.to_list a
      | CAnd rl rr => fun a =>
          List.app (ann_to_list rl (fst a)) (ann_to_list rr (snd a))
      | COr rl rr => fun a =>
          List.app (ann_to_list rl (fst a)) (ann_to_list rr (snd a))
      | CThresh _ _ _ rs _ _ => fun a => annl_gen ann_to_list rs a
      end.

    (** ** The non-interactive protocol *)

    (** The non-interactive prover.

        Given the statement tree [r], a hash function [hash], a
        witness [w] and the prover's randomness [rnd], this produces
        a complete transcript with nobody else in the room.

        It works in two steps.  First it runs the ordinary prover at
        some arbitrary challenge, here [zero], and reads off the
        announcement with [transcript_ann].  Then it hashes that
        announcement to obtain the real challenge, and runs the
        ordinary prover again at that challenge.

        The arbitrary [zero] in the first step looks suspicious, and
        would be, if the announcement depended on the challenge.  It
        does not: [prove_ann_independent] proves that an honest
        prover produces the same announcement whatever challenge it
        is given.  So the announcement obtained at [zero] is the
        same one the returned transcript actually carries, and the
        definition is not circular.

        The challenge is not stored in the result.  It does not need
        to be: the verifier recomputes it. *)
    Definition nizk_prove (r : comp_relC)
      (hash : comp_ann_t r -> F)
      (w : comp_witnessC r) (rnd : comp_randC r) : comp_transcriptC r :=
      comp_proveC r w rnd
        (hash (transcript_ann r (comp_proveC r w rnd zero))).

    (** The non-interactive verifier.

        Given the statement tree [r], the same hash function [hash],
        and a transcript [t] that arrived from somewhere, this
        recomputes the challenge as the hash of the transcript's own
        announcement, and then runs the ordinary verifier at that
        challenge.

        The prover never sends a challenge, so there is nothing for
        a cheating prover to lie about here: the challenge is
        entirely determined by the announcement the prover
        committed to.  This is the whole trick of Fiat-Shamir.  Its
        security rests on the hash being hard to control, which is
        the part this file does not attempt to prove. *)
    Definition nizk_verify (r : comp_relC)
      (hash : comp_ann_t r -> F)
      (t : comp_transcriptC r) : bool :=
      comp_verifyC r (hash (transcript_ann r t)) t.

  End Def.

  (** Shorthands for the two generic walkers, applied to the
      functions they are meant to recurse with: [annlist] projects
      the announcements of a vector of children, and [annl]
      flattens them. *)
  #[local] Notation annlist := (annlist_gen transcript_ann).
  #[local] Notation annl := (annl_gen ann_to_list).

  (** ** Proofs *)
  Section Proofs.

    (** The proofs, unlike the definitions, need the field and the
        group to actually be a field and a group acting on it.
        [Hvec] is that assumption: it says [G] is a vector space
        over [F], which packages the group laws together with the
        exponentiation laws relating [gpow] to the field
        operations.  The [Add Field] line then lets the [field]
        tactic discharge routine algebraic identities. *)
    Context
      {Hvec : @vector_space F (@eq F) zero one add mul sub
        div opp inv G (@eq G) gid ginv gop gpow}.
    Add Field field : (@field_theory_for_stdlib_tactic F
      eq zero one opp add mul sub inv div vector_space_field).

    (** ** The flattening loses nothing

        The four results below build up to [ann_to_list_inj]: an
        announcement can be recovered from its flattening.  The
        proof is by structural induction, and at every branching
        node it has the same shape: the flattening is a
        concatenation of the children's flattenings, so to undo it
        one has to cut the list back into pieces.  That is possible
        because the length of each piece is known in advance from
        the statement tree, which is what [ann_size] and
        [ann_to_list_length] provide, and because a concatenation
        determines its parts once the first part's length is fixed,
        which is [app_split_eq]. *)

    (** The flattening of a threshold node's children has the length
        the statement tree predicts.

        [v] is the vector of children and [a] their announcements.
        The hypothesis, written with [vall], says the same fact is
        already known for every child; it is the induction
        hypothesis that [comp_rel_ind'] hands over.  The proof is a
        plain induction on the vector, using that the length of a
        concatenation is the sum of the lengths. *)
    Lemma annl_length :
      ∀ (n : nat) (v : Vector.t comp_relC n) (a : tlist_gen comp_ann_t v),
      vall (fun r => ∀ a : comp_ann_t r, List.length (ann_to_list r a) = ann_size r) v ->
      List.length (annl v a) = slist_gen ann_size v.
    Proof.
      intros n v.
      induction v as [| r n v ih]; intros a hall; cbn.
      + reflexivity.
      + destruct hall as (hr & hall).
        rewrite List.length_app, hr, (ih (snd a) hall). reflexivity.
    Qed.

    (** The flattened announcement has exactly [ann_size r]
        elements.

        The length of the list depends only on the shape of the
        statement tree, never on the particular group elements in
        the announcement.  That is what makes the count usable as a
        cutting point in the injectivity proof below, and it is also
        what an instantiation needs in order to know that its
        encoding of the hash input has a fixed layout.

        The proof is the structural induction [comp_rel_ind'].  At a
        leaf the length of [Vector.to_list] of a vector of size [m]
        is [m]; at a branching node the lengths add up; at a
        threshold node the previous lemma applies. *)
    Lemma ann_to_list_length :
      ∀ (r : comp_relC) (a : comp_ann_t r),
      List.length (ann_to_list r a) = ann_size r.
    Proof.
      intros r.
      induction r as [m n mat pub | rl rr ihl ihr | rl rr ihl ihr | t k xs rs Hxs Ht ihrs]
        using comp_rel_ind'; intros a; cbn.
      + eapply VectorSpec.length_to_list.
      + rewrite List.length_app, ihl, ihr; reflexivity.
      + rewrite List.length_app, ihl, ihr; reflexivity.
      + eapply annl_length; exact ihrs.
    Qed.

    (** Concatenation is determined by its parts, once the first
        part's length is fixed.

        If [l1] and [l1'] have the same length and the two
        concatenations agree, then the two first parts agree and the
        two second parts agree.  In other words, cutting a list at a
        known position is unambiguous.

        This is the ordinary list fact that drives every branching
        case of the injectivity proof.  It is stated separately
        because it is a self-contained fact about lists, with
        nothing cryptographic in it, and it is used four times. *)
    Lemma app_split_eq :
      ∀ (A : Type) (l1 l1' l2 l2' : list A),
      List.length l1 = List.length l1' ->
      List.app l1 l2 = List.app l1' l2' -> l1 = l1' ∧ l2 = l2'.
    Proof.
      induction l1 as [| x xs ih]; intros l1' l2 l2' hlen heq.
      + destruct l1' as [| y ys];
        [cbn in heq; split; [reflexivity | exact heq] | cbn in hlen; lia].
      + destruct l1' as [| y ys]; [cbn in hlen; lia |].
        cbn in hlen, heq.
        injection heq as hxy heq'.
        destruct (ih ys l2 l2' ltac:(lia) heq') as (h1 & h2).
        subst; split; reflexivity.
    Qed.

    (** Flattening the children of a threshold node loses nothing.

        The hypothesis states that injectivity is already known for
        every child; the conclusion lifts it to the whole list.  The
        argument is induction on the vector of children: the head
        child's two flattenings have the same length, by
        [ann_to_list_length], so [app_split_eq] cuts the two equal
        concatenations at the same place, and the head and the tail
        can be treated separately. *)
    Lemma annl_inj :
      ∀ (n : nat) (v : Vector.t comp_relC n) (a a' : tlist_gen comp_ann_t v),
      vall (fun r => ∀ a a' : comp_ann_t r,
        ann_to_list r a = ann_to_list r a' -> a = a') v ->
      annl v a = annl v a' -> a = a'.
    Proof.
      intros n v.
      induction v as [| r n v ih]; intros a a' hall heq; cbn in heq.
      + destruct a, a'; reflexivity.
      + destruct hall as (hr & hall).
        destruct a as (ah & at'); destruct a' as (ah' & at''); cbn in heq |- *.
        assert (hlen : List.length (ann_to_list r ah) = List.length (ann_to_list r ah')).
        { rewrite !ann_to_list_length; reflexivity. }
        destruct (app_split_eq _ _ _ _ _ hlen heq) as (h1 & h2).
        f_equal; [eapply hr; exact h1 | eapply ih; [exact hall | exact h2]].
    Qed.

    (** The flattening is injective: nothing is lost.

        If two announcements for the same statement tree flatten to
        the same list of group elements, they are the same
        announcement.

        This is the guarantee that makes [ann_to_list] a safe hash
        input.  Hashing the flattened list binds the entire
        announcement, because no two different announcements can
        produce the same list.  An ad hoc flattening that skipped
        some group elements would fail exactly this property, and a
        proof that skips group elements is a proof an attacker can
        tamper with after the challenge is fixed.

        Why it is true: the announcement's shape is fully determined
        by the statement tree, which both sides share, so the
        flattening always cuts the list at the same places.  At a
        leaf, turning a vector into a list is injective.  At a
        branching node the two halves have known, equal lengths, so
        [app_split_eq] separates them and the induction hypotheses
        finish the job.  At a threshold node [annl_inj] does the
        same for the whole vector of children.

        Examples/ThresholdIns.v uses this theorem to show that its
        concrete hash input, a string built from the instance
        followed by the flattened announcement, determines the
        announcement it came from. *)
    Theorem ann_to_list_inj :
      ∀ (r : comp_relC) (a a' : comp_ann_t r),
      ann_to_list r a = ann_to_list r a' -> a = a'.
    Proof.
      intros r.
      induction r as [m n mat pub | rl rr ihl ihr | rl rr ihl ihr | t k xs rs Hxs Ht ihrs]
        using comp_rel_ind'; intros a a' heq; cbn in heq |- *.
      + eapply VectorSpec.to_list_inj; exact heq.
      + destruct a as (al & ar); destruct a' as (al' & ar'); cbn in heq |- *.
        assert (hlen : List.length (ann_to_list rl al) = List.length (ann_to_list rl al'))
          by (rewrite !ann_to_list_length; reflexivity).
        destruct (app_split_eq _ _ _ _ _ hlen heq) as (h1 & h2).
        f_equal; [eapply ihl; exact h1 | eapply ihr; exact h2].
      + destruct a as (al & ar); destruct a' as (al' & ar'); cbn in heq |- *.
        assert (hlen : List.length (ann_to_list rl al) = List.length (ann_to_list rl al'))
          by (rewrite !ann_to_list_length; reflexivity).
        destruct (app_split_eq _ _ _ _ _ hlen heq) as (h1 & h2).
        f_equal; [eapply ihl; exact h1 | eapply ihr; exact h2].
      + eapply annl_inj; [exact ihrs | exact heq].
    Qed.

    (** ** Challenge independence

        The results below establish [prove_ann_independent]: an
        honest prover's announcement is the same whatever challenge
        it is asked to answer.  Without this the Fiat-Shamir
        definition would be circular, since the prover hashes its
        announcement to obtain the challenge it is about to answer.

        Leaves, AND nodes and OR nodes are straightforward.  The
        work is all at a threshold node, where the root challenge
        [c] is shared out among the children by a polynomial, and
        one has to check that the children's announcements do not
        move when [c] moves.  They do not, for two different
        reasons.  A child the prover answers honestly announces
        before it sees its challenge at all.  A child the prover
        simulates receives a challenge that was fixed in advance, in
        the prover's randomness, and the interpolating polynomial
        reproduces that fixed value at that child's node no matter
        what [c] is. *)

    (** The shared-out challenge of a simulated child does not move
        when the root challenge moves.

        [expand_chalC c nodes vals] is the polynomial that passes
        through the point with coordinates [zero] and [c], and
        through each node in [nodes] paired with the corresponding
        value in [vals].  Those values are the challenges the prover
        pre-committed to for the children it will simulate.

        The hypotheses: [nodes] together with [zero] has no repeated
        element, so the interpolation problem is well posed;
        [nodes] and [vals] have the same length, so every node has
        a value; and [x] is one of the nodes.

        The conclusion is that the polynomial's value at [x] is the
        same for two different root challenges [c] and [c'].

        Why: by [expand_chal_nodes] from Composition.v, the
        interpolant through those points takes at each node exactly
        the value it was told to take there.  That value comes from
        [vals], which has nothing to do with [c].  So both sides
        equal the same entry of [vals], and the root challenge never
        enters.  The proof is just this observation, plus the
        bookkeeping of turning a statement about mapping over a list
        into a statement about one position in it. *)
    Lemma expand_chal_indep :
      ∀ (c c' x : F) (nodes vals : list F),
      List.NoDup (List.cons zero nodes) ->
      List.length nodes = List.length vals ->
      List.In x nodes ->
      expand_chalC c nodes vals x = expand_chalC c' nodes vals x.
    Proof.
      intros c c' x nodes vals hnd hl hin.
      pose proof (expand_chal_nodes (Hvec := Hvec) c nodes vals hnd hl) as h1.
      pose proof (expand_chal_nodes (Hvec := Hvec) c' nodes vals hnd hl) as h2.
      destruct (List.In_nth nodes x zero hin) as (j & hj & hx).
      rewrite <-hx.
      assert (ha : List.nth j (List.map (expand_chalC c nodes vals) nodes) zero =
        List.nth j vals zero).
      { rewrite h1; reflexivity. }
      assert (hb : List.nth j (List.map (expand_chalC c' nodes vals) nodes) zero =
        List.nth j vals zero).
      { rewrite h2; reflexivity. }
      rewrite (List.nth_indep _ zero (expand_chalC c nodes vals zero)) in ha;
      [| rewrite List.length_map; exact hj].
      rewrite (List.nth_indep _ zero (expand_chalC c' nodes vals zero)) in hb;
      [| rewrite List.length_map; exact hj].
      rewrite List.map_nth in ha, hb.
      rewrite ha, hb. reflexivity.
    Qed.

    (** A flagged child's node is one of the selected nodes.

        At a threshold node the prover marks, with a list of
        booleans [fl], which children it will simulate.
        [select_nodes xs fl] keeps the interpolation nodes of the
        marked children.  This lemma says the obvious thing: if
        position [j] is marked, then the node [xs] carries at
        position [j] really does appear in that selection.

        It exists so that [expand_chal_indep] can be applied to a
        simulated child: that lemma demands its point be one of the
        interpolation nodes, and this is where that side condition
        comes from.  The proof is a routine simultaneous induction
        on the list of nodes and the list of flags. *)
    Lemma select_nodes_in :
      ∀ (xs : list F) (fl : list bool) (j : nat),
      (j < List.length xs)%nat ->
      List.nth j fl false = true ->
      List.In (List.nth j xs zero) (select_nodes xs fl).
    Proof.
      intros xs.
      induction xs as [| x xs ih]; intros [| b fl] j hj hf; cbn in hj; try lia.
      + destruct j; cbn in hf; discriminate hf.
      + destruct j as [| j]; cbn in hf |- *.
        - subst b. left; reflexivity.
        - destruct b; [right |]; eapply ih; [lia | exact hf | lia | exact hf].
    Qed.

    (** The children of a threshold node announce the same thing
        under two challenge assignments that agree on the simulated
        children.

        This is the inductive heart of [prove_ann_independent].
        Read the arguments: [v] is the vector of children, [w]
        their optional witnesses, [s] their randomness, [seeds] the
        number of witness-carrying children the prover chooses to
        simulate anyway, and [chal] and [chal'] are two functions
        assigning a challenge to each child, offset by the starting
        index [i].

        The hypotheses:

        - the [vall] hypothesis says every child already has the
          property that its announcement ignores its challenge; this
          is the induction hypothesis from [comp_rel_ind'];
        - [wholds v w] says every witness that is present is a good
          one;
        - the last hypothesis says the two challenge assignments
          agree on every child the prover simulates.  They are
          allowed to differ everywhere else.

        Why the conclusion holds: each child is handled in one of
        two ways.  If it is proved honestly, its announcement does
        not depend on its challenge at all, by the first hypothesis,
        so the two assignments need not agree there.  If it is
        simulated, its announcement does depend on its challenge,
        but the two assignments were assumed to agree exactly there.
        Either way the head child announces the same thing, and the
        induction handles the tail. *)
    Lemma annlist_provelist_indep :
      ∀ (n : nat) (v : Vector.t comp_relC n) (w : wlist v) (s : rlist v)
        (seeds : nat) (chal chal' : nat -> F) (i : nat),
      vall (fun r => ∀ (w : comp_witnessC r) (s : comp_randC r) (c c' : F),
        comp_rel_holdsC r w ->
        transcript_ann r (comp_proveC r w s c) =
        transcript_ann r (comp_proveC r w s c')) v ->
      wholds v w ->
      (∀ j, (j < n)%nat -> List.nth j (sim_flags v w seeds) false = true ->
         chal (i + j)%nat = chal' (i + j)%nat) ->
      annlist v (provelist v w s (sim_flags v w seeds) chal i) =
      annlist v (provelist v w s (sim_flags v w seeds) chal' i).
    Proof.
      intros n v.
      induction v as [| r n v ih]; intros w s seeds chal chal' i hall hw hc; cbn.
      + reflexivity.
      + destruct hall as (hr & hall).
        destruct w as (ow & w'); cbn in hw |- *.
        destruct hw as (hw & hw').
        (* the head child is proved (its announcement is challenge-free
           by the hypothesis) or simulated (its two challenges agree) *)
        destruct ow as [x |].
        - destruct seeds as [| seeds]; cbn.
          * f_equal.
            { eapply hr; exact hw. }
            { eapply ih; [exact hall | exact hw' |].
              intros j hj hf. specialize (hc (S j) ltac:(lia) hf).
              rewrite Nat.add_succ_r in hc. exact hc. }
          * f_equal.
            { pose proof (hc 0 ltac:(lia) eq_refl) as hc0. rewrite Nat.add_0_r in hc0.
              rewrite hc0. reflexivity. }
            { eapply ih; [exact hall | exact hw' |].
              intros j hj hf. specialize (hc (S j) ltac:(lia) hf).
              rewrite Nat.add_succ_r in hc. exact hc. }
        - cbn. f_equal.
          { pose proof (hc 0 ltac:(lia) eq_refl) as hc0. rewrite Nat.add_0_r in hc0.
            rewrite hc0. reflexivity. }
          { eapply ih; [exact hall | exact hw' |].
            intros j hj hf. specialize (hc (S j) ltac:(lia) hf).
            rewrite Nat.add_succ_r in hc. exact hc. }
    Qed.

    (** An honest prover's announcement does not depend on the
        challenge.

        For any statement tree [r], any witness [w] that satisfies
        it, any randomness [rnd], and any two challenges [c] and
        [c'], the announcement part of the two honest transcripts is
        the same.

        This is what licenses the Fiat-Shamir definitions above.
        [nizk_prove] computes the announcement by running the prover
        at [zero], then hashes it, then runs the prover again at the
        resulting challenge.  Because of this lemma the second run
        carries the same announcement as the first, so the hash the
        verifier recomputes is the hash the prover used.  Without
        it, [nizk_prove] would be answering a challenge derived from
        an announcement it no longer sends.

        Note the hypothesis [comp_rel_holdsC r w]: a real witness is
        required.  For leaves, AND nodes and OR nodes it is not
        needed, but a threshold node uses it.  There the prover
        simulates exactly as many children as its polynomial has
        free points, and that count is only correct when it holds at
        least [t] witnesses.  The hypothesis is no burden, since
        completeness assumes a valid witness in any case.

        Why it is true, node by node.  A leaf announces
        [mat_evalC mat us], computed from the randomness alone, with
        no [c] in sight.  An AND node passes the same challenge to
        both children and the induction hypotheses apply.  An OR
        node proves one branch and simulates the other at the
        pre-committed challenge stored in the randomness, so again
        neither announcement sees [c].  A threshold node is the real
        case: the simulated children's challenges come out of the
        interpolant, and [expand_chal_indep] says the interpolant
        takes the pre-committed values at their nodes whatever [c]
        is.  Feeding that into [annlist_provelist_indep] finishes
        it.  The side conditions are the ones the [CThresh]
        constructor carries, namely that the nodes together with
        [zero] are distinct, plus the count of selected nodes, which
        is where the witness hypothesis is spent. *)
    Lemma prove_ann_independent :
      ∀ (r : comp_relC) (w : comp_witnessC r) (rnd : comp_randC r) (c c' : F),
      comp_rel_holdsC r w ->
      transcript_ann r (comp_proveC r w rnd c) =
      transcript_ann r (comp_proveC r w rnd c').
    Proof.
      intros r.
      induction r as [m n mat pub | rl rr ihl ihr | rl rr ihl ihr | t k xs rs Hxs Ht ihrs]
        using comp_rel_ind'.
      + intros *; cbn. reflexivity.
      + intros * hh; cbn in hh |- *. destruct hh as (hl & hr).
        f_equal; [eapply ihl; exact hl | eapply ihr; exact hr].
      + intros * hh; cbn in hh |- *.
        destruct w as [wl | wr]; cbn.
        - f_equal. eapply ihl; exact hh.
        - f_equal. eapply ihr; exact hh.
      + intros * hh; cbn in hh |- *.
        destruct hh as (hcount & hholds).
        pose proof (VectorSpec.length_to_list F k xs) as Hlen.
        set (xl := Vector.to_list xs) in *.
        set (fl := sim_flags rs w (wcount rs w - t)) in *.
        pose proof (wcount_le k rs w) as hle.
        (* a valid witness selects exactly k - t nodes *)
        assert (hsl : List.length (select_nodes xl fl) = (k - t)%nat).
        { unfold fl. rewrite select_nodes_length, sim_flags_count.
          rewrite Nat.min_l; lia.
          rewrite sim_flags_length; symmetry; exact Hlen. }
        eapply annlist_provelist_indep; [exact ihrs | exact hholds |].
        intros j hj hf.
        unfold chal_of. rewrite !Nat.add_0_l.
        eapply expand_chal_indep.
        - eapply nodup_zero_select; exact Hxs.
        - rewrite hsl, VectorSpec.length_to_list; reflexivity.
        - eapply select_nodes_in; [rewrite Hlen; exact hj | exact hf].
    Qed.

    (** ** Completeness of the non-interactive protocol *)

    (** An honestly produced non-interactive proof always verifies.

        Completeness is the promise that the protocol works when
        everybody is honest: a prover who really knows a witness is
        never rejected.  Here it says that for any statement tree
        [r], any hash function [hash], any witness [w] satisfying
        the relation, and any randomness [rnd], the proof produced
        by [nizk_prove] is accepted by [nizk_verify].

        The theorem holds for every hash function, with no
        assumption on it at all.  A constant hash would do.  That is
        not a weakness of the statement, it is the nature of
        completeness: hash quality is what soundness needs, not
        completeness.

        Why it is true: the verifier hashes the announcement of the
        transcript it received, and the prover hashed the
        announcement of the transcript it ran at [zero].  By
        [prove_ann_independent] those two announcements are equal,
        so both sides arrive at the same challenge.  The rest is
        completeness of the interactive protocol,
        [comp_completeness] in Composition.v, applied at that
        challenge. *)
    Theorem nizk_completeness :
      ∀ (r : comp_relC) (hash : comp_ann_t r -> F)
        (w : comp_witnessC r) (rnd : comp_randC r),
      comp_rel_holdsC r w ->
      nizk_verify r hash (nizk_prove r hash w rnd) = true.
    Proof.
      intros * ha.
      unfold nizk_verify, nizk_prove.
      set (c0 := hash (transcript_ann r (comp_proveC r w rnd zero))).
      rewrite (prove_ann_independent r w rnd c0 zero ha).
      fold c0.
      eapply (@comp_completeness F zero one add mul sub div opp inv Fdec
        G gid ginv gop gpow Gdec Hvec r w rnd c0 ha).
    Qed.

    (** End to end: from a statement in the source language to an
        accepting non-interactive proof.

        This is the previous theorem lifted to the level a user
        works at.  Dsl.v offers a small language of statements,
        [stmt], written in terms of named variables, and a
        [compile] function turning such a statement into a
        statement tree.  This corollary says that if the source
        statement is true of some assignment of values to those
        variables, then the compiled protocol can produce a
        non-interactive proof of it that verifies.

        The arguments and hypotheses:

        - [privs] is the vector of private variable names, [genv]
          and [penv] assign a group element and a field element to
          each name, and [node] supplies the interpolation points
          for threshold nodes;
        - [s] is the source statement and [wenv] assigns a field
          value to every variable, which is the user's secret data;
        - [wf_stmt] returning [true] says [s] is well formed, that
          is, every term mentions a declared private variable;
        - [nodupb] returning [true] says the declared private
          variables are pairwise different, so that the columns of
          the compiled matrices are unambiguous;
        - the hypothesis about [compile] returning [Some r] says
          compilation succeeded and produced the tree [r];
        - the hypothesis about [stmt_denote] says the statement is
          actually true under [wenv].

        The conclusion produces a witness [w] for [r] such that for
        every hash function and every choice of randomness the
        non-interactive proof verifies.  Note the order of the
        quantifiers: the witness is fixed first and works for all
        hash functions, which is what one wants, since the witness
        is the user's secret and does not depend on the encoding
        chosen for hashing.

        Why it is true: [compile_stmt_sound] from Dsl.v turns the
        truth of the source statement into a witness satisfying the
        compiled relation, and [nizk_completeness] then applies to
        that witness. *)
    Corollary compile_nizk_completeness :
      ∀ {V : Type} {vdec : ∀ x y : V, {x = y} + {x <> y}}
        {n : nat} (privs : Vector.t V n)
        (genv : V -> G) (penv : V -> F) (node : nat -> F)
        (s : @stmt F V) (r : comp_relC) (wenv : V -> F),
      wf_stmt (vdec := vdec) privs s = true ->
      nodupb (vdec := vdec) (Vector.to_list privs) = true ->
      @compile F zero add mul opp Fdec G gid ginv gop gpow V vdec n
        privs genv penv node s = Some r ->
      @stmt_denote F add mul opp G gid gop gpow V genv penv wenv s ->
      ∃ (w : comp_witnessC r),
        ∀ (hash : comp_ann_t r -> F) (rnd : comp_randC r),
        nizk_verify r hash (nizk_prove r hash w rnd) = true.
    Proof.
      intros * ha hb hc hd.
      destruct (compile_stmt_sound privs genv penv node (Hvec := Hvec) s r wenv ha hb hc hd)
        as (w & hw).
      exists w. intros hash rnd.
      eapply nizk_completeness. exact hw.
    Qed.

  End Proofs.

  (** ** The compact wire format

      A transcript has to travel over a wire, and the announcements
      are its bulkiest part: one group element per equation, at
      every leaf.  They are also redundant.  The verifier's check at
      a leaf is an equation relating the announcement, the
      challenge, the response and the public data, and it can be
      read in either direction.  Read forwards it tests an
      announcement that was sent.  Read backwards it computes the
      only announcement that could have been sent.

      So the compact format simply drops them.  It keeps the
      responses, and the sub-challenges that OR and threshold nodes
      need in order to reconstruct how the root challenge was split,
      and nothing else.  The verifier rebuilds each leaf
      announcement as the response evaluated through the leaf's
      matrix, multiplied by the public point raised to minus the
      challenge.  That formula is exactly the simulator's, which is
      no coincidence: the simulator exists precisely because this
      equation can be solved for the announcement.

      [comp_compact_recover] proves the round trip: for any
      transcript the verifier would have accepted, dropping the
      announcements and recomputing them returns the original
      transcript unchanged.  So nothing is lost by transmitting the
      compact form. *)
  Section Compact.

    (** As in the previous section, the proofs need [G] to be a
        vector space over [F], and the [Add Field] line enables the
        [field] tactic for the small algebraic identities. *)
    Context
      {Hvec : @vector_space F (@eq F) zero one add mul sub
        div opp inv G (@eq G) gid ginv gop gpow}.
    Add Field field : (@field_theory_for_stdlib_tactic F
      eq zero one opp add mul sub inv div vector_space_field).

    (** The type of a compact transcript, computed from the
        statement tree.

        Compare it with [comp_transcript] in Composition.v: every
        announcement has been removed, and everything else is kept.
        A [Leaf] with [n] private columns keeps only its response, a
        vector of [n] field elements.  An [CAnd] node keeps the pair
        of its children.  A [COr] node keeps the pair of its
        children plus the stored sub-challenge, which the verifier
        cannot derive on its own.  A [CThresh] node keeps its
        children plus the list of compressed challenges, the values
        of the sharing polynomial at the first few nodes. *)
    Fixpoint compact_t (r : comp_relC) : Type :=
      match r with
      | Leaf _ n _ _ => Vector.t F n
      | CAnd rl rr => (compact_t rl * compact_t rr)%type
      | COr rl rr => (compact_t rl * compact_t rr * F)%type
      | CThresh _ _ _ rs _ _ => (tlist_gen compact_t rs * list F)%type
      end.

    (** Compacting each child of a threshold node.

        The usual generic walker over the vector of children, taking
        the compaction function as its argument [cp], for the same
        reason as the walkers earlier in the file. *)
    Fixpoint projlist_gen (cp : ∀ r : comp_relC, comp_transcriptC r -> compact_t r)
      {n : nat} (v : Vector.t comp_relC n) {struct v} :
      tlist v -> tlist_gen compact_t v :=
      match v as v' return tlist v' -> tlist_gen compact_t v' with
      | [] => fun _ => tt
      | r :: v' => fun t => (cp r (fst t), projlist_gen cp v' (snd t))
      end.

    (** Compacting a transcript by dropping its announcements.

        [compact_proj r t] walks the transcript [t] and throws away
        every announcement, keeping the responses and the stored
        sub-challenges.  This is what the prover sends.

        At a [Leaf] the transcript is a pair of announcement and
        response, so the result is its second component.  At an
        [CAnd] node both children are compacted.  At a [COr] node
        both children are compacted and the stored sub-challenge is
        carried over.  At a [CThresh] node the children are
        compacted and the list of compressed challenges is carried
        over. *)
    Fixpoint compact_proj (r : comp_relC) : comp_transcriptC r -> compact_t r :=
      match r return comp_transcriptC r -> compact_t r with
      | Leaf _ _ _ _ => fun t => snd t
      | CAnd rl rr => fun t =>
          (compact_proj rl (fst t), compact_proj rr (snd t))
      | COr rl rr => fun t =>
          (compact_proj rl (fst (fst t)),
           compact_proj rr (snd (fst t)), snd t)
      | CThresh _ _ _ rs _ _ => fun t =>
          (projlist_gen compact_proj rs (fst t), snd t)
      end.

    (** Rebuilding each child of a threshold node.

        The generic walker for [compact_fill].  Besides the vector
        of children it takes a function [chal] assigning a challenge
        to each child by index, and a starting index; child number
        [i] is rebuilt at challenge [chal i].  The indexing matches
        the one [provelist_gen] and [verlist_gen] use in
        Composition.v, so that the challenges line up with the ones
        the prover and the verifier used. *)
    Fixpoint filllist_gen (cf : ∀ r : comp_relC, F -> compact_t r -> comp_transcriptC r)
      {n : nat} (v : Vector.t comp_relC n) {struct v} :
      (nat -> F) -> tlist_gen compact_t v -> nat -> tlist v :=
      match v as v' return (nat -> F) -> tlist_gen compact_t v' -> nat -> tlist v' with
      | [] => fun _ _ _ => tt
      | r :: v' => fun chal t i =>
          (cf r (chal i) (fst t), filllist_gen cf v' chal (snd t) (S i))
      end.

    (** Rebuilding a full transcript from the compact one and the
        challenge.

        [compact_fill r c cp] is the inverse of [compact_proj]: it
        puts the missing announcements back.  This is what the
        verifier runs on arriving data, and in the non-interactive
        setting [c] is the hash, so the verifier has it.

        At a [Leaf] each announcement is recovered from the
        verification equation.  The verifier's check says that the
        response, evaluated through the row of bases, equals the
        announcement times the public point raised to the
        challenge.  Solving for the announcement gives the row
        evaluation times the public point raised to minus the
        challenge, which is [gop (row_evalC row res) (p ^ (opp c))],
        applied to every row with [zip_with].  This is the same
        formula the simulator uses in [comp_simulate].

        At an [CAnd] node both children are rebuilt at the same
        challenge, since an AND passes its challenge down unchanged.
        At a [COr] node the stored sub-challenge is the left child's
        and the difference is the right child's, exactly as the
        verifier splits it.  At a [CThresh] node the sharing
        polynomial is reconstructed from the root challenge and the
        stored compressed values, and each child is rebuilt at the
        polynomial's value at its own node.

        The rebuilt announcements are correct by construction for
        any accepting transcript; that is the content of
        [comp_compact_recover] below.  For a transcript that would
        not have been accepted, [compact_fill] still returns
        something, but there is no claim that it means anything. *)
    Fixpoint compact_fill (r : comp_relC) : F -> compact_t r -> comp_transcriptC r :=
      match r return F -> compact_t r -> comp_transcriptC r with
      | Leaf m n mat pub => fun c res =>
          (zip_with (fun row p => gop (row_evalC row res) (p ^ (opp c))) mat pub, res)
      | CAnd rl rr => fun c t =>
          (compact_fill rl c (fst t), compact_fill rr c (snd t))
      | COr rl rr => fun c t =>
          (compact_fill rl (snd t) (fst (fst t)),
           compact_fill rr (c - snd t) (snd (fst t)), snd t)
      | CThresh t k xs rs _ _ => fun c tr =>
          (filllist_gen compact_fill rs
             (@chal_of F zero (Vector.to_list xs)
               (expand_chalC c (List.firstn (k - t) (Vector.to_list xs)) (snd tr)))
             (fst tr) 0,
           snd tr)
      end.

    (** The round trip works for every child of a threshold node.

        The [vall] hypothesis says the round trip is already known
        for each child; it is the induction hypothesis coming from
        [comp_rel_ind'].  The hypothesis about [verlist] says the
        verifier accepted every child at its own
        challenge.  The conclusion is that compacting all the
        children and refilling them returns the original
        transcripts.

        The proof is induction on the vector.  The verifier's
        acceptance is a boolean conjunction, so it splits into
        acceptance of the head and acceptance of the tail, and each
        half is handled by its own hypothesis. *)
    Lemma filllist_projlist :
      ∀ (n : nat) (v : Vector.t comp_relC n) (chal : nat -> F) (ts : tlist v) (i : nat),
      vall (fun r => ∀ (c : F) (t : comp_transcriptC r),
        comp_verifyC r c t = true -> compact_fill r c (compact_proj r t) = t) v ->
      verlist v chal ts i = true ->
      filllist_gen compact_fill v chal (projlist_gen compact_proj v ts) i = ts.
    Proof.
      intros n v.
      induction v as [| r n v ih]; intros chal ts i hall hv; cbn.
      + destruct ts; reflexivity.
      + destruct hall as (hr & hall).
        cbn in hv. eapply andb_true_iff in hv. destruct hv as (hv1 & hv2).
        rewrite (hr _ _ hv1), (ih chal (snd ts) (S i) hall hv2).
        destruct ts; reflexivity.
    Qed.

    (** Dropping the announcements loses nothing, for any transcript
        the verifier accepts.

        If [comp_verifyC r c t] returns [true], then compacting [t]
        and refilling it at the same challenge [c] gives back
        exactly [t].  So the compact encoding is a faithful
        representation of accepting transcripts, and a verifier may
        safely be handed the compact form instead of the full one.

        Note that acceptance is a hypothesis, not a conclusion.  The
        claim is not that every compact object expands to a valid
        transcript; it is that a valid transcript survives the round
        trip.

        Why it is true: at a leaf, acceptance means the verification
        equation holds for every row, which is
        [verify_linear_relation_forward] in LinearRelation.v.  That
        equation says the row evaluation of the response equals the
        announcement times the public point raised to the challenge.
        Multiplying both sides by the public point raised to minus
        the challenge leaves the announcement alone, because the two
        exponents add to [zero] and a group element raised to [zero]
        is the identity.  Those two steps are the vector-space laws
        [vector_space_smul_distributive_fadd] and
        [vector_space_field_zero].  At the other nodes acceptance is
        a conjunction of the children's acceptance, the challenges
        the refilling uses are the very ones the verifier used, and
        the induction hypotheses apply directly. *)
    Theorem comp_compact_recover :
      ∀ (r : comp_relC) (c : F) (t : comp_transcriptC r),
      comp_verifyC r c t = true ->
      compact_fill r c (compact_proj r t) = t.
    Proof.
      intros r.
      induction r as [m n mat pub | rl rr ihl ihr | rl rr ihl ihr | t k xs rs Hxs Ht ihrs]
        using comp_rel_ind'.
      + intros * hv.
        destruct t as (comm & res); cbn.
        f_equal.
        eapply Vector.eq_nth_iff.
        intros i j hij; subst.
        rewrite nth_zip_with.
        pose proof (verify_linear_relation_forward m n mat pub comm c res hv j) as hf.
        rewrite hf.
        rewrite <-associative.
        rewrite <-(@vector_space_smul_distributive_fadd
          F (@eq F) zero one add mul sub div opp inv
          G (@eq G) gid ginv gop gpow Hvec).
        assert (ha : add c (opp c) = zero). { field. }
        rewrite ha.
        rewrite (@vector_space_field_zero
          F (@eq F) zero one add mul sub div opp inv
          G (@eq G) gid ginv gop gpow Hvec).
        rewrite right_identity.
        reflexivity.
      + intros * hv; cbn in hv |- *.
        eapply andb_true_iff in hv. destruct hv as (hvl & hvr).
        rewrite (ihl _ _ hvl), (ihr _ _ hvr).
        destruct t as (tl & tr); reflexivity.
      + intros * hv; cbn in hv |- *.
        eapply andb_true_iff in hv. destruct hv as (hvl & hvr).
        rewrite (ihl _ _ hvl), (ihr _ _ hvr).
        destruct t as ((tl & tr) & c1); reflexivity.
      + intros * hv; cbn in hv |- *.
        eapply andb_true_iff in hv. destruct hv as (hlen & hvl).
        rewrite (filllist_projlist k rs _ (fst t0) 0 ihrs hvl).
        destruct t0; reflexivity.
    Qed.

  End Compact.

End Nizk.
