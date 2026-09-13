From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool List.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import Util.
From Crypto Require Import Sigma.
From Compiler Require Import
  LinearRelation Composition.

Import VectorNotations.

(** * Serialization: the wire format for composed transcripts

    ** What a wire format is

    A proof has to travel.  The prover builds a transcript, a piece
    of structured data living in memory, and the verifier, somewhere
    else, has to receive it and check it.  Between the two there is
    only a flat sequence of values.  A wire format is the pair of
    functions that flattens a transcript into such a sequence
    ([encode]) and rebuilds the transcript from it ([decode]).

    This is exactly the sort of code that is easy to get subtly
    wrong and where a mistake is expensive.  A decoder that reads
    one element too few, or that reassembles the parts in the wrong
    order, can hand the verifier a transcript that is not the one
    the prover sent.  Depending on which side of the check the error
    falls, that either breaks honest proofs or, much worse, lets a
    dishonest one through.  So the format is proved correct here
    rather than tested.

    ** Vocabulary

    A transcript of a sigma protocol has three parts.  The
    announcement is the prover's first message, a group element or
    several, committing it to some random choice.  The challenge is
    the verifier's reply, a single scalar the prover could not
    predict.  The response is the prover's last message, computed
    from its secret, its randomness and that challenge.  The
    verifier accepts if announcement, challenge and response satisfy
    a fixed equation.

    The simulator is a function that produces an accepting
    transcript for a given challenge without knowing any secret.  It
    is what makes the protocol zero knowledge, and inside a
    composed proof it is also used for real: at an OR node the
    prover genuinely knows only one branch and simulates the other.

    In this development a transcript is not a flat triple but a tree,
    because the statement itself is a tree ([comp_rel] of
    Composition.v, with leaf, AND, OR and threshold nodes).  A leaf
    transcript is an announcement and a response.  Its challenge is
    not stored: it comes from the parent.  An OR node additionally
    stores one scalar, the challenge given to the left branch, from
    which the right branch's challenge is the difference.  A
    threshold node additionally stores a list of compressed
    challenges.

    ** The tagged encoding

    The wire is a list of values, each of which is either a scalar
    of [F] or an element of the group [G].  A value carries a tag
    saying which it is: [inl] for a scalar, [inr] for a group
    element.  Since the two are different types, a decoder that
    asked for a group element and found a scalar has no way to
    coerce one into the other, and the tag makes the decoder notice
    and fail instead of silently going on.  The readers
    [read_points] and [read_scalars] are the two ends of that
    discipline.

    ** Decoding is driven by the statement tree

    There are no length prefixes anywhere in the format.  None are
    needed, because both sides already know the statement being
    proved, and the statement fixes the shape of every transcript
    for it.  A leaf [Leaf m n mat pub] has an announcement of [m]
    group elements and a response of [n] scalars, so the decoder
    reads exactly [m] then exactly [n].  An AND reads its left child
    then its right.  An OR reads both children and then one scalar.
    Every [decode] call is therefore a recursion over [r], the same
    tree the encoder walked, and the two stay in step by
    construction.  The format is compact for the same reason: it
    carries data only, no framing.

    ** The one side condition

    A threshold node is the single place where the type of a
    transcript does not pin down its size.  A node [CThresh t k ...]
    has [k] children and requires at least [t] of them; its
    transcript carries the [k - t] compressed challenges as a plain
    [list F], and a list type says nothing about length.  The
    decoder reads exactly [k - t] of them, because that is what the
    tree prescribes, so a transcript whose list has some other
    length cannot survive a round trip: it was never a legal
    transcript in the first place.

    [transcript_wf] is the predicate that rules those out.  It walks
    the tree and requires at every threshold node that the stored
    list has length exactly [k - t].  It says nothing anywhere else,
    since the types already do.

    ** Results

    [serialize_deserialize] is the round trip, in the form a real
    network layer needs.  It does not merely say that encoding then
    decoding gives back the transcript; it says that decoding the
    encoding followed by arbitrary further bytes returns the
    original transcript and hands back that remainder untouched:
    [decode r (encode r t ++ rest) = Some (t, rest)].  This is the
    statement one needs to decode a transcript out of a stream that
    continues with something else, and it is what makes the format
    composable, since encoding a node is encoding its children one
    after another.

    The last group of lemmas shows that the side condition costs
    nothing in practice.  [prove_wf] says every transcript the
    prover builds is well formed, [simulate_wf] says the same of the
    simulator, and [verify_wf] says that any transcript the verifier
    accepts is well formed, whoever produced it.  Together they say
    that the transcripts one actually meets are always in the domain
    of the round-trip theorem. *)
Section Serialization.

  (** ** Parameters

      Everything is parametric, so no particular group or prime is
      baked in.

      - [F] is the field of scalars, with constants [zero] and
        [one], operations [add], [mul], [sub], [div], [opp] and
        [inv], and a procedure [Fdec] deciding equality.
      - [G] is the group, with identity [gid], inverse [ginv],
        group operation [gop], exponentiation [gpow], and a
        procedure [Gdec] deciding equality.  [Gdec] is what lets the
        verifier be a boolean test rather than a proposition. *)
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

  (** Shorthands for the machinery of Composition.v, already applied
      to this section's field and group.

      - [comp_relC] is the statement tree; its constructors are
        [Leaf], [CAnd], [COr] and [CThresh].
      - [comp_transcriptC r] is the type of transcripts for the
        statement [r], computed from the shape of [r].
      - [comp_witnessC r] and [comp_randC r] are, likewise, the
        types of witnesses and of prover randomness for [r].
      - [comp_proveC], [comp_simulateC] and [comp_verifyC] are the
        honest prover, the simulator and the verifier.
      - [tlist v] is the type of one transcript per child, for a
        vector [v] of statements; a threshold node holds its
        children in such a vector. *)
  #[local] Notation comp_relC := (@comp_rel F zero G).
  #[local] Notation comp_transcriptC := (@comp_transcript F zero G).
  #[local] Notation comp_witnessC := (@comp_witness F zero G).
  #[local] Notation comp_randC := (@comp_rand F zero G).
  #[local] Notation comp_proveC :=
    (@comp_prove F zero one add mul sub opp inv G gid gop gpow).
  #[local] Notation comp_simulateC :=
    (@comp_simulate F zero one add mul sub opp inv G gid gop gpow).
  #[local] Notation comp_verifyC :=
    (@comp_verify F zero one add mul sub inv G gid gop gpow Gdec).
  #[local] Notation tlist := (tlist_gen comp_transcriptC).

  (** ** Tagged values on the wire

      A wire is a flat list of values, each tagged as either a
      scalar or a group element.  [inl] marks a scalar of [F] and
      [inr] a group element of [G].  A real implementation would
      turn each of these into bytes; that last step is orthogonal to
      the tree structure and is not modelled here. *)
  Definition wire : Type := list (F + G).

  (** [read_points m l] takes the first [m] values off the wire [l]
      and returns them as a vector of [m] group elements, together
      with whatever is left of [l].

      It returns [None] if the wire runs out early, or if one of the
      values it meets is tagged as a scalar.  That second check is
      the point of the tags: a decoder expecting an announcement
      never mistakes a response for one. *)
  Fixpoint read_points (m : nat) (l : wire) : option (Vector.t G m * wire) :=
    match m with
    | 0 => Some ([], l)
    | S m' =>
        match l with
        | List.cons (inr g) l' =>
            match read_points m' l' with
            | Some (v, l'') => Some (g :: v, l'')
            | None => None
            end
        | _ => None
        end
    end.

  (** [read_scalars n l] is the same for scalars: it takes the first
      [n] values off [l], insisting that each is tagged [inl], and
      returns them as a vector of [n] field elements together with
      the rest of the wire. *)
  Fixpoint read_scalars (n : nat) (l : wire) : option (Vector.t F n * wire) :=
    match n with
    | 0 => Some ([], l)
    | S n' =>
        match l with
        | List.cons (inl f) l' =>
            match read_scalars n' l' with
            | Some (v, l'') => Some (f :: v, l'')
            | None => None
            end
        | _ => None
        end
    end.

  (** [write_points v] is the encoder matching [read_points]: it
      tags each of the [m] group elements of [v] with [inr] and lays
      them out in order. *)
  Definition write_points {m : nat} (v : Vector.t G m) : wire :=
    List.map inr (Vector.to_list v).

  (** [write_scalars v] is the encoder matching [read_scalars] for a
      vector: it tags each of the [n] field elements of [v] with
      [inl]. *)
  Definition write_scalars {n : nat} (v : Vector.t F n) : wire :=
    List.map inl (Vector.to_list v).

  (** [write_scalar_list l] is the same for a plain list of scalars
      of unknown length.  It is used only at a threshold node, for
      the compressed challenges, which are the one part of a
      transcript whose type does not fix how many there are. *)
  Definition write_scalar_list (l : list F) : wire := List.map inl l.

  (** ** Well-formed transcripts *)

  (** [wflist_gen cw v ts] lifts a per-statement predicate [cw] to a
      whole list of children: it says that [cw] holds of each
      transcript in [ts], the transcripts of the children [v].

      It exists for a technical reason.  A threshold node holds its
      children in a vector, so [comp_rel] is a nested inductive type
      and a recursive definition cannot simply call itself on the
      children.  The pattern used throughout Composition.v, and
      followed here, is to write a generic walker parameterised by
      the function being defined and tie the knot at the call
      site. *)
  Fixpoint wflist_gen (cw : ∀ r : comp_relC, comp_transcriptC r -> Prop)
    {n : nat} (v : Vector.t comp_relC n) {struct v} : tlist v -> Prop :=
    match v as v' return tlist v' -> Prop with
    | [] => fun _ => True
    | r :: v' => fun t => cw r (fst t) ∧ wflist_gen cw v' (snd t)
    end.

  (** [transcript_wf r t] says that the transcript [t] has the
      shape a transcript for the statement [r] is supposed to have,
      in the one respect the types do not already guarantee.

      At a leaf there is nothing to say: the announcement and the
      response are vectors whose lengths are part of their type.
      At an AND and at an OR the condition is just passed down to
      the two children.  Only at a threshold node is there real
      content: the stored list of compressed challenges must have
      length exactly [k - t], where [k] is the number of children
      and [t] the threshold.  That is the number the decoder will
      read, so it is the number that must be there.

      This is the side condition of the round-trip theorem, and the
      last section of the file shows it is never a real restriction. *)
  Fixpoint transcript_wf (r : comp_relC) : comp_transcriptC r -> Prop :=
    match r return comp_transcriptC r -> Prop with
    | Leaf _ _ _ _ => fun _ => True
    | CAnd rl rr => fun t => transcript_wf rl (fst t) ∧ transcript_wf rr (snd t)
    | COr rl rr => fun t =>
        transcript_wf rl (fst (fst t)) ∧ transcript_wf rr (snd (fst t))
    | CThresh t k _ rs _ _ => fun tr =>
        List.length (snd tr) = (k - t)%nat ∧ wflist_gen transcript_wf rs (fst tr)
    end.

  (** ** Encoding and decoding *)

  (** [enclist_gen ce v ts] encodes the transcripts of all the
      children of a threshold node, one after another, by appending
      their encodings in order.  Like [wflist_gen] it is a generic
      walker, parameterised by the encoder [ce] so that [encode] can
      pass itself in. *)
  Fixpoint enclist_gen (ce : ∀ r : comp_relC, comp_transcriptC r -> wire)
    {n : nat} (v : Vector.t comp_relC n) {struct v} : tlist v -> wire :=
    match v as v' return tlist v' -> wire with
    | [] => fun _ => List.nil
    | r :: v' => fun t => List.app (ce r (fst t)) (enclist_gen ce v' (snd t))
    end.

  (** [encode r t] flattens the transcript [t] of the statement [r]
      into a wire.

      It walks the tree.  A leaf writes its announcement, as [m]
      tagged group elements, followed by its response, as [n] tagged
      scalars.  An AND writes its left child then its right.  An OR
      writes both children and then the one scalar it stores, the
      challenge of the left branch.  A threshold node writes all its
      children and then its compressed challenges.

      Nothing else is written: no tags for the nodes, no lengths.
      The tree is the header, and both parties have it already. *)
  Fixpoint encode (r : comp_relC) : comp_transcriptC r -> wire :=
    match r return comp_transcriptC r -> wire with
    | Leaf m n _ _ => fun t =>
        List.app (write_points (fst t)) (write_scalars (snd t))
    | CAnd rl rr => fun t =>
        List.app (encode rl (fst t)) (encode rr (snd t))
    | COr rl rr => fun t =>
        List.app (encode rl (fst (fst t)))
          (List.app (encode rr (snd (fst t)))
            (List.cons (inl (snd t)) List.nil))
    | CThresh _ _ _ rs _ _ => fun t =>
        List.app (enclist_gen encode rs (fst t)) (write_scalar_list (snd t))
    end.

  (** [declist_gen cd v l] is the counterpart of [enclist_gen]: it
      decodes one transcript per child of a threshold node, in
      order, threading the remaining wire from each child to the
      next, and fails as soon as any child fails. *)
  Fixpoint declist_gen (cd : ∀ r : comp_relC, wire -> option (comp_transcriptC r * wire))
    {n : nat} (v : Vector.t comp_relC n) {struct v} : wire -> option (tlist v * wire) :=
    match v as v' return wire -> option (tlist v' * wire) with
    | [] => fun l => Some (tt, l)
    | r :: v' => fun l =>
        match cd r l with
        | Some (t, l1) =>
            match declist_gen cd v' l1 with
            | Some (ts, l2) => Some ((t, ts), l2)
            | None => None
            end
        | None => None
        end
    end.

  (** [decode r l] reads a transcript for the statement [r] off the
      front of the wire [l], and returns it together with the part
      of [l] that was not consumed.  It returns [None] if the wire
      does not have the right shape.

      Each case mirrors one case of [encode], and each knows from
      [r] alone how much to read.  A leaf reads [m] group elements
      and then [n] scalars.  An AND decodes its left child and feeds
      the leftover to its right child.  An OR decodes both children
      and then insists that the next value is a scalar, the stored
      challenge [c1].  A threshold node decodes all its children and
      then reads exactly [k - t] scalars, turning them back into a
      list.

      The leftover wire is returned rather than required to be
      empty.  That is what lets a caller decode one transcript out
      of a longer stream, and it is also what makes the recursive
      cases work at all, since a child hands its leftover to its
      sibling. *)
  Fixpoint decode (r : comp_relC) (l : wire) : option (comp_transcriptC r * wire) :=
    match r return option (comp_transcriptC r * wire) with
    | Leaf m n _ _ =>
        match read_points m l with
        | Some (comm, l1) =>
            match read_scalars n l1 with
            | Some (res, l2) => Some ((comm, res), l2)
            | None => None
            end
        | None => None
        end
    | CAnd rl rr =>
        match decode rl l with
        | Some (tl, l1) =>
            match decode rr l1 with
            | Some (tr, l2) => Some ((tl, tr), l2)
            | None => None
            end
        | None => None
        end
    | COr rl rr =>
        match decode rl l with
        | Some (tl, l1) =>
            match decode rr l1 with
            | Some (tr, l2) =>
                match l2 with
                | List.cons (inl c1) l3 => Some ((tl, tr, c1), l3)
                | _ => None
                end
            | None => None
            end
        | None => None
        end
    | CThresh t k _ rs _ _ =>
        match declist_gen decode rs l with
        | Some (ts, l1) =>
            match read_scalars (k - t) l1 with
            | Some (cs, l2) => Some ((ts, Vector.to_list cs), l2)
            | None => None
            end
        | None => None
        end
    end.

  (** ** The round trip *)

  (** Reading back what was written, for group elements: [write_points]
      followed by [read_points] returns the original vector and
      whatever was appended after it.

      Carrying the extra wire [rest] is not a generalisation for its
      own sake.  It strengthens the induction hypothesis, since the
      tail of the vector is followed by [rest] as well, and it is
      the form the recursive cases of the main theorem need, where
      what follows a child on the wire is its sibling.  The proof is
      induction on [m], peeling one element off both sides at each
      step. *)
  Lemma read_write_points :
    ∀ (m : nat) (v : Vector.t G m) (rest : wire),
    read_points m (List.app (write_points v) rest) = Some (v, rest).
  Proof.
    induction m as [| m ih]; intros *.
    + rewrite (vector_inv_0 v). reflexivity.
    + destruct (vector_inv_S v) as (vh & vt & ha); subst.
      change (write_points (vh :: vt)) with (List.cons (inr vh) (write_points vt)).
      cbn [List.app read_points].
      rewrite (ih vt rest). reflexivity.
  Qed.

  (** The same for scalars: [write_scalars] followed by
      [read_scalars] returns the original vector and the untouched
      remainder.  Induction on [n]. *)
  Lemma read_write_scalars :
    ∀ (n : nat) (v : Vector.t F n) (rest : wire),
    read_scalars n (List.app (write_scalars v) rest) = Some (v, rest).
  Proof.
    induction n as [| n ih]; intros *.
    + rewrite (vector_inv_0 v). reflexivity.
    + destruct (vector_inv_S v) as (vh & vt & ha); subst.
      change (write_scalars (vh :: vt)) with (List.cons (inl vh) (write_scalars vt)).
      cbn [List.app read_scalars].
      rewrite (ih vt rest). reflexivity.
  Qed.

  (** The same for a plain list of scalars, which is how the
      compressed challenges of a threshold node are written.

      Note the length: the reader is asked for exactly
      [List.length l] scalars, and it gets back [Vector.of_list l],
      the list turned into a vector of that length.  This is where
      the well-formedness condition will be used in the main proof:
      the decoder asks for [k - t] scalars, not for
      [List.length l], and the two agree precisely when the
      transcript is well formed. *)
  Lemma read_write_scalar_list :
    ∀ (l : list F) (rest : wire),
    read_scalars (List.length l) (List.app (write_scalar_list l) rest) =
    Some (Vector.of_list l, rest).
  Proof.
    induction l as [| x l ih]; intros rest.
    + reflexivity.
    + unfold write_scalar_list; cbn [List.map List.length List.app read_scalars].
      unfold write_scalar_list in ih. rewrite (ih rest). reflexivity.
  Qed.

  (** The round trip for the children of a threshold node.

      Two hypotheses are needed.  The first, written with [vall],
      says the round trip already holds for each child; this is the
      induction hypothesis supplied by [comp_rel_ind'], the
      induction principle for the nested tree type.  The second says
      the transcripts of the children are all well formed.  The
      conclusion is that decoding the concatenated encodings returns
      the children's transcripts and the untouched remainder.

      The proof is induction over the vector of children.  At each
      step the associativity of append ([List.app_assoc]) exposes
      the first child's encoding at the front of the wire, the first
      hypothesis consumes it and hands back the rest, and the
      induction hypothesis takes care of the remaining children. *)
  Lemma declist_enclist :
    ∀ (n : nat) (v : Vector.t comp_relC n) (ts : tlist v) (rest : wire),
    vall (fun r => ∀ (t : comp_transcriptC r) (rest : wire),
      transcript_wf r t ->
      decode r (List.app (encode r t) rest) = Some (t, rest)) v ->
    wflist_gen transcript_wf v ts ->
    declist_gen decode v (List.app (enclist_gen encode v ts) rest) = Some (ts, rest).
  Proof.
    intros n v.
    induction v as [| r n v ih]; intros ts rest hall hwf; cbn.
    + destruct ts; reflexivity.
    + destruct hall as (hr & hall). destruct hwf as (hwf & hwf').
      rewrite <-List.app_assoc.
      rewrite (hr (fst ts) _ hwf).
      rewrite (ih (snd ts) rest hall hwf').
      destruct ts; reflexivity.
  Qed.

  (** The round trip, and the main theorem of the file.

      If the transcript [t] is well formed, then encoding it,
      appending any further data [rest], and decoding the result
      gives back exactly [t] together with [rest] unchanged.

      Two things are being claimed at once.  That [t] comes back
      says the format loses nothing: the verifier checks the
      transcript the prover meant to send.  That [rest] comes back
      unchanged says the decoder consumed exactly the bytes of [t]
      and not one more, which is what lets transcripts be
      concatenated, and is what the recursive cases rely on when a
      child hands its leftover to its sibling.

      The proof is structural induction on [r], using [comp_rel_ind']
      so that a threshold node gets an induction hypothesis for each
      of its children.  Every case has the same shape: rewrite the
      append so that this node's own bytes sit at the front,
      discharge them with the matching reader lemma or the induction
      hypothesis, and pass the remainder on.  Well-formedness is
      used exactly once, in the threshold case, to know that the
      [k - t] scalars the decoder asks for are the
      [List.length (snd tr)] scalars that were actually written. *)
  Theorem serialize_deserialize :
    ∀ (r : comp_relC) (t : comp_transcriptC r) (rest : wire),
    transcript_wf r t ->
    decode r (List.app (encode r t) rest) = Some (t, rest).
  Proof.
    intros r.
    induction r as [m n mat pub | rl rr ihl ihr | rl rr ihl ihr | t k xs rs Hxs Ht ihrs]
      using comp_rel_ind'; intros tr rest hwf.
    + destruct tr as (comm & res).
      cbn [encode decode].
      rewrite <-List.app_assoc.
      rewrite read_write_points.
      rewrite read_write_scalars.
      reflexivity.
    + destruct tr as (tl & tr'); cbn in hwf |- *.
      destruct hwf as (hl & hr).
      rewrite <-List.app_assoc.
      rewrite (ihl tl _ hl).
      rewrite (ihr tr' _ hr).
      reflexivity.
    + destruct tr as ((tl & tr') & c1); cbn in hwf |- *.
      destruct hwf as (hl & hr).
      rewrite <-List.app_assoc.
      rewrite (ihl tl _ hl).
      rewrite <-List.app_assoc.
      rewrite (ihr tr' _ hr).
      reflexivity.
    + destruct tr as (ts & cs); cbn in hwf |- *.
      destruct hwf as (hlen & hwf).
      rewrite <-List.app_assoc.
      rewrite (declist_enclist k rs ts _ ihrs hwf).
      rewrite <-hlen.
      rewrite read_write_scalar_list.
      rewrite VectorSpec.to_list_of_list_opp.
      reflexivity.
  Qed.

  (** The special case where nothing follows the transcript on the
      wire: decoding an encoding on its own returns the transcript
      and an empty remainder.

      This is the statement one usually quotes, but it is the weaker
      one; it follows from the theorem above by taking [rest] to be
      the empty list. *)
  Corollary serialize_deserialize_full :
    ∀ (r : comp_relC) (t : comp_transcriptC r),
    transcript_wf r t ->
    decode r (encode r t) = Some (t, List.nil).
  Proof.
    intros * hwf.
    pose proof (serialize_deserialize r t List.nil hwf) as ha.
    rewrite List.app_nil_r in ha.
    exact ha.
  Qed.

  (** ** Everyone who matters produces well-formed transcripts

      The round trip assumes [transcript_wf].  The lemmas below show
      that this assumption is free: it holds of every transcript the
      honest prover produces, of every transcript the simulator
      produces, and of every transcript the verifier accepts.  Since
      a transcript the verifier rejects is of no interest, nothing
      that can ever matter falls outside the theorem. *)

  (** Simulating all the children of a threshold node yields well-formed
      transcripts, given that simulating each child does.  This is
      the list-level step of [simulate_wf], separated out because
      the children live in a vector; [vall] carries the per-child
      hypothesis. *)
  Lemma wflist_simlist :
    ∀ (n : nat) (v : Vector.t comp_relC n) (s : tlist_gen comp_randC v)
      (chal : nat -> F) (i : nat),
    vall (fun r => ∀ (s : comp_randC r) (c : F),
      transcript_wf r (comp_simulateC r s c)) v ->
    wflist_gen transcript_wf v (simlist_gen comp_simulateC v s chal i).
  Proof.
    intros n v.
    induction v as [| r n v ih]; intros s chal i hall; cbn.
    + exact I.
    + destruct hall as (hr & hall).
      split; [eapply hr | eapply ih; exact hall].
  Qed.

  (** Every transcript produced by the simulator is well formed.

      The simulator is given randomness [s] and a challenge [c] and
      returns an accepting transcript without any witness.  At a
      threshold node it emits the [k - t] free challenges it was
      handed as randomness; those come from a vector of that exact
      length, so converting it to a list gives a list of that length
      ([VectorSpec.length_to_list]).  Every other case is immediate
      or is the two children. *)
  Lemma simulate_wf :
    ∀ (r : comp_relC) (s : comp_randC r) (c : F),
    transcript_wf r (comp_simulateC r s c).
  Proof.
    intros r.
    induction r as [m n mat pub | rl rr ihl ihr | rl rr ihl ihr | t k xs rs Hxs Ht ihrs]
      using comp_rel_ind'; intros s c; cbn.
    + exact I.
    + split; [eapply ihl | eapply ihr].
    + split; [eapply ihl | eapply ihr].
    + split; [eapply VectorSpec.length_to_list | eapply wflist_simlist; exact ihrs].
  Qed.

  (** The list-level step of [prove_wf]: proving or simulating each
      child of a threshold node yields well-formed transcripts.

      At each child the prover either runs honestly, when it has a
      witness and the child is not flagged for simulation, or
      simulates.  Both alternatives give a well-formed transcript,
      the first by the per-child hypothesis and the second by
      [simulate_wf], so the case analysis on the flag and on the
      presence of a witness closes every branch. *)
  Lemma wflist_provelist :
    ∀ (n : nat) (v : Vector.t comp_relC n) (w : wlist_gen comp_witnessC v)
      (s : tlist_gen comp_randC v) (fl : list bool) (chal : nat -> F) (i : nat),
    vall (fun r => ∀ (w : comp_witnessC r) (s : comp_randC r) (c : F),
      transcript_wf r (comp_proveC r w s c)) v ->
    wflist_gen transcript_wf v
      (provelist_gen comp_proveC comp_simulateC v w s fl chal i).
  Proof.
    intros n v.
    induction v as [| r n v ih]; intros w s fl chal i hall; cbn.
    + exact I.
    + destruct hall as (hr & hall).
      split; [| eapply ih; exact hall].
      destruct (fst w) as [x |]; [destruct fl as [| [|] fl] |]; try (eapply hr).
      all: eapply simulate_wf.
  Qed.

  (** Every transcript produced by the honest prover is well formed.

      The only case with content is again the threshold node.  There
      the prover does not take its compressed challenges from
      randomness; it computes them, by evaluating the challenge
      polynomial at the first [k - t] interpolation nodes.  That is
      a [List.map] over [List.firstn (k - t)] of the node list, so
      its length is [k - t] as long as there are at least that many
      nodes, which holds because there are [k] of them and
      [t <= k]. *)
  Lemma prove_wf :
    ∀ (r : comp_relC) (w : comp_witnessC r) (s : comp_randC r) (c : F),
    transcript_wf r (comp_proveC r w s c).
  Proof.
    intros r.
    induction r as [m n mat pub | rl rr ihl ihr | rl rr ihl ihr | t k xs rs Hxs Ht ihrs]
      using comp_rel_ind'; intros w s c; cbn.
    + exact I.
    + split; [eapply ihl | eapply ihr].
    + destruct w as [wl | wr]; cbn; split;
      first [eapply ihl | eapply ihr | eapply simulate_wf].
    + split.
      - rewrite List.length_map. eapply List.firstn_length_le.
        rewrite VectorSpec.length_to_list. lia.
      - eapply wflist_provelist; exact ihrs.
  Qed.

  (** The list-level step of [verify_wf]: if the verifier accepts
      every child of a threshold node, then every child's transcript
      is well formed.  The verifier for a list of children is a
      conjunction of boolean checks, so accepting the whole list
      means accepting each child. *)
  Lemma wflist_verlist :
    ∀ (n : nat) (v : Vector.t comp_relC n) (chal : nat -> F) (ts : tlist v) (i : nat),
    vall (fun r => ∀ (c : F) (t : comp_transcriptC r),
      comp_verifyC r c t = true -> transcript_wf r t) v ->
    verlist_gen comp_verifyC v chal ts i = true ->
    wflist_gen transcript_wf v ts.
  Proof.
    intros n v.
    induction v as [| r n v ih]; intros chal ts i hall hv; cbn.
    + exact I.
    + destruct hall as (hr & hall).
      cbn in hv. eapply andb_true_iff in hv. destruct hv as (hv1 & hv2).
      split; [eapply hr; exact hv1 | eapply ih; [exact hall | exact hv2]].
  Qed.

  (** Any transcript the verifier accepts is well formed, no matter
      who produced it.

      This is the lemma that makes the side condition harmless on
      the receiving side, where the transcript arrives from someone
      possibly dishonest.  The reason it is true is that the
      verifier already performs the check: at a threshold node its
      very first test is [Nat.eqb] comparing the length of the
      stored challenge list with [k - t], and it rejects outright if
      they differ.  So [transcript_wf] asks for nothing the verifier
      does not already insist on, and the proof simply reads that
      test out of the accepting boolean and recurses into the
      children. *)
  Lemma verify_wf :
    ∀ (r : comp_relC) (c : F) (t : comp_transcriptC r),
    comp_verifyC r c t = true -> transcript_wf r t.
  Proof.
    intros r.
    induction r as [m n mat pub | rl rr ihl ihr | rl rr ihl ihr | t k xs rs Hxs Ht ihrs]
      using comp_rel_ind'; intros c tr hv; cbn in hv |- *.
    + exact I.
    + eapply andb_true_iff in hv. destruct hv as (h1 & h2).
      split; [eapply ihl; exact h1 | eapply ihr; exact h2].
    + eapply andb_true_iff in hv. destruct hv as (h1 & h2).
      split; [eapply ihl; exact h1 | eapply ihr; exact h2].
    + eapply andb_true_iff in hv. destruct hv as (h1 & h2).
      split; [eapply PeanoNat.Nat.eqb_eq; exact h1
             | eapply wflist_verlist; [exact ihrs | exact h2]].
  Qed.

End Serialization.
