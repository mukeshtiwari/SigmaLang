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

(** * Decide: establishing the composed relation by computation

    ** Why a boolean version is needed

    Composition.v builds a statement tree [comp_rel] out of four
    kinds of node: a [Leaf] holding a system of group equations, an
    [CAnd] node joining two sub-statements, a [COr] node offering a
    choice of two sub-statements, and a [CThresh] node asking that
    at least [t] out of [k] children hold.  For each such tree it
    also computes the type [comp_witness] of the secret data a
    prover would have to know, and the predicate [comp_rel_holds],
    which says that a given piece of secret data really does satisfy
    the tree.

    A witness is exactly that secret data: the exponents at a leaf,
    a tagged choice of branch at an OR node, and an optional witness
    for each child at a threshold node.

    [comp_rel_holds] lives in [Prop].  A [Prop] is a mathematical
    claim, and the only way to establish one is to produce a proof
    of it.  That is the right form for stating theorems about the
    protocol, but it is an awkward form for a concrete example.

    A concrete example, such as Examples/ThresholdIns.v, fixes a
    small prime group and writes down actual numbers.  It then has
    to establish that those numbers satisfy the relation.  Proving
    every leaf equation by hand would be tedious, and the whole
    proof would have to be redone whenever one of the numbers
    changes.  What one wants instead is to let the machine do the
    arithmetic: raise the bases to the exponents, multiply, and
    compare the results.

    ** What is here

    [comp_rel_holdsb] is the boolean mirror of [comp_rel_holds].  It
    walks the very same tree, but returns [true] or [false] instead
    of producing a [Prop].  Since [true] and [false] are values, a
    claim of the form [comp_rel_holdsb r w = true] can be settled by
    evaluation, with tactics such as [vm_compute].

    [comp_rel_holdsb_sound] is the bridge between the two worlds.
    It transports a computed [true] into the corresponding [Prop].
    So a concrete example proves [comp_rel_holds r w] by running the
    boolean test and applying this one lemma, which is exactly what
    Examples/ThresholdIns.v does.

    Only this direction is needed anywhere in the development, so
    only this direction is proven here. *)
Section Decide.

  (** ** Parameters

      The file is parametric in a field [F] and a group [G], given
      as carriers plus operations, in the same style as the rest of
      the compiler.  Nothing here depends on a particular choice, so
      the decision procedure applies to any group a real deployment
      might use.

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

  (** The group in which the statements live.

      - [gid] is the identity element;
      - [ginv] is inversion and [gop] the group operation;
      - [gpow] raises a group element to a field exponent;
      - [Gdec] decides equality of two group elements.  This last
        one is what makes the whole file possible: without a
        decision procedure for the group there would be no way to
        compare the two sides of a leaf equation by computation. *)
  Context
    {G : Type}
    {gid : G}
    {ginv : G -> G}
    {gop : G -> G -> G}
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}.

  (** ** Shorthands

      The constants of Composition.v and LinearRelation.v are
      defined in sections of their own, so they take this section's
      field and group operations as explicit arguments.  These local
      notations apply them once, so that the definitions below read
      as they would on paper.

      - [comp_relC] is the statement tree;
      - [comp_witnessC] is the witness type computed from a tree;
      - [comp_rel_holdsC] is the [Prop] this file decides;
      - [mat_evalC] evaluates a whole system of linear equations at
        a vector of exponents;
      - [wlist] is the type of the per-child optional witnesses of a
        threshold node, and [wholds] the statement that every
        present one of them is good. *)
  #[local] Notation comp_relC := (@comp_rel F zero G).
  #[local] Notation comp_witnessC := (@comp_witness F zero G).
  #[local] Notation comp_rel_holdsC := (@comp_rel_holds F zero G gid gop gpow).
  #[local] Notation mat_evalC := (@mat_eval F G gid gop gpow _ _).
  #[local] Notation wlist := (wlist_gen comp_witnessC).
  #[local] Notation wholds := (wholds_gen comp_rel_holdsC).

  (** ** The boolean test

      Checking every child of a threshold node.

      A threshold node stores its children in a vector, so a
      statement tree is a nested inductive type.  Rocq will not
      accept a direct recursive call inside such a vector, so the
      recursion over the children is factored out into a generic
      walker that takes the function being defined as its first
      argument [ch].  This is the same pattern as [wholds_gen] and
      [wcount] in Composition.v.

      [v] is the vector of children and [w] the matching list of
      optional witnesses.  A child that carries a witness [Some x]
      is checked with [ch]; a child with no witness contributes
      [true], because the threshold relation does not require every
      child to hold, only that enough of them do.  The counting is
      done separately, by [wcount], in [comp_rel_holdsb] below. *)
  Fixpoint holdslist_gen (ch : ∀ r : comp_relC, comp_witnessC r -> bool)
    {n : nat} (v : Vector.t comp_relC n) {struct v} : wlist v -> bool :=
    match v as v' return wlist v' -> bool with
    | [] => fun _ => true
    | r :: v' => fun w =>
        (match fst w with Some x => ch r x | None => true end) &&
        holdslist_gen ch v' (snd w)
    end.

  (** The relation, decided by computation.

      [comp_rel_holdsb r w] returns [true] exactly when the witness
      [w] can be checked, by arithmetic alone, to satisfy the
      statement tree [r].  It follows the shape of [comp_rel_holds]
      node by node.

      - At a [Leaf] the witness is a vector of exponents [xs].  The
        test evaluates the whole system, [mat_evalC mat xs], and
        compares the result with the vector [pub] of public values.
        The comparison is done on [Vector.to_list] of both sides
        rather than on the vectors themselves, because deciding
        equality of two lists from [Gdec] is a ready-made library
        function, [List.list_eq_dec], while the vector version would
        have to cope with the length index.  Nothing is lost:
        [VectorSpec.to_list_inj] turns the list equality back into a
        vector equality in the soundness proof.
      - At a [CAnd] node both children must pass, so the two results
        are combined with boolean conjunction.
      - At a [COr] node the witness itself says which branch it is
        for, and only that branch is checked.  This is the whole
        point of an OR statement: the prover knows one of the two
        sides and need not know the other.
      - At a [CThresh] node two things are checked.  First that at
        least [t] children actually carry a witness, using [wcount]
        to count them and [Nat.leb] to compare.  Second that every
        witness that is present is a good one, using
        [holdslist_gen]. *)
  Fixpoint comp_rel_holdsb (r : comp_relC) : comp_witnessC r -> bool :=
    match r return comp_witnessC r -> bool with
    | Leaf m n mat pub => fun xs =>
        if List.list_eq_dec Gdec (Vector.to_list (mat_evalC mat xs)) (Vector.to_list pub)
        then true else false
    | CAnd rl rr => fun w => comp_rel_holdsb rl (fst w) && comp_rel_holdsb rr (snd w)
    | COr rl rr => fun w =>
        match w with
        | inl wl => comp_rel_holdsb rl wl
        | inr wr => comp_rel_holdsb rr wr
        end
    | CThresh t _ _ rs _ _ => fun w =>
        Nat.leb t (wcount rs w) && holdslist_gen comp_rel_holdsb rs w
    end.

  (** ** Soundness

      Soundness of the boolean test on the children of a threshold
      node.

      The hypothesis written with [vall] says that soundness is
      already known for each child: this is the induction hypothesis
      that [comp_rel_ind'] hands over when the main proof reaches a
      threshold node.  Given that, if the boolean walker returns
      [true] on the whole list then [wholds] holds of the whole
      list.

      The argument is a plain induction over the vector of children.
      The head of the list gives [true] on the left of the boolean
      conjunction, which the child's own soundness turns into a
      [Prop]; a child with no witness gives the trivial proposition,
      which is inhabited by [I]. *)
  Lemma holdslist_sound :
    ∀ (n : nat) (v : Vector.t comp_relC n) (w : wlist v),
    vall (fun r => ∀ w : comp_witnessC r, comp_rel_holdsb r w = true -> comp_rel_holdsC r w) v ->
    holdslist_gen comp_rel_holdsb v w = true -> wholds v w.
  Proof.
    intros n v.
    induction v as [| r n v ih]; intros w hall hb; cbn in hb |- *.
    + exact I.
    + destruct hall as (hr & hall).
      eapply andb_true_iff in hb. destruct hb as (h1 & h2).
      split; [| eapply ih; [exact hall | exact h2]].
      destruct (fst w) as [x |]; [eapply hr; exact h1 | exact I].
  Qed.

  (** A computed [true] really does establish the relation.

      This is the lemma the whole file exists for.  If the boolean
      test succeeds on [r] and [w], then the proposition
      [comp_rel_holdsC r w] holds.  A concrete example can therefore
      discharge the proposition by evaluating the test and applying
      this theorem, with no hand-written proof of any leaf equation.

      Why it is true: the two definitions have the same shape, node
      for node, and at each node the boolean answer is decided by a
      procedure that is correct by construction.  At a leaf,
      [List.list_eq_dec] answers [true] only in its [left] branch,
      which carries an actual equality of the two lists of group
      elements; [VectorSpec.to_list_inj] lifts that back to the
      equality of vectors that [comp_rel_holds] asks for.  At the
      other nodes the boolean connectives mirror the logical ones:
      [andb] mirrors conjunction and [Nat.leb] mirrors [<=], each
      with a standard reflection lemma.  The proof is the structural
      induction [comp_rel_ind'], which supplies an induction
      hypothesis for every child of a threshold node. *)
  Theorem comp_rel_holdsb_sound :
    ∀ (r : comp_relC) (w : comp_witnessC r),
    comp_rel_holdsb r w = true -> comp_rel_holdsC r w.
  Proof.
    intros r.
    induction r as [m n mat pub | rl rr ihl ihr | rl rr ihl ihr | t k xs rs Hxs Ht ihrs]
      using comp_rel_ind'; intros w hb; cbn in hb |- *.
    + destruct (List.list_eq_dec Gdec (Vector.to_list (mat_evalC mat w)) (Vector.to_list pub))
        as [e | ne]; [eapply VectorSpec.to_list_inj; exact e | discriminate hb].
    + eapply andb_true_iff in hb. destruct hb as (h1 & h2).
      split; [eapply ihl; exact h1 | eapply ihr; exact h2].
    + destruct w as [wl | wr]; [eapply ihl; exact hb | eapply ihr; exact hb].
    + eapply andb_true_iff in hb. destruct hb as (h1 & h2).
      split; [eapply PeanoNat.Nat.leb_le; exact h1 | eapply holdslist_sound; [exact ihrs | exact h2]].
  Qed.

End Decide.
