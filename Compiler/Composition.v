From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef
  BinPos Permutation List PeanoNat
  FunctionalExtensionality FinFun.
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
  LinearRelation Lagrange Shamir.

Import MonadNotation
  VectorNotations.

#[local] Open Scope monad_scope.

(** * Composition: building large sigma protocols out of small ones

    ** What a sigma protocol is

    A sigma protocol is a three-message conversation between a
    prover and a verifier.  The prover wants to convince the
    verifier that it knows a secret, called the witness, without
    revealing anything about it.

    - The prover speaks first and sends an announcement, also
      called a commitment.
    - The verifier replies with a challenge, a random field
      element.
    - The prover answers with a response computed from the witness,
      its own randomness, and the challenge.

    The messages together form a transcript.  The verifier then
    runs a public test on the transcript and either accepts or
    rejects.

    Three properties are wanted, and all three are proven in this
    file.

    - Completeness: an honest prover holding a real witness always
      convinces the verifier.  See [comp_completeness].
    - Special soundness: from two accepting transcripts that share
      the same announcement but use two different challenges, one
      can compute a witness.  A prover who does not know a witness
      can therefore succeed for at most one challenge out of the
      whole challenge space.  See [comp_special_soundness].
    - Zero knowledge: the transcripts leak nothing about the
      witness, because a simulator holding no witness at all can
      produce transcripts that look exactly the same.  See
      [comp_special_honest_verifier_zkp] and the much stronger
      [comp_distribution_perm].

    ** What this file composes

    The leaf protocol lives in LinearRelation.v.  It proves
    knowledge of a vector of scalars [xs] solving a system of group
    equations [mat_evalC mat xs = pub], where the matrix [mat] of
    group elements and the vector [pub] of group elements are
    public.  Knowledge of a discrete logarithm, of a Pedersen
    commitment opening, and many other statements are instances.

    This file glues such leaves into a tree of statements,
    [comp_rel], and equips the whole tree with a prover, a
    verifier, a simulator, and proofs of the three properties
    above.  There are four kinds of node.

    - [Leaf]: a single linear-relation statement, handled by the
      protocol of LinearRelation.v.
    - [CAnd]: both children must hold.  Both are run at the same
      challenge, so there is nothing to share out.
    - [COr]: at least one child holds, and the verifier must not
      learn which one.  The two children are run at two challenges
      that add up to the verifier's challenge [c].  The transcript
      stores the left child's challenge [c₁]; the right child's is
      then forced to be the difference.  The prover first picks,
      freely, the challenge of the branch it cannot prove and fakes
      that branch; it then has no freedom left on the branch it can
      prove.  This is the classic construction of Cramer, Damgard
      and Schoenmakers.
    - [CThresh]: at least [t] of the [k] children hold.  The
      challenge is shared out in the style of Shamir secret
      sharing.  The prover picks a polynomial of degree at most
      [k - t] passing through the point [(zero, c)], and child
      number [i] is run at the value of that polynomial at a fixed
      public node, the [i]-th entry of [xs].  Such a polynomial has
      exactly [k - t] degrees of freedom besides its value at
      [zero], so the prover may choose the challenges of [k - t]
      children by hand and fake them, while the remaining [t]
      children receive challenges it cannot control and must be
      answered honestly.  The transcript records the polynomial's
      values at the first [k - t] nodes, which is all the verifier
      needs to rebuild it.

    ** How the types are built

    The witness type, the transcript type and the prover randomness
    type are not fixed in advance: each is computed from the tree by
    recursion, producing nested pairs.  See [comp_witness],
    [comp_transcript] and [comp_rand].  This keeps everything
    first-order and avoids heterogeneous vector machinery.  Every
    function and every theorem then proceeds by the same structural
    induction, [comp_rel_ind'], which supplies an induction
    hypothesis for every child of a threshold node.

    ** Two forms of zero knowledge

    [comp_special_honest_verifier_zkp] is the accept-bit form: real
    and simulated transcripts are accepted with the same
    probabilities.  It is cheap to state but weak, and in
    particular it cannot tell apart a prover using one branch of a
    [COr] from a prover using the other.

    [comp_distribution_perm] is the strong form: the real and the
    simulated transcript distributions are literally the same
    distribution, one list being a permutation of the other.  It
    needs the challenge space to be a duplicate-free enumeration of
    the whole field.  Witness indistinguishability,
    [comp_witness_indistinguishable], falls out of it at once: two
    provers holding different witnesses are each equal to the same
    witness-free simulator, hence to each other. *)

(** ** Generic list lemmas

    Small facts about [List.firstn], [List.combine] and
    [List.seq].  They are ordinary bookkeeping, pulled out here so
    that the cryptographic proofs below stay readable.  All of them
    serve the threshold node, which has to juggle node lists, value
    lists and flag lists of matching lengths. *)
Section ListLemmas.
  Context {A : Type}.

  (** Membership in a prefix implies membership in the whole list.

      [List.firstn n l] is the list of the first [n] elements of
      [l], so anything found there was already in [l].  It is used
      to carry the side condition "the point [zero] is not one of
      the interpolation nodes" from a full node list to a truncated
      one. *)
  Lemma in_firstn : ∀ (l : list A) (n : nat) (x : A),
    List.In x (List.firstn n l) -> List.In x l.
  Proof.
    induction l as [|y l ih]; intros [|n] x hin; cbn in hin;
    try contradiction.
    destruct hin as [hin | hin]; [left; exact hin | right; eapply ih; exact hin].
  Qed.

  (** A prefix of a duplicate-free list is duplicate-free.

      [List.NoDup l] says that no element of [l] occurs twice.
      Deleting elements cannot create a repetition.  The threshold
      node needs this because its interpolation nodes must be
      pairwise distinct, and the verifier works with only the first
      [k - t] of them. *)
  Lemma nodup_firstn : ∀ (l : list A) (n : nat),
    List.NoDup l -> List.NoDup (List.firstn n l).
  Proof.
    intros * hnd.
    rewrite <-(List.firstn_skipn n l) in hnd.
    eapply List.NoDup_app_remove_r; exact hnd.
  Qed.

  (** Reading inside a prefix agrees with reading the original
      list.

      If the position [i] lies below the cut point [n], then
      [List.nth i] cannot tell whether the list was truncated. *)
  Lemma nth_firstn' : ∀ (l : list A) (n i : nat) (d : A),
    (i < n)%nat -> List.nth i (List.firstn n l) d = List.nth i l d.
  Proof.
    induction l as [|y l ih]; intros [|n] [|i] d hi; cbn; try lia;
    try reflexivity.
    eapply ih; lia.
  Qed.

  (** Zipping two lists of equal length and then projecting the
      first components returns the first list.

      [List.combine] pairs two lists element by element and stops at
      the shorter one; the length hypothesis rules that truncation
      out.  This is what lets us say that the nodes of an
      interpolation point set are exactly the node list we started
      from, which is the shape the lemmas of Lagrange.v ask for. *)
  Lemma combine_map_fst : ∀ {B : Type} (l : list A) (l' : list B),
    List.length l = List.length l' ->
    List.map fst (List.combine l l') = l.
  Proof.
    induction l as [|y l ih]; intros [|z l'] hl; cbn in *; try lia;
    try reflexivity.
    rewrite ih; [reflexivity | lia].
  Qed.

  (** Reading position [i] of [List.map f (List.seq 0 k)] gives
      [f i].

      [List.seq 0 k] is the list of the first [k] natural numbers,
      so mapping [f] over it tabulates [f].  The hypothesis
      [i < k] keeps the read inside the list, where the default
      value is never reached.  The threshold soundness proof builds
      the two child challenge lists this way and then has to read
      them back position by position. *)
  Lemma nth_map_seq : ∀ {B : Type} (f : nat -> B) (k i : nat) (d : B),
    (i < k)%nat -> List.nth i (List.map f (List.seq 0 k)) d = f i.
  Proof.
    intros * hi.
    rewrite (List.nth_indep (List.map f (List.seq 0 k)) d (f 0)).
    +
      rewrite List.map_nth, List.seq_nth; [reflexivity | exact hi].
    +
      rewrite List.map_length, List.seq_length; exact hi.
  Qed.

End ListLemmas.

Section Composition.

  (** ** The ambient algebra

      Everything below is parametric in a field [F] of scalars and
      a group [G] of group elements, each given as a carrier plus
      its operations.  Nothing depends on a particular choice, so
      the results apply to whichever prime field and group a real
      deployment uses.

      The scalars: [zero] and [one] are the two constants, [add],
      [mul], [sub] and [div] the four binary operations, [opp] is
      negation and [inv] the multiplicative inverse.  [Fdec]
      decides equality of scalars, which is what allows the
      challenge comparisons in the soundness proof to be made by
      computation. *)
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}.

  (** The group is written multiplicatively.  [gid] is the neutral
      element, [ginv] the inverse, [gop] the product, and
      [gpow g x] is [g] raised to the power [x], the action of a
      scalar on a group element.  [Gdec] decides equality of group
      elements, which is what lets the verifier be a boolean
      function. *)
  Context
    {G : Type}
    {gid : G}
    {ginv : G -> G}
    {gop : G -> G -> G}
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}.

  (** Local infix notations.  The power symbol denotes the group
      power [gpow], and the four arithmetic symbols denote this
      section's field operations, not those of the standard
      library. *)
  #[local] Infix "^" := gpow.
  #[local] Infix "*" := mul.
  #[local] Infix "/" := div.
  #[local] Infix "+" := add.
  #[local] Infix "-" := sub.

  (** Notation for the three-message record of Crypto/Sigma.v,
      written as announcement, challenge, response. *)
  #[local] Notation "( a ; c ; r )" := (mk_sigma _ _ _ a c r).

  (** Shorthands for the constants imported from
      LinearRelation.v and Lagrange.v, already applied to this
      section's field and group operations.

      - [row_evalC] evaluates one linear equation.
      - [mat_evalC] evaluates a whole system of them.
      - [verifyC] is the leaf verifier.
      - [lag_interpF] is Lagrange interpolation: given a list of
        node and value pairs it returns the unique function of low
        enough degree passing through them. *)
  #[local] Notation row_evalC :=
    (@row_eval F G gid gop gpow _).
  #[local] Notation mat_evalC :=
    (@mat_eval F G gid gop gpow _ _).
  #[local] Notation verifyC :=
    (@verify_linear_relation_proof F G gid gop gpow Gdec _ _).
  #[local] Notation lag_interpF :=
    (@lag_interp F zero one add mul sub inv).

  (** ** The statement tree, and the types computed from it *)
  Section Def.

    (** The statement tree: what can be proven.

        A [comp_rel] is a statement built from four kinds of node.

        - [Leaf m n mat pub] is a single linear-relation
          statement.  [mat] is a public matrix of group elements
          with [m] rows and [n] columns, [pub] is a public vector
          of [m] group elements, and the secret is a vector of [n]
          scalars.
        - [CAnd rl rr] holds when both children hold.
        - [COr rl rr] holds when at least one child holds.
        - [CThresh t k xs rs Hxs Ht] holds when at least [t] of the
          [k] children listed in [rs] hold.  [xs] gives the [k]
          public interpolation nodes, one per child.  [Hxs] says
          that [zero] together with those nodes are pairwise
          distinct; this is what makes the challenge sharing sound,
          since the nodes must differ from one another and none of
          them may coincide with [zero], which is the point where
          the root challenge itself lives.  [Ht] says the threshold
          does not exceed the number of children.

        The children of a threshold node are a [Vector.t] rather
        than a [list] on purpose.  Their number is then the same
        [k] that indexes the node vector [xs], so the two are tied
        together by typing alone.  The alternative, a list of
        children plus a side condition equating its length with the
        length of [xs], would place a proposition mentioning
        [comp_rel] inside the declaration of [comp_rel] itself,
        which the positivity checker rejects.

        Because it recurses through [Vector.t], [comp_rel] is a
        nested inductive type.  That is the reason for the custom
        induction principle and the generic walkers further
        down. *)
    Inductive comp_rel : Type :=
    | Leaf (m n : nat)
        (mat : Vector.t (Vector.t G n) m)
        (pub : Vector.t G m) : comp_rel
    | CAnd (rl rr : comp_rel) : comp_rel
    | COr (rl rr : comp_rel) : comp_rel
    | CThresh (t k : nat) (xs : Vector.t F k) (rs : Vector.t comp_rel k)
        (Hxs : List.NoDup (List.cons zero (Vector.to_list xs)))
        (Ht : (t <= k)%nat) : comp_rel.

    (** [vall P v] says that the predicate [P] holds of every child
        in the vector [v].

        It is written by hand rather than reused from the standard
        library so that it unfolds by plain computation, which
        keeps the proofs about threshold nodes short. *)
    Fixpoint vall (P : comp_rel -> Prop) {n : nat}
      (v : Vector.t comp_rel n) : Prop :=
      match v with
      | [] => True
      | r :: v' => P r ∧ vall P v'
      end.

    (** [vall] is monotone: weakening the predicate weakens the
        statement.

        If [P] holds of every child and [P] implies [Q], then [Q]
        holds of every child.  This is used to reshape the
        induction hypothesis handed out by [comp_rel_ind'] into
        whatever form the proof at hand needs; the clearest case is
        the threshold branch of [comp_distribution_perm]. *)
    Lemma vall_mono :
      ∀ (P Q : comp_rel -> Prop) (n : nat) (v : Vector.t comp_rel n),
      vall P v -> (∀ r, P r -> Q r) -> vall Q v.
    Proof.
      induction v as [| r n v ih]; intros hp hpq; cbn in hp |- *.
      + exact I.
      + destruct hp as (hr & hv).
        split; [eapply hpq; exact hr | eapply ih; assumption].
    Qed.

    (** ** Structural induction over the statement tree

        The induction principle Rocq generates for [comp_rel] is
        useless at a threshold node: it offers no induction
        hypothesis for the children, because they sit under a
        [Vector.t].  [comp_rel_ind'] repairs this.  It takes the
        usual four cases, except that the threshold case also
        receives [vall P rs], the statement that [P] already holds
        of every child.

        The fixpoint builds that extra argument with an inner
        recursion over the vector, which calls [comp_rel_ind'] on
        each child.  This is the standard way of giving a nested
        inductive type a usable induction principle.  Every
        function and every theorem below is proven with it. *)
    Section Induction.
      Variable P : comp_rel -> Prop.
      Hypothesis HLeaf : ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m)
        (pub : Vector.t G m), P (Leaf m n mat pub).
      Hypothesis HAnd : ∀ (rl rr : comp_rel), P rl -> P rr -> P (CAnd rl rr).
      Hypothesis HOr : ∀ (rl rr : comp_rel), P rl -> P rr -> P (COr rl rr).
      Hypothesis HThresh : ∀ (t k : nat) (xs : Vector.t F k) 
        (rs : Vector.t comp_rel k) 
        (Hxs : List.NoDup (List.cons zero (Vector.to_list xs)))
        (Ht : (t <= k)%nat), vall P rs -> P (CThresh t k xs rs Hxs Ht).

      (** The induction principle itself.  The inner fixpoint
          walks the children of a threshold node and assembles
          their individual proofs into a [vall]. *)
      Fixpoint comp_rel_ind' (r : comp_rel) : P r :=
        match r with
        | Leaf m n mat pub => HLeaf m n mat pub
        | CAnd rl rr => HAnd rl rr (comp_rel_ind' rl) (comp_rel_ind' rr)
        | COr rl rr => HOr rl rr (comp_rel_ind' rl) (comp_rel_ind' rr)
        | CThresh t k xs rs Hxs Ht =>
            HThresh t k xs rs Hxs Ht
              ((fix go (n : nat) (v : Vector.t comp_rel n) : vall P v :=
                  match v as v' return vall P v' with
                  | [] => I
                  | r' :: v' => conj (comp_rel_ind' r') (go _ v')
                  end) k rs)
        end.
    End Induction.

    (** ** Generic walkers over the children of a threshold node

        [comp_rel] is a nested inductive type, so a function defined
        by recursion on the tree cannot simply recurse over the
        vector of children with something like [Vector.map]: the
        guard checker cannot see, through an opaque higher-order
        argument, that the children are structurally smaller.

        The way around this is to define, for each such traversal, a
        separate fixpoint that recurses on the vector only and takes
        the function being defined as a parameter.  Those are the
        walkers whose names end in [_gen].  A definition such as
        [comp_witness] may then call [wlist_gen comp_witness rs] on
        its own children, which the guard checker does accept.  The
        local notations further down ([wlist], [tlist], [provelist]
        and the rest) are these walkers already applied to the
        function they were meant for. *)

    (** The type of the witness list of a threshold node.

        [wlist_gen cw v] is a nested tuple with one slot per child,
        each slot holding [option (cw r)]: the prover may or may
        not have a witness for that child.  The parameter [cw] is
        instantiated with [comp_witness]. *)
    Fixpoint wlist_gen (cw : comp_rel -> Type) {n : nat}
      (v : Vector.t comp_rel n) {struct v} : Type :=
      match v with
      | [] => unit
      | r :: v' => (option (cw r) * wlist_gen cw v')%type
      end.

    (** The type of the transcript list of a threshold node: a
        nested tuple with one transcript per child.  Unlike
        witnesses there is no [option] here, because every child,
        faked or honest, contributes a transcript.  The parameter
        [ct] is instantiated with [comp_transcript]. *)
    Fixpoint tlist_gen (ct : comp_rel -> Type) {n : nat}
      (v : Vector.t comp_rel n) {struct v} : Type :=
      match v with
      | [] => unit
      | r :: v' => (ct r * tlist_gen ct v')%type
      end.

    (** The type of a witness for a statement, computed from the
        tree.

        A witness is the secret whose knowledge the prover claims.

        - At a [Leaf] it is the vector of [n] secret scalars.
        - At a [CAnd] it is a pair, since both children need one.
        - At a [COr] it is a sum type: a witness for the left child
          or a witness for the right child.  Nothing outside the
          prover says which.
        - At a [CThresh] it is an optional witness per child.  The
          type alone does not require [t] of them to be present;
          that requirement belongs to the relation
          [comp_rel_holds]. *)
    Fixpoint comp_witness (r : comp_rel) : Type :=
      match r with
      | Leaf m n _ _ => Vector.t F n
      | CAnd rl rr => (comp_witness rl * comp_witness rr)%type
      | COr rl rr => (comp_witness rl + comp_witness rr)%type
      | CThresh _ _ _ rs _ _ => wlist_gen comp_witness rs
      end.

    (** How many children of a threshold node actually come with a
        witness.

        It walks the nested tuple and counts one for every [Some].
        The threshold relation demands [t <= wcount rs w], and the
        prover uses the surplus, [wcount rs w - t], to decide how
        many witness-holding children it may nevertheless fake. *)
    Fixpoint wcount {n : nat} (v : Vector.t comp_rel n) {struct v} :
      wlist_gen comp_witness v -> nat :=
      match v as v' return wlist_gen comp_witness v' -> nat with
      | [] => fun _ => 0
      | r :: v' => fun w =>
          ((match fst w with Some _ => 1 | None => 0 end) +
            wcount v' (snd w))%nat
      end.

    (** Every witness that is present is a correct one.

        [wholds_gen ch v w] says that whenever a child holds
        [Some x], the relation [ch] holds of [x]; children holding
        [None] impose no condition.  The parameter [ch] is
        instantiated with [comp_rel_holds]. *)
    Fixpoint wholds_gen (ch : ∀ r : comp_rel, comp_witness r -> Prop)
      {n : nat} (v : Vector.t comp_rel n) {struct v} : wlist_gen comp_witness v -> Prop :=
      match v as v' return wlist_gen comp_witness v' -> Prop with
      | [] => fun _ => True
      | r :: v' => fun w =>
          (match fst w with
           | Some x => ch r x
           | None => True
           end) ∧ wholds_gen ch v' (snd w)
      end.

    (** The relation the composed protocol proves: when is [w] a
        genuine witness for the statement [r].

        - At a [Leaf] the witness must solve the system of group
          equations, [mat_evalC mat xs = pub].
        - At a [CAnd] both halves of the pair must be witnesses.
        - At a [COr] the branch that is present must be a witness.
        - At a [CThresh] at least [t] children must carry a
          witness, and every witness carried must be correct.

        This is the statement [comp_completeness] assumes and the
        statement [comp_special_soundness] produces. *)
    Fixpoint comp_rel_holds (r : comp_rel) :
      comp_witness r -> Prop :=
      match r return comp_witness r -> Prop with
      | Leaf m n mat pub => fun xs => mat_evalC mat xs = pub
      | CAnd rl rr => fun w =>
          comp_rel_holds rl (fst w) ∧ comp_rel_holds rr (snd w)
      | COr rl rr => fun w =>
          match w with
          | inl wl => comp_rel_holds rl wl
          | inr wr => comp_rel_holds rr wr
          end
      | CThresh t _ _ rs _ _ => fun w =>
          (t <= wcount rs w)%nat ∧ wholds_gen comp_rel_holds rs w
      end.

    (** The shape of a transcript, computed from the tree.

        The challenge is never stored inside a transcript; it is
        handed to the verifier separately.  What is stored is the
        extra data the verifier needs in order to derive the
        children's challenges from the root challenge.

        - At a [Leaf] a transcript is the announcement, a vector of
          [m] group elements, together with the response, a vector
          of [n] scalars.
        - At a [CAnd] it is just the pair of child transcripts,
          since both children run at the same challenge.
        - At a [COr] it is the two child transcripts plus one field
          element, the left child's challenge.  The right child's
          challenge is the difference between the root challenge
          and it, so it need not be stored.
        - At a [CThresh] it is the child transcripts plus a list of
          [k - t] field elements, the values of the sharing
          polynomial at the first [k - t] nodes.  Together with the
          value [c] at [zero] that is [k - t + 1] points, exactly
          enough to determine a polynomial of degree at most
          [k - t], so the verifier can rebuild every child
          challenge from them. *)
    Fixpoint comp_transcript (r : comp_rel) : Type :=
      match r with
      | Leaf m n _ _ => (Vector.t G m * Vector.t F n)%type
      | CAnd rl rr => (comp_transcript rl * comp_transcript rr)%type
      | COr rl rr =>
          (comp_transcript rl * comp_transcript rr * F)%type
      | CThresh _ _ _ rs _ _ => (tlist_gen comp_transcript rs * list F)%type
      end.

    (** The randomness the prover consumes, computed from the tree.

        - At a [Leaf] it is the commitment randomness, one scalar
          per secret scalar.
        - At a [CAnd] it is the pair of the children's randomness.
        - At a [COr] there is one extra scalar, the challenge used
          for the branch being simulated.  Committing to it in
          advance is what allows that branch to be faked.
        - At a [CThresh] there are [k - t] extra scalars, the
          challenges the prover is free to choose for the children
          it fakes.

        The simulator consumes randomness of exactly the same type.
        That is what makes the real and the simulated distributions
        comparable at all. *)
    Fixpoint comp_rand (r : comp_rel) : Type :=
      match r with
      | Leaf m n _ _ => Vector.t F n
      | CAnd rl rr => (comp_rand rl * comp_rand rr)%type
      | COr rl rr => (comp_rand rl * comp_rand rr * F)%type
      | CThresh t k _ rs _ _ =>
          (tlist_gen comp_rand rs * Vector.t F (k - t))%type
      end.

    (** Total number of scalars drawn across the children of a
        threshold node, used to size that node's randomness. *)
    Fixpoint slist_gen (cs : comp_rel -> nat) {n : nat}
      (v : Vector.t comp_rel n) {struct v} : nat :=
      match v with
      | [] => 0
      | r :: v' => (cs r + slist_gen cs v')%nat
      end.

    (** How many field elements the prover, or the simulator, draws
        for the statement [r].

        It is the size of [comp_rand r] counted as a flat list of
        scalars: [n] at a leaf, the sum of the children at a
        [CAnd], the sum plus one at a [COr] for the stored branch
        challenge, and the sum plus [k - t] at a [CThresh] for the
        free child challenges.  It appears in every probability
        computation below, because each randomness is drawn with
        probability one over the size of the challenge space raised
        to the power [comp_size r]. *)
    Fixpoint comp_size (r : comp_rel) : nat :=
      match r with
      | Leaf m n _ _ => n
      | CAnd rl rr => (comp_size rl + comp_size rr)%nat
      | COr rl rr => S (comp_size rl + comp_size rr)
      | CThresh t k _ rs _ _ => (slist_gen comp_size rs + (k - t))%nat
      end.

    (** ** Sharing the challenge at a threshold node

        The next four definitions implement the Shamir-style
        sharing described at the top of the file.  The prover must
        turn the single root challenge [c] into [k] child
        challenges in such a way that it controls exactly [k - t]
        of them, no more and no fewer. *)

    (** The sharing polynomial, seen as a function of the node.

        [expand_chal c nodes vals] is the interpolant through the
        point [(zero, c)] together with the pairs formed from
        [nodes] and [vals].  Its degree is at most the length of
        [nodes].  It returns [c] at [zero], which is
        [expand_chal_zero], and it returns [vals] at [nodes],
        which is [expand_chal_nodes].

        Both the prover and the verifier call it, but with
        different node lists.  The prover interpolates through the
        nodes of the children it fakes; the verifier interpolates
        through the first [k - t] nodes, which is where the
        transcript records its values.  The two functions
        nevertheless coincide, because they have the same degree
        bound and the same value at [zero]; that is
        [expand_agree]. *)
    Definition expand_chal (c : F) (nodes vals : list F) : F -> F :=
      lag_interpF (List.cons (zero, c) (List.combine nodes vals)).

    (** The challenge handed to child number [i]: the sharing
        polynomial [f] evaluated at the [i]-th public node of [xs].

        Reading past the end of [xs] would return the default
        [zero], but that never happens, since the index always
        ranges below the number of children. *)
    Definition chal_of (xs : list F) (f : F -> F) (i : nat) : F :=
      f (List.nth i xs zero).

    (** Which children the prover is going to fake.

        [sim_flags v w seeds] returns one boolean per child:
        [true] means simulate, [false] means prove honestly.  Every
        child without a witness has to be simulated.  On top of
        those, the first [seeds] children that do hold a witness
        are simulated as well.

        The prover calls it with [seeds] equal to
        [wcount rs w - t], the number of witnesses it holds in
        excess of the threshold.  The number of flagged children
        then comes out at exactly [k - t], which is
        [sim_flags_count], and that is precisely how many child
        challenges a polynomial of degree at most [k - t] lets it
        choose freely.

        Padding up to [k - t] is not an optimisation but a security
        requirement.  If the prover faked only the children it
        cannot prove, the number of faked children would reveal how
        many witnesses it holds. *)
    Fixpoint sim_flags {n : nat} (v : Vector.t comp_rel n) {struct v} :
      wlist_gen comp_witness v -> nat -> list bool :=
      match v as v' return wlist_gen comp_witness v' -> nat -> list bool with
      | [] => fun _ _ => List.nil
      | r :: v' => fun w seeds =>
          match fst w with
          | None => List.cons true (sim_flags v' (snd w) seeds)
          | Some _ =>
              match seeds with
              | 0 => List.cons false (sim_flags v' (snd w) 0)
              | S k => List.cons true (sim_flags v' (snd w) k)
              end
          end
      end.

    (** How many entries of a flag list are [true], that is, how
        many children are being simulated. *)
    Fixpoint count_true (fl : list bool) : nat :=
      match fl with
      | List.nil => 0
      | List.cons b fl' => ((if b then 1 else 0) + count_true fl')%nat
      end.

    (** The public nodes of the flagged children.

        [select_nodes xs fl] walks the node list and the flag list
        together and keeps a node whenever its flag is [true].
        These are the nodes at which the prover pins its sharing
        polynomial down to challenges of its own choosing. *)
    Fixpoint select_nodes (xs : list F) (fl : list bool) : list F :=
      match xs, fl with
      | List.cons x xs', List.cons b fl' =>
          if b then List.cons x (select_nodes xs' fl')
          else select_nodes xs' fl'
      | _, _ => List.nil
      end.

    (** Simulate every child of a threshold node.

        [simlist_gen cs v s chal i] runs the simulator [cs] on each
        child, giving child number [i] the challenge [chal i] and
        the randomness taken from [s], and collects the resulting
        transcripts into the nested tuple.  The index counts up as
        the walk proceeds, so every child receives its own
        challenge. *)
    Fixpoint simlist_gen
      (cs : ∀ r : comp_rel, comp_rand r -> F -> comp_transcript r)
      {n : nat} (v : Vector.t comp_rel n) {struct v} :
      tlist_gen comp_rand v -> (nat -> F) -> nat -> tlist_gen comp_transcript v :=
      match v as v' return tlist_gen comp_rand v' -> (nat -> F) -> nat -> tlist_gen comp_transcript v' with
      | [] => fun _ _ _ => tt
      | r :: v' => fun s chal i =>
          (cs r (fst s) (chal i), simlist_gen cs v' (snd s) chal (S i))
      end.

    (** The simulator: an accepting transcript for the challenge
        [c], built with no witness at all.

        The existence of such a procedure is what makes the
        protocol zero knowledge.  A transcript on its own proves
        nothing, since anybody could have manufactured it; what
        convinces the verifier is only that the challenge was
        chosen after the announcement was fixed.

        - At a [Leaf] the response is chosen first, as the drawn
          randomness, and the announcement is then computed
          backwards from the verification equation.
        - At a [CAnd] both children are simulated at the same
          challenge.
        - At a [COr] the branch challenge taken from the randomness
          becomes the left child's challenge and the difference
          becomes the right child's, mirroring the verifier
          exactly.
        - At a [CThresh] the free scalars of the randomness are
          read as the polynomial's values at the first [k - t]
          nodes, every child is simulated at its resulting
          challenge, and those same scalars are recorded in the
          transcript. *)
    Fixpoint comp_simulate (r : comp_rel) :
      comp_rand r -> F -> comp_transcript r :=
      match r return comp_rand r -> F -> comp_transcript r with
      | Leaf m n mat pub => fun zs c =>
          (zip_with (fun row p => gop (row_evalC row zs) (p ^ (opp c)))
            mat pub, zs)
      | CAnd rl rr => fun s c =>
          (comp_simulate rl (fst s) c, comp_simulate rr (snd s) c)
      | COr rl rr => fun s c =>
          (comp_simulate rl (fst (fst s)) (snd s),
           comp_simulate rr (snd (fst s)) (c - snd s),
           snd s)
      | CThresh t k xs rs _ _ => fun s c =>
          (simlist_gen comp_simulate rs (fst s)
             (chal_of (Vector.to_list xs) (expand_chal c (List.firstn (k - t) (Vector.to_list xs))
               (Vector.to_list (snd s)))) 0,
           Vector.to_list (snd s))
      end.

    (** Walk the children of a threshold node, proving some and
        faking the rest.

        [provelist_gen cp cs v w s fl chal i] gives child number
        [i] the challenge [chal i].  A child is proven with [cp]
        when it holds a witness and its flag in [fl] is [false]; in
        every other case it is simulated with [cs].  The flag list
        comes from [sim_flags], so exactly [k - t] children take
        the simulated route. *)
    Fixpoint provelist_gen
      (cp : ∀ r : comp_rel, comp_witness r -> comp_rand r -> F -> comp_transcript r)
      (cs : ∀ r : comp_rel, comp_rand r -> F -> comp_transcript r)
      {n : nat} (v : Vector.t comp_rel n) {struct v} :
      wlist_gen comp_witness v -> tlist_gen comp_rand v -> list bool -> (nat -> F) -> nat -> tlist_gen comp_transcript v :=
      match v as v' return
        wlist_gen comp_witness v' -> tlist_gen comp_rand v' -> list bool -> (nat -> F) -> nat -> tlist_gen comp_transcript v'
      with
      | [] => fun _ _ _ _ _ => tt
      | r :: v' => fun w s fl chal i =>
          ((match fst w, fl with
            | Some x, List.cons false _ => cp r x (fst s) (chal i)
            | _, _ => cs r (fst s) (chal i)
            end),
           provelist_gen cp cs v' (snd w) (snd s) (List.tl fl) chal (S i))
      end.

    (** The honest prover.

        Given a witness [w], randomness [s] and the verifier's
        challenge [c], it produces a transcript that [comp_verify]
        accepts; that is [comp_completeness].

        - At a [Leaf] the announcement is the matrix applied to the
          randomness, and the response is the randomness plus [c]
          times the secret, coordinate by coordinate.
        - At a [CAnd] both children are proven at the same
          challenge.
        - At a [COr] the branch the prover cannot do is simulated
          at the challenge committed to in the randomness, and the
          branch it can do is proven at whatever remains of [c].
          The field element recorded is always the left child's
          challenge: it is [c] minus the committed value when the
          left branch is the real one, and the committed value
          itself when the right branch is.  From outside, the two
          cases look identical.
        - At a [CThresh] the prover uses [sim_flags] to decide
          which [k - t] children to fake, treats the free scalars
          of its randomness as those children's challenges by
          interpolating through their nodes, and answers the
          remaining [t] children honestly at the challenges that
          the interpolation forces upon them.  The transcript
          records the polynomial's values at the first [k - t]
          nodes, which is the form the verifier expects and which
          hides which children were faked. *)
    Fixpoint comp_prove (r : comp_rel) :
      comp_witness r -> comp_rand r -> F -> comp_transcript r :=
      match r return comp_witness r -> comp_rand r -> F -> comp_transcript r with
      | Leaf m n mat pub => fun xs us c =>
          (mat_evalC mat us,
           zip_with (fun u x => u + c * x) us xs)
      | CAnd rl rr => fun w s c =>
          (comp_prove rl (fst w) (fst s) c,
           comp_prove rr (snd w) (snd s) c)
      | COr rl rr => fun w s c =>
          match w with
          | inl wl =>
              (comp_prove rl wl (fst (fst s)) (c - snd s),
               comp_simulate rr (snd (fst s)) (snd s),
               c - snd s)
          | inr wr =>
              (comp_simulate rl (fst (fst s)) (snd s),
               comp_prove rr wr (snd (fst s)) (c - snd s),
               snd s)
          end
      | CThresh t k xs rs _ _ => fun w s c =>
          (provelist_gen comp_prove comp_simulate rs w (fst s)
             (sim_flags rs w (wcount rs w - t))
             (chal_of (Vector.to_list xs) (expand_chal c
               (select_nodes (Vector.to_list xs) (sim_flags rs w (wcount rs w - t)))
               (Vector.to_list (snd s)))) 0,
           List.map
             (expand_chal c
               (select_nodes (Vector.to_list xs) (sim_flags rs w (wcount rs w - t)))
               (Vector.to_list (snd s)))
             (List.firstn (k - t) (Vector.to_list xs)))
      end.

    (** Verify every child of a threshold node, each at its own
        challenge [chal i], and take the conjunction of the
        answers. *)
    Fixpoint verlist_gen
      (cv : ∀ r : comp_rel, F -> comp_transcript r -> bool)
      {n : nat} (v : Vector.t comp_rel n) {struct v} :
      (nat -> F) -> tlist_gen comp_transcript v -> nat -> bool :=
      match v as v' return (nat -> F) -> tlist_gen comp_transcript v' -> nat -> bool with
      | [] => fun _ _ _ => true
      | r :: v' => fun chal tr i =>
          cv r (chal i) (fst tr) && verlist_gen cv v' chal (snd tr) (S i)
      end.

    (** The verifier: a boolean test on a transcript, given the
        challenge [c].

        It mirrors the prover node by node, and it uses no secret
        information, so anybody can run it.

        - A [Leaf] runs the linear-relation check of
          LinearRelation.v.
        - A [CAnd] passes the same challenge to both children.
        - A [COr] reads the recorded field element as the left
          child's challenge and uses the difference for the right
          child, so the two child challenges always add up to [c],
          whichever branch was the real one.
        - A [CThresh] first checks that exactly [k - t] values were
          recorded, then rebuilds the sharing polynomial from those
          values together with the point [(zero, c)], and checks
          every child at its interpolated challenge.  The length
          check is what caps the degree of the polynomial, and
          hence what forces the prover to answer [t] children
          honestly. *)
    Fixpoint comp_verify (r : comp_rel) :
      F -> comp_transcript r -> bool :=
      match r return F -> comp_transcript r -> bool with
      | Leaf m n mat pub => fun c t =>
          verifyC mat pub (fst t; [c]; snd t)
      | CAnd rl rr => fun c t =>
          comp_verify rl c (fst t) && comp_verify rr c (snd t)
      | COr rl rr => fun c t =>
          comp_verify rl (snd t) (fst (fst t)) &&
          comp_verify rr (c - snd t) (snd (fst t))
      | CThresh t k xs rs _ _ => fun c tr =>
          Nat.eqb (List.length (snd tr)) (k - t) &&
          verlist_gen comp_verify rs
            (chal_of (Vector.to_list xs) (expand_chal c (List.firstn (k - t) (Vector.to_list xs)) (snd tr)))
            (fst tr) 0
      end.

    (** Two transcript lists for the same children carry the same
        announcements, child by child. *)
    Fixpoint salist_gen
      (csa : ∀ r : comp_rel, comp_transcript r -> comp_transcript r -> Prop)
      {n : nat} (v : Vector.t comp_rel n) {struct v} :
      tlist_gen comp_transcript v -> tlist_gen comp_transcript v -> Prop :=
      match v as v' return tlist_gen comp_transcript v' -> tlist_gen comp_transcript v' -> Prop with
      | [] => fun _ _ => True
      | r :: v' => fun t t' =>
          csa r (fst t) (fst t') ∧ salist_gen csa v' (snd t) (snd t')
      end.

    (** Two transcripts for the same statement carry the same
        announcements everywhere.

        Only leaves have announcements, so the recursion bottoms
        out in an equality of leaf announcement vectors;
        challenges, responses and recorded challenge data are free
        to differ.

        This is the hypothesis of special soundness.  Rewinding a
        prover means running it twice from the same first message
        and answering with two different challenges, which produces
        exactly a pair of transcripts related by this
        predicate. *)
    Fixpoint comp_same_announcement (r : comp_rel) :
      comp_transcript r -> comp_transcript r -> Prop :=
      match r return comp_transcript r -> comp_transcript r -> Prop with
      | Leaf m n _ _ => fun t t' => fst t = fst t'
      | CAnd rl rr => fun t t' =>
          comp_same_announcement rl (fst t) (fst t') ∧
          comp_same_announcement rr (snd t) (snd t')
      | COr rl rr => fun t t' =>
          comp_same_announcement rl (fst (fst t)) (fst (fst t')) ∧
          comp_same_announcement rr (snd (fst t)) (snd (fst t'))
      | CThresh _ _ _ rs _ _ => fun t t' =>
          salist_gen comp_same_announcement rs (fst t) (fst t')
      end.

    (** Draw randomness independently for every child of a
        threshold node and collect it into the nested tuple. *)
    Fixpoint rand_list_gen (cd : ∀ r : comp_rel, dist (comp_rand r))
      {n : nat} (v : Vector.t comp_rel n) {struct v} : dist (tlist_gen comp_rand v) :=
      match v as v' return dist (tlist_gen comp_rand v') with
      | [] => Ret tt
      | r :: v' =>
          x <- cd r ;;
          xs <- rand_list_gen cd v' ;;
          Ret (x, xs)
      end.

    (** The uniform distribution over the prover's randomness.

        [lf] is the challenge space, given as a list of field
        elements, and [Hlfn] says it is not empty, so that drawing
        from it makes sense.  Every scalar the prover needs is
        drawn uniformly and independently from [lf]: the leaf
        commitment randomness, the branch challenge at a [COr], and
        the free child challenges at a [CThresh].  A distribution
        here is a concrete list of value and probability pairs,
        built with the monad of Probability/Distr.v.

        Since all draws are uniform and independent, every
        randomness comes out with the same probability; that is
        [comp_rand_distribution_prob]. *)
    Fixpoint comp_rand_distribution
      (lf : list F) (Hlfn : lf <> List.nil) (r : comp_rel) {struct r} :
      dist (comp_rand r) :=
      match r return dist (comp_rand r) with
      | Leaf m n _ _ =>
          repeat_dist_ntimes_vector
            (uniform_with_replacement lf Hlfn) n
      | CAnd rl rr =>
          sl <- comp_rand_distribution lf Hlfn rl ;;
          sr <- comp_rand_distribution lf Hlfn rr ;;
          Ret (sl, sr)
      | COr rl rr =>
          c₁ <- uniform_with_replacement lf Hlfn ;;
          sl <- comp_rand_distribution lf Hlfn rl ;;
          sr <- comp_rand_distribution lf Hlfn rr ;;
          Ret (sl, sr, c₁)
      | CThresh t k _ rs _ _ =>
          d <- repeat_dist_ntimes_vector
            (uniform_with_replacement lf Hlfn) (k - t) ;;
          rl <- rand_list_gen (comp_rand_distribution lf Hlfn) rs ;;
          Ret (rl, d)
      end.

    (** The distribution of transcripts the honest prover
        produces: draw the randomness, then run [comp_prove] on the
        witness [w] and the challenge [c]. *)
    Definition comp_real_distribution
      (lf : list F) (Hlfn : lf <> List.nil) (r : comp_rel)
      (w : comp_witness r) (c : F) : dist (comp_transcript r) :=
      s <- comp_rand_distribution lf Hlfn r ;;
      Ret (comp_prove r w s c).

    (** The distribution of transcripts the simulator produces:
        draw randomness of the very same type, then run
        [comp_simulate] on the challenge [c] alone.  Zero knowledge
        is the statement that this equals the distribution
        above. *)
    Definition comp_simulator_distribution
      (lf : list F) (Hlfn : lf <> List.nil) (r : comp_rel)
      (c : F) : dist (comp_transcript r) :=
      s <- comp_rand_distribution lf Hlfn r ;;
      Ret (comp_simulate r s c).

  End Def.

  (** ** The walkers, instantiated

      Each of these notations applies one generic walker of the
      previous section to the function it was designed for, so that
      the proofs below can write [wlist], [provelist] and so on
      without repeating the parameter every time. *)
  #[local] Notation wlist := (wlist_gen comp_witness).
  #[local] Notation wholds := (wholds_gen comp_rel_holds).
  #[local] Notation tlist := (tlist_gen comp_transcript).
  #[local] Notation rlist := (tlist_gen comp_rand).
  #[local] Notation slist := (slist_gen comp_size).
  #[local] Notation simlist := (simlist_gen comp_simulate).
  #[local] Notation provelist := (provelist_gen comp_prove comp_simulate).
  #[local] Notation verlist := (verlist_gen comp_verify).
  #[local] Notation salist := (salist_gen comp_same_announcement).
  #[local] Notation rand_list lf Hlfn :=
    (rand_list_gen (comp_rand_distribution lf Hlfn)).

  (** ** The proofs *)
  Section Proofs.

    (** The proofs need more than bare operations.  [Hvec] states
        that the field [F] acts on the group [G] as a vector space,
        which is what makes the leaf verification equation
        algebraically true, and it carries a field structure on [F]
        along with it.  The [field] tactic is registered so that
        routine scalar identities are discharged automatically. *)
    Context
      {Hvec : @vector_space F (@eq F) zero one add mul sub
        div opp inv G (@eq G) gid ginv gop gpow}.
    Add Field field : (@field_theory_for_stdlib_tactic F
      eq zero one opp add mul sub inv div vector_space_field).

    (** Shorthands for the imported results.  [lag_evalF] says an
        interpolant takes the prescribed value at a prescribed
        node; [lag_uniqF] is the uniqueness theorem for
        interpolants of low enough degree; [thresh_extractF] is the
        counting theorem [threshold_extraction] of Shamir.v; and
        [agreebF] is its boolean test for "the two challenge lists
        agree at position [i]". *)
    #[local] Notation lag_evalF :=
      (@lag_interp_eval F zero one add mul sub div opp inv
        vector_space_field).
    #[local] Notation lag_uniqF :=
      (@lag_interp_unique F zero one add mul sub div opp inv Fdec
        vector_space_field).
    #[local] Notation thresh_extractF :=
      (@threshold_extraction F zero one add mul sub div opp inv Fdec
        vector_space_field).
    #[local] Notation agreebF := (@agreeb F zero Fdec).

    (** ** Bookkeeping for the threshold node

        A block of small lemmas about [sim_flags], [select_nodes]
        and the interpolation helpers.  Their only job is to
        establish the one fact the interesting proofs need: the
        prover flags exactly [k - t] children, hence selects
        exactly [k - t] pairwise distinct nodes, hence builds an
        interpolant of exactly the degree the verifier expects. *)

    (** A threshold node cannot hold more witnesses than it has
        children.  Needed to know that [wcount v w - t] is a
        sensible number of extra children to fake, and to simplify
        the minimum in [sim_flags_count]. *)
    Lemma wcount_le :
      ∀ (n : nat) (v : Vector.t comp_rel n) (w : wlist v),
      (wcount v w <= n)%nat.
    Proof.
      induction v as [|r n v ih]; intros w; cbn.
      + lia.
      + destruct (fst w); specialize (ih (snd w)); lia.
    Qed.

    (** [sim_flags] returns exactly one flag per child.

        Immediate by construction, but needed explicitly whenever a
        flag list is matched up against the node list, which also
        has length [k]. *)
    Lemma sim_flags_length :
      ∀ (n : nat) (v : Vector.t comp_rel n) (w : wlist v) (s : nat),
      List.length (sim_flags v w s) = n.
    Proof.
      induction v as [|r n v ih]; intros w s; cbn.
      + reflexivity.
      + destruct (fst w); [destruct s |]; cbn; rewrite ih; reflexivity.
    Qed.

    (** Exactly how many children get flagged for simulation.

        Of the [n] children, the [n - wcount v w] that hold no
        witness are always flagged, and [seeds] more are flagged
        among those that do hold one, capped by how many such
        children exist.  When the prover uses [seeds] equal to
        [wcount v w - t], and the relation guarantees
        [t <= wcount v w], the minimum simplifies and the total
        comes out at [n - t].

        This is the key counting fact of the whole threshold
        construction.  It is what makes the prover's interpolant
        have degree at most [k - t], which is exactly the degree
        cap the verifier enforces by checking the length of the
        recorded value list. *)
    Lemma sim_flags_count :
      ∀ (n : nat) (v : Vector.t comp_rel n) (w : wlist v) (s : nat),
      count_true (sim_flags v w s) =
      (n - wcount v w + Nat.min s (wcount v w))%nat.
    Proof.
      induction v as [|r n v ih]; intros w s; cbn.
      + lia.
      + pose proof (wcount_le n v (snd w)) as hle.
        destruct (fst w); [destruct s |]; cbn; rewrite ih;
        destruct (wcount v (snd w)) eqn:hw; lia.
    Qed.

    (** Selecting nodes by a flag list keeps as many nodes as there
        are [true] flags, provided the two lists have the same
        length.  Combined with [sim_flags_count], this pins down
        the number of interpolation points the prover uses. *)
    Lemma select_nodes_length :
      ∀ (xs : list F) (fl : list bool),
      List.length fl = List.length xs ->
      List.length (select_nodes xs fl) = count_true fl.
    Proof.
      induction xs as [|x xs ih]; intros [|b fl] hl; cbn in hl |- *;
      try lia; try reflexivity.
      destruct b; cbn; rewrite ih; lia.
    Qed.

    (** Selected nodes come from the original node list.  Used to
        carry distinctness, and the fact that [zero] is not among
        them, from the full node list down to the selection. *)
    Lemma select_nodes_incl :
      ∀ (xs : list F) (fl : list bool) (x : F),
      List.In x (select_nodes xs fl) -> List.In x xs.
    Proof.
      induction xs as [|y xs ih]; intros [|b fl] x hin; cbn in hin;
      try contradiction.
      destruct b.
      + destruct hin as [hin | hin]; [left; exact hin | right; eapply ih; exact hin].
      + right; eapply ih; exact hin.
    Qed.

    (** Selecting from a duplicate-free node list leaves a
        duplicate-free node list.  Interpolation requires pairwise
        distinct nodes, so this side condition has to travel with
        every selection. *)
    Lemma select_nodes_nodup :
      ∀ (xs : list F) (fl : list bool),
      List.NoDup xs -> List.NoDup (select_nodes xs fl).
    Proof.
      induction xs as [|y xs ih]; intros [|b fl] hnd; cbn;
      try constructor.
      inversion hnd as [| ? ? hnin hnd']; subst.
      destruct b.
      + constructor.
        intro hin; eapply hnin; eapply select_nodes_incl; exact hin.
        eapply ih; exact hnd'.
      + eapply ih; exact hnd'.
    Qed.

    (** The point [zero], where the root challenge sits, remains
        distinct from every selected node.

        This is the exact shape of side condition the interpolation
        lemmas ask for: [zero] consed onto the node list must be
        duplicate-free.  It is inherited from the [Hxs] field
        carried by the [CThresh] constructor. *)
    Lemma nodup_zero_select :
      ∀ (xs : list F) (fl : list bool),
      List.NoDup (List.cons zero xs) ->
      List.NoDup (List.cons zero (select_nodes xs fl)).
    Proof.
      intros * hnd.
      inversion hnd as [| ? ? hnin hnd']; subst.
      constructor.
      intro hin; eapply hnin; eapply select_nodes_incl; exact hin.
      eapply select_nodes_nodup; exact hnd'.
    Qed.

    (** The same statement for the verifier's node list: [zero]
        together with the first [n] public nodes are still pairwise
        distinct. *)
    Lemma nodup_zero_firstn :
      ∀ (xs : list F) (n : nat),
      List.NoDup (List.cons zero xs) ->
      List.NoDup (List.cons zero (List.firstn n xs)).
    Proof.
      intros * hnd.
      inversion hnd as [| ? ? hnin hnd']; subst.
      constructor.
      intro hin; eapply hnin; eapply in_firstn; exact hin.
      eapply nodup_firstn; exact hnd'.
    Qed.

    (** The sharing polynomial returns the root challenge at
        [zero].

        By construction [(zero, c)] is one of the interpolation
        points, and an interpolant passes through its own points.
        The two hypotheses are the usual ones: the nodes together
        with [zero] must be pairwise distinct, and there must be as
        many values as nodes, so that [List.combine] loses nothing.

        Soundness rests on this.  It is what lets the rewinding
        argument say that the two reconstructed polynomials really
        do take the two different root challenges at [zero]. *)
    Lemma expand_chal_zero :
      ∀ (c : F) (nodes vals : list F),
      List.NoDup (List.cons zero nodes) ->
      List.length nodes = List.length vals ->
      lag_interpF (List.cons (zero, c) (List.combine nodes vals)) zero = c.
    Proof.
      intros * hnd hl.
      eapply lag_evalF.
      + cbn; rewrite combine_map_fst; [exact hnd | exact hl].
      + left; reflexivity.
    Qed.

    (** A function that matches a list of values on a list of
        nodes, pointwise, maps those nodes onto exactly those
        values.

        A plain induction, stated on its own because this is the
        only place where the pairing performed by [List.combine]
        has to be undone element by element. *)
    Lemma map_of_combine :
      ∀ (nodes vals : list F) (f : F -> F),
      (∀ x v, List.In (x, v) (List.combine nodes vals) -> f x = v) ->
      List.length nodes = List.length vals ->
      List.map f nodes = vals.
    Proof.
      induction nodes as [|x nodes ih]; intros [|v vals] f hf hl;
      cbn in hl |- *; try lia; try reflexivity.
      f_equal.
      + eapply hf; left; reflexivity.
      + eapply ih; [| lia].
        intros y u hin; eapply hf; right; exact hin.
    Qed.

    (** The sharing polynomial returns the prescribed values at the
        prescribed nodes.

        The companion of [expand_chal_zero] for the remaining
        interpolation points.  It is what lets the prover claim
        that the children it faked really did receive the
        challenges it picked for them. *)
    Lemma expand_chal_nodes :
      ∀ (c : F) (nodes vals : list F),
      List.NoDup (List.cons zero nodes) ->
      List.length nodes = List.length vals ->
      List.map (expand_chal c nodes vals) nodes = vals.
    Proof.
      intros * hnd hl.
      eapply map_of_combine; [| exact hl].
      intros x v hin.
      unfold expand_chal.
      eapply lag_evalF.
      + cbn; rewrite combine_map_fst; [exact hnd | exact hl].
      + right; exact hin.
    Qed.

    (** Zipping a list with its own image under [f] contains the
        pair of every element with its image.  A small step inside
        [expand_agree]. *)
    Lemma in_combine_map :
      ∀ (l : list F) (f : F -> F) (x : F),
      List.In x l -> List.In (x, f x) (List.combine l (List.map f l)).
    Proof.
      induction l as [|y l ih]; intros f x hin; cbn in hin |- *.
      + contradiction.
      + destruct hin as [hin | hin].
        ++ subst; left; reflexivity.
        ++ right; eapply ih; exact hin.
    Qed.

    (** The prover's polynomial and the verifier's polynomial are
        the same function.

        The prover pins its polynomial down at the nodes [src], the
        nodes of the children it fakes.  The transcript, however,
        records the polynomial's values at a different node list
        [dst], the first [k - t] public nodes, and that is what the
        verifier re-interpolates from.  This lemma says that
        re-interpolating from the values at [dst] gives back the
        very same function, provided [dst] has the same length as
        [src] and both lists are pairwise distinct and avoid
        [zero].

        The reason is uniqueness of interpolation, [lag_uniqF] from
        Lagrange.v.  Both functions have degree at most the common
        length, and they agree at [zero] and at all of [dst], which
        is one point more than two different functions of that
        degree could agree on.

        This is the hinge of the whole threshold node.
        Completeness needs it, to know that the honest children
        were checked at the challenges they were answered at; the
        distribution proof needs it, to know that the prover's and
        the simulator's challenge functions coincide. *)
    Lemma expand_agree :
      ∀ (c : F) (src vals dst : list F),
      List.NoDup (List.cons zero src) ->
      List.NoDup (List.cons zero dst) ->
      List.length src = List.length vals ->
      List.length dst = List.length src ->
      ∀ x,
      expand_chal c dst (List.map (expand_chal c src vals) dst) x =
      expand_chal c src vals x.
    Proof.
      intros * hsnd hdnd hsl hdl x.
      eapply lag_uniqF with (nodes := List.cons zero dst).
      + exact hdnd.
      + cbn; rewrite List.combine_length, List.map_length; lia.
      + cbn; rewrite List.combine_length; lia.
      + intros a hin.
        destruct hin as [hin | hin].
        ++
          subst a.
          rewrite (expand_chal_zero c src vals hsnd hsl).
          rewrite (expand_chal_zero c dst); [reflexivity | exact hdnd |].
          rewrite List.map_length; reflexivity.
        ++
          rewrite (lag_evalF
            (List.cons (zero, c) (List.combine dst
              (List.map (expand_chal c src vals) dst)))
            a (expand_chal c src vals a)).
          +++ reflexivity.
          +++ cbn; rewrite combine_map_fst; [exact hdnd |].
              rewrite List.map_length; reflexivity.
          +++ right; eapply in_combine_map; exact hin.
    Qed.

    (** ** The simulator always convinces the verifier *)

    (** Every simulated child of a threshold node passes its own
        check.

        The [vall] hypothesis is the induction hypothesis for the
        children, supplied by [comp_rel_ind'].  The lemma exists
        only to carry that hypothesis across the walk over the
        vector of children. *)
    Lemma verlist_simlist :
      ∀ (n : nat) (v : Vector.t comp_rel n) (s : rlist v)
        (chal : nat -> F) (i : nat),
      vall (fun r => ∀ (s : comp_rand r) (c : F),
        comp_verify r c (comp_simulate r s c) = true) v ->
      verlist v chal (simlist v s chal i) i = true.
    Proof.
      induction v as [|r n v ih]; intros s chal i hall; cbn.
      + reflexivity.
      + destruct hall as (hr & hall).
        eapply andb_true_iff; split.
        eapply hr. eapply ih; exact hall.
    Qed.

    (** The simulator's output is accepted, for every statement,
        every randomness and every challenge.

        On its own this is not a security property but a sanity
        check: a simulator producing rejected transcripts would be
        trivial to write and would say nothing about zero
        knowledge.  It is also used inside [comp_completeness],
        because the honest prover itself simulates the branches it
        has no witness for. *)
    Theorem comp_simulate_completeness :
      ∀ (r : comp_rel) (s : comp_rand r) (c : F),
      comp_verify r c (comp_simulate r s c) = true.
    Proof.
      induction r as [m n mat pub | rl rr ihl ihr | rl rr ihl ihr
        | t k xs rs Hxs Ht ihrs] using comp_rel_ind'.
      +
        intros *; cbn.
        eapply linear_relation_simulator_completeness.
      +
        intros *; cbn.
        eapply andb_true_iff; split.
        eapply ihl. eapply ihr.
      +
        intros *; cbn.
        eapply andb_true_iff; split.
        eapply ihl. eapply ihr.
      +
        intros *; cbn.
        eapply andb_true_iff; split.
        eapply Nat.eqb_eq; eapply length_to_list.
        eapply verlist_simlist; exact ihrs.
    Qed.

    (** ** Completeness *)

    (** Every child of a threshold node passes its check, whether
        it was proven or faked.

        The [vall] hypothesis is again the induction hypothesis for
        the children, and [wholds v w] says that every witness
        present is genuine.

        The pair of challenge functions [chal] and [chal'],
        assumed equal at every index, is there for a concrete
        reason: the prover and the verifier reach a child's
        challenge by two syntactically different routes.  The
        prover interpolates through the nodes it selected, the
        verifier through the first [k - t] nodes.  [expand_agree]
        shows the two routes give the same function, and this
        lemma is stated so that it can take that agreement as a
        hypothesis instead of rediscovering it. *)
    Lemma verlist_provelist :
      ∀ (n : nat) (v : Vector.t comp_rel n) (w : wlist v) (s : rlist v)
        (fl : list bool) (chal chal' : nat -> F) (i : nat),
      vall (fun r => ∀ (w : comp_witness r) (s : comp_rand r) (c : F),
        comp_rel_holds r w -> comp_verify r c (comp_prove r w s c) = true) v ->
      wholds v w ->
      (∀ j, chal' j = chal j) ->
      verlist v chal' (provelist v w s fl chal i) i = true.
    Proof.
      induction v as [|r n v ih]; intros w s fl chal chal' i hall hw hc; cbn.
      + reflexivity.
      + destruct hall as (hr & hall).
        destruct w as (ow & w'); cbn in hw |- *.
        destruct hw as (hw & hw').
        eapply andb_true_iff; split.
        ++
          rewrite hc.
          destruct ow as [x |]; [destruct fl as [| [|] fl] |];
          try (eapply hr; exact hw);
          eapply comp_simulate_completeness.
        ++
          eapply ih; assumption.
    Qed.

    (** Completeness: an honest prover holding a genuine witness
        always convinces the verifier.

        The proof is the structural induction.  Leaves are the
        completeness of the linear-relation protocol.  [CAnd] is
        immediate.  At a [COr] the point worth noticing is that the
        branch simulated at the committed challenge is checked by
        the verifier at the root challenge minus its complement,
        which is the committed challenge again.  At a [CThresh] the
        counting lemmas give that exactly [k - t] values are
        recorded, so the length test passes, and [expand_agree]
        gives that each child is checked at the very challenge it
        was answered at. *)
    Theorem comp_completeness :
      ∀ (r : comp_rel) (w : comp_witness r) (s : comp_rand r) (c : F),
      comp_rel_holds r w ->
      comp_verify r c (comp_prove r w s c) = true.
    Proof.
      induction r as [m n mat pub | rl rr ihl ihr | rl rr ihl ihr
        | t k xs rs Hxs Ht ihrs] using comp_rel_ind'.
      +
        intros * ha; cbn.
        eapply linear_relation_completeness.
        rewrite ha; reflexivity.
      +
        intros * ha; cbn in ha |- *.
        destruct ha as (hal & har).
        eapply andb_true_iff; split.
        eapply ihl; exact hal.
        eapply ihr; exact har.
      +
        intros * ha; cbn in ha |- *.
        destruct w as [wl | wr]; cbn.
        ++
          eapply andb_true_iff; split.
          eapply ihl; exact ha.
          assert (hb : c - (c - snd s) = snd s). field.
          rewrite hb.
          eapply comp_simulate_completeness.
        ++
          eapply andb_true_iff; split.
          eapply comp_simulate_completeness.
          eapply ihr; exact ha.
      +
        intros * ha; cbn in ha |- *.
        destruct ha as (hcount & hholds).
        pose proof (length_to_list F k xs) as Hlen.
        set (xl := Vector.to_list xs) in *.
        eapply andb_true_iff; split.
        ++
          eapply Nat.eqb_eq.
          rewrite List.map_length.
          eapply List.firstn_length_le; lia.
        ++
          pose proof (wcount_le k rs w) as hle.
          assert (hsl : List.length
            (select_nodes xl (sim_flags rs w (wcount rs w - t))) = (k - t)%nat).
          { rewrite select_nodes_length, sim_flags_count.
            rewrite Nat.min_l; lia.
            rewrite sim_flags_length; symmetry; exact Hlen. }
          eapply verlist_provelist; try assumption.
          intro j.
          eapply expand_agree.
          +++ eapply nodup_zero_select; exact Hxs.
          +++ eapply nodup_zero_firstn; exact Hxs.
          +++ rewrite hsl, length_to_list; reflexivity.
          +++ rewrite hsl; eapply List.firstn_length_le; lia.
    Qed.

    (** ** Special soundness *)

    (** From two accepting runs of the children of a threshold
        node, extract a witness for every child whose two
        challenges differed.

        The [vall] hypothesis is the children's induction
        hypothesis; [salist v ts ts'] says the two runs used the
        same announcements child by child; the two [verlist]
        hypotheses say both runs were accepted.

        The conclusion is deliberately quantitative.  It does not
        merely produce a witness list: it states that the number of
        witnesses obtained is exactly the number of positions in
        the index range where the two challenge functions disagree.
        That number is what the counting theorem of Shamir.v bounds
        from below, so the two results fit together to give the
        threshold condition [t <= wcount rs w]. *)
    Lemma extract_list :
      ∀ (n : nat) (v : Vector.t comp_rel n) (i : nat)
        (chal chal' : nat -> F) (ts ts' : tlist v),
      vall (fun r => ∀ (c c' : F) (t t' : comp_transcript r),
        c <> c' -> comp_same_announcement r t t' ->
        comp_verify r c t = true -> comp_verify r c' t' = true ->
        ∃ w, comp_rel_holds r w) v ->
      salist v ts ts' ->
      verlist v chal ts i = true -> verlist v chal' ts' i = true ->
      ∃ w : wlist v,
        wholds v w ∧
        wcount v w =
        List.length (List.filter
          (fun j => negb (if Fdec (chal j) (chal' j) then true else false))
          (List.seq i n)).
    Proof.
      induction v as [|r n v ih]; intros i chal chal' ts ts' hall hsa hv hv'.
      + exists tt; split; [exact I | reflexivity].
      + cbn in hall, hsa, hv, hv'.
        destruct hall as (hr & hall).
        destruct hsa as (hsa & hsa').
        eapply andb_true_iff in hv, hv'.
        destruct hv as (hv1 & hv2).
        destruct hv' as (hv1' & hv2').
        destruct (ih (S i) chal chal' (snd ts) (snd ts') hall hsa' hv2 hv2')
          as (w' & hw' & hcnt).
        cbn.
        destruct (Fdec (chal i) (chal' i)) as [heq | hne]; cbn.
        ++
          exists (None, w'); cbn.
          split; [split; [exact I | exact hw'] | exact hcnt].
        ++
          destruct (hr _ _ _ _ hne hsa hv1 hv1') as (x & hx).
          exists (Some x, w'); cbn.
          split; [split; [exact hx | exact hw'] | rewrite hcnt; reflexivity].
    Qed.

    (** Special soundness: two accepting transcripts with the same
        announcements but different challenges yield a witness.

        This is the precise sense in which the protocol proves
        knowledge.  A prover able to answer two different
        challenges after committing to a single announcement could,
        by this theorem, compute a witness.  So a prover that
        cannot compute one succeeds for at most one challenge out
        of the whole challenge space.

        Node by node:

        - At a [Leaf] the two responses differ by the challenge
          difference times the secret, and dividing recovers the
          secret.  That is the special soundness of
          LinearRelation.v.
        - At a [CAnd] the same pair of challenges serves both
          children, giving a witness for each.
        - At a [COr] the two child challenges add up to the root
          challenge in both runs.  Since the root challenges
          differ, the left pair and the right pair cannot both
          agree.  Whichever side differs is the side that yields a
          witness, and the proof simply case-splits on that.
        - At a [CThresh] the two runs induce two sharing
          polynomials, each of degree at most [k - t], taking the
          two different root challenges at [zero].  If they agreed
          at more than [k - t] of the public nodes they would be
          the same polynomial and would then agree at [zero] as
          well.  Hence they disagree at at least [t] nodes, which
          is [thresh_extractF] from Shamir.v, and [extract_list]
          turns every disagreeing child into a witness. *)
    Theorem comp_special_soundness :
      ∀ (r : comp_rel) (c c' : F)
        (tr tr' : comp_transcript r),
      c <> c' ->
      comp_same_announcement r tr tr' ->
      comp_verify r c tr = true ->
      comp_verify r c' tr' = true ->
      ∃ (w : comp_witness r), comp_rel_holds r w.
    Proof.
      induction r as [m n mat pub | rl rr ihl ihr | rl rr ihl ihr
        | t k xs rs Hxs Ht ihrs] using comp_rel_ind'.
      +
        intros * ha hb hc hd.
        destruct tr as (comm & res).
        destruct tr' as (comm' & res').
        cbn in hb, hc, hd; subst.
        eapply linear_relation_special_soundness.
        exact ha. exact hc. exact hd.
      +
        intros * ha hb hc hd.
        destruct tr as (tl & tr).
        destruct tr' as (tl' & tr').
        cbn in hb, hc, hd.
        destruct hb as (hbl & hbr).
        eapply andb_true_iff in hc, hd.
        destruct hc as (hcl & hcr).
        destruct hd as (hdl & hdr).
        destruct (ihl _ _ _ _ ha hbl hcl hdl) as (wl & hwl).
        destruct (ihr _ _ _ _ ha hbr hcr hdr) as (wr & hwr).
        exists (wl, wr); cbn.
        exact (conj hwl hwr).
      +
        intros * ha hb hc hd.
        destruct tr as ((tl & tr) & e).
        destruct tr' as ((tl' & tr') & e').
        cbn in hb, hc, hd.
        destruct hb as (hbl & hbr).
        eapply andb_true_iff in hc, hd.
        destruct hc as (hcl & hcr).
        destruct hd as (hdl & hdr).
        destruct (Fdec e e') as [he | he].
        ++
          (* left challenges equal, so right challenges differ *)
          subst e'.
          assert (hf : c - e <> c' - e).
          intro hf. eapply ha.
          eapply f_equal with (f := fun x => x + e) in hf.
          assert (hg : ∀ a : F, a - e + e = a). intros; field.
          rewrite !hg in hf. exact hf.
          destruct (ihr _ _ _ _ hf hbr hcr hdr) as (wr & hwr).
          exists (inr wr); cbn.
          exact hwr.
        ++
          (* left challenges differ *)
          destruct (ihl _ _ _ _ he hbl hcl hdl) as (wl & hwl).
          exists (inl wl); cbn.
          exact hwl.
      +
        intros * ha hb hc hd.
        destruct tr as (ts & ds).
        destruct tr' as (ts' & ds').
        cbn in hb, hc, hd.
        eapply andb_true_iff in hc, hd.
        destruct hc as (hc1 & hc2).
        destruct hd as (hd1 & hd2).
        eapply Nat.eqb_eq in hc1, hd1.
        pose proof (length_to_list F k xs) as Hlen.
        set (xl := Vector.to_list xs) in *.
        destruct (extract_list k rs 0 _ _ ts ts' ihrs hb hc2 hd2)
          as (w & hw & hcnt).
        exists w; cbn.
        split; [| exact hw].
        rewrite hcnt.
        assert (hfl : List.length (List.firstn (k - t) xl) = (k - t)%nat).
        { eapply List.firstn_length_le; lia. }
        set (f := expand_chal c (List.firstn (k - t) xl) ds).
        set (f' := expand_chal c' (List.firstn (k - t) xl) ds').
        set (CS := List.map (chal_of xl f) (List.seq 0 k)).
        set (CS' := List.map (chal_of xl f') (List.seq 0 k)).
        assert (hnd : List.NoDup xl).
        { inversion Hxs; assumption. }
        assert (hnth : ∀ g i, (i < k)%nat ->
          List.nth i (List.map (chal_of xl g) (List.seq 0 k)) zero =
          g (List.nth i xl zero)).
        { intros g i hi. rewrite nth_map_seq; [reflexivity | exact hi]. }
        assert (hext : (t <= List.length
          (List.filter (fun i => negb (agreebF CS CS' i)) (List.seq 0 k)))%nat).
        {
          eapply (thresh_extractF k t xl CS CS'
            (List.cons (zero, c) (List.combine (List.firstn (k - t) xl) ds))
            (List.cons (zero, c') (List.combine (List.firstn (k - t) xl) ds'))
            c c').
          + exact Ht.
          + exact hnd.
          + exact Hlen.
          + cbn; rewrite List.combine_length, hfl, hc1; lia.
          + cbn; rewrite List.combine_length, hfl, hd1; lia.
          + eapply (expand_chal_zero c).
            eapply nodup_zero_firstn; exact Hxs. congruence.
          + eapply (expand_chal_zero c').
            eapply nodup_zero_firstn; exact Hxs. congruence.
          + intros i hi. unfold CS. rewrite hnth; [reflexivity | exact hi].
          + intros i hi. unfold CS'. rewrite hnth; [reflexivity | exact hi].
          + exact ha.
        }
        rewrite List.filter_ext_in with
          (g := fun i => negb (agreebF CS CS' i)).
        exact hext.
        intros i hi.
        eapply List.in_seq in hi.
        unfold agreeb, CS, CS'.
        rewrite !hnth; [reflexivity | lia | lia].
    Qed.

    (** ** Zero knowledge, accept-bit form *)

    (** Every randomness for the children of a threshold node is
        drawn with the same probability.

        That probability is one over the size of the challenge
        space raised to [slist v], the total number of scalars
        drawn across the children.  The draws for different
        children are independent, so the probabilities multiply and
        the exponents add. *)
    Lemma rand_list_prob :
      ∀ (n : nat) (v : Vector.t comp_rel n) (lf : list F)
        (Hlfn : lf <> List.nil) (s : rlist v) (q : prob),
      vall (fun r => ∀ (lf : list F) (Hlfn : lf <> List.nil)
        (s : comp_rand r) (q : prob),
        List.In (s, q) (comp_rand_distribution lf Hlfn r) ->
        q = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) (comp_size r)))) v ->
      List.In (s, q) (rand_list lf Hlfn v) ->
      q = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) (slist v))).
    Proof.
      induction v as [|r n v ih]; intros lf Hlfn s q hall hin; cbn in hin |- *.
      +
        destruct hin as [hin | hin]; [| contradiction].
        inversion hin; subst.
        reflexivity.
      +
        destruct hall as (hr & hall).
        assert (hL : List.length lf <> 0%nat).
        destruct lf; [congruence | cbn; lia].
        eapply bind_in_inv in hin.
        destruct hin as (x & px & py & hb & hc & hd).
        eapply bind_ret_prob in hc.
        2: { intros y qy he. eapply ih; [exact hall | exact he]. }
        eapply hr in hb.
        subst.
        rewrite PeanoNat.Nat.pow_add_r.
        eapply prob_mul_split;
        eapply PeanoNat.Nat.pow_nonzero; exact hL.
    Qed.

    (** The prover randomness is uniform: every value occurring in
        [comp_rand_distribution lf Hlfn r] carries probability one
        over the size of [lf] raised to the power [comp_size r].

        Nothing in the definition favours any value, since it is
        built only from uniform draws and independent products.
        The proof is the structural induction, splitting a product
        of two uniform probabilities at each internal node. *)
    Lemma comp_rand_distribution_prob :
      ∀ (r : comp_rel) (lf : list F) (Hlfn : lf <> List.nil)
        (s : comp_rand r) (q : prob),
      List.In (s, q) (comp_rand_distribution lf Hlfn r) ->
      q = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) (comp_size r))).
    Proof.
      induction r as [m n mat pub | rl rr ihl ihr | rl rr ihl ihr
        | t k xs rs Hxs Ht ihrs] using comp_rel_ind'.
      +
        intros * ha; cbn in ha |- *.
        eapply uniform_probability_multidraw_prob.
        exact ha.
      +
        intros * ha; cbn in ha |- *.
        assert (hL : List.length lf <> 0%nat).
        destruct lf; [congruence | cbn; lia].
        eapply bind_in_inv in ha.
        destruct ha as (sl & px & py & hb & hc & hd).
        eapply bind_ret_prob in hc.
        2: { intros x qx he. eapply ihr. exact he. }
        specialize (ihl lf Hlfn sl px hb).
        subst.
        rewrite PeanoNat.Nat.pow_add_r.
        eapply prob_mul_split;
        eapply PeanoNat.Nat.pow_nonzero; exact hL.
      +
        intros * ha; cbn in ha |- *.
        assert (hL : List.length lf <> 0%nat).
        destruct lf; [congruence | cbn; lia].
        eapply bind_in_inv in ha.
        destruct ha as (c₁ & px & py & hb & hc & hd).
        eapply bind_in_inv in hc.
        destruct hc as (sl & px2 & py2 & he & hf & hg).
        eapply bind_ret_prob in hf.
        2: { intros x qx hh. eapply ihr. exact hh. }
        eapply uniform_probability in hb.
        specialize (ihl lf Hlfn sl px2 he).
        subst.
        assert (h₁ : Nat.pow (List.length lf) (comp_size rl) <> 0%nat).
        eapply PeanoNat.Nat.pow_nonzero; exact hL.
        assert (h₂ : Nat.pow (List.length lf) (comp_size rr) <> 0%nat).
        eapply PeanoNat.Nat.pow_nonzero; exact hL.
        rewrite (prob_mul_split _ _ h₁ h₂).
        rewrite prob_mul_split; [| exact hL | nia].
        f_equal; f_equal.
        rewrite ?PeanoNat.Nat.pow_succ_r', ?PeanoNat.Nat.pow_add_r.
        reflexivity.
      +
        intros * ha; cbn in ha |- *.
        assert (hL : List.length lf <> 0%nat).
        destruct lf; [congruence | cbn; lia].
        eapply bind_in_inv in ha.
        destruct ha as (d & px & py & hb & hc & hd).
        eapply bind_ret_prob in hc.
        2: { intros x qx he. eapply rand_list_prob; [exact ihrs | exact he]. }
        eapply uniform_probability_multidraw_prob in hb.
        subst.
        rewrite prob_mul_split;
        try (eapply PeanoNat.Nat.pow_nonzero; exact hL).
        f_equal; f_equal.
        rewrite PeanoNat.Nat.pow_add_r; nia.
    Qed.

    (** Everything the real prover can output is accepted, and is
        output with the uniform probability.

        The first half is [comp_completeness] transported along the
        [Ret] at the end of the distribution; the second half is
        [comp_rand_distribution_prob].  This is one of the two
        halves of the accept-bit zero-knowledge theorem. *)
    Lemma comp_real_distribution_transcript_generic :
      ∀ (r : comp_rel) (lf : list F) (Hlfn : lf <> List.nil)
        (w : comp_witness r) (c : F) (t : comp_transcript r)
        (p : prob),
      comp_rel_holds r w ->
      List.In (t, p) (comp_real_distribution lf Hlfn r w c) ->
      comp_verify r c t = true ∧
      p = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) (comp_size r))).
    Proof.
      intros * ha hb.
      refine (conj _ _).
      +
        unfold comp_real_distribution in hb.
        eapply bind_ret_in in hb.
        destruct hb as (s & q & hc & hd & he).
        subst.
        eapply comp_completeness.
        exact ha.
      +
        unfold comp_real_distribution in hb.
        eapply bind_ret_prob in hb.
        exact hb.
        intros s q hc.
        eapply comp_rand_distribution_prob.
        exact hc.
    Qed.

    (** The same for the simulator, and this time with no witness
        hypothesis at all: everything the simulator can output is
        accepted, and carries the same uniform probability. *)
    Lemma comp_simulator_distribution_transcript_generic :
      ∀ (r : comp_rel) (lf : list F) (Hlfn : lf <> List.nil)
        (c : F) (t : comp_transcript r) (p : prob),
      List.In (t, p) (comp_simulator_distribution lf Hlfn r c) ->
      comp_verify r c t = true ∧
      p = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) (comp_size r))).
    Proof.
      intros * ha.
      refine (conj _ _).
      +
        unfold comp_simulator_distribution in ha.
        eapply bind_ret_in in ha.
        destruct ha as (s & q & hb & hc & hd).
        subst.
        eapply comp_simulate_completeness.
      +
        unfold comp_simulator_distribution in ha.
        eapply bind_ret_prob in ha.
        exact ha.
        intros s q hb.
        eapply comp_rand_distribution_prob.
        exact hb.
    Qed.

    (** Special honest-verifier zero knowledge, accept-bit form.

        Map every transcript in the real distribution to its accept
        bit, keeping its probability; do the same for the simulated
        distribution; the two resulting lists are equal.

        Honest-verifier means the challenge [c] is fixed in advance
        rather than chosen adversarially after the announcement is
        seen.  The statement says that an observer who only sees
        whether transcripts are accepted, and how likely they are,
        learns nothing: both distributions consist entirely of
        accepting transcripts occurring with the same uniform
        probability.

        This form is weak.  It says nothing about the transcripts
        themselves, so it cannot tell whether the prover used the
        left or the right branch of a [COr].  The strong statement
        is [comp_distribution_perm] below. *)
    Theorem comp_special_honest_verifier_zkp :
      ∀ (r : comp_rel) (lf : list F) (Hlfn : lf <> List.nil)
        (w : comp_witness r) (c : F),
      comp_rel_holds r w ->
      List.map (fun '(t, p) => (comp_verify r c t, p))
        (comp_real_distribution lf Hlfn r w c) =
      List.map (fun '(t, p) => (comp_verify r c t, p))
        (comp_simulator_distribution lf Hlfn r c).
    Proof.
      intros * ha.
      eapply map_ext_eq.
      +
        unfold comp_real_distribution,
          comp_simulator_distribution.
        repeat rewrite distribution_length.
        reflexivity.
      +
        intros t p hb.
        eapply comp_real_distribution_transcript_generic.
        exact ha. exact hb.
      +
        intros t p hb.
        eapply comp_simulator_distribution_transcript_generic.
        exact hb.
    Qed.

    (** ** Zero knowledge as equality of distributions *)
    (** The accept-bit theorem above compares only accept bits, so
        it cannot distinguish a prover using one witness of a [COr]
        or a [CThresh] from a prover using another: both are simply
        accepted.

        What follows proves the real thing.  The real and the
        simulated transcript distributions are equal as
        distributions.  A distribution here is a concrete list of
        value and probability pairs, built by [Bind] and [Ret], so
        equality of distributions means equality up to reordering,
        that is [Permutation]; this is [dist_equiv] in
        Probability/Distr.v.

        One extra assumption is needed, and it is the natural one:
        the challenge space [lf] must enumerate the field without
        duplicates.  Every proof below works by exhibiting a
        bijection of the prover's randomness that carries the real
        output to the simulated output, and a bijection permutes a
        uniform draw only when that draw really does list every
        value exactly once.

        Witness indistinguishability,
        [comp_witness_indistinguishable], then follows in three
        lines. *)

    (** A tactic that flattens a nested tower of [Bind] and [Ret]
        into a normal form, descending under binders.  Pure
        bookkeeping: the definitions of the distributions produce
        towers associated differently from the ones the statements
        below are written with, and this makes the two match. *)
    Ltac norm_bind :=
      repeat first
        [ rewrite bind_assoc
        | rewrite bind_ret_left
        | progress cbn [fst snd]
        | (eapply bind_ext; intro) ].

    (** [zip_with] computed on a pair of non-empty vectors.  True
        by definition, stated as a lemma so that it can be
        rewritten with underneath a binder. *)
    Lemma zip_with_cons :
      ∀ {A B C : Type} (n : nat) (f : A -> B -> C)
        (a : A) (v : Vector.t A n) (b : B) (w : Vector.t B n),
      zip_with f (a :: v) (b :: w) = f a b :: zip_with f v w.
    Proof.
      intros *; reflexivity.
    Qed.

    (** ** Uniform multidraws and bijections of the randomness *)

    (** Drawing [n] scalars uniformly and independently: a pair of
        a vector and a probability occurs in the distribution
        exactly when the probability is the uniform one.

        The left-to-right direction is uniformity.  The
        right-to-left direction is completeness of the enumeration,
        and this is where the hypotheses that [lf] is duplicate-free
        and contains every field element are used.  Together they
        say that the multidraw lists every vector of [n] scalars
        exactly once, which is precisely what a bijection needs in
        order to permute it. *)
    Lemma multidraw_in_iff :
      ∀ (lf : list F) (Hlfn : lf <> List.nil) (n : nat)
        (v : Vector.t F n) (p : prob),
      List.NoDup lf -> (∀ x : F, List.In x lf) ->
      (List.In (v, p) (repeat_dist_ntimes_vector
        (uniform_with_replacement lf Hlfn) n) <->
       p = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) n))).
    Proof.
      intros * hnd hin; split; intro ha.
      + eapply uniform_probability_multidraw_prob; exact ha.
      + subst.
        destruct (multidraw_complete lf Hlfn n v hin) as (q & hq).
        pose proof (uniform_probability_multidraw_prob _ _ _ _ _ hq); subst.
        exact hq.
    Qed.

    (** A bijection of the randomness only permutes the
        distribution.

        [φ] and [ψ] are mutually inverse maps on vectors of [n]
        scalars, as stated by the two round-trip hypotheses.
        Drawing [v] uniformly and continuing with [g] applied to
        [φ v] yields the same list of outcomes, up to order, as
        drawing [v] and continuing with [g] directly: the bijection
        merely renames which draw produces which outcome, and all
        draws are equally likely.

        This is the engine of the strong zero-knowledge proof.  At
        each kind of node one exhibits the bijection turning the
        prover's randomness into the simulator's, and this lemma
        converts it into an equality of distributions.  At a
        threshold node that bijection is the change of
        interpolation nodes, [shift_nodes]. *)
    Lemma multidraw_bij_perm {B : Type} :
      ∀ (lf : list F) (Hlfn : lf <> List.nil) (n : nat)
        (φ ψ : Vector.t F n -> Vector.t F n) (g : Vector.t F n -> dist B),
      List.NoDup lf -> (∀ x : F, List.In x lf) ->
      (∀ v, ψ (φ v) = v) -> (∀ v, φ (ψ v) = v) ->
      Permutation
        (Bind (repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn) n)
          (fun v => g (φ v)))
        (Bind (repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn) n) g).
    Proof.
      intros * hnd hin hψφ hφψ.
      rewrite <-bind_map_values.
      eapply bind_perm_left.
      eapply NoDup_Permutation.
      +
        eapply Injective_map_NoDup.
        ++
          intros (v, p) (v', p') heq.
          inversion heq as [(heq1 & heq2)].
          rewrite <-(hψφ v), <-(hψφ v'), heq1; reflexivity.
        ++
          eapply NoDup_map_inv with (f := fst).
          eapply multidraw_nodup; exact hnd.
      +
        eapply NoDup_map_inv with (f := fst).
        eapply multidraw_nodup; exact hnd.
      +
        intros (u, p); split; intro ha.
        ++
          eapply in_map_iff in ha.
          destruct ha as ((v & q) & heq & hv).
          inversion heq; subst.
          eapply multidraw_in_iff; try assumption.
          eapply multidraw_in_iff in hv; assumption.
        ++
          eapply multidraw_in_iff in ha; try assumption; subst.
          eapply in_map_iff.
          exists (ψ u, mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) n))).
          split.
          +++ rewrite hφψ; reflexivity.
          +++ eapply multidraw_in_iff; try assumption; reflexivity.
    Qed.

    (** The leaf bijection: translating every coordinate of a
        uniform multidraw permutes it.

        The map sends the commitment randomness [us] to
        [zip_with (fun u x => u + c * x) us xs], which is exactly
        the honest prover's response.  Adding a fixed field element
        is a bijection of a field, so the uniform distribution is
        unchanged.

        This single fact is the whole of zero knowledge at a leaf:
        the honest response is a uniformly random vector, and
        therefore tells the verifier nothing about the secret
        [xs]. *)
    Lemma multidraw_shift_perm :
      ∀ (n : nat) (lf : list F) (Hlfn : lf <> List.nil) (c : F)
        (xs : Vector.t F n) {B : Type} (f : Vector.t F n -> dist B),
      List.NoDup lf -> (∀ x : F, List.In x lf) ->
      Permutation
        (Bind (repeat_dist_ntimes_vector
          (uniform_with_replacement lf Hlfn) n)
          (fun us => f (zip_with (fun u x => u + c * x) us xs)))
        (Bind (repeat_dist_ntimes_vector
          (uniform_with_replacement lf Hlfn) n) f).
    Proof.
      induction n as [|n ihn].
      +
        intros * hnd hin.
        rewrite (vector_inv_0 xs).
        cbn [repeat_dist_ntimes_vector].
        rewrite !bind_ret_left; cbn.
        reflexivity.
      +
        intros * hnd hin.
        destruct (vector_inv_S xs) as (xh & xt & ha); subst.
        rewrite !bind_multidraw_S.
        erewrite bind_ext with
          (l := uniform_with_replacement lf Hlfn)
          (g := fun u =>
            Bind (repeat_dist_ntimes_vector
              (uniform_with_replacement lf Hlfn) n)
              (fun v => f ((u + c * xh) ::
                zip_with (fun u x => u + c * x) v xt))).
        2: { intro u. eapply bind_ext; intro v.
             cbn beta. rewrite zip_with_cons. reflexivity. }
        eapply Permutation_trans.
        eapply uniform_shift_perm with
          (σ := fun u => u + c * xh) (τ := fun u => u - c * xh)
          (f := fun u =>
            Bind (repeat_dist_ntimes_vector
              (uniform_with_replacement lf Hlfn) n)
              (fun v => f (u :: zip_with (fun u x => u + c * x) v xt))).
        exact hnd. exact hin.
        intro; cbn beta; field. intro; cbn beta; field.
        eapply bind_perm_right; intro u.
        eapply ihn with (f := fun v => f (u :: v)); assumption.
    Qed.

    (** ** The Shamir share bijection *)

    (** Transport a vector along a proof that its length equals
        another number.  Plumbing: it lets a list known to have
        length [m] be used where a [Vector.t A m] is expected. *)
    Definition vec_cast {A : Type} {n m : nat} (H : n = m)
      (v : Vector.t A n) : Vector.t A m :=
      eq_rect n (Vector.t A) v m H.

    (** Casting a vector does not change its underlying list. *)
    Lemma to_list_vec_cast :
      ∀ {A : Type} {n m : nat} (H : n = m) (v : Vector.t A n),
      Vector.to_list (vec_cast H v) = Vector.to_list v.
    Proof.
      intros *; destruct H; reflexivity.
    Qed.

    (** Re-express a set of shares at a different set of nodes.

        [shift_nodes c m src dst Hdst d] reads the [m] values [d]
        as the values of the sharing polynomial at the nodes [src],
        rebuilds that polynomial, and returns its values at the
        nodes [dst].

        This is the map relating the prover to the simulator at a
        threshold node.  The prover draws its free scalars and
        treats them as values at the nodes of the children it
        fakes; the simulator draws the same scalars and treats them
        as values at the first [k - t] nodes.  [shift_nodes]
        converts one reading into the other. *)
    Definition shift_nodes (c : F) (m : nat) (src dst : list F)
      (Hdst : List.length dst = m) (d : Vector.t F m) : Vector.t F m :=
      Vector.map (expand_chal c src (Vector.to_list d))
        (vec_cast Hdst (Vector.of_list dst)).

    (** [shift_nodes] viewed as an operation on lists: it maps the
        rebuilt sharing polynomial over the destination nodes. *)
    Lemma to_list_shift_nodes :
      ∀ (c : F) (m : nat) (src dst : list F) (Hdst : List.length dst = m)
        (d : Vector.t F m),
      Vector.to_list (shift_nodes c m src dst Hdst d) =
      List.map (expand_chal c src (Vector.to_list d)) dst.
    Proof.
      intros *; unfold shift_nodes.
      rewrite to_list_map, to_list_vec_cast, to_list_of_list_opp.
      reflexivity.
    Qed.

    (** Changing nodes and then changing back is the identity.

        Both node lists have the same length [m], and both are
        pairwise distinct and avoid [zero], so both readings
        determine the same polynomial of degree at most [m];
        going one way and back therefore returns the original
        values.  This is what makes [shift_nodes] one half of the
        bijection pair required by [multidraw_bij_perm]. *)
    Lemma shift_nodes_inv :
      ∀ (c : F) (m : nat) (src dst : list F)
        (Hsrc : List.length src = m) (Hdst : List.length dst = m)
        (d : Vector.t F m),
      List.NoDup (List.cons zero src) -> List.NoDup (List.cons zero dst) ->
      shift_nodes c m dst src Hsrc (shift_nodes c m src dst Hdst d) = d.
    Proof.
      intros * hsnd hdnd.
      eapply to_list_inj.
      rewrite !to_list_shift_nodes.
      rewrite <-(expand_chal_nodes c src (Vector.to_list d) hsnd) at 2;
      [| rewrite length_to_list; exact Hsrc].
      eapply List.map_ext.
      intro x.
      eapply expand_agree; try assumption.
      rewrite length_to_list; exact Hsrc.
      congruence.
    Qed.

    (** ** Normal forms of the two distributions at each node

        Each of the next seven lemmas unfolds one distribution at
        one kind of node into an explicit tower of [Bind] and
        [Ret] over the children's distributions.  They hold by
        computation alone.  They exist so that the permutation
        proof can work node by node without ever unfolding the
        prover or the simulator again. *)

    (** The real distribution at a [CAnd] node is the independent
        product of the two children's real distributions, both
        taken at the same challenge. *)
    Lemma comp_real_and_eq :
      ∀ (rl rr : comp_rel) (lf : list F) (Hlfn : lf <> List.nil)
        (wl : comp_witness rl) (wr : comp_witness rr) (c : F),
      comp_real_distribution lf Hlfn (CAnd rl rr) (wl, wr) c =
      Bind (comp_real_distribution lf Hlfn rl wl c) (fun tl =>
        Bind (comp_real_distribution lf Hlfn rr wr c) (fun tr =>
          Ret (tl, tr))).
    Proof.
      intros *.
      unfold comp_real_distribution;
      cbn [comp_rand_distribution comp_prove].
      norm_bind; reflexivity.
    Qed.

    (** The same shape for the simulator at a [CAnd] node. *)
    Lemma comp_sim_and_eq :
      ∀ (rl rr : comp_rel) (lf : list F) (Hlfn : lf <> List.nil) (c : F),
      comp_simulator_distribution lf Hlfn (CAnd rl rr) c =
      Bind (comp_simulator_distribution lf Hlfn rl c) (fun tl =>
        Bind (comp_simulator_distribution lf Hlfn rr c) (fun tr =>
          Ret (tl, tr))).
    Proof.
      intros *.
      unfold comp_simulator_distribution;
      cbn [comp_rand_distribution comp_simulate].
      norm_bind; reflexivity.
    Qed.

    (** The real distribution at a [COr] node when the prover holds
        a left witness: draw the branch challenge [c₁] uniformly,
        prove the left child at [c - c₁], simulate the right child
        at [c₁], and record [c - c₁] as the stored challenge. *)
    Lemma comp_real_or_inl_eq :
      ∀ (rl rr : comp_rel) (lf : list F) (Hlfn : lf <> List.nil)
        (wl : comp_witness rl) (c : F),
      comp_real_distribution lf Hlfn (COr rl rr) (inl wl) c =
      Bind (uniform_with_replacement lf Hlfn) (fun c₁ =>
        Bind (comp_real_distribution lf Hlfn rl wl (c - c₁)) (fun tl =>
          Bind (comp_simulator_distribution lf Hlfn rr c₁) (fun tr =>
            Ret (tl, tr, c - c₁)))).
    Proof.
      intros *.
      unfold comp_real_distribution, comp_simulator_distribution;
      cbn [comp_rand_distribution comp_prove comp_simulate].
      norm_bind; reflexivity.
    Qed.

    (** The real distribution at a [COr] node when the prover holds
        a right witness: draw [c₁], simulate the left child at
        [c₁], prove the right child at [c - c₁], and record [c₁].

        Note that this already has the shape of the simulated
        distribution with one simulator call replaced by a prover
        call, so the induction closes immediately.  The left-witness
        case above needs a change of variable first, because there
        the roles of [c₁] and [c - c₁] are swapped. *)
    Lemma comp_real_or_inr_eq :
      ∀ (rl rr : comp_rel) (lf : list F) (Hlfn : lf <> List.nil)
        (wr : comp_witness rr) (c : F),
      comp_real_distribution lf Hlfn (COr rl rr) (inr wr) c =
      Bind (uniform_with_replacement lf Hlfn) (fun c₁ =>
        Bind (comp_simulator_distribution lf Hlfn rl c₁) (fun tl =>
          Bind (comp_real_distribution lf Hlfn rr wr (c - c₁)) (fun tr =>
            Ret (tl, tr, c₁)))).
    Proof.
      intros *.
      unfold comp_real_distribution, comp_simulator_distribution;
      cbn [comp_rand_distribution comp_prove comp_simulate].
      norm_bind; reflexivity.
    Qed.

    (** The simulated distribution at a [COr] node: draw [c₁] and
        simulate both children, the left at [c₁] and the right at
        [c - c₁]. *)
    Lemma comp_sim_or_eq :
      ∀ (rl rr : comp_rel) (lf : list F) (Hlfn : lf <> List.nil) (c : F),
      comp_simulator_distribution lf Hlfn (COr rl rr) c =
      Bind (uniform_with_replacement lf Hlfn) (fun c₁ =>
        Bind (comp_simulator_distribution lf Hlfn rl c₁) (fun tl =>
          Bind (comp_simulator_distribution lf Hlfn rr (c - c₁)) (fun tr =>
            Ret (tl, tr, c₁)))).
    Proof.
      intros *.
      unfold comp_simulator_distribution;
      cbn [comp_rand_distribution comp_simulate].
      norm_bind; reflexivity.
    Qed.

    (** The real distribution at a [CThresh] node, written out:
        draw the [k - t] free scalars, draw the children's
        randomness, then prove or fake each child at the challenge
        obtained by interpolating through the selected nodes, and
        record the polynomial's values at the first [k - t]
        nodes. *)
    Lemma comp_real_thresh_eq :
      ∀ (t k : nat) (xs : Vector.t F k) (rs : Vector.t comp_rel k) Hxs Ht
        (lf : list F) (Hlfn : lf <> List.nil)
        (w : wlist rs) (c : F),
      comp_real_distribution lf Hlfn (CThresh t k xs rs Hxs Ht) w c =
      Bind (repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn) (k - t))
        (fun d =>
          Bind (rand_list lf Hlfn rs) (fun rl =>
            Ret (provelist rs w rl (sim_flags rs w (wcount rs w - t))
                   (chal_of (Vector.to_list xs) (expand_chal c
                     (select_nodes (Vector.to_list xs) (sim_flags rs w (wcount rs w - t)))
                     (Vector.to_list d))) 0,
                 List.map (expand_chal c
                     (select_nodes (Vector.to_list xs) (sim_flags rs w (wcount rs w - t)))
                     (Vector.to_list d)) (List.firstn (k - t) (Vector.to_list xs))))).
    Proof.
      intros *.
      unfold comp_real_distribution;
      cbn [comp_rand_distribution comp_prove].
      norm_bind; reflexivity.
    Qed.

    (** The simulated distribution at a [CThresh] node: draw the
        same randomness, read the free scalars directly as the
        values at the first [k - t] nodes, simulate every child at
        the resulting challenge, and record those scalars
        unchanged.

        Comparing this with [comp_real_thresh_eq] shows exactly
        what the bijection has to do: move the free scalars from
        the selected nodes to the first [k - t] nodes. *)
    Lemma comp_sim_thresh_eq :
      ∀ (t k : nat) (xs : Vector.t F k) (rs : Vector.t comp_rel k) Hxs Ht
        (lf : list F) (Hlfn : lf <> List.nil) (c : F),
      comp_simulator_distribution lf Hlfn (CThresh t k xs rs Hxs Ht) c =
      Bind (repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn) (k - t))
        (fun d =>
          Bind (rand_list lf Hlfn rs) (fun rl =>
            Ret (simlist rs rl
                   (chal_of (Vector.to_list xs) (expand_chal c (List.firstn (k - t) (Vector.to_list xs))
                     (Vector.to_list d))) 0,
                 Vector.to_list d))).
    Proof.
      intros *.
      unfold comp_simulator_distribution;
      cbn [comp_rand_distribution comp_simulate].
      norm_bind; reflexivity.
    Qed.

    (** Attaching one and the same constant [z] to both sides of a
        permutation preserves it.  Used at the threshold node,
        where the recorded challenge values are literally identical
        on both sides once the bijection has been applied, so that
        only the child transcripts still need comparing. *)
    Lemma bind_ret_pair_perm {A B C : Type} :
      ∀ (d : dist A) (f g : A -> B) (z : C),
      Permutation (Bind d (fun x => Ret (f x))) (Bind d (fun x => Ret (g x))) ->
      Permutation (Bind d (fun x => Ret (f x, z))) (Bind d (fun x => Ret (g x, z))).
    Proof.
      intros * ha.
      assert (hb : ∀ h : A -> B,
        Bind d (fun x => Ret (h x, z)) =
        Bind (Bind d (fun x => Ret (h x))) (fun y => Ret (y, z))).
      { intro h. rewrite bind_assoc. eapply bind_ext; intro x.
        rewrite bind_ret_left. reflexivity. }
      rewrite !hb.
      eapply bind_perm_left; exact ha.
    Qed.

    (** Two independent draws combined into a pair can be
        rearranged so that each draw is mapped on its own first.
        Bookkeeping for [bind_prod_perm]. *)
    Lemma bind_split {A B C D : Type} :
      ∀ (d₁ : dist A) (d₂ : dist B) (f : A -> C) (g : B -> D),
      Bind d₁ (fun x => Bind d₂ (fun y => Ret (f x, g y))) =
      Bind (Bind d₁ (fun x => Ret (f x))) (fun u =>
        Bind (Bind d₂ (fun y => Ret (g y))) (fun v => Ret (u, v))).
    Proof.
      intros *.
      norm_bind; reflexivity.
    Qed.

    (** Independent products of permutation-equal distributions are
        permutation-equal.

        If mapping [f] and mapping [f'] over the first draw agree
        up to order, and likewise [g] and [g'] over the second,
        then the distributions of pairs agree up to order.  This is
        how the induction combines the two children of a [CAnd],
        and the children of a threshold node one at a time inside
        [walk_perm]. *)
    Lemma bind_prod_perm {A B C D : Type} :
      ∀ (d₁ : dist A) (d₂ : dist B) (f f' : A -> C) (g g' : B -> D),
      Permutation (Bind d₁ (fun x => Ret (f x))) (Bind d₁ (fun x => Ret (f' x))) ->
      Permutation (Bind d₂ (fun y => Ret (g y))) (Bind d₂ (fun y => Ret (g' y))) ->
      Permutation
        (Bind d₁ (fun x => Bind d₂ (fun y => Ret (f x, g y))))
        (Bind d₁ (fun x => Bind d₂ (fun y => Ret (f' x, g' y)))).
    Proof.
      intros * ha hb.
      rewrite (bind_split d₁ d₂ f g), (bind_split d₁ d₂ f' g').
      eapply bind_perm.
      exact ha.
      intro u.
      eapply bind_perm_left.
      exact hb.
    Qed.

    (** Drawing randomness for a non-empty vector of children
        splits into the first child's draw followed by the draw for
        the rest.  Stated underneath a [Ret], because that is the
        shape the permutation proofs manipulate. *)
    Lemma rand_list_cons_bind {C : Type} :
      ∀ (lf : list F) (Hlfn : lf <> List.nil) (n : nat) (r : comp_rel)
        (v : Vector.t comp_rel n) (P : rlist (r :: v) -> C),
      Bind (rand_list lf Hlfn (r :: v)) (fun rl => Ret (P rl)) =
      Bind (comp_rand_distribution lf Hlfn r) (fun x =>
        Bind (rand_list lf Hlfn v) (fun xs => Ret (P (x, xs)))).
    Proof.
      intros *.
      cbn [rand_list_gen].
      norm_bind; reflexivity.
    Qed.

    (** The walk over the children of a threshold node carries the
        real distribution onto the simulated one.

        The [vall] hypothesis says that for every child the real
        and the simulated distributions are already known to be
        permutations of each other; it is the induction hypothesis
        of [comp_distribution_perm].  [wholds v w] says the
        witnesses present are genuine.

        The conclusion is that proving some children and faking the
        rest, at a fixed challenge function, is distributed exactly
        like faking all of them.  Faked children contribute
        identical terms on both sides, and proven children
        contribute terms the hypothesis equates.

        Note that the flag list [fl] is completely arbitrary here.
        Which children the prover chose to fake makes no difference
        to the distribution, and that is exactly why a threshold
        proof hides which witnesses the prover holds. *)
    Lemma walk_perm :
      ∀ (n : nat) (v : Vector.t comp_rel n) (lf : list F)
        (Hlfn : lf <> List.nil) (w : wlist v) (fl : list bool)
        (chal : nat -> F) (i : nat),
      vall (fun r => ∀ (w : comp_witness r) (c : F),
        comp_rel_holds r w ->
        Permutation (comp_real_distribution lf Hlfn r w c)
                    (comp_simulator_distribution lf Hlfn r c)) v ->
      wholds v w ->
      Permutation
        (Bind (rand_list lf Hlfn v) (fun rl => Ret (provelist v w rl fl chal i)))
        (Bind (rand_list lf Hlfn v) (fun rl => Ret (simlist v rl chal i))).
    Proof.
      induction v as [|r n v ih]; intros lf Hlfn w fl chal i hall hw.
      +
        reflexivity.
      +
        destruct hall as (hr & hall).
        destruct w as (ow & w'); cbn in hw.
        destruct hw as (hw & hw').
        cbn [provelist_gen simlist_gen].
        rewrite !rand_list_cons_bind.
        cbn [fst snd].
        eapply bind_prod_perm.
        ++
          destruct ow as [x0 |]; [destruct fl as [| [|] fl] |];
          try reflexivity.
          eapply (hr x0 (chal i) hw).
        ++
          eapply ih; assumption.
    Qed.

    (** At a leaf, the honest prover and the simulator produce the
        same transcript once the randomness is translated.

        Precisely: the prover run on commitment randomness [us]
        produces the transcript the simulator produces on
        randomness [zip_with (fun u x => u + c * x) us xs].  The
        hypothesis is that [xs] really is a witness.

        The computation is the verification equation itself.  The
        simulator rebuilds the announcement as the matrix applied
        to the response, divided by the public value raised to the
        challenge, and the two occurrences of the public value
        cancel because the witness solves the system.

        Composed with [multidraw_shift_perm], which says the
        translation is a bijection of the randomness, this gives
        zero knowledge at a leaf. *)
    Lemma comp_leaf_prove_simulate :
      ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m)
        (pub : Vector.t G m) (xs us : Vector.t F n) (c : F),
      mat_evalC mat xs = pub ->
      comp_prove (Leaf m n mat pub) xs us c =
      comp_simulate (Leaf m n mat pub)
        (zip_with (fun u x => u + c * x) us xs) c.
    Proof.
      intros * ha; subst pub.
      cbn [comp_prove comp_simulate].
      f_equal.
      eapply eq_nth_iff.
      intros i j hij; subst.
      rewrite nth_zip_with.
      unfold mat_eval.
      rewrite !(nth_map _ _ j j eq_refl).
      rewrite row_eval_response.
      rewrite <-associative, <-smul_distributive_fadd.
      assert (ha : c + opp c = zero). field.
      rewrite ha, field_zero, right_identity.
      reflexivity.
    Qed.

    (** Zero knowledge, strong form: the real and the simulated
        transcript distributions are one and the same distribution.

        The two hypotheses on [lf] say that the challenge space is
        a duplicate-free enumeration of the whole field, which is
        what allows a bijection of the randomness to permute a
        uniform draw.  [comp_rel_holds r w] says the prover really
        holds a witness.

        At each kind of node the proof exhibits a bijection of the
        randomness carrying the prover's output to the simulator's.

        - At a [Leaf] it is the translation of the commitment
          randomness: [comp_leaf_prove_simulate] identifies the two
          outputs, and [multidraw_shift_perm] says the translation
          is a bijection.
        - At a [CAnd] there is nothing to do beyond combining the
          two children.
        - At a [COr] with a left witness it is the reflection
          sending the recorded branch challenge [c₁] to [c - c₁],
          which is its own inverse.  With a right witness the two
          distributions already line up.
        - At a [CThresh] it is [shift_nodes], moving the free
          scalars from the nodes of the faked children to the first
          [k - t] nodes, together with [walk_perm] for the children
          themselves.

        The simulated side never mentions the witness, and that is
        exactly what [comp_witness_indistinguishable] exploits. *)
    Theorem comp_distribution_perm :
      ∀ (r : comp_rel) (lf : list F) (Hlfn : lf <> List.nil)
        (w : comp_witness r) (c : F),
      List.NoDup lf -> (∀ x : F, List.In x lf) ->
      comp_rel_holds r w ->
      Permutation
        (comp_real_distribution lf Hlfn r w c)
        (comp_simulator_distribution lf Hlfn r c).
    Proof.
      induction r as [m n mat pub | rl rr ihl ihr | rl rr ihl ihr
        | t k xs rs Hxs Ht ihrs] using comp_rel_ind'.
      +
        intros * hnd hin ha; cbn in ha.
        unfold comp_real_distribution, comp_simulator_distribution;
        cbn [comp_rand_distribution].
        erewrite bind_ext with
          (f := fun us => Ret (comp_prove (Leaf m n mat pub) w us c))
          (g := fun us => Ret (comp_simulate (Leaf m n mat pub)
            (zip_with (fun u x => u + c * x) us w) c)).
        2: { intro us.
             rewrite (comp_leaf_prove_simulate _ _ _ _ _ _ _ ha).
             reflexivity. }
        eapply multidraw_shift_perm with
          (f := fun zs => Ret (comp_simulate (Leaf m n mat pub) zs c));
        assumption.
      +
        intros * hnd hin ha.
        destruct w as (wl & wr); cbn in ha.
        destruct ha as (hal & har).
        rewrite comp_real_and_eq, comp_sim_and_eq.
        eapply bind_perm.
        eapply ihl; assumption.
        intro tl.
        eapply bind_perm.
        eapply ihr; assumption.
        intro tr; reflexivity.
      +
        intros * hnd hin ha.
        destruct w as [wl | wr]; cbn in ha.
        ++
          rewrite comp_real_or_inl_eq, comp_sim_or_eq.
          erewrite bind_ext with
            (f := fun c₁ =>
              Bind (comp_real_distribution lf Hlfn rl wl (c - c₁)) (fun tl =>
                Bind (comp_simulator_distribution lf Hlfn rr c₁)
                  (fun tr => Ret (tl, tr, c - c₁))))
            (g := fun c₁ =>
              Bind (comp_real_distribution lf Hlfn rl wl (c - c₁)) (fun tl =>
                Bind (comp_simulator_distribution lf Hlfn rr (c - (c - c₁)))
                  (fun tr => Ret (tl, tr, c - c₁)))).
          2: { intro c₁.
               assert (hb : c - (c - c₁) = c₁). field.
               rewrite hb. reflexivity. }
          eapply Permutation_trans.
          eapply uniform_shift_perm with
            (σ := fun c₁ => c - c₁) (τ := fun c₁ => c - c₁)
            (f := fun c₁ =>
              Bind (comp_real_distribution lf Hlfn rl wl c₁) (fun tl =>
                Bind (comp_simulator_distribution lf Hlfn rr (c - c₁))
                  (fun tr => Ret (tl, tr, c₁)))).
          exact hnd. exact hin.
          intro; cbn beta; field. intro; cbn beta; field.
          eapply bind_perm_right; intro c₁.
          eapply bind_perm.
          eapply ihl; assumption.
          intro tl; reflexivity.
        ++
          rewrite comp_real_or_inr_eq, comp_sim_or_eq.
          eapply bind_perm_right; intro c₁.
          eapply bind_perm_right; intro tl.
          eapply bind_perm.
          eapply ihr; assumption.
          intro tr; reflexivity.
      +
        intros * hnd hin ha; cbn in ha.
        destruct ha as (hcount & hholds).
        pose proof (wcount_le k rs w) as hle.
        pose proof (length_to_list F k xs) as Hlen.
        set (xl := Vector.to_list xs) in *.
        set (fl := sim_flags rs w (wcount rs w - t)).
        set (snodes := select_nodes xl fl).
        set (fnodes := List.firstn (k - t) xl).
        assert (hsl : List.length snodes = (k - t)%nat).
        { unfold snodes, fl.
          rewrite select_nodes_length, sim_flags_count.
          rewrite Nat.min_l; lia.
          rewrite sim_flags_length; symmetry; exact Hlen. }
        assert (hfl : List.length fnodes = (k - t)%nat).
        { unfold fnodes; eapply List.firstn_length_le; lia. }
        assert (hsnd : List.NoDup (List.cons zero snodes)).
        { eapply nodup_zero_select; exact Hxs. }
        assert (hfnd : List.NoDup (List.cons zero fnodes)).
        { eapply nodup_zero_firstn; exact Hxs. }
        rewrite comp_real_thresh_eq, comp_sim_thresh_eq.
        fold xl.
        fold fl snodes fnodes.
        (* the real prover's continuation, reindexed by the share
           bijection φ = shift_nodes c _ snodes fnodes *)
        erewrite bind_ext with
          (g := fun d =>
            Bind (rand_list lf Hlfn rs) (fun rl =>
              Ret (provelist rs w rl fl
                     (chal_of xl (expand_chal c snodes
                       (Vector.to_list (shift_nodes c (k - t) fnodes snodes hsl
                         (shift_nodes c (k - t) snodes fnodes hfl d))))) 0,
                   Vector.to_list (shift_nodes c (k - t) snodes fnodes hfl d)))).
        2: { intro d.
             rewrite shift_nodes_inv; try assumption.
             rewrite to_list_shift_nodes.
             reflexivity. }
        eapply Permutation_trans.
        eapply multidraw_bij_perm with
          (φ := shift_nodes c (k - t) snodes fnodes hfl)
          (ψ := shift_nodes c (k - t) fnodes snodes hsl)
          (g := fun e =>
            Bind (rand_list lf Hlfn rs) (fun rl =>
              Ret (provelist rs w rl fl
                     (chal_of xl (expand_chal c snodes
                       (Vector.to_list (shift_nodes c (k - t) fnodes snodes hsl e)))) 0,
                   Vector.to_list e))).
        exact hnd. exact hin.
        intro; eapply shift_nodes_inv; assumption.
        intro; eapply shift_nodes_inv; assumption.
        eapply bind_perm_right; intro e.
        (* the reindexed real challenge is the simulator's challenge *)
        assert (hchal :
          chal_of xl (expand_chal c snodes
            (Vector.to_list (shift_nodes c (k - t) fnodes snodes hsl e))) =
          chal_of xl (expand_chal c fnodes (Vector.to_list e))).
        { extensionality j; unfold chal_of.
          rewrite to_list_shift_nodes.
          eapply expand_agree; try assumption.
          rewrite length_to_list; exact hfl.
          congruence. }
        rewrite hchal.
        eapply bind_ret_pair_perm.
        eapply walk_perm; [| exact hholds].
        eapply vall_mono; [exact ihrs |].
        intros r0 hr0 w0 c0 hw0.
        eapply hr0; assumption.
    Qed.

    (** Witness indistinguishability.

        Two provers holding different witnesses [w₁] and [w₂] for
        the same statement produce exactly the same transcript
        distribution.

        For a [COr] this says the verifier cannot tell which branch
        the prover is actually able to do.  For a [CThresh] it says
        the verifier cannot tell which qualified subset of children
        the prover used.  That is the property these compositions
        exist for.

        The proof is immediate from [comp_distribution_perm]: both
        real distributions are permutations of the one simulated
        distribution, which mentions no witness at all, so they are
        permutations of each other. *)
    Theorem comp_witness_indistinguishable :
      ∀ (r : comp_rel) (lf : list F) (Hlfn : lf <> List.nil)
        (w₁ w₂ : comp_witness r) (c : F),
      List.NoDup lf -> (∀ x : F, List.In x lf) ->
      comp_rel_holds r w₁ -> comp_rel_holds r w₂ ->
      Permutation
        (comp_real_distribution lf Hlfn r w₁ c)
        (comp_real_distribution lf Hlfn r w₂ c).
    Proof.
      intros * hnd hin ha hb.
      eapply Permutation_trans.
      eapply comp_distribution_perm; assumption.
      eapply Permutation_sym.
      eapply comp_distribution_perm; assumption.
    Qed.

  End Proofs.
End Composition.
