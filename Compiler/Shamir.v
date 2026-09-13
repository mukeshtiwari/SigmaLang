From Stdlib Require Import Setoid
  setoid_ring.Field Lia List Utf8
  Psatz Bool Arith.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Compiler Require Import Lagrange.
Import ListNotations.

(** * Shamir: the counting argument behind threshold soundness

    This file proves the one arithmetic fact that makes a
    "at least [thr] out of [n]" proof sound.

    ** The setting, in words

    A threshold node of the composed protocol works like Shamir
    secret sharing.  The verifier sends one challenge [c].  The
    prover spreads that single challenge over the [n] children by
    picking a polynomial that passes through the point [(zero, c)],
    and handing child number [i] the value of that polynomial at a
    fixed public point [x_i] (the "node" of child [i]).  The nodes
    are chosen once, are public, and are pairwise different.

    The prover is allowed to choose the polynomial freely except for
    one constraint: its degree is capped.  A polynomial of degree at
    most [d] is pinned down by [d + 1] points, so capping the degree
    caps how many child challenges the prover can pick by hand.  In
    the threshold protocol the cap is [n - thr], which leaves the
    prover exactly [n - thr] free child challenges.  Those are the
    children it fakes; for the remaining [thr] children it must do
    real work, which means it must know [thr] witnesses.

    ** What is proven here

    Soundness of a sigma protocol is proven by rewinding: you take
    two accepting runs that start with the same first message but
    use two different challenges, and you extract a witness from the
    pair.  For a threshold node the two runs give two root
    challenges [c] and [c'] with [c <> c'], and two lists of child
    challenges [cs] and [cs'].

    [threshold_extraction] says: if [c <> c'], then [cs] and [cs']
    differ in at least [thr] positions.  Each differing position is
    a child that received two different challenges under the same
    first message, which is exactly what the child's own extractor
    needs.  So [thr] children yield [thr] witnesses, and the
    threshold relation really holds.

    ** Why it is true

    Suppose the two lists agreed in more than [n - thr] positions.
    Both interpolants have degree at most [n - thr], and they would
    agree on more than [n - thr] different nodes.  Two polynomials
    of degree at most [d] that agree on more than [d] points are the
    same polynomial ([lag_interp_unique] in Lagrange.v).  Being the
    same polynomial, they also agree at the point [zero], where they
    evaluate to [c] and [c'].  That contradicts [c <> c'].  So the
    agreement set has at most [n - thr] positions, and the remaining
    ones, at least [thr] of them, are disagreements. *)
Section Threshold.

  (** ** Parameters

      The whole file is parametric in an arbitrary field [F], given
      as its carrier plus its operations.  Nothing below depends on
      a particular choice of field, so the result applies to any
      prime field a real deployment might use.

      - [zero], [one] are the two constants;
      - [add], [mul], [sub], [div] the four binary operations;
      - [opp] is negation and [inv] is the multiplicative inverse;
      - [Fdec] decides whether two field elements are equal, which
        is what lets us write the boolean test [agreeb] below;
      - [Hfield] is the proof that all of this really forms a
        field. *)
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hfield : @field F (@eq F) zero one opp add sub mul inv div}.

  (** Register the field with the [field] tactic so that routine
      algebraic identities can be discharged automatically. *)
  Add Field field : (@field_theory_for_stdlib_tactic F
    eq zero one opp add mul sub inv div Hfield).

  (** Shorthand for the interpolation function of Lagrange.v,
      already applied to this section's field operations. *)
  #[local] Notation lag_interpF :=
    (@lag_interp F zero one add mul sub inv).

  (** Shorthand for the uniqueness theorem of Lagrange.v: two
      interpolants with few enough points that agree on enough
      distinct nodes are the same function. *)
  #[local] Notation lag_interp_uniqueF :=
    (@lag_interp_unique F zero one add mul sub div opp inv Fdec Hfield).

  (** ** Comparing two challenge lists

      [agreeb cs cs' i] answers the question "did child number [i]
      receive the same challenge in both runs?".

      It reads position [i] out of each list and compares the two
      field elements with the decidable equality [Fdec], turning the
      answer into a plain boolean so that it can be used with
      [List.filter].

      Reading past the end of a list yields the default value
      [zero].  That never happens where the function is used, because
      the indices always come from [seq 0 n] and both lists have
      length [n]. *)
  Definition agreeb (cs cs' : list F) (i : nat) : bool :=
    match Fdec (nth i cs zero) (nth i cs' zero) with
    | left _ => true
    | right _ => false
    end.

  (** ** Helper facts about lists

      These three lemmas are ordinary list bookkeeping.  They are
      stated separately because each is a self-contained fact that
      is easier to read on its own than inlined in the main proof. *)

  (** Splitting a list by a test loses nothing.

      Filtering with a test [p] and filtering with its negation
      produce two lists whose lengths add up to the length of the
      original.  Every element goes to exactly one side.

      In the main proof this is what turns "the agreement set is
      small" into "the disagreement set is large". *)
  Lemma filter_partition_length :
    ∀ (A : Type) (p : A -> bool) (l : list A),
    (length (filter p l) +
     length (filter (fun x => negb (p x)) l))%nat = length l.
  Proof.
    intros A p.
    induction l as [|a l ih]; cbn.
    reflexivity.
    destruct (p a); cbn; lia.
  Qed.

  (** Looking up distinct positions in a duplicate-free list gives
      distinct results.

      Given a list [xs] with no repeated element, and a list [idxs]
      of positions that are themselves all different and all inside
      [xs], reading [xs] at each of those positions produces a list
      with no repeated element either.

      This is used to go from "these child indices agree" to "these
      interpolation nodes are distinct points", which is what the
      uniqueness theorem needs: it counts pairwise different points
      of agreement, so duplicates would not help. *)
  Lemma nth_map_nodup :
    ∀ (xs : list F) (idxs : list nat),
    List.NoDup idxs ->
    (∀ i, List.In i idxs -> (i < length xs)%nat) ->
    List.NoDup xs ->
    List.NoDup (List.map (fun i => nth i xs zero) idxs).
  Proof.
    intros xs.
    induction idxs as [|a idxs ih]; intros hnd hlt hxs; cbn.
    +
      constructor.
    +
      inversion hnd as [| ? ? hnin hnd']; subst.
      constructor.
      ++
        intro hin.
        eapply List.in_map_iff in hin.
        destruct hin as (j & hj & hjin).
        assert (haj : a = j).
        eapply (proj1 (List.NoDup_nth xs zero) hxs).
        eapply hlt; left; reflexivity.
        eapply hlt; right; exact hjin.
        symmetry; exact hj.
        subst; contradiction.
      ++
        eapply ih.
        exact hnd'.
        intros i hi; eapply hlt; right; exact hi.
        exact hxs.
  Qed.

  (** Filtering the list [0, 1, ..., n - 1] keeps only numbers below
      [n].

      Obvious, but needed explicitly: the main proof gets its indices
      by filtering [seq 0 n], and then has to feed them to lemmas
      that demand the index be a legal position in a list of length
      [n]. *)
  Lemma filter_seq_lt :
    ∀ (p : nat -> bool) (n i : nat),
    List.In i (filter p (seq 0 n)) -> (i < n)%nat.
  Proof.
    intros * hi.
    eapply filter_In in hi.
    destruct hi as (hi & _).
    eapply in_seq in hi.
    lia.
  Qed.

  (** ** The main theorem

      Two accepting runs with different root challenges disagree on
      at least [thr] children.

      Reading the hypotheses one by one:

      - [thr <= n]: the threshold cannot ask for more children than
        there are.
      - [List.NoDup xs] and [length xs = n]: the [n] public
        interpolation nodes, one per child, are pairwise different.
        Distinctness is essential; repeated nodes would let the
        prover cheat.
      - [length base <= S (n - thr)] and the same for [base']: each
        run's polynomial is given by at most [n - thr + 1] points,
        which is the degree cap described at the top of the file.
        [base] is the first run's point set and [base'] the second's.
      - [lag_interpF base zero = c] and likewise for [c']: each
        polynomial passes through the root challenge of its own run
        at the point [zero].
      - the two [∀ i] hypotheses: evaluating a run's polynomial at
        the node of child [i] gives exactly the challenge that child
        [i] received in that run.  So [cs] and [cs'] are the child
        challenge lists of the two runs.
      - [c <> c']: the two runs used different root challenges,
        which is what rewinding provides.

      The conclusion counts the positions where the two child
      challenge lists differ, and states that there are at least
      [thr] of them. *)
  Theorem threshold_extraction :
    ∀ (n thr : nat) (xs cs cs' : list F)
      (base base' : list (F * F)) (c c' : F),
    (thr <= n)%nat ->
    List.NoDup xs ->
    length xs = n ->
    (length base <= S (n - thr))%nat ->
    (length base' <= S (n - thr))%nat ->
    lag_interpF base zero = c ->
    lag_interpF base' zero = c' ->
    (∀ i, (i < n)%nat -> lag_interpF base (nth i xs zero) = nth i cs zero) ->
    (∀ i, (i < n)%nat -> lag_interpF base' (nth i xs zero) = nth i cs' zero) ->
    c <> c' ->
    (thr <=
      length (filter (fun i => negb (agreeb cs cs' i)) (seq 0 n)))%nat.
  Proof.
    intros * hthr hnd hlen hb hb' h0 h0' hcs hcs' hne.
    (* [E] is the set of children that got the same challenge twice,
       [D] the set of children that got different challenges. *)
    set (E := filter (agreeb cs cs') (seq 0 n)).
    set (D := filter (fun i => negb (agreeb cs cs' i)) (seq 0 n)).
    (* Every child is in exactly one of the two sets. *)
    pose proof (filter_partition_length _ (agreeb cs cs') (seq 0 n))
      as hpart.
    rewrite seq_length in hpart.
    fold E D in hpart.
    (* The heart of the argument: the agreement set is small. *)
    assert (hEsmall : (length E <= n - thr)%nat).
    {
      destruct (Nat.le_gt_cases (length E) (n - thr)) as [hle | hgt];
      [exact hle |].
      (* Suppose not, and derive a contradiction. *)
      exfalso.
      (* Turn the agreeing child indices into their public nodes. *)
      set (nodes := List.map (fun i => nth i xs zero) E).
      assert (hndE : List.NoDup E).
      eapply NoDup_filter, seq_NoDup.
      (* Distinct indices into a duplicate-free node list give
         distinct nodes, so these really are many different points. *)
      assert (hnodes_nd : List.NoDup nodes).
      eapply nth_map_nodup.
      exact hndE.
      intros i hi; rewrite hlen; eapply filter_seq_lt; exact hi.
      exact hnd.
      assert (hnodes_len : length nodes = length E).
      unfold nodes; rewrite map_length; reflexivity.
      (* At every one of those nodes the two polynomials take the
         same value, because the two runs gave that child the same
         challenge. *)
      assert (hagree : ∀ a, List.In a nodes ->
        lag_interpF base a = lag_interpF base' a).
      {
        intros a ha.
        unfold nodes in ha.
        eapply in_map_iff in ha.
        destruct ha as (i & hia & hiin).
        subst a.
        assert (hilt : (i < n)%nat).
        eapply filter_seq_lt; exact hiin.
        rewrite (hcs i hilt), (hcs' i hilt).
        unfold E in hiin.
        eapply filter_In in hiin.
        destruct hiin as (_ & hag).
        unfold agreeb in hag.
        destruct (Fdec (nth i cs zero) (nth i cs' zero)) as [he | he];
        [exact he | discriminate].
      }
      (* Two low-degree polynomials agreeing on that many distinct
         points are the same function, so they also agree at [zero]
         where they evaluate to [c] and [c']. *)
      pose proof (lag_interp_uniqueF base base' nodes hnodes_nd)
        as huniq.
      assert (hbn : (length base <= length nodes)%nat).
      rewrite hnodes_len; lia.
      assert (hbn' : (length base' <= length nodes)%nat).
      rewrite hnodes_len; lia.
      pose proof (huniq hbn hbn' hagree zero) as hz.
      rewrite h0, h0' in hz.
      (* [c = c'] contradicts the hypothesis. *)
      contradiction.
    }
    (* The agreement set has at most [n - thr] children out of [n],
       so the disagreement set has at least [thr]. *)
    lia.
  Qed.

  (** ** Note on where the threshold protocol itself lives

      This file deliberately contains only the counting argument.
      The protocol that uses it is the [CThresh] constructor of
      Composition.v.

      One observation from the design is worth recording here.  The
      children of a threshold node all share a single transcript
      type.  That works because the transcript type of a [Leaf]
      depends only on its dimensions, the number of equations and
      the number of private variables, and not on its public data.
      So a "t out of n" threshold taken over n instances of one
      protocol shape is homogeneous, and the children can be stored
      in a vector rather than in a heterogeneous list. *)

End Threshold.
