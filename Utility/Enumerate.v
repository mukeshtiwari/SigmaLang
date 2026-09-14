From Stdlib Require Import Utf8 List Arith Lia.
Import ListNotations.

(** * Enumerating a search space, with a proof that nothing is missed

    When a search reports that exactly one candidate survives, the
    report is only as good as the space searched.  A list of
    candidates written out by hand carries no guarantee at all: a
    reader has to take on trust that the author did not omit the
    interesting case, and an author who already knows the answer
    cannot easily prove otherwise even to themselves.

    This module replaces the list with a specification and an
    enumerator, and proves the two directions that make the pair
    worth having.  Soundness says the enumerator produces nothing
    outside the specification, so a survivor really is a candidate of
    the kind claimed.  Completeness says it produces everything inside
    it, so a search that finds one survivor has genuinely ruled the
    others out.  A reader then audits a predicate, which is short,
    instead of a list, which is long and unrevealing.

    ** What is being enumerated

    The space is repetition-free sequences of positions.  A
    Fiat-Shamir hash input is built by picking some of the
    announcement elements, in some order, so a candidate rule is
    exactly a list of distinct indices into the announcement.
    Dropping an index models a rule that omits an element, which is
    the shape behind weak Fiat-Shamir; reordering models the ordering
    ambiguities that implementations disagree about.

    Repetitions are excluded deliberately.  Hashing the same element
    twice is not a rule any implementation follows, and admitting it
    would enlarge the space without adding a candidate anyone would
    write. *)
Section Enumerate.

  (** ** The enumerator

      [injections fuel avail] lists every repetition-free sequence
      drawn from [avail].  The fuel bounds the recursion: each step
      removes the chosen element from the pool, and the pool shrinks,
      so [length avail] fuel always suffices.  Carrying fuel
      explicitly is what lets this be a structural fixpoint, since
      [remove] is not syntactically smaller than its argument. *)
  Fixpoint injections (fuel : nat) (avail : list nat) : list (list nat) :=
    match fuel with
    | O => [ [] ]
    | S f =>
        [] :: flat_map
                (fun i => map (fun l => i :: l)
                            (injections f (remove Nat.eq_dec i avail)))
                avail
    end.

  (** Every repetition-free sequence of positions below [n]. *)
  Definition all_selections (n : nat) : list (list nat) :=
    injections n (seq 0 n).

  (** ** Soundness: nothing outside the specification

      Everything the enumerator produces is repetition-free and drawn
      from the pool.  Without this, a surviving candidate might not be
      a candidate of the kind the search claims to be searching. *)
  Lemma injections_sound :
    ∀ (fuel : nat) (avail l : list nat),
    In l (injections fuel avail) -> NoDup l ∧ incl l avail.
  Proof.
    induction fuel as [| f ih]; intros avail l hin.
    - (* no fuel: the empty sequence is the only one produced *)
      destruct hin as [heq | []]; subst l.
      split; [constructor | apply incl_nil_l].
    - cbn in hin. destruct hin as [heq | hin].
      + subst l; split; [constructor | apply incl_nil_l].
      + apply in_flat_map in hin as (i & hi & hin).
        apply in_map_iff in hin as (l' & heq & hin).
        subst l.
        apply ih in hin as (hnd & hincl).
        split.
        * constructor; [| exact hnd].
          (* [i] cannot reappear: the tail was drawn from a pool with
             [i] removed *)
          intro hbad. apply hincl in hbad.
          exact (remove_In Nat.eq_dec avail i hbad).
        * intros x hx. destruct hx as [heq | hx].
          -- subst x; exact hi.
          -- apply hincl, in_remove in hx as (hx & _); exact hx.
  Qed.

  (** ** Completeness: nothing inside it is missed

      Every repetition-free sequence drawn from the pool is produced,
      given enough fuel.  This is the direction that makes a search
      result meaningful: a candidate absent from the enumeration was
      never tested, and its absence from the survivors would say
      nothing. *)
  Lemma injections_complete :
    ∀ (l avail : list nat) (fuel : nat),
    NoDup l -> incl l avail -> length avail <= fuel ->
    In l (injections fuel avail).
  Proof.
    induction l as [| i l' ih]; intros avail fuel hnd hincl hlen.
    - (* the empty sequence is produced at every fuel *)
      destruct fuel; cbn; left; reflexivity.
    - assert (hi : In i avail) by (apply hincl; left; reflexivity).
      destruct fuel as [| f].
      + (* the pool contains [i], so it is non-empty, so the fuel
           cannot be zero *)
        exfalso. destruct avail as [| a avail']; [contradiction |].
        cbn in hlen; lia.
      + cbn. right.
        apply in_flat_map. exists i. split; [exact hi |].
        apply in_map_iff. exists l'. split; [reflexivity |].
        apply ih.
        * inversion hnd; assumption.
        * intros x hx. apply in_in_remove.
          -- intro heq; subst x.
             inversion hnd as [| ? ? hni ?]; exact (hni hx).
          -- apply hincl; right; exact hx.
        * pose proof (remove_length_lt Nat.eq_dec avail i hi); lia.
  Qed.

  (** ** The specification, and the enumerator against it

      [valid_selection n l] is the whole of what a candidate hash rule
      may be.  It is three lines, and it is what a reader has to
      accept in place of a hand-written list. *)
  Definition valid_selection (n : nat) (l : list nat) : Prop :=
    NoDup l ∧ ∀ i, In i l -> i < n.

  Theorem all_selections_sound :
    ∀ (n : nat) (l : list nat),
    In l (all_selections n) -> valid_selection n l.
  Proof.
    intros n l hin.
    apply injections_sound in hin as (hnd & hincl).
    split; [exact hnd |].
    intros i hi. apply hincl, in_seq in hi. lia.
  Qed.

  Theorem all_selections_complete :
    ∀ (n : nat) (l : list nat),
    valid_selection n l -> In l (all_selections n).
  Proof.
    intros n l (hnd & hlt).
    apply injections_complete.
    - exact hnd.
    - intros i hi. apply in_seq. split; [lia | cbn; apply hlt; exact hi].
    - rewrite length_seq; reflexivity.
  Qed.

  (** Membership in the enumeration is exactly the specification.
      Stated as an iff because that is the form a reader should check:
      neither direction alone justifies a search result. *)
  Corollary all_selections_spec :
    ∀ (n : nat) (l : list nat),
    In l (all_selections n) <-> valid_selection n l.
  Proof.
    intros n l; split;
      [apply all_selections_sound | apply all_selections_complete].
  Qed.

  (** ** Applying a selection

      A selection is turned into a rule by reading the chosen
      positions out of a list.  [d] is returned for an index out of
      range, which [all_selections_sound] guarantees never happens for
      an enumerated selection applied to a list of the right length. *)
  Definition apply_selection {A : Type} (d : A) (idxs : list nat)
    (l : list A) : list A :=
    map (fun i => nth i l d) idxs.

  (** Selecting every position in order is the identity, so the rule
      that hashes the whole announcement is in the space. *)
  Lemma apply_selection_id :
    ∀ (A : Type) (d : A) (l : list A),
    apply_selection d (seq 0 (length l)) l = l.
  Proof.
    intros A d l.
    unfold apply_selection.
    apply (nth_ext _ _ d d).
    - rewrite length_map, length_seq; reflexivity.
    - intros k hk. rewrite length_map, length_seq in hk.
      rewrite (nth_indep (map (fun i => nth i l d) (seq 0 (length l))) d
                 ((fun i : nat => nth i l d) 0)).
      + rewrite (map_nth (fun i : nat => nth i l d) (seq 0 (length l)) 0 k).
        rewrite seq_nth by exact hk. cbn. reflexivity.
      + rewrite length_map, length_seq; exact hk.
  Qed.

  (** How large the space is, for reporting. *)
  Definition selection_count (n : nat) : nat := length (all_selections n).

End Enumerate.
