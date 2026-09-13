From Stdlib Require Import Utf8 List Lia String Ascii.

Import ListNotations.

(** * VarType: variables that can be compared and extended

    ** Why fresh names are needed

    Almost every pass of the compiler introduces new variables.  The
    repair pass of Dsl.v adds names when it has to rewrite a
    statement; the linearisation pass adds one name per intermediate
    product; the not-equals gadget of DslNeq.v adds two names, one
    for the claimed inverse and one for the blinding correction.  In
    every case the new name must not collide with a name the user
    already wrote.  If it did, the pass would silently tie together
    two quantities that have nothing to do with each other, and the
    resulting protocol would prove the wrong thing.

    So each pass needs a supply of fresh names, and needs a proof
    that they really are fresh.

    ** Why a type class

    The obligation was previously handled twice over, and badly.
    One pass pushed it onto its caller, by taking a name generator
    as an argument and demanding a proof that the generator is
    injective.  Another marked every generated name with a special
    leading character and then ran a boolean check afterwards to
    confirm that nothing collided.  Both are sound, and neither
    scales: every new pass pays the same cost again.

    A type class fixes this.  A type class in Rocq is a bundle of
    operations together with the proofs they must satisfy, attached
    to a type; writing an instance discharges the obligations once,
    and from then on any function may simply ask for a type in the
    class and use the operations without further argument.  Here the
    obligation is discharged once per variable type instead of once
    per use site.

    ** The two instances

    Two instances are supplied, so that examples keep readable
    string names while passes that need real freshness can be
    written against any instance at all.

    The two freshness proofs are different in character and both are
    short.  For numbers the fresh name is chosen larger than every
    name in use, and no number in a list can exceed the largest
    element of that list.  For strings the fresh name is chosen
    longer than every name in use, and no string in a list can be
    longer than the longest one in it.  In both cases the new name
    differs from every old one because it differs in a measurable
    quantity: its size, or its length. *)

(** The class itself.

    A type [V] is a [VarType] when it offers three things:

    - [vdec] decides whether two names are equal.  This is what
      lets environments be updated at a single name, and what lets
      a pass test whether a variable it sees is one it introduced.
    - [vfresh] takes the list of names already in use and returns
      one name.
    - [vfresh_not_in] is the proof that the returned name does not
      occur in that list.  It is part of the class, so it is
      discharged once inside each instance and is then available
      everywhere for free. *)
Class VarType (V : Type) := {
  vdec : ∀ x y : V, {x = y} + {x <> y};
  vfresh : list V -> V;
  vfresh_not_in : ∀ l : list V, ~ List.In (vfresh l) l
}.

(** ** The arithmetic fact both instances need *)

(** Every element of a list of numbers is at most the largest
    element of that list.

    This is the single arithmetic fact behind both instances.  For
    numbers it is used directly: the fresh name is one more than the
    largest name in use, so it cannot be in the list.  For strings
    it is used on the list of lengths: the fresh string is longer
    than the longest string in use, so it cannot be in the list
    either.

    It is true because [List.list_max] is by construction an upper
    bound of the list, which the standard lemma [List.list_max_le]
    expresses in the form of a [Forall]. *)
Lemma in_le_list_max :
  ∀ (l : list nat) (x : nat), List.In x l -> (x <= List.list_max l)%nat.
Proof.
  intros l x hx.
  assert (h : (List.list_max l <= List.list_max l)%nat) by lia.
  eapply List.list_max_le in h.
  rewrite List.Forall_forall in h; eapply h; exact hx.
Qed.

(** ** Numbers: the fresh name is bigger *)

(** Natural numbers as variable names.

    Equality of numbers is decidable, and the fresh name for a list
    is one more than the largest number in the list.  That name
    cannot already be in the list: if it were, it would be at most
    the largest element, by [in_le_list_max], and a number cannot be
    at most one less than itself.

    This is the instance that passes should use internally, where
    names only have to be distinct and never have to be read. *)
#[export] Instance VarTypeNat : VarType nat.
Proof.
  refine {| vdec := PeanoNat.Nat.eq_dec;
            vfresh := fun l => S (List.list_max l) |}.
  intros l h.
  pose proof (in_le_list_max l (S (List.list_max l)) h); lia.
Defined.

(** ** Strings: the fresh name is longer *)

(** [ticks n] is the string made of [n] copies of the prime
    character, the single closing quote mark used to decorate a
    name.  So [ticks] applied to zero is the empty string, and each
    step prepends one more prime.

    It exists only as a way to manufacture a string of any
    prescribed length out of nothing.  The particular character does
    not matter; what matters is that the length is controlled
    exactly, which is what [ticks_length] records. *)
Fixpoint ticks (n : nat) : string :=
  match n with
  | 0%nat => EmptyString
  | S m => String "'"%char (ticks m)
  end.

(** [ticks n] has length exactly [n].

    An immediate induction: the empty string has length zero, and
    prepending one character to a string of length [n] gives one of
    length [n] plus one.  It is stated separately because it is the
    only property of [ticks] that the string instance uses. *)
Lemma ticks_length : ∀ n : nat, String.length (ticks n) = n.
Proof.
  induction n as [| n ih]; cbn [ticks String.length]; [reflexivity |].
  rewrite ih; reflexivity.
Qed.

(** Strings as variable names.

    Equality of strings is decidable, and the fresh name for a list
    is a run of prime characters one longer than the longest string
    in the list.

    The freshness proof measures instead of comparing.  Suppose the
    new string did occur in the list.  Then its length would occur
    in the list of lengths, so by [in_le_list_max] that length would
    be at most the largest length in use.  But [ticks_length] says
    the new string is exactly one longer than that maximum, which is
    a contradiction.

    This instance is what keeps examples readable: a user writes
    names like the string for a public key or a bid, and the passes
    can still manufacture names that are guaranteed not to clash
    with them. *)
#[export] Instance VarTypeString : VarType string.
Proof.
  refine {| vdec := String.string_dec;
            vfresh := fun l =>
              ticks (S (List.list_max (List.map String.length l))) |}.
  intros l h.
  set (m := List.list_max (List.map String.length l)) in *.
  assert (hin : List.In (String.length (ticks (S m)))
                  (List.map String.length l))
    by (eapply (List.in_map String.length l _ h)).
  rewrite ticks_length in hin.
  pose proof (in_le_list_max (List.map String.length l) (S m) hin).
  subst m; lia.
Defined.

(** ** What the class buys *)

(** A fresh name differs from any particular name in use.

    [vfresh_not_in] says the fresh name is not a member of the list.
    This restates the same fact in the form the passes actually
    want: pick any name [x] that occurs in the list, and the fresh
    name is different from it.  Rewriting a term is done one
    variable at a time, so a one-at-a-time statement is what fits.

    It holds at every instance, because it is proved from the class
    field alone: if the fresh name equalled [x] it would occur
    wherever [x] does, contradicting [vfresh_not_in].

    This is the lemma the earlier arrangements lacked.  One pass
    assumed an injective generator instead; another marked the names
    it generated with a reserved character and checked afterwards
    that nothing clashed. *)
Lemma vfresh_neq :
  ∀ (V : Type) (H : VarType V) (l : list V) (x : V),
  List.In x l -> vfresh l <> x.
Proof.
  intros V H l x hx he; eapply (vfresh_not_in l).
  rewrite he; exact hx.
Qed.

(** Generating twice in a row gives two different names.

    A pass that needs two fresh names cannot call [vfresh] twice on
    the same list: it would get the same name twice.  The right move
    is to add the first name to the list of names in use before
    asking for the second.  This lemma confirms that the move works:
    the name generated from the extended list differs from the name
    that was added to it.

    It follows from [vfresh_neq], since the first name is by
    construction a member of the extended list.  It is the base case
    of the pattern that [fresh_list] below generalises to any
    number of names. *)
Lemma vfresh_cons_neq :
  ∀ (V : Type) (H : VarType V) (l : list V),
  vfresh (vfresh l :: l)%list <> vfresh l.
Proof.
  intros V H l.
  eapply vfresh_neq; cbn [List.In]; left; reflexivity.
Qed.

(** ** Several fresh names at once *)

(** [fresh_list l n] produces [n] new names, given the list [l] of
    names already in use.

    A pass rarely wants a single name.  Linearising a long product,
    or lowering several inequalities, calls for a whole batch, and
    the batch must be fresh in two senses at once: no name in it may
    clash with an existing name, and no two names in it may clash
    with each other.

    The definition gets both by generating one name at a time and
    treating the names produced so far as used.  Concretely, it
    first builds the [n] minus one names recursively, then appends
    them to [l] and asks [vfresh] for one more name relative to that
    longer list.  Since the new name avoids everything in the
    concatenation, it avoids both the original names and its own
    siblings.

    The three lemmas that follow state exactly the three properties
    a caller needs: the list has the requested length, none of its
    names were already in use, and its names are pairwise
    different. *)
Fixpoint fresh_list {V : Type} {H : VarType V} (l : list V) (n : nat) : list V :=
  match n with
  | 0%nat => []
  | S m => let r := fresh_list l m in vfresh (l ++ r) :: r
  end.

(** The generated list has the requested length.

    Asking for [n] names really gives [n] names, never fewer.  A
    caller that has [n] holes to fill can therefore match them up
    with the list without a side condition.

    The proof is a direct induction on [n]: the empty request gives
    the empty list, and each step adds exactly one name to the front
    of the list produced by the smaller request. *)
Lemma fresh_list_length :
  ∀ (V : Type) (H : VarType V) (l : list V) (n : nat),
  List.length (fresh_list l n) = n.
Proof.
  intros V H l n; induction n as [| n ih]; cbn [fresh_list List.length];
  [reflexivity | rewrite ih; reflexivity].
Qed.

(** No generated name was already in use.

    If [x] is one of the names produced by [fresh_list l n], then
    [x] does not occur in [l].  This is what guarantees that
    substituting the new names into a statement cannot capture a
    variable the user wrote.

    The proof is by induction on [n].  The head of the list is
    [vfresh] applied to [l] appended with the names generated so
    far; by [vfresh_not_in] it occurs nowhere in that concatenation,
    and in particular nowhere in [l].  Every other element of the
    list is handled by the induction hypothesis. *)
Lemma fresh_list_not_in :
  ∀ (V : Type) (H : VarType V) (l : list V) (n : nat) (x : V),
  List.In x (fresh_list l n) -> ~ List.In x l.
Proof.
  intros V H l n; induction n as [| n ih]; intros x hx;
  cbn [fresh_list List.In] in hx.
  + contradiction.
  + destruct hx as [hx | hx].
    - subst x. intro hl. eapply (vfresh_not_in (l ++ fresh_list l n)).
      eapply List.in_or_app; left; exact hl.
    - eapply ih; exact hx.
Qed.

(** The generated names are pairwise different.

    [List.NoDup] says a list has no repeated element.  Without this,
    a pass could hand the same name to two different intermediate
    quantities and quietly force them to be equal, which is the
    exact failure mode that fresh names are meant to prevent.

    The proof is again by induction on [n], and it is the same
    observation as in the previous lemma read on the other component
    of the concatenation.  The head name avoids everything in [l]
    appended with the tail, so in particular it avoids the tail; the
    tail has no duplicates by the induction hypothesis. *)
Lemma fresh_list_nodup :
  ∀ (V : Type) (H : VarType V) (l : list V) (n : nat),
  List.NoDup (fresh_list l n).
Proof.
  intros V H l n; induction n as [| n ih]; cbn [fresh_list].
  + constructor.
  + constructor; [| exact ih].
    intro hin. eapply (vfresh_not_in (l ++ fresh_list l n)).
    eapply List.in_or_app; right; exact hin.
Qed.
