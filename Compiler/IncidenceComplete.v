From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef BinPos List
  Morphisms.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import Util.
From Compiler Require Import LinearRelation LeafValidity Degeneracy.

Import VectorNotations.

(** * Why the incidence system is the end of the search

    Degeneracy.v shows that a solution of the incidence system is a
    kernel vector in every group, so every solution is a real
    degeneracy.  That says the criterion is not too generous.  This
    file says it is not too strict either, and in doing so answers the
    question the two conditions of LeafValidity.v could not: is the
    list finished?

    ** What "finished" has to mean

    It cannot mean that the criterion finds every kernel vector.  A
    kernel vector can hide in the discrete logarithms: if the bases
    happen to satisfy [h = g^2], then [(2, -1)] is in the kernel of
    [[g, h]] and no amount of looking at the matrix will reveal it.
    Finding that needs the discrete logarithm, which is the thing the
    protocol is built on not being findable.

    What "finished" can mean is this.  A leaf is a matrix of group
    elements, and the group is whatever the deployment chose.  A
    criterion is honest only if the degeneracy it reports is a
    degeneracy for every group the matrix could be read in, since it
    has no way to know which one is meant.  The theorem below is that
    the incidence system is exactly the set of vectors that are kernel
    vectors under every reading.

    ** The readings

    The readings used are cheap and concrete.  Fix a base [s] other
    than the neutral element and send [s] to one and every other base
    to zero, inside the additive group of the field itself, which
    [field_as_vector_space] shows really is a vector space over the
    field.  This reading sends the neutral element to the neutral
    element, as any reading must, because [s] is not the neutral
    element.

    Under it the whole relation collapses to one equation per row:
    the exponents sitting under the occurrences of [s] must sum to
    zero.  That is one row of the incidence system, and letting [s]
    range over the bases recovers all of it.

    ** The two consequences

    [incidence_zero_iff_relabellings] is the equivalence.
    [relabelling_refutes] is the direction that matters for a
    checker: given a vector failing one incidence equation, it hands
    back the reading in which that vector is not a kernel vector at
    all.  A checker rejecting the leaf on account of that vector would
    be rejecting a statement which, read that way, determines its
    secret perfectly well.  So no criterion that is sound for every
    reading can be stronger than this one. *)
Section IncidenceComplete.

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
    {Hvec : @vector_space F (@eq F) zero one add mul sub
      div opp inv G (@eq G) gid ginv gop gpow}.

  Add Field field : (@field_theory_for_stdlib_tactic F
    eq zero one opp add mul sub inv div vector_space_field).

  (** ** The field as a vector space over itself

      The reading below lands in the additive group of [F], with
      scalar multiplication being the field product.  Every law is a
      field identity, so the instance is immediate; it is stated
      because without it the reading would not be a reading at all,
      and the completeness theorem would be comparing the incidence
      system against nothing. *)
  Definition fpow (a x : F) : F := mul a x.

  (** Shorthands.  [feval] and [fmat_eval] are the evaluation maps of
      LinearRelation.v read in the field-as-vector-space instance;
      [sum_atC] and [incidence_zeroC] are those of Degeneracy.v at
      this file's field and group. *)
  #[local] Notation sum_atC := (@sum_at F zero add G Gdec).
  #[local] Notation incidence_zeroC := (@incidence_zero F zero add G gid Gdec).
  #[local] Notation feval := (@row_eval F F zero add fpow).
  #[local] Notation fmat_eval := (@mat_eval F F zero add fpow).

  (** The additive group of the field is a commutative group.  Each
      law is a field identity; they are separated out so the instance
      below reads as the four things it is. *)
  Lemma field_add_monoid : @monoid F (@eq F) add zero.
  Proof.
    constructor.
    - red; intros x y z; field.
    - red; intros x; field.
    - red; intros x; field.
    - intros x y hxy u w huw; subst; reflexivity.
    - exact eq_equivalence.
  Qed.

  Lemma field_add_group : @group F (@eq F) add zero opp.
  Proof.
    constructor.
    - exact field_add_monoid.
    - red; intros x; field.
    - red; intros x; field.
    - intros x y hxy; subst; reflexivity.
  Qed.

  Lemma field_add_commutative_group :
    @commutative_group F (@eq F) add zero opp.
  Proof.
    constructor; [exact field_add_group | red; intros x y; field].
  Qed.

  Lemma field_as_vector_space :
    @vector_space F (@eq F) zero one add mul sub div opp inv
      F (@eq F) zero opp add fpow.
  Proof.
    constructor.
    - exact field_add_commutative_group.
    - exact (vector_space_field (vector_space := Hvec)).
    - red; intros v; unfold fpow; field.
    - red; intros v; unfold fpow; field.
    - red; intros r1 r2 v; unfold fpow; field.
    - red; intros r1 r2 v; unfold fpow; field.
    - red; intros r v1 v2; unfold fpow; field.
    - intros x y hxy u w huw; subst; reflexivity.
  Qed.

  (** ** One reading, one base

      [relabel s row] sends the occurrences of [s] to one and
      everything else to zero.  It is a legitimate reading precisely
      because it sends the neutral element to the neutral element,
      which is what [relabel_respects_identity] records. *)
  Definition relabel (s : G) {n : nat} (row : Vector.t G n) : Vector.t F n :=
    Vector.map (fun b => if Gdec b s then one else zero) row.

  Definition relabel_mat (s : G) {m n : nat}
    (mat : Vector.t (Vector.t G n) m) : Vector.t (Vector.t F n) m :=
    Vector.map (relabel s) mat.

  Lemma relabel_respects_identity :
    ∀ s : G, s <> gid -> (if Gdec gid s then one else zero) = zero.
  Proof.
    intros s hs; destruct (Gdec gid s) as [heq | _];
      [exfalso; exact (hs (eq_sym heq)) | reflexivity].
  Qed.

  (** Evaluating a row one entry at a time, inside the field. *)
  Lemma feval_cons :
    ∀ (n : nat) (b a : F) (r : Vector.t F n) (v : Vector.t F n),
    feval (b :: r) (a :: v) =
    add (fpow b a) (feval r v).
  Proof. intros *; unfold row_eval; cbn; reflexivity. Qed.

  (** The heart of the file: under the reading that keeps only [s],
      a row evaluates to its incidence sum at [s].  Everything else
      is bookkeeping around this one line. *)
  Theorem row_eval_relabel :
    ∀ (n : nat) (row : Vector.t G n) (v : Vector.t F n) (s : G),
    feval (relabel s row) v = sum_atC row v s.
  Proof.
    induction n as [| n ih]; intros row v s.
    - rewrite (vector_inv_0 row), (vector_inv_0 v); reflexivity.
    - destruct (vector_inv_S row) as (b & row' & hrow).
      destruct (vector_inv_S v) as (a & v' & hv).
      subst.
      unfold relabel; cbn [Vector.map].
      rewrite feval_cons; fold (relabel s row').
      rewrite ih, sum_at_cons.
      destruct (Gdec b s); unfold fpow; field.
  Qed.

  Corollary mat_eval_relabel_nth :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m)
      (v : Vector.t F n) (s : G) (i : Fin.t m),
    Vector.nth (fmat_eval (relabel_mat s mat) v) i =
    sum_atC (Vector.nth mat i) v s.
  Proof.
    intros m n mat v s i.
    unfold mat_eval, relabel_mat.
    rewrite !(Vector.nth_map _ _ i i eq_refl).
    apply row_eval_relabel.
  Qed.

  (** ** The completeness theorem

      A vector solves the incidence system exactly when it is a kernel
      vector under every one of these readings.  The forward direction
      is soundness of the criterion against this particular family;
      the backward direction is the one that closes the search, since
      it says nothing outside the incidence system is forced. *)
  Theorem incidence_zero_iff_relabellings :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (v : Vector.t F n),
    incidence_zeroC mat v <->
    (∀ s : G, s <> gid ->
       fmat_eval (relabel_mat s mat) v
       = Vector.const zero m).
  Proof.
    intros m n mat v; split.
    - intros hinc s hs.
      apply Vector.eq_nth_iff; intros p q hpq; subst q.
      rewrite mat_eval_relabel_nth, nth_const.
      exact (hinc p s hs).
    - intros hall i s hs.
      rewrite <- mat_eval_relabel_nth.
      rewrite (hall s hs).
      apply nth_const.
  Qed.

  (** The usable form.  A vector that fails one incidence equation is
      not a kernel vector in the reading that isolates the base of
      that equation, so no criterion sound for every reading could
      have rejected the leaf on its account. *)
  Theorem relabelling_refutes :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (v : Vector.t F n)
      (i : Fin.t m) (s : G),
    s <> gid -> sum_atC (Vector.nth mat i) v s <> zero ->
    fmat_eval (relabel_mat s mat) v
    <> Vector.const zero m.
  Proof.
    intros m n mat v i s hs hne hbad.
    apply hne.
    rewrite <- (mat_eval_relabel_nth m n mat v s i), hbad.
    apply nth_const.
  Qed.

End IncidenceComplete.
