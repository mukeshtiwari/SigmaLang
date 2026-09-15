From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef BinPos List.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import Util.
From Compiler Require Import LinearRelation LeafValidity Degeneracy
  Determined Invisible.

Import VectorNotations.

(** * What a proof of a linear statement establishes, exactly

    The other modules answer a yes-or-no question: does this statement
    determine its witness? This one answers the question underneath
    it. Whatever the statement does or does not determine, what
    precisely has a verifier been convinced of when a proof goes
    through?

    The answer is a coset, and it is pinned from both sides by results
    already in this development.

    From below, by extraction. Special soundness yields a witness, and
    [Degeneracy.witness_difference_in_kernel] says any two witnesses
    for the same public data differ by a kernel vector. So a verifier
    that is convinced at all is convinced the prover knows some member
    of one coset of the kernel.

    From above, by [Invisible.degeneracy_is_invisible]. Members of that
    coset produce identical transcripts under a bijection of the
    randomness, so no verifier is ever convinced of more than the
    coset: which member the prover holds is not a question any run can
    answer.

    The two bounds meet. A proof of a linear statement establishes
    knowledge of the coset, no less and no more, and the kernel is the
    whole of what it leaves open.

    That is why the incidence system of [Degeneracy.v] is more than a
    decision procedure. It is a computable description of this coset:
    sound always, and by [IncidenceComplete.v] the largest description
    any checker reading the statement can produce. A verdict of
    "determined" is the statement that the coset is a point. *)

Section Exact.

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

  #[local] Notation mat_evalC := (@mat_eval F G gid gop gpow).
  #[local] Notation waddC := (@wadd F add).
  #[local] Notation wsubC := (@wsub F sub).
  #[local] Notation wscaleC := (@wscale F mul).
  #[local] Notation in_kernelC := (@in_kernel F G gid gop gpow).
  #[local] Notation incidenceC := (@incidence_zero F zero add G gid Gdec).
  #[local] Notation transcriptC :=
    (@construct_linear_relation_real_proof F add mul G gid gop gpow).

  (** ** The guarantee, from both sides at once

      Take any two witnesses for the same public data. The first two
      conjuncts say the second is the first shifted by a kernel vector,
      which is what extraction can reach. The third says that shift is
      undetectable: for every run of the protocol by the one prover
      there is a run by the other that is the same run. *)
  Theorem knowledge_is_exactly_the_coset :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m)
      (x y : Vector.t F n) (c : F),
    mat_evalC mat x = pub -> mat_evalC mat y = pub ->
    in_kernelC mat (wsubC y x) /\
    waddC x (wsubC y x) = y /\
    (∀ us : Vector.t F n,
       transcriptC mat y (waddC us (wscaleC (opp c) (wsubC y x))) c =
       transcriptC mat x us c).
  Proof.
    intros m n mat pub x y c hx hy.
    pose proof (witness_difference_in_kernel m n mat pub x y hx hy) as hker.
    pose proof (witness_shifted_by_difference n x y) as hshift.
    repeat split; [exact hker | exact hshift |].
    intros us; rewrite <- hshift at 1.
    apply degeneracy_is_invisible; exact hker.
  Qed.

  (** ** What is established, and what is left open

      A linear functional of the witness is \emph{established} when
      every vector the statement leaves free vanishes on it: its value
      is then the same at every witness the statement admits, so a
      proof pins it down. The definition is over the incidence system
      rather than the kernel, because that is the part a checker can
      compute, and [IncidenceComplete.v] is the theorem that this is as
      much as any checker can compute. *)
  Definition established {m n : nat}
    (mat : Vector.t (Vector.t G n) m) (f : Vector.t F n) : Prop :=
    ∀ v : Vector.t F n, incidenceC mat v -> @dot F zero add mul n f v = zero.

  (** Determination is the special case where the functionals reading
      off single positions are established. So the yes-or-no verdict of
      the earlier modules is one question about this specification, and
      not a different subject. *)
  Lemma determined_iff_coordinates_established :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m),
    (∀ v : Vector.t F n, incidenceC mat v -> v = @wzero F zero n) <->
    (∀ j : Fin.t n, established mat (@wpoint F zero n j one)).
  Proof.
    intros m n mat; split.
    - intros hdet j v hv.
      rewrite (dot_wpoint n j v).
      rewrite (hdet v hv); unfold wzero; rewrite Vector.const_nth.
      reflexivity.
    - intros hcoord v hv.
      apply Vector.eq_nth_iff; intros p q hpq; subst q.
      pose proof (hcoord p v hv) as h.
      rewrite (dot_wpoint n p v) in h.
      rewrite h; unfold wzero; rewrite Vector.const_nth; reflexivity.
  Qed.

End Exact.
