From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef BinPos List.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import Util.
From Compiler Require Import LinearRelation LeafValidity Degeneracy Determined.

Import VectorNotations.

(** * Why the statement has to be checked, and not the protocol

    Everything else in this development checks a statement before any
    proof is made.  A reader is entitled to ask why: if a relation
    fails to determine its witness, why not catch it by watching the
    protocol run?

    Because there is nothing to watch.  This module proves that a
    prover holding the witness [x] and a prover holding [x + v], for
    [v] any kernel vector, produce not merely indistinguishable
    transcripts but *identical* ones, under a relabelling of the
    randomness that is a bijection.  No verifier -- however much
    computation it has, however many runs it sees, however it picks
    its challenges -- can tell the two apart, because there is no
    observation that differs.

    So the degeneracy of a statement is invisible from its proofs by
    construction, and a static check of the statement is not the
    convenient way to find it but the only way.

    The pleasing part is which object does the work.  A kernel vector
    is what [Degeneracy.v] emits as the certificate that a relation is
    degenerate: it is the *evidence of the defect*.  Here the same
    vector is the thing that hides the defect from every verifier.
    One object, both roles. *)

Section Invisible.

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

  #[local] Notation row_evalC := (@row_eval F G gid gop gpow).
  #[local] Notation mat_evalC := (@mat_eval F G gid gop gpow).
  #[local] Notation waddC := (@wadd F add).
  #[local] Notation wscaleC := (@wscale F mul).
  #[local] Notation in_kernelC := (@in_kernel F G gid gop gpow).
  #[local] Notation transcriptC :=
    (@construct_linear_relation_real_proof F add mul G gid gop gpow).
  #[local] Infix "^" := gpow.

  (** ** Scaling a witness scales what it evaluates to *)

  Lemma row_eval_scale :
    ∀ (n : nat) (row : Vector.t G n) (c : F) (v : Vector.t F n),
    row_evalC row (wscaleC c v) = (row_evalC row v) ^ c.
  Proof.
    induction n as [| n ih]; intros row c v.
    - rewrite (vector_inv_0 row), (vector_inv_0 v).
      unfold wscale, row_eval; cbn; symmetry; apply vid_identity.
    - destruct (vector_inv_S row) as (g & row' & hrow).
      destruct (vector_inv_S v) as (a & v' & hv); subst.
      unfold wscale in ih |- *; cbn [Vector.map].
      rewrite !row_eval_cons, ih, smul_distributive_vadd, smul_pow_up.
      assert (hc : mul a c = mul c a) by field.
      rewrite hc; reflexivity.
  Qed.

  (** So the kernel is closed under scaling, which is the only
      algebraic fact the theorem below needs. *)
  Lemma kernel_scale :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (c : F)
      (v : Vector.t F n),
    in_kernelC mat v -> in_kernelC mat (wscaleC c v).
  Proof.
    intros m n mat c v hker; unfold in_kernel in hker |- *.
    apply Vector.eq_nth_iff; intros p q hpq; subst q.
    unfold mat_eval.
    rewrite (Vector.nth_map _ _ p p eq_refl), row_eval_scale.
    assert (hp : row_evalC (Vector.nth mat p) v = gid).
    { replace (row_evalC (Vector.nth mat p) v)
        with (Vector.nth (mat_evalC mat v) p)
        by (unfold mat_eval; rewrite (Vector.nth_map _ _ p p eq_refl);
            reflexivity).
      rewrite hker, Vector.const_nth; reflexivity. }
    rewrite hp, Vector.const_nth.
    apply vid_identity.
  Qed.

  Lemma announcement_unchanged :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m)
      (us v : Vector.t F n) (c : F),
    in_kernelC mat v ->
    mat_evalC mat (waddC us (wscaleC (opp c) v)) = mat_evalC mat us.
  Proof.
    intros m n mat us v c hker.
    (* The scaled shift is in the kernel, but reading that fact off one
       entry at a time is what keeps the proof free of functional
       extensionality: rewriting a whole vector equation under
       [zip_with] pulls the axiom in. *)
    pose proof (kernel_scale m n mat (opp c) v hker) as hk.
    rewrite mat_eval_add.
    apply Vector.eq_nth_iff; intros p q hpq; subst q.
    apply (f_equal (fun w => Vector.nth w p)) in hk.
    rewrite Vector.const_nth in hk.
    rewrite nth_zip_with, hk; apply right_identity.
  Qed.

  (** ** Two witnesses, one transcript

      Shifting the witness by a kernel vector and the randomness by
      [-c] times the same vector leaves the run *identical*.  The
      announcement survives because the shift is in the kernel; the
      response survives because the two shifts cancel. *)
  Theorem degeneracy_is_invisible :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m)
      (xs us v : Vector.t F n) (c : F),
    in_kernelC mat v ->
    transcriptC mat (waddC xs v) (waddC us (wscaleC (opp c) v)) c =
    transcriptC mat xs us c.
  Proof.
    intros m n mat xs us v c hker.
    pose proof (announcement_unchanged m n mat us v c hker) as ha.
    (* the response survives because the two shifts cancel *)
    assert (hr : zip_with (fun u x => add u (mul c x))
                   (waddC us (wscaleC (opp c) v)) (waddC xs v) =
                 zip_with (fun u x => add u (mul c x)) us xs).
    { clear ha hker mat m; induction n as [| n ih].
      - rewrite (vector_inv_0 xs), (vector_inv_0 us), (vector_inv_0 v).
        reflexivity.
      - destruct (vector_inv_S xs) as (a & xs' & hx).
        destruct (vector_inv_S us) as (u & us' & hu).
        destruct (vector_inv_S v) as (b & v' & hv); subst.
        unfold wadd, wscale in ih |- *; cbn [Vector.map].
        rewrite !zip_with_cons, ih; f_equal; field. }
    (* rewriting the two components, rather than splitting the triple
       with [f_equal], is what keeps this free of functional
       extensionality *)
    unfold construct_linear_relation_real_proof; rewrite ha, hr; reflexivity.
  Qed.

  (** The relabelling of the randomness is a bijection, so the two
      witnesses do not merely produce matching transcripts one at a
      time: they induce the very same distribution of them, whatever
      the distribution on randomness was. *)
  Lemma randomness_shift_cancels :
    ∀ (n : nat) (us v : Vector.t F n) (c : F),
    waddC (waddC us (wscaleC (opp c) v)) (wscaleC c v) = us.
  Proof.
    induction n as [| n ih]; intros us v c.
    - rewrite (vector_inv_0 us), (vector_inv_0 v); reflexivity.
    - destruct (vector_inv_S us) as (u & us' & hu).
      destruct (vector_inv_S v) as (b & v' & hv); subst.
      unfold wadd, wscale in ih |- *; cbn [Vector.map].
      rewrite !zip_with_cons, ih; f_equal; field.
  Qed.

  (** ** What it means for the checker

      Put together: when a relation fails to determine its witness,
      the two witnesses it confuses are two the verifier confuses as
      well.  There is no run to inspect, no statistic to gather and no
      number of proofs that would separate them.  A checker that hopes
      to find degeneracy by watching the protocol is looking for a
      difference that this theorem says is not there, which is why the
      criterion of [Degeneracy.v] is applied to the statement instead. *)
  Corollary degenerate_witnesses_are_indistinguishable :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m)
      (xs v : Vector.t F n) (c : F),
    in_kernelC mat v -> v <> @wzero F zero n ->
    mat_evalC mat xs = pub ->
    (* a second, different witness for the same public data ... *)
    waddC xs v <> xs /\
    mat_evalC mat (waddC xs v) = pub /\
    (* ... whose proofs a verifier cannot tell from the first's *)
    (∀ us : Vector.t F n,
       transcriptC mat (waddC xs v) (waddC us (wscaleC (opp c) v)) c =
       transcriptC mat xs us c).
  Proof.
    intros m n mat pub xs v c hker hnz hx; repeat split.
    - intro hbad; apply hnz, (wadd_cancel n xs v hbad).
    - apply kernel_shifts_witness; assumption.
    - intros us; apply degeneracy_is_invisible; exact hker.
  Qed.

  (** ** The same, for the non-interactive protocol

      Fiat--Shamir derives the challenge from the prover's own
      announcement, and at first sight that should break the argument
      above. The shift applied to the randomness depends on the
      challenge; the challenge depends on the announcement; the
      announcement depends on the randomness. The construction appears
      to chase its own tail.

      It does not, and the reason is the kernel once more. Shifting
      the randomness by any multiple of a kernel vector leaves the
      announcement exactly where it was, so the hash is handed the
      same input and returns the same challenge whichever prover is
      running. The circle closes instead of spinning.

      Both parts of a correctly bound hash agree, for two different
      reasons. The announcement agrees because the kernel preserves
      it. The instance agrees because the two provers are proving the
      same statement about the same public data, which is what it
      means for a statement to fail to determine its witness. So the
      argument does not depend on the hash omitting the instance: it
      works for the strongly bound transform, which is the one a
      deployment must use. *)
  Theorem fiat_shamir_is_invisible :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m)
      (hash : Vector.t G m -> F) (xs us v : Vector.t F n),
    in_kernelC mat v ->
    let c := hash (mat_evalC mat us) in
    (* the challenge the second prover derives is the first's ... *)
    hash (mat_evalC mat (waddC us (wscaleC (opp c) v))) = c /\
    (* ... and at it the two runs are the same run *)
    transcriptC mat (waddC xs v) (waddC us (wscaleC (opp c) v)) c =
    transcriptC mat xs us c.
  Proof.
    intros m n mat hash xs us v hker c; split.
    - unfold c; rewrite (announcement_unchanged m n mat us v _ hker).
      reflexivity.
    - apply degeneracy_is_invisible; exact hker.
  Qed.

End Invisible.
