From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef BinPos List.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import Util.
From Compiler Require Import LinearRelation LeafValidity Degeneracy.

Import VectorNotations.

(** * Deciding the incidence criterion

    Degeneracy.v says which leaves are degenerate and
    IncidenceComplete.v says nothing else is.  Neither runs.  This
    file supplies the two things a compiler needs: a boolean test that
    a proposed degeneracy is real, and a condition under which a leaf
    can be accepted outright.

    ** Why a certificate and not a decision procedure

    Deciding whether the incidence system has a nonzero solution is a
    rank computation over the field, and a verified Gaussian
    elimination is a development in its own right.  It is also
    unnecessary.  The search for a solution can be done by any means
    at all, trusted or not, because a proposed solution is checked in
    linear time by [incidence_zerob] and [wzerob], and the checking is
    what the soundness theorem rests on.  This is the same division
    the rest of this development uses: search where it is cheap and
    unverified, check where it matters.

    ** The two sides

    [reject_certificate_sound] is the rejection side.  Given a vector
    the checker confirms is a nonzero solution, every witness of the
    leaf has a second witness beside it, so the leaf does not
    determine its secret.  No assumption on the group is used.

    [separating_row_determines] is the acceptance side, and is
    deliberately partial.  A row whose bases are pairwise distinct and
    none neutral forces every incidence equation to read [x_j = 0], so
    the system has only the zero solution and the leaf is structurally
    sound.  Most statements written in practice have such a row.  When
    none does, [pinned_column_vanishes] extends the reach one column
    at a time, and beyond that the honest answer is that the rank
    computation has not been verified. *)
Section IncidenceDecide.

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
  #[local] Notation sum_atC := (@sum_at F zero add G Gdec).
  #[local] Notation incidence_zeroC := (@incidence_zero F zero add G gid Gdec).
  #[local] Notation wzeroC := (@wzero F zero).

  (** ** Reading a vector predicate off its list form

      [forallb] over [Vector.to_list] is the convenient way to write
      these tests, and this is the bridge to the [Fin.t]-indexed
      statements the theorems are phrased in. *)
  Lemma forallb_to_list_nth :
    ∀ (A : Type) (p : A -> bool) (k : nat) (w : Vector.t A k),
    List.forallb p (Vector.to_list w) = true <->
    (∀ i : Fin.t k, p (Vector.nth w i) = true).
  Proof.
    intros A p k; induction k as [| k ih]; intro w.
    - rewrite (vector_inv_0 w); cbn; split;
        [intros _ i; inversion i | reflexivity].
    - destruct (vector_inv_S w) as (a & w' & hw); subst w.
      rewrite Vector.to_list_cons; cbn [List.forallb].
      rewrite Bool.andb_true_iff, (ih w'); split.
      + intros (hhead & hrest) i; revert hhead hrest.
        apply (Fin.caseS' i); [intros hhead _; exact hhead |].
        intros i' _ hrest; cbn; exact (hrest i').
      + intro hall; split; [exact (hall Fin.F1) |].
        intro i'; exact (hall (Fin.FS i')).
  Qed.

  (** ** Checking that a vector solves the incidence system

      Only the bases that actually occur in a row can carry a nonzero
      incidence sum, so it is enough to walk the row.  The neutral
      element is skipped because its equation is not part of the
      system. *)
  Definition row_incidence_zerob {n : nat}
    (row : Vector.t G n) (v : Vector.t F n) : bool :=
    List.forallb
      (fun b => if Gdec b gid then true
                else if Fdec (sum_atC row v b) zero then true else false)
      (Vector.to_list row).

  Definition incidence_zerob {m n : nat}
    (mat : Vector.t (Vector.t G n) m) (v : Vector.t F n) : bool :=
    List.forallb (fun row => row_incidence_zerob row v) (Vector.to_list mat).

  Lemma row_incidence_zerob_spec :
    ∀ (n : nat) (row : Vector.t G n) (v : Vector.t F n),
    row_incidence_zerob row v = true <->
    (∀ b : G, b <> gid -> sum_atC row v b = zero).
  Proof.
    intros n row v; unfold row_incidence_zerob; split.
    - intros hall b hb.
      (* a base absent from the row has an empty sum anyway *)
      destruct (List.in_dec Gdec b (Vector.to_list row)) as [hin | hout].
      + rewrite List.forallb_forall in hall.
        specialize (hall b hin).
        destruct (Gdec b gid) as [heq | _]; [exfalso; exact (hb heq) |].
        destruct (Fdec (sum_atC row v b) zero) as [heq | _];
          [exact heq | discriminate hall].
      + apply sum_at_absent; intros j hbad.
        apply hout; rewrite <- hbad; apply in_to_list.
    - intro hsum; rewrite List.forallb_forall; intros b _.
      destruct (Gdec b gid) as [_ | hb]; [reflexivity |].
      rewrite (hsum b hb).
      destruct (Fdec zero zero) as [_ | hne];
        [reflexivity | exfalso; exact (hne eq_refl)].
  Qed.

  Theorem incidence_zerob_spec :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (v : Vector.t F n),
    incidence_zerob mat v = true <-> incidence_zeroC mat v.
  Proof.
    intros m n mat v; unfold incidence_zerob, incidence_zero.
    rewrite forallb_to_list_nth; split.
    - intros hall i b hb.
      exact (proj1 (row_incidence_zerob_spec n (Vector.nth mat i) v) (hall i) b hb).
    - intros hall i.
      exact (proj2 (row_incidence_zerob_spec n (Vector.nth mat i) v) (hall i)).
  Qed.

  (** ** Checking that the proposed solution is not the zero vector

      A solution says nothing unless it is nonzero, so the certificate
      carries this test too. *)
  Fixpoint wzerob {n : nat} (v : Vector.t F n) : bool :=
    match v with
    | [] => true
    | a :: v' => andb (if Fdec a zero then true else false) (wzerob v')
    end.

  Lemma wzerob_spec :
    ∀ (n : nat) (v : Vector.t F n), wzerob v = true <-> v = wzeroC n.
  Proof.
    induction n as [| n ih]; intro v.
    - rewrite (vector_inv_0 v); cbn; split; reflexivity.
    - destruct (vector_inv_S v) as (a & v' & hv); subst v.
      cbn [wzerob]; rewrite Bool.andb_true_iff, (ih v'); split.
      + intros (ha & hrest).
        destruct (Fdec a zero) as [heq | _]; [| discriminate ha].
        subst a; rewrite hrest; reflexivity.
      + intro heq.
        assert (ha : a = zero)
          by (change a with (Vector.hd (a :: v')); rewrite heq; reflexivity).
        assert (hr : v' = wzeroC n)
          by (change v' with (Vector.tl (a :: v')); rewrite heq; reflexivity).
        split; [| exact hr].
        subst a; destruct (Fdec zero zero) as [_ | hne];
          [reflexivity | exfalso; exact (hne eq_refl)].
  Qed.

  Lemma wzerob_false_nonzero :
    ∀ (n : nat) (v : Vector.t F n), wzerob v = false -> v <> wzeroC n.
  Proof.
    intros n v hfalse hbad.
    rewrite (proj2 (wzerob_spec n v) hbad) in hfalse.
    discriminate hfalse.
  Qed.

  (** ** The rejection certificate

      Everything the checker needs is here: two boolean tests on a
      proposed solution, and the conclusion that the leaf leaves its
      secret undetermined.  The group is arbitrary and no assumption
      about the bases is used. *)
  Theorem reject_certificate_sound :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m)
      (v x : Vector.t F n),
    incidence_zerob mat v = true -> wzerob v = false ->
    mat_evalC mat x = pub ->
    ∃ y : Vector.t F n, mat_evalC mat y = pub ∧ y <> x.
  Proof.
    intros m n mat pub v x hinc hnz hx.
    apply (@incidence_solution_breaks_determination F zero one add mul
             sub div opp inv G gid ginv gop gpow Gdec Hvec m n mat pub v x).
    - exact (proj1 (incidence_zerob_spec m n mat v) hinc).
    - exact (wzerob_false_nonzero n v hnz).
    - exact hx.
  Qed.

  (** ** The acceptance side

      Rejection needs a certificate; acceptance needs an argument that
      no certificate exists.  The argument here is the one that covers
      ordinary statements: if some row lists pairwise distinct bases,
      none of them neutral, then the incidence equations of that row
      read [x_j = 0] one by one and the system has only the zero
      solution. *)

  (** A base whose positions all carry zero has a zero incidence sum. *)
  Lemma sum_at_all_zero :
    ∀ (n : nat) (row : Vector.t G n) (v : Vector.t F n) (b : G),
    (∀ j : Fin.t n, Vector.nth row j = b -> Vector.nth v j = zero) ->
    sum_atC row v b = zero.
  Proof.
    induction n as [| n ih]; intros row v b hz.
    - rewrite (vector_inv_0 row), (vector_inv_0 v); reflexivity.
    - destruct (vector_inv_S row) as (c & row' & hrow).
      destruct (vector_inv_S v) as (a & v' & hv).
      subst.
      rewrite sum_at_cons, (ih row' v' b)
        by (intros j hj; exact (hz (Fin.FS j) hj)).
      destruct (Gdec c b) as [heq | _].
      + assert (ha : a = zero) by (exact (hz Fin.F1 heq)).
        rewrite ha; apply left_identity.
      + apply left_identity.
  Qed.

  (** A base occurring at exactly one position where the witness may
      be nonzero has that entry as its incidence sum.  This is what
      turns an incidence equation into a statement about a single
      secret. *)
  Lemma sum_at_singleton :
    ∀ (n : nat) (row : Vector.t G n) (v : Vector.t F n) (j : Fin.t n),
    (∀ j' : Fin.t n, j' <> j ->
       Vector.nth row j' = Vector.nth row j -> Vector.nth v j' = zero) ->
    sum_atC row v (Vector.nth row j) = Vector.nth v j.
  Proof.
    intros n row v j; revert row v.
    induction j as [p | p j ih]; intros row v hone.
    - destruct (vector_inv_S row) as (b & row' & hrow).
      destruct (vector_inv_S v) as (a & v' & hv).
      subst.
      cbn [Vector.nth Vector.caseS Nat.pred].
      rewrite sum_at_cons, (sum_at_all_zero p row' v' b)
        by (intros k hk; apply (hone (Fin.FS k)); [discriminate | exact hk]).
      destruct (Gdec b b) as [_ | hne];
        [apply right_identity | exfalso; exact (hne eq_refl)].
    - destruct (vector_inv_S row) as (b & row' & hrow).
      destruct (vector_inv_S v) as (a & v' & hv).
      subst.
      cbn [Vector.nth Vector.caseS Nat.pred].
      rewrite sum_at_cons, (ih row' v')
        by (intros k hk hb; apply (hone (Fin.FS k));
            [intro hbad; exact (hk (Fin.FS_inj k j hbad)) | exact hb]).
      destruct (Gdec b (Vector.nth row' j)) as [heq | _].
      + (* the head shares the base, so the hypothesis zeroes it *)
        assert (ha : a = zero)
          by (apply (hone Fin.F1); [discriminate | exact heq]).
        rewrite ha; apply left_identity.
      + apply left_identity.
  Qed.

  (** One column pinned by one row, given that the other columns
      sharing its base are already known to vanish. *)
  Theorem pinned_column_vanishes :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (v : Vector.t F n)
      (i : Fin.t m) (j : Fin.t n),
    incidence_zeroC mat v ->
    Vector.nth (Vector.nth mat i) j <> gid ->
    (∀ j' : Fin.t n, j' <> j ->
       Vector.nth (Vector.nth mat i) j' = Vector.nth (Vector.nth mat i) j ->
       Vector.nth v j' = zero) ->
    Vector.nth v j = zero.
  Proof.
    intros m n mat v i j hinc hlive hpin.
    rewrite <- (sum_at_singleton n (Vector.nth mat i) v j hpin).
    exact (hinc i _ hlive).
  Qed.

  (** The acceptance theorem.  A row of pairwise distinct non-neutral
      bases leaves the incidence system with only the zero solution,
      so the leaf has no structural degeneracy at all. *)
  Theorem separating_row_determines :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (i : Fin.t m),
    (∀ j : Fin.t n, Vector.nth (Vector.nth mat i) j <> gid) ->
    (∀ j j' : Fin.t n, j <> j' ->
       Vector.nth (Vector.nth mat i) j <> Vector.nth (Vector.nth mat i) j') ->
    ∀ v : Vector.t F n, incidence_zeroC mat v -> v = wzeroC n.
  Proof.
    intros m n mat i hlive hdist v hinc.
    apply Vector.eq_nth_iff; intros p q hpq; subst q.
    unfold wzero; rewrite nth_const.
    apply (pinned_column_vanishes m n mat v i p hinc (hlive p)).
    intros j' hne heq; exfalso; exact (hdist j' p hne heq).
  Qed.

End IncidenceDecide.
