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

    [leaf_determinedb] is the acceptance side, and it runs on the same
    terms: a [true] from it is a proof, not a report from a search.  A
    row whose bases are pairwise distinct and none neutral forces every
    incidence equation of that row to read [x_j = 0], so the system has
    only the zero solution and the leaf carries no structural
    degeneracy; [leaf_determinedb_sound] is that implication and
    [separating_row_determines] the mathematics behind it.  Neither
    verdict, accept or reject, depends on trusting the elimination that
    looks for a certificate.

    What the acceptance test is not is complete.  The condition it
    decides is sufficient and not necessary: a system can have only the
    zero solution with no single row separating, as
    [[g,g,h];[h,g,g]] does, where the two rows between them pin every
    column but neither does so alone.  [pinned_column_vanishes] extends
    the reach one column at a time, and beyond that a leaf with no
    separating row is reported as undecided rather than accepted.
    Deciding those needs a rank computation over the field, which is
    not verified here.  [leaf_determinedb_spec] makes the boundary
    legible: a [false] says exactly that no row of the leaf separates,
    which is a statement about the leaf and not about the checker. *)
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
      solution.  [leaf_determinedb] at the end of the file decides it. *)

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

  (** ** The acceptance test, as a boolean

      The theorem above is about positions, and a test has to be about
      the row as it is stored, so the two are bridged here.  Without
      this, acceptance would have to rest on whatever unverified
      search failed to find a certificate, which is the arrangement
      the rejection side was built to avoid. *)

  Fixpoint no_dupb (l : list G) : bool :=
    match l with
    | List.nil => true
    | List.cons b l' =>
        andb (if List.in_dec Gdec b l' then false else true) (no_dupb l')
    end.

  Lemma no_dupb_spec :
    ∀ l : list G, no_dupb l = true <-> List.NoDup l.
  Proof.
    induction l as [| b l ih]; cbn.
    - split; [intros _; constructor | reflexivity].
    - rewrite Bool.andb_true_iff, ih; split.
      + intros (hb & hnd); constructor; [| exact hnd].
        destruct (List.in_dec Gdec b l) as [_ | hout];
          [discriminate hb | exact hout].
      + intro hnd; inversion hnd as [| ? ? hout hrest]; subst; split;
          [| exact hrest].
        destruct (List.in_dec Gdec b l) as [hin | _];
          [exfalso; exact (hout hin) | reflexivity].
  Qed.

  (** A row lists distinct elements exactly when distinct positions
      carry distinct bases. *)
  Lemma nodup_to_list_iff_distinct_positions :
    ∀ (n : nat) (row : Vector.t G n),
    List.NoDup (Vector.to_list row) <->
    (∀ j j' : Fin.t n, j <> j' ->
       Vector.nth row j <> Vector.nth row j').
  Proof.
    induction n as [| n ih]; intro row.
    - rewrite (vector_inv_0 row); cbn; split;
        [intros _ j; inversion j | intros _; constructor].
    - destruct (vector_inv_S row) as (b & row' & hrow); subst row.
      rewrite Vector.to_list_cons; split.
      + intro hnd; inversion hnd as [| ? ? hout hrest]; subst.
        intros j j'; revert j'; apply (Fin.caseS' j); clear j.
        * intro j'; apply (Fin.caseS' j').
          -- intro hne; exfalso; exact (hne eq_refl).
          -- intros k _ heq; cbn in heq.
             (* the head would then occur in the tail *)
             apply hout; rewrite heq; apply in_to_list.
        * intros k j'; apply (Fin.caseS' j').
          -- intros _ heq; cbn in heq.
             apply hout; rewrite <- heq; apply in_to_list.
          -- intros k' hne; cbn.
             apply (proj1 (ih row') hrest).
             intro hbad; apply hne; rewrite hbad; reflexivity.
      + intro hdist; constructor.
        * (* a repeat of the head would be a second position holding it *)
          intro hin.
          destruct (in_to_list_inv G n row' b hin) as (k & hk).
          exact (hdist Fin.F1 (Fin.FS k) ltac:(discriminate) (eq_sym hk)).
        * apply ih; intros k k' hne.
          exact (hdist (Fin.FS k) (Fin.FS k')
                   (fun h => hne (Fin.FS_inj k k' h))).
  Qed.

  (** A row is *separating* when its bases are pairwise distinct and
      none of them is the neutral element.  That is exactly the
      hypothesis of [separating_row_determines]. *)
  Definition row_separatingb {n : nat} (row : Vector.t G n) : bool :=
    andb
      (List.forallb (fun b => if Gdec b gid then false else true)
         (Vector.to_list row))
      (no_dupb (Vector.to_list row)).

  Theorem row_separatingb_spec :
    ∀ (n : nat) (row : Vector.t G n),
    row_separatingb row = true <->
    ((∀ j : Fin.t n, Vector.nth row j <> gid) ∧
     (∀ j j' : Fin.t n, j <> j' -> Vector.nth row j <> Vector.nth row j')).
  Proof.
    intros n row; unfold row_separatingb.
    rewrite Bool.andb_true_iff, forallb_to_list_nth, no_dupb_spec,
      nodup_to_list_iff_distinct_positions.
    split.
    - intros (hlive & hdist); split; [| exact hdist].
      intro j; specialize (hlive j).
      destruct (Gdec (Vector.nth row j) gid) as [_ | hne];
        [discriminate hlive | exact hne].
    - intros (hlive & hdist); split; [| exact hdist].
      intro j; destruct (Gdec (Vector.nth row j) gid) as [heq | _];
        [exfalso; exact (hlive j heq) | reflexivity].
  Qed.

  (** The leaf-level test: some row separates. *)
  Definition leaf_determinedb {m n : nat}
    (mat : Vector.t (Vector.t G n) m) : bool :=
    List.existsb (fun row => row_separatingb row) (Vector.to_list mat).

  (** The acceptance theorem the compiler can run.  A [true] here is
      a proof that the incidence system has only the zero solution, so
      the leaf carries no structural degeneracy at all. *)
  Theorem leaf_determinedb_sound :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m),
    leaf_determinedb mat = true ->
    ∀ v : Vector.t F n, incidence_zeroC mat v -> v = wzeroC n.
  Proof.
    intros m n mat hdet v hinc.
    unfold leaf_determinedb in hdet.
    rewrite List.existsb_exists in hdet.
    destruct hdet as (row & hin & hsep).
    destruct (in_to_list_inv (Vector.t G n) m mat row hin) as (i & hi).
    rewrite <- hi in hsep.
    destruct (proj1 (row_separatingb_spec n (Vector.nth mat i)) hsep)
      as (hlive & hdist).
    exact (separating_row_determines m n mat i hlive hdist v hinc).
  Qed.

  (** And the test is exactly the condition it is meant to decide, so
      a [false] is a statement about the leaf and not about the
      checker: no row of it separates. *)
  Theorem leaf_determinedb_spec :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m),
    leaf_determinedb mat = true <->
    (∃ i : Fin.t m,
       (∀ j : Fin.t n, Vector.nth (Vector.nth mat i) j <> gid) ∧
       (∀ j j' : Fin.t n, j <> j' ->
          Vector.nth (Vector.nth mat i) j <> Vector.nth (Vector.nth mat i) j')).
  Proof.
    intros m n mat; unfold leaf_determinedb.
    rewrite List.existsb_exists; split.
    - intros (row & hin & hsep).
      destruct (in_to_list_inv (Vector.t G n) m mat row hin) as (i & hi).
      rewrite <- hi in hsep.
      exists i; exact (proj1 (row_separatingb_spec n (Vector.nth mat i)) hsep).
    - intros (i & hsep).
      exists (Vector.nth mat i); split;
        [apply in_to_list |
         exact (proj2 (row_separatingb_spec n (Vector.nth mat i)) hsep)].
  Qed.

  (** ** Where the acceptance test stops

      The condition [leaf_determinedb] decides is sufficient and not
      necessary, and this is the smallest example of the gap.  Neither
      row of [[g,g,h]; [h,g,g]] separates, because [g] occurs twice in
      each, so the test says nothing.  But the two rows between them
      pin every column: the first reads [x1 + x2 = 0] and [x3 = 0],
      the second [x1 = 0] and [x2 + x3 = 0], and unit propagation
      through those four equations leaves only the zero solution.

      A leaf of this shape is sound and the checker will not say so.
      Deciding it needs a rank computation over the field, which is
      not verified here. *)
  Definition two_row_mat (g h : G) : Vector.t (Vector.t G 3) 2 :=
    [[g; g; h]; [h; g; g]].

  Theorem two_rows_pin_what_no_row_pins :
    ∀ (g h : G),
    g <> gid -> h <> gid -> g <> h ->
    (* the acceptance test declines *)
    leaf_determinedb (two_row_mat g h) = false
    (* though the leaf is sound *)
    ∧ (∀ v : Vector.t F 3,
         incidence_zeroC (two_row_mat g h) v -> v = wzeroC 3).
  Proof.
    intros g h hg hh hgh; split.
    - (* each row repeats [g], so neither has distinct bases *)
      destruct (leaf_determinedb (two_row_mat g h)) eqn:hb; [| reflexivity].
      exfalso.
      destruct (proj1 (leaf_determinedb_spec 2 3 (two_row_mat g h)) hb)
        as (i & _ & hdist).
      revert hdist; unfold two_row_mat.
      apply (fin2_cases
               (fun i => ~ (∀ j j' : Fin.t 3, j <> j' ->
                  Vector.nth (Vector.nth [[g; g; h]; [h; g; g]] i) j <>
                  Vector.nth (Vector.nth [[g; g; h]; [h; g; g]] i) j')));
        intro hdist.
      + exact (hdist Fin.F1 (Fin.FS Fin.F1) ltac:(discriminate) eq_refl).
      + exact (hdist (Fin.FS Fin.F1) (Fin.FS (Fin.FS Fin.F1))
                 ltac:(discriminate) eq_refl).
    - intros v hinc.
      (* [pattern] before [revert] fixes the motive by hand; left to
         itself the unifier picks a constant one and the case analysis
         does nothing. *)
      (* the third secret: [h] occurs once in the first row *)
      assert (h2 : Vector.nth v (Fin.FS (Fin.FS Fin.F1)) = zero).
      { apply (pinned_column_vanishes 2 3 (two_row_mat g h) v
                 Fin.F1 (Fin.FS (Fin.FS Fin.F1)) hinc); [exact hh |].
        intro j'; pattern j'; revert j'; apply fin3_cases; cbn;
          intros hne hbad.
        - exfalso; exact (hgh hbad).
        - exfalso; exact (hgh hbad).
        - exfalso; exact (hne eq_refl). }
      (* the first secret: [h] occurs once in the second row *)
      assert (h0 : Vector.nth v Fin.F1 = zero).
      { apply (pinned_column_vanishes 2 3 (two_row_mat g h) v
                 (Fin.FS Fin.F1) Fin.F1 hinc); [exact hh |].
        intro j'; pattern j'; revert j'; apply fin3_cases; cbn;
          intros hne hbad.
        - exfalso; exact (hne eq_refl).
        - exfalso; exact (hgh hbad).
        - exfalso; exact (hgh hbad). }
      (* the second secret: [g] occupies the first two positions of the
         first row, and the first of them is already known to vanish *)
      assert (h1 : Vector.nth v (Fin.FS Fin.F1) = zero).
      { apply (pinned_column_vanishes 2 3 (two_row_mat g h) v
                 Fin.F1 (Fin.FS Fin.F1) hinc); [exact hg |].
        intro j'; pattern j'; revert j'; apply fin3_cases; cbn;
          intros hne hbad.
        - exact h0.
        - exfalso; exact (hne eq_refl).
        - exfalso; exact (hgh (eq_sym hbad)). }
      apply Vector.eq_nth_iff; intros p q hpq; subst q.
      unfold wzero; rewrite nth_const.
      pattern p; revert p; apply fin3_cases; assumption.
  Qed.

End IncidenceDecide.
