From Stdlib Require Import Setoid
  setoid_ring.Field Lia Arith Vector Utf8
  Psatz Bool Pnat BinNatDef BinPos List.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import Util.
From Compiler Require Import LinearRelation LeafValidity
  Degeneracy IncidenceDecide Vacuity.

Import VectorNotations.

(** * A verdict on a leaf, carrying the reason for it

    The pieces are all in place and none of them is usable from one
    place.  Degeneracy.v proves what a nonzero incidence solution
    costs, IncidenceDecide.v checks one and decides a sufficient
    acceptance condition, Vacuity.v settles the second axis as far as
    it can be settled.  A compiler wants one call and one answer.

    ** The shape, and where it comes from

    The answer is not a boolean.  A boolean has two values and there
    are three things to say about the determination of a leaf: that
    its witness is pinned down, that it is not and here is the second
    witness, and that this checker cannot tell.  Folding the last two
    together, which is what [leaf_determinedb] alone does, loses the
    distinction between a leaf that is broken and a leaf that is
    merely beyond the test.

    The shape used instead is the one from Tim Griffin's CAS library,
    where a constructed algebraic structure carries, for each
    property, either an assertion that it holds or a counterexample
    witnessing that it fails - [check_commutative] is
    [Certify_Commutative] or [Certify_Not_Commutative (a, b)].  The
    verdict and its evidence travel together, so a consumer never has
    to consult a separate theorem to learn what a [false] meant.

    Two things here differ from CAS.  The certificates below admit an
    undecided case, because determination is decided by a rank
    computation this development has not verified and satisfiability
    is not decidable at all.  And the evidence for degeneracy is not
    found here: it comes in as [proposal], from a search that may be
    anything at all, and is validated by [incidence_zerob] before it
    is believed.

    ** Reading the result

    [classify_leaf_sound] is the whole interface.  It says that
    whichever constructor comes back, the corresponding claim holds:
    [Cert_determined] means the incidence system has only the zero
    solution, [Cert_degenerate v] means [v] really is a nonzero
    solution and therefore a second witness beside every first one,
    [Cert_vacuous] means the all-zero witness already satisfies the
    leaf, [Cert_unsatisfiable i] means row [i] is why nothing
    satisfies it, and the undecided constructors claim nothing.  A
    caller needs no other theorem. *)
Section LeafStatus.

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

  #[local] Notation mat_evalC := (@mat_eval F G gid gop gpow).
  #[local] Notation incidence_zeroC := (@incidence_zero F zero add G gid Gdec).
  #[local] Notation wzeroC := (@wzero F zero).
  #[local] Notation incidence_zerobC :=
    (@incidence_zerob F zero add Fdec G gid Gdec).
  #[local] Notation wzerobC := (@wzerob F zero Fdec).
  #[local] Notation leaf_determinedbC := (@leaf_determinedb G gid Gdec).

  (** ** The two certificates *)

  (** Whether the leaf pins its witness down.  [Cert_degenerate]
      carries the second witness, which is the whole of the evidence;
      [Cert_determination_undecided] carries nothing and claims
      nothing. *)
  Inductive determination_cert (n : nat) : Type :=
  | Cert_determined : determination_cert n
  | Cert_degenerate : Vector.t F n -> determination_cert n
  | Cert_determination_undecided : determination_cert n.

  Arguments Cert_determined {n}.
  Arguments Cert_degenerate {n}.
  Arguments Cert_determination_undecided {n}.

  (** Whether the leaf says anything at all.  [Cert_unsatisfiable]
      carries the row that makes it impossible.  The undecided case is
      the ordinary one here, not a failure of effort: deciding
      satisfiability is deciding discrete logarithms, by
      [leaf_satisfiability_is_discrete_log]. *)
  Inductive vacuity_cert (m : nat) : Type :=
  | Cert_vacuous : vacuity_cert m
  | Cert_unsatisfiable : Fin.t m -> vacuity_cert m
  | Cert_vacuity_undecided : vacuity_cert m.

  Arguments Cert_vacuous {m}.
  Arguments Cert_unsatisfiable {m}.
  Arguments Cert_vacuity_undecided {m}.

  Record leaf_cert (m n : nat) : Type := mk_leaf_cert
    { lc_determination : determination_cert n
    ; lc_vacuity : vacuity_cert m }.

  Arguments mk_leaf_cert {m n}.
  Arguments lc_determination {m n}.
  Arguments lc_vacuity {m n}.

  (** ** What each certificate claims

      Written as one function from certificate to proposition, so the
      soundness theorem below can be a single statement rather than a
      list of cases a caller has to assemble. *)
  Definition determination_claim {m n : nat}
    (mat : Vector.t (Vector.t G n) m) (c : determination_cert n) : Prop :=
    match c with
    | Cert_determined => ∀ v : Vector.t F n, incidence_zeroC mat v -> v = wzeroC n
    | Cert_degenerate v => incidence_zeroC mat v ∧ v <> wzeroC n
    | Cert_determination_undecided => True
    end.

  Definition vacuity_claim {m n : nat}
    (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m)
    (c : vacuity_cert m) : Prop :=
    match c with
    | Cert_vacuous => mat_evalC mat (wzeroC n) = pub
    | Cert_unsatisfiable i =>
        (∀ j : Fin.t n, Vector.nth (Vector.nth mat i) j = gid) ∧
        Vector.nth pub i <> gid ∧
        (∀ v : Vector.t F n, mat_evalC mat v <> pub)
    | Cert_vacuity_undecided => True
    end.

  (** ** Deciding the vacuity axis as far as it decides *)

  Definition all_gidb {k : nat} (w : Vector.t G k) : bool :=
    List.forallb (fun b => if Gdec b gid then true else false)
      (Vector.to_list w).

  Lemma all_gidb_spec :
    ∀ (k : nat) (w : Vector.t G k),
    all_gidb w = true <-> (∀ i : Fin.t k, Vector.nth w i = gid).
  Proof.
    intros k w; unfold all_gidb; rewrite forallb_to_list_nth; split.
    - intros hall i; specialize (hall i).
      destruct (Gdec (Vector.nth w i) gid) as [heq | _];
        [exact heq | discriminate hall].
    - intros hall i; rewrite (hall i).
      destruct (Gdec gid gid) as [_ | hne];
        [reflexivity | exfalso; exact (hne eq_refl)].
  Qed.

  (** The first row whose bases are all neutral while its target is
      not.  Recursion is on the arity rather than on the vectors, so
      that the matrix and the targets can be taken apart in step
      without a dependent match. *)
  Fixpoint find_dead_row (m : nat) {n : nat} :
    Vector.t (Vector.t G n) m -> Vector.t G m -> option (Fin.t m) :=
    match m as m' return
      Vector.t (Vector.t G n) m' -> Vector.t G m' -> option (Fin.t m')
    with
    | O => fun _ _ => None
    | S m' => fun mat pub =>
        if andb (all_gidb (Vector.hd mat))
                (if Gdec (Vector.hd pub) gid then false else true)
        then Some Fin.F1
        else option_map Fin.FS
               (find_dead_row m' (Vector.tl mat) (Vector.tl pub))
    end.

  Lemma find_dead_row_sound :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m)
      (i : Fin.t m),
    find_dead_row m mat pub = Some i ->
    (∀ j : Fin.t n, Vector.nth (Vector.nth mat i) j = gid) ∧
    Vector.nth pub i <> gid.
  Proof.
    intros m n; induction m as [| m ih]; intros mat pub i hfind.
    - discriminate hfind.
    - destruct (vector_inv_S mat) as (row & mat' & hmat).
      destruct (vector_inv_S pub) as (p & pub' & hpub).
      subst; cbn [find_dead_row Vector.hd Vector.tl Vector.caseS] in hfind.
      destruct (all_gidb row) eqn:hrow; cbn [andb] in hfind.
      + destruct (Gdec p gid) as [heq | hne].
        * (* the target is neutral, so this row is not the one *)
          cbn [option_map] in hfind.
          destruct (find_dead_row m mat' pub') as [i' |] eqn:hrec;
            [| discriminate hfind].
          injection hfind as hfind; subst i; cbn.
          exact (ih mat' pub' i' hrec).
        * injection hfind as hfind; subst i; cbn.
          split; [apply all_gidb_spec; exact hrow | exact hne].
      + cbn [option_map] in hfind.
        destruct (find_dead_row m mat' pub') as [i' |] eqn:hrec;
          [| discriminate hfind].
        injection hfind as hfind; subst i; cbn.
        exact (ih mat' pub' i' hrec).
  Qed.

  Definition classify_vacuity {m n : nat}
    (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m) : vacuity_cert m :=
    if all_gidb pub then Cert_vacuous
    else match find_dead_row m mat pub with
         | Some i => Cert_unsatisfiable i
         | None => Cert_vacuity_undecided
         end.

  Theorem classify_vacuity_sound :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m),
    vacuity_claim mat pub (classify_vacuity mat pub).
  Proof.
    intros m n mat pub; unfold classify_vacuity.
    destruct (all_gidb pub) eqn:hpub.
    - cbn; apply leaf_vacuous_iff_neutral_targets.
      apply all_gidb_spec; exact hpub.
    - destruct (find_dead_row m mat pub) as [i |] eqn:hfind; cbn; [| exact I].
      destruct (find_dead_row_sound m n mat pub i hfind) as (hdead & hlive).
      split; [exact hdead |]; split; [exact hlive |].
      exact (dead_row_unsatisfiable m n mat pub i hdead hlive).
  Qed.

  (** ** Deciding the determination axis as far as it decides

      A proposed second witness is validated before it is believed, so
      the search that produced it need not be trusted.  When there is
      none, or it does not check out, the sufficient acceptance test
      of IncidenceDecide.v is tried, and failing that the answer is
      that this checker cannot tell. *)
  Definition classify_determination {m n : nat}
    (mat : Vector.t (Vector.t G n) m)
    (proposal : option (Vector.t F n)) : determination_cert n :=
    match proposal with
    | Some v =>
        if andb (incidence_zerobC mat v) (negb (wzerobC v))
        then Cert_degenerate v
        else if leaf_determinedbC mat
             then Cert_determined
             else Cert_determination_undecided
    | None =>
        if leaf_determinedbC mat
        then Cert_determined
        else Cert_determination_undecided
    end.

  Theorem classify_determination_sound :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m)
      (proposal : option (Vector.t F n)),
    determination_claim mat (classify_determination mat proposal).
  Proof.
    intros m n mat proposal.
    (* the fallback is shared by both branches *)
    assert (hfall : determination_claim mat
                      (if leaf_determinedbC mat
                       then Cert_determined
                       else Cert_determination_undecided)).
    { destruct (leaf_determinedbC mat) eqn:hdet; cbn; [| exact I].
      exact (@leaf_determinedb_sound F zero one add mul sub div opp inv
               G gid ginv gop gpow Gdec Hvec m n mat hdet). }
    unfold classify_determination.
    destruct proposal as [v |]; [| exact hfall].
    destruct (andb (incidence_zerobC mat v) (negb (wzerobC v))) eqn:hb;
      [| exact hfall].
    apply Bool.andb_true_iff in hb as (hinc & hnz).
    apply Bool.negb_true_iff in hnz.
    cbn; split.
    - exact (proj1 (@incidence_zerob_spec F zero one add mul sub div opp inv
                      Fdec G gid ginv gop gpow Gdec Hvec m n mat v) hinc).
    - exact (@wzerob_false_nonzero F zero Fdec n v hnz).
  Qed.

  (** ** The one call and the one theorem *)
  Definition classify_leaf {m n : nat}
    (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m)
    (proposal : option (Vector.t F n)) : leaf_cert m n :=
    mk_leaf_cert (classify_determination mat proposal)
                 (classify_vacuity mat pub).

  Theorem classify_leaf_sound :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m)
      (proposal : option (Vector.t F n)),
    determination_claim mat
      (lc_determination (classify_leaf mat pub proposal)) ∧
    vacuity_claim mat pub (lc_vacuity (classify_leaf mat pub proposal)).
  Proof.
    intros m n mat pub proposal; split; cbn.
    - apply classify_determination_sound.
    - apply classify_vacuity_sound.
  Qed.

  (** ** What a caller does with it

      A leaf is fit to compile when its witness is pinned down and
      neither vacuity check fired.  Undecided on either axis is not
      acceptance: it is the checker declining to speak. *)
  Definition leaf_acceptable {m n : nat} (c : leaf_cert m n) : bool :=
    match lc_determination c, lc_vacuity c with
    | Cert_determined, Cert_vacuity_undecided => true
    | _, _ => false
    end.

  (** Acceptance means the witness is determined and the two
      structural vacuity failures were ruled out. *)
  Theorem leaf_acceptable_sound :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m)
      (proposal : option (Vector.t F n)),
    leaf_acceptable (classify_leaf mat pub proposal) = true ->
    (∀ v : Vector.t F n, incidence_zeroC mat v -> v = wzeroC n).
  Proof.
    intros m n mat pub proposal hacc.
    pose proof (classify_leaf_sound m n mat pub proposal) as (hdet & _).
    unfold leaf_acceptable in hacc; cbn in hacc, hdet.
    destruct (classify_determination mat proposal);
      [exact hdet | discriminate hacc | discriminate hacc].
  Qed.

  (** And a degenerate verdict really does mean every witness has a
      second one beside it, which is what the verdict is for. *)
  Theorem degenerate_cert_gives_second_witness :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m)
      (proposal : option (Vector.t F n)) (v x : Vector.t F n),
    lc_determination (classify_leaf mat pub proposal) = Cert_degenerate v ->
    mat_evalC mat x = pub ->
    ∃ y : Vector.t F n, mat_evalC mat y = pub ∧ y <> x.
  Proof.
    intros m n mat pub proposal v x hcert hx.
    pose proof (classify_leaf_sound m n mat pub proposal) as (hdet & _).
    cbn in hdet, hcert; rewrite hcert in hdet; cbn in hdet.
    destruct hdet as (hinc & hnz).
    apply (@incidence_solution_breaks_determination F zero one add mul
             sub div opp inv G gid ginv gop gpow Gdec Hvec m n mat pub v x);
      assumption.
  Qed.

  (** ** The old conditions, subsumed

      LeafValidity.v rejects a leaf with a dead column and a leaf with
      any neutral target.  Replacing that checker with this one is
      only justified if nothing is lost, so here is what happens to
      each condition.

      The first is subsumed outright.  A dead column is an incidence
      solution supported at that column, so a leaf whose incidence
      system has only the zero solution has no dead column; the old
      test is implied by the new verdict and need not be run. *)
  Theorem determined_implies_columns_liveb :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m),
    (∀ v : Vector.t F n, incidence_zeroC mat v -> v = wzeroC n) ->
    @columns_liveb G gid Gdec m n mat = true.
  Proof.
    intros m n mat hdet.
    destruct (@columns_liveb G gid Gdec m n mat) eqn:hb;
      [reflexivity | exfalso].
    (* a false verdict names a dead column *)
    unfold columns_liveb in hb; rewrite Bool.negb_false_iff in hb.
    apply fold_orb_true in hb as (j & hj).
    pose proof (proj1 (@dead_columns_spec G gid Gdec m n mat j) hj) as hdead.
    (* which supports a nonzero incidence solution *)
    pose proof (@dead_column_incidence F zero one add mul sub div opp inv
                  G gid ginv gop gpow Gdec Hvec m n mat j one hdead) as hinc.
    apply (@wpoint_nonzero F zero n j one
             (fun h => @zero_neq_one F (@eq F) zero one _ (eq_sym h))).
    exact (hdet _ hinc).
  Qed.

  (** The second is not subsumed, because it was wrong.
      [target_live] asks that no target be neutral, while the leaf is
      vacuous only when they all are.  So the new test fires strictly
      less often, and every leaf the old condition accepted is still
      accepted here - except at [m = 0], where [target_live] holds for
      want of a target and the leaf really is vacuous. *)
  Theorem target_live_implies_not_vacuous :
    ∀ (m : nat) (pub : Vector.t G (S m)),
    @target_live G gid (S m) pub -> all_gidb pub = false.
  Proof.
    intros m pub htl.
    destruct (all_gidb pub) eqn:hb; [exfalso | reflexivity].
    exact (htl Fin.F1 (proj1 (all_gidb_spec (S m) pub) hb Fin.F1)).
  Qed.

End LeafStatus.

(** The arities are recoverable from the payloads, so they are hidden
    outside the section; [Arguments] inside one does not survive it. *)
Arguments Cert_determined {F n}.
Arguments Cert_degenerate {F n}.
Arguments Cert_determination_undecided {F n}.
Arguments Cert_vacuous {m}.
Arguments Cert_unsatisfiable {m}.
Arguments Cert_vacuity_undecided {m}.
