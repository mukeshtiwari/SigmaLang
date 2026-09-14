From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef BinPos.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import Util.
From Compiler Require Import LinearRelation.

Import VectorNotations.

(** * When a leaf proves less than it looks like it proves

    A leaf says [mat_eval mat xs = pub]: a matrix of group elements
    raised to a vector of secrets equals a vector of targets.  Not
    every such statement is worth proving, and two degeneracies are
    easy to write by accident and invisible once written.

    We found them by accident ourselves.  Pointing the statement
    identifier of this development at the test vectors of the CFRG
    sigma-protocol draft, three of the draft's negative controls were
    accepted by our verifier and rejected by the standard.  The
    disagreement was not in the verification equation, which those
    proofs satisfy; it was that the standard validates instances in
    ways we did not.  This file supplies the two conditions we were
    missing, together with proofs that neither may be dropped.

    ** The two conditions

    The first is that every declared secret must actually appear.  If
    a column of the matrix is the neutral element in every row, then
    the corresponding secret is multiplied into nothing, and the
    relation says nothing about it.

    The second is that no target may be the neutral element.  An
    equation whose target is neutral reads "this product of powers is
    the identity", which the all-zero witness satisfies whatever the
    bases are.

    ** Why necessity, and not merely soundness

    A checker that rejects some statements is only interesting if the
    rejection is forced.  So each condition below comes with a theorem
    saying what goes wrong without it.  For the first, two witnesses
    that differ in the unconstrained secret both satisfy the relation,
    so knowledge of that secret is not proven.  For the second, the
    all-zero witness satisfies the relation, so nothing is proven at
    all.  These follow the pattern of [checker_necessary] in
    DslNecessity.v, which does the same for the disjunction
    condition. *)
Section LeafValidity.

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

  #[local] Notation row_evalC := (@row_eval F G gid gop gpow).
  #[local] Notation mat_evalC := (@mat_eval F G gid gop gpow).

  (** ** Two facts about the neutral element

      Both come straight from the vector space and are used
      throughout: the neutral element absorbs every exponent, and
      every base raised to zero is neutral. *)

  Lemma gpow_gid_absorbs : ∀ x : F, gpow gid x = gid.
  Proof. intro x; exact (Vector_space.vid_identity (Hvec := Hvec) x). Qed.

  Lemma gpow_zero_is_gid : ∀ g : G, gpow g zero = gid.
  Proof.
    intro g.
    exact (vector_space_field_zero (vector_space := Hvec) g).
  Qed.

  (** ** Condition one: every secret is constrained

      Column [j] is *live* in a matrix when some row carries a base
      other than the neutral element there.  A leaf is well formed
      only if every column is live: otherwise the secret at that
      position is never multiplied into anything. *)

  Definition column_live {m n : nat}
    (mat : Vector.t (Vector.t G n) m) (j : Fin.t n) : Prop :=
    ∃ i : Fin.t m, Vector.nth (Vector.nth mat i) j <> gid.

  (** A row whose entry at [j] is neutral cannot tell two witnesses
      apart when they agree everywhere but [j].  This is the whole
      content of the condition; everything else is lifting it. *)
  Lemma row_eval_blind :
    ∀ (n : nat) (row : Vector.t G n) (xs ys : Vector.t F n) (j : Fin.t n),
    Vector.nth row j = gid ->
    (∀ k : Fin.t n, k <> j -> Vector.nth xs k = Vector.nth ys k) ->
    row_evalC row xs = row_evalC row ys.
  Proof.
    intros n row xs ys j hj hagree.
    unfold row_eval.
    (* the two zipped vectors are equal pointwise, hence equal *)
    assert (heq : zip_with gpow row xs = zip_with gpow row ys).
    { apply Vector.eq_nth_iff; intros p q hpq; subst q.
      rewrite !nth_zip_with.
      destruct (Fin.eq_dec p j) as [heqp | hnep].
      + subst p. rewrite hj, !gpow_gid_absorbs; reflexivity.
      + rewrite (hagree p hnep); reflexivity. }
    rewrite heq; reflexivity.
  Qed.

  (** The necessity theorem for the first condition.

      If column [j] is dead, then any witness satisfying the relation
      may be altered at [j] to anything at all and still satisfy it.
      So the protocol does not prove knowledge of that secret: it
      proves knowledge of the others, and is silent about this one. *)
  Theorem dead_column_proves_nothing_about_it :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m)
      (pub : Vector.t G m) (j : Fin.t n) (xs ys : Vector.t F n),
    (∀ i : Fin.t m, Vector.nth (Vector.nth mat i) j = gid) ->
    (∀ k : Fin.t n, k <> j -> Vector.nth xs k = Vector.nth ys k) ->
    mat_evalC mat xs = pub ->
    mat_evalC mat ys = pub.
  Proof.
    intros m n mat pub j xs ys hdead hagree hxs.
    rewrite <- hxs.
    unfold mat_eval.
    apply Vector.eq_nth_iff; intros p q hpq; subst q.
    rewrite !(Vector.nth_map _ _ p p eq_refl).
    symmetry.
    eapply row_eval_blind; [apply hdead | exact hagree].
  Qed.

  (** ** Condition two: no target is neutral

      An equation with a neutral target is satisfied by the all-zero
      witness, whatever its bases are.  The statement is therefore
      true of every instance, and proving it demonstrates nothing. *)

  Definition target_live {m : nat} (pub : Vector.t G m) : Prop :=
    ∀ i : Fin.t m, Vector.nth pub i <> gid.

  Lemma row_eval_zero :
    ∀ (n : nat) (row : Vector.t G n),
    row_evalC row (Vector.const zero n) = gid.
  Proof.
    intros n row.
    unfold row_eval.
    induction row as [| g k row ih]; cbn; [reflexivity |].
    rewrite ih, gpow_zero_is_gid.
    apply left_identity.
  Qed.

  (** The necessity theorem for the second condition.

      If every target is neutral, the all-zero witness satisfies the
      relation.  A prover needs to know nothing to produce it, so the
      proof carries no information. *)
  Theorem neutral_targets_are_free :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m),
    (∀ i : Fin.t m, Vector.nth pub i = gid) ->
    mat_evalC mat (Vector.const zero n) = pub.
  Proof.
    intros m n mat pub hpub.
    unfold mat_eval.
    apply Vector.eq_nth_iff; intros p q hpq; subst q.
    rewrite (Vector.nth_map _ _ p p eq_refl).
    rewrite hpub.
    apply row_eval_zero.
  Qed.

  (** ** Deciding the two conditions

      The theorems above say what goes wrong without the conditions.
      A compiler needs to decide them, so here they are as a boolean
      test, with the equivalence proven in both directions.  Only then
      is a rejection evidence about the statement rather than about
      the checker. *)

  (** Which entries of a row are the neutral element. *)
  Definition gid_mask {n : nat} (row : Vector.t G n) : Vector.t bool n :=
    Vector.map (fun g => if Gdec g gid then true else false) row.

  (** Columnwise conjunction over the rows: position [j] is [true]
      exactly when every row is neutral there, that is when column [j]
      is dead. *)
  Definition dead_columns {m n : nat}
    (mat : Vector.t (Vector.t G n) m) : Vector.t bool n :=
    Vector.fold_right (fun row acc => zip_with andb (gid_mask row) acc)
      mat (Vector.const true n).

  Lemma dead_columns_spec :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (j : Fin.t n),
    Vector.nth (dead_columns mat) j = true <->
    (∀ i : Fin.t m, Vector.nth (Vector.nth mat i) j = gid).
  Proof.
    intros m n mat j.
    induction mat as [| row m' mat ih]; cbn [dead_columns Vector.fold_right].
    - split.
      + intros _ i; inversion i.
      + intros _. clear. induction j as [k | k j ih]; cbn; [reflexivity | exact ih].
    - rewrite nth_zip_with, Bool.andb_true_iff.
      unfold gid_mask. rewrite (Vector.nth_map _ _ j j eq_refl).
      split.
      + intros (hrow & hrest) i.
        (* the head row, then the rest, by the induction hypothesis *)
        revert hrow hrest. apply (Fin.caseS' i).
        * intros hrow _; cbn.
          destruct (Gdec (Vector.nth row j) gid) as [heq | hne];
            [exact heq | discriminate hrow].
        * intros i' _ hrest; cbn. apply ih; exact hrest.
      + intro hall. split.
        * specialize (hall Fin.F1); cbn in hall.
          destruct (Gdec (Vector.nth row j) gid) as [_ | hne];
            [reflexivity | exfalso; exact (hne hall)].
        * apply ih. intro i'. exact (hall (Fin.FS i')).
  Qed.

  (** The other direction of the same fact, constructively: a column
      the mask does not mark gives a row witnessing why.  Stated
      separately because the [true] direction alone would force
      classical reasoning to invert, and this development stays
      axiom-free. *)
  Lemma nth_const_true :
    ∀ (n : nat) (j : Fin.t n), Vector.nth (Vector.const true n) j = true.
  Proof.
    intros n j; induction j as [k | k j ih]; cbn; [reflexivity | exact ih].
  Qed.

  Lemma dead_columns_false :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (j : Fin.t n),
    Vector.nth (dead_columns mat) j = false ->
    ∃ i : Fin.t m, Vector.nth (Vector.nth mat i) j <> gid.
  Proof.
    intros m n mat j.
    induction mat as [| row m' mat ih]; cbn [dead_columns Vector.fold_right].
    - rewrite nth_const_true; discriminate.
    - rewrite nth_zip_with. unfold gid_mask.
      rewrite (Vector.nth_map _ _ j j eq_refl).
      intro h. apply Bool.andb_false_iff in h as [hrow | hrest].
      + exists Fin.F1; cbn.
        destruct (Gdec (Vector.nth row j) gid) as [_ | hne];
          [discriminate hrow | exact hne].
      + destruct (ih hrest) as (i & hi). exists (Fin.FS i); cbn; exact hi.
  Qed.

  (** No column is dead. *)
  Definition columns_liveb {m n : nat}
    (mat : Vector.t (Vector.t G n) m) : bool :=
    negb (Vector.fold_right orb (dead_columns mat) false).

  Lemma fold_orb_true :
    ∀ (n : nat) (v : Vector.t bool n),
    Vector.fold_right orb v false = true <->
    (∃ j : Fin.t n, Vector.nth v j = true).
  Proof.
    intros n v; induction v as [| b n' v ih]; cbn.
    - split; [discriminate | intros (j & _); inversion j].
    - rewrite Bool.orb_true_iff. split.
      + intros [hb | hrest].
        * exists Fin.F1; cbn; exact hb.
        * destruct (proj1 ih hrest) as (j & hj). exists (Fin.FS j); cbn; exact hj.
      + intros (j & hj). revert hj. apply (Fin.caseS' j).
        * cbn; intro hb; left; exact hb.
        * cbn; intros j' hj'; right; apply ih; exists j'; exact hj'.
  Qed.

  Theorem columns_liveb_spec :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m),
    columns_liveb mat = true <-> (∀ j : Fin.t n, column_live mat j).
  Proof.
    intros m n mat. unfold columns_liveb, column_live.
    rewrite Bool.negb_true_iff, <- Bool.not_true_iff_false, fold_orb_true.
    split.
    - intros hno j.
      destruct (Vector.nth (dead_columns mat) j) eqn:he.
      + exfalso; apply hno; exists j; exact he.
      + exact (dead_columns_false m n mat j he).
    - intros hlive (j & hj).
      destruct (hlive j) as (i & hi).
      apply hi. exact (proj1 (dead_columns_spec m n mat j) hj i).
  Qed.

  (** No target is the neutral element. *)
  Definition target_liveb {m : nat} (pub : Vector.t G m) : bool :=
    Vector.fold_right
      (fun p acc => andb (if Gdec p gid then false else true) acc) pub true.

  Theorem target_liveb_spec :
    ∀ (m : nat) (pub : Vector.t G m),
    target_liveb pub = true <-> target_live pub.
  Proof.
    intros m pub; unfold target_liveb, target_live.
    induction pub as [| p m' pub ih]; cbn.
    - split; [intros _ i; inversion i | reflexivity].
    - rewrite Bool.andb_true_iff. split.
      + intros (hp & hrest) i. revert hp hrest. apply (Fin.caseS' i).
        * intros hp _; cbn.
          destruct (Gdec p gid) as [heq | hne]; [discriminate hp | exact hne].
        * intros i' _ hrest; cbn. apply ih; exact hrest.
      + intro hall; split.
        * specialize (hall Fin.F1); cbn in hall.
          destruct (Gdec p gid) as [heq | _];
            [exfalso; exact (hall heq) | reflexivity].
        * apply ih. intro i'. exact (hall (Fin.FS i')).
  Qed.

  (** The checker, and the theorem that it decides exactly the two
      conditions. *)
  Definition leaf_validb {m n : nat}
    (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m) : bool :=
    andb (columns_liveb mat) (target_liveb pub).

  (** ** The two conditions together *)

  Definition leaf_valid {m n : nat}
    (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m) : Prop :=
    (∀ j : Fin.t n, column_live mat j) ∧ target_live pub.

  Theorem leaf_validb_spec :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m),
    leaf_validb mat pub = true <-> leaf_valid mat pub.
  Proof.
    intros m n mat pub. unfold leaf_validb, leaf_valid.
    rewrite Bool.andb_true_iff, columns_liveb_spec, target_liveb_spec.
    reflexivity.
  Qed.

  (** A leaf that fails either condition is degenerate, and the two
      degeneracies are different.  Failing the first leaves a secret
      undetermined; failing the second leaves the whole statement
      free.  Stated together so a reader sees that the conjunction is
      not redundant. *)
  Theorem leaf_invalid_is_degenerate :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m),
    (* a dead column: some secret is undetermined *)
    ((∃ j : Fin.t n, ∀ i : Fin.t m, Vector.nth (Vector.nth mat i) j = gid) ->
     ∀ (j : Fin.t n) (xs ys : Vector.t F n),
     (∀ i : Fin.t m, Vector.nth (Vector.nth mat i) j = gid) ->
     (∀ k : Fin.t n, k <> j -> Vector.nth xs k = Vector.nth ys k) ->
     mat_evalC mat xs = pub -> mat_evalC mat ys = pub)
    ∧
    (* neutral targets: the statement is free *)
    ((∀ i : Fin.t m, Vector.nth pub i = gid) ->
     mat_evalC mat (Vector.const zero n) = pub).
  Proof.
    intros m n mat pub; split.
    - intros _ j xs ys hdead hagree hxs.
      eapply dead_column_proves_nothing_about_it; eauto.
    - apply neutral_targets_are_free.
  Qed.

End LeafValidity.
