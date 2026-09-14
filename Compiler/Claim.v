From Stdlib Require Import Setoid
  setoid_ring.Field Lia Arith Vector Utf8
  Psatz Bool Pnat BinNatDef BinPos List.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import Util.
From Compiler Require Import LinearRelation LeafValidity Degeneracy
  IncidenceDecide.

Import VectorNotations.

(** * What the statement claims, and why the question needs it

    Degeneracy.v asks whether a leaf determines its witness and
    answers with the kernel.  Run against a deployed corpus that
    question turns out to be under-specified, and the way it fails is
    worth recording, because the repair is the point of this file.

    ** The observation

    Pointing the checker at 6524 Helios ballot proofs reported 700 of
    724 leaves degenerate.  None of them was.  The DSL gives every
    compiled leaf the width of the *global* private-variable vector,
    so the left branch of a disjunction carries a column for the right
    branch's secret and never mentions it.  That column is dead, and
    [dead_column_proves_nothing_about_it] says truthfully that the
    leaf does not determine the secret sitting there.  It is not
    supposed to.  A branch of an OR abstains from the secrets of the
    other branch; that is what an OR is for.

    Meanwhile the very same shape, in the negative controls of a
    standard's test suite, is a real defect: an instance arriving off
    the wire declares how many scalars it has, and a declared scalar
    appearing in no equation means the proof establishes less than the
    instance advertises.

    The two are indistinguishable as matrices.  What differs is who
    declared the secret and whether this leaf is the one claiming it.

    ** The repair

    So determination is not a property of a matrix.  It is a property
    of a matrix *together with a claim*: the set of secrets this leaf
    is asserting it pins down.  [determines mat cl] says no incidence
    solution is nonzero anywhere the claim reaches; slack outside the
    claim is abstention, not degeneracy.

    The claim is an input, and the two settings supply it differently.
    An instance off the wire declares its own scalars, so the claim is
    everything and [determines_full_iff_trivial_kernel] recovers the
    original criterion unchanged.  A compiled leaf claims the secrets
    it actually mentions, so the claim is its live columns, and
    [live_claim_ignores_dead_columns] is why the Helios branches pass.

    Both are instances of one definition.  That is the whole repair:
    not a weaker criterion, but a criterion that had an argument
    missing. *)
Section Claim.

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

  #[local] Notation incidence_zeroC := (@incidence_zero F zero add G gid Gdec).
  #[local] Notation wzeroC := (@wzero F zero).

  (** ** The claim

      A claim marks the positions whose secrets this leaf asserts it
      determines.  It is a vector of flags rather than a predicate so
      that it can be computed and compared. *)
  Definition claim (n : nat) : Type := Vector.t bool n.

  Definition full_claim (n : nat) : claim n := Vector.const true n.

  (** Every position carrying a base other than the neutral element
      somewhere: the secrets a compiled leaf actually mentions. *)
  Definition live_claim {m n : nat}
    (mat : Vector.t (Vector.t G n) m) : claim n :=
    Vector.map negb (@dead_columns G gid Gdec m n mat).

  (** ** Determination, relative to a claim *)
  Definition determines {m n : nat}
    (mat : Vector.t (Vector.t G n) m) (cl : claim n) : Prop :=
    ∀ v : Vector.t F n,
    incidence_zeroC mat v ->
    ∀ j : Fin.t n, Vector.nth cl j = true -> Vector.nth v j = zero.

  (** ** The full claim recovers the original criterion

      An instance that declares its own scalars claims all of them, so
      nothing changes for the setting Degeneracy.v was written
      against.  In particular a declared scalar appearing in no
      equation is still a defect. *)
  Theorem determines_full_iff_trivial_kernel :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m),
    determines mat (full_claim n) <->
    (∀ v : Vector.t F n, incidence_zeroC mat v -> v = wzeroC n).
  Proof.
    intros m n mat; unfold determines, full_claim; split.
    - intros hdet v hv.
      apply Vector.eq_nth_iff; intros p q hpq; subst q.
      unfold wzero; rewrite nth_const.
      apply hdet; [exact hv | apply nth_const].
    - intros htriv v hv j _.
      rewrite (htriv v hv); unfold wzero; apply nth_const.
  Qed.

  (** ** The live claim ignores what the leaf does not mention

      A compiled branch claims the secrets it mentions.  Slack
      confined to columns it never mentions is abstention, and this is
      the theorem that says so: such a solution cannot witness a
      failure of [determines] against the live claim. *)
  Lemma nth_live_claim :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (j : Fin.t n),
    Vector.nth (live_claim mat) j =
    negb (Vector.nth (@dead_columns G gid Gdec m n mat) j).
  Proof.
    intros m n mat j; unfold live_claim.
    rewrite (Vector.nth_map _ _ j j eq_refl); reflexivity.
  Qed.

  Theorem live_claim_ignores_dead_columns :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (j : Fin.t n),
    (∀ i : Fin.t m, Vector.nth (Vector.nth mat i) j = gid) ->
    Vector.nth (live_claim mat) j = false.
  Proof.
    intros m n mat j hdead.
    rewrite nth_live_claim, (proj2 (@dead_columns_spec G gid Gdec m n mat j) hdead).
    reflexivity.
  Qed.

  (** And the converse: a claimed position really is one the leaf
      mentions, so the claim is not hiding anything the matrix
      constrains. *)
  Theorem live_claim_is_mentioned :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (j : Fin.t n),
    Vector.nth (live_claim mat) j = true ->
    ∃ i : Fin.t m, Vector.nth (Vector.nth mat i) j <> gid.
  Proof.
    intros m n mat j hcl.
    rewrite nth_live_claim, Bool.negb_true_iff in hcl.
    exact (@dead_columns_false G gid Gdec m n mat j hcl).
  Qed.

  (** ** The two cases, now separated

      This is what the repair is for.  The same shape - a column of
      neutral bases - is a defect under one claim and abstention under
      another, and the two theorems below say so. *)

  (** Off the wire.  An instance declaring a scalar that appears in no
      equation claims to pin down something it does not constrain, and
      that is a defect however the matrix is read.  This is the
      standard's E1 control, and the verdict is unchanged. *)
  Theorem dead_column_breaks_full_claim :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (j : Fin.t n),
    (∀ i : Fin.t m, Vector.nth (Vector.nth mat i) j = gid) ->
    ~ determines mat (full_claim n).
  Proof.
    intros m n mat j hdead hdet.
    (* the solution concentrated at [j] is nonzero exactly there *)
    pose proof (@dead_column_incidence F zero one add mul sub div opp inv
                  G gid ginv gop gpow Gdec Hvec m n mat j one hdead) as hinc.
    assert (hone : Vector.nth (wpoint j one) j = zero)
      by (apply hdet; [exact hinc | unfold full_claim; apply nth_const]).
    rewrite nth_wpoint_same in hone.
    exact (@zero_neq_one F (@eq F) zero one _ (eq_sym hone)).
  Qed.

  (** A compiled branch.  The shape every Helios ballot produces: two
      equations in the branch's own secret, and a column standing in
      for the other branch's secret that this branch never mentions.
      Under the live claim it is determined, which is the verdict the
      6524-proof corpus should have returned. *)
  Definition branch_mat (g h : G) : Vector.t (Vector.t G 2) 2 :=
    [[g; gid]; [h; gid]].

  Theorem branch_claim_is_first_column :
    ∀ (g h : G), g <> gid -> h <> gid ->
    Vector.nth (live_claim (branch_mat g h)) Fin.F1 = true ∧
    Vector.nth (live_claim (branch_mat g h)) (Fin.FS Fin.F1) = false.
  Proof.
    intros g h hg hh; split.
    - rewrite nth_live_claim, Bool.negb_true_iff.
      destruct (Vector.nth (@dead_columns G gid Gdec 2 2 (branch_mat g h))
                  Fin.F1) eqn:he; [exfalso | reflexivity].
      exact (hg (proj1 (@dead_columns_spec G gid Gdec 2 2 (branch_mat g h)
                          Fin.F1) he Fin.F1)).
    - apply live_claim_ignores_dead_columns.
      apply fin2_cases; cbn; reflexivity.
  Qed.

  Theorem branch_determines_what_it_claims :
    ∀ (g h : G), g <> gid -> h <> gid ->
    determines (branch_mat g h) (live_claim (branch_mat g h)).
  Proof.
    intros g h hg hh v hv j hcl.
    destruct (branch_claim_is_first_column g h hg hh) as (h0 & h1).
    (* only the first column is claimed *)
    revert hcl; pattern j; revert j; apply fin2_cases; intro hcl.
    - (* the base [g] sits at exactly one position of the first row, so
         that row's incidence equation reads [v_0 = 0] *)
      assert (hone : ∀ j' : Fin.t 2, j' <> Fin.F1 ->
                Vector.nth (Vector.nth (branch_mat g h) Fin.F1) j' =
                Vector.nth (Vector.nth (branch_mat g h) Fin.F1) Fin.F1 ->
                Vector.nth v j' = zero).
      { intro j'; pattern j'; revert j'; apply fin2_cases; cbn.
        - intros hne _; exfalso; exact (hne eq_refl).
        - intros _ hbad; exfalso; exact (hg (eq_sym hbad)). }
      pose proof (@sum_at_singleton F zero one add mul sub div opp inv
                    G gid ginv gop gpow Gdec Hvec 2
                    (Vector.nth (branch_mat g h) Fin.F1) v Fin.F1 hone) as hs.
      rewrite <- hs.
      apply hv; cbn; exact hg.
    - rewrite h1 in hcl; discriminate hcl.
  Qed.

End Claim.
