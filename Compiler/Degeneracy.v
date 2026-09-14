From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef BinPos List.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import Util.
From Compiler Require Import LinearRelation LeafValidity.

Import VectorNotations.

(** * What a leaf can fail to prove, and how much of that is visible

    LeafValidity.v rejects two shapes of leaf: one with a dead column,
    and one whose targets are all neutral.  Both were found by running
    against the negative controls of the CFRG sigma-protocol draft,
    which is to say by accident, and neither came with an argument
    that the list was finished.  This file supplies the argument, and
    in supplying it finds a third shape that neither our checker nor
    the draft rejects.

    ** The question, made precise

    A leaf says [mat_eval mat xs = pub].  Two different things can go
    wrong with it, and only one of them admits a complete answer.

    The first is that the statement may fail to *determine* its
    witness: two different vectors both satisfy it, so a proof of
    knowledge establishes knowledge of neither.  This is the axis a
    checker can be complete on, and the rest of this file is about
    why.

    The second is that the statement may be *vacuous* or
    *unsatisfiable*: [pub] may lie at the neutral element, where the
    all-zero witness works, or outside the image, where nothing works.
    Deciding membership in the image is the discrete logarithm
    problem, so no structural checker is complete here, and
    LeafValidity.v's second condition is a necessity result with no
    converse.  Vacuity.v carries what can be said on that axis.

    ** Why the first axis closes

    [mat_eval mat] is a group homomorphism from the additive group of
    witnesses to [G^m].  So its fibres are cosets of its kernel, and
    "the statement determines the witness" is exactly "the kernel is
    trivial".  There is no third thing to look for: every way a leaf
    can fail to pin down its secret is a nonzero kernel vector.

    A checker cannot compute that kernel, because it depends on
    discrete logarithms among the bases.  What it can compute is the
    part of the kernel forced by the *pattern* of the matrix, and that
    part is the solution space of a linear system over [F] which this
    file calls the incidence system.  Its equations are indexed by a
    row and a base: for row [i] and base [g], the exponents sitting
    under the occurrences of [g] in row [i] must sum to zero.

    Two theorems bracket it.  [incidence_zero_in_kernel], here, says a
    solution of the incidence system is a kernel vector in *every*
    group, with no assumption whatever.  IncidenceComplete.v says the
    converse holds generically: a vector outside the incidence
    solution space fails to be a kernel vector in a specific group,
    the free module on the distinct bases, so no checker reading only
    the pattern could have rejected on its account.  Together the
    incidence system is exactly the structurally visible part of the
    kernel.

    ** What that buys

    A dead column is the incidence solution [e_j]; two equal columns
    give [e_j - e_k].  Both are in this file as corollaries.  The
    third shape is neither:

      mat = [[g, g, gid]; [gid, h, h]]

    has every column live and no two columns equal, so
    [leaf_validb] accepts it and so does the draft's validation, yet
    the incidence system reads [x1 + x2 = 0] and [x2 + x3 = 0] and is
    solved by [(1, -1, 1)].  The statement fixes [x1 + x2] and
    [x2 + x3] and nothing more.  It appears below as
    [three_column_counterexample]. *)
Section Degeneracy.

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
  #[local] Infix "^" := gpow.

  (** Reducing [zip_with] one position at a time.  It is defined by
      well-founded recursion on the first vector, so the computation
      rule is worth having as a rewrite. *)
  Lemma zip_with_cons :
    ∀ (P T U : Type) (f : P -> T -> U) (n : nat)
      (a : P) (b : T) (u : Vector.t P n) (v : Vector.t T n),
    zip_with f (a :: u) (b :: v) = f a b :: zip_with f u v.
  Proof. intros; cbn; reflexivity. Qed.

  (** The two facts about the neutral element that every collapse
      below uses: it absorbs every exponent, and every base raised to
      zero reaches it.  Stated locally so that rewriting can find the
      vector-space instance without search. *)
  Lemma gpow_zero : ∀ g : G, g ^ zero = gid.
  Proof. intro g; exact (vector_space_field_zero (vector_space := Hvec) g). Qed.

  Lemma gpow_gid : ∀ x : F, gid ^ x = gid.
  Proof. intro x; exact (Vector_space.vid_identity (Hvec := Hvec) x). Qed.

  (** Every position of a constant vector holds that constant. *)
  Lemma nth_const :
    ∀ (A : Type) (a : A) (n : nat) (j : Fin.t n),
    Vector.nth (Vector.const a n) j = a.
  Proof.
    intros A a n j; induction j as [k | k j ih]; cbn; [reflexivity | exact ih].
  Qed.

  (** ** Witness arithmetic

      Witnesses are vectors over the field, and the only operation on
      them this file needs is addition, done position by position. *)
  Definition wadd {n : nat} (x y : Vector.t F n) : Vector.t F n :=
    zip_with add x y.

  Definition wzero (n : nat) : Vector.t F n := Vector.const zero n.

  (** ** The evaluation map is a homomorphism

      Everything in this file rests on this one fact.  A base raised
      to a sum of exponents is the product of the two powers, so a
      whole row evaluated at a sum of witnesses is the product of the
      two evaluations, and a whole matrix likewise. *)
  Lemma row_eval_add :
    ∀ (n : nat) (row : Vector.t G n) (x y : Vector.t F n),
    row_evalC row (wadd x y) = gop (row_evalC row x) (row_evalC row y).
  Proof.
    induction n as [| n ih]; intros row x y.
    - rewrite (vector_inv_0 row), (vector_inv_0 x), (vector_inv_0 y).
      unfold wadd, row_eval; cbn.
      rewrite left_identity; reflexivity.
    - destruct (vector_inv_S row) as (g & row' & hrow).
      destruct (vector_inv_S x) as (a & x' & hx).
      destruct (vector_inv_S y) as (b & y' & hy).
      subst.
      unfold wadd in ih |- *.
      rewrite zip_with_cons, !row_eval_cons, ih.
      rewrite smul_distributive_fadd.
      apply gop_simp.
  Qed.

  Lemma mat_eval_add :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (x y : Vector.t F n),
    mat_evalC mat (wadd x y) =
    zip_with gop (mat_evalC mat x) (mat_evalC mat y).
  Proof.
    intros m n mat x y.
    apply Vector.eq_nth_iff; intros p q hpq; subst q.
    unfold mat_eval.
    rewrite nth_zip_with, !(Vector.nth_map _ _ p p eq_refl).
    apply row_eval_add.
  Qed.

  (** ** The kernel, and why it is the whole story

      A witness lies in the kernel when the system sends it to the
      all-neutral vector.  Adding a kernel vector to a solution gives
      another solution, so a nonzero kernel vector is exactly a way
      for the statement to leave its secret undetermined. *)
  Definition in_kernel {m n : nat}
    (mat : Vector.t (Vector.t G n) m) (v : Vector.t F n) : Prop :=
    mat_evalC mat v = Vector.const gid m.

  Lemma kernel_shifts_witness :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m)
      (pub : Vector.t G m) (x v : Vector.t F n),
    in_kernel mat v -> mat_evalC mat x = pub ->
    mat_evalC mat (wadd x v) = pub.
  Proof.
    intros m n mat pub x v hker hx.
    subst pub.
    rewrite mat_eval_add.
    apply Vector.eq_nth_iff; intros p q hpq; subst q.
    rewrite nth_zip_with.
    unfold in_kernel in hker.
    (* rewriting the whole vector would drag in functional
       extensionality, so read off the one entry that is needed *)
    assert (hp : Vector.nth (mat_evalC mat v) p = gid)
      by (rewrite hker; apply nth_const).
    rewrite hp.
    apply right_identity.
  Qed.
  (** Adding a nonzero vector really does move the witness, so the
      two solutions above are genuinely different. *)
  Lemma wadd_nonzero_moves :
    ∀ (n : nat) (x v : Vector.t F n),
    v <> wzero n -> wadd x v <> x.
  Proof.
    intros n x v hv hbad.
    apply hv.
    apply Vector.eq_nth_iff; intros p q hpq; subst q.
    unfold wzero; rewrite nth_const.
    assert (h : Vector.nth (wadd x v) p = Vector.nth x p)
      by (rewrite hbad; reflexivity).
    unfold wadd in h; rewrite nth_zip_with in h.
    (* [a + b = a] in a field forces [b = zero] *)
    assert (hz : add (Vector.nth x p) (Vector.nth v p)
                 = add (Vector.nth x p) zero)
      by (rewrite h; field).
    revert hz.
    generalize (Vector.nth x p) (Vector.nth v p); intros a b hz.
    assert (hfin : b = zero) by (apply (f_equal (fun t => sub t a)) in hz; field_simplify in hz; exact hz).
    exact hfin.
  Qed.

  (** ** Vectors supported at a single position

      The degeneracies below are all exhibited by kernel vectors with
      one or two nonzero entries, so it pays to have such vectors and
      their behaviour under [sum_at] once and for all. *)
  Fixpoint wpoint {n : nat} (j : Fin.t n) (a : F) : Vector.t F n :=
    match j in Fin.t n' return Vector.t F n' with
    | Fin.F1 => a :: wzero _
    | Fin.FS j' => zero :: wpoint j' a
    end.

  Lemma nth_wpoint_same :
    ∀ (n : nat) (j : Fin.t n) (a : F), Vector.nth (wpoint j a) j = a.
  Proof.
    intros n j a; induction j as [k | k j ih]; cbn; [reflexivity | exact ih].
  Qed.

  Lemma nth_wpoint_other :
    ∀ (n : nat) (j k : Fin.t n) (a : F),
    k <> j -> Vector.nth (wpoint j a) k = zero.
  Proof.
    intros n j; induction j as [p | p j ih]; intros k a hne.
    - revert hne; apply (Fin.caseS' k).
      + intro hne; exfalso; exact (hne eq_refl).
      + intros k' _; cbn; unfold wzero; apply nth_const.
    - revert hne; apply (Fin.caseS' k).
      + intros _; cbn; reflexivity.
      + intros k' hne; cbn; apply ih.
        intro heq; apply hne; rewrite heq; reflexivity.
  Qed.

  (** ** The incidence system

      [sum_at row v g] adds up the entries of [v] sitting under the
      occurrences of the base [g] in [row].  The incidence system of a
      matrix demands that every one of these sums vanish, for every
      row and every base other than the neutral one.

      The neutral base is excluded because it carries no information:
      [gid] raised to anything is [gid], so the exponents under a
      neutral base are unconstrained however they sum. *)
  Definition sum_at {n : nat}
    (row : Vector.t G n) (v : Vector.t F n) (g : G) : F :=
    Vector.fold_right add
      (zip_with (fun b a => if Gdec b g then a else zero) row v) zero.

  Definition incidence_zero {m n : nat}
    (mat : Vector.t (Vector.t G n) m) (v : Vector.t F n) : Prop :=
    ∀ (i : Fin.t m) (g : G), g <> gid -> sum_at (Vector.nth mat i) v g = zero.

  Lemma sum_at_cons :
    ∀ (n : nat) (b : G) (row : Vector.t G n) (a : F) (v : Vector.t F n) (g : G),
    sum_at (b :: row) (a :: v) g =
    add (if Gdec b g then a else zero) (sum_at row v g).
  Proof.
    intros *; unfold sum_at; rewrite zip_with_cons; cbn; reflexivity.
  Qed.

  (** The all-zero witness contributes nothing anywhere. *)
  Lemma sum_at_wzero :
    ∀ (n : nat) (row : Vector.t G n) (g : G), sum_at row (wzero n) g = zero.
  Proof.
    induction n as [| n ih]; intros row g.
    - rewrite (vector_inv_0 row); unfold sum_at, wzero; cbn; reflexivity.
    - destruct (vector_inv_S row) as (b & row' & hrow); subst row.
      replace (wzero (S n)) with (zero :: wzero n) by reflexivity.
      rewrite sum_at_cons, ih.
      destruct (Gdec b g); field.
  Qed.

  (** A vector supported at one position contributes its value to the
      sum at [g] exactly when the base under that position is [g].
      Every exhibited kernel vector below is built from these. *)
  Lemma sum_at_wpoint :
    ∀ (n : nat) (row : Vector.t G n) (j : Fin.t n) (a : F) (g : G),
    sum_at row (wpoint j a) g =
    if Gdec (Vector.nth row j) g then a else zero.
  Proof.
    intros n row j; revert row.
    induction j as [p | p j ih]; intros row a g.
    - destruct (vector_inv_S row) as (b & row' & hrow); subst row.
      cbn [wpoint]; rewrite sum_at_cons; cbn [Vector.nth Vector.caseS].
      rewrite sum_at_wzero.
      destruct (Gdec b g); field.
    - destruct (vector_inv_S row) as (b & row' & hrow); subst row.
      cbn [wpoint]; rewrite sum_at_cons, ih; cbn [Vector.nth Vector.caseS].
      (* the head of [wpoint (FS j) a] is zero, so it contributes nothing *)
      destruct (Gdec b g); apply left_identity.
  Qed.

  Lemma sum_at_add :
    ∀ (n : nat) (row : Vector.t G n) (v w : Vector.t F n) (g : G),
    sum_at row (wadd v w) g = add (sum_at row v g) (sum_at row w g).
  Proof.
    induction n as [| n ih]; intros row v w g.
    - rewrite (vector_inv_0 row), (vector_inv_0 v), (vector_inv_0 w).
      unfold sum_at, wadd; cbn; field.
    - destruct (vector_inv_S row) as (b & row' & hrow).
      destruct (vector_inv_S v) as (a & v' & hv).
      destruct (vector_inv_S w) as (c & w' & hw).
      subst.
      unfold wadd in ih |- *; rewrite zip_with_cons.
      rewrite !sum_at_cons, ih.
      destruct (Gdec b g); field.
  Qed.

  (** ** Solutions of the incidence system are kernel vectors

      This is the theorem that makes the incidence system worth
      writing down, and it holds in every group with no assumption at
      all: if the exponents under each base sum to zero in every row,
      the whole product collapses to the neutral element.

      The proof factors the product one base at a time.  [mask_out]
      replaces every occurrence of a chosen base by the neutral
      element, so that [row_eval] of the masked row is the product of
      all the *other* factors, and [row_eval_factor_out] says the
      original product is the chosen base raised to its incidence sum,
      times that remainder.  When the incidence sum is zero the first
      factor disappears, and an induction over a list of bases
      covering the row removes them all. *)
  Definition mask_out {n : nat} (row : Vector.t G n) (g : G) : Vector.t G n :=
    Vector.map (fun b => if Gdec b g then gid else b) row.

  Lemma nth_mask_out :
    ∀ (n : nat) (row : Vector.t G n) (g : G) (j : Fin.t n),
    Vector.nth (mask_out row g) j =
    (if Gdec (Vector.nth row j) g then gid else Vector.nth row j).
  Proof.
    intros n row g j; unfold mask_out.
    rewrite (Vector.nth_map _ _ j j eq_refl); reflexivity.
  Qed.

  Lemma row_eval_factor_out :
    ∀ (n : nat) (row : Vector.t G n) (v : Vector.t F n) (g : G),
    row_evalC row v =
    gop (g ^ sum_at row v g) (row_evalC (mask_out row g) v).
  Proof.
    induction n as [| n ih]; intros row v g.
    - rewrite (vector_inv_0 row), (vector_inv_0 v).
      unfold sum_at, mask_out, row_eval; cbn.
      rewrite gpow_zero; symmetry; apply left_identity.
    - destruct (vector_inv_S row) as (b & row' & hrow).
      destruct (vector_inv_S v) as (a & v' & hv).
      subst.
      unfold mask_out; cbn [Vector.map].
      rewrite !row_eval_cons, sum_at_cons, (ih row' v' g).
      fold (mask_out row' g).
      destruct (Gdec b g) as [heq | hne].
      + subst b.
        rewrite gpow_gid, left_identity, smul_distributive_fadd.
        rewrite associative; reflexivity.
      + rewrite left_identity.
        rewrite !associative.
        setoid_rewrite commutative at 2; reflexivity.
  Qed.

  Lemma row_eval_all_gid :
    ∀ (n : nat) (row : Vector.t G n) (v : Vector.t F n),
    (∀ j : Fin.t n, Vector.nth row j = gid) -> row_evalC row v = gid.
  Proof.
    induction n as [| n ih]; intros row v hall.
    - apply row_eval_nil.
    - destruct (vector_inv_S row) as (b & row' & hrow).
      destruct (vector_inv_S v) as (a & v' & hv).
      subst.
      pose proof (hall Fin.F1) as hb; cbn in hb.
      rewrite row_eval_cons, ih.
      + rewrite hb, gpow_gid; apply left_identity.
      + intro j; exact (hall (Fin.FS j)).
  Qed.

  (** Two bases that mark the same positions give the same incidence
      sum.  [mask_out] only moves positions to the neutral element, so
      it leaves every other base's positions alone. *)
  Lemma sum_at_ext :
    ∀ (n : nat) (r1 r2 : Vector.t G n) (v : Vector.t F n) (g : G),
    (∀ j : Fin.t n, Vector.nth r1 j = g <-> Vector.nth r2 j = g) ->
    sum_at r1 v g = sum_at r2 v g.
  Proof.
    induction n as [| n ih]; intros r1 r2 v g hiff.
    - rewrite (vector_inv_0 r1), (vector_inv_0 r2); reflexivity.
    - destruct (vector_inv_S r1) as (b1 & r1' & h1).
      destruct (vector_inv_S r2) as (b2 & r2' & h2).
      destruct (vector_inv_S v) as (a & v' & hv).
      subst.
      rewrite !sum_at_cons, (ih r1' r2' v' g)
        by (intro j; exact (hiff (Fin.FS j))).
      pose proof (hiff Fin.F1) as hhead; cbn in hhead.
      destruct (Gdec b1 g) as [e1 | n1], (Gdec b2 g) as [e2 | n2];
        try reflexivity.
      + exfalso; exact (n2 (proj1 hhead e1)).
      + exfalso; exact (n1 (proj2 hhead e2)).
  Qed.

  Lemma sum_at_absent :
    ∀ (n : nat) (row : Vector.t G n) (v : Vector.t F n) (g : G),
    (∀ j : Fin.t n, Vector.nth row j <> g) -> sum_at row v g = zero.
  Proof.
    induction n as [| n ih]; intros row v g habs.
    - rewrite (vector_inv_0 row), (vector_inv_0 v); reflexivity.
    - destruct (vector_inv_S row) as (b & row' & hrow).
      destruct (vector_inv_S v) as (a & v' & hv).
      subst.
      rewrite sum_at_cons, (ih row' v' g)
        by (intro j; exact (habs (Fin.FS j))).
      pose proof (habs Fin.F1) as hhead; cbn in hhead.
      destruct (Gdec b g) as [e | _]; [exfalso; exact (hhead e) |].
      apply left_identity.
  Qed.

  Lemma sum_at_mask_out_same :
    ∀ (n : nat) (row : Vector.t G n) (v : Vector.t F n) (g : G),
    g <> gid -> sum_at (mask_out row g) v g = zero.
  Proof.
    intros n row v g hg.
    apply sum_at_absent; intro j.
    rewrite nth_mask_out.
    destruct (Gdec (Vector.nth row j) g) as [_ | hne].
    - intro hbad; exact (hg (eq_sym hbad)).
    - exact hne.
  Qed.

  Lemma sum_at_mask_out_other :
    ∀ (n : nat) (row : Vector.t G n) (v : Vector.t F n) (g h : G),
    h <> g -> h <> gid -> sum_at (mask_out row g) v h = sum_at row v h.
  Proof.
    intros n row v g h hhg hhgid.
    apply sum_at_ext; intro j.
    rewrite nth_mask_out.
    destruct (Gdec (Vector.nth row j) g) as [heq | hne]; split.
    - intro hbad; exfalso; exact (hhgid (eq_sym hbad)).
    - intro hbad; exfalso; apply hhg; rewrite <- hbad; exact heq.
    - intro h1; exact h1.
    - intro h1; exact h1.
  Qed.

  (** Every entry of a vector appears in its list form, and every
      element of the list form is an entry.  The first supplies the
      covering list in the theorem below; the second is what lets a
      list-shaped boolean test be read back as a statement about
      positions, which IncidenceDecide.v needs.  Both are stated for
      an arbitrary element type because they are used at [G] and at
      vectors over [G]. *)
  Lemma in_to_list :
    ∀ (A : Type) (n : nat) (w : Vector.t A n) (j : Fin.t n),
    List.In (Vector.nth w j) (Vector.to_list w).
  Proof.
    intros A n w j; revert w.
    induction j as [p | p j ih]; intros w;
      destruct (vector_inv_S w) as (b & w' & hw); subst w;
      rewrite Vector.to_list_cons; cbn.
    - left; reflexivity.
    - right; exact (ih w').
  Qed.

  Lemma in_to_list_inv :
    ∀ (A : Type) (n : nat) (w : Vector.t A n) (a : A),
    List.In a (Vector.to_list w) -> ∃ j : Fin.t n, Vector.nth w j = a.
  Proof.
    intros A n; induction n as [| n ih]; intros w a hin.
    - rewrite (vector_inv_0 w) in hin; cbn in hin; contradiction.
    - destruct (vector_inv_S w) as (b & w' & hw); subst w.
      rewrite Vector.to_list_cons in hin.
      destruct hin as [heq | hin].
      + exists Fin.F1; cbn; exact heq.
      + destruct (ih w' a hin) as (j & hj).
        exists (Fin.FS j); cbn; exact hj.
  Qed.

  Lemma row_eval_incidence_zero_aux :
    ∀ (syms : list G) (n : nat) (row : Vector.t G n) (v : Vector.t F n),
    (∀ j : Fin.t n, Vector.nth row j <> gid ->
                    List.In (Vector.nth row j) syms) ->
    (∀ h : G, h <> gid -> sum_at row v h = zero) ->
    row_evalC row v = gid.
  Proof.
    induction syms as [| g syms ih]; intros n row v hcover hsum.
    - (* nothing left to cover with, so every base is neutral *)
      apply row_eval_all_gid; intro j.
      destruct (Gdec (Vector.nth row j) gid) as [heq | hne];
        [exact heq | destruct (hcover j hne)].
    - destruct (Gdec g gid) as [hgid | hg].
      + (* the neutral base constrains nothing, so drop it *)
        subst g; apply (ih n row v); [| exact hsum].
        intros j hj; destruct (hcover j hj) as [heq | hin];
          [exfalso; exact (hj (eq_sym heq)) | exact hin].
      + (* peel off [g]: its incidence sum is zero, so it contributes
           the neutral element and disappears *)
        rewrite (row_eval_factor_out n row v g), (hsum g hg).
        rewrite gpow_zero, left_identity.
        apply (ih n (mask_out row g) v).
        * intros j hj; rewrite nth_mask_out in hj |- *.
          destruct (Gdec (Vector.nth row j) g) as [heq | hne];
            [exfalso; exact (hj eq_refl) |].
          destruct (hcover j hj) as [heqg | hin];
            [exfalso; exact (hne (eq_sym heqg)) | exact hin].
        * intros h hh.
          destruct (Gdec h g) as [heq | hne].
          -- subst h; apply sum_at_mask_out_same; exact hg.
          -- rewrite sum_at_mask_out_other by assumption; exact (hsum h hh).
  Qed.

  Theorem row_eval_incidence_zero :
    ∀ (n : nat) (row : Vector.t G n) (v : Vector.t F n),
    (∀ h : G, h <> gid -> sum_at row v h = zero) ->
    row_evalC row v = gid.
  Proof.
    intros n row v hsum.
    apply (row_eval_incidence_zero_aux (Vector.to_list row) n row v);
      [intros j _; apply in_to_list | exact hsum].
  Qed.

  (** The theorem the file is built around: a solution of the
      incidence system lies in the kernel, in every group, with no
      assumption on the bases. *)
  Theorem incidence_zero_in_kernel :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (v : Vector.t F n),
    incidence_zero mat v -> in_kernel mat v.
  Proof.
    intros m n mat v hinc.
    unfold in_kernel, mat_eval.
    apply Vector.eq_nth_iff; intros p q hpq; subst q.
    rewrite (Vector.nth_map _ _ p p eq_refl), nth_const.
    apply row_eval_incidence_zero.
    intros h hh; exact (hinc p h hh).
  Qed.

  (** ** What a solution of the incidence system costs the statement

      A nonzero solution is a second witness sitting beside every
      first one.  The statement therefore constrains the secret but
      does not pin it down, and a proof of knowledge for it proves
      knowledge of a coset rather than of a value. *)
  Theorem incidence_solution_breaks_determination :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m)
      (v x : Vector.t F n),
    incidence_zero mat v -> v <> wzero n -> mat_evalC mat x = pub ->
    ∃ y : Vector.t F n, mat_evalC mat y = pub ∧ y <> x.
  Proof.
    intros m n mat pub v x hinc hnz hx.
    exists (wadd x v); split.
    - apply (kernel_shifts_witness m n mat pub x v);
        [apply incidence_zero_in_kernel; exact hinc | exact hx].
    - apply wadd_nonzero_moves; exact hnz.
  Qed.

  (** ** The two conditions of LeafValidity.v, as incidence solutions

      Both degeneracies that file rejects are solutions of the
      incidence system, which is what it means to say the incidence
      criterion generalises them.  A dead column gives the solution
      supported at that column alone. *)
  Theorem dead_column_incidence :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (j : Fin.t n) (a : F),
    (∀ i : Fin.t m, Vector.nth (Vector.nth mat i) j = gid) ->
    incidence_zero mat (wpoint j a).
  Proof.
    intros m n mat j a hdead i g hg.
    rewrite sum_at_wpoint, hdead.
    destruct (Gdec gid g) as [heq | _];
      [exfalso; exact (hg (eq_sym heq)) | reflexivity].
  Qed.

  (** Two columns that agree in every row give the solution that adds
      one to the first secret and subtracts it from the second.  This
      degeneracy is invisible to [leaf_validb], and to the instance
      validation of the CFRG draft. *)
  Theorem equal_columns_incidence :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (j k : Fin.t n),
    (∀ i : Fin.t m,
       Vector.nth (Vector.nth mat i) j = Vector.nth (Vector.nth mat i) k) ->
    incidence_zero mat (wadd (wpoint j one) (wpoint k (opp one))).
  Proof.
    intros m n mat j k heq i g hg.
    rewrite sum_at_add, !sum_at_wpoint, (heq i).
    destruct (Gdec (Vector.nth (Vector.nth mat i) k) g); field.
  Qed.

  (** ** Nonzero solutions

      A solution only says something when it is not the zero vector,
      so each exhibited solution comes with its own proof. *)
  Lemma wpoint_nonzero :
    ∀ (n : nat) (j : Fin.t n) (a : F), a <> zero -> wpoint j a <> wzero n.
  Proof.
    intros n j a ha hbad; apply ha.
    rewrite <- (nth_wpoint_same n j a), hbad.
    unfold wzero; apply nth_const.
  Qed.

  Lemma two_point_nonzero :
    ∀ (n : nat) (j k : Fin.t n) (a b : F),
    j <> k -> a <> zero -> wadd (wpoint j a) (wpoint k b) <> wzero n.
  Proof.
    intros n j k a b hjk ha hbad; apply ha.
    assert (hj : Vector.nth (wadd (wpoint j a) (wpoint k b)) j
                 = Vector.nth (wzero n) j) by (rewrite hbad; reflexivity).
    unfold wadd in hj; rewrite nth_zip_with, nth_wpoint_same in hj.
    rewrite (nth_wpoint_other n k j b) in hj by exact hjk.
    unfold wzero in hj; rewrite nth_const in hj.
    rewrite <- hj; field.
  Qed.

  (** ** A leaf that everybody accepts and nobody should

      This is the shape the incidence criterion finds and the two
      conditions of LeafValidity.v do not.  Every column is live, so
      the first condition passes; every target is off the neutral
      element, so the second passes; no two columns are equal, so the
      generalisation to equal columns would not catch it either.  The
      CFRG draft's instance validation accepts it for the same
      reasons.

      Yet its incidence system reads [x1 + x2 = 0] and [x2 + x3 = 0],
      and [(1, -1, 1)] solves it.  The statement fixes [x1 + x2] and
      [x2 + x3]; the three secrets themselves are free along a line. *)
  (** Case analysis on the small index types the example uses.
      Written as lemmas rather than with [destruct], which cannot
      generalise the width of a matrix literal. *)
  Lemma fin1_is_F1 : ∀ j : Fin.t 1, j = Fin.F1.
  Proof.
    intro j; apply (Fin.caseS' j); [reflexivity | intro j1; inversion j1].
  Qed.

  Lemma fin2_cases :
    ∀ (P : Fin.t 2 -> Prop),
    P Fin.F1 -> P (Fin.FS Fin.F1) -> ∀ i : Fin.t 2, P i.
  Proof.
    intros P h0 h1 i.
    apply (Fin.caseS' i); [exact h0 |].
    intro i1; apply (Fin.caseS' i1); [exact h1 | intro i2; inversion i2].
  Qed.

  Lemma fin3_cases :
    ∀ (P : Fin.t 3 -> Prop),
    P Fin.F1 -> P (Fin.FS Fin.F1) -> P (Fin.FS (Fin.FS Fin.F1)) ->
    ∀ j : Fin.t 3, P j.
  Proof.
    intros P h0 h1 h2 j.
    apply (Fin.caseS' j); [exact h0 |].
    intro j1; apply (Fin.caseS' j1); [exact h1 |].
    intro j2; apply (Fin.caseS' j2); [exact h2 | intro j3; inversion j3].
  Qed.

  Definition tricky_mat (g h : G) : Vector.t (Vector.t G 3) 2 :=
    [[g; g; gid]; [gid; h; h]].

  Definition tricky_sol : Vector.t F 3 := [one; opp one; one].

  (** Every column carries a base other than the neutral element and
      every target is off it, so [leaf_validb] accepts. *)
  Theorem tricky_accepted :
    ∀ (g h P Q : G),
    g <> gid -> h <> gid -> P <> gid -> Q <> gid ->
    @leaf_validb G gid Gdec 2 3 (tricky_mat g h) [P; Q] = true.
  Proof.
    intros g h P Q hg hh hP hQ.
    apply leaf_validb_spec; split.
    - unfold column_live, tricky_mat; apply fin3_cases.
      + exists Fin.F1; cbn; exact hg.
      + exists Fin.F1; cbn; exact hg.
      + exists (Fin.FS Fin.F1); cbn; exact hh.
    - unfold target_live; apply fin2_cases; cbn; assumption.
  Qed.

  (** And no two columns agree in every row, so the generalisation to
      equal columns would not catch it either.  The three pairs are
      spelled out because there are only three. *)
  Theorem tricky_columns_distinct :
    ∀ (g h : G),
    g <> gid -> h <> gid ->
    Vector.nth (Vector.nth (tricky_mat g h) (Fin.FS Fin.F1)) Fin.F1
      <> Vector.nth (Vector.nth (tricky_mat g h) (Fin.FS Fin.F1))
                    (Fin.FS Fin.F1)
    ∧ Vector.nth (Vector.nth (tricky_mat g h) Fin.F1) (Fin.FS Fin.F1)
      <> Vector.nth (Vector.nth (tricky_mat g h) Fin.F1)
                    (Fin.FS (Fin.FS Fin.F1))
    ∧ Vector.nth (Vector.nth (tricky_mat g h) Fin.F1) Fin.F1
      <> Vector.nth (Vector.nth (tricky_mat g h) Fin.F1)
                    (Fin.FS (Fin.FS Fin.F1)).
  Proof.
    intros g h hg hh; unfold tricky_mat; cbn.
    repeat split; try exact hg.
    intro hbad; exact (hh (eq_sym hbad)).
  Qed.

  (** Its incidence system is [x1 + x2 = 0] and [x2 + x3 = 0], solved
      by [(1, -1, 1)]. *)
  Theorem tricky_incidence :
    ∀ (g h : G), incidence_zero (tricky_mat g h) tricky_sol.
  Proof.
    intros g h; unfold incidence_zero, tricky_mat, tricky_sol.
    apply (fin2_cases
             (fun i => ∀ g' : G, g' <> gid ->
                sum_at (Vector.nth [[g; g; gid]; [gid; h; h]] i)
                       [one; opp one; one] g' = zero));
      intros g' hg'; cbn [Vector.nth Vector.caseS];
      rewrite !sum_at_cons;
      destruct (Gdec gid g') as [he | _];
      try (exfalso; exact (hg' (eq_sym he))).
    - destruct (Gdec g g'); unfold sum_at; cbn; field.
    - destruct (Gdec h g'); unfold sum_at; cbn; field.
  Qed.

  Theorem tricky_sol_nonzero : tricky_sol <> wzero 3.
  Proof.
    intro hbad; unfold tricky_sol in hbad.
    assert (h1 : one = zero).
    { change one with
        (Vector.nth ([one; opp one; one] : Vector.t F 3) Fin.F1).
      rewrite hbad; unfold wzero; apply nth_const. }
    exact (@zero_neq_one F (@eq F) zero one _ (eq_sym h1)).
  Qed.

  (** Put together: a leaf our checker accepts, whose columns are all
      live and pairwise distinct, and which still fails to determine
      its witness. *)
  Corollary three_column_counterexample :
    ∀ (g h P Q : G),
    g <> gid -> h <> gid -> P <> gid -> Q <> gid ->
    ∀ x : Vector.t F 3,
    @leaf_validb G gid Gdec 2 3 (tricky_mat g h) [P; Q] = true ∧
    (mat_evalC (tricky_mat g h) x = [P; Q] ->
     ∃ y : Vector.t F 3, mat_evalC (tricky_mat g h) y = [P; Q] ∧ y <> x).
  Proof.
    intros g h P Q hg hh hP hQ x; split.
    - apply tricky_accepted; assumption.
    - intro hx.
      apply (incidence_solution_breaks_determination 2 3
               (tricky_mat g h) [P; Q] tricky_sol x);
        [apply tricky_incidence | apply tricky_sol_nonzero | exact hx].
  Qed.

End Degeneracy.
