From Stdlib Require Import Setoid Lia Vector Utf8 Bool List
  setoid_ring.Ring setoid_ring.Ring_theory.
From Utility Require Import Util.
From Compiler Require Import Degeneracy NoChecklist.

Import VectorNotations.

(** * Uniqueness of a rank-one solution reduces to unsatisfiability

    [Linear.v] and [Character.v] together say where an exact
    design-time criterion can exist. They say nothing about how hard
    the question is once the instance is in hand, and that is the
    second half of the separation: at degree one, determination is
    decided by a rank computation, in polynomial time, whatever the
    instance. This module shows that one degree up it is not decided
    in polynomial time at all unless P = NP.

    The reduction is a switch. Given a rank-one system [s] over
    variables [v], adjoin one fresh variable [z] and three kinds of
    constraint: [z * z = z], which confines [z] to the two idempotents
    of a domain; [z * v_j = v_j] for each [j], which collapses [v] when
    [z] is zero; and each original constraint with its constant term
    moved onto [z]. The extended system's solutions are then the origin
    together with the original solutions carried at [z = 1], so the
    extended system pins down its witness exactly when the original one
    had no solution at all.

    Since satisfiability of rank-one systems is NP-hard, deciding
    determination is coNP-hard. We prove the reduction correct here and
    leave the complexity classification, which is about machines rather
    than about algebra, to the prose.

    The constant-to-[z] move needs no new data: a linear form is
    coefficients plus a constant, and reading the constant as the
    coefficient of [z] is the identity on that representation. So
    [cstr] below is interpreted twice, by [cval] over the original
    variables and by [xval] over the extended ones, exactly as
    [Instantiate.v] reads one incidence system over names and over
    group elements. *)

Section Switch.

  (** A commutative ring with no zero divisors and a nontrivial unit.
      Both conditions are used once: the first to split [z * z = z]
      into its two roots, the second to tell the origin from the
      lifted solution. *)
  Context
    {A : Type}
    {a0 a1 : A}
    {aadd amul asub : A -> A -> A}
    {aopp : A -> A}.

  Hypothesis Arth : ring_theory a0 a1 aadd amul asub aopp (@eq A).
  Add Ring Aring : Arth.

  Hypothesis no_zero_divisors :
    ∀ x y : A, amul x y = a0 -> x = a0 ∨ y = a0.
  Hypothesis one_neq_zero : a1 <> a0.

  (** ** Ring facts, named

      [ring] discharges these on its own when every leaf is a variable,
      but not once a leaf is a vector lookup, so the identities are
      proved here on variables and rewritten with afterwards. *)

  Lemma add_0_l : ∀ x : A, aadd a0 x = x.
  Proof. intro x; ring. Qed.

  Lemma add_0_r : ∀ x : A, aadd x a0 = x.
  Proof. intro x; ring. Qed.

  Lemma mul_0_l : ∀ x : A, amul a0 x = a0.
  Proof. intro x; ring. Qed.

  Lemma mul_0_r : ∀ x : A, amul x a0 = a0.
  Proof. intro x; ring. Qed.

  Lemma mul_1_l : ∀ x : A, amul a1 x = x.
  Proof. intro x; ring. Qed.

  Lemma mul_1_r : ∀ x : A, amul x a1 = x.
  Proof. intro x; ring. Qed.

  (** The two arithmetic steps the switch needs: an idempotent of a
      domain is zero or one. *)

  Lemma idempotent_factor :
    ∀ z : A, amul z z = z -> amul z (asub z a1) = a0.
  Proof.
    intros z h.
    replace (amul z (asub z a1)) with (asub (amul z z) z) by ring.
    rewrite h; ring.
  Qed.

  Lemma sub_eq_zero : ∀ x y : A, asub x y = a0 -> x = y.
  Proof.
    intros x y h.
    replace x with (aadd (asub x y) y) by ring.
    rewrite h; ring.
  Qed.

  (** ** Linear forms

      [Determined.v] has a [dot] already, but it lives under a full
      vector space over a group, and there is no group here. The three
      facts needed below are short enough to prove directly. *)

  Definition dotm {m : nat} (w v : Vector.t A m) : A :=
    Vector.fold_right aadd (zip_with amul w v) a0.

  Lemma dotm_cons :
    ∀ (m : nat) (c x : A) (w v : Vector.t A m),
    dotm (c :: w) (x :: v) = aadd (amul c x) (dotm w v).
  Proof. intros *; reflexivity. Qed.

  Lemma dotm_zero_l :
    ∀ (m : nat) (v : Vector.t A m), dotm (Vector.const a0 m) v = a0.
  Proof.
    induction m as [| m ih]; intro v.
    + rewrite (vector_inv_0 v); unfold dotm; cbn; reflexivity.
    + destruct (vector_inv_S v) as (x & v' & hv); subst.
      change (Vector.const a0 (S m)) with (a0 :: Vector.const a0 m).
      rewrite dotm_cons, mul_0_l, ih; apply add_0_l.
  Qed.

  Lemma dotm_zero_r :
    ∀ (m : nat) (w : Vector.t A m), dotm w (Vector.const a0 m) = a0.
  Proof.
    induction m as [| m ih]; intro w.
    + rewrite (vector_inv_0 w); unfold dotm; cbn; reflexivity.
    + destruct (vector_inv_S w) as (c & w' & hw); subst.
      change (Vector.const a0 (S m)) with (a0 :: Vector.const a0 m).
      rewrite dotm_cons, mul_0_r, ih; apply add_0_l.
  Qed.

  Fixpoint basis (m : nat) (j : Fin.t m) {struct j} : Vector.t A m :=
    match j in Fin.t p return Vector.t A p with
    | @Fin.F1 q => a1 :: Vector.const a0 q
    | @Fin.FS q j' => a0 :: basis q j'
    end.

  Lemma dotm_basis :
    ∀ (m : nat) (j : Fin.t m) (v : Vector.t A m),
    dotm (basis m j) v = Vector.nth v j.
  Proof.
    intros m j; induction j as [p | p j ih]; intro v;
      destruct (vector_inv_S v) as (x & v' & hv); subst v;
      cbn [basis Vector.nth Vector.caseS].
    + rewrite dotm_cons, dotm_zero_l, mul_1_l; apply add_0_r.
    + rewrite dotm_cons, ih, mul_0_l; apply add_0_l.
  Qed.

  (** ** Rank-one systems, read twice

      [k] is the number of original variables. A form is coefficients
      on those variables plus one further scalar, and a constraint
      multiplies two forms and equates the product to a third -- which
      is what an arithmetic-circuit compiler emits. *)

  Context (k : nat).

  Record form : Type := mkform { f_c : Vector.t A k ; f_k : A }.
  Record cstr : Type := mkcstr { c_A : form ; c_B : form ; c_C : form }.

  (** The original reading: the further scalar is a constant term. *)
  Definition cval (f : form) (v : Vector.t A k) : A :=
    aadd (dotm (f_c f) v) (f_k f).

  Definition csat (c : cstr) (v : Vector.t A k) : Prop :=
    amul (cval (c_A c) v) (cval (c_B c) v) = cval (c_C c) v.

  Definition CSol (s : list cstr) (v : Vector.t A k) : Prop :=
    List.Forall (fun c => csat c v) s.

  (** The extended reading: the further scalar is the coefficient of
      the switch [z], and a witness carries [z] alongside [v]. *)
  Definition xval (f : form) (w : Vector.t A k * A) : A :=
    aadd (dotm (f_c f) (fst w)) (amul (f_k f) (snd w)).

  Definition xsat (c : cstr) (w : Vector.t A k * A) : Prop :=
    amul (xval (c_A c) w) (xval (c_B c) w) = xval (c_C c) w.

  Definition XSol (s : list cstr) (w : Vector.t A k * A) : Prop :=
    List.Forall (fun c => xsat c w) s.

  (** At [z = 1] the two readings agree: that is the whole reason the
      constant may be moved without changing what the system says. *)
  Lemma xval_at_one :
    ∀ (f : form) (v : Vector.t A k), xval f (v, a1) = cval f v.
  Proof. intros f v; unfold xval, cval; cbn [fst snd]; rewrite mul_1_r; reflexivity. Qed.

  (** ** The switch *)

  Definition zform : form := mkform (Vector.const a0 k) a1.
  Definition vform (j : Fin.t k) : form := mkform (basis k j) a0.

  Definition idempotent : cstr := mkcstr zform zform zform.
  Definition gate (j : Fin.t k) : cstr := mkcstr zform (vform j) (vform j).
  Definition gates : list cstr := List.map gate (Vector.to_list (all_fin k)).

  Definition extend (s : list cstr) : list cstr :=
    idempotent :: gates ++ s.

  Lemma xval_zform : ∀ w, xval zform w = snd w.
  Proof.
    intros w; unfold xval, zform; cbn [f_c f_k].
    rewrite dotm_zero_l, mul_1_l; apply add_0_l.
  Qed.

  Lemma xval_vform :
    ∀ (j : Fin.t k) (w : Vector.t A k * A),
    xval (vform j) w = Vector.nth (fst w) j.
  Proof.
    intros j w; unfold xval, vform; cbn [f_c f_k].
    rewrite dotm_basis, mul_0_l; apply add_0_r.
  Qed.

  (** ** The origin always solves the extended system *)

  Lemma xval_at_origin :
    ∀ f : form, xval f (Vector.const a0 k, a0) = a0.
  Proof.
    intros f; unfold xval; cbn [fst snd].
    rewrite dotm_zero_r, mul_0_r; apply add_0_l.
  Qed.

  Lemma origin_solves :
    ∀ s : list cstr, XSol (extend s) (Vector.const a0 k, a0).
  Proof.
    intros s; apply List.Forall_forall; intros c _; unfold xsat.
    rewrite !xval_at_origin; apply mul_0_l.
  Qed.

  (** ** Every original solution is carried up, at [z = 1] *)

  Lemma lifted_solves :
    ∀ (s : list cstr) (v : Vector.t A k),
    CSol s v -> XSol (extend s) (v, a1).
  Proof.
    intros s v hv; unfold extend; constructor; [| apply List.Forall_app; split].
    + unfold xsat; cbn [c_A c_B c_C idempotent].
      rewrite !xval_zform; cbn [fst snd]; apply mul_1_l.
    + apply List.Forall_forall; intros c hc.
      apply List.in_map_iff in hc as (j & hj & _); subst c.
      unfold xsat; cbn [c_A c_B c_C gate].
      rewrite xval_zform, !xval_vform; cbn [fst snd]; apply mul_1_l.
    + revert hv; apply List.Forall_impl; intros c hc.
      unfold xsat; rewrite !xval_at_one; exact hc.
  Qed.

  (** ** And there is nothing else

      The idempotent constraint leaves [z] at zero or one. At zero the
      gates flatten [v]; at one the original system is back. *)

  Lemma switch_is_binary :
    ∀ (s : list cstr) (w : Vector.t A k * A),
    XSol (extend s) w -> snd w = a0 ∨ snd w = a1.
  Proof.
    intros s w h.
    inversion h as [| c l hc _]; subst.
    unfold xsat in hc; cbn [c_A c_B c_C idempotent] in hc.
    rewrite !xval_zform in hc.
    destruct (no_zero_divisors _ _ (idempotent_factor _ hc)) as [hz | hz].
    + left; exact hz.
    + right; exact (sub_eq_zero _ _ hz).
  Qed.

  Lemma zero_switch_flattens :
    ∀ (s : list cstr) (w : Vector.t A k * A),
    XSol (extend s) w -> snd w = a0 -> fst w = Vector.const a0 k.
  Proof.
    intros s w h hz.
    inversion h as [| c l _ hrest]; subst.
    apply List.Forall_app in hrest as (hgates & _).
    apply Vector.eq_nth_iff; intros p q hpq; subst q.
    rewrite Vector.const_nth.
    assert (hp : xsat (gate p) w).
    { rewrite List.Forall_forall in hgates; apply hgates.
      apply List.in_map_iff; exists p; split; [reflexivity |].
      rewrite <- (nth_all_fin k p) at 1; apply in_to_list. }
    unfold xsat in hp; cbn [c_A c_B c_C gate] in hp.
    rewrite xval_zform, !xval_vform, hz, mul_0_l in hp.
    symmetry; exact hp.
  Qed.

  Lemma one_switch_restores :
    ∀ (s : list cstr) (w : Vector.t A k * A),
    XSol (extend s) w -> snd w = a1 -> CSol s (fst w).
  Proof.
    intros s w h hz.
    inversion h as [| c l _ hrest]; subst.
    apply List.Forall_app in hrest as (_ & horig).
    revert horig; apply List.Forall_impl; intros c hc.
    unfold csat; rewrite <- !xval_at_one.
    replace (fst w, a1) with w by (destruct w; cbn in hz; subst; reflexivity).
    exact hc.
  Qed.

  Theorem extended_solutions :
    ∀ (s : list cstr) (w : Vector.t A k * A),
    XSol (extend s) w ->
    w = (Vector.const a0 k, a0) ∨ (snd w = a1 ∧ CSol s (fst w)).
  Proof.
    intros s w h; destruct (switch_is_binary s w h) as [hz | hz].
    + left; destruct w as (v & z); cbn in hz; subst z.
      pose proof (zero_switch_flattens s _ h eq_refl) as hv; cbn in hv.
      rewrite hv; reflexivity.
    + right; split; [exact hz | exact (one_switch_restores s w h hz)].
  Qed.

  (** ** The reduction

      Determination of the extended system is unsatisfiability of the
      original one. Neither direction needs anything but the two
      readings and the fact that zero and one are different. *)

  Definition determined (s : list cstr) : Prop :=
    ∃ w : Vector.t A k * A,
      XSol s w ∧ ∀ w' : Vector.t A k * A, XSol s w' -> w' = w.

  Theorem uniqueness_is_unsatisfiability :
    ∀ s : list cstr,
    determined (extend s) <-> (∀ v : Vector.t A k, ¬ CSol s v).
  Proof.
    intros s; split.
    + intros (w & _ & hu) v hv.
      pose proof (hu _ (origin_solves s)) as horigin.
      pose proof (hu _ (lifted_solves s v hv)) as hlift.
      rewrite <- horigin in hlift.
      apply one_neq_zero.
      exact (f_equal snd hlift).
    + intros hunsat.
      exists (Vector.const a0 k, a0); split; [apply origin_solves |].
      intros w' hw'.
      destruct (extended_solutions s w' hw') as [-> | (_ & hsol)].
      - reflexivity.
      - exfalso; exact (hunsat _ hsol).
  Qed.

End Switch.
