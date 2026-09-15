From Stdlib Require Import Setoid Lia Vector Utf8 Bool List
  setoid_ring.Ring setoid_ring.Ring_theory.
From Utility Require Import Util.

Import VectorNotations.

(** * Pure pairing products pin down nothing

    [Character.v] shows that one degree above the linear case no exact
    criterion exists. The obvious hope is that the failure is an
    artefact of full quadratic systems and that the bilinear ones a
    pairing gives -- secrets split into two blocks, one per source
    group -- are better behaved. [Bipartite.v] shows they are not, as
    soon as an equation may carry linear terms.

    This module closes the other side. Forbid the linear terms, so that
    every equation is a pure product

      sum_{i,j} gamma_ij x_i y_j = tau,

    which is what a pairing-product equation reads as in the exponents.
    Then determination is decidable, trivially, and the answer is
    always no: such a system never pins down its witness. The reason is
    a symmetry the pairing itself supplies, since
    [e(g1^(l x), g2^(y/l)) = e(g1^x, g2^y)], so scaling one block up and
    the other down carries solutions to solutions.

    Together with [Bipartite.v] this leaves no useful class above the
    linear one. Pure products are decidable and vacuous; add the linear
    terms that real protocols need and the quadratic obstruction is
    back. *)

Section Bilinear.

  (** A field, in the form the argument uses it: a commutative ring
      with no zero divisors, inverses for the nonzero elements, and at
      least three elements, so that some scalar is neither zero nor
      one. The last is genuinely needed -- over the two-element field
      the scaling symmetry below is the identity. *)
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
  Hypothesis inverses : ∀ x : A, x <> a0 -> ∃ y : A, amul x y = a1.
  Hypothesis three_elements : ∃ l : A, l <> a0 ∧ l <> a1.

  (** ** Ring facts, named

      As in [Switch.v]: [ring] discharges these when every leaf is a
      variable but not once a leaf is a vector lookup. The two modules
      keep separate copies because they work under different
      hypotheses -- [Switch.v] needs only a domain, and sharing would
      force a field on it. *)

  Lemma add_0_l : ∀ x : A, aadd a0 x = x.
  Proof. intro x; ring. Qed.

  Lemma mul_0_l : ∀ x : A, amul a0 x = a0.
  Proof. intro x; ring. Qed.

  Lemma mul_0_r : ∀ x : A, amul x a0 = a0.
  Proof. intro x; ring. Qed.

  Lemma mul_1_l : ∀ x : A, amul a1 x = x.
  Proof. intro x; ring. Qed.

  Lemma scalar_fixes_only_zero :
    ∀ (l x : A), l <> a1 -> amul l x = x -> x = a0.
  Proof.
    intros l x hl h.
    assert (hfac : amul (asub l a1) x = a0)
      by (replace (amul (asub l a1) x) with (asub (amul l x) x) by ring;
          rewrite h; ring).
    destruct (no_zero_divisors _ _ hfac) as [hz | hz].
    + exfalso; apply hl.
      replace l with (aadd (asub l a1) a1) by ring; rewrite hz; ring.
    + exact hz.
  Qed.

  (** ** Linear and bilinear forms *)

  Definition dotm {k : nat} (w v : Vector.t A k) : A :=
    Vector.fold_right aadd (zip_with amul w v) a0.

  Definition scale {k : nat} (l : A) (v : Vector.t A k) : Vector.t A k :=
    Vector.map (amul l) v.

  Lemma dotm_cons :
    ∀ (k : nat) (c x : A) (w v : Vector.t A k),
    dotm (c :: w) (x :: v) = aadd (amul c x) (dotm w v).
  Proof. intros *; reflexivity. Qed.

  Lemma dotm_zero_l :
    ∀ (k : nat) (v : Vector.t A k), dotm (Vector.const a0 k) v = a0.
  Proof.
    induction k as [| k ih]; intro v.
    + rewrite (vector_inv_0 v); unfold dotm; cbn; reflexivity.
    + destruct (vector_inv_S v) as (x & v' & hv); subst.
      change (Vector.const a0 (S k)) with (a0 :: Vector.const a0 k).
      rewrite dotm_cons, mul_0_l, ih; apply add_0_l.
  Qed.

  Lemma dotm_scale_l :
    ∀ (k : nat) (l : A) (w v : Vector.t A k),
    dotm (scale l w) v = amul l (dotm w v).
  Proof.
    induction k as [| k ih]; intros l w v.
    + rewrite (vector_inv_0 w), (vector_inv_0 v).
      unfold dotm, scale; cbn; rewrite mul_0_r; reflexivity.
    + destruct (vector_inv_S w) as (c & w' & hw).
      destruct (vector_inv_S v) as (x & v' & hv); subst.
      unfold scale in ih |- *; cbn [Vector.map].
      rewrite !dotm_cons, ih; ring.
  Qed.

  Lemma dotm_scale_r :
    ∀ (k : nat) (l : A) (w v : Vector.t A k),
    dotm w (scale l v) = amul l (dotm w v).
  Proof.
    induction k as [| k ih]; intros l w v.
    + rewrite (vector_inv_0 w), (vector_inv_0 v).
      unfold dotm, scale; cbn; rewrite mul_0_r; reflexivity.
    + destruct (vector_inv_S w) as (c & w' & hw).
      destruct (vector_inv_S v) as (x & v' & hv); subst.
      unfold scale in ih |- *; cbn [Vector.map].
      rewrite !dotm_cons, ih; ring.
  Qed.

  (** The number of secrets in each source group. Only the second
      block has to be nonempty, and only in the degenerate case where
      the first collapses. *)
  Context (m n0 : nat).

  Notation n := (S n0).

  (** A pure pairing-product equation: a coefficient for each pair of
      secrets, one from each block, and a target. No linear term, which
      is exactly the restriction this module is about. *)
  Record ppe : Type :=
    mkppe { p_g : Vector.t (Vector.t A n) m ; p_t : A }.

  Definition bil (g : Vector.t (Vector.t A n) m)
    (X : Vector.t A m) (Y : Vector.t A n) : A :=
    dotm X (Vector.map (fun r => dotm r Y) g).

  Definition psat (e : ppe) (w : Vector.t A m * Vector.t A n) : Prop :=
    bil (p_g e) (fst w) (snd w) = p_t e.

  Definition PSol (s : list ppe) (w : Vector.t A m * Vector.t A n) : Prop :=
    List.Forall (fun e => psat e w) s.

  Definition determined (s : list ppe) : Prop :=
    ∃ w : Vector.t A m * Vector.t A n,
      PSol s w ∧ ∀ w' : Vector.t A m * Vector.t A n, PSol s w' -> w' = w.

  (** ** The symmetry

      Scaling the first block by [l] and the second by [r] scales every
      pure product by [l * r]. With [r] the inverse of [l] the equations
      are untouched, which is the pairing's own
      [e(g1^(l x), g2^(y/l)) = e(g1^x, g2^y)] written in the
      exponents. *)

  Lemma map_dotm_scale :
    ∀ (q : nat) (g : Vector.t (Vector.t A n) q) (r : A) (Y : Vector.t A n),
    Vector.map (fun row => dotm row (scale r Y)) g =
    scale r (Vector.map (fun row => dotm row Y) g).
  Proof.
    induction q as [| q ih]; intros g r Y.
    + rewrite (vector_inv_0 g); reflexivity.
    + destruct (vector_inv_S g) as (row & g' & hg); subst.
      cbn [Vector.map].
      rewrite dotm_scale_r, ih.
      unfold scale; cbn [Vector.map]; reflexivity.
  Qed.

  Lemma bil_scale :
    ∀ (g : Vector.t (Vector.t A n) m) (l r : A)
      (X : Vector.t A m) (Y : Vector.t A n),
    bil g (scale l X) (scale r Y) = amul (amul l r) (bil g X Y).
  Proof.
    intros g l r X Y; unfold bil.
    rewrite map_dotm_scale, dotm_scale_l, dotm_scale_r; ring.
  Qed.

  Theorem scaling_preserves_solutions :
    ∀ (s : list ppe) (l r : A) (w : Vector.t A m * Vector.t A n),
    amul l r = a1 -> PSol s w -> PSol s (scale l (fst w), scale r (snd w)).
  Proof.
    intros s l r w hlr; apply List.Forall_impl; intros e he.
    unfold psat in *; cbn [fst snd].
    rewrite bil_scale, hlr, mul_1_l; exact he.
  Qed.

  (** ** A collapsed first block leaves the second free *)

  Lemma bil_zero_l :
    ∀ (g : Vector.t (Vector.t A n) m) (Y : Vector.t A n),
    bil g (Vector.const a0 m) Y = a0.
  Proof. intros g Y; unfold bil; apply dotm_zero_l. Qed.

  Lemma const_neq :
    Vector.const a0 n <> Vector.const a1 n.
  Proof.
    intro h; apply one_neq_zero.
    apply (f_equal (fun v => Vector.nth v Fin.F1)) in h.
    rewrite !Vector.const_nth in h; exact (eq_sym h).
  Qed.

  (** ** Nothing is ever pinned down

      Either the system has no solution, or it has one whose first
      block is zero -- and then every second block is a solution -- or
      it has one whose first block is not, and then scaling produces a
      different one. *)

  Theorem pure_products_never_determine :
    ∀ s : list ppe, ¬ determined s.
  Proof.
    intros s (w & hw & hu).
    destruct three_elements as (l & hl0 & hl1).
    destruct (inverses l hl0) as (r & hlr).
    (* the scaled solution must be the solution, so the first block is
       fixed by a scalar that is not one, hence zero *)
    pose proof (hu _ (scaling_preserves_solutions s l r w hlr hw)) as heq.
    assert (hX : scale l (fst w) = fst w) by exact (f_equal fst heq).
    assert (hzero : fst w = Vector.const a0 m).
    { apply Vector.eq_nth_iff; intros p q hpq; subst q.
      rewrite Vector.const_nth.
      unfold scale in hX.
      apply (f_equal (fun v => Vector.nth v p)) in hX; cbn in hX.
      rewrite (Vector.nth_map _ (fst w) p p eq_refl) in hX.
      exact (scalar_fixes_only_zero l _ hl1 hX). }
    (* with the first block zero every target is zero, and then the
       second block is unconstrained *)
    assert (htargets : ∀ e : ppe, List.In e s -> p_t e = a0).
    { unfold PSol in hw; rewrite List.Forall_forall in hw.
      intros e he; specialize (hw e he); unfold psat in hw.
      rewrite hzero, bil_zero_l in hw; exact (eq_sym hw). }
    assert (hs0 : PSol s (Vector.const a0 m, Vector.const a0 n)).
    { unfold PSol; apply List.Forall_forall; intros e he;
        unfold psat; cbn [fst snd].
      rewrite bil_zero_l; exact (eq_sym (htargets e he)). }
    assert (hs1 : PSol s (Vector.const a0 m, Vector.const a1 n)).
    { unfold PSol; apply List.Forall_forall; intros e he;
        unfold psat; cbn [fst snd].
      rewrite bil_zero_l; exact (eq_sym (htargets e he)). }
    pose proof (hu _ hs0) as h0; pose proof (hu _ hs1) as h1.
    rewrite <- h0 in h1.
    apply const_neq; exact (eq_sym (f_equal snd h1)).
  Qed.

End Bilinear.
