From Stdlib Require Import Setoid Lia Vector Utf8 Bool List.
From Utility Require Import Util.
From Compiler Require Import LinearRelation LeafValidity Degeneracy Instantiate.
From Boundary Require Import Schema.

Import VectorNotations.

(** * Linear schemas are never sensitive

    [Schema.v] shows that an exact design-time criterion exists only
    where determination ignores the interpretation, and
    [Character.v] shows that one degree up it does not. This module
    supplies the other side: at degree one it does, so the criterion
    of the companion development is not merely sound but exact, and
    the two papers' results are the same statement with opposite
    signs.

    Nothing here is new mathematics. [Instantiate.v] already proves
    that a faithful environment leaves the incidence system's solutions
    alone, and everything below is that theorem read through the
    vocabulary of [Schema.v]: a constraint is a row of base names, an
    interpretation is the compiler's environment, and determination is
    triviality of the kernel because a homogeneous system always has
    the zero solution. Doing the translation is the point -- it is what
    lets the linear case and the quadratic case be compared at all. *)

Section Linear.

  Context
    {F : Type}
    {zero : F}
    {add : F -> F -> F}.

  Hypothesis add_zero_l : ∀ a : F, add zero a = a.

  Context
    {G : Type}
    {gid : G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}
    {B : Type}
    {bid : B}
    {Bdec : forall x y : B, {x = y} + {x <> y}}.

  (** The number of secrets is fixed: a witness has to live in one
      type for [Schema.v]'s definitions to apply, and a schema is then
      a list of rows over that many positions. *)
  Context (n : nat).

  Definition row : Type := Vector.t B n.
  Definition wit : Type := Vector.t F n.

  #[local] Notation sum_overG := (@sum_over F zero add G Gdec n).
  #[local] Notation sum_overB := (@sum_over F zero add B Bdec n).

  (** A row is satisfied at an environment when the instantiated row's
      incidence equations all vanish; read over names instead, the same
      row gives the statement's own equations. *)
  Definition lin_sat (e : B -> G) (r : row) (v : wit) : Prop :=
    ∀ g : G, g <> gid -> sum_overG (Vector.map e r) v g = zero.

  Definition name_sat (r : row) (v : wit) : Prop :=
    ∀ b : B, b <> bid -> sum_overB r v b = zero.

  (** Faithfulness, as the compiler checks it, row by row, plus the
      well-formedness condition that the absence marker instantiates to
      the identity. It depends on the schema, which is why
      [Schema.v] lets the side condition do so. *)
  Definition lin_faithful (e : B -> G) (s : list row) : Prop :=
    e bid = gid ∧ List.Forall (fun r => @faithful_row G gid B bid e n r) s.

  (** ** One row at a time

      [Instantiate.v] states the preservation theorem for a matrix. A
      single row is that theorem at one equation, and reading it that
      way is what makes it composable with [Schema.v]'s list-shaped
      schemas. *)

  Lemma incidence_single :
    ∀ (A : Type) (Adec : forall x y : A, {x = y} + {x <> y}) (aid : A)
      (r : Vector.t A n) (v : wit),
    @incidence F zero add A Adec aid 1 n [r] v <->
    (∀ a : A, a <> aid -> @sum_over F zero add A Adec n r v a = zero).
  Proof.
    intros A Adec aid r v; split; intro h.
    + intros a ha; exact (h Fin.F1 a ha).
    + intros i a ha.
      destruct (fin_inv_S 0 i) as [-> | (q & _)].
      - exact (h a ha).
      - exfalso; apply (fin_inv_0 q).
  Qed.

  Lemma faithful_row_preserves :
    ∀ (e : B -> G), e bid = gid ->
    ∀ (r : row) (v : wit),
    @faithful_row G gid B bid e n r ->
    (name_sat r v <-> lin_sat e r v).
  Proof.
    intros e hbid r v hf.
    pose proof
      (@faithful_preserves_incidence F zero add add_zero_l G gid Gdec B bid Bdec
         e hbid 1 n [r] v) as h.
    unfold name_sat, lin_sat.
    rewrite <- (incidence_single B Bdec bid r v),
            <- (incidence_single G Gdec gid (Vector.map e r) v).
    apply h; intros i.
    destruct (fin_inv_S 0 i) as [-> | (q & _)].
    + exact hf.
    + exfalso; apply (fin_inv_0 q).
  Qed.

  (** ** Solutions, at the names and at any faithful instance *)

  Lemma Sol_iff_names :
    ∀ (e : B -> G) (s : list row) (v : wit),
    lin_faithful e s ->
    (Sol lin_sat e s v <-> List.Forall (fun r => name_sat r v) s).
  Proof.
    intros e s v (hbid & hf); unfold Sol.
    induction s as [| r s ih].
    + split; intro; constructor.
    + inversion hf as [| r' s' hr hs]; subst.
      split; intro h; inversion h as [| c l hc ht]; subst; constructor.
      - exact (proj2 (faithful_row_preserves e hbid r v hr) hc).
      - exact (proj1 (ih hs) ht).
      - exact (proj1 (faithful_row_preserves e hbid r v hr) hc).
      - exact (proj2 (ih hs) ht).
  Qed.

  (** ** Determination is triviality of the kernel

      A homogeneous system always has the zero solution, so it
      determines exactly when it has no other. This is where the
      linear case gets its dichotomy cheaply: the witness is never in
      question, only its uniqueness. *)

  Lemma sum_over_const_zero :
    ∀ (A : Type) (Adec : forall x y : A, {x = y} + {x <> y})
      (m : nat) (r : Vector.t A m) (a : A),
    @sum_over F zero add A Adec m r (Vector.const zero m) a = zero.
  Proof.
    intros A Adec m; induction m as [| m ih]; intros r a.
    + rewrite (vector_inv_0 r); unfold sum_over; cbn; reflexivity.
    + destruct (vector_inv_S r) as (c & r' & hr); subst.
      change (Vector.const zero (S m))
        with (zero :: Vector.const zero m).
      rewrite sum_over_cons, ih.
      destruct (Adec c a); apply add_zero_l.
  Qed.

  Lemma zero_is_a_solution :
    ∀ (e : B -> G) (s : list row), Sol lin_sat e s (Vector.const zero n).
  Proof.
    intros e s; apply List.Forall_forall; intros r _ g _.
    apply sum_over_const_zero.
  Qed.

  Lemma determines_iff_trivial :
    ∀ (e : B -> G) (s : list row),
    determines lin_sat e s <->
    (∀ v : wit, Sol lin_sat e s v -> v = Vector.const zero n).
  Proof.
    intros e s; split.
    + intros (w & _ & hu) v hv.
      rewrite (hu v hv), <- (hu _ (zero_is_a_solution e s)); reflexivity.
    + intros h; exists (Vector.const zero n); split.
      - apply zero_is_a_solution.
      - exact h.
  Qed.

  (** ** The dichotomy

      Two faithful environments give the same solutions, because each
      gives the statement's own. So determination is settled by the
      names, and no interpretation can disagree with another. *)

  Theorem linear_determination_ignores_the_instance :
    ∀ (s : list row) (e1 e2 : B -> G),
    lin_faithful e1 s -> lin_faithful e2 s ->
    (determines lin_sat e1 s <-> determines lin_sat e2 s).
  Proof.
    intros s e1 e2 hf1 hf2.
    rewrite !determines_iff_trivial.
    split; intros h v hv; apply h, (Sol_iff_names _ s v);
      [ exact hf1 | apply (Sol_iff_names e2 s v hf2), hv
      | exact hf2 | apply (Sol_iff_names e1 s v hf1), hv ].
  Qed.

  (** And therefore no linear schema is of the kind that rules out a
      criterion. The companion development exhibits one that is exact;
      this says no obstruction to exactness can be found here, whatever
      criterion one tries. *)

  Theorem linear_schemas_are_never_sensitive :
    ∀ s : list row, ¬ interpretation_sensitive lin_sat lin_faithful s.
  Proof.
    intros s (e1 & e2 & hf1 & hf2 & hd1 & hd2).
    apply hd2, (linear_determination_ignores_the_instance s e1 e2 hf1 hf2), hd1.
  Qed.

End Linear.
