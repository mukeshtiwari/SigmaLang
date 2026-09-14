From Stdlib Require Import Setoid
  setoid_ring.Field Lia Arith Vector Utf8
  Psatz Bool Pnat BinNatDef BinPos List.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import Util.
From Compiler Require Import LinearRelation LeafValidity Degeneracy
  IncidenceDecide Claim.

Import VectorNotations.

(** * Certifying that a statement does determine what it claims

    Rejection has had a certificate since IncidenceDecide.v: a nonzero
    solution of the incidence system, checked in linear time, is a
    second witness beside every first one.  Acceptance has had only a
    sufficient test - a row whose bases are pairwise distinct and none
    neutral - and beyond it the checker declined to speak.

    That gap is not engineering.  The theory says determination is
    decidable, a rank computation over the field, and then decides a
    fragment.  Everywhere else the development says where the line is
    and proves it; here it stopped.  This file closes it.

    ** The certificate

    An incidence equation says that the exponents under one base of
    one row sum to zero.  A linear combination of those equations is
    again a linear form in the witness, and if some combination equals
    the form that reads off position [j], then every solution vanishes
    at [j].  That combination is the certificate, and checking it is a
    matrix multiplication and a comparison - no linear algebra needs
    to be trusted or verified.

    Coefficients are indexed by a row and a position in that row: the
    pair names the equation for that row and the base sitting there.
    A coefficient on a neutral base would name no equation, so the
    combination masks those to zero rather than asking the checker to
    rule them out.

    ** What it buys

    The search is free to be anything.  Gaussian elimination already
    computes the combination as a by-product of row reduction, and
    nothing about that elimination is proven; it emits the
    coefficients and [determined_by_certificate] checks them.  An
    undecided verdict then means only that no search was run or it
    found nothing, never that the checker cannot tell. *)
Section Determined.

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

  #[local] Notation sum_atC := (@sum_at F zero add G Gdec).
  #[local] Notation incidence_zeroC := (@incidence_zero F zero add G gid Gdec).
  #[local] Notation wzeroC := (@wzero F zero).
  #[local] Notation waddC := (@wadd F add).
  #[local] Notation wpointC := (@wpoint F zero).

  (** ** Linear forms in the witness

      [dot w v] is the form with coefficients [w] evaluated at [v].
      Every incidence equation is one of these, and so is every
      combination of them. *)
  Definition dot {n : nat} (w v : Vector.t F n) : F :=
    Vector.fold_right add (zip_with mul w v) zero.

  Definition wscale {n : nat} (c : F) (w : Vector.t F n) : Vector.t F n :=
    Vector.map (mul c) w.

  (** The form belonging to one incidence equation: pick out the
      positions of [row] carrying the base [b]. *)
  Definition mask {n : nat} (b : G) (row : Vector.t G n) : Vector.t F n :=
    Vector.map (fun x => if Gdec x b then one else zero) row.

  Lemma dot_cons :
    ∀ (n : nat) (a b : F) (w v : Vector.t F n),
    dot (a :: w) (b :: v) = add (mul a b) (dot w v).
  Proof.
    intros *; unfold dot; rewrite zip_with_cons; cbn; reflexivity.
  Qed.

  Lemma dot_wzero :
    ∀ (n : nat) (v : Vector.t F n), dot (wzeroC n) v = zero.
  Proof.
    induction n as [| n ih]; intro v.
    - rewrite (vector_inv_0 v); unfold dot, wzero; cbn; reflexivity.
    - destruct (vector_inv_S v) as (a & v' & hv); subst v.
      replace (wzeroC (S n)) with (zero :: wzeroC n) by reflexivity.
      rewrite dot_cons, ih; field.
  Qed.

  Lemma dot_add :
    ∀ (n : nat) (w1 w2 v : Vector.t F n),
    dot (waddC w1 w2) v = add (dot w1 v) (dot w2 v).
  Proof.
    induction n as [| n ih]; intros w1 w2 v.
    - rewrite (vector_inv_0 w1), (vector_inv_0 w2), (vector_inv_0 v).
      unfold dot, wadd; cbn; field.
    - destruct (vector_inv_S w1) as (a & w1' & h1).
      destruct (vector_inv_S w2) as (b & w2' & h2).
      destruct (vector_inv_S v) as (c & v' & hv).
      subst.
      unfold wadd; rewrite zip_with_cons, !dot_cons.
      fold (waddC w1' w2'); rewrite ih; field.
  Qed.

  Lemma dot_scale :
    ∀ (n : nat) (c : F) (w v : Vector.t F n),
    dot (wscale c w) v = mul c (dot w v).
  Proof.
    induction n as [| n ih]; intros c w v.
    - rewrite (vector_inv_0 w), (vector_inv_0 v).
      unfold dot, wscale; cbn; field.
    - destruct (vector_inv_S w) as (a & w' & hw).
      destruct (vector_inv_S v) as (b & v' & hv).
      subst.
      unfold wscale; cbn [Vector.map]; rewrite !dot_cons.
      fold (wscale c w'); rewrite ih; field.
  Qed.

  (** Reading off one position is itself a linear form. *)
  Lemma dot_wpoint :
    ∀ (n : nat) (j : Fin.t n) (v : Vector.t F n),
    dot (wpointC j one) v = Vector.nth v j.
  Proof.
    intros n j.
    induction j as [p | p j ih]; intro v;
      destruct (vector_inv_S v) as (a & v' & hv); subst v;
      cbn [wpoint Vector.nth Vector.caseS].
    - rewrite dot_cons, dot_wzero;
        ring.
    - rewrite dot_cons, ih;
        (* [field] and [ring] both balk at the zero product here *)
        rewrite ring_mul_0_l, left_identity; reflexivity.
  Qed.

  (** The bridge: the form of an incidence equation evaluates to that
      equation's incidence sum. *)
  Lemma dot_mask :
    ∀ (n : nat) (row : Vector.t G n) (v : Vector.t F n) (b : G),
    dot (mask b row) v = sum_atC row v b.
  Proof.
    induction n as [| n ih]; intros row v b.
    - rewrite (vector_inv_0 row), (vector_inv_0 v); reflexivity.
    - destruct (vector_inv_S row) as (c & row' & hrow).
      destruct (vector_inv_S v) as (a & v' & hv).
      subst.
      unfold mask; cbn [Vector.map]; rewrite dot_cons.
      fold (mask b row'); rewrite ih, sum_at_cons.
      destruct (Gdec c b); field.
  Qed.

  (** ** Combining incidence equations

      A coefficient is attached to a row and a position in it, naming
      the equation for the base sitting there.  A neutral base names
      no equation, so its coefficient is discarded here rather than
      being ruled out by a side condition the checker would have to
      test. *)
  Definition contrib {n : nat} (row : Vector.t G n) (p : F * G)
    : Vector.t F n :=
    wscale (if Gdec (snd p) gid then zero else fst p) (mask (snd p) row).

  Definition combo_row {n : nat}
    (row : Vector.t G n) (cs : Vector.t F n) : Vector.t F n :=
    Vector.fold_right (fun p acc => waddC (contrib row p) acc)
      (zip_with (fun c b => (c, b)) cs row) (wzeroC n).

  Definition combo {m n : nat} (mat : Vector.t (Vector.t G n) m)
    (C : Vector.t (Vector.t F n) m) : Vector.t F n :=
    Vector.fold_right (fun p acc => waddC (combo_row (fst p) (snd p)) acc)
      (zip_with (fun r c => (r, c)) mat C) (wzeroC n).

  (** Any combination of one row's equations vanishes on any solution
      of that row's incidence system. *)
  Lemma dot_contrib_fold :
    ∀ (n : nat) (row : Vector.t G n) (v : Vector.t F n)
      (k : nat) (ps : Vector.t (F * G) k),
    (∀ b : G, b <> gid -> sum_atC row v b = zero) ->
    dot (Vector.fold_right (fun p acc => waddC (contrib row p) acc)
           ps (wzeroC n)) v = zero.
  Proof.
    intros n row v k ps hsum.
    induction ps as [| p k ps ih]; cbn [Vector.fold_right].
    - apply dot_wzero.
    - rewrite dot_add, ih.
      unfold contrib; rewrite dot_scale, dot_mask.
      destruct (Gdec (snd p) gid) as [_ | hne].
      + rewrite ring_mul_0_l, left_identity; reflexivity.
      + rewrite (hsum (snd p) hne), ring_mul_0_r, left_identity; reflexivity.
  Qed.

  Lemma dot_combo_row :
    ∀ (n : nat) (row : Vector.t G n) (cs v : Vector.t F n),
    (∀ b : G, b <> gid -> sum_atC row v b = zero) ->
    dot (combo_row row cs) v = zero.
  Proof.
    intros n row cs v hsum; unfold combo_row.
    apply dot_contrib_fold; exact hsum.
  Qed.

  Lemma dot_combo_fold :
    ∀ (n k : nat) (v : Vector.t F n)
      (qs : Vector.t (Vector.t G n * Vector.t F n) k),
    (∀ (i : Fin.t k) (b : G), b <> gid ->
       sum_atC (fst (Vector.nth qs i)) v b = zero) ->
    dot (Vector.fold_right (fun p acc => waddC (combo_row (fst p) (snd p)) acc)
           qs (wzeroC n)) v = zero.
  Proof.
    intros n k v qs; induction qs as [| q k qs ih]; intro hall;
      cbn [Vector.fold_right].
    - apply dot_wzero.
    - rewrite dot_add.
      rewrite (dot_combo_row n (fst q) (snd q) v)
        by (intros b hb; exact (hall Fin.F1 b hb)).
      rewrite ih by (intros i b hb; exact (hall (Fin.FS i) b hb)).
      apply left_identity.
  Qed.

  Theorem dot_combo :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m)
      (C : Vector.t (Vector.t F n) m) (v : Vector.t F n),
    incidence_zeroC mat v -> dot (combo mat C) v = zero.
  Proof.
    intros m n mat C v hv; unfold combo.
    apply dot_combo_fold.
    intros i b hb; rewrite nth_zip_with; cbn [fst].
    exact (hv i b hb).
  Qed.

  (** ** The certificate

      One combination per claimed position, each equal to the form
      that reads off that position.  Checking it is a matrix
      multiplication and a comparison; the search that produced the
      coefficients is not trusted and need not be verified. *)
  Theorem determined_by_certificate :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m)
      (cl : claim n) (C : Fin.t n -> Vector.t (Vector.t F n) m),
    (∀ j : Fin.t n, Vector.nth cl j = true ->
       combo mat (C j) = wpointC j one) ->
    @determines F zero add G gid Gdec m n mat cl.
  Proof.
    intros m n mat cl C hcert v hv j hcl.
    rewrite <- (dot_wpoint n j v), <- (hcert j hcl).
    exact (dot_combo m n mat (C j) v hv).
  Qed.

  (** ** Checking a certificate

      The certificate is one coefficient block per position.  Checking
      it compares each claimed block's combination against the form
      that reads off that position, which is one row of the identity;
      [ident] builds those rows so that the comparison needs no index
      arithmetic. *)
  Fixpoint vec_eqb {n : nat} : Vector.t F n -> Vector.t F n -> bool :=
    match n with
    | O => fun _ _ => true
    | S n' => fun u w =>
        andb (if Fdec (Vector.hd u) (Vector.hd w) then true else false)
             (vec_eqb (Vector.tl u) (Vector.tl w))
    end.

  Lemma vec_eqb_sound :
    ∀ (n : nat) (u w : Vector.t F n), vec_eqb u w = true -> u = w.
  Proof.
    induction n as [| n ih]; intros u w hb.
    - rewrite (vector_inv_0 u), (vector_inv_0 w); reflexivity.
    - destruct (vector_inv_S u) as (a & u' & hu).
      destruct (vector_inv_S w) as (b & w' & hw).
      subst; cbn in hb.
      apply Bool.andb_true_iff in hb as (hh & ht).
      destruct (Fdec a b) as [heq | _]; [| discriminate hh].
      rewrite heq, (ih u' w' ht); reflexivity.
  Qed.

  Fixpoint ident (n : nat) : Vector.t (Vector.t F n) n :=
    match n with
    | O => []
    | S n' => (one :: wzeroC n') ::
              Vector.map (fun r => zero :: r) (ident n')
    end.

  Lemma nth_ident :
    ∀ (n : nat) (j : Fin.t n), Vector.nth (ident n) j = wpointC j one.
  Proof.
    intros n j; induction j as [p | p j ih];
      cbn [ident wpoint Vector.nth Vector.caseS Nat.pred].
    - reflexivity.
    - rewrite (Vector.nth_map _ _ j j eq_refl), ih; reflexivity.
  Qed.

  Definition certificate (m n : nat) : Type :=
    Vector.t (Vector.t (Vector.t F n) m) n.

  Definition combo_checkb {m n : nat}
    (mat : Vector.t (Vector.t G n) m) (cl : claim n)
    (cs : certificate m n) : bool :=
    List.forallb
      (fun t : bool * (Vector.t (Vector.t F n) m * Vector.t F n) =>
         if fst t then vec_eqb (combo mat (fst (snd t))) (snd (snd t))
         else true)
      (Vector.to_list
         (zip_with (fun (b : bool) (p : Vector.t (Vector.t F n) m * Vector.t F n)
                    => (b, p)) cl
            (zip_with (fun (c : Vector.t (Vector.t F n) m) (e : Vector.t F n)
                       => (c, e)) cs (ident n)))).

  (** A checked certificate is a proof that the statement determines
      what it claims.  Nothing about the search that produced the
      coefficients is trusted or verified. *)
  Theorem combo_checkb_sound :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (cl : claim n)
      (cs : certificate m n),
    combo_checkb mat cl cs = true ->
    @determines F zero add G gid Gdec m n mat cl.
  Proof.
    intros m n mat cl cs hb.
    apply (determined_by_certificate m n mat cl (fun j => Vector.nth cs j)).
    intros j hcl.
    unfold combo_checkb in hb.
    rewrite (forallb_to_list_nth _ _ n _) in hb.
    specialize (hb j); rewrite !nth_zip_with in hb; cbn [fst snd] in hb.
    rewrite hcl in hb.
    rewrite <- (nth_ident n j).
    exact (vec_eqb_sound n _ _ hb).
  Qed.

End Determined.
