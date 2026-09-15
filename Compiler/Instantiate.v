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

(** * What instantiation can do to a statement

    [Degeneracy.v] and the modules above it answer a question about a
    *relation*: given a matrix of group elements, does it pin down the
    secrets it claims?  That question is settled there, and settled
    completely.

    This module is about the level above.  A statement is written over
    base *names* -- "g", "h", "M" -- and becomes a relation only once
    an environment sends each name to a group element.  The compiler
    calls that environment [genv].  Two statements with the same shape
    can compile to relations of quite different quality, because the
    environment is free to send two names to the same element, or a
    name to the identity, and the incidence system sees group
    elements, not names.

    So the question here is not "is this relation good" but "did
    instantiation preserve what the statement said".  The two results
    below answer it.  Neither is a new check: the incidence system is
    the same one, read once over names and once over group elements,
    and everything follows from comparing the two readings.

    The payoff is [statement_determines_every_faithful_instance]: a
    statement checked once, at design time, stays checked under every
    faithful instantiation.  The checker no longer has to run per
    instance. *)

Section Instantiation.

  (** The exponents need only add, commutatively.  Nothing here uses
      the field, the group operation or the action: [sum_over] adds
      exponents up, and bases are only ever compared for equality.
      That is not economy for its own sake -- it is what makes the two
      readings below comparable at all, since a statement's bases are
      names and names carry no group structure whatever. *)
  Context
    {F : Type}
    {zero : F}
    {add : F -> F -> F}.

  Hypothesis add_zero_l : ∀ a : F, add zero a = a.
  Hypothesis add_assoc : ∀ a b c : F, add a (add b c) = add (add a b) c.
  Hypothesis add_comm : ∀ a b : F, add a b = add b a.

  (** The instance's bases: group elements, with the identity
      distinguished because a neutral base constrains nothing. *)
  Context
    {G : Type}
    {gid : G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}.

  (** The statement's bases: names, with a marker for "this secret
      does not occur in this equation". *)
  Context
    {B : Type}
    {bid : B}
    {Bdec : forall x y : B, {x = y} + {x <> y}}.

  (** And the environment the compiler carries between them. *)
  Context (genv : B -> G).

  (** The one thing an environment must do: the absence marker has to
      instantiate to the identity, since that is how absence is
      written in a compiled matrix. *)
  Hypothesis genv_bid : genv bid = gid.

  (** ** The incidence system, read over any type of bases

      [Degeneracy.sum_at] and [Degeneracy.incidence_zero] never touch
      the group operation: they compare bases for equality and add up
      the exponents underneath.  So the same construction reads over a
      type of names as happily as over a type of group elements, and
      that is the whole reason the comparison below is possible. *)
  Definition sum_over {A : Type}
    (Adec : forall x y : A, {x = y} + {x <> y}) {n : nat}
    (row : Vector.t A n) (v : Vector.t F n) (a : A) : F :=
    Vector.fold_right add
      (zip_with (fun c x => if Adec c a then x else zero) row v) zero.

  Definition incidence {A : Type}
    (Adec : forall x y : A, {x = y} + {x <> y}) (aid : A) {m n : nat}
    (mat : Vector.t (Vector.t A n) m) (v : Vector.t F n) : Prop :=
    ∀ (i : Fin.t m) (a : A), a <> aid ->
      sum_over Adec (Vector.nth mat i) v a = zero.

  (** Read at the group, this is literally [Degeneracy]'s system. *)
  Lemma incidence_is_incidence_zero :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (v : Vector.t F n),
    incidence Gdec gid mat v <->
    @incidence_zero F zero add G gid Gdec m n mat v.
  Proof. intros *; split; intro h; exact h. Qed.

  (** *** Reading the sum one position at a time *)
  Lemma sum_over_cons :
    ∀ (A : Type) (Adec : forall x y : A, {x = y} + {x <> y}) (n : nat)
      (c : A) (row : Vector.t A n) (x : F) (v : Vector.t F n) (a : A),
    sum_over Adec (c :: row) (x :: v) a =
    add (if Adec c a then x else zero) (sum_over Adec row v a).
  Proof.
    intros *; unfold sum_over; rewrite zip_with_cons; cbn; reflexivity.
  Qed.

  (** A base that occurs nowhere in a row constrains nothing there.
      This is why the incidence system may skip the neutral base, and
      it is also what makes the comparison below total: a group element
      the instantiated row never mentions has an empty equation on both
      sides. *)
  Lemma sum_over_absent :
    ∀ (A : Type) (Adec : forall x y : A, {x = y} + {x <> y}) (n : nat)
      (row : Vector.t A n) (v : Vector.t F n) (a : A),
    (∀ j : Fin.t n, Vector.nth row j <> a) ->
    sum_over Adec row v a = zero.
  Proof.
    intros A Adec n; induction n as [| n ih]; intros row v a hj.
    - rewrite (vector_inv_0 row), (vector_inv_0 v).
      unfold sum_over; cbn; reflexivity.
    - destruct (vector_inv_S row) as (c & row' & hrow).
      destruct (vector_inv_S v) as (x & v' & hv); subst.
      rewrite sum_over_cons, ih.
      + destruct (Adec c a) as [he | _].
        * exfalso; apply (hj Fin.F1); cbn; exact he.
        * apply add_zero_l.
      + intros j; exact (hj (Fin.FS j)).
  Qed.

  (** Whether a base occurs in a row is decidable, which is what lets
      the comparison split into the two cases it needs. *)
  Lemma occurs_or_absent :
    ∀ (A : Type) (Adec : forall x y : A, {x = y} + {x <> y}) (n : nat)
      (row : Vector.t A n) (a : A),
    (∃ j : Fin.t n, Vector.nth row j = a) \/
    (∀ j : Fin.t n, Vector.nth row j <> a).
  Proof.
    intros A Adec n; induction n as [| n ih]; intros row a.
    - right; intros j; pattern j; revert j; apply Fin.case0.
    - destruct (vector_inv_S row) as (c & row' & hrow); subst.
      destruct (Adec c a) as [he | hne].
      + left; exists Fin.F1; cbn; exact he.
      + destruct (ih row' a) as [(j & hjj) | hnone].
        * left; exists (Fin.FS j); cbn; exact hjj.
        * right; intros j; pattern j; refine (Fin.caseS' j _ _ _); cbn.
          -- exact hne.
          -- intros k; exact (hnone k).
  Qed.

  (** ** Statements, environments and instances *)

  Definition inst {m n : nat} (mat : Vector.t (Vector.t B n) m)
    : Vector.t (Vector.t G n) m :=
    Vector.map (Vector.map genv) mat.

  (** *** The one comparison everything rests on

      Fix a name [b].  The instantiated row has an equation for the
      group element [genv b], and the statement's row has one for [b]
      itself.  They are the same equation exactly when [genv] does not
      drag any other name of the row onto [genv b] -- which is what the
      hypothesis says, and all it says.  No global injectivity is
      needed, and none would be reasonable to ask for: an environment
      sends every name it does not use to the identity. *)
  Lemma sum_over_map_agree :
    ∀ (n : nat) (row : Vector.t B n) (v : Vector.t F n) (b : B),
    (∀ j : Fin.t n,
       genv (Vector.nth row j) = genv b -> Vector.nth row j = b) ->
    sum_over Gdec (Vector.map genv row) v (genv b) =
    sum_over Bdec row v b.
  Proof.
    induction n as [| n ih]; intros row v b hsep.
    - rewrite (vector_inv_0 row), (vector_inv_0 v).
      unfold sum_over; cbn; reflexivity.
    - destruct (vector_inv_S row) as (c & row' & hrow).
      destruct (vector_inv_S v) as (x & v' & hv); subst.
      cbn [Vector.map]; rewrite !sum_over_cons, ih.
      + destruct (Gdec (genv c) (genv b)) as [he | hne];
        destruct (Bdec c b) as [hb | hnb].
        * reflexivity.
        * exfalso; apply hnb, (hsep Fin.F1); cbn; exact he.
        * exfalso; apply hne; cbn in hb; rewrite hb; reflexivity.
        * reflexivity.
      + intros j; exact (hsep (Fin.FS j)).
  Qed.

  (** ** Faithfulness

      An environment is faithful to a row when it keeps that row's
      names apart and keeps them off the identity.  Both halves are
      needed and neither implies the other: collapsing two names
      merges their equations, and sending a name to the identity
      deletes its equation. *)
  Definition faithful_row {n : nat} (row : Vector.t B n) : Prop :=
    (∀ j k : Fin.t n,
       genv (Vector.nth row j) = genv (Vector.nth row k) ->
       Vector.nth row j = Vector.nth row k)
    /\ (∀ j : Fin.t n,
          Vector.nth row j <> bid -> genv (Vector.nth row j) <> gid).

  Definition faithful {m n : nat} (mat : Vector.t (Vector.t B n) m)
    : Prop :=
    ∀ i : Fin.t m, faithful_row (Vector.nth mat i).

  (** *** Splitting an instantiated equation into the statement's

      When [genv] is not faithful, the instantiated row's equation for
      a group element [g] is not one of the statement's equations: it
      is the *sum* of all of them whose name lands on [g].  That is the
      only thing instantiation can do, and proving it is what makes the
      first theorem below true with no hypothesis on [genv] at all.

      The sum is indexed by a list of names rather than by a fibre, so
      that the induction has something finite to walk. *)

  (** A fold of zeros is zero. *)
  Lemma fold_zeros :
    ∀ (L : list B) (f : B -> F),
    (∀ b : B, List.In b L -> f b = zero) ->
    List.fold_right add zero (List.map f L) = zero.
  Proof.
    induction L as [| d L ih]; intros f hf; cbn.
    - reflexivity.
    - rewrite (hf d (or_introl eq_refl)), ih.
      + apply add_zero_l.
      + intros b hb; exact (hf b (or_intror hb)).
  Qed.

  (** Peeling one name off a fold, when the list mentions it once. *)
  Lemma fold_split_at :
    ∀ (L : list B) (c : B) (x : F) (g : G) (h : B -> F),
    List.NoDup L -> List.In c L ->
    List.fold_right add zero
      (List.map (fun b => if Gdec (genv b) g
                          then add (if Bdec c b then x else zero) (h b)
                          else zero) L) =
    add (if Gdec (genv c) g then x else zero)
        (List.fold_right add zero
           (List.map (fun b => if Gdec (genv b) g then h b else zero) L)).
  Proof.
    assert (hswap : forall a b c : F, add a (add b c) = add b (add a c))
      by (intros a b c;
          rewrite add_assoc, (add_comm a b), <- add_assoc; reflexivity).
    intros L; induction L as [| d L ih]; intros c x g h hnd hin.
    - destruct hin.
    - inversion hnd as [| d' L' hdl hndl heq]; subst; cbn in hin |- *.
      destruct hin as [hdc | hin].
      + (* the name being peeled is at the head, so it occurs nowhere
           in the tail and the two tails agree pointwise *)
        subst d.
        rewrite (List.map_ext_in
                   (fun b => if Gdec (genv b) g
                             then add (if Bdec c b then x else zero) (h b)
                             else zero)
                   (fun b => if Gdec (genv b) g then h b else zero) L).
        * destruct (Gdec (genv c) g) as [_ | _];
          destruct (Bdec c c) as [_ | hne];
          try (exfalso; apply hne; reflexivity).
          -- symmetry; apply add_assoc.
          -- rewrite !add_zero_l; reflexivity.
        * intros b hb.
          destruct (Bdec c b) as [hcb | _].
          -- exfalso; apply hdl; rewrite hcb; exact hb.
          -- destruct (Gdec (genv b) g);
             [rewrite add_zero_l; reflexivity | reflexivity].
      + rewrite (ih c x g h hndl hin).
        destruct (Bdec c d) as [hcd | _].
        * exfalso; apply hdl; rewrite <- hcd; exact hin.
        * destruct (Gdec (genv d) g) as [_ | _].
          -- rewrite add_zero_l; apply hswap.
          -- rewrite !add_zero_l; reflexivity.
  Qed.

  (** And so an instantiated equation is the sum of exactly those of
      the statement's equations whose name lands on the same group
      element.  [L] is any duplicate-free list naming every base the
      row uses. *)
  Lemma sum_over_map_merge :
    ∀ (n : nat) (row : Vector.t B n) (v : Vector.t F n) (g : G) (L : list B),
    List.NoDup L ->
    (∀ j : Fin.t n, List.In (Vector.nth row j) L) ->
    sum_over Gdec (Vector.map genv row) v g =
    List.fold_right add zero
      (List.map (fun b => if Gdec (genv b) g
                          then sum_over Bdec row v b else zero) L).
  Proof.
    induction n as [| n ih]; intros row v g L hnd hall.
    - rewrite (vector_inv_0 row), (vector_inv_0 v).
      symmetry; apply fold_zeros; intros b _.
      destruct (Gdec (genv b) g); unfold sum_over; cbn; reflexivity.
    - destruct (vector_inv_S row) as (c & row' & hrow).
      destruct (vector_inv_S v) as (x & v' & hv); subst.
      cbn [Vector.map]; rewrite sum_over_cons.
      rewrite (ih row' v' g L hnd (fun j => hall (Fin.FS j))).
      rewrite (List.map_ext
                 (fun b => if Gdec (genv b) g
                           then sum_over Bdec (c :: row') (x :: v') b
                           else zero)
                 (fun b => if Gdec (genv b) g
                           then add (if Bdec c b then x else zero)
                                    (sum_over Bdec row' v' b)
                           else zero)).
      + symmetry; apply fold_split_at.
        * exact hnd.
        * exact (hall Fin.F1).
      + intros b; rewrite sum_over_cons; reflexivity.
  Qed.

  (** ** Deciding faithfulness

      The split is worth making because the two halves cost different
      things.  Deciding that a statement determines its claim means
      building an incidence system and eliminating over the scalar
      field, which is where the certificates come from.  Deciding that
      an environment is faithful means comparing bases: no field
      arithmetic, no elimination, no certificate.  So the expensive
      half is paid once per statement and the cheap one once per
      instance, and the theorems below are what make that sound. *)

  (** Two names may share a group element only if they are the same
      name. *)
  Definition pair_okb (c1 c2 : B) : bool :=
    if Gdec (genv c1) (genv c2)
    then (if Bdec c1 c2 then true else false)
    else true.

  (** A name that is not the absence marker may not land on the
      identity. *)
  Definition live_okb (c : B) : bool :=
    if Bdec c bid then true
    else (if Gdec (genv c) gid then false else true).

  Definition row_faithfulb {n : nat} (row : Vector.t B n) : bool :=
    let l := Vector.to_list row in
    andb (List.forallb live_okb l)
         (List.forallb (fun c1 => List.forallb (pair_okb c1) l) l).

  Definition mat_faithfulb {m n : nat}
    (mat : Vector.t (Vector.t B n) m) : bool :=
    List.forallb row_faithfulb (Vector.to_list mat).

  Lemma row_faithfulb_sound :
    ∀ (n : nat) (row : Vector.t B n),
    row_faithfulb row = true -> faithful_row row.
  Proof.
    intros n row h; unfold row_faithfulb in h.
    apply andb_true_iff in h as (hlive & hpair); split.
    - intros j k hjk.
      pose proof (proj1 (List.forallb_forall _ _) hpair
                    (Vector.nth row j) (in_to_list _ _ row j)) as hj.
      pose proof (proj1 (List.forallb_forall _ _) hj
                    (Vector.nth row k) (in_to_list _ _ row k)) as hjk'.
      unfold pair_okb in hjk'.
      destruct (Gdec (genv (Vector.nth row j)) (genv (Vector.nth row k)))
        as [_ | hne]; [| exfalso; apply hne; exact hjk].
      destruct (Bdec (Vector.nth row j) (Vector.nth row k))
        as [he | _]; [exact he | discriminate].
    - intros j hj.
      pose proof (proj1 (List.forallb_forall _ _) hlive
                    (Vector.nth row j) (in_to_list _ _ row j)) as hl.
      unfold live_okb in hl.
      destruct (Bdec (Vector.nth row j) bid) as [he | _];
      [exfalso; apply hj; exact he |].
      destruct (Gdec (genv (Vector.nth row j)) gid) as [_ | hne];
      [discriminate | exact hne].
  Qed.

  (** The check a driver runs per instance. *)
  Lemma mat_faithfulb_sound :
    ∀ (m n : nat) (mat : Vector.t (Vector.t B n) m),
    mat_faithfulb mat = true -> faithful mat.
  Proof.
    intros m n mat h i; apply row_faithfulb_sound.
    exact (proj1 (List.forallb_forall _ _) h
             (Vector.nth mat i) (in_to_list _ _ mat i)).
  Qed.

  (** ** The two results *)

  (** Instantiation can only weaken: whatever solved the statement's
      incidence system still solves the instance's.  Nothing is
      assumed about [genv] beyond the marker convention. *)
  Theorem instantiation_monotone :
    ∀ (m n : nat) (mat : Vector.t (Vector.t B n) m) (v : Vector.t F n),
    incidence Bdec bid mat v -> incidence Gdec gid (inst mat) v.
  Proof.
    intros m n mat v hB i g hg.
    unfold inst; rewrite (Vector.nth_map _ mat i i eq_refl).
    rewrite (sum_over_map_merge n (Vector.nth mat i) v g
               (List.nodup Bdec (Vector.to_list (Vector.nth mat i)))).
    - (* every summand is one of the statement's equations, and the
         name carrying it cannot be the absent marker, since that
         instantiates to the identity and [g] is not the identity *)
      apply fold_zeros; intros b _.
      destruct (Gdec (genv b) g) as [he | _]; [| reflexivity].
      apply hB; intro hb; apply hg; rewrite <- he, hb; exact genv_bid.
    - apply List.NoDup_nodup.
    - intros j; apply (proj2 (List.nodup_In Bdec _ _)); apply in_to_list.
  Qed.

  (** A faithful environment changes nothing: the two systems have the
      same solutions. *)
  Theorem faithful_preserves_incidence :
    ∀ (m n : nat) (mat : Vector.t (Vector.t B n) m) (v : Vector.t F n),
    faithful mat ->
    (incidence Bdec bid mat v <-> incidence Gdec gid (inst mat) v).
  Proof.
    intros m n mat v hf; unfold inst; split.
    - intros hB i g hg.
      destruct (hf i) as (hinj & hnid).
      rewrite (Vector.nth_map _ mat i i eq_refl).
      destruct (occurs_or_absent G Gdec n
                  (Vector.map genv (Vector.nth mat i)) g) as [(j & hj) | habs].
      + (* [g] is the image of a name the row actually uses, so the two
           equations are the same equation *)
        rewrite (Vector.nth_map _ (Vector.nth mat i) j j eq_refl) in hj.
        rewrite <- hj, sum_over_map_agree.
        * apply hB; intro hb; apply hg; rewrite <- hj, hb; exact genv_bid.
        * intros k hk; apply hinj; exact hk.
      + (* the instantiated row never mentions [g] *)
        apply sum_over_absent; exact habs.
    - intros hG i b hb.
      destruct (hf i) as (hinj & hnid).
      destruct (occurs_or_absent B Bdec n (Vector.nth mat i) b)
        as [(j & hj) | habs].
      + rewrite <- sum_over_map_agree.
        * specialize (hG i (genv b)).
          rewrite (Vector.nth_map _ mat i i eq_refl) in hG.
          apply hG; rewrite <- hj; apply hnid; rewrite hj; exact hb.
        * intros k hk; rewrite <- hj in hk |- *; apply hinj; exact hk.
      + apply sum_over_absent; exact habs.
  Qed.

  (** The design-time checking theorem. *)
  Theorem statement_determines_every_faithful_instance :
    ∀ (m n : nat) (mat : Vector.t (Vector.t B n) m),
    faithful mat ->
    (∀ v : Vector.t F n, incidence Bdec bid mat v -> v = @wzero F zero n) ->
    (∀ v : Vector.t F n, incidence Gdec gid (inst mat) v -> v = @wzero F zero n).
  Proof.
    intros m n mat hf hstmt v hv.
    apply hstmt, (proj2 (faithful_preserves_incidence m n mat v hf)); exact hv.
  Qed.

  (** And the designer's contrapositive: a statement that is degenerate
      on its own names is degenerate however it is instantiated. *)
  Theorem degenerate_statement_stays_degenerate :
    ∀ (m n : nat) (mat : Vector.t (Vector.t B n) m) (v : Vector.t F n),
    incidence Bdec bid mat v -> v <> @wzero F zero n ->
    ∃ w : Vector.t F n, incidence Gdec gid (inst mat) w /\ w <> @wzero F zero n.
  Proof.
    intros m n mat v hv hnz.
    exists v; split; [apply instantiation_monotone; exact hv | exact hnz].
  Qed.

  (** The same statement in the checker's own vocabulary.  A claim
      names the secrets a statement asserts it pins down, and
      [Claim.determines] is the property the extracted checker decides
      on a compiled relation.  Read over names, it is a property of the
      statement; the theorem says a faithful environment carries it
      across unchanged, so the checker's verdict is earned once and
      inherited by every faithful instance. *)
  Definition determines_claim {A : Type}
    (Adec : forall x y : A, {x = y} + {x <> y}) (aid : A) {m n : nat}
    (mat : Vector.t (Vector.t A n) m) (cl : Vector.t bool n) : Prop :=
    ∀ v : Vector.t F n,
    incidence Adec aid mat v ->
    ∀ j : Fin.t n, Vector.nth cl j = true -> Vector.nth v j = zero.

  Theorem faithful_transfers_the_claim :
    ∀ (m n : nat) (mat : Vector.t (Vector.t B n) m) (cl : Vector.t bool n),
    faithful mat ->
    determines_claim Bdec bid mat cl ->
    determines_claim Gdec gid (inst mat) cl.
  Proof.
    intros m n mat cl hf hstmt v hv j hj.
    apply (hstmt v
             (proj2 (faithful_preserves_incidence m n mat v hf) hv) j hj).
  Qed.

  (** Without faithfulness only one direction survives, and it is the
      one a designer needs: a claim the statement fails to pin down is
      a claim no instantiation will pin down either. *)
  Theorem instance_claim_implies_statement_claim :
    ∀ (m n : nat) (mat : Vector.t (Vector.t B n) m) (cl : Vector.t bool n),
    determines_claim Gdec gid (inst mat) cl ->
    determines_claim Bdec bid mat cl.
  Proof.
    intros m n mat cl hinst v hv j hj.
    apply (hinst v (instantiation_monotone m n mat v hv) j hj).
  Qed.

End Instantiation.

(** * That the faithfulness hypothesis is doing work

    A theorem with a hypothesis is worth only as much as the hypothesis
    is hard to satisfy, so here is a statement that passes the check on
    its own names and fails it after an unfaithful instantiation.  It
    is the credential relation of [Examples/StatementQuality.v] read one
    level up: two attributes carried by two different generators, and
    an environment that sends both generators to the same group
    element.

    Names and group elements are both taken to be natural numbers, with
    zero serving as the absence marker and as the identity; the
    exponents are integers, which form the commutative monoid the
    section asks for and nothing more. *)
Section FaithfulnessIsNeeded.

  Import ZArith.

  (** One equation, two secrets, a generator each. *)
  Definition two_generators : Vector.t (Vector.t nat 2) 1 :=
    [[1; 2]%nat].

  (** The environment that confuses the two generators. *)
  Definition collapse (b : nat) : nat :=
    match b with 0%nat => 0%nat | _ => 1%nat end.

  Lemma collapse_absent : collapse 0%nat = 0%nat.
  Proof. reflexivity. Qed.

  (** Read over its own names the statement is sound: each generator
      carries one secret, so each secret is pinned. *)
  Lemma two_generators_determines :
    ∀ v : Vector.t Z 2,
    incidence (zero := 0%Z) (add := Z.add) Nat.eq_dec 0%nat two_generators v ->
    v = @wzero Z 0%Z 2.
  Proof.
    intros v hv.
    destruct (vector_inv_S v) as (a & v' & hv1).
    destruct (vector_inv_S v') as (b & v'' & hv2).
    rewrite (vector_inv_0 v'') in hv2; subst.
    pose proof (hv Fin.F1 1%nat ltac:(discriminate)) as h1.
    pose proof (hv Fin.F1 2%nat ltac:(discriminate)) as h2.
    cbn in h1, h2.
    assert (a = 0%Z) by lia.
    assert (b = 0%Z) by lia.
    subst; reflexivity.
  Qed.

  (** Instantiated by [collapse] it is not: the two secrets trade. *)
  Lemma collapsed_instance_is_degenerate :
    ~ (∀ v : Vector.t Z 2,
         incidence (zero := 0%Z) (add := Z.add) Nat.eq_dec 0%nat
           (inst collapse two_generators) v -> v = @wzero Z 0%Z 2).
  Proof.
    intro hall.
    assert (hbad : incidence (zero := 0%Z) (add := Z.add) Nat.eq_dec 0%nat
                     (inst collapse two_generators) [1%Z; (-1)%Z]).
    { intros i g hg.
      pattern i; refine (Fin.caseS' i _ _ _).
      - replace ((inst collapse two_generators)[@Fin.F1]) with ([1; 1]%nat)
          by reflexivity.
        rewrite !sum_over_cons; unfold sum_over.
        cbn [zip_with Vector.fold_right]; destruct (Nat.eq_dec 1 g); lia.
      - intros k; pattern k; revert k; apply Fin.case0. }
    pose proof (hall _ hbad) as heq.
    inversion heq as [hcontra]; discriminate.
  Qed.

  (** So the hypothesis cannot be dropped from
      [statement_determines_every_faithful_instance], and the reason it
      fails here is the one the theorem names. *)
  Lemma collapse_is_not_faithful :
    ~ faithful (gid := 0%nat) (bid := 0%nat) collapse two_generators.
  Proof.
    intros (hinj & _)%(fun h => h Fin.F1).
    pose proof (hinj Fin.F1 (Fin.FS Fin.F1) eq_refl) as h; cbn in h.
    discriminate.
  Qed.

End FaithfulnessIsNeeded.
