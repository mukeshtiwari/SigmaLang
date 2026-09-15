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

(** * Why a checklist can never be finished

    Every system that compiles statements keeps a list of shapes to
    reject: a repeated base in one equation, an element that is the
    identity, and so on. The usual complaint about such a list is that
    nobody knows when it is complete. The complaint is too weak. Most
    of the entries can never be right at all, and this module says
    which and why.

    The reason is that adding equations can only help. Constraints
    accumulate, so a statement that fails to pin down its secrets can
    always be repaired by saying more, and the repair does not remove
    whatever shape the checklist objected to. So a shape that occurs
    in a broken statement also occurs in a sound one, and rejecting on
    sight of it is wrong.

    The credential is the example. It repeats a base and is degenerate.
    Add one equation and it is sound, with the repeated base still
    sitting in the first row. Any rule that rejected it for repeating a
    base would reject the repaired statement too.

    This is not an argument against checking. It is an argument about
    the shape of the check: what cannot be done by looking for
    forbidden configurations can be done by solving a linear system,
    which is what [Degeneracy.v] does. *)

Section NoChecklist.

  Context
    {F : Type}
    {zero : F}
    {add : F -> F -> F}.

  Hypothesis add_zero_l : ∀ a : F, add zero a = a.
  Hypothesis add_comm : ∀ a b : F, add a b = add b a.

  Context
    {G : Type}
    {gid : G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}.

  #[local] Notation sum_atC := (@sum_at F zero add G Gdec).
  #[local] Notation incidenceC := (@incidence_zero F zero add G gid Gdec).

  (** ** A row that pins one secret

      [gpoint j g] carries the base [g] at position [j] and the
      identity everywhere else. Its incidence equation at [g] reads
      off position [j] and says nothing about any other. *)
  Fixpoint gpoint {n : nat} (j : Fin.t n) (g : G) : Vector.t G n :=
    match j in Fin.t n' return Vector.t G n' with
    | Fin.F1 => g :: Vector.const gid _
    | Fin.FS j' => gid :: gpoint j' g
    end.

  Lemma sum_at_const_gid :
    ∀ (n : nat) (v : Vector.t F n) (g : G),
    g <> gid -> sum_atC (Vector.const gid n) v g = zero.
  Proof.
    induction n as [| n ih]; intros v g hg.
    - rewrite (vector_inv_0 v); unfold sum_at; cbn; reflexivity.
    - destruct (vector_inv_S v) as (a & v' & hv); subst.
      replace (Vector.const gid (S n)) with (gid :: Vector.const gid n)
        by reflexivity.
      rewrite sum_at_cons, ih by exact hg.
      destruct (Gdec gid g) as [he | _].
      + exfalso; apply hg; symmetry; exact he.
      + apply add_zero_l.
  Qed.

  Lemma sum_at_gpoint :
    ∀ (n : nat) (j : Fin.t n) (g : G) (v : Vector.t F n),
    g <> gid -> sum_atC (gpoint j g) v g = Vector.nth v j.
  Proof.
    intros n j; induction j as [k | k j ih]; intros g v hg.
    - destruct (vector_inv_S v) as (a & v' & hv); subst.
      cbn [gpoint]; rewrite sum_at_cons, sum_at_const_gid by exact hg.
      destruct (Gdec g g) as [_ | hne];
        [| exfalso; apply hne; reflexivity].
      cbn [Vector.nth Vector.caseS].
      rewrite add_comm; apply add_zero_l.
    - destruct (vector_inv_S v) as (a & v' & hv); subst.
      cbn [gpoint]; rewrite sum_at_cons, ih by exact hg.
      destruct (Gdec gid g) as [he | _].
      + exfalso; apply hg; symmetry; exact he.
      + rewrite add_zero_l; cbn [Vector.nth Vector.caseS]; reflexivity.
  Qed.

  (** ** A matrix that pins everything

      If every secret has a row of its own, nothing is left free. *)
  Theorem pinning_rows_determine :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (fresh : Fin.t n -> G),
    (∀ j : Fin.t n, fresh j <> gid) ->
    (∀ j : Fin.t n, ∃ i : Fin.t m,
        Vector.nth mat i = gpoint j (fresh j)) ->
    ∀ v : Vector.t F n, incidenceC mat v -> v = @wzero F zero n.
  Proof.
    intros m n mat fresh hne hrow v hv.
    apply Vector.eq_nth_iff; intros p q hpq; subst q.
    destruct (hrow p) as (i & hi).
    pose proof (hv i (fresh p) (hne p)) as h.
    rewrite hi, sum_at_gpoint in h by exact (hne p).
    rewrite h; unfold wzero; rewrite Vector.const_nth; reflexivity.
  Qed.

  (** ** Every statement extends to a sound one

      [all_fin] is the vector of all positions, so [pin_rows] holds one
      pinning row per secret. *)
  Fixpoint all_fin (n : nat) : Vector.t (Fin.t n) n :=
    match n with
    | 0 => []
    | S k => Fin.F1 :: Vector.map Fin.FS (all_fin k)
    end.

  Lemma nth_all_fin :
    ∀ (n : nat) (j : Fin.t n), Vector.nth (all_fin n) j = j.
  Proof.
    intros n j; induction j as [k | k j ih]; cbn [all_fin].
    - reflexivity.
    - cbn [Vector.nth Vector.caseS].
      rewrite (Vector.nth_map _ (all_fin k) j j eq_refl), ih; reflexivity.
  Qed.

  Definition pin_rows {n : nat} (fresh : Fin.t n -> G)
    : Vector.t (Vector.t G n) n :=
    Vector.map (fun j => gpoint j (fresh j)) (all_fin n).

  Definition extend {m n : nat} (mat : Vector.t (Vector.t G n) m)
    (fresh : Fin.t n -> G) : Vector.t (Vector.t G n) (m + n) :=
    Vector.append mat (pin_rows fresh).

  Theorem extension_is_determined :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (fresh : Fin.t n -> G),
    (∀ j : Fin.t n, fresh j <> gid) ->
    ∀ v : Vector.t F n, incidenceC (extend mat fresh) v -> v = @wzero F zero n.
  Proof.
    intros m n mat fresh hne v hv.
    apply (pinning_rows_determine (m + n) n (extend mat fresh) fresh hne);
    [| exact hv].
    intros j; exists (Fin.R m j); unfold extend.
    rewrite VectorSpec.nth_append_R; unfold pin_rows.
    rewrite (Vector.nth_map _ (all_fin n) j j eq_refl), nth_all_fin.
    reflexivity.
  Qed.

  (** Extension keeps every row it started with. *)
  Theorem extension_keeps_every_row :
    ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m) (fresh : Fin.t n -> G)
      (i : Fin.t m),
    Vector.nth (extend mat fresh) (Fin.L n i) = Vector.nth mat i.
  Proof.
    intros m n mat fresh i; unfold extend.
    apply VectorSpec.nth_append_L.
  Qed.

  (** ** No rule that rejects on sight of a row can be sound

      Suppose a checker rejects a statement because one of its rows
      looks a certain way: it repeats a base, or carries the identity,
      or whatever the list says. Then the rule is wrong, because the
      very same row sits inside a statement that pins down every one of
      its secrets.

      The predicate [P] is arbitrary. Nothing is assumed about what the
      rule is looking for, which is the point: the argument is about
      the \emph{form} of the rule and not its content. *)
  Theorem no_row_rule_is_sound :
    ∀ (n : nat) (P : Vector.t G n -> Prop) (m : nat)
      (mat : Vector.t (Vector.t G n) m) (fresh : Fin.t n -> G)
      (i : Fin.t m),
    (∀ j : Fin.t n, fresh j <> gid) ->
    P (Vector.nth mat i) ->
    (* the extended statement still shows the rule what it objected to *)
    (∃ i' : Fin.t (m + n), P (Vector.nth (extend mat fresh) i')) /\
    (* and yet it leaves no secret undetermined *)
    (∀ v : Vector.t F n,
       incidenceC (extend mat fresh) v -> v = @wzero F zero n).
  Proof.
    intros n P m mat fresh i hne hP; split.
    - exists (Fin.L n i); rewrite extension_keeps_every_row; exact hP.
    - apply extension_is_determined; exact hne.
  Qed.

End NoChecklist.
