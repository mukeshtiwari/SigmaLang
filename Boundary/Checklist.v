From Stdlib Require Import Utf8 List Bool.
From Boundary Require Import Schema Character.

Import ListNotations.

(** * Why no checklist is ever right

    Every system that compiles statements keeps a list of shapes to
    reject: a repeated base in one equation, a coefficient that is
    zero, a variable that occurs only once. The companion development
    proves that no such list can be correct for linear statements. The
    proof there is specific -- it builds the repair out of rows of
    group elements -- and the specificity is misleading, because the
    argument uses almost nothing about the class.

    It uses two things. Constraints accumulate, so adding equations can
    only shrink the solution set; and any witness can be pinned, by
    constraints that the witness itself satisfies. Both hold in every
    class this development considers, and the first holds in every
    conjunctive system whatever. So a statement that fails to pin down
    its secrets can always be repaired by saying more, the repair does
    not remove whatever shape the checklist objected to, and rejecting
    on sight of that shape is therefore wrong.

    We state this once, abstractly, and then discharge the pinning
    hypothesis for the rank-one class of [Character.v], so that the
    theorem is not an implication with an assumption nobody can meet.

    This is not an argument against checking. It is an argument about
    the shape of the check: what cannot be done by looking for
    forbidden configurations can be done by solving a system, which is
    what the companion criterion does, and which
    [Character.v] shows cannot be done exactly above degree one. *)

Section Checklist.

  Context
    {Name : Type}
    {Val : Type}
    {W : Type}
    {Constraint : Type}
    (sat : (Name -> Val) -> Constraint -> W -> Prop).

  (** ** Constraints accumulate

      The one fact that is free in every conjunctive system: a solution
      of a longer schema is a solution of each part. *)

  #[local] Notation schemaC := (@schema Constraint).

  Lemma Sol_app :
    ∀ (i : Name -> Val) (s1 s2 : schemaC) (w : W),
    Sol sat i (s1 ++ s2) w <-> Sol sat i s1 w ∧ Sol sat i s2 w.
  Proof.
    intros i s1 s2 w; unfold Sol; split.
    + apply List.Forall_app.
    + intros (h1 & h2); apply List.Forall_app; split; assumption.
  Qed.

  (** ** Witnesses can be pinned

      The only hypothesis. [pin w] is a schema whose unique solution is
      [w] -- in a rank-one system, one constraint per variable fixing
      its value; in a linear statement, one equation per secret on a
      fresh base. *)

  Context (pin : W -> schemaC).

  Hypothesis pin_solves :
    ∀ (i : Name -> Val) (w : W), Sol sat i (pin w) w.

  Hypothesis pin_determines :
    ∀ (i : Name -> Val) (w w' : W), Sol sat i (pin w) w' -> w' = w.

  (** ** Every satisfiable schema extends to a determined one

      And the extension keeps every constraint the original had, which
      is what makes the checklist argument go through. *)

  Theorem extension_determines :
    ∀ (i : Name -> Val) (s : schemaC) (w : W),
    Sol sat i s w -> determines sat i (s ++ pin w).
  Proof.
    intros i s w hw; exists w; split.
    + apply Sol_app; split; [exact hw | apply pin_solves].
    + intros w' h; apply (pin_determines i), (proj2 (proj1 (Sol_app i s (pin w) w') h)).
  Qed.

  Theorem extension_keeps_every_constraint :
    ∀ (s : schemaC) (w : W) (c : Constraint),
    List.In c s -> List.In c (s ++ pin w).
  Proof. intros s w c hc; apply List.in_or_app; left; exact hc. Qed.

  (** ** No rule that looks at one constraint is sound

      A rule is a property of a single constraint, and it rejects a
      schema when some constraint has that property. It is sound if
      every schema it rejects really does fail to determine. No rule
      that rejects anything at all is sound. *)

  Definition rejects (P : Constraint -> Prop) (s : schemaC) : Prop :=
    ∃ c : Constraint, List.In c s ∧ P c.

  Definition rule_is_sound (P : Constraint -> Prop) (i : Name -> Val) : Prop :=
    ∀ s : schemaC, rejects P s -> ¬ determines sat i s.

  Theorem no_constraint_rule_is_sound :
    ∀ (P : Constraint -> Prop) (i : Name -> Val) (s : schemaC) (w : W),
    Sol sat i s w -> rejects P s -> ¬ rule_is_sound P i.
  Proof.
    intros P i s w hw (c & hc & hp) hsound.
    apply (hsound (s ++ pin w)).
    + exists c; split; [apply extension_keeps_every_constraint; exact hc | exact hp].
    + apply extension_determines; exact hw.
  Qed.

End Checklist.

(** * The hypothesis is met by rank-one systems

    [Character.v]'s class: two variables over the integers mod seven,
    constraints of the form (linear) * (linear) = (linear). A variable
    is pinned by multiplying it by one and equating the product to the
    value it should take. *)

Definition one_lin : lin := mklin (Kc F0) (Kc F0) (Kc F1).

Definition const_lin (c : Fp) : lin := mklin (Kc F0) (Kc F0) (Kc c).

Definition pin_x (c : Fp) : r1c := mkr1c lin_x one_lin (const_lin c).
Definition pin_t (c : Fp) : r1c := mkr1c lin_t one_lin (const_lin c).

Definition pin (w : Fp * Fp) : list r1c :=
  [pin_x (fst w); pin_t (snd w)].

Lemma pin_solves_r1c : ∀ (i : env) (w : Fp * Fp), Sol sat i (pin w) w.
Proof.
  intros i (x & t); repeat constructor;
    unfold sat, satb; destruct x; destruct t; vm_compute; reflexivity.
Qed.

Lemma pin_determines_r1c :
  ∀ (i : env) (w w' : Fp * Fp), Sol sat i (pin w) w' -> w' = w.
Proof.
  intros i (x & t) (x' & t') h.
  inversion h as [| c l hx hrest]; subst.
  inversion hrest as [| c' l' ht _]; subst.
  unfold sat, satb in hx, ht.
  destruct x; destruct t; destruct x'; destruct t';
    vm_compute in hx, ht; try discriminate; reflexivity.
Qed.

(** And so the companion development's no-checklist theorem is not
    about linear statements. It holds one degree up, for exactly the
    class in which exactness itself fails. *)

Theorem no_r1c_rule_is_sound :
  ∀ (P : r1c -> Prop) (i : env) (s : list r1c) (w : Fp * Fp),
  Sol sat i s w -> rejects P s -> ¬ rule_is_sound sat P i.
Proof.
  intros P i s w.
  apply (no_constraint_rule_is_sound sat pin pin_solves_r1c pin_determines_r1c
           P i s w).
Qed.
