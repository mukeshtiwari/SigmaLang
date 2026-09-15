From Stdlib Require Import Utf8 List Bool.

Import ListNotations.

(** * What an exact criterion would have to be

    The companion development decides one question: given a statement
    written over base names, does it pin down the secrets it names?
    The answer there is a syntactic computation -- the rank of the
    incidence system -- and it is exact, not conservative. A designer
    runs it once, at design time, over names, and it stays correct for
    every faithful instantiation.

    That exactness is a strong property and it is easy to mistake for
    good engineering. It is not. This module says what it costs, in
    the most general setting we can state it: a schema is a list of
    constraints over names, an interpretation sends names to values,
    and determination is a property of the pair. A criterion sees only
    the schema.

    The one theorem here, [exactness_forces_a_dichotomy], is that a
    criterion can be exact only if determination never depends on the
    interpretation at all. Everything a designer wants from a
    design-time check follows from that dichotomy, and nothing weaker
    will do. So the question "for which relations can a check like
    ours exist?" has a single answer -- exactly those where the
    dichotomy holds -- and the rest of this development is about where
    that is and is not the case. *)

Section Schema.

  (** The names a schema is written over, and the values an
      interpretation gives them. Neither carries structure: a criterion
      compares names and nothing else, which is the whole point. *)
  Context
    {Name : Type}
    {Val : Type}.

  Definition interp : Type := Name -> Val.

  (** A witness, and a class of constraints. A constraint becomes a
      condition on witnesses only once an interpretation is fixed;
      before that it is syntax. *)
  Context
    {W : Type}
    {Constraint : Type}
    (sat : interp -> Constraint -> W -> Prop).

  Definition schema : Type := list Constraint.

  Definition Sol (i : interp) (s : schema) (w : W) : Prop :=
    List.Forall (fun c => sat i c w) s.

  (** Determination: the schema is satisfiable and its solution is
      unique. This is the semantic property; a criterion never sees
      it directly. *)
  Definition determines (i : interp) (s : schema) : Prop :=
    ∃ w : W, Sol i s w ∧ ∀ w' : W, Sol i s w' -> w' = w.

  (** The side condition a compiler can discharge at design time. In
      the linear case it is faithfulness -- the names a statement uses
      get distinct values, and none of them the identity -- but nothing
      below depends on which condition it is. It may even depend on the
      schema, as that one does, and allowing it to makes the negative
      result stronger: the schemas ruled out below survive every side
      condition, including the ones tailored to them. *)
  Context (faithful : interp -> schema -> Prop).

  (** ** Exactness

      A criterion is any function of the syntax. Allowing it to be an
      arbitrary function, rather than a rank computation or a pattern
      search, is what makes the theorem below a statement about every
      possible check rather than about ours. *)
  Definition criterion : Type := schema -> bool.

  Definition exact (crit : criterion) : Prop :=
    ∀ (i : interp) (s : schema),
      faithful i s -> (crit s = true <-> determines i s).

  (** A schema on which two faithful interpretations disagree. *)
  Definition interpretation_sensitive (s : schema) : Prop :=
    ∃ i1 i2 : interp,
      faithful i1 s ∧ faithful i2 s ∧ determines i1 s ∧ ¬ determines i2 s.

  (** ** Exactness is the dichotomy

      If some criterion is exact then determination cannot depend on
      the interpretation, because the criterion's verdict does not.
      This is the only place the argument needs: a criterion is a
      function of [s] alone, so it cannot separate [i1] from [i2]. *)
  Theorem exactness_forces_a_dichotomy :
    ∀ crit : criterion,
      exact crit ->
      ∀ (s : schema) (i1 i2 : interp),
        faithful i1 s -> faithful i2 s ->
        (determines i1 s <-> determines i2 s).
  Proof.
    intros crit hcrit s i1 i2 hf1 hf2.
    split; intro hd.
    + apply (hcrit i2 s hf2), (hcrit i1 s hf1), hd.
    + apply (hcrit i1 s hf1), (hcrit i2 s hf2), hd.
  Qed.

  (** And therefore a single sensitive schema rules out every
      criterion at once -- not merely the ones anyone has proposed. *)
  Theorem sensitivity_refutes_every_criterion :
    ∀ s : schema,
      interpretation_sensitive s ->
      ∀ crit : criterion, ¬ exact crit.
  Proof.
    intros s (i1 & i2 & hf1 & hf2 & hd1 & hd2) crit hcrit.
    apply hd2.
    exact (proj1 (exactness_forces_a_dichotomy crit hcrit s i1 i2 hf1 hf2) hd1).
  Qed.

End Schema.
