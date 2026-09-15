From Stdlib Require Import Vector Utf8 List ZArith PeanoNat Lia.
From Utility Require Import Util.
From Compiler Require Import LeafValidity Degeneracy Dsl Instantiate
  DslInstantiate.

Import VectorNotations.

(** * Instantiation, demonstrated

    [Compiler/Instantiate.v] proves that instantiation can only weaken
    a statement, and that a faithful environment weakens nothing; and
    [Compiler/DslInstantiate.v] carries that to the compiler and splits
    the work into an expensive design-time half and a cheap
    per-instance one.

    Both files state their results and neither exercises them.  This
    one does, and it lives in [Examples/] rather than beside them for a
    practical reason as well as a tidy one: anything defined in
    [Compiler/] is swept into the extracted library that the verifiers
    link against, and a demonstration has no business being shipped
    there. *)

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

(** * The split, computed

    A statement giving each of its two secrets a generator of its own,
    and two environments: one that keeps the generators apart and one
    that does not.  Only the cheap per-instance check is run, and it
    never touches the scalar field.

    Scalars, points and names are all natural numbers here, and the
    group is addition with zero as its identity; so raising a base to a
    power is multiplication, and a coefficient of one leaves a base
    alone. *)
Section SplitComputed.

  Definition tm (coeff v b : nat) : @term nat nat := mkterm (PConst coeff) v b.

  (** One equation: secret 1 on base 3, secret 2 on base 4. *)
  Definition two_bases : list (@term nat nat) :=
    (tm 1 1 3 :: tm 1 2 4 :: List.nil)%list.

  Definition one_equation : list (@equation nat nat) :=
    (mkeq two_bases List.nil :: List.nil)%list.

  Definition privs2 : Vector.t nat 2 := [1; 2]%nat.
  Definition penv1 : nat -> nat := fun _ => 1%nat.

  (** Keeps the two bases apart. *)
  Definition genv_ok : nat -> nat := fun v => v.

  (** Sends every base to the same point. *)
  Definition genv_collapse : nat -> nat :=
    fun v => match v with 0%nat => 0%nat | _ => 1%nat end.

  Definition checkb (genv : nat -> nat) : bool :=
    @faithful_tob nat Nat.add Nat.mul (fun x => x) PeanoNat.Nat.eq_dec
      nat 0%nat Nat.add Nat.mul PeanoNat.Nat.eq_dec
      nat PeanoNat.Nat.eq_dec 2 privs2 genv penv1 one_equation.

  (** The statement is the same in both lines; only the environment
      differs, and the per-instance check is what separates them. *)
  Example faithful_environment_passes : checkb genv_ok = true.
  Proof. vm_compute; reflexivity. Qed.

  Example collapsing_environment_fails : checkb genv_collapse = false.
  Proof. vm_compute; reflexivity. Qed.

End SplitComputed.
