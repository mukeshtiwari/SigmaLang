From Stdlib Require Import Vector Arith ZArith.
From Compiler Require Import LeafStatus Claim.

Open Scope Z_scope.

(** * A design mistake, and the checker finding it

    The theory of Degeneracy.v and its successors says which
    statements determine their witness.  This file is that theory
    doing one job, on a mistake a protocol designer actually makes.

    ** The setting

    An anonymous credential showing proof.  The prover demonstrates
    that it knows attributes [a1] and [a2] and a blinding value [r]
    behind a published commitment.  Written out, the designer's
    statement is

      C = g ^ a1 * g ^ a2 * h ^ r

    which is one line and looks unremarkable.  The slip is that the
    same generator carries both attributes.

    ** What goes wrong

    That statement pins down [a1 + a2] and [r].  It does not pin down
    [a1] and [a2].  A holder of attributes [(5, 0)] can present a
    perfectly valid proof as [(3, 2)], because adding one to the first
    attribute and subtracting one from the second leaves the equation
    untouched.

    Every theorem about the protocol still holds.  It is complete, it
    is specially sound, it is zero knowledge, and the prover really
    does know a witness.  The witness is simply not the one the
    verifier believes it has seen, and if [a1] gates access to
    anything then that is the whole security argument gone.

    ** What the checker says

    The computations below are the verdicts, and there are four worth
    seeing.  With nothing supplied the checker declines: its cheap
    acceptance test looks for a row of distinct bases and this row
    repeats one, so [undecided] is the honest answer rather than a
    guess in either direction.  Given the vector [(1, -1, 0)] it
    reports the statement degenerate and carries that vector with the
    verdict, so a developer sees not only that the statement is broken
    but how: the two attributes trade against each other.  Given a
    wrong vector it is not fooled, which is why the search that
    produces candidates need not be trusted.  And the repaired
    statement, with one generator per attribute, is settled outright
    with no evidence supplied at all.

    The field is [Z] and group elements are labelled by [nat] with the
    identity at zero.  Nothing here depends on that choice: the
    classifier is parametric, and these labels only have to be
    distinguishable. *)

Notation V3 a b c :=
  (Vector.cons _ a _ (Vector.cons _ b _ (Vector.cons _ c _ (Vector.nil _)))).
Notation V1 a := (Vector.cons _ a _ (Vector.nil _)).

#[local] Notation classify :=
  (@classify_leaf Z 0%Z 1%Z Z.add Z.mul Z.eq_dec nat 0%nat Nat.eq_dec).
#[local] Notation evidence_of := (@LeafStatus.mk_evidence Z 1%nat 3%nat).

(** The designer's statement: one equation, three secrets, and the
    generator [g] carrying both attributes. *)
Definition reused_generator : Vector.t (Vector.t nat 3) 1 := V1 (V3 1 1 2)%nat.

(** The repair: a generator of its own for each attribute. *)
Definition distinct_generators : Vector.t (Vector.t nat 3) 1 := V1 (V3 1 3 2)%nat.

Definition commitment : Vector.t nat 1 := V1 5%nat.

(** The instance declares three secrets, so it claims all three. *)
Definition claims_all := full_claim 3%nat.

(** No evidence: the cheap test declines rather than guessing. *)
Compute classify reused_generator commitment claims_all
  (evidence_of None None).

(** The second witness, supplied and checked: degenerate, and the
    verdict carries the vector that shows why. *)
Compute classify reused_generator commitment claims_all
  (evidence_of (Some (V3 1 (-1) 0)) None).

(** A wrong candidate is not believed. *)
Compute classify reused_generator commitment claims_all
  (evidence_of (Some (V3 1 1 0)) None).

(** The repaired statement needs no evidence at all. *)
Compute classify distinct_generators commitment claims_all
  (evidence_of None None).

(** And the verdict a compiler would act on. *)
Compute leaf_acceptable
  (classify distinct_generators commitment claims_all (evidence_of None None)).

Compute leaf_acceptable
  (classify reused_generator commitment claims_all
     (evidence_of (Some (V3 1 (-1) 0)) None)).
