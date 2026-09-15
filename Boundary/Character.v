From Stdlib Require Import Utf8 List Bool Arith.
From Boundary Require Import Schema.

Import ListNotations.

(** * Determination can depend on a quadratic character

    [Schema.v] reduces the existence of an exact design-time criterion
    to a single question: can two admissible interpretations of the
    same schema disagree about whether it pins down its witness?  For
    linear statements the answer is no, and that is why the companion
    development's criterion is exact.

    One degree up the answer is yes, and this module exhibits it.  The
    schema is three rank-one constraints over two variables and one
    coefficient name,

      t * t = t,    t * x = x,    x * x = a * t,

    each of the form (linear) * (linear) = (linear), which is what an
    arithmetic-circuit compiler emits.  The first confines [t] to
    {0,1}; the second forces [x] to 0 when [t] is 0; the third reads
    [x * x = a] when [t] is 1.  So the origin always solves it, and
    the square roots of [a] solve it as well -- when [a] has any.

    The schema therefore determines its witness exactly when [a] is a
    quadratic non-residue.  That is not a condition a compiler can
    check by looking at the schema, and it is not a condition of the
    kind design-time side conditions are made of: faithfulness asks
    that distinct names be distinct and that no name be the identity,
    and every such condition is satisfied by both interpretations
    below.  By [sensitivity_refutes_every_criterion] no exact
    criterion exists for this class at all.

    We work over the integers mod seven, where 3 is a non-residue and
    2 = 3 * 3 is a residue.  A single prime suffices: the claim is an
    existence claim, and keeping the field concrete keeps the module
    free of axioms. *)

(** ** The field *)

Inductive Fp : Type := F0 | F1 | F2 | F3 | F4 | F5 | F6.

Definition val (x : Fp) : nat :=
  match x with
  | F0 => 0 | F1 => 1 | F2 => 2 | F3 => 3
  | F4 => 4 | F5 => 5 | F6 => 6
  end.

Definition emb (n : nat) : Fp :=
  match Nat.modulo n 7 with
  | 0 => F0 | 1 => F1 | 2 => F2 | 3 => F3
  | 4 => F4 | 5 => F5 | _ => F6
  end.

Definition fadd (x y : Fp) : Fp := emb (val x + val y).
Definition fmul (x y : Fp) : Fp := emb (val x * val y).
Definition Fp_eqb (x y : Fp) : bool := Nat.eqb (val x) (val y).

Lemma Fp_eqb_eq : ∀ x y : Fp, Fp_eqb x y = true <-> x = y.
Proof.
  intros x y; split; intro h.
  + destruct x; destruct y; cbn in h; try discriminate; reflexivity.
  + subst; destruct y; reflexivity.
Qed.

(** ** Rank-one constraints over two variables

    A witness is the pair [(x, t)].  A linear form is a coefficient on
    each variable and a constant term, and a coefficient is either a
    literal or the schema's one name.  A constraint multiplies two
    linear forms and equates the product to a third. *)

Inductive nm : Type := a_nm.

Inductive coeff : Type := Kc (k : Fp) | Kn (n : nm).

Record lin : Type := mklin { l_x : coeff ; l_t : coeff ; l_1 : coeff }.

Record r1c : Type := mkr1c { r_A : lin ; r_B : lin ; r_C : lin }.

Definition env : Type := nm -> Fp.

Definition cval (i : env) (c : coeff) : Fp :=
  match c with Kc k => k | Kn n => i n end.

Definition lval (i : env) (l : lin) (w : Fp * Fp) : Fp :=
  fadd (fadd (fmul (cval i (l_x l)) (fst w))
             (fmul (cval i (l_t l)) (snd w)))
       (cval i (l_1 l)).

Definition satb (i : env) (c : r1c) (w : Fp * Fp) : bool :=
  Fp_eqb (fmul (lval i (r_A c) w) (lval i (r_B c) w)) (lval i (r_C c) w).

Definition sat (i : env) (c : r1c) (w : Fp * Fp) : Prop :=
  satb i c w = true.

(** ** The schema *)

Definition lin_x : lin := mklin (Kc F1) (Kc F0) (Kc F0).
Definition lin_t : lin := mklin (Kc F0) (Kc F1) (Kc F0).
Definition lin_at : lin := mklin (Kc F0) (Kn a_nm) (Kc F0).

Definition boolean : r1c := mkr1c lin_t lin_t lin_t.   (** t * t = t *)
Definition gated   : r1c := mkr1c lin_t lin_x lin_x.   (** t * x = x *)
Definition square  : r1c := mkr1c lin_x lin_x lin_at.  (** x * x = a * t *)

Definition branch : list r1c := [boolean; gated; square].

(** The design-time side condition: a name may not be sent to zero.
    Any stronger condition of the same kind -- distinctness of names,
    non-triviality -- is equally satisfied by both interpretations
    below, since there is only one name and neither sends it to zero. *)
Definition faithful (i : env) : Prop := i a_nm <> F0.

Definition i_nonresidue : env := fun _ => F3.
Definition i_residue    : env := fun _ => F2.

Lemma faithful_nonresidue : faithful i_nonresidue.
Proof. discriminate. Qed.

Lemma faithful_residue : faithful i_residue.
Proof. discriminate. Qed.

(** ** Membership is a computation

    [Sol] is a [Forall] over three decidable conditions, so it is
    settled by evaluation once the witness is a literal pair.  These
    two lemmas are what let the case analyses below be discharged by
    [vm_compute]. *)

Lemma Sol_iff : ∀ (i : env) (w : Fp * Fp),
  Sol sat i branch w <->
    satb i boolean w && satb i gated w && satb i square w = true.
Proof.
  intros i w; split; intro h.
  + inversion h as [| c l hc ht]; subst.
    inversion ht as [| c' l' hc' ht']; subst.
    inversion ht' as [| c'' l'' hc'' ht'']; subst.
    unfold sat in hc, hc', hc''.
    rewrite hc, hc', hc''; reflexivity.
  + apply andb_true_iff in h as [h12 h3].
    apply andb_true_iff in h12 as [h1 h2].
    repeat constructor; assumption.
Qed.

(** ** A non-residue determines

    With [a = 3] the third constraint asks for a square root of 3 mod
    7, and there is none, so the gate [t] can only be 0 and the origin
    is the only solution. *)

Theorem nonresidue_determines : determines sat i_nonresidue branch.
Proof.
  exists (F0, F0); split.
  + apply Sol_iff; vm_compute; reflexivity.
  + intros [x t] h; apply Sol_iff in h.
    destruct x; destruct t; vm_compute in h; try discriminate; reflexivity.
Qed.

(** ** A residue does not

    With [a = 2] the same constraint has the roots 3 and 4, so the
    origin is joined by two further solutions and nothing is pinned
    down.  Two of them suffice. *)

Theorem residue_does_not_determine : ¬ determines sat i_residue branch.
Proof.
  intros (w & _ & hu).
  assert (horigin : (F0, F0) = w).
  { apply hu, Sol_iff; vm_compute; reflexivity. }
  assert (hroot : (F3, F1) = w).
  { apply hu, Sol_iff; vm_compute; reflexivity. }
  rewrite <- horigin in hroot; discriminate.
Qed.

(** ** Consequences

    The two interpretations differ only in the value of one name, both
    satisfy every design-time condition, and they disagree about
    determination.  So determination is not a property of this schema,
    and by [sensitivity_refutes_every_criterion] no function of the
    syntax decides it. *)

Theorem character_is_sensitive :
  interpretation_sensitive sat faithful branch.
Proof.
  exists i_nonresidue, i_residue.
  repeat split.
  + exact faithful_nonresidue.
  + exact faithful_residue.
  + exact nonresidue_determines.
  + exact residue_does_not_determine.
Qed.

Theorem no_exact_criterion :
  ∀ crit : criterion (Constraint := r1c), ¬ exact sat faithful crit.
Proof.
  apply (sensitivity_refutes_every_criterion sat faithful branch
           character_is_sensitive).
Qed.
