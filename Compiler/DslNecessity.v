From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool List PeanoNat.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import
  Util.
From Compiler Require Import
  LinearRelation Composition Dsl.

Import VectorNotations.

(** * DslNecessity: why the disjunction checker cannot be dropped

    ** The checker in question

    The compiler of Dsl.v does not accept every statement.  Before
    compiling, it runs a purely syntactic test, [disj_inv].  The
    test rejects a statement in which one private variable is shared
    between two parts that compilation will give independent
    witnesses: the two sides of an AND that cannot be merged into a
    single leaf, or two children of a threshold.  Branches of an OR
    are exempt, because only one branch's witness is ever used.

    The correctness theorem [compile_stmt_reflect] carries that test
    as a hypothesis.  It is the direction that reads a witness of
    the compiled relation back as an environment satisfying the
    source statement, and it holds only when [disj_inv] returned
    true.

    A hypothesis like that invites a question.  Is it a real
    restriction, or just an artefact of how the proof was written?
    Could the checker be relaxed, or dropped, with the theorem still
    holding?  This file answers: no.  It exhibits one concrete
    statement on which the conclusion is plainly false.

    ** The counterexample

    The statement is: the point [P] is [g] raised to the private
    scalar [x], and, at the same time, either the point [Q] is [g]
    raised to [x] or the point [Q] is [g] raised to [x].  The two
    branches of the OR are deliberately the same; the OR is there
    only to stop the right-hand side from being a plain conjunction
    of equations.

    The same private name [x] occurs on both sides of the AND.  A
    reader takes that to mean one value: whatever [x] is, it must
    explain [P] and it must explain [Q].  Since [g] raised to a
    given scalar is one definite point, this forces [P] and [Q] to
    be the same point.  So if [P] and [Q] differ, no assignment of a
    value to [x] satisfies the statement at all.  That is the second
    half of [checker_necessary].

    Compilation does not see it that way.  Because the right-hand
    side is not an AND-tree of equations, the compiler cannot merge
    the two sides into a single leaf with a shared witness vector;
    it keeps a [CAnd] node instead.  The witness of a [CAnd] is a
    pair, one witness for each side, and the two components are
    entirely independent.  The left component may assign one value
    to the first column and the right component another.  So if [P]
    is [g] raised to [a] and [Q] is [g] raised to [b], the pair
    consisting of [a] on the left and [b] in the left branch of the
    OR on the right satisfies the compiled relation.  That is the
    first half of [checker_necessary].

    ** Why this makes the checker necessary

    Put the two halves together.  Here is a statement whose compiled
    relation has a witness even though the statement itself has
    none.  A sigma protocol built from that relation is perfectly
    sound for the relation: a successful prover really does know a
    pair of independent values.  But knowing such a pair is strictly
    weaker than knowing what the user asked for, which was one value
    doing both jobs.

    So without the checker the compiler would be a trap.  It would
    accept a statement, produce a protocol, and that protocol would
    convince a verifier of something weaker than the sentence the
    user wrote, with nothing in the output to signal the gap.  The
    checker is the thing that closes the gap, by refusing the input
    rather than compiling it badly.  It is a necessary condition of
    the correctness theorem, not a convenience. *)

Section CheckerNecessity.

  (** ** Parameters

      The field of scalars: carrier [F], constants [zero] and [one],
      the four operations, negation [opp], inverse [inv], and
      [Fdec] deciding equality of scalars. *)
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}.

  (** The group: carrier [G], identity [gid], inversion [ginv],
      operation [gop], and [gpow] for raising a group element to a
      scalar power.  [Hvec] is the assumption that scalars and group
      together form a vector space, which is what makes powers
      behave: it is needed to compute what the equations of the
      counterexample actually say. *)
  Context
    {G : Type}
    {gid : G}
    {ginv : G -> G}
    {gop : G -> G -> G}
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}
    {Hvec : @vector_space F (@eq F) zero one add mul sub
      div opp inv G (@eq G) gid ginv gop gpow}.
  (** Register the field with the [field] tactic, which here only
      has to discharge the identity that multiplying by [one]
      changes nothing. *)
  Add Field field : (@field_theory_for_stdlib_tactic F
    eq zero one opp add mul sub inv div vector_space_field).

  #[local] Infix "^" := gpow.

  (** ** The instance

      Three group elements are fixed for the rest of the file: the
      generator [g], and the two points [P] and [Q] that the
      statement talks about.  They are arbitrary; the theorem below
      supplies the relations between them as hypotheses. *)
  Variable g P Q : G.

  (** Variable names are natural numbers here, since nothing needs
      to be readable.

      - [privs] declares the private variables of the statement.
        There is exactly one, the name [0], which is the [x] of the
        discussion above.
      - [genv] is the point environment: it says which group
        element each point name stands for.  Name [0] is the
        generator, name [1] is [P], and every other name is [Q], so
        in particular name [2] is [Q].
      - [penv] is the public scalar environment.  The statement uses
        no public scalars beyond the literal [one], so every name is
        sent to [zero] and the choice is irrelevant.
      - [node] supplies the interpolation nodes for threshold
        nodes.  The counterexample has no threshold, so this is
        equally irrelevant; the compiler simply takes it as a
        parameter. *)
  Definition privs : Vector.t nat 1 := [0].
  Definition genv (v : nat) : G :=
    match v with 0 => g | 1 => P | _ => Q end.
  Definition penv (_ : nat) : F := zero.
  Definition node (_ : nat) : F := zero.

  (** ** The statement *)

  (** The single term used by both equations: the base named [0],
      which is the generator, raised to the constant [one] times the
      private variable named [0], which is [x].  In readable form
      this is the generator raised to [x]. *)
  Definition tx : @term F nat := mkterm (PConst one) 0 0.

  (** The equation saying that the point named [1], that is [P], is
      the generator raised to [x].  [simple_eq] is the readable
      shape in which one named point equals a product of terms. *)
  Definition eqP : @equation F nat := simple_eq (one := one) 1 (List.cons tx List.nil).

  (** The equation saying that the point named [2], that is [Q], is
      the generator raised to the same [x].  It is deliberately the
      same equation as [eqP] with a different point on the left, so
      that the two cannot both hold unless the two points coincide. *)
  Definition eqQ : @equation F nat := simple_eq (one := one) 2 (List.cons tx List.nil).

  (** The counterexample statement itself: [eqP], conjoined with an
      OR whose two branches are both [eqQ].

      The duplicated branch is not an oversight.  If the right-hand
      side were simply [eqQ], both sides would be conjunctions of
      equations and the compiler would merge them into a single
      leaf, giving them a shared witness vector and removing the
      problem.  Wrapping [eqQ] in an OR blocks the merge while
      changing nothing about what the statement means, since a
      disjunction of a sentence with itself is that sentence. *)
  Definition x_shared : @stmt F nat :=
    SAnd (SEqs (List.cons eqP List.nil))
      (SOr (SEqs (List.cons eqQ List.nil)) (SEqs (List.cons eqQ List.nil))).

  (** Abbreviations for the compiler, the statement semantics, and
      the relation semantics, all applied to the parameters and
      environments fixed above. *)
  #[local] Notation compileC :=
    (@compile F zero add mul opp Fdec G gid ginv gop gpow nat
      PeanoNat.Nat.eq_dec 1 privs genv penv node).
  #[local] Notation stmt_denoteC :=
    (@stmt_denote F add mul opp G gid gop gpow nat genv penv).
  #[local] Notation comp_rel_holdsC :=
    (@comp_rel_holds F zero G gid gop gpow).

  (** ** What the checkers say about it *)

  (** The counterexample is well formed.

      [wf_stmt] is the other syntactic check of Dsl.v: it demands
      that every private variable occurring in a term be one of the
      declared variables in [privs].  This statement passes it, and
      the proof is by computation.

      The point of stating this is to isolate the blame.  The
      statement is not rejected for some unrelated defect; every
      check except [disj_inv] is happy with it.  [disj_inv] is the
      only thing standing between it and the compiler. *)
  Lemma x_shared_wf : wf_stmt (vdec := PeanoNat.Nat.eq_dec) privs x_shared = true.
  Proof. reflexivity. Qed.

  (** The disjunction checker rejects the counterexample.

      Again the proof is by computation: [disj_inv] evaluates to
      false on this statement.  It does so because the right-hand
      side of the AND is not a conjunction of equations, so the
      checker falls through to its second case and demands that the
      two sides share no private variable, which they plainly do.

      Together with the theorem below, this is the whole argument:
      the checker says no to a statement that the compiler would
      otherwise handle wrongly. *)
  Lemma x_shared_rejected :
    disj_inv (vdec := PeanoNat.Nat.eq_dec) x_shared = false.
  Proof. reflexivity. Qed.

  (** Abbreviation for the compilation of a conjunction of equations
      into one leaf of the relation tree. *)
  #[local] Notation compile_leafC :=
    (@compile_leaf F zero add mul opp G gid ginv gop gpow nat
      PeanoNat.Nat.eq_dec 1 privs genv penv).

  (** ** The compiled relation *)

  (** What the compiler produces from [x_shared], written out by
      hand.

      It is a [CAnd] node whose left child is the leaf for [eqP] and
      whose right child is a [COr] of two copies of the leaf for
      [eqQ].  The [CAnd] is what does the damage.  Its witness type
      is a pair, so the left child and the right child each carry
      their own vector of private values and nothing ties the two
      together.  The column standing for [x] exists twice over, once
      on each side, and the relation never asks the two copies to
      agree. *)
  Definition x_shared_rel : @comp_rel F zero G :=
    CAnd (compile_leafC (List.cons eqP List.nil))
      (COr (compile_leafC (List.cons eqQ List.nil))
           (compile_leafC (List.cons eqQ List.nil))).

  (** The compiler really does produce that relation.

      Proved by computation, so the description above is not a
      guess about what the compiler would do; it is what the
      compiler does.  Without this lemma the counterexample would
      say nothing about the actual pipeline. *)
  Lemma x_shared_compile : compileC x_shared = Some x_shared_rel.
  Proof. reflexivity. Qed.

  (** ** The main theorem *)

  (** The compiled relation is satisfiable while the source
      statement is not.

      The hypotheses describe an instance in which the
      counterexample bites.  The scalars [a] and [b] are the discrete
      logarithms of the two points: raising the generator to [a]
      gives [P], and raising it to [b] gives [Q].  Such scalars
      exist whenever the two points lie in the subgroup generated
      by [g], which is the normal situation.  The last hypothesis
      is that [P] and [Q] are different points, and it is the one
      that makes the two halves of the conclusion pull apart.

      The conclusion has two halves.

      The first half exhibits a relation and a witness: the compiled
      relation of [x_shared], together with the witness that places
      [a] on the left of the pair and, on the right, the left branch
      of the OR carrying [b].  Checking that this witness satisfies
      the relation is exactly checking the two leaves separately,
      which is what the two hypotheses about [a] and [b] give.

      The second half says that no witness environment satisfies the
      source statement.  Suppose one did.  Then the left conjunct
      would give the generator raised to the value of [x] equal to
      [P], and whichever branch of the OR holds would give the
      generator raised to the same value of [x] equal to [Q].  Both
      readings compute the same group element, so [P] and [Q] would
      be equal, contradicting the last hypothesis.

      The gap between the two halves is the whole content of the
      file: the compiled protocol can be satisfied in a situation
      where the sentence the user wrote cannot be. *)
  Theorem checker_necessary :
    ∀ (a b : F),
    g ^ a = P -> g ^ b = Q -> P <> Q ->
    (∃ (r : @comp_rel F zero G) (w : comp_witness r),
       compileC x_shared = Some r ∧ comp_rel_holdsC r w) ∧
    ¬ (∃ wenv : nat -> F, stmt_denoteC wenv x_shared).
  Proof.
    intros a b ha hb hne.
    assert (hone : ∀ c : F, mul one c = c). { intro c; field. }
    split.
    +
      (* the compiled relation has the witness (a, inl b) *)
      exists x_shared_rel.
      exists (Vector.map (fun _ => a) privs, inl (Vector.map (fun _ => b) privs)).
      split; [exact x_shared_compile |].
      cbn [comp_rel_holds x_shared_rel fst snd].
      split.
      ++
        eapply (compile_leaf_correct privs genv penv);
        [reflexivity | reflexivity |].
        constructor; [| constructor].
        eapply (simple_eq_denote genv penv (Hvec := Hvec)).
        cbn. unfold term_denote; cbn.
        rewrite hone, right_identity. symmetry; exact ha.
      ++
        eapply (compile_leaf_correct privs genv penv);
        [reflexivity | reflexivity |].
        constructor; [| constructor].
        eapply (simple_eq_denote genv penv (Hvec := Hvec)).
        cbn. unfold term_denote; cbn.
        rewrite hone, right_identity. symmetry; exact hb.
    +
      (* but no environment gives x both values *)
      intros (wenv & hw).
      cbn in hw.
      destruct hw as (hp & hq).
      inversion hp as [| ? ? hp' _]; subst.
      eapply (simple_eq_denote genv penv (Hvec := Hvec)) in hp'; cbn in hp'.
      unfold term_denote in hp'; cbn in hp'.
      rewrite hone, right_identity in hp'.
      destruct hq as [hq | hq];
      inversion hq as [| ? ? hq'' _]; subst;
      eapply (simple_eq_denote genv penv (Hvec := Hvec)) in hq''; cbn in hq'';
      unfold term_denote in hq''; cbn in hq'';
      rewrite hone, right_identity in hq'';
      eapply hne; rewrite hp', hq''; reflexivity.
  Qed.

End CheckerNecessity.
