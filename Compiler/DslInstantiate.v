From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef BinPos List PeanoNat.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import Util.
From Compiler Require Import LinearRelation LeafValidity Degeneracy Dsl Claim Instantiate.

Import VectorNotations.

(** * Wiring the instantiation theory to the compiler

    [Instantiate.v] proves two things about an abstract matrix of
    names and an environment that instantiates it.  This module
    connects that to the compiler this repository actually runs:
    [Dsl.compile_eq_row] and [Dsl.compile_leaf].

    The connection is not immediate, because a compiled cell is not a
    single base.  [row_of_terms] puts, in the column of variable [x],
    the product over all terms carrying [x] of that term's base raised
    to its public coefficient.  So the object that plays the part of a
    name is the whole cell: the list of (base name, coefficient) pairs
    the equation puts on that variable.

    [cell] reads that list off the syntax and [gcell] evaluates it, and
    [row_of_terms_is_instantiated] says the compiler's row is exactly
    the instantiation of the syntactic one.  Everything then transports
    from [Instantiate.v] with no new argument.

    What this buys is stated at the foot of the file: the statement is
    checked once over its own syntax, and every environment faithful to
    it inherits the verdict, however many instances there are. *)

Section DslInstantiation.

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
    {V : Type}
    {vdec : forall x y : V, {x = y} + {x <> y}}.

  (** The group needs a left unit, and the exponents a commutative
      monoid.  Nothing else about either structure is used, here or in
      [Instantiate.v]. *)
  Hypothesis gop_gid_l : ∀ a : G, gop gid a = a.
  Hypothesis add_zero_l : ∀ a : F, add zero a = a.
  Hypothesis add_assoc : ∀ a b c : F, add a (add b c) = add (add a b) c.
  Hypothesis add_comm : ∀ a b : F, add a b = add b a.

  Context {n : nat}.
  Variable privs : Vector.t V n.
  Variable genv : V -> G.
  Variable penv : V -> F.

  #[local] Notation pexprC := (@pexpr F V).
  #[local] Notation termC := (@term F V).
  #[local] Notation equationC := (@equation F V).
  #[local] Notation pevalC := (@peval F add mul opp V penv).
  #[local] Notation term_colC := (@term_col F add mul opp G gid gpow V vdec genv penv).
  #[local] Notation row_of_termsC :=
    (@row_of_terms F add mul opp G gid gop gpow V vdec n privs genv penv).
  #[local] Notation compile_eq_rowC :=
    (@compile_eq_row F add mul opp G gid gop gpow V vdec n privs genv penv).

  (** ** A cell, as syntax and as a group element *)

  (** The syntactic content of one matrix cell: which bases the
      equation puts on this variable, and with what coefficients.  An
      empty list means the variable does not occur, which is the
      absence marker the abstract theory asks for. *)
  Definition cellname : Type := list (V * pexprC).

  Definition cell (ts : list termC) (x : V) : cellname :=
    List.map (fun t => (t_base t, t_coeff t))
      (List.filter (fun t => veqb (vdec := vdec) (t_var t) x) ts).

  (** Evaluating that content is what the compiler does. *)
  Definition gcell (c : cellname) : G :=
    List.fold_right
      (fun p acc => gop (gpow (genv (fst p)) (pevalC (snd p))) acc) gid c.

  Lemma gcell_nil : gcell List.nil = gid.
  Proof. reflexivity. Qed.

  (** Cells are compared syntactically, so the statement-level check
      needs equality of public coefficient expressions to be decidable.
      It is, since they are built from scalars and names. *)
  Definition pexpr_dec : ∀ x y : pexprC, {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Definition cell_dec : ∀ x y : cellname, {x = y} + {x <> y}.
  Proof.
    apply List.list_eq_dec; intros [v1 p1] [v2 p2].
    destruct (vdec v1 v2) as [hv | hv]; [| right; intro h; congruence].
    destruct (pexpr_dec p1 p2) as [hp | hp]; [| right; intro h; congruence].
    left; subst; reflexivity.
  Defined.

  (** ** The bridge *)

  (** Column [x] of a compiled row is the evaluation of column [x] of
      the syntactic row.  This is the only calculation in the file. *)
  Lemma col_is_gcell :
    ∀ (ts : list termC) (x : V),
    List.fold_right (fun t acc => gop (term_colC t x) acc) gid ts =
    gcell (cell ts x).
  Proof.
    induction ts as [| t ts ih]; intros x.
    - reflexivity.
    - unfold cell, term_col in *; cbn [List.filter List.map List.fold_right].
      destruct (veqb (vdec := vdec) (t_var t) x).
      + cbn [List.fold_right fst snd]; rewrite ih; reflexivity.
      + rewrite gop_gid_l; exact (ih x).
  Qed.

  Definition name_row (ts : list termC) : Vector.t cellname n :=
    Vector.map (cell ts) privs.

  Theorem row_of_terms_is_instantiated :
    ∀ ts : list termC,
    row_of_termsC ts = Vector.map gcell (name_row ts).
  Proof.
    intros ts; unfold row_of_terms, name_row.
    rewrite VectorSpec.map_map.
    apply VectorSpec.map_ext; intros x; apply col_is_gcell.
  Qed.

  Definition name_mat (eqs : list equationC)
    : Vector.t (Vector.t cellname (n)) (List.length eqs) :=
    Vector.map (fun e => name_row (eq_rhs e)) (Vector.of_list eqs).

  (** And so the whole compiled matrix is the instantiation of the
      statement's own matrix, with [gcell] as the environment. *)
  Theorem compiled_matrix_is_instantiated :
    ∀ eqs : list equationC,
    Vector.map compile_eq_rowC (Vector.of_list eqs) =
    @inst G cellname gcell (List.length eqs) n (name_mat eqs).
  Proof.
    intros eqs; unfold inst, name_mat.
    rewrite VectorSpec.map_map.
    apply VectorSpec.map_ext; intros e.
    unfold compile_eq_row; apply row_of_terms_is_instantiated.
  Qed.

  (** ** What the wiring buys

      The extracted checker decides [Claim.determines] on a compiled
      matrix.  That predicate and the one the instantiation theory is
      stated over are the same predicate, which is what lets the two
      meet. *)
  Lemma determines_claim_is_determines :
    ∀ (m : nat) (mat : Vector.t (Vector.t G n) m) (cl : Vector.t bool n),
    @determines_claim F zero add G Gdec gid m n mat cl <->
    @determines F zero add G gid Gdec m n mat cl.
  Proof. intros *; split; intro h; exact h. Qed.

  (** An environment is faithful to a statement when, within each
      equation, it keeps the cells apart and keeps the occupied ones
      off the identity.  Spelled out: two variables carrying different
      collections of bases must not end up with the same group element,
      and a variable that does occur must not have its whole cell
      collapse to the identity. *)
  Definition faithful_to (eqs : list equationC) : Prop :=
    @faithful G gid cellname List.nil gcell (List.length eqs) n
      (name_mat eqs).

  (** ** Deciding faithfulness

      The point of the split is that the two halves cost very different
      things.  Checking that a statement determines its claim means
      building an incidence system and eliminating over the scalar
      field, and it is where the certificates come from.  Checking that
      an environment is faithful means comparing group elements: no
      field arithmetic, no elimination, no certificate.  So the
      expensive half is paid once for a statement and the cheap half
      once per instance, and the theorem above is what makes that
      sound. *)

  (** Two cells may share a group element only if they are the same
      cell. *)
  Definition pair_okb (c1 c2 : cellname) : bool :=
    if Gdec (gcell c1) (gcell c2)
    then (if cell_dec c1 c2 then true else false)
    else true.

  (** An occupied cell may not collapse to the identity. *)
  Definition live_okb (c : cellname) : bool :=
    match c with
    | List.nil => true
    | _ => if Gdec (gcell c) gid then false else true
    end.

  Definition row_faithfulb (row : Vector.t cellname n) : bool :=
    let l := Vector.to_list row in
    andb (List.forallb live_okb l)
         (List.forallb (fun c1 => List.forallb (pair_okb c1) l) l).

  Definition mat_faithfulb {m : nat}
    (mat : Vector.t (Vector.t cellname n) m) : bool :=
    List.forallb row_faithfulb (Vector.to_list mat).

  Lemma row_faithfulb_sound :
    ∀ row : Vector.t cellname n,
    row_faithfulb row = true ->
    @faithful_row G gid cellname List.nil gcell n row.
  Proof.
    intros row h; unfold row_faithfulb in h.
    apply andb_true_iff in h as (hlive & hpair); split.
    - intros j k hjk.
      pose proof (proj1 (List.forallb_forall _ _) hpair
                    (Vector.nth row j) (in_to_list _ _ row j)) as hj.
      pose proof (proj1 (List.forallb_forall _ _) hj
                    (Vector.nth row k) (in_to_list _ _ row k)) as hjk'.
      unfold pair_okb in hjk'.
      destruct (Gdec (gcell (Vector.nth row j)) (gcell (Vector.nth row k)))
        as [_ | hne]; [| exfalso; apply hne; exact hjk].
      destruct (cell_dec (Vector.nth row j) (Vector.nth row k))
        as [he | _]; [exact he | discriminate].
    - intros j hj.
      pose proof (proj1 (List.forallb_forall _ _) hlive
                    (Vector.nth row j) (in_to_list _ _ row j)) as hl.
      unfold live_okb in hl.
      destruct (Vector.nth row j) as [| p c] eqn:hrow.
      + exfalso; apply hj; reflexivity.
      + destruct (Gdec (gcell (p :: c)%list) gid) as [_ | hne];
        [discriminate | exact hne].
  Qed.

  Lemma mat_faithfulb_sound :
    ∀ (m : nat) (mat : Vector.t (Vector.t cellname n) m),
    mat_faithfulb mat = true ->
    @faithful G gid cellname List.nil gcell m n mat.
  Proof.
    intros m mat h i; apply row_faithfulb_sound.
    exact (proj1 (List.forallb_forall _ _) h
             (Vector.nth mat i) (in_to_list _ _ mat i)).
  Qed.

  (** The check a driver runs per instance. *)
  Definition faithful_tob (eqs : list equationC) : bool :=
    mat_faithfulb (name_mat eqs).

  Lemma faithful_tob_sound :
    ∀ eqs : list equationC, faithful_tob eqs = true -> faithful_to eqs.
  Proof. intros eqs h; apply mat_faithfulb_sound; exact h. Qed.

  (** The design-time theorem.  Check the statement once, over its own
      syntax; then every environment faithful to it compiles to a
      relation that determines the same claim, and the checker need not
      be run again. *)
  Theorem statement_checked_once_determines_every_faithful_instance :
    ∀ (eqs : list equationC) (cl : Vector.t bool n),
    faithful_to eqs ->
    @determines_claim F zero add cellname cell_dec List.nil
      (List.length eqs) n (name_mat eqs) cl ->
    @determines F zero add G gid Gdec (List.length eqs) n
      (Vector.map compile_eq_rowC (Vector.of_list eqs)) cl.
  Proof.
    intros eqs cl hf hstmt.
    apply determines_claim_is_determines.
    rewrite compiled_matrix_is_instantiated.
    exact (faithful_transfers_the_claim add_zero_l gcell gcell_nil
             (List.length eqs) n (name_mat eqs) cl hf hstmt).
  Qed.

  (** And the direction that needs no hypothesis at all, which is what
      makes a design-time failure worth acting on: if some compiled
      instance determines the claim then the statement did already, so
      a statement that fails the check fails it in every instance and
      no environment will rescue it. *)
  Theorem no_instance_rescues_a_bad_statement :
    ∀ (eqs : list equationC) (cl : Vector.t bool n),
    @determines F zero add G gid Gdec (List.length eqs) n
      (Vector.map compile_eq_rowC (Vector.of_list eqs)) cl ->
    @determines_claim F zero add cellname cell_dec List.nil
      (List.length eqs) n (name_mat eqs) cl.
  Proof.
    intros eqs cl hinst.
    apply (@instance_claim_implies_statement_claim F zero add add_zero_l
             add_assoc add_comm G gid Gdec cellname List.nil cell_dec
             gcell gcell_nil (List.length eqs) n (name_mat eqs) cl).
    apply determines_claim_is_determines.
    rewrite <- compiled_matrix_is_instantiated; exact hinst.
  Qed.

  (** The form a driver uses: one boolean per instance, and one
      design-time fact about the statement that no instance repeats. *)
  Theorem faithful_check_transfers_the_design_time_verdict :
    ∀ (eqs : list equationC) (cl : Vector.t bool n),
    faithful_tob eqs = true ->
    @determines_claim F zero add cellname cell_dec List.nil
      (List.length eqs) n (name_mat eqs) cl ->
    @determines F zero add G gid Gdec (List.length eqs) n
      (Vector.map compile_eq_rowC (Vector.of_list eqs)) cl.
  Proof.
    intros eqs cl hb hstmt.
    apply statement_checked_once_determines_every_faithful_instance;
    [apply faithful_tob_sound; exact hb | exact hstmt].
  Qed.

End DslInstantiation.

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
