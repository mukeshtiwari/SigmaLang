From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef BinPos List PeanoNat.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import Util.
From Compiler Require Import LinearRelation LeafValidity Degeneracy Composition Dsl Claim Instantiate.

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
  Variable node : nat -> F.

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

  (** The per-instance check, at the cell type.  [Instantiate.v] has
      the procedure and its soundness proof; this is only the
      instance. *)
  Definition faithful_tob (eqs : list equationC) : bool :=
    @mat_faithfulb G gid Gdec cellname List.nil cell_dec gcell
      (List.length eqs) n (name_mat eqs).

  Lemma faithful_tob_sound :
    ∀ eqs : list equationC, faithful_tob eqs = true -> faithful_to eqs.
  Proof.
    intros eqs h.
    exact (@mat_faithfulb_sound G gid Gdec cellname List.nil cell_dec gcell
             (List.length eqs) n (name_mat eqs) h).
  Qed.

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

  (** ** The claim a compiled branch makes is itself a design-time fact

      The checker does not take a branch's claim on trust: it computes
      one, [Claim.live_claim], by finding the columns neutral in every
      row.  That is a property of the *instantiated* matrix, so the
      theorem above quantifies over a claim nobody could compute at
      design time -- unless the two agree.  Under a faithful
      environment they do, and for the reason faithfulness already
      names: a cell collapses to the identity only when it is empty.

      Without this the chain does not reach a single compiled branch,
      because every branch of a disjunction carries columns for the
      other branch's secrets and claims only its own. *)
  Lemma dead_columns_transfer :
    ∀ (m : nat) (nm : Vector.t (Vector.t cellname n) m),
    @faithful G gid cellname List.nil gcell m n nm ->
    @dead_columns G gid Gdec m n (@inst G cellname gcell m n nm) =
    @dead_columns cellname List.nil cell_dec m n nm.
  Proof.
    intros m nm hf.
    apply Vector.eq_nth_iff; intros p1 p2 hp; subst p2.
    apply Bool.eq_iff_eq_true; split; intro h.
    - apply (proj2 (dead_columns_spec m n nm p1)); intros i.
      pose proof (proj1 (dead_columns_spec m n _ p1) h i) as hgi.
      unfold inst in hgi.
      rewrite (Vector.nth_map _ nm i i eq_refl),
              (Vector.nth_map _ (Vector.nth nm i) p1 p1 eq_refl) in hgi.
      destruct (hf i) as (_ & hnid).
      destruct (cell_dec (Vector.nth (Vector.nth nm i) p1) List.nil)
        as [he | hne]; [exact he | exfalso; exact (hnid p1 hne hgi)].
    - apply (proj2 (dead_columns_spec m n _ p1)); intros i.
      pose proof (proj1 (dead_columns_spec m n nm p1) h i) as hci.
      unfold inst.
      rewrite (Vector.nth_map _ nm i i eq_refl),
              (Vector.nth_map _ (Vector.nth nm i) p1 p1 eq_refl), hci.
      exact gcell_nil.
  Qed.

  Theorem live_claim_is_design_time :
    ∀ (m : nat) (nm : Vector.t (Vector.t cellname n) m),
    @faithful G gid cellname List.nil gcell m n nm ->
    @live_claim G gid Gdec m n (@inst G cellname gcell m n nm) =
    @live_claim cellname List.nil cell_dec m n nm.
  Proof.
    intros m nm hf; unfold live_claim.
    rewrite (dead_columns_transfer m nm hf); reflexivity.
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

  (** A compiled branch, claim and all, settled at design time.  This
      is the statement that reaches the artefacts: nothing is supplied
      by hand, and the only per-instance work is the boolean. *)
  Theorem branch_checked_once :
    ∀ eqs : list equationC,
    faithful_tob eqs = true ->
    @determines_claim F zero add cellname cell_dec List.nil
      (List.length eqs) n (name_mat eqs)
      (@live_claim cellname List.nil cell_dec (List.length eqs) n
         (name_mat eqs)) ->
    @determines F zero add G gid Gdec (List.length eqs) n
      (Vector.map compile_eq_rowC (Vector.of_list eqs))
      (@live_claim G gid Gdec (List.length eqs) n
         (Vector.map compile_eq_rowC (Vector.of_list eqs))).
  Proof.
    intros eqs hb hstmt.
    pose proof (faithful_tob_sound eqs hb) as hf.
    apply determines_claim_is_determines.
    rewrite compiled_matrix_is_instantiated.
    rewrite (live_claim_is_design_time (List.length eqs) (name_mat eqs) hf).
    exact (faithful_transfers_the_claim add_zero_l gcell gcell_nil
             (List.length eqs) n (name_mat eqs) _ hf hstmt).
  Qed.

  (** ** From a branch to a whole statement

      Nothing anyone actually proves is a bare leaf.  A Helios ballot
      is a disjunction of two conjunctions, so it compiles to a [COr]
      of two leaves, and the 13,072 leaves of a real election come from
      about 6,500 proofs.  So the branch result has to be lifted to the
      tree the compiler really builds.

      The lift is structural and says nothing new: [compile] makes
      leaves in exactly one way, by [compile_leaf], and the
      combinators only assemble them. *)

  #[local] Notation comp_relC := (@comp_rel F zero G).
  #[local] Notation stmtC := (@stmt F V).
  #[local] Notation compile_leafC :=
    (@compile_leaf F zero add mul opp G gid ginv gop gpow V vdec n privs genv penv).
  #[local] Notation compileC :=
    (@compile F zero add mul opp Fdec G gid ginv gop gpow V vdec n privs
       genv penv node).
  #[local] Notation compile_listC :=
    (@compile_list F zero add mul opp Fdec G gid ginv gop gpow V vdec n privs
       genv penv node).

  (** What a design-time check of one equation list amounts to. *)
  Definition eqs_checked (eqs : list equationC) : Prop :=
    faithful_tob eqs = true /\
    @determines_claim F zero add cellname cell_dec List.nil
      (List.length eqs) n (name_mat eqs)
      (@live_claim cellname List.nil cell_dec (List.length eqs) n
         (name_mat eqs)).

  (** Every leaf of a compiled relation determines the claim it makes.
      The inner recursion is spelled out rather than routed through
      [Composition.vall], so that it passes the guard checker. *)
  Fixpoint leaves_determine (r : comp_relC) : Prop :=
    match r with
    | Leaf m nn mat _ =>
        @determines F zero add G gid Gdec m nn mat
          (@live_claim G gid Gdec m nn mat)
    | CAnd a b => leaves_determine a /\ leaves_determine b
    | COr a b => leaves_determine a /\ leaves_determine b
    | CThresh _ k _ rs _ _ =>
        (fix go (k' : nat) (v : Vector.t comp_relC k') : Prop :=
           match v with
           | [] => True
           | r' :: v' => leaves_determine r' /\ go _ v'
           end) k rs
    end.

  (** The design-time check on a source statement, following exactly
      the shape [compile] follows -- in particular the conjunction of
      two pure statements, which the compiler merges into one leaf and
      which must therefore be checked as one. *)
  Fixpoint stmt_checked (s : stmtC) : Prop :=
    match s with
    | SEqs eqs => eqs_checked eqs
    | SAnd a b =>
        match leaves_only a, leaves_only b with
        | Some la, Some lb => eqs_checked (List.app la lb)
        | _, _ => stmt_checked a /\ stmt_checked b
        end
    | SOr a b => stmt_checked a /\ stmt_checked b
    | SThresh _ l =>
        (fix goP (l' : list stmtC) : Prop :=
           match l' with
           | List.nil => True
           | List.cons s' l'' => stmt_checked s' /\ goP l''
           end) l
    end.

  (** A checked equation list compiles to a leaf that determines its
      claim: this is [branch_checked_once] with the leaf assembled. *)
  Lemma compile_leaf_determines :
    ∀ eqs : list equationC,
    eqs_checked eqs -> leaves_determine (compile_leafC eqs).
  Proof.
    intros eqs (hb & hstmt); cbn [leaves_determine compile_leaf].
    exact (branch_checked_once eqs hb hstmt).
  Qed.

  (** The recursion inlined in the threshold case of [compile] is
      [compile_list]; a syntactic fact, proved here rather than
      imported so that this module needs no algebra. *)
  Lemma compile_go_is_compile_list :
    ∀ l : list stmtC,
    (fix go (l0 : list stmtC) : option (list comp_relC) :=
       match l0 with
       | List.nil => Some List.nil
       | List.cons s' l' =>
           match compileC s', go l' with
           | Some r, Some rs => Some (List.cons r rs)
           | _, _ => None
           end
       end) l = compile_listC l.
  Proof.
    induction l as [| s l ih]; cbn [compile_list]; [reflexivity |].
    rewrite ih; reflexivity.
  Qed.

  (** The lift. *)
  Theorem compiled_statement_leaves_determine :
    ∀ (s : stmtC) (r : comp_relC),
    stmt_checked s -> compileC s = Some r -> leaves_determine r.
  Proof.
    intro s; pattern s; revert s; apply stmt_ind'.
    - intros eqs r hchk hcomp; cbn [compile] in hcomp.
      injection hcomp as hcomp; subst r.
      exact (compile_leaf_determines eqs hchk).
    - intros a b iha ihb r hchk hcomp; cbn [compile stmt_checked] in hcomp, hchk.
      destruct (leaves_only a) as [la |] eqn:hla;
      destruct (leaves_only b) as [lb |] eqn:hlb.
      + injection hcomp as hcomp; subst r.
        exact (compile_leaf_determines _ hchk).
      + destruct hchk as (hca & hcb).
        destruct (compileC a) as [ra |] eqn:hra; [| discriminate].
        destruct (compileC b) as [rb |] eqn:hrb; [| discriminate].
        injection hcomp as hcomp; subst r; cbn [leaves_determine].
        split; [exact (iha ra hca eq_refl) | exact (ihb rb hcb eq_refl)].
      + destruct hchk as (hca & hcb).
        destruct (compileC a) as [ra |] eqn:hra; [| discriminate].
        destruct (compileC b) as [rb |] eqn:hrb; [| discriminate].
        injection hcomp as hcomp; subst r; cbn [leaves_determine].
        split; [exact (iha ra hca eq_refl) | exact (ihb rb hcb eq_refl)].
      + destruct hchk as (hca & hcb).
        destruct (compileC a) as [ra |] eqn:hra; [| discriminate].
        destruct (compileC b) as [rb |] eqn:hrb; [| discriminate].
        injection hcomp as hcomp; subst r; cbn [leaves_determine].
        split; [exact (iha ra hca eq_refl) | exact (ihb rb hcb eq_refl)].
    - intros a b iha ihb r (hca & hcb) hcomp; cbn [compile] in hcomp.
      destruct (compileC a) as [ra |] eqn:hra; [| discriminate].
      destruct (compileC b) as [rb |] eqn:hrb; [| discriminate].
      injection hcomp as hcomp; subst r; cbn [leaves_determine].
      split; [exact (iha ra hca eq_refl) | exact (ihb rb hcb eq_refl)].
    - intros t l hall r hchk hcomp; cbn [compile] in hcomp.
      rewrite compile_go_is_compile_list in hcomp.
      destruct (compile_listC l) as [rs |] eqn:hrs; [| discriminate].
      destruct (Compare_dec.le_dec t (List.length rs)) as [Ht |]; [| discriminate].
      destruct (Sumbool.sumbool_of_bool (nodes_ok node (List.length rs)))
        as [Hok |]; [| discriminate].
      injection hcomp as hcomp; subst r; cbn [leaves_determine].
      (* every compiled child determines, by the list induction *)
      clear Ht Hok; revert rs hrs.
      induction hall as [| s l hs hl ih]; intros rs hrs.
      + cbn [compile_list] in hrs; injection hrs as hrs; subst rs; exact I.
      + cbn [compile_list] in hrs; cbn [stmt_checked] in hchk.
        destruct hchk as (hcs & hcl).
        destruct (compileC s) as [r0 |] eqn:hr0; [| discriminate].
        destruct (compile_listC l) as [rs0 |] eqn:hrs0; [| discriminate].
        injection hrs as hrs; subst rs; cbn [Vector.of_list].
        split; [exact (hs r0 hcs eq_refl) | exact (ih hcl rs0 eq_refl)].
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
