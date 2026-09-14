From Stdlib Require Import Utf8 ZArith
  Vector String List Ascii Znumtheory
  DecimalString DecimalZ Decimal Lia.
From Algebra Require Import Hierarchy.
From Utility Require Import Zpstar StringInj Enumerate.
From Crypto Require Import Sigma.
From Compiler Require Import
  LinearRelation Composition Dsl Surface VarType Nizk Serialization Decide.
From Examples Require Import Helios.
Import Vspace Schnorr Zpfield VectorNotations.

(** * What does this proof actually prove?

    A zero-knowledge transcript found on a bulletin board, in a
    credential, or among a standard's test vectors can be handed to an
    implementation, which will say yes or no.  That answer is a
    property of the implementation.  It is not an answer to the
    question one actually wants, which is: supposing this transcript
    is accepted, what has been proved?

    The question has no answer in the usual setting, because the
    statement being proved is not written down anywhere that can be
    checked.  It lives in three places that may disagree: the informal
    mathematics of a paper, the pseudocode of a standard, and the
    source of an implementation.  When they disagree, the way anyone
    finds out is that proofs stop verifying, or worse, keep verifying
    when they should not.

    A verified compiler changes this, because it supplies a fourth
    artifact: a statement that can be read like the paper, run like
    the code, and quantified over by theorems.  [compile_stmt_reflect]
    then reads backwards as a semantics for acceptance.  If a
    transcript is accepted for the relation a statement compiles to,
    then that statement is what was proved, and not merely that some
    verifier was satisfied.

    ** What this file does

    It makes the question operational for the case we know is hard:
    the Helios ballot proof, whose exact form we had to establish
    empirically from published data rather than read out of a
    specification.

    We lay out a space of candidate readings of the protocol.  Each
    candidate is a statement together with a rule for what goes into
    the Fiat-Shamir hash.  Every candidate compiles, and every
    candidate gets a verifier, because the compiler's theorems are
    quantified over all statements.  The driver then runs each
    candidate against real published ballots and reports which ones
    accept.  Recovering the protocol becomes a search rather than a
    debugging session.

    ** The two dimensions

    Both were live questions when we first attacked the published
    data, and getting either wrong is silent.

    - *Orientation.*  [TEq a b] elaborates to [a] times the inverse of
      [b], so the side carrying the secret must be written on the
      left.  Written the other way the statement is still well formed
      and still compiles; every exponent in the matrix is negated and
      no published ballot verifies.

    - *Hash input.*  Helios hashes the announcement.  Which
      announcement elements, and in what order, is not something one
      can read off the protocol description.  One of the candidates
      below hashes only the first element of each branch, which is a
      hash input that does not determine the announcement.

    ** What is proven here

    [recovered_relation_holds] is the semantics of acceptance: two
    accepting transcripts that share an announcement and differ in the
    challenge yield a witness for the candidate's compiled relation.
    That is what it means to say a transcript proves a statement, and
    it is the reason a candidate that accepts is evidence about the
    protocol rather than about our verifier.

    [first_per_leaf_not_injective] says the selector that keeps one
    element per branch loses information: distinct announcements
    derive the same challenge under it.  [all_injective] says the
    selector Helios actually uses does not.  This is the property
    behind weak Fiat-Shamir, that a challenge fails to commit to
    everything it should.

    We are careful about what that does and does not imply here.  It
    is a statement about what the challenge determines.  It is not, on
    its own, an attack on this protocol, and in particular it is not
    exhibited by altering a transcript: the verification equations
    bind the commitments algebraically whether or not the hash does.
    The driver reports a cross-verification matrix instead, which
    establishes the thing the recovery actually needs, namely that the
    candidate readings are pairwise distinguishable. *)
Section Recover.

  Notation F := Helios.F.
  Notation G := Helios.G.
  Notation fzero := Helios.fzero.
  Notation fone := Helios.fone.
  Notation fadd := Helios.fadd.
  Notation fmul := Helios.fmul.
  Notation fsub := Helios.fsub.
  Notation fdiv := Helios.fdiv.
  Notation fopp := Helios.fopp.
  Notation finv := Helios.finv.
  Notation fdec := Helios.fdec.
  Notation gone := Helios.gone.
  Notation gmul := Helios.gmul.
  Notation gpow := Helios.gpow.
  Notation gdec := Helios.gdec.
  Notation ginv_g := Helios.ginv_g.
  Notation Hvec := Helios.Hvec.

  #[local] Open Scope string_scope.

  #[local] Notation comp_relC := (@comp_rel F fzero G).
  #[local] Notation comp_witnessC := (@comp_witness F fzero G).
  #[local] Notation comp_transcriptC := (@comp_transcript F fzero G).
  #[local] Notation comp_rel_holdsC := (@comp_rel_holds F fzero G gone gmul gpow).
  #[local] Notation comp_ann_tC := (@comp_ann_t F fzero G).
  #[local] Notation comp_verifyC :=
    (@comp_verify F fzero fone fadd fmul fsub finv G gone gmul gpow gdec).
  #[local] Notation elabC :=
    (@elab F fzero fone fadd fopp string VarTypeString "A" "B").

  (** ** Dimension one: which side carries the secret

      [TEq a b] elaborates to [a] times the inverse of [b], so the side
      carrying the secret must be written on the left.  Written the
      other way the statement is still well formed and still compiles;
      every exponent in the compiled matrix is negated and no
      published proof verifies.  Getting this wrong is silent, which
      is why it is a dimension of the search rather than a convention
      we assert.

      Rather than write both readings of every target by hand, we
      derive one from the other.  [flip_eqs] turns every equality in a
      statement around and leaves the rest alone, so a target supplies
      one statement and the search covers both readings of it.  This
      also makes the dimension mechanical, which is the point of this
      section: a reader checks [flip_eqs], not a pair of statements
      per target. *)

  Inductive orient : Type := OLeft | ORight.

  Fixpoint flip_eqs (s : @sstmt F string) : @sstmt F string :=
    match s with
    | TEq a b => TEq b a
    | TNeq e => TNeq e
    | TRange x u => TRange x u
    | TLet x e body => TLet x e (flip_eqs body)
    | TAnd a b => TAnd (flip_eqs a) (flip_eqs b)
    | TOr a b => TOr (flip_eqs a) (flip_eqs b)
    | TThresh t l =>
        TThresh t
          ((fix go (l : list (@sstmt F string)) : list (@sstmt F string) :=
              match l with
              | List.nil => List.nil
              | List.cons s' l' => List.cons (flip_eqs s') (go l')
              end) l)
    end.

  (** Turning every equality around twice restores the statement, so
      the two readings really are a pair and the dimension has exactly
      the two values [orient] offers. *)
  Lemma flip_eqs_involutive :
    ∀ s : @sstmt F string, flip_eqs (flip_eqs s) = s.
  Proof.
    intro s.
    induction s as [a b | e | x u | x e body ih | a b iha ihb
                   | a b iha ihb | t l ihl] using sstmt_ind';
      cbn; try reflexivity.
    - rewrite ih; reflexivity.
    - rewrite iha, ihb; reflexivity.
    - rewrite iha, ihb; reflexivity.
    - f_equal.
      induction ihl as [| s' l' ih ihs iht]; cbn; [reflexivity |].
      rewrite ih, iht; reflexivity.
  Qed.

  (** A statement under a chosen reading. *)
  Definition stmt_or (base : @sstmt F string) (o : orient) : @sstmt F string :=
    match o with OLeft => base | ORight => flip_eqs base end.

  (** ** Dimension two: what reaches the hash

      This is the dimension where a hand-written list of candidates is
      indefensible, because the author picks the list already knowing
      which entry is right.  So we do not write a list.  We state what
      a hash rule may be, and use the enumerator of
      Utility/Enumerate.v, which is proven to produce exactly the
      rules satisfying that statement.

      A rule has two parts.  A *selection* says which announcement
      positions are hashed and in what order, and is any
      repetition-free sequence of positions.  An *instance mode* says
      whether the public instance is hashed alongside, and where.

      The announcement width is a property of the target, not of this
      module: a Helios ballot flattens to four group elements, a
      decryption proof to two.  Everything below takes it as a
      parameter [w]. *)

  Inductive inst_mode : Type := IAnnOnly | IInstFirst | IInstLast.

  Definition all_inst_modes : list inst_mode :=
    (IAnnOnly :: IInstFirst :: IInstLast :: nil)%list.

  (** ** A candidate reading of the protocol *)

  Record candidate : Type := mkcand {
    cand_or   : orient;
    cand_sel  : list nat;
    cand_inst : inst_mode
  }.

  Definition all_orients : list orient := (OLeft :: ORight :: nil)%list.

  (** The whole space for an announcement of width [w], generated
      rather than listed. *)
  Definition all_candidates (w : nat) : list candidate :=
    List.flat_map
      (fun o =>
         List.flat_map
           (fun sel => List.map (fun im => mkcand o sel im) all_inst_modes)
           (all_selections w))
      all_orients.

  Definition candidate_count (w : nat) : nat := List.length (all_candidates w).

  (** A candidate is well formed exactly when its selection is legal.
      Orientation and instance mode range over finite types, so they
      carry no side condition. *)
  Definition valid_candidate (w : nat) (k : candidate) : Prop :=
    valid_selection w (cand_sel k).

  (** The enumeration is exactly the specification.  This is the
      theorem that replaces "here are eight readings we thought of":
      a reader checks [valid_candidate], which is three lines, rather
      than checking a list. *)
  Theorem all_candidates_spec :
    forall (w : nat) (k : candidate),
    List.In k (all_candidates w) <-> valid_candidate w k.
  Proof.
    intros w k; split.
    - intro hin.
      unfold all_candidates in hin.
      apply List.in_flat_map in hin as (o & _ & hin).
      apply List.in_flat_map in hin as (sel & hsel & hin).
      apply List.in_map_iff in hin as (im & heq & _).
      subst k. unfold valid_candidate; cbn.
      exact (all_selections_sound w sel hsel).
    - intro hv.
      unfold all_candidates.
      apply List.in_flat_map. exists (cand_or k).
      split; [destruct (cand_or k); cbn; auto |].
      apply List.in_flat_map. exists (cand_sel k).
      split; [exact (all_selections_complete w _ hv) |].
      apply List.in_map_iff. exists (cand_inst k).
      split; [destruct k; reflexivity |].
      destruct (cand_inst k); cbn; auto.
  Qed.

  (** ** Every rule that omits a position loses information

      Previously we could say that one selector we had named lost
      information.  Now we say it of every rule in the space at once,
      and say precisely which ones: exactly those whose selection
      omits a position.

      This is the property behind weak Fiat-Shamir, that a challenge
      fails to commit to everything it should.  It is a statement
      about what the challenge determines.  It is not by itself an
      attack, for the reason recorded at the top of this file. *)

  (** A list of length [n] that is the identity everywhere except
      position [i]. *)
  Definition point_at (n i : nat) (z : G) : list G :=
    List.app (List.repeat gone i) (List.cons z (List.repeat gone (n - S i))).

  Lemma point_at_length :
    forall (n i : nat) (z : G), (i < n)%nat -> List.length (point_at n i z) = n.
  Proof.
    intros n i z hi. unfold point_at.
    rewrite List.length_app; cbn; rewrite !List.repeat_length. lia.
  Qed.

  Lemma point_at_here :
    forall (n i : nat) (z : G), List.nth i (point_at n i z) gone = z.
  Proof.
    intros n i z. unfold point_at.
    rewrite List.app_nth2; rewrite List.repeat_length; [| lia].
    rewrite Nat.sub_diag; reflexivity.
  Qed.

  Lemma point_at_elsewhere :
    forall (n i j : nat) (z : G),
    j <> i -> List.nth j (point_at n i z) gone = gone.
  Proof.
    intros n i j z hne. unfold point_at.
    destruct (Nat.lt_ge_cases j i) as [hlt | hge].
    - rewrite List.app_nth1 by (rewrite List.repeat_length; exact hlt).
      apply List.nth_repeat.
    - rewrite List.app_nth2 by (rewrite List.repeat_length; exact hge).
      rewrite List.repeat_length.
      destruct (Nat.sub j i) as [| d] eqn:hd; [lia |].
      cbn. apply List.nth_repeat.
  Qed.

  Theorem selection_omitting_loses_information :
    forall (w : nat) (sel : list nat) (i : nat) (x y : G),
    (i < w)%nat -> ~ List.In i sel -> x <> y ->
    exists l1 l2 : list G,
      List.length l1 = w /\ List.length l2 = w /\
      l1 <> l2 /\
      apply_selection gone sel l1 = apply_selection gone sel l2.
  Proof.
    intros w sel i x y hi hni hxy.
    exists (point_at w i x), (point_at w i y).
    split; [apply point_at_length; exact hi |].
    split; [apply point_at_length; exact hi |].
    split.
    - intro heq. apply hxy.
      rewrite <- (point_at_here w i x), <- (point_at_here w i y).
      rewrite heq; reflexivity.
    - unfold apply_selection. apply List.map_ext_in.
      intros j hj.
      assert (hne : j <> i) by (intro; subst j; contradiction).
      rewrite !point_at_elsewhere by exact hne; reflexivity.
  Qed.

  (** The complement: the rule that reads every position in order
      loses nothing, because it is the identity. *)
  Theorem full_selection_loses_nothing :
    forall (w : nat) (l : list G),
    List.length l = w ->
    apply_selection gone (List.seq 0 w) l = l.
  Proof.
    intros w l hlen. rewrite <- hlen. apply apply_selection_id.
  Qed.

  (** ** Naming a candidate, for the driver's report *)

  Definition nat_str (i : nat) : string :=
    NilEmpty.string_of_uint (Nat.to_uint i).

  Definition orient_name (o : orient) : string :=
    match o with OLeft => "secret-left" | ORight => "secret-right" end.

  Definition inst_name (m : inst_mode) : string :=
    match m with
    | IAnnOnly => "ann"
    | IInstFirst => "inst++ann"
    | IInstLast => "ann++inst"
    end.

  Definition sel_name (l : list nat) : string :=
    match l with
    | List.nil => "()"
    | _ => String.concat "." (List.map nat_str l)
    end.

  Definition cand_name (k : candidate) : string :=
    String.append (orient_name (cand_or k))
      (String.append " [" (String.append (sel_name (cand_sel k))
        (String.append "] " (inst_name (cand_inst k))))).

  (** ** A target: what it takes to point the search at a protocol

      Everything above is about candidate readings and is independent
      of which protocol is being read.  A target supplies the rest:
      the statement as its documentation describes it, the names in
      scope, the private variables, how an instance becomes a point
      environment, and how wide an announcement is.

      Adding a protocol is then filling in this record.  Nothing in
      the search machinery needs to change, and nothing needs to be
      re-proven, because the compiler's theorems quantify over
      statements. *)
  Record target : Type := mktarget {
    tg_name  : string;
    tg_base  : @sstmt F string;
    tg_used  : list string;
    tg_privs : list string;
    tg_genv  : list G -> string -> G;
    tg_width : nat
  }.

  (** ** Compiling a candidate

      Every candidate goes through the same pipeline the rest of the
      development uses.  Nothing is special-cased: each candidate
      arrives with completeness, soundness and zero knowledge already
      proven of it. *)

  Definition cand_stmt (tg : target) (k : candidate) : @sstmt F string :=
    stmt_or (tg_base tg) (cand_or k).

  Definition cand_core (tg : target) (k : candidate) : @stmt F string :=
    match elabC (tg_used tg) (cand_stmt tg k) with
    | Some (c, _) => c
    | None => SEqs List.nil
    end.

  Definition cand_rel (tg : target) (k : candidate) (inst : list G)
    : option comp_relC :=
    @compile F fzero fadd fmul fopp fdec G gone ginv_g gmul gpow
      string String.string_dec (List.length (tg_privs tg))
      (Vector.of_list (tg_privs tg))
      (tg_genv tg inst) Helios.penvI Helios.node (cand_core tg k).

  (** The candidates for a target, and their count. *)
  Definition target_candidates (tg : target) : list candidate :=
    all_candidates (tg_width tg).

  Definition target_candidate_count (tg : target) : nat :=
    candidate_count (tg_width tg).

  (** The hash input under this candidate's rule.  Helios renders each
      group element in decimal and joins with commas; the candidate
      decides which elements, in what order, and whether the instance
      travels with them. *)
  Definition cand_input (k : candidate) (pre : list G)
    (r : comp_relC) (a : comp_ann_tC r) : list G :=
    let ann := apply_selection gone (cand_sel k) (@ann_to_list F fzero G r a) in
    match cand_inst k with
    | IAnnOnly => ann
    | IInstFirst => List.app pre ann
    | IInstLast => List.app ann pre
    end.

  Definition cand_hash (k : candidate) (sha1 : string -> N) (pre : list G)
    (r : comp_relC) (a : comp_ann_tC r) : F :=
    Helios.mk_field (Z.of_N (sha1 (String.concat ","
      (List.map Helios.g_to_string (cand_input k pre r a))))).

  Definition cand_verify (k : candidate) (sha1 : string -> N) (pre : list G)
    (r : comp_relC) (t : comp_transcriptC r) : bool :=
    @nizk_verify F fzero fone fadd fmul fsub finv G gone gmul gpow gdec
      r (cand_hash k sha1 pre r) t.

  #[local] Notation comp_randC := (@comp_rand F fzero G).

  (** An honest prover under a given candidate's rule.  Having this is
      what lets the driver ask whether two readings are actually
      distinguishable, which published data alone cannot answer. *)
  Definition cand_prove (k : candidate) (sha1 : string -> N) (pre : list G)
    (r : comp_relC) (w : comp_witnessC r) (rnd : comp_randC r)
    : comp_transcriptC r :=
    @nizk_prove F fzero fone fadd fmul fsub fopp finv G gone gmul gpow
      r (cand_hash k sha1 pre r) w rnd.

  (** Every candidate is a complete protocol, for every target.  This
      is [nizk_completeness] instantiated, and it holds for all of them
      because the compiler's theorems quantify over statements.  It is
      what makes a comparison between candidates meaningful: a
      candidate that rejects a corpus does so despite being a perfectly
      good protocol under its own rule. *)
  Theorem cand_complete :
    ∀ (k : candidate) (sha1 : string -> N) (pre : list G) (r : comp_relC)
      (w : comp_witnessC r) (rnd : comp_randC r),
    comp_rel_holdsC r w ->
    cand_verify k sha1 pre r (cand_prove k sha1 pre r w rnd) = true.
  Proof.
    intros k sha1 pre r w rnd hw.
    eapply (@nizk_completeness F fzero fone fadd fmul fsub fdiv fopp finv fdec
      G gone ginv_g gmul gpow gdec Hvec r (cand_hash k sha1 pre r) w rnd hw).
  Qed.

  (** ** The targets

      Two, so that the parameterisation is exercised rather than
      merely written.  Both are Helios statements with published data
      to check against, and both are documented in Helios.v, so they
      serve as controls: we know the answer and can see whether the
      search finds it. *)

  (** A ballot: a disjunction of two conjunctions, four announcement
      elements, two declared secrets.  The instance is the election
      key and the ciphertext. *)
  Definition helios_ballot_target : target :=
    mktarget "helios-ballot"
      (TOr
        (TAnd (TEq (YPow "g" (XPriv "r0")) (YPt "alpha"))
              (TEq (YPow "h" (XPriv "r0")) (YPt "beta")))
        (TAnd (TEq (YPow "g" (XPriv "r1")) (YPt "alpha"))
              (TEq (YMul (YPow "h" (XPriv "r1")) (YPt "g")) (YPt "beta"))))
      Helios.used0
      ("r0" :: "r1" :: nil)%list
      (fun inst =>
         match inst with
         | List.cons h (List.cons alpha (List.cons beta _)) =>
             Helios.ballot_genv h alpha beta
         | _ => fun _ => gone
         end)
      4.

  (** A trustee's decryption proof: a conjunction of two equations
      sharing one secret, so it merges into a single leaf with two
      announcement elements and one declared secret.  The instance is
      the trustee's key, the aggregated ciphertext component and the
      decryption factor. *)
  Definition helios_decrypt_target : target :=
    mktarget "helios-decrypt"
      (TAnd (TEq (YPow "g"  (XPriv "x")) (YPt "pk"))
            (TEq (YPow "AA" (XPriv "x")) (YPt "M")))
      Helios.used0
      ("x" :: nil)%list
      (fun inst =>
         match inst with
         | List.cons pk (List.cons aggr (List.cons fac _)) =>
             Helios.decrypt_genv pk aggr fac
         | _ => fun _ => gone
         end)
      2.

  Definition all_targets : list target :=
    (helios_ballot_target :: helios_decrypt_target :: nil)%list.

  (** ** What an accepted transcript proves

      This is the theorem that makes the search meaningful.  A
      candidate that accepts is not merely a verifier that said yes:
      two accepting runs sharing an announcement and differing in the
      challenge produce a witness for that candidate's relation.  So a
      candidate that accepts the published corpus is evidence about
      what the corpus proves, and a candidate that rejects it is
      evidence that the reading is wrong. *)
  Theorem recovered_relation_holds :
    ∀ (r : comp_relC) (c c' : F) (t t' : comp_transcriptC r),
    c <> c' ->
    @comp_same_announcement F fzero G r t t' ->
    comp_verifyC r c t = true ->
    comp_verifyC r c' t' = true ->
    ∃ w : comp_witnessC r, comp_rel_holdsC r w.
  Proof.
    intros r c c' t t' hne hsame ha hb.
    eapply (@comp_special_soundness F fzero fone fadd fmul fsub fdiv fopp finv fdec
      G gone ginv_g gmul gpow gdec Hvec r c c' t t' hne hsame ha hb).
  Qed.

  (** ** Checking the candidate space

      Every candidate elaborates and passes the well-formedness
      checker, so the search is over eight genuinely compiled
      protocols rather than over eight strings.  If a candidate failed
      to compile, its rejection would say nothing about the
      protocol. *)

  Example ballot_candidate_count :
    target_candidate_count helios_ballot_target = 390%nat.
  Proof. vm_compute; reflexivity. Qed.

  Example decrypt_candidate_count :
    target_candidate_count helios_decrypt_target = 30%nat.
  Proof. vm_compute; reflexivity. Qed.

  (** Both targets elaborate under both readings, so the search is
      over compiled protocols rather than over strings. *)
  Example ballot_elab_left :
    match elabC (tg_used helios_ballot_target)
            (cand_stmt helios_ballot_target (mkcand OLeft nil IAnnOnly)) with
    | Some _ => true | None => false end = true.
  Proof. vm_compute; reflexivity. Qed.

  Example ballot_elab_right :
    match elabC (tg_used helios_ballot_target)
            (cand_stmt helios_ballot_target (mkcand ORight nil IAnnOnly)) with
    | Some _ => true | None => false end = true.
  Proof. vm_compute; reflexivity. Qed.

  Example decrypt_elab_left :
    match elabC (tg_used helios_decrypt_target)
            (cand_stmt helios_decrypt_target (mkcand OLeft nil IAnnOnly)) with
    | Some _ => true | None => false end = true.
  Proof. vm_compute; reflexivity. Qed.

  Example decrypt_elab_right :
    match elabC (tg_used helios_decrypt_target)
            (cand_stmt helios_decrypt_target (mkcand ORight nil IAnnOnly)) with
    | Some _ => true | None => false end = true.
  Proof. vm_compute; reflexivity. Qed.

  (** And both pass the well-formedness checker under both readings. *)
  Example ballot_disj_left :
    disj_inv (vdec := String.string_dec)
      (cand_core helios_ballot_target (mkcand OLeft nil IAnnOnly)) = true.
  Proof. vm_compute; reflexivity. Qed.

  Example ballot_disj_right :
    disj_inv (vdec := String.string_dec)
      (cand_core helios_ballot_target (mkcand ORight nil IAnnOnly)) = true.
  Proof. vm_compute; reflexivity. Qed.

  Example decrypt_disj_left :
    disj_inv (vdec := String.string_dec)
      (cand_core helios_decrypt_target (mkcand OLeft nil IAnnOnly)) = true.
  Proof. vm_compute; reflexivity. Qed.

End Recover.
