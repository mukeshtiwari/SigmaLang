From Stdlib Require Import Utf8 ZArith
  Vector String List Ascii Znumtheory
  DecimalString DecimalZ Decimal Lia.
From Algebra Require Import Hierarchy.
From Utility Require Import Zpstar StringInj.
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

  (** ** Dimension one: which side carries the secret *)

  Inductive orient : Type := OLeft | ORight.

  (** The ballot statement under each reading.  [OLeft] is Helios as it
      actually is; [ORight] is the same sentence with each equality
      turned around, which is what one writes if one reads the
      protocol description as "the ciphertext equals a power of the
      generator" rather than "a power of the generator equals the
      ciphertext". *)
  Definition ballot_stmt_or (o : orient) : @sstmt F string :=
    match o with
    | OLeft =>
        TOr
          (TAnd (TEq (YPow "g" (XPriv "r0")) (YPt "alpha"))
                (TEq (YPow "h" (XPriv "r0")) (YPt "beta")))
          (TAnd (TEq (YPow "g" (XPriv "r1")) (YPt "alpha"))
                (TEq (YMul (YPow "h" (XPriv "r1")) (YPt "g")) (YPt "beta")))
    | ORight =>
        TOr
          (TAnd (TEq (YPt "alpha") (YPow "g" (XPriv "r0")))
                (TEq (YPt "beta")  (YPow "h" (XPriv "r0"))))
          (TAnd (TEq (YPt "alpha") (YPow "g" (XPriv "r1")))
                (TEq (YPt "beta")  (YMul (YPow "h" (XPriv "r1")) (YPt "g"))))
    end.

  (** ** Dimension two: what reaches the hash

      A ballot announcement flattens to four group elements, the two
      commitments of each branch in tree order. *)

  Inductive hsel : Type := HAll | HFirstPerLeaf | HRev | HLeafSwap.

  (** Keep only the first commitment of each branch.  This is the
      selector that loses information: see
      [first_per_leaf_not_injective]. *)
  Definition first_per_leaf (l : list G) : list G :=
    match l with
    | List.cons a0 (List.cons _ (List.cons a1 (List.cons _ List.nil))) =>
        List.cons a0 (List.cons a1 List.nil)
    | _ => l
    end.

  (** Present the second branch first.  Injective, but a different
      function, so it derives different challenges. *)
  Definition leaf_swap (l : list G) : list G :=
    match l with
    | List.cons a0 (List.cons b0 (List.cons a1 (List.cons b1 List.nil))) =>
        List.cons a1 (List.cons b1 (List.cons a0 (List.cons b0 List.nil)))
    | _ => l
    end.

  Definition apply_hsel (s : hsel) (l : list G) : list G :=
    match s with
    | HAll => l
    | HFirstPerLeaf => first_per_leaf l
    | HRev => List.rev l
    | HLeafSwap => leaf_swap l
    end.

  (** ** A candidate reading of the protocol *)

  Record candidate : Type := mkcand { cand_or : orient; cand_hsel : hsel }.

  Definition all_orients : list orient := (OLeft :: ORight :: nil)%list.
  Definition all_hsels : list hsel :=
    (HAll :: HFirstPerLeaf :: HRev :: HLeafSwap :: nil)%list.

  (** The eight candidates, in a fixed order so the driver can name
      them. *)
  Definition all_candidates : list candidate :=
    List.flat_map (fun o => List.map (fun s => mkcand o s) all_hsels) all_orients.

  Definition orient_name (o : orient) : string :=
    match o with OLeft => "secret-left" | ORight => "secret-right" end.

  Definition hsel_name (s : hsel) : string :=
    match s with
    | HAll => "all four"
    | HFirstPerLeaf => "first per branch"
    | HRev => "reversed"
    | HLeafSwap => "branches swapped"
    end.

  Definition cand_name (k : candidate) : string :=
    String.append (orient_name (cand_or k))
      (String.append " / " (hsel_name (cand_hsel k))).

  (** ** Compiling a candidate

      Every candidate goes through the same pipeline the rest of the
      development uses.  Nothing here is special-cased: the compiler's
      theorems are quantified over all statements, so each candidate
      arrives with completeness, soundness and zero knowledge already
      proven of it. *)

  Definition cand_core (k : candidate) : @stmt F string :=
    match elabC Helios.used0 (ballot_stmt_or (cand_or k)) with
    | Some (c, _) => c
    | None => SEqs List.nil
    end.

  Definition cand_rel (k : candidate) (h alpha beta : G) : option comp_relC :=
    @compile F fzero fadd fmul fopp fdec G gone ginv_g gmul gpow
      string String.string_dec 2 Helios.ballot_privs
      (Helios.ballot_genv h alpha beta) Helios.penvI Helios.node (cand_core k).

  (** The challenge, derived under this candidate's hash rule.  Helios
      renders each group element in decimal and joins with commas; the
      candidate decides which elements, and in what order. *)
  Definition cand_hash (k : candidate) (sha1 : string -> N)
    (r : comp_relC) (a : comp_ann_tC r) : F :=
    Helios.mk_field (Z.of_N (sha1 (String.concat ","
      (List.map Helios.g_to_string
        (apply_hsel (cand_hsel k) (@ann_to_list F fzero G r a)))))).

  Definition cand_verify (k : candidate) (sha1 : string -> N)
    (r : comp_relC) (t : comp_transcriptC r) : bool :=
    @nizk_verify F fzero fone fadd fmul fsub finv G gone gmul gpow gdec
      r (cand_hash k sha1 r) t.

  #[local] Notation comp_randC := (@comp_rand F fzero G).

  (** An honest prover under a given candidate's hash rule.  Having
      this is what lets the driver ask the question testing cannot
      answer from published data alone: if a system had adopted one of
      the other readings, would tampering be caught?  Generate a proof
      under that reading and see. *)
  Definition cand_prove (k : candidate) (sha1 : string -> N)
    (r : comp_relC) (w : comp_witnessC r) (rnd : comp_randC r)
    : comp_transcriptC r :=
    @nizk_prove F fzero fone fadd fmul fsub fopp finv G gone gmul gpow
      r (cand_hash k sha1 r) w rnd.

  (** Every candidate is complete: an honest prover under its rule is
      accepted by the verifier under the same rule.  This is
      [nizk_completeness] instantiated, and it holds for all eight
      because the compiler's theorems are quantified over statements.
      It is also what makes the tampering experiment meaningful: a
      candidate that accepts a tampered transcript does so despite
      being a perfectly complete protocol. *)
  Theorem cand_complete :
    ∀ (k : candidate) (sha1 : string -> N) (r : comp_relC)
      (w : comp_witnessC r) (rnd : comp_randC r),
    comp_rel_holdsC r w ->
    cand_verify k sha1 r (cand_prove k sha1 r w rnd) = true.
  Proof.
    intros k sha1 r w rnd hw.
    eapply (@nizk_completeness F fzero fone fadd fmul fsub fdiv fopp finv fdec
      G gone ginv_g gmul gpow gdec Hvec r (cand_hash k sha1 r) w rnd hw).
  Qed.

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

  (** ** The selectors are genuinely different

      Keeping one element per branch throws information away.  Two
      announcements differing only in the discarded positions derive
      the same challenge, so the challenge does not determine the
      announcement.  That is the property whose absence weak
      Fiat-Shamir attacks exploit. *)
  Theorem first_per_leaf_not_injective :
    ∀ x y : G, x <> y ->
    ∃ l1 l2 : list G, l1 <> l2 ∧ first_per_leaf l1 = first_per_leaf l2.
  Proof.
    intros x y hxy.
    exists (List.cons gone (List.cons x (List.cons gone (List.cons gone List.nil)))).
    exists (List.cons gone (List.cons y (List.cons gone (List.cons gone List.nil)))).
    split.
    - intro heq. inversion heq as [hxy']. exact (hxy hxy').
    - cbn [first_per_leaf]. reflexivity.
  Qed.

  (** The selector we use keeps everything, so it loses nothing. *)
  Theorem all_injective :
    ∀ l1 l2 : list G,
    apply_hsel HAll l1 = apply_hsel HAll l2 -> l1 = l2.
  Proof. intros l1 l2 h; exact h. Qed.

  (** Reversal and the branch swap also lose nothing; they derive
      different challenges without being unsound in the way
      [HFirstPerLeaf] is.  A search must therefore distinguish them by
      running them, which is what the driver does. *)
  Theorem rev_injective :
    ∀ l1 l2 : list G,
    apply_hsel HRev l1 = apply_hsel HRev l2 -> l1 = l2.
  Proof.
    intros l1 l2 h; cbn [apply_hsel] in h.
    rewrite <- (List.rev_involutive l1), <- (List.rev_involutive l2), h.
    reflexivity.
  Qed.

  Theorem leaf_swap_involutive :
    ∀ l : list G, leaf_swap (leaf_swap l) = l.
  Proof.
    intro l.
    destruct l as [| a0 [| b0 [| a1 [| b1 [| z l']]]]]; cbn [leaf_swap]; reflexivity.
  Qed.

  (** ** Checking the candidate space

      Every candidate elaborates and passes the well-formedness
      checker, so the search is over eight genuinely compiled
      protocols rather than over eight strings.  If a candidate failed
      to compile, its rejection would say nothing about the
      protocol. *)

  Example all_candidates_length : List.length all_candidates = 8%nat.
  Proof. vm_compute; reflexivity. Qed.

  Example cand_elab_left :
    match elabC Helios.used0 (ballot_stmt_or OLeft) with
    | Some _ => true | None => false end = true.
  Proof. vm_compute; reflexivity. Qed.

  Example cand_elab_right :
    match elabC Helios.used0 (ballot_stmt_or ORight) with
    | Some _ => true | None => false end = true.
  Proof. vm_compute; reflexivity. Qed.

  Example cand_disj_left :
    disj_inv (vdec := String.string_dec) (cand_core (mkcand OLeft HAll)) = true.
  Proof. vm_compute; reflexivity. Qed.

  Example cand_disj_right :
    disj_inv (vdec := String.string_dec) (cand_core (mkcand ORight HAll)) = true.
  Proof. vm_compute; reflexivity. Qed.

End Recover.
