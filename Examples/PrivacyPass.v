From Stdlib Require Import Utf8 ZArith
  Vector String List Ascii Znumtheory
  DecimalString DecimalZ Decimal Lia.
From Algebra Require Import Hierarchy Vector_space.
From Utility Require Import Zpstar StringInj.
From Crypto Require Import Sigma.
From Compiler Require Import
  LinearRelation Composition Dsl Surface VarType Nizk Serialization Decide.
From Examples Require Import Helios.
Import Vspace Schnorr Zpfield VectorNotations.

(** * Privacy Pass: anonymous tokens for bypassing internet challenges

    Privacy Pass lets someone who has already solved a CAPTCHA skip
    the next one without being recognised.  It is due to Davidson,
    Goldberg, Sullivan, Tankersley and Valsorda, and is deployed as a
    browser extension and as a Cloudflare service.

    ** How the scheme works

    A server holds a secret key [k] and publishes a commitment to it,
    [Y = X ^ k], where [X] is a fixed generator.  When a client solves
    a challenge it receives a batch of blinded tokens:

    - the client picks random token seeds and blinding factors, hashes
      each seed to a group element [T], and sends [P = T ^ r];
    - the server returns [Q = P ^ k] for each one;
    - the client unblinds, recovering [T ^ k], and stores the pair.

    Later the client spends a token by revealing the seed together
    with a message authentication code keyed on [T ^ k].  Because the
    server never saw the unblinded [T], it cannot link the spend to
    the issuance.

    ** Where the zero-knowledge proof is

    Only one step of Privacy Pass needs a proof of knowledge, and it
    is the server that gives it.  A malicious server could use a
    different key for different clients, and the key it used would
    then act as a tag identifying the client at redemption.  This is
    the "key rotation" attack the paper is careful about.

    The server therefore proves, without revealing [k], that the key
    signing the tokens is the key it committed to:

      log_X (Y)  =  log_P (Q)

    which is a conjunction of two discrete logarithms sharing one
    exponent,

      X ^ k = Y   and   P ^ k = Q .

    This is the discrete log equivalence proof, DLEQ, which is Chaum
    and Pedersen's protocol.  Section 3.2 of the paper writes the
    prover as: sample a nonce, commit to it against both bases,
    derive the challenge by hashing the whole instance together with
    the two commitments, and answer.  That is exactly what our
    compiler emits for the statement below.

    ** Batching

    Issuing [N] tokens naively would need [N] proofs.  Privacy Pass
    instead uses Henry's batching trick: derive coefficients
    [c_1, ..., c_N] by hashing the instance, form the composites

      M = P_1 ^ c_1 * ... * P_N ^ c_N ,
      Z = Q_1 ^ c_1 * ... * Q_N ^ c_N ,

    and give a single DLEQ proof for [(X, Y, M, Z)].  The batching is
    arithmetic done outside the proof system, so it needs no new
    language feature: the same two-equation statement serves, with [M]
    and [Z] supplied as the instance.  What batching does need is the
    theorem that it preserves the relation, and that is
    [batch_same_exponent] below.

    ** What this file contains, and what it does not

    The statement, its compilation, the Fiat-Shamir binding, and the
    algebra of batching are here.  The concrete group elements, the
    token seeds, the blinding factors and the hash arrive from OCaml,
    exactly as in Helios.v and Cmz.v.

    We prove that batching preserves the relation, which is the
    direction an honest server needs.  We do not prove the converse,
    that a batched proof implies each individual pair is well formed;
    that is Henry's probabilistic argument over the random
    coefficients, and it is not mechanised here.  Nor do we model the
    unlinkability of the scheme, which is a property of the whole
    protocol rather than of this proof.

    The group is the one Helios.v already sets up, reused so this file
    needs no primality work of its own.  A deployment uses a
    prime-order elliptic curve; the statement does not change. *)
Section PrivacyPass.

  (** ** The ambient group

      Inherited from Helios.v purely to avoid duplicating the
      parameters and their certificates.  Nothing about Privacy Pass
      depends on this choice. *)

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

  (** ** Algebraic facts used by the batching theorem

      Four small facts about raising group elements to field
      elements.  All four come from the vector space structure the
      development already carries; they are stated here because the
      batching proof rewrites with them repeatedly. *)

  (** Multiplication of scalars commutes.  Read off the commutative
      ring inside the field inside the vector space. *)
  Lemma fmul_comm : ∀ a b : F, fmul a b = fmul b a.
  Proof.
    intros a b.
    exact (commutative_ring_is_commutative
             (commutative_ring :=
                field_commutative_ring
                  (field := vector_space_field (vector_space := Hvec))) a b).
  Qed.

  (** The identity raised to anything is the identity.  Needed for
      the empty batch. *)
  Lemma gpow_gone : ∀ c : F, gpow gone c = gone.
  Proof.
    intro c.
    exact (Vector_space.vid_identity (Hvec := Hvec) c).
  Qed.

  (** Raising a product raises each factor. *)
  Lemma gpow_gmul : ∀ (u v : G) (c : F),
    gpow (gmul u v) c = gmul (gpow u c) (gpow v c).
  Proof.
    intros u v c.
    exact (vector_space_smul_distributive_vadd (vector_space := Hvec) c u v).
  Qed.

  (** Raising twice multiplies the exponents. *)
  Lemma gpow_gpow : ∀ (u : G) (a b : F),
    gpow (gpow u a) b = gpow u (fmul a b).
  Proof.
    intros u a b.
    symmetry.
    exact (vector_space_smul_associative_fmul (vector_space := Hvec) a b u).
  Qed.

  (** Two exponentiations may be applied in either order.  This is the
      fact that makes batching work: raising each point to its
      coefficient and then to the key gives the same thing as raising
      to the key first. *)
  Lemma gpow_swap : ∀ (u : G) (a b : F),
    gpow (gpow u a) b = gpow (gpow u b) a.
  Proof.
    intros u a b.
    rewrite !gpow_gpow, fmul_comm.
    reflexivity.
  Qed.

  (** ** The statement

      [X] is the fixed generator, [Y] the server's published key
      commitment, and [M] and [Z] the two points whose discrete
      logarithms are claimed equal.  For a single token [M] and [Z]
      are the blinded point and its signature; for a batch they are
      the composites, which is why the names are not [P] and [Q].

      The secret side of each equality is written on the left.  That
      is not cosmetic: [TEq a b] elaborates to [a] times the inverse
      of [b], so the side carrying the secret keeps positive exponents
      in the compiled matrix while the other becomes the public
      target.

      The two equations are conjoined, so they merge into a single
      leaf with one witness column.  That is what forces the same [k]
      to answer both, and it is the whole content of the proof. *)
  Definition dleq_stmt : @sstmt F string :=
    TAnd (TEq (YPow "X" (XPriv "k")) (YPt "Y"))
         (TEq (YPow "M" (XPriv "k")) (YPt "Z")).

  (** The names in play.  Elaboration needs the set already in use so
      that gadgets can draw fresh ones; this statement uses no gadget,
      but the interface still asks. *)
  Definition dleq_names : list string :=
    ("X" :: "Y" :: "M" :: "Z" :: "k" :: nil)%list.

  (** The one secret: the server's key. *)
  Definition dleq_privs_list : list string := ("k" :: nil)%list.

  #[local] Notation elabC :=
    (@elab F fzero fone fadd fopp string VarTypeString "A" "B").

  Definition dleq_core : @stmt F string :=
    match elabC dleq_names dleq_stmt with
    | Some (c, _) => c
    | None => SEqs List.nil
    end.

  (** ** Checking the statement

      Elaboration succeeds, the compiled statement passes the
      well-formedness checker, and the private names are distinct.
      All three run by computation. *)

  Example dleq_elab_ok :
    match elabC dleq_names dleq_stmt with
    | Some _ => true | None => false end = true.
  Proof. vm_compute; reflexivity. Qed.

  Example dleq_disj : disj_inv (vdec := String.string_dec) dleq_core = true.
  Proof. vm_compute; reflexivity. Qed.

  Example dleq_nodup :
    nodupb (vdec := String.string_dec) dleq_privs_list = true.
  Proof. vm_compute; reflexivity. Qed.

  (** ** Compiling against an instance

      The instance changes with every issuance, because [M] and [Z]
      are computed from the tokens the client just sent, so
      compilation happens per proof rather than once here. *)

  #[local] Notation comp_relC := (@comp_rel F fzero G).
  #[local] Notation comp_witnessC := (@comp_witness F fzero G).
  #[local] Notation comp_randC := (@comp_rand F fzero G).
  #[local] Notation comp_transcriptC := (@comp_transcript F fzero G).
  #[local] Notation comp_rel_holdsC := (@comp_rel_holds F fzero G gone gmul gpow).
  #[local] Notation comp_ann_tC := (@comp_ann_t F fzero G).

  Definition penvI : string -> F := fun _ => fone.
  Definition node (i : nat) : F := Helios.mk_field (Z.of_nat (S i)).

  (** The point environment for one instance.  Anything unnamed is the
      identity, which never arises because the statement mentions only
      these four. *)
  Definition dleq_genv (X Y M Z : G) : string -> G :=
    fun s =>
      if String.eqb s "X" then X else
      if String.eqb s "Y" then Y else
      if String.eqb s "M" then M else
      if String.eqb s "Z" then Z else gone.

  Definition compile_with (genv : string -> G) (s : @stmt F string)
    : option comp_relC :=
    @compile F fzero fadd fmul fopp fdec G gone ginv_g gmul gpow
      string String.string_dec (List.length dleq_privs_list)
      (Vector.of_list dleq_privs_list) genv penvI node s.

  Definition dleq_rel (X Y M Z : G) : option comp_relC :=
    compile_with (dleq_genv X Y M Z) dleq_core.

  (** The witness, read out of an environment supplied at runtime.
      There is one private name, so this is a one-element vector
      holding the server's key. *)
  Definition scalars (wenv : string -> F)
    : Vector.t F (List.length dleq_privs_list) :=
    @compile_witness F string (List.length dleq_privs_list)
      (Vector.of_list dleq_privs_list) wenv.

  (** ** Binding the proof

      Privacy Pass derives the challenge as [H3 (X, Y, M, Z, A, B)],
      where [A] and [B] are the prover's two commitments.  The whole
      instance is hashed, not only the commitments, which is what
      binds the proof to the tokens it is about.

      Our [pre] argument carries the instance and [ann_to_list]
      supplies the commitments in tree order, so passing
      [[X; Y; M; Z]] reproduces Privacy Pass's input exactly, up to
      the encoding of a group element as a string.  The encoding here
      is decimal joined by commas; the paper's is the compressed point
      encoding of its curve.  Nothing below depends on which is used,
      because the hash is a parameter and every theorem is proven for
      all of them. *)
  Definition pp_hash (hash : string -> N) (pre : list G)
    (r : comp_relC) (a : comp_ann_tC r) : F :=
    Helios.mk_field (Z.of_N (hash (String.concat ","
      (List.map Helios.g_to_string
        (List.app pre (@ann_to_list F fzero G r a)))))).

  Definition pp_prove (hash : string -> N) (pre : list G) (r : comp_relC)
    (w : comp_witnessC r) (rnd : comp_randC r) : comp_transcriptC r :=
    @nizk_prove F fzero fone fadd fmul fsub fopp finv G gone gmul gpow
      r (pp_hash hash pre r) w rnd.

  Definition pp_verify (hash : string -> N) (pre : list G) (r : comp_relC)
    (t : comp_transcriptC r) : bool :=
    @nizk_verify F fzero fone fadd fmul fsub finv G gone gmul gpow gdec
      r (pp_hash hash pre r) t.

  (** The instance, in the order Privacy Pass hashes it. *)
  Definition dleq_pre (X Y M Z : G) : list G := (X :: Y :: M :: Z :: nil)%list.

  (** An honest server's proof verifies, for any instance and any
      hash function. *)
  Theorem pp_complete :
    ∀ (hash : string -> N) (pre : list G) (r : comp_relC)
      (w : comp_witnessC r) (rnd : comp_randC r),
    comp_rel_holdsC r w ->
    pp_verify hash pre r (pp_prove hash pre r w rnd) = true.
  Proof.
    intros hash pre r w rnd hw.
    eapply (@nizk_completeness F fzero fone fadd fmul fsub fdiv fopp finv fdec
      G gone ginv_g gmul gpow gdec Hvec r (pp_hash hash pre r) w rnd hw).
  Qed.

  (** ** Batching

      [batch cs ps] is the composite point [p_1 ^ c_1 * ... * p_n ^ c_n].
      Where the two lists differ in length the surplus is ignored;
      wherever this is used they agree, because the coefficients are
      generated one per token. *)
  Fixpoint batch (cs : list F) (ps : list G) : G :=
    match cs, ps with
    | List.cons c cs', List.cons p ps' => gmul (gpow p c) (batch cs' ps')
    | _, _ => gone
    end.

  (** The theorem that makes batching sound for an honest server: if
      every signed point [q_i] is the corresponding blinded point
      [p_i] raised to the key, then the composite of the signed points
      is the composite of the blinded points raised to that same key.

      So a single DLEQ proof for [(X, Y, batch cs ps, batch cs qs)]
      is a proof about a relation that genuinely holds, for whatever
      coefficients the hash produced.  The coefficients are arbitrary
      here, which is stronger than needed and is what lets the driver
      derive them however it likes. *)
  Theorem batch_same_exponent :
    ∀ (k : F) (ps qs : list G),
    List.Forall2 (fun p q => q = gpow p k) ps qs ->
    ∀ cs : list F, batch cs qs = gpow (batch cs ps) k.
  Proof.
    intros k ps qs hall.
    induction hall as [| p q ps' qs' hpq hall ih]; intro cs.
    - (* both lists empty: the batch is the identity on each side *)
      destruct cs as [| c cs']; cbn [batch]; rewrite gpow_gone; reflexivity.
    - destruct cs as [| c cs'].
      + (* no coefficients left: both sides are the identity *)
        cbn [batch]; rewrite gpow_gone; reflexivity.
      + cbn [batch].
        rewrite gpow_gmul, ih, hpq, gpow_swap.
        reflexivity.
  Qed.

  (** ** What the batched instance satisfies

      Stated at the level of the surface language: under the
      environment that binds [X], [Y] and the two composites, and a
      witness environment that binds [k] to the server's key, the DLEQ
      statement holds.  This is the hypothesis [pp_complete] needs,
      transported back to the sentence the user wrote. *)

  #[local] Notation sstmt_denoteC :=
    (@sstmt_denote F fzero fone fadd fmul fopp G gone ginv_g gmul gpow
       string VarTypeString penvI).

  (** The witness environment: one name, one value. *)
  Definition dleq_wenv (k : F) : string -> F :=
    fun s => if String.eqb s "k" then k else fzero.

  Theorem batch_dleq_holds :
    ∀ (k : F) (X : G) (ps qs : list G) (cs : list F),
    List.Forall2 (fun p q => q = gpow p k) ps qs ->
    sstmt_denoteC
      (dleq_genv X (gpow X k) (batch cs ps) (batch cs qs))
      (dleq_wenv k) dleq_stmt.
  Proof.
    intros k X ps qs cs hall.
    cbn [sstmt_denote dleq_stmt].
    split; cbn [gdenote sdenote dleq_genv dleq_wenv String.eqb]; cbn.
    - reflexivity.
    - symmetry. eapply batch_same_exponent. exact hall.
  Qed.

  (** The unbatched case is the singleton batch with coefficient one,
      which is the statement a server proves when it signs a single
      token.  Stated separately because it is the shape Section 3.2 of
      the paper writes out. *)
  Theorem dleq_holds :
    ∀ (k : F) (X P : G),
    sstmt_denoteC (dleq_genv X (gpow X k) P (gpow P k)) (dleq_wenv k) dleq_stmt.
  Proof.
    intros k X P.
    cbn [sstmt_denote dleq_stmt].
    split; cbn [gdenote sdenote dleq_genv dleq_wenv String.eqb]; cbn; reflexivity.
  Qed.

End PrivacyPass.
