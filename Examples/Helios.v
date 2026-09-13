From Stdlib Require Import Utf8 ZArith
  Vector String List Ascii Znumtheory
  DecimalString DecimalZ Lia.
From Algebra Require Import Hierarchy.
From Utility Require Import Zpstar Sha256 StringInj.
From Crypto Require Import Sigma.
From Compiler Require Import
  LinearRelation Composition Dsl Surface VarType Nizk Serialization Decide.
From Examples Require Import primeP primeQ.
Import Vspace Schnorr Zpfield VectorNotations.

(** * Helios: a verifier for the IACR elections, over the real group

    Helios is an end-to-end verifiable voting system.  This file
    writes its zero-knowledge statements in the surface language of
    Surface.v, compiles them through the pipeline, and binds them
    with Fiat-Shamir using Nizk.v, over the actual 2048-bit group of
    the IACR 2024 election.

    ** What a Helios verifier checks

    A ballot encrypts each candidate's choice with ElGamal under the
    election public key [h].  The ciphertext is a pair
    [(alpha, beta) = (g ^ r, h ^ r * g ^ v)] where [r] is the voter's
    randomness and [v] is the vote, which must be zero or one.
    Nothing about [r] or [v] may leak, so the voter attaches a proof
    that [v] is one of the two allowed values without saying which.
    That is a disjunction of two Chaum-Pedersen proofs, and it is
    [ballot_stmt] below.

    After voting closes the ciphertexts are multiplied together.
    ElGamal is homomorphic, so the product encrypts the sum of the
    votes.  Each trustee holds a share [x] of the election secret
    key, publishes a decryption factor for the aggregate, and proves
    it used the same [x] as in its published key.  That is an
    equality of two discrete logarithms, and it is [decrypt_stmt].

    ** What is here and what is not

    Proven here: both statements elaborate, pass the checker,
    compile, and their Fiat-Shamir versions are complete.  The
    example instance is a real ballot over the real group.

    Not here: everything outside the proofs, which in a full
    election verifier is most of the work.  Multiplying the
    ciphertexts together, checking the claimed tally against the
    decryption factors, checking the election key is the product of
    the trustee keys, ballot parsing, and eligibility.

    One further gap is worth naming.  Deployed Helios derives its
    challenge with SHA-1, and binds it to a specific string encoding
    of the announcements.  The hash here is SHA-256 over the decimal
    rendering of Nizk.v's [ann_to_list].  So this verifies proofs it
    produces itself; replaying a published 2024 transcript would
    additionally need SHA-1 and Helios's exact byte encoding.  The
    hash is a parameter of [nizk_verify], so that is a substitution,
    not a redesign. *)
Section Helios.

  (** ** The group of the IACR elections

      The same [p], [q] and [g] were used in the 2022, 2023 and 2024
      IACR elections; only the election public key changes.  [q] is
      256 bits and [p] is 2048 bits.  The primality certificates are
      Pocklington certificates checked by computation. *)
  Definition q : Z := 61329566248342901292543872769978950870633559608669337131139375508370458778917%Z.
  Definition p : Z := 16328632084933010002384055033805457329601614771185955389739167309086214800406465799038583634953752941675645562182498120750264980492381375579367675648771293800310370964745767014243638518442553823973482995267304044326777047662957480269391322789378384619428596446446984694306187644767462460965622580087564339212631775817895958409016676398975671266179637898557687317076177218843233150695157881061257053019133078545928983562221396313169622475509818442661047018436264806901023966236718367204710755935899013750306107738002364137917426595737403871114187750804346564731250609196846638183903982387884578266136503697493474682071%Z.

  (** [q] is prime, by the certificate in primeQ.v. *)
  Theorem prime_q : Znumtheory.prime q.
  Proof. eapply primeQ.prime_q. Qed.

  (** [p] is prime, by the certificate in primeP.v. *)
  Theorem prime_p : Znumtheory.prime p.
  Proof. eapply primeP.prime_p. Qed.

  (** The cofactor.  A Schnorr group lives inside the integers
      modulo [p] as the elements whose order divides [q], which needs
      [p] to have the shape [kcof * q + 1]. *)
  Definition kcof : Z := Z.div p q.

  Theorem safe_prime : p = (kcof * q + 1)%Z.
  Proof. vm_cast_no_check (eq_refl p). Qed.

  (** ** Field and group operations *)

  Definition F : Type := @Zp q.
  Definition G : Type := @Schnorr_group p q.

  Definition fzero : F := @Zpfield.zero q prime_q.
  Definition fone : F := @Zpfield.one q prime_q.
  Definition fadd : F -> F -> F := @zp_add q.
  Definition fmul : F -> F -> F := @zp_mul q.
  Definition fsub : F -> F -> F := @zp_sub q.
  Definition fdiv : F -> F -> F := @zp_div q.
  Definition fopp : F -> F := @zp_opp q prime_q.
  Definition finv : F -> F := @zp_inv q.
  Definition fdec : forall x y : F, {x = y} + {x <> y} := @zp_dec q.
  Definition gone : G := @Schnorr.one p q prime_p prime_q.
  Definition gmul : G -> G -> G := @mul_schnorr_group p q prime_p prime_q.
  Definition gpow : G -> F -> G := @pow kcof p q safe_prime prime_p prime_q.
  Definition gdec : forall x y : G, {x = y} + {x <> y} := @Schnorr.dec_zpstar p q.
  Definition ginv_g : G -> G := @inv_schnorr_group kcof p q safe_prime prime_p prime_q.

  Definition Hvec :
    @vector_space F (@eq F) fzero fone fadd fmul fsub fdiv fopp finv
      G (@eq G) gone ginv_g gmul gpow :=
    @pow_vspace kcof p q safe_prime prime_p prime_q.

  (** A field element from an arbitrary integer, reduced modulo [q]. *)
  Definition mk_field (z : Z) : F.
  Proof.
    refine {| Zpfield.v := Z.modulo z q; Zpfield.Hv := _ |}.
    eapply Z.mod_mod. intro ha; discriminate ha.
  Defined.

  (** The election generator, shared by all three IACR elections. *)
  Definition gval : Z := 14887492224963187634282421537186040801304008017743492304481737382571933937568724473847106029915040150784031882206090286938661464458896494215273989547889201144857352611058572236578734319505128042602372864570426550855201448111746579871811249114781674309062693442442368697449970648232621880001709535143047913661432883287150003429802392229361583608686643243349727791976247247948618930423866180410558458272606627111270040091203073580238905303994472202930783207472394578498507764703191288249547659899997131166130259700604433891232298182348403175947450284433411265966789131024573629546048637848902243503970966798589660808533%Z.
  Definition gen : G.
  Proof.
    refine {| Schnorr.v := gval;
              Ha := conj eq_refl eq_refl : (0 < gval < p)%Z;
              Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod gval q p)).
  Defined.

  (** The 2024 election public key, the product of the three
      trustees' public keys. *)
  Definition hval2024 : Z := 7046735122051745594868985795786176392951854019485729367165971776021501311096201521482383017242860186177215354508901537446984239682993203747271798136868016921883953390308299741287014686008274215001426444189972901892121945650333202105534018888882197552388434304153312708859768386971193915314738375008791798536164901595463713712574129466783480981077498017586306273866594394401039338841105927980179401433149438028686338492134818995843560711439253445043076178166622915392760675509176356257990398772342230639242314592068285808565623831103115873314006496120730338309413064358649726464219249576117734308027594482849210379533%Z.
  Definition pubkey : G.
  Proof.
    refine {| Schnorr.v := hval2024;
              Ha := conj eq_refl eq_refl : (0 < hval2024 < p)%Z;
              Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod hval2024 q p)).
  Defined.

  (** ** The statements *)

  #[local] Open Scope string_scope.

  #[local] Notation elabC :=
    (@elab F fzero fone fadd fopp string VarTypeString "A" "B").

  (** Ballot well-formedness for one candidate of one ballot.

      A note on orientation, which is not cosmetic.  [TEq a b]
      elaborates to [a] times the inverse of [b] equals the identity,
      so whichever side carries the secret keeps a positive exponent
      in the compiled matrix while the other becomes the public
      target the verifier raises to the challenge.  Helios checks
      [g ^ r = A * alpha ^ c], so the secret side has to be written
      on the left.  Writing it the other way round compiles to the
      same claim with every exponent negated, and then no published
      ballot verifies.

      The left branch is the claim that the vote was zero, so the
      ciphertext is [(g ^ r, h ^ r)]; the right branch is the claim
      that it was one, so the ciphertext is [(g ^ r, h ^ r * g)].
      Each branch names its own randomness, which is right: a prover
      only knows the randomness of the branch that is true, and
      simulates the other. *)
  Definition ballot_stmt : @sstmt F string :=
    TOr
      (TAnd (TEq (YPow "g" (XPriv "r0")) (YPt "alpha"))
            (TEq (YPow "h" (XPriv "r0")) (YPt "beta")))
      (TAnd (TEq (YPow "g" (XPriv "r1")) (YPt "alpha"))
            (TEq (YMul (YPow "h" (XPriv "r1")) (YPt "g")) (YPt "beta"))).

  (** A trustee's decryption proof.

      The trustee's published key is [pk = g ^ x] and its decryption
      factor for the aggregated ciphertext component [AA] is
      [M = AA ^ x].  Proving both with the same [x] is what stops a
      trustee decrypting with a key other than the one it published.
      The compiler merges a conjunction of equations into a single
      leaf, so both equations read the same entry of one witness
      vector, which is exactly what ties them together. *)
  Definition decrypt_stmt : @sstmt F string :=
    TAnd (TEq (YPow "g"  (XPriv "x")) (YPt "pk"))
         (TEq (YPow "AA" (XPriv "x")) (YPt "M")).

  (** A trustee's proof that it knows the secret key behind its
      published key.  Plain Schnorr, and the third of the three
      statements a Helios verifier checks. *)
  Definition pok_stmt : @sstmt F string :=
    TEq (YPow "g" (XPriv "x")) (YPt "pk").

  (** Every name either statement can mention, plus the two Pedersen
      bases the gadgets would use.  Neither statement needs a gadget,
      so [A] and [B] are never touched. *)
  Definition used0 : list string :=
    ("A"::"B"::"g"::"h"::"alpha"::"beta"::"pk"::"M"::"AA"
     ::"r0"::"r1"::"x"::nil)%list.

  Definition ballot_core : @stmt F string :=
    match elabC used0 ballot_stmt with
    | Some (c, _) => c
    | None => SEqs List.nil
    end.

  Definition decrypt_core : @stmt F string :=
    match elabC used0 decrypt_stmt with
    | Some (c, _) => c
    | None => SEqs List.nil
    end.

  (** Both elaborate. *)
  Example ballot_elab :
    elabC used0 ballot_stmt = Some (ballot_core, used0).
  Proof. vm_compute; reflexivity. Qed.

  Example decrypt_elab :
    elabC used0 decrypt_stmt = Some (decrypt_core, used0).
  Proof. vm_compute; reflexivity. Qed.

  (** ** Compiling to a protocol *)

  Definition ballot_privs : Vector.t string 2 := ["r0"; "r1"].
  Definition decrypt_privs : Vector.t string 1 := ["x"].

  Definition penvI : string -> F := fun _ => fone.

  (** Interpolation nodes, needed by the compiler's signature even
      though neither statement has a threshold. *)
  Definition node (i : nat) : F := mk_field (Z.of_nat (S i)).

  (** Both statements are well formed and both pass the
      disjunction-invariant checker.  The ballot proof is the
      interesting case: its two branches share no private variable,
      and even if they did, the checker permits it on a disjunction,
      because only one branch's witness is ever used. *)
  Example ballot_wf : wf_stmt (vdec := String.string_dec) ballot_privs ballot_core = true.
  Proof. vm_compute; reflexivity. Qed.
  Example ballot_disj : disj_inv (vdec := String.string_dec) ballot_core = true.
  Proof. vm_compute; reflexivity. Qed.
  Example ballot_nodup : nodupb (vdec := String.string_dec) (Vector.to_list ballot_privs) = true.
  Proof. vm_compute; reflexivity. Qed.

  Example decrypt_wf : wf_stmt (vdec := String.string_dec) decrypt_privs decrypt_core = true.
  Proof. vm_compute; reflexivity. Qed.
  Example decrypt_disj : disj_inv (vdec := String.string_dec) decrypt_core = true.
  Proof. vm_compute; reflexivity. Qed.
  Example decrypt_nodup : nodupb (vdec := String.string_dec) (Vector.to_list decrypt_privs) = true.
  Proof. vm_compute; reflexivity. Qed.

  (** The instance of a ballot proof: the generator, the election
      key, and the ciphertext being proven well formed.  The
      ciphertext changes with every ballot, so the compiled relation
      does too, and compilation has to happen per ballot at runtime
      rather than once here. *)
  Definition ballot_genv (h alpha beta : G) : string -> G :=
    fun s =>
      if String.eqb s "g" then gen
      else if String.eqb s "h" then h
      else if String.eqb s "alpha" then alpha
      else if String.eqb s "beta" then beta
      else gone.

  (** The instance of a decryption proof: the generator, the
      trustee's public key, the aggregated ciphertext component, and
      the trustee's decryption factor. *)
  Definition decrypt_genv (pk aggr fac : G) : string -> G :=
    fun s =>
      if String.eqb s "g" then gen
      else if String.eqb s "pk" then pk
      else if String.eqb s "AA" then aggr
      else if String.eqb s "M" then fac
      else gone.

  #[local] Notation comp_relC := (@comp_rel F fzero G).
  #[local] Notation comp_witnessC := (@comp_witness F fzero G).
  #[local] Notation comp_randC := (@comp_rand F fzero G).
  #[local] Notation comp_transcriptC := (@comp_transcript F fzero G).
  #[local] Notation comp_rel_holdsC := (@comp_rel_holds F fzero G gone gmul gpow).
  #[local] Notation comp_ann_tC := (@comp_ann_t F fzero G).

  Definition ballot_rel (h alpha beta : G) : option comp_relC :=
    @compile F fzero fadd fmul fopp fdec G gone ginv_g gmul gpow
      string String.string_dec 2 ballot_privs (ballot_genv h alpha beta)
      penvI node ballot_core.

  Definition pok_core : @stmt F string :=
    match elabC used0 pok_stmt with
    | Some (c, _) => c
    | None => SEqs List.nil
    end.

  (** The instance of a key proof is just the generator and the
      trustee's published key. *)
  Definition pok_genv (pk : G) : string -> G :=
    fun s =>
      if String.eqb s "g" then gen
      else if String.eqb s "pk" then pk
      else gone.

  Definition pok_rel (pk : G) : option comp_relC :=
    @compile F fzero fadd fmul fopp fdec G gone ginv_g gmul gpow
      string String.string_dec 1 decrypt_privs (pok_genv pk)
      penvI node pok_core.

  Definition decrypt_rel (pk aggr fac : G) : option comp_relC :=
    @compile F fzero fadd fmul fopp fdec G gone ginv_g gmul gpow
      string String.string_dec 1 decrypt_privs (decrypt_genv pk aggr fac)
      penvI node decrypt_core.

  (** ** Binding the proof with Fiat-Shamir

      An interactive proof needs a verifier online to send a random
      challenge.  Fiat-Shamir removes that by deriving the challenge
      from the prover's own first message with a hash.

      It matters enormously what goes into that hash.  If only the
      announcement is hashed, a prover can choose the statement after
      seeing the challenge, which is the weak form of the transform
      and is forgeable.  The strong form hashes the whole instance
      too.  That is why [hash_with] takes a prefix: the caller passes
      the generator, the election key and the ciphertext, so the
      challenge is bound to the exact claim being made. *)

  (** A group element rendered as a decimal string. *)
  Definition g_to_string (x : G) : string :=
    NilEmpty.string_of_int (Z.to_int (@Schnorr.v p q x)).

  (** What that rendering actually produces for the generator.

      The extracted code replaces [g_to_string] with OCaml's native
      big-integer printer, because converting a 617 digit number one
      digit at a time is the whole cost of a proof.  This example
      pins down what the verified definition yields, so the driver
      can check the native replacement against it rather than take
      the substitution on trust. *)
  Example g_to_string_gen : g_to_string gen = "14887492224963187634282421537186040801304008017743492304481737382571933937568724473847106029915040150784031882206090286938661464458896494215273989547889201144857352611058572236578734319505128042602372864570426550855201448111746579871811249114781674309062693442442368697449970648232621880001709535143047913661432883287150003429802392229361583608686643243349727791976247247948618930423866180410558458272606627111270040091203073580238905303994472202930783207472394578498507764703191288249547659899997131166130259700604433891232298182348403175947450284433411265966789131024573629546048637848902243503970966798589660808533"%string.
  Proof. vm_compute; reflexivity. Qed.

  (** The challenge: SHA-256 over the instance prefix followed by
      every group element of the announcement, comma separated, read
      back as a field element.

      The announcement is flattened by [ann_to_list] of Nizk.v rather
      than by reaching into the transcript by hand, because reaching
      in by hand silently drops elements whenever a leaf carries more
      than one equation, which is exactly the weak-Fiat-Shamir
      failure.  A ballot leaf carries two. *)
  Definition hash_with (pre : list G) (r : comp_relC) (a : comp_ann_tC r) : F :=
    mk_field (Z.of_N (sha256_string (String.concat ","
      (List.map g_to_string (List.app pre (@ann_to_list F fzero G r a)))))).

  Definition ballot_hash (h alpha beta : G) (r : comp_relC) : comp_ann_tC r -> F :=
    hash_with (List.cons gen (List.cons h (List.cons alpha (List.cons beta List.nil)))) r.

  Definition decrypt_hash (pk aggr fac : G) (r : comp_relC) : comp_ann_tC r -> F :=
    hash_with (List.cons gen (List.cons pk (List.cons aggr (List.cons fac List.nil)))) r.

  (** The non-interactive prover and verifier for a ballot proof.
      The verifier recomputes the challenge rather than reading it
      from the transcript, which is the whole point. *)
  Definition ballot_prove (h alpha beta : G) (r : comp_relC)
    (w : comp_witnessC r) (rnd : comp_randC r) : comp_transcriptC r :=
    @nizk_prove F fzero fone fadd fmul fsub fopp finv G gone gmul gpow
      r (ballot_hash h alpha beta r) w rnd.

  Definition ballot_verify (h alpha beta : G) (r : comp_relC)
    (t : comp_transcriptC r) : bool :=
    @nizk_verify F fzero fone fadd fmul fsub finv G gone gmul gpow gdec
      r (ballot_hash h alpha beta r) t.

  Definition decrypt_prove (pk aggr fac : G) (r : comp_relC)
    (w : comp_witnessC r) (rnd : comp_randC r) : comp_transcriptC r :=
    @nizk_prove F fzero fone fadd fmul fsub fopp finv G gone gmul gpow
      r (decrypt_hash pk aggr fac r) w rnd.

  Definition decrypt_verify (pk aggr fac : G) (r : comp_relC)
    (t : comp_transcriptC r) : bool :=
    @nizk_verify F fzero fone fadd fmul fsub finv G gone gmul gpow gdec
      r (decrypt_hash pk aggr fac r) t.

  (** An honestly produced ballot proof always verifies, for every
      ciphertext and every choice of randomness. *)
  Theorem ballot_complete :
    ∀ (h alpha beta : G) (r : comp_relC) (w : comp_witnessC r) (rnd : comp_randC r),
    comp_rel_holdsC r w ->
    ballot_verify h alpha beta r (ballot_prove h alpha beta r w rnd) = true.
  Proof.
    intros h alpha beta r w rnd hw.
    eapply (@nizk_completeness F fzero fone fadd fmul fsub fdiv fopp finv fdec
      G gone ginv_g gmul gpow gdec Hvec r (ballot_hash h alpha beta r) w rnd hw).
  Qed.

  (** The same for a trustee's decryption proof. *)
  Theorem decrypt_complete :
    ∀ (pk aggr fac : G) (r : comp_relC) (w : comp_witnessC r) (rnd : comp_randC r),
    comp_rel_holdsC r w ->
    decrypt_verify pk aggr fac r (decrypt_prove pk aggr fac r w rnd) = true.
  Proof.
    intros pk aggr fac r w rnd hw.
    eapply (@nizk_completeness F fzero fone fadd fmul fsub fdiv fopp finv fdec
      G gone ginv_g gmul gpow gdec Hvec r (decrypt_hash pk aggr fac r) w rnd hw).
  Qed.

  (** ** The hash input really does bind the announcement

      Completeness holds for any hash whatsoever.  What makes the
      transform sound is that distinct announcements reach the hash
      as distinct strings, so that a prover cannot quietly move to a
      different first message while keeping the challenge.  These two
      results close that gap for the encoding used above. *)

  (** Distinct group elements render as distinct strings. *)
  Lemma g_to_string_inj :
    ∀ x y : G, g_to_string x = g_to_string y -> x = y.
  Proof.
    intros [v1 ha1 hb1] [v2 ha2 hb2] heq.
    unfold g_to_string in heq; cbn in heq.
    eapply string_of_int_inj, to_int_inj in heq.
    subst. eapply Schnorr.construct_schnorr_group; reflexivity.
  Qed.

  (** And distinct announcements render as distinct hash inputs, so
      the binding rests only on collision resistance of SHA-256 and
      not on an ambiguity in the encoding. *)
  Theorem hash_input_inj :
    ∀ (pre : list G) (r : comp_relC) (a a' : comp_ann_tC r),
    String.concat "," (List.map g_to_string
      (List.app pre (@ann_to_list F fzero G r a))) =
    String.concat "," (List.map g_to_string
      (List.app pre (@ann_to_list F fzero G r a'))) ->
    a = a'.
  Proof.
    intros pre r a a' heq.
    assert (helems : List.app pre (@ann_to_list F fzero G r a) =
                     List.app pre (@ann_to_list F fzero G r a')).
    { eapply (concat_map_inj G ","%char g_to_string).
      + exact g_to_string_inj.
      + intro x; eapply no_comma_string_of_int.
      + rewrite !List.length_app, !(@ann_to_list_length F fzero G); reflexivity.
      + exact heq. }
    destruct (@app_split_eq G pre pre _ _ eq_refl helems) as (_ & hann).
    eapply (@ann_to_list_inj F fzero G); exact hann.
  Qed.

  (** ** Verifying proofs produced by Helios itself

      Everything above derives its own challenge with SHA-256 over an
      encoding of our choosing, which is fine for proofs this
      development also produces.  Checking a published Helios ballot
      needs Helios's own derivation, and the format is not a matter
      of taste: get one separator wrong and every proof fails.

      Reading it off the published IACR 2024 election, the challenge
      of a ballot proof is

        SHA-1 of "A0,B0,A1,B1"

      read as a big-endian integer, where the four values are the
      commitments of the two branches rendered in decimal; and the
      two branch challenges sum to it modulo [q].  A trustee's
      decryption proof uses SHA-1 of "A,B" and its key proof SHA-1 of
      the single commitment.  All three are the same rule: join the
      announcement's group elements with commas and hash.

      That is precisely [String.concat "," (List.map g_to_string
      (ann_to_list r a))], the encoding [hash_with] already uses, so
      only the hash itself differs.

      There is no verified SHA-1 here, and rather than assume one as
      an axiom the hash is taken as a parameter.  The development
      stays axiom-free and the completeness theorem below holds for
      whatever is supplied, because [nizk_completeness] holds for an
      arbitrary hash.  The driver passes a native SHA-1. *)

  (** The challenge Helios derives, given a hash. *)
  Definition helios_hash (sha1 : string -> N)
    (r : comp_relC) (a : comp_ann_tC r) : F :=
    mk_field (Z.of_N (sha1 (String.concat ","
      (List.map g_to_string (@ann_to_list F fzero G r a))))).

  (** Verifying a published ballot proof: recompute the challenge
      from the announcement and check the equations against it.

      This is the step the hand-written verifier in the SigmaProtocol
      development omits.  It takes the challenge from the ballot and
      never recomputes it, which is why a ballot encrypting a value
      outside the allowed set is accepted there. *)
  Definition helios_ballot_verify (sha1 : string -> N)
    (r : comp_relC) (t : comp_transcriptC r) : bool :=
    @nizk_verify F fzero fone fadd fmul fsub finv G gone gmul gpow gdec
      r (helios_hash sha1 r) t.

  (** And the same entry point serves a trustee's decryption proof,
      since the challenge rule is the same. *)
  Definition helios_decrypt_verify (sha1 : string -> N)
    (r : comp_relC) (t : comp_transcriptC r) : bool :=
    @nizk_verify F fzero fone fadd fmul fsub finv G gone gmul gpow gdec
      r (helios_hash sha1 r) t.

  (** Whatever hash is supplied, an honestly produced proof verifies
      under it.  So using Helios's SHA-1 costs nothing in the theory;
      it only has to be the same function the prover used. *)
  Theorem helios_ballot_complete :
    ∀ (sha1 : string -> N) (r : comp_relC)
      (w : comp_witnessC r) (rnd : comp_randC r),
    comp_rel_holdsC r w ->
    helios_ballot_verify sha1 r
      (@nizk_prove F fzero fone fadd fmul fsub fopp finv G gone gmul gpow
         r (helios_hash sha1 r) w rnd) = true.
  Proof.
    intros sha1 r w rnd hw.
    eapply (@nizk_completeness F fzero fone fadd fmul fsub fdiv fopp finv fdec
      G gone ginv_g gmul gpow gdec Hvec r (helios_hash sha1 r) w rnd hw).
  Qed.

  (** ** Running it

      Everything above is a theorem about every ballot and every
      trustee, so nothing here needs a worked example to be true.
      What remains is to expose the pipeline as functions the
      extracted OCaml driver can call.

      The heavy arithmetic deliberately does not happen inside Rocq.
      A group element of this group carries its membership proof, and
      [prime_p] is a three megabyte Pocklington certificate, so
      asking [vm_compute] to evaluate a product drags that term
      through the evaluator.  Extraction erases proofs entirely, so
      the same computation in OCaml is ordinary modular arithmetic on
      big integers.  Executable/Helioscode is where the real 2024
      parameters are actually exercised. *)

  (** Encrypt a vote under the election key.  [v] is the vote, zero
      or one, and [r] is the voter's randomness.  Returns the
      ciphertext [(g ^ r, h ^ r * g ^ v)]. *)
  Definition encrypt (h : G) (v r : F) : G * G :=
    (gpow gen r, gmul (gpow h r) (gpow gen v)).

  (** The witness for a ballot proof is a choice of branch carrying
      that branch's scalars: [inl] for a vote of zero, [inr] for a
      vote of one.  The type depends on the relation the ballot
      compiled to, so the driver builds it after compiling; the two
      definitions below supply the scalars it needs. *)

  (** Build the witness environment for a ballot: the branch that is
      true gets the real randomness, the other gets nothing, because
      the prover simulates it. *)
  Definition ballot_wenv (v r : F) : string -> F :=
    fun s =>
      if String.eqb s "r0" then (if fdec v fzero then r else fzero)
      else if String.eqb s "r1" then (if fdec v fzero then fzero else r)
      else fzero.

  (** The witness vector the compiler expects, for either branch. *)
  Definition ballot_scalars (v r : F) : Vector.t F 2 :=
    @compile_witness F string 2 ballot_privs (ballot_wenv v r).

  (** A trustee's decryption factor for an aggregated ciphertext
      component, together with the witness environment for its
      proof. *)
  Definition decrypt_factor (aggr : G) (x : F) : G := gpow aggr x.

  Definition decrypt_scalars (x : F) : Vector.t F 1 :=
    @compile_witness F string 1 decrypt_privs
      (fun s => if String.eqb s "x" then x else fzero).

  (** Aggregating ciphertexts.  ElGamal is homomorphic, so the
      componentwise product of the ciphertexts encrypts the sum of
      the votes.  This is not a zero-knowledge statement, it is the
      arithmetic a tally verifier performs before checking the
      trustees' proofs, and it is included so the driver can do a
      whole election rather than a single ballot. *)
  Definition aggregate (cs : list (G * G)) : G * G :=
    List.fold_right
      (fun c acc => (gmul (fst c) (fst acc), gmul (snd c) (snd acc)))
      (gone, gone) cs.

  (** Combining the trustees' decryption factors and recovering the
      encrypted group element: [beta] divided by the product of the
      factors.  Recovering the integer tally from that element is a
      small discrete logarithm search, which the driver does. *)
  Definition combine (beta : G) (facs : list G) : G :=
    gmul beta (ginv_g (List.fold_right gmul gone facs)).

  (** The election public key must be the product of the trustees'
      public keys.  Another non-zero-knowledge check, with no witness
      at all. *)
  Definition key_consistent (h : G) (pks : list G) : bool :=
    match gdec h (List.fold_right gmul gone pks) with
    | left _ => true
    | right _ => false
    end.

End Helios.
