From Stdlib Require Import Utf8 ZArith
  Vector String List Ascii
  DecimalString DecimalZ Lia.
From Algebra Require Import Hierarchy.
From Utility Require Import Zpstar Sha256 StringInj.
From Crypto Require Import Sigma.
From Compiler Require Import
  LinearRelation Composition Dsl Surface VarType Nizk Serialization Decide.
From Examples Require Import Prime.
Import Vspace Schnorr Zpfield
  VectorNotations.

(** * ThresholdIns: the whole pipeline on one concrete example

    This file is the end of the road.  Everything the rest of the
    development builds in the abstract is instantiated here on a
    single small statement, and then actually run.

    ** The statement, in words

    There is one public generator [gen] and three public group
    elements [h1], [h2] and [h3].  The prover claims:

    - I know a secret number [x1] with [h1] equal to [gen] raised to
      [x1], or
    - I know a secret number [x2] with [h2] equal to [gen] raised to
      [x2], or
    - I know a secret number [x3] with [h3] equal to [gen] raised to
      [x3],

    and at least two of those three claims are ones I can back up.

    The secret exponent attached to a public point in this way is
    called its discrete logarithm.  Recovering it from the public
    point alone is believed to be hard in a well chosen group, which
    is what makes knowing one worth proving.

    The interesting part is that the prover here genuinely holds only
    two of the three.  The scalars [x1] and [x2] are chosen by hand
    and [h1] and [h2] are computed from them.  The third point [h3]
    is built from an exponent that is then thrown away: the witness
    environment [wenvI] returns a dummy value for the name of the
    third secret, and the witness [thr_witness] supplies [None] for
    the third child.  So the threshold machinery is exercised
    honestly, by a prover that is genuinely one witness short.

    ** A demonstration, not a secure setting

    The group is built from [q] equal to 2963 and [p] equal to
    [2 * q + 1].  These numbers are tiny.  A discrete logarithm in a
    group of a few thousand elements is found by trying every
    exponent, in far less than a second, on any machine.  Nothing
    here is secure, and nothing here is meant to be.  The small
    parameters exist so that every check in this file can be settled
    by letting Rocq compute, and so that the extracted program runs
    instantly.  A real deployment would leave this file unchanged
    except for the two numbers, which would have hundreds of digits.

    ** What happens, step by step

    - The statement is written in the surface language of
      Compiler/Surface.v, as [thr_surface].
    - It is elaborated down to the core language of Compiler/Dsl.v,
      giving [thr_core]; [thr_elab_ok] records that elaboration
      succeeded.
    - Three well formedness checkers are run on the core statement.
    - The core statement is compiled into the statement tree
      [thr_rel] of Compiler/Composition.v, which has a threshold node
      with three children.
    - An interactive prover and verifier are instantiated, as
      [thr_prove] and [thr_verify].
    - The protocol is made non-interactive by Fiat-Shamir
      (Compiler/Nizk.v) using SHA-256 from Utility/Sha256.v, and
      [thr_nizk_complete] proves that honest proofs verify.
    - Transcripts are pushed through the wire format of
      Compiler/Serialization.v, and [thr_roundtrip] proves that
      nothing is lost on the way.
    - Finally a handful of wrappers with concrete first order types
      are exported so that the OCaml driver in Executable/ can run
      and time all of this.

    Extraction, the last step, is the translation of these Rocq
    definitions into OCaml source code that can be compiled and run
    outside Rocq; see Extraction/ and
    Executable/Thresholdcode/main.ml. *)
Section ThresholdIns.

  (** ** The two primes

      The group is a Schnorr group: the subgroup of prime order [q]
      inside the multiplicative group of integers modulo [p], where [p]
      is [2 * q + 1].  A prime of that shape is called a safe prime,
      and it makes the subgroup easy to describe, since the squares
      modulo [p] are exactly the elements whose order divides [q].

      Both numbers are far too small to hide anything; see the note at
      the top of the file. *)

  (** The order of the group, and so the modulus of the scalars.
      Exponents, challenges and responses are all counted modulo
      [q]. *)
  Definition q : Z := 2963.
  (** The modulus of the arithmetic the group lives in.  Group
      elements are integers modulo [p]. *)
  Definition p : Z := 2 * q + 1.

  (** [q] is prime.

      The proof is a computation rather than an argument.
      [is_prime_sqrt] of Examples/Prime.v is a boolean primality test,
      [is_prime_sqrt_correct] says that a true answer can be trusted,
      and the kernel evaluates the test on this particular number.
      Doing the same by hand would be a page of arithmetic with nothing
      to learn from it.

      The fact is needed because the field and group constructions of
      Utility/Zpstar.v take the primality of the modulus as an explicit
      argument. *)
  Theorem prime_q : Znumtheory.prime q.
  Proof. eapply is_prime_sqrt_correct. compute; reflexivity. Qed.

  (** [p] is prime, established the same way as [prime_q], and needed
      for the same reason: the Schnorr group construction cannot be
      applied without it. *)
  Theorem prime_p : Znumtheory.prime p.
  Proof. eapply is_prime_sqrt_correct. compute; reflexivity. Qed.

  (** [p] really is [2 * q + 1].

      This is stated rather than left implicit because several
      constructions in Utility/Zpstar.v take the equation as an
      argument.  Knowing the shape of [p] is what lets them build the
      order [q] subgroup and invert inside it. *)
  Theorem safe_prime : p = (2 * q + 1)%Z.
  Proof. compute. exact eq_refl. Qed.

  (** ** The field and the group

      [F] is the field of scalars and [G] is the group of public
      points.  The definitions that follow are plain abbreviations:
      each one fixes the parameters of a general construction from
      Utility/Zpstar.v, so that the rest of the file can write [fadd]
      instead of repeating the modulus and its primality proof at every
      use. *)

  (** The scalar field: the integers modulo [q].  A value is a record
      pairing an integer with a proof that it is already reduced. *)
  Definition F : Type := @Zp q.
  (** The group: the elements of order dividing [q] modulo [p].  A
      value is a record pairing an integer with a proof that it is in
      range and a proof that raising it to [q] gives one. *)
  Definition G : Type := @Schnorr_group p q.

  (** The additive unit of the scalar field. *)
  Definition fzero : F := @Zpfield.zero q prime_q.
  (** The multiplicative unit of the scalar field. *)
  Definition fone : F := @Zpfield.one q prime_q.
  (** Addition of scalars, modulo [q]. *)
  Definition fadd : F -> F -> F := @zp_add q.
  (** Multiplication of scalars, modulo [q]. *)
  Definition fmul : F -> F -> F := @zp_mul q.
  (** Subtraction of scalars, modulo [q]. *)
  Definition fsub : F -> F -> F := @zp_sub q.
  (** Division of scalars.  It is total because [q] is prime, so every
      nonzero scalar has an inverse. *)
  Definition fdiv : F -> F -> F := @zp_div q.
  (** Negation of a scalar. *)
  Definition fopp : F -> F := @zp_opp q prime_q.
  (** The multiplicative inverse of a scalar. *)
  Definition finv : F -> F := @zp_inv q.
  (** Decidable equality on scalars.  Several parts of the pipeline
      need to compare scalars while computing, not merely to state that
      they are equal. *)
  Definition fdec : forall x y : F, {x = y} + {x <> y} := @zp_dec q.
  (** The identity element of the group. *)
  Definition gone : G := @Schnorr.one p q prime_p prime_q.
  (** The group operation, written multiplicatively. *)
  Definition gmul : G -> G -> G := @mul_schnorr_group p q prime_p prime_q.
  (** Raising a group element to a scalar.  This is the operation the
      whole protocol is about: the relation between a public point and
      its discrete logarithm.

      The leading [2] is the cofactor.  A Schnorr group is built inside
      the integers modulo [p] by taking the elements whose order
      divides [q], and that construction needs [p] to have the shape
      [k * q + 1] for some [k].  Here [p] is [2 * q + 1], so the
      cofactor [k] is [2], and [safe_prime] is the proof of exactly
      that equation.  A prime of this shape is called a safe prime. *)
  Definition gpow : G -> F -> G := @pow 2 p q safe_prime prime_p prime_q.
  (** Decidable equality on group elements.  The verifier is a boolean
      function, so it needs to compare points by computation. *)
  Definition gdec : forall x y : G, {x = y} + {x <> y} := @Schnorr.dec_zpstar p q.
  (** The inverse of a group element. *)
  Definition ginv_g : G -> G := @inv_schnorr_group 2 p q safe_prime prime_p prime_q.

  (** The proof that the field and the group fit together as a vector
      space.

      Vector space here means: the group is written multiplicatively,
      scalars act on it by exponentiation, and the expected laws hold,
      for example that raising to a sum of scalars multiplies the two
      results.  Every general theorem of the development is stated for
      an arbitrary pair of a field and a group related in this way, so
      handing over [Hvec] is what allows those theorems to be applied
      to this concrete instance. *)
  Definition Hvec :
    @vector_space F (@eq F) fzero fone fadd fmul fsub fdiv fopp finv
      G (@eq G) gone ginv_g gmul gpow :=
    @pow_vspace 2 p q safe_prime prime_p prime_q.

  (** Build a scalar from an arbitrary integer.

      A scalar is an integer together with a proof that it equals its
      own reduction modulo [q].  [mk_field z] reduces [z] and supplies
      that proof, so any integer literal can be used where a scalar is
      expected.  It is built with [refine] and closed with [Defined]
      rather than [Qed] so that it reduces during evaluation, which
      matters because everything in this file is meant to be
      computed. *)
  Definition mk_field (z : Z) : F.
  Proof.
    refine {| Zpfield.v := Z.modulo z q; Zpfield.Hv := _ |}.
    eapply Z.mod_mod.
    intro ha; discriminate ha.
  Defined.

  (** The first discrete logarithm the prover knows, the scalar three.

      This is a witness: a private value whose existence the proof
      asserts without revealing it.  It is small and public in the
      source, which is fine, because the file demonstrates the
      machinery rather than keeping a secret. *)
  Definition x1 : F := mk_field 3.
  (** The second discrete logarithm the prover knows, the scalar five.
      Together with [x1] these are the only two secrets the prover ever
      has. *)
  Definition x2 : F := mk_field 5.

  (** The generator of the group, the element four.

      The record carries two side conditions: that the value lies
      strictly between zero and [p], and that raising it to [q] modulo
      [p] gives one, which is what places it inside the order [q]
      subgroup.  Both are settled by evaluation rather than by
      argument. *)
  Definition gen : G.
  Proof.
    refine
    {| Schnorr.v := 4;
       Ha := conj eq_refl eq_refl : (0 < 4 < p)%Z;
       Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 4 q p)).
  Defined.

  (** The first public point, [gen] raised to [x1].

      The [Eval compute in] stores the resulting group element as a
      concrete number rather than as an unevaluated exponentiation.
      Later definitions compare points against it, and comparing
      evaluated values is far cheaper. *)
  Definition h1 : G := Eval compute in gpow gen x1.
  (** The second public point, [gen] raised to [x2], evaluated for the
      same reason as [h1]. *)
  Definition h2 : G := Eval compute in gpow gen x2.
  (** The third public point, [gen] raised to the scalar seven.

      The exponent seven occurs only in this line and is never stored
      anywhere the prover can reach.  That is the whole point of the
      example: [h3] is an ordinary group element with an ordinary
      discrete logarithm, but the prover of this file does not have it,
      so it can back up only two of the three claims. *)
  Definition h3 : G := Eval compute in gpow gen (mk_field 7).

  (** ** The statement in the surface language

      The surface language of Compiler/Surface.v is what a user writes.
      It speaks of named public points and named private scalars, and
      is later elaborated into the smaller core language that the
      compiler works on. *)

  (** Names are plain strings in this instance, so string notation is
      opened for the rest of the section. *)
  #[local] Open Scope string_scope.

  (** The example statement, written out.

      [TThresh 2] is the threshold combinator: at least two of the
      statements in the list must hold.  Each entry is an equality
      between two group expressions, where [YPt] names a public point
      and [YPow] raises a named public point to a named private scalar.
      So the three entries say that the first public point is the
      generator raised to the first secret, and likewise for the second
      and the third.

      This is the statement described in words at the top of the
      file. *)
  Definition thr_surface : @sstmt F string :=
    TThresh 2
      (List.cons (TEq (YPt "H1") (YPow "G" (XPriv "x1")))
      (List.cons (TEq (YPt "H2") (YPow "G" (XPriv "x2")))
      (List.cons (TEq (YPt "H3") (YPow "G" (XPriv "x3"))) List.nil))).

  (** Every name the statement mentions, plus two spare ones.

      Elaboration has to know which names are already taken, because it
      invents fresh names for the intermediate variables that some
      surface constructs expand into.  The list holds the generator,
      the three public points and the three private scalars.  The last
      two entries are the names of the Pedersen bases used by the range
      and inequality gadgets.  This statement uses neither gadget, so
      those bases are never touched, but the elaborator takes them
      regardless. *)
  Definition used0 : list string :=
    List.cons "G" (List.cons "H1" (List.cons "H2" (List.cons "H3"
      (List.cons "x1" (List.cons "x2" (List.cons "x3"
      (List.cons "A" (List.cons "B" List.nil)))))))).

  (** Elaboration from the surface language to the core language, with
      all of its parameters already fixed: this file's field
      operations, strings as the type of names together with their
      variable type instance, and the two Pedersen base names. *)
  #[local] Notation elabC :=
    (@elab F fzero fone fadd fopp string VarTypeString "A" "B").

  (** The statement after elaboration, in the core language of
      Compiler/Dsl.v.

      Elaboration may fail, so it returns an option.  The [match] picks
      the successful branch and falls back on the empty conjunction
      otherwise, which keeps the definition total.  The fallback is
      never taken here, and [thr_elab_ok] is the proof of that. *)
  Definition thr_core : @stmt F string :=
    match elabC used0 thr_surface with
    | Some (c, _) => c
    | None => SEqs List.nil
    end.

  (** Elaboration really did succeed, and produced exactly [thr_core]
      while leaving the set of used names unchanged.

      Both sides are closed terms, so the claim is settled by
      evaluating them and observing that they agree.  Besides being a
      sanity check, this equation is a hypothesis of
      [thr_surface_sound] at the end of the file, which is what carries
      the guarantee back up to the surface statement. *)
  Example thr_elab_ok : elabC used0 thr_surface = Some (thr_core, used0).
  Proof. vm_compute; reflexivity. Qed.

  (** ** The instance: names, points and secrets *)

  (** The declared private variables, in order.

      The compiler turns a statement about named secrets into linear
      algebra over a fixed length witness vector, and this vector fixes
      that order: position zero is the first secret, position one the
      second, position two the third.  Its length, three, is what makes
      a compiled witness a vector of three scalars. *)
  Definition privs : Vector.t string 3 := ["x1"; "x2"; "x3"].

  (** The public environment: what each public name stands for.

      It sends the generator name to [gen] and the three point names to
      [h1], [h2] and [h3].  Every other name, including the two unused
      Pedersen bases, is sent to the identity element. *)
  Definition genvI : string -> G :=
    fun s =>
      if String.eqb s "G" then gen
      else if String.eqb s "H1" then h1
      else if String.eqb s "H2" then h2
      else if String.eqb s "H3" then h3
      else gone.

  (** The environment of public scalars.

      This statement mentions none, so the function is constant.  It
      still has to be supplied, because the general definitions take
      one. *)
  Definition penvI : string -> F := fun _ => fone.

  (** The prover's private environment: what each secret name stands
      for.

      The first two names return the two scalars the prover knows.
      Every other name, the third secret included, returns zero.
      Returning zero is not a claim that the third discrete logarithm
      is zero; it is simply a value that is never used, because
      [thr_witness] marks the third child as absent. *)
  Definition wenvI : string -> F :=
    fun s =>
      if String.eqb s "x1" then x1
      else if String.eqb s "x2" then x2
      else fzero.

  (** The public interpolation points used by threshold nodes.

      A threshold node spreads the verifier's single challenge over its
      children by choosing a polynomial whose value at zero is that
      challenge, and giving child number [i] the value of the
      polynomial at a fixed public point.  [node i] is that fixed point
      for child [i], namely the scalar [i + 1].  The points must be
      pairwise different and different from zero, which is why the
      counting starts at one.  Compiler/Shamir.v explains why this
      construction makes the threshold sound. *)
  Definition node (i : nat) : F := mk_field (Z.of_nat (S i)).

  (** The core statement is well formed.

      Well formedness means that every private variable occurring in
      the statement was declared in [privs].  The checker is a boolean
      function, so the fact is established by running it and seeing
      true, rather than by inspecting the statement by hand. *)
  Example thr_wf : wf_stmt (vdec := String.string_dec) privs thr_core = true.
  Proof. vm_compute; reflexivity. Qed.

  (** The declared private variables are pairwise different.

      Duplicates in [privs] would make the mapping from names to
      positions in the witness vector ambiguous, so the compiler
      requires them to be distinct.  Again the check is a computation. *)
  Example thr_nodup : nodupb (vdec := String.string_dec) (Vector.to_list privs) = true.
  Proof. vm_compute; reflexivity. Qed.

  (** The branches of the statement use disjoint sets of private
      variables where they have to.

      Branches that are proved independently, as the children of a
      threshold node are, need independent witnesses; a variable shared
      between two such branches would let one branch's answer constrain
      another's.  The checker confirms that this does not happen
      here. *)
  Example thr_disj : disj_inv (vdec := String.string_dec) thr_core = true.
  Proof. vm_compute; reflexivity. Qed.

  (** ** The compiled protocol *)

  (** Compilation from the core language to a statement tree, with
      every parameter fixed: the field and group operations, strings as
      names with their decidable equality, the three declared secrets,
      the public environments, and the interpolation points. *)
  #[local] Notation compileC :=
    (@compile F fzero fadd fmul fopp fdec G gone ginv_g gmul gpow
      string String.string_dec 3 privs genvI penvI node).

  (** Compilation succeeds.

      Compilation is partial: it returns [None] when a checker fails,
      or when the interpolation points chosen for a threshold node fail
      to be distinct.  Running it here shows that neither happens. *)
  Example thr_compiles :
    match compileC thr_core with Some _ => true | None => false end = true.
  Proof. vm_compute; reflexivity. Qed.

  (** The compiled statement tree.

      This is the object that the prover, the verifier and the
      simulator of Compiler/Composition.v all work against.  For this
      statement it is a threshold node with three leaves, each leaf a
      small linear relation between public points and secret scalars.

      The definition is forced through [Eval vm_compute in] so that
      [thr_rel] is a concrete tree rather than a stuck [match].  That
      matters because the types of almost everything below, the witness
      type, the randomness type and the transcript type, are computed
      from the shape of this tree; if the tree did not reduce, those
      types would not reduce either.  The [None] branch is dead, by
      [thr_compiles], and the dummy leaf there exists only to keep the
      definition total. *)
  Definition thr_rel : @comp_rel F fzero G :=
    Eval vm_compute in
      match compileC thr_core with
      | Some r => r
      | None => Leaf 0 0 [] []
      end.

  (** Shorthands for four families of Compiler/Composition.v, applied
      to this file's field and group.  Given a statement tree they
      compute, in order: the type of its witnesses, the type of the
      randomness its prover consumes, the type of its transcripts, and
      the proposition saying that a witness satisfies the statement. *)
  #[local] Notation comp_witnessC := (@comp_witness F fzero G).
  #[local] Notation comp_randC := (@comp_rand F fzero G).
  #[local] Notation comp_transcriptC := (@comp_transcript F fzero G).
  #[local] Notation comp_rel_holdsC := (@comp_rel_holds F fzero G gone gmul gpow).

  (** The prover's witness.

      A witness for a threshold node is one optional witness per child.
      The first two children receive [Some] applied to the compiled
      witness vector, which is [wenvI] read off at each declared name;
      the third receives [None].  The trailing [tt] closes the nested
      tuple that the witness type unfolds to.

      This is where the claim made at the top of the file, that the
      prover holds exactly two of the three discrete logarithms,
      becomes a concrete term. *)
  Definition thr_witness : comp_witnessC thr_rel :=
    (Some (compile_witness privs wenvI),
     (Some (compile_witness privs wenvI), (None, tt))).

  (** Assemble the randomness the prover consumes.

      A sigma protocol run begins with the prover sending a first
      message, called the announcement, computed from fresh random
      values.  Each of the three children needs one vector of three
      random scalars for its announcement, which are [u1], [u2] and
      [u3].  Beyond that the threshold node needs one free challenge
      per child it is going to fake, and with three children and a
      threshold of two that is exactly one, the argument [d].

      In a real deployment every one of these values would be drawn
      uniformly at random and never reused.  Here they are taken as
      arguments so that the extracted program can supply whatever it
      likes. *)
  Definition thr_rand (u1 u2 u3 : Vector.t F 3) (d : F) : comp_randC thr_rel :=
    ((u1, (u2, (u3, tt))), [d]).

  (** The interactive prover.

      Given a witness, the randomness and the verifier's challenge [c],
      it produces a transcript: the announcement, together with the
      responses computed from the challenge.  A transcript is the full
      record of one protocol run.  The definition only fixes the
      parameters of the general [comp_prove]. *)
  Definition thr_prove (w : comp_witnessC thr_rel) (rnd : comp_randC thr_rel) (c : F) :
    comp_transcriptC thr_rel :=
    @comp_prove F fzero fone fadd fmul fsub fopp finv G gone gmul gpow thr_rel w rnd c.

  (** The interactive verifier.

      Given the challenge it sent and a transcript, it returns true
      exactly when the transcript is accepting.  It is a boolean
      function of public data only, so anybody can run it. *)
  Definition thr_verify (c : F) (t : comp_transcriptC thr_rel) : bool :=
    @comp_verify F fzero fone fadd fmul fsub finv G gone gmul gpow gdec thr_rel c t.

  (** The prover's witness really satisfies the compiled statement.

      In principle this is a statement about group elements that could
      be proved by hand, but there is nothing to gain: both sides are
      concrete numbers.  Compiler/Decide.v provides a boolean version
      of the relation together with a soundness theorem, so the proof
      runs the boolean version, obtains true, and transports that
      answer to the proposition.

      Concretely the claim is twofold: each of the first two children
      really is a correct discrete logarithm statement for the scalar
      the prover holds, and the number of children that carry a
      witness, two, reaches the threshold. *)
  Lemma thr_holds : comp_rel_holdsC thr_rel thr_witness.
  Proof.
    eapply (@comp_rel_holdsb_sound F fzero G gone gmul gpow gdec).
    vm_compute; reflexivity.
  Qed.

  (** ** Making it non-interactive: strong Fiat-Shamir with SHA-256

      In the interactive protocol the verifier draws the challenge at
      random after seeing the prover's announcement.  The Fiat-Shamir
      transformation replaces that verifier by a hash function: the
      prover computes the challenge itself, as the hash of its own
      announcement.  Since it cannot predict the hash before committing
      to the announcement, it is in much the same position as if a
      verifier had answered.  The outcome is a single message that
      anybody can check later, with nobody to talk to.

      The strong form of the transformation, recommended by Bernhard,
      Pereira and Warinschi, insists that the hash input contain not
      only the announcement but the entire instance: which statement is
      being proved, and about which public points.  If only the
      announcement were hashed, a proof made for one statement could be
      replayed as a proof of a different statement that happens to
      produce the same announcement.  That is why [thr_hash_elems]
      places the generator and all three public points in front of the
      announcement. *)

  (** Render a group element as a decimal string.

      A hash consumes bytes, so group elements have to be written down
      first.  A group element is an integer strictly between zero and
      [p], and this writes that integer the ordinary way, with no
      padding and no sign. *)
  Definition g_to_string (g : G) : string :=
    NilEmpty.string_of_int (Z.to_int (@Schnorr.v p q g)).

  (** The list of group elements that go into the hash.

      First the instance: the generator and the three public points.
      Then the whole announcement, flattened into a list by
      [ann_to_list] of Compiler/Nizk.v, which walks the statement tree
      and collects every group element in order.

      Flattening loses nothing.  The shape of the tree is fixed by
      [thr_rel] and each node contributes a known number of elements,
      so the list can be read back unambiguously; [ann_to_list_inj] is
      the proof, and it is what makes [thr_hash_input_inj] below
      possible. *)
  Definition thr_hash_elems (a : @comp_ann_t F fzero G thr_rel) : list G :=
    List.app
      (List.cons gen (List.cons h1 (List.cons h2 (List.cons h3 List.nil))))
      (ann_to_list thr_rel a).

  (** The challenge, as a function of the announcement.

      The elements are rendered one by one, joined into a single string
      with commas as separators, hashed with SHA-256, and the resulting
      number is reduced modulo [q] so that it lands in the scalar
      field.

      This function is what gets handed to the Fiat-Shamir
      transformation as the stand-in for the verifier.  The whole
      instance is inside it, through [thr_hash_elems], which is what
      makes this the strong variant. *)
  Definition thr_hash (a : @comp_ann_t F fzero G thr_rel) : F :=
    mk_field (Z.of_N (sha256_string (String.concat ","
      (List.map g_to_string (thr_hash_elems a))))).

  (** Distinct group elements get distinct strings.

      Two group elements with the same decimal rendering carry the same
      underlying integer, and two group elements with the same integer
      are equal: the other two fields of the record are proofs of
      statements about integers, and such proofs are unique, so they
      cannot tell two records apart.  The step from equal strings back
      to equal integers is injectivity of decimal notation, taken from
      the standard library through Utility/StringInj.v. *)
  Lemma g_to_string_inj :
    ∀ g₁ g₂ : G, g_to_string g₁ = g_to_string g₂ -> g₁ = g₂.
  Proof.
    intros [v₁ ha₁ hb₁] [v₂ ha₂ hb₂] heq.
    unfold g_to_string in heq; cbn in heq.
    eapply string_of_int_inj, to_int_inj in heq.
    subst.
    eapply Schnorr.construct_schnorr_group; reflexivity.
  Qed.

  (** The string fed to the hash determines the announcement.

      If two announcements render to the same string, they are the same
      announcement.

      Why this matters: Fiat-Shamir is only as good as the binding
      between the announcement and the challenge.  If two different
      announcements could produce the same hash input, a prover could
      commit to one of them and later claim the other, and the
      challenge would no longer be tied to what was actually committed.
      That kind of ambiguity would come from the rendering, not from
      SHA-256, so it has to be ruled out here, where the rendering is
      chosen.

      Why it is true, in three ingredients.  The separator is a comma
      and no rendered element ever contains a comma, so the joined
      string can be split back into the individual renderings; that is
      [concat_map_inj] of Utility/StringInj.v, which also asks that the
      two lists have the same length, and they do because the instance
      prefix is fixed and both announcements have the shape of the same
      tree.  The rendering of a single element is injective, by
      [g_to_string_inj].  Finally the instance prefix has a known
      length of four, so the recovered list splits at a known position
      into the prefix and the flattened announcement, and
      [ann_to_list_inj] turns the flattened announcement back into the
      announcement itself. *)
  Theorem thr_hash_input_inj :
    ∀ a a' : @comp_ann_t F fzero G thr_rel,
    String.concat "," (List.map g_to_string (thr_hash_elems a))
      = String.concat "," (List.map g_to_string (thr_hash_elems a')) ->
    a = a'.
  Proof.
    intros a a' heq.
    assert (helems : thr_hash_elems a = thr_hash_elems a').
    { eapply (concat_map_inj G ","%char g_to_string).
      + exact g_to_string_inj.
      + intro x; eapply no_comma_string_of_int.
      + unfold thr_hash_elems.
        rewrite !List.length_app, !ann_to_list_length; reflexivity.
      + exact heq. }
    unfold thr_hash_elems in helems.
    destruct (app_split_eq _ _ _ _ _ eq_refl helems) as (_ & hann).
    eapply ann_to_list_inj; exact hann.
  Qed.

  (** The non-interactive prover.

      It takes a witness and the randomness, but no challenge: the
      challenge is computed by [thr_hash] from the announcement that
      the prover has just produced.  The result is a transcript that
      can be published as it stands. *)
  Definition thr_nizk_prove (w : comp_witnessC thr_rel) (rnd : comp_randC thr_rel) :
    comp_transcriptC thr_rel :=
    @nizk_prove F fzero fone fadd fmul fsub fopp finv G gone gmul gpow thr_rel thr_hash w rnd.

  (** The non-interactive verifier.

      It takes a transcript alone.  It recomputes the challenge from
      the announcement inside that transcript, with the same hash, and
      then performs the ordinary verification.  There is no challenge
      argument and no interaction: this is a check anybody can run on a
      proof they were handed. *)
  Definition thr_nizk_verify (t : comp_transcriptC thr_rel) : bool :=
    @nizk_verify F fzero fone fadd fmul fsub finv G gone gmul gpow gdec thr_rel thr_hash t.

  (** Honest proofs are accepted, whatever randomness is used.

      This is completeness: when the prover follows the protocol with a
      witness that really satisfies the statement, the verifier answers
      true.  The quantifier over [rnd] says this holds for every choice
      of the random values, not merely for a lucky one.

      It follows from the general completeness theorem of
      Compiler/Nizk.v applied to this instance, with [thr_holds]
      supplying the fact that the witness is genuine and [Hvec]
      supplying the algebra.

      Completeness is the direction that can be proved outright.  The
      other two properties one wants of a proof system, soundness and
      zero knowledge, hold for the non-interactive protocol only in the
      random oracle model, which is an assumption about the hash
      function rather than a theorem; the development deliberately does
      not assume it, and so stays free of axioms. *)
  Theorem thr_nizk_complete :
    ∀ rnd : comp_randC thr_rel,
    thr_nizk_verify (thr_nizk_prove thr_witness rnd) = true.
  Proof.
    intros rnd.
    eapply (@nizk_completeness F fzero fone fadd fmul fsub fdiv fopp finv fdec
      G gone ginv_g gmul gpow gdec Hvec thr_rel thr_hash thr_witness rnd thr_holds).
  Qed.

  (** ** The wire format *)

  (** Serialise a transcript into a flat list of scalars and group
      elements.

      This is the shape a proof takes when it leaves the program: a
      sequence of values with no tree structure and no labels.  The
      structure is recovered on the other side from the statement tree,
      which both parties already know. *)
  Definition thr_encode (t : comp_transcriptC thr_rel) : @wire F G :=
    @encode F fzero G thr_rel t.

  (** Read a transcript back off the wire.

      It returns the transcript together with whatever input is left
      over, so that a proof can sit inside a larger message, or [None]
      when the input does not match the shape that [thr_rel]
      demands. *)
  Definition thr_decode (l : @wire F G) : option (comp_transcriptC thr_rel * @wire F G) :=
    @decode F fzero G thr_rel l.

  (** Every proof the prover emits survives the round trip.

      Decoding the encoding of an honest non-interactive proof returns
      exactly that proof, with nothing left over.  As with completeness
      the statement is quantified over all randomness, so it covers
      every proof this prover can ever produce.

      Why it is true: the general round trip theorem of
      Compiler/Serialization.v needs the transcript to be well formed,
      meaning that its shape matches the statement tree, and [prove_wf]
      says that transcripts produced by the prover always are. *)
  Theorem thr_roundtrip :
    ∀ rnd : comp_randC thr_rel,
    thr_decode (thr_encode (thr_nizk_prove thr_witness rnd)) =
    Some (thr_nizk_prove thr_witness rnd, List.nil).
  Proof.
    intros rnd.
    eapply serialize_deserialize_full.
    eapply prove_wf.
  Qed.

  (** ** What the verifier learns *)

  (** An accepting proof means the surface statement holds.

      Everything above establishes facts about the compiled statement.
      This corollary carries one of them back up to the language the
      user actually wrote in: if a private environment [wenv] satisfies
      the core statement [thr_core], then either it satisfies the
      original surface statement [thr_surface], or the public
      environment is degenerate.

      Degenerate means that the two Pedersen bases are related in a way
      that breaks the gadgets: one of them is the identity, or one is a
      known power of the other.  It is an escape clause in the general
      elaboration theorem, because a caller who supplies bad bases
      cannot be promised anything.  This statement uses no gadget that
      needs the bases, so the clause is irrelevant here, but the
      general theorem states it and the corollary inherits it.

      In plain words: what the protocol proves is knowledge of at least
      two of the three discrete logarithms, as written, and not some
      weaker property that happens to survive compilation. *)
  Corollary thr_surface_sound :
    ∀ wenv : string -> F,
    @stmt_denote F fadd fmul fopp G gone gmul gpow string genvI penvI wenv thr_core ->
    @sstmt_denote F fzero fone fadd fmul fopp G gone ginv_g gmul gpow string VarTypeString
      penvI genvI wenv thr_surface
    ∨ @degenerate F G gone gpow string "A" "B" genvI.
  Proof.
    intros wenv hd.
    eapply (elab_sound (Fdec := fdec) penvI "A" "B" (Hvec := Hvec) thr_surface used0 used0
      thr_core genvI wenv thr_elab_ok hd).
  Qed.

  (** ** Exported wrappers for the OCaml driver

      Everything above can be evaluated inside Rocq, but evaluating it
      inside Rocq is slow and says nothing about how the protocol
      behaves as a program.  The definitions in this last section exist
      to be extracted: translated into OCaml source by Extraction/,
      compiled, and driven by Executable/Thresholdcode/main.ml, which
      feeds them scalars and times the runs.

      They take their arguments one scalar at a time and return plain
      tuples of booleans and numbers.  The point is to keep the
      interface first order and free of dependent types, which are
      awkward to call from hand written OCaml. *)

  (** Build the prover's randomness out of ten separate scalars.

      Three for each of the three children's announcements, and one
      free challenge for the threshold node.  The driver generates ten
      values and passes them in positionally. *)
  Definition mk_rand (a b c d e f g h i j : F) : comp_randC thr_rel :=
    thr_rand [a; b; c] [d; e; f] [g; h; i] j.

  (** One interactive run.

      Given ten random scalars and a challenge, it proves, verifies,
      and returns whether verification succeeded together with the
      number of wire elements the transcript occupies.  The second
      component is the proof size, which is what the driver reports. *)
  Definition thr_run (a b c d e f g h i j ch : F) : bool * nat :=
    let t := thr_prove thr_witness (mk_rand a b c d e f g h i j) ch in
    (thr_verify ch t, List.length (thr_encode t)).

  (** One non-interactive run.

      It produces a proof, encodes it, and returns three things:
      whether the proof verifies, whether it still verifies after being
      written to the wire and read back, and its size in wire elements.
      The middle component checks the round trip in practice, next to
      [thr_roundtrip], which settles it in principle. *)
  Definition thr_nizk_run (a b c d e f g h i j : F) : bool * bool * nat :=
    let t := thr_nizk_prove thr_witness (mk_rand a b c d e f g h i j) in
    let w := thr_encode t in
    (thr_nizk_verify t,
     match thr_decode w with
     | Some (t', List.nil) => thr_nizk_verify t'
     | _ => false
     end,
     List.length w).

  (** A tampered proof, which the verifier is expected to reject.

      It produces an honest proof and then overwrites the responses of
      the first child, replacing every one of them by the scalar [z],
      before running the non-interactive verifier.  The expected answer
      is false.

      This is a negative test meant to be run from OCaml.  The theorems
      above say that honest proofs are accepted; a run of this says
      that a damaged one is not.  It is evidence rather than a proof: a
      tampering that went undetected would be a bug, but the check
      coming out false does not by itself establish soundness. *)
  Definition thr_nizk_tamper (a b c d e f g h i j z : F) : bool :=
    let t := thr_nizk_prove thr_witness (mk_rand a b c d e f g h i j) in
    match t with
    | ((t1, rest), cs) =>
        thr_nizk_verify (((fst t1, Vector.map (fun _ => z) (snd t1)), rest), cs)
    end.

End ThresholdIns.
