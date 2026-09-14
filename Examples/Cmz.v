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

(** * CMZ: keyed-verification anonymous credentials

    CMZ credentials let someone prove they hold a credential, and
    prove facts about the attributes inside it, while revealing
    neither the credential nor the attributes.  The scheme is due to
    Chase, Meiklejohn and Zaverucha; the Rust implementation this
    file follows is Goldberg's [cmz] crate, which compiles its
    protocols into the [sigma-compiler] crate.

    ** The shape of the thing

    A credential holds some number of attributes, which are secret
    scalars, and a message authentication code, which is a pair of
    group elements.  Only the issuer can check a credential, because
    checking needs the same secret key that made it.

    Showing a credential works like this.  The holder rerandomises
    the MAC so the issuer cannot recognise it, publishes a Pedersen
    commitment to each attribute it wishes to hide, and proves in
    zero knowledge that those commitments open to the attributes of a
    credential the issuer once signed.  The issuer, who knows the key,
    can then check validity without learning the attributes.

    ** Why this fits

    Everything CMZ proves is linear.  The [sigma-compiler] crate it
    targets forbids multiplying two private subexpressions and
    forbids multiplying two points, which is exactly the condition
    our [Leaf] implements.  Where the underlying arithmetic really is
    bilinear the scheme publishes an intermediate point and states
    the relation against that instead, so no equation ever contains a
    product of two secrets.

    ** What is parameterised, and where

    Unlike the Helios statements, which are one fixed shape, a CMZ
    statement depends on how many attributes the credential has and
    which of them are being hidden.  The Rust implementation handles
    that with a procedural macro that generates code at compile time.

    Here a statement is ordinary data, so the same thing is a
    function: [show_stmt] and [issue_stmt] below take the attribute
    count and build the statement.  The count can therefore be a
    runtime value, decided when the credential type is, rather than
    baked into generated source.  Everything else follows the same
    division as Helios.v: the statement, its compilation and the
    Fiat-Shamir binding are here, and the actual group elements and
    attribute values arrive from OCaml.

    The group below is the one Helios.v already sets up, reused so
    this file needs no primality work of its own.  A deployment would
    use a prime-order elliptic curve such as Ristretto instead; the
    statements do not change. *)
Section Cmz.

  (** ** The ambient group

      Everything is inherited from Helios.v, purely to avoid
      duplicating the parameters and their certificates.  Nothing
      about CMZ depends on this choice. *)

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

  (** ** Generated names

      A statement over [k] attributes needs [k] attribute names, [k]
      randomiser names and so on, so the names are generated rather
      than written out.  [ix base i] is [base] followed by [i] in
      decimal. *)
  Definition ix (base : string) (i : nat) : string :=
    String.append base (NilEmpty.string_of_uint (Nat.to_uint i)).

  (** The private scalars of a showing proof: one attribute and one
      commitment randomiser per attribute, plus the randomiser of the
      validity equation. *)
  Definition a_ (i : nat) : string := ix "a" i.
  Definition z_ (i : nat) : string := ix "z" i.
  Definition zQ : string := "zQ".

  (** The public points: the Pedersen bases [A] and [B], the
      rerandomised MAC point [P], the issuer's per-attribute public
      keys [X_i], the commitments [C_i] the holder publishes, and the
      validity target [V]. *)
  Definition X_ (i : nat) : string := ix "X" i.
  Definition C_ (i : nat) : string := ix "C" i.

  (** [seq_list k] is [0, 1, ..., k-1], the attribute indices. *)
  Definition seq_list (k : nat) : list nat := List.seq 0 k.

  (** ** The statements *)

  (** The product over the attributes of [X_i] raised to [z_i],
      folded into a point expression.  This is the sum that makes a
      CMZ statement depend on the attribute count. *)
  Fixpoint zX_prod (idxs : list nat) : @gexpr F string :=
    match idxs with
    | List.nil => YOne
    | List.cons i r => YMul (YPow (X_ i) (XPriv (z_ i))) (zX_prod r)
    end.

  Fixpoint aX_prod (idxs : list nat) : @gexpr F string :=
    match idxs with
    | List.nil => YOne
    | List.cons i r => YMul (YPow (X_ i) (XPriv (a_ i))) (aX_prod r)
    end.

  (** One commitment equation: the holder's commitment to attribute
      [i] opens to [a_i] under the rerandomised MAC point [P], blinded
      by [z_i] under the base [A].

      The secret side is written on the left.  That is not cosmetic:
      [TEq a b] elaborates to [a] times the inverse of [b], so the
      side carrying the secrets keeps positive exponents in the
      compiled matrix while the other becomes the public target. *)
  Definition commit_eq_i (i : nat) : @sstmt F string :=
    TEq (YMul (YPow "P" (XPriv (a_ i))) (YPow "A" (XPriv (z_ i))))
        (YPt (C_ i)).

  Fixpoint commit_eqs (idxs : list nat) : @sstmt F string :=
    match idxs with
    | List.nil => TEq YOne YOne
    | List.cons i List.nil => commit_eq_i i
    | List.cons i r => TAnd (commit_eq_i i) (commit_eqs r)
    end.

  (** The validity equation.  The issuer recomputes [V] from its own
      secret key; the holder recomputes it from the blinding factors
      it chose.  The two agree exactly when the committed attributes
      are those of a credential the issuer signed, which is what makes
      the MAC check linear. *)
  Definition validity_eq (k : nat) : @sstmt F string :=
    TEq (YMul (YPow "B" (XPriv zQ)) (zX_prod (seq_list k))) (YPt "V").

  (** Showing a credential with [k] attributes, all hidden. *)
  Definition show_stmt (k : nat) : @sstmt F string :=
    TAnd (commit_eqs (seq_list k)) (validity_eq k).

  (** Requesting issuance of a credential with [k] attributes, all
      hidden from the issuer: one blinded commitment carrying every
      attribute at once, blinded by [s]. *)
  Definition issue_stmt (k : nat) : @sstmt F string :=
    TEq (YMul (YPow "A" (XPriv "s")) (aX_prod (seq_list k))) (YPt "C").

  (** The issuer's own proof, that it issued with the key it
      published.  [P = b * A] fixes the MAC point it chose, [X0 = x0 *
      B] its public key (named [PK0] to keep it clear of the
      attribute keys [X0], [X1] and so on), and [R] ties the two
      together.  The bilinear
      fact behind [R] is linearised by publishing [P] first and
      writing [R] against it, so no equation multiplies two secrets. *)
  Definition issuer_stmt : @sstmt F string :=
    TAnd (TAnd (TEq (YPow "A" (XPriv "b"))  (YPt "P"))
               (TEq (YPow "B" (XPriv "x0")) (YPt "PK0")))
         (TEq (YMul (YPow "P" (XPriv "x0")) (YPow "K" (XPriv "b"))) (YPt "R")).

  (** ** Names in play

      Elaboration needs the set of names already in use, so that the
      gadgets can draw fresh ones.  Neither statement uses a gadget,
      but the interface still asks. *)
  Definition show_names (k : nat) : list string :=
    List.app ("A"::"B"::"P"::"V"::zQ::"s"::"C"::"K"::"PK0"::"R"::nil)%list
      (List.flat_map (fun i => (a_ i :: z_ i :: X_ i :: C_ i :: nil)%list)
         (seq_list k)).

  #[local] Notation elabC :=
    (@elab F fzero fone fadd fopp string VarTypeString "A" "B").

  Definition core_of (k : nat) (s : @sstmt F string) : @stmt F string :=
    match elabC (show_names k) s with
    | Some (c, _) => c
    | None => SEqs List.nil
    end.

  Definition show_core (k : nat) : @stmt F string := core_of k (show_stmt k).
  Definition issue_core (k : nat) : @stmt F string := core_of k (issue_stmt k).
  Definition issuer_core : @stmt F string := core_of 0 issuer_stmt.

  (** ** The private scalars

      A showing proof knows every attribute, every commitment
      randomiser, and the randomiser of the validity equation, so
      [2k + 1] scalars in all. *)
  Definition show_privs_list (k : nat) : list string :=
    List.app (List.flat_map (fun i => (a_ i :: z_ i :: nil)%list) (seq_list k))
      (zQ :: nil)%list.

  Definition issue_privs_list (k : nat) : list string :=
    List.cons "s" (List.map a_ (seq_list k)).

  Definition issuer_privs_list : list string := ("b" :: "x0" :: nil)%list.

  (** ** Checking the statements

      These run by computation for a given attribute count.  Four
      attributes is the size of a typical credential; the checks below
      fix that, and the driver exercises other sizes at runtime. *)
  Definition k4 : nat := 4.

  Example show_elab_ok :
    match elabC (show_names k4) (show_stmt k4) with
    | Some _ => true | None => false end = true.
  Proof. vm_compute; reflexivity. Qed.

  Example issue_elab_ok :
    match elabC (show_names k4) (issue_stmt k4) with
    | Some _ => true | None => false end = true.
  Proof. vm_compute; reflexivity. Qed.

  Example issuer_elab_ok :
    match elabC (show_names 0) issuer_stmt with
    | Some _ => true | None => false end = true.
  Proof. vm_compute; reflexivity. Qed.

  Example show_disj : disj_inv (vdec := String.string_dec) (show_core k4) = true.
  Proof. vm_compute; reflexivity. Qed.
  Example issue_disj : disj_inv (vdec := String.string_dec) (issue_core k4) = true.
  Proof. vm_compute; reflexivity. Qed.
  Example issuer_disj : disj_inv (vdec := String.string_dec) issuer_core = true.
  Proof. vm_compute; reflexivity. Qed.

  Example show_nodup :
    nodupb (vdec := String.string_dec) (show_privs_list k4) = true.
  Proof. vm_compute; reflexivity. Qed.
  Example issue_nodup :
    nodupb (vdec := String.string_dec) (issue_privs_list k4) = true.
  Proof. vm_compute; reflexivity. Qed.

  (** ** Compiling

      As in Helios.v, the instance is a runtime value: the
      commitments, the rerandomised MAC point and the issuer's public
      keys all change with every showing, so compilation happens per
      proof rather than once here. *)

  #[local] Notation comp_relC := (@comp_rel F fzero G).
  #[local] Notation comp_witnessC := (@comp_witness F fzero G).
  #[local] Notation comp_randC := (@comp_rand F fzero G).
  #[local] Notation comp_transcriptC := (@comp_transcript F fzero G).
  #[local] Notation comp_rel_holdsC := (@comp_rel_holds F fzero G gone gmul gpow).
  #[local] Notation comp_ann_tC := (@comp_ann_t F fzero G).

  Definition penvI : string -> F := fun _ => fone.
  Definition node (i : nat) : F := Helios.mk_field (Z.of_nat (S i)).

  (** Compile a statement against a point environment supplied at
      runtime.  [privs] is given as a list and converted, so the
      caller does not have to produce a dependently typed vector. *)
  Definition compile_with (privs : list string) (genv : string -> G)
    (s : @stmt F string) : option comp_relC :=
    @compile F fzero fadd fmul fopp fdec G gone ginv_g gmul gpow
      string String.string_dec (List.length privs)
      (Vector.of_list privs) genv penvI node s.

  Definition show_rel (k : nat) (genv : string -> G) : option comp_relC :=
    compile_with (show_privs_list k) genv (show_core k).

  Definition issue_rel (k : nat) (genv : string -> G) : option comp_relC :=
    compile_with (issue_privs_list k) genv (issue_core k).

  Definition issuer_rel (genv : string -> G) : option comp_relC :=
    compile_with issuer_privs_list genv issuer_core.

  (** The witness scalars, read out of an environment supplied at
      runtime in the same order as the private list. *)
  Definition scalars (privs : list string) (wenv : string -> F) :
    Vector.t F (List.length privs) :=
    @compile_witness F string (List.length privs) (Vector.of_list privs) wenv.

  (** ** Binding the proof

      Same arrangement as Helios.v: the challenge is derived from the
      announcement, the hash is a parameter, and the instance is
      hashed alongside so the challenge is bound to the claim rather
      than only to the first message. *)
  Definition cmz_hash (hash : string -> N) (pre : list G)
    (r : comp_relC) (a : comp_ann_tC r) : F :=
    Helios.mk_field (Z.of_N (hash (String.concat ","
      (List.map Helios.g_to_string
        (List.app pre (@ann_to_list F fzero G r a)))))).

  Definition cmz_prove (hash : string -> N) (pre : list G) (r : comp_relC)
    (w : comp_witnessC r) (rnd : comp_randC r) : comp_transcriptC r :=
    @nizk_prove F fzero fone fadd fmul fsub fopp finv G gone gmul gpow
      r (cmz_hash hash pre r) w rnd.

  Definition cmz_verify (hash : string -> N) (pre : list G) (r : comp_relC)
    (t : comp_transcriptC r) : bool :=
    @nizk_verify F fzero fone fadd fmul fsub finv G gone gmul gpow gdec
      r (cmz_hash hash pre r) t.

  (** An honest proof verifies, for any attribute count, any instance
      and any hash. *)
  Theorem cmz_complete :
    ∀ (hash : string -> N) (pre : list G) (r : comp_relC)
      (w : comp_witnessC r) (rnd : comp_randC r),
    comp_rel_holdsC r w ->
    cmz_verify hash pre r (cmz_prove hash pre r w rnd) = true.
  Proof.
    intros hash pre r w rnd hw.
    eapply (@nizk_completeness F fzero fone fadd fmul fsub fdiv fopp finv fdec
      G gone ginv_g gmul gpow gdec Hvec r (cmz_hash hash pre r) w rnd hw).
  Qed.

End Cmz.
