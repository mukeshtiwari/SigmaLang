From Stdlib Require Import Setoid
  setoid_ring.Field Lia Arith Vector Utf8
  Psatz Bool Pnat BinNatDef BinPos List.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import Util.
From Crypto Require Import Sigma.
From Compiler Require Import LinearRelation LeafValidity
  Composition Degeneracy Vacuity.

Import VectorNotations.

(** * Vacuity of a whole statement, not just of a leaf

    Vacuity.v asks when a single leaf is satisfied by a witness
    anybody could write down.  A compiled statement is a tree, and the
    question has to be asked of the tree, because the answer at the
    root is not the conjunction of the answers at the leaves.

    ** How vacuity travels up the tree

    An [CAnd] node is vacuous only when both children are, since a
    prover must produce both halves.  An [COr] node is vacuous as soon
    as *one* child is, because the prover picks the branch and nobody
    outside learns which.  A [CThresh] node is vacuous when at least
    [t] of its children are, since the prover needs no more than [t]
    witnesses, and in particular it is vacuous whenever [t] is zero,
    whatever its children say.

    That last case is a hole in the compiler as it stands.  The DSL
    elaborates [SThresh t l] through [le_dec t (List.length rs)],
    which accepts [t = 0] because zero is below everything, and the
    relation of such a node is satisfied by the witness that carries
    nothing.  [zero_threshold_is_free] is that fact, and
    [free_witness] is the witness in question.

    ** What is proven

    [free_proof r] is a certificate that [r] can be proven by anyone:
    at a leaf, that every target is the neutral element; at [CAnd], a
    pair; at [COr], a choice of side; at [CThresh], at least [t]
    children with certificates of their own, counted by
    [atleast_gen].  [free_witness] turns such a certificate into an
    actual witness, and [free_proof_is_free] proves that witness
    satisfies [comp_rel_holds].

    The certificate is data rather than a proposition because the
    witness is built from it: which branch of an [COr] is vacuous, and
    which [t] children of a [CThresh] are, is information the
    construction needs and a [Prop] would not carry. *)
Section CompVacuity.

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
    {Hvec : @vector_space F (@eq F) zero one add mul sub
      div opp inv G (@eq G) gid ginv gop gpow}.

  #[local] Notation comp_relC := (@comp_rel F zero G).
  #[local] Notation comp_witnessC := (@comp_witness F zero G).
  #[local] Notation comp_rel_holdsC := (@comp_rel_holds F zero G gid gop gpow).
  #[local] Notation mat_evalC := (@mat_eval F G gid gop gpow).
  #[local] Notation wlist := (wlist_gen comp_witnessC).
  #[local] Notation wcountC := (@wcount F zero G).
  #[local] Notation wholds := (wholds_gen comp_rel_holdsC).
  #[local] Notation vallC := (@vall F zero G).

  (** ** At least [t] children carry a certificate

      A generic walker in the style of [wlist_gen]: it takes the
      predicate as a parameter so that [free_proof] below may pass
      itself, which the guard checker would not accept from a direct
      recursive call under a [Vector.t].

      Each step either spends a child, decrementing the count, or
      skips it.  The empty vector carries a certificate only for a
      count of zero. *)
  Fixpoint atleast_gen (ct : comp_relC -> Type) (t : nat) {n : nat}
    (v : Vector.t comp_relC n) {struct v} : Type :=
    match v with
    | [] => (t = 0)%type
    | r :: v' =>
        ((ct r * atleast_gen ct (Nat.pred t) v') +
         atleast_gen ct t v')%type
    end.

  (** ** A certificate that a statement can be proven by anyone *)
  Fixpoint free_proof (r : comp_relC) : Type :=
    match r with
    | Leaf m n _ pub => ∀ i : Fin.t m, Vector.nth pub i = gid
    | CAnd rl rr => (free_proof rl * free_proof rr)%type
    | COr rl rr => (free_proof rl + free_proof rr)%type
    | CThresh t _ _ rs _ _ => atleast_gen free_proof t rs
    end.

  (** ** The witness the certificate describes *)
  Fixpoint free_witness_list
    (fw : ∀ r : comp_relC, free_proof r -> comp_witnessC r)
    (t : nat) {n : nat} (v : Vector.t comp_relC n) {struct v}
    : atleast_gen free_proof t v -> wlist v :=
    match v as v' return atleast_gen free_proof t v' -> wlist v' with
    | [] => fun _ => tt
    | r :: v' => fun h =>
        match h with
        | inl hp => (Some (fw r (fst hp)),
                     free_witness_list fw (Nat.pred t) v' (snd hp))
        | inr hrest => (None, free_witness_list fw t v' hrest)
        end
    end.

  Fixpoint free_witness (r : comp_relC) : free_proof r -> comp_witnessC r :=
    match r return free_proof r -> comp_witnessC r with
    | Leaf m n mat pub => fun _ => Vector.const zero n
    | CAnd rl rr => fun h =>
        (free_witness rl (fst h), free_witness rr (snd h))
    | COr rl rr => fun h =>
        match h with
        | inl hl => inl (free_witness rl hl)
        | inr hr => inr (free_witness rr hr)
        end
    | CThresh t k xs rs _ _ => fun h => free_witness_list free_witness t rs h
    end.

  (** ** The two facts a threshold node needs

      Enough children carry a witness, and every witness carried is a
      good one. *)
  Lemma free_witness_list_count :
    ∀ (t n : nat) (v : Vector.t comp_relC n)
      (h : atleast_gen free_proof t v),
    (t <= wcountC v (free_witness_list free_witness t v h))%nat.
  Proof.
    intros t n v; revert t.
    induction v as [| r n v ih]; intros t h; cbn in h |- *.
    - subst t; apply Nat.le_0_l.
    - destruct h as [hp | hrest]; cbn.
      + (* a child was spent, so the count went down by one *)
        pose proof (ih (Nat.pred t) (snd hp)) as hih.
        assert (hle : (t <= S (Nat.pred t))%nat) by (destruct t; cbn; lia).
        eapply Nat.le_trans; [exact hle | apply le_n_S; exact hih].
      + exact (ih t hrest).
  Qed.

  Lemma free_witness_list_holds :
    ∀ (t n : nat) (v : Vector.t comp_relC n),
    vallC (fun r => ∀ h : free_proof r,
             comp_rel_holdsC r (free_witness r h)) v ->
    ∀ h : atleast_gen free_proof t v,
    wholds v (free_witness_list free_witness t v h).
  Proof.
    intros t n v; revert t.
    induction v as [| r n v ih]; intros t hall h; cbn in hall, h |- *.
    - exact I.
    - destruct hall as (hr & hrest).
      destruct h as [hp | hskip]; cbn.
      + split; [exact (hr (fst hp)) | exact (ih (Nat.pred t) hrest (snd hp))].
      + split; [exact I | exact (ih t hrest hskip)].
  Qed.

  (** ** The theorem

      A certificate really does hand anybody a witness. *)
  Theorem free_proof_is_free :
    ∀ (r : comp_relC) (h : free_proof r),
    comp_rel_holdsC r (free_witness r h).
  Proof.
    apply (@comp_rel_ind' F zero G
             (fun r => ∀ h : free_proof r, comp_rel_holdsC r (free_witness r h))).
    - (* a leaf with neutral targets is satisfied by the zero witness *)
      intros m n mat pub h; cbn.
      apply neutral_targets_are_free; exact h.
    - intros rl rr ihl ihr h; cbn; split; [apply ihl | apply ihr].
    - intros rl rr ihl ihr h; cbn.
      destruct h as [hl | hr]; [apply ihl | apply ihr].
    - intros t k xs rs Hxs Ht hall h; cbn; split.
      + apply free_witness_list_count.
      + apply free_witness_list_holds; exact hall.
  Qed.

  (** ** A threshold of zero

      No child needs a certificate, because the witness that carries
      nothing already meets the count.  The DSL of Dsl.v admits
      [SThresh 0 l] for any [l], so this is reachable from the surface
      language. *)
  Fixpoint none_certificate {n : nat} (v : Vector.t comp_relC n)
    : atleast_gen free_proof 0 v :=
    match v as v' return atleast_gen free_proof 0 v' with
    | [] => eq_refl
    | r :: v' => inr (none_certificate v')
    end.

  Theorem zero_threshold_is_free :
    ∀ (k : nat) (xs : Vector.t F k) (rs : Vector.t comp_relC k)
      (Hxs : List.NoDup (List.cons zero (Vector.to_list xs)))
      (Ht : (0 <= k)%nat),
    comp_rel_holdsC (CThresh 0 k xs rs Hxs Ht)
      (free_witness (CThresh 0 k xs rs Hxs Ht) (none_certificate rs)).
  Proof.
    intros k xs rs Hxs Ht.
    apply free_proof_is_free.
  Qed.

End CompVacuity.
