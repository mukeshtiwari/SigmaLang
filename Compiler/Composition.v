From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef
  BinPos Permutation List PeanoNat
  FunctionalExtensionality FinFun.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Probability Require Import
  Prob Distr.
From Utility Require Import
  Util.
From ExtLib.Structures Require Import
  Monad.
From Crypto Require Import
  Sigma.
From Compiler Require Import
  LinearRelation Lagrange Shamir.

Import MonadNotation
  VectorNotations.

#[local] Open Scope monad_scope.

(*
  Composition of linear-relation sigma protocols by structural
  induction on a statement tree:

      comp_rel ::= Leaf (mat, pub) | CAnd comp_rel comp_rel
                 | COr comp_rel comp_rel
                 | CThresh t k xs [r₁; …; rₖ]

  - Leaf: the generic Maurer protocol of LinearRelation.v.
  - CAnd: both children share the challenge.
  - COr (CDS composition): the transcript stores the left child's
    challenge c₁; the right child's challenge is c - c₁, so the two
    sub-challenges always sum to the top-level challenge.  The prover
    simulates the branch it has no witness for using a
    pre-committed challenge and answers the other branch honestly.
  - CThresh (Shamir / CDS threshold, t-out-of-k): child i receives
    the value at node xs[i] of a polynomial of degree ≤ k - t through
    (0, c).  The transcript stores the polynomial's values at the
    first k - t nodes; the verifier re-interpolates.  The prover
    picks exactly k - t children to simulate (every child it has no
    witness for, plus enough others) and chooses their challenges
    freely; the remaining t children are answered honestly at the
    interpolated challenge.  Two accepting transcripts at different
    top challenges induce interpolants differing at ≥ t nodes, so ≥ t
    witnesses are extracted.  The node list xs and the side
    conditions (0 ∉ xs, xs duplicate-free, |xs| = k, t ≤ k) are
    carried by the constructor.

  Witness, transcript, and randomness *types* are computed by
  recursion on the tree (nested products) — no heterogeneous vector
  machinery, and every function and proof proceeds by the same
  structural induction (comp_rel_ind', which supplies a Forall
  hypothesis for the children of a threshold node).

  Besides completeness, special soundness and the accept-bit form of
  SHVZK, we prove that the real and simulated transcript
  distributions are equal as distributions (permutations of each
  other) when the challenge space is sampled from a duplicate-free,
  complete enumeration of the field.  Witness indistinguishability
  of the OR / threshold composition follows as a corollary.
*)

(* ---------- generic list lemmas used by the threshold node ---------- *)
Section ListLemmas.
  Context {A : Type}.

  Lemma in_firstn : ∀ (l : list A) (n : nat) (x : A),
    List.In x (List.firstn n l) -> List.In x l.
  Proof.
    induction l as [|y l ih]; intros [|n] x hin; cbn in hin;
    try contradiction.
    destruct hin as [hin | hin]; [left; exact hin | right; eapply ih; exact hin].
  Qed.

  Lemma nodup_firstn : ∀ (l : list A) (n : nat),
    List.NoDup l -> List.NoDup (List.firstn n l).
  Proof.
    intros * hnd.
    rewrite <-(List.firstn_skipn n l) in hnd.
    eapply List.NoDup_app_remove_r; exact hnd.
  Qed.

  Lemma nth_firstn' : ∀ (l : list A) (n i : nat) (d : A),
    (i < n)%nat -> List.nth i (List.firstn n l) d = List.nth i l d.
  Proof.
    induction l as [|y l ih]; intros [|n] [|i] d hi; cbn; try lia;
    try reflexivity.
    eapply ih; lia.
  Qed.

  Lemma combine_map_fst : ∀ {B : Type} (l : list A) (l' : list B),
    List.length l = List.length l' ->
    List.map fst (List.combine l l') = l.
  Proof.
    induction l as [|y l ih]; intros [|z l'] hl; cbn in *; try lia;
    try reflexivity.
    rewrite ih; [reflexivity | lia].
  Qed.

  Lemma nth_map_seq : ∀ {B : Type} (f : nat -> B) (k i : nat) (d : B),
    (i < k)%nat -> List.nth i (List.map f (List.seq 0 k)) d = f i.
  Proof.
    intros * hi.
    rewrite (List.nth_indep (List.map f (List.seq 0 k)) d (f 0)).
    +
      rewrite List.map_nth, List.seq_nth; [reflexivity | exact hi].
    +
      rewrite List.map_length, List.seq_length; exact hi.
  Qed.

End ListLemmas.

Section Composition.

  (* Underlying Field of Vector Space *)
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}.

  (* Vector Element *)
  Context
    {G : Type}
    {gid : G}
    {ginv : G -> G}
    {gop : G -> G -> G}
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}.

  #[local] Infix "^" := gpow.
  #[local] Infix "*" := mul.
  #[local] Infix "/" := div.
  #[local] Infix "+" := add.
  #[local] Infix "-" := sub.

  #[local] Notation "( a ; c ; r )" := (mk_sigma _ _ _ a c r).

  (* The section-closed constants of LinearRelation.v, applied to
     this section's group structure. *)
  #[local] Notation row_evalC :=
    (@row_eval F G gid gop gpow _).
  #[local] Notation mat_evalC :=
    (@mat_eval F G gid gop gpow _ _).
  #[local] Notation verifyC :=
    (@verify_linear_relation_proof F G gid gop gpow Gdec _ _).
  #[local] Notation lag_interpF :=
    (@lag_interp F zero one add mul sub inv).

  Section Def.

    (* The statement tree.  The children of a threshold node are a
       vector so that the node list xs can be tied to their number
       without mentioning comp_rel in a Prop (positivity). *)
    Inductive comp_rel : Type :=
    | Leaf (m n : nat)
        (mat : Vector.t (Vector.t G n) m)
        (pub : Vector.t G m) : comp_rel
    | CAnd (rl rr : comp_rel) : comp_rel
    | COr (rl rr : comp_rel) : comp_rel
    | CThresh (t k : nat) (xs : Vector.t F k) (rs : Vector.t comp_rel k)
        (Hxs : List.NoDup (List.cons zero (Vector.to_list xs)))
        (Ht : (t <= k)%nat) : comp_rel.

    (* A predicate holding of every child *)
    Fixpoint vall (P : comp_rel -> Prop) {n : nat}
      (v : Vector.t comp_rel n) : Prop :=
      match v with
      | [] => True
      | r :: v' => P r ∧ vall P v'
      end.

    Lemma vall_mono :
      ∀ (P Q : comp_rel -> Prop) (n : nat) (v : Vector.t comp_rel n),
      vall P v -> (∀ r, P r -> Q r) -> vall Q v.
    Proof.
      induction v as [| r n v ih]; intros hp hpq; cbn in hp |- *.
      + exact I.
      + destruct hp as (hr & hv).
        split; [eapply hpq; exact hr | eapply ih; assumption].
    Qed.

    (* Structural induction with a hypothesis for every child of a
       threshold node. *)
    Section Induction.
      Variable P : comp_rel -> Prop.
      Hypothesis HLeaf : ∀ m n mat pub, P (Leaf m n mat pub).
      Hypothesis HAnd : ∀ rl rr, P rl -> P rr -> P (CAnd rl rr).
      Hypothesis HOr : ∀ rl rr, P rl -> P rr -> P (COr rl rr).
      Hypothesis HThresh : ∀ t k xs rs Hxs Ht,
        vall P rs -> P (CThresh t k xs rs Hxs Ht).

      Fixpoint comp_rel_ind' (r : comp_rel) : P r :=
        match r with
        | Leaf m n mat pub => HLeaf m n mat pub
        | CAnd rl rr => HAnd rl rr (comp_rel_ind' rl) (comp_rel_ind' rr)
        | COr rl rr => HOr rl rr (comp_rel_ind' rl) (comp_rel_ind' rr)
        | CThresh t k xs rs Hxs Ht =>
            HThresh t k xs rs Hxs Ht
              ((fix go (n : nat) (v : Vector.t comp_rel n) : vall P v :=
                  match v as v' return vall P v' with
                  | [] => I
                  | r' :: v' => conj (comp_rel_ind' r') (go _ v')
                  end) k rs)
        end.
    End Induction.

    (* ---------- per-child walkers ----------
       comp_rel is a nested inductive (a threshold node holds a
       vector of children), so recursion over the children is done
       by generic walkers parameterised by the function being
       defined; the local notations below instantiate them. *)

    Fixpoint wlist_gen (cw : comp_rel -> Type) {n : nat}
      (v : Vector.t comp_rel n) {struct v} : Type :=
      match v with
      | [] => unit
      | r :: v' => (option (cw r) * wlist_gen cw v')%type
      end.

    Fixpoint tlist_gen (ct : comp_rel -> Type) {n : nat}
      (v : Vector.t comp_rel n) {struct v} : Type :=
      match v with
      | [] => unit
      | r :: v' => (ct r * tlist_gen ct v')%type
      end.

    (* Witness type, computed from the tree: an OR witness is a
       witness for one branch; a threshold witness is an optional
       witness per child (the relation additionally requires at
       least t of them to be present). *)
    Fixpoint comp_witness (r : comp_rel) : Type :=
      match r with
      | Leaf m n _ _ => Vector.t F n
      | CAnd rl rr => (comp_witness rl * comp_witness rr)%type
      | COr rl rr => (comp_witness rl + comp_witness rr)%type
      | CThresh _ _ _ rs _ _ => wlist_gen comp_witness rs
      end.

    (* Number of witnesses present in a threshold witness *)
    Fixpoint wcount {n : nat} (v : Vector.t comp_rel n) {struct v} :
      wlist_gen comp_witness v -> nat :=
      match v as v' return wlist_gen comp_witness v' -> nat with
      | [] => fun _ => 0
      | r :: v' => fun w =>
          ((match fst w with Some _ => 1 | None => 0 end) +
            wcount v' (snd w))%nat
      end.

    Fixpoint wholds_gen (ch : ∀ r : comp_rel, comp_witness r -> Prop)
      {n : nat} (v : Vector.t comp_rel n) {struct v} : wlist_gen comp_witness v -> Prop :=
      match v as v' return wlist_gen comp_witness v' -> Prop with
      | [] => fun _ => True
      | r :: v' => fun w =>
          (match fst w with
           | Some x => ch r x
           | None => True
           end) ∧ wholds_gen ch v' (snd w)
      end.

    (* The relation the composed protocol proves *)
    Fixpoint comp_rel_holds (r : comp_rel) :
      comp_witness r -> Prop :=
      match r return comp_witness r -> Prop with
      | Leaf m n mat pub => fun xs => mat_evalC mat xs = pub
      | CAnd rl rr => fun w =>
          comp_rel_holds rl (fst w) ∧ comp_rel_holds rr (snd w)
      | COr rl rr => fun w =>
          match w with
          | inl wl => comp_rel_holds rl wl
          | inr wr => comp_rel_holds rr wr
          end
      | CThresh t _ _ rs _ _ => fun w =>
          (t <= wcount rs w)%nat ∧ wholds_gen comp_rel_holds rs w
      end.

    (* Transcript shape, computed from the tree.  A leaf transcript
       is (announcement, response); its challenge is supplied
       externally.  An OR transcript additionally stores the left
       child's challenge c₁ (the right child's is the difference).
       A threshold transcript stores the k - t compressed
       challenges (values at the first k - t nodes). *)
    Fixpoint comp_transcript (r : comp_rel) : Type :=
      match r with
      | Leaf m n _ _ => (Vector.t G m * Vector.t F n)%type
      | CAnd rl rr => (comp_transcript rl * comp_transcript rr)%type
      | COr rl rr =>
          (comp_transcript rl * comp_transcript rr * F)%type
      | CThresh _ _ _ rs _ _ => (tlist_gen comp_transcript rs * list F)%type
      end.

    (* Prover randomness: leaf commitment randomness, plus — at each
       OR node — the challenge used for the simulated branch, and —
       at each threshold node — the k - t free challenges. *)
    Fixpoint comp_rand (r : comp_rel) : Type :=
      match r with
      | Leaf m n _ _ => Vector.t F n
      | CAnd rl rr => (comp_rand rl * comp_rand rr)%type
      | COr rl rr => (comp_rand rl * comp_rand rr * F)%type
      | CThresh t k _ rs _ _ =>
          (tlist_gen comp_rand rs * Vector.t F (k - t))%type
      end.

    (* Number of field elements drawn by the prover / simulator *)
    Fixpoint slist_gen (cs : comp_rel -> nat) {n : nat}
      (v : Vector.t comp_rel n) {struct v} : nat :=
      match v with
      | [] => 0
      | r :: v' => (cs r + slist_gen cs v')%nat
      end.

    Fixpoint comp_size (r : comp_rel) : nat :=
      match r with
      | Leaf m n _ _ => n
      | CAnd rl rr => (comp_size rl + comp_size rr)%nat
      | COr rl rr => S (comp_size rl + comp_size rr)
      | CThresh t k _ rs _ _ => (slist_gen comp_size rs + (k - t))%nat
      end.

    (* ---------- threshold challenge sharing ---------- *)

    (* The interpolant through (0, c) and the given (node, value)
       pairs, as a function of the node. *)
    Definition expand_chal (c : F) (nodes vals : list F) : F -> F :=
      lag_interpF (List.cons (zero, c) (List.combine nodes vals)).

    (* Challenge of child i: the interpolant at node xs[i]. *)
    Definition chal_of (xs : list F) (f : F -> F) (i : nat) : F :=
      f (List.nth i xs zero).

    (* Which children the prover simulates: every child without a
       witness, plus the first `seeds` children with one. *)
    Fixpoint sim_flags {n : nat} (v : Vector.t comp_rel n) {struct v} :
      wlist_gen comp_witness v -> nat -> list bool :=
      match v as v' return wlist_gen comp_witness v' -> nat -> list bool with
      | [] => fun _ _ => List.nil
      | r :: v' => fun w seeds =>
          match fst w with
          | None => List.cons true (sim_flags v' (snd w) seeds)
          | Some _ =>
              match seeds with
              | 0 => List.cons false (sim_flags v' (snd w) 0)
              | S k => List.cons true (sim_flags v' (snd w) k)
              end
          end
      end.

    Fixpoint count_true (fl : list bool) : nat :=
      match fl with
      | List.nil => 0
      | List.cons b fl' => ((if b then 1 else 0) + count_true fl')%nat
      end.

    (* The nodes of the flagged children *)
    Fixpoint select_nodes (xs : list F) (fl : list bool) : list F :=
      match xs, fl with
      | List.cons x xs', List.cons b fl' =>
          if b then List.cons x (select_nodes xs' fl')
          else select_nodes xs' fl'
      | _, _ => List.nil
      end.

    (* Simulate every child at its challenge *)
    Fixpoint simlist_gen
      (cs : ∀ r : comp_rel, comp_rand r -> F -> comp_transcript r)
      {n : nat} (v : Vector.t comp_rel n) {struct v} :
      tlist_gen comp_rand v -> (nat -> F) -> nat -> tlist_gen comp_transcript v :=
      match v as v' return tlist_gen comp_rand v' -> (nat -> F) -> nat -> tlist_gen comp_transcript v' with
      | [] => fun _ _ _ => tt
      | r :: v' => fun s chal i =>
          (cs r (fst s) (chal i), simlist_gen cs v' (snd s) chal (S i))
      end.

    (* Simulator: builds an accepting transcript for challenge c
       without any witness. *)
    Fixpoint comp_simulate (r : comp_rel) :
      comp_rand r -> F -> comp_transcript r :=
      match r return comp_rand r -> F -> comp_transcript r with
      | Leaf m n mat pub => fun zs c =>
          (zip_with (fun row p => gop (row_evalC row zs) (p ^ (opp c)))
            mat pub, zs)
      | CAnd rl rr => fun s c =>
          (comp_simulate rl (fst s) c, comp_simulate rr (snd s) c)
      | COr rl rr => fun s c =>
          (comp_simulate rl (fst (fst s)) (snd s),
           comp_simulate rr (snd (fst s)) (c - snd s),
           snd s)
      | CThresh t k xs rs _ _ => fun s c =>
          (simlist_gen comp_simulate rs (fst s)
             (chal_of (Vector.to_list xs) (expand_chal c (List.firstn (k - t) (Vector.to_list xs))
               (Vector.to_list (snd s)))) 0,
           Vector.to_list (snd s))
      end.

    (* Prove the unflagged children (which hold a witness) and
       simulate the flagged ones, all at their challenge *)
    Fixpoint provelist_gen
      (cp : ∀ r : comp_rel, comp_witness r -> comp_rand r -> F -> comp_transcript r)
      (cs : ∀ r : comp_rel, comp_rand r -> F -> comp_transcript r)
      {n : nat} (v : Vector.t comp_rel n) {struct v} :
      wlist_gen comp_witness v -> tlist_gen comp_rand v -> list bool -> (nat -> F) -> nat -> tlist_gen comp_transcript v :=
      match v as v' return
        wlist_gen comp_witness v' -> tlist_gen comp_rand v' -> list bool -> (nat -> F) -> nat -> tlist_gen comp_transcript v'
      with
      | [] => fun _ _ _ _ _ => tt
      | r :: v' => fun w s fl chal i =>
          ((match fst w, fl with
            | Some x, List.cons false _ => cp r x (fst s) (chal i)
            | _, _ => cs r (fst s) (chal i)
            end),
           provelist_gen cp cs v' (snd w) (snd s) (List.tl fl) chal (S i))
      end.

    (* Prover: honest on the branches it has witnesses for,
       simulated (with the pre-committed challenge from the
       randomness) on the others. *)
    Fixpoint comp_prove (r : comp_rel) :
      comp_witness r -> comp_rand r -> F -> comp_transcript r :=
      match r return comp_witness r -> comp_rand r -> F -> comp_transcript r with
      | Leaf m n mat pub => fun xs us c =>
          (mat_evalC mat us,
           zip_with (fun u x => u + c * x) us xs)
      | CAnd rl rr => fun w s c =>
          (comp_prove rl (fst w) (fst s) c,
           comp_prove rr (snd w) (snd s) c)
      | COr rl rr => fun w s c =>
          match w with
          | inl wl =>
              (comp_prove rl wl (fst (fst s)) (c - snd s),
               comp_simulate rr (snd (fst s)) (snd s),
               c - snd s)
          | inr wr =>
              (comp_simulate rl (fst (fst s)) (snd s),
               comp_prove rr wr (snd (fst s)) (c - snd s),
               snd s)
          end
      | CThresh t k xs rs _ _ => fun w s c =>
          (provelist_gen comp_prove comp_simulate rs w (fst s)
             (sim_flags rs w (wcount rs w - t))
             (chal_of (Vector.to_list xs) (expand_chal c
               (select_nodes (Vector.to_list xs) (sim_flags rs w (wcount rs w - t)))
               (Vector.to_list (snd s)))) 0,
           List.map
             (expand_chal c
               (select_nodes (Vector.to_list xs) (sim_flags rs w (wcount rs w - t)))
               (Vector.to_list (snd s)))
             (List.firstn (k - t) (Vector.to_list xs)))
      end.

    Fixpoint verlist_gen
      (cv : ∀ r : comp_rel, F -> comp_transcript r -> bool)
      {n : nat} (v : Vector.t comp_rel n) {struct v} :
      (nat -> F) -> tlist_gen comp_transcript v -> nat -> bool :=
      match v as v' return (nat -> F) -> tlist_gen comp_transcript v' -> nat -> bool with
      | [] => fun _ _ _ => true
      | r :: v' => fun chal tr i =>
          cv r (chal i) (fst tr) && verlist_gen cv v' chal (snd tr) (S i)
      end.

    (* Verifier: leaf checks are the linear-relation checks; an AND
       passes the same challenge down; an OR verifies the left child
       at the stored challenge c₁ and the right child at c - c₁; a
       threshold node re-expands the compressed challenges. *)
    Fixpoint comp_verify (r : comp_rel) :
      F -> comp_transcript r -> bool :=
      match r return F -> comp_transcript r -> bool with
      | Leaf m n mat pub => fun c t =>
          verifyC mat pub (fst t; [c]; snd t)
      | CAnd rl rr => fun c t =>
          comp_verify rl c (fst t) && comp_verify rr c (snd t)
      | COr rl rr => fun c t =>
          comp_verify rl (snd t) (fst (fst t)) &&
          comp_verify rr (c - snd t) (snd (fst t))
      | CThresh t k xs rs _ _ => fun c tr =>
          Nat.eqb (List.length (snd tr)) (k - t) &&
          verlist_gen comp_verify rs
            (chal_of (Vector.to_list xs) (expand_chal c (List.firstn (k - t) (Vector.to_list xs)) (snd tr)))
            (fst tr) 0
      end.

    Fixpoint salist_gen
      (csa : ∀ r : comp_rel, comp_transcript r -> comp_transcript r -> Prop)
      {n : nat} (v : Vector.t comp_rel n) {struct v} :
      tlist_gen comp_transcript v -> tlist_gen comp_transcript v -> Prop :=
      match v as v' return tlist_gen comp_transcript v' -> tlist_gen comp_transcript v' -> Prop with
      | [] => fun _ _ => True
      | r :: v' => fun t t' =>
          csa r (fst t) (fst t') ∧ salist_gen csa v' (snd t) (snd t')
      end.

    (* Two transcripts with the same announcements everywhere
       (challenges and responses may differ) — the hypothesis of
       special soundness. *)
    Fixpoint comp_same_announcement (r : comp_rel) :
      comp_transcript r -> comp_transcript r -> Prop :=
      match r return comp_transcript r -> comp_transcript r -> Prop with
      | Leaf m n _ _ => fun t t' => fst t = fst t'
      | CAnd rl rr => fun t t' =>
          comp_same_announcement rl (fst t) (fst t') ∧
          comp_same_announcement rr (snd t) (snd t')
      | COr rl rr => fun t t' =>
          comp_same_announcement rl (fst (fst t)) (fst (fst t')) ∧
          comp_same_announcement rr (snd (fst t)) (snd (fst t'))
      | CThresh _ _ _ rs _ _ => fun t t' =>
          salist_gen comp_same_announcement rs (fst t) (fst t')
      end.

    Fixpoint rand_list_gen (cd : ∀ r : comp_rel, dist (comp_rand r))
      {n : nat} (v : Vector.t comp_rel n) {struct v} : dist (tlist_gen comp_rand v) :=
      match v as v' return dist (tlist_gen comp_rand v') with
      | [] => Ret tt
      | r :: v' =>
          x <- cd r ;;
          xs <- rand_list_gen cd v' ;;
          Ret (x, xs)
      end.

    (* Uniform distribution over the prover randomness *)
    Fixpoint comp_rand_distribution
      (lf : list F) (Hlfn : lf <> List.nil) (r : comp_rel) {struct r} :
      dist (comp_rand r) :=
      match r return dist (comp_rand r) with
      | Leaf m n _ _ =>
          repeat_dist_ntimes_vector
            (uniform_with_replacement lf Hlfn) n
      | CAnd rl rr =>
          sl <- comp_rand_distribution lf Hlfn rl ;;
          sr <- comp_rand_distribution lf Hlfn rr ;;
          Ret (sl, sr)
      | COr rl rr =>
          c₁ <- uniform_with_replacement lf Hlfn ;;
          sl <- comp_rand_distribution lf Hlfn rl ;;
          sr <- comp_rand_distribution lf Hlfn rr ;;
          Ret (sl, sr, c₁)
      | CThresh t k _ rs _ _ =>
          d <- repeat_dist_ntimes_vector
            (uniform_with_replacement lf Hlfn) (k - t) ;;
          rl <- rand_list_gen (comp_rand_distribution lf Hlfn) rs ;;
          Ret (rl, d)
      end.

    Definition comp_real_distribution
      (lf : list F) (Hlfn : lf <> List.nil) (r : comp_rel)
      (w : comp_witness r) (c : F) : dist (comp_transcript r) :=
      s <- comp_rand_distribution lf Hlfn r ;;
      Ret (comp_prove r w s c).

    Definition comp_simulator_distribution
      (lf : list F) (Hlfn : lf <> List.nil) (r : comp_rel)
      (c : F) : dist (comp_transcript r) :=
      s <- comp_rand_distribution lf Hlfn r ;;
      Ret (comp_simulate r s c).

  End Def.

  (* The walkers instantiated at the functions above *)
  #[local] Notation wlist := (wlist_gen comp_witness).
  #[local] Notation wholds := (wholds_gen comp_rel_holds).
  #[local] Notation tlist := (tlist_gen comp_transcript).
  #[local] Notation rlist := (tlist_gen comp_rand).
  #[local] Notation slist := (slist_gen comp_size).
  #[local] Notation simlist := (simlist_gen comp_simulate).
  #[local] Notation provelist := (provelist_gen comp_prove comp_simulate).
  #[local] Notation verlist := (verlist_gen comp_verify).
  #[local] Notation salist := (salist_gen comp_same_announcement).
  #[local] Notation rand_list lf Hlfn :=
    (rand_list_gen (comp_rand_distribution lf Hlfn)).

  Section Proofs.

    Context
      {Hvec : @vector_space F (@eq F) zero one add mul sub
        div opp inv G (@eq G) gid ginv gop gpow}.
    Add Field field : (@field_theory_for_stdlib_tactic F
      eq zero one opp add mul sub inv div vector_space_field).

    #[local] Notation lag_evalF :=
      (@lag_interp_eval F zero one add mul sub div opp inv
        vector_space_field).
    #[local] Notation lag_uniqF :=
      (@lag_interp_unique F zero one add mul sub div opp inv Fdec
        vector_space_field).
    #[local] Notation thresh_extractF :=
      (@threshold_extraction F zero one add mul sub div opp inv Fdec
        vector_space_field).
    #[local] Notation agreebF := (@agreeb F zero Fdec).

    (* ---------- threshold bookkeeping ---------- *)

    Lemma wcount_le :
      ∀ (n : nat) (v : Vector.t comp_rel n) (w : wlist v),
      (wcount v w <= n)%nat.
    Proof.
      induction v as [|r n v ih]; intros w; cbn.
      + lia.
      + destruct (fst w); specialize (ih (snd w)); lia.
    Qed.

    Lemma sim_flags_length :
      ∀ (n : nat) (v : Vector.t comp_rel n) (w : wlist v) (s : nat),
      List.length (sim_flags v w s) = n.
    Proof.
      induction v as [|r n v ih]; intros w s; cbn.
      + reflexivity.
      + destruct (fst w); [destruct s |]; cbn; rewrite ih; reflexivity.
    Qed.

    Lemma sim_flags_count :
      ∀ (n : nat) (v : Vector.t comp_rel n) (w : wlist v) (s : nat),
      count_true (sim_flags v w s) =
      (n - wcount v w + Nat.min s (wcount v w))%nat.
    Proof.
      induction v as [|r n v ih]; intros w s; cbn.
      + lia.
      + pose proof (wcount_le n v (snd w)) as hle.
        destruct (fst w); [destruct s |]; cbn; rewrite ih;
        destruct (wcount v (snd w)) eqn:hw; lia.
    Qed.

    Lemma select_nodes_length :
      ∀ (xs : list F) (fl : list bool),
      List.length fl = List.length xs ->
      List.length (select_nodes xs fl) = count_true fl.
    Proof.
      induction xs as [|x xs ih]; intros [|b fl] hl; cbn in hl |- *;
      try lia; try reflexivity.
      destruct b; cbn; rewrite ih; lia.
    Qed.

    Lemma select_nodes_incl :
      ∀ (xs : list F) (fl : list bool) (x : F),
      List.In x (select_nodes xs fl) -> List.In x xs.
    Proof.
      induction xs as [|y xs ih]; intros [|b fl] x hin; cbn in hin;
      try contradiction.
      destruct b.
      + destruct hin as [hin | hin]; [left; exact hin | right; eapply ih; exact hin].
      + right; eapply ih; exact hin.
    Qed.

    Lemma select_nodes_nodup :
      ∀ (xs : list F) (fl : list bool),
      List.NoDup xs -> List.NoDup (select_nodes xs fl).
    Proof.
      induction xs as [|y xs ih]; intros [|b fl] hnd; cbn;
      try constructor.
      inversion hnd as [| ? ? hnin hnd']; subst.
      destruct b.
      + constructor.
        intro hin; eapply hnin; eapply select_nodes_incl; exact hin.
        eapply ih; exact hnd'.
      + eapply ih; exact hnd'.
    Qed.

    Lemma nodup_zero_select :
      ∀ (xs : list F) (fl : list bool),
      List.NoDup (List.cons zero xs) ->
      List.NoDup (List.cons zero (select_nodes xs fl)).
    Proof.
      intros * hnd.
      inversion hnd as [| ? ? hnin hnd']; subst.
      constructor.
      intro hin; eapply hnin; eapply select_nodes_incl; exact hin.
      eapply select_nodes_nodup; exact hnd'.
    Qed.

    Lemma nodup_zero_firstn :
      ∀ (xs : list F) (n : nat),
      List.NoDup (List.cons zero xs) ->
      List.NoDup (List.cons zero (List.firstn n xs)).
    Proof.
      intros * hnd.
      inversion hnd as [| ? ? hnin hnd']; subst.
      constructor.
      intro hin; eapply hnin; eapply in_firstn; exact hin.
      eapply nodup_firstn; exact hnd'.
    Qed.

    (* The interpolant through (0, c) and the given points takes
       value c at 0. *)
    Lemma expand_chal_zero :
      ∀ (c : F) (nodes vals : list F),
      List.NoDup (List.cons zero nodes) ->
      List.length nodes = List.length vals ->
      lag_interpF (List.cons (zero, c) (List.combine nodes vals)) zero = c.
    Proof.
      intros * hnd hl.
      eapply lag_evalF.
      + cbn; rewrite combine_map_fst; [exact hnd | exact hl].
      + left; reflexivity.
    Qed.

    (* A function agreeing with a list of values on a list of nodes *)
    Lemma map_of_combine :
      ∀ (nodes vals : list F) (f : F -> F),
      (∀ x v, List.In (x, v) (List.combine nodes vals) -> f x = v) ->
      List.length nodes = List.length vals ->
      List.map f nodes = vals.
    Proof.
      induction nodes as [|x nodes ih]; intros [|v vals] f hf hl;
      cbn in hl |- *; try lia; try reflexivity.
      f_equal.
      + eapply hf; left; reflexivity.
      + eapply ih; [| lia].
        intros y u hin; eapply hf; right; exact hin.
    Qed.

    (* The interpolant through (0, c) and (nodes, vals) takes the
       values vals on nodes. *)
    Lemma expand_chal_nodes :
      ∀ (c : F) (nodes vals : list F),
      List.NoDup (List.cons zero nodes) ->
      List.length nodes = List.length vals ->
      List.map (expand_chal c nodes vals) nodes = vals.
    Proof.
      intros * hnd hl.
      eapply map_of_combine; [| exact hl].
      intros x v hin.
      unfold expand_chal.
      eapply lag_evalF.
      + cbn; rewrite combine_map_fst; [exact hnd | exact hl].
      + right; exact hin.
    Qed.

    Lemma in_combine_map :
      ∀ (l : list F) (f : F -> F) (x : F),
      List.In x l -> List.In (x, f x) (List.combine l (List.map f l)).
    Proof.
      induction l as [|y l ih]; intros f x hin; cbn in hin |- *.
      + contradiction.
      + destruct hin as [hin | hin].
        ++ subst; left; reflexivity.
        ++ right; eapply ih; exact hin.
    Qed.

    (* Re-expanding from the values at another node list of the
       same size gives the same interpolant. *)
    Lemma expand_agree :
      ∀ (c : F) (src vals dst : list F),
      List.NoDup (List.cons zero src) ->
      List.NoDup (List.cons zero dst) ->
      List.length src = List.length vals ->
      List.length dst = List.length src ->
      ∀ x,
      expand_chal c dst (List.map (expand_chal c src vals) dst) x =
      expand_chal c src vals x.
    Proof.
      intros * hsnd hdnd hsl hdl x.
      eapply lag_uniqF with (nodes := List.cons zero dst).
      + exact hdnd.
      + cbn; rewrite List.combine_length, List.map_length; lia.
      + cbn; rewrite List.combine_length; lia.
      + intros a hin.
        destruct hin as [hin | hin].
        ++
          subst a.
          rewrite (expand_chal_zero c src vals hsnd hsl).
          rewrite (expand_chal_zero c dst); [reflexivity | exact hdnd |].
          rewrite List.map_length; reflexivity.
        ++
          rewrite (lag_evalF
            (List.cons (zero, c) (List.combine dst
              (List.map (expand_chal c src vals) dst)))
            a (expand_chal c src vals a)).
          +++ reflexivity.
          +++ cbn; rewrite combine_map_fst; [exact hdnd |].
              rewrite List.map_length; reflexivity.
          +++ right; eapply in_combine_map; exact hin.
    Qed.

    (* ------------------ Simulator correctness ------------------ *)

    Lemma verlist_simlist :
      ∀ (n : nat) (v : Vector.t comp_rel n) (s : rlist v)
        (chal : nat -> F) (i : nat),
      vall (fun r => ∀ (s : comp_rand r) (c : F),
        comp_verify r c (comp_simulate r s c) = true) v ->
      verlist v chal (simlist v s chal i) i = true.
    Proof.
      induction v as [|r n v ih]; intros s chal i hall; cbn.
      + reflexivity.
      + destruct hall as (hr & hall).
        eapply andb_true_iff; split.
        eapply hr. eapply ih; exact hall.
    Qed.

    Theorem comp_simulate_completeness :
      ∀ (r : comp_rel) (s : comp_rand r) (c : F),
      comp_verify r c (comp_simulate r s c) = true.
    Proof.
      induction r as [m n mat pub | rl rr ihl ihr | rl rr ihl ihr
        | t k xs rs Hxs Ht ihrs] using comp_rel_ind'.
      +
        intros *; cbn.
        eapply linear_relation_simulator_completeness.
      +
        intros *; cbn.
        eapply andb_true_iff; split.
        eapply ihl. eapply ihr.
      +
        intros *; cbn.
        eapply andb_true_iff; split.
        eapply ihl. eapply ihr.
      +
        intros *; cbn.
        eapply andb_true_iff; split.
        eapply Nat.eqb_eq; eapply length_to_list.
        eapply verlist_simlist; exact ihrs.
    Qed.

    (* ------------------ Completeness ------------------ *)

    Lemma verlist_provelist :
      ∀ (n : nat) (v : Vector.t comp_rel n) (w : wlist v) (s : rlist v)
        (fl : list bool) (chal chal' : nat -> F) (i : nat),
      vall (fun r => ∀ (w : comp_witness r) (s : comp_rand r) (c : F),
        comp_rel_holds r w -> comp_verify r c (comp_prove r w s c) = true) v ->
      wholds v w ->
      (∀ j, chal' j = chal j) ->
      verlist v chal' (provelist v w s fl chal i) i = true.
    Proof.
      induction v as [|r n v ih]; intros w s fl chal chal' i hall hw hc; cbn.
      + reflexivity.
      + destruct hall as (hr & hall).
        destruct w as (ow & w'); cbn in hw |- *.
        destruct hw as (hw & hw').
        eapply andb_true_iff; split.
        ++
          rewrite hc.
          destruct ow as [x |]; [destruct fl as [| [|] fl] |];
          try (eapply hr; exact hw);
          eapply comp_simulate_completeness.
        ++
          eapply ih; assumption.
    Qed.

    Theorem comp_completeness :
      ∀ (r : comp_rel) (w : comp_witness r) (s : comp_rand r) (c : F),
      comp_rel_holds r w ->
      comp_verify r c (comp_prove r w s c) = true.
    Proof.
      induction r as [m n mat pub | rl rr ihl ihr | rl rr ihl ihr
        | t k xs rs Hxs Ht ihrs] using comp_rel_ind'.
      +
        intros * ha; cbn.
        eapply linear_relation_completeness.
        rewrite ha; reflexivity.
      +
        intros * ha; cbn in ha |- *.
        destruct ha as (hal & har).
        eapply andb_true_iff; split.
        eapply ihl; exact hal.
        eapply ihr; exact har.
      +
        intros * ha; cbn in ha |- *.
        destruct w as [wl | wr]; cbn.
        ++
          eapply andb_true_iff; split.
          eapply ihl; exact ha.
          assert (hb : c - (c - snd s) = snd s). field.
          rewrite hb.
          eapply comp_simulate_completeness.
        ++
          eapply andb_true_iff; split.
          eapply comp_simulate_completeness.
          eapply ihr; exact ha.
      +
        intros * ha; cbn in ha |- *.
        destruct ha as (hcount & hholds).
        pose proof (length_to_list F k xs) as Hlen.
        set (xl := Vector.to_list xs) in *.
        eapply andb_true_iff; split.
        ++
          eapply Nat.eqb_eq.
          rewrite List.map_length.
          eapply List.firstn_length_le; lia.
        ++
          pose proof (wcount_le k rs w) as hle.
          assert (hsl : List.length
            (select_nodes xl (sim_flags rs w (wcount rs w - t))) = (k - t)%nat).
          { rewrite select_nodes_length, sim_flags_count.
            rewrite Nat.min_l; lia.
            rewrite sim_flags_length; symmetry; exact Hlen. }
          eapply verlist_provelist; try assumption.
          intro j.
          eapply expand_agree.
          +++ eapply nodup_zero_select; exact Hxs.
          +++ eapply nodup_zero_firstn; exact Hxs.
          +++ rewrite hsl, length_to_list; reflexivity.
          +++ rewrite hsl; eapply List.firstn_length_le; lia.
    Qed.

    (* ------------------ Special soundness ------------------ *)

    (* Extract a witness for every child whose two challenges differ. *)
    Lemma extract_list :
      ∀ (n : nat) (v : Vector.t comp_rel n) (i : nat)
        (chal chal' : nat -> F) (ts ts' : tlist v),
      vall (fun r => ∀ (c c' : F) (t t' : comp_transcript r),
        c <> c' -> comp_same_announcement r t t' ->
        comp_verify r c t = true -> comp_verify r c' t' = true ->
        ∃ w, comp_rel_holds r w) v ->
      salist v ts ts' ->
      verlist v chal ts i = true -> verlist v chal' ts' i = true ->
      ∃ w : wlist v,
        wholds v w ∧
        wcount v w =
        List.length (List.filter
          (fun j => negb (if Fdec (chal j) (chal' j) then true else false))
          (List.seq i n)).
    Proof.
      induction v as [|r n v ih]; intros i chal chal' ts ts' hall hsa hv hv'.
      + exists tt; split; [exact I | reflexivity].
      + cbn in hall, hsa, hv, hv'.
        destruct hall as (hr & hall).
        destruct hsa as (hsa & hsa').
        eapply andb_true_iff in hv, hv'.
        destruct hv as (hv1 & hv2).
        destruct hv' as (hv1' & hv2').
        destruct (ih (S i) chal chal' (snd ts) (snd ts') hall hsa' hv2 hv2')
          as (w' & hw' & hcnt).
        cbn.
        destruct (Fdec (chal i) (chal' i)) as [heq | hne]; cbn.
        ++
          exists (None, w'); cbn.
          split; [split; [exact I | exact hw'] | exact hcnt].
        ++
          destruct (hr _ _ _ _ hne hsa hv1 hv1') as (x & hx).
          exists (Some x, w'); cbn.
          split; [split; [exact hx | exact hw'] | rewrite hcnt; reflexivity].
    Qed.

    Theorem comp_special_soundness :
      ∀ (r : comp_rel) (c c' : F)
        (tr tr' : comp_transcript r),
      c <> c' ->
      comp_same_announcement r tr tr' ->
      comp_verify r c tr = true ->
      comp_verify r c' tr' = true ->
      ∃ (w : comp_witness r), comp_rel_holds r w.
    Proof.
      induction r as [m n mat pub | rl rr ihl ihr | rl rr ihl ihr
        | t k xs rs Hxs Ht ihrs] using comp_rel_ind'.
      +
        intros * ha hb hc hd.
        destruct tr as (comm & res).
        destruct tr' as (comm' & res').
        cbn in hb, hc, hd; subst.
        eapply linear_relation_special_soundness.
        exact ha. exact hc. exact hd.
      +
        intros * ha hb hc hd.
        destruct tr as (tl & tr).
        destruct tr' as (tl' & tr').
        cbn in hb, hc, hd.
        destruct hb as (hbl & hbr).
        eapply andb_true_iff in hc, hd.
        destruct hc as (hcl & hcr).
        destruct hd as (hdl & hdr).
        destruct (ihl _ _ _ _ ha hbl hcl hdl) as (wl & hwl).
        destruct (ihr _ _ _ _ ha hbr hcr hdr) as (wr & hwr).
        exists (wl, wr); cbn.
        exact (conj hwl hwr).
      +
        intros * ha hb hc hd.
        destruct tr as ((tl & tr) & e).
        destruct tr' as ((tl' & tr') & e').
        cbn in hb, hc, hd.
        destruct hb as (hbl & hbr).
        eapply andb_true_iff in hc, hd.
        destruct hc as (hcl & hcr).
        destruct hd as (hdl & hdr).
        destruct (Fdec e e') as [he | he].
        ++
          (* left challenges equal, so right challenges differ *)
          subst e'.
          assert (hf : c - e <> c' - e).
          intro hf. eapply ha.
          eapply f_equal with (f := fun x => x + e) in hf.
          assert (hg : ∀ a : F, a - e + e = a). intros; field.
          rewrite !hg in hf. exact hf.
          destruct (ihr _ _ _ _ hf hbr hcr hdr) as (wr & hwr).
          exists (inr wr); cbn.
          exact hwr.
        ++
          (* left challenges differ *)
          destruct (ihl _ _ _ _ he hbl hcl hdl) as (wl & hwl).
          exists (inl wl); cbn.
          exact hwl.
      +
        intros * ha hb hc hd.
        destruct tr as (ts & ds).
        destruct tr' as (ts' & ds').
        cbn in hb, hc, hd.
        eapply andb_true_iff in hc, hd.
        destruct hc as (hc1 & hc2).
        destruct hd as (hd1 & hd2).
        eapply Nat.eqb_eq in hc1, hd1.
        pose proof (length_to_list F k xs) as Hlen.
        set (xl := Vector.to_list xs) in *.
        destruct (extract_list k rs 0 _ _ ts ts' ihrs hb hc2 hd2)
          as (w & hw & hcnt).
        exists w; cbn.
        split; [| exact hw].
        rewrite hcnt.
        assert (hfl : List.length (List.firstn (k - t) xl) = (k - t)%nat).
        { eapply List.firstn_length_le; lia. }
        set (f := expand_chal c (List.firstn (k - t) xl) ds).
        set (f' := expand_chal c' (List.firstn (k - t) xl) ds').
        set (CS := List.map (chal_of xl f) (List.seq 0 k)).
        set (CS' := List.map (chal_of xl f') (List.seq 0 k)).
        assert (hnd : List.NoDup xl).
        { inversion Hxs; assumption. }
        assert (hnth : ∀ g i, (i < k)%nat ->
          List.nth i (List.map (chal_of xl g) (List.seq 0 k)) zero =
          g (List.nth i xl zero)).
        { intros g i hi. rewrite nth_map_seq; [reflexivity | exact hi]. }
        assert (hext : (t <= List.length
          (List.filter (fun i => negb (agreebF CS CS' i)) (List.seq 0 k)))%nat).
        {
          eapply (thresh_extractF k t xl CS CS'
            (List.cons (zero, c) (List.combine (List.firstn (k - t) xl) ds))
            (List.cons (zero, c') (List.combine (List.firstn (k - t) xl) ds'))
            c c').
          + exact Ht.
          + exact hnd.
          + exact Hlen.
          + cbn; rewrite List.combine_length, hfl, hc1; lia.
          + cbn; rewrite List.combine_length, hfl, hd1; lia.
          + eapply (expand_chal_zero c).
            eapply nodup_zero_firstn; exact Hxs. congruence.
          + eapply (expand_chal_zero c').
            eapply nodup_zero_firstn; exact Hxs. congruence.
          + intros i hi. unfold CS. rewrite hnth; [reflexivity | exact hi].
          + intros i hi. unfold CS'. rewrite hnth; [reflexivity | exact hi].
          + exact ha.
        }
        rewrite List.filter_ext_in with
          (g := fun i => negb (agreebF CS CS' i)).
        exact hext.
        intros i hi.
        eapply List.in_seq in hi.
        unfold agreeb, CS, CS'.
        rewrite !hnth; [reflexivity | lia | lia].
    Qed.

    (* ------------------ SHVZK ------------------ *)

    Lemma rand_list_prob :
      ∀ (n : nat) (v : Vector.t comp_rel n) (lf : list F)
        (Hlfn : lf <> List.nil) (s : rlist v) (q : prob),
      vall (fun r => ∀ (lf : list F) (Hlfn : lf <> List.nil)
        (s : comp_rand r) (q : prob),
        List.In (s, q) (comp_rand_distribution lf Hlfn r) ->
        q = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) (comp_size r)))) v ->
      List.In (s, q) (rand_list lf Hlfn v) ->
      q = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) (slist v))).
    Proof.
      induction v as [|r n v ih]; intros lf Hlfn s q hall hin; cbn in hin |- *.
      +
        destruct hin as [hin | hin]; [| contradiction].
        inversion hin; subst.
        reflexivity.
      +
        destruct hall as (hr & hall).
        assert (hL : List.length lf <> 0%nat).
        destruct lf; [congruence | cbn; lia].
        eapply bind_in_inv in hin.
        destruct hin as (x & px & py & hb & hc & hd).
        eapply bind_ret_prob in hc.
        2: { intros y qy he. eapply ih; [exact hall | exact he]. }
        eapply hr in hb.
        subst.
        rewrite PeanoNat.Nat.pow_add_r.
        eapply prob_mul_split;
        eapply PeanoNat.Nat.pow_nonzero; exact hL.
    Qed.

    Lemma comp_rand_distribution_prob :
      ∀ (r : comp_rel) (lf : list F) (Hlfn : lf <> List.nil)
        (s : comp_rand r) (q : prob),
      List.In (s, q) (comp_rand_distribution lf Hlfn r) ->
      q = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) (comp_size r))).
    Proof.
      induction r as [m n mat pub | rl rr ihl ihr | rl rr ihl ihr
        | t k xs rs Hxs Ht ihrs] using comp_rel_ind'.
      +
        intros * ha; cbn in ha |- *.
        eapply uniform_probability_multidraw_prob.
        exact ha.
      +
        intros * ha; cbn in ha |- *.
        assert (hL : List.length lf <> 0%nat).
        destruct lf; [congruence | cbn; lia].
        eapply bind_in_inv in ha.
        destruct ha as (sl & px & py & hb & hc & hd).
        eapply bind_ret_prob in hc.
        2: { intros x qx he. eapply ihr. exact he. }
        specialize (ihl lf Hlfn sl px hb).
        subst.
        rewrite PeanoNat.Nat.pow_add_r.
        eapply prob_mul_split;
        eapply PeanoNat.Nat.pow_nonzero; exact hL.
      +
        intros * ha; cbn in ha |- *.
        assert (hL : List.length lf <> 0%nat).
        destruct lf; [congruence | cbn; lia].
        eapply bind_in_inv in ha.
        destruct ha as (c₁ & px & py & hb & hc & hd).
        eapply bind_in_inv in hc.
        destruct hc as (sl & px2 & py2 & he & hf & hg).
        eapply bind_ret_prob in hf.
        2: { intros x qx hh. eapply ihr. exact hh. }
        eapply uniform_probability in hb.
        specialize (ihl lf Hlfn sl px2 he).
        subst.
        assert (h₁ : Nat.pow (List.length lf) (comp_size rl) <> 0%nat).
        eapply PeanoNat.Nat.pow_nonzero; exact hL.
        assert (h₂ : Nat.pow (List.length lf) (comp_size rr) <> 0%nat).
        eapply PeanoNat.Nat.pow_nonzero; exact hL.
        rewrite (prob_mul_split _ _ h₁ h₂).
        rewrite prob_mul_split; [| exact hL | nia].
        f_equal; f_equal.
        rewrite ?PeanoNat.Nat.pow_succ_r', ?PeanoNat.Nat.pow_add_r.
        reflexivity.
      +
        intros * ha; cbn in ha |- *.
        assert (hL : List.length lf <> 0%nat).
        destruct lf; [congruence | cbn; lia].
        eapply bind_in_inv in ha.
        destruct ha as (d & px & py & hb & hc & hd).
        eapply bind_ret_prob in hc.
        2: { intros x qx he. eapply rand_list_prob; [exact ihrs | exact he]. }
        eapply uniform_probability_multidraw_prob in hb.
        subst.
        rewrite prob_mul_split;
        try (eapply PeanoNat.Nat.pow_nonzero; exact hL).
        f_equal; f_equal.
        rewrite PeanoNat.Nat.pow_add_r; nia.
    Qed.

    Lemma comp_real_distribution_transcript_generic :
      ∀ (r : comp_rel) (lf : list F) (Hlfn : lf <> List.nil)
        (w : comp_witness r) (c : F) (t : comp_transcript r)
        (p : prob),
      comp_rel_holds r w ->
      List.In (t, p) (comp_real_distribution lf Hlfn r w c) ->
      comp_verify r c t = true ∧
      p = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) (comp_size r))).
    Proof.
      intros * ha hb.
      refine (conj _ _).
      +
        unfold comp_real_distribution in hb.
        eapply bind_ret_in in hb.
        destruct hb as (s & q & hc & hd & he).
        subst.
        eapply comp_completeness.
        exact ha.
      +
        unfold comp_real_distribution in hb.
        eapply bind_ret_prob in hb.
        exact hb.
        intros s q hc.
        eapply comp_rand_distribution_prob.
        exact hc.
    Qed.

    Lemma comp_simulator_distribution_transcript_generic :
      ∀ (r : comp_rel) (lf : list F) (Hlfn : lf <> List.nil)
        (c : F) (t : comp_transcript r) (p : prob),
      List.In (t, p) (comp_simulator_distribution lf Hlfn r c) ->
      comp_verify r c t = true ∧
      p = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) (comp_size r))).
    Proof.
      intros * ha.
      refine (conj _ _).
      +
        unfold comp_simulator_distribution in ha.
        eapply bind_ret_in in ha.
        destruct ha as (s & q & hb & hc & hd).
        subst.
        eapply comp_simulate_completeness.
      +
        unfold comp_simulator_distribution in ha.
        eapply bind_ret_prob in ha.
        exact ha.
        intros s q hb.
        eapply comp_rand_distribution_prob.
        exact hb.
    Qed.

    (* Special honest-verifier zero-knowledge, accept-bit form: both
       distributions consist of accepting transcripts drawn with the
       same uniform probability. *)
    Theorem comp_special_honest_verifier_zkp :
      ∀ (r : comp_rel) (lf : list F) (Hlfn : lf <> List.nil)
        (w : comp_witness r) (c : F),
      comp_rel_holds r w ->
      List.map (fun '(t, p) => (comp_verify r c t, p))
        (comp_real_distribution lf Hlfn r w c) =
      List.map (fun '(t, p) => (comp_verify r c t, p))
        (comp_simulator_distribution lf Hlfn r c).
    Proof.
      intros * ha.
      eapply map_ext_eq.
      +
        unfold comp_real_distribution,
          comp_simulator_distribution.
        repeat rewrite distribution_length.
        reflexivity.
      +
        intros t p hb.
        eapply comp_real_distribution_transcript_generic.
        exact ha. exact hb.
      +
        intros t p hb.
        eapply comp_simulator_distribution_transcript_generic.
        exact hb.
    Qed.

    (* ---------- Distribution equality and witness indistinguishability ---------- *)
    (*
      The accept-bit theorem above cannot distinguish a prover using
      one OR / threshold witness from one using another.  Here we
      show the stronger fact that the real and simulated
      distributions are permutations of each other, assuming the
      challenge space lf enumerates the field without duplicates.
      Since Bind and Ret build lists, permutation is the natural
      notion of distribution equality (dist_equiv in Distr.v).
    *)

    (* Normalise nested Bind/Ret towers, descending under binders. *)
    Ltac norm_bind :=
      repeat first
        [ rewrite bind_assoc
        | rewrite bind_ret_left
        | progress cbn [fst snd]
        | (eapply bind_ext; intro) ].

    Lemma zip_with_cons :
      ∀ {A B C : Type} (n : nat) (f : A -> B -> C)
        (a : A) (v : Vector.t A n) (b : B) (w : Vector.t B n),
      zip_with f (a :: v) (b :: w) = f a b :: zip_with f v w.
    Proof.
      intros *; reflexivity.
    Qed.

    (* ---- uniform multidraws and bijections ---- *)

    Lemma multidraw_in_iff :
      ∀ (lf : list F) (Hlfn : lf <> List.nil) (n : nat)
        (v : Vector.t F n) (p : prob),
      List.NoDup lf -> (∀ x : F, List.In x lf) ->
      (List.In (v, p) (repeat_dist_ntimes_vector
        (uniform_with_replacement lf Hlfn) n) <->
       p = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) n))).
    Proof.
      intros * hnd hin; split; intro ha.
      + eapply uniform_probability_multidraw_prob; exact ha.
      + subst.
        destruct (multidraw_complete lf Hlfn n v hin) as (q & hq).
        pose proof (uniform_probability_multidraw_prob _ _ _ _ _ hq); subst.
        exact hq.
    Qed.

    (* A bijection of F^n permutes the uniform multidraw. *)
    Lemma multidraw_bij_perm {B : Type} :
      ∀ (lf : list F) (Hlfn : lf <> List.nil) (n : nat)
        (φ ψ : Vector.t F n -> Vector.t F n) (g : Vector.t F n -> dist B),
      List.NoDup lf -> (∀ x : F, List.In x lf) ->
      (∀ v, ψ (φ v) = v) -> (∀ v, φ (ψ v) = v) ->
      Permutation
        (Bind (repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn) n)
          (fun v => g (φ v)))
        (Bind (repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn) n) g).
    Proof.
      intros * hnd hin hψφ hφψ.
      rewrite <-bind_map_values.
      eapply bind_perm_left.
      eapply NoDup_Permutation.
      +
        eapply Injective_map_NoDup.
        ++
          intros (v, p) (v', p') heq.
          inversion heq as [(heq1 & heq2)].
          rewrite <-(hψφ v), <-(hψφ v'), heq1; reflexivity.
        ++
          eapply NoDup_map_inv with (f := fst).
          eapply multidraw_nodup; exact hnd.
      +
        eapply NoDup_map_inv with (f := fst).
        eapply multidraw_nodup; exact hnd.
      +
        intros (u, p); split; intro ha.
        ++
          eapply in_map_iff in ha.
          destruct ha as ((v & q) & heq & hv).
          inversion heq; subst.
          eapply multidraw_in_iff; try assumption.
          eapply multidraw_in_iff in hv; assumption.
        ++
          eapply multidraw_in_iff in ha; try assumption; subst.
          eapply in_map_iff.
          exists (ψ u, mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) n))).
          split.
          +++ rewrite hφψ; reflexivity.
          +++ eapply multidraw_in_iff; try assumption; reflexivity.
    Qed.

    (* Shifting every coordinate of a uniform multidraw by a field
       translation permutes the distribution (the Leaf case). *)
    Lemma multidraw_shift_perm :
      ∀ (n : nat) (lf : list F) (Hlfn : lf <> List.nil) (c : F)
        (xs : Vector.t F n) {B : Type} (f : Vector.t F n -> dist B),
      List.NoDup lf -> (∀ x : F, List.In x lf) ->
      Permutation
        (Bind (repeat_dist_ntimes_vector
          (uniform_with_replacement lf Hlfn) n)
          (fun us => f (zip_with (fun u x => u + c * x) us xs)))
        (Bind (repeat_dist_ntimes_vector
          (uniform_with_replacement lf Hlfn) n) f).
    Proof.
      induction n as [|n ihn].
      +
        intros * hnd hin.
        rewrite (vector_inv_0 xs).
        cbn [repeat_dist_ntimes_vector].
        rewrite !bind_ret_left; cbn.
        reflexivity.
      +
        intros * hnd hin.
        destruct (vector_inv_S xs) as (xh & xt & ha); subst.
        rewrite !bind_multidraw_S.
        erewrite bind_ext with
          (l := uniform_with_replacement lf Hlfn)
          (g := fun u =>
            Bind (repeat_dist_ntimes_vector
              (uniform_with_replacement lf Hlfn) n)
              (fun v => f ((u + c * xh) ::
                zip_with (fun u x => u + c * x) v xt))).
        2: { intro u. eapply bind_ext; intro v.
             cbn beta. rewrite zip_with_cons. reflexivity. }
        eapply Permutation_trans.
        eapply uniform_shift_perm with
          (σ := fun u => u + c * xh) (τ := fun u => u - c * xh)
          (f := fun u =>
            Bind (repeat_dist_ntimes_vector
              (uniform_with_replacement lf Hlfn) n)
              (fun v => f (u :: zip_with (fun u x => u + c * x) v xt))).
        exact hnd. exact hin.
        intro; cbn beta; field. intro; cbn beta; field.
        eapply bind_perm_right; intro u.
        eapply ihn with (f := fun v => f (u :: v)); assumption.
    Qed.

    (* ---- the Shamir share bijection ---- *)

    Definition vec_cast {A : Type} {n m : nat} (H : n = m)
      (v : Vector.t A n) : Vector.t A m :=
      eq_rect n (Vector.t A) v m H.

    Lemma to_list_vec_cast :
      ∀ {A : Type} {n m : nat} (H : n = m) (v : Vector.t A n),
      Vector.to_list (vec_cast H v) = Vector.to_list v.
    Proof.
      intros *; destruct H; reflexivity.
    Qed.

    (* The values, at the nodes dst, of the interpolant through
       (0, c) and the pairs (src, d). *)
    Definition shift_nodes (c : F) (m : nat) (src dst : list F)
      (Hdst : List.length dst = m) (d : Vector.t F m) : Vector.t F m :=
      Vector.map (expand_chal c src (Vector.to_list d))
        (vec_cast Hdst (Vector.of_list dst)).

    Lemma to_list_shift_nodes :
      ∀ (c : F) (m : nat) (src dst : list F) (Hdst : List.length dst = m)
        (d : Vector.t F m),
      Vector.to_list (shift_nodes c m src dst Hdst d) =
      List.map (expand_chal c src (Vector.to_list d)) dst.
    Proof.
      intros *; unfold shift_nodes.
      rewrite to_list_map, to_list_vec_cast, to_list_of_list_opp.
      reflexivity.
    Qed.

    Lemma shift_nodes_inv :
      ∀ (c : F) (m : nat) (src dst : list F)
        (Hsrc : List.length src = m) (Hdst : List.length dst = m)
        (d : Vector.t F m),
      List.NoDup (List.cons zero src) -> List.NoDup (List.cons zero dst) ->
      shift_nodes c m dst src Hsrc (shift_nodes c m src dst Hdst d) = d.
    Proof.
      intros * hsnd hdnd.
      eapply to_list_inj.
      rewrite !to_list_shift_nodes.
      rewrite <-(expand_chal_nodes c src (Vector.to_list d) hsnd) at 2;
      [| rewrite length_to_list; exact Hsrc].
      eapply List.map_ext.
      intro x.
      eapply expand_agree; try assumption.
      rewrite length_to_list; exact Hsrc.
      congruence.
    Qed.

    (* ---- normal forms of the distributions at each node ---- *)

    Lemma comp_real_and_eq :
      ∀ (rl rr : comp_rel) (lf : list F) (Hlfn : lf <> List.nil)
        (wl : comp_witness rl) (wr : comp_witness rr) (c : F),
      comp_real_distribution lf Hlfn (CAnd rl rr) (wl, wr) c =
      Bind (comp_real_distribution lf Hlfn rl wl c) (fun tl =>
        Bind (comp_real_distribution lf Hlfn rr wr c) (fun tr =>
          Ret (tl, tr))).
    Proof.
      intros *.
      unfold comp_real_distribution;
      cbn [comp_rand_distribution comp_prove].
      norm_bind; reflexivity.
    Qed.

    Lemma comp_sim_and_eq :
      ∀ (rl rr : comp_rel) (lf : list F) (Hlfn : lf <> List.nil) (c : F),
      comp_simulator_distribution lf Hlfn (CAnd rl rr) c =
      Bind (comp_simulator_distribution lf Hlfn rl c) (fun tl =>
        Bind (comp_simulator_distribution lf Hlfn rr c) (fun tr =>
          Ret (tl, tr))).
    Proof.
      intros *.
      unfold comp_simulator_distribution;
      cbn [comp_rand_distribution comp_simulate].
      norm_bind; reflexivity.
    Qed.

    Lemma comp_real_or_inl_eq :
      ∀ (rl rr : comp_rel) (lf : list F) (Hlfn : lf <> List.nil)
        (wl : comp_witness rl) (c : F),
      comp_real_distribution lf Hlfn (COr rl rr) (inl wl) c =
      Bind (uniform_with_replacement lf Hlfn) (fun c₁ =>
        Bind (comp_real_distribution lf Hlfn rl wl (c - c₁)) (fun tl =>
          Bind (comp_simulator_distribution lf Hlfn rr c₁) (fun tr =>
            Ret (tl, tr, c - c₁)))).
    Proof.
      intros *.
      unfold comp_real_distribution, comp_simulator_distribution;
      cbn [comp_rand_distribution comp_prove comp_simulate].
      norm_bind; reflexivity.
    Qed.

    Lemma comp_real_or_inr_eq :
      ∀ (rl rr : comp_rel) (lf : list F) (Hlfn : lf <> List.nil)
        (wr : comp_witness rr) (c : F),
      comp_real_distribution lf Hlfn (COr rl rr) (inr wr) c =
      Bind (uniform_with_replacement lf Hlfn) (fun c₁ =>
        Bind (comp_simulator_distribution lf Hlfn rl c₁) (fun tl =>
          Bind (comp_real_distribution lf Hlfn rr wr (c - c₁)) (fun tr =>
            Ret (tl, tr, c₁)))).
    Proof.
      intros *.
      unfold comp_real_distribution, comp_simulator_distribution;
      cbn [comp_rand_distribution comp_prove comp_simulate].
      norm_bind; reflexivity.
    Qed.

    Lemma comp_sim_or_eq :
      ∀ (rl rr : comp_rel) (lf : list F) (Hlfn : lf <> List.nil) (c : F),
      comp_simulator_distribution lf Hlfn (COr rl rr) c =
      Bind (uniform_with_replacement lf Hlfn) (fun c₁ =>
        Bind (comp_simulator_distribution lf Hlfn rl c₁) (fun tl =>
          Bind (comp_simulator_distribution lf Hlfn rr (c - c₁)) (fun tr =>
            Ret (tl, tr, c₁)))).
    Proof.
      intros *.
      unfold comp_simulator_distribution;
      cbn [comp_rand_distribution comp_simulate].
      norm_bind; reflexivity.
    Qed.

    Lemma comp_real_thresh_eq :
      ∀ (t k : nat) (xs : Vector.t F k) (rs : Vector.t comp_rel k) Hxs Ht
        (lf : list F) (Hlfn : lf <> List.nil)
        (w : wlist rs) (c : F),
      comp_real_distribution lf Hlfn (CThresh t k xs rs Hxs Ht) w c =
      Bind (repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn) (k - t))
        (fun d =>
          Bind (rand_list lf Hlfn rs) (fun rl =>
            Ret (provelist rs w rl (sim_flags rs w (wcount rs w - t))
                   (chal_of (Vector.to_list xs) (expand_chal c
                     (select_nodes (Vector.to_list xs) (sim_flags rs w (wcount rs w - t)))
                     (Vector.to_list d))) 0,
                 List.map (expand_chal c
                     (select_nodes (Vector.to_list xs) (sim_flags rs w (wcount rs w - t)))
                     (Vector.to_list d)) (List.firstn (k - t) (Vector.to_list xs))))).
    Proof.
      intros *.
      unfold comp_real_distribution;
      cbn [comp_rand_distribution comp_prove].
      norm_bind; reflexivity.
    Qed.

    Lemma comp_sim_thresh_eq :
      ∀ (t k : nat) (xs : Vector.t F k) (rs : Vector.t comp_rel k) Hxs Ht
        (lf : list F) (Hlfn : lf <> List.nil) (c : F),
      comp_simulator_distribution lf Hlfn (CThresh t k xs rs Hxs Ht) c =
      Bind (repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn) (k - t))
        (fun d =>
          Bind (rand_list lf Hlfn rs) (fun rl =>
            Ret (simlist rs rl
                   (chal_of (Vector.to_list xs) (expand_chal c (List.firstn (k - t) (Vector.to_list xs))
                     (Vector.to_list d))) 0,
                 Vector.to_list d))).
    Proof.
      intros *.
      unfold comp_simulator_distribution;
      cbn [comp_rand_distribution comp_simulate].
      norm_bind; reflexivity.
    Qed.

    (* Pairing a constant onto a Bind/Ret preserves permutation. *)
    Lemma bind_ret_pair_perm {A B C : Type} :
      ∀ (d : dist A) (f g : A -> B) (z : C),
      Permutation (Bind d (fun x => Ret (f x))) (Bind d (fun x => Ret (g x))) ->
      Permutation (Bind d (fun x => Ret (f x, z))) (Bind d (fun x => Ret (g x, z))).
    Proof.
      intros * ha.
      assert (hb : ∀ h : A -> B,
        Bind d (fun x => Ret (h x, z)) =
        Bind (Bind d (fun x => Ret (h x))) (fun y => Ret (y, z))).
      { intro h. rewrite bind_assoc. eapply bind_ext; intro x.
        rewrite bind_ret_left. reflexivity. }
      rewrite !hb.
      eapply bind_perm_left; exact ha.
    Qed.

    (* Splitting a product Ret over two independent draws *)
    Lemma bind_split {A B C D : Type} :
      ∀ (d₁ : dist A) (d₂ : dist B) (f : A -> C) (g : B -> D),
      Bind d₁ (fun x => Bind d₂ (fun y => Ret (f x, g y))) =
      Bind (Bind d₁ (fun x => Ret (f x))) (fun u =>
        Bind (Bind d₂ (fun y => Ret (g y))) (fun v => Ret (u, v))).
    Proof.
      intros *.
      norm_bind; reflexivity.
    Qed.

    (* Two independent draws whose images are permutation-equal
       give permutation-equal products. *)
    Lemma bind_prod_perm {A B C D : Type} :
      ∀ (d₁ : dist A) (d₂ : dist B) (f f' : A -> C) (g g' : B -> D),
      Permutation (Bind d₁ (fun x => Ret (f x))) (Bind d₁ (fun x => Ret (f' x))) ->
      Permutation (Bind d₂ (fun y => Ret (g y))) (Bind d₂ (fun y => Ret (g' y))) ->
      Permutation
        (Bind d₁ (fun x => Bind d₂ (fun y => Ret (f x, g y))))
        (Bind d₁ (fun x => Bind d₂ (fun y => Ret (f' x, g' y)))).
    Proof.
      intros * ha hb.
      rewrite (bind_split d₁ d₂ f g), (bind_split d₁ d₂ f' g').
      eapply bind_perm.
      exact ha.
      intro u.
      eapply bind_perm_left.
      exact hb.
    Qed.

    (* Drawing randomness for a cons of children, under a Ret *)
    Lemma rand_list_cons_bind {C : Type} :
      ∀ (lf : list F) (Hlfn : lf <> List.nil) (n : nat) (r : comp_rel)
        (v : Vector.t comp_rel n) (P : rlist (r :: v) -> C),
      Bind (rand_list lf Hlfn (r :: v)) (fun rl => Ret (P rl)) =
      Bind (comp_rand_distribution lf Hlfn r) (fun x =>
        Bind (rand_list lf Hlfn v) (fun xs => Ret (P (x, xs)))).
    Proof.
      intros *.
      cbn [rand_list_gen].
      norm_bind; reflexivity.
    Qed.

    (* The walk over the children: proving (resp. simulating) each
       child at its challenge gives permutation-equal distributions
       when every proven child does. *)
    Lemma walk_perm :
      ∀ (n : nat) (v : Vector.t comp_rel n) (lf : list F)
        (Hlfn : lf <> List.nil) (w : wlist v) (fl : list bool)
        (chal : nat -> F) (i : nat),
      vall (fun r => ∀ (w : comp_witness r) (c : F),
        comp_rel_holds r w ->
        Permutation (comp_real_distribution lf Hlfn r w c)
                    (comp_simulator_distribution lf Hlfn r c)) v ->
      wholds v w ->
      Permutation
        (Bind (rand_list lf Hlfn v) (fun rl => Ret (provelist v w rl fl chal i)))
        (Bind (rand_list lf Hlfn v) (fun rl => Ret (simlist v rl chal i))).
    Proof.
      induction v as [|r n v ih]; intros lf Hlfn w fl chal i hall hw.
      +
        reflexivity.
      +
        destruct hall as (hr & hall).
        destruct w as (ow & w'); cbn in hw.
        destruct hw as (hw & hw').
        cbn [provelist_gen simlist_gen].
        rewrite !rand_list_cons_bind.
        cbn [fst snd].
        eapply bind_prod_perm.
        ++
          destruct ow as [x0 |]; [destruct fl as [| [|] fl] |];
          try reflexivity.
          eapply (hr x0 (chal i) hw).
        ++
          eapply ih; assumption.
    Qed.

    (* At a leaf, the real prover's transcript for randomness us is
       the simulator's transcript for randomness us + c·xs. *)
    Lemma comp_leaf_prove_simulate :
      ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m)
        (pub : Vector.t G m) (xs us : Vector.t F n) (c : F),
      mat_evalC mat xs = pub ->
      comp_prove (Leaf m n mat pub) xs us c =
      comp_simulate (Leaf m n mat pub)
        (zip_with (fun u x => u + c * x) us xs) c.
    Proof.
      intros * ha; subst pub.
      cbn [comp_prove comp_simulate].
      f_equal.
      eapply eq_nth_iff.
      intros i j hij; subst.
      rewrite nth_zip_with.
      unfold mat_eval.
      rewrite !(nth_map _ _ j j eq_refl).
      rewrite row_eval_response.
      rewrite <-associative, <-smul_distributive_fadd.
      assert (ha : c + opp c = zero). field.
      rewrite ha, field_zero, right_identity.
      reflexivity.
    Qed.

    Theorem comp_distribution_perm :
      ∀ (r : comp_rel) (lf : list F) (Hlfn : lf <> List.nil)
        (w : comp_witness r) (c : F),
      List.NoDup lf -> (∀ x : F, List.In x lf) ->
      comp_rel_holds r w ->
      Permutation
        (comp_real_distribution lf Hlfn r w c)
        (comp_simulator_distribution lf Hlfn r c).
    Proof.
      induction r as [m n mat pub | rl rr ihl ihr | rl rr ihl ihr
        | t k xs rs Hxs Ht ihrs] using comp_rel_ind'.
      +
        intros * hnd hin ha; cbn in ha.
        unfold comp_real_distribution, comp_simulator_distribution;
        cbn [comp_rand_distribution].
        erewrite bind_ext with
          (f := fun us => Ret (comp_prove (Leaf m n mat pub) w us c))
          (g := fun us => Ret (comp_simulate (Leaf m n mat pub)
            (zip_with (fun u x => u + c * x) us w) c)).
        2: { intro us.
             rewrite (comp_leaf_prove_simulate _ _ _ _ _ _ _ ha).
             reflexivity. }
        eapply multidraw_shift_perm with
          (f := fun zs => Ret (comp_simulate (Leaf m n mat pub) zs c));
        assumption.
      +
        intros * hnd hin ha.
        destruct w as (wl & wr); cbn in ha.
        destruct ha as (hal & har).
        rewrite comp_real_and_eq, comp_sim_and_eq.
        eapply bind_perm.
        eapply ihl; assumption.
        intro tl.
        eapply bind_perm.
        eapply ihr; assumption.
        intro tr; reflexivity.
      +
        intros * hnd hin ha.
        destruct w as [wl | wr]; cbn in ha.
        ++
          rewrite comp_real_or_inl_eq, comp_sim_or_eq.
          erewrite bind_ext with
            (f := fun c₁ =>
              Bind (comp_real_distribution lf Hlfn rl wl (c - c₁)) (fun tl =>
                Bind (comp_simulator_distribution lf Hlfn rr c₁)
                  (fun tr => Ret (tl, tr, c - c₁))))
            (g := fun c₁ =>
              Bind (comp_real_distribution lf Hlfn rl wl (c - c₁)) (fun tl =>
                Bind (comp_simulator_distribution lf Hlfn rr (c - (c - c₁)))
                  (fun tr => Ret (tl, tr, c - c₁)))).
          2: { intro c₁.
               assert (hb : c - (c - c₁) = c₁). field.
               rewrite hb. reflexivity. }
          eapply Permutation_trans.
          eapply uniform_shift_perm with
            (σ := fun c₁ => c - c₁) (τ := fun c₁ => c - c₁)
            (f := fun c₁ =>
              Bind (comp_real_distribution lf Hlfn rl wl c₁) (fun tl =>
                Bind (comp_simulator_distribution lf Hlfn rr (c - c₁))
                  (fun tr => Ret (tl, tr, c₁)))).
          exact hnd. exact hin.
          intro; cbn beta; field. intro; cbn beta; field.
          eapply bind_perm_right; intro c₁.
          eapply bind_perm.
          eapply ihl; assumption.
          intro tl; reflexivity.
        ++
          rewrite comp_real_or_inr_eq, comp_sim_or_eq.
          eapply bind_perm_right; intro c₁.
          eapply bind_perm_right; intro tl.
          eapply bind_perm.
          eapply ihr; assumption.
          intro tr; reflexivity.
      +
        intros * hnd hin ha; cbn in ha.
        destruct ha as (hcount & hholds).
        pose proof (wcount_le k rs w) as hle.
        pose proof (length_to_list F k xs) as Hlen.
        set (xl := Vector.to_list xs) in *.
        set (fl := sim_flags rs w (wcount rs w - t)).
        set (snodes := select_nodes xl fl).
        set (fnodes := List.firstn (k - t) xl).
        assert (hsl : List.length snodes = (k - t)%nat).
        { unfold snodes, fl.
          rewrite select_nodes_length, sim_flags_count.
          rewrite Nat.min_l; lia.
          rewrite sim_flags_length; symmetry; exact Hlen. }
        assert (hfl : List.length fnodes = (k - t)%nat).
        { unfold fnodes; eapply List.firstn_length_le; lia. }
        assert (hsnd : List.NoDup (List.cons zero snodes)).
        { eapply nodup_zero_select; exact Hxs. }
        assert (hfnd : List.NoDup (List.cons zero fnodes)).
        { eapply nodup_zero_firstn; exact Hxs. }
        rewrite comp_real_thresh_eq, comp_sim_thresh_eq.
        fold xl.
        fold fl snodes fnodes.
        (* the real prover's continuation, reindexed by the share
           bijection φ = shift_nodes c _ snodes fnodes *)
        erewrite bind_ext with
          (g := fun d =>
            Bind (rand_list lf Hlfn rs) (fun rl =>
              Ret (provelist rs w rl fl
                     (chal_of xl (expand_chal c snodes
                       (Vector.to_list (shift_nodes c (k - t) fnodes snodes hsl
                         (shift_nodes c (k - t) snodes fnodes hfl d))))) 0,
                   Vector.to_list (shift_nodes c (k - t) snodes fnodes hfl d)))).
        2: { intro d.
             rewrite shift_nodes_inv; try assumption.
             rewrite to_list_shift_nodes.
             reflexivity. }
        eapply Permutation_trans.
        eapply multidraw_bij_perm with
          (φ := shift_nodes c (k - t) snodes fnodes hfl)
          (ψ := shift_nodes c (k - t) fnodes snodes hsl)
          (g := fun e =>
            Bind (rand_list lf Hlfn rs) (fun rl =>
              Ret (provelist rs w rl fl
                     (chal_of xl (expand_chal c snodes
                       (Vector.to_list (shift_nodes c (k - t) fnodes snodes hsl e)))) 0,
                   Vector.to_list e))).
        exact hnd. exact hin.
        intro; eapply shift_nodes_inv; assumption.
        intro; eapply shift_nodes_inv; assumption.
        eapply bind_perm_right; intro e.
        (* the reindexed real challenge is the simulator's challenge *)
        assert (hchal :
          chal_of xl (expand_chal c snodes
            (Vector.to_list (shift_nodes c (k - t) fnodes snodes hsl e))) =
          chal_of xl (expand_chal c fnodes (Vector.to_list e))).
        { extensionality j; unfold chal_of.
          rewrite to_list_shift_nodes.
          eapply expand_agree; try assumption.
          rewrite length_to_list; exact hfl.
          congruence. }
        rewrite hchal.
        eapply bind_ret_pair_perm.
        eapply walk_perm; [| exact hholds].
        eapply vall_mono; [exact ihrs |].
        intros r0 hr0 w0 c0 hw0.
        eapply hr0; assumption.
    Qed.

    (* Witness indistinguishability: two provers holding different
       witnesses for the same statement (e.g. the two branches of an
       OR, or two qualified subsets of a threshold) produce the same
       transcript distribution. *)
    Theorem comp_witness_indistinguishable :
      ∀ (r : comp_rel) (lf : list F) (Hlfn : lf <> List.nil)
        (w₁ w₂ : comp_witness r) (c : F),
      List.NoDup lf -> (∀ x : F, List.In x lf) ->
      comp_rel_holds r w₁ -> comp_rel_holds r w₂ ->
      Permutation
        (comp_real_distribution lf Hlfn r w₁ c)
        (comp_real_distribution lf Hlfn r w₂ c).
    Proof.
      intros * hnd hin ha hb.
      eapply Permutation_trans.
      eapply comp_distribution_perm; assumption.
      eapply Permutation_sym.
      eapply comp_distribution_perm; assumption.
    Qed.

  End Proofs.
End Composition.
