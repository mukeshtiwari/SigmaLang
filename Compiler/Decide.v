From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool List.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import Util.
From Crypto Require Import Sigma.
From Compiler Require Import
  LinearRelation Composition.

Import VectorNotations.

(*
  Deciding the composed relation.

  comp_rel_holds is a Prop; for concrete instances one wants to
  establish it by computation.  comp_rel_holdsb is the boolean
  version (leaf equations decided on the underlying lists of points),
  and comp_rel_holdsb_sound transports a computed `true` to the Prop.
*)
Section Decide.

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

  #[local] Notation comp_relC := (@comp_rel F zero G).
  #[local] Notation comp_witnessC := (@comp_witness F zero G).
  #[local] Notation comp_rel_holdsC := (@comp_rel_holds F zero G gid gop gpow).
  #[local] Notation mat_evalC := (@mat_eval F G gid gop gpow _ _).
  #[local] Notation wlist := (wlist_gen comp_witnessC).
  #[local] Notation wholds := (wholds_gen comp_rel_holdsC).

  Fixpoint holdslist_gen (ch : ∀ r : comp_relC, comp_witnessC r -> bool)
    {n : nat} (v : Vector.t comp_relC n) {struct v} : wlist v -> bool :=
    match v as v' return wlist v' -> bool with
    | [] => fun _ => true
    | r :: v' => fun w =>
        (match fst w with Some x => ch r x | None => true end) &&
        holdslist_gen ch v' (snd w)
    end.

  Fixpoint comp_rel_holdsb (r : comp_relC) : comp_witnessC r -> bool :=
    match r return comp_witnessC r -> bool with
    | Leaf m n mat pub => fun xs =>
        if List.list_eq_dec Gdec (Vector.to_list (mat_evalC mat xs)) (Vector.to_list pub)
        then true else false
    | CAnd rl rr => fun w => comp_rel_holdsb rl (fst w) && comp_rel_holdsb rr (snd w)
    | COr rl rr => fun w =>
        match w with
        | inl wl => comp_rel_holdsb rl wl
        | inr wr => comp_rel_holdsb rr wr
        end
    | CThresh t _ _ rs _ _ => fun w =>
        Nat.leb t (wcount rs w) && holdslist_gen comp_rel_holdsb rs w
    end.

  Lemma holdslist_sound :
    ∀ (n : nat) (v : Vector.t comp_relC n) (w : wlist v),
    vall (fun r => ∀ w : comp_witnessC r, comp_rel_holdsb r w = true -> comp_rel_holdsC r w) v ->
    holdslist_gen comp_rel_holdsb v w = true -> wholds v w.
  Proof.
    intros n v.
    induction v as [| r n v ih]; intros w hall hb; cbn in hb |- *.
    + exact I.
    + destruct hall as (hr & hall).
      eapply andb_true_iff in hb. destruct hb as (h1 & h2).
      split; [| eapply ih; [exact hall | exact h2]].
      destruct (fst w) as [x |]; [eapply hr; exact h1 | exact I].
  Qed.

  Theorem comp_rel_holdsb_sound :
    ∀ (r : comp_relC) (w : comp_witnessC r),
    comp_rel_holdsb r w = true -> comp_rel_holdsC r w.
  Proof.
    intros r.
    induction r as [m n mat pub | rl rr ihl ihr | rl rr ihl ihr | t k xs rs Hxs Ht ihrs]
      using comp_rel_ind'; intros w hb; cbn in hb |- *.
    + destruct (List.list_eq_dec Gdec (Vector.to_list (mat_evalC mat w)) (Vector.to_list pub))
        as [e | ne]; [eapply VectorSpec.to_list_inj; exact e | discriminate hb].
    + eapply andb_true_iff in hb. destruct hb as (h1 & h2).
      split; [eapply ihl; exact h1 | eapply ihr; exact h2].
    + destruct w as [wl | wr]; [eapply ihl; exact hb | eapply ihr; exact hb].
    + eapply andb_true_iff in hb. destruct hb as (h1 & h2).
      split; [eapply PeanoNat.Nat.leb_le; exact h1 | eapply holdslist_sound; [exact ihrs | exact h2]].
  Qed.

End Decide.
