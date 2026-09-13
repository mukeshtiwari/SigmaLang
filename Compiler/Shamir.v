From Stdlib Require Import Setoid
  setoid_ring.Field Lia List Utf8
  Psatz Bool Arith.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Compiler Require Import Lagrange.
Import ListNotations.

Section Threshold.

  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hfield : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F
    eq zero one opp add mul sub inv div Hfield).

  #[local] Notation lag_interpF :=
    (@lag_interp F zero one add mul sub inv).
  #[local] Notation lag_interp_uniqueF :=
    (@lag_interp_unique F zero one add mul sub div opp inv Fdec Hfield).

  Definition agreeb (cs cs' : list F) (i : nat) : bool :=
    match Fdec (nth i cs zero) (nth i cs' zero) with
    | left _ => true
    | right _ => false
    end.

  (* ---------- helper list lemmas ---------- *)

  Lemma filter_partition_length :
    ∀ (A : Type) (p : A -> bool) (l : list A),
    (length (filter p l) +
     length (filter (fun x => negb (p x)) l))%nat = length l.
  Proof.
    intros A p.
    induction l as [|a l ih]; cbn.
    reflexivity.
    destruct (p a); cbn; lia.
  Qed.

  Lemma nth_map_nodup :
    ∀ (xs : list F) (idxs : list nat),
    List.NoDup idxs ->
    (∀ i, List.In i idxs -> (i < length xs)%nat) ->
    List.NoDup xs ->
    List.NoDup (List.map (fun i => nth i xs zero) idxs).
  Proof.
    intros xs.
    induction idxs as [|a idxs ih]; intros hnd hlt hxs; cbn.
    +
      constructor.
    +
      inversion hnd as [| ? ? hnin hnd']; subst.
      constructor.
      ++
        intro hin.
        eapply List.in_map_iff in hin.
        destruct hin as (j & hj & hjin).
        assert (haj : a = j).
        eapply (proj1 (List.NoDup_nth xs zero) hxs).
        eapply hlt; left; reflexivity.
        eapply hlt; right; exact hjin.
        symmetry; exact hj.
        subst; contradiction.
      ++
        eapply ih.
        exact hnd'.
        intros i hi; eapply hlt; right; exact hi.
        exact hxs.
  Qed.

  Lemma filter_seq_lt :
    ∀ (p : nat -> bool) (n i : nat),
    List.In i (filter p (seq 0 n)) -> (i < n)%nat.
  Proof.
    intros * hi.
    eapply filter_In in hi.
    destruct hi as (hi & _).
    eapply in_seq in hi.
    lia.
  Qed.

  (* ---------- the Shamir soundness core ---------- *)

  Theorem threshold_extraction :
    ∀ (n thr : nat) (xs cs cs' : list F)
      (base base' : list (F * F)) (c c' : F),
    (thr <= n)%nat ->
    List.NoDup xs ->
    length xs = n ->
    (length base <= S (n - thr))%nat ->
    (length base' <= S (n - thr))%nat ->
    lag_interpF base zero = c ->
    lag_interpF base' zero = c' ->
    (∀ i, (i < n)%nat -> lag_interpF base (nth i xs zero) = nth i cs zero) ->
    (∀ i, (i < n)%nat -> lag_interpF base' (nth i xs zero) = nth i cs' zero) ->
    c <> c' ->
    (thr <=
      length (filter (fun i => negb (agreeb cs cs' i)) (seq 0 n)))%nat.
  Proof.
    intros * hthr hnd hlen hb hb' h0 h0' hcs hcs' hne.
    set (E := filter (agreeb cs cs') (seq 0 n)).
    set (D := filter (fun i => negb (agreeb cs cs' i)) (seq 0 n)).
    pose proof (filter_partition_length _ (agreeb cs cs') (seq 0 n))
      as hpart.
    rewrite seq_length in hpart.
    fold E D in hpart.
    (* the agreement set is small *)
    assert (hEsmall : (length E <= n - thr)%nat).
    {
      destruct (Nat.le_gt_cases (length E) (n - thr)) as [hle | hgt];
      [exact hle |].
      exfalso.
      set (nodes := List.map (fun i => nth i xs zero) E).
      assert (hndE : List.NoDup E).
      eapply NoDup_filter, seq_NoDup.
      assert (hnodes_nd : List.NoDup nodes).
      eapply nth_map_nodup.
      exact hndE.
      intros i hi; rewrite hlen; eapply filter_seq_lt; exact hi.
      exact hnd.
      assert (hnodes_len : length nodes = length E).
      unfold nodes; rewrite map_length; reflexivity.
      assert (hagree : ∀ a, List.In a nodes ->
        lag_interpF base a = lag_interpF base' a).
      {
        intros a ha.
        unfold nodes in ha.
        eapply in_map_iff in ha.
        destruct ha as (i & hia & hiin).
        subst a.
        assert (hilt : (i < n)%nat).
        eapply filter_seq_lt; exact hiin.
        rewrite (hcs i hilt), (hcs' i hilt).
        unfold E in hiin.
        eapply filter_In in hiin.
        destruct hiin as (_ & hag).
        unfold agreeb in hag.
        destruct (Fdec (nth i cs zero) (nth i cs' zero)) as [he | he];
        [exact he | discriminate].
      }
      pose proof (lag_interp_uniqueF base base' nodes hnodes_nd)
        as huniq.
      assert (hbn : (length base <= length nodes)%nat).
      rewrite hnodes_len; lia.
      assert (hbn' : (length base' <= length nodes)%nat).
      rewrite hnodes_len; lia.
      pose proof (huniq hbn hbn' hagree zero) as hz.
      rewrite h0, h0' in hz.
      contradiction.
    }
    lia.
  Qed.

  (* ---------- abstract threshold protocol ---------- *)

  (* Children are an indexed family sharing one transcript type T
     (for comp_rel children of the same shape, T = comp_transcript
     r0; a Leaf's transcript type depends only on its dimensions,
     not its public data, so a t-of-n threshold over instances of
     one protocol shape is homogeneous). *)
End Threshold.
