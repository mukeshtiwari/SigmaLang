From Stdlib Require Import Utf8 List Lia Morphisms
  QArith Qminmax micromega.Lqa ZArith.
From Probability Require Import Convex.

Import ListNotations.
Open Scope Q_scope.

(*
  Drawing without replacement, and averaging over the draws.

  This is the sampling layer Attema-Cramer's Lemma 3 needs.  Their
  Tree(x, a, c_1, ..., c_m) samples k challenges y_1, ..., y_k
  uniformly at random from C such that y_i <> y_j, and succeeds when
  every child does; so the object to reason about is

      E over ordered distinct k-tuples of prod_l v(y_l)

  for values v indexed by the challenge set.  `ktuples' enumerates the
  draws, `avg_prod' is that expectation, and `avg_prod_cons' is the
  sequential decomposition their inequality (26) rests on: the first
  draw ranges over all of C, and the rest is the same problem on C
  minus that element.

  Everything here is finite and exact -- a uniform draw from a
  duplicate-free list is a division by a count, so no distribution
  monad is involved and the results are rationals.

  The main result is `avg_prod_lower': drawing k distinct elements
  without replacement, the expected product of values in [0,1] with
  mean eps is at least max(eps - (k-1)/q, 0)^k.  That is the bound
  Attema-Cramer reach through their inequality (26) and the sequential
  conditioning around it; the induction here is shorter, because
  `avg_prod_cons' peels off the first draw and what remains needs only
  that each value is at most 1 (so the shrunken list's threshold does
  not drop) and that a smaller positive denominator only helps.

  The examples at the bottom check the bound is not vacuous.
*)

Section Sampling.

  Context {A : Type}.
  Variable Adec : forall x y : A, {x = y} + {x <> y}.

  (* every ordered k-tuple of distinct elements drawn from l *)
  Fixpoint ktuples (l : list A) (k : nat) : list (list A) :=
    match k with
    | 0%nat => [[]%list]%list
    | S k' =>
        List.flat_map
          (fun x => List.map (fun ys => (x :: ys)%list)
                      (ktuples (List.remove Adec x l) k'))
          l
    end.

  (* the falling factorial q (q-1) ... (q-k+1) *)
  Fixpoint falling (q k : nat) : nat :=
    match k with
    | 0%nat => 1%nat
    | S k' => (q * falling (Nat.pred q) k')%nat
    end.

  Lemma list_sum_const :
    ∀ (B : Type) (n : nat) (l : list B),
    List.list_sum (List.map (fun _ => n) l) = (List.length l * n)%nat.
  Proof.
    intros B n l; unfold List.list_sum.
    induction l as [| a l ih]; cbn; [reflexivity | lia].
  Qed.

  Lemma remove_notin :
    ∀ (l : list A) (x : A),
    ~ List.In x l -> List.remove Adec x l = l.
  Proof.
    induction l as [| a l ih]; intros x hx; cbn; [reflexivity |].
    destruct (Adec x a) as [he | hne].
    + exfalso; eapply hx; left; symmetry; exact he.
    + rewrite ih; [reflexivity | intro hc; eapply hx; right; exact hc].
  Qed.

  Lemma remove_length_nodup :
    ∀ (l : list A) (x : A),
    List.NoDup l -> List.In x l ->
    List.length (List.remove Adec x l) = Nat.pred (List.length l).
  Proof.
    induction l as [| a l ih]; intros x hnd hin; cbn in hin |- *;
    [contradiction |].
    inversion hnd as [| ? ? hna hnl]; subst.
    destruct (Adec x a) as [he | hne].
    +
      subst a; rewrite (remove_notin l x hna); reflexivity.
    +
      destruct hin as [hc | hin]; [exfalso; eapply hne; symmetry; exact hc |].
      cbn; rewrite (ih x hnl hin).
      assert (hpos : (0 < List.length l)%nat)
        by (destruct l; [contradiction | cbn; lia]).
      lia.
  Qed.

  Lemma remove_nodup :
    ∀ (l : list A) (x : A),
    List.NoDup l -> List.NoDup (List.remove Adec x l).
  Proof.
    intros l x hnd; eapply List.NoDup_filter with (f := fun y =>
      if Adec x y then false else true) in hnd.
    revert hnd; clear.
    assert (heq : List.remove Adec x l
                  = List.filter (fun y => if Adec x y then false else true) l).
    {
      induction l as [| a l ih]; cbn; [reflexivity |].
      destruct (Adec x a); cbn; rewrite ih; reflexivity.
    }
    rewrite heq; exact (fun h => h).
  Qed.

  Lemma ktuples_length :
    ∀ (k : nat) (l : list A),
    List.NoDup l ->
    List.length (ktuples l k) = falling (List.length l) k.
  Proof.
    induction k as [| k ih]; intros l hnd; cbn [ktuples falling]; [reflexivity |].
    rewrite List.length_flat_map.
    erewrite List.map_ext_in.
    2:{
      intros x hx.
      rewrite List.length_map, (ih (List.remove Adec x l) (remove_nodup l x hnd)).
      rewrite (remove_length_nodup l x hnd hx).
      reflexivity.
    }
    rewrite list_sum_const; lia.
  Qed.


  (* ---------------- sums over the enumeration ---------------- *)

  Lemma qsum_app :
    ∀ (l1 l2 : list Q), qsum (l1 ++ l2)%list == qsum l1 + qsum l2.
  Proof.
    induction l1 as [| x l1 ih]; intro l2; cbn; [ring |].
    setoid_rewrite ih; ring.
  Qed.

  Lemma qsum_map_flat_map :
    ∀ (B C : Type) (f : C -> Q) (g : B -> list C) (l : list B),
    qsum (List.map f (List.flat_map g l))
    == qsum (List.map (fun x => qsum (List.map f (g x))) l).
  Proof.
    intros B C f g; induction l as [| x l ih]; cbn; [reflexivity |].
    rewrite List.map_app; setoid_rewrite qsum_app.
    setoid_rewrite ih; reflexivity.
  Qed.

  Lemma qsum_map_map :
    ∀ (B C : Type) (f : C -> Q) (h : B -> C) (l : list B),
    qsum (List.map f (List.map h l))
    == qsum (List.map (fun x => f (h x)) l).
  Proof.
    intros B C f h; induction l as [| x l ih]; cbn; [reflexivity |].
    setoid_rewrite ih; reflexivity.
  Qed.

  Lemma qsum_map_ext :
    ∀ (B : Type) (f g : B -> Q) (l : list B),
    (∀ x, List.In x l -> f x == g x) ->
    qsum (List.map f l) == qsum (List.map g l).
  Proof.
    intros B f g; induction l as [| x l ih]; intro h; cbn; [reflexivity |].
    setoid_rewrite (h x (or_introl eq_refl)).
    setoid_rewrite (ih (fun y hy => h y (or_intror hy))).
    reflexivity.
  Qed.

  Lemma qsum_scale :
    ∀ (B : Type) (c : Q) (f : B -> Q) (l : list B),
    qsum (List.map (fun x => c * f x) l) == c * qsum (List.map f l).
  Proof.
    intros B c f; induction l as [| x l ih]; cbn; [ring |].
    setoid_rewrite ih; ring.
  Qed.

  Lemma falling_pos :
    ∀ (k q : nat), (k <= q)%nat -> (0 < falling q k)%nat.
  Proof.
    induction k as [| k ih]; intros q h; cbn [falling]; [lia |].
    assert (hq : (0 < q)%nat) by lia.
    pose proof (ih (Nat.pred q) ltac:(lia)) as hp.
    eapply Nat.mul_pos_pos; lia.
  Qed.

  (* ---------------- the expectation ---------------- *)

  Definition tuple_val (v : A -> Q) (ys : list A) : Q :=
    qprod_list (List.map v ys).

  (* E[ prod_l v(y_l) ] over uniform ordered distinct k-tuples from l *)
  Definition avg_prod (v : A -> Q) (l : list A) (k : nat) : Q :=
    qsum (List.map (tuple_val v) (ktuples l k))
    / qn (List.length (ktuples l k)).

  Lemma qn_pos : ∀ n : nat, (0 < n)%nat -> ~ qn n == 0.
  Proof.
    intros n h; unfold qn; intro hc; unfold Qeq in hc; cbn in hc; lia.
  Qed.

  (*
    The sequential decomposition Attema-Cramer's inequality (26) rests
    on: the first draw ranges uniformly over all of l, and what follows
    is the same expectation on l minus that element.
  *)
  Theorem avg_prod_cons :
    ∀ (v : A -> Q) (l : list A) (k : nat),
    List.NoDup l -> (S k <= List.length l)%nat ->
    avg_prod v l (S k)
    == qsum (List.map (fun x => v x * avg_prod v (List.remove Adec x l) k) l)
       / qn (List.length l).
  Proof.
    intros v l k hnd hk; unfold avg_prod.
    assert (hq : (0 < List.length l)%nat) by lia.
    (* every branch draws from a list of the same size *)
    assert (hsub : ∀ x, List.In x l ->
      List.length (ktuples (List.remove Adec x l) k)
      = falling (Nat.pred (List.length l)) k).
    {
      intros x hx.
      rewrite (ktuples_length k _ (remove_nodup l x hnd)).
      rewrite (remove_length_nodup l x hnd hx); reflexivity.
    }
    assert (hD : (0 < falling (Nat.pred (List.length l)) k)%nat)
      by (eapply falling_pos; lia).
    assert (hDz : ~ qn (falling (Nat.pred (List.length l)) k) == 0)
      by (eapply qn_pos; exact hD).
    assert (hqz : ~ qn (List.length l) == 0) by (eapply qn_pos; exact hq).
    (* the denominator *)
    assert (hden : List.length (ktuples l (S k))
                   = (List.length l
                      * falling (Nat.pred (List.length l)) k)%nat)
      by (rewrite (ktuples_length (S k) l hnd); reflexivity).
    (* the numerator, unfolded one level *)
    assert (hnum :
      qsum (List.map (tuple_val v) (ktuples l (S k)))
      == qsum (List.map
                 (fun x => v x
                           * qsum (List.map (tuple_val v)
                                     (ktuples (List.remove Adec x l) k))) l)).
    {
      cbn [ktuples].
      setoid_rewrite qsum_map_flat_map.
      eapply qsum_map_ext; intros x hx.
      setoid_rewrite qsum_map_map.
      setoid_rewrite <-(qsum_scale _ (v x) (tuple_val v)).
      reflexivity.
    }
    setoid_rewrite hnum.
    rewrite hden, qn_mul.
    (* pull the common denominator out of each branch *)
    assert (hbr :
      qsum (List.map
              (fun x => v x
                        * qsum (List.map (tuple_val v)
                                  (ktuples (List.remove Adec x l) k))) l)
      == qn (falling (Nat.pred (List.length l)) k)
         * qsum (List.map
                   (fun x => v x
                             * avg_prod v (List.remove Adec x l) k) l)).
    {
      setoid_rewrite <-(qsum_scale _ (qn (falling (Nat.pred (List.length l)) k))).
      eapply qsum_map_ext; intros x hx.
      unfold avg_prod; rewrite (hsub x hx).
      field; exact hDz.
    }
    setoid_rewrite hbr.
    (* both sides now speak of the same atoms *)
    unfold avg_prod.
    field; split; assumption.
  Qed.


  (* ---------------- basic facts about the expectation ---------------- *)

  Lemma qsum_map_nonneg :
    ∀ (B : Type) (f : B -> Q) (l : list B),
    (∀ x, List.In x l -> 0 <= f x) -> 0 <= qsum (List.map f l).
  Proof.
    intros B f; induction l as [| x l ih]; intro h; cbn; [lra |].
    pose proof (h x (or_introl eq_refl)).
    pose proof (ih (fun y hy => h y (or_intror hy))); lra.
  Qed.

  Lemma qsum_map_le :
    ∀ (B : Type) (f g : B -> Q) (l : list B),
    (∀ x, List.In x l -> f x <= g x) ->
    qsum (List.map f l) <= qsum (List.map g l).
  Proof.
    intros B f g; induction l as [| x l ih]; intro h; cbn; [lra |].
    pose proof (h x (or_introl eq_refl)).
    pose proof (ih (fun y hy => h y (or_intror hy))); lra.
  Qed.

  Lemma qsum_map_remove :
    ∀ (v : A -> Q) (l : list A) (x : A),
    List.NoDup l -> List.In x l ->
    qsum (List.map v (List.remove Adec x l)) == qsum (List.map v l) - v x.
  Proof.
    intros v l x; induction l as [| a l ih]; intros hnd hin;
    cbn in hin |- *; [contradiction |].
    inversion hnd as [| ? ? hna hnl]; subst.
    destruct (Adec x a) as [he | hne].
    + subst a; rewrite (remove_notin l x hna); ring.
    +
      destruct hin as [hc | hin]; [exfalso; eapply hne; symmetry; exact hc |].
      cbn; setoid_rewrite (ih hnl hin); ring.
  Qed.

  Lemma tuple_val_nonneg :
    ∀ (v : A -> Q) (ys : list A),
    (∀ x : A, 0 <= v x) -> 0 <= tuple_val v ys.
  Proof.
    intros v ys hv; unfold tuple_val.
    induction ys as [| y ys ih]; cbn; [lra |].
    pose proof (hv y); nra.
  Qed.

  Lemma avg_prod_zero : ∀ (v : A -> Q) (l : list A), avg_prod v l 0 == 1.
  Proof.
    intros v l; unfold avg_prod, tuple_val; cbn; reflexivity.
  Qed.

  Lemma avg_prod_nonneg :
    ∀ (v : A -> Q) (l : list A) (k : nat),
    (∀ x : A, 0 <= v x) -> List.NoDup l -> (k <= List.length l)%nat ->
    0 <= avg_prod v l k.
  Proof.
    intros v l k hv hnd hk; unfold avg_prod.
    eapply Qle_shift_div_l.
    +
      assert (hp : (0 < List.length (ktuples l k))%nat)
        by (rewrite (ktuples_length k l hnd); eapply falling_pos; exact hk).
      unfold qn; unfold Qlt; cbn; lia.
    +
      assert (h0 : 0 <= qsum (List.map (tuple_val v) (ktuples l k)))
        by (eapply qsum_map_nonneg; intros; eapply tuple_val_nonneg; exact hv).
      lra.
  Qed.

  (* ---------------- the key inequality ---------------- *)

  (*
    eps - (k-1)/q, written unnormalised so that the induction does not
    have to renormalise when the list shrinks.
  *)
  Lemma qsum_map_sub_const :
    ∀ (w : A -> Q) (c : Q) (l : list A),
    qsum (List.map (fun x => w x - c) l)
    == qsum (List.map w l) - c * qn (List.length l).
  Proof.
    intros w c; induction l as [| a l ih]; cbn.
    + unfold qn; cbn; ring.
    + setoid_rewrite ih; setoid_rewrite qn_succ; ring.
  Qed.

  Lemma qprod_list_ext :
    ∀ (v1 v2 : A -> Q) (ys : list A),
    (∀ x : A, v1 x == v2 x) ->
    qprod_list (List.map v1 ys) == qprod_list (List.map v2 ys).
  Proof.
    intros v1 v2 ys h; induction ys as [| y ys ih]; cbn; [reflexivity |].
    setoid_rewrite (h y); setoid_rewrite ih; reflexivity.
  Qed.

  Lemma avg_prod_ext :
    ∀ (v1 v2 : A -> Q) (l : list A) (k : nat),
    (∀ x : A, v1 x == v2 x) -> avg_prod v1 l k == avg_prod v2 l k.
  Proof.
    intros v1 v2 l k h; unfold avg_prod, tuple_val.
    setoid_rewrite (qsum_map_ext _ _ _ (ktuples l k)
      (fun ys _ => qprod_list_ext v1 v2 ys h)).
    reflexivity.
  Qed.

  (*
    eps - (k-1)/q - kap*(q-k+1)/q, unnormalised.  At the top of a round
    this is exactly eps - kap_at q kap k, the threshold Attema-Cramer's
    Equation 27 raises to as the recursion unwinds.
  *)
  Definition shift_thresh (w : A -> Q) (l : list A) (kap : Q) (k : nat) : Q :=
    (qsum (List.map w l) - (qn k - 1)
     - kap * (qn (List.length l) - qn k + 1)) / qn (List.length l).

  (*
    The bound with the threshold shift carried inside the induction.

    This is what the multi-round chaining needs.  Pulling the shift out
    first -- bounding the mean of clamp(w - kap) below by eps - kap and
    then applying the unshifted bound -- loses the factor (q-k+1)/q on
    kap, and with it the difference between Attema-Cramer's Equation 23
    and its cruder upper bound sum_i (k_i - 1)/q.  Carrying the shift
    through the peeling keeps the exact threshold.
  *)
  Theorem avg_prod_lower_shift :
    ∀ (k : nat) (w : A -> Q) (l : list A) (kap : Q),
    (∀ x : A, 0 <= w x /\ w x <= 1) ->
    0 <= kap -> kap <= 1 ->
    List.NoDup l -> (k <= List.length l)%nat ->
    qpow (clamp (shift_thresh w l kap k)) k
    <= avg_prod (fun c => clamp (w c - kap)) l k.
  Proof.
    induction k as [| k ih]; intros w l kap hw hk0 hk1 hnd hk.
    + cbn [qpow]; setoid_rewrite (avg_prod_zero _ l); lra.
    +
      assert (hw0 : ∀ x : A, 0 <= w x) by (intro x; eapply hw).
      assert (hV0 : ∀ x : A, 0 <= clamp (w x - kap)) by (intro; eapply clamp_nonneg).
      assert (hq : (0 < List.length l)%nat) by lia.
      assert (hqz : ~ qn (List.length l) == 0) by (eapply qn_pos; exact hq).
      assert (hqp : 0 < qn (List.length l)) by (unfold qn, Qlt; cbn; lia).
      assert (hB0 : 0 <= clamp (shift_thresh w l kap (S k))) by eapply clamp_nonneg.
      (* every child beats the parent's guarantee *)
      assert (hchild : ∀ x, List.In x l ->
        qpow (clamp (shift_thresh w l kap (S k))) k
        <= avg_prod (fun c => clamp (w c - kap)) (List.remove Adec x l) k).
      {
        intros x hx.
        assert (hrnd : List.NoDup (List.remove Adec x l))
          by (eapply remove_nodup; exact hnd).
        assert (hrlen : List.length (List.remove Adec x l)
                        = Nat.pred (List.length l))
          by (eapply remove_length_nodup; assumption).
        destruct k as [| k'].
        + cbn [qpow]; setoid_rewrite (avg_prod_zero _ _); lra.
        +
          assert (hq2 : (2 <= List.length l)%nat) by lia.
          eapply Qle_trans;
            [| eapply (ih w (List.remove Adec x l) kap hw hk0 hk1 hrnd);
               rewrite hrlen; lia].
          eapply qpow_mono; [eapply clamp_nonneg |].
          destruct (Qlt_le_dec (shift_thresh w l kap (S (S k'))) 0)
            as [hneg | hposm].
          ++
            assert (hz : clamp (shift_thresh w l kap (S (S k'))) == 0)
              by (unfold clamp; eapply Q.max_r; lra).
            setoid_rewrite hz; eapply clamp_nonneg.
          ++
            assert (hnum : 0 <= qsum (List.map w l) - (qn (S (S k')) - 1)
                                - kap * (qn (List.length l)
                                         - qn (S (S k')) + 1)).
            {
              unfold shift_thresh in hposm.
              assert (hd : (qsum (List.map w l) - (qn (S (S k')) - 1)
                            - kap * (qn (List.length l)
                                     - qn (S (S k')) + 1))
                           / qn (List.length l) * qn (List.length l)
                           == qsum (List.map w l) - (qn (S (S k')) - 1)
                              - kap * (qn (List.length l)
                                       - qn (S (S k')) + 1))
                by (field; exact hqz).
              nra.
            }
            eapply clamp_mono.
            unfold shift_thresh.
            setoid_rewrite (qsum_map_remove w l x hnd hx).
            rewrite hrlen.
            assert (hpm : qn (Nat.pred (List.length l))
                          == qn (List.length l) - 1).
            {
              replace (List.length l) with (S (Nat.pred (List.length l)))
                at 2 by lia.
              setoid_rewrite qn_succ; ring.
            }
            setoid_rewrite hpm.
            eapply qdiv_le_cross.
            +++ setoid_rewrite <-hpm; unfold qn, Qlt; cbn; lia.
            +++ setoid_rewrite <-hpm; eapply qn_le; lia.
            +++ exact hnum.
            +++
              setoid_rewrite (qn_succ (S k')).
              setoid_rewrite (qn_succ k').
              pose proof (proj2 (hw x)); nra.
      }
      (* sum the children *)
      assert (hsum :
        qpow (clamp (shift_thresh w l kap (S k))) k
        * qsum (List.map (fun c => clamp (w c - kap)) l)
        <= qsum (List.map
                   (fun x => clamp (w x - kap)
                             * avg_prod (fun c => clamp (w c - kap))
                                 (List.remove Adec x l) k) l)).
      {
        setoid_rewrite
          <-(qsum_scale _ (qpow (clamp (shift_thresh w l kap (S k))) k)
               (fun c => clamp (w c - kap))).
        eapply qsum_map_le; intros x hx.
        pose proof (hchild x hx) as hc.
        pose proof (hV0 x) as hvx.
        pose proof (qpow_nonneg k _ hB0) as hpB.
        nra.
      }
      (* the threshold never exceeds the shifted mean *)
      assert (hBq : clamp (shift_thresh w l kap (S k)) * qn (List.length l)
                    <= qsum (List.map (fun c => clamp (w c - kap)) l)).
      {
        assert (hlow : qsum (List.map w l) - kap * qn (List.length l)
                       <= qsum (List.map (fun c => clamp (w c - kap)) l)).
        {
          setoid_rewrite <-(qsum_map_sub_const w kap l).
          eapply qsum_map_le; intros x hx; eapply clamp_ge.
        }
        destruct (Qlt_le_dec (shift_thresh w l kap (S k)) 0) as [hneg | hposm].
        +
          assert (hz : clamp (shift_thresh w l kap (S k)) == 0)
            by (unfold clamp; eapply Q.max_r; lra).
          setoid_rewrite hz.
          assert (h0 : 0 <= qsum (List.map (fun c => clamp (w c - kap)) l))
            by (eapply qsum_map_nonneg; intros; eapply clamp_nonneg).
          nra.
        +
          assert (hz : clamp (shift_thresh w l kap (S k))
                       == shift_thresh w l kap (S k))
            by (unfold clamp; eapply Q.max_l; lra).
          setoid_rewrite hz; unfold shift_thresh.
          assert (hd : (qsum (List.map w l) - (qn (S k) - 1)
                        - kap * (qn (List.length l) - qn (S k) + 1))
                       / qn (List.length l) * qn (List.length l)
                       == qsum (List.map w l) - (qn (S k) - 1)
                          - kap * (qn (List.length l) - qn (S k) + 1))
            by (field; exact hqz).
          setoid_rewrite hd.
          setoid_rewrite (qn_succ k).
          pose proof (qn_nonneg k); nra.
      }
      setoid_rewrite (avg_prod_cons (fun c => clamp (w c - kap)) l k hnd hk).
      cbn [qpow].
      eapply Qle_shift_div_l; [exact hqp |].
      eapply Qle_trans; [| exact hsum].
      pose proof (qpow_nonneg k _ hB0) as hpB.
      nra.
  Qed.

  Definition mean_thresh (v : A -> Q) (l : list A) (k : nat) : Q :=
    (qsum (List.map v l) - (qn k - 1)) / qn (List.length l).

  (*
    Drawing k distinct challenges without replacement, the expected
    product of values in [0,1] with mean eps is at least
    max(eps - (k-1)/q, 0)^k.

    This is the bound Attema-Cramer reach through their inequality (26)
    and the sequential conditioning around it.  The induction here is
    shorter: avg_prod_cons peels off the first draw, and what remains
    needs only that each value is at most 1 (so the shrunken list's
    threshold does not drop) and that a smaller positive denominator
    only helps.
  *)
  Theorem avg_prod_lower :
    ∀ (k : nat) (v : A -> Q) (l : list A),
    (∀ x : A, 0 <= v x /\ v x <= 1) ->
    List.NoDup l -> (k <= List.length l)%nat ->
    qpow (clamp (mean_thresh v l k)) k <= avg_prod v l k.
  Proof.
    intros k v l hv hnd hk.
    (* the kap = 0 case of avg_prod_lower_shift *)
    assert (hext : ∀ x : A, clamp (v x - 0) == v x).
    {
      intro x; unfold clamp.
      assert (h : Qmax (v x - 0) 0 == v x - 0)
        by (eapply Q.max_l; pose proof (proj1 (hv x)); lra).
      setoid_rewrite h; ring.
    }
    setoid_rewrite <-(avg_prod_ext (fun c => clamp (v c - 0)) v l k hext).
    eapply Qle_trans;
      [| eapply (avg_prod_lower_shift k v l 0 hv); try lra; assumption].
    eapply qpow_mono; [eapply clamp_nonneg |].
    eapply clamp_mono.
    unfold shift_thresh, mean_thresh.
    assert (hnum : qsum (List.map v l) - (qn k - 1)
                   - 0 * (qn (List.length l) - qn k + 1)
                   == qsum (List.map v l) - (qn k - 1)) by ring.
    setoid_rewrite hnum; lra.
  Qed.


  (* ---------------- monotonicity and Jensen ---------------- *)

  Lemma qprod_list_mono :
    ∀ (v1 v2 : A -> Q) (ys : list A),
    (∀ x : A, 0 <= v1 x) -> (∀ x : A, v1 x <= v2 x) ->
    qprod_list (List.map v1 ys) <= qprod_list (List.map v2 ys).
  Proof.
    intros v1 v2 ys h0 h12; induction ys as [| y ys ih]; cbn; [lra |].
    assert (hp : 0 <= qprod_list (List.map v1 ys))
      by (eapply (tuple_val_nonneg v1 ys h0)).
    pose proof (h0 y); pose proof (h12 y); nra.
  Qed.

  Lemma avg_prod_mono :
    ∀ (v1 v2 : A -> Q) (l : list A) (k : nat),
    (∀ x : A, 0 <= v1 x) -> (∀ x : A, v1 x <= v2 x) ->
    List.NoDup l -> (k <= List.length l)%nat ->
    avg_prod v1 l k <= avg_prod v2 l k.
  Proof.
    intros v1 v2 l k h0 h12 hnd hk; unfold avg_prod.
    assert (hp : (0 < List.length (ktuples l k))%nat)
      by (rewrite (ktuples_length k l hnd); eapply falling_pos; exact hk).
    eapply qdiv_mono; [unfold qn, Qlt; cbn; lia |].
    eapply qsum_map_le; intros ys hys.
    unfold tuple_val; eapply qprod_list_mono; assumption.
  Qed.

  Lemma qprod_list_pow :
    ∀ (v : A -> Q) (K : nat) (ys : list A),
    qprod_list (List.map (fun c => qpow (v c) K) ys)
    == qpow (qprod_list (List.map v ys)) K.
  Proof.
    intros v K; induction ys as [| y ys ih]; cbn.
    + induction K as [| K ihk]; cbn; [reflexivity | setoid_rewrite <-ihk; ring].
    +
      setoid_rewrite ih.
      clear ih; induction K as [| K ihk]; cbn; [ring |].
      setoid_rewrite <-ihk; ring.
  Qed.

  (* uniform Jensen: a convex F may be pushed inside a uniform average *)
  Lemma wtot_uniform :
    ∀ (B : Type) (c : Q) (Z : B -> Q) (lb : list B),
    wtot (List.map (fun x => (c, Z x)) lb) == qn (List.length lb) * c.
  Proof.
    intros B c Z; induction lb as [| x lb ih]; cbn.
    + unfold qn; cbn; ring.
    + setoid_rewrite ih; setoid_rewrite qn_succ; ring.
  Qed.

  Lemma wsum_uniform :
    ∀ (B : Type) (c : Q) (Z : B -> Q) (lb : list B),
    wsum (List.map (fun x => (c, Z x)) lb) == c * qsum (List.map Z lb).
  Proof.
    intros B c Z; induction lb as [| x lb ih]; cbn; [ring |].
    setoid_rewrite ih; ring.
  Qed.

  Lemma wsumf_uniform :
    ∀ (B : Type) (F : Q -> Q) (c : Q) (Z : B -> Q) (lb : list B),
    wsumf F (List.map (fun x => (c, Z x)) lb)
    == c * qsum (List.map (fun x => F (Z x)) lb).
  Proof.
    intros B F c Z; induction lb as [| x lb ih]; cbn; [ring |].
    setoid_rewrite ih; ring.
  Qed.

  Lemma uniform_jensen :
    ∀ (B : Type) (F : Q -> Q) (Z : B -> Q) (lb : list B),
    Proper (Qeq ==> Qeq) F -> convex F ->
    (0 < List.length lb)%nat ->
    F (qsum (List.map Z lb) / qn (List.length lb))
    <= qsum (List.map (fun x => F (Z x)) lb) / qn (List.length lb).
  Proof.
    intros B F Z lb hF hcv hlb.
    assert (hmz : ~ qn (List.length lb) == 0) by (eapply qn_pos; exact hlb).
    assert (hmp : 0 < qn (List.length lb)) by (unfold qn, Qlt; cbn; lia).
    set (c := 1 / qn (List.length lb)).
    assert (hw : weights_nonneg (List.map (fun x => (c, Z x)) lb)).
    {
      eapply List.Forall_forall; intros p hp.
      eapply List.in_map_iff in hp; destruct hp as (x & hx & _); subst p.
      cbn; unfold c; eapply Qle_shift_div_l; lra.
    }
    assert (h1 : wtot (List.map (fun x => (c, Z x)) lb) == 1).
    { setoid_rewrite (wtot_uniform B c Z lb); unfold c; field; exact hmz. }
    pose proof (jensen F hF hcv _ hw h1) as hj.
    setoid_rewrite (wsum_uniform B c Z lb) in hj.
    setoid_rewrite (wsumf_uniform B F c Z lb) in hj.
    assert (he1 : c * qsum (List.map Z lb)
                  == qsum (List.map Z lb) / qn (List.length lb))
      by (unfold c; field; exact hmz).
    assert (he2 : c * qsum (List.map (fun x => F (Z x)) lb)
                  == qsum (List.map (fun x => F (Z x)) lb)
                     / qn (List.length lb))
      by (unfold c; field; exact hmz).
    setoid_rewrite he1 in hj; setoid_rewrite he2 in hj; exact hj.
  Qed.

  (* raising the whole draw to a power only helps *)
  Theorem avg_prod_pow :
    ∀ (v : A -> Q) (l : list A) (k K : nat),
    (∀ x : A, 0 <= v x) ->
    List.NoDup l -> (k <= List.length l)%nat ->
    qpow (avg_prod v l k) K
    <= avg_prod (fun c => qpow (v c) K) l k.
  Proof.
    intros v l k K hv hnd hk.
    assert (hp : (0 < List.length (ktuples l k))%nat)
      by (rewrite (ktuples_length k l hnd); eapply falling_pos; exact hk).
    (* F t = clamp(t)^K is convex, and agrees with t^K on non-negatives *)
    pose proof (uniform_jensen (list A) (shift_pow 0 K) (tuple_val v)
                  (ktuples l k) (shift_pow_proper 0 K)
                  (shift_pow_convex 0 K) hp) as hj.
    unfold avg_prod.
    eapply Qle_trans; [| eapply Qle_trans; [exact hj |]].
    +
      (* clamp is the identity on the non-negative average *)
      assert (havg : 0 <= qsum (List.map (tuple_val v) (ktuples l k))
                          / qn (List.length (ktuples l k))).
      {
        eapply Qle_shift_div_l; [unfold qn, Qlt; cbn; lia |].
        assert (h0 : 0 <= qsum (List.map (tuple_val v) (ktuples l k)))
          by (eapply qsum_map_nonneg; intros;
              eapply tuple_val_nonneg; exact hv).
        lra.
      }
      unfold shift_pow.
      assert (hc : clamp (qsum (List.map (tuple_val v) (ktuples l k))
                          / qn (List.length (ktuples l k)) - 0)
                   == qsum (List.map (tuple_val v) (ktuples l k))
                      / qn (List.length (ktuples l k)))
        by (unfold clamp; setoid_rewrite (Q.max_l _ 0); [ring | lra]).
      setoid_rewrite hc; lra.
    +
      eapply qdiv_mono; [unfold qn, Qlt; cbn; lia |].
      eapply qsum_map_le; intros ys hys.
      unfold shift_pow, tuple_val.
      setoid_rewrite (qprod_list_pow v K ys).
      assert (hz : 0 <= qprod_list (List.map v ys))
        by (eapply (tuple_val_nonneg v ys hv)).
      assert (hc : clamp (qprod_list (List.map v ys) - 0)
                   == qprod_list (List.map v ys))
        by (unfold clamp; setoid_rewrite (Q.max_l _ 0); [ring | lra]).
      setoid_rewrite hc; lra.
  Qed.

End Sampling.

(* ------------------------------------------------------------------ *)

Section Examples.

  (*
    Three challenges, drawn two at a time without replacement: six
    ordered pairs.  With two of the three leading to success the
    expectation is 1/3 and the bound is 1/9; with all three it is 1 and
    the bound is 4/9.  Both computed, so the statement is not vacuous.
  *)

  Import ListNotations.

  Definition ex_l : list nat := [0; 1; 2]%nat.
  Definition ex_two (n : nat) : Q := if Nat.ltb n 2 then 1 else 0.
  Definition ex_all (n : nat) : Q := 1.

  Example ex_draws : List.length (ktuples Nat.eq_dec ex_l 2) = 6%nat.
  Proof. reflexivity. Qed.

  Example ex_two_actual : Qred (avg_prod Nat.eq_dec ex_two ex_l 2) = (1 # 3).
  Proof. reflexivity. Qed.

  Example ex_two_bound :
    Qred (qpow (clamp (mean_thresh ex_two ex_l 2)) 2) = (1 # 9).
  Proof. reflexivity. Qed.

  Example ex_all_actual : Qred (avg_prod Nat.eq_dec ex_all ex_l 2) = 1.
  Proof. reflexivity. Qed.

  Example ex_all_bound :
    Qred (qpow (clamp (mean_thresh ex_all ex_l 2)) 2) = (4 # 9).
  Proof. reflexivity. Qed.

End Examples.
