From Stdlib Require Import Utf8 List Lia Morphisms ZArith
  QArith Qminmax micromega.Lqa.

Import ListNotations.
Open Scope Q_scope.

(*
  Convexity and Jensen's inequality over the rationals.

  This is the piece Attema-Cramer's Appendix A needs and Prob.v cannot
  supply: Prob.prob is {num : nat; denum : positive} and non-negative
  by construction, while the functions in the extractor analysis take
  negative values.  Stdlib's Q is signed and comes with lra/nra, so the
  whole development below is elementary -- no reals, no derivatives,
  and in particular no appeal to "f'' >= 0", which is how the paper
  establishes convexity.

  Delivered:
    convex, nondecreasing        -- the definitions
    qpow_convex_nonneg           -- t |-> t^n is convex on non-negatives
    clamp_convex                 -- x |-> max(x, 0) is convex
    shift_pow_convex             -- x |-> max(x - kap, 0)^K is convex,
                                    which is the paper's Equation 28
    jensen                       -- the weighted finite-sum form

  Everything is stated with Qle and Qeq, so the Proper instances below
  are not decoration: Q's equality is setoid equality, and an arbitrary
  f : Q -> Q need not respect it.  Where a theorem applies f to two
  Qeq-equal arguments it takes `Proper (Qeq ==> Qeq) f' as a
  hypothesis.
*)

Section Convexity.

  Definition convex (f : Q -> Q) : Prop :=
    ∀ (a b l : Q), 0 <= l -> l <= 1 ->
    f (l * a + (1 - l) * b) <= l * f a + (1 - l) * f b.

  Definition nondecreasing (f : Q -> Q) : Prop :=
    ∀ a b : Q, a <= b -> f a <= f b.

  (* ---------------- powers ---------------- *)

  Fixpoint qpow (x : Q) (n : nat) : Q :=
    match n with
    | 0%nat => 1
    | S m => x * qpow x m
    end.

  #[export] Instance qpow_proper : Proper (Qeq ==> eq ==> Qeq) qpow.
  Proof.
    intros x y hxy n m hnm; subst m.
    induction n as [| n ih]; cbn; [reflexivity |].
    setoid_rewrite hxy at 1; setoid_rewrite ih; reflexivity.
  Qed.

  Lemma qpow_nonneg : ∀ (n : nat) (x : Q), 0 <= x -> 0 <= qpow x n.
  Proof.
    induction n as [| n ih]; intros x hx; cbn; [lra |].
    pose proof (ih x hx); nra.
  Qed.

  Lemma qpow_mono :
    ∀ (n : nat) (x y : Q), 0 <= x -> x <= y -> qpow x n <= qpow y n.
  Proof.
    induction n as [| n ih]; intros x y hx hxy; cbn; [lra |].
    pose proof (ih x y hx hxy) as ihn.
    pose proof (qpow_nonneg n x hx).
    nra.
  Qed.

  (* the sign fact that drives the convexity induction:
     (a - b) and (a^n - b^n) never disagree on non-negatives *)
  Lemma qpow_diff_sign :
    ∀ (n : nat) (a b : Q), 0 <= a -> 0 <= b ->
    0 <= (a - b) * (qpow a n - qpow b n).
  Proof.
    intros n a b ha hb.
    destruct (Qlt_le_dec a b) as [hlt | hle].
    + pose proof (qpow_mono n a b ha ltac:(lra)); nra.
    + pose proof (qpow_mono n b a hb hle); nra.
  Qed.

  Lemma qpow_convex_nonneg :
    ∀ (n : nat) (a b l : Q),
    0 <= a -> 0 <= b -> 0 <= l -> l <= 1 ->
    qpow (l * a + (1 - l) * b) n <= l * qpow a n + (1 - l) * qpow b n.
  Proof.
    induction n as [| n ih]; intros a b l ha hb hl0 hl1; cbn [qpow]; [lra |].
    pose proof (ih a b l ha hb hl0 hl1) as ihn.
    pose proof (qpow_nonneg n a ha) as pa.
    pose proof (qpow_nonneg n b hb) as pb.
    pose proof (qpow_diff_sign n a b ha hb) as hs.
    assert (hm : 0 <= l * a + (1 - l) * b) by nra.
    assert (hll : 0 <= l * (1 - l)) by nra.
    eapply Qle_trans with
      ((l * a + (1 - l) * b) * (l * qpow a n + (1 - l) * qpow b n)).
    +
      setoid_rewrite (Qmult_comm (l * a + (1 - l) * b)).
      eapply Qmult_le_compat_r; assumption.
    +
      (* the gap is exactly l(1-l)(a-b)(a^n - b^n), which qpow_diff_sign
         says is non-negative *)
      assert (hpos : 0 <= l * (1 - l)
                          * ((a - b) * (qpow a n - qpow b n))) by nra.
      nra.
  Qed.

  (* ---------------- the clamp ---------------- *)

  Definition clamp (x : Q) : Q := Qmax x 0.

  #[export] Instance clamp_proper : Proper (Qeq ==> Qeq) clamp.
  Proof.
    intros x y hxy; unfold clamp; setoid_rewrite hxy; reflexivity.
  Qed.

  Lemma clamp_nonneg : ∀ x : Q, 0 <= clamp x.
  Proof. intro x; unfold clamp; eapply Q.le_max_r. Qed.

  Lemma clamp_ge : ∀ x : Q, x <= clamp x.
  Proof. intro x; unfold clamp; eapply Q.le_max_l. Qed.

  Lemma clamp_lub : ∀ x z : Q, x <= z -> 0 <= z -> clamp x <= z.
  Proof. intros x z h1 h2; unfold clamp; eapply Q.max_lub; assumption. Qed.

  Lemma clamp_mono : ∀ x y : Q, x <= y -> clamp x <= clamp y.
  Proof.
    intros x y h; eapply clamp_lub;
    [eapply Qle_trans; [exact h | eapply clamp_ge] | eapply clamp_nonneg].
  Qed.

  Lemma clamp_convex : convex clamp.
  Proof.
    intros a b l hl0 hl1.
    pose proof (clamp_ge a); pose proof (clamp_ge b).
    pose proof (clamp_nonneg a); pose proof (clamp_nonneg b).
    eapply clamp_lub; nra.
  Qed.

  (* ---------------- the paper's Equation 28 ---------------- *)

  (* f(x) = (x - kap)^K for x >= kap, and 0 otherwise *)
  Definition shift_pow (kap : Q) (K : nat) (x : Q) : Q :=
    qpow (clamp (x - kap)) K.

  #[export] Instance shift_pow_proper :
    ∀ kap K, Proper (Qeq ==> Qeq) (shift_pow kap K).
  Proof.
    intros kap K x y hxy; unfold shift_pow.
    setoid_rewrite hxy; reflexivity.
  Qed.

  (* Proper in the threshold too, so the kappa recursion can be
     rewritten under shift_pow *)
  #[export] Instance shift_pow_proper_all :
    Proper (Qeq ==> eq ==> Qeq ==> Qeq) shift_pow.
  Proof.
    intros k1 k2 hk n m hnm x y hxy; subst m; unfold shift_pow.
    setoid_rewrite hk; setoid_rewrite hxy; reflexivity.
  Qed.

  Lemma shift_pow_nonneg : ∀ kap K x, 0 <= shift_pow kap K x.
  Proof.
    intros kap K x; unfold shift_pow.
    eapply qpow_nonneg, clamp_nonneg.
  Qed.

  Lemma shift_pow_convex : ∀ (kap : Q) (K : nat), convex (shift_pow kap K).
  Proof.
    intros kap K a b l hl0 hl1; unfold shift_pow.
    (* the shift distributes over the convex combination *)
    assert (hsh : l * a + (1 - l) * b - kap
                  == l * (a - kap) + (1 - l) * (b - kap)) by ring.
    setoid_rewrite hsh.
    eapply Qle_trans with
      (qpow (l * clamp (a - kap) + (1 - l) * clamp (b - kap)) K).
    +
      eapply qpow_mono; [eapply clamp_nonneg |].
      eapply clamp_convex; assumption.
    +
      eapply qpow_convex_nonneg;
      [eapply clamp_nonneg | eapply clamp_nonneg | assumption | assumption].
  Qed.


  (* ---------------- weighted sums and Jensen ---------------- *)

  (* a finite distribution, as a list of (weight, point) pairs *)
  Fixpoint wtot (l : list (Q * Q)) : Q :=
    match l with
    | []%list => 0
    | ((w, _) :: t)%list => w + wtot t
    end.

  Fixpoint wsum (l : list (Q * Q)) : Q :=
    match l with
    | []%list => 0
    | ((w, x) :: t)%list => w * x + wsum t
    end.

  Fixpoint wsumf (f : Q -> Q) (l : list (Q * Q)) : Q :=
    match l with
    | []%list => 0
    | ((w, x) :: t)%list => w * f x + wsumf f t
    end.

  Definition weights_nonneg (l : list (Q * Q)) : Prop :=
    List.Forall (fun wx => 0 <= fst wx) l.

  Lemma wtot_nonneg : ∀ l, weights_nonneg l -> 0 <= wtot l.
  Proof.
    induction l as [| (w, x) t ih]; intros hw; cbn; [lra |].
    inversion hw as [| ? ? h1 h2]; subst; cbn in h1.
    pose proof (ih h2); lra.
  Qed.

  Lemma wsum_zero : ∀ l, weights_nonneg l -> wtot l == 0 -> wsum l == 0.
  Proof.
    induction l as [| (w, x) t ih]; intros hw h0; cbn in *; [reflexivity |].
    inversion hw as [| ? ? h1 h2]; subst; cbn in h1.
    pose proof (wtot_nonneg t h2) as ht.
    assert (hw0 : w == 0) by lra.
    assert (ht0 : wtot t == 0) by lra.
    rewrite (ih h2 ht0).
    setoid_rewrite hw0; ring.
  Qed.

  Lemma wsumf_zero :
    ∀ f l, weights_nonneg l -> wtot l == 0 -> wsumf f l == 0.
  Proof.
    intros f; induction l as [| (w, x) t ih]; intros hw h0;
    cbn in *; [reflexivity |].
    inversion hw as [| ? ? h1 h2]; subst; cbn in h1.
    pose proof (wtot_nonneg t h2) as ht.
    assert (hw0 : w == 0) by lra.
    assert (ht0 : wtot t == 0) by lra.
    rewrite (ih h2 ht0).
    setoid_rewrite hw0; ring.
  Qed.

  (*
    Jensen, in the form the induction wants: no normalisation of the
    weights, so the inductive step never has to rescale a list.
  *)
  Theorem jensen_scaled :
    ∀ (f : Q -> Q), Proper (Qeq ==> Qeq) f -> convex f ->
    ∀ (l : list (Q * Q)), weights_nonneg l -> 0 < wtot l ->
    wtot l * f (wsum l / wtot l) <= wsumf f l.
  Proof.
    intros f hf hcv.
    induction l as [| (w, x) t ih]; intros hw hpos; cbn in hpos |- *;
    [lra |].
    inversion hw as [| ? ? h1 h2]; subst; cbn in h1.
    pose proof (wtot_nonneg t h2) as ht.
    destruct (Qlt_le_dec 0 (wtot t)) as [htp | htz].
    +
      (* both parts carry weight: one application of convexity *)
      assert (hW : ~ (w + wtot t) == 0) by lra.
      assert (hT : ~ wtot t == 0) by lra.
      assert (hsplit : (w * x + wsum t) / (w + wtot t)
                       == (w / (w + wtot t)) * x
                          + (1 - w / (w + wtot t)) * (wsum t / wtot t))
        by (field; repeat split; assumption).
      assert (hfe : f ((w * x + wsum t) / (w + wtot t))
                    == f ((w / (w + wtot t)) * x
                          + (1 - w / (w + wtot t)) * (wsum t / wtot t)))
        by (eapply hf; exact hsplit).
      setoid_rewrite hfe.
      assert (hl0 : 0 <= w / (w + wtot t))
        by (eapply Qle_shift_div_l; lra).
      assert (hl1 : w / (w + wtot t) <= 1)
        by (eapply Qle_shift_div_r; lra).
      pose proof (hcv x (wsum t / wtot t) (w / (w + wtot t)) hl0 hl1) as hc.
      pose proof (ih h2 htp) as iht.
      assert (hWc : (w + wtot t)
                    * ((w / (w + wtot t)) * f x
                       + (1 - w / (w + wtot t)) * f (wsum t / wtot t))
                    == w * f x + wtot t * f (wsum t / wtot t))
        by (field; exact hW).
      eapply Qle_trans with
        ((w + wtot t)
         * ((w / (w + wtot t)) * f x
            + (1 - w / (w + wtot t)) * f (wsum t / wtot t))).
      ++
        setoid_rewrite (Qmult_comm (w + wtot t)).
        eapply Qmult_le_compat_r; lra.
      ++
        setoid_rewrite hWc; lra.
    +
      (* the tail carries no weight *)
      assert (ht0 : wtot t == 0) by lra.
      setoid_rewrite (wsum_zero t h2 ht0).
      setoid_rewrite (wsumf_zero f t h2 ht0).
      assert (hw0 : ~ w == 0) by lra.
      assert (heq : (w * x + 0) / (w + wtot t) == x)
        by (setoid_rewrite ht0; field; exact hw0).
      assert (hfe : f ((w * x + 0) / (w + wtot t)) == f x)
        by (eapply hf; exact heq).
      setoid_rewrite hfe.
      setoid_rewrite ht0.
      lra.
  Qed.

  (* the usual statement: weights summing to one *)
  Corollary jensen :
    ∀ (f : Q -> Q), Proper (Qeq ==> Qeq) f -> convex f ->
    ∀ (l : list (Q * Q)), weights_nonneg l -> wtot l == 1 ->
    f (wsum l) <= wsumf f l.
  Proof.
    intros f hf hcv l hw h1.
    pose proof (jensen_scaled f hf hcv l hw ltac:(rewrite h1; lra)) as hj.
    assert (heq : wsum l / wtot l == wsum l)
      by (setoid_rewrite h1; field).
    assert (hfe : f (wsum l / wtot l) == f (wsum l))
      by (eapply hf; exact heq).
    setoid_rewrite hfe in hj.
    setoid_rewrite h1 in hj.
    lra.
  Qed.


  (* ---------------- rationals from naturals ---------------- *)

  Definition qn (n : nat) : Q := inject_Z (Z.of_nat n).

  Lemma qn_nonneg : ∀ n, 0 <= qn n.
  Proof.
    intro n; unfold qn, Qle, inject_Z; cbn; lia.
  Qed.

  Lemma qn_le : ∀ m n, (m <= n)%nat -> qn m <= qn n.
  Proof.
    intros m n h; unfold qn, Qle, inject_Z; cbn; lia.
  Qed.

  Lemma qn_sub :
    ∀ m n, (n <= m)%nat -> qn (m - n)%nat == qn m - qn n.
  Proof.
    intros m n h; unfold qn.
    rewrite Nat2Z.inj_sub by exact h.
    unfold Qminus, Qopp, inject_Z, Qplus; cbn.
    unfold Qeq; cbn; lia.
  Qed.

  Lemma qn_add : ∀ m n, qn (m + n)%nat == qn m + qn n.
  Proof.
    intros m n; unfold qn.
    rewrite Nat2Z.inj_add.
    unfold inject_Z, Qplus, Qeq; cbn; lia.
  Qed.

  Lemma qn_mul : ∀ m n, qn (m * n)%nat == qn m * qn n.
  Proof.
    intros m n; unfold qn.
    rewrite Nat2Z.inj_mul.
    unfold inject_Z, Qmult, Qeq; cbn; lia.
  Qed.

  Lemma qn_one : qn 1 == 1.
  Proof. reflexivity. Qed.

  Lemma qdiv_mono : ∀ (a b q : Q), 0 < q -> a <= b -> a / q <= b / q.
  Proof.
    intros a b q hq hab.
    assert (h1 : a / q == a * (1 / q)) by (field; lra).
    assert (h2 : b / q == b * (1 / q)) by (field; lra).
    setoid_rewrite h1; setoid_rewrite h2.
    eapply Qmult_le_compat_r; [exact hab |].
    eapply Qle_shift_div_l; lra.
  Qed.

  Lemma qn_succ : ∀ n : nat, qn (S n) == qn n + 1.
  Proof.
    intro n; replace (S n) with (n + 1)%nat by lia.
    setoid_rewrite qn_add; setoid_rewrite qn_one; reflexivity.
  Qed.

  (* a bigger numerator over a smaller positive denominator *)
  Lemma qdiv_le_cross :
    ∀ (n1 n2 d1 d2 : Q),
    0 < d1 -> d1 <= d2 -> 0 <= n1 -> n1 <= n2 ->
    n1 / d2 <= n2 / d1.
  Proof.
    intros n1 n2 d1 d2 hd1 hd12 hn1 hn12.
    assert (hd2 : 0 < d2) by lra.
    eapply Qle_shift_div_r; [exact hd2 |].
    assert (h : (n2 / d1) * d2 == n2 * d2 / d1) by (field; lra).
    setoid_rewrite h.
    eapply Qle_shift_div_l; [exact hd1 |].
    nra.
  Qed.

  (* ---------------- sums and products over lists ---------------- *)

  Fixpoint qsum (l : list Q) : Q :=
    match l with
    | []%list => 0
    | (x :: t)%list => x + qsum t
    end.

  Fixpoint qprod_list (l : list Q) : Q :=
    match l with
    | []%list => 1
    | (x :: t)%list => x * qprod_list t
    end.

  Lemma qprod_list_lower :
    ∀ (c : Q) (P : list Q),
    0 <= c -> List.Forall (fun p => c <= p) P ->
    qpow c (List.length P) <= qprod_list P.
  Proof.
    intros c P hc; induction P as [| p t ih]; intro hall;
    cbn [qpow qprod_list List.length].
    + lra.
    +
      pose proof (List.Forall_inv hall) as hp; cbv beta in hp.
      pose proof (ih (List.Forall_inv_tail hall)) as iht.
      pose proof (qpow_nonneg (List.length t) c hc) as hpc.
      assert (hY : 0 <= qprod_list t) by lra.
      (* p*Y - c*X = (p-c)*Y + c*(Y-X), both summands non-negative *)
      assert (h1 : 0 <= (p - c) * qprod_list t) by nra.
      assert (h2 : 0 <= c * (qprod_list t - qpow c (List.length t)))
        by nra.
      nra.
  Qed.

End Convexity.
