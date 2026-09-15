From Stdlib Require Import Utf8 List Bool Arith.
From Boundary Require Import Schema Character.

Import ListNotations.

(** * Splitting the secrets does not help

    [Character.v] breaks exactness with a general quadratic schema.
    The natural hope is that the pairing-based statements people
    actually write are safe, because a pairing-product equation is not
    an arbitrary quadratic: the secrets split into two blocks, one per
    source group, and every product takes one factor from each. A
    secret cannot be multiplied by itself, so the square root that did
    the damage looks unavailable.

    It is available. A pairing-product equation may also carry linear
    terms in either block -- that is what [e(g1^x, g2)] contributes --
    and a linear term is enough to identify a secret across the split.
    Once [x] in the first block is tied to [y] in the second, the
    product [x * y] is a square in disguise.

    So the schema below has four secrets, [u] and [x] in the first
    block and [v] and [y] in the second. Every constraint is a legal
    pairing-product relation:

      u v = u,   u v = v,   x - y = 0,   u y = y,   x v = x,
      x y + a u = 0.

    The first two make [u] and [v] equal and idempotent, the gates
    collapse [x] and [y] when [u] is zero, and the third identifies the
    two blocks' copy of the secret, so the last constraint reads
    [x * x = -a] when [u] is one. The schema therefore determines
    exactly when [-a] is a quadratic non-residue, and we are back where
    [Character.v] was.

    [Bilinear.v] closes the other side: forbid the linear terms and
    determination becomes decidable but always false. Between them
    there is no useful class above the linear one. *)

(** ** Pairing-product relations over two blocks

    We write the relation in the exponents, which is where the
    condition lives: a coefficient for each cross pair, a coefficient
    for each secret on its own, and a target. There is deliberately no
    coefficient for [u v'] within a block, since a pairing cannot form
    one. *)

Definition wit4 : Type := Fp * Fp * Fp * Fp.

Record ppe : Type := mkppe
  { g_uv : coeff ; g_uy : coeff ; g_xv : coeff ; g_xy : coeff
  ; a_u : coeff ; a_x : coeff
  ; b_v : coeff ; b_y : coeff
  ; p_t : coeff }.

Definition peval (i : env) (e : ppe) (w : wit4) : Fp :=
  let '(u, v, x, y) := w in
  fadd (fadd (fadd (fadd (fadd (fadd (fadd
    (fmul (cval i (g_uv e)) (fmul u v))
    (fmul (cval i (g_uy e)) (fmul u y)))
    (fmul (cval i (g_xv e)) (fmul x v)))
    (fmul (cval i (g_xy e)) (fmul x y)))
    (fmul (cval i (a_u e)) u))
    (fmul (cval i (a_x e)) x))
    (fmul (cval i (b_v e)) v))
    (fmul (cval i (b_y e)) y).

Definition psatb (i : env) (e : ppe) (w : wit4) : bool :=
  Fp_eqb (peval i e w) (cval i (p_t e)).

Definition psat (i : env) (e : ppe) (w : wit4) : Prop :=
  psatb i e w = true.

(** ** The schema

    [blank] is the relation with every coefficient zero; each
    constraint names only the coefficients it needs. [F6] is [-1]. *)

Definition K0 : coeff := Kc F0.

Definition blank : ppe := mkppe K0 K0 K0 K0 K0 K0 K0 K0 K0.

(** u v = u *)
Definition idem_u : ppe :=
  {| g_uv := Kc F1 ; g_uy := K0 ; g_xv := K0 ; g_xy := K0
   ; a_u := Kc F6 ; a_x := K0 ; b_v := K0 ; b_y := K0 ; p_t := K0 |}.

(** u v = v *)
Definition idem_v : ppe :=
  {| g_uv := Kc F1 ; g_uy := K0 ; g_xv := K0 ; g_xy := K0
   ; a_u := K0 ; a_x := K0 ; b_v := Kc F6 ; b_y := K0 ; p_t := K0 |}.

(** x - y = 0: the linear term that ties the two blocks together *)
Definition tie : ppe :=
  {| g_uv := K0 ; g_uy := K0 ; g_xv := K0 ; g_xy := K0
   ; a_u := K0 ; a_x := Kc F1 ; b_v := K0 ; b_y := Kc F6 ; p_t := K0 |}.

(** u y = y *)
Definition gate_y : ppe :=
  {| g_uv := K0 ; g_uy := Kc F1 ; g_xv := K0 ; g_xy := K0
   ; a_u := K0 ; a_x := K0 ; b_v := K0 ; b_y := Kc F6 ; p_t := K0 |}.

(** x v = x *)
Definition gate_x : ppe :=
  {| g_uv := K0 ; g_uy := K0 ; g_xv := Kc F1 ; g_xy := K0
   ; a_u := K0 ; a_x := Kc F6 ; b_v := K0 ; b_y := K0 ; p_t := K0 |}.

(** x y + a u = 0, which reads x * x = -a once u is one *)
Definition square : ppe :=
  {| g_uv := K0 ; g_uy := K0 ; g_xv := K0 ; g_xy := Kc F1
   ; a_u := Kn a_nm ; a_x := K0 ; b_v := K0 ; b_y := K0 ; p_t := K0 |}.

Definition split : list ppe :=
  [idem_u; idem_v; tie; gate_y; gate_x; square].

Definition faithful4 (i : env) (_ : list ppe) : Prop := i a_nm <> F0.

(** [-2 = 5] is a non-residue mod seven and [-3 = 4] is a residue, so
    the first environment determines and the second does not. *)
Definition i_det   : env := fun _ => F2.
Definition i_undet : env := fun _ => F3.

Lemma faithful_det : ∀ s, faithful4 i_det s.
Proof. intros s; discriminate. Qed.

Lemma faithful_undet : ∀ s, faithful4 i_undet s.
Proof. intros s; discriminate. Qed.

(** ** Membership is a computation *)

Definition splitb (i : env) (w : wit4) : bool :=
  List.forallb (fun e => psatb i e w) split.

Lemma Sol_iff : ∀ (i : env) (w : wit4),
  Sol psat i split w <-> splitb i w = true.
Proof.
  intros i w; unfold Sol, splitb; split; intro h.
  + apply List.forallb_forall; intros e he.
    rewrite List.Forall_forall in h; exact (h e he).
  + apply List.Forall_forall; intros e he.
    exact (proj1 (List.forallb_forall _ split) h e he).
Qed.

(** ** An exhaustive check

    Four secrets over seven values is a finite question, and stating it
    as one boolean keeps the proofs to a single evaluation each rather
    than to two thousand case splits. *)

Definition enum : list Fp := [F0; F1; F2; F3; F4; F5; F6].

Lemma in_enum : ∀ x : Fp, List.In x enum.
Proof. intro x; destruct x; cbn; tauto. Qed.

Definition quad : list wit4 :=
  List.flat_map (fun u =>
  List.flat_map (fun v =>
  List.flat_map (fun x =>
  List.map (fun y => (u, v, x, y)) enum) enum) enum) enum.

Lemma in_quad : ∀ w : wit4, List.In w quad.
Proof.
  intros ((( u & v) & x) & y); unfold quad.
  apply List.in_flat_map; exists u; split; [apply in_enum |].
  apply List.in_flat_map; exists v; split; [apply in_enum |].
  apply List.in_flat_map; exists x; split; [apply in_enum |].
  apply List.in_map_iff; exists y; split; [reflexivity | apply in_enum].
Qed.

Definition origin : wit4 := (F0, F0, F0, F0).

Definition wit4_eqb (w w' : wit4) : bool :=
  let '(u, v, x, y) := w in
  let '(u', v', x', y') := w' in
  Fp_eqb u u' && Fp_eqb v v' && Fp_eqb x x' && Fp_eqb y y'.

Lemma wit4_eqb_eq : ∀ w w' : wit4, wit4_eqb w w' = true -> w = w'.
Proof.
  intros ((( u & v) & x) & y) ((( u' & v') & x') & y') h; cbn in h.
  apply andb_true_iff in h as (h & hy).
  apply andb_true_iff in h as (h & hx).
  apply andb_true_iff in h as (hu & hv).
  apply Fp_eqb_eq in hu, hv, hx, hy; subst; reflexivity.
Qed.

(** ** The non-residue determines *)

Lemma det_check :
  List.forallb (fun w => implb (splitb i_det w) (wit4_eqb w origin)) quad = true.
Proof. vm_compute; reflexivity. Qed.

Theorem split_determines : determines psat i_det split.
Proof.
  exists origin; split.
  + apply Sol_iff; vm_compute; reflexivity.
  + intros w' h; apply Sol_iff in h.
    apply wit4_eqb_eq.
    pose proof (proj1 (List.forallb_forall _ quad) det_check w' (in_quad w')) as hw.
    cbv beta in hw; rewrite h in hw; cbn [implb] in hw; exact hw.
Qed.

(** ** The residue does not

    With [-a = 4 = 2 * 2] the gate can open, and the two square roots
    of four join the origin. *)

Theorem split_does_not_determine : ¬ determines psat i_undet split.
Proof.
  intros (w & _ & hu).
  assert (horigin : origin = w) by (apply hu, Sol_iff; vm_compute; reflexivity).
  assert (hroot : (F1, F1, F2, F2) = w)
    by (apply hu, Sol_iff; vm_compute; reflexivity).
  rewrite <- horigin in hroot; discriminate.
Qed.

(** ** Consequences *)

Theorem split_is_sensitive :
  interpretation_sensitive psat faithful4 split.
Proof.
  exists i_det, i_undet.
  repeat split.
  + exact (faithful_det split).
  + exact (faithful_undet split).
  + exact split_determines.
  + exact split_does_not_determine.
Qed.

Theorem no_exact_criterion_for_pairings :
  ∀ crit : criterion (Constraint := ppe), ¬ exact psat faithful4 crit.
Proof.
  apply (sensitivity_refutes_every_criterion psat faithful4 split
           split_is_sensitive).
Qed.
