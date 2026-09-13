From Stdlib Require Import Utf8 String Ascii List
  ZArith DecimalString DecimalZ Decimal Lia.

Import ListNotations.

(*
  Injectivity of the comma-separated decimal encoding used as
  Fiat-Shamir hash input.

  Nizk.ann_to_list_inj shows that flattening an announcement to a list
  of group elements loses nothing.  That leaves the last step of the
  chain: the list of group elements is rendered as decimal strings
  joined by a separator before being fed to SHA-256, and an ambiguous
  rendering would reintroduce exactly the binding failure that
  ann_to_list was introduced to prevent (two different announcements
  producing the same byte string).

  The lemmas here close that step.  The key one is concat_map_inj: if
  the per-element encoding is injective and never emits the separator,
  then joining a *fixed-length* list with that separator is injective.
  The length condition is necessary, not incidental — String.concat
  maps both [] and [""] to the empty string — and it is available in
  practice because the number of fields is determined by the statement
  tree, which is public.
*)

(* The separator does not occur in s. *)
Fixpoint no_char (c : ascii) (s : string) : Prop :=
  match s with
  | EmptyString => True
  | String a s' => a <> c ∧ no_char c s'
  end.

(* A field that avoids the separator is delimited by the first
   occurrence of it, so the split is unique. *)
Lemma split_at_sep :
  ∀ (c : ascii) (x y A B : string),
  no_char c x -> no_char c y ->
  (x ++ String c A)%string = (y ++ String c B)%string ->
  x = y ∧ A = B.
Proof.
  induction x as [| a x' ih]; intros y A B hx hy heq.
  +
    destruct y as [| b y']; cbn in heq.
    ++ injection heq as heq'; split; [reflexivity | exact heq'].
    ++
      injection heq as hcb heq'.
      destruct hy as (hby & _).
      exfalso; eapply hby; symmetry; exact hcb.
  +
    destruct hx as (hax & hx').
    destruct y as [| b y']; cbn in heq.
    ++
      injection heq as hac _.
      exfalso; eapply hax; exact hac.
    ++
      destruct hy as (hby & hy').
      injection heq as hab heq'.
      destruct (ih y' A B hx' hy' heq') as (h1 & h2).
      subst; split; reflexivity.
Qed.

Lemma concat_inj_len :
  ∀ (c : ascii) (l1 l2 : list string),
  List.length l1 = List.length l2 ->
  (∀ s, List.In s l1 -> no_char c s) ->
  (∀ s, List.In s l2 -> no_char c s) ->
  String.concat (String c EmptyString) l1
    = String.concat (String c EmptyString) l2 ->
  l1 = l2.
Proof.
  induction l1 as [| x xs ih]; intros l2 hlen h1 h2 heq.
  +
    destruct l2; [reflexivity | cbn in hlen; lia].
  +
    destruct l2 as [| y ys]; [cbn in hlen; lia |].
    cbn in hlen.
    destruct xs as [| x1 xs']; destruct ys as [| y1 ys'];
    try (cbn in hlen; lia).
    ++
      cbn in heq; subst; reflexivity.
    ++
      cbn [String.concat] in heq.
      cbn [String.append] in heq.
      destruct (split_at_sep c x y
        (String.concat (String c EmptyString) (x1 :: xs'))
        (String.concat (String c EmptyString) (y1 :: ys'))
        (h1 x (or_introl eq_refl)) (h2 y (or_introl eq_refl)) heq)
        as (hxy & hrest).
      subst.
      f_equal.
      eapply ih.
      +++ cbn in hlen |- *; lia.
      +++ intros s hs; eapply h1; right; exact hs.
      +++ intros s hs; eapply h2; right; exact hs.
      +++ exact hrest.
Qed.

(* Decimal rendering emits only digits (and a leading '-'), so any
   separator outside that set is safe. *)
Lemma no_sep_string_of_uint :
  ∀ (c : ascii) (d : uint),
  c <> "0"%char -> c <> "1"%char -> c <> "2"%char -> c <> "3"%char ->
  c <> "4"%char -> c <> "5"%char -> c <> "6"%char -> c <> "7"%char ->
  c <> "8"%char -> c <> "9"%char ->
  no_char c (NilEmpty.string_of_uint d).
Proof.
  intros c d h0 h1 h2 h3 h4 h5 h6 h7 h8 h9.
  induction d; cbn; try exact I;
  split; try assumption; congruence.
Qed.

Lemma no_sep_string_of_int :
  ∀ (c : ascii) (i : int),
  c <> "-"%char ->
  c <> "0"%char -> c <> "1"%char -> c <> "2"%char -> c <> "3"%char ->
  c <> "4"%char -> c <> "5"%char -> c <> "6"%char -> c <> "7"%char ->
  c <> "8"%char -> c <> "9"%char ->
  no_char c (NilEmpty.string_of_int i).
Proof.
  intros c i hm h0 h1 h2 h3 h4 h5 h6 h7 h8 h9.
  destruct i as [d | d]; cbn.
  + eapply no_sep_string_of_uint; assumption.
  + split; [congruence | eapply no_sep_string_of_uint; assumption].
Qed.

(* The comma, specifically — the separator the instances use. *)
Lemma no_comma_string_of_int :
  ∀ (i : int), no_char ","%char (NilEmpty.string_of_int i).
Proof.
  intro i.
  eapply no_sep_string_of_int; intro h; discriminate h.
Qed.

(* Decimal rendering is injective, by its parsing round-trip. *)
Lemma string_of_int_inj :
  ∀ (i j : int),
  NilEmpty.string_of_int i = NilEmpty.string_of_int j -> i = j.
Proof.
  intros i j heq.
  pose proof (NilEmpty.isi i) as hi.
  rewrite heq in hi.
  rewrite (NilEmpty.isi j) in hi.
  injection hi as hij; symmetry; exact hij.
Qed.

(*
  The packaged statement: joining a fixed-length list with a separator
  the encoding never emits is injective, so distinct lists give
  distinct strings.
*)
Lemma concat_map_inj :
  ∀ (A : Type) (c : ascii) (enc : A -> string) (l1 l2 : list A),
  (∀ x y, enc x = enc y -> x = y) ->
  (∀ x, no_char c (enc x)) ->
  List.length l1 = List.length l2 ->
  String.concat (String c EmptyString) (List.map enc l1)
    = String.concat (String c EmptyString) (List.map enc l2) ->
  l1 = l2.
Proof.
  intros A c enc l1 l2 hinj hno hlen heq.
  assert (hmap : List.map enc l1 = List.map enc l2).
  {
    eapply (concat_inj_len c).
    + rewrite !List.length_map; exact hlen.
    + intros s hs; eapply List.in_map_iff in hs.
      destruct hs as (x & hx & _); subst; eapply hno.
    + intros s hs; eapply List.in_map_iff in hs.
      destruct hs as (x & hx & _); subst; eapply hno.
    + exact heq.
  }
  clear heq hlen.
  revert l2 hmap.
  induction l1 as [| x xs ih]; intros [| y ys] hmap; cbn in hmap;
  try discriminate hmap; [reflexivity |].
  injection hmap as hxy hrest.
  f_equal; [eapply hinj; exact hxy | eapply ih; exact hrest].
Qed.
