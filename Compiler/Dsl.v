From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef
  BinPos List PeanoNat Permutation Arith.
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
  LinearRelation Composition.

Import VectorNotations.

(*
  The statement language.

  A statement is a monotone formula over linear group equations:

      stmt ::= SEqs [e₁; …; eₘ]            conjunction of equations
             | SAnd stmt stmt | SOr stmt stmt
             | SThresh t [s₁; …; sₖ]        at least t of the sᵢ

  An equation is  Π Bᵢ ^ (cᵢ · xᵢ) · Π Pⱼ ^ cⱼ = 1  with private
  scalars xᵢ, public scalars cᵢ (expressions), points Bᵢ, Pⱼ.

  Variables are abstract (any type with decidable equality).  The
  instance is given by environments: genv (points), penv (public
  scalars); the witness by wenv (private scalars).  The formula
  itself carries no instance data.

  Compilation targets Composition.comp_rel.  Every AND-tree of
  equations becomes one Leaf whose columns are the declared private
  variables privs, so variables shared between equations are bound
  by one witness vector.  SOr becomes COr and SThresh becomes
  CThresh (polynomial size; no expansion into subsets), with
  threshold nodes supplied by a parameter `node : nat -> F` and
  checked distinct at compile time.
*)

Section Dsl.

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

  (* Variables *)
  Context
    {V : Type}
    {vdec : forall x y : V, {x = y} + {x <> y}}.

  #[local] Infix "^" := gpow.
  #[local] Infix "*" := mul.
  #[local] Infix "+" := add.

  Definition veqb (x y : V) : bool :=
    if vdec x y then true else false.

  Definition feqb (x y : F) : bool :=
    if Fdec x y then true else false.

  (* Section-closed constants from LinearRelation.v/Composition.v,
     applied to this section's structure. *)
  #[local] Notation row_evalC :=
    (@row_eval F G gid gop gpow _).
  #[local] Notation comp_relC := (@comp_rel F zero G).
  #[local] Notation comp_rel_holdsC :=
    (@comp_rel_holds F zero G gid gop gpow).
  #[local] Notation comp_witnessC :=
    (@comp_witness F zero G).
  #[local] Notation wlist := (wlist_gen comp_witnessC).
  #[local] Notation wholds := (wholds_gen comp_rel_holdsC).
  #[local] Notation comp_randC := (@comp_rand F zero G).
  #[local] Notation comp_verifyC :=
    (@comp_verify F zero one add mul sub inv G gid gop gpow Gdec).
  #[local] Notation comp_proveC :=
    (@comp_prove F zero one add mul sub opp inv G gid gop gpow).
  #[local] Notation comp_real_distributionC :=
    (@comp_real_distribution F zero one add mul sub opp inv G gid gop gpow).
  #[local] Notation comp_simulator_distributionC :=
    (@comp_simulator_distribution F zero one add mul sub opp inv G gid gop gpow).

  (* ---------------- Syntax ---------------- *)

  (* Public scalar expressions *)
  Inductive pexpr : Type :=
  | PConst (c : F)
  | PVar (x : V)
  | PAdd (a b : pexpr)
  | PMul (a b : pexpr)
  | POpp (a : pexpr).

  (* One term  base ^ (coeff · var)  of a linear equation *)
  Record term : Type := mkterm
    { t_coeff : pexpr;
      t_var : V;
      t_base : V }.

  (* One equation, in homogeneous form:
       Π base_i ^ (coeff_i · x_i)  ·  Π base_j ^ coeff_j  =  1.
     eq_rhs are the private terms; eq_off the public offsets. *)
  Record equation : Type := mkeq
    { eq_rhs : list term;
      eq_off : list (pexpr * V) }.

  (* The readable form  P = Π terms *)
  Definition simple_eq (Pn : V) (ts : list term) : equation :=
    mkeq ts (List.cons (POpp (PConst one), Pn) List.nil).

  (* Statement tree *)
  Inductive stmt : Type :=
  | SEqs (eqs : list equation)
  | SAnd (a b : stmt)
  | SOr (a b : stmt)
  | SThresh (t : nat) (l : list stmt).

  (* Structural induction with a Forall hypothesis for the children
     of a threshold. *)
  Section StmtInduction.
    Variable P : stmt -> Prop.
    Hypothesis HEqs : ∀ eqs, P (SEqs eqs).
    Hypothesis HAnd : ∀ a b, P a -> P b -> P (SAnd a b).
    Hypothesis HOr : ∀ a b, P a -> P b -> P (SOr a b).
    Hypothesis HThresh : ∀ t l, List.Forall P l -> P (SThresh t l).

    Fixpoint stmt_ind' (s : stmt) : P s :=
      match s with
      | SEqs eqs => HEqs eqs
      | SAnd a b => HAnd a b (stmt_ind' a) (stmt_ind' b)
      | SOr a b => HOr a b (stmt_ind' a) (stmt_ind' b)
      | SThresh t l =>
          HThresh t l
            ((fix go (l : list stmt) : List.Forall P l :=
                match l with
                | List.nil => @List.Forall_nil _ P
                | List.cons s' l' =>
                    @List.Forall_cons _ P s' l' (stmt_ind' s') (go l')
                end) l)
      end.
  End StmtInduction.

  Fixpoint peval (penv : V -> F) (e : pexpr) : F :=
    match e with
    | PConst c => c
    | PVar x => penv x
    | PAdd a b => peval penv a + peval penv b
    | PMul a b => peval penv a * peval penv b
    | POpp a => opp (peval penv a)
    end.

  Fixpoint nodupb (l : list V) : bool :=
    match l with
    | List.nil => true
    | List.cons x r => negb (List.existsb (veqb x) r) && nodupb r
    end.

  Fixpoint nodupb_F (l : list F) : bool :=
    match l with
    | List.nil => true
    | List.cons x r => negb (List.existsb (feqb x) r) && nodupb_F r
    end.

  (* Which children hold: a flag per child, at least t of them set *)
  Fixpoint count_true (bs : list bool) : nat :=
    match bs with
    | List.nil => 0
    | List.cons b bs' => ((if b then 1 else 0) + count_true bs')%nat
    end.

  Section Spec.

    Context {n : nat}.
    Variable privs : Vector.t V n.  (* private scalar names *)
    Variable genv : V -> G.         (* point environment *)
    Variable penv : V -> F.         (* public scalar environment *)
    Variable node : nat -> F.       (* threshold interpolation nodes *)

    (* ---------------- Semantics ---------------- *)

    Definition term_denote (wenv : V -> F) (t : term) : G :=
      (genv (t_base t)) ^ (peval penv (t_coeff t) * wenv (t_var t)).

    Definition terms_fold (wenv : V -> F) (ts : list term) : G :=
      List.fold_right (fun t acc => gop (term_denote wenv t) acc)
        gid ts.

    Definition off_denote (o : pexpr * V) : G :=
      (genv (snd o)) ^ (peval penv (fst o)).

    Definition off_fold (os : list (pexpr * V)) : G :=
      List.fold_right (fun o acc => gop (off_denote o) acc) gid os.

    Definition eq_denote (wenv : V -> F) (e : equation) : Prop :=
      gop (terms_fold wenv (eq_rhs e)) (off_fold (eq_off e)) = gid.

    (* The flagged children all hold *)
    Fixpoint stmt_denote (wenv : V -> F) (s : stmt) : Prop :=
      match s with
      | SEqs eqs => List.Forall (eq_denote wenv) eqs
      | SAnd a b => stmt_denote wenv a ∧ stmt_denote wenv b
      | SOr a b => stmt_denote wenv a ∨ stmt_denote wenv b
      | SThresh t l =>
          ∃ bs : list bool,
            List.length bs = List.length l ∧
            (t <= count_true bs)%nat ∧
            (fix flagged (l : list stmt) (bs : list bool) : Prop :=
               match l, bs with
               | List.cons s' l', List.cons b bs' =>
                   (if b then stmt_denote wenv s' else True) ∧
                   flagged l' bs'
               | _, _ => True
               end) l bs
      end.

    (* The flagged-children conjunction, as a standalone function *)
    Fixpoint flagged_denote (wenv : V -> F) (l : list stmt) (bs : list bool)
      : Prop :=
      match l, bs with
      | List.cons s' l', List.cons b bs' =>
          (if b then stmt_denote wenv s' else True) ∧
          flagged_denote wenv l' bs'
      | _, _ => True
      end.

    Lemma stmt_denote_thresh :
      ∀ (wenv : V -> F) (t : nat) (l : list stmt),
      stmt_denote wenv (SThresh t l) <->
      ∃ bs : list bool,
        List.length bs = List.length l ∧
        (t <= count_true bs)%nat ∧ flagged_denote wenv l bs.
    Proof.
      intros *; cbn.
      split; intros (bs & ha & hb & hc); exists bs; repeat split; try assumption.
      + clear ha hb. revert bs hc.
        induction l as [|s l ih]; intros [|b bs] hc; cbn in hc |- *; try exact I.
        destruct hc as (hc & hd); split; [exact hc | eapply ih; exact hd].
      + clear ha hb. revert bs hc.
        induction l as [|s l ih]; intros [|b bs] hc; cbn in hc |- *; try exact I.
        destruct hc as (hc & hd); split; [exact hc | eapply ih; exact hd].
    Qed.

    (* ---------------- Well-formedness ---------------- *)

    Definition wf_term (t : term) : bool :=
      List.existsb (veqb (t_var t)) (Vector.to_list privs).

    Definition wf_eq (e : equation) : bool :=
      List.forallb wf_term (eq_rhs e).

    Fixpoint wf_stmt (s : stmt) : bool :=
      match s with
      | SEqs eqs => List.forallb wf_eq eqs
      | SAnd a b => wf_stmt a && wf_stmt b
      | SOr a b => wf_stmt a && wf_stmt b
      | SThresh t l =>
          (fix go (l : list stmt) : bool :=
             match l with
             | List.nil => true
             | List.cons s' l' => wf_stmt s' && go l'
             end) l
      end.

    (* ---------------- Compilation ---------------- *)

    (* Column entry of a term at declared variable x: the public
       coefficient folds into the base. *)
    Definition term_col (t : term) (x : V) : G :=
      if veqb (t_var t) x
      then (genv (t_base t)) ^ (peval penv (t_coeff t))
      else gid.

    (* The matrix row of a term list: column x collects the product
       of the folded bases of all terms with variable x. *)
    Definition row_of_terms (ts : list term) : Vector.t G n :=
      Vector.map (fun x =>
        List.fold_right (fun t acc => gop (term_col t x) acc) gid ts)
        privs.

    Definition compile_eq_row (e : equation) : Vector.t G n :=
      row_of_terms (eq_rhs e).

    Definition compile_leaf (eqs : list equation) : comp_relC :=
      Leaf (List.length eqs) n
        (Vector.map compile_eq_row (Vector.of_list eqs))
        (Vector.map (fun e => ginv (off_fold (eq_off e)))
          (Vector.of_list eqs)).

    (* A statement is "pure" when it is an AND-tree of equations;
       those merge into a single Leaf so that shared private
       variables are bound by one shared witness vector. *)
    Fixpoint leaves_only (s : stmt) : option (list equation) :=
      match s with
      | SEqs eqs => Some eqs
      | SAnd a b =>
          match leaves_only a, leaves_only b with
          | Some la, Some lb => Some (List.app la lb)
          | _, _ => None
          end
      | SOr _ _ => None
      | SThresh _ _ => None
      end.

    (* The first k interpolation nodes, as a vector *)
    Fixpoint node_vec (k i : nat) : Vector.t F k :=
      match k with
      | 0 => []
      | S k' => node i :: node_vec k' (S i)
      end.

    (* Threshold nodes are valid when 0 and the k nodes are
       pairwise distinct; decided at compile time. *)
    Definition nodes_ok (k : nat) : bool :=
      nodupb_F (List.cons zero (Vector.to_list (node_vec k 0))).

    Lemma nodupb_F_sound :
      ∀ l : list F, nodupb_F l = true -> List.NoDup l.
    Proof.
      induction l as [|x l ih]; intro ha; cbn in ha.
      + constructor.
      + eapply andb_true_iff in ha.
        destruct ha as (ha & hb).
        constructor.
        ++ intro hin; eapply negb_true_iff in ha.
           assert (hc : List.existsb (feqb x) l = true).
           { eapply List.existsb_exists. exists x; split; [exact hin |].
             unfold feqb; destruct (Fdec x x); congruence. }
           congruence.
        ++ eapply ih; exact hb.
    Qed.

    (* Compile a statement; None when a threshold node is malformed
       (t > k) or its interpolation nodes collide. *)
    Fixpoint compile (s : stmt) : option comp_relC :=
      match s with
      | SEqs eqs => Some (compile_leaf eqs)
      | SAnd a b =>
          match leaves_only a, leaves_only b with
          | Some la, Some lb => Some (compile_leaf (List.app la lb))
          | _, _ =>
              match compile a, compile b with
              | Some ra, Some rb => Some (CAnd ra rb)
              | _, _ => None
              end
          end
      | SOr a b =>
          match compile a, compile b with
          | Some ra, Some rb => Some (COr ra rb)
          | _, _ => None
          end
      | SThresh t l =>
          match
            (fix go (l : list stmt) : option (list comp_relC) :=
               match l with
               | List.nil => Some List.nil
               | List.cons s' l' =>
                   match compile s', go l' with
                   | Some r, Some rs => Some (List.cons r rs)
                   | _, _ => None
                   end
               end) l
          with
          | None => None
          | Some rs =>
              match le_dec t (List.length rs),
                    Sumbool.sumbool_of_bool (nodes_ok (List.length rs))
              with
              | left Ht, left Hok =>
                  Some (CThresh t (List.length rs)
                    (node_vec (List.length rs) 0) (Vector.of_list rs)
                    (nodupb_F_sound _ Hok) Ht)
              | _, _ => None
              end
          end
      end.

    (* The children compiler, as a standalone function *)
    Fixpoint compile_list (l : list stmt) : option (list comp_relC) :=
      match l with
      | List.nil => Some List.nil
      | List.cons s' l' =>
          match compile s', compile_list l' with
          | Some r, Some rs => Some (List.cons r rs)
          | _, _ => None
          end
      end.

    (* The compiled witness vector of a DSL witness environment *)
    Definition compile_witness (wenv : V -> F) : Vector.t F n :=
      Vector.map wenv privs.


    (* ---------------- Disjunction invariant ---------------- *)

    (* All private-variable occurrences of a statement *)
    Fixpoint stmt_vars (s : stmt) : list V :=
      match s with
      | SEqs eqs =>
          List.flat_map (fun e => List.map t_var (eq_rhs e)) eqs
      | SAnd a b => List.app (stmt_vars a) (stmt_vars b)
      | SOr a b => List.app (stmt_vars a) (stmt_vars b)
      | SThresh _ l =>
          (fix go (l : list stmt) : list V :=
             match l with
             | List.nil => List.nil
             | List.cons s' l' => List.app (stmt_vars s') (go l')
             end) l
      end.

    Definition vars_of_list (l : list stmt) : list V :=
      List.flat_map stmt_vars l.

    Definition disjointb (l₁ l₂ : list V) : bool :=
      List.forallb (fun x => negb (List.existsb (veqb x) l₂)) l₁.

    (* Is the statement a pure AND-tree of equations (compiled to a
       single merged Leaf)? *)
    Definition pureb (s : stmt) : bool :=
      match leaves_only s with
      | Some _ => true
      | None => false
      end.

    (* Children of a disjunction node have pairwise disjoint
       variable sets *)
    Fixpoint pairwise_disjointb (l : list stmt) : bool :=
      match l with
      | List.nil => true
      | List.cons s' l' =>
          disjointb (stmt_vars s') (vars_of_list l') && pairwise_disjointb l'
      end.

    (*
      The disjunction-invariant checker.  A private variable shared
      between two subtrees is only bound to a single value when both
      subtrees compile into the same merged Leaf (one shared witness
      vector).  Whenever compilation keeps a CAnd node, or at an OR /
      THRESH node, the branches have independent witnesses, so the
      checker requires their variable sets to be disjoint.  An OR
      needs no such condition: only one branch's witness is ever
      used, so a variable shared between OR branches is harmless
      (∃x. P x ∨ Q x is the same as (∃x. P x) ∨ (∃x. Q x)).
    *)
    Fixpoint disj_inv (s : stmt) : bool :=
      match s with
      | SEqs _ => true
      | SAnd a b =>
          (pureb a && pureb b) ||
          (disjointb (stmt_vars a) (stmt_vars b) &&
           disj_inv a && disj_inv b)
      | SOr a b => disj_inv a && disj_inv b
      | SThresh _ l =>
          pairwise_disjointb l &&
          (fix go (l : list stmt) : bool :=
             match l with
             | List.nil => true
             | List.cons s' l' => disj_inv s' && go l'
             end) l
      end.

    (* First-match lookup: reconstruct a witness environment from a
       compiled witness vector. *)
    Fixpoint lookup (names : list V) (vals : list F) (x : V) : F :=
      match names, vals with
      | List.cons nm names', List.cons v vals' =>
          if veqb nm x then v else lookup names' vals' x
      | _, _ => zero
      end.

    (* Merge two branch environments: variables of the left branch
       read from w₁, all others from w₂. *)
    Definition combine_env (va : list V) (w₁ w₂ : V -> F) : V -> F :=
      fun x => if List.existsb (veqb x) va then w₁ x else w₂ x.

    (* The flags of a threshold witness: which children carry one *)
    Fixpoint wflags {m : nat} (v : Vector.t comp_relC m) :
      wlist v -> list bool :=
      match v as v' return wlist v' -> list bool with
      | [] => fun _ => List.nil
      | r :: v' => fun w =>
          List.cons (match fst w with Some _ => true | None => false end)
            (wflags v' (snd w))
      end.

    (* ---------------- Proofs ---------------- *)

    Section Proofs.

      Context
        {Hvec : @vector_space F (@eq F) zero one add mul sub
          div opp inv G (@eq G) gid ginv gop gpow}.
      Add Field field : (@field_theory_for_stdlib_tactic F
        eq zero one opp add mul sub inv div vector_space_field).

      Lemma veqb_refl : ∀ x : V, veqb x x = true.
      Proof.
        intro x; unfold veqb; destruct (vdec x x); congruence.
      Qed.

      Lemma veqb_eq : ∀ x y : V, veqb x y = true -> x = y.
      Proof.
        intros x y; unfold veqb; destruct (vdec x y); congruence.
      Qed.

      (* ---- leaf algebra (ported from SigmaCompiler) ---- *)

      (* row_eval of an all-identity row *)
      Lemma row_eval_map_gid :
        ∀ (m : nat) (sv : Vector.t V m) (ws : Vector.t F m),
        row_evalC (Vector.map (fun _ => gid) sv) ws = gid.
      Proof.
        induction m as [|m ihm].
        +
          intros *.
          rewrite (vector_inv_0 sv), (vector_inv_0 ws).
          reflexivity.
        +
          intros *.
          destruct (vector_inv_S sv) as (svh & svt & ha).
          destruct (vector_inv_S ws) as (wsh & wst & hb).
          subst.
          specialize (ihm svt wst).
          unfold row_eval in ihm |- *; cbn.
          rewrite vid_identity, left_identity.
          exact ihm.
      Qed.

      (* row_eval is homomorphic in pointwise products of rows *)
      Lemma row_eval_zip_gop :
        ∀ (m : nat) (r₁ r₂ : Vector.t G m) (ws : Vector.t F m),
        row_evalC (zip_with gop r₁ r₂) ws =
        gop (row_evalC r₁ ws) (row_evalC r₂ ws).
      Proof.
        induction m as [|m ihm].
        +
          intros *.
          rewrite (vector_inv_0 r₁), (vector_inv_0 r₂),
            (vector_inv_0 ws).
          unfold row_eval; cbn.
          rewrite left_identity.
          reflexivity.
        +
          intros *.
          destruct (vector_inv_S r₁) as (rh₁ & rt₁ & ha).
          destruct (vector_inv_S r₂) as (rh₂ & rt₂ & hb).
          destruct (vector_inv_S ws) as (wh & wt & hc).
          subst.
          specialize (ihm rt₁ rt₂ wt).
          unfold row_eval in ihm |- *; cbn.
          rewrite ihm, smul_distributive_vadd, gop_simp.
          reflexivity.
      Qed.

      (* pointwise gop under map splits into zip_with *)
      Lemma map_pointwise_zip :
        ∀ (A : Type) (m : nat) (v : Vector.t A m) (f g : A -> G),
        Vector.map (fun x => gop (f x) (g x)) v =
        zip_with gop (Vector.map f v) (Vector.map g v).
      Proof.
        induction m as [|m ihm].
        +
          intros *.
          rewrite (vector_inv_0 v).
          reflexivity.
        +
          intros *.
          destruct (vector_inv_S v) as (vh & vt & ha); subst.
          cbn.
          rewrite ihm.
          reflexivity.
      Qed.

      (* A term whose variable does not occur in sv contributes an
         all-identity row. *)
      Lemma term_col_absent :
        ∀ (m : nat) (sv : Vector.t V m) (ws : Vector.t F m)
          (t : term),
        List.existsb (veqb (t_var t)) (Vector.to_list sv) = false ->
        row_evalC (Vector.map (term_col t) sv) ws = gid.
      Proof.
        induction m as [|m ihm].
        +
          intros * ha.
          rewrite (vector_inv_0 sv), (vector_inv_0 ws).
          reflexivity.
        +
          intros * ha.
          destruct (vector_inv_S sv) as (svh & svt & hb).
          destruct (vector_inv_S ws) as (wsh & wst & hc).
          subst; cbn in ha.
          eapply orb_false_iff in ha.
          destruct ha as (hal & har).
          specialize (ihm svt wst t har).
          unfold term_col in ihm |- *.
          unfold row_eval in ihm |- *; cbn.
          rewrite hal.
          rewrite vid_identity, left_identity.
          exact ihm.
      Qed.

      (* One-hot row: a term with a declared variable evaluates to
         its denotation. *)
      Lemma term_col_one_hot :
        ∀ (m : nat) (sv : Vector.t V m) (wenv : V -> F)
          (t : term),
        List.existsb (veqb (t_var t)) (Vector.to_list sv) = true ->
        nodupb (Vector.to_list sv) = true ->
        row_evalC (Vector.map (term_col t) sv) (Vector.map wenv sv) =
        (genv (t_base t)) ^ (peval penv (t_coeff t) * wenv (t_var t)).
      Proof.
        induction m as [|m ihm].
        +
          intros * ha hb.
          rewrite (vector_inv_0 sv) in ha.
          cbn in ha; congruence.
        +
          intros * ha hb.
          destruct (vector_inv_S sv) as (svh & svt & hc); subst.
          cbn in ha, hb.
          eapply andb_true_iff in hb.
          destruct hb as (hbl & hbr).
          destruct (veqb (t_var t) svh) eqn:hd.
          ++
            eapply veqb_eq in hd.
            assert (he :
              List.existsb (veqb (t_var t)) (Vector.to_list svt) = false).
            rewrite hd.
            eapply negb_true_iff in hbl.
            exact hbl.
            unfold row_eval; cbn.
            unfold term_col at 1.
            rewrite hd, veqb_refl.
            pose proof (term_col_absent m svt
              (Vector.map wenv svt) t he) as hf.
            unfold row_eval in hf; cbn in hf.
            rewrite hf, right_identity.
            rewrite smul_associative_fmul.
            reflexivity.
          ++
            cbn in ha.
            specialize (ihm svt wenv t ha hbr).
            unfold row_eval in ihm |- *; cbn.
            unfold term_col at 1.
            rewrite hd.
            rewrite vid_identity, left_identity.
            exact ihm.
      Qed.

      (* The main per-equation lemma: evaluating the compiled row at
         the compiled witness is the product of term denotations. *)
      Lemma row_of_terms_correct :
        ∀ (ts : list term) (wenv : V -> F),
        List.forallb wf_term ts = true ->
        nodupb (Vector.to_list privs) = true ->
        row_evalC (row_of_terms ts) (compile_witness wenv) =
        terms_fold wenv ts.
      Proof.
        induction ts as [|t ts iht].
        +
          intros * ha hb.
          unfold row_of_terms; cbn.
          eapply row_eval_map_gid.
        +
          intros * ha hb.
          cbn in ha.
          eapply andb_true_iff in ha.
          destruct ha as (hal & har).
          unfold row_of_terms; cbn.
          rewrite map_pointwise_zip.
          rewrite row_eval_zip_gop.
          unfold compile_witness.
          rewrite term_col_one_hot;
          [| exact hal | exact hb].
          unfold row_of_terms, terms_fold in iht.
          unfold compile_witness in iht.
          unfold terms_fold; cbn.
          rewrite iht; [| exact har | exact hb].
          reflexivity.
      Qed.


      Lemma gop_eq_gid_iff : ∀ (a b : G),
        gop a b = gid <-> a = ginv b.
      Proof.
        intros *; split; intro ha.
        +
          eapply f_equal with (f := fun z => gop z (ginv b)) in ha.
          rewrite <-associative, right_inverse, right_identity,
            left_identity in ha.
          exact ha.
        +
          rewrite ha.
          rewrite commutative, right_inverse.
          reflexivity.
      Qed.

      (* The readable  P = Π terms  reading of simple_eq *)
      Lemma simple_eq_denote :
        ∀ (Pn : V) (ts : list term) (wenv : V -> F),
        eq_denote wenv (simple_eq Pn ts) <->
        genv Pn = terms_fold wenv ts.
      Proof.
        intros *.
        unfold eq_denote, simple_eq; cbn.
        unfold off_fold, off_denote; cbn.
        rewrite right_identity.
        assert (ha : (genv Pn) ^ (opp one) = ginv (genv Pn)).
        rewrite <-connection_between_vopp_and_fopp.
        rewrite field_one. reflexivity.
        rewrite ha.
        rewrite gop_eq_gid_iff.
        rewrite group_inv_inv.
        split; intro hb; symmetry; exact hb.
      Qed.

      (* Leaf-level equivalence: the compiled relation holds of the
         compiled witness iff the denotation holds. *)
      Lemma compile_leaf_correct :
        ∀ (eqs : list equation) (wenv : V -> F),
        List.forallb wf_eq eqs = true ->
        nodupb (Vector.to_list privs) = true ->
        (comp_rel_holdsC (compile_leaf eqs) (compile_witness wenv) <->
         List.Forall (eq_denote wenv) eqs).
      Proof.
        induction eqs as [|e eqs ihe].
        +
          intros * ha hb.
          split; intro hc.
          constructor.
          reflexivity.
        +
          intros * ha hb.
          cbn in ha.
          eapply andb_true_iff in ha.
          destruct ha as (hae & har).
          specialize (ihe wenv har hb).
          split; intro hc.
          ++
            cbn in hc.
            pose proof (f_equal (@Vector.hd G _) hc) as hh;
            cbn in hh.
            pose proof (f_equal (@Vector.tl G _) hc) as ht;
            cbn in ht.
            constructor.
            +++
              unfold eq_denote.
              eapply gop_eq_gid_iff.
              rewrite <-(row_of_terms_correct (eq_rhs e) wenv hae hb).
              exact hh.
            +++
              eapply ihe.
              exact ht.
          ++
            inversion hc as [| ? ? hde hrest]; subst.
            cbn.
            f_equal.
            +++
              unfold compile_eq_row.
              rewrite row_of_terms_correct;
              [| exact hae | exact hb].
              eapply gop_eq_gid_iff.
              exact hde.
            +++
              eapply ihe.
              exact hrest.
      Qed.

      (* Pure AND-subtrees denote the conjunction of their collected
         equations. *)
      Lemma leaves_only_denote :
        ∀ (s : stmt) (eqs : list equation) (wenv : V -> F),
        leaves_only s = Some eqs ->
        (stmt_denote wenv s <-> List.Forall (eq_denote wenv) eqs).
      Proof.
        induction s as [leqs | a b iha ihb | a b iha ihb | t l ihl]
          using stmt_ind'.
        +
          intros * ha; cbn in ha.
          injection ha as ha; subst.
          cbn; reflexivity.
        +
          intros * ha; cbn in ha.
          destruct (leaves_only a) as [la|] eqn:hb;
          [| congruence].
          destruct (leaves_only b) as [lb|] eqn:hc;
          [| congruence].
          injection ha as ha; subst.
          cbn.
          rewrite (iha la wenv eq_refl), (ihb lb wenv eq_refl).
          rewrite List.Forall_app.
          reflexivity.
        +
          intros * ha; cbn in ha; congruence.
        +
          intros * ha; cbn in ha; congruence.
      Qed.

      Lemma leaves_only_wf :
        ∀ (s : stmt) (eqs : list equation),
        leaves_only s = Some eqs ->
        wf_stmt s = true ->
        List.forallb wf_eq eqs = true.
      Proof.
        induction s as [leqs | a b iha ihb | a b iha ihb | t l ihl]
          using stmt_ind'.
        +
          intros * ha hb; cbn in ha, hb.
          injection ha as ha; subst.
          exact hb.
        +
          intros * ha hb; cbn in ha, hb.
          eapply andb_true_iff in hb.
          destruct hb as (hbl & hbr).
          destruct (leaves_only a) as [la|] eqn:hc;
          [| congruence].
          destruct (leaves_only b) as [lb|] eqn:hd;
          [| congruence].
          injection ha as ha; subst.
          rewrite List.forallb_app.
          eapply andb_true_iff; split.
          eapply iha; [reflexivity | exact hbl].
          eapply ihb; [reflexivity | exact hbr].
        +
          intros * ha; cbn in ha; congruence.
        +
          intros * ha; cbn in ha; congruence.
      Qed.

      (* The children compiler inside `compile` is compile_list *)
      Lemma compile_thresh :
        ∀ (t : nat) (l : list stmt),
        compile (SThresh t l) =
        match compile_list l with
        | None => None
        | Some rs =>
            match le_dec t (List.length rs),
                  Sumbool.sumbool_of_bool (nodes_ok (List.length rs))
            with
            | left Ht, left Hok =>
                Some (CThresh t (List.length rs)
                  (node_vec (List.length rs) 0) (Vector.of_list rs)
                  (nodupb_F_sound _ Hok) Ht)
            | _, _ => None
            end
        end.
      Proof.
        intros *; cbn.
        assert (ha : ∀ l', (fix go (l : list stmt) : option (list comp_relC) :=
            match l with
            | List.nil => Some List.nil
            | List.cons s' l' =>
                match compile s', go l' with
                | Some r, Some rs => Some (List.cons r rs)
                | _, _ => None
                end
            end) l' = compile_list l').
        { induction l' as [|s' l' ih]; cbn; [reflexivity |].
          rewrite ih; reflexivity. }
        rewrite ha; reflexivity.
      Qed.

      Lemma wf_stmt_thresh :
        ∀ (t : nat) (l : list stmt),
        wf_stmt (SThresh t l) = true -> List.Forall (fun s => wf_stmt s = true) l.
      Proof.
        intros t l; cbn.
        induction l as [|s l ih]; intro ha; cbn in ha.
        + constructor.
        + eapply andb_true_iff in ha; destruct ha as (ha & hb).
          constructor; [exact ha | eapply ih; exact hb].
      Qed.

      (* A threshold witness from the flagged children *)
      Lemma thresh_witness :
        ∀ (l : list stmt) (rs : list comp_relC) (bs : list bool) (wenv : V -> F),
        List.Forall (fun s => ∀ r, wf_stmt s = true -> compile s = Some r ->
          stmt_denote wenv s -> ∃ w, comp_rel_holdsC r w) l ->
        List.Forall (fun s => wf_stmt s = true) l ->
        compile_list l = Some rs ->
        List.length bs = List.length l ->
        flagged_denote wenv l bs ->
        ∃ w : wlist (Vector.of_list rs),
          count_true bs = wcount (Vector.of_list rs) w ∧
          wholds (Vector.of_list rs) w.
      Proof.
        induction l as [|s l ih]; intros rs bs wenv hall hwf hc hlen hfl.
        +
          cbn in hc.
          injection hc as hc; subst.
          destruct bs; [| cbn in hlen; lia].
          exists tt; cbn; split; [reflexivity | exact I].
        +
          cbn in hc.
          destruct (compile s) as [r |] eqn:hr; [| congruence].
          destruct (compile_list l) as [rs' |] eqn:hrs; [| congruence].
          injection hc as hc; subst.
          destruct bs as [| b bs]; [cbn in hlen; lia |].
          cbn in hlen, hfl.
          destruct hfl as (hs & hfl).
          inversion hall as [| ? ? hs' hall']; subst.
          inversion hwf as [| ? ? hwfs hwf']; subst.
          destruct (ih rs' bs wenv hall' hwf' eq_refl ltac:(lia) hfl)
            as (w' & hcount & hw').
          destruct b.
          ++
            destruct (hs' r hwfs hr hs) as (x & hx).
            exists (Some x, w'); cbn.
            split; [rewrite hcount; reflexivity | split; [exact hx | exact hw']].
          ++
            exists (None, w'); cbn.
            split; [rewrite hcount; reflexivity | split; [exact I | exact hw']].
      Qed.

      (* Main theorem (completeness direction): a denotation proof
         yields a witness for the compiled relation. *)
      Theorem compile_stmt_sound :
        ∀ (s : stmt) (r : comp_relC) (wenv : V -> F),
        wf_stmt s = true ->
        nodupb (Vector.to_list privs) = true ->
        compile s = Some r ->
        stmt_denote wenv s ->
        ∃ (w : comp_witnessC r), comp_rel_holdsC r w.
      Proof.
        induction s as [leqs | a b iha ihb | a b iha ihb | t l ihl]
          using stmt_ind'.
        +
          intros * ha hb hc hd; cbn in ha, hc, hd.
          injection hc as hc; subst.
          exists (compile_witness wenv).
          eapply compile_leaf_correct; assumption.
        +
          intros * ha hb hc hd; cbn in ha, hc, hd.
          eapply andb_true_iff in ha; destruct ha as (hwa & hwb).
          destruct hd as (hda & hdb).
          destruct (leaves_only a) as [la |] eqn:hla;
          [destruct (leaves_only b) as [lb |] eqn:hlb |].
          ++
            injection hc as hc; subst.
            exists (compile_witness wenv).
            eapply compile_leaf_correct.
            +++
              rewrite List.forallb_app; eapply andb_true_iff; split;
              eapply leaves_only_wf; eassumption.
            +++
              exact hb.
            +++
              eapply List.Forall_app; split;
              eapply leaves_only_denote; eassumption.
          ++
            destruct (compile a) as [ra |] eqn:hra; [| congruence].
            destruct (compile b) as [rb |] eqn:hrb; [| congruence].
            injection hc as hc; subst.
            destruct (iha ra wenv hwa hb eq_refl hda) as (wa & hwa').
            destruct (ihb rb wenv hwb hb eq_refl hdb) as (wb & hwb').
            exists (wa, wb); cbn; split; assumption.
          ++
            destruct (compile a) as [ra |] eqn:hra; [| congruence].
            destruct (compile b) as [rb |] eqn:hrb; [| congruence].
            injection hc as hc; subst.
            destruct (iha ra wenv hwa hb eq_refl hda) as (wa & hwa').
            destruct (ihb rb wenv hwb hb eq_refl hdb) as (wb & hwb').
            exists (wa, wb); cbn; split; assumption.
        +
          intros * ha hb hc hd; cbn in ha, hc, hd.
          eapply andb_true_iff in ha; destruct ha as (hwa & hwb).
          destruct (compile a) as [ra |] eqn:hra; [| congruence].
          destruct (compile b) as [rb |] eqn:hrb; [| congruence].
          injection hc as hc; subst.
          destruct hd as [hda | hdb].
          ++
            destruct (iha ra wenv hwa hb eq_refl hda) as (wa & hwa').
            exists (inl wa); cbn; exact hwa'.
          ++
            destruct (ihb rb wenv hwb hb eq_refl hdb) as (wb & hwb').
            exists (inr wb); cbn; exact hwb'.
        +
          intros * ha hb hc hd.
          rewrite compile_thresh in hc.
          eapply wf_stmt_thresh in ha.
          eapply stmt_denote_thresh in hd.
          destruct hd as (bs & hlen & hcnt & hfl).
          destruct (compile_list l) as [rs |] eqn:hrs; [| congruence].
          destruct (le_dec t (List.length rs)) as [Ht |]; [| congruence].
          destruct (Sumbool.sumbool_of_bool (nodes_ok (List.length rs)))
            as [Hok |]; [| congruence].
          injection hc as hc; subst.
          destruct (thresh_witness l rs bs wenv) as (w & hw & hw');
          try assumption.
          ++
            eapply List.Forall_impl; [| exact ihl].
            intros s hs r hwf hcs hds; eapply hs; eassumption.
          ++
            exists w; cbn; split; [lia | exact hw'].
      Qed.

      (* ---- protocol-level corollaries ---- *)

      (* A true statement compiles to a protocol the prover can
         always make the verifier accept. *)
      Corollary compile_protocol_completeness :
        ∀ (s : stmt) (r : comp_relC) (wenv : V -> F),
        wf_stmt s = true ->
        nodupb (Vector.to_list privs) = true ->
        compile s = Some r ->
        stmt_denote wenv s ->
        ∃ (w : comp_witnessC r),
          ∀ (rnd : comp_randC r) (c : F),
          comp_verifyC r c (comp_proveC r w rnd c) = true.
      Proof.
        intros * ha hb hc hd.
        destruct (compile_stmt_sound s r wenv ha hb hc hd) as (w & hw).
        exists w; intros *.
        exact (@comp_completeness F zero one add mul sub div opp inv Fdec
          G gid ginv gop gpow Gdec Hvec r w rnd c hw).
      Qed.

      (* The compiled protocol is zero-knowledge: for a true
         statement, the real and simulated transcript distributions
         are permutations of each other. *)
      Corollary compile_protocol_zkp :
        ∀ (s : stmt) (r : comp_relC) (wenv : V -> F)
          (lf : list F) (Hlfn : lf <> List.nil) (c : F),
        wf_stmt s = true ->
        nodupb (Vector.to_list privs) = true ->
        compile s = Some r ->
        stmt_denote wenv s ->
        List.NoDup lf -> (∀ x : F, List.In x lf) ->
        ∃ (w : comp_witnessC r),
          Permutation (comp_real_distributionC lf Hlfn r w c)
                      (comp_simulator_distributionC lf Hlfn r c).
      Proof.
        intros * ha hb hc hd hnd hin.
        destruct (compile_stmt_sound s r wenv ha hb hc hd) as (w & hw).
        exists w.
        exact (@comp_distribution_perm F zero one add mul sub div opp inv Fdec
          G gid ginv gop gpow Hvec r lf Hlfn w c hnd hin hw).
      Qed.


      (* ---------------- Soundness reflection ---------------- *)

      Lemma in_vars_existsb :
        ∀ (l : list V) (x : V),
        List.In x l -> List.existsb (veqb x) l = true.
      Proof.
        intros * ha.
        eapply List.existsb_exists.
        exists x.
        split. exact ha. eapply veqb_refl.
      Qed.

      Lemma disjointb_existsb :
        ∀ (l₁ l₂ : list V) (x : V),
        disjointb l₁ l₂ = true ->
        List.In x l₂ ->
        List.existsb (veqb x) l₁ = false.
      Proof.
        intros * ha hb.
        destruct (List.existsb (veqb x) l₁) eqn:hc;
        [| reflexivity].
        eapply List.existsb_exists in hc.
        destruct hc as (y & hy & hxy).
        eapply veqb_eq in hxy; subst.
        unfold disjointb in ha.
        pose proof (proj1 (List.forallb_forall _ _) ha y hy) as hd.
        eapply negb_true_iff in hd.
        pose proof (in_vars_existsb _ _ hb) as he.
        congruence.
      Qed.

      Lemma lookup_skip :
        ∀ (m : nat) (sv : Vector.t V m) (names : list V)
          (vals : list F) (nm : V) (v : F),
        List.existsb (veqb nm) (Vector.to_list sv) = false ->
        Vector.map
          (fun x => if veqb nm x then v else lookup names vals x) sv =
        Vector.map (lookup names vals) sv.
      Proof.
        induction m as [|m ihm].
        +
          intros * ha.
          rewrite (vector_inv_0 sv).
          reflexivity.
        +
          intros * ha.
          destruct (vector_inv_S sv) as (svh & svt & hb); subst.
          cbn in ha.
          eapply orb_false_iff in ha.
          destruct ha as (hal & har).
          cbn.
          rewrite hal.
          f_equal.
          eapply ihm.
          exact har.
      Qed.

      (* Round trip: mapping the reconstructed environment over the
         declarations recovers the witness vector. *)
      Lemma map_lookup_gen :
        ∀ (m : nat) (sv : Vector.t V m) (ws : Vector.t F m),
        nodupb (Vector.to_list sv) = true ->
        Vector.map (lookup (Vector.to_list sv) (Vector.to_list ws)) sv
          = ws.
      Proof.
        induction m as [|m ihm].
        +
          intros * ha.
          rewrite (vector_inv_0 sv), (vector_inv_0 ws).
          reflexivity.
        +
          intros * ha.
          destruct (vector_inv_S sv) as (svh & svt & hb).
          destruct (vector_inv_S ws) as (wh & wt & hc).
          subst.
          cbn in ha.
          eapply andb_true_iff in ha.
          destruct ha as (hal & har).
          eapply negb_true_iff in hal.
          cbn.
          rewrite veqb_refl.
          f_equal.
          rewrite lookup_skip.
          eapply ihm.
          exact har.
          exact hal.
      Qed.

      (* Frame lemmas: denotations depend only on the values of the
         variables occurring in the statement. *)
      Lemma term_fold_ext :
        ∀ (ts : list term) (w₁ w₂ : V -> F),
        (∀ x, List.In x (List.map t_var ts) -> w₁ x = w₂ x) ->
        List.fold_right (fun t acc => gop (term_denote w₁ t) acc)
          gid ts =
        List.fold_right (fun t acc => gop (term_denote w₂ t) acc)
          gid ts.
      Proof.
        induction ts as [|t ts iht].
        +
          intros; reflexivity.
        +
          intros * ha.
          cbn.
          f_equal.
          ++
            unfold term_denote.
            rewrite (ha (t_var t) (or_introl eq_refl)).
            reflexivity.
          ++
            eapply iht.
            intros x hx.
            eapply ha.
            right; exact hx.
      Qed.

      Lemma eq_denote_ext :
        ∀ (e : equation) (w₁ w₂ : V -> F),
        (∀ x, List.In x (List.map t_var (eq_rhs e)) -> w₁ x = w₂ x) ->
        eq_denote w₁ e -> eq_denote w₂ e.
      Proof.
        intros * ha hb.
        unfold eq_denote, terms_fold in hb |- *.
        rewrite <-(term_fold_ext (eq_rhs e) w₁ w₂ ha).
        exact hb.
      Qed.

      Lemma eqs_denote_ext :
        ∀ (eqs : list equation) (w₁ w₂ : V -> F),
        (∀ x, List.In x (List.flat_map
          (fun e => List.map t_var (eq_rhs e)) eqs) -> w₁ x = w₂ x) ->
        List.Forall (eq_denote w₁) eqs ->
        List.Forall (eq_denote w₂) eqs.
      Proof.
        induction eqs as [|e eqs ihe].
        +
          intros; constructor.
        +
          intros * ha hb.
          inversion hb as [| ? ? hbe hbr]; subst.
          constructor.
          ++
            eapply eq_denote_ext; [| exact hbe].
            intros x hx.
            eapply ha; cbn.
            eapply List.in_or_app.
            left; exact hx.
          ++
            eapply ihe; [| exact hbr].
            intros x hx.
            eapply ha; cbn.
            eapply List.in_or_app.
            right; exact hx.
      Qed.

      (* The variables of a threshold node are those of its children *)
      Lemma stmt_vars_thresh :
        ∀ (t : nat) (l : list stmt), stmt_vars (SThresh t l) = vars_of_list l.
      Proof.
        intros t l; cbn; unfold vars_of_list.
        induction l as [|s l ih]; cbn; [reflexivity |].
        rewrite ih; reflexivity.
      Qed.

      Lemma disj_inv_thresh :
        ∀ (t : nat) (l : list stmt),
        disj_inv (SThresh t l) = true ->
        pairwise_disjointb l = true ∧ List.Forall (fun s => disj_inv s = true) l.
      Proof.
        intros t l ha; cbn in ha.
        eapply andb_true_iff in ha; destruct ha as (ha & hb).
        split; [exact ha |].
        clear ha.
        induction l as [|s l ih]; cbn in hb.
        + constructor.
        + eapply andb_true_iff in hb; destruct hb as (hb & hc).
          constructor; [exact hb | eapply ih; exact hc].
      Qed.

      Lemma stmt_denote_ext :
        ∀ (s : stmt) (w₁ w₂ : V -> F),
        (∀ x, List.In x (stmt_vars s) -> w₁ x = w₂ x) ->
        stmt_denote w₁ s -> stmt_denote w₂ s.
      Proof.
        induction s as [eqs | a b iha ihb | a b iha ihb | t l ihl]
          using stmt_ind'.
        +
          intros * ha hb; cbn in *.
          eapply eqs_denote_ext; [exact ha | exact hb].
        +
          intros * ha hb; cbn in *.
          destruct hb as (hbl & hbr).
          split.
          ++
            eapply iha; [| exact hbl].
            intros x hx. eapply ha, List.in_or_app. left; exact hx.
          ++
            eapply ihb; [| exact hbr].
            intros x hx. eapply ha, List.in_or_app. right; exact hx.
        +
          intros * ha hb; cbn in *.
          destruct hb as [hb | hb].
          ++
            left. eapply iha; [| exact hb].
            intros x hx. eapply ha, List.in_or_app. left; exact hx.
          ++
            right. eapply ihb; [| exact hb].
            intros x hx. eapply ha, List.in_or_app. right; exact hx.
        +
          intros * ha hb.
          rewrite stmt_vars_thresh in ha.
          eapply stmt_denote_thresh in hb.
          eapply stmt_denote_thresh.
          destruct hb as (bs & hlen & hcnt & hfl).
          exists bs; split; [exact hlen | split; [exact hcnt |]].
          clear hlen hcnt.
          revert bs hfl.
          induction l as [|s l ih]; intros [|b bs] hfl; cbn in hfl |- *;
          try exact I.
          inversion ihl as [| ? ? hs hl]; subst.
          destruct hfl as (hfs & hfl).
          split.
          ++
            destruct b; [| exact I].
            eapply hs; [| exact hfs].
            intros x hx. eapply ha. unfold vars_of_list; cbn.
            eapply List.in_or_app; left; exact hx.
          ++
            eapply ih; [exact hl | | exact hfl].
            intros x hx. eapply ha. unfold vars_of_list in hx |- *; cbn.
            eapply List.in_or_app; right; exact hx.
      Qed.

      Lemma flagged_denote_ext :
        ∀ (l : list stmt) (bs : list bool) (w₁ w₂ : V -> F),
        (∀ x, List.In x (vars_of_list l) -> w₁ x = w₂ x) ->
        flagged_denote w₁ l bs -> flagged_denote w₂ l bs.
      Proof.
        induction l as [|s l ih]; intros [|b bs] w₁ w₂ ha hfl;
        cbn in hfl |- *; try exact I.
        destruct hfl as (hfs & hfl).
        split.
        +
          destruct b; [| exact I].
          eapply stmt_denote_ext; [| exact hfs].
          intros x hx. eapply ha. unfold vars_of_list; cbn.
          eapply List.in_or_app; left; exact hx.
        +
          eapply ih; [| exact hfl].
          intros x hx. eapply ha. unfold vars_of_list in hx |- *; cbn.
          eapply List.in_or_app; right; exact hx.
      Qed.

      (* Two statements with disjoint variables that hold in their
         own environments hold together in the merged one. *)
      Lemma combine_env_denote :
        ∀ (a b : stmt) (wa wb : V -> F),
        disjointb (stmt_vars a) (stmt_vars b) = true ->
        stmt_denote wa a -> stmt_denote wb b ->
        stmt_denote (combine_env (stmt_vars a) wa wb) a ∧
        stmt_denote (combine_env (stmt_vars a) wa wb) b.
      Proof.
        intros * hdisj ha hb.
        split.
        +
          eapply stmt_denote_ext; [| exact ha].
          intros x hx.
          unfold combine_env.
          rewrite (in_vars_existsb _ _ hx).
          reflexivity.
        +
          eapply stmt_denote_ext; [| exact hb].
          intros x hx.
          unfold combine_env.
          rewrite (disjointb_existsb _ _ _ hdisj hx).
          reflexivity.
      Qed.

      Lemma wflags_count :
        ∀ (m : nat) (v : Vector.t comp_relC m) (w : wlist v),
        count_true (wflags v w) = wcount v w.
      Proof.
        induction v as [|r m v ih]; intros w; cbn.
        + reflexivity.
        + destruct (fst w); cbn; rewrite ih; reflexivity.
      Qed.

      Lemma wflags_length :
        ∀ (m : nat) (v : Vector.t comp_relC m) (w : wlist v),
        List.length (wflags v w) = m.
      Proof.
        induction v as [|r m v ih]; intros w; cbn.
        + reflexivity.
        + rewrite ih; reflexivity.
      Qed.

      (* Reflection for the children of a threshold: the children
         carrying a witness hold in one merged environment. *)
      Lemma thresh_reflect :
        ∀ (l : list stmt) (rs : list comp_relC) (w : wlist (Vector.of_list rs)),
        List.Forall (fun s => ∀ r, wf_stmt s = true -> disj_inv s = true ->
          compile s = Some r ->
          ∀ w : comp_witnessC r, comp_rel_holdsC r w ->
          ∃ wenv, stmt_denote wenv s) l ->
        List.Forall (fun s => wf_stmt s = true) l ->
        List.Forall (fun s => disj_inv s = true) l ->
        pairwise_disjointb l = true ->
        compile_list l = Some rs ->
        wholds (Vector.of_list rs) w ->
        ∃ wenv, flagged_denote wenv l (wflags (Vector.of_list rs) w).
      Proof.
        induction l as [|s l ih]; intros rs w hall hwf hinv hpair hc hw.
        +
          cbn in hc.
          injection hc as hc; subst.
          exists (fun _ => zero); cbn; exact I.
        +
          cbn in hc.
          destruct (compile s) as [r |] eqn:hr; [| congruence].
          destruct (compile_list l) as [rs' |] eqn:hrs; [| congruence].
          injection hc as hc; subst.
          cbn in hpair.
          eapply andb_true_iff in hpair; destruct hpair as (hdisj & hpair).
          inversion hall as [| ? ? hs hall']; subst.
          inversion hwf as [| ? ? hwfs hwf']; subst.
          inversion hinv as [| ? ? hinvs hinv']; subst.
          destruct w as (ow & w'); cbn in hw.
          destruct hw as (hws & hw').
          destruct (ih rs' w' hall' hwf' hinv' hpair eq_refl hw')
            as (wenv' & hfl).
          destruct ow as [x |].
          ++
            destruct (hs r hwfs hinvs hr x hws) as (wenv_s & hd).
            exists (combine_env (stmt_vars s) wenv_s wenv'); cbn.
            split.
            +++
              eapply stmt_denote_ext; [| exact hd].
              intros y hy. unfold combine_env.
              rewrite (in_vars_existsb _ _ hy). reflexivity.
            +++
              eapply flagged_denote_ext; [| exact hfl].
              intros y hy. unfold combine_env.
              rewrite (disjointb_existsb _ _ _ hdisj hy). reflexivity.
          ++
            exists wenv'; cbn.
            split; [exact I | exact hfl].
      Qed.

      Lemma compile_list_length :
        ∀ (l : list stmt) (rs : list comp_relC),
        compile_list l = Some rs -> List.length rs = List.length l.
      Proof.
        induction l as [|s l ih]; intros rs hc; cbn in hc.
        + injection hc as hc; subst; reflexivity.
        + destruct (compile s); [| congruence].
          destruct (compile_list l) as [rs' |] eqn:hrs; [| congruence].
          injection hc as hc; subst; cbn.
          rewrite (ih rs' eq_refl); reflexivity.
      Qed.

      (* An unmerged AND has independent branch witnesses; under
         disjointness their environments combine. *)
      Lemma and_reflect_unmerged :
        ∀ (a b : stmt) (ra rb : comp_relC),
        (∀ w : comp_witnessC ra, comp_rel_holdsC ra w ->
          ∃ wenv, stmt_denote wenv a) ->
        (∀ w : comp_witnessC rb, comp_rel_holdsC rb w ->
          ∃ wenv, stmt_denote wenv b) ->
        disjointb (stmt_vars a) (stmt_vars b) = true ->
        ∀ (w : comp_witnessC (CAnd ra rb)), comp_rel_holdsC (CAnd ra rb) w ->
        ∃ wenv, stmt_denote wenv (SAnd a b).
      Proof.
        intros * iha ihb hdisj w hw.
        destruct w as (wa & wb); cbn in hw.
        destruct hw as (hwa & hwb).
        destruct (iha wa hwa) as (wea & hwea).
        destruct (ihb wb hwb) as (web & hweb).
        exists (combine_env (stmt_vars a) wea web); cbn.
        eapply combine_env_denote; assumption.
      Qed.

      (* Main theorem (soundness reflection): under the disjunction
         invariant, a witness for the compiled relation yields a DSL
         witness environment satisfying the denotation. *)
      Theorem compile_stmt_reflect :
        ∀ (s : stmt) (r : comp_relC),
        wf_stmt s = true ->
        nodupb (Vector.to_list privs) = true ->
        disj_inv s = true ->
        compile s = Some r ->
        ∀ (w : comp_witnessC r),
        comp_rel_holdsC r w ->
        ∃ (wenv : V -> F), stmt_denote wenv s.
      Proof.
        induction s as [eqs | a b iha ihb | a b iha ihb | t l ihl]
          using stmt_ind'.
        +
          intros r ha hb hinv hc w hw; cbn in ha, hc.
          injection hc as hc; subst.
          exists (lookup (Vector.to_list privs) (Vector.to_list w)); cbn.
          eapply compile_leaf_correct; [exact ha | exact hb |].
          unfold compile_witness.
          rewrite map_lookup_gen; [exact hw | exact hb].
        +
          intros r ha hb hinv hc; cbn in ha, hc, hinv.
          eapply andb_true_iff in ha; destruct ha as (hal & har).
          unfold pureb in hinv.
          destruct (leaves_only a) as [la |] eqn:hd;
          destruct (leaves_only b) as [lb |] eqn:he.
          ++
            (* both pure: one merged Leaf, shared witness vector *)
            injection hc as hc; subst.
            intros w hw.
            exists (lookup (Vector.to_list privs) (Vector.to_list w)).
            assert (hf : List.Forall
              (eq_denote (lookup (Vector.to_list privs) (Vector.to_list w)))
              (List.app la lb)).
            { eapply compile_leaf_correct; [| exact hb |].
              - rewrite List.forallb_app; eapply andb_true_iff; split;
                eapply leaves_only_wf; eassumption.
              - unfold compile_witness.
                rewrite map_lookup_gen; [exact hw | exact hb]. }
            eapply List.Forall_app in hf; destruct hf as (hfl & hfr).
            cbn; split.
            - eapply (leaves_only_denote a la _ hd); exact hfl.
            - eapply (leaves_only_denote b lb _ he); exact hfr.
          ++
            (* unmerged: independent witnesses, disjointness *)
            cbn in hinv.
            eapply andb_true_iff in hinv; destruct hinv as (hinv & hinvb).
            eapply andb_true_iff in hinv; destruct hinv as (hdisj & hinva).
            destruct (compile a) as [ra |] eqn:hra; [| congruence].
            destruct (compile b) as [rb |] eqn:hrb; [| congruence].
            injection hc as hc; subst.
            eapply and_reflect_unmerged; [| | exact hdisj].
            - intros wa hwa; eapply (iha ra hal hb hinva eq_refl wa hwa).
            - intros wb hwb; eapply (ihb rb har hb hinvb eq_refl wb hwb).
          ++
            cbn in hinv.
            eapply andb_true_iff in hinv; destruct hinv as (hinv & hinvb).
            eapply andb_true_iff in hinv; destruct hinv as (hdisj & hinva).
            destruct (compile a) as [ra |] eqn:hra; [| congruence].
            destruct (compile b) as [rb |] eqn:hrb; [| congruence].
            injection hc as hc; subst.
            eapply and_reflect_unmerged; [| | exact hdisj].
            - intros wa hwa; eapply (iha ra hal hb hinva eq_refl wa hwa).
            - intros wb hwb; eapply (ihb rb har hb hinvb eq_refl wb hwb).
          ++
            cbn in hinv.
            eapply andb_true_iff in hinv; destruct hinv as (hinv & hinvb).
            eapply andb_true_iff in hinv; destruct hinv as (hdisj & hinva).
            destruct (compile a) as [ra |] eqn:hra; [| congruence].
            destruct (compile b) as [rb |] eqn:hrb; [| congruence].
            injection hc as hc; subst.
            eapply and_reflect_unmerged; [| | exact hdisj].
            - intros wa hwa; eapply (iha ra hal hb hinva eq_refl wa hwa).
            - intros wb hwb; eapply (ihb rb har hb hinvb eq_refl wb hwb).
        +
          intros r ha hb hinv hc; cbn in ha, hc, hinv.
          eapply andb_true_iff in ha; destruct ha as (hal & har).
          eapply andb_true_iff in hinv; destruct hinv as (hinva & hinvb).
          destruct (compile a) as [ra |] eqn:hra; [| congruence].
          destruct (compile b) as [rb |] eqn:hrb; [| congruence].
          injection hc as hc; subst.
          intros w hw.
          destruct w as [wa | wb].
          ++
            destruct (iha ra hal hb hinva eq_refl wa hw) as (wea & hwea).
            exists wea; left; exact hwea.
          ++
            destruct (ihb rb har hb hinvb eq_refl wb hw) as (web & hweb).
            exists web; right; exact hweb.
        +
          intros r ha hb hinv hc.
          rewrite compile_thresh in hc.
          eapply wf_stmt_thresh in ha.
          eapply disj_inv_thresh in hinv; destruct hinv as (hpair & hinvl).
          destruct (compile_list l) as [rs |] eqn:hrs; [| congruence].
          destruct (le_dec t (List.length rs)) as [Ht |]; [| congruence].
          destruct (Sumbool.sumbool_of_bool (nodes_ok (List.length rs)))
            as [Hok |]; [| congruence].
          injection hc as hc; subst.
          intros w hw; cbn in hw.
          destruct hw as (hcount & hholds).
          destruct (thresh_reflect l rs w) as (wenv & hfl); try assumption.
          ++
            eapply List.Forall_impl; [| exact ihl].
            intros s hs r hwf hinvs hcs; eapply hs; eassumption.
          ++
            exists wenv.
            eapply stmt_denote_thresh.
            exists (wflags (Vector.of_list rs) w).
            split; [| split].
            - rewrite wflags_length. eapply compile_list_length; exact hrs.
            - rewrite wflags_count; exact hcount.
            - exact hfl.
      Qed.

      (* DSL-level special soundness: two accepting transcripts with
         the same announcements and different challenges imply the
         *statement itself* has a witness environment. *)
      Corollary compile_protocol_soundness :
        ∀ (s : stmt) (r : comp_relC) (c c' : F)
          (tr tr' : @comp_transcript F zero G r),
        wf_stmt s = true ->
        nodupb (Vector.to_list privs) = true ->
        disj_inv s = true ->
        compile s = Some r ->
        c <> c' ->
        @comp_same_announcement F zero G r tr tr' ->
        comp_verifyC r c tr = true ->
        comp_verifyC r c' tr' = true ->
        ∃ (wenv : V -> F), stmt_denote wenv s.
      Proof.
        intros * ha hb hc hr hd he hf hg.
        destruct (@comp_special_soundness F zero one add mul sub div
          opp inv Fdec G gid ginv gop gpow Gdec Hvec
          r c c' tr tr' hd he hf hg) as (w & hw).
        eapply compile_stmt_reflect; eassumption.
      Qed.

    End Proofs.

  End Spec.

End Dsl.
