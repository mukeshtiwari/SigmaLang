(* Running the *verified* verifier on the CFRG vectors.
 *
 * The extracted verifier is parametric in the field and the group: it
 * takes zero, one, addition, multiplication, subtraction, inversion,
 * the group identity, the group operation, exponentiation and an
 * equality test as arguments.  Nothing about it is tied to the
 * election group it was first instantiated at.  So the composition
 * logic, the Fiat-Shamir wiring and the announcement flattening can
 * all be run on P-256 without a curve inside Rocq.
 *
 * Be exact about what that does and does not give.  The code being run
 * is the verified code.  The theorems about it are conditional on the
 * group satisfying the vector-space axioms, and we have not proven
 * that our P-256 does.  So this is verified code on an unverified
 * instantiation: strictly better than a hand-written verifier, and
 * strictly weaker than the Helios case, where the group carries its
 * proofs.  Closing that last gap needs a curve in Rocq, which is a
 * separate undertaking. *)

module B = Big_int_Z
open Helioslib

(* ---------- scalars modulo the group order ---------- *)

let n = P256.order
let fmod x = let r = B.mod_big_int x n in
  if B.sign_big_int r < 0 then B.add_big_int r n else r
let fzero = B.zero_big_int
let fone = B.unit_big_int
let fadd a b = fmod (B.add_big_int a b)
let fmul a b = fmod (B.mult_big_int a b)
let fsub a b = fmod (B.sub_big_int a b)
let finv a = Z.powm a (B.sub_big_int n (B.big_int_of_int 2)) n

(* ---------- the relation, as the verified code expects it ---------- *)

(* A Leaf carries its matrix as a vector of rows and its targets as a
   vector, with the arities in the type.  Extraction erases those, so
   the shapes are built from lists here. *)
let leaf_rel (l : Cfrg.leaf) : (B.big_int, P256.t) Composition.comp_rel =
  let rows =
    Array.to_list l.Cfrg.mat
    |> List.map (fun r -> Vector.of_list (Array.to_list r)) in
  Composition.Leaf
    (Big_int_Z.big_int_of_int (Array.length l.Cfrg.mat),
     Big_int_Z.big_int_of_int
       (if Array.length l.Cfrg.mat = 0 then 0
        else Array.length l.Cfrg.mat.(0)),
     Vector.of_list rows,
     Vector.of_list (Array.to_list l.Cfrg.target))

let leaf_transcript (t : Cfrg.transcript)
  : (B.big_int, P256.t) Composition.comp_transcript =
  Obj.magic (Vector.of_list (Array.to_list t.Cfrg.comm),
             Vector.of_list (Array.to_list t.Cfrg.resp))

(* ---------- leaf validity, the verified checker ----------
 *
 * Two conditions the standard validates and we did not, until its
 * negative controls said so: every declared secret must appear in some
 * equation, and no target may be the neutral element. Compiler/
 * LeafValidity.v proves each necessary, by exhibiting what goes wrong
 * without it, and proves this decider equivalent to them. *)
let leaf_valid (l : Cfrg.leaf) : bool =
  let rows =
    Array.to_list l.Cfrg.mat
    |> List.map (fun r -> Vector.of_list (Array.to_list r)) in
  LeafValidity.leaf_validb
    P256.identity (fun p q -> P256.equal p q)
    (Big_int_Z.big_int_of_int (Array.length l.Cfrg.mat))
    (Big_int_Z.big_int_of_int
       (if Array.length l.Cfrg.mat = 0 then 0 else Array.length l.Cfrg.mat.(0)))
    (Vector.of_list rows)
    (Vector.of_list (Array.to_list l.Cfrg.target))

(* ---------- the verified verifier, instantiated ---------- *)

(* A degenerate leaf is rejected before the equation is even checked:
 * an equation whose target is neutral is satisfied by the zero
 * witness, and a secret in a dead column is not proven at all, so
 * accepting such a proof would mean accepting one that proves less
 * than it appears to. *)
let verify (l : Cfrg.leaf) (t : Cfrg.transcript) (c : B.big_int) : bool =
  leaf_valid l &&
  Composition.comp_verify
    fzero fone fadd fmul fsub finv
    P256.identity P256.add (fun p k -> P256.mul k p)
    (fun p q -> P256.equal p q)
    (leaf_rel l) c (leaf_transcript t)

(* ---------- compact proofs ----------
 *
 * A compact proof carries the challenge and the responses but not the
 * announcement, which the verifier recomputes.  That recomputation is
 * [compact_fill], and it is verified: comp_compact_recover proves that
 * compacting an accepted transcript and refilling it at the same
 * challenge returns the original.  So we use the extracted function
 * rather than recomputing by hand.
 *
 * Verification is then the challenge check.  Rebuild the announcement
 * from the claimed challenge, derive the challenge the rebuilt
 * announcement implies, and require the two to agree.  That is where
 * a compact proof gets its soundness, since the equation holds by
 * construction. *)
let fopp a = fsub fzero a

let compact_fill (l : Cfrg.leaf) (c : B.big_int) (resp : B.big_int array)
  : (B.big_int, P256.t) Composition.comp_transcript =
  Obj.magic
    (Nizk.compact_fill
       fzero fone fadd fmul fsub fopp finv
       P256.identity P256.add (fun p k -> P256.mul k p)
       (leaf_rel l) c (Obj.magic (Vector.of_list (Array.to_list resp))))

(* The announcement the recomputation produced, as a list of points in
   the order the hash expects. *)
let recovered_commitment (m : int)
    (t : (B.big_int, P256.t) Composition.comp_transcript) : P256.t array =
  let (comm, _) =
    (Obj.magic t : P256.t Vector.t * B.big_int Vector.t) in
  let rec take k = function
    | Vector.Coq_nil -> []
    | Vector.Coq_cons (x, _, tl) -> if k = 0 then [] else x :: take (k-1) tl in
  Array.of_list (take m comm)
