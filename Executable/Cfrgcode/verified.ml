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

(* ---------- the verified verifier, instantiated ---------- *)

let verify (l : Cfrg.leaf) (t : Cfrg.transcript) (c : B.big_int) : bool =
  Composition.comp_verify
    fzero fone fadd fmul fsub finv
    P256.identity P256.add (fun p k -> P256.mul k p)
    (fun p q -> P256.equal p q)
    (leaf_rel l) c (leaf_transcript t)
