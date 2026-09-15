(* Privacy Pass token issuance, with the server's DLEQ proof.
 *
 * The statement, its compilation, the Fiat-Shamir binding and the
 * algebra of batching are in Examples/PrivacyPass.v.  This file
 * supplies what cannot be a theorem: the group elements, the token
 * seeds, the blinding factors, and the hash.
 *
 * Scope, stated plainly.  There is no published Privacy Pass
 * transcript to check against, the way Helios has published ballots,
 * so this is a self-test: it plays both sides of an issuance and
 * checks that an honest server's proof verifies and that a
 * key-rotating server's does not.
 *
 * The key-rotation test is the one worth watching.  A server that
 * signs one token in a batch with a different key is exactly the
 * attack the DLEQ proof exists to stop: the odd key would act as a
 * tag identifying that client when the token is later spent.  Note
 * that batch soundness is a probabilistic argument over the random
 * coefficients, due to Henry, and is not mechanised in our
 * development; what we prove is the other direction, that batching
 * preserves the relation for an honest server.  The rejection below
 * is evidence, not proof. *)

open Helioslib

let big = Big_int_Z.big_int_of_int

let rnd () : Helios.coq_F =
  let a = Big_int_Z.big_int_of_string (string_of_int (Random.bits ())) in
  let b = Big_int_Z.big_int_of_string (string_of_int (Random.bits ())) in
  let c = Big_int_Z.big_int_of_string (string_of_int (Random.bits ())) in
  Helios.mk_field
    Big_int_Z.(add_big_int (mult_big_int a (big 1073741824))
                 (add_big_int (mult_big_int b (big 32768)) c))

let get = function Some x -> x | None -> failwith "compilation failed"

let pow = Helios.gpow

(* SHA-256 as a big integer.  Privacy Pass uses SHA-256 for its
 * challenge hash H3 and for the batching seed; the verified entry
 * points take the hash as a parameter, so supplying it here is all
 * that is needed, and pp_complete is proven for every choice. *)
let sha256_bigint (s : string) : Big_int_Z.big_int =
  let d = Cryptokit.hash_string (Cryptokit.Hash.sha256 ()) s in
  let r = ref Big_int_Z.zero_big_int in
  String.iter
    (fun c -> r := Big_int_Z.add_int_big_int (Char.code c)
                     (Big_int_Z.mult_int_big_int 256 !r))
    d;
  !r

(* The fixed generator X and the server's key commitment Y = X ^ k. *)
let base_x = Helios.gen

(* Token seeds.  A deployment hashes the seed to a curve point, so
 * that nobody knows its discrete logarithm with respect to X.  Here
 * the point is the generator raised to a value that is then
 * discarded, which exercises the same arithmetic; nothing in the
 * proof depends on how the point was produced. *)
let token_point () = pow base_x (rnd ())

(* --------------- the batching coefficients ---------------
 *
 * Privacy Pass seeds a PRNG with a hash of the whole instance and
 * reads the coefficients off it.  Any derivation serves: the verified
 * theorem batch_same_exponent holds for arbitrary coefficients, which
 * is deliberately stronger than the protocol needs. *)
let coefficients n (ps : Helios.coq_G list) (qs : Helios.coq_G list)
    (y : Helios.coq_G) : Helios.coq_F list =
  let render g = Helios.g_to_string g in
  let seed =
    String.concat "," (List.map render ([base_x; y] @ ps @ qs)) in
  List.init n (fun i ->
      Helios.mk_field (sha256_bigint (seed ^ "|" ^ string_of_int i)))

(* --------------- one issuance ---------------
 *
 * The server holds k.  For each of n tokens the client sends a
 * blinded point P_i; the server returns Q_i = P_i ^ k.  [bad_at]
 * optionally names one index the server signs with a different key,
 * which is the key-rotation attack. *)
let issue ?(bad_at = -1) n =
  let k = rnd () in
  let k_odd = rnd () in
  let y = pow base_x k in
  let ps = List.init n (fun _ -> token_point ()) in
  let qs =
    List.mapi (fun i p -> pow p (if i = bad_at then k_odd else k)) ps in
  (k, y, ps, qs)

(* ---------- statement quality ----------
 *
 * The same classifier the Helios and CFRG drivers use.  A compiled
 * leaf claims the secrets it mentions, so the claim is its live
 * columns; the certificate search is the single-coefficient case and
 * is not trusted, since Compiler/Determined.v checks what it emits. *)
let rec leaves_of (r : (Helios.coq_F, Helios.coq_G) Composition.comp_rel) =
  match r with
  | Composition.Leaf (m, n, mat, pub) -> [ (m, n, mat, pub) ]
  | Composition.CAnd (a, b) | Composition.COr (a, b) ->
      leaves_of a @ leaves_of b
  | Composition.CThresh (_, k, _, rs) ->
      List.concat_map leaves_of (Vector.to_list k rs)

(* Certificates by elimination.  Search.Incidence is ordinary OCaml
   and is not trusted: whatever it returns goes to the extracted
   checker, which refuses a wrong answer. *)
let hfield : Helios.coq_F Search.Incidence.field =
  { Search.Incidence.zero = Helios.fzero; one = Helios.fone;
    add = Helios.fadd; mul = Helios.fmul; sub = Helios.fsub;
    div = Helios.fdiv; eq = Helios.fdec }

let to_arrays m n mat =
  Array.of_list
    (List.map (fun r -> Array.of_list (Vector.to_list n r))
       (Vector.to_list m mat))

let vec_of_array a = Vector.of_list (Array.to_list a)

let evidence_for m n mat cl =
  match
    Search.Incidence.certify hfield Helios.gdec Helios.gone
      (to_arrays m n mat) (Array.of_list (Vector.to_list n cl))
  with
  | Search.Incidence.Degenerate v ->
      { LeafStatus.ev_degenerate = Some (vec_of_array v)
      ; LeafStatus.ev_determined = None }
  | Search.Incidence.Determined blocks ->
      { LeafStatus.ev_degenerate = None
      ; LeafStatus.ev_determined =
          Some (Vector.of_list
                  (List.map
                     (fun blk ->
                        Vector.of_list
                          (List.map vec_of_array (Array.to_list blk)))
                     (Array.to_list blocks))) }
  | Search.Incidence.Undecided ->
      { LeafStatus.ev_degenerate = None; LeafStatus.ev_determined = None }

let qdet = ref 0 and qdeg = ref 0 and qund = ref 0
and qvac = ref 0 and quns = ref 0 and qtot = ref 0

let record_quality r =
  List.iter
    (fun (m, n, mat, pub) ->
       let c =
         LeafStatus.classify_leaf
           Helios.fzero Helios.fone Helios.fadd Helios.fmul Helios.fdec
           Helios.gone Helios.gdec m n mat pub
           (Claim.live_claim Helios.gone Helios.gdec m n mat)
           (evidence_for m n mat
              (Claim.live_claim Helios.gone Helios.gdec m n mat)) in
       incr qtot;
       (match c.LeafStatus.lc_determination with
        | LeafStatus.Cert_determined -> incr qdet
        | LeafStatus.Cert_degenerate _ -> incr qdeg
        | LeafStatus.Cert_determination_undecided -> incr qund);
       (match c.LeafStatus.lc_vacuity with
        | LeafStatus.Cert_vacuous -> incr qvac
        | LeafStatus.Cert_unsatisfiable _ -> incr quns
        | LeafStatus.Cert_vacuity_undecided -> ()))
    (leaves_of r)

let report_quality () =
  Printf.printf "\n  Statement quality over every leaf\n";
  Printf.printf "    %d leaves: determined %d, DEGENERATE %d, undecided %d\n"
    !qtot !qdet !qdeg !qund;
  Printf.printf "    vacuity: VACUOUS %d, UNSATISFIABLE %d, neither %d\n"
    !qvac !quns (!qtot - !qvac - !quns)

(* Compile, prove and verify one batched DLEQ.  The composites are
 * computed by PrivacyPass.batch, the verified definition, rather than
 * being folded here, so the executable and the theorem are talking
 * about the same thing. *)
let run label n (k, y, ps, qs) =
  (* Forming the composites is linear in the batch size and is where
   * the cost of a large batch actually sits, so it is timed
   * separately from the proof, which is one fixed-size DLEQ however
   * many tokens went into it. *)
  let t0 = Unix.gettimeofday () in
  let cs = coefficients n ps qs y in
  let m = PrivacyPass.batch cs ps in
  let z = PrivacyPass.batch cs qs in
  let t_batch = Unix.gettimeofday () -. t0 in
  let genv = PrivacyPass.dleq_genv base_x y m z in
  let pre = PrivacyPass.dleq_pre base_x y m z in
  let rel = get (PrivacyPass.compile_with genv PrivacyPass.dleq_core) in
  record_quality rel;
  let w : (Helios.coq_F, Helios.coq_G) Composition.comp_witness =
    Obj.magic (PrivacyPass.scalars (PrivacyPass.dleq_wenv k)) in
  let rnd_vec : (Helios.coq_F, Helios.coq_G) Composition.comp_rand =
    Obj.magic (Vector.of_list [rnd ()]) in
  let t1 = Unix.gettimeofday () in
  let t = PrivacyPass.pp_prove sha256_bigint pre rel w rnd_vec in
  let ok = PrivacyPass.pp_verify sha256_bigint pre rel t in
  let t_proof = Unix.gettimeofday () -. t1 in
  Printf.printf
    "  %-34s verifies=%-5b  batching %7.1f ms   proof %5.1f ms\n"
    label ok (t_batch *. 1000.0) (t_proof *. 1000.0);
  (rel, pre, t, ok)

let () =
  Random.self_init ();
  Printf.printf "Privacy Pass: the server's DLEQ proof over a batch of tokens\n";
  Printf.printf "  group: the 2048-bit IACR group (a deployment would use an\n";
  Printf.printf "         elliptic curve; the statement does not change)\n\n";

  Printf.printf "Honest issuance, by batch size\n";
  List.iter
    (fun n ->
       ignore (run (Printf.sprintf "%d token%s" n (if n = 1 then "" else "s"))
                 n (issue n)))
    [1; 10; 30; 100];

  Printf.printf "\nA server that signs one token with a different key\n";
  let n = 10 in
  let (_, _, _, ok) =
    run "one token signed with the wrong key" n (issue ~bad_at:3 n) in
  Printf.printf "  %-34s %s\n"
    "verdict"
    (if ok then "ACCEPTED - this would be a bug"
     else "rejected, as the DLEQ proof intends");

  Printf.printf "\nA valid proof offered against another issuance\n";
  let (_, _, t, _) = run "honest batch" n (issue n) in
  let (_, y', ps', qs') = issue n in
  let cs' = coefficients n ps' qs' y' in
  let m' = PrivacyPass.batch cs' ps' in
  let z' = PrivacyPass.batch cs' qs' in
  let rel' =
    get (PrivacyPass.compile_with
           (PrivacyPass.dleq_genv base_x y' m' z') PrivacyPass.dleq_core) in
  let pre' = PrivacyPass.dleq_pre base_x y' m' z' in
  Printf.printf "  %-34s verifies=%-5b  (must be false)\n"
    "same proof, different tokens"
    (PrivacyPass.pp_verify sha256_bigint pre' rel' t);

  (* The instance is hashed into the challenge, so a proof that is not
   * bound to its instance is rejected even when the algebra would
   * otherwise go through.  Dropping the instance from the hash input
   * is the weak Fiat-Shamir failure. *)
  Printf.printf "  %-34s verifies=%-5b  (must be false)\n"
    "same proof, instance not in hash"
    (PrivacyPass.pp_verify sha256_bigint [] rel' t);
  report_quality ()
