(* A self-test of the compiled Helios statements.
 *
 * This is NOT a verifier for a real Helios election.  It reads no
 * election data.  Every proof it checks is one it generated moments
 * earlier, so what it demonstrates is that the compiled protocol is
 * internally consistent at the real 2048-bit parameters, plus that
 * the two tamper cases fail.  The election below invents its own
 * trustee key rather than using the three real ones.
 *
 * Verifying published 2024 ballots would additionally need SHA-1,
 * Helios's exact byte encoding of the hash input, and a parser for
 * the election JSON.  None of those are here.
 *
 * The statements, their compilation, the Fiat-Shamir binding and the
 * completeness theorems all live in Examples/Helios.v, and those ARE
 * general: they quantify over every ciphertext and every trustee. *)

open Helioslib

let big = Big_int_Z.big_int_of_int
let bigs = Big_int_Z.big_int_of_string
let str = Big_int_Z.string_of_big_int

(* Demo randomness.  A deployment must use a CSPRNG; this is a
 * demonstration of the protocol, not of key generation. *)
let rnd_scalar () : Helios.coq_F =
  let a = bigs (string_of_int (Random.bits ())) in
  let b = bigs (string_of_int (Random.bits ())) in
  let c = bigs (string_of_int (Random.bits ())) in
  Helios.mk_field
    Big_int_Z.(add_big_int (mult_big_int a (big 1073741824))
                 (add_big_int (mult_big_int b (big 32768)) c))

let vec2 a b = Vector.of_list [a; b]
let vec1 a = Vector.of_list [a]

(* The randomness a ballot proof consumes: a commitment scalar per
 * branch, plus the challenge the prover picks freely for the branch
 * it simulates.  The shape follows comp_rand of a COr of two Leafs. *)
let ballot_rand () : (Helios.coq_F, Helios.coq_G) Composition.comp_rand =
  let u0 = rnd_scalar () and u1 = rnd_scalar () in
  let s0 = rnd_scalar () and s1 = rnd_scalar () in
  let c = rnd_scalar () in
  Obj.magic ((vec2 u0 s0, vec2 u1 s1), c)

(* A decryption proof is a single leaf with one secret, so its
 * randomness is one scalar. *)
let decrypt_rand () : (Helios.coq_F, Helios.coq_G) Composition.comp_rand =
  Obj.magic (vec1 (rnd_scalar ()))

let get = function Some x -> x | None -> failwith "compilation failed"

(* ---------------- one ballot, at the real 2024 parameters ---------- *)

let one_ballot () =
  Printf.printf "A self-generated ballot under the real IACR 2024 election key\n";
  let v = Helios.mk_field (big 1) in          (* the voter votes yes *)
  let r = rnd_scalar () in
  let (alpha, beta) = Helios.encrypt Helios.pubkey v r in
  let rel = get (Helios.ballot_rel Helios.pubkey alpha beta) in
  (* the voter knows the randomness of the right branch, the one
     claiming the vote was one, and simulates the left *)
  let w : (Helios.coq_F, Helios.coq_G) Composition.comp_witness =
    Obj.magic (Datatypes.Coq_inr (Helios.ballot_scalars v r)) in
  let t = Helios.ballot_prove Helios.pubkey alpha beta rel w (ballot_rand ()) in
  Printf.printf "  proof verifies                    : %b\n"
    (Helios.ballot_verify Helios.pubkey alpha beta rel t);
  (* the challenge is derived from the instance, so the same proof
     offered against a different ciphertext must fail *)
  Printf.printf "  same proof, ciphertext swapped    : %b  (must be false)\n"
    (Helios.ballot_verify Helios.pubkey beta alpha rel t);
  (* and a proof of a vote of one, re-presented as a proof for a
     ciphertext that is not the one it was made for *)
  let r' = rnd_scalar () in
  let (alpha', beta') = Helios.encrypt Helios.pubkey v r' in
  Printf.printf "  same proof, different ballot      : %b  (must be false)\n"
    (Helios.ballot_verify Helios.pubkey alpha' beta' rel t)

(* ---------------- a whole small election ---------------------------- *)

(* Recover the integer tally from g^tally by searching the small range
 * of possible totals.  Helios does the same; the tally is at most the
 * number of ballots. *)
let dlog_search (target : Helios.coq_G) (limit : int) : int option =
  let rec go i acc =
    if i > limit then None
    else if Helios.gdec acc target then Some i
    else go (i + 1) (Helios.gmul acc Helios.gen)
  in
  go 0 Helios.gone

let election nvoters =
  Printf.printf "\nA %d-voter mock election, self-generated trustee key\n" nvoters;
  (* trustee key *)
  let x = rnd_scalar () in
  let pk = Helios.gpow Helios.gen x in
  Printf.printf "  election key is the product of trustee keys: %b\n"
    (Helios.key_consistent pk [pk]);
  (* every voter encrypts a vote and proves it well formed *)
  let votes = Array.init nvoters (fun i -> if i mod 3 = 0 then 0 else 1) in
  let cts = ref [] and ok = ref true in
  Array.iter
    (fun vi ->
       let v = Helios.mk_field (big vi) in
       let r = rnd_scalar () in
       let (alpha, beta) = Helios.encrypt pk v r in
       let rel = get (Helios.ballot_rel pk alpha beta) in
       let sc = Helios.ballot_scalars v r in
       let w : (Helios.coq_F, Helios.coq_G) Composition.comp_witness =
         Obj.magic (if vi = 0 then Datatypes.Coq_inl sc else Datatypes.Coq_inr sc) in
       let t = Helios.ballot_prove pk alpha beta rel w (ballot_rand ()) in
       ok := !ok && Helios.ballot_verify pk alpha beta rel t;
       cts := (alpha, beta) :: !cts)
    votes;
  Printf.printf "  all %d ballot proofs verify         : %b\n" nvoters !ok;
  (* homomorphic aggregation, then the trustee decrypts and proves it *)
  let (aggr_a, aggr_b) = Helios.aggregate !cts in
  let fac = Helios.decrypt_factor aggr_a x in
  let drel = get (Helios.decrypt_rel pk aggr_a fac) in
  let dw : (Helios.coq_F, Helios.coq_G) Composition.comp_witness =
    Obj.magic (Helios.decrypt_scalars x) in
  let dt = Helios.decrypt_prove pk aggr_a fac drel dw (decrypt_rand ()) in
  Printf.printf "  trustee decryption proof verifies  : %b\n"
    (Helios.decrypt_verify pk aggr_a fac drel dt);
  (* recover the tally and check it against the votes actually cast *)
  let m = Helios.combine aggr_b [fac] in
  let expected = Array.fold_left (+) 0 votes in
  (match dlog_search m nvoters with
   | Some t ->
     Printf.printf "  recovered tally                    : %d (expected %d) %s\n"
       t expected (if t = expected then "" else "MISMATCH")
   | None -> Printf.printf "  recovered tally                    : not found\n")

(* The extracted code uses a native SHA-256 in place of the verified
 * one.  The security theorems hold for any hash, so nothing formal
 * depends on the two agreeing; interoperability does, so check the
 * substitution against a published test vector before trusting it. *)
let check_hash () =
  let got = Sha256.sha256_string "abc" in
  let expect =
    Big_int_Z.big_int_of_string
      "0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
  in
  Printf.printf "  native SHA-256 matches the test vector: %b\n"
    (Big_int_Z.eq_big_int got expect)

(* Helios.g_to_string_gen proves the verified rendering of the
 * generator is exactly this string.  The extracted code uses OCaml's
 * native printer instead, so check the two agree. *)
let check_rendering () =
  let expect = "14887492224963187634282421537186040801304008017743492304481737382571933937568724473847106029915040150784031882206090286938661464458896494215273989547889201144857352611058572236578734319505128042602372864570426550855201448111746579871811249114781674309062693442442368697449970648232621880001709535143047913661432883287150003429802392229361583608686643243349727791976247247948618930423866180410558458272606627111270040091203073580238905303994472202930783207472394578498507764703191288249547659899997131166130259700604433891232298182348403175947450284433411265966789131024573629546048637848902243503970966798589660808533" in
  Printf.printf "  native rendering matches the theorem   : %b\n"
    (String.equal (Helios.g_to_string Helios.gen) expect)

let () =
  Random.self_init ();
  Printf.printf "Self-test of the compiled Helios statements\n";
  Printf.printf "  (not a verifier for a real election; see the header)\n";
  check_hash ();
  check_rendering ();
  Printf.printf "  q = %d bits, p = %d bits\n"
    (String.length (Big_int_Z.string_of_big_int Helios.q) * 10 / 3)
    (String.length (Big_int_Z.string_of_big_int Helios.p) * 10 / 3);
  Printf.printf "  p = %s...\n" (String.sub (str Helios.p) 0 40);
  print_newline ();
  one_ballot ();
  election 12

let () =
  (* throughput of ballot proving and verifying at 2048 bits *)
  let iters = 20 in
  let v = Helios.mk_field (big 1) in
  let r = rnd_scalar () in
  let (alpha, beta) = Helios.encrypt Helios.pubkey v r in
  let rel = get (Helios.ballot_rel Helios.pubkey alpha beta) in
  let w : (Helios.coq_F, Helios.coq_G) Composition.comp_witness =
    Obj.magic (Datatypes.Coq_inr (Helios.ballot_scalars v r)) in
  let t0 = Unix.gettimeofday () in
  let ok = ref true in
  for _ = 1 to iters do
    let t = Helios.ballot_prove Helios.pubkey alpha beta rel w (ballot_rand ()) in
    ok := !ok && Helios.ballot_verify Helios.pubkey alpha beta rel t
  done;
  let dt = Unix.gettimeofday () -. t0 in
  Printf.printf
    "\nbenchmark: %d ballot prove+verify in %.3fs = %.1f/s (all ok: %b)\n"
    iters dt (float_of_int iters /. dt) !ok

let () =
  (* Where does the time actually go?  Compare raw group arithmetic
   * against a full proof, to see whether the bottleneck is the
   * 2048-bit exponentiations or the verified SHA-256 over the
   * decimal rendering of the hash input. *)
  let v = Helios.mk_field (big 1) in
  let r = rnd_scalar () in
  let n = 200 in
  let t0 = Unix.gettimeofday () in
  for _ = 1 to n do ignore (Helios.encrypt Helios.pubkey v r) done;
  let dt_enc = Unix.gettimeofday () -. t0 in
  Printf.printf "  %d encryptions (2 exponentiations each): %.3fs = %.2f ms each\n"
    n dt_enc (dt_enc *. 1000.0 /. float_of_int n);
  let (alpha, beta) = Helios.encrypt Helios.pubkey v r in
  let t1 = Unix.gettimeofday () in
  for _ = 1 to n do ignore (Helios.ballot_rel Helios.pubkey alpha beta) done;
  let dt_c = Unix.gettimeofday () -. t1 in
  Printf.printf "  %d compilations of the statement       : %.3fs = %.2f ms each\n"
    n dt_c (dt_c *. 1000.0 /. float_of_int n)
