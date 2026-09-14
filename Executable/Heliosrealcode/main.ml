(* Verify a published Helios election with the extracted compiler.
 *
 * Usage:  main.exe [election file] [ballot limit]
 *
 * With no argument it reads Heliosdata/IACR2024.txt, so it runs out of
 * the box from the repository root.
 *
 * The file is the format used by SigmaProtocol's HeliosDatacode: the
 * ballots as one JSON object per line, then a semicolon, then the
 * trustees as a JSON array, then a semicolon, then the tally.
 *
 * Every zero-knowledge check below is Helios.helios_ballot_verify or
 * Helios.helios_decrypt_verify, extracted from the verified
 * development.  This file only parses, marshals and does the
 * arithmetic that is not a proof: aggregating the ciphertexts,
 * combining the decryption factors, and recovering the tally.
 *
 * The challenge is RECOMPUTED from the announcement, not read from
 * the ballot.  That is the point of the exercise. *)

open Helioslib

let bis = Big_int_Z.big_int_of_string
let bi = Big_int_Z.big_int_of_int

(* SHA-1 of a string, as a big-endian integer.  Helios derives every
 * challenge this way; the hash is a parameter of the verified entry
 * points, so supplying it here is all that is needed.
 *
 * SHA-1 is collision broken, and Cryptokit says so.  For a Fiat-Shamir
 * challenge what is wanted is more than collision resistance anyway,
 * and a fresh design should use SHA-256.  Verifying ballots that were
 * already cast leaves no choice. *)
let sha1_bigint (s : string) : Big_int_Z.big_int =
  let d = Cryptokit.hash_string (Cryptokit.Hash.sha1 ()) s in
  let r = ref Big_int_Z.zero_big_int in
  String.iter
    (fun c -> r := Big_int_Z.add_int_big_int (Char.code c)
                     (Big_int_Z.mult_int_big_int 256 !r))
    d;
  !r

(* Group and field elements extract to plain big integers. *)
let gof (s : string) : Helios.coq_G = bis s
let fof (s : string) : Helios.coq_F = Helios.mk_field (bis s)
let fzero : Helios.coq_F = Helios.mk_field (bi 0)

let get = function Some x -> x | None -> failwith "compilation failed"

(* ---------------- JSON helpers ---------------- *)

open Yojson.Safe.Util

let str j = to_string j

(* ---------------- transcripts ---------------- *)

(* A leaf transcript is its announcements and its responses, one
 * response per declared private variable.  A ballot branch mentions
 * only its own randomness, so the other column is unconstrained and
 * any value does; zero is as good as any. *)
let leaf a b responses =
  (Vector.of_list [a; b], Vector.of_list responses)

(* A disjunction transcript carries both branches and the challenge
 * of the first; the verifier derives the second as c minus it, which
 * is exactly Helios's rule that the two branch challenges sum to the
 * hash. *)
let ballot_transcript pf =
  let br j =
    let c = List.nth pf j in
    let com = member "commitment" c in
    (gof (str (member "A" com)), gof (str (member "B" com)),
     fof (str (member "challenge" c)), fof (str (member "response" c)))
  in
  let (a0, b0, c0, r0) = br 0 and (a1, b1, _, r1) = br 1 in
  let l0 = leaf a0 b0 [r0; fzero] and l1 = leaf a1 b1 [fzero; r1] in
  (Obj.magic ((l0, l1), c0) : (Helios.coq_F, Helios.coq_G) Composition.comp_transcript)

(* A decryption or key proof is a single leaf. *)
let single_transcript a b responses =
  (Obj.magic (leaf a b responses)
   : (Helios.coq_F, Helios.coq_G) Composition.comp_transcript)

(* ---------------- the election ---------------- *)

(* ---------- statement quality over the deployed corpus ----------
 *
 * Every zero-knowledge check in this file verifies a proof against a
 * statement the verifier builds for itself from the ballot.  This
 * section asks a different question: is that statement worth proving?
 * Compiler/LeafStatus.v decides it, and Degeneracy.v says what a bad
 * answer costs - a second witness beside every first one, so the
 * proof establishes less than it appears to.
 *
 * The statements here are not fixed.  ballot_rel builds its matrix
 * out of the ciphertext the voter submitted, so a voter chooses part
 * of the statement they are then asked to prove.  That is exactly the
 * setting where a degenerate statement could be reached on purpose,
 * and it is why running this over real ballots says something that
 * running it over a draft's seven example relations does not. *)

let rec leaves_of (r : (Helios.coq_F, Helios.coq_G) Composition.comp_rel) =
  match r with
  | Composition.Leaf (m, n, mat, pub) -> [ (m, n, mat, pub) ]
  | Composition.CAnd (a, b) | Composition.COr (a, b) ->
      leaves_of a @ leaves_of b
  | Composition.CThresh (_, k, _, rs) ->
      List.concat_map leaves_of (Vector.to_list k rs)

(* A column that is the identity in every row supports the kernel
   vector concentrated there.  The verdict still checks it. *)
let dead_column_proposal m n mat =
  let rows = List.map (Vector.to_list n) (Vector.to_list m mat) in
  let ni = Big_int_Z.int_of_big_int n in
  let dead j =
    rows <> [] &&
    List.for_all (fun row -> Helios.gdec (List.nth row j) Helios.gone) rows in
  let rec find j =
    if j >= ni then None else if dead j then Some j else find (j + 1) in
  match find 0 with
  | None -> None
  | Some j ->
      Some (Vector.of_list
              (List.init ni
                 (fun k -> if k = j then Helios.fone else Helios.fzero)))

(* A compiled branch claims only the secrets it mentions.  The DSL
   gives every leaf the width of the global private-variable vector,
   so a branch of a disjunction carries columns for the other
   branch's secrets and never mentions them; those are abstention,
   not degeneracy, and live_claim is what says so. *)
(* The search for an acceptance certificate, and it is a search, not a
   decision procedure: nothing here is trusted.  If some equation
   carries a claimed secret on a base that appears nowhere else in
   that equation, then that one equation already reads "this secret is
   zero" for any incidence solution, so the combination certifying
   that column is the single coefficient one.  Compiler/Determined.v
   checks whatever comes out; a wrong guess is simply not believed.

   The general case needs Gaussian elimination over the field, which
   would emit its certificate the same way and be checked by the same
   code. *)
let certificate_for m n mat cl =
  let mi = Big_int_Z.int_of_big_int m and ni = Big_int_Z.int_of_big_int n in
  let rows =
    Array.of_list
      (List.map (fun r -> Array.of_list (Vector.to_list n r))
         (Vector.to_list m mat)) in
  let unique_in_row i j =
    let b = rows.(i).(j) in
    (not (Helios.gdec b Helios.gone)) &&
    (let c = ref 0 in
     Array.iter (fun x -> if Helios.gdec x b then incr c) rows.(i);
     !c = 1) in
  let block j =
    let rec find i =
      if i >= mi then None else if unique_in_row i j then Some i else find (i+1) in
    let pivot = find 0 in
    Vector.of_list
      (List.init mi
         (fun i ->
            Vector.of_list
              (List.init ni
                 (fun j' ->
                    if pivot = Some i && j' = j then Helios.fone
                    else Helios.fzero)))) in
  Vector.of_list (List.init ni block)

let classify_one (m, n, mat, pub) =
  LeafStatus.classify_leaf
    Helios.fzero Helios.fone Helios.fadd Helios.fmul Helios.fdec
    Helios.gone Helios.gdec
    m n mat pub
    (Claim.live_claim Helios.gone Helios.gdec m n mat)
    { LeafStatus.ev_degenerate = dead_column_proposal m n mat
    ; LeafStatus.ev_determined =
        Some (certificate_for m n mat
                (Claim.live_claim Helios.gone Helios.gdec m n mat)) }

type qtally =
  { mutable det : int; mutable deg : int; mutable und : int
  ; mutable vac : int; mutable uns : int; mutable ok : int
  ; mutable tot : int }

let qt = { det = 0; deg = 0; und = 0; vac = 0; uns = 0; ok = 0; tot = 0 }

let record_quality r =
  List.iter
    (fun l ->
       let c = classify_one l in
       qt.tot <- qt.tot + 1;
       (match c.LeafStatus.lc_determination with
        | LeafStatus.Cert_determined -> qt.det <- qt.det + 1
        | LeafStatus.Cert_degenerate _ -> qt.deg <- qt.deg + 1
        | LeafStatus.Cert_determination_undecided -> qt.und <- qt.und + 1);
       (match c.LeafStatus.lc_vacuity with
        | LeafStatus.Cert_vacuous -> qt.vac <- qt.vac + 1
        | LeafStatus.Cert_unsatisfiable _ -> qt.uns <- qt.uns + 1
        | LeafStatus.Cert_vacuity_undecided -> ());
       let (m, n, _, _) = l in
       if LeafStatus.leaf_acceptable m n c then qt.ok <- qt.ok + 1)
    (leaves_of r)

let () =
  (* With no argument, use the copy of the 2024 election kept in the
     repository, so the verifier runs out of the box from the
     repository root. *)
  let path =
    if Array.length Sys.argv > 1 then Sys.argv.(1)
    else "Heliosdata/IACR2024.txt"
  in
  if not (Sys.file_exists path) then
    failwith (Printf.sprintf
                "no such file: %s (usage: main.exe [election file])" path);
  (* an optional second argument caps how many ballots to check, for
     a fast turnaround while debugging the encoding *)
  let limit =
    if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else max_int in
  Printf.printf "Verifying %s%s\n" (Filename.basename path)
    (if limit = max_int then "" else Printf.sprintf " (first %d ballots)" limit);
  let raw = In_channel.with_open_bin path In_channel.input_all in
  let parts = String.split_on_char ';' raw in
  let ballots_s, trustees_s, tally_s =
    match parts with
    | [a; b; c] -> a, b, c
    | _ -> failwith "expected three semicolon-separated sections"
  in
  let ballots =
    String.split_on_char '\n' ballots_s
    |> List.filter (fun l -> String.trim l <> "")
    |> List.filteri (fun i _ -> i < limit)
    |> List.map Yojson.Safe.from_string
  in
  let trustees = Yojson.Safe.from_string trustees_s |> to_list in
  let tally =
    Yojson.Safe.from_string tally_s |> to_list |> List.hd |> to_list
    |> List.map to_int
  in
  let ncand = List.length tally in
  Printf.printf "  %d ballots, %d trustees, %d candidates\n"
    (List.length ballots) (List.length trustees) ncand;

  (* the election key is the product of the trustees' keys *)
  let pks = List.map (fun t -> gof (str (member "y" (member "public_key" t)))) trustees in
  let h = List.fold_left Helios.gmul Helios.gone pks in
  Printf.printf "  election key is the product of trustee keys : %b\n"
    (Helios.key_consistent h pks);

  (* every trustee proves it knows its own secret key *)
  let pok_ok = ref true in
  List.iter
    (fun t ->
       let pk = gof (str (member "y" (member "public_key" t))) in
       let pok = member "pok" t in
       let rel = get (Helios.pok_rel pk) in
       record_quality rel;
       (* a key proof has one equation, so its announcement is one
          element; the leaf still expects a pair, so reuse it *)
       let a = gof (str (member "commitment" pok)) in
       let r = fof (str (member "response" pok)) in
       let t' = Obj.magic (Vector.of_list [a], Vector.of_list [r]) in
       pok_ok := !pok_ok && Helios.helios_decrypt_verify sha1_bigint rel t')
    trustees;
  Printf.printf "  all trustee key proofs verify               : %b\n" !pok_ok;

  (* every ballot proves each of its ciphertexts encrypts 0 or 1 *)
  let t0 = Unix.gettimeofday () in
  let nproofs = ref 0 and nbad = ref 0 in
  List.iter
    (fun b ->
       List.iter
         (fun ans ->
            let choices = member "choices" ans |> to_list in
            let proofs = member "individual_proofs" ans |> to_list in
            List.iter2
              (fun ch pf ->
                 let alpha = gof (str (member "alpha" ch))
                 and beta = gof (str (member "beta" ch)) in
                 let rel = get (Helios.ballot_rel h alpha beta) in
                 record_quality rel;
                 let t = ballot_transcript (to_list pf) in
                 incr nproofs;
                 if not (Helios.helios_ballot_verify sha1_bigint rel t) then incr nbad)
              choices proofs)
         (member "answers" (member "vote" b) |> to_list))
    ballots;
  let dt = Unix.gettimeofday () -. t0 in
  Printf.printf "  %d ballot proofs verified in %.1fs, failures : %d\n"
    !nproofs dt !nbad;

  (* homomorphic aggregation *)
  let cts =
    List.concat_map
      (fun b ->
         List.concat_map
           (fun ans ->
              member "choices" ans |> to_list
              |> List.map (fun ch ->
                  (gof (str (member "alpha" ch)), gof (str (member "beta" ch)))))
           (member "answers" (member "vote" b) |> to_list))
      ballots
  in
  let per_candidate i =
    List.filteri (fun k _ -> k mod ncand = i) cts |> Helios.aggregate
  in
  let aggr = List.init ncand per_candidate in

  (* each trustee proves its decryption factor uses the same key *)
  let dec_ok = ref true and ndec = ref 0 in
  List.iter
    (fun t ->
       let pk = gof (str (member "y" (member "public_key" t))) in
       let facs = member "decryption_factors" t |> to_list |> List.hd |> to_list in
       let pfs = member "decryption_proofs" t |> to_list |> List.hd |> to_list in
       List.iteri
         (fun i (fac, pf) ->
            let d = gof (str fac) in
            let (a, _) = List.nth aggr i in
            let rel = get (Helios.decrypt_rel pk a d) in
            record_quality rel;
            let com = member "commitment" pf in
            let t' =
              single_transcript
                (gof (str (member "A" com))) (gof (str (member "B" com)))
                [fof (str (member "response" pf))]
            in
            incr ndec;
            if not (Helios.helios_decrypt_verify sha1_bigint rel t') then dec_ok := false)
         (List.combine facs pfs))
    trustees;
  Printf.printf "  %d decryption proofs verify                 : %b\n" !ndec !dec_ok;

  (* combine the factors and check the published tally *)
  let nb = List.length ballots in
  let rec dlog i acc target =
    if i > nb then None
    else if Helios.gdec acc target then Some i
    else dlog (i + 1) (Helios.gmul acc Helios.gen) target
  in
  let recovered =
    List.mapi
      (fun i (_, beta) ->
         let facs =
           List.map
             (fun t ->
                gof (str (List.nth (member "decryption_factors" t |> to_list
                                    |> List.hd |> to_list) i)))
             trustees
         in
         dlog 0 Helios.gone (Helios.combine beta facs))
      aggr
  in
  let shown = List.map (function Some t -> string_of_int t | None -> "?") recovered in
  Printf.printf "  recovered tally : [%s]\n" (String.concat "; " shown);
  Printf.printf "  published tally : [%s]\n"
    (String.concat "; " (List.map string_of_int tally));
  let agree = List.for_all2 (fun r t -> r = Some t) recovered tally in
  Printf.printf "\n  Statement quality over every leaf checked\n";
  Printf.printf "    %d leaves from ballot, key-proof and decryption statements\n" qt.tot;
  Printf.printf "    witness determined %d, DEGENERATE %d, undecided %d\n"
    qt.det qt.deg qt.und;
  Printf.printf "    vacuity: VACUOUS %d, UNSATISFIABLE %d, neither %d\n"
    qt.vac qt.uns (qt.tot - qt.vac - qt.uns);
  Printf.printf "    fit to compile: %d of %d\n" qt.ok qt.tot;

  Printf.printf "\n  VERDICT: proofs %s, tally %s, statements %s\n"
    (if !nbad = 0 && !dec_ok && !pok_ok then "all verify" else "FAILED")
    (if agree then "matches" else "MISMATCH")
    (if qt.ok = qt.tot then "all sound"
     else Printf.sprintf "%d NOT SOUND" (qt.tot - qt.ok))
