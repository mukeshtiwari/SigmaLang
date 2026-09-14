(* Recovering the statement a published election actually proves.
 *
 * Usage:  main.exe [election file] [ballot limit]
 *
 * The question this answers is not "do these ballots verify?" but
 * "what do they prove?".  Those are different questions, and only the
 * second one is about the protocol rather than about whichever
 * verifier happened to be run.
 *
 * Examples/Recover.v lays out a space of candidate readings of the
 * Helios ballot proof: which side of each equality carries the
 * secret, and which announcement elements reach the Fiat-Shamir hash.
 *
 * Scope, stated plainly.  This selects among readings a human wrote
 * down; it does not solve for an unknown relation.  The group
 * elements below are read from the ballots, and each candidate's
 * matrix is computed from them by the compiler before any data is
 * examined.  Solving instead of selecting would mean fitting unknown
 * group elements to observed transcripts, which is
 * discrete-logarithm hard: anyone who could do it would have broken
 * the scheme rather than documented it.
 * Each candidate is a statement, so each compiles, and each arrives
 * with the compiler's theorems already proven of it.  This driver
 * runs every candidate against real published ballots and reports
 * which ones accept.
 *
 * The point is recovered_relation_holds in Recover.v.  A candidate
 * that accepts is not merely a verifier saying yes: two accepting
 * runs sharing an announcement and differing in the challenge yield a
 * witness for that candidate's relation.  So a candidate that accepts
 * the published corpus is evidence about what the corpus proves.
 *
 * We established the right reading by hand the first time, which took
 * a day and a detour through Python.  This makes it a search. *)

open Helioslib

let bis = Big_int_Z.big_int_of_string
let bi = Big_int_Z.big_int_of_int

(* Helios derives every challenge with SHA-1.  The hash is a parameter
 * of the verified entry points, so supplying it here is all that is
 * needed; the candidates differ in what is fed to it, not in which
 * function it is. *)
let sha1_bigint (s : string) : Big_int_Z.big_int =
  let d = Cryptokit.hash_string (Cryptokit.Hash.sha1 ()) s in
  let r = ref Big_int_Z.zero_big_int in
  String.iter
    (fun c -> r := Big_int_Z.add_int_big_int (Char.code c)
                     (Big_int_Z.mult_int_big_int 256 !r))
    d;
  !r

let gof (s : string) : Helios.coq_G = bis s
let fof (s : string) : Helios.coq_F = Helios.mk_field (bis s)
let fzero : Helios.coq_F = Helios.mk_field (bi 0)

let get = function Some x -> x | None -> failwith "compilation failed"

open Yojson.Safe.Util
let str j = to_string j

(* A ballot proof, marshalled into the transcript shape the compiled
 * disjunction expects: both branches, and the stored challenge of the
 * first.  This part does not vary with the candidate; what varies is
 * the statement it is checked against. *)
let leaf a b responses = (Vector.of_list [a; b], Vector.of_list responses)

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

let () =
  let path =
    if Array.length Sys.argv > 1 then Sys.argv.(1)
    else "Heliosdata/IACR2024.txt" in
  if not (Sys.file_exists path) then
    failwith (Printf.sprintf "no such file: %s" path);
  let limit =
    if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 60 in

  let raw = In_channel.with_open_bin path In_channel.input_all in
  let ballots_s, trustees_s =
    match String.split_on_char ';' raw with
    | a :: b :: _ -> a, b
    | _ -> failwith "expected semicolon-separated sections" in
  let ballots =
    String.split_on_char '\n' ballots_s
    |> List.filter (fun l -> String.trim l <> "")
    |> List.filteri (fun i _ -> i < limit)
    |> List.map Yojson.Safe.from_string in
  let trustees = Yojson.Safe.from_string trustees_s |> to_list in
  let h =
    List.fold_left Helios.gmul Helios.gone
      (List.map (fun t -> gof (str (member "y" (member "public_key" t)))) trustees) in

  (* every (ciphertext, proof) pair in the ballots we read *)
  let proofs =
    List.concat_map
      (fun b ->
         List.concat_map
           (fun ans ->
              let choices = member "choices" ans |> to_list in
              let pfs = member "individual_proofs" ans |> to_list in
              List.map2
                (fun ch pf ->
                   (gof (str (member "alpha" ch)), gof (str (member "beta" ch)),
                    to_list pf))
                choices pfs)
           (member "answers" (member "vote" b) |> to_list))
      ballots in

  Printf.printf "Recovering the statement from published ballots\n";
  Printf.printf "  file    : %s\n" (Filename.basename path);
  Printf.printf "  ballots : %d   proofs : %d\n" (List.length ballots)
    (List.length proofs);
  Printf.printf "  the search is over %d candidate readings of the protocol\n\n"
    (List.length Recover.all_candidates);

  Printf.printf "  %-34s %8s %8s\n" "candidate" "accepts" "of";
  Printf.printf "  %s\n" (String.make 52 '-');

  let results =
    List.map
      (fun k ->
         let ok = ref 0 and total = ref 0 in
         List.iter
           (fun (alpha, beta, pf) ->
              let rel = get (Recover.cand_rel k h alpha beta) in
              let t = ballot_transcript pf in
              incr total;
              if Recover.cand_verify k sha1_bigint rel t then incr ok)
           proofs;
         Printf.printf "  %-34s %8d %8d\n" (Recover.cand_name k) !ok !total;
         flush stdout;
         (k, !ok, !total))
      Recover.all_candidates in

  let survivors = List.filter (fun (_, ok, tot) -> ok = tot && tot > 0) results in
  Printf.printf "\n";
  (match survivors with
   | [ (k, _, n) ] ->
       Printf.printf "  Identified: of the %d candidate readings, exactly one\n"
         (List.length Recover.all_candidates);
       Printf.printf "  is consistent with all %d published proofs:\n" n;
       Printf.printf "    %s\n" (Recover.cand_name k);
       Printf.printf "  recovered_relation_holds says acceptance under a reading\n";
       Printf.printf "  means that reading's relation is satisfied, so this is a\n";
       Printf.printf "  fact about the corpus and not about our verifier.\n";
       Printf.printf "  Note the scope: the group elements were read from the\n";
       Printf.printf "  ballots and each candidate's matrix was computed from them\n";
       Printf.printf "  before any data was touched. What is determined here is\n";
       Printf.printf "  which candidate fits, not the value of any matrix entry.\n"
   | [] ->
       Printf.printf "  No candidate accepts every proof, so the true reading lies\n";
       Printf.printf "  outside the space searched and the space needs widening.\n";
       Printf.printf "  That is evidence that our understanding of the protocol is\n";
       Printf.printf "  wrong, which is useful, but it is not an identification.\n"
   | many ->
       Printf.printf "  %d candidates accept every proof, so honest data does not\n"
         (List.length many);
       List.iter (fun (k, _, _) -> Printf.printf "    %s\n" (Recover.cand_name k)) many;
       Printf.printf "  separate them. This is the weak Fiat-Shamir situation:\n";
       Printf.printf "  a selector that discards announcement elements accepts\n";
       Printf.printf "  every honest proof, so no amount of honest data rules it\n";
       Printf.printf "  out. Recover.first_per_leaf_not_injective is the proof\n";
       Printf.printf "  that it cannot be ruled out by testing at all.\n");

  (* Is the recovery well posed?
   *
   * Above, exactly one candidate accepted the published corpus. That
   * is only meaningful if the candidates are pairwise
   * distinguishable: if two of them accepted the same transcripts, a
   * search could never tell them apart, and "recovered" would be the
   * wrong word.
   *
   * So we check it directly. For each candidate, generate an honest
   * proof under that candidate's own rule with the verified prover.
   * Every one verifies under its own rule, which is cand_complete.
   * Then check it under every other rule. A diagonal matrix says the
   * candidates are pairwise distinguishable and the recovery above is
   * well posed. An off-diagonal hit would say two readings are
   * observationally equal, which is worth knowing too.
   *
   * Note what this does NOT show. Dropping announcement elements from
   * the hash is a real hazard, and first_per_leaf_not_injective
   * states it, but it is not exhibited by tampering with a
   * transcript: the verification equations bind the commitments
   * algebraically whether or not the hash does. The hazard is about
   * what a challenge commits to, not about what an equation checks. *)
  Printf.printf "\n  Cross-verification: proof made under the row rule,\n";
  Printf.printf "  checked under the column rule (1 = accepted)\n\n";

  let rnd_scalar () =
    let a = Big_int_Z.big_int_of_int (Random.bits ()) in
    let b = Big_int_Z.big_int_of_int (Random.bits ()) in
    Helios.mk_field
      Big_int_Z.(add_big_int (mult_big_int a (Big_int_Z.big_int_of_int 1073741824)) b) in
  let vec2 a b = Vector.of_list [a; b] in
  Random.self_init ();

  let cands = Array.of_list Recover.all_candidates in
  let n = Array.length cands in
  Printf.printf "  %-34s" "";
  for j = 0 to n - 1 do Printf.printf " %2d" j done;
  Printf.printf "\n";

  for i = 0 to n - 1 do
    let k = cands.(i) in
    (* one honest encryption of zero, proved under rule i *)
    let r = rnd_scalar () in
    let alpha = Helios.gpow Helios.gen r in
    let beta = Helios.gpow h r in
    let rel_of kk = get (Recover.cand_rel kk h alpha beta) in
    let w : (Helios.coq_F, Helios.coq_G) Composition.comp_witness =
      Obj.magic (Datatypes.Coq_inl (vec2 r fzero)) in
    let rnd : (Helios.coq_F, Helios.coq_G) Composition.comp_rand =
      Obj.magic ((vec2 (rnd_scalar ()) (rnd_scalar ()),
                  vec2 (rnd_scalar ()) (rnd_scalar ())),
                 rnd_scalar ()) in
    let t = Recover.cand_prove k sha1_bigint (rel_of k) w rnd in
    Printf.printf "  %2d %-31s" i (Recover.cand_name k);
    for j = 0 to n - 1 do
      let kk = cands.(j) in
      let ok = Recover.cand_verify kk sha1_bigint (rel_of kk) (Obj.magic t) in
      Printf.printf " %2d" (if ok then 1 else 0)
    done;
    Printf.printf "\n"; flush stdout
  done;

  Printf.printf "\n  A diagonal matrix means every reading is observationally\n";
  Printf.printf "  distinct, so exactly one accepting candidate above is a\n";
  Printf.printf "  recovery and not a coincidence.\n"
