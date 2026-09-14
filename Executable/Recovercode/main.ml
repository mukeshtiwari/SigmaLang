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

  Printf.printf "Identifying the statement from published ballots\n";
  Printf.printf "  file    : %s\n" (Filename.basename path);
  Printf.printf "  ballots : %d   proofs : %d\n" (List.length ballots)
    (List.length proofs);
  Printf.printf "  candidate readings enumerated in Rocq : %d\n"
    (List.length Recover.all_candidates);
  Printf.printf "  the space is specified by valid_candidate, and\n";
  Printf.printf "  all_candidates_spec proves the enumeration is exactly it\n\n";

  (* Early exit. A candidate that fails one proof cannot be the answer,
   * so stop it there. This is the only kind of pruning allowed if the
   * exhaustiveness theorem is to mean anything: we discard a candidate
   * because we refuted it, never because we guessed. It is also what
   * makes the larger space affordable, since all but the survivor die
   * on their first proof. *)
  let check k =
    let rec go n = function
      | [] -> (n, true)
      | (alpha, beta, pf) :: rest ->
          let rel = get (Recover.cand_rel k h alpha beta) in
          let pre = [alpha; beta] in
          if Recover.cand_verify k sha1_bigint pre rel (ballot_transcript pf)
          then go (n + 1) rest
          else (n, false)
    in
    go 0 proofs in

  let t0 = Unix.gettimeofday () in
  let results = List.map (fun k -> (k, check k)) Recover.all_candidates in
  let dt = Unix.gettimeofday () -. t0 in

  let survivors = List.filter (fun (_, (_, ok)) -> ok) results in
  let best_failure =
    List.fold_left (fun acc (_, (n, ok)) -> if ok then acc else max acc n)
      0 results in
  let total = List.length proofs in

  Printf.printf "  searched %d candidates against %d proofs in %.1fs\n"
    (List.length results) total dt;
  Printf.printf "  deepest rejected candidate got through %d proofs\n\n"
    best_failure;

  (match survivors with
   | [ (k, _) ] ->
       Printf.printf "  Identified: exactly one of the %d enumerated readings is\n"
         (List.length results);
       Printf.printf "  consistent with all %d published proofs:\n" total;
       Printf.printf "    %s\n\n" (Recover.cand_name k);
       Printf.printf "  recovered_relation_holds says acceptance under a reading\n";
       Printf.printf "  means that reading's relation is satisfied, so this is a\n";
       Printf.printf "  fact about the corpus and not about our verifier.\n";
       Printf.printf "  Scope: the group elements were read from the ballots and\n";
       Printf.printf "  each candidate's matrix was computed from them before any\n";
       Printf.printf "  data was touched. What is determined is which candidate\n";
       Printf.printf "  fits, not the value of any matrix entry.\n"
   | [] ->
       Printf.printf "  No candidate accepts every proof, so the true reading lies\n";
       Printf.printf "  outside the space specified by valid_candidate. That is\n";
       Printf.printf "  evidence our understanding of the protocol is wrong, which\n";
       Printf.printf "  is useful, but it is not an identification.\n"
   | many ->
       Printf.printf "  %d readings accept every proof, so the published data does\n"
         (List.length many);
       Printf.printf "  not separate them:\n";
       List.iter (fun (k, _) -> Printf.printf "    %s\n" (Recover.cand_name k)) many;
       Printf.printf "\n  This is a finding about what the corpus can distinguish,\n";
       Printf.printf "  not a failure. Reported rather than tuned away.\n");
  flush stdout;

  (* Are the survivors actually distinguishable from the rest?
   *
   * A single survivor is only meaningful if the readings differ
   * observationally. We check that by generating an honest proof under
   * each survivor's own rule with the verified prover, which is
   * accepted by construction (cand_complete), and then checking it
   * under every other reading. A reading that also accepts it is
   * observationally equal to the survivor on this instance. *)
  (match survivors with
   | [] -> ()
   | _ ->
       Printf.printf "\n  Cross-checking the survivor against every other reading\n";
       let rnd_scalar () =
         let a = Big_int_Z.big_int_of_int (Random.bits ()) in
         let b = Big_int_Z.big_int_of_int (Random.bits ()) in
         Helios.mk_field
           Big_int_Z.(add_big_int
                        (mult_big_int a (Big_int_Z.big_int_of_int 1073741824)) b) in
       let vec2 a b = Vector.of_list [a; b] in
       Random.self_init ();
       List.iter
         (fun (k, _) ->
            let r = rnd_scalar () in
            let alpha = Helios.gpow Helios.gen r in
            let beta = Helios.gpow h r in
            let pre = [alpha; beta] in
            let rel_of kk = get (Recover.cand_rel kk h alpha beta) in
            let w : (Helios.coq_F, Helios.coq_G) Composition.comp_witness =
              Obj.magic (Datatypes.Coq_inl (vec2 r fzero)) in
            let rnd : (Helios.coq_F, Helios.coq_G) Composition.comp_rand =
              Obj.magic ((vec2 (rnd_scalar ()) (rnd_scalar ()),
                          vec2 (rnd_scalar ()) (rnd_scalar ())),
                         rnd_scalar ()) in
            let t = Recover.cand_prove k sha1_bigint pre (rel_of k) w rnd in
            let agreeing =
              List.filter
                (fun kk ->
                   Recover.cand_verify kk sha1_bigint pre (rel_of kk) (Obj.magic t))
                Recover.all_candidates in
            Printf.printf
              "    %s\n      accepted by %d of %d readings%s\n"
              (Recover.cand_name k)
              (List.length agreeing) (List.length Recover.all_candidates)
              (if List.length agreeing = 1 then " (uniquely identified)"
               else " -- see below");
            if List.length agreeing > 1 then
              List.iter
                (fun kk -> Printf.printf "        also: %s\n" (Recover.cand_name kk))
                agreeing;
            flush stdout)
         survivors)
