(* Identifying the statement a published election proves.
 *
 * Usage:  main.exe [election file] [ballot limit]
 *
 * The question is not "do these transcripts verify?" but "what do
 * they prove?".  Those are different questions, and only the second
 * is about the protocol rather than about whichever verifier happened
 * to be run.
 *
 * Examples/Recover.v specifies what a candidate reading may be and
 * proves the enumeration is exactly that specification, so the space
 * searched is auditable rather than hand-picked.  A target says which
 * protocol to point the search at; this file supplies the transcripts
 * and the group elements, which cannot be theorems.
 *
 * Scope, stated plainly.  This selects among readings; it does not
 * solve for an unknown relation.  The group elements are read from
 * the election file, and each candidate's matrix is computed from
 * them by the compiler before any data is examined.
 *
 * A candidate is dropped the moment it fails one transcript.  That is
 * the only pruning, and it is by refutation rather than heuristic,
 * which is what keeps all_candidates_spec meaningful.  It is also why
 * a larger space costs less than a smaller one did: all but the
 * survivor die on their first transcript. *)

open Helioslib

let bis = Big_int_Z.big_int_of_string
let bi = Big_int_Z.big_int_of_int

(* Helios derives every challenge with SHA-1.  The hash is a parameter
 * of the verified entry points, so supplying it here is all that is
 * needed; candidates differ in what is fed to it, not in which
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

(* ---------------- transcripts ----------------
 *
 * Marshalling only.  What varies between candidates is the statement
 * a transcript is checked against, never the transcript itself. *)

type transcript = (Helios.coq_F, Helios.coq_G) Composition.comp_transcript

let leaf comms resps = (Vector.of_list comms, Vector.of_list resps)

(* A ballot proof: a disjunction carrying both branches and the stored
 * challenge of the first. *)
let ballot_transcript pf : transcript =
  let br j =
    let c = List.nth pf j in
    let com = member "commitment" c in
    (gof (str (member "A" com)), gof (str (member "B" com)),
     fof (str (member "challenge" c)), fof (str (member "response" c)))
  in
  let (a0, b0, c0, r0) = br 0 and (a1, b1, _, r1) = br 1 in
  let l0 = leaf [a0; b0] [r0; fzero] and l1 = leaf [a1; b1] [fzero; r1] in
  Obj.magic ((l0, l1), c0)

(* A decryption proof: a single leaf, two announcement elements, one
 * response. *)
let decrypt_transcript pf : transcript =
  let com = member "commitment" pf in
  Obj.magic (leaf [gof (str (member "A" com)); gof (str (member "B" com))]
               [fof (str (member "response" pf))])

(* ---------------- a target, as this driver sees it ---------------- *)

type observation = { inst : Helios.coq_G list; tr : transcript }

type job = {
  job_name : string;
  job_tg   : Recover.target;
  job_obs  : observation list;
}

(* ---------------- the search ---------------- *)

let search (j : job) =
  let cands = Recover.target_candidates j.job_tg in
  let check k =
    let rec go n = function
      | [] -> (n, true)
      | o :: rest ->
          let rel = get (Recover.cand_rel j.job_tg k o.inst) in
          if Recover.cand_verify k sha1_bigint o.inst rel o.tr
          then go (n + 1) rest
          else (n, false)
    in
    go 0 j.job_obs in
  let t0 = Unix.gettimeofday () in
  let results = List.map (fun k -> (k, check k)) cands in
  let dt = Unix.gettimeofday () -. t0 in
  let survivors = List.filter (fun (_, (_, ok)) -> ok) results in
  let deepest =
    List.fold_left (fun acc (_, (n, ok)) -> if ok then acc else max acc n)
      0 results in
  let total = List.length j.job_obs in

  Printf.printf "\n== %s ==\n" j.job_name;
  Printf.printf "  transcripts            : %d\n" total;
  Printf.printf "  readings enumerated    : %d\n" (List.length cands);
  Printf.printf "  search time            : %.1fs\n" dt;
  Printf.printf "  deepest refuted reading: %d transcripts\n" deepest;
  (match survivors with
   | [ (k, _) ] ->
       Printf.printf "  IDENTIFIED             : %s\n" (Recover.cand_name k)
   | [] ->
       Printf.printf "  no reading is consistent with the transcripts, so the\n";
       Printf.printf "  true one lies outside the specified space\n"
   | many ->
       Printf.printf "  %d readings are consistent; the data does not separate\n"
         (List.length many);
       List.iter (fun (k, _) ->
           Printf.printf "      %s\n" (Recover.cand_name k)) many);
  flush stdout;
  (cands, survivors)

(* Is a survivor actually distinguishable from every other reading?
 * Generate an honest proof under its own rule with the verified
 * prover, which cand_complete says is accepted, then check it under
 * every other reading. *)
let cross_check (j : job) cands survivors mk_witness mk_rand =
  match survivors with
  | [] -> ()
  | _ ->
      List.iter
        (fun (k, _) ->
           match j.job_obs with
           | [] -> ()
           | o :: _ ->
               let rel_of kk = get (Recover.cand_rel j.job_tg kk o.inst) in
               let t = Recover.cand_prove k sha1_bigint o.inst (rel_of k)
                         (mk_witness ()) (mk_rand ()) in
               let agreeing =
                 List.filter
                   (fun kk ->
                      Recover.cand_verify kk sha1_bigint o.inst (rel_of kk)
                        (Obj.magic t))
                   cands in
               Printf.printf
                 "  cross-check            : accepted by %d of %d readings%s\n"
                 (List.length agreeing) (List.length cands)
                 (if List.length agreeing = 1 then " (unique)" else "");
               flush stdout)
        survivors

(* ---------------- reading the election ---------------- *)

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
  let all_lines =
    String.split_on_char '\n' ballots_s
    |> List.filter (fun l -> String.trim l <> "") in
  let ballots =
    all_lines |> List.filteri (fun i _ -> i < limit)
              |> List.map Yojson.Safe.from_string in
  (* whether the cap actually truncated the election *)
  let truncated = List.length ballots < List.length all_lines in
  let trustees = Yojson.Safe.from_string trustees_s |> to_list in
  let h =
    List.fold_left Helios.gmul Helios.gone
      (List.map (fun t -> gof (str (member "y" (member "public_key" t)))) trustees) in

  (* ballot proofs: instance is the election key and the ciphertext *)
  let ballot_obs =
    List.concat_map
      (fun b ->
         List.concat_map
           (fun ans ->
              let choices = member "choices" ans |> to_list in
              let pfs = member "individual_proofs" ans |> to_list in
              List.map2
                (fun ch pf ->
                   { inst = [h;
                             gof (str (member "alpha" ch));
                             gof (str (member "beta" ch))];
                     tr = ballot_transcript (to_list pf) })
                choices pfs)
           (member "answers" (member "vote" b) |> to_list))
      ballots in

  (* decryption proofs: these are about the aggregate over every
     ballot, so they only make sense when the whole election was read.
     With a cap they are skipped rather than reported as failures. *)
  let decrypt_obs =
    if truncated then []
    else begin
      let cts =
        List.concat_map
          (fun b ->
             List.concat_map
               (fun ans ->
                  member "choices" ans |> to_list
                  |> List.map (fun ch ->
                      (gof (str (member "alpha" ch)), gof (str (member "beta" ch)))))
               (member "answers" (member "vote" b) |> to_list))
          ballots in
      let ncand =
        match ballots with
        | [] -> 0
        | b :: _ ->
            List.length (member "choices"
                           (List.hd (member "answers" (member "vote" b) |> to_list))
                         |> to_list) in
      let aggr =
        List.init ncand
          (fun i -> List.filteri (fun k _ -> k mod ncand = i) cts |> Helios.aggregate) in
      List.concat_map
        (fun t ->
           let pk = gof (str (member "y" (member "public_key" t))) in
           let facs = member "decryption_factors" t |> to_list |> List.hd |> to_list in
           let pfs = member "decryption_proofs" t |> to_list |> List.hd |> to_list in
           List.mapi
             (fun i (fac, pf) ->
                let (a, _) = List.nth aggr i in
                { inst = [pk; a; gof (str fac)]; tr = decrypt_transcript pf })
             (List.combine facs pfs))
        trustees
    end in

  Printf.printf "Identifying statements from published transcripts\n";
  Printf.printf "  file    : %s\n" (Filename.basename path);
  Printf.printf "  ballots : %d\n" (List.length ballots);
  Printf.printf "  the candidate space is specified by valid_candidate;\n";
  Printf.printf "  all_candidates_spec proves the enumeration is exactly it\n";
  flush stdout;

  let rnd_scalar () =
    let a = Big_int_Z.big_int_of_int (Random.bits ()) in
    let b = Big_int_Z.big_int_of_int (Random.bits ()) in
    Helios.mk_field
      Big_int_Z.(add_big_int (mult_big_int a (bi 1073741824)) b) in
  let vec l = Vector.of_list l in
  Random.self_init ();

  (* Each job carries: the target, its transcripts, a way to build a
     fresh instance together with a witness for it, and the shape of
     the prover randomness. *)
  let jobs =
    [ ({ job_name = "Helios ballot validity";
         job_tg = Recover.helios_ballot_target;
         job_obs = ballot_obs },
       (* an encryption of zero, whose witness is the randomness; the
          other branch is the one an honest prover simulates *)
       (fun () ->
          let r = rnd_scalar () in
          ([h; Helios.gpow Helios.gen r; Helios.gpow h r],
           (fun () -> Obj.magic (Datatypes.Coq_inl (vec [r; fzero]))))),
       (fun () -> Obj.magic ((vec [rnd_scalar (); rnd_scalar ()],
                              vec [rnd_scalar (); rnd_scalar ()]),
                             rnd_scalar ())))
    ; ({ job_name = "Helios correct decryption";
         job_tg = Recover.helios_decrypt_target;
         job_obs = decrypt_obs },
       (* a key and a decryption factor sharing one exponent *)
       (fun () ->
          let x = rnd_scalar () in
          let aggr = Helios.gpow Helios.gen (rnd_scalar ()) in
          ([Helios.gpow Helios.gen x; aggr; Helios.gpow aggr x],
           (fun () -> Obj.magic (vec [x]))))
      ,
       (fun () -> Obj.magic (vec [rnd_scalar ()])))
    ] in

  List.iter
    (fun (j, mkinstance, mkr) ->
       if j.job_obs = [] then begin
         Printf.printf "\n== %s ==\n" j.job_name;
         Printf.printf "  skipped: no transcripts read.  Decryption proofs are\n";
         Printf.printf "  about the aggregate over every ballot, so they need the\n";
         Printf.printf "  whole election; re-run without a ballot cap.\n";
         flush stdout
       end else begin
         let (cands, survivors) = search j in
         (* The cross-check proves under the survivor's own rule, so it
            needs an instance we hold a witness for.  Build a fresh
            honest one of the right shape rather than reuse a published
            transcript, whose witness we of course do not have. *)
         let (inst, mkw') = mkinstance () in
         let j' = { j with job_obs = [ { inst; tr = (List.hd j.job_obs).tr } ] } in
         cross_check j' cands survivors mkw' mkr
       end)
    jobs
