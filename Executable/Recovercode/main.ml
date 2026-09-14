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


(* ================= Stage two: solving for the relation =================
 *
 * Everything above selects among readings a human wrote down.  This
 * section does not.  It solves for the relation.
 *
 * A leaf's verification equation, for row i, is
 *
 *     M[i][1]^r1 * ... * M[i][n]^rn  =  a[i] * P[i]^c
 *
 * with the announcement a, the challenge c and the responses r all
 * read from the transcript.  The unknowns are the matrix entries and
 * the target, each ranging over a pool of published elements.  So a
 * row is a subset-product problem over a finite pool rather than a
 * search for unknown group elements, and it is small.
 *
 * Three facts make it cheap.  Rows are independent given the observed
 * response vector, so they are solved one at a time.  A wrong
 * assignment satisfies a group equation only by accident, with
 * probability about one over the group order, so one observation
 * rejects nearly everything and a second confirms.  And the target
 * slot need not be enumerated at all: precompute the right-hand side
 * for every pool element into a table and look the left-hand side up,
 * which turns a quadratic scan into a linear one.
 *
 * This stage uses the challenge *published in the transcript*, never
 * a recomputed one, so it is independent of the hash rule.  That
 * matters, or stage one and stage two would each need the other's
 * answer.
 *
 * Scope.  The pool is the published elements and a closure of them,
 * so this solves an assignment problem, not a discrete logarithm.  An
 * element outside the closure cannot be found, and the run says so by
 * reporting no solution rather than a wrong one. *)

(* A pool element is a symbolic expression over the named instance
 * elements, so a solution can be printed as something a human reads
 * rather than as a 617-digit number. *)
type pexp = PB of int | PInv of pexp | PMul of pexp * pexp

let rec pname (bases : string array) = function
  | PB i -> bases.(i)
  | PInv e -> pname bases e ^ "^-1"
  | PMul (a, b) -> pname bases a ^ "*" ^ pname bases b

let rec peval (vals : Helios.coq_G array) = function
  | PB i -> vals.(i)
  | PInv e -> Helios.ginv_g (peval vals e)
  | PMul (a, b) -> Helios.gmul (peval vals a) (peval vals b)

(* Closed under inverses and pairwise products.  Closure is not
 * optional: the right branch of a Helios ballot proves against
 * beta * g^-1, which nobody publishes. *)
let closure (nbase : int) : pexp list =
  let b = List.init nbase (fun i -> PB i) in
  let l1 = b @ List.map (fun e -> PInv e) b in
  let prods = List.concat_map (fun a -> List.map (fun x -> PMul (a, x)) l1) l1 in
  l1 @ prods

(* One transcript, as this stage sees it: the values of the named
 * instance elements, the announcement, the published challenge, and
 * the responses. *)
type obs = {
  ovals : Helios.coq_G array;
  oann  : Helios.coq_G array;
  ochal : Helios.coq_F;
  oresp : Helios.coq_F array;
}

let key (g : Helios.coq_G) : string = Helios.g_to_string g

(* Solutions for row [i]: assignments to the n matrix slots and the
 * target that fit every observation.  The first observation is the
 * filter, the rest confirm. *)
let solve_row (pool : pexp array) (obs : obs list) (n : int) (i : int) =
  match obs with
  | [] -> []
  | first :: rest ->
      (* Evaluate the pool once per observation, never per candidate.
       * Inverses are modular inversions and the pool is full of them,
       * so re-evaluating inside the inner loop dominated everything. *)
      let eval_all o = Array.map (peval o.ovals) pool in
      let vals0 = eval_all first in
      (* Distinct pool expressions can denote the same element: the
       * closure contains 1*g, g*1, 1^-1*g and so on. Keep one
       * representative of each value, so the report names a relation
       * once rather than five times. *)
      let seen = Hashtbl.create (2 * Array.length pool) in
      let keep =
        Array.to_list (Array.mapi (fun j v -> (j, v)) vals0)
        |> List.filter (fun (_, v) ->
             let k = key v in
             if Hashtbl.mem seen k then false
             else (Hashtbl.add seen k (); true))
        |> List.map fst
        |> Array.of_list in
      let np = Array.length keep in
      let powr0 = Array.init n (fun k ->
          Array.map (fun j -> Helios.gpow vals0.(j) first.oresp.(k)) keep) in
      let tbl0 = Hashtbl.create (2 * np) in
      Array.iteri
        (fun idx j ->
           Hashtbl.replace tbl0
             (key (Helios.gmul first.oann.(i) (Helios.gpow vals0.(j) first.ochal)))
             idx)
        keep;
      (* enumerate the matrix slots; the target is a table lookup *)
      let out = ref [] in
      let rec go k acc prod =
        if k = n then
          (match Hashtbl.find_opt tbl0 (key prod) with
           | Some p -> out := (List.rev acc, keep.(p)) :: !out
           | None -> ())
        else
          for idx = 0 to np - 1 do
            go (k + 1) (keep.(idx) :: acc) (Helios.gmul prod powr0.(k).(idx))
          done in
      go 0 [] Helios.gone;
      (* confirm the survivors on the remaining observations *)
      let rest_vals = List.map (fun o -> (o, eval_all o)) rest in
      let confirm (ms, p) =
        List.for_all
          (fun (o, vals) ->
             let lhs =
               List.fold_left2
                 (fun acc j k -> Helios.gmul acc (Helios.gpow vals.(j) o.oresp.(k)))
                 Helios.gone ms (List.init n (fun k -> k)) in
             Helios.gdec lhs
               (Helios.gmul o.oann.(i) (Helios.gpow vals.(p) o.ochal)))
          rest_vals in
      List.filter confirm !out


(* ---- closing the loop on a solved relation ----
 *
 * What the solver printed is an untrusted guess. Turn it into a
 * surface statement, push it through the verified compiler, and check
 * that the resulting protocol accepts the published transcripts. Only
 * then is there anything to believe, and by recovered_relation_holds
 * what is believed is a fact about the corpus.
 *
 * One honest limitation. In the surface language the base of an
 * exponentiation must be a name the environment resolves, so a solved
 * matrix entry that is a derived element cannot be written directly;
 * it would need the environment extended with a fresh name. Targets
 * have no such restriction, being ordinary group expressions, which
 * is why beta*g^-1 causes no trouble. We report the case rather than
 * silently dropping it. *)

let rec pexp_to_gexpr (bases : string array) = function
  | PB i -> Surface.YPt bases.(i)
  | PInv e -> Surface.YInv (pexp_to_gexpr bases e)
  | PMul (a, b) -> Surface.YMul (pexp_to_gexpr bases a, pexp_to_gexpr bases b)

let secret_name k = Printf.sprintf "x%d" k

(* One row becomes one equality, with the secret-carrying side on the
 * left, which is the orientation the elaborator needs. *)
let row_to_eq (bases : string array) (pool : pexp array) (ms, p) =
  let lhs =
    List.fold_left
      (fun acc (k, j) ->
         match pool.(j) with
         | PB i ->
             let term = Surface.YPow (bases.(i), Surface.XPriv (secret_name k)) in
             (match acc with None -> Some term | Some a -> Some (Surface.YMul (a, term)))
         | _ -> raise Exit)
      None
      (List.mapi (fun k j -> (k, j)) ms) in
  match lhs with
  | None -> raise Exit
  | Some l -> Surface.TEq (l, pexp_to_gexpr bases pool.(p))

let conjoin = function
  | [] -> raise Exit
  | x :: rest -> List.fold_left (fun a b -> Surface.TAnd (a, b)) x rest

(* Build the statement from the per-row solutions, compile it with the
 * verified compiler, and verify every transcript under it. *)
let close_loop (bases : string array) (pool : pexp array)
    (sols : (int list * int) list) (obs : obs list) (n : int)
    (mk_tr : obs -> transcript) =
  Printf.printf "  closing the loop     : " ;
  match (try Some (conjoin (List.map (row_to_eq bases pool) sols))
         with Exit -> None) with
  | None ->
      Printf.printf
        "not expressible directly (a solved base is a derived element)\n";
      flush stdout
  | Some stmt ->
      let used = Array.to_list bases
                 @ List.init n secret_name in
      let privs = List.init n secret_name in
      (match obs with
       | [] -> Printf.printf "no transcripts\n"; flush stdout
       | _ :: _ ->
            (* recompile per transcript, since the instance changes *)
            let ok = ref 0 and bad = ref 0 in
            List.iter
              (fun o ->
                 let genv s =
                   let rec look i =
                     if i >= Array.length bases then Helios.gone
                     else if bases.(i) = s then o.ovals.(i)
                     else look (i + 1) in
                   look 0 in
                 match Recover.compile_sstmt used privs genv stmt with
                 | None -> incr bad
                 | Some rel ->
                     (* hash every announcement element in order,
                        instance not included, which is the rule the
                        identification stage established *)
                     let k = { Recover.cand_or = Recover.OLeft;
                               Recover.cand_sel =
                                 List.init (Array.length o.oann)
                                   (fun i -> Big_int_Z.big_int_of_int i);
                               Recover.cand_inst = Recover.IAnnOnly } in
                     if Recover.cand_verify k sha1_bigint [] rel (mk_tr o)
                     then incr ok else incr bad)
              obs;
            Printf.printf "compiled; %d of %d transcripts verify\n"
              !ok (!ok + !bad);
            flush stdout)

let render (bases : string array) (pool : pexp array) (ms, p) =
  let terms =
    List.mapi (fun k j -> Printf.sprintf "%s^x%d" (pname bases pool.(j)) k) ms in
  Printf.sprintf "%s = %s" (String.concat " * " terms) (pname bases pool.(p))

let infer label (bases : string array) (obs : obs list) (nrows : int) (n : int)
    (closer : (obs -> transcript) option) =
  Printf.printf "\n== solving for the relation: %s ==\n" label;
  (match obs with
   | [] -> Printf.printf "  no transcripts\n"; flush stdout
   | _ ->
     let pool = Array.of_list (closure (Array.length bases)) in
     Printf.printf "  published elements : %s\n" (String.concat " " (Array.to_list bases));
     Printf.printf "  pool after closure : %d\n" (Array.length pool);
     Printf.printf "  transcripts        : %d\n" (List.length obs);
     let t0 = Unix.gettimeofday () in
     let all_sols = List.init nrows (fun i -> solve_row pool obs n i) in
     List.iteri
       (fun i sols ->
          Printf.printf "  row %d : %d solution%s\n" i (List.length sols)
            (if List.length sols = 1 then "" else "s");
          List.iter (fun s -> Printf.printf "      %s\n" (render bases pool s)) sols)
       all_sols;
     Printf.printf "  time               : %.1fs\n" (Unix.gettimeofday () -. t0);
     (match closer with
      | None ->
          Printf.printf
            "  closing the loop     : not applicable here. A ballot branch is\n";
          Printf.printf
            "                         half of a disjunction, so its challenge is\n";
          Printf.printf
            "                         not a hash and it is not a standalone\n";
          Printf.printf
            "                         proof. The disjunction as a whole is\n";
          Printf.printf
            "                         checked by the identification stage.\n"
      | Some mk_tr ->
          if List.for_all (fun l -> List.length l = 1) all_sols then
            close_loop bases pool (List.map List.hd all_sols) obs n mk_tr
          else
            Printf.printf
              "  closing the loop     : skipped, a row is not uniquely solved\n");
     flush stdout)

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
  (* the per-candidate aggregate, needed by both the decryption
     identification and the decryption inference *)
  let aggr_list =
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
      aggr
    end in

  let decrypt_obs =
    if aggr_list = [] then []
    else
      List.concat_map
        (fun t ->
           let pk = gof (str (member "y" (member "public_key" t))) in
           let facs = member "decryption_factors" t |> to_list |> List.hd |> to_list in
           let pfs = member "decryption_proofs" t |> to_list |> List.hd |> to_list in
           List.mapi
             (fun i (fac, pf) ->
                let (a, _) = List.nth aggr_list i in
                { inst = [pk; a; gof (str fac)]; tr = decrypt_transcript pf })
             (List.combine facs pfs))
        trustees in

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


  (* ---- stage two: solve for the relations ----
   *
   * A handful of transcripts is plenty. A wrong assignment survives a
   * group equation only by accident, so the first observation does
   * nearly all the filtering and the rest only confirm. We take ninfer
   * and say so rather than sweeping the corpus for no gain. *)
  let take n l = List.filteri (fun i _ -> i < n) l in
  (* Five is already generous. The first observation does the
     filtering; the rest only guard against a coincidence whose
     probability is about one over the group order. *)
  let ninfer = 5 in

  let decrypt_infer_obs =
    take ninfer
      (List.concat_map
         (fun t ->
            let pk = gof (str (member "y" (member "public_key" t))) in
            let facs = member "decryption_factors" t |> to_list |> List.hd |> to_list in
            let pfs = member "decryption_proofs" t |> to_list |> List.hd |> to_list in
            if aggr_list = [] then []
            else
              List.mapi
                (fun i (fac, pf) ->
                   let (a, _) = List.nth aggr_list i in
                   let com = member "commitment" pf in
                   { ovals = [| Helios.gen; pk; a; gof (str fac); Helios.gone |];
                     oann  = [| gof (str (member "A" com)); gof (str (member "B" com)) |];
                     ochal = fof (str (member "challenge" pf));
                     oresp = [| fof (str (member "response" pf)) |] })
                (List.combine facs pfs))
         trustees) in

  let ballot_branch_obs br =
    take ninfer
      (List.concat_map
         (fun b ->
            List.concat_map
              (fun ans ->
                 let choices = member "choices" ans |> to_list in
                 let pfs = member "individual_proofs" ans |> to_list in
                 List.map2
                   (fun ch pf ->
                      let p = List.nth (to_list pf) br in
                      let com = member "commitment" p in
                      { ovals = [| Helios.gen; h;
                                   gof (str (member "alpha" ch));
                                   gof (str (member "beta" ch));
                                   Helios.gone |];
                        oann  = [| gof (str (member "A" com));
                                   gof (str (member "B" com)) |];
                        ochal = fof (str (member "challenge" p));
                        oresp = [| fof (str (member "response" p)) |] })
                   choices pfs)
              (member "answers" (member "vote" b) |> to_list))
         ballots) in

  infer "Helios ballot, branch 0 (vote is zero)"
    [| "g"; "h"; "alpha"; "beta"; "1" |] (ballot_branch_obs 0) 2 1 None;
  infer "Helios ballot, branch 1 (vote is one)"
    [| "g"; "h"; "alpha"; "beta"; "1" |] (ballot_branch_obs 1) 2 1 None;
  (* A decryption proof is a single leaf and a standalone
     non-interactive proof, so the loop can be closed on it: the solved
     relation goes back through the verified compiler and its verifier
     is run against the published transcripts. *)
  infer "Helios correct decryption"
    [| "g"; "pk"; "AA"; "M"; "1" |] decrypt_infer_obs 2 1
    (Some (fun o ->
       Obj.magic (leaf [o.oann.(0); o.oann.(1)] [o.oresp.(0)])));

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
