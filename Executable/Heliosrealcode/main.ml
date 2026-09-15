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

(* Certificates, found by elimination over the scalar field.
   Search.Incidence is ordinary OCaml and is not trusted: whatever it
   returns is handed to the extracted checker, which refuses a wrong
   answer.  A bug here costs a verdict, never a wrong one. *)
let hfield : Helios.coq_F Search.Incidence.field =
  { Search.Incidence.zero = Helios.fzero; one = Helios.fone;
    add = Helios.fadd; mul = Helios.fmul; sub = Helios.fsub;
    div = Helios.fdiv; eq = Helios.fdec }

let to_arrays m n mat =
  Array.of_list
    (List.map (fun r -> Array.of_list (Vector.to_list n r))
       (Vector.to_list m mat))

let claim_array n cl = Array.of_list (Vector.to_list n cl)

let vec_of_array a = Vector.of_list (Array.to_list a)

let evidence_for m n mat cl =
  match
    Search.Incidence.certify hfield Helios.gdec Helios.gone
      (to_arrays m n mat) (claim_array n cl)
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

let classify_one (m, n, mat, pub) =
  LeafStatus.classify_leaf
    Helios.fzero Helios.fone Helios.fadd Helios.fmul Helios.fdec
    Helios.gone Helios.gdec
    m n mat pub
    (Claim.live_claim Helios.gone Helios.gdec m n mat)
    (evidence_for m n mat (Claim.live_claim Helios.gone Helios.gdec m n mat))

type qtally =
  { mutable det : int; mutable deg : int; mutable und : int
  ; mutable vac : int; mutable uns : int; mutable ok : int
  ; mutable tot : int }

let qt = { det = 0; deg = 0; und = 0; vac = 0; uns = 0; ok = 0; tot = 0 }

(* Every compiled relation, kept so the two routes can be run over the
   same leaves and compared. *)
let compiled : (Helios.coq_F, Helios.coq_G) Composition.comp_rel list ref = ref []

let record_quality r =
  compiled := r :: !compiled;
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

(* ---------- the same question, asked once instead of 13,072 times ----------
 *
 * Compiler/DslInstantiate.v proves that a statement can be checked
 * over its own syntax, and that every environment faithful to it
 * compiles to a relation determining the same claim.  The two halves
 * cost very different things: checking the statement means
 * eliminating over the scalar field, while checking an environment
 * means comparing group elements.  Helios has three statements and
 * this election has thousands of instances of them, so the split is
 * worth measuring rather than asserting.
 *
 * Both routes are run below over the same leaves and their verdicts
 * compared, so a disagreement would show up as a failure rather than
 * as a faster wrong answer. *)

let big = Big_int_Z.big_int_of_int

(* Names, as the compiler's variables. *)
let veq (a : string) (b : string) = String.equal a b

(* The statement's own bases: a cell is the list of (base, coefficient)
   pairs an equation puts on one variable, and two cells are the same
   base exactly when they are syntactically equal. *)
let cellq = DslInstantiate.cell_dec Helios.fdec veq
let cellid : (Helios.coq_F, string) DslInstantiate.cellname = []

(* Certificates, found the same way whatever the bases are. *)
let evidence_gen gdec gid m n mat cl =
  match Search.Incidence.certify hfield gdec gid
          (to_arrays m n mat) (claim_array n cl) with
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

let determination_gen gdec gid m n mat =
  let cl = Claim.live_claim gid gdec m n mat in
  LeafStatus.classify_determination
    Helios.fzero Helios.fone Helios.fadd Helios.fmul Helios.fdec
    gid gdec m n mat cl (evidence_gen gdec gid m n mat cl)

(* The leaves of a statement as equation lists, in the order compile
   builds them -- including the conjunction of two pure statements,
   which the compiler merges into a single leaf. *)
let rec leaf_eqs (s : (Helios.coq_F, string) Dsl.stmt) =
  match s with
  | Dsl.SEqs eqs -> [ eqs ]
  | Dsl.SAnd (a, b) ->
      (match Dsl.leaves_only a, Dsl.leaves_only b with
       | Some la, Some lb -> [ la @ lb ]
       | _ -> leaf_eqs a @ leaf_eqs b)
  | Dsl.SOr (a, b) -> leaf_eqs a @ leaf_eqs b
  | Dsl.SThresh (_, l) -> List.concat_map leaf_eqs l

(* Design time: the statement's own leaves, over names. *)
let design_time_determination n privs eqs =
  let nm = DslInstantiate.name_mat veq n privs eqs in
  determination_gen cellq cellid (big (List.length eqs)) n nm

(* Per instance: the cheap half. *)
let is_faithful n privs genv eqs =
  DslInstantiate.faithful_tob
    Helios.fadd Helios.fmul Helios.fopp Helios.fdec
    Helios.gone Helios.gmul Helios.gpow Helios.gdec
    veq n privs genv Helios.penvI eqs

(* Helios has exactly three statements. *)
let statements =
  [ ("ballot",  big 2, Helios.ballot_privs,  Helios.ballot_core)
  ; ("key",     big 1, Helios.decrypt_privs, Helios.pok_core)
  ; ("decrypt", big 1, Helios.decrypt_privs, Helios.decrypt_core) ]

(* The instance environments that produced those relations. *)
let envs : (Big_int_Z.big_int * string Vector.t
            * (string -> Helios.coq_G)
            * (Helios.coq_F, string) Dsl.equation list list) list ref = ref []

let record_split name genv =
  match List.find_opt (fun (nm, _, _, _) -> nm = name) statements with
  | None -> ()
  | Some (_, n, privs, core) ->
      envs := (n, privs, genv, leaf_eqs core) :: !envs

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
       record_split "key" (Helios.pok_genv pk);
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
                 record_split "ballot" (Helios.ballot_genv h alpha beta);
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
            record_split "decrypt" (Helios.decrypt_genv pk a d);
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

  (* ---------- the same question by two routes, timed ---------- *)
  (* The checks are fast enough that one reading is mostly noise, so
     each is run several times and the best is reported: the best run
     is the one least disturbed by everything else on the machine. *)
  let reps = 5 in
  let clock f =
    let best = ref infinity and last = ref (f ()) in
    for _ = 1 to reps do
      let t = Unix.gettimeofday () in
      last := f ();
      let d = Unix.gettimeofday () -. t in
      if d < !best then best := d
    done;
    (!last, !best) in

  let leaves = List.concat_map leaves_of !compiled in
  let nleaves = List.length leaves in
  let nshapes =
    List.fold_left (fun a (_, _, _, core) -> a + List.length (leaf_eqs core))
      0 statements in

  (* Route A, as the verifier does it today: eliminate over the scalar
     field once per compiled leaf. *)
  let (a_det, ta) =
    clock (fun () ->
        List.fold_left
          (fun acc (m, n, mat, _) ->
             match determination_gen Helios.gdec Helios.gone m n mat with
             | LeafStatus.Cert_determined -> acc + 1
             | _ -> acc)
          0 leaves) in

  (* Route B, design time: the same elimination, over the statements'
     own names, once each. *)
  let (b_shapes, tb1) =
    clock (fun () ->
        List.fold_left
          (fun acc (_, n, privs, core) ->
             List.fold_left
               (fun acc eqs ->
                  match design_time_determination n privs eqs with
                  | LeafStatus.Cert_determined -> acc + 1
                  | _ -> acc)
               acc (leaf_eqs core))
          0 statements) in

  (* Route B, per instance: group comparisons and nothing else. *)
  let (b_ok, tb2) =
    clock (fun () ->
        List.fold_left
          (fun acc (n, privs, genv, eqss) ->
             List.fold_left
               (fun acc eqs ->
                  if is_faithful n privs genv eqs then acc + 1 else acc)
               acc eqss)
          0 !envs) in

  let routes_agree =
    a_det = nleaves && b_shapes = nshapes && b_ok = nleaves in

  Printf.printf "\n  The same question by two routes (best of %d)\n" reps;
  Printf.printf "    per instance : %5d leaves eliminated over the field   %8.4fs\n"
    nleaves ta;
  Printf.printf "    design time  : %5d statement leaves, checked once     %8.4fs\n"
    nshapes tb1;
  Printf.printf "     + instances : %5d faithfulness checks                %8.4fs\n"
    nleaves tb2;
  Printf.printf "    split total  : %41s %8.4fs" "" (tb1 +. tb2);
  if tb1 +. tb2 > 0.0 then
    Printf.printf "   (%.1fx)" (ta /. (tb1 +. tb2));
  Printf.printf "\n    both routes determine every leaf : %s\n"
    (if routes_agree then "yes" else "NO -- DISAGREEMENT");

  Printf.printf "\n  VERDICT: proofs %s, tally %s, statements %s\n"
    (if !nbad = 0 && !dec_ok && !pok_ok then "all verify" else "FAILED")
    (if agree then "matches" else "MISMATCH")
    (if qt.ok = qt.tot then "all sound"
     else Printf.sprintf "%d NOT SOUND" (qt.tot - qt.ok))
