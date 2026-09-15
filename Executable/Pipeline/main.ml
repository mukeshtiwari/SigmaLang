(* One statement, all the way through.
 *
 * The other drivers report verdicts.  This one reports the pipeline:
 * it takes a single statement and prints what the compiler makes of
 * it at each stage, so that "the compiler works" is something you can
 * read rather than something the exit status asserts.
 *
 * The statement is Privacy Pass's issuance proof, the smallest real
 * one we have: a server convinces a client that the token it just
 * signed was signed with the key behind its published public key,
 * without revealing the key.
 *
 * Every function called below is extracted from Rocq except the
 * printing and the hash.  Examples/PrivacyPass.v's [pp_complete] is
 * the theorem this run instantiates: for any relation, witness and
 * randomness, if the relation holds of the witness then the verifier
 * accepts the proof the prover builds.  A run cannot establish that
 * -- only the proof does -- but a run that contradicted it would show
 * the extraction had gone wrong. *)

open Helioslib

let get = function Some x -> x | None -> failwith "compilation failed"
let big = Big_int_Z.big_int_of_int

let rnd () : Helios.coq_F =
  Helios.mk_field (Big_int_Z.big_int_of_string
                     (string_of_int (Random.int 1000000000)))

let sha256_bigint (s : string) : Big_int_Z.big_int =
  let d = Cryptokit.hash_string (Cryptokit.Hash.sha256 ()) s in
  let r = ref Big_int_Z.zero_big_int in
  String.iter
    (fun c -> r := Big_int_Z.add_int_big_int (Char.code c)
                     (Big_int_Z.mult_int_big_int 256 !r)) d;
  !r

(* ---------- rendering the syntax ---------- *)

let rec show_sexpr (e : (Helios.coq_F, string) Surface.sexpr) =
  match e with
  | Surface.XConst _ -> "c"
  | Surface.XPub v -> v
  | Surface.XPriv v -> v
  | Surface.XAdd (a, b) -> "(" ^ show_sexpr a ^ " + " ^ show_sexpr b ^ ")"
  | Surface.XMul (a, b) -> show_sexpr a ^ "*" ^ show_sexpr b
  | Surface.XNeg a -> "-" ^ show_sexpr a

let rec show_gexpr (e : (Helios.coq_F, string) Surface.gexpr) =
  match e with
  | Surface.YOne -> "1"
  | Surface.YPt v -> v
  | Surface.YMul (a, b) -> show_gexpr a ^ " * " ^ show_gexpr b
  | Surface.YInv a -> show_gexpr a ^ "^-1"
  | Surface.YPow (p, e) -> p ^ "^" ^ show_sexpr e

let rec show_sstmt ind (s : (Helios.coq_F, string) Surface.sstmt) =
  let pad = String.make ind ' ' in
  match s with
  | Surface.TEq (a, b) -> pad ^ show_gexpr a ^ "  =  " ^ show_gexpr b
  | Surface.TAnd (a, b) ->
      show_sstmt ind a ^ "\n" ^ pad ^ "AND\n" ^ show_sstmt ind b
  | Surface.TOr (a, b) ->
      show_sstmt ind a ^ "\n" ^ pad ^ "OR\n" ^ show_sstmt ind b
  | Surface.TNeq e -> pad ^ show_sexpr e ^ " <> 0"
  | Surface.TRange (v, _) -> pad ^ v ^ " in range"
  | Surface.TLet (v, e, b) ->
      pad ^ "let " ^ v ^ " = " ^ show_sexpr e ^ " in\n" ^ show_sstmt ind b
  | Surface.TThresh (_, l) ->
      pad ^ "threshold of " ^ string_of_int (List.length l)

(* Public coefficients are field elements and print as 617 digits, so
   the two that actually occur here are named and the rest shown as a
   placeholder rather than silently dropped. *)
let show_f (c : Helios.coq_F) =
  if Helios.fdec c Helios.fone then "1"
  else if Helios.fdec c (Helios.fsub Helios.fzero Helios.fone) then "-1"
  else if Helios.fdec c Helios.fzero then "0"
  else "<scalar>"

let rec show_pexpr (e : (Helios.coq_F, string) Dsl.pexpr) =
  match e with
  | Dsl.PConst c -> show_f c
  | Dsl.PVar v -> v
  | Dsl.PAdd (a, b) -> "(" ^ show_pexpr a ^ "+" ^ show_pexpr b ^ ")"
  | Dsl.PMul (a, b) -> show_pexpr a ^ "*" ^ show_pexpr b
  | Dsl.POpp a -> "-" ^ show_pexpr a

(* A term is a base raised to (public coefficient times secret); the
   coefficient is left out when it is one, which it is throughout this
   statement. *)
let show_term (t : (Helios.coq_F, string) Dsl.term) =
  let c = show_pexpr t.Dsl.t_coeff in
  t.Dsl.t_base ^ "^" ^ (if c = "1" then t.Dsl.t_var else c ^ "*" ^ t.Dsl.t_var)

let show_equation (e : (Helios.coq_F, string) Dsl.equation) =
  let priv = List.map show_term e.Dsl.eq_rhs in
  let off =
    List.map (fun (c, v) -> v ^ "^" ^ show_pexpr c) e.Dsl.eq_off in
  let all = priv @ off in
  (if all = [] then "1" else String.concat " * " all) ^ "  =  1"

let rec show_stmt ind (s : (Helios.coq_F, string) Dsl.stmt) =
  let pad = String.make ind ' ' in
  match s with
  | Dsl.SEqs eqs ->
      String.concat "\n" (List.map (fun e -> pad ^ show_equation e) eqs)
  | Dsl.SAnd (a, b) -> show_stmt ind a ^ "\n" ^ pad ^ "AND\n" ^ show_stmt ind b
  | Dsl.SOr (a, b) -> show_stmt ind a ^ "\n" ^ pad ^ "OR\n" ^ show_stmt ind b
  | Dsl.SThresh (_, l) -> pad ^ "threshold of " ^ string_of_int (List.length l)

(* A compiled matrix holds group elements, which print as 617 digits.
   Naming them back is only possible because we know the environment
   that produced them, which is exactly the point of
   Compiler/Instantiate.v: the names are gone by this stage. *)
let namer genv names g =
  if Helios.gdec g Helios.gone then "1"
  else
    match List.find_opt (fun n -> Helios.gdec (genv n) g) names with
    | Some n -> n
    | None -> "?"

let () =
  Random.self_init ();
  Printf.printf "One statement, all the way through the compiler\n";
  Printf.printf "  Privacy Pass issuance: the server proves it used the key\n";
  Printf.printf "  behind its published key, without revealing it.\n\n";

  (* ---- 1. what the designer writes ---- *)
  Printf.printf "1. The statement, as written in the surface language\n";
  Printf.printf "   (Examples/PrivacyPass.v, dleq_stmt)\n\n%s\n\n"
    (show_sstmt 6 PrivacyPass.dleq_stmt);

  (* ---- 2. elaboration ---- *)
  Printf.printf "2. Elaborated to the core language: every equation moved\n";
  Printf.printf "   onto one side, so a conjunction is list concatenation\n\n%s\n\n"
    (show_stmt 6 PrivacyPass.dleq_core);

  (* ---- 3. compilation ---- *)
  let k = rnd () in
  let base_x = Helios.gen in
  let y = Helios.gpow base_x k in
  let m = Helios.gpow Helios.gen (rnd ()) in
  let z = Helios.gpow m k in
  let genv = PrivacyPass.dleq_genv base_x y m z in
  let names = [ "X"; "Y"; "M"; "Z" ] in
  let name = namer genv names in
  let rel = get (PrivacyPass.compile_with genv PrivacyPass.dleq_core) in
  Printf.printf "3. Compiled against an instance (X, Y, M, Z) to a leaf:\n";
  Printf.printf "   one row per equation, one column per secret\n\n";
  (match rel with
   | Composition.Leaf (mm, nn, mat, pub) ->
       let rows = Vector.to_list mm mat and tgts = Vector.to_list mm pub in
       Printf.printf "      secrets: k          (%s column, %s row(s))\n"
         (Big_int_Z.string_of_big_int nn) (Big_int_Z.string_of_big_int mm);
       List.iter2
         (fun row t ->
            Printf.printf "      %-8s =  %s\n" (name t)
              (String.concat " * "
                 (List.map (fun b -> name b ^ "^k") (Vector.to_list nn row))))
         rows tgts
   | _ -> Printf.printf "      (not a leaf)\n");
  Printf.printf "\n";

  (* ---- 4. prove and verify ---- *)
  let pre = PrivacyPass.dleq_pre base_x y m z in
  let w : (Helios.coq_F, Helios.coq_G) Composition.comp_witness =
    Obj.magic (PrivacyPass.scalars (PrivacyPass.dleq_wenv k)) in
  let rnd_vec : (Helios.coq_F, Helios.coq_G) Composition.comp_rand =
    Obj.magic (Vector.of_list [ rnd () ]) in
  let t = PrivacyPass.pp_prove sha256_bigint pre rel w rnd_vec in
  Printf.printf "4. Proved with the real key, and verified\n";
  Printf.printf "      verifier accepts                       %b\n"
    (PrivacyPass.pp_verify sha256_bigint pre rel t);
  Printf.printf "      this is the case pp_complete covers\n\n";

  (* ---- 5. the proof is about this instance and no other ---- *)
  let z' = Helios.gpow m (rnd ()) in
  let genv' = PrivacyPass.dleq_genv base_x y m z' in
  let rel' = get (PrivacyPass.compile_with genv' PrivacyPass.dleq_core) in
  let pre' = PrivacyPass.dleq_pre base_x y m z' in
  Printf.printf "5. The same proof against a token signed with another key\n";
  Printf.printf "      verifier accepts                       %b\n"
    (PrivacyPass.pp_verify sha256_bigint pre' rel' t);
  Printf.printf "      the same proof with the instance left out of the hash\n";
  Printf.printf "      verifier accepts                       %b\n\n"
    (PrivacyPass.pp_verify sha256_bigint [] rel t);

  (* ---- 6. the second half, in detail ---- *)
  Printf.printf "6. The second half, on the same leaf\n\n";

  (* The incidence system, read off the matrix: one equation per row
     per distinct non-neutral base, saying that the exponents sitting
     under that base must sum to zero. *)
  let incidence_of mat mm nn =
    List.concat_map
      (fun row ->
         let bases = Vector.to_list nn row in
         let distinct =
           List.sort_uniq compare
             (List.filter_map
                (fun b -> if Helios.gdec b Helios.gone then None
                          else Some (name b)) bases) in
         List.map
           (fun b ->
              let carried =
                List.filteri (fun _ _ -> true)
                  (List.map (fun x -> x)
                     (List.filter (fun (_, bb) -> name bb = b)
                        (List.mapi (fun i bb -> (i, bb)) bases))) in
              Printf.sprintf "under %-3s :  %s  =  0" b
                (String.concat " + "
                   (List.map (fun (i, _) -> Printf.sprintf "v%d" i) carried)))
           distinct)
      (Vector.to_list mm mat) in

  let quality label mat pub mm nn =
    let cl = Claim.live_claim Helios.gone Helios.gdec mm nn mat in
    let ev = { LeafStatus.ev_degenerate = None
             ; LeafStatus.ev_determined = None } in
    let c =
      LeafStatus.classify_leaf Helios.fzero Helios.fone Helios.fadd
        Helios.fmul Helios.fdec Helios.gone Helios.gdec mm nn mat pub cl ev in
    Printf.printf "      %-34s %-22s %s\n" label
      (match c.LeafStatus.lc_determination with
       | LeafStatus.Cert_determined -> "determined"
       | LeafStatus.Cert_degenerate _ -> "DEGENERATE"
       | LeafStatus.Cert_determination_undecided -> "undecided")
      (match c.LeafStatus.lc_vacuity with
       | LeafStatus.Cert_vacuous -> "VACUOUS"
       | LeafStatus.Cert_unsatisfiable _ -> "UNSATISFIABLE"
       | LeafStatus.Cert_vacuity_undecided -> "-") in

  (match rel with
   | Composition.Leaf (mm, nn, mat, pub) ->
       Printf.printf "   The incidence system, read off the matrix:\n";
       List.iter (fun l -> Printf.printf "      %s\n" l)
         (incidence_of mat mm nn);
       Printf.printf "\n   Only the zero vector solves it, so the relation\n";
       Printf.printf "   determines k, and the checker says so with a\n";
       Printf.printf "   certificate the extracted code verifies:\n\n";
       Printf.printf "      %-34s %-22s %s\n" "instance" "witness" "vacuity";
       quality "honest" mat pub mm nn
   | _ -> ());

  (* Now the instantiations that go wrong.  M is the batch composite,
     formed from the tokens the client sent, so unlike X it is not a
     fixed generator. *)
  let ident_batch = Helios.gone in
  let relM = get (PrivacyPass.compile_with
                    (PrivacyPass.dleq_genv base_x y ident_batch Helios.gone)
                    PrivacyPass.dleq_core) in
  let relXM = get (PrivacyPass.compile_with
                     (PrivacyPass.dleq_genv Helios.gone y ident_batch z)
                     PrivacyPass.dleq_core) in
  (match relM with
   | Composition.Leaf (mm, nn, mat, pub) -> quality "batch composite = identity" mat pub mm nn
   | _ -> ());
  (match relXM with
   | Composition.Leaf (mm, nn, mat, pub) -> quality "both bases = identity" mat pub mm nn
   | _ -> ());

  Printf.printf "\n   The middle line is the honest limit of the criterion.\n";
  Printf.printf "   With the batch composite at the identity the second\n";
  Printf.printf "   equation reads 1 = 1^k and says nothing, yet the first\n";
  Printf.printf "   still pins k -- so the relation does determine what it\n";
  Printf.printf "   claims, and 'determined' is the right answer to the\n";
  Printf.printf "   question asked.  What has been lost is the batch, and\n";
  Printf.printf "   that loss happened before the relation existed.\n\n";

  (* Which is what the instantiation check is for. *)
  let privs = Vector.of_list PrivacyPass.dleq_privs_list in
  let rec leaf_eqs (st : (Helios.coq_F, string) Dsl.stmt) =
    match st with
    | Dsl.SEqs eqs -> [ eqs ]
    | Dsl.SAnd (a, b) ->
        (match Dsl.leaves_only a, Dsl.leaves_only b with
         | Some la, Some lb -> [ la @ lb ]
         | _ -> leaf_eqs a @ leaf_eqs b)
    | Dsl.SOr (a, b) -> leaf_eqs a @ leaf_eqs b
    | Dsl.SThresh (_, l) -> List.concat_map leaf_eqs l in
  let faithful g =
    List.for_all
      (fun eqs ->
         DslInstantiate.faithful_tob Helios.fadd Helios.fmul Helios.fopp
           Helios.fdec Helios.gone Helios.gmul Helios.gpow Helios.gdec
           (fun a b -> String.equal a b) (big 1) privs g PrivacyPass.penvI eqs)
      (leaf_eqs PrivacyPass.dleq_core) in
  Printf.printf "7. The instantiation check, which looks at the environment\n";
  Printf.printf "   rather than the relation, and costs only group compares\n\n";
  Printf.printf "      %-34s %s\n" "honest"
    (string_of_bool (faithful genv));
  Printf.printf "      %-34s %s\n" "batch composite = identity"
    (string_of_bool
       (faithful (PrivacyPass.dleq_genv base_x y ident_batch Helios.gone)));
  Printf.printf "\n   It rejects the instance the relation check accepts,\n";
  Printf.printf "   because a base name has been sent to the identity.\n";
  Printf.printf "   That is Compiler/Instantiate.v, and it is why the two\n";
  Printf.printf "   checks live at different levels.\n\n";

  Printf.printf "   The first half says the proof convinces the verifier.\n";
  Printf.printf "   The second says the statement was worth proving.\n"
