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

  (* ---- 6. and the second half, on the same object ---- *)
  Printf.printf "6. The second half of the project, asked of the same leaf:\n";
  (match rel with
   | Composition.Leaf (mm, nn, mat, pub) ->
       let cl = Claim.live_claim Helios.gone Helios.gdec mm nn mat in
       let ev = { LeafStatus.ev_degenerate = None
                ; LeafStatus.ev_determined = None } in
       let c =
         LeafStatus.classify_leaf Helios.fzero Helios.fone Helios.fadd
           Helios.fmul Helios.fdec Helios.gone Helios.gdec mm nn mat pub cl ev in
       Printf.printf "      does it determine the key it claims?   %s\n"
         (match c.LeafStatus.lc_determination with
          | LeafStatus.Cert_determined -> "yes, with a certificate"
          | LeafStatus.Cert_degenerate _ -> "NO"
          | LeafStatus.Cert_determination_undecided -> "undecided")
   | _ -> ());
  Printf.printf "\n   The first half says the proof convinces the verifier.\n";
  Printf.printf "   The second says the statement was worth proving.\n"
