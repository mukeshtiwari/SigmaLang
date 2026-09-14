(* CMZ credential statements, exercised at realistic sizes.
 *
 * The statements, their compilation and the Fiat-Shamir binding are
 * in Examples/Cmz.v.  This file supplies what cannot be a theorem:
 * the group elements, the attribute values, and the randomness.
 *
 * Scope, stated plainly.  There is no published CMZ transcript to
 * check against, the way Helios has published ballots, so this is a
 * self-test: it builds instances that satisfy the relations, proves
 * them, and verifies.  What it demonstrates is that the compiler
 * handles CMZ's statements at CMZ's sizes with a real challenge
 * binding, and how the cost grows with the attribute count.  It does
 * not demonstrate that these equations constitute a sound credential
 * scheme; that is CMZ's design, and is argued in their paper. *)

open Helioslib

let big = Big_int_Z.big_int_of_int

let rnd () : Helios.coq_F =
  let a = Big_int_Z.big_int_of_string (string_of_int (Random.bits ())) in
  let b = Big_int_Z.big_int_of_string (string_of_int (Random.bits ())) in
  let c = Big_int_Z.big_int_of_string (string_of_int (Random.bits ())) in
  Helios.mk_field
    Big_int_Z.(add_big_int (mult_big_int a (big 1073741824))
                 (add_big_int (mult_big_int b (big 32768)) c))

let fzero = Helios.mk_field (big 0)
let get = function Some x -> x | None -> failwith "compilation failed"

(* SHA-256 for the challenge.  CMZ's own implementation uses a
 * transcript hash from the sigma-proofs crate; any hash serves, and
 * cmz_complete is proven for all of them. *)
let sha256_bigint (s : string) : Big_int_Z.big_int =
  let d = Cryptokit.hash_string (Cryptokit.Hash.sha256 ()) s in
  let r = ref Big_int_Z.zero_big_int in
  String.iter
    (fun c -> r := Big_int_Z.add_int_big_int (Char.code c)
                     (Big_int_Z.mult_int_big_int 256 !r))
    d;
  !r

(* Two independent generators for the Pedersen commitments.  A real
 * deployment derives these by hashing to the group, so that nobody
 * knows a discrete logarithm between them; here the second is the
 * election generator raised to a value that is then discarded, which
 * is good enough to exercise the arithmetic. *)
let base_a = Helios.gen
let base_b = Helios.pubkey

let pow = Helios.gpow
let mul = Helios.gmul

(* Build an environment from an association list, defaulting to the
 * identity for anything not mentioned. *)
let env_of tbl name =
  match List.assoc_opt name tbl with Some v -> v | None -> Helios.gone

let fenv_of tbl name =
  match List.assoc_opt name tbl with Some v -> v | None -> fzero

let idx base i = base ^ string_of_int i

(* ---------------- showing a credential ---------------- *)

(* Build an instance that satisfies the showing relation for k
 * hidden attributes: choose the secrets, then compute the public
 * commitments from them. *)
let show_instance k =
  let attrs = List.init k (fun _ -> rnd ()) in        (* the attributes *)
  let zs    = List.init k (fun _ -> rnd ()) in        (* their blinders *)
  let zq    = rnd () in
  let xs    = List.init k (fun _ -> rnd ()) in        (* issuer key shares *)
  let p     = pow base_a (rnd ()) in                  (* rerandomised MAC *)
  let bigx  = List.map (fun x -> pow base_a x) xs in  (* X_i = A ^ x_i *)
  (* C_i = P ^ a_i * A ^ z_i *)
  let cs = List.map2 (fun a z -> mul (pow p a) (pow base_a z)) attrs zs in
  (* V = B ^ zQ * prod X_i ^ z_i *)
  let v =
    List.fold_left2 (fun acc x z -> mul acc (pow x z))
      (pow base_b zq) bigx zs
  in
  let points =
    ("A", base_a) :: ("B", base_b) :: ("P", p) :: ("V", v)
    :: List.concat (List.mapi (fun i x -> [(idx "X" i, x); (idx "C" i, List.nth cs i)]) bigx)
  in
  let scalars =
    ("zQ", zq)
    :: List.concat (List.mapi (fun i a -> [(idx "a" i, a); (idx "z" i, List.nth zs i)]) attrs)
  in
  (env_of points, fenv_of scalars, [base_a; base_b; p; v])

(* ---------------- requesting issuance ---------------- *)

let issue_instance k =
  let attrs = List.init k (fun _ -> rnd ()) in
  let s = rnd () in
  let xs = List.init k (fun _ -> rnd ()) in
  let bigx = List.map (fun x -> pow base_a x) xs in
  (* C = A ^ s * prod X_j ^ a_j *)
  let c = List.fold_left2 (fun acc x a -> mul acc (pow x a)) (pow base_a s) bigx attrs in
  let points =
    ("A", base_a) :: ("B", base_b) :: ("C", c)
    :: List.mapi (fun i x -> (idx "X" i, x)) bigx
  in
  let scalars = ("s", s) :: List.mapi (fun i a -> (idx "a" i, a)) attrs in
  (env_of points, fenv_of scalars, [base_a; c])

(* ---------------- the issuer's own proof ---------------- *)

let issuer_instance () =
  let b = rnd () and x0 = rnd () in
  let p = pow base_a b in
  let pk0 = pow base_b x0 in
  let k = pow base_a (rnd ()) in           (* the blinded attribute carrier *)
  let r = mul (pow p x0) (pow k b) in      (* R = P ^ x0 * K ^ b *)
  let points =
    [("A", base_a); ("B", base_b); ("P", p); ("PK0", pk0); ("K", k); ("R", r)]
  in
  let scalars = [("b", b); ("x0", x0)] in
  (env_of points, fenv_of scalars, [base_a; base_b; p; pk0; k; r])

(* ---------------- proving and verifying ---------------- *)

(* A statement whose equations all conjoin compiles to a single leaf,
 * so its witness and its randomness are each one vector of scalars,
 * one entry per declared private variable. *)
let run label privs core genv wenv pre =
  let rel = get (Cmz.compile_with privs genv core) in
  let w : (Helios.coq_F, Helios.coq_G) Composition.comp_witness =
    Obj.magic (Cmz.scalars privs wenv) in
  let rnd_vec : (Helios.coq_F, Helios.coq_G) Composition.comp_rand =
    Obj.magic (Vector.of_list (List.map (fun _ -> rnd ()) privs)) in
  let t0 = Unix.gettimeofday () in
  let t = Cmz.cmz_prove sha256_bigint pre rel w rnd_vec in
  let ok = Cmz.cmz_verify sha256_bigint pre rel t in
  let dt = Unix.gettimeofday () -. t0 in
  Printf.printf "  %-34s verifies=%-5b  secrets=%-3d  %6.1f ms\n"
    label ok (List.length privs) (dt *. 1000.0);
  (rel, t, ok)

let () =
  Random.self_init ();
  Printf.printf "CMZ credential statements, compiled and proven\n";
  Printf.printf "  group: the 2048-bit IACR group (a deployment would use Ristretto)\n\n";

  Printf.printf "Showing a credential, by number of hidden attributes\n";
  List.iter
    (fun k ->
       let (genv, wenv, pre) = show_instance k in
       ignore (run (Printf.sprintf "show, %d attributes" k)
                 (Cmz.show_privs_list (big k)) (Cmz.show_core (big k)) genv wenv pre))
    [1; 2; 4; 6; 8];

  Printf.printf "\nRequesting issuance\n";
  List.iter
    (fun k ->
       let (genv, wenv, pre) = issue_instance k in
       ignore (run (Printf.sprintf "issue, %d attributes" k)
                 (Cmz.issue_privs_list (big k)) (Cmz.issue_core (big k)) genv wenv pre))
    [1; 4; 8];

  Printf.printf "\nThe issuer's own proof\n";
  let (genv, wenv, pre) = issuer_instance () in
  ignore (run "issuer key consistency" Cmz.issuer_privs_list Cmz.issuer_core genv wenv pre);

  Printf.printf "\nA proof offered against the wrong instance\n";
  let (genv, wenv, pre) = show_instance 4 in
  let (rel, t, _) =
    run "show, 4 attributes (honest)" (Cmz.show_privs_list (big 4)) (Cmz.show_core (big 4)) genv wenv pre in
  let (genv', _, pre') = show_instance 4 in
  let rel' = get (Cmz.compile_with (Cmz.show_privs_list (big 4)) genv' (Cmz.show_core (big 4))) in
  ignore rel;
  Printf.printf "  %-34s verifies=%-5b  (must be false)\n"
    "same proof, different credential" (Cmz.cmz_verify sha256_bigint pre' rel' t);
  Printf.printf "  %-34s verifies=%-5b  (must be false)\n"
    "same proof, instance not in hash" (Cmz.cmz_verify sha256_bigint pre rel' t)
