open Thresholdlib.ThresholdIns

let big = Big_int_Z.big_int_of_int
let str = Big_int_Z.string_of_big_int

(* demo randomness only; a deployment should draw from a CSPRNG *)
let rnd_field () : coq_F = mk_field (big (Random.int 2963))

let ten () =
  let r = Array.init 10 (fun _ -> rnd_field ()) in
  (r.(0), r.(1), r.(2), r.(3), r.(4), r.(5), r.(6), r.(7), r.(8), r.(9))

let () =
  Random.self_init ();
  Printf.printf "p = %s, q = %s\n" (str p) (str q);
  Printf.printf "statement: at least 2 of { H1 = G^x1, H2 = G^x2, H3 = G^x3 }\n";
  Printf.printf "prover knows x1 and x2 only\n\n";
  let (a, b, c, d, e, f, g, h, i, j) = ten () in
  let ch = rnd_field () in
  let (ok, n) = thr_run a b c d e f g h i j ch in
  Printf.printf "interactive run: verified = %b, wire elements = %s\n" ok (str n);
  let (a, b, c, d, e, f, g, h, i, j) = ten () in
  let ((ok, ok'), n) = thr_nizk_run a b c d e f g h i j in
  Printf.printf
    "NIZK (strong Fiat-Shamir, SHA-256): verified = %b, verified after wire round trip = %b, wire elements = %s\n"
    ok ok' (str n);
  let (a, b, c, d, e, f, g, h, i, j) = ten () in
  let z = rnd_field () in
  Printf.printf "NIZK with a tampered response: verified = %b\n"
    (thr_nizk_tamper a b c d e f g h i j z)

let () =
  let iters = 500 in
  let (a, b, c, d, e, f, g, h, i, j) = ten () in
  let t0 = Unix.gettimeofday () in
  let ok = ref true in
  for _ = 1 to iters do
    let ((v, v'), _) = thr_nizk_run a b c d e f g h i j in
    ok := !ok && v && v'
  done;
  let dt = Unix.gettimeofday () -. t0 in
  Printf.printf
    "\nbenchmark: %d NIZK prove+verify (with wire round trip) in %.3fs = %.0f/s (all ok: %b)\n"
    iters dt (float_of_int iters /. dt) !ok
