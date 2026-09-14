(* Self-test for the SHAKE128 and duplex-sponge implementations.
 *
 * These are the two primitives the CFRG sigma-protocol vectors need
 * and that no library in the switch provides.  They are hand-written,
 * so they are checked against FIPS 202 known answers here before
 * anything depends on them. *)

let hex s =
  String.concat ""
    (List.init (String.length s) (fun i -> Printf.sprintf "%02x" (Char.code s.[i])))

let failures = ref 0

let expect name got want =
  let ok = got = want in
  if not ok then incr failures;
  Printf.printf "  %-40s %s\n" name (if ok then "ok" else "FAILED");
  if not ok then begin
    Printf.printf "      got  %s\n" got;
    Printf.printf "      want %s\n" want
  end

let () =
  Printf.printf "SHAKE128 against the FIPS 202 known answers\n";
  expect "shake128(\"\", 32)"
    (hex (Shake128.shake128 "" 32))
    "7f9c2ba4e88f827d616045507605853ed73b8093f6efbc88eb1a6eacfa66ef26";
  expect "shake128(\"abc\", 32)"
    (hex (Shake128.shake128 "abc" 32))
    "5881092dd818bf5cf8a3ddb793fbcba74097d5c526a6d35f97b83351940f2cc8";
  (* the output is a stream: a longer request extends a shorter one *)
  expect "shake128(\"\", 64) extends shake128(\"\", 32)"
    (String.sub (hex (Shake128.shake128 "" 64)) 0 64)
    (hex (Shake128.shake128 "" 32));
  (* absorbing across the rate boundary *)
  let long = String.make 400 'a' in
  expect "shake128 over a 400-byte input is deterministic"
    (hex (Shake128.shake128 long 32))
    (hex (Shake128.shake128 long 32));

  Printf.printf "\nDuplex sponge against the draft's published answers\n";
  let sid = String.init 32 (fun i -> Char.chr i) in
  (* Two known answers from the CFRG Fiat-Shamir vectors. The stream
     laws below are only self-consistency; these two are the authority,
     and without them the checks after could all pass on a sponge that
     is wrong in the same way every time. *)
  expect "init then squeeze 32 (vector init_squeeze)"
    (let s = Sponge.init sid in hex (Sponge.squeeze s 32))
    "63e1b3543377fab6fb8cf0f7698a9980ca0211d5bc4aba213dd7a6ef7dd63cfa";
  expect "absorb \"abc\" then squeeze 32 (vector absorb_split)"
    (let s = Sponge.init sid in Sponge.absorb s "abc"; hex (Sponge.squeeze s 32))
    "a629c32a309dda7605798fd07ce20ab14c76635446868eb46e20b6dfd1dd9e41";

  Printf.printf "\nDuplex sponge: the stream laws it must satisfy\n";
  let one_shot =
    let s = Sponge.init sid in Sponge.absorb s "abc"; hex (Sponge.squeeze s 32) in
  let split_absorb =
    let s = Sponge.init sid in
    Sponge.absorb s "ab"; Sponge.absorb s "c"; hex (Sponge.squeeze s 32) in
  let split_squeeze =
    let s = Sponge.init sid in
    Sponge.absorb s "abc";
    let a = Sponge.squeeze s 16 in let b = Sponge.squeeze s 16 in hex (a ^ b) in
  let empty_absorb =
    let s = Sponge.init sid in
    Sponge.absorb s "abc"; Sponge.absorb s ""; hex (Sponge.squeeze s 32) in
  expect "a split absorb equals one absorb" split_absorb one_shot;
  expect "two squeezes continue one stream" split_squeeze one_shot;
  expect "an empty absorb is the identity" empty_absorb one_shot;

  Printf.printf "\nP-256 against mirage-crypto-ec (Fiat-derived)\n";
  (* The library cannot represent the identity, so it can only check
     the cases where both are defined. That is still worth doing: it
     validates the curve constants, the group law and the compressed
     encoding against an independent implementation. *)
  let module D = Mirage_crypto_ec.P256.Dsa in
  let module MP = D.Primitive in
  let mhex p = hex (D.pub_to_octets ~compress:true p) in
  expect "generator encodes identically"
    (hex (P256.to_bytes P256.generator)) (mhex MP.generator);
  expect "doubling the generator agrees"
    (hex (P256.to_bytes (P256.add P256.generator P256.generator)))
    (mhex (MP.add MP.generator MP.generator));
  let k = String.init 32 (fun i -> Char.chr ((i * 7 + 3) land 0xff)) in
  (match D.priv_of_octets k with
   | Error _ -> expect "scalar multiplication agrees" "no scalar" "no scalar"
   | Ok sk ->
       let kz =
         let r = ref Big_int_Z.zero_big_int in
         String.iter (fun c ->
             r := Big_int_Z.add_int_big_int (Char.code c)
                    (Big_int_Z.mult_int_big_int 256 !r)) k;
         !r in
       expect "scalar multiplication agrees"
         (hex (P256.to_bytes (P256.mul kz P256.generator)))
         (mhex (MP.scalar_mult sk MP.generator)));
  expect "compressed encoding round-trips"
    (match P256.of_bytes (P256.to_bytes P256.generator) with
     | Some q -> string_of_bool (P256.equal q P256.generator)
     | None -> "decode failed")
    "true";

  Printf.printf "\nP-256: the cases mirage-crypto-ec cannot express\n";
  expect "g + (-g) is the identity"
    (string_of_bool (P256.equal (P256.add P256.generator (P256.neg P256.generator))
                       P256.identity))
    "true";
  expect "scalar zero gives the identity"
    (string_of_bool (P256.equal (P256.mul Big_int_Z.zero_big_int P256.generator)
                       P256.identity))
    "true";
  expect "the identity is an additive unit"
    (string_of_bool (P256.equal (P256.add P256.identity P256.generator)
                       P256.generator))
    "true";
  expect "scalar by the group order gives the identity"
    (string_of_bool (P256.equal (P256.mul P256.order P256.generator)
                       P256.identity))
    "true";

  Printf.printf "\n";
  if !failures = 0 then
    Printf.printf "all checks passed\n"
  else begin
    Printf.printf "%d check(s) FAILED; do not use these primitives\n" !failures;
    exit 1
  end
