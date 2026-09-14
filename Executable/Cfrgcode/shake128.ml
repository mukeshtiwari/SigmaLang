(* SHAKE128 and the CFRG Fiat-Shamir duplex sponge.
 *
 * Written rather than depended upon: no library in the opam switch has
 * SHAKE.  Cryptokit and digestif both offer fixed-output SHA-3, which
 * is a different construction, and neither offers an extendable-output
 * function.  SHAKE128 is Keccak-f[1600] with a 168-byte rate, the
 * domain separator 0x1F, and a squeeze loop.
 *
 * Hand-written cryptographic code is normally a bad idea.  It is
 * defensible here because the standard supplies known-answer vectors,
 * so this is checked against an authority before it is used: main.ml
 * runs the FIPS 202 vectors at start-up and refuses to continue if any
 * of them fails.
 *
 * Not constant-time.  It computes a public challenge from public
 * values, so there is no secret to leak through timing. *)

(* SHAKE128, from FIPS 202.
 *
 * Written rather than depended upon, because no library in the switch
 * has it: cryptokit and digestif both offer fixed-output SHA-3, which
 * is a different construction, and neither offers an extendable-output
 * function. SHAKE128 is Keccak-f[1600] with a 168-byte rate, the
 * domain separator 0x1F, and a squeeze loop.
 *
 * Hand-written cryptographic code is normally a bad idea. It is
 * defensible here only because the CFRG draft ships known-answer
 * vectors, so this is checked against an authority before it is used
 * for anything. *)

let rotl (x : int64) (n : int) : int64 =
  if n = 0 then x
  else Int64.logor (Int64.shift_left x n) (Int64.shift_right_logical x (64 - n))

let rc = [|
  0x0000000000000001L; 0x0000000000008082L; 0x800000000000808AL;
  0x8000000080008000L; 0x000000000000808BL; 0x0000000080000001L;
  0x8000000080008081L; 0x8000000000008009L; 0x000000000000008AL;
  0x0000000000000088L; 0x0000000080008009L; 0x000000008000000AL;
  0x000000008000808BL; 0x800000000000008BL; 0x8000000000008089L;
  0x8000000000008003L; 0x8000000000008002L; 0x8000000000000080L;
  0x000000000000800AL; 0x800000008000000AL; 0x8000000080008081L;
  0x8000000000008080L; 0x0000000080000001L; 0x8000000080008008L |]

(* rotation offsets, indexed by lane x + 5y *)
let rho = [|
   0;  1; 62; 28; 27;
  36; 44;  6; 55; 20;
   3; 10; 43; 25; 39;
  41; 45; 15; 21;  8;
  18;  2; 61; 56; 14 |]

let keccak_f (a : int64 array) : unit =
  let b = Array.make 25 0L and c = Array.make 5 0L and d = Array.make 5 0L in
  for round = 0 to 23 do
    (* theta *)
    for x = 0 to 4 do
      c.(x) <- Int64.logxor a.(x)
                 (Int64.logxor a.(x+5)
                    (Int64.logxor a.(x+10) (Int64.logxor a.(x+15) a.(x+20))))
    done;
    for x = 0 to 4 do
      d.(x) <- Int64.logxor c.((x+4) mod 5) (rotl c.((x+1) mod 5) 1)
    done;
    for y = 0 to 4 do
      for x = 0 to 4 do
        a.(x + 5*y) <- Int64.logxor a.(x + 5*y) d.(x)
      done
    done;
    (* rho and pi *)
    for y = 0 to 4 do
      for x = 0 to 4 do
        b.(y + 5*((2*x + 3*y) mod 5)) <- rotl a.(x + 5*y) rho.(x + 5*y)
      done
    done;
    (* chi *)
    for y = 0 to 4 do
      for x = 0 to 4 do
        a.(x + 5*y) <-
          Int64.logxor b.(x + 5*y)
            (Int64.logand (Int64.lognot b.(((x+1) mod 5) + 5*y))
               b.(((x+2) mod 5) + 5*y))
      done
    done;
    (* iota *)
    a.(0) <- Int64.logxor a.(0) rc.(round)
  done

let rate = 168  (* SHAKE128: 1600 bits state, 256-bit capacity *)

let lane_get (a : int64 array) (i : int) : int =
  Int64.to_int (Int64.logand (Int64.shift_right_logical a.(i/8) ((i mod 8)*8)) 0xFFL)

let lane_xor (a : int64 array) (i : int) (byte : int) : unit =
  a.(i/8) <- Int64.logxor a.(i/8)
               (Int64.shift_left (Int64.of_int byte) ((i mod 8)*8))

(* [shake128 input outlen] is the first [outlen] bytes of the XOF. *)
let shake128 (input : string) (outlen : int) : string =
  let a = Array.make 25 0L in
  let n = String.length input in
  let full = n / rate in
  for blk = 0 to full - 1 do
    for i = 0 to rate - 1 do
      lane_xor a i (Char.code input.[blk*rate + i])
    done;
    keccak_f a
  done;
  (* final partial block, padded pad10*1 with the SHAKE domain
     separator 0x1F *)
  let tailn = n - full*rate in
  for i = 0 to tailn - 1 do
    lane_xor a i (Char.code input.[full*rate + i])
  done;
  lane_xor a tailn 0x1F;
  lane_xor a (rate - 1) 0x80;
  keccak_f a;
  (* squeeze *)
  let out = Bytes.create outlen in
  let produced = ref 0 in
  while !produced < outlen do
    let take = min rate (outlen - !produced) in
    for i = 0 to take - 1 do
      Bytes.set out (!produced + i) (Char.chr (lane_get a i))
    done;
    produced := !produced + take;
    if !produced < outlen then keccak_f a
  done;
  Bytes.to_string out
