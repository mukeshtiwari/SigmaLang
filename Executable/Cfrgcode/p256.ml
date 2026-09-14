(* P-256 as a group, with an explicit point at infinity.
 *
 * mirage-crypto-ec has Fiat-derived P-256 and was the obvious
 * dependency, but its interface is ECDH and ECDSA rather than a group:
 * its point type is a public key, so the identity is not
 * representable.  Adding a point to its own negation raises
 * Invalid_argument, and the scalar zero is rejected.  Our search needs
 * all of that: the pool contains the identity, closure takes
 * differences that can land on it, and a matrix carries the identity
 * wherever a column is unused.  So the arithmetic is here, affine with
 * an explicit Inf.
 *
 * This computes on public values only, so it is deliberately plain
 * rather than constant-time.  main.ml cross-checks it against
 * mirage-crypto-ec on the cases where that library is defined, which
 * is the point of keeping the dependency. *)

(* Big_int_Z is a compatibility shim over zarith and has no modular
   exponentiation, so the raw Z module is used for that.  The names are
   kept apart deliberately: shadowing Z hid Z.powm the first time. *)
module B = Big_int_Z

let ( %! ) x m =
  let r = B.mod_big_int x m in
  if B.sign_big_int r < 0 then B.add_big_int r m else r

let powm x e m = Z.powm x e m

let of_hex h = B.big_int_of_string ("0x" ^ h)

let p = of_hex "FFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF"
let a = B.sub_big_int p (B.big_int_of_int 3)
let b = of_hex "5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B"
let order = of_hex "FFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551"
let gx = of_hex "6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296"
let gy = of_hex "4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5"

type t = Inf | Aff of Big_int_Z.big_int * Big_int_Z.big_int

let generator = Aff (gx, gy)
let identity = Inf

let ( *% ) x y = ( %! ) (B.mult_big_int x y) p
let ( +% ) x y = ( %! ) (B.add_big_int x y) p
let ( -% ) x y = ( %! ) (B.sub_big_int x y) p
let inv_mod x = Z.powm x (B.sub_big_int p (B.big_int_of_int 2)) p

let equal q r = match q, r with
  | Inf, Inf -> true
  | Aff (x1,y1), Aff (x2,y2) -> B.eq_big_int x1 x2 && B.eq_big_int y1 y2
  | _ -> false

let add q r = match q, r with
  | Inf, x | x, Inf -> x
  | Aff (x1,y1), Aff (x2,y2) ->
      if B.eq_big_int x1 x2 && B.eq_big_int (y1 +% y2) B.zero_big_int then Inf
      else
        let l =
          if B.eq_big_int x1 x2 && B.eq_big_int y1 y2 then
            ((B.big_int_of_int 3 *% x1 *% x1) +% a) *% inv_mod (B.big_int_of_int 2 *% y1)
          else (y2 -% y1) *% inv_mod (x2 -% x1) in
        let x3 = (l *% l) -% x1 -% x2 in
        Aff (x3, ((l *% (x1 -% x3)) -% y1))

let neg = function Inf -> Inf | Aff (x,y) -> Aff (x, ( %! ) (B.minus_big_int y) p)

(* [mul k q] is q added to itself k times, for any k including zero. *)
let mul k q =
  let k = ( %! ) k order in
  let rec go acc base k =
    if B.sign_big_int k = 0 then acc
    else
      let acc = if B.eq_big_int (( %! ) k (B.big_int_of_int 2)) B.unit_big_int
                then add acc base else acc in
      go acc (add base base) (B.div_big_int k (B.big_int_of_int 2)) in
  go Inf q k

(* SEC1 compressed encoding, 33 bytes.  The identity has no compressed
   encoding in SEC1; we never serialize it, and decoding rejects
   anything that is not a curve point. *)
let ne = 33

let to_bytes = function
  | Inf -> invalid_arg "the identity has no compressed encoding"
  | Aff (x, y) ->
      let s = Bytes.create ne in
      Bytes.set s 0
        (if B.eq_big_int (( %! ) y (B.big_int_of_int 2)) B.zero_big_int
         then '\002' else '\003');
      let xs = B.string_of_big_int x in
      ignore xs;
      for i = 0 to 31 do
        let sh = 8 * (31 - i) in
        let byte =
          B.int_of_big_int
            (( %! ) (B.shift_right_big_int x sh) (B.big_int_of_int 256)) in
        Bytes.set s (1 + i) (Char.chr byte)
      done;
      Bytes.to_string s

let of_bytes (s : string) : t option =
  if String.length s <> ne then None
  else if s.[0] <> '\002' && s.[0] <> '\003' then None
  else begin
    let x = ref B.zero_big_int in
    for i = 1 to 32 do
      x := B.add_big_int (B.mult_int_big_int 256 !x)
             (B.big_int_of_int (Char.code s.[i]))
    done;
    let x = !x in
    let y2 = ((x *% x *% x) +% (a *% x)) +% b in
    let y = powm y2 (B.div_big_int (B.add_big_int p B.unit_big_int)
                         (B.big_int_of_int 4)) p in
    if not (B.eq_big_int (y *% y) y2) then None
    else
      let odd = B.eq_big_int (( %! ) y (B.big_int_of_int 2)) B.unit_big_int in
      let want_odd = s.[0] = '\003' in
      Some (Aff (x, if odd = want_odd then y else ( %! ) (B.minus_big_int y) p))
  end
