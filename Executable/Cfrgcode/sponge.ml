(* The duplex sponge of draft-irtf-cfrg-fiat-shamir.
 *
 * The name is about the interface, not the construction.  Squeezing
 * yields the next bytes of
 *
 *     SHAKE128(session_id || zeros to the rate || everything absorbed)
 *
 * so consecutive squeezes continue one stream, a non-empty absorb
 * after a squeeze restarts it, and an empty absorb does nothing.  We
 * had assumed a raw-permutation duplex in overwrite mode and tested
 * four state layouts against the published answer before reading the
 * specification; none matched, because there is no such state. *)

let rate = 168

type t = { mutable absorbed : Buffer.t; mutable off : int; mutable live : bool }

(* [init sid] requires a 32-byte session id, padded to the rate. *)
let init (sid : string) : t =
  if String.length sid <> 32 then invalid_arg "session id must be 32 bytes";
  let b = Buffer.create 256 in
  Buffer.add_string b sid;
  Buffer.add_string b (String.make (rate - 32) '\000');
  { absorbed = b; off = 0; live = false }

(* An empty absorb is the identity: it must not restart the stream. *)
let absorb (s : t) (x : string) : unit =
  if String.length x > 0 then begin
    s.live <- false;
    Buffer.add_string s.absorbed x
  end

let squeeze (s : t) (n : int) : string =
  if not s.live then (s.off <- 0; s.live <- true);
  let all = Shake128.shake128 (Buffer.contents s.absorbed) (s.off + n) in
  let out = String.sub all s.off n in
  s.off <- s.off + n;
  out

(* DeriveSessionID: absorb the application tag under a fixed label. *)
let derive_session_id (tag : string) : string =
  let s = init "irtf-cfrg-fiat-shamir/session-id" in
  absorb s tag;
  squeeze s 32
