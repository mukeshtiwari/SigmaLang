(* The CFRG sigma-protocol wire format, and the translation into the
 * leaf form our compiler uses.
 *
 * Written from draft-irtf-cfrg-sigma-protocols and its Fiat-Shamir
 * companion.  Everything here is parsing and arithmetic on public
 * values; none of it is a proof.
 *
 * The draft's relation is slightly richer than our Leaf: a term
 * carries a scalar coefficient, and a target is a linear combination
 * of elements rather than a single one.  Both fold away.  A term
 * (secret, element, coefficient) contributes element^coefficient to
 * the matrix entry for that secret, and several terms on one secret
 * multiply together; a target is the product of its own terms.  So the
 * translation is total, which is why every relation the draft tests
 * fits our leaf. *)

module B = Big_int_Z

(* ---------- scalars ---------- *)

(* Group scalars serialize big-endian: the draft's byte-order carve-out
   for curves whose defining standards fix that order.  The Fiat-Shamir
   codec is little-endian, which is why the two appear together below
   and must not be confused. *)
let scalar_be (s : string) (off : int) : B.big_int =
  let r = ref B.zero_big_int in
  for i = 0 to 31 do
    r := B.add_int_big_int (Char.code s.[off + i]) (B.mult_int_big_int 256 !r)
  done;
  !r

let uint_le (s : string) (off : int) (width : int) : int =
  let r = ref 0 in
  for i = width - 1 downto 0 do r := (!r * 256) + Char.code s.[off + i] done;
  !r

(* DecodeUint: squeezed bytes read little-endian, then reduced. *)
let decode_scalar_le (s : string) : B.big_int =
  let r = ref B.zero_big_int in
  for i = String.length s - 1 downto 0 do
    r := B.add_int_big_int (Char.code s.[i]) (B.mult_int_big_int 256 !r)
  done;
  B.mod_big_int !r P256.order

(* ---------- the relation ---------- *)

type term = { t_secret : int; t_elem : int; t_coeff : B.big_int }
type eqn  = { e_image : (int * B.big_int) list; e_terms : term list }

type instance = { elements : P256.t array; equations : eqn array }

exception Bad of string

(* SerializeLinearRelation, read backwards.  Element zero is the
   generator and is never serialized, so the element list starts there
   and the encoded points follow. *)
let parse_instance (buf : string) : instance =
  let pos = ref 0 in
  let u32 () =
    if !pos + 4 > String.length buf then raise (Bad "truncated header");
    let v = uint_le buf !pos 4 in pos := !pos + 4; v in
  let coeff () =
    if !pos + 32 > String.length buf then raise (Bad "truncated coefficient");
    let v = scalar_be buf !pos in pos := !pos + 32; v in
  let n_eq = u32 () in
  if n_eq = 0 then raise (Bad "no equations");
  let equations =
    Array.init n_eq (fun _ ->
        let n_img = u32 () in
        let image = List.init n_img (fun _ -> let e = u32 () in (e, coeff ())) in
        let n_trm = u32 () in
        let terms =
          List.init n_trm (fun _ ->
              let s = u32 () in let e = u32 () in
              { t_secret = s; t_elem = e; t_coeff = coeff () }) in
        { e_image = image; e_terms = terms }) in
  let rest = String.length buf - !pos in
  if rest mod P256.ne <> 0 then raise (Bad "trailing bytes are not whole points");
  let extra = rest / P256.ne in
  let elements =
    Array.init (extra + 1) (fun i ->
        if i = 0 then P256.generator
        else
          match P256.of_bytes (String.sub buf (!pos + (i-1) * P256.ne) P256.ne) with
          | Some p -> p
          | None -> raise (Bad "element is not a curve point")) in
  { elements; equations }

let num_secrets (inst : instance) : int =
  Array.fold_left
    (fun acc eq ->
       List.fold_left (fun a t -> max a (t.t_secret + 1)) acc eq.e_terms)
    0 inst.equations

(* ---------- the leaf form ---------- *)

type leaf = { mat : P256.t array array; target : P256.t array }

let to_leaf (inst : instance) : leaf =
  let m = Array.length inst.equations and n = num_secrets inst in
  let mat = Array.make_matrix m n P256.identity in
  let target = Array.make m P256.identity in
  Array.iteri
    (fun i eq ->
       List.iter
         (fun t ->
            mat.(i).(t.t_secret) <-
              P256.add mat.(i).(t.t_secret)
                (P256.mul t.t_coeff inst.elements.(t.t_elem)))
         eq.e_terms;
       List.iter
         (fun (ei, c) ->
            target.(i) <- P256.add target.(i) (P256.mul c inst.elements.(ei)))
         eq.e_image)
    inst.equations;
  { mat; target }

(* ---------- the transcript ---------- *)

type transcript = { comm : P256.t array; resp : B.big_int array }

let parse_batchable (inst : instance) (proof : string) : transcript =
  let m = Array.length inst.equations and n = num_secrets inst in
  let nc = P256.ne * m in
  if String.length proof <> nc + 32 * n then raise (Bad "wrong proof length");
  let comm =
    Array.init m (fun i ->
        match P256.of_bytes (String.sub proof (i * P256.ne) P256.ne) with
        | Some p -> p
        | None -> raise (Bad "commitment is not a curve point")) in
  let resp = Array.init n (fun j -> scalar_be proof (nc + 32 * j)) in
  { comm; resp }

(* ---------- the challenge ---------- *)

(* DeriveChallenge: a sponge keyed by the session id, absorbing the
   serialized instance and then the serialized commitment.  The
   instance bytes are the ones we were handed, not a re-serialization,
   so a disagreement about the encoding shows up as a failed proof
   rather than being papered over. *)
let derive_challenge ~(tag : string) ~(instance_bytes : string)
    ~(commitment_bytes : string) : B.big_int =
  let sid = Sponge.derive_session_id tag in
  let s = Sponge.init sid in
  Sponge.absorb s instance_bytes;
  Sponge.absorb s commitment_bytes;
  decode_scalar_le (Sponge.squeeze s (32 + 16))

(* ---------- verification ---------- *)

(* The draft's equation, which is also ours: the matrix raised to the
   responses equals the announcement times the target raised to the
   challenge. *)
let verify (l : leaf) (t : transcript) (c : B.big_int) : bool =
  let m = Array.length l.mat in
  let ok = ref true in
  for i = 0 to m - 1 do
    let lhs = ref P256.identity in
    Array.iteri
      (fun j e -> lhs := P256.add !lhs (P256.mul t.resp.(j) e))
      l.mat.(i);
    let rhs = P256.add t.comm.(i) (P256.mul c l.target.(i)) in
    if not (P256.equal !lhs rhs) then ok := false
  done;
  !ok
