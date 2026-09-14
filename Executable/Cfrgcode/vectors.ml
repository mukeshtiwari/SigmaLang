(* Running the published CFRG test vectors.
 *
 * Two questions, in order.  Does the relation the vector states,
 * translated into our leaf form, satisfy the verification equation on
 * the published transcript?  And, hiding the equations and keeping
 * only the published elements, can we solve for the relation from the
 * transcript alone?
 *
 * The vectors are not bundled: pass the directory holding
 * sigma-proofs_Shake128_P256.json.  They are third-party data and
 * their licence has not been checked. *)

module B = Big_int_Z
open Yojson.Safe.Util

let unhex (h : string) : string =
  String.init (String.length h / 2)
    (fun i -> Char.chr (int_of_string ("0x" ^ String.sub h (2*i) 2)))

type entry = {
  relation : string; flavor : string; tag : string;
  instance : string; proof : string;
  expected : string;   (* "accept" or "reject"; only the invalid file sets it *)
  comment : string;
}

let load (path : string) : entry list =
  Yojson.Safe.from_file path |> to_list
  |> List.map (fun j ->
      { relation = (match j |> member "Relation" with
                    | `String v -> v
                    | _ -> (* the invalid file names the case, not the relation *)
                      (match j |> member "Id" with
                       | `String v ->
                           (match List.rev (String.split_on_char '/' v) with
                            | last :: _ -> last | [] -> v)
                       | _ -> "?"));
        flavor   = j |> member "Flavor"   |> to_string;
        tag      = j |> member "Tag"      |> to_string;
        instance = j |> member "Instance" |> to_string;
        proof    = j |> member "NargString" |> to_string;
        expected = (match j |> member "Expected" with
                    | `String v -> v | _ -> "accept");
        comment  = (match j |> member "Comment" with
                    | `String v -> v | _ -> "") })

(* ---------- question one: does the stated relation check out? ---------- *)

let check (e : entry) =
  let ib = unhex e.instance and pb = unhex e.proof in
  let inst = Cfrg.parse_instance ib in
  let leaf = Cfrg.to_leaf inst in
  let tr = Cfrg.parse_batchable inst pb in
  let nc = P256.ne * Array.length inst.equations in
  let c =
    Cfrg.derive_challenge ~tag:e.tag ~instance_bytes:ib
      ~commitment_bytes:(String.sub pb 0 nc) in
  (Cfrg.verify leaf tr c,
   Array.length inst.equations, Cfrg.num_secrets inst,
   Array.length inst.elements)

(* ---------- question two: solve for it ---------- *)

(* A pool entry is a readable name and its value.  Closure under sums
 * and differences is not decoration: elgamal_decryption proves against
 * a target that is a sum of two published elements, exactly as Helios
 * proves against beta times g inverse. *)
type pooled = { pname : string; pval : P256.t }

let pool_of (inst : Cfrg.instance) : pooled array =
  let base =
    { pname = "1"; pval = P256.identity }
    :: List.init (Array.length inst.elements)
         (fun i -> { pname = Printf.sprintf "e%d" i; pval = inst.elements.(i) }) in
  let combos =
    List.concat_map
      (fun a ->
         List.concat_map
           (fun b ->
              if a.pname = b.pname || P256.equal a.pval P256.identity
                 || P256.equal b.pval P256.identity then []
              else
                [ { pname = a.pname ^ "+" ^ b.pname; pval = P256.add a.pval b.pval };
                  { pname = a.pname ^ "-" ^ b.pname;
                    pval = P256.add a.pval (P256.neg b.pval) } ])
           base)
      base in
  let seen = Hashtbl.create 64 in
  List.filter
    (fun x ->
       let k = if P256.equal x.pval P256.identity then "inf"
               else P256.to_bytes x.pval in
       if Hashtbl.mem seen k then false else (Hashtbl.add seen k (); true))
    (base @ combos)
  |> Array.of_list

let key (p : P256.t) = if P256.equal p P256.identity then "inf" else P256.to_bytes p

(* Solve row [i].
 *
 * Enumerating every slot costs pool^n, which is 7.3 million for the
 * four-secret relation and unworkable.  Meet in the middle instead.
 * The equation is
 *
 *     prod_left * prod_right  =  a_i + c * P
 *
 * so tabulate the left half by its partial product, then enumerate the
 * right half together with the target and look up what the left half
 * would have to be.  Cost drops from pool^n to about
 * pool^ceil(n/2) + pool^(floor(n/2)+1): for four secrets over a pool of
 * 52 that is roughly 140 thousand instead of 7.3 million.
 *
 * This is exact, not heuristic.  Nothing is pruned, so a solution
 * cannot be missed; only the order of enumeration changes. *)
let solve_row (pool : pooled array) (tr : Cfrg.transcript) (c : B.big_int)
    (n : int) (i : int) =
  let np = Array.length pool in
  let powr =
    Array.init n (fun j -> Array.map (fun p -> P256.mul tr.resp.(j) p.pval) pool) in
  let nl = (n + 1) / 2 in                   (* left half: slots 0 .. nl-1 *)
  (* table: partial product of the left half -> the assignments reaching it *)
  let tbl = Hashtbl.create 4096 in
  let rec build j acc prod =
    if j = nl then
      Hashtbl.replace tbl (key prod)
        (List.rev acc :: (try Hashtbl.find tbl (key prod) with Not_found -> []))
    else
      for pj = 0 to np - 1 do
        build (j + 1) (pj :: acc) (P256.add prod powr.(j).(pj))
      done in
  build 0 [] P256.identity;
  (* enumerate the right half and the target, and look the left half up *)
  let out = ref [] in
  let rec walk j acc prod =
    if j = n then
      for pi = 0 to np - 1 do
        let want =
          P256.add (P256.add tr.comm.(i) (P256.mul c pool.(pi).pval))
            (P256.neg prod) in
        match Hashtbl.find_opt tbl (key want) with
        | None -> ()
        | Some lefts ->
            List.iter (fun l -> out := (l @ List.rev acc, pi) :: !out) lefts
      done
    else
      for pj = 0 to np - 1 do
        walk (j + 1) (pj :: acc) (P256.add prod powr.(j).(pj))
      done in
  walk nl [] P256.identity;
  !out

let render (pool : pooled array) (slots, pi) =
  let terms =
    List.filteri (fun _ _ -> true)
      (List.mapi (fun j pj ->
           if P256.equal pool.(pj).pval P256.identity then None
           else Some (Printf.sprintf "%s^x%d" pool.(pj).pname j)) slots)
    |> List.filter_map (fun x -> x) in
  Printf.sprintf "%s = %s"
    (if terms = [] then "1" else String.concat " * " terms) pool.(pi).pname

let solve (e : entry) ~(cap : int) =
  let ib = unhex e.instance and pb = unhex e.proof in
  let inst = Cfrg.parse_instance ib in
  let tr = Cfrg.parse_batchable inst pb in
  let m = Array.length inst.equations and n = Cfrg.num_secrets inst in
  let nc = P256.ne * m in
  let c =
    Cfrg.derive_challenge ~tag:e.tag ~instance_bytes:ib
      ~commitment_bytes:(String.sub pb 0 nc) in
  let pool = pool_of inst in
  (* cost estimate for meet in the middle, not for naive enumeration *)
  let np = float_of_int (Array.length pool) in
  let nl = (n + 1) / 2 in
  let work =
    int_of_float (np ** float_of_int nl +. np ** float_of_int (n - nl + 1)) in
  if work > cap then Error (Array.length pool, n, work)
  else Ok (List.init m (fun i -> solve_row pool tr c n i), pool)
