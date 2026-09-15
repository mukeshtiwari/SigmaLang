(* Analysing a relation you supply.
 *
 * The four other drivers in this directory each answer the statement
 * quality question for one protocol, with the relation built into the
 * program.  This one reads the relation from a file, so a protocol we
 * have never seen can be checked without writing any OCaml.
 *
 * The two layers are visible in classify below.  Search.Incidence
 * hunts for a certificate and is ordinary untrusted OCaml;
 * LeafStatus.classify_leaf checks the certificate and is extracted
 * from Rocq.  A wrong guess from the first costs a verdict of
 * "undecided" and never a wrong verdict.
 *
 * Bases are written as names rather than as group elements, and that
 * is not a convenience.  Both questions the checker answers depend on
 * the relation only through which positions carry the same base and
 * which carry the identity: the incidence system is built from that
 * pattern alone, and so is the vacuity test.  Naming the bases says
 * exactly that much and no more, which is why the group instance is
 * the string type below, with "1" for the identity. *)

open Helioslib

(* ---------- the input format ---------- *)

(* secrets a1 a2 r        the secret scalars, in the column order used
 *                        by every equation below
 * claims  a1 a2 r        which of them the relation asserts it pins
 *                        down (optional; the default is all of them)
 * eq  C   g g h          one equation: the target, then one base per
 *                        secret in the declared order.  A base of 1
 *                        means that secret does not occur in this
 *                        equation, and a target of 1 means the target
 *                        is the identity.
 *
 * Anything after # is a comment, and blank lines are ignored. *)

type input =
  { secrets : string array
  ; claims : bool array
  ; targets : string array
  ; rows : string array array }

exception Bad of string

let strip_comment s =
  match String.index_opt s '#' with
  | None -> s
  | Some i -> String.sub s 0 i

let tokens s =
  List.filter (fun t -> t <> "")
    (String.split_on_char ' '
       (String.map (fun c -> if c = '\t' then ' ' else c) (strip_comment s)))

let parse (text : string) : input =
  let secrets = ref [||] and claimed = ref None in
  let targets = ref [] and rows = ref [] in
  let seen_secrets = ref false in
  let index_of name =
    let n = Array.length !secrets in
    let rec go i =
      if i >= n then raise (Bad (Printf.sprintf "unknown secret: %s" name))
      else if !secrets.(i) = name then i else go (i + 1) in
    go 0 in
  List.iteri
    (fun lineno line ->
       let where msg =
         raise (Bad (Printf.sprintf "line %d: %s" (lineno + 1) msg)) in
       match tokens line with
       | [] -> ()
       | "secrets" :: names ->
           if !seen_secrets then where "secrets declared twice";
           if names = [] then where "no secrets declared";
           seen_secrets := true;
           secrets := Array.of_list names
       | "claims" :: names ->
           if not !seen_secrets then where "claims before secrets";
           if !claimed <> None then where "claims declared twice";
           let c = Array.make (Array.length !secrets) false in
           List.iter (fun nm -> c.(index_of nm) <- true) names;
           claimed := Some c
       | "eq" :: target :: bases ->
           if not !seen_secrets then where "eq before secrets";
           let n = Array.length !secrets in
           if List.length bases <> n then
             where (Printf.sprintf "%d bases for %d secrets"
                      (List.length bases) n);
           targets := target :: !targets;
           rows := Array.of_list bases :: !rows
       | "eq" :: _ -> where "eq needs a target and one base per secret"
       | tok :: _ -> where (Printf.sprintf "unrecognised keyword: %s" tok))
    (String.split_on_char '\n' text);
  if not !seen_secrets then raise (Bad "no secrets line");
  if !rows = [] then raise (Bad "no equations");
  { secrets = !secrets
  ; claims =
      (match !claimed with
       | Some c -> c
       | None -> Array.make (Array.length !secrets) true)
  ; targets = Array.of_list (List.rev !targets)
  ; rows = Array.of_list (List.rev !rows) }

(* ---------- the two layers ---------- *)

(* The scalar field is the real one: the incidence system lives in the
   field the secrets are drawn from, so the elimination is exact. *)
let fd : Helios.coq_F Search.Incidence.field =
  { Search.Incidence.zero = Helios.fzero; one = Helios.fone;
    add = Helios.fadd; mul = Helios.fmul; sub = Helios.fsub;
    div = Helios.fdiv; eq = Helios.fdec }

let gid = "1"
let geq : string -> string -> bool = String.equal

let big = Big_int_Z.big_int_of_int
let vec l = Vector.of_list l
let vec_of_array a = Vector.of_list (Array.to_list a)

(* the untrusted half *)
let evidence_for (mat : string array array) (claim : bool array) =
  match Search.Incidence.certify fd geq gid mat claim with
  | Search.Incidence.Degenerate v ->
      { LeafStatus.ev_degenerate = Some (vec_of_array v)
      ; LeafStatus.ev_determined = None }
  | Search.Incidence.Determined blocks ->
      { LeafStatus.ev_degenerate = None
      ; LeafStatus.ev_determined =
          Some (vec (List.map
                       (fun blk -> vec (List.map vec_of_array
                                          (Array.to_list blk)))
                       (Array.to_list blocks))) }
  | Search.Incidence.Undecided ->
      { LeafStatus.ev_degenerate = None; LeafStatus.ev_determined = None }

(* the verified half *)
let classify (inp : input) =
  let m = Array.length inp.rows and n = Array.length inp.secrets in
  let mat = vec (List.map vec_of_array (Array.to_list inp.rows)) in
  let pub = vec_of_array inp.targets in
  let cl = vec_of_array inp.claims in
  LeafStatus.classify_leaf
    Helios.fzero Helios.fone Helios.fadd Helios.fmul Helios.fdec
    gid geq
    (big m) (big n) mat pub cl
    (evidence_for inp.rows inp.claims)

(* ---------- reporting ---------- *)

(* A residue near the top of the field is a small negative number, and
   reads far better written that way: the credential's kernel vector is
   (-1, 1, 0), not (q-1, 1, 0). *)
let render_scalar (x : Helios.coq_F) =
  let v : Big_int_Z.big_int = x in
  let half = Big_int_Z.div_big_int Helios.q (big 2) in
  if Big_int_Z.gt_big_int v half
  then Big_int_Z.string_of_big_int (Big_int_Z.sub_big_int v Helios.q)
  else Big_int_Z.string_of_big_int v

let rec fin_to_int (f : Fin.t) =
  match f with Fin.F1 _ -> 0 | Fin.FS (_, g) -> 1 + fin_to_int g

let show_relation inp =
  Array.iteri
    (fun i row ->
       let terms =
         List.filteri (fun _ t -> t <> "")
           (Array.to_list
              (Array.mapi
                 (fun j b ->
                    if b = gid then ""
                    else Printf.sprintf "%s^%s" b inp.secrets.(j))
                 row)) in
       Printf.printf "    %s = %s\n" inp.targets.(i)
         (if terms = [] then "1" else String.concat " * " terms))
    inp.rows

let report inp =
  let m = Array.length inp.rows and n = Array.length inp.secrets in
  Printf.printf "Relation: %d equation%s over %d secret%s\n"
    m (if m = 1 then "" else "s") n (if n = 1 then "" else "s");
  show_relation inp;
  let claimed =
    List.filteri (fun j _ -> inp.claims.(j)) (Array.to_list inp.secrets) in
  Printf.printf "  claims to pin down: %s\n\n"
    (if claimed = [] then "nothing" else String.concat ", " claimed);
  let c = classify inp in
  (match c.LeafStatus.lc_determination with
   | LeafStatus.Cert_determined ->
       Printf.printf "  determination  DETERMINED\n";
       Printf.printf "    a combination of the equations pins down each\n";
       Printf.printf "    claimed secret, and the checker verified it.\n"
   | LeafStatus.Cert_degenerate v ->
       let a = Array.of_list (Vector.to_list (big n) v) in
       Printf.printf "  determination  DEGENERATE\n";
       Printf.printf "    the relation does not pin down what it claims.\n";
       Printf.printf "    Adding this vector to any witness gives another\n";
       Printf.printf "    witness for the same targets:\n";
       Array.iteri
         (fun j s ->
            let d = render_scalar a.(j) in
            if d <> "0" then
              Printf.printf "      %s  %s %s\n" s
                (if String.length d > 0 && d.[0] = '-' then "-" else "+")
                (if String.length d > 0 && d.[0] = '-'
                 then String.sub d 1 (String.length d - 1) else d))
         inp.secrets
   | LeafStatus.Cert_determination_undecided ->
       Printf.printf "  determination  UNDECIDED\n";
       Printf.printf "    no certificate either way.  This is not\n";
       Printf.printf "    acceptance: the checker is declining to speak.\n");
  (match c.LeafStatus.lc_vacuity with
   | LeafStatus.Cert_vacuous ->
       Printf.printf "  vacuity        VACUOUS\n";
       Printf.printf "    every target is the identity, so the all-zero\n";
       Printf.printf "    witness works and the proof demonstrates nothing.\n"
   | LeafStatus.Cert_unsatisfiable i ->
       Printf.printf "  vacuity        UNSATISFIABLE\n";
       Printf.printf "    equation %d has every base the identity but a\n"
         (fin_to_int i + 1);
       Printf.printf "    target that is not, so no witness exists.\n"
   | LeafStatus.Cert_vacuity_undecided ->
       Printf.printf "  vacuity        no finding\n");
  (* What the statement establishes, whatever the verdict.  This is
     the specification the protocol actually implements: the linear
     combinations of the secrets whose value a proof fixes.  When it
     lists every secret separately the statement is determined, and
     that identity is what the acceptance certificate proves. *)
  let forms =
    Search.Incidence.established fd geq gid inp.rows in
  Printf.printf "\n  what a proof of this establishes knowledge of\n";
  if Array.length forms = 0 then
    Printf.printf "    nothing\n"
  else
    Array.iter
      (fun row ->
         (* rendered as a sum, with negative coefficients folded into
            the connective so the form reads the way it would be
            written by hand *)
         let buf = Buffer.create 32 in
         Array.iteri
           (fun j coeff ->
              let d = render_scalar coeff in
              if d <> "0" then begin
                let neg = String.length d > 0 && d.[0] = '-' in
                let mag = if neg then String.sub d 1 (String.length d - 1)
                          else d in
                if Buffer.length buf = 0 then
                  (if neg then Buffer.add_string buf "-")
                else
                  Buffer.add_string buf (if neg then " - " else " + ");
                if mag = "1" then Buffer.add_string buf inp.secrets.(j)
                else Buffer.add_string buf (mag ^ "*" ^ inp.secrets.(j))
              end)
           row;
         Printf.printf "    %s\n" (Buffer.contents buf))
      forms;
  Printf.printf "\n  verdict        %s\n"
    (if LeafStatus.leaf_acceptable (big m) (big n) c
     then "acceptable"
     else "NOT acceptable");
  LeafStatus.leaf_acceptable (big m) (big n) c

let usage = "usage: main.exe RELATION-FILE   (or - to read stdin)\n\n\
\  secrets a1 a2 r      the secret scalars, in column order\n\
\  claims  a1 a2 r      which ones the relation claims to pin down\n\
\                       (optional; the default is all of them)\n\
\  eq  C   g g h        one equation: the target, then one base per\n\
\                       secret.  1 is the identity in either position.\n"

let () =
  if Array.length Sys.argv < 2 then (print_string usage; exit 2);
  let path = Sys.argv.(1) in
  let text =
    if path = "-" then In_channel.input_all stdin
    else if Sys.file_exists path then
      In_channel.with_open_bin path In_channel.input_all
    else (Printf.eprintf "no such file: %s\n\n%s" path usage; exit 2) in
  match parse text with
  | exception Bad msg -> Printf.eprintf "%s\n\n%s" msg usage; exit 2
  | inp -> if report inp then exit 0 else exit 1
