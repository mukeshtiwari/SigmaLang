(* Does the elimination find the certificates the cheap search could
   not?  Two cases decide it: a statement that is degenerate, and one
   that is sound but has no equation with pairwise distinct bases, so
   the sufficient test of IncidenceDecide.v declines on it. *)

open Helioslib

let fd : Helios.coq_F Search.Incidence.field =
  { Search.Incidence.zero = Helios.fzero; one = Helios.fone;
    add = Helios.fadd; mul = Helios.fmul; sub = Helios.fsub;
    div = Helios.fdiv; eq = Helios.fdec }

let g = Helios.gen
let h = Helios.gpow Helios.gen (Helios.mk_field (Big_int_Z.big_int_of_int 7))
let one_ = Helios.gone

let claim_all n = Array.make n true

let report name mat =
  let n = Array.length mat.(0) in
  match Search.Incidence.certify fd Helios.gdec one_ mat (claim_all n) with
  | Search.Incidence.Degenerate v ->
      (* render each entry as k or -k for a small k, else "?" *)
      let render x =
        let rec try_k k =
          if k > 6 then "?"
          else
            let kf = Helios.mk_field (Big_int_Z.big_int_of_int k) in
            if Helios.fdec x kf then string_of_int k
            else if Helios.fdec x (Helios.fsub Helios.fzero kf)
            then "-" ^ string_of_int k
            else try_k (k + 1) in
        try_k 0 in
      Printf.printf "  %-34s DEGENERATE  kernel = (%s)\n" name
        (String.concat ", " (Array.to_list (Array.map render v)))
  | Search.Incidence.Determined _ -> Printf.printf "  %-34s determined\n" name
  | Search.Incidence.Undecided -> Printf.printf "  %-34s undecided\n" name

let () =
  Printf.printf "Elimination over the scalar field\n";
  (* the credential: both attributes on the same generator *)
  report "C = g^a1 * g^a2 * h^r" [| [| g; g; h |] |];
  (* the repair *)
  report "C = g1^a1 * g2^a2 * h^r"
    [| [| g; Helios.gpow Helios.gen (Helios.mk_field (Big_int_Z.big_int_of_int 11)); h |] |];
  (* the counterexample every checklist accepts *)
  report "P = g^x1 g^x2 ; Q = h^x2 h^x3"
    [| [| g; g; one_ |]; [| one_; h; h |] |];
  (* the boundary case: no row has distinct bases, yet it is sound *)
  report "P = g^x1 g^x2 h^x3 ; Q = h^x1 g^x2 g^x3"
    [| [| g; g; h |]; [| h; g; g |] |]
