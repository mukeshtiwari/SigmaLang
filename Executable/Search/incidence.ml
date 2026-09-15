(* Finding the certificates that Compiler/Determined.v and
   Compiler/IncidenceDecide.v check.
 *
 * Nothing here is trusted.  Whatever this emits is handed to the
 * extracted checker, which rejects a wrong answer, so the only cost of
 * a bug in this file is a verdict of "undecided" that should have been
 * something else.  That is why it is ordinary OCaml and why it carries
 * no proof.
 *
 * The mathematics is one observation.  Write A for the incidence
 * matrix over the scalar field: one row per (equation, distinct
 * non-identity base occurring in that equation), one column per
 * secret, with a 1 where that secret sits on that base.  The incidence
 * solutions are exactly the orthogonal complement of the row space of
 * A, so for a claimed secret j,
 *
 *     every solution vanishes at j   <->   e_j lies in rowspace(A).
 *
 * One row reduction answers that for every j at once.  In reduced row
 * echelon form, e_j is in the row space exactly when some row *is*
 * e_j, and the combination producing it is the corresponding row of
 * the recorded transformation.  When no such row exists, the same
 * reduction yields a kernel vector that is nonzero at j.
 *
 * So a single elimination produces whichever certificate applies, and
 * never needs to answer "I do not know". *)

type 'f field = {
  zero : 'f;
  one : 'f;
  add : 'f -> 'f -> 'f;
  mul : 'f -> 'f -> 'f;
  sub : 'f -> 'f -> 'f;
  div : 'f -> 'f -> 'f;
  eq : 'f -> 'f -> bool;
}

type 'f verdict =
  | Degenerate of 'f array
      (** a solution of the incidence system, nonzero on a claimed
          position: the statement does not determine what it claims *)
  | Determined of 'f array array array
      (** one coefficient block per position; the block for a claimed
          j combines the equations into the form that reads off j *)
  | Undecided
      (** the claim is empty, or the statement has no equations *)

(* ---------- the incidence matrix ---------- *)

(* Row (i, j') of the incidence matrix is the equation for the base
   sitting at position j' of equation i.  Positions of equation i that
   share a base give the same equation, so only the first occurrence is
   kept; [rep] records which (i, j') each row came from, which is what
   lets a combination be written back in the coefficient layout the
   checker expects. *)
let incidence (type f g) (fd : f field) (geq : g -> g -> bool) (gid : g)
    (mat : g array array) : f array array * (int * int) array =
  let m = Array.length mat in
  let n = if m = 0 then 0 else Array.length mat.(0) in
  let rows = ref [] and reps = ref [] in
  for i = 0 to m - 1 do
    for j = 0 to n - 1 do
      let b = mat.(i).(j) in
      if not (geq b gid) then begin
        (* keep only the first position of equation i carrying b *)
        let earlier = ref false in
        for k = 0 to j - 1 do
          if geq mat.(i).(k) b then earlier := true
        done;
        if not !earlier then begin
          let r = Array.make n fd.zero in
          for k = 0 to n - 1 do
            if geq mat.(i).(k) b then r.(k) <- fd.one
          done;
          rows := r :: !rows;
          reps := (i, j) :: !reps
        end
      end
    done
  done;
  (Array.of_list (List.rev !rows), Array.of_list (List.rev !reps))

(* ---------- reduced row echelon form, with the transformation ---------- *)

(* Returns the reduced matrix, a transformation [t] with
   [t * a0 = a_reduced], and the pivot column of each row, or -1 for a
   zero row.  Every row operation is applied to [a] and [t] alike,
   which is the whole reason [t] tracks what was done. *)
let rref (type f) (fd : f field) (a0 : f array array) =
  let p = Array.length a0 in
  let n = if p = 0 then 0 else Array.length a0.(0) in
  let a = Array.map Array.copy a0 in
  let t =
    Array.init p (fun i ->
        Array.init p (fun j -> if i = j then fd.one else fd.zero)) in
  let pivot_of = Array.make p (-1) in
  let row = ref 0 in
  for col = 0 to n - 1 do
    if !row < p then begin
      let sel = ref (-1) in
      for r = p - 1 downto !row do
        if not (fd.eq a.(r).(col) fd.zero) then sel := r
      done;
      if !sel >= 0 then begin
        let s = !sel and r0 = !row in
        let tmp = a.(s) in a.(s) <- a.(r0); a.(r0) <- tmp;
        let tmt = t.(s) in t.(s) <- t.(r0); t.(r0) <- tmt;
        let pv = a.(r0).(col) in
        for k = 0 to n - 1 do a.(r0).(k) <- fd.div a.(r0).(k) pv done;
        for k = 0 to p - 1 do t.(r0).(k) <- fd.div t.(r0).(k) pv done;
        for r = 0 to p - 1 do
          if r <> r0 && not (fd.eq a.(r).(col) fd.zero) then begin
            let f = a.(r).(col) in
            for k = 0 to n - 1 do
              a.(r).(k) <- fd.sub a.(r).(k) (fd.mul f a.(r0).(k))
            done;
            for k = 0 to p - 1 do
              t.(r).(k) <- fd.sub t.(r).(k) (fd.mul f t.(r0).(k))
            done
          end
        done;
        pivot_of.(r0) <- col;
        incr row
      end
    end
  done;
  (a, t, pivot_of)

(* ---------- the verdict ---------- *)

(* A kernel vector that is nonzero at [j], given the reduced form.
   If [j] is a free column its own basis vector serves.  If [j] is a
   pivot whose row still carries a free column [c], the basis vector
   for [c] has the negated entry at [j], which is nonzero exactly when
   [e_j] failed to be in the row space. *)
let kernel_vector_at (type f) (fd : f field) (a : f array array)
    (pivot_of : int array) (n : int) (j : int) : f array option =
  let is_pivot = Array.make n (-1) in
  Array.iteri (fun r c -> if c >= 0 then is_pivot.(c) <- r) pivot_of;
  let basis_for c =
    (* the kernel basis vector for a free column c *)
    let v = Array.make n fd.zero in
    v.(c) <- fd.one;
    Array.iteri
      (fun r pc -> if pc >= 0 then v.(pc) <- fd.sub fd.zero a.(r).(c))
      pivot_of;
    v in
  if is_pivot.(j) < 0 then Some (basis_for j)
  else begin
    let r = is_pivot.(j) in
    let found = ref None in
    for c = n - 1 downto 0 do
      if is_pivot.(c) < 0 && not (fd.eq a.(r).(c) fd.zero) then
        found := Some (basis_for c)
    done;
    !found
  end

(* Given a statement and a claim, produce whichever certificate
   applies.  The caller hands the result to the extracted checker;
   nothing here is believed on its own authority. *)
let certify (type f g) (fd : f field) (geq : g -> g -> bool) (gid : g)
    (mat : g array array) (claim : bool array) : f verdict =
  let m = Array.length mat in
  let n = if m = 0 then 0 else Array.length mat.(0) in
  if n = 0 then Undecided
  else begin
    let a0, reps = incidence fd geq gid mat in
    let a, t, pivot_of = rref fd a0 in
    let p = Array.length a0 in
    (* a row of the reduced form equal to e_j names the combination *)
    let row_is_e j =
      let rec scan r =
        if r >= p then None
        else if pivot_of.(r) = j
             && (let only = ref true in
                 for k = 0 to n - 1 do
                   if k <> j && not (fd.eq a.(r).(k) fd.zero) then only := false
                 done; !only)
        then Some r else scan (r + 1) in
      scan 0 in
    (* the first claimed position the equations fail to pin down *)
    let unpinned = ref (-1) in
    for j = n - 1 downto 0 do
      if claim.(j) && row_is_e j = None then unpinned := j
    done;
    if !unpinned >= 0 then
      match kernel_vector_at fd a pivot_of n !unpinned with
      | Some v -> Degenerate v
      | None -> Undecided
    else begin
      (* every claimed position is pinned: emit one block per position,
         placing each combination weight on the representative of the
         equation it came from *)
      let blocks =
        Array.init n (fun j ->
            let block =
              Array.init m (fun _ -> Array.make n fd.zero) in
            (match row_is_e j with
             | None -> ()
             | Some r ->
                 Array.iteri
                   (fun k w ->
                      if not (fd.eq w fd.zero) then begin
                        let (i, jrep) = reps.(k) in
                        block.(i).(jrep) <- fd.add block.(i).(jrep) w
                      end)
                   t.(r));
            block) in
      Determined blocks
    end
  end
