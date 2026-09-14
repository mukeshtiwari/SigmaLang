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

  (* With a vectors directory, run the published CFRG vectors. *)
  if Array.length Sys.argv > 1 then begin
    let dir = Sys.argv.(1) in
    let path = Filename.concat dir "sigma-proofs_Shake128_P256.json" in
    if not (Sys.file_exists path) then begin
      Printf.printf "\nno vectors at %s\n" path
    end else begin
      let all = Vectors.load path in
      let batch = List.filter (fun e -> e.Vectors.flavor = "batchable") all in
      Printf.printf "\nCFRG P-256 vectors: does the stated relation check out\n";
      Printf.printf "  %-34s %3s %3s %4s  %s\n" "relation" "m" "n" "els" "our equation";
      List.iter
        (fun e ->
           let (ok, m, n, els) = Vectors.check e in
           if not ok then incr failures;
           Printf.printf "  %-34s %3d %3d %4d  %s\n" e.Vectors.relation m n els
             (if ok then "holds" else "FAILS"))
        batch;

      (* The incidence criterion, run for the first time on statements
         nobody here wrote.  This reports only; the accept/reject
         decision below still uses the old checker, so a disagreement
         shows up as a line rather than as a changed verdict. *)
      Printf.printf "\nStatement quality, by the incidence criterion\n";
      Printf.printf "  (Compiler/LeafStatus.v; the old checker is shown beside it)\n";
      Printf.printf "  %-34s %-10s %-14s %s\n"
        "relation" "witness" "vacuity" "old";
      let undecided = ref 0 and disagree = ref 0 in
      List.iter
        (fun e ->
           try
             let inst = Cfrg.parse_instance (Vectors.unhex e.Vectors.instance) in
             let leaf = Cfrg.to_leaf inst in
             let c = Verified.classify leaf in
             let nu = Verified.leaf_sound leaf
             and old = Verified.leaf_valid leaf in
             if Verified.determination_undecided c then incr undecided;
             if nu <> old then incr disagree;
             Printf.printf "  %-34s %s %s\n" e.Vectors.relation
               (Verified.describe c)
               (if old then "accepts" else "rejects")
           with _ -> Printf.printf "  %-34s (unparsed)\n" e.Vectors.relation)
        batch;
      Printf.printf "  %d of %d need the rank computation; %d disagree with the old checker\n"
        !undecided (List.length batch) !disagree;

      Printf.printf "\nThe same vectors, checked by the VERIFIED verifier\n";
      Printf.printf "  (extracted from Rocq, instantiated at our P-256; the code\n";
      Printf.printf "   is verified, the group it runs on is not)\n";
      List.iter
        (fun e ->
           let ib = Vectors.unhex e.Vectors.instance
           and pb = Vectors.unhex e.Vectors.proof in
           let inst = Cfrg.parse_instance ib in
           let leaf = Cfrg.to_leaf inst in
           let tr = Cfrg.parse_batchable inst pb in
           let nc = P256.ne * Array.length inst.Cfrg.equations in
           let c = Cfrg.derive_challenge ~tag:e.Vectors.tag ~instance_bytes:ib
                     ~commitment_bytes:(String.sub pb 0 nc) in
           let ok = Verified.verify leaf tr c in
           if not ok then incr failures;
           Printf.printf "  %-34s %s\n" e.Vectors.relation
             (if ok then "accepted" else "REJECTED"))
        batch;

      (* Compact proofs: the announcement is not transmitted, so the
         verifier recomputes it and checks that it implies the claimed
         challenge. The recomputation is the extracted compact_fill,
         which comp_compact_recover proves faithful. *)
      let compact_ok (e : Vectors.entry) : bool =
        try
          let ib = Vectors.unhex e.Vectors.instance
          and pb = Vectors.unhex e.Vectors.proof in
          let inst = Cfrg.parse_instance ib in
          let leaf = Cfrg.to_leaf inst in
          let m = Array.length inst.Cfrg.equations
          and n = Cfrg.num_secrets inst in
          if String.length pb <> 32 * (1 + n) then false
          else if not (Verified.leaf_valid leaf) then false
          else begin
            let c = Cfrg.scalar_be pb 0 in
            let resp = Array.init n (fun j -> Cfrg.scalar_be pb (32 * (j+1))) in
            let t = Verified.compact_fill leaf c resp in
            let comm = Verified.recovered_commitment m t in
            let cb =
              String.concat "" (Array.to_list (Array.map P256.to_bytes comm)) in
            let c' = Cfrg.derive_challenge ~tag:e.Vectors.tag
                       ~instance_bytes:ib ~commitment_bytes:cb in
            Big_int_Z.eq_big_int c c'
          end
        with _ -> false in
      let compact = List.filter (fun e -> e.Vectors.flavor = "compact") all in
      if compact <> [] then begin
        Printf.printf "\nCompact vectors: announcement recomputed, not sent\n";
        List.iter
          (fun e ->
             let ok = compact_ok e in
             if not ok then incr failures;
             Printf.printf "  %-34s %s\n" e.Vectors.relation
               (if ok then "accepted" else "REJECTED"))
          compact
      end;

      (* Negative controls. A verifier that accepts everything would have
         passed every check above; these are the ones that discriminate. *)
      let ipath = Filename.concat dir "sigma-proofs-invalid_Shake128_P256.json" in
      if Sys.file_exists ipath then begin
        Printf.printf "\nInvalid vectors, checked by the VERIFIED verifier\n";
        let inv = List.filter (fun e -> e.Vectors.flavor = "batchable")
                    (Vectors.load ipath) in
        (* What the incidence criterion says about the draft's own
           instance-validation cases.  These are the E-series: a
           secret appearing in no equation, image terms summing to the
           identity, a statement element that is the identity. *)
        Printf.printf "  statement quality on the instance-validation cases:\n";
        List.iter
          (fun e0 ->
             try
               let inst = Cfrg.parse_instance (Vectors.unhex e0.Vectors.instance) in
               let leaf = Cfrg.to_leaf inst in
               Printf.printf "    %-58s %s  old %s\n"
                 e0.Vectors.relation
                 (Verified.describe (Verified.classify leaf))
                 (if Verified.leaf_valid leaf then "accepts" else "rejects")
             with e ->
               (* say so rather than drop the case: a silently skipped
                  negative control looks exactly like a passing one *)
               Printf.printf "    %-58s unparsed: %s\n"
                 e0.Vectors.relation (Printexc.to_string e))
          (List.filter
             (fun e ->
                let c = e.Vectors.comment in
                String.length c >= 19 && String.sub c 0 19 = "Instance validation")
             inv);
        let wrong = ref 0 and shown = ref 0 in
        List.iter
          (fun e ->
             let verdict =
               try
                 let ib = Vectors.unhex e.Vectors.instance
                 and pb = Vectors.unhex e.Vectors.proof in
                 let inst = Cfrg.parse_instance ib in
                 let leaf = Cfrg.to_leaf inst in
                 let tr = Cfrg.parse_batchable inst pb in
                 let nc = P256.ne * Array.length inst.Cfrg.equations in
                 let c = Cfrg.derive_challenge ~tag:e.Vectors.tag
                           ~instance_bytes:ib
                           ~commitment_bytes:(String.sub pb 0 nc) in
                 if Verified.verify leaf tr c then "accept" else "reject"
               with _ ->
                 (* a malformed instance or proof is a rejection too *)
                 "reject" in
             let ok = verdict = e.Vectors.expected in
             if not ok then begin
               incr wrong;
               Printf.printf "  %-22s wanted %-6s got %-6s  %s\n"
                 e.Vectors.relation e.Vectors.expected verdict e.Vectors.comment
             end else if !shown < 3 then begin
               incr shown;
               Printf.printf "  %-22s wanted %-6s got %-6s\n"
                 e.Vectors.relation e.Vectors.expected verdict
             end)
          inv;
        Printf.printf "  %d batchable, %d disagreements\n"
          (List.length inv) !wrong;
        if !wrong > 0 then incr failures;
        (* the same for compact proofs, where rejection has to come from
           the challenge check rather than the equation *)
        let cinv = List.filter (fun e -> e.Vectors.flavor = "compact")
                     (Vectors.load ipath) in
        let cwrong = ref 0 in
        List.iter
          (fun e ->
             let verdict = if compact_ok e then "accept" else "reject" in
             if verdict <> e.Vectors.expected then begin
               incr cwrong;
               Printf.printf "  %-22s wanted %-6s got %-6s  %s\n"
                 e.Vectors.relation e.Vectors.expected verdict e.Vectors.comment
             end)
          cinv;
        Printf.printf "  %d compact, %d disagreements\n"
          (List.length cinv) !cwrong;
        if !cwrong > 0 then incr failures
      end;

      Printf.printf "\nSolving for the relation from the transcript alone\n";
      Printf.printf "  Given: the published elements and the proof.\n";
      Printf.printf "  Hidden: which element sits in which slot, and each target.\n\n";
      List.iter
        (fun e ->
           match Vectors.solve e ~cap:5_000_000 with
           | Error (np, n, work) ->
               Printf.printf "  %-34s skipped: pool %d, %d secrets, %d\n"
                 e.Vectors.relation np n work;
               Printf.printf "  %-34s assignments per row; needs sparsity-first\n" ""
           | Ok (rows, pool) ->
               let uniq = List.for_all (fun r -> List.length r = 1) rows in
               Printf.printf "  %-34s %s\n" e.Vectors.relation
                 (if uniq then "unique per row" else
                    "counts " ^ String.concat "," 
                      (List.map (fun r -> string_of_int (List.length r)) rows));
               if uniq then
                 List.iteri
                   (fun i r ->
                      Printf.printf "        row %d:  %s\n" i
                        (Vectors.render pool (List.hd r)))
                   rows)
        batch
    end
  end;

  Printf.printf "\n";
  if !failures = 0 then
    Printf.printf "all checks passed\n"
  else begin
    Printf.printf "%d check(s) FAILED; do not use these primitives\n" !failures;
    exit 1
  end
