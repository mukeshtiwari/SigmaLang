From Stdlib Require Import Extraction
  ExtrOcamlBasic ExtrOcamlNativeString
  ExtrOcamlZBigInt ExtrOcamlNatBigInt.
From Utility Require Import Sha256.
From Examples Require Import Helios Cmz.
Extraction Blacklist String List Nat Ascii Byte Decimal.

(*
  Replace the verified SHA-256 with a native one, at extraction time
  only.  The Rocq development is unchanged and still uses the
  verified definition; this substitution affects the extracted code
  alone.

  Nothing formal is lost.  The completeness theorems of Nizk.v hold
  for an arbitrary hash, so they cover this one; and the security of
  the Fiat-Shamir transform rests on modelling the hash as a random
  oracle, which is an assumption about the function rather than a
  property of any particular implementation.  What the substitution
  does require, for a proof made by one implementation to verify
  under the other, is that the two compute the same function.  The
  driver checks that against a published test vector at startup.

  The verified definition folds the 32 digest bytes big-endian into a
  single number, so the replacement does the same.
*)
Extract Constant sha256_string =>
  "(fun s ->
      let d = Cryptokit.hash_string (Cryptokit.Hash.sha256 ()) s in
      let r = ref Big_int_Z.zero_big_int in
      String.iter
        (fun c ->
           r := Big_int_Z.add_int_big_int (Char.code c)
                  (Big_int_Z.mult_int_big_int 256 !r))
        d;
      !r)".

(*
  Likewise for the decimal rendering of a group element.  The
  verified definition converts a 617 digit number one digit at a
  time, and a single proof renders about ten group elements, twice.
  OCaml's big-integer printer computes the same string; Helios.v's
  g_to_string_gen pins what the verified definition yields, and the
  driver checks the replacement against it.
*)
Extract Constant g_to_string => "Big_int_Z.string_of_big_int".

Set Extraction Output Directory ".".
Separate Extraction Helios Cmz.
