// Does this library accept a statement that does not determine its
// witness?
//
// The relation is an anonymous-credential showing with two attributes:
//
//     C = G1^a1 * G2^a2 * H^r
//
// written over four point *names* -- C, G1, G2, H -- and three scalar
// names. Nothing is wrong with that statement. What is wrong is an
// instantiation that binds G1 and G2 to the same group element, and
// this API lets the caller do that, because the points are supplied at
// run time and the names are only transcript labels.
//
// Under such an instantiation the relation pins a1 + a2 and not a1 and
// a2 separately, so a holder of the attributes (5, 0) can present as
// (3, 2) with a proof that verifies.
#![allow(non_snake_case)]

use curve25519_dalek::constants as dalek_constants;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use sha2::Sha512;
use zkp::toolbox::{prover::Prover, verifier::Verifier, SchnorrCS};
use zkp::Transcript;

fn credential<CS: SchnorrCS>(
    cs: &mut CS,
    a1: CS::ScalarVar,
    a2: CS::ScalarVar,
    r: CS::ScalarVar,
    C: CS::PointVar,
    G1: CS::PointVar,
    G2: CS::PointVar,
    H: CS::PointVar,
) {
    cs.constrain(C, vec![(a1, G1), (a2, G2), (r, H)]);
}

// Prove the showing for the given attributes, against bases G1 and G2.
fn show(
    a1: u64,
    a2: u64,
    r: Scalar,
    G1: RistrettoPoint,
    G2: RistrettoPoint,
    H: RistrettoPoint,
) -> (Vec<u8>, CompressedRistretto) {
    let (a1, a2) = (Scalar::from(a1), Scalar::from(a2));
    let C = G1 * a1 + G2 * a2 + H * r;

    let mut transcript = Transcript::new(b"Credential");
    let mut prover = Prover::new(b"Showing", &mut transcript);
    let var_a1 = prover.allocate_scalar(b"a1", a1);
    let var_a2 = prover.allocate_scalar(b"a2", a2);
    let var_r = prover.allocate_scalar(b"r", r);
    let (var_G1, _) = prover.allocate_point(b"G1", G1);
    let (var_G2, _) = prover.allocate_point(b"G2", G2);
    let (var_H, _) = prover.allocate_point(b"H", H);
    let (var_C, cmpr_C) = prover.allocate_point(b"C", C);
    credential(&mut prover, var_a1, var_a2, var_r, var_C, var_G1, var_G2, var_H);
    let proof = prover.prove_compact();
    (bincode::serialize(&proof).unwrap(), cmpr_C)
}

fn accepts(
    bytes: &[u8],
    C: CompressedRistretto,
    G1: RistrettoPoint,
    G2: RistrettoPoint,
    H: RistrettoPoint,
) -> bool {
    let proof: zkp::CompactProof = bincode::deserialize(bytes).unwrap();
    let mut transcript = Transcript::new(b"Credential");
    let mut verifier = Verifier::new(b"Showing", &mut transcript);
    let var_a1 = verifier.allocate_scalar(b"a1");
    let var_a2 = verifier.allocate_scalar(b"a2");
    let var_r = verifier.allocate_scalar(b"r");
    let var_G1 = verifier.allocate_point(b"G1", G1.compress()).unwrap();
    let var_G2 = verifier.allocate_point(b"G2", G2.compress()).unwrap();
    let var_H = verifier.allocate_point(b"H", H.compress()).unwrap();
    let var_C = verifier.allocate_point(b"C", C).unwrap();
    credential(&mut verifier, var_a1, var_a2, var_r, var_C, var_G1, var_G2, var_H);
    verifier.verify_compact(&proof).is_ok()
}

#[test]
fn two_attributes_on_one_generator_are_interchangeable() {
    let B = dalek_constants::RISTRETTO_BASEPOINT_POINT;
    let H = RistrettoPoint::hash_from_bytes::<Sha512>(b"H");
    let r = Scalar::from(999u64);

    // The instantiation the API permits: one generator, used twice.
    let G = B;

    let (proof_5_0, C_5_0) = show(5, 0, r, G, G, H);
    let (proof_3_2, C_3_2) = show(3, 2, r, G, G, H);

    // The two showings are of different attribute vectors, and they
    // produce the *same* commitment: the statement cannot tell them
    // apart.
    assert_eq!(C_5_0, C_3_2);

    // Both proofs verify against it, and the library raises nothing.
    assert!(accepts(&proof_5_0, C_5_0, G, G, H));
    assert!(accepts(&proof_3_2, C_5_0, G, G, H));

    // The repair is a generator each, and then the commitments differ.
    let G2 = RistrettoPoint::hash_from_bytes::<Sha512>(b"G2");
    let (_, C_ok_5_0) = show(5, 0, r, G, G2, H);
    let (_, C_ok_3_2) = show(3, 2, r, G, G2, H);
    assert_ne!(C_ok_5_0, C_ok_3_2);
}
