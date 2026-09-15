//! Does an instance that sigma-rs accepts necessarily determine its
//! witness?
//!
//!     P = x1*G + x2*G
//!     Q = x2*H + x3*H
//!
//! Three scalars, all used, both images non-identity, no repeated
//! column. Accepted. But the equations fix only x1+x2 and x2+x3, so
//! adding (1,-1,1) to any witness gives another witness for the same
//! statement. Both are exhibited and their images compared.
use curve25519_dalek::ristretto::RistrettoPoint as G;
use curve25519_dalek::scalar::Scalar;
use group::Group;
use sigma_proofs::linear_relation::{Instance, LinearRelation};

fn build(w: [u64; 3]) -> LinearRelation<G> {
    let mut r = LinearRelation::<G>::new();
    let [x1, x2, x3] = r.allocate_scalars();
    let g = r.allocate_element();
    let h = r.allocate_element();
    r.set_element(g, G::generator());
    r.set_element(h, G::generator() * Scalar::from(7u64));
    let _p = r.allocate_eq(g * x1 + g * x2);
    let _q = r.allocate_eq(h * x2 + h * x3);
    let s: Vec<Scalar> = w.iter().map(|v| Scalar::from(*v)).collect();
    r.compute_image(&s).expect("image computable");
    r
}

#[test]
fn accepted_yet_has_two_witnesses() {
    let a = build([3, 5, 11]);
    let b = build([4, 4, 12]); // = (3,5,11) + (1,-1,1)

    let ia = Instance::try_from(&a).expect("sigma-rs accepted the instance");
    let ib = Instance::try_from(&b).expect("sigma-rs accepted the instance");
    assert_eq!(ia.image(), ib.image(), "witnesses disagree on the image");

    println!("sigma-rs validation : ACCEPTED");
    println!("witness A           : (3, 5, 11)");
    println!("witness B           : (4, 4, 12)");
    println!("images              : identical");
}
