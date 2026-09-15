**Title:** What is lost when instance validation stops rejecting
underdetermined relations — and a decidable characterisation

Not a bug report. #218 is about to change instance validation
deliberately, and this is an offer of theory for the decision rather
than an objection to it.

## What we noticed

In #218 the instance-validation vectors invert four of the five
E-cases relative to the version the current published vectors came
from:

| case | now | in #218 |
|---|---|---|
| E0 empty relation | — | accept |
| E1 scalar in no equation | reject | accept |
| E1b that scalar's response is free | reject | accept |
| E2 image terms summing to the identity | reject | accept |
| E3 an element is the identity | reject | accept |
| E4 index out of range | reject | reject |

and `instance.rs` keeps count bounds, index ranges, and the
every-element-used check.

We read this as a scoping decision rather than an oversight, and a
defensible one: the library proves what the caller asked for, and
deciding whether the caller asked for the right thing is the caller's
business. E1b says as much in its own comment.

The question that then has no published answer is what the caller is
now responsible for. That is what we have been working on.

## Why the question is not just "check for unused scalars"

Unused scalars are the visible end of it. The general condition is
that the linear map has a non-trivial kernel, and a kernel vector can
exist with no scalar unused and no two columns equal:

```
P = x1*G + x2*G
Q = x2*H + x3*H
```

Three scalars, all used, both images non-identity, no repeated column.
We ran it against `3e12c83` and against the #218 branch; both accept.
It also passes, by inspection of the checks rather than by running
them, the ten-check version the published vectors came from — that
revision no longer builds against the registry, since it was written
against an unpublished `spongefish`. But it constrains
only `x1 + x2` and `x2 + x3`, so `(3, 5, 11)` and `(4, 4, 12)` are
both witnesses for the same statement. Reproduction, as
`tests/underdetermined.rs` against `3e12c83`:

```rust
use curve25519_dalek::ristretto::RistrettoPoint as G;
use curve25519_dalek::scalar::Scalar;
use group::Group;
use sigma_proofs::linear_relation::{CanonicalLinearRelation, LinearRelation};

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
    let b = build([4, 4, 12]);            // = (3,5,11) + (1,-1,1)
    assert!(CanonicalLinearRelation::try_from(&a).is_ok());
    assert_eq!(a.image().unwrap(), b.image().unwrap());
}
```

The same holds on this branch. Against `3e12c83` the validation is
reached through `CanonicalLinearRelation::try_from`; on #218 it is
`Instance::try_from` and `image` is a field. Both accept, and both
give the same pair of witnesses.

Nothing is unsound here: the proof does demonstrate knowledge of a
solution. It matters only when the surrounding protocol treats the
scalars as separately meaningful — distinct attribute openings, key
shares — and that is precisely the judgement being handed to the
caller.

## What we can offer

We have machine-checked, in Rocq, a characterisation of exactly which
relations determine their witness:

- the question reduces to the linear map having trivial kernel, so
  there is one property rather than a growing list of shapes;
- the part of that kernel visible from the relation's pattern is a
  small linear system. For anything outside it we exhibit a legitimate
  reading of the same relation in which it is not a kernel vector, so
  a checker rejecting on that basis would be rejecting a relation
  that, read that way, is fine. Seeing more means computing discrete
  logarithms, so the line is permanent rather than a limit of our
  effort;
- whether a relation has *any* witness is separately out of reach:
  for `P = x*G` it is asking whether `P` lies in the subgroup `G`
  generates, so a checker that decided it would compute discrete
  logarithms. Not undecidable — the group is finite — but hard under
  exactly the assumption the protocol rests on, which is why a
  checker's honest verdicts are three rather than two.

Practically, a checker can be cheap and still carry proof: a rejection
carries the second witness, an acceptance carries a combination of
equations forcing each scalar, and both are verified in one pass. The
search that finds them need not be trusted — a wrong guess fails its
check. A sufficient condition covering every relation in your test
vectors is a few lines; the general case is a rank computation that
emits the same certificate.

Happy to open a PR with a certificate checker if that is useful, or to
leave it entirely in caller-land and just document the condition. We
would also value being told if the scoping decision in #218 is
intended to be permanent, since we are writing this up and would
rather describe it correctly.
