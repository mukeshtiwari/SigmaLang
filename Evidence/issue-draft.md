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

## Why we think #218 is moving the right way

Since first drafting this we proved something that bears directly on
the decision, and it is the reason we are sending this rather than
leaving it.

Adding equations to a relation can only help it determine its witness:
constraints accumulate. So any relation that fails to determine can be
repaired by saying more — and the repair leaves untouched whatever
shape a checklist objected to. Concretely, append one equation per
scalar, each on a fresh base. The credential

    C = x1*G + x2*G + x3*H

is underdetermined and repeats a base. Add

    D = x1*G + x2*K

and it determines all three scalars, with the repeated base still
sitting in the first equation.

It follows that no rule of the form *reject because an equation looks
like this* can be sound, whatever shape it names, because that shape
occurs in relations that are perfectly fine. That covers E2 (image
terms summing to the identity) and E3 (an element is the identity):
both are conditions on something being **present**, so both were
unsound as stated, and removing them is correct rather than merely a
scoping choice.

It does not cover E1. "A declared scalar occurs in **no** equation" is
a condition on something being **absent** everywhere, so adding an
equation destroys the pattern instead of preserving it. That rule is
sound and we think you are right to keep it.

So our reading of #218 is that it is removing the entries that could
never have worked and keeping the one that does. If that is the
intent, the theorem says it is correct.

## One disagreement, so you hear it from us

We ran your negative vectors: 23 batchable cases and 11 compact. Our
verdicts match the published expectation everywhere except E0, the
empty relation, which your vectors expect to be accepted and we
reject.

We think this is a difference of position rather than a defect on
either side. A relation with no equations is satisfied by every
witness, so a proof of it demonstrates nothing, which is what our
vacuity check reports. Your position — that a well-formed relation
with nothing to say is still well-formed — is equally coherent. The
two answer different questions. We mention it only so that a
mismatch, if you ever run our checker against your suite, is not a
surprise.

(These are the vectors at `92c63fc`, which is the last revision whose
instance encoding our reader parses. `main` now carries five relations
in a different wire format and no invalid file, so we have kept a copy
in our artefact to keep the comparison reproducible.)

## What a checker could tell your users

The more useful output is not a verdict. Because a proof establishes
knowledge of a coset of the kernel — no less, since extraction gives a
member of it, and no more, since the members produce identical
transcripts — what a relation establishes is exactly the linear
combinations of the scalars that are constant on that coset. Those are
computable, and the elimination that produces a certificate already
produces them.

So instead of *rejected*, a library could say:

    you wrote:     C = x1*G + x2*G + x3*H
    this proves:   x1 + x2
                   x3

For the relation at the top of this issue it prints `x1 - x3` and
`x2 + x3`: two combinations, where the author wrote three scalars. For
a well-formed relation it prints each scalar on its own line, and that
listing is the acceptance certificate.

We suspect that is the form in which this is worth having in a
library, whatever you decide about validation: not a gate that rejects
people's relations, but an answer to "what does my proof actually
prove".

## What we are asking

Nothing urgent, and no action if you would rather leave statement
quality in caller-land — that is a defensible line and we will
describe it as such.

We would value being told whether the scoping decision in #218 is
intended to be permanent, since we are writing this up and would
rather get it right. And we are happy to open a PR, either with a
certificate checker or with just the specification-printing described
above, if either is useful.
