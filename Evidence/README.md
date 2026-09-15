# Evidence produced outside this repository

There are two variants because the API differs across versions.
`sigmalang_counterexample.rs` targets `main` at `3e12c83`, where
validation is reached through `CanonicalLinearRelation::try_from`.
`sigmalang_counterexample_pr218.rs` targets the branch of PR #218,
where `Instance::try_from` is restored and `image` becomes a field.
Both are accepted and both exhibit the same two witnesses.

## sigmalang_counterexample.rs

A test against the sigma-rs reference implementation, not against this
development.  It builds the statement

    P = x1*G + x2*G
    Q = x2*H + x3*H

hands it to `CanonicalLinearRelation::try_from`, which is sigma-rs's
instance validation, and exhibits two different witnesses with the
same image.  The validator accepts; the statement does not determine
its witness.

To run it, drop the file into `tests/` of a sigma-rs checkout and

    cargo test --test sigmalang_counterexample -- --nocapture

Result at sigma-rs `3e12c83` (v0.3.2), a fresh clone of upstream main:

    sigma-rs validation : ACCEPTED
    witness A           : (3, 5, 11)
    witness B           : (4, 4, 12)
    images              : identical

Two cautions for anyone citing this.

The check surface moved.  The version our test vectors came from
(`92c63fc^`) ran ten numbered instance checks; at 0.3.2 most are gone,
leaving equation/image count agreement, assignment of elements,
skipping trivially-true equations, an identity check on the canonical
image, and the rejection of non-trivial homogeneous equations.  Any
claim about what sigma-rs checks has to name a commit.

That last rejection is reported as "Trivial kernel in this relation",
which is a misnomer worth not repeating: it fires when an equation's
image equals its constant term, so the all-zero witness satisfies it.
That is vacuity, the condition of Vacuity.v, and it says nothing about
the kernel of the linear map.  The determination question is not
addressed there.

The version the vectors came from could not be built: it was written
against an unpublished spongefish, and the registry's 0.7.0 lacks the
symbols it uses.  So this is a demonstration against current sigma-rs
and a reading against the tested commit.
