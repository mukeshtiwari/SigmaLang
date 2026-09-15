# Do Σ-protocol libraries accept a statement that determines nothing?

The criterion in `Compiler/` decides whether a relation pins down the
secrets it claims. A library that builds relations from caller input
is the place where a relation that does not can actually arise, since
the caller supplies the bases and the library is the only thing in a
position to object.

We asked three libraries the same question, using the same relation:
an anonymous-credential showing with two attributes,

```
C = G1^a1 · G2^a2 · H^r
```

instantiated so that `G1` and `G2` are the same group element. The
statement is fine; the instantiation is not. It pins `a1 + a2` and
neither attribute, so a holder of `(5, 0)` can present as `(3, 2)`.

| library | what it checks | verdict |
|---|---|---|
| sigma-rs `3e12c83` | count bounds, index ranges, every element used | accepts — demonstrated |
| zkp 0.8.0 (`cdca489`) | nothing about the statement | accepts — demonstrated |
| zksk (`075ccdc`) | that all bases share a group | accepts — by reading |

None of these is a vulnerability in a deployed system, and we do not
report one. What they are is three independent APIs that will build,
prove and verify a relation asserting less than its caller believes,
and say nothing.

## sigma-rs

`../sigmalang_counterexample.rs` and `../sigmalang_counterexample_pr218.rs`,
with the surrounding argument in `../issue-draft.md`. The relation
there is the two-equation form with no unused scalar and no repeated
column, which is the sharper counterexample: it passes every shape on
the checklist and still fails to determine.

## zkp

`zkp_underdetermined.rs`, which runs as a test in that crate's own
harness. It proves the showing twice, once with attributes `(5, 0)`
and once with `(3, 2)`, and asserts three things: the two showings
produce the *same* commitment, both proofs verify against it, and
giving the attributes a generator each makes the commitments differ
again.

The API is what permits it. `allocate_point(b"G1", G1)` binds a
transcript *label* to a point chosen at run time, so two labels may
carry one element and the constraint system cannot tell. That is
exactly the gap between a statement and its instantiation that
`Compiler/Instantiate.v` is about, in a library's type signature.

## zksk

Read rather than run: `petlib` does not build here. The relevant code
is `DLRep.__init__` in `zksk/primitives/dlrep.py`, whose only check on
the bases is

```python
# Check all the generators live in the same group
test_group = self.bases[0].group
for g in self.bases:
    if g.group != test_group:
        raise InvalidExpression("All bases should come from the same group", ...)
```

No repeated base is rejected and no identity is excluded, so
`DLRep(C, a1 * g + a2 * g + r * h)` is constructed without complaint.
We report this as a reading of the source, not as an executed test.
