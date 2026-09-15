# Relations

Input for `Executable/Analyse`, which decides whether a relation
determines the secrets it claims to determine:

```
$ dune build Executable/Analyse/main.exe
$ ./_build/default/Executable/Analyse/main.exe Examples/Relations/cmz-show.rel
```

Three keywords. `secrets` fixes the column order, `claims` says which
of those secrets the relation asserts it pins down (the default is all
of them), and each `eq` gives a target followed by one base per
secret. A `1` is the identity in either position: as a base it means
that secret does not occur in that equation, and as a target it means
the target is the identity.

Bases are names rather than group elements because that is all the
question depends on. Two positions constrain each other exactly when
they carry the same base, so naming the bases says everything the
checker can use and nothing it cannot.

## Deployed protocols

Transcribed from the Rocq sources named in each file. Every one is
determined, which is the same verdict the drivers reach when they run
the compiled relations on live data — 13,072 Helios leaves from a real
election, and the CMZ, Privacy Pass and CFRG statements.

| file | protocol |
|---|---|
| `helios-ballot-zero.rel` | the vote-was-zero branch of a Helios ballot proof |
| `helios-ballot-one.rel` | the vote-was-one branch of the same proof |
| `helios-decrypt.rel` | a trustee's decryption proof |
| `helios-pok.rel` | a trustee's proof of knowledge of its key |
| `cmz-show.rel` | showing a two-attribute CMZ credential |
| `cmz-issue.rel` | requesting issuance of one |
| `cmz-issuer.rel` | the issuer's proof that it used its published key |
| `privacypass-dleq.rel` | the Privacy Pass issuance proof |
| `cfrg-discrete-logarithm.rel` | the CFRG draft's Schnorr relation |
| `cfrg-dleq.rel` | its equality of discrete logarithms |
| `cfrg-pedersen-commitment.rel` | its Pedersen commitment opening |

The two Helios ballot branches are worth opening. Each carries a
column for the other branch's randomness, because the witness vector
spans the whole disjunction, and each claims only its own. Claiming
both instead is a two-line experiment:

```
$ printf 'secrets r0 r1\nclaims r0 r1\neq alpha g 1\neq beta h 1\n' | \
    ./_build/default/Executable/Analyse/main.exe -
```

and it reports `DEGENERATE`. That is not a defect in Helios; it is
what happens when a branch is asked to pin down a secret it never
claimed, and running the checker without that distinction reported 700
of 724 leaves of a real election as degenerate, every one of them
wrongly.

## Cases that fail, and why

| file | verdict |
|---|---|
| `credential-broken.rel` | `DEGENERATE` — both attributes on one generator, so the relation pins down their sum |
| `credential-fixed.rel` | `DETERMINED` — a generator each |
| `no-unused-scalar.rel` | `DEGENERATE` — every scalar used, no repeated column, no identity image, and still two witnesses |
| `dead-column.rel` | `DEGENERATE` claimed, `DETERMINED` unclaimed — the same matrix, so the claim is a real input |
| `two-rows.rel` | `DETERMINED` — sound, but no equation has pairwise distinct bases, so the sufficient test of `Compiler/IncidenceDecide.v` declines and the elimination is what decides it |
| `vacuous.rel` | determined and still rejected — every target the identity, so the all-zero witness works |

`no-unused-scalar.rel` is the relation sigma-rs accepts at `3e12c83`
and on the `#218` branch; `Evidence/` has that reproduction as a Rust
test.
