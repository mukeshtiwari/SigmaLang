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

## Voting systems, read out of their specifications

These were transcribed from the published specifications cited in each
file, not from our own code, as a check on whether the criterion says
anything about systems nobody here wrote.

| file | source | verdict |
|---|---|---|
| `belenios-signature.rel` | Belenios 3.0 §4.16 | determined |
| `belenios-iprove-branch.rel` | Belenios 3.0 §4.12 | determined |
| `belenios-decrypt.rel` | Belenios 3.0 §4.20 | determined |
| `belenios-nonzero.rel` | Belenios 3.0 §4.15 | determined |
| `belenios-nonzero-unchecked.rel` | the same, one check dropped | **vacuous** |
| `electionguard-range-branch.rel` | ElectionGuard 2.1.0 §3.3.7 | determined |
| `electionguard-decrypt.rel` | ElectionGuard 2.1.0 | determined |
| `swisspost-schnorr.rel` | Swiss Post primitives 1.6.0 §10.2 | determined |
| `swisspost-exponentiation.rel` | §10.4 | determined |
| `swisspost-exponentiation-identity-bases.rel` | §10.4 at an admitted input | **vacuous** |
| `swisspost-plaintext-equality.rel` | §10.5 | determined |
| `swisspost-plaintext-equality-identity-keys.rel` | §10.5 at an admitted input | **unsatisfiable** |

Every relation as its specification intends it is determined. The
three that are not are what happens at the edges, and two of those
edges are reachable through the specification's own input types.

### Belenios, and a check that is exactly this axis

Belenios's proof that a ciphertext encrypts a non-zero value publishes
`A0` and proves it has the same representation in base `(beta, y)`
that `1` has in base `(alpha, g)`. The first equation's target is the
identity, and `A0` is chosen by the prover.

The specification's verifier begins: *check that A0 ≠ 1*. That check
is load-bearing and the equations do not show why. Eliminating `v`
from the first equation leaves `A0 = g^(m*u)`, so `u` is pinned only
when the encrypted `m` is non-zero — and when `m` is zero, `A0` is
forced to `1`. Drop the check and every target is the identity, which
is `belenios-nonzero-unchecked.rel`, and the checker calls it vacuous.

So a deployed system already performs, by hand and for this one proof,
what the vacuity axis performs for every relation.

### Swiss Post, and an exclusion that is stated once

The Swiss Post primitives specification builds its proofs on Maurer's
framework, which is the class this repository formalises, so its
phi-functions transcribe directly.

Its Schnorr proof types the base as `g ∈ G_q \ {1}`, and says so
three times — on the phi-function, on the prover and on the verifier.
The identity is excluded deliberately.

The two many-base proofs in the same section do not repeat it:

- §10.4, the exponentiation proof, types its base vector `G_q^n`.
  The identity is a member of `G_q`, so an all-identity base vector is
  type-correct, and then phi is the constant map — every witness has
  the same image, the honest image is all ones, and the proof says
  nothing about the exponent. The checker reports it vacuous.
- §10.5, the plaintext equality proof, types both public keys `G_q`.
  With both the identity, the only equation that mentions the
  plaintexts collapses, and the checker reports it unsatisfiable
  whenever the two ciphertexts differ.

**What this is and is not.** It is a gap between what these
algorithms accept as stated and what the same document is careful
about one page earlier. It is not a demonstrated attack: whether an
adversary can reach either algorithm with such inputs depends on the
call sites in the protocol specification, which is a separate document
we have not audited. The primitives specification is the artefact
being read here.

The plaintext equality case also marks a limit worth being plain
about. With both keys the identity, an honest `c1` and `c1'` are both
the message, so their quotient is the identity and the checker reports
the relation determined and acceptable — correctly, because the
relation is fine. It has simply stopped being a statement about
plaintext equality. Whether a relation says what its author meant is
not a question either axis decides.

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
