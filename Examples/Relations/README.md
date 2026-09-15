# Relations

Input for `Executable/Analyse`, which decides whether a relation
determines the secrets it claims to determine:

```
$ dune build Executable/Analyse/main.exe
$ ./_build/default/Executable/Analyse/main.exe Examples/Relations/cmz-show.rel
```

Four keywords. `secrets` fixes the column order, `claims` says which
of those secrets the relation asserts it pins down (the default is all
of them), and each `eq` gives a target followed by one base per
secret. A `1` is the identity in either position: as a base it means
that secret does not occur in that equation, and as a target it means
the target is the identity.

What the checker reads is not a matrix of its own invention. Each
`eq` line is parsed into the compiler's own `Dsl.equation` --- the
type `compile` consumes --- and the matrix the checker sees is
`DslInstantiate.name_mat` of exactly those equations. So the statement
you check is the statement you would compile, with no transcription
between the two. That is the same defect this development is about,
one level up, and it would be poor form to leave it open here.

Bases are names rather than group elements because that is all the
*statement* question depends on. Two positions constrain each other
exactly when they carry the same base, so naming the bases says
everything the checker can use and nothing it cannot.

The instance is a separate question, and `point` is how you ask it:

```
eq  C   g1  g2  h        # the statement: a generator each

point g1  2              # the deployment: which element each name
point g2  2              # stands for.  Here g1 and g2 are the same.
point h   5
```

The statement is sound and stays sound. The instance is not, because
an environment that sends two names to one element merges their
equations, and the tool reports it:

```
  environment    NOT FAITHFUL -- two bases coincide, or one is the identity
  verdict        statement acceptable, INSTANCE NOT
```

That second check is what `Compiler/DslInstantiate.v` proves sound,
and it is the hypothesis under which a design-time verdict transfers
to a running system. Omit the `point` lines and the tool says so
rather than pretending: the verdict is then about the statement alone.

An exponent names an element because every element of a prime-order
group is a power of the generator. A real deployment would hand its
own encodings to the library rather than write them in a file; the
exponent form is here so that a faithful and an unfaithful instance of
one statement can be written down side by side. Two positions constrain each other exactly when
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

Every relation carries an instance as well as a statement, so each
file exercises both checks. Except where a file exists to show a
failure, the instance gives every base name a generator of its own and
is therefore faithful, and the exponents are ours and carry no
meaning. In particular they are not taken from any specification: we
transcribed statements from those documents, not deployments.

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

## Other domains

Voting is one family. These are transcribed from the specifications
cited in each file, across credentials, verifiable randomness,
oblivious pseudorandom functions and threshold signing.

| file | source | verdict |
|---|---|---|
| `bbs-proof.rel` | BBS signatures, draft-irtf-cfrg-bbs-signatures-08 §3.7.3 | determined |
| `bbs-proof-colliding-generators.rel` | the same, at a collision the draft forbids | **degenerate** |
| `vrf-ecvrf.rel` | ECVRF, RFC 9381 §5.3 | determined |
| `voprf-batched-dleq.rel` | VOPRF, RFC 9497 §2.2.2 | determined |
| `frost-signature-share.rel` | FROST, RFC 9591 §5.3 | determined |

### Six specifications, each hand-coding a case of one axis

The interesting result is not any single verdict. It is that every
specification read here already states a special case of what the
criterion decides in general, each in its own vocabulary and each for
its own proof:

| specification | what it says | which axis |
|---|---|---|
| Swiss Post §10.2 | the Schnorr base is `g ∈ G_q \ {1}` | vacuity, one base |
| Belenios §4.15 | the verifier checks `A0 ≠ 1` | vacuity, a prover-chosen target |
| ElectionGuard 6.A | `α, β` lie in the prime-order subgroup, and `K` comes from the key ceremony | vacuity, by construction |
| RFC 9381 | `ECVRF_validate_key(Y)`, and no encoding for the identity | vacuity |
| BBS §3.3 | "The generators MUST be unique and pseudo-random i.e., with no known relationship to each other" | **both** |
| RFC 9497 | nothing, on the composite `M` that carries the batch | — |

The BBS sentence is the one to read twice, because it states both
halves of the theory and draws the line in the same place we do.
*Unique* is the half a checker reading the relation can decide, and
`bbs-proof-colliding-generators.rel` is what its failure looks like:
two withheld messages on one generator, so the proof pins only their
sum. That is `credential-broken.rel`, arrived at independently by a
different committee. *No known relationship* is the other half, and
our completeness theorem says no checker reading the relation can
decide it — seeing that two generators are related means computing a
discrete logarithm. So the draft asks for it as a construction
requirement rather than as a check, which is the only place it can
live.

Swiss Post is the only one of the six that states its rule and then
does not apply it uniformly.

### Not a gap in the criterion — a level below it

RFC 9497 turned up a case that looks at first like something neither
axis catches, and the Swiss Post plaintext-equality case has the same
shape. It is worth being exact about what it is, because the first
diagnosis we wrote here was wrong.

When the batch composite `M` lands on the identity, the relation reads

```
pkS = G^k
1   = 1^k
```

and the checker reports `determined, acceptable`. That verdict is
correct, and nothing is missing from the criterion: a trivially-true
equation is not part of the relation at all. The relation above **is**
the relation `pkS = G^k` — same witnesses, same kernel, same
everything — and the criterion is complete about it.

What went wrong happened before the relation existed. The designer
wrote a *statement* with two equations; the *instantiation* produced a
relation with one. The damage is in the map between them, which is a
different object with its own theory.

`Compiler/Instantiate.v` is that theory. A statement's bases are
names; an environment `genv` sends them to group elements; and the
same incidence system reads over either. Two results, both
machine-checked and axiom-free:

- **`instantiation_monotone`** — every solution of the statement's
  incidence system is a solution of the instance's, for *any*
  environment. Instantiation can only weaken. So a statement that is
  degenerate on its own names is degenerate however it is
  instantiated, and a claim the statement fails to pin down is one no
  environment will rescue (`instance_claim_implies_statement_claim`).
- **`faithful_preserves_incidence`** — if `genv` keeps each equation's
  names apart and off the identity, the two systems are *equal*.
  Hence `faithful_transfers_the_claim`: the statement is checked once,
  and every faithful instance inherits the verdict.

The hypothesis is doing real work, and `FaithfulnessIsNeeded` at the
foot of that file proves it rather than asserting it: a statement that
determines both its secrets, an environment that confuses its two
generators, and the resulting instance exhibiting `(1, -1)`.

This is why it was worth resisting a third check. One condition
covers all three phenomena in this directory, and it was never told
about any of them:

| | what `genv` did | which clause |
|---|---|---|
| BBS colliding generators | identified two names in one equation | separation |
| Swiss Post identity base | sent a name to the identity | non-identity |
| VOPRF vanished equation | sent *every* name in an equation to the identity | non-identity |

It also explains the table above. Every one of those six hand-coded
checks is a side condition on the **instantiation**, not on the
statement, which is why no two of them are phrased alike.

`Compiler/DslInstantiate.v` wires this to the compiler this
repository actually runs. A compiled cell is not a single base —
`row_of_terms` puts, in a variable's column, the product of every term
carrying it — so the object playing the part of a name is the whole
cell: the list of (base, coefficient) pairs the equation places on
that variable. `row_of_terms_is_instantiated` shows the compiled row
is exactly the instantiation of the syntactic one, and everything else
transports.

**Why this is cheaper.** The two halves cost very different things.
Deciding that a statement determines its claim means building an
incidence system and eliminating over the scalar field — that is where
the certificates come from. Deciding that an environment is faithful
means comparing group elements: no field arithmetic, no elimination,
no certificate. `faithful_tob` is that decision procedure, proved
sound, and
`faithful_check_transfers_the_design_time_verdict` is the form a driver
uses — one boolean per instance, and one design-time fact about the
statement that no instance repeats.

The split also puts the blame in the right place. A statement that
gives two attributes the *same* generator is a bad statement, and
`no_instance_rescues_a_bad_statement` says no environment will save it.
A statement with two proper generators that an environment then
collapses is a bad *instance*, and only the cheap check sees it. Two
`Example`s at the foot of the file compute both.

Two further pieces carry this to the statements people actually
write. `live_claim_is_design_time` closes a gap that would otherwise
have sunk the whole chain: the checker does not take a branch's claim
on trust, it *computes* one from the instantiated matrix by finding
the neutral columns, so the theorem above quantified over a claim
nobody could produce at design time. Under a faithful environment the
two agree, and for the reason faithfulness already names — a cell
collapses to the identity only when it is empty. And
`compiled_statement_leaves_determine` lifts the branch result to the
whole source language, conjunction, disjunction and threshold alike:
check a statement, and every leaf of whatever the compiler builds from
it determines the claim it makes. That matters because nothing anyone
proves is a bare leaf — a Helios ballot is a disjunction of two
conjunctions, and its 13,072 leaves come from about 6,500 proofs.

**What is deliberately not covered.** The vacuity axis. Its question
is whether every target is the identity, and a target is a product of
public points the instance supplies — Belenios's `A0` is chosen by the
prover at proof time. So it is instance-dependent by nature, not by an
accident of how these theorems are stated, and there is nothing to
move to design time. It is also already cheap, O(m) group
comparisons, the same order as the faithfulness check; the expensive
half was always determination.

**Measured.** `Executable/Heliosrealcode` now runs both routes over
the same leaves of the 2024 IACR election and compares their verdicts,
so a disagreement would surface as a failure rather than as a faster
wrong answer:

```
    per instance : 13072 leaves eliminated over the field   0.7160s
    design time  :     4 statement leaves, checked once     0.0002s
     + instances : 13072 faithfulness checks                0.0183s
    both routes determine every leaf : yes
```

Four statement leaves, not three: the ballot proof is a disjunction,
and each branch is a leaf of its own.

That is **38.8x** on the statement-quality work. It is also the
honest place to stop, because the verifier as a whole takes about two
minutes on this election and is dominated by modular exponentiation
and SHA-256. Quality checking goes from roughly half a percent of the
run to a few hundredths — a large win on the line item and close to
invisible on the wall clock. That was the expected shape before
measuring, and it is worth reporting either way: it says the design-time
split is worth having for the analysis it makes possible, not because
anyone was waiting on the old route.

Helios is the only corpus where this could be measured at all. CMZ has
ten leaves, Privacy Pass six, the CFRG vectors seven; per-instance cost
is not a question there.

## Cases that fail, and why

| file | verdict |
|---|---|
| `credential-broken.rel` | `DEGENERATE` — both attributes on one generator, so the relation pins down their sum |
| `credential-fixed.rel` | `DETERMINED` — a generator each |
| `no-unused-scalar.rel` | `DEGENERATE` — every scalar used, no repeated column, no identity image, and still two witnesses |
| `dead-column.rel` | `DEGENERATE` claimed, `DETERMINED` unclaimed — the same matrix, so the claim is a real input |
| `two-rows.rel` | `DETERMINED` — sound, but no equation has pairwise distinct bases, so the sufficient test of `Compiler/IncidenceDecide.v` declines and the elimination is what decides it |
| `bbs-proof-collapsed-instance.rel` | statement `DETERMINED`, **instance not faithful** — the sound BBS statement under an environment that collapses its two message generators, which is where the draft's requirement actually lives |
| `credential-repaired-by-adding.rel` | `DETERMINED` — the same repeated base as `credential-broken.rel`, plus one equation. The shape a checklist objects to is still there and the statement is sound, which is why no such rule can work (`Compiler/NoChecklist.v`) |
| `vacuous.rel` | determined and still rejected — every target the identity, so the all-zero witness works |

`no-unused-scalar.rel` is the relation sigma-rs accepts at `3e12c83`
and on the `#218` branch; `Evidence/` has that reproduction as a Rust
test.
