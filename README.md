# SigmaLang

A compiler from a small statement language to sigma protocols, with
completeness, special soundness and zero knowledge machine-checked in
Rocq, and extraction to running OCaml.

You write a statement such as "at least two of these three points is a
power of the generator by a scalar I know". The compiler turns it into
a sigma protocol with a prover, a verifier and a simulator, and the
security properties come from theorems proven once about the
translation rather than re-argued for each statement.

Three case studies drive the development:

- **Helios**, the end-to-end verifiable voting system. The verifier
  here checks the published IACR 2023 and 2024 elections.
- **CMZ**, keyed-verification anonymous credentials, following the
  statements of Goldberg's `cmz` crate.
- **Privacy Pass**, anonymous tokens for skipping internet
  challenges, following the PoPETs 2018 paper. The server's discrete
  log equivalence proof, batched over many tokens at once.

## Requirements

Install with `opam`. The versions below are the ones the development
is built and tested against.

| package | version |
| --- | --- |
| `rocq-prover` | 9.0.1 |
| `dune` | 3.23.1 |
| `coq-ext-lib` | 0.13.1 |
| `coq-coqprime` | 1.6.0 |
| `coq-bignums` | 9.0.0 |
| `zarith` | 1.14 |
| `cryptokit` | 1.21.1 |
| `yojson` | 3.0.0 |

```sh
opam install rocq-prover dune coq-ext-lib coq-coqprime coq-bignums \
             zarith cryptokit yojson
```

## Building

```sh
dune build
```

**The first build is slow, and most of it is one file.** `Examples/primeP.v`
checks a Pocklington certificate for the 2048-bit prime of the IACR
elections, which takes roughly half an hour of CPU on its own.
Everything else builds in a couple of minutes. Later builds are
incremental and fast.

If you only want the compiler and its proofs, without the concrete
elections, build just that part and skip the certificate entirely:

```sh
dune build @Compiler/default
```

## Running the experiments

Four executables are produced. Each is self-contained; run them from
the repository root.

### 1. Verifying a real Helios election

This is the main result: the published IACR elections, checked by the
extracted verifier, with the Fiat-Shamir challenge recomputed from the
announcement rather than read out of the ballot.

Both election files are bundled in `Heliosdata/`, so this needs nothing
else checked out. With no argument it reads the 2024 election:

```sh
./_build/default/Executable/Heliosrealcode/main.exe
```

Expected output, in about two minutes:

```
Verifying IACR2024.txt
  932 ballots, 3 trustees, 7 candidates
  election key is the product of trustee keys : true
  all trustee key proofs verify               : true
  6524 ballot proofs verified in 121.8s, failures : 0
  21 decryption proofs verify                 : true
  recovered tally : [457; 216; 285; 181; 195; 212; 377]
  published tally : [457; 216; 285; 181; 195; 212; 377]

  VERDICT: proofs all verify, tally matches
```

The 2023 election works the same way and takes about ninety seconds:

```sh
./_build/default/Executable/Heliosrealcode/main.exe Heliosdata/IACR2023.txt
```

A second argument caps how many ballots are read, which is useful when
you only want to see it start:

```sh
./_build/default/Executable/Heliosrealcode/main.exe Heliosdata/IACR2024.txt 20
```

Note that the decryption proofs and the tally will then fail, correctly:
they are checked against an aggregate over every ballot, so a partial
read gives the wrong aggregate.

### 2. Helios self-test

Generates its own ballots at the real 2024 parameters rather than
reading an election. Useful as a quick check that the build works, and
it reports timings. Runs in a few seconds.

```sh
./_build/default/Executable/Helioscode/main.exe
```

It also checks the two native substitutions used by the extraction, SHA-256
against a published test vector and the decimal rendering against a
theorem, and it confirms that a valid proof re-presented against a
different ciphertext is rejected.

### 3. CMZ credential statements

Exercises the CMZ showing, issuance and issuer statements at credential
sizes from one to eight attributes, and reports how the cost grows.
Runs in a few seconds.

```sh
./_build/default/Executable/Cmzcode/main.exe
```

This one is a self-test: there is no published CMZ transcript to check
against, so it builds instances satisfying the relations, proves them
and verifies. It shows the compiler handles CMZ's statements at CMZ's
sizes with a real challenge binding; it is not evidence about the
credential scheme itself, which is argued in the CMZ paper.

### 4. Privacy Pass token issuance

Plays both sides of a Privacy Pass issuance: the client sends blinded
tokens, the server signs them and proves in zero knowledge that it
used the key it published. Runs in a few seconds.

```sh
./_build/default/Executable/Privacypasscode/main.exe
```

The proof is one discrete log equivalence over composite points,
whatever the batch size, so its cost is flat while forming the
composites grows linearly. The run also checks the attack the proof
exists to stop: a server that signs one token in the batch with a
different key is rejected.

Like the CMZ run this is a self-test, since there is no published
Privacy Pass transcript to check against. Note also that soundness of
*batching* is Henry's probabilistic argument over the random
coefficients and is not mechanised here; what is proven in Rocq is
that batching preserves the relation, which is the direction an honest
server needs.

### 5. Recovering the statement a published election proves

Asks a different question from the verifier above. Not "do these
ballots verify?" but "what do they prove?". Those are different
questions, and only the second is about the protocol rather than about
whichever verifier happened to be run.

```sh
./_build/default/Executable/Recovercode/main.exe Heliosdata/IACR2024.txt 40
```

`Examples/Recover.v` defines a space of candidate readings, varying
which side of each equality carries the secret, which announcement
positions reach the Fiat-Shamir hash and in what order, and whether
the instance is hashed alongside. A *target* says which protocol to
point the search at: its statement, its names, its private variables,
how an instance becomes a point environment, and how wide an
announcement is. Two are defined, ballot validity and correct
decryption, and the run below identifies both. The space is
not a list someone wrote down. It is specified by `valid_candidate`,
and `all_candidates_spec` proves the enumeration is exactly that
specification, so a reader audits a three-line predicate instead of
trusting a list. For Helios it comes to 390 readings.

Each candidate is a statement, so each compiles and each arrives with
the compiler's theorems already proven of it. The driver runs all 390
against the published ballots. Exactly one is consistent with them.
The decryption statement is narrower, 30 readings over two
announcement elements, and is identified from the election's 21
published decryption proofs.

The two orientations are not written out per target.
`flip_eqs` turns every equality in a statement around, and
`flip_eqs_involutive` proves doing so twice restores the original, so
a target supplies one statement and the search covers both readings.

Three results make that an identification rather than a coincidence.
`all_candidates_spec` says nothing was omitted from the search.
`recovered_relation_holds` says two accepting runs sharing an
announcement and differing in the challenge yield a witness for the
candidate's relation, so acceptance is evidence about the protocol
rather than about our verifier. And the driver cross-checks the
survivor by generating an honest proof under its own rule and
confirming no other reading accepts it.

`selection_omitting_loses_information` covers the whole space at once:
every reading whose selection omits a position fails to determine the
announcement from the challenge, which is the property behind weak
Fiat-Shamir.

We established the right reading by hand the first time, which took a
day and a detour through Python. This makes it a search.

The run then does something stronger than selecting: it **solves** for
the relation. A leaf's verification equation is a product of unknown
matrix entries raised to known responses, equal to a known value, so
each row is a subset-product problem over a pool of published elements
rather than a search for unknown group elements. The pool is closed
under inverses and products, which is not optional: the right branch
of a Helios ballot proves against `beta * g^-1`, which nobody
publishes. From five transcripts it recovers

```
branch 0 :  g^x = alpha        h^x = beta
branch 1 :  g^x = alpha        h^x = beta*g^-1
decrypt  :  g^x = pk           AA^x = M
```

each uniquely, in about three seconds per target, using the challenge
published in the transcript rather than a recomputed one, so this
stage is independent of the hash rule.

The solved relation is then a guess until it is checked. For the
decryption proof, which is a standalone non-interactive proof, the run
closes the loop: it renders the solution as a surface statement,
compiles it with the verified compiler, and confirms the resulting
verifier accepts the published transcripts. A ballot branch is half of
a disjunction, so its challenge is not a hash and it is not a
standalone proof; the disjunction as a whole is checked by the
identification stage instead.

A candidate is dropped the moment it fails one proof, since a
refutation is final. That is the only pruning used, so the
exhaustiveness theorem still means something, and it is what keeps the
larger space affordable.

The second argument caps how many ballots are read. Without it the run
checks all 390 readings against all 6524 proofs of the 2024 election
in about two minutes, which is faster than a plain verification pass
over the same corpus: 389 readings are refuted by the first proof they
see and never look at a second.

### 6. Threshold composition

A three-way threshold statement over a small group, proved and verified
both interactively and non-interactively, with a wire round trip and a
tamper test. Runs in under a second.

```sh
./_build/default/Executable/Thresholdcode/main.exe
```

## Documentation

Browsable HTML for every module, generated by `rocqdoc`:

```sh
./make-docs.sh          # then open docs/index.html
```

The script builds all six theories, collects them under `docs/` behind
a landing page, and replaces `rocqdoc`'s default stylesheet with a
readable one. Only comments written as `(** ... *)` appear; plain
`(* ... *)` comments are used for notes inside proof bodies and are
deliberately invisible to `rocqdoc`.

## Layout

| directory | contents |
| --- | --- |
| `Algebra/` | groups, rings, fields, vector spaces |
| `Utility/` | vectors, a concrete prime-order group, SHA-256, string encodings |
| `Probability/` | finite distributions, used to state zero knowledge |
| `Crypto/` | the single-equation Schnorr protocol |
| `Compiler/` | the languages, the compiler, and the security proofs |
| `Examples/` | concrete instances: Helios, CMZ, Privacy Pass, statement recovery, a threshold example |
| `Extraction/`, `Executable/` | extraction to OCaml and the drivers |
| `Heliosdata/` | published transcripts of the IACR 2023 and 2024 elections |

Inside `Compiler/`, the places to start are `LinearRelation.v` for the
leaf protocol everything is built from, `Composition.v` for how leaves
combine with AND, OR and thresholds, and `Surface.v` for the language a
user actually writes.

## What is and is not proven

Proven, with no axioms beyond those noted below: the compiler preserves
meaning; every compiled protocol is complete, specially sound and
honest-verifier zero knowledge; the gadgets for ranges, inequalities and
shared variables are sound; and the non-interactive transform is
complete for any hash function.

Not proven, and deliberately not assumed: soundness and zero knowledge
of the non-interactive protocol hold in the random-oracle model, and
that step is not axiomatised, so the development stays free of axioms.

Two qualifications on the trusted base. Over the small demonstration
group the main theorems are closed under the global context. Over the
2048-bit group of the IACR elections they additionally depend on the
primitive 63-bit integer axioms, which arrive with Coqprime's
certificate. And the extracted code replaces the verified SHA-256 and
the verified decimal rendering with native OCaml implementations, for
speed; both substitutions are checked at startup, the hash against a
published test vector and the rendering against a theorem.
