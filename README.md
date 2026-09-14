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

### 5. Threshold composition

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
| `Examples/` | concrete instances: Helios, CMZ, Privacy Pass, a threshold example |
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
