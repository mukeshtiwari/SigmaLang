# The CFRG P-256 vectors this evaluation ran

Taken from the sigma-rs reference implementation at commit `92c63fc`,
which is the last revision whose instance encoding
`Executable/Cfrgcode/cfrg.ml` reads:

- `sigma-proofs_Shake128_P256.json` — seven relations, fourteen
  entries (each in a batchable and a compact flavour)
- `sigma-proofs-invalid_Shake128_P256.json` — the negative controls,
  including the five instance-validation cases E0 to E4

They are kept here because upstream carries neither any more. The file
at `main` holds five relations in a wire format this parser rejects,
and the invalid file was dropped altogether. Without these copies the
CFRG row of the paper's corpus table and its table of negative
controls could not be reproduced from the artefact.

```
$ dune build Executable/Cfrgcode/main.exe
$ ./_build/default/Executable/Cfrgcode/main.exe Evidence/cfrg-vectors
```

## The seven relations

| relation | equations | secrets |
|---|---|---|
| `discrete_logarithm` | 1 | 1 |
| `dleq` | 2 | 1 |
| `dleq_derived_element` | 2 | 1 |
| `elgamal_decryption` | 2 | 1 |
| `pedersen_commitment` | 1 | 2 |
| `pedersen_commitment_dleq` | 2 | 2 |
| `bbs_blind_commitment_computation` | 1 | 4 |

All seven hold as stated, all seven are determined with no undecided
verdict, and the verified verifier accepts every batchable and every
compact proof.

## The one disagreement

Of 23 batchable negative controls, 22 agree with the published
expectation and one does not:

```
E0   wanted accept got reject
     The empty relation, with no equations and no image, is valid.
```

We reject it, and the disagreement is deliberate rather than a defect
on either side. A relation with no equations is satisfied by every
witness, so a proof of it demonstrates nothing; that is what our
vacuity axis reports and what `Vacuity.empty_leaf_is_vacuous` proves.
The reference implementation takes the view that a well-formed
relation with nothing to say is still well-formed. Both positions are
coherent; they answer different questions, and the point of the two
axes is to keep those questions apart.

The eleven compact controls agree without exception.

E3 and E4 are rejected below the theory rather than by it --- at the
SEC1 point decoder and at an index bound --- which is the right place
for them and is why they appear as `unparsed` rather than with a
verdict.

Licence: the vectors are from the sigma-rs project, dual-licensed
Apache-2.0 / MIT.
