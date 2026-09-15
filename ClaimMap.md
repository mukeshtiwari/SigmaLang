# Claim–evidence map

Working document. Every sentence the paper may assert, with the theorem
name or the measurement that backs it. Nothing enters prose without a
row here.

**Thesis.** Σ-protocol soundness is conditional on the statement. We
characterise which statements make it worth having: decidably, with a
completeness theorem, on the axis where a checker's limit is that it
cannot see discrete logarithms; and provably not, on the axis where
deciding would compute them.

---

## Framing

| # | Claim | Evidence | Status |
|---|---|---|---|
| F1 | A verified compiler guarantees you prove the statement you wrote, not that the statement says anything | `Dsl.compile_protocol_soundness` concludes `∃ wenv, stmt_denote wenv s`; `CompVacuity.zero_threshold_is_free` exhibits an `s` anyone satisfies; `Dsl.compile` admits `SThresh 0` | supported |
| F2 | The determination question is not new | Picus/QED² (PLDI 2023), read directly | supported |
| F3 | No completeness characterisation exists, in any setting | Picus: *"this algorithm is incomplete, so it can also return ?"*, soundness proofs for inference rules only; ZKCrypt, CSF 2010, ESORICS 2010, sigma-rs source, Coda — all checklists or tools | supported |
| F4 | In our setting the obstruction is invisibility, not nonlinearity, which is why a completeness-relative-to-visibility theorem is meaningful here and vacuous for circuits | `IncidenceComplete.field_as_vector_space` + `relabelling_refutes`; for R1CS the visible and actual kernels coincide | supported |

## Theory

| # | Claim | Evidence | Status |
|---|---|---|---|
| T1 | Determination reduces to triviality of the kernel — there is exactly one thing to look for | `Degeneracy.determination_is_trivial_kernel`, `witness_difference_in_kernel` | supported |
| T2 | Determination is a property of a matrix *together with a claim*, not of a matrix | `Claim.determines`; `determines_full_iff_trivial_kernel`; `dead_column_breaks_full_claim` vs `branch_determines_what_it_claims` | supported — and forced by the corpus, not designed in advance |
| T3 | Incidence solutions are kernel vectors in every group, with no assumption | `Degeneracy.incidence_zero_in_kernel` | supported |
| T4 | The incidence system is exactly the structurally visible kernel | `IncidenceComplete.incidence_zero_iff_relabellings`, `relabelling_refutes` (constructive) | supported |
| T5 | The satisfiability axis provably does not close | `Vacuity.leaf_satisfiability_is_discrete_log` | supported — phrase as a reduction under the DL assumption, NOT as undecidability |
| T6 | A statement tree is provable-by-anyone in exactly two ways | `CompVacuity.tree_not_freeb_sound`, `zero_threshold_fails_the_test` | supported |
| T7 | Both verdicts are certified; the search is untrusted | `IncidenceDecide.reject_certificate_sound`, `Claim.claimed_certificate_refutes`, `Determined.combo_checkb_sound`, `LeafStatus.classify_leaf_sound` | supported |
| T8 | The sufficient acceptance test is incomplete, and here is the boundary | `IncidenceDecide.two_rows_pin_what_no_row_pins` | supported |

## Findings about existing artefacts

| # | Claim | Evidence | Status |
|---|---|---|---|
| A1 | Our own checker was wrong in both directions | `Vacuity.target_live_rejects_a_sound_leaf`, `empty_leaf_accepted`, `dead_row_unsatisfiable`, `Degeneracy.three_column_counterexample` | supported |
| A2 | A statement sigma-rs accepts can fail to determine its witness | `Evidence/sigmalang_counterexample.rs`, run against sigma-rs 0.3.2: validation ACCEPTED, witnesses (3,5,11) and (4,4,12), images identical | **demonstrated** — executable test in their harness, not a reading |
| A3 | ~~sigma-rs Check 9 is stronger than its justification~~ | — | **dropped**: Check 9 no longer exists at HEAD |
| A4 | Claims about what sigma-rs checks must name a commit | the vectors' commit ran ten numbered checks; 0.3.2 keeps count agreement, assignment, skipping trivially-true equations, an image identity check, and rejection of non-trivial homogeneous equations | supported by reading both versions |
| A5 | sigma-rs's `"Trivial kernel in this relation"` is a misnomer: it is vacuity, not the kernel of the linear map | `canonical.rs:471-473` fires when image equals constant term, i.e. the all-zero witness works — our `leaf_vacuous_iff_neutral_targets`; determination is unaddressed there | supported — do not repeat their wording |
| A6 | The Swiss Post primitives spec excludes the identity from the Schnorr base but not from the exponentiation proof's base vector or the plaintext-equality public keys | v1.6.0: §10.2 types `g ∈ G_q \ {1}` on algs 10.1/10.2/10.3; §10.4 alg 10.7 types the bases `G_q^n`; §10.5 alg 10.10 types `h, h' ∈ G_q`, and `1 ∈ G_q`. `Examples/Relations/swisspost-*.rel`: all-identity bases → `VACUOUS`, identity keys → `UNSATISFIABLE` | supported **as a reading of the primitives spec only** — call sites are in the protocol spec, unaudited; NOT an attack |
| A7 | Belenios's non-zero proof performs the vacuity check by hand | §4.15 verifier step 1 is "check that A0 ≠ 1"; A0 is prover-chosen and is the only non-identity target. `belenios-nonzero-unchecked.rel` → `VACUOUS` | supported |
| A8 | ElectionGuard's range and decryption proofs are determined, and structurally cannot hit either axis | v2.1.0 Verification 6.A puts α, β in the prime-order subgroup; K is fixed by the key ceremony, not by the prover | supported |
| A9 | Six independent specifications each hand-code a special case of one of the two axes; one does not apply its own rule uniformly | table in `Examples/Relations/README.md`, each row cited to its spec | supported |
| A10 | BBS states both halves of our characterisation and draws the line where our completeness theorem puts it | draft-irtf-cfrg-bbs-signatures-08 §3.3: generators "MUST be unique and pseudo-random i.e., with no known relationship to each other" — uniqueness is the decidable half, "no known relationship" the half the theorem says no pattern checker can reach | supported — the strongest external confirmation we have |
| A11 | ~~Our own criterion misses a third case~~ | — | **withdrawn**: a trivially-true equation is not part of the relation, so the criterion is complete and its `acceptable` verdict is correct. The defect is in the instantiation, one level up — see A12 |
| A12 | Instantiation can only weaken a statement, and a faithful environment changes nothing | `Compiler/Instantiate.v`, axiom-free: `instantiation_monotone` (any `genv`), `faithful_preserves_incidence` and `faithful_transfers_the_claim` (separation + non-identity per equation), with `FaithfulnessIsNeeded` proving the hypothesis cannot be dropped | supported |
| A13 | One condition explains all three observed phenomena and all six specifications' hand-coded checks | BBS collision = names identified; Swiss Post identity base and VOPRF vanished equation = names sent to the identity; each spec's check is a side condition on the instantiation, not on the statement | supported |
| A14 | The instantiation theory is wired to this repository's own compiler, and splits the work into a design-time half and a cheap per-instance half | `Compiler/DslInstantiate.v`, axiom-free: `row_of_terms_is_instantiated` and `compiled_matrix_is_instantiated` (the bridge — a cell is the list of (base, coefficient) pairs on a variable), `faithful_tob` + `faithful_tob_sound` (the per-instance decision procedure: group-element comparisons only, no field arithmetic), `faithful_check_transfers_the_design_time_verdict`, `no_instance_rescues_a_bad_statement`, and two computed `Example`s | supported |

## Measurements

| # | Claim | Evidence | Status |
|---|---|---|---|
| M1 | 13,072 leaves from a deployed Helios election: all determined, 0 degenerate, 0 undecided | IACR2024, 932 ballots, 6,524 ballot proofs, tally matches | supported |
| M2 | CMZ 10/10, Privacy Pass 6/6, CFRG P-256 relations 7/7 determined | driver runs | supported |
| M5 | Every relation of Belenios, ElectionGuard, Swiss Post, BBS, ECVRF, VOPRF and FROST, as its specification intends it, is determined | `Examples/Relations/`, transcribed by hand from the seven specifications | supported — again a NEGATIVE result |
| M3 | The criterion fires exactly on the draft's instance-validation controls | E1/E1b `DEGENERATE` with checked witness, E2 `VACUOUS`; E3/E4 rejected below the theory, at the SEC1 decoder and an index bound | supported |
| M4 | **No deployed statement was found degenerate** | all corpora | supported — this is a NEGATIVE result and the paper must say so |

## Claims not to make

- "first verified compiler for ZK statements" — ZKCrypt (CCS 2012) has priority
- "nobody has asked whether statements determine their witness" — Picus has
- "undecidable" — it is a reduction under the DL assumption; the group is finite
- "we found a vulnerability" — we did not
- "Swiss Post's exponentiation proof is broken" — A6 is a gap in the primitives spec's stated input types; we have not shown any call site reaches it, and the protocol spec may constrain the bases at every one
- "our tool found the Swiss Post gap automatically" — the transcription from the spec was by hand; the tool decided the transcribed relations
- "the checker now runs faster" / "we measured a speedup" — A14 makes the design-time split sound, but no driver uses it and nothing has been measured
- "statement quality is settled at design time" — A14 covers the matrix and so the determination axis; vacuity depends on the target vector and is not covered, and the tree cases are unstated
- any third axis or extra check for trivially-true equations — A11 was withdrawn; the case is covered by A12 and needs no new verdict
- "the CFRG draft's validation accepts X" — the validation is sigma-rs's; draft -02 has no validation section
- "sigma-rs performs ten instance checks" without a commit — at 0.3.2 most are gone
