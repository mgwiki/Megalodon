# Vampire Certificate Tests

This directory tests the replacement certificate path described in
`reports/vampire-megalodon-certificate-spec.md`.

The first smoke tests intentionally cover only binary resolution, factoring,
explicit substitution, equality resolution, paramodulation, and contradiction.
They are not a substitute for
Megalodon kernel checking. Their purpose is to prevent the new path from
accepting malformed certificate constructors while the Vampire exporter and
Megalodon elaborator are built.

Run:

```sh
tests/vampire_certificate/run_native_cert_v1_smoke.sh
```

This is the primary certificate smoke test. It checks the OCaml
`-vampirecertv1` importer against native S-expression fixtures and should be the
first test used for counted reconstruction work.
Use `-vampirecertv1strict` with `-vampirecertv1` for the stricter counted gate;
that mode accepts shape-checked AVATAR component bridge clauses and traced
AVATAR SAT refutations. Legacy AVATAR refutations without `(sat_proof ...)`
remain rejected in strict mode.

The default smoke command is native-only:

```sh
tests/vampire_certificate/run_smoke.sh
```

For live corpora, use:

```sh
tests/vampire_certificate/run_native_live_parallel.sh
```

This script runs Vampire in parallel, extracts only the native S-expression
certificate block emitted by Vampire, and checks it with Megalodon's OCaml
`-vampirecertv1` importer. It rejects certificates that contain
Vampire-derived source assumptions; a counted success must be traced through
certificate steps rather than imported as a fresh input. By default it invokes
Vampire with the same extra proof-detail options used by Megalodon's live
`-vampireabyproof megalodon` bridge:
`--proof_extra lean --skolemization syntactic --shuffle_input off`. Override
`VAMPIRE_PROOF_ARGS` only when intentionally testing another proof-export
configuration.

For freshly exported TH0 files containing `% megalodon_source_map` comments,
set `CHECK_SOURCE_MAP=1` to additionally run `-vampirecertv1source` for every
accepted native certificate. Use `PROBLEM_DIR` or `PROBLEMS_FILE` to select the
fresh source-mapped corpus. The script also writes `rule_counts.txt` under the
work directory so broad runs show which native certificate constructors were
actually exercised.
Set `STRICT_CERT_V1=1` to run the live certificates through
`-vampirecertv1strict`; these stricter runs require source maps and traced SAT
proofs for AVATAR refutations.

For repeatable non-overlapping corpus slices, use:

```sh
tests/vampire_certificate/run_native_corpus_slice.sh
```

Set `PROBLEM_DIR`, `SLICE_START`, `SLICE_SIZE` or `SLICE_END`, `WORK_DIR`,
`JOBS`, `VAMPIRE_SECONDS`, `WALL_SECONDS`, and `MIN_PASS` to control the run.
The defaults use `/project/tmp`, `JOBS=20`, `VAMPIRE_SECONDS=10`,
`CHECK_SOURCE_MAP=1`, and `STRICT_CERT_V1=1`. The wrapper writes the selected
filename list to `/project/tmp/native_slice_START_END.list` and then delegates
to `run_native_live_parallel.sh`.

To export a Megalodon development once and then check the resulting source-mapped
TH0 corpus in parallel, use:

```sh
tests/vampire_certificate/run_source_linked_corpus_parallel.sh
```

Set `MEGALODON_FILE`, `LIMIT`, `JOBS`, `VAMPIRE_SECONDS`, `WALL_SECONDS`, and
`WORK_DIR` to control the corpus and runtime. Temporary corpora and outputs
default to `/project/tmp`. This wrapper enables source-map validation and
strict certificate checking by default; set `STRICT_CERT_V1=0` only for
diagnostic non-counted runs.

The older Python/JSON prototype smoke script is now named
`run_legacy_python_smoke.sh`. It remains useful for diagnostics and regression
comparison, but its successes do not count as accepted Vampire-to-Megalodon
reconstruction.

The legacy smoke script also uses `--emit-megalodon` on the propositional
`valid_resolution.json` certificate and the first-order
`valid_substituted_resolution.json` and
`valid_equality_resolution_refutation.json` and
`valid_paramodulation_refutation.json` and
`valid_paramodulation_negative_refutation.json` and
`valid_paramodulation_side_literals_refutation.json` and
`valid_prop_paramodulation_refutation.json` and
`valid_prop_equality_symmetry_refutation.json` and
`valid_definition_input_refutation.json` certificates, then checks the generated
files with `bin/megalodon`. Those generated proofs are required to contain no
`admit`, no `aby`, and no `-allowincompleteqed`.

The separate `run_vampire_outline_smoke.sh` script runs tiny FOF and THF TPTP
problems through a Vampire binary that emits `megalodon_certificate_clause(...)`
records and explicit `megalodon_certificate_step(...)` records where Vampire
already knows the normalized proof object. It converts the printed outline to
the small JSON certificate fragment, emits Megalodon, and checks it with
`bin/megalodon`. It currently covers the real-output bridge for clause
inputs/derived preprocessing assumptions, Vampire-side `definition_input`
function-definition records, Vampire-side exact `resolve` records,
Vampire-side exact `equality_resolution` records, Vampire-side exact `factor`
records for duplicate-literal contraction, Vampire-side top-level
empty-substitution `paramodulate` records for simple demodulation, and
Vampire-side `paramodulate` plus `equality_symmetry` multi-step records for
definition folding that needs an atomic symmetry step. It also covers
Vampire-side `substitute` plus `resolve` multi-step records for substituted
binary resolution, and Vampire-side `substitute`/optional `equality_symmetry`
plus `paramodulate` expansions for simple superposition. It also covers typed
proposition equality, higher-order application terms, and uniquely determined
resolution-like clause endings. Equality-resolution/factoring/paramodulation
steps that need explicit substitutions or nested or simultaneous rewrite
positions and the remaining unsupported CNF/FOOL transformations are still
recorded or bridged outside the final normalized Vampire certificate until
Vampire exports richer certificate steps for them too.
