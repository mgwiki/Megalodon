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

The older `run_smoke.sh` script exercises the Python/JSON prototype. It remains
useful for diagnostics and regression comparison, but its successes do not count
as accepted Vampire-to-Megalodon reconstruction.

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
