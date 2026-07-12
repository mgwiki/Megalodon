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
tests/vampire_certificate/run_smoke.sh
```

The smoke script also uses `--emit-megalodon` on the propositional
`valid_resolution.json` certificate and the first-order
`valid_substituted_resolution.json` and
`valid_equality_resolution_refutation.json` and
`valid_paramodulation_refutation.json` and
`valid_paramodulation_side_literals_refutation.json` certificates, then checks
the generated files with `bin/megalodon`. Those generated proofs are required
to contain no `admit`, no `aby`, and no `-allowincompleteqed`.
