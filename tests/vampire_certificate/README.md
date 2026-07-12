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
`valid_resolution.json` certificate and checks the generated file with
`bin/megalodon`. That generated proof is required to contain no `admit`, no
`aby`, and no `-allowincompleteqed`.
