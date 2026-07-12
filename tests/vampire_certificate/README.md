# Vampire Certificate Tests

This directory tests the replacement certificate path described in
`reports/vampire-megalodon-certificate-spec.md`.

The first smoke tests intentionally cover only propositional binary resolution,
factoring, and contradiction. They are not a substitute for Megalodon kernel
checking. Their purpose is to prevent the new path from accepting malformed
certificate constructors while the Vampire exporter and Megalodon elaborator are
built.

Run:

```sh
tests/vampire_certificate/run_smoke.sh
```

