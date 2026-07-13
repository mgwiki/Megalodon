# Response to `audit-REPORT-2026-07-13.md`

The audit is correct on the main architectural point. The reported live-outline
successes were too permissive because unsupported Vampire-derived clauses could
be reclassified as theorem assumptions. Those runs are useful diagnostics, but
they must not count as proof reconstruction.

The branch now treats certificate v1 as a fail-closed path:

- `scripts/vampire_certificate.py` has `--strict-certificate-v1`.
- Strict mode rejects unsupported rule constructors.
- Strict mode rejects `vampire_derived_clause`,
  `vampire_unexpanded_derived_clause`, AVATAR component assumptions, and any
  `input` with Vampire parents.
- Strict mode rejects outline statistics showing Python inference recovery,
  derived assumptions, CNF projection, or AVATAR fallback.
- `tests/vampire_certificate/run_vampire_outline_smoke.sh` no longer imports
  `scripts/vampire_reconstruct_megalodon.py`.
- The qualifying live smoke now uses already-clausal CNF problems only. THF,
  clausification, AVATAR, lambda/HO, and normal-form examples are diagnostics
  until their transformations have explicit certificates.

This does not make the project finished. It deliberately reduces what is allowed
to count.

## Native Importer Direction

The audit is also correct that the accepted importer should not be the growing
Python prototype. A new native starting point has been added in
`src/vampire_cert_v1.ml` and `src/vampire_cert_v1.mli`.

This is not a port of the Python logic. It is a small OCaml S-expression reader
and certificate AST that uses Megalodon's own `Syntax.tm` representation for
certificate atoms. The source type has no generic "derived input" constructor,
so a Vampire-derived clause cannot be parsed as an input premise.

The next implementation step is to wire this module into Megalodon proper and
add the local mechanical checkers for:

- input source lookup;
- resolution;
- factoring;
- equality resolution;
- paramodulation;
- contradiction;
- proof-term elaboration through existing `Syntax.pf` constructors.

Python remains useful for diagnostics, corpus statistics, and exporter
experiments, but it should not be used for counted reconstruction results.

## Immediate Policy Change

Until the native path is wired through the Megalodon executable, the scoreboard
must distinguish:

- diagnostic Python/prototype successes;
- strict certificate-v1 successes;
- native OCaml-imported successes;
- final Megalodon kernel checks without `admit`, `aby`, or
  `-allowincompleteqed`.

Only the last two categories should be used as evidence that the project is
progressing toward the requested Vampire-to-Megalodon proof reconstruction.
