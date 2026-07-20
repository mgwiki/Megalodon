# Kernel Extraction Update, 2026-07-20

This branch starts the audit-requested extraction from the large certificate
reconstructor into small deterministic modules.

## Extracted Now

Two new modules are compiled into Megalodon:

- `src/vampire_kernel_check.ml`
- `src/vampire_kernel_elab.ml`

`Vampire_kernel_check` contains deterministic clause-level checks for:

- explicit substitution;
- condensation;
- duplicate-literal factoring;
- binary resolution with explicit pivot indices.

`src/vampire_cert_v1.ml` now delegates those four simple clause primitives to
`Vampire_kernel_check`.  This is intentionally small.  It is the first live
extraction step, not a parallel unused implementation.

`Vampire_kernel_elab` currently defines the clause-proposition boundary:

```text
literal -> proposition
clause  -> proposition
```

It is parameterized by the live logical basis (`false`, `or`, and atom
normalization), so it does not bake in library-specific names.

## Still To Extract

The following remain in the monolithic path and are not yet qualifying
small-kernel elaboration:

- equality resolution and equality factoring;
- superposition/paramodulation;
- FOOL and Boolean simplification;
- Skolemization and Smolka-style preprocessing transformations;
- AVATAR/SAT proof objects;
- proof-term construction for the extracted primitive checks.

## Qualifying Interpretation

This commit does not establish the five clean E1 examples requested by the
audit.  It does make the next step more concrete: new qualifying work should
extend these modules rather than adding more heuristic replay code to
`megalodon.ml` or broad ad hoc logic to `vampire_cert_v1.ml`.
