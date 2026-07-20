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

`Vampire_kernel_elab` initially defined the clause-proposition boundary:

```text
literal -> proposition
clause  -> proposition
```

It is parameterized by the live logical basis (`false`, `or`, and atom
normalization), so it does not bake in library-specific names.

It now also owns the deterministic Skolem/choice helper boundary that was
previously scattered through `vampire_cert_v1.ml`:

- exact proof-term and term replacement utilities used to reject hidden
  certificate-local witness leaks;
- branch-choice selection from Vampire-emitted Skolem contracts;
- construction of the classical-choice proof term `exists P -> P (Eps P)`;
- explicit transport terms for the epsilon-instantiated body and Vampire's
  witnessed body;
- existential-binder type/count accounting for `vampire_exists_prop` shapes.

These helpers are not proof search.  They are deterministic elaboration of
fields already emitted by Vampire and then checked by Megalodon's ordinary
proof checker.

## Still To Extract

The following remain in the monolithic path and are not yet qualifying
small-kernel elaboration:

- equality resolution and equality factoring;
- superposition/paramodulation;
- FOOL and Boolean simplification;
- Skolemization and Smolka-style preprocessing transformations;
- AVATAR/SAT proof objects;
- proof-term construction for the extracted primitive checks.

## Audit Reset Rules

For this branch, a result is not counted as qualifying E1 unless all of the
following hold:

- the proof is replayed in the original source file and theorem context;
- Vampire is run with a timeout of at most 10 seconds;
- qualifying mode rejects unchecked finishing and broad fallback search;
- the global Megalodon signature is unchanged by certificate-local
  reconstruction state after the command;
- no `aby`, `admit`, incomplete QED, target-stop run, or detached bridge file
  participates in the counted proof;
- every remaining `Known` is either live source context or the fixed logical
  basis;
- no certificate-local Skolem or choice symbol survives in the final proof.

The current counted frontier is therefore deliberately only three
original-source proofs: `FalseE`, `andEL`, and `andER`.  The fourth theorem
`and3I` is kept as a fail-closed regression until the scoped Skolem/choice
transport proof is explicit.

## Qualifying Interpretation

This commit does not establish the five clean E1 examples requested by the
audit.  It does make the next step more concrete: new qualifying work should
extend these modules rather than adding more heuristic replay code to
`megalodon.ml` or broad ad hoc logic to `vampire_cert_v1.ml`.

The immediate plan is:

1. Continue reducing `vampire_cert_v1.ml` by moving pure certificate
   validation and proof-term constructors into `vampire_kernel_check.ml` and
   `vampire_kernel_elab.ml`.
2. Finish the explicit scoped Skolem/choice transport proof for the `and3I`
   certificate using Vampire's emitted branch-choice payload.
3. Re-establish five clean E1 examples under the audit reset rules before
   expanding to larger library theorems, AVATAR, or additional inference
   classes.
