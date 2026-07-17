# Vampire to Megalodon Design Update

Date: 2026-07-17

Branch: `vampire/megalodon5`

Audit basis:

- `reports/audit-REPORT-2026-07-16.md`
- `reports/audit-response-2026-07-17.md`
- `reports/VAMPIRE-MEGALODON-DESIGN-PLAN-2026-07-16.md`
- `reports/VAMPIRE-MEGALODON-SMALL-KERNEL-PLAN-2026-07-16.md`
- `reports/VAMPIRE-MEGALODON-EXECUTION-PLAN-2026-07-16.md`

## Executive Correction

The July 16 audit is accepted. The project should not pursue broader
Megalodon-side reconstruction as the main path. The qualifying path is:

```text
Vampire primitive expansion
  -> small typed clausal certificate
  -> Megalodon native Syntax.pf checker
  -> source/preprocessing proof layer
  -> original Megalodon theorem/context
```

This means no pass-count milestone may rely on certificate-derived `Known`
propositions, and strict live certificate validation remains integration
evidence until a native proof term is checked.

## Current Technical Update

The counted core path now has a narrow direct-existential Skolemization proof
using an explicit generated delta definition and classical choice. The checker
also handles dependent generated Skolem delta unfolding at conversion time
rather than by eagerly rewriting certificate formulas.

That moved the representative real hammer case
`hammer.1007.43.th0.p` past the earlier Skolem formula mismatch. A later
clausal proof-term failure at `u210` exposed a theorem-opening issue:
proof bodies were being wrapped in result-step `TLam`s while still containing
unclosed result-variable references. Commit `7bc7068` fixed this by closing
native proof bodies in the intended result-variable context before adding the
result binders. The focused regenerated `hammer.1007.43` certificate now
checks 68 native core proof-term steps.

## Rejected Quick Fixes

Several broad fixes were tested and rejected:

- disabling proof shifting for closed equality parents in paramodulation;
- broadly changing local closure to ignore global certificate variables;
- globally normalizing every native proof before storing it;
- treating generated Skolem symbols as ordinary function definitions in the
  main formula comparison path;
- eagerly expanding generated Skolem definitions inside certificate formulas.

These failures support the audit's warning. The next implementation needs a
specified theorem-opening operation with a clear binder invariant, not another
broad Megalodon-side heuristic.

## Kernel-Opening Requirement

The native checker stores step proofs as theorem-like proof terms:

```text
forall step variables, clause proposition
```

A later primitive may need that proof in a result context that keeps, drops, or
substitutes parent variables. The implementation must define one operation:

```ocaml
open_step_theorem :
  global_context ->
  parent_step_variables ->
  result_step_variables ->
  substitution ->
  stored_proof ->
  opened_proof
```

Required behavior:

- exact retained variables are opened without stale shifted applications;
- substituted variables are closed in the result context;
- dropped variables must have explicit substitutions or fail closed;
- globals and result variables must have a documented shadowing rule;
- the operation must be shared by `instantiate`, `resolve`,
  `equality_resolution`, `equality_factoring`, `paramodulate`, and `flip`.

This belongs in the future isolated kernel module, not as another collection
of local special cases in `src/vampire_cert_v1.ml`.

## Source-Context Requirement

The original-context part remains underdeveloped unless this concrete API is
implemented and consumed by the checker:

```ocaml
type source_proof =
  | GlobalKnown of string * Syntax.tm
  | LocalHyp of int * Syntax.tm
  | Definitional of Syntax.tm * Syntax.pf
  | Generated of Syntax.tm * Syntax.pf

type source_context = source_id -> source_proof
```

The source context must explain global facts, local hypotheses, definitions,
set-command generated equalities, conjecture negation, and generated formulas
from Smolka-style transformations.

## Revised Immediate Queue

1. Keep all counted native paths free of certificate-derived `Known`.
2. Extract small clausal-kernel data structures and theorem-opening logic out
   of the monolithic importer.
3. Specify and implement `open_step_theorem`, then retest the focused
   `hammer.1007.43` `u210` case.
4. Start the Vampire `MegalodonKernelStep` builder so macro lowerings become
   first-class primitive records.
5. Implement source-context binding for a small committed example set,
   including one local hypothesis and one set-command equality.
6. Add Smolka-style transformations one at a time, with proof terms.

## Evidence Labels

- E1: original-context, source-bound, closed native proof terms.
- E2: exported-THF-bound closed native proof terms.
- E3: primitive-kernel native proof-term checks, synthetic or live.
- E4: structural certificate/source/metadata validation and transitional
  diagnostics.

Current evidence after commits `7bc7068` and `ab4765a`:

- Focused regenerated `hammer.1007.43` native core proof-term check passes,
  including the previous `u210` paramodulation case.
- The staged closed audit covers all 172 tracked `closed_cases` certificates
  as a disjoint highest-layer assignment:
  - core-only: 24
  - preprocess: 84
  - Skolem: 35
  - definition: 12
  - AVATAR: 15
  - inequality: 1
  - definition-rewrite: 1
- The same aggregate run reports `LAYERED_CLOSED_TOTAL 172`,
  `LAYERED_CLOSED_COVERED 172`, `LAYERED_CLOSED_MISSING 0`,
  `LAYERED_CLOSED_EXTRA 0`, and `LAYERED_CLOSED_DUPLICATE 0`.
- A fresh strict live run over `source_linked_strict_100.list`, with THF input,
  20-way parallelism, and a 10-second Vampire cap, reports `PASS 100`.
  The generated certificate corpus includes 1300 `fool_atom_lift`, 490
  `paramodulate`, 400 `substitute`, 338 `superposition` kernel records, 77
  `skolem_formula`, 39 `avatar_definition`, and 215 `split_dependency`
  records.
- The native primitive audit and kernel-v1 metadata audit pass on that fresh
  live corpus.

This is stronger E2/E4 evidence and some E3 evidence for the native core
proof-term path. It is still not a claim of project completion: E1
original-context proof composition for larger Megalodon developments remains
the main unfinished requirement.
