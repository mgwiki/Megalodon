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
`hammer.1007.43.th0.p` past the earlier Skolem formula mismatch. It now
reaches a later clausal proof-term failure:

```text
u210: paramodulate
Term de Bruijn index 15 is out of bounds for context length 15
while checking proof-term application argument: _15
```

This is a small-kernel elaboration issue: reusing stored theorem proofs with
retained step-variable `TLam`s inside paramodulation.

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

The `u210` focused run is currently a failing E3/E2 frontier, not E1 progress.
