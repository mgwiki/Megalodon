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

## Later July 17 Certificate-Checker Update

The current `vampire/megalodon5` work also improves strict certificate
validation for real hammer proofs, but this remains E4 structural evidence
unless the checked path constructs native proof terms without transitional
`Known` insertion.

Implemented changes:

- Predicate-definition folding now treats stripped universal binders as scoped
  definition parameters. The checker matches the definition body as a pattern,
  binds those parameters to the actual source-context terms, and instantiates
  the definiendum instead of relying on literal de Bruijn equality.
- Predicate-definition folds also accept the boolean/proposition equality
  wrappers that Vampire emits around folded predicate atoms.
- Fold chains use the same scoped matcher at each step, so macro folding can
  proceed through a sequence of generated predicates.
- Skolem formula checking now includes an ordered candidate that consumes
  Vampire's explicit substitution list through nested existential binders.
- THF source parsing now maps formula lambdas to real Megalodon lambdas for
  source comparison instead of introducing a synthetic `vLAM` application.

Validation after these changes:

- `TMPDIR=/project/tmp ./makeopt` passed.
- `TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh`
  passed.
- The cached predicate-definition fold frontier from the previous 300-case
  run moved from `1 PASS / 5 FAIL` to `6 PASS / 0 FAIL`.
- A cached recheck of the previous 300-case directory, without rerunning
  Vampire, reports `118 PASS`, `12` real checker failures, and `170`
  non-certificate placeholders from the old timeout/unavailable cases. The
  previous strict live run had `111 PASS`, so this is a concrete structural
  improvement on the cached corpus.
- A fresh strict live run over `source_linked_strict_100.list`, using THF,
  20-way parallelism, and a 10-second Vampire cap, again reports `PASS 100`.
  The native primitive audit and kernel-v1 metadata audit also pass.

This does not relax the audit response. The next qualifying milestone is
still to isolate the small clausal kernel and eliminate all certificate-derived
`Known` declarations from counted native proof-term paths. These fold and
Skolem changes are useful because they reduce structural rejection before that
kernel boundary, but they are not a substitute for the Vampire-side primitive
IR or the original-source context API.

## Kernel Boundary Extraction

A first small extraction has now moved the shared `kernel_v1` vocabulary out
of `src/vampire_cert_v1.ml` and into `src/vampire_kernel_syntax.ml`.

This module currently owns:

- the accepted schema string, `prover9-small-kernel-v1`;
- the supported kernel rule names;
- the rule-to-required-primitive contract used by strict checking.

`src/vampire_cert_v1.ml` now consumes this module when validating strict
`kernel_v1` metadata. Unsupported kernel rule names are rejected by Megalodon
itself, not only by the shell metadata audit. The negative fixture
`tests/vampire_certificate/native_cert_v1_invalid_kernel_rule.sexp` checks
this behavior.

Validation:

- `TMPDIR=/project/tmp ./makeopt` passed.
- `TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh`
  passed, including the unsupported-rule negative fixture.
- `TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_v1_metadata_audit.sh
  /project/tmp/live_strict_100_megalodon5_after_fold_skolem` passed over
  3145 `kernel_v1` records.

This is deliberately a boundary commit, not a proof-power claim. The next
extractions should move term/clause kernel syntax and theorem-opening logic
out of the monolithic importer, and the Vampire side still needs a real
primitive-step builder instead of metadata assembled in the large exporter.

Follow-up: Vampire now has the corresponding small C++ extraction in
`Shell/MegalodonChecker/MegalodonKernelSyntax.{hpp,cpp}`. That helper owns the
same schema string and rule-to-required-primitive table used while emitting
`kernel_v1` metadata. `Shell/MegalodonChecker/MegalodonChecker.cpp` consumes
the helper instead of carrying the full primitive-contract if-chain inline.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` passed in
  `/project/vampire-leancheck` after wiring the new object into both
  `Makefile` and `cmake/sources.cmake`.
- A 5-case live THF run with the new Vampire binary
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11044` produced
  `PASS 5`.
- The focused native primitive audit passed on that 5-case artifact with
  small-sample minima.
- The kernel-v1 metadata audit passed on that artifact over 280
  `kernel_v1` records.

This still is not the full Vampire primitive-step builder requested by the
audit. It is the first shared contract extraction needed before that builder
can be made explicit and tested independently.

Additional follow-up: Vampire commit `2701d87e4` moves construction of the
`primitive_expansion=prefix`, `primitive_expansion_prefix=...`, and
`primitive_expansion_requires=...` fields into
`MegalodonKernelSyntax`. `MegalodonChecker.cpp` still owns the dynamic choice
between alternative primitives such as `cnf_literal` vs
`cnf_formula_clause`, but the fixed contract field construction is no longer
open-coded in the large exporter.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` passed and produced
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11045`.
- A 5-case live THF run with that binary produced `PASS 5`.
- The focused native primitive audit passed on the artifact.
- The kernel-v1 metadata audit passed over 280 `kernel_v1` records.

Additional follow-up: Vampire commit `37e23d654` makes primitive expansions
an explicit C++ value:

```cpp
struct PrimitiveExpansion {
  std::string prefix;
  std::string requiredRule;
};
```

Call sites now construct a `PrimitiveExpansion` and pass it to
`MegalodonKernelSyntax::appendPrimitiveExpansion`. This is still a small
boundary extraction, not the final Prover9/Ivy-style primitive-step object,
but it removes another raw string-field interface from the large exporter and
gives the next extraction a concrete data type to extend with parent
selection, substitutions, rewritten positions, and introduced-symbol data.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` passed and produced
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11046`.
- A 5-case live THF run with that binary produced `PASS 5`.
- The focused native primitive audit passed on the artifact.
- The kernel-v1 metadata audit passed over 280 `kernel_v1` records, including
  37 rewrite-position records.

Additional follow-up: Vampire commit `770e929fa` introduces the first
`MegalodonKernelStep` builder object in
`Shell/MegalodonChecker/MegalodonKernelSyntax`. The object currently carries:

- the step id;
- the kernel rule name;
- zero or more `PrimitiveExpansion` records;
- the remaining string fields needed by the existing migration certificate.

The main exporter now builds a `MegalodonKernelStep` for the general
`emitKernelV1` path and for the standalone instantiation kernel metadata path,
then renders it through `MegalodonKernelSyntax::kernelStepFields`. This is the
first implementation step for the audit's requested Prover9/Ivy-style
primitive IR. It still preserves the current `step_extra "kernel_v1"` output
shape, and it does not yet move selected literals, substitutions, rewrite
positions, or clauses into typed C++ fields.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` passed and produced
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11047`.
- A 5-case live THF run with that binary produced `PASS 5`.
- The focused native primitive audit passed on the final artifact.
- The kernel-v1 metadata audit passed over 280 `kernel_v1` records, including
  37 rewrite-position records.

Additional follow-up: Vampire commit `cef60e641` moves the general
`kernel_v1` conclusion and parent metadata into structured builder records.
`MegalodonKernelStep` now owns `RenderedKernelConclusion` and
`RenderedKernelParent` values in addition to the primitive-expansion list and
migration payload fields. `MegalodonChecker.cpp` still renders Vampire terms,
clauses, literals, and substitutions, but it now passes the rendered pieces as
records and lets `MegalodonKernelSyntax::kernelStepFields` serialize the
standard `conclusion_*`, `result_*`, `parent_*`, and substituted-parent
fields.

This keeps the existing `step_extra "kernel_v1"` output shape but moves
another part of the certificate structure out of the monolithic exporter. The
next extraction should type selected literals, rewrite positions,
substitutions, and URR trace steps instead of leaving them as ad hoc strings.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` passed and produced
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11048`.
- A 5-case live THF run with that binary produced `PASS 5`.
- The focused native primitive audit passed on the artifact.
- The kernel-v1 metadata audit passed over 280 `kernel_v1` records, including
  37 rewrite-position records.

Additional follow-up: Vampire commit `9719c7960` adds
`RenderedKernelLiteralSelection` to `MegalodonKernelSyntax` and routes the
shared selected-literal helper through it. The general emitter now constructs a
record for fields such as `selected`, `other`, `condition`, `then`, and
`else`, including parent index, literal index, parent unit, and substituted
literal when available. `MegalodonKernelSyntax::appendLiteralSelection`
serializes the standard field cluster.

This is still rendered data, not a typed literal IR. It is a useful migration
step because selected-literal metadata now has a single Vampire-side field
layout owner and can later be backed by typed literal/parent references without
changing all call sites.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` passed and produced
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11049`.
- A 5-case live THF run with that binary produced `PASS 5`.
- The focused native primitive audit passed on the artifact.
- The kernel-v1 metadata audit passed over 280 `kernel_v1` records, including
  37 rewrite-position records.

Additional follow-up: Vampire commit `a3c121ecc` adds
`RenderedKernelRewrite` to `MegalodonKernelSyntax` and routes the superposition
rewrite metadata through it. The record owns the rendered target/equality
substituted literals, target and equality parent locations, rewrite direction,
rewrite position, from/to terms, and rewritten target field layout.

This keeps the `kernel_v1` metadata format stable and still uses rendered
strings, but it removes another high-frequency rewrite-specific field cluster
from `MegalodonChecker.cpp`. The remaining rewrite work is to give
demodulation/rewrite and URR trace steps the same treatment, then replace the
rendered strings with typed literal, term, substitution, and position records.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` passed and produced
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11050`.
- A 5-case live THF run with that binary produced `PASS 5`.
- The focused native primitive audit passed on the artifact.
- The kernel-v1 metadata audit passed over 280 `kernel_v1` records, including
  37 rewrite-position records.

Additional follow-up: Vampire commit `c7131a343` routes demodulation rewrite
metadata through the same `RenderedKernelRewrite` record. The demodulation
path now builds the equality location, target location, from/to terms, rewrite
position, substituted target/equality literals, and rewritten target as a
rewrite record before serializing the standard fields.

This means superposition and demodulation no longer have separate field-layout
code for the same rewrite certificate shape. The representation is still
rendered text rather than typed terms/literals/positions. The remaining
Vampire-side extraction target is URR trace steps and then typed replacements
for these rendered fields.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` passed and produced
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11051`.
- A 5-case live THF run with that binary produced `PASS 5`.
- The focused native primitive audit passed on the artifact.
- The kernel-v1 metadata audit passed over 280 `kernel_v1` records, including
  37 rewrite-position records.
