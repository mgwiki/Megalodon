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

Additional follow-up: Vampire commit `0b5abbeb8` extracts URR trace-step
metadata into `RenderedKernelUrrTraceStep`. The unit-resulting-resolution
emitter still computes the trace locally, but the per-step fields for unit
parent, selected literal, substituted selected/unit literals, and remaining
clause now pass through a single Vampire-side record before serialization.

This finishes the current rendered-record pass over the most frequent
certificate field clusters: parents/conclusions, selected literals, rewrite
records, and URR traces. It is still not the final Prover9/Ivy-style object.
The next audit-relevant step is to replace these rendered records with typed
term, literal, substitution, position, and parent-reference structures, then
lower Vampire macro inferences into those primitive records before Megalodon
checks them.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` passed and produced
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11052`.
- A 5-case live THF run with that binary produced `PASS 5`.
- The focused native primitive audit passed on the 5-case artifact.
- The kernel-v1 metadata audit passed over 280 `kernel_v1` records, including
  37 rewrite-position records.
- A focused two-case URR live run over `hammer.11703.242.th0.p` and
  `hammer.11453.77.th0.p` produced `PASS 2`.
- The focused URR kernel-v1 metadata audit passed over 48 `kernel_v1` records,
  including 3 `unit_resulting_resolution` records.
- The focused URR primitive audit passed with small-sample minima relaxed; the
  two-case sample contains no equality-resolution records, which is expected
  for that artifact rather than a regression.

Additional follow-up: Vampire commit `453f734c9` introduces rendered-domain
wrapper types in `MegalodonKernelSyntax`: unit references, terms, formulas,
literals, clauses, substitutions, and positions are no longer stored in the
builder records as undifferentiated `std::string` fields. The external
`step_extra "kernel_v1"` format is intentionally unchanged, but
`RenderedKernelParent`, `RenderedKernelConclusion`,
`RenderedKernelLiteralSelection`, `RenderedKernelRewrite`, and
`RenderedKernelUrrTraceStep` now expose which certificate fields are clauses,
literals, substitutions, positions, and units.

This is a small but important migration step toward the audit's requested
Prover9/Ivy-style object. It does not yet make the fields fully typed Vampire
kernel terms or lower macro inferences into primitive proof objects. It does
make the next replacement mechanical and reviewable: each rendered wrapper can
be replaced by a typed term/literal/clause/position record without re-auditing
the whole string serializer.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` passed and produced
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11053`.
- A fresh 20-case live THF run with 10-way parallelism and a 10-second Vampire
  cap produced `PASS 20`.
- The native primitive audit passed on that artifact, including 122
  `paramodulate`, 102 `substitute`, 88 `equality_resolution`, and 25
  `resolve` primitive records.
- The kernel-v1 metadata audit passed on that artifact, covering 738
  `kernel_v1` records and 106 rewrite-position records.

Additional follow-up: Vampire commit `99256e4cf` separates the residual
string payload in `MegalodonKernelStep` into explicit `MigrationField` values.
The builder now has typed rendered records for the certificate fields already
extracted, plus a separately named migration bridge for legacy fields that
have not yet been converted.

This keeps the external certificate stable while making the architectural
debt visible in the type. Future commits should shrink `migrationFields` by
moving one field cluster at a time into typed records rather than adding new
unstructured strings to the builder.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` passed and produced
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11054`.
- A fresh 5-case live THF run with 5-way parallelism and a 10-second Vampire
  cap produced `PASS 5`.
- The kernel-v1 metadata audit passed on that artifact, covering 280
  `kernel_v1` records and 37 rewrite-position records.
- The native primitive audit passed with small-sample minima relaxed; the
  artifact covered 37 `paramodulate`, 46 `substitute`, 36
  `equality_resolution`, and 7 `resolve` records.

Additional follow-up: Vampire commit `c2393b33c` removes another clausal
field cluster from `migrationFields`: primitive parent substitutions are now
stored as `RenderedKernelPrimitiveParentSubstitution` records on
`MegalodonKernelStep`. Superposition, equality factoring, resolution, and
factoring still emit the same `primitive_parent_N_substitution=...` metadata,
but that metadata is now owned by the step builder rather than assembled as
free-form strings at the call sites.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` passed and produced
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11055`.
- A fresh 10-case live THF run with 10-way parallelism and a 10-second Vampire
  cap produced `PASS 10`.
- The kernel-v1 metadata audit passed on that artifact, covering 361
  `kernel_v1` records, 47 rewrite-position records, and 10
  `subsumption_resolution` records.
- The native primitive audit passed on the same artifact, including 55
  `paramodulate`, 53 `substitute`, 43 `equality_resolution`, 11 `resolve`,
  and 2 `equality_symmetry` records.

Additional follow-up: Vampire commit `c105b6e53` extracts Skolem
introduced-symbol metadata into `RenderedKernelSkolemIntroducedSymbol` and
`RenderedKernelSkolemDependency` records. The `kernel_v1` Skolem serializer
now owns the `introduced_count`, `introduced_N_kind`, raw symbol id, recovered
symbol/declaration, replaced variable, replaced-variable sort, witness
term/sort, source-variable application count, dependency term/variable/sort,
and `classical_choice` fields.

This is directly relevant to the Smolka-style transformation layer. The
records still carry rendered s-expressions rather than fully typed Vampire
terms, but the Skolem proof-critical data is no longer a long sequence of
free-form migration strings inside `MegalodonChecker.cpp`. The next step is
to replace these rendered Skolem records with typed Vampire term/type/symbol
references and connect the corresponding Megalodon proof term to the
source-context Skolemization proof.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` passed and produced
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11057`.
- A fresh 20-case live THF run with 10-way parallelism and a 10-second Vampire
  cap produced `PASS 20`.
- The kernel-v1 metadata audit passed on that artifact, covering 738
  `kernel_v1` records, 106 rewrite-position records, and 18 `skolemize`
  records.
- The native primitive audit passed on the same artifact, including 18
  `skolem_formula`, 122 `paramodulate`, 102 `substitute`, 88
  `equality_resolution`, and 25 `resolve` records.

Additional follow-up: Vampire commit `2e4441c77` extracts a shared
source/result formula transformation record into
`RenderedKernelSourceFormulaTransform` and
`RenderedKernelTransformationPair`. The formula-copy, formula-normalize, and
FOOL-formula kernel records now serialize `source_unit`, `parent_0_unit`,
`source_formula`, `parent_0_formula`, `proof_parent_count`, `result_formula`,
copy kind, normal-form rule, and transformation pair fields from this
Vampire-side record rather than from repeated free-form field vectors.

This is another step toward the Smolka-style transformation layer. The record
still carries rendered formula s-expressions, so it is not yet a checked
Megalodon proof of the preprocessing transformation. It does, however, make
the transformation boundary explicit and shared across the normal-form and
FOOL cases that were previously assembled ad hoc.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` passed and produced
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11058`.
- A fresh 20-case live THF run with 10-way parallelism and a 10-second Vampire
  cap produced `PASS 20`.
- The kernel-v1 metadata audit passed on that artifact, covering 738
  `kernel_v1` records, 49 `fool_formula`, 43 `formula_normalize`, 37
  `formula_copy`, and 106 rewrite-position records.
- The native primitive audit passed on the same artifact, including 330
  `fool_atom_lift`, 43 `ennf_formula`, 8 `formula_copy`, 29
  `formula_term_copy`, 122 `paramodulate`, and 102 `substitute` records.

Additional follow-up: Vampire commit `f102adc80` extracts rectification
renaming metadata into `RenderedKernelRectifyRenaming` and
`RenderedKernelRectifyRenamings`. The `rectify_formula` kernel record now
serializes `renaming_count`, bounded `renaming_N_source`,
`renaming_N_target`, `renaming_N_substitution`, and `renaming_truncated`
through `MegalodonKernelSyntax`. When source and result formulas are both
available, the same `RenderedKernelSourceFormulaTransform` record supplies
the source/result formula context for rectification.

This further reduces the Smolka-style preprocessing migration surface. The
renamings are still rendered formula/substitution s-expressions, not typed
Vampire objects and not yet Megalodon proof terms. The next implementation
step is to make these records typed enough for the Megalodon importer to
construct the actual rectification proof rather than only validating metadata.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` passed and produced
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11059`.
- A fresh 20-case live THF run with 10-way parallelism and a 10-second Vampire
  cap produced `PASS 20`.
- The kernel-v1 metadata audit passed on that artifact, covering 738
  `kernel_v1` records, 77 `rectify_formula` records, and 106 rewrite-position
  records.
- The native primitive audit passed on the same artifact, including 77
  `rectify_formula`, 43 `ennf_formula`, 18 `skolem_formula`, 122
  `paramodulate`, and 102 `substitute` records.

Additional follow-up: Vampire commit `60866e6c8` extracts CNF
source-to-clause metadata into `RenderedKernelCnfClause`. The `cnf_clause`
kernel record now serializes source unit, parent unit, proof-parent count,
source kind, source formula or source clause, result clause, parent clause
count, and clause index/count fields through `MegalodonKernelSyntax`.

This is the CNF analogue of the source/result formula and rectification
record extractions. It keeps the certificate format stable while moving the
formula-to-clause boundary out of ad hoc string assembly. The remaining
proof-reconstruction work is to make these CNF records typed and consume them
in Megalodon's preprocessing/source proof layer, so CNF projection is checked
as a proof step rather than only structurally validated.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` passed and produced
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11060`.
- A fresh 20-case live THF run with 10-way parallelism and a 10-second Vampire
  cap produced `PASS 20`.
- The kernel-v1 metadata audit passed on that artifact, covering 738
  `kernel_v1` records, 101 `cnf_clause` records, and 106 rewrite-position
  records.
- The native primitive audit passed on the same artifact, including 71
  `cnf_formula_clause`, 30 `cnf_literal`, 77 `rectify_formula`, 43
  `ennf_formula`, 122 `paramodulate`, and 102 `substitute` records.

Additional follow-up: Vampire commit `05fe04c5d` extracts
subsumption-resolution pivot metadata into
`RenderedKernelSubsumptionResolutionPivot`. The main/side parent indexes,
side substitution, side pivot literal, pivot location, substituted side pivot,
and symmetry flag are now one structured record serialized by
`MegalodonKernelSyntax`.

This continues shrinking the migration bridge in the audit-requested
direction. The field values are still rendered s-expressions, but the
remaining legacy payload is narrower: source/preprocessing annotations,
Skolem introduced-symbol details, SAT/AVATAR traces, and miscellaneous
rule-specific formula fields remain the main migration-field clusters.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` passed and produced
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11056`.
- A fresh 10-case live THF run with 10-way parallelism and a 10-second Vampire
  cap produced `PASS 10`.
- The kernel-v1 metadata audit passed on that artifact, covering 361
  `kernel_v1` records, 47 rewrite-position records, and 10
  `subsumption_resolution` records.
- The native primitive audit passed on the same artifact, including 55
  `paramodulate`, 53 `substitute`, 43 `equality_resolution`, 11 `resolve`,
  and 2 `equality_symmetry` records.

Additional follow-up: Vampire commit `46ac092f5` extracts predicate
definition-fold metadata into explicit certificate records:
`RenderedKernelDefinitionFold` and `RenderedKernelDefinitionParent`. The
`predicate_definition_fold` and `predicate_definition_fold_chain` kernel
records now serialize `source_unit`, optional source formula, ordered
definition parents, definition formulas, definition symbols, and result
formula through `MegalodonKernelSyntax` instead of assembling those fields in
the large exporter branch.

This follows the same direction as the CNF, rectification, Skolem, and
source-formula transform extractions. It is not yet a native Megalodon proof
of predicate definition folding: the formulas and symbols are still rendered
certificate payloads, and Megalodon still needs a typed importer that turns
these definition-fold objects into proof terms. The important design change
is that the boundary is now a named Vampire-side record rather than another
free-form migration-field cluster.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` passed and produced
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11061`.
- A fresh 20-case strict source-linked live THF run with `JOBS=10` and
  `VAMPIRE_SECONDS=10` produced `PASS 20`.
- The kernel-v1 metadata audit passed on that strict artifact, covering 738
  `kernel_v1` records and 106 rewrite-position records.
- The native primitive audit passed on the same strict artifact, including
  18 `skolem_formula`, 122 `paramodulate`, 102 `substitute`, 88
  `equality_resolution`, and 25 `resolve` records.
- The strict 20-case sample did not contain predicate definition folding, so
  a focused non-strict smoke run was made for `hammer.11364.33.th0.p`, which
  produced `PASS 1` and two `predicate_definition_fold` records in
  `/project/tmp/live_definition_fold_focus_vampire_nonstrict`.
- The focused kernel-v1 metadata audit passed on that artifact, covering 214
  `kernel_v1` records, 20 rewrite-position records, and 2
  `predicate_definition_fold` records. The focused native primitive audit was
  not used as a pass/fail signal because its fixed one-sample minima require
  an `equality_symmetry` record that this particular proof does not contain.

Additional follow-up: Vampire commit `ea3f4631a` extracts
unit-resulting-resolution trace metadata into `RenderedKernelUrrTrace`. The
exporter already built `RenderedKernelUrrTraceStep` objects, but previously
flattened them immediately into the residual field vector. The kernel step
now owns the trace main parent, ordered trace steps, selected and substituted
literals, unit-parent clauses, intermediate remainders, and final trace
remainder through the centralized `MegalodonKernelSyntax` serializer.

This is still certificate metadata, not a completed Megalodon proof-term
implementation of URR. It does, however, remove another concrete clausal
macro explanation from the unstructured migration path and makes the
Prover9/Ivy-style expansion boundary explicit: URR is represented as a
sequence of resolve-compatible trace steps that Megalodon can later consume
as primitive proof terms.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` passed and produced
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11062`.
- A fresh 20-case strict source-linked live THF run with `JOBS=10` and
  `VAMPIRE_SECONDS=10` produced `PASS 20`.
- The kernel-v1 metadata audit passed on that strict artifact, covering 738
  `kernel_v1` records and 106 rewrite-position records.
- The native primitive audit passed on that same strict artifact, including
  122 `paramodulate`, 102 `substitute`, 88 `equality_resolution`, and 25
  `resolve` records.
- A focused two-case strict source-linked URR run for `hammer.11453.77.th0.p`
  and `hammer.11703.242.th0.p` produced `PASS 2` in
  `/project/tmp/live_urr_trace_record_vampire`.
- The focused kernel-v1 metadata audit passed on that artifact, covering 48
  `kernel_v1` records and 3 `unit_resulting_resolution` records. The focused
  native primitive audit was not used as a pass/fail signal because this
  intentionally narrow sample has no `equality_resolution` record, while the
  broader strict primitive audit passed.

Additional follow-up: Vampire commit `96cce436a` extracts
`avatar_component` metadata into explicit `RenderedKernelAvatarComponent` and
`RenderedKernelAvatarSplit` records. The exporter now builds one object for
the AVATAR component result clause, component literal payloads, split count,
and split descriptors (`level`, `var`, and polarity), and
`MegalodonKernelSyntax` owns the serialization of those fields.

This is a direct response to the audit's request to stop growing anonymous
migration-field blobs. It is not yet a native Megalodon proof of AVATAR
reasoning or SAT refutation. The value is that one AVATAR macro boundary now
has a named Vampire-side certificate object that can later be lowered to a
small primitive sequence or consumed by a dedicated Megalodon AVATAR proof
layer. The remaining AVATAR work is still substantial: `avatar_definition`,
`avatar_split`, `split_dependency`, and `avatar_refutation` need the same
explicit treatment, and the SAT/refutation proof must eventually be checked
rather than structurally accepted.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` passed and produced
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11063`.
- A fresh 20-case strict source-linked live THF run with `JOBS=10` and
  `VAMPIRE_SECONDS=10` produced `PASS 20`.
- The kernel-v1 metadata audit passed on that artifact, covering 738
  `kernel_v1` records and 8 `avatar_component` records.
- The native primitive audit passed on the same artifact, including 8
  `avatar_component`, 8 `avatar_definition`, 2 `avatar_refutation`, 10
  `avatar_split`, 47 `split_dependency`, 122 `paramodulate`, and 102
  `substitute` records.

Additional follow-up: Vampire commit `e03e87a83` extracts
`avatar_definition` metadata into `RenderedKernelAvatarDefinition`. The
component split descriptor, rendered component clause, kernel clause sexpr,
component variable sorts, component de Bruijn sorts, and result clause are
now owned by the Vampire-side kernel syntax object for `kernel_v1`
serialization.

The legacy diagnostic `avatar_definition` `step_extra` is intentionally left
unchanged for compatibility, but the strict `kernel_v1` certificate no longer
gets this record by copying an anonymous `fields` vector from
`MegalodonChecker.cpp`. This continues the audit-requested movement toward a
named certificate object layer that can be lowered to small checked steps.
It is still not a native proof of AVATAR definitions: the payload is rendered
text, and Megalodon still needs typed consumption and proof-term generation
for the AVATAR/SAT layer.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` passed and produced
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11064`.
- A fresh 20-case strict source-linked live THF run with `JOBS=10` and
  `VAMPIRE_SECONDS=10` produced `PASS 20`.
- The strict run included 8 `avatar_definition` records and 8
  `avatar_component` records.
- The kernel-v1 metadata audit passed on that artifact, covering 738
  `kernel_v1` records, 8 `avatar_definition` records, and 8
  `avatar_component` records.
- The native primitive audit passed on the same artifact, including 8
  `avatar_definition`, 8 `avatar_component`, 2 `avatar_refutation`, 10
  `avatar_split`, and 47 `split_dependency` records.

Additional follow-up: Vampire commit `f4f4ecf59` extracts
`split_dependency` metadata into `RenderedKernelSplitDependency` and
`RenderedKernelSplitDependencyItem`. The strict kernel record now owns the
dependency split descriptors, optional component clauses, component kernel
clause sexprs, component variable/db sort annotations, preserved lambda and
scoped-split annotations, dependency count, and result clause through
`MegalodonKernelSyntax`.

This is a higher-frequency AVATAR-side boundary than `avatar_definition`: the
20-case strict sample contains 47 `split_dependency` records. The change
keeps the legacy diagnostic `split_dependency` `step_extra` stable, but the
`kernel_v1` record no longer depends on copying the legacy field vector.
This still does not prove split dependencies in Megalodon; the data is now
organized for a later typed AVATAR/SAT proof layer or primitive lowering.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` passed and produced
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11065`.
- A fresh 20-case strict source-linked live THF run with `JOBS=10` and
  `VAMPIRE_SECONDS=10` produced `PASS 20`.
- The strict run included 47 `split_dependency` records.
- The kernel-v1 metadata audit passed on that artifact, covering 738
  `kernel_v1` records and 47 `split_dependency` records.
- The native primitive audit passed on the same artifact, including 47
  `split_dependency`, 8 `avatar_definition`, 8 `avatar_component`, 2
  `avatar_refutation`, and 10 `avatar_split` records.

Additional follow-up: Vampire commit `1fbfd3199` extracts
`avatar_split` metadata into `RenderedKernelAvatarSplitStep` and related
subrecords. The strict kernel record now owns the source unit and source
clause, result formula/clause, Vampire rule name, rendered source/target
text, previous split descriptors, SAT literals, component parent references,
literal classes, matched split levels, and parent-variable bindings through
`MegalodonKernelSyntax`.

This removes another large AVATAR cluster from the direct field-splicing path
in `MegalodonChecker.cpp`. The old diagnostic `avatar_split` `step_extra`
remains stable, while the `kernel_v1` AVATAR split record is now a named
Vampire-side object. This still does not make AVATAR split reasoning a native
Megalodon proof: the next qualifying step is to type these payloads and
consume them in a checked AVATAR/SAT proof layer or lower them to a small
primitive kernel.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` passed and produced
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11066`.
- A fresh 20-case strict source-linked live THF run with `JOBS=10` and
  `VAMPIRE_SECONDS=10` produced `PASS 20`.
- The strict run included 10 native `avatar_split` records and 7
  `kernel_v1` `avatar_split` records.
- The kernel-v1 metadata audit passed on that artifact, covering 738
  `kernel_v1` records and 7 `avatar_split` records.
- The native primitive audit passed on the same artifact, including 10
  `avatar_split`, 47 `split_dependency`, 8 `avatar_definition`, 8
  `avatar_component`, and 2 `avatar_refutation` records.

Additional follow-up: Vampire commit `cc64aa131` extracts
`avatar_refutation` metadata into `RenderedKernelAvatarRefutation` and SAT
subrecords for inputs, proof steps, and proof parents. The strict kernel
record now owns the empty result clause, optional SAT refutation clause,
ordered SAT inputs with origin units, SAT proof step count, input/RUP step
kinds, RUP parent ids, parent clauses, and parent counts through
`MegalodonKernelSyntax`.

This completes the first AVATAR metadata-object extraction pass:
`avatar_component`, `avatar_definition`, `split_dependency`, `avatar_split`,
and `avatar_refutation` are now represented as named Vampire-side kernel
objects for `kernel_v1` serialization. This is still not a proof-completion
claim. The AVATAR/SAT payloads remain rendered certificate data, and
Megalodon still needs a typed checked SAT/AVATAR proof layer or a lowering of
these records into the small primitive kernel.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` passed and produced
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11067`.
- A fresh 20-case strict source-linked live THF run with `JOBS=10` and
  `VAMPIRE_SECONDS=10` produced `PASS 20`.
- The strict run included 2 native `avatar_refutation` records and 2
  `kernel_v1` `avatar_refutation` records.
- The kernel-v1 metadata audit passed on that artifact, covering 738
  `kernel_v1` records and 2 `avatar_refutation` records.
- The native primitive audit passed on the same artifact, including 2
  `avatar_refutation`, 10 `avatar_split`, 47 `split_dependency`, 8
  `avatar_definition`, and 8 `avatar_component` records.

Additional follow-up: Megalodon now also validates structured
`avatar_component` `kernel_v1` metadata as typed certificate data. The
importer checks that the metadata result/conclusion clauses match the parsed
`avatar_component` step, that `literal_count` and each `literal_i` field match
the non-split component literals, and that the single split descriptor
`split_0_level`/`split_0_var`/`split_0_positive` is well formed and matches
the actual `split_N` literal in the certificate clause. This uses Vampire's
existing convention that a positive component split descriptor is represented
by a negative `split_N` literal in the component clause.

This keeps the AVATAR work on the certificate-object path: Vampire emits the
component metadata, and Megalodon checks it directly. It is still not a claim
that AVATAR component reasoning has been fully lowered to final Megalodon
proof terms in the native small-kernel path.

Validation:

- `TMPDIR=/project/tmp ./makeopt` passed in `/project/Megalodon`.
- New focused fixtures
  `native_cert_v1_avatar_component_kernel_valid.sexp` and
  `native_cert_v1_avatar_component_kernel_split_bad.sexp` cover the valid
  metadata path and a bad split descriptor.
- `TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh`
  passed.
- A fresh 20-case strict source-linked live THF run with `JOBS=10` and
  `VAMPIRE_SECONDS=10` produced `PASS 20` using
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11067`.
- The kernel-v1 metadata audit passed on that artifact, covering 738
  `kernel_v1` records and 8 `avatar_component` records.
- The native primitive audit passed on the same artifact, including 8
  `avatar_component`, 8 `avatar_definition`, 2 `avatar_refutation`, 10
  `avatar_split`, and 47 `split_dependency` records.

Additional follow-up: Megalodon now validates structured
`avatar_definition` `kernel_v1` metadata as typed certificate data. The
importer checks `component_split_level`, `component_split_var`,
`component_split_positive`, `component_clause_sexpr`,
`component_clause_variable_sort_count`, `component_clause_db_sort_count`, and
`result_clause` against the parsed `avatar_definition` step. The split
variable and polarity must match the certificate constructor, the component
clause sexpr must match the result clause, and the variable/de-Bruijn sort
counts must enumerate concrete fields.

This moves another AVATAR object from shell-audited string payloads into the
Megalodon typed certificate boundary. It remains a validation step, not final
proof-term lowering for AVATAR definitions.

Validation:

- `TMPDIR=/project/tmp ./makeopt` passed in `/project/Megalodon`.
- New focused fixtures
  `native_cert_v1_avatar_definition_kernel_valid.sexp` and
  `native_cert_v1_avatar_definition_kernel_polarity_bad.sexp` cover the valid
  metadata path and a bad split polarity.
- `TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh`
  passed.
- A fresh 20-case strict source-linked live THF run with `JOBS=10` and
  `VAMPIRE_SECONDS=10` produced `PASS 20` using
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11067`.
- The kernel-v1 metadata audit passed on that artifact, covering 738
  `kernel_v1` records and 8 `avatar_definition` records.
- The native primitive audit passed on the same artifact, including 8
  `avatar_definition`, 8 `avatar_component`, 2 `avatar_refutation`, 10
  `avatar_split`, and 47 `split_dependency` records.

Additional follow-up: Megalodon now validates structured
`split_dependency` `kernel_v1` metadata as typed certificate data. The live
format attaches the metadata to the owner unit, while the first-class
certificate step is suffixed, such as `u122_split_dependency`; the importer
now resolves that mapping explicitly. It checks the owner unit, result clause,
dependency count, every dependency split level/variable/polarity, component
clause sexpr, and component variable/de-Bruijn sort count fields against the
parsed `SplitDependency` step.

This covers the highest-frequency AVATAR-side metadata family in the focused
20-case sample: 47 split-dependency records. It is still certificate-object
validation; proof-term lowering of split dependencies remains open.

Validation:

- `TMPDIR=/project/tmp ./makeopt` passed in `/project/Megalodon`.
- New focused fixtures
  `native_cert_v1_split_dependency_kernel_valid.sexp` and
  `native_cert_v1_split_dependency_kernel_split_bad.sexp` cover the valid
  metadata path and a bad dependency split descriptor.
- `TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh`
  passed.
- A fresh 20-case strict source-linked live THF run with `JOBS=10` and
  `VAMPIRE_SECONDS=10` produced `PASS 20` using
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11067`.
- The kernel-v1 metadata audit passed on that artifact, covering 738
  `kernel_v1` records and 47 `split_dependency` records.
- The native primitive audit passed on the same artifact, including 47
  `split_dependency`, 8 `avatar_definition`, 8 `avatar_component`, 2
  `avatar_refutation`, and 10 `avatar_split` records.

Additional follow-up: Megalodon now validates the structured
`avatar_refutation` `kernel_v1` metadata as typed SAT certificate data before
the ordinary strict step checker runs. The importer parses and checks the
empty result clause, empty SAT refutation clause, ordered SAT input clauses,
input origin units, SAT proof-step ids, input/RUP step kinds, RUP parent ids,
RUP parent clauses, and the final empty SAT clause. RUP parents must refer to
earlier SAT proof steps and the recorded parent clauses must match those
earlier steps. Input origins are checked against earlier certificate units and
against the `avatar_refutation` parent list when the certificate step carries
one.

This is the first Megalodon-side typed consumption pass for the
AVATAR/SAT data emitted by the named Vampire-side `RenderedKernelAvatar*`
objects. It is deliberately classified as certificate checking, not as
completed Megalodon proof-term reconstruction: the SAT/RUP trace is now a
checked object at the importer boundary, but it still has to be lowered into
Megalodon proof terms or into a small dedicated AVATAR/SAT kernel whose
checker constructs proof terms.

Validation:

- `TMPDIR=/project/tmp ./makeopt` passed in `/project/Megalodon`.
- A new negative regression
  `tests/vampire_certificate/native_cert_v1_avatar_refutation_kernel_bad_parent.sexp`
  is rejected because a recorded SAT RUP parent id is not an earlier proof
  step.
- `TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh`
  passed.
- A fresh 20-case strict source-linked live THF run with `JOBS=10` and
  `VAMPIRE_SECONDS=10` produced `PASS 20` using
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11067`.
- The kernel-v1 metadata audit passed on that artifact, covering 738
  `kernel_v1` records and 2 `avatar_refutation` records.
- The native primitive audit passed on the same artifact, including 2
  `avatar_refutation`, 10 `avatar_split`, 47 `split_dependency`, 8
  `avatar_definition`, and 8 `avatar_component` records.
