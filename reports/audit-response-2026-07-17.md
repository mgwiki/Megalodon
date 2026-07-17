# Audit Response for REPORT-2026-07-16

Date: 2026-07-17

Branch: `vampire/megalodon5`

Audit file:

- `reports/audit-REPORT-2026-07-16.md`

## Summary

The audit is accepted. The most important correction is the trust-boundary
reset: broad preprocessing runs that relied on certificate-derived `Known`
propositions are structural diagnostics, not proof reconstruction evidence.
The qualifying path is the native small-kernel `Syntax.pf` path, then
source/preprocessing proofs, then original-context theorem reconstruction.

## Changes Already Made on This Branch

- `-vampirecertv1preprocesspfcheck` now fails closed by default when a step
  would require installing a certificate-derived theorem into `Known`.
- The old behavior is available only through
  `MEGALODON_CERT_ALLOW_TRANSITIONAL_PREPROCESS_KNOWN=1`, and the harnesses
  classify such runs as `PREPROCESS_STRUCTURAL_PASS`.
- `tests/vampire_certificate/README.md` now separates `corepfcheck` from
  structural preprocessing diagnostics.
- The main design plans now use evidence classes E1-E4 and test stages T0-T4
  so integration results are not confused with proof reconstruction.
- The real-core frontier is now measured separately from synthetic core
  fixtures.

## Current Technical Reading

The current native proof-term frontier is real but still limited. The good
part is that `corepfcheck` constructs and checks `Syntax.pf` terms for the
source-entry/core subset. The bad part is that most real hammer certificates
still stop before the clausal core because the source/preprocessing layer is
incomplete.

The largest immediate blocker is Skolemization. Vampire emits useful metadata:
the source existential, the result formula, introduced Skolem symbols, and a
`parent_1_formula` implication from the existential to the instantiated body.
However, that implication is currently only annotation data. It is not a
proof-producing certificate step, so Megalodon cannot count it without either:

1. a real proof term based on conservative Skolem definitions and choice, or
2. a Vampire-side primitive expansion that explains the transformation in
   small checked steps.

The project should not solve this by adding another dynamic `Known`
proposition for `parent_1_formula`.

## Revised Work Order

1. Keep certificate-derived `Known` insertion out of every counted native path.
2. Extract the genuine clausal proof-term checker into isolated kernel modules.
3. Make Vampire emit a real primitive-certificate IR, not just ad hoc printer
   branches.
4. Get at least ten live regenerated certificates through the primitive
   `corepfcheck` gate.
5. Implement a concrete original-source context API for global facts, local
   hypotheses, definitional facts, set-command equalities, and conjecture
   negation.
6. Add Smolka-style transformations one by one with actual proof terms:
   source entry, rectification, FOOL/boolean normalization, ENNF, CNF
   projection, and Skolemization.
7. Only then use the 100-theorem original-context gate as the main success
   criterion.

## Non-Goals for Counted Progress

- No `admit`, `aby`, or incomplete QED.
- No Python reconstruction on the qualifying path.
- No private equality or private logical constants.
- No pass-count growth by enabling transitional `Known` propositions.
- No broad Megalodon-side proof search to recover data Vampire could emit.

## Status for Expert Review

The branch is now directionally aligned with the audit, but the architectural
pivot is incomplete. The expert should focus on whether the next code work is
really isolating the small kernel and moving proof detail into Vampire-side
primitive expansion, especially for Skolemization and source/preprocessing
transformations.

## July 17 Skolem/Kernel Update

After the audit response, the counted core path gained a narrow
metadata-backed Skolem proof term for direct existential choice. The accepted
case defines the generated Skolem symbol by a Megalodon delta definition,
uses the fixed choice principle, and checks the resulting `Syntax.pf` without
dynamic `Known` insertion.

The next real hammer frontier is more precise than "Skolemization" in
general. The representative case
`tests/vampire_certificate/closed_cases/hammer.1007.43.th0.p` now reaches
step `u210`, a Prover9-style `paramodulate` step over a clause that contains
dependent Skolem terms. The remaining failure is a proof-term well-formedness
issue:

```text
u210: Term de Bruijn index 15 is out of bounds for context length 15
while checking proof-term application argument: _15
```

This is not an admission gap and not a missing source-map label. It is a
specific retained-variable/term-binder accounting problem in the native
proof-term elaboration for a parent proof reused under paramodulation. Broad
fixes that skipped parent instantiation or changed global proof closing were
tested and rejected because they break earlier checked steps. The next fix
should therefore be local and principled: specify how stored theorem proofs
with step-variable `TLam`s are opened into a result-variable context, then
apply that rule uniformly to paramodulation and the other clausal kernel
rules.

## Later July 17 Structural Certificate Update

A subsequent checker change improved the strict certificate-validation
frontier, but it should be counted as E4 structural progress rather than as
native proof-term reconstruction.

The change adds scoped parameter matching for Vampire
`predicate_definition_fold` and `predicate_definition_fold_chain` steps. The
checker now treats the stripped universal binders of a predicate definition as
pattern parameters, matches the definition body against the actual source
subterm, and instantiates the folded predicate atom with the terms found in
that source context. This handles generated definitions whose parameters are
separated by unrelated source binders. The checker also accepts Vampire's
boolean/proposition equality wrappers around folded predicate atoms.

The same batch adds an ordered Skolemization candidate for structural formula
checking. It consumes Vampire's explicit substitution list through nested
existential binders, which fixes the representative failure that appeared
after the fold-chain blocker was removed.

Validation:

- optimized build passed;
- native certificate v1 smoke passed;
- the cached predicate-definition fold frontier now passes all 6 former
  failures;
- cached recheck of the previous 300-case directory reports 118 real
  certificate passes, 12 real checker failures, and 170 old non-certificate
  placeholders;
- fresh strict live 100 still reports `PASS 100`, with native primitive and
  kernel-v1 metadata audits passing.

This update does not change the revised work order above. It reduces
structural rejection in front of the kernel, but the qualifying path still
requires isolated primitive proof terms, no certificate-derived `Known`
insertion, and original-context source binding.

## Later July 17 Kernel Boundary Update

I made the first small implementation move requested by the audit's monolith
freeze: the `kernel_v1` schema/rule vocabulary and primitive-expansion
contract now live in `src/vampire_kernel_syntax.ml`, with an interface in
`src/vampire_kernel_syntax.mli`.

The strict certificate checker in `src/vampire_cert_v1.ml` uses that module
when validating `kernel_v1` metadata. Unsupported kernel rule names now fail
inside Megalodon's checker. The new negative fixture
`tests/vampire_certificate/native_cert_v1_invalid_kernel_rule.sexp` asserts
that behavior.

Validation:

- `TMPDIR=/project/tmp ./makeopt`
- `TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh`
- `TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_v1_metadata_audit.sh
  /project/tmp/live_strict_100_megalodon5_after_fold_skolem`

This remains a boundary extraction, not a completed audit response. The larger
work still has to extract the typed kernel syntax/checker/elaborator, remove
certificate-derived `Known` from every counted native path, and add the
Vampire-side primitive builder.

The same boundary was then extracted on the Vampire side. Commit
`2b095b0ae` in `/project/vampire-leancheck` adds
`Shell/MegalodonChecker/MegalodonKernelSyntax.{hpp,cpp}` and makes
`MegalodonChecker.cpp` consume it for the schema string and
rule-to-required-primitive contract. This removes one hardcoded contract
if-chain from the large exporter without changing the emitted certificate
format.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel`
- 5-case live THF run with the new binary:
  `PASS 5`
- `run_native_primitive_audit.sh` on the 5-case artifact with small-sample
  minima
- `run_kernel_v1_metadata_audit.sh` on the same artifact, covering 280
  `kernel_v1` records

Vampire commit `2701d87e4` then moved the fixed
`primitive_expansion` field construction into the same helper. This is still
not a full primitive-step IR, but it reduces the amount of certificate contract
logic embedded directly in `MegalodonChecker.cpp` and gives the next builder
extraction a concrete place to grow.

Vampire commit `37e23d654` continues that extraction by introducing an
explicit `PrimitiveExpansion` record in
`Shell/MegalodonChecker/MegalodonKernelSyntax.hpp`. The record currently holds
the expansion prefix and required primitive rule, and the large exporter now
passes that value to the syntax helper instead of passing two unrelated
strings. This does not yet satisfy the audit's requested primitive certificate
IR: it is intentionally only the smallest data boundary that can later absorb
parent selections, substitutions, rewrite positions, Skolem introductions, and
macro-to-primitive lowering traces.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel`
- 5-case live THF run with
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11046`:
  `PASS 5`
- native primitive audit on that artifact
- kernel-v1 metadata audit on that artifact, covering 280 `kernel_v1` records
  and 37 rewrite-position records

Vampire commit `770e929fa` starts the actual `MegalodonKernelStep` builder
requested in the audit. The new record lives in
`Shell/MegalodonChecker/MegalodonKernelSyntax` and currently owns the step id,
kernel rule, primitive-expansion list, and migration payload fields. Both the
general `emitKernelV1` path and the standalone instantiation metadata path now
construct this record before rendering `step_extra "kernel_v1"`.

This is intentionally not counted as a completed primitive certificate IR. The
remaining fields are still strings, so selected literals, parent references,
substitutions, rewrite positions, Skolem introductions, and result clauses
still need to be pulled into typed fields. The value of this commit is that
macro lowerings now have a concrete Vampire-side object to grow instead of
adding more direct string splicing in `MegalodonChecker.cpp`.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel`
- 5-case live THF run with
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11047`:
  `PASS 5`
- native primitive audit on the final artifact
- kernel-v1 metadata audit on the final artifact, covering 280 `kernel_v1`
  records and 37 rewrite-position records

Vampire commit `cef60e641` continues the same builder extraction by adding
`RenderedKernelConclusion` and `RenderedKernelParent` records to
`MegalodonKernelStep`. The general `kernel_v1` emission path now builds these
records and delegates the standard conclusion/result/parent field serialization
to `MegalodonKernelSyntax::kernelStepFields`.

This is still a migration-stage certificate object, because the records carry
rendered clause/literal/substitution text rather than typed Vampire kernel
objects. It is nevertheless aligned with the audit: parent and conclusion
structure now has a single Vampire-side owner, and future macro lowerings can
replace rendered strings with typed subrecords without touching every
`MegalodonChecker.cpp` call site.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel`
- 5-case live THF run with
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11048`:
  `PASS 5`
- native primitive audit on the artifact
- kernel-v1 metadata audit on the artifact, covering 280 `kernel_v1` records
  and 37 rewrite-position records

Vampire commit `9719c7960` extracts the recurring selected-literal field
cluster into `RenderedKernelLiteralSelection`. The local exporter still
discovers and renders the literal, but the standard `prefix=...`,
`prefix_parent_index=...`, `prefix_literal_index=...`,
`prefix_parent_unit=...`, and `prefix_substituted=...` layout is now owned by
`MegalodonKernelSyntax`.

This continues the audit-aligned move away from scattered printer branches.
The next more substantive step is to replace rendered selections, rewrite
positions, substitutions, and URR traces with typed records rather than only
centralizing their string serialization.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel`
- 5-case live THF run with
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11049`:
  `PASS 5`
- native primitive audit on the artifact
- kernel-v1 metadata audit on the artifact, covering 280 `kernel_v1` records
  and 37 rewrite-position records

Vampire commit `a3c121ecc` extracts the superposition rewrite metadata cluster
into `RenderedKernelRewrite`. The exporter still computes the target/equality
substitution, direction, position, and rewritten target locally, but
`MegalodonKernelSyntax` now owns the standard field serialization for that
rewrite record.

This is another boundary extraction, not final proof reconstruction. It is
aligned with the Prover9/Ivy path because rewrite metadata is now a first-class
Vampire-side object that can later become typed. Demodulation rewrite records,
URR trace steps, substitutions, and true typed term/literal records remain
unfinished.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel`
- 5-case live THF run with
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11050`:
  `PASS 5`
- native primitive audit on the artifact
- kernel-v1 metadata audit on the artifact, covering 280 `kernel_v1` records
  and 37 rewrite-position records

Vampire commit `c7131a343` applies the same rewrite record to demodulation
metadata. Superposition and demodulation now share `RenderedKernelRewrite` for
target/equality locations, from/to terms, rewrite position, substituted
literals, and rewritten target serialization.

This is still not a typed small-kernel proof object, but it reduces duplicated
rewrite printer logic and gives the next typed rewrite representation one
Vampire-side boundary to replace. URR trace steps and typed substitution,
term, literal, and position records remain open.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel`
- 5-case live THF run with
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11051`:
  `PASS 5`
- native primitive audit on the artifact
- kernel-v1 metadata audit on the artifact, covering 280 `kernel_v1` records
  and 37 rewrite-position records

Vampire commit `0b5abbeb8` extracts the unit-resulting-resolution trace-step
field cluster into `RenderedKernelUrrTraceStep`. The exporter still computes
each trace step from Vampire's inference metadata, but the standard fields for
unit parent, selected literal, substituted selected/unit literals, and the
remaining clause now have a single Vampire-side record and serializer.

This is the end of the first rendered-record extraction pass. It does not yet
provide the small typed kernel certificate requested by the audit, but it
does reduce the remaining work to a clearer replacement task: turn the
rendered parent, literal-selection, rewrite, substitution, position, and URR
trace records into typed objects, then lower macro rules into those primitive
objects before Megalodon imports them.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel`
- 5-case live THF run with
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11052`:
  `PASS 5`
- native primitive audit on the 5-case artifact
- kernel-v1 metadata audit on the 5-case artifact, covering 280 `kernel_v1`
  records and 37 rewrite-position records
- focused URR live THF run over `hammer.11703.242.th0.p` and
  `hammer.11453.77.th0.p`: `PASS 2`
- focused URR kernel-v1 metadata audit, covering 48 `kernel_v1` records and
  3 `unit_resulting_resolution` records
- focused URR primitive audit with small-sample minima relaxed; this artifact
  has no equality-resolution records, which is expected for the selected
  two-case sample

Vampire commit `453f734c9` then turns the rendered-record boundary into a
more explicit domain model. `MegalodonKernelSyntax` now distinguishes rendered
unit references, terms, formulas, literals, clauses, substitutions, and
positions. The main builder records use those wrapper types instead of raw
`std::string` fields for parent/conclusion data, literal selections, rewrite
metadata, and URR traces.

This still falls short of the audit's final requirement: these are rendered
wrappers, not fully typed Vampire kernel objects and not yet primitive proof
objects. The benefit is that the remaining replacement target is much more
precise. The next extraction should replace individual wrappers with typed
records carrying actual Vampire-side structure while keeping the single
serializer as the migration bridge.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel`
- fresh 20-case live THF run with
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11053`,
  `JOBS=10`, and `VAMPIRE_SECONDS=10`: `PASS 20`
- native primitive audit on the 20-case artifact, including 122
  `paramodulate`, 102 `substitute`, 88 `equality_resolution`, and 25
  `resolve` records
- kernel-v1 metadata audit on the same artifact, covering 738 `kernel_v1`
  records and 106 rewrite-position records

Vampire commit `99256e4cf` makes the remaining unstructured payload explicit
by renaming the builder's residual string vector to `migrationFields` and
wrapping each entry as a `MigrationField`. This does not add proof power and
does not change the emitted certificate format. Its purpose is architectural:
new typed rendered records and old bridge data are now visibly separate in the
Vampire-side object.

The next audit-relevant action is to reduce `migrationFields`, not grow it.
Good candidates are primitive parent substitutions, subsumption-resolution
side pivots, Skolem introduced-symbol records, and preprocessing
source/result formula pairs.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel`
- fresh 5-case live THF run with
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11054`,
  `JOBS=5`, and `VAMPIRE_SECONDS=10`: `PASS 5`
- kernel-v1 metadata audit on the artifact, covering 280 `kernel_v1` records
  and 37 rewrite-position records
- native primitive audit with small-sample minima relaxed, covering 37
  `paramodulate`, 46 `substitute`, 36 `equality_resolution`, and 7 `resolve`
  records

Vampire commit `c2393b33c` removes primitive parent substitutions from the
legacy migration-field path for the common clausal macro records. The builder
now carries `RenderedKernelPrimitiveParentSubstitution` entries and serializes
the existing `primitive_parent_N_substitution=...` fields from the syntax
module. This covers the substitution metadata emitted for superposition,
equality factoring, resolution, and factoring.

Vampire commit `05fe04c5d` applies the same treatment to
subsumption-resolution side-pivot metadata. `main_parent_index`,
`side_parent_index`, `side_substitution`, `side_pivot`,
`side_pivot_parent_*`, `side_pivot_substituted`, and the symmetry flag now
come from `RenderedKernelSubsumptionResolutionPivot`.

These commits still do not complete the Prover9/Ivy-style certificate. They
do, however, move two more clausal-kernel data clusters out of free-form
migration strings and into the Vampire-side kernel-step object. The next
typed replacements should focus on the remaining high-value clusters:
Skolem introduced symbols/dependencies, source/result formula pairs for
Smolka-style transformations, and SAT/AVATAR proof traces.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` for
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11055`
- fresh 10-case live THF run with `JOBS=10` and `VAMPIRE_SECONDS=10`:
  `PASS 10`
- kernel-v1 metadata audit on that artifact: 361 `kernel_v1` records, 47
  rewrite-position records, and 10 `subsumption_resolution` records
- native primitive audit on that artifact, including 55 `paramodulate`, 53
  `substitute`, 43 `equality_resolution`, 11 `resolve`, and 2
  `equality_symmetry` records
- `TMPDIR=/project/tmp make -j10 vampire_rel` for
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11056`
- fresh 10-case live THF run with `JOBS=10` and `VAMPIRE_SECONDS=10`:
  `PASS 10`
- kernel-v1 metadata audit on that artifact: 361 `kernel_v1` records, 47
  rewrite-position records, and 10 `subsumption_resolution` records
- native primitive audit on that artifact with the same primitive counts

Vampire commit `c105b6e53` then moves the Skolem introduced-symbol and
dependency metadata out of free-form `migrationFields`. The builder now
contains `RenderedKernelSkolemIntroducedSymbol` and
`RenderedKernelSkolemDependency` records, with centralized serialization for
the existing `introduced_N_*` fields.

This addresses one of the audit's high-priority areas, but only at the
certificate-object boundary. The Skolem fields still hold rendered terms,
types, names, and declarations. The remaining proof-reconstruction work is to
make those records carry typed Vampire-side objects and consume them in the
Megalodon source/preprocessing proof layer, so Skolemization is justified by
the classical choice proof rather than merely structurally accepted.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` for
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11057`
- fresh 20-case live THF run with `JOBS=10` and `VAMPIRE_SECONDS=10`:
  `PASS 20`
- kernel-v1 metadata audit on that artifact: 738 `kernel_v1` records, 106
  rewrite-position records, and 18 `skolemize` records
- native primitive audit on the same artifact, including 18 `skolem_formula`,
  122 `paramodulate`, 102 `substitute`, 88 `equality_resolution`, and 25
  `resolve` records

Vampire commit `2e4441c77` then extracts the repeated source/result formula
metadata for formula-copy, formula-normalize, and FOOL-formula records into
`RenderedKernelSourceFormulaTransform`. Transformation pair metadata is now
represented by `RenderedKernelTransformationPair` and serialized centrally by
`MegalodonKernelSyntax`.

This reduces the migration-field surface for Smolka-style transformations,
but it remains a certificate-object boundary improvement rather than a full
proof-producing implementation. Rectification renamings, definition-folding
source/definition records, CNF source-to-clause records, and original
Megalodon source-context proof composition still need the same treatment and
then actual Megalodon proof-term consumption.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` for
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11058`
- fresh 20-case live THF run with `JOBS=10` and `VAMPIRE_SECONDS=10`:
  `PASS 20`
- kernel-v1 metadata audit on that artifact: 738 `kernel_v1` records, 49
  `fool_formula`, 43 `formula_normalize`, 37 `formula_copy`, and 106
  rewrite-position records
- native primitive audit on the same artifact, including 330
  `fool_atom_lift`, 43 `ennf_formula`, 8 `formula_copy`, 29
  `formula_term_copy`, 122 `paramodulate`, and 102 `substitute` records

Vampire commit `f102adc80` extracts rectification renaming metadata from the
large exporter into `RenderedKernelRectifyRenaming` and
`RenderedKernelRectifyRenamings`. The source/result formula context is reused
through `RenderedKernelSourceFormulaTransform` when available, while the
renaming list and truncation marker are serialized by `MegalodonKernelSyntax`.

This is still not a completed Smolka-style proof layer. The record carries
rendered formulas and substitutions, and Megalodon still needs to consume
typed rectification records to produce native proof terms. It does, however,
remove another high-frequency preprocessing metadata cluster from
`migrationFields` and makes the rectification certificate shape explicit on
the Vampire side.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` for
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11059`
- fresh 20-case live THF run with `JOBS=10` and `VAMPIRE_SECONDS=10`:
  `PASS 20`
- kernel-v1 metadata audit on that artifact: 738 `kernel_v1` records, 77
  `rectify_formula` records, and 106 rewrite-position records
- native primitive audit on the same artifact, including 77
  `rectify_formula`, 43 `ennf_formula`, 18 `skolem_formula`, 122
  `paramodulate`, and 102 `substitute` records

Vampire commit `60866e6c8` extracts CNF source-to-clause metadata into
`RenderedKernelCnfClause`. The builder now owns the CNF source unit, source
kind, optional source formula/clause, result clause, parent clause count, and
clause index/count fields for `cnf_clause` kernel records.

This removes another Smolka-style preprocessing cluster from
`migrationFields`, but it is still a certificate-object extraction. The
Megalodon importer still needs typed CNF records and native proof terms for
the actual formula-to-clause projection.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel` for
  `/project/vampire-leancheck/vampire_rel_vampire/megalodon5_11060`
- fresh 20-case live THF run with `JOBS=10` and `VAMPIRE_SECONDS=10`:
  `PASS 20`
- kernel-v1 metadata audit on that artifact: 738 `kernel_v1` records, 101
  `cnf_clause` records, and 106 rewrite-position records
- native primitive audit on the same artifact, including 71
  `cnf_formula_clause`, 30 `cnf_literal`, 77 `rectify_formula`, 43
  `ennf_formula`, 122 `paramodulate`, and 102 `substitute` records
