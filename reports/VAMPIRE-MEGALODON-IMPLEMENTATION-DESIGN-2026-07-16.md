# Vampire to Megalodon Implementation Design

Date: 2026-07-16

Repositories:

- Megalodon: `/project/Megalodon`
- Vampire proof-export fork: `/project/vampire-leancheck`
- Temporary artifacts: `/project/tmp`

This document is the controlling design plan for the next phase of the
Vampire-to-Megalodon proof reconstruction project. It consolidates the prior
reports, audits, the Prover9/Ivy analysis, and the current small-kernel plan
into a concrete implementation contract.

Post-audit note, 2026-07-16: `reports/audit-REPORT-2026-07-16.md`
supersedes the evidence classification in this document where it describes
the 94/100 native preprocessing frontier or the strict live 100 run. The
preprocessing frontier is structural/transitional evidence because it used
certificate-derived `Known` propositions. The strict live 100 run is
integration and metadata evidence. Counted proof reconstruction now starts
from the genuine `-vampirecertv1corepfcheck` seed and from future
preprocessing transformations that do not use dynamic known-theorem insertion.

The purpose is to stop ad-hoc growth. A new change is aligned with this plan
only if it does one of the following:

1. makes Vampire emit more exact primitive proof data;
2. makes Megalodon check an already explicit primitive proof step as
   `Syntax.pf`;
3. links certificate inputs to original Megalodon source facts;
4. proves a source-to-clause preprocessing transformation;
5. strengthens tests or audits for those paths.

Changes that make Megalodon rediscover missing Vampire data by search, add
library-specific proof tricks, grow Python reconstruction, or add admitted
proof skeletons are outside the plan.

## Objective

The target system is:

```text
original Megalodon theorem and local context
  -> THF/TPTP export with source map
  -> Vampire proof search
  -> Vampire Prover9/Ivy-style primitive certificate
  -> Megalodon native checker
  -> Syntax.tm * Syntax.pf for the original theorem
```

The accepted final path must not use:

- `admit`;
- `aby`;
- `-allowincompleteqed`;
- bridge assumptions;
- derived non-source premises;
- unchecked source labels;
- private logical constants in place of Megalodon's equality, false, or, and
  classical principles.

Classical reasoning is assumed available. The checker may use the existing
Megalodon library/context facts for `xm`, disjunction, false, equality, and
related logical constants.

## Current State

The branch has useful evidence, but it is not finished.

Current positive evidence, as reclassified by the July 16 audit:

- Vampire emits native S-expression certificates.
- Megalodon parses and structurally validates those certificates.
- Strict source-linked live 100-case checking passes as integration and
  metadata evidence. It is not a checked proof-reconstruction result.
- The current live strict 100-case run reports 3143 `kernel_v1` records,
  including 375 instantiation records.
- The native preprocess frontier was 94/100 as structural/transitional
  native-AST plumbing. It is not qualifying proof-term evidence while it relies
  on certificate-derived `Known` propositions.
- The native core proof-term audit passes on the current 23 eligible
  core-closed cases.
- Source formulas are checked for the supported THF fragment.
- Closed modes reject bridge and derived assumptions.

Current limitations:

- The broad textual replay engine in `src/vampire_cert_v1.ml` is still too
  large and is not the final architecture.
- The main success count is still mostly exported-THF-bound, not
  original-context proof reconstruction.
- Vampire has detailed metadata in `step_extra kernel_v1`, but there is not yet
  a clean internal Vampire primitive-certificate IR.
- Some macro inferences are still surfaced as broad constructors rather than
  lowered to simple kernel steps.
- Skolemization and source-to-clause transformations are only partially
  proof-producing.
- Set-command generated equalities still need explicit original-context
  reflexivity handling.
- AVATAR/split proof composition remains transitional.

The current work should therefore be treated as a regression oracle and
frontier finder, not as the final proof reconstruction architecture.

## Design Boundary

The project has three proof layers. Keeping them separate is mandatory.

### Layer A: Source and preprocessing proofs

This layer proves that original Megalodon facts justify the clauses that enter
the clausal refutation.

Responsibilities:

- map exported TPTP names back to original Megalodon theorem, lemma,
  hypothesis, definition, or conjecture origins;
- prove `set`-generated equalities by reflexivity or definitional conversion;
- handle conjecture negation;
- prove rectification, FOOL, ENNF, CNF, definition introduction, and
  Skolemization transformations;
- produce Megalodon proof terms for the generated clause inputs.

Non-responsibilities:

- clausal resolution;
- equality superposition;
- guessing how Vampire performed proof search.

### Layer B: Clausal small kernel

This layer checks the refutation once clause inputs are justified.

The intended stable primitive vocabulary is:

- `input`
- `instantiate`
- `rename`
- `flip`
- `resolve`
- `factor`
- `equality_resolution`
- `equality_factoring`
- `paramodulate`
- `truth_conflict`
- `contradiction`

Every primitive must contain enough data for simple local checking:

- parent unit ids;
- parent clauses or hashes sufficient to resolve them;
- result clause;
- selected literal indices;
- selected literals;
- substitutions;
- variable sorts;
- rewrite position, direction, `from`, and `to` terms for equality transport;
- origin metadata linking primitive substeps back to the original Vampire
  inference.

Megalodon may check side conditions and elaborate fixed proof templates. It
must not infer missing substitutions, pivots, positions, or rewrite direction.

### Layer C: Macro expansion

This layer belongs primarily in Vampire.

Vampire should lower complex inferences into Layer B primitives while it still
has exact proof-search data. This mirrors Prover9's `expand_proof` followed by
`expand_proof_ivy`.

Required macro lowering:

- `superposition`
  -> instantiate equality parent, instantiate target parent, optional flip,
  one `paramodulate`, optional factor/rename.

- `demodulation` / `rewrite`
  -> instantiate demodulator, instantiate target, optional flip, one
  `paramodulate` per occurrence, optional factor/rename.

- `unit_resulting_resolution`
  -> instantiate current parent, instantiate each unit parent, optional flips,
  binary `resolve` chain, optional rename.

- `subsumption_resolution`
  -> instantiate side parent, optional side equality flip, one `resolve`,
  checked side-remainder coverage.

- `condensation`
  -> instantiate, `factor` or propositional duplicate deletion, optional
  rename.

- AVATAR
  -> later: a separate propositional proof object connected to split clauses,
  not an opaque Megalodon assumption.

## Vampire Implementation Plan

The Vampire fork should gain an explicit primitive certificate builder instead
of emitting every constructor directly from scattered printer logic.

Proposed internal shape:

```cpp
enum class MegalodonKernelRule {
  Input,
  Instantiate,
  Rename,
  Flip,
  Resolve,
  Factor,
  EqualityResolution,
  EqualityFactoring,
  Paramodulate,
  TruthConflict,
  Contradiction
};

struct MegalodonKernelStep {
  std::string id;
  MegalodonKernelRule rule;
  std::vector<std::string> parents;
  ClauseLike result;
  VariableSortMap variableSorts;
  SourceOrigin source;
  OptionalSubstitution substitution;
  OptionalLiteralSelection selected;
  OptionalLiteralSelection other;
  OptionalPosition position;
  OptionalTerm from;
  OptionalTerm to;
  OriginalInferenceOrigin origin;
};
```

The exact C++ types can follow Vampire conventions. The important invariant is
that macro-specific code constructs a list of primitive steps first, and the
printer only serializes those primitive steps.

Near-term Vampire tasks:

1. Introduce a small `MegalodonKernelStep`/builder layer next to
   `MegalodonChecker`.
2. Convert existing `kernel_v1` metadata generation for instantiation into a
   first-class `instantiate` primitive path.
3. Convert superposition and rewrite metadata to primitive `paramodulate`
   records with exact positions and direction.
4. Convert unit-resulting resolution and subsumption resolution expansions to
   use the same builder instead of custom local S-expression fragments.
5. Keep `step_extra kernel_v1` as a migration audit until the primitive records
   themselves carry all required fields.
6. Remove or quarantine old JSON and legacy diagnostic printers from the
   qualifying path.

Acceptance rule for Vampire-side work:

- a complex inference is not considered handled merely because Megalodon can
  reconstruct it after searching;
- it is handled when Vampire emits a sequence of primitive steps whose local
  side conditions are independently checkable.

## Megalodon Implementation Plan

Megalodon should converge on a native checker:

```ocaml
source_context -> certificate -> Syntax.tm * Syntax.pf
```

The textual `.mg` emitter can remain as a debug view, but counted progress
should come from `check_propofpf` on constructed proof terms.

Near-term Megalodon tasks:

1. Keep `-vampirecertv1strict` and closed/source audits as fail-closed gates.
2. Expand `-vampirecertv1corepfcheck` and
   `-vampirecertv1preprocesspfcheck` only for explicit primitive steps or
   explicit preprocessing transformations.
3. Refuse unsupported constructors in proof-term modes rather than falling
   back to textual replay.
4. Replace transitional surface constructors:
   - `substitute` becomes `instantiate`;
   - `equality_symmetry` becomes `flip`;
   - macro `rewrite` and `superposition` become primitive `paramodulate`
     sequences.
5. Keep equality as Megalodon's typed equality. Do not introduce a private
   equality encoding.
6. Add original-context binding so source inputs are proofs from the real
   Megalodon context, not only re-parsed exported THF.
7. Add set-command equality handling as a small source/preprocessing rule:
   generated equality facts are proved by reflexivity/definitional conversion.
8. Add Skolemization as an explicit preprocessing proof rule with generated
   symbol, dependency vector, sorts, and the classical/choice principle used.

Acceptance rule for Megalodon-side work:

- adding a new OCaml checker case is acceptable only if the certificate already
  contains exact proof data or the case is a well-specified preprocessing
  transformation;
- adding a search heuristic to guess missing Vampire data is not acceptable
  except as temporary diagnostic code explicitly excluded from qualifying
  gates.

## Original-Context Linking Plan

The system needs a source object model, not only TPTP names.

Each exported source should carry:

- stable exported TPTP name;
- original Megalodon declaration name or local hypothesis id;
- source kind: theorem, lemma, hypothesis, definition, set equality,
  conjecture negation, generated transformation;
- original proposition as `Syntax.tm` or a stable hash checked against it;
- exported THF proposition hash;
- binder/sort environment;
- name-mangling map for constants, type symbols, and local variables.

The importer should resolve each certificate input by source kind:

- theorem/lemma/hypothesis: use the existing proof from the Megalodon context;
- definition: unfold or use the generated definitional proof;
- set equality: prove by reflexivity after unfolding the set assignment;
- conjecture negation: introduce the negated target in the proof by
  contradiction;
- generated transformation: use the preprocessing proof chain.

This is the main Tier 1 gap. Exported-THF source checking is useful Tier 2
evidence, but it is not enough to claim original Megalodon reconstruction.

## Smolka-Style Transformation Plan

The preprocessing layer should follow the Smolka-style discipline: every
formula transformation is a proof-producing step, separate from clausal
resolution.

Required transformation families:

1. Formula input and formula-term input.
2. Rectification and alpha-renaming.
3. FOOL boolean lifting and boolean exhaustiveness.
4. ENNF.
5. CNF formula-to-clause steps.
6. Definition introduction and definition input.
7. Skolemization.
8. Inequality/name introduction.
9. AVATAR split definition and split refutation, later via a separate
   propositional certificate.

Skolemization requires special care. The certificate must include:

- source formula;
- result formula or clause;
- full quantifier prefix;
- universally scoped dependency variables;
- generated Skolem symbol;
- symbol sort;
- dependency vector;
- proof principle used, e.g. classical choice;
- exact parent step id.

Megalodon should not infer Skolem dependencies from names.

## Test Strategy

Tests must be fast, parallel, and frontier-oriented.

Permanent constraints:

- use `/project/tmp` for generated artifacts;
- use Vampire timeout at most 10 seconds per problem;
- run broad checks with `JOBS=10` to `JOBS=20`;
- do not repeatedly rerun unsolved Vampire searches during development;
- cache the set of Vampire-solvable THF problems for the current benchmark
  suite;
- focus iteration on the first failing proof-term frontier, not on full
  expensive sweeps after every edit.

Test tiers:

1. Unit fixtures for each primitive constructor:
   - positive certificate;
   - malformed schema;
   - invalid side condition;
   - proof-term check.

2. Native core proof-term gate:
   - `tests/vampire_certificate/run_native_cert_v1_core_closed_audit.sh`
   - counts only certificates on the small clausal core path.

3. Native preprocess structural frontier:
   - `tests/vampire_certificate/run_native_live_preprocess_pf_frontier.sh`
   - runs live Vampire in parallel over the fixed solvable 100-case list with
     explicit transitional-known diagnostic opt-in;
   - this is structural evidence only, not counted proof reconstruction.

4. Strict live 100-case gate:
   - `tests/vampire_certificate/run_native_live_parallel.sh`
   - requires source linkage, strict certificates, primitive audit, kernel
     metadata audit, and substitute metadata audit.

5. Original-context gate:
   - new gate to be added;
   - exports from original Megalodon files;
   - imports the Vampire certificate;
   - constructs `Syntax.pf` for the original theorem;
   - rejects exported-THF-only assumptions.

Progress should be reported by evidence class and test stage. Use the E1-E4
and T0-T4 terminology from `VAMPIRE-MEGALODON-DESIGN-PLAN-2026-07-16.md`.

## Immediate Work Queue

The next implementation iterations should be ordered as follows.

### Milestone 1: Freeze and document the frontier

Deliverables:

- keep the current 100-case solvable list fixed;
- keep latest strict and proof-term frontier summaries under `/project/tmp`;
- record the remaining proof-term failures and their first unsupported or
  invalid primitive;
- avoid unrelated broad sweeps.

Success criterion:

- everyone can identify the next proof-term blocker without rerunning Vampire
  search.

### Milestone 2: Trust reset and core extraction

The July 16 audit supersedes the old instruction to drive the preprocessing
frontier to 100/100. Current priority:

- remove certificate-derived `Known` propositions from counted native paths;
- keep the old preprocessing frontier as `PREPROCESS_STRUCTURAL_PASS`
  diagnostics only;
- extract the genuine `corepfcheck` seed into isolated kernel modules;
- find real live core certificates before resuming preprocessing pass-count
  work.

Decision rule:

- if the failure is caused by missing Vampire data, fix Vampire emission first;
- if the data is present and the Megalodon proof template is missing, add the
  native proof-term case;
- if the failure is a source/preprocessing transformation, put it in Layer A,
  not in the clausal kernel.

Success criterion:

- counted native paths contain no dynamic known-theorem insertion;
- the real clausal core has at least ten live regenerated Vampire examples.

### Milestone 3: Replace `kernel_v1` metadata with first-class primitives

Deliverables:

- first-class `instantiate` primitive;
- first-class `paramodulate` primitive for superposition/rewrite;
- first-class `resolve` chains for URR/subsumption expansions;
- `step_extra kernel_v1` retained only as audit/migration data.

Success criterion:

- primitive audit can validate the actual certificate steps without relying on
  side metadata as the main carrier of proof data.

### Milestone 4: Original-context source glue

Deliverables:

- source map resolves original Megalodon declaration/local hypothesis ids;
- set-command equalities are discharged by reflexivity;
- conjecture negation is connected to the target theorem;
- exported THF formula comparison remains as a consistency check, not the only
  source of truth.

Success criterion:

- at least 10 real original-context theorems reconstruct through native
  `Syntax.pf`, not through exported-THF assumptions.

### Milestone 5: Skolemization and Smolka transformations

Deliverables:

- explicit Skolemization certificate fields;
- Megalodon proof-term checker for the supported Skolemization pattern;
- ENNF/CNF/definition/FOOL transformations as proof-producing steps;
- unsupported transformations fail closed.

Success criterion:

- source-to-clause preprocessing proof composes with the clausal refutation for
  the fixed 100-case list.

### Milestone 6: Held-out evaluation

Deliverables:

- regenerate a fresh or held-out THF suite;
- run Vampire once in parallel with 10-second timeout;
- cache the solvable set;
- reconstruct all solvable proofs through the native path.

Success criterion:

- at least 100 original-context no-admit Megalodon reconstructions.

## Engineering Rules

Use these rules when deciding what to implement next:

1. Prefer Vampire-side expansion over Megalodon-side guessing.
2. Prefer native `Syntax.pf` over textual `.mg` printing.
3. Prefer small primitive rules over macro rules.
4. Prefer explicit source/preprocessing proofs over treating generated clauses
   as axioms.
5. Prefer one focused frontier run over repeated full-suite runs.
6. Commit tests and harnesses with the feature they validate.
7. Keep generated benchmarks and temporary proof output out of source commits
   unless intentionally adding a small fixture.
8. Report pass counts by tier and include the exact command and artifact
   directory.

## Open Questions

1. Exact Vampire C++ location for the primitive builder:
   - likely near `Shell/MegalodonChecker`, but the builder should be separated
     from raw printing logic.

2. Long-term treatment of AVATAR:
   - likely a small SAT/propositional proof object connected to first-order
     split clauses;
   - should not be accepted as an opaque primitive.

3. Exact original-context source representation:
   - ideal form is direct `Syntax.tm` plus context identifiers;
   - exported THF hashes can remain as consistency checks.

4. How much of the old textual emitter to delete:
   - keep it until native gates reach parity;
   - then quarantine it as debug-only or remove it from normal builds.

5. Whether some macro constructors should remain in the certificate:
   - acceptable only if they are preprocessing rules with explicit proofs;
   - clausal proof-search macros should lower to the primitive kernel.

## Bottom Line

The project should proceed on a Prover9/Ivy-style architecture:

```text
Vampire explains complex inferences.
Megalodon checks small explicit steps.
Source/preprocessing proofs connect clauses to the original development.
```

The next work should not be another round of broad OCaml or Python
reconstruction. It should be a controlled sequence of small-kernel primitive
emission, native proof-term checking, original-context source glue, and
Smolka-style preprocessing proofs.
