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

Second post-audit note, 2026-07-16, historical before the source-entry core
update: the real-core frontier audit on
`vampire/megalodon5` found `REAL_CORE_ELIGIBLE 0`,
`SYNTHETIC_CORE_ELIGIBLE 23`, and `EXCLUDED 149`. The first blockers for real
closed hammer certificates are `formula_term_input` and `formula_input`, not
missing clausal proof-term templates. This document therefore treats
source/preprocessing proof production as the next qualifying gate, with
Vampire-side clausal primitive lowering proceeding in parallel. The fourth
note below supersedes these counts at the current branch head.

Third post-audit note, 2026-07-16: live original-context replay now has a
stricter source-obligation invariant. Source-map entries are audited, but only
inputs in the dependency closure of an empty-clause root become proof
obligations for the native clausal core. This avoids treating unused exported
local definitions from Megalodon `set` commands as premises of the proof. The
remaining source obligations are instantiated together with each candidate
native refutation proof before local hypotheses and the negated conjecture are
composed back into the current Megalodon goal.

Fourth post-audit note, 2026-07-16, historical source-entry increment: the
proof-producing core gate gained
a narrow source-entry layer for `formula_input`, `formula_term_input`, identity
`formula_term_copy`, `formula_copy`, `cnf_literal`, and `cnf_formula_clause`.
These are admitted only because the native elaborator builds and checks
`Syntax.pf` terms for them; no certificate-derived `Known` proposition is
installed. Before the later rectification increment, the closed-corpus core
audit had 26 `CORE_PF_PASS` cases:
23 synthetic `core.cnf.*` fixtures and 3 non-synthetic/source-entry cases,
including two `hammer.*` certificates. The remaining first blocker is dominated
by `rectify_formula`, so general Smolka-style preprocessing is still open.

Fifth post-audit note, 2026-07-17: adding checked `rectify_formula` to the
same source-entry/core path moves the closed-corpus core audit to
27 `CORE_PF_PASS` cases: 23 synthetic fixtures and 4 non-synthetic/source-entry
cases. The first excluded-rule distribution is now dominated by FOOL
transformations (`fool_atom_lift`, `fool_formula`, and `fool_bool`), not
rectification.

Sixth post-audit note, 2026-07-17: the counted core gate now includes a narrow
checked FOOL Boolean-lifting subset: `fool_atom_lift` metadata validation plus
proof-producing `fool_formula` and `fool_bool` steps. The native elaborator
constructs `Syntax.pf` terms and immediately checks them; it does not install
certificate-derived `Known` propositions. The closed-corpus core audit now
reports 32 `CORE_PF_PASS` cases: 23 synthetic fixtures and 9 non-synthetic
cases. The first blockers are now `ennf_formula` and `definition_input`, so
the next qualifying work is Smolka-style ENNF proof production and original
source-definition composition.

Seventh post-audit note, 2026-07-17: the counted core gate now includes
checked `ennf_formula`, `definition_input`, `fool_exhaustiveness`,
inequality intro/split, and annotated instantiation `substitute` steps. The
instantiation change is primarily an audit correction: substitutions with
explicit `kernel_v1` `rule=instantiation` metadata were already proof-producing
in the native core elaborator, but the shell classifier was counting them as
unsupported `nonidentity_substitute` steps. The closed-corpus audit now reports
114 `CORE_PF_PASS` cases: 23 synthetic fixtures and 91 non-synthetic cases.
The first blockers are now `skolem_formula`, unannotated non-identity
substitutions, and AVATAR/definition macro composition.

Eighth post-audit note, 2026-07-17: the Skolem work has split into two
concrete subproblems. First, direct metadata-backed existential
Skolemization can be elaborated as a real `Syntax.pf` using generated delta
definitions and choice, with no dynamic `Known` proposition. Second,
dependent Skolem symbols must remain as certificate terms and unfold by
definitional equality under the current proof-binder depth; eager formula
rewriting is not the right architecture. The current representative blocker
is `hammer.1007.43.th0.p` step `u210`, where a paramodulation parent proof
with retained variables is opened into the result context and produces an
out-of-bounds de Bruijn argument (`_15` in context length 15). The next
implementation should define a small theorem-opening API for stored
`TLam` proofs and use it in resolution/paramodulation/substitution, rather
than adding theorem- or library-specific rewrites.

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
- The native core proof-term audit passes on the current 114 eligible
  core/source-entry closed cases. This includes 23 synthetic `core.cnf.*`
  fixtures and 91 non-synthetic/source-entry/preprocessing cases.
- The real closed hammer frontier is measured and reproducible:
  `REAL_CORE_ELIGIBLE 91`, `SYNTHETIC_CORE_ELIGIBLE 23`, `EXCLUDED 58`.
  This is the first proof-producing real-hammer movement through the source
  entry gate, but most real cases still require Smolka-style preprocessing
  obligations before their clausal refutations can count.
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
  proof-producing. Direct choice-backed Skolemization has a checked native
  proof-term path; dependent Skolem functions currently expose the theorem
  opening/binder-accounting issue described above.
- The simplest `formula_input` and `formula_term_input` source-entry cases are
  proof-producing when they feed identity formula-copy/CNF-entry steps, and a
  narrow FOOL Boolean-lifting subset is proof-producing. More complex formula
  preprocessing remains open, especially ENNF, FOOL exhaustiveness,
  definition-input, and Skolemization transformations.
- Generated set-command equalities that are exported as
  `set_reflexivity`/`local_set_reflexivity` now have native reflexivity proofs.
  Matched theorem-local definitions from `set` commands are audited and ignored
  when unused by the empty-clause proof dependency closure, but still need
  explicit definitional proof production when a refutation actually depends on
  them.
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
- distinguish exported but unused source facts from source facts on the actual
  empty-clause dependency path;
- handle conjecture negation;
- prove rectification, FOOL, ENNF, CNF, definition introduction, and
  Skolemization transformations;
- produce Megalodon proof terms for the generated clause inputs.

Immediate scope:

- `formula_input`: prove the exported formula directly from a source origin or
  from a generated source fact such as a conjecture-negation wrapper.
- `formula_term_input`: prove the certificate-level formula term from the
  corresponding source formula, including the boolean/formula-term coercion
  used by the THF export.
- set-command equalities: do not look for a source claim; prove them by
  reflexivity or definitional conversion in the original Megalodon context.
- local definitions: source-map matching is only an audit result. A matched
  local definition becomes a proof obligation only if the clausal proof
  dependency closure uses its input step.
- Skolemization: introduce a transformation certificate carrying the source
  formula, result formula, introduced symbols, replaced variables, and the
  freshness/dependency data needed for a Megalodon proof term.

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

The builder is still required, but the real-core audit changes its role in the
next milestone. It is not enough to lower later `superposition`, `rewrite`, or
unit-resulting-resolution steps if every real certificate remains blocked at
`formula_input`/`formula_term_input`. Vampire should therefore also print
source/preprocessing transformation records in the same disciplined style:
explicit parent formulas, result formulas, source ids, variable/symbol sorts,
renaming maps, transformation paths, Skolem introductions, and formula-term
coercion data. Megalodon should check those records; it should not synthesize
missing Smolka transformations from before/after formulas.

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

Implementation update, 2026-07-16:

- `src/vampire_source_context.ml` now contains the concrete source-context
  resolver seed.
- Standalone certificate checks use it to consume hash-backed global source
  facts as `Known hash` proofs.
- Live `vampireaby` certificate validation passes the current theorem-local
  proof context into this resolver, so `local_fact` source-map entries can be
  checked against original Megalodon hypotheses and represented as `Hyp i`.
- Branch `vampire/megalodon5` consumes this information in the first live
  proof-term composition path.  Hash-backed global facts are passed into the
  native core elaborator as source proofs, but local `Hyp` facts are left as
  explicit certificate assumptions.  The importer then instantiates leading
  Vampire variables with live Megalodon context variables, applies the local
  `Hyp` proofs at the original-context boundary, and uses loaded `xm` to turn
  the remaining negated-conjecture refutation into the current goal.
- `xm` is now an explicit trusted classical principle only when an axiom named
  `xm` has the standard excluded-middle proposition.  The smoke suite checks
  the positive live certificate path, a negative malformed-`xm` case, and the
  same live certificate theorem appended after an `UpToOctonions` library
  prelude that declares `xm`.  It also checks a multi-local source case where
  two local facts are resolved and applied at the Megalodon boundary.
- Strict live `vampireaby` now fails closed when a configured Vampire run does
  not provide a native certificate, or when the certificate cannot be composed
  into the current goal.  Direct native `aby` reconstruction remains a
  development fallback only outside that strict certificate path.
- Generated `set_reflexivity` and `local_set_reflexivity` source-map entries
  now produce native reflexivity proofs in `src/vampire_source_context.ml`;
  the consuming native elaborator checks them with the certificate-local symbol
  table. These entries cover Megalodon `set`-command equality obligations that
  have no corresponding original claim name.
- The live source-context object now carries proof-local `set` definitions.
  A `local_definition` source-map entry is reported as
  `local_definition_matched` when it names one of those bindings. This is
  deliberately not counted as proof reconstruction yet: strict mode fails
  closed until the definition equality can be converted into a checked proof
  and composed with the certificate.
- Local fact matching now projects certificate/source term indices through
  proof-local definitions, so facts introduced before or after `set` commands
  are checked against the same proof context that Megalodon uses internally.
- This is still partial original theorem reconstruction: it handles the simple
  core shape `local facts -> negated conjecture -> False`, including multiple
  local facts, but not local
  definitions, generated preprocessing facts, Skolemization, or general
  Smolka-style transformation chains.

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

This remains the main E1 gap. The branch-5 live path closes the first
small piece of it for local facts plus conjecture negation, while exported-THF
source checking by itself remains E2 evidence and is not enough to claim
general original Megalodon reconstruction.

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

Test stages and evidence classes:

1. T0 unit fixtures for each primitive constructor:
   - positive certificate;
   - malformed schema;
   - invalid side condition;
   - proof-term check.

2. T1/T2 native core proof-term gate:
   - `tests/vampire_certificate/run_native_cert_v1_core_closed_audit.sh`
   - counts only certificates on the small clausal core path;
   - reports E3 unless the certificate is also linked to the original
     Megalodon context.

3. T1/T3 native preprocess structural frontier:
   - `tests/vampire_certificate/run_native_live_preprocess_pf_frontier.sh`
   - runs live Vampire in parallel over the fixed solvable 100-case list with
     explicit transitional-known diagnostic opt-in;
   - this is E4 structural evidence only, not counted proof reconstruction.

4. T3 strict live 100-case gate:
   - `tests/vampire_certificate/run_native_live_parallel.sh`
   - requires source linkage, strict certificates, primitive audit, kernel
     metadata audit, and substitute metadata audit;
   - this is E4 unless a closed proof term is checked.

5. T4 original-context gate:
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
