# Vampire to Megalodon Controlling Plan

Date: 2026-07-16

Repositories:

- Megalodon: `/project/Megalodon`
- Vampire fork: `/project/vampire-leancheck`
- Temporary artifacts: `/project/tmp`

This is the controlling design and execution plan for the next phase of the
Vampire-to-Megalodon proof reconstruction project. It is meant to make the
work less ad hoc. A future patch should be easy to classify against this
document before it is written.

## Short Answer

The project should follow a Prover9/Ivy-style architecture:

```text
Vampire proof
  -> Vampire-side expansion into a small primitive certificate
  -> Megalodon native checker over Syntax.tm and Syntax.pf
  -> source/preprocessing proof composition
  -> original Megalodon theorem
```

The important point is ownership:

- Vampire explains proof-search inferences while it still has exact
  substitutions, selected literals, equality orientation, term positions, and
  sorts.
- Megalodon checks explicit primitive steps and elaborates them to proof terms.
- A separate preprocessing layer proves that exported clauses follow from the
  original Megalodon context by Smolka-style formula transformations.

The project currently has useful infrastructure and some real proof-term
progress, but it does not yet have the final clean small-kernel implementation.
The next phase should build that implementation deliberately instead of growing
another broad reconstruction engine.

## Current Baseline

The current branch has the following useful pieces:

- native S-expression certificates emitted by Vampire;
- an OCaml parser/checker in Megalodon;
- strict source-linked live tests;
- bridge and derived-assumption rejection in closed modes;
- native proof-term checking for a growing clausal/preprocessing subset;
- parallel frontier harnesses using `/project/tmp`;
- a fixed 10s Vampire timeout discipline;
- an emerging `kernel_v1` metadata audit.

Recent local progress on 2026-07-16:

- `inequality_name_intro` and `inequality_split` now have native proof-term
  support.
- A unit-resulting-resolution case was moved to explicit primitive steps with
  typed equality symmetry handling on the Vampire side.
- A subsumption-resolution case was moved away from the broad macro checker:
  Vampire emits the primitive expansion and a final identity alias, and
  Megalodon audits the symmetry/substitution chain.
- A focused subsumption run passed:

```text
PREPROCESS_PF_PASS 1
artifact: /project/tmp/live_subsumption_after_audit_chain
```

Current focused six-case proof-term frontier:

```text
PREPROCESS_PF_PASS       2
CHECK_FAILED             1
ILL_FORMED_PROOF_TERM    2
WRONG_PROPOSITION        1
artifact: /project/tmp/live_preprocess_pf_frontier6_plan_baseline
```

Remaining focused failures:

```text
hammer.10806.144.th0.p  WRONG_PROPOSITION      u445
hammer.11405.35.th0.p   ILL_FORMED_PROOF_TERM  u283
hammer.11497.79.th0.p   ILL_FORMED_PROOF_TERM  u573
hammer.11577.51.th0.p   CHECK_FAILED           u792 paramodulation result mismatch
```

This is a useful frontier, but it is not the whole objective. The final
objective is original-context Megalodon proof reconstruction with no admitted
or bridge assumptions.

## Non-Negotiable Trust Boundary

Counted success must not use:

- `admit`;
- `aby`;
- `-allowincompleteqed`;
- bridge assumptions;
- derived non-source premises;
- unchecked source labels;
- private equality or private logical constants;
- Python reconstruction on the qualifying path;
- Megalodon-side search that guesses data Vampire failed to emit.

The checker may assume the ordinary Megalodon library context, including:

- classical reasoning;
- `xm`;
- Megalodon's equality;
- Megalodon's false, disjunction, and related logical constants.

Set-command generated equalities are not ordinary named lemmas. They must be
proved explicitly in Megalodon, normally by reflexivity or definitional
conversion.

## Architecture

The architecture has four layers. Keeping them separate is the main discipline.

### Layer 1: Source and Export

Input:

```text
original Megalodon theorem/context
```

Output:

```text
THF/TPTP problem + source map
```

Responsibilities:

- record the original declaration, local hypothesis, definition, set command,
  or conjecture origin for every exported source;
- preserve enough binder, type, and name-mangling information to map Vampire
  names back to Megalodon names;
- record the exported formula and a stable hash;
- distinguish real user/library facts from generated preprocessing facts.

This layer must not hide generated transformation facts as ordinary source
axioms.

### Layer 2: Source-to-Clause Transformations

Input:

```text
original source fact or conjecture
```

Output:

```text
clausal input justified by a proof term
```

Responsibilities:

- conjecture negation;
- formula copying and alpha-renaming;
- rectification;
- FOOL transformations;
- ENNF;
- CNF;
- definition introduction;
- Skolemization;
- inequality/name introduction;
- set-command equality proofs.

This is the Smolka-style part of the project. Each transformation should be
proof-producing or certificate-checked. Unsupported transformations must fail
closed.

### Layer 3: Clausal Small Kernel

Input:

```text
source-justified clauses + primitive clausal proof steps
```

Output:

```text
refutation proof term
```

The intended primitive vocabulary is:

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

The current surface names `substitute` and `equality_symmetry` are migration
names for `instantiate` and `flip`.

Every primitive step should contain:

- exact parent ids;
- parent/result clauses or checked hashes;
- selected literal indices;
- selected literal terms;
- substitutions with variable sorts;
- rewrite position and direction for equality transport;
- equality `from` and `to` terms where relevant;
- origin metadata pointing back to the Vampire inference being expanded.

Megalodon may check local side conditions and elaborate fixed proof templates.
It must not infer missing pivots, substitutions, rewrite positions, or equality
orientation by search.

### Layer 4: Vampire Macro Expansion

Input:

```text
Vampire internal proof with complex inferences
```

Output:

```text
small primitive certificate
```

This layer belongs primarily in Vampire. Vampire has the proof-search state:

- selected literals;
- unifiers and side substitutions;
- equality orientation;
- rewrite positions;
- term and variable sorts;
- clause parents;
- AVATAR state;
- inference-specific metadata.

The desired pattern is the Prover9/prooftrans pattern:

```text
normal proof
  -> expanded proof
  -> small Ivy-like proof object
```

For this project:

```text
Vampire proof
  -> expanded primitive Megalodon certificate
  -> native Megalodon proof terms
```

## Required Vampire Lowerings

The following complex Vampire inferences should not survive as broad Megalodon
macros in the qualifying path.

### Unit-Resulting Resolution

Target lowering:

```text
instantiate current parent
instantiate unit parent 1
optional flip
resolve
instantiate unit parent 2
optional flip
resolve
...
optional factor/rename
```

Status:

- one important case now emits primitive steps after typed equality symmetry
  support;
- this needs to move into a shared primitive builder rather than remain local
  printer code.

### Subsumption Resolution

Target lowering:

```text
instantiate side parent
optional equality flips
resolve selected literal
verify side remainder coverage
identity alias to original Vampire unit id
```

Status:

- the current focused case passes after moving the final step away from the
  broad `subsumption_resolution` macro;
- the audit now accepts symmetry chains over the side substitution parent.

### Superposition and Rewrite

Target lowering:

```text
instantiate equality parent
instantiate target parent
optional flip
paramodulate at exact position
optional factor/rename
```

Status:

- `paramodulate` exists in the native path;
- one current failure is a paramodulation target mismatch at `u792`;
- next action is to inspect whether Vampire emitted wrong orientation/position
  or whether Megalodon's native proof template mishandles the explicit data.

### Condensation

Target lowering:

```text
instantiate
factor or duplicate-literal deletion
optional rename
```

Status:

- should be implemented only after the current four proof-term frontier
  failures are understood, unless a focused case makes it the next blocker.

### AVATAR

Target lowering:

```text
first-order split clauses + separate propositional/SAT proof certificate
```

Status:

- not part of the immediate small clausal kernel;
- must not be represented as an opaque assumption in counted proofs.

## Required Megalodon Work

### Native Proof-Term Checker

The qualifying checker should converge on:

```ocaml
source_context -> certificate -> Syntax.tm * Syntax.pf
```

Every constructed proof term should be checked by Megalodon's native proof
checker, not only printed as text.

Near-term rules:

- keep textual `.mg` emission as a debug view and regression oracle;
- do not add new broad textual replay features unless needed for diagnostics;
- in proof-term modes, unsupported constructors fail closed;
- if a certificate has exact primitive data, add a small proof-term template;
- if the data is missing, fix Vampire emission first.

### Original-Context Source Glue

This is the main Tier 1 gap.

For every certificate input, the importer needs a source object:

```text
source id
exported TPTP name
original Megalodon name or local hypothesis id
source kind
original proposition as Syntax.tm or checked hash
exported formula hash
binder/type environment
name-mangling map
```

Resolution policy:

- theorem/lemma/hypothesis: use the proof already available in the original
  Megalodon context;
- definition: unfold or use a generated definitional proof;
- set equality: prove by reflexivity or definitional conversion;
- conjecture negation: introduce the negated target for contradiction;
- generated preprocessing fact: follow the transformation proof chain.

The current exported-THF formula comparison remains useful, but it is Tier 2
evidence. It is not enough for original-context reconstruction.

### Skolemization

Skolemization must be explicit. The certificate should include:

- parent formula;
- result formula/clause;
- quantifier prefix;
- dependency variables;
- generated Skolem symbol;
- symbol type;
- dependency vector;
- proof principle used, probably classical choice;
- parent step id.

Megalodon should not infer dependencies from symbol names.

## What Is Frozen

The following are frozen except for correctness fixes or diagnostic support:

- growth of Python reconstruction;
- new broad OCaml textual replay tactics;
- library-specific name hacks;
- inferred source matching based only on mangled names;
- macro constructors accepted as opaque proof steps in counted modes;
- repeated broad Vampire runs during tight iteration.

The old code is still useful as:

- a parser compatibility check;
- a diagnostic pretty-printer;
- a regression oracle while native proof terms catch up.

It should not define success.

## Implementation Milestones

### Milestone 0: Commit and Stabilize Current Frontier

Deliverables:

- commit the current subsumption-resolution primitive-alias fix in Vampire;
- commit the corresponding Megalodon audit fix;
- record the current frontier artifact directory.

Acceptance:

- focused subsumption case passes;
- six-case frontier remains 2 pass / 4 fail or better.

### Milestone 1: Finish the Current Four Proof-Term Failures

Current failures:

```text
u445  wrong proposition
u283  ill-formed proof term: nonfunction applied to an argument
u573  ill-formed proof term: nonfunction applied to an argument
u792  paramodulation result mismatch
```

Decision rule for each:

- if explicit Vampire data is wrong or missing, fix Vampire emission;
- if explicit data is correct and the proof template is wrong, fix
  Megalodon native proof-term elaboration;
- if the issue is a source transformation, move it to the preprocessing layer.

Acceptance:

- fixed 100-case native preprocess proof-term frontier reaches 100/100;
- no `admit`, `aby`, bridge, or derived assumption participates.

### Milestone 2: Introduce a Vampire Primitive Builder

Deliverables:

- a small C++ builder object for primitive certificate steps;
- existing local URR/subsumption/superposition fragments migrated to it;
- one canonical printer for terms, literals, clauses, substitutions, positions,
  and variable sorts.

Acceptance:

- macro-specific code returns a list of primitive steps;
- printer logic no longer owns proof expansion decisions;
- `step_extra kernel_v1` becomes audit/migration metadata, not the primary
  data carrier.

### Milestone 3: Rename the Surface Kernel

Deliverables:

- `substitute` migrated toward `instantiate`;
- `equality_symmetry` migrated toward `flip`;
- `paramodulate`, `resolve`, `factor`, and equality rules use the same field
  discipline;
- old names accepted only as compatibility aliases for committed fixtures.

Acceptance:

- new certificates are expressed in the stable primitive vocabulary;
- the checker rejects primitive steps missing required fields.

### Milestone 4: Original-Context Source Binding

Deliverables:

- source map contains original Megalodon identifiers and source kinds;
- importer resolves those identifiers in the real context;
- set-command equalities are discharged by reflexivity;
- conjecture negation composes with the target theorem.

Acceptance:

- at least 10 original Megalodon theorems reconstruct through native
  `Syntax.pf`;
- exported-THF assumptions are not counted as original-context proofs.

### Milestone 5: Smolka-Style Preprocessing Proofs

Deliverables:

- proof-producing rectification;
- FOOL transformations;
- ENNF;
- CNF;
- definition introduction;
- Skolemization;
- source-to-clause composition.

Acceptance:

- source-generated clauses used by the clausal refutation all have proof terms
  from original sources;
- unsupported transformations fail closed.

### Milestone 6: Held-Out Evaluation

Procedure:

1. Export all benchmark problems once.
2. Run Vampire once in parallel with 10s timeout.
3. Cache the solvable set.
4. Reconstruct certificates in parallel.
5. Check native Megalodon proof terms in parallel.

Acceptance:

- at least 100 original-context theorem reconstructions;
- no `admit`, `aby`, bridge, derived source, or unchecked generated axiom;
- exact commands and artifact directories recorded.

## Test Plan

Development runs should be frontier-oriented:

- use `/project/tmp`;
- use `VAMPIRE_SECONDS=10`;
- use `JOBS=10` to `JOBS=20` for broad runs;
- avoid repeatedly rerunning unsolved Vampire searches;
- run focused 1-case or small frontier sets during implementation;
- run the 100-case gate only after focused fixes.

Test tiers:

```text
Tier 4: parser/shape/unit fixtures
Tier 3: synthetic closed core certificates
Tier 2: exported-THF-bound source-linked certificates
Tier 1: original-context native Megalodon proofs
```

Pass counts must always name their tier. A Tier 2 exported-THF-bound pass is
not an original-context proof.

Required gates:

- primitive unit fixtures for malformed and valid certificates;
- native core proof-term audit;
- fixed 100-case native preprocess proof-term frontier;
- strict live 100-case source-linked gate;
- new original-context gate.

## Design Review Checklist

Before implementing a patch, answer:

1. Does this make Vampire emit more exact primitive proof data?
2. Does this make Megalodon check an explicit primitive step as `Syntax.pf`?
3. Does this link a certificate input to the original Megalodon context?
4. Does this prove a source/preprocessing transformation?
5. Does this strengthen a fail-closed test gate?

If the answer to all five is no, the patch is probably off-plan.

Also reject the patch if it:

- makes Megalodon guess a missing Vampire substitution or position;
- adds a new macro theorem to repair a corpus-specific disjunction shape;
- adds a Python dependency to the qualifying path;
- maps source names by special-casing one library theorem;
- increases broad replay power without moving toward native proof terms.

## Immediate Next Actions

1. Commit the current subsumption primitive-alias and audit-chain fixes after
   the six-case frontier result is recorded.
2. Investigate `u792` first, because it is a clausal primitive failure and
   likely belongs either in Vampire's paramodulation export or Megalodon's
   fixed `paramodulate` template.
3. Investigate the two nonfunction proof-term failures next, because they
   likely reveal a malformed proof-term construction pattern.
4. Investigate `u445` wrong proposition after the term-formation issues,
   unless it shares the same root cause.
5. Start the C++ primitive builder as soon as the current frontier is stable,
   so the next macro fix does not add another local printer branch.
6. In parallel with clausal cleanup, design the original-context source object
   and the set-equality reflexivity rule.
7. Treat Skolemization as the first major Smolka-style transformation milestone
   after original source binding is in place.

## Bottom Line

The plan is not to make Megalodon smarter at rediscovering Vampire proofs.
The plan is to make Vampire emit a small, explicit, typed proof certificate and
make Megalodon check it as native proof terms, then separately prove that the
clausal inputs come from the original Megalodon development.

That is the line that should guide the next implementation work.
