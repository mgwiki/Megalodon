# Vampire to Megalodon Execution Plan

Date: 2026-07-16

Repositories:

- Megalodon: `/project/Megalodon`
- Vampire fork: `/project/vampire-leancheck`
- Temporary artifacts: `/project/tmp`

This document is the concrete work plan for the next phase of the
Vampire-to-Megalodon reconstruction project. It is intentionally stricter than
the status reports. A future change should be judged by whether it moves the
system toward this plan.

Post-audit note, 2026-07-16: the execution order below is superseded where it
prioritizes growing the native preprocessing frontier. The first step is now
the trust reset from `reports/audit-REPORT-2026-07-16.md`: no
certificate-derived `Known` propositions on counted native paths. Use evidence
classes E1-E4 and test stages T0-T4 from
`reports/VAMPIRE-MEGALODON-DESIGN-PLAN-2026-07-16.md` to avoid confusing
integration evidence with proof reconstruction.

## One-Sentence Plan

Make Vampire emit a Prover9/Ivy-style sequence of explicit primitive proof
steps, make Megalodon check those steps as native `Syntax.pf` proof terms, and
separately prove the source-to-clause transformations that connect the clausal
refutation back to the original Megalodon theorem and library facts.

## Current Reality

The project already has useful infrastructure:

- native S-expression certificates from Vampire;
- an OCaml certificate parser/checker in Megalodon;
- strict source-linked live tests;
- rejection of bridge assumptions in the stricter modes;
- a native proof-term checker for a growing clausal subset;
- focused frontier harnesses using `/project/tmp`;
- a 10s Vampire timeout discipline;
- parallel live-test harnesses.

The project is not finished:

- the success path is still mostly exported-THF-bound, not original-context
  Megalodon proof reconstruction;
- the OCaml file still contains too much broad reconstruction logic;
- Vampire does not yet have a clean internal primitive-certificate IR;
- some Vampire macros still escape as broad certificate constructors;
- source/preprocessing proof production is partial;
- Skolemization is not yet solved in a source-connected way;
- AVATAR/split composition remains transitional.

As of this plan, the focused live proof-term frontier has moved past
`inequality_name_intro` and `inequality_split` on `hammer.11453.77.th0.p` and
now stops at:

```text
u346: unit_resulting_resolution
```

This is a useful diagnostic: the next correct move is not to add a broad
Megalodon-side macro proof searcher. The next correct move is to make Vampire
expand this macro into primitive instantiation and binary resolution steps.

## Non-Negotiable Constraints

The final counted path must not use:

- `admit`;
- `aby`;
- `-allowincompleteqed`;
- bridge assumptions;
- derived non-source premises;
- unchecked source labels;
- private replacements for Megalodon's equality, false, disjunction, or
  classical facts.

The working assumptions are:

- classical reasoning is available;
- `xm` is available in the Megalodon context;
- Megalodon's own equality and logical constants are used;
- set-command generated equalities are proved in Megalodon, usually by
  reflexivity or definitional conversion;
- all generated artifacts go under `/project/tmp`;
- Vampire proof search is limited to 10 seconds per problem;
- large validation runs are parallel, normally with 10 to 20 jobs.

## Architecture

The intended pipeline is:

```text
Original Megalodon theorem/context
  -> THF export with source map
  -> Vampire proof search
  -> Vampire primitive proof expansion
  -> native S-expression certificate
  -> Megalodon OCaml parser/checker
  -> Syntax.tm and Syntax.pf proof object
  -> original Megalodon theorem checked without extra assumptions
```

The pipeline has three layers.

### Layer A: Source and Transformation Proofs

This layer proves that the clauses fed to the clausal refutation are justified
by the original Megalodon context.

It owns:

- lookup of original theorem, lemma, hypothesis, definition, and conjecture
  names from exported TPTP names;
- unmangling of exported names back to Megalodon identifiers;
- source formula validation against the original `Syntax.tm`;
- set-command generated equalities;
- conjecture negation;
- rectification;
- FOOL transformations;
- ENNF;
- CNF;
- definition introduction;
- Skolemization.

It must produce proof terms or checked transformation certificates. It must not
pretend that a generated clause is a source axiom unless it has been linked to
and proved from the original source.

### Layer B: Clausal Kernel

This layer checks the actual clausal refutation once every input clause has a
source proof.

The intended stable primitive rules are:

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

The Megalodon checker may verify local side conditions and elaborate fixed
proof templates. It must not infer missing pivots, substitutions, rewrite
positions, or orientation choices.

Each primitive step should carry:

- exact parent ids;
- parent/result clauses or checked hashes;
- selected literal indices;
- selected literal terms;
- explicit substitutions with variable sorts;
- rewrite position and direction for equality transport;
- equality `from` and `to` terms where relevant;
- result clause;
- origin metadata pointing back to the Vampire inference being expanded.

### Layer C: Vampire Macro Expansion

This layer belongs primarily in Vampire because Vampire has the relevant proof
search state when the inference is made.

The rule is:

```text
complex Vampire inference -> sequence of Layer B primitives
```

Required lowerings:

- `unit_resulting_resolution`
  -> instantiate current parent, instantiate unit parent, optional flip, binary
  `resolve`, repeat for each unit, optional rename/factor.

- `subsumption_resolution`
  -> instantiate side parent, optional flip, one `resolve`, check that the side
  remainder is covered.

- `superposition`
  -> instantiate equality parent, instantiate target parent, optional flip,
  one `paramodulate`, optional factor/rename.

- `rewrite` and demodulation
  -> instantiate demodulator, instantiate target, optional flip, one
  `paramodulate` per occurrence, optional factor/rename.

- `condensation`
  -> instantiate, factor or duplicate-literal deletion, optional rename.

- AVATAR
  -> separate propositional certificate layer, later; no opaque assumption.

This follows the Prover9 pattern:

```text
normal proof
  -> expanded proof with explicit clause operations
  -> Ivy proof object with input/instantiate/flip/resolve/paramod/propositional
```

For this project, the Ivy object is typed and Megalodon-oriented, but the
separation is the same.

## Vampire-Side Work Plan

### V1. Create a Primitive Certificate Builder

Add an internal builder near `Shell/MegalodonChecker`:

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
  OptionalSubstitution substitution;
  OptionalLiteralSelection selected;
  OptionalLiteralSelection other;
  OptionalPosition position;
  OptionalTerm from;
  OptionalTerm to;
  OriginalInferenceOrigin origin;
};
```

The exact C++ type names should follow Vampire conventions. The important part
is that inference-specific code constructs primitive steps first, then a single
printer serializes them.

### V2. Convert Existing `kernel_v1` Metadata Into Real Primitives

Current metadata is useful for auditing but is not enough as a final proof
object. The next migration is:

- make non-identity substitution metadata become first-class `instantiate`;
- make `equality_symmetry` become first-class `flip`;
- make existing `paramodulate` metadata the canonical equality transport
  primitive;
- preserve old `step_extra kernel_v1` records temporarily as an audit trail.

### V3. Expand Frequent Macros in Vampire

Immediate priority order:

1. `unit_resulting_resolution`, because it is the current focused frontier.
2. `subsumption_resolution`, because it is frequent and structurally similar.
3. `superposition` and rewrite/demodulation through the same `paramodulate`
   primitive path.
4. `condensation` and duplicate deletion.
5. AVATAR only after the clausal kernel is stable.

For `unit_resulting_resolution`, the implementation should debug why the
current exporter sometimes falls back to a macro S-expression instead of the
existing expansion path. If Vampire has enough trace data, fix the fallback by
emitting:

```text
instantiate current parent if needed
instantiate unit parent if needed
resolve selected complementary literals
repeat
rename/factor if needed
```

If the trace data is insufficient, extend the Vampire-side trace data. Do not
compensate by adding heuristic Megalodon search.

### V4. Record Positions at Inference Time

For equality steps, the exporter must not ask Megalodon to rediscover rewrite
positions.

Vampire should record:

- equality parent id;
- target parent id;
- literal index;
- term position inside the literal;
- direction;
- matched substitution;
- before and after terms;
- result clause.

This is the same lesson as Prover9's demodulation expansion: record the exact
rewrite occurrence while the prover has it.

## Megalodon-Side Work Plan

### M1. Shrink the Accepted Checker Surface

The native OCaml checker should converge toward:

```ocaml
source_context -> certificate -> Syntax.tm * Syntax.pf
```

Broad textual replay code may remain as a diagnostic oracle, but it should not
be counted as proof reconstruction.

### M2. Implement Fixed Proof Templates for Kernel Rules

For each Layer B primitive, implement a small proof-term template:

- `instantiate`: quantified parent proof applied to explicit terms.
- `rename`: alpha/variable renaming only, checked structurally.
- `flip`: equality symmetry at the given literal.
- `resolve`: binary resolution over explicitly complementary literals.
- `factor`: duplicate literal contraction or equality factoring.
- `equality_resolution`: contradiction from disequality/reflexivity.
- `paramodulate`: equality transport at an explicit position.
- `truth_conflict`: contradiction from true/false conflict.
- `contradiction`: empty-clause closure to the target theorem.

The checker may compare expected and actual clauses after beta/eta and
definitional normalization, but it should not search for the missing inference.

### M3. Treat Broad Rules as Failures Unless Lowered

Rules such as `unit_resulting_resolution`, `superposition`, `rewrite`,
`subsumption_resolution`, and `condensation` should be accepted in the final
path only when represented by primitive steps. Transitional support can exist
for diagnostics, but the counted gate should audit that no broad macro remains.

### M4. Finish Source Linkage

The source map must connect every certificate input to one of:

- original Megalodon theorem/lemma/hypothesis;
- original definition;
- conjecture negation;
- set-generated equality proved by reflexivity/conversion;
- certified transformation output from Layer A.

The checker should compare against actual Megalodon `Syntax.tm` where possible,
not just string names or comments.

### M5. Implement Smolka-Style Transformations Separately

Smolka-style transformations are not clausal proof search. They belong in
Layer A and should have their own proof-producing transformations:

- rectification with explicit fresh-name map;
- FOOL elimination/lifting;
- ENNF;
- CNF distribution and clause projection;
- definitional CNF where used;
- Skolemization with explicit dependency lists and witness principles.

The deliverable for each transformation is a Megalodon proof from the source
formula to the generated formula or clause, not a bridge assumption.

### M6. Skolemization Plan

Skolemization must be handled as a source transformation, not as a clausal
inference.

Each Skolem step should carry:

- quantified source formula;
- polarity/context;
- existential variable being Skolemized;
- dependency variables and their sorts;
- introduced Skolem symbol name and type;
- result formula;
- proof principle used in Megalodon.

The expected proof shape is classical. It may use the available classical
choice/existence principles from the Megalodon library if present; otherwise
the missing library principle must be added explicitly and reviewed, not hidden
inside the importer.

## Testing Plan

The test suite should be tiered.

### Tier 0: Handwritten Unit Certificates

Purpose: keep each primitive rule honest.

Contents:

- one positive and one negative fixture per kernel primitive;
- malformed substitution;
- wrong pivot;
- wrong rewrite position;
- wrong source id;
- wrong result clause;
- wrong type/sort.

These tests should be fast and run on every edit.

### Tier 1: Focused Frontier Tests

Purpose: iterate quickly on the current blocker.

Rules:

- use a one-problem or small-list frontier file;
- use `/project/tmp`;
- use `VAMPIRE_SECONDS=10`;
- run with `JOBS=1` for a single debugging target and `JOBS=10` for a small
  frontier batch;
- inspect only the first unsupported rule or proof-term failure.

Current target:

```sh
TMPDIR=/project/tmp \
PROBLEM_DIR=/project/Megalodon/tests/vampire_certificate/closed_cases \
PROBLEMS_FILE=/project/tmp/inequality_name_intro_focus.list \
LIMIT=1 JOBS=1 VAMPIRE_SECONDS=10 WALL_SECONDS=15 \
MIN_CERT=1 REQUIRE_SOURCE_ORIGIN=1 STRICT_CERT_V1=1 \
WORK_DIR=/project/tmp/live_preprocess_pf_unit_resulting_resolution_focus \
tests/vampire_certificate/run_native_live_preprocess_pf_frontier.sh
```

Expected current failure before the next Vampire-side fix:

```text
UNSUPPORTED_RULE_unit_resulting_resolution
```

### Tier 2: Cached Solved-Problem Regression

Purpose: avoid wasting time rerunning unsolved Vampire searches.

Rules:

- determine solvable problems once;
- cache Vampire outputs/certificates under `/project/tmp`;
- replay reconstruction repeatedly against cached certificates;
- regenerate only when Vampire exporter code changes.

### Tier 3: Parallel Live 100 Gate

Purpose: check the exported-THF/source-linked pipeline.

Run only at meaningful milestones:

```sh
TMPDIR=/project/tmp \
PROBLEM_DIR=/project/Megalodon/tests/vampire_certificate/closed_cases \
PROBLEMS_FILE=/project/Megalodon/tests/vampire_certificate/source_linked_strict_100.list \
LIMIT=100 JOBS=20 VAMPIRE_SECONDS=10 WALL_SECONDS=15 MIN_PASS=100 \
CHECK_SOURCE_MAP=1 REQUIRE_SOURCE_ORIGIN=1 STRICT_CERT_V1=1 \
AUDIT_NATIVE_PRIMITIVES=1 AUDIT_KERNEL_V1_METADATA=1 \
AUDIT_SUBSTITUTE_METADATA=1 \
WORK_DIR=/project/tmp/live_strict_100_next \
tests/vampire_certificate/run_native_live_parallel.sh
```

This is not yet the final success criterion because it is exported-THF-bound.

### Tier 4: Original-Context Gate

Purpose: count real project success.

Requirements:

- no `admit`;
- no `aby`;
- no incomplete QED;
- no bridge assumptions;
- every clause input linked to an original Megalodon fact or proved
  transformation;
- final theorem checked in the original Megalodon context.

This is the gate that should eventually be run on 100 theorems.

## Acceptance Criteria

A change is accepted as architectural progress if it satisfies at least one of
these:

- removes a broad macro from the final certificate path by lowering it in
  Vampire;
- adds a fixed proof-term checker for an already explicit primitive;
- strengthens source linkage against original Megalodon terms;
- proves a source/preprocessing transformation;
- improves tests so false successes are rejected.

A change is not accepted as architectural progress if it mainly:

- adds Python proof search;
- adds a Megalodon-side heuristic to guess missing Vampire data;
- hardwires a library theorem or symbol name;
- converts a derived clause into an input assumption;
- counts exported-THF checking as original-context reconstruction;
- expands the certificate language with another broad macro instead of
  lowering that macro.

## Immediate Engineering Queue

The next implementation queue is:

1. Finish validating and committing the current `inequality_name_intro` /
   `inequality_split` native proof-term work if it passes the focused and
   small frontier gates.
2. Debug Vampire's `unit_resulting_resolution` expansion fallback with
   `MEGALODON_CERT_DEBUG=1`.
3. Change Vampire so `unit_resulting_resolution` emits primitive
   instantiate/resolve steps in the focused failing case.
4. Rebuild Vampire with parallel make:

   ```sh
   TMPDIR=/project/tmp make -j10 vampire_rel
   ```

5. Re-run the one-problem frontier, then a small parallel frontier.
6. Only after that, run the 100-case live gate.
7. Start the source-linkage work in parallel with the clausal kernel cleanup:
   source name lookup, set-equality reflexivity, conjecture negation, and
   first Smolka transformations.

## Design Decision for the Current Frontier

For `u346: unit_resulting_resolution`, the planned fix is Vampire-side macro
lowering.

Megalodon-side implementation of a `unit_resulting_resolution` macro checker is
only acceptable as a temporary diagnostic if it does not enter the counted
proof path. The counted path should see only primitive instantiation and
resolution steps.

This is the practical test of whether the project is now following the
Prover9/Ivy path rather than growing another reconstruction engine.
