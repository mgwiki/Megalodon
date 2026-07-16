# Vampire to Megalodon Design and Execution Plan

Date: 2026-07-16

Repositories:

- Megalodon: `/project/Megalodon`
- Vampire fork: `/project/vampire-leancheck`
- Temporary/generated artifacts: `/project/tmp`

This is the working design plan for the next phase of the Vampire-to-Megalodon
proof reconstruction project. It consolidates the prior reports, audits,
small-kernel plans, and current frontier results into one implementation
contract.

The purpose is to stop ad-hoc growth. A future change is aligned with this
plan only if it clearly moves one of the work packages below.

## Executive Decision

The project should follow a Prover9/Ivy-style architecture:

```text
original Megalodon theorem/context
  -> THF/TPTP export with a source/preprocessing map
  -> Vampire proof search
  -> Vampire-side expansion into primitive certificate steps
  -> Megalodon small-kernel checker over Syntax.tm and Syntax.pf
  -> composed proof of the original Megalodon theorem
```

The main ownership rule is:

- Vampire explains proof-search inferences while it still has exact
  substitutions, selected literals, equality orientation, term positions,
  sorts, and macro-specific state.
- Megalodon checks explicit primitive steps and elaborates them to proof
  terms.
- A separate source/preprocessing layer proves that the clauses used by the
  refutation follow from the original Megalodon context by Smolka-style
  transformations.

The broad OCaml textual replay engine and old Python tools are useful
diagnostic oracles. They are not the final architecture and should not keep
growing except for narrow correctness or audit fixes.

## Current Baseline

The branch has real infrastructure:

- Vampire emits native S-expression certificates.
- Megalodon parses, checks, and audits these certificates.
- Strict modes reject bridge assumptions and derived non-source premises.
- Source formulas are structurally checked for the supported exported THF
  fragment.
- Parallel live harnesses use `/project/tmp` and 10 second Vampire timeouts.
- A native proof-term path exists in Megalodon for a growing clausal and
  preprocessing fragment.

The best recent native preprocessing proof-term run on the 100-case source
linked list is:

```text
PREPROCESS_PF_PASS       97
ILL_FORMED_PROOF_TERM     2
WRONG_PROPOSITION         1
artifact: /project/tmp/live_preprocess_pf_100_after_multi_superposition_chain
```

The remaining failures in that run were:

```text
hammer.10806.144.th0.p  WRONG_PROPOSITION      u445
hammer.11405.35.th0.p   ILL_FORMED_PROOF_TERM  u283
hammer.11497.79.th0.p   ILL_FORMED_PROOF_TERM  u573
```

This is useful progress, but it is not the final target. The current success
is still largely exported-THF-bound. The next target is original-context
proof reconstruction with a small primitive certificate and no broad replay
fallback.

## Non-Negotiable Trust Boundary

Counted success must not use:

- `admit`;
- `aby`;
- `-allowincompleteqed`;
- bridge assumptions;
- derived non-source premises;
- unchecked source labels;
- private equality or private logical constants;
- Python proof reconstruction;
- Megalodon-side search that guesses data Vampire could have emitted.

The checker may assume the ordinary Megalodon context, including:

- classical reasoning;
- `xm`;
- Megalodon's equality;
- Megalodon's false, disjunction, and related logical constants.

Generated equalities from Megalodon's `set` command are not ordinary named
lemmas. They must be proved explicitly, normally by reflexivity or definitional
conversion.

## What Is Frozen

The following should not grow as a normal way to make progress:

- new Python proof-production logic;
- new JSON proof formats on the qualifying path;
- new large textual `.mg` replay constructors in Megalodon;
- library-specific proof tricks keyed to concrete theorem names;
- Megalodon-side heuristic reconstruction of missing substitutions, pivots,
  equality orientations, or rewrite positions;
- pass-count chasing that does not move primitive proof-term or
  original-context reconstruction.

Existing broad replay code can remain as:

- a regression oracle;
- a source of comparison artifacts;
- a way to classify failures;
- a temporary debug printer.

It should not be treated as the proof checker we are trying to finish.

## Layered Design

### Layer A: Source and Preprocessing Proofs

Input:

```text
original Megalodon theorem, definitions, local hypotheses, set commands,
and conjecture
```

Output:

```text
proof-producing clause inputs for the clausal refutation
```

This layer owns:

- mapping exported TPTP names back to original Megalodon names;
- recording source hashes and formulas at export time;
- validating that certificate inputs are justified by original `Syntax.tm`
  objects, not only by re-parsed THF strings;
- conjecture negation;
- rectification and alpha-renaming;
- FOOL transformations;
- ENNF;
- CNF;
- definition introduction;
- Skolemization;
- inequality/name introduction;
- `set`-generated equality proofs by reflexivity or definitional conversion.

This layer must not hide generated formulas as source axioms. Every generated
formula needs either a proof term or a checked transformation certificate.

### Layer B: Clausal Small Kernel

Input:

```text
source-justified clauses and primitive clausal proof steps
```

Output:

```text
Megalodon proof term for the clausal refutation
```

The stable primitive vocabulary is:

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

The current surface constructors `substitute` and `equality_symmetry` are
migration names for `instantiate` and `flip`.

Every primitive step must carry enough information for local checking:

- exact parent ids;
- parent/result clauses or hashes;
- selected literal indices;
- selected literal terms;
- substitutions with variable sorts;
- rewrite positions;
- equality direction and `from`/`to` terms;
- result clause;
- origin metadata pointing back to the original Vampire inference.

Megalodon may verify side conditions and instantiate fixed proof templates.
It must not rediscover missing proof-search data.

### Layer C: Vampire Macro Expansion

Input:

```text
Vampire internal proof with complex inferences
```

Output:

```text
Layer B primitive certificate sequence
```

This layer belongs primarily in Vampire.

Required lowerings:

- `superposition`
  -> instantiate equality parent, instantiate target parent, optional flip,
  one or more `paramodulate` steps, optional factor/rename.

- demodulation/rewrite
  -> instantiate demodulator, instantiate target, optional flip, one
  `paramodulate` per occurrence, optional factor/rename.

- `unit_resulting_resolution`
  -> instantiate parent clauses, optional flips, binary `resolve` chain,
  optional factor/rename.

- `subsumption_resolution`
  -> instantiate side parent, optional flip, resolve selected literal, check
  side-remainder coverage.

- `condensation`
  -> instantiate, factor or duplicate deletion, optional rename.

- AVATAR/split reasoning
  -> later separate propositional certificate; no opaque assumptions.

The accepted pattern is the Prover9/prooftrans pattern: complex prover proof,
expanded proof, then a small proof object. The Megalodon certificate is typed
and proof-term-oriented, but the separation is the same.

## Certificate IR Design

Vampire should gain a small internal primitive-certificate builder near
`Shell/MegalodonChecker`, so macro-specific code constructs primitive records
first and a single printer serializes them.

Representative shape:

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
  SourceOrigin source;
  OriginalInferenceOrigin origin;
};
```

The exact C++ names should follow Vampire conventions. The design invariant is
more important than the spelling: there should be one small primitive IR, not
scattered ad-hoc S-expression fragments for each failing benchmark.

## Work Packages

### WP0: Guardrails and Stop-Doing Rules

Goal:

Make it hard to accidentally grow the wrong system.

Tasks:

- Keep broad replay modes available only as diagnostics.
- Add comments and tests marking Python/JSON/text replay as non-qualifying.
- Keep strict modes rejecting bridges, derived premises, admits, `aby`, and
  unsupported source labels.
- Make unsupported proof-term constructors fail closed.

Acceptance:

- Running the qualifying harness cannot silently fall back to textual replay or
  Python.
- A new broad constructor requires an explicit design exception.

### WP1: Vampire Primitive Builder

Goal:

Move primitive proof construction into Vampire-side data structures.

Tasks:

- Introduce `MegalodonKernelStep` or equivalent.
- Route existing `kernel_v1` instantiation metadata through first-class
  `instantiate` records.
- Route equality flips through first-class `flip` records.
- Route superposition/rewrite through canonical `paramodulate` records.
- Preserve `kernel_v1` metadata temporarily as an audit layer.

Acceptance:

- Macro emitters build primitive records, not raw final strings.
- Existing strict 100-case certificate checks still pass.
- Native proof-term frontier does not regress.

### WP2: Clausal Kernel Proof Terms

Goal:

Make the Layer B primitive rules check as native `Syntax.pf`.

Tasks:

- Finish robust proof-term templates for `truth_conflict`, `paramodulate`,
  `resolve`, `factor`, equality resolution, equality factoring, instantiate,
  rename, and flip.
- Use Megalodon's equality and logical constants directly.
- Remove assumptions that specific library theorem names or arities exist.
- Ensure all proof terms check with `check_propofpf`.

Acceptance:

- The 100-case native preprocess proof-term run reaches 100/100 on the current
  source-linked list.
- Failures, if any, are unsupported source/preprocessing transformations, not
  clausal primitive proof-term bugs.

### WP3: Original-Context Source Binding

Goal:

Connect input clauses to the original Megalodon development, not just to
exported THF text.

Tasks:

- Extend/export source maps with original declaration ids, generated formula
  ids, hashes, and unmangling data.
- Implement reverse name mapping from TPTP/Vampire names to Megalodon names.
- Resolve theorem, lemma, definition, hypothesis, conjecture, and set-command
  origins in the original Megalodon context.
- Prove set-command equalities by reflexivity/definitional conversion.

Acceptance:

- At least 10 committed examples produce proof terms whose assumptions are
  original Megalodon facts, not re-parsed THF inputs.
- A deliberately wrong source label or wrong source formula fails closed.

### WP4: Smolka-Style Transformation Layer

Goal:

Prove the source-to-clause path explicitly.

Tasks:

- Specify each transformation as input proposition, output proposition, and
  proof constructor.
- Implement proof-producing transformations for conjecture negation,
  rectification, FOOL, ENNF, CNF, definition introduction, inequality/name
  introduction, and Skolemization.
- Treat Skolemization as a transformation with explicit introduced symbols,
  dependencies, sorts, and proof obligations.
- Separate transformation certificates from clausal refutation certificates.

Acceptance:

- Transformation steps are checked independently before clausal proof replay.
- Generated clauses cannot enter the clausal refutation unless justified by a
  transformation proof.
- Skolem symbols are scoped, typed, and linked to their source existential or
  choice principle use.

### WP5: Macro Lowering Coverage

Goal:

Lower frequent Vampire inferences into the small kernel in Vampire.

Priority:

1. superposition/rewrite/demodulation;
2. unit-resulting resolution;
3. subsumption resolution;
4. condensation;
5. equality factoring variants;
6. AVATAR/splits.

Acceptance:

- Each macro has a corpus of focused examples and at least one negative test
  for missing metadata.
- Megalodon does not implement broad search for these macros.
- Macro success means a sequence of primitive steps checks, not that a macro
  constructor is accepted opaquely.

### WP6: Test Suite and Evidence

Goal:

Have fast iteration and meaningful final evidence.

Test tiers:

- Tier 0: one focused failing proof, no Vampire rerun if an existing
  certificate suffices.
- Tier 1: 5-10 focused frontier cases in parallel.
- Tier 2: current 100-case source-linked live list, Vampire timeout 10s,
  10-20 parallel jobs.
- Tier 3: held-out or freshly regenerated 100+ theorem run.
- Tier 4: committed original-context regression suite.

Rules:

- Use `/project/tmp` for generated artifacts.
- Do not rerun unsolved Vampire searches repeatedly.
- Cache the list of Vampire-solvable THF problems for iteration.
- Run broad tests only after focused tests pass.
- Treat pass counts separately:
  - exported-THF-bound closed pass;
  - native proof-term pass;
  - original-context pass.

Acceptance:

- Final claims report exact tier and artifact directory.
- The qualifying suite has at least 100 theorems, no admits, no `aby`, no
  incomplete QED, and no non-source premises.

## Immediate Plan

The next engineering sequence should be:

1. Fix the three remaining native proof-term failures on the current 100-case
   frontier only when the fix is a general primitive proof-term or Vampire
   primitive emission fix.
2. Introduce or start extracting the Vampire primitive builder so future macro
   expansions stop adding scattered printer fragments.
3. Move `substitute`/`equality_symmetry` terminology toward
   `instantiate`/`flip`.
4. Add original-context source binding for a small committed set of examples,
   including at least one set-command equality.
5. Specify and implement the first proof-producing Smolka transformations in a
   separate layer, starting with the transformations most common in the
   current corpus.
6. Only after those are in place, run a fresh 100-theorem gate and report it as
   original-context or exported-THF-bound, as appropriate.

## Risk Register

### Risk: Building Another Reconstruction Prover in Megalodon

Symptom:

- `src/vampire_cert_v1.ml` grows with more heuristic matching and arity-specific
  proof helpers.

Mitigation:

- New proof power must come from Vampire primitive data or small proof-term
  templates.
- Broad replay additions require explicit justification.

### Risk: Certificate Format Drifts With Each Benchmark

Symptom:

- New fields are added for one example without becoming part of a typed
  primitive contract.

Mitigation:

- Add fields only to the primitive IR/spec.
- Add negative tests for missing or inconsistent metadata.

### Risk: Source Linkage Remains Exported-THF-Bound

Symptom:

- The system proves the exported problem but cannot inhabit the original
  Megalodon theorem.

Mitigation:

- Track original declaration ids and proof terms from export.
- Maintain separate scoreboards for exported-THF, native proof-term, and
  original-context passes.

### Risk: Skolemization Is Treated as an Axiom

Symptom:

- Skolem clauses appear as source facts or unchecked generated inputs.

Mitigation:

- Treat Skolemization as a checked transformation with introduced symbol
  metadata, dependencies, sorts, and a proof object using the allowed classical
  context.

### Risk: Slow Iteration

Symptom:

- Broad Vampire runs are repeated while debugging one proof-term template.

Mitigation:

- Reuse existing certificates when possible.
- Use focused lists and 10-20 parallel jobs for live runs.
- Keep all generated artifacts in `/project/tmp`.

## Definition of Done

The project is not done when a generated `.mg` script happens to check on a
fixed exported corpus.

The project is done for a milestone when:

- Vampire emits primitive proof data for the relevant proof-search inferences;
- Megalodon checks those primitives as native proof terms;
- source/preprocessing steps are proved or fail closed;
- the final proof is connected to the original Megalodon theorem/context;
- no admits, `aby`, incomplete QED, bridge assumptions, or derived non-source
  premises are used;
- a parallel 100+ theorem suite passes and its artifacts are reproducible.

## Review Checklist for Future Changes

Before committing a change, answer:

1. Does this move data emission into Vampire or checking into the small
   Megalodon kernel?
2. Is the change source/preprocessing proof work, and if so is it separated
   from clausal replay?
3. Does it avoid Python, JSON, textual replay growth, and library-specific
   special cases on the qualifying path?
4. Does it use Megalodon's equality and logical constants?
5. Does it fail closed when metadata is missing?
6. Was it tested first on a focused case, then on an appropriate parallel
   frontier?
7. Are generated artifacts under `/project/tmp`?

If the answer to any of these is no, the change should be treated as a
diagnostic experiment, not as progress toward the final reconstruction system.
