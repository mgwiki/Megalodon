# Vampire to Megalodon Small-Kernel Certificate Plan

Date: 2026-07-16

Status: design plan for the `vampire/megalodon5` branch and successors

Post-audit note, 2026-07-16: `reports/audit-REPORT-2026-07-16.md`
changes the milestone order. The native preprocessing frontier described
below is no longer qualifying proof-term evidence because it relied on
certificate-derived `Known` propositions. The first milestone is now a trust
reset: dynamic known-theorem insertion must be absent from counted native
paths. The strict live 100 run is integration/metadata evidence, not closed
proof reconstruction.

Second post-audit note, 2026-07-16: the `vampire/megalodon5` real-core
frontier audit confirms that no non-synthetic closed hammer certificate enters
the current native proof-term core. The 23 `CORE_PF_PASS` cases are still only
`core.cnf.*` fixtures. All 149 real closed hammer certificates are stopped by
source/preprocessing entry rules before the clausal kernel can qualify them.
The next milestone is therefore not another corpus selection pass. It is a
proof-producing source/preprocessing certificate layer for `formula_input` and
`formula_term_input`, plus continued Vampire-side primitive lowering for the
clausal part that follows.

Progress note, 2026-07-17: the core proof-term path now handles one narrow
Skolemization case without admissions or dynamic `Known` injection:
direct nullary existential Skolemization with explicit Vampire
`kernel_v1` metadata, zero dependencies, an introduced-symbol declaration,
and `classical_choice`. Megalodon adds a generated delta definition
`sk = Eps_i (fun x => P x)`, closes that definition over the original
certificate variables, and checks the step by applying the fixed choice
principle to the parent existential proof. This is a real `Syntax.pf` step,
but it is not yet the full Skolemization solution: dependent Skolem functions,
multiple simultaneous introductions, and broader Smolka-style preprocessing
still remain frontier work.

Second progress note, 2026-07-17: dependent Skolem delta unfolding is now
handled by the proof checker at the conversion/head-normalization boundary
rather than by eagerly rewriting generated Skolem terms out of certificate
formulas. The representative real hammer case
`hammer.1007.43.th0.p` gets past the earlier formula-level Skolem mismatch
and stops at a later clausal proof-term opening problem in step `u210`
(`paramodulate`): a retained-variable parent proof is instantiated into a
result context and produces `_15` in a context of length 15. This is the next
small-kernel elaboration issue. It should be solved by specifying and
implementing the theorem-opening operation for stored `TLam` proofs, not by
adding special cases for `famunion`, `sK1`, this library, or this theorem.

Primary repositories:

- Megalodon: `/project/Megalodon`
- Vampire proof-export fork: `/project/vampire-leancheck`
- Temporary artifacts: `/project/tmp`

Related documents:

- `reports/VAMPIRE-MEGALODON-IMPLEMENTATION-DESIGN-2026-07-16.md`
- `reports/vampire-megalodon-certificate-spec.md`
- `reports/PROVER9-IVY-ANALYSIS-2026-07-13.md`
- `reports/REPORT-2026-07-16.md`
- `reports/audit-REPORT-2026-07-15.md`
- `reports/audit-response-2026-07-15.md`

## Executive Plan

The overall plan is to turn Vampire's proof into a small certificate that is
checked by Megalodon, not to build a second theorem prover in Megalodon.

The work is organized around three explicit boundaries:

1. Vampire expands its own complex inferences while it still has exact
   substitutions, selected literals, positions, sorts, and parent clauses.
2. Megalodon checks a fixed clausal kernel and elaborates it to native
   `Syntax.pf` proof terms.
3. A separate source/preprocessing layer connects the clausal inputs back to
   original Megalodon theorems, lemmas, definitions, set-generated equalities,
   conjecture negation, and Smolka-style transformations.

The current branch has useful regression infrastructure, but the broad textual
replay engine is no longer the architectural target. It is a temporary oracle
and debugging tool. Counted success should increasingly move to the native
`Syntax.pf` path and then to original-context reconstruction.

The immediate sequencing is now:

1. Keep certificate-derived `Known` insertion out of every counted native path.
2. Make `formula_input` and `formula_term_input` proof-producing from the
   original Megalodon source context, including set-generated equalities by
   reflexivity and conjecture negation.
3. Add the first Smolka-style transformation proofs needed to justify real
   clausal inputs: rectification, FOOL/boolean normalization, ENNF, CNF
   projection, and then Skolemization.
4. Move frequent Vampire clausal macros onto a shared Vampire-side primitive
   builder so the post-preprocessing refutation is a small kernel proof.
5. Expand native Megalodon proof-term checking for the same primitive kernel.
6. Only then run the final fresh 100-theorem gate as a qualifying result.

## Purpose

This document is the implementation plan for moving the project away from
ad-hoc textual replay and toward a Prover9/Ivy-style proof object:

```text
Vampire proof
  -> Vampire-side expansion into small primitive steps
  -> native S-expression certificate
  -> Megalodon small-kernel checker / Syntax.pf elaborator
  -> original-context Megalodon proof
```

The purpose is not to describe what has already happened. The purpose is to
define the target architecture clearly enough that implementation work can be
judged as aligned or misaligned.

The key rule is:

> New proof reconstruction power should come from Vampire emitting more exact
> primitive proof data, and from Megalodon checking a small fixed calculus.
> It should not come from a growing Megalodon-side heuristic reconstruction
> engine or from Python proof search.

## Current Problem

The project has made real progress:

- Vampire emits a native S-expression certificate.
- Megalodon parses and validates that certificate in OCaml.
- Closed mode rejects bridge and derived assumptions.
- Source formulas are checked for the supported exported THF fragment.
- The branch has a native `Syntax.pf` seed via `-vampirecertv1corepfcheck`.
- A strict live 100-case artifact has all 100 certificates passing Megalodon
  checking with source linkage, primitive metadata audit, and substitute
  metadata audit enabled.
- A 23-case core-closed frontier now passes the native proof-term audit.

But the architecture is not yet clean:

- `src/vampire_cert_v1.ml` still contains a large textual replay engine.
- Many broad certificate constructors are checked or replayed outside the
  native proof-term path.
- Some Vampire-side expansions are implemented locally inside
  `MegalodonChecker.cpp`, but there is no clean internal primitive proof IR.
- Non-identity helper substitutions have metadata in the current 100-case
  live gate, but the certificate vocabulary still exposes `substitute` as a
  transitional surface constructor rather than a first-class `instantiate`
  primitive.
- Original-context reconstruction is not complete.
- Smolka-style preprocessing transformations are not yet a separate small
  proof-producing layer.

The plan below addresses these gaps.

## Measured Baseline on 2026-07-16

The following results define the current local baseline on
`vampire/megalodon5`.

Strict live 100-case gate:

```sh
TMPDIR=/project/tmp \
PROBLEM_DIR=/project/Megalodon/tests/vampire_certificate/closed_cases \
PROBLEMS_FILE=/project/Megalodon/tests/vampire_certificate/source_linked_strict_100.list \
LIMIT=100 JOBS=20 VAMPIRE_SECONDS=10 WALL_SECONDS=15 MIN_PASS=100 \
CHECK_SOURCE_MAP=1 REQUIRE_SOURCE_ORIGIN=1 STRICT_CERT_V1=1 \
AUDIT_NATIVE_PRIMITIVES=1 AUDIT_KERNEL_V1_METADATA=1 \
AUDIT_SUBSTITUTE_METADATA=1 \
WORK_DIR=/project/tmp/live_strict_100_metadata_fix \
tests/vampire_certificate/run_native_live_parallel.sh
```

Result:

- `PASS 100`
- `kernel_v1 records: 3143`
- `instantiation: 375`
- `rewrite: 99`
- `superposition: 338`
- `unit_resulting_resolution: 1`

After the July 16 audit this is classified as integration/metadata evidence:
exported-THF-bound, source-linked, structurally checked certificate data. It
is not closed proof reconstruction and not E1 original-context proof
reconstruction.

Synthetic core native proof-term gate:

```sh
TMPDIR=/project/tmp JOBS=10 \
tests/vampire_certificate/run_native_cert_v1_core_closed_audit.sh
```

Result:

- `CORE_ELIGIBLE 114`
- `CLOSED_PASS 114`
- `CORE_CLOSED_PASS 114`
- `CORE_PF_PASS 114`

Artifacts:

- `/project/tmp/native_cert_v1_core_closed_audit.8kHy49`
- `/project/tmp/latest_native_cert_v1_core_closed_audit`

Real closed hammer frontier:

```sh
TMPDIR=/project/tmp JOBS=10 \
tests/vampire_certificate/run_native_cert_v1_real_core_frontier.sh
```

Result:

- `REAL_CORE_ELIGIBLE 91`
- `SYNTHETIC_CORE_ELIGIBLE 23`
- `EXCLUDED 58`

The source-entry, checked-rectification, checked FOOL, checked ENNF,
definition-input, inequality, and annotated-instantiation updates moved the
first large real batch into the native proof-producing gate. These steps are
accepted only when the native elaborator constructs checked `Syntax.pf` terms
for the source entry, transformation, and identity/CNF/instantiation step; they
do not use dynamic `Known` propositions.

The first excluded-rule distribution is now dominated by Skolemization and
unannotated non-identity substitutions:

- `skolem_formula`: 48
- `nonidentity_substitute`: 9
- `avatar_definition`: 1

This is now the controlling blocker for most real examples. A real hammer proof
cannot count merely because its later clausal steps contain `resolve`,
`paramodulate`, `factor`, or `equality_resolution`; its formula and generated
clausal inputs must first be proved from the original Megalodon context and
all macro substitutions must either carry explicit Vampire primitive metadata
or be expanded before reaching the counted gate.

The first blockers beyond this frontier are not clausal primitive failures.
They are mostly source/preprocessing and macro territory:

- `nonidentity_substitute`
- `skolem_formula`
- AVATAR/split rules

This confirms the next architectural split: do not grow broad Megalodon
reconstruction to handle these as opaque replay tricks. First make the
source/preprocessing layer proof-producing for real inputs; in parallel, push
clausal macros down to Vampire-side primitive steps so the already justified
clauses can be checked by the small kernel.

Source-obligation audit:

```sh
TMPDIR=/project/tmp JOBS=10 \
tests/vampire_certificate/run_native_cert_v1_source_obligation_audit.sh
```

Result on the default 96-case closed-corpus selection:

- `AUDIT_PASS 96`
- `total 388`
- `formula_checked 388`
- `formula_unsupported 0`
- `formula_missing 0`
- `equality_checked 2`
- `set_reflexivity_checked 0`
- `true_checked 0`

Artifacts:

- `/project/tmp/native_cert_v1_source_obligations.1CaqDj`
- `/project/tmp/latest_native_cert_v1_source_obligations`

This is a source-linking measurement, not proof reconstruction evidence. It
shows that the selected committed source inputs are within the currently
checked exported THF fragment, while the real-core frontier still shows that
their first proof-producing blocker is `formula_input`/`formula_term_input`.
The next implementation step is to turn these audited source obligations into
native Megalodon proof bindings instead of treating them merely as validated
certificate inputs.

Original-context source resolver gate:

- `-vampirecertv1sourcecontext` now loads the main Megalodon file before
  auditing the certificate and checks hash-backed `known`/`axiom` source
  bindings against the loaded `sigdelta` with `Known hash`.
- `-vampirecertv1sourcecontextstrict` fails when a hash-backed source is
  missing or mismatched.
- The smoke suite generates a fresh Megalodon axiom, extracts its real hash,
  emits a matching THF source map and native certificate, and checks that the
  context audit reports `known_checked=1`.

This does not yet eliminate local source assumptions. It is the prerequisite
for replacing global source hypotheses by `Known hash` proofs while preserving
the audit's trust boundary: the proposition must already be in the loaded
Megalodon context and cannot be installed from the certificate.

Implementation update:

- The core and preprocess native proof-term elaborators now accept a
  source-proof table plus an external delta table.
- `-vampirecertv1sourcecontext` populates that table for hash-backed sources
  that successfully check as `Known hash` in the loaded Megalodon context.
- Those sources are omitted from the generated source-hypothesis spine and are
  checked internally as ordinary proof terms.
- The smoke suite includes a generated core fixture proving that one
  hash-backed source is consumed this way.

Branch `vampire/megalodon5` adds the first live original-context composition
for `vampireaby`:

- hash-backed global facts are still discharged inside the native core checker
  as `Known hash`;
- local theorem hypotheses are deliberately *not* inserted under Vampire's
  closed variable binders, because doing so shifts them under certificate-local
  `forall`s and makes a live `Hyp` prove the wrong de Bruijn variable;
- instead, local facts remain explicit source assumptions in the certificate
  proposition, Vampire variables are instantiated with matching live context
  variables, and the local `Hyp` proofs are applied at the Megalodon boundary;
- when the only remaining certificate source is the negated conjecture, the
  resulting `~~goal` proof is converted to `goal` using the loaded `xm`
  theorem.

The smoke suite now has a live fake-Vampire fixture that checks this path:
`source_context known=0 local=1 unresolved=1` followed by `Vampire native
certificate reconstructed aby proof term` and a closing `Everything looks
good`.  Because the project setting assumes classical reasoning, an axiom
named `xm` is treated as a trusted classical principle only when its
proposition is convertible to the standard excluded-middle shape
`forall P:prop, P \/ ~P`; a negative fixture checks that a malformed `xm` is
not trusted.  A second live fixture appends the same certificate-reconstructed
theorem after the `xm` declaration in an `UpToOctonions` library prelude and
checks that it also closes.  A third fixture checks a multi-local case with
two local source facts plus the negated conjecture, ensuring the boundary
application handles more than one local `Hyp`.

This is still partial original-context reconstruction: local facts and
conjecture negation now compose in simple core cases, including multiple local
facts, but local definitions, generated source transformations, quantified
source matching beyond direct context-variable instantiation, and
Smolka-style preprocessing proofs remain open.

## Design Principles

### 1. Vampire explains, Megalodon checks

Vampire has access to:

- selected literals;
- active substitutions;
- side substitutions;
- unification results;
- equality orientation;
- rewrite positions;
- AVATAR state;
- clause parents;
- inference-specific extras;
- term and variable sorts.

Megalodon should not rediscover this information from before/after formulas.
It should receive it explicitly and check it locally.

### 2. Small primitive kernel first

The primitive clausal kernel should remain small. A proposed stable kernel is:

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

This is slightly larger than Prover9 Ivy because Megalodon needs explicit
typed equality behavior and because Vampire exposes equality factoring and
truth/FOOL interactions as important recurring cases. It is still small enough
to check directly.

The existing certificate constructors `substitute` and `equality_symmetry`
should be treated as surface names for `instantiate` and `flip` respectively.
Long term, the certificate should converge on the kernel vocabulary above.

### 3. Macro inferences lower before printing

Complex Vampire inferences should not be primitive Megalodon rules. They should
lower to the kernel:

```text
superposition
  -> instantiate equality parent
  -> instantiate target parent
  -> optional flip
  -> paramodulate
  -> factor / rename if needed

demodulation / rewrite
  -> instantiate demodulator if needed
  -> instantiate target if needed
  -> optional flip
  -> one paramodulate per occurrence
  -> factor / rename if needed

unit-resulting resolution
  -> instantiate current parent
  -> instantiate unit parent
  -> optional flips
  -> one binary resolve per unit step
  -> rename if needed

subsumption resolution
  -> instantiate side parent
  -> optional flips
  -> resolve selected literal
  -> check side-remainder coverage

condensation
  -> instantiate
  -> factor / propositional duplicate deletion
  -> rename if needed
```

This mirrors Prover9's `expand_proof` plus `expand_proof_ivy` split.

### 4. Source transformations are separate from the clausal kernel

FOOL, ENNF, CNF, rectification, definition introduction, Skolemization,
conjecture negation, and set-generated equalities should not be hidden inside
clausal proof replay.

They need a separate preprocessing certificate layer:

```text
original Megalodon source fact
  -> exported THF formula
  -> normalized formula
  -> clausal input
```

The clausal kernel starts after source-to-clause transformation has produced
clause inputs. The final proof composes the preprocessing proof with the
clausal refutation.

### 5. Native proof terms are the qualifying path

Textual `.mg` emission is useful for debugging and regression. It should not
remain the primary success criterion.

The qualifying path should converge on:

```ocaml
source_context -> certificate -> Syntax.tm * Syntax.pf
```

and every constructed proof term should be checked with `check_propofpf`.

### 6. No hidden admissions

Accepted proofs must not use:

- `admit`;
- `aby`;
- `-allowincompleteqed`;
- bridge assumptions;
- derived non-source premises;
- unsupported axiom injection;
- source labels without formula/context verification.

## Target Architecture

### Layer 1: Megalodon export

Responsibilities:

- Export THF/TPTP problems.
- Emit source-map metadata for every exported formula.
- Preserve origin information:
  - original theorem;
  - original lemma/fact;
  - local hypothesis;
  - definition;
  - set-generated equality;
  - conjecture negation;
  - generated transformation artifact.
- Emit enough metadata to recover original names and propositions.

Non-responsibilities:

- It should not pre-prove Vampire inferences.
- It should not hide source transformations as unlabelled axioms.

Required future additions:

- stable source formula hashes;
- stable original-context identifiers;
- explicit classification of set-command equalities;
- exported formula hash recomputed independently by Megalodon importer.

### Layer 2: Vampire proof search

Responsibilities:

- Solve THF/TPTP problems.
- Preserve proof/inference metadata needed for reconstruction.
- Avoid losing substitutions, selected literals, and positions.

Non-responsibilities:

- It does not need to emit Megalodon proof terms.
- It does not need to know original Megalodon local proof contexts beyond
  exported source metadata.

### Layer 3: Vampire proof expansion

This is the missing Prover9-style layer.

Proposed internal structure:

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
  Clause result;
  SortMap variableSorts;
  SourceOrigin source;              // only for input-like steps
  std::optional<Substitution> subst;
  std::optional<SelectedLiteral> selected;
  std::optional<SelectedLiteral> other;
  std::optional<Position> position;
  std::optional<Term> from;
  std::optional<Term> to;
  std::optional<OriginalInference> origin;
};
```

This does not need to be exactly the final C++ shape. The important point is
that Vampire should build a normalized list of small kernel steps before
printing the S-expression certificate.

Each macro inference should expand to a list:

```cpp
std::vector<MegalodonKernelStep>
expandForMegalodon(Unit* unit, InferenceInformation* info);
```

Each emitted primitive step must be self-checkable by simple syntactic
conditions.

### Layer 4: Certificate printer

Responsibilities:

- Print kernel steps as S-expressions.
- Print terms, literals, clauses, substitutions, sorts, and positions in one
  canonical format.
- Include `kernel_v1` metadata only when needed during migration.

Long-term goal:

- The primitive step itself should contain the data now duplicated in
  `step_extra`.
- `step_extra "kernel_v1"` remains a migration bridge but should shrink.

### Layer 5: Megalodon certificate parser and checker

Responsibilities:

- Parse the S-expression certificate.
- Validate local side conditions.
- Reject malformed or unsupported certificates.
- Elaborate primitive clausal steps to `Syntax.pf`.
- Check every proof term with `check_propofpf`.

Non-responsibilities:

- It must not search for missing pivots.
- It must not infer substitutions that Vampire failed to emit.
- It must not repair malformed clauses.
- It must not silently fall back from native proof terms to textual replay in
  a qualifying mode.

### Layer 6: Original-context composition

Responsibilities:

- Replace exported source assumptions by original Megalodon facts.
- Prove set-generated equality facts by reflexivity/definitional conversion.
- Connect conjecture negation to the target theorem.
- Resolve approved logical principles such as classical `xm` from the library.
- Compose preprocessing proofs with the clausal refutation.

This is required for E1 success.

## Primitive Rule Specification

This section defines the intended kernel rules. The names may be adjusted, but
the proof obligations should stay stable.

### `input`

Introduces a clause already justified by the source/preprocessing layer.

Fields:

- `id`
- `source`
- `result_clause`

Megalodon checker:

- obtains or assumes the clause proof from the source/preprocessing context;
- does not treat arbitrary certificate input as trusted in E1.

### `instantiate`

Applies an explicit substitution to a parent clause.

Fields:

- `id`
- `parent`
- `substitution`
- `parent_clause`
- `parent_substituted_clause`
- `result_clause`
- variable sorts for introduced result variables.

Side condition:

- `result_clause = subst(parent_clause, substitution)` up to the agreed clause
  representation and alpha-renaming policy.

Megalodon proof:

- universal elimination / proof term application over quantified clause
  variables;
- no search.

Current state:

- `substitute` steps exist.
- The current strict 100-case live gate has metadata for non-identity helper
  substitutes.
- `corepfcheck` has support for explicit instantiation/substitution when
  enough data is present.

Immediate implementation target:

- keep the audit that rejects unmetadataed non-identity `substitute` steps;
- migrate the surface constructor toward a first-class `instantiate`
  primitive emitted by the Vampire primitive builder.

### `rename`

Renames variables without changing logical content.

Fields:

- `id`
- `parent`
- `renaming`
- `result_clause`

Side condition:

- the result is alpha-equivalent to the parent under the exact renaming.

Megalodon proof:

- alpha conversion / context renaming.

Current state:

- Some renaming metadata exists in `kernel_v1`.
- This should become a first-class kernel primitive or be folded into a
  checked alpha-equivalence layer.

### `flip`

Swaps sides of a typed equality literal.

Fields:

- `id`
- `parent`
- `literal_index`
- `result_clause`

Side condition:

- selected literal is typed Megalodon equality;
- result clause is parent with that equality swapped.

Megalodon proof:

- equality symmetry.

Current surface constructor:

- `equality_symmetry`.

### `resolve`

Binary resolution.

Fields:

- `id`
- `left_parent`
- `right_parent`
- `left_pivot_index`
- `right_pivot_index`
- `left_selected_literal`
- `right_selected_literal`
- `result_clause`

Side condition:

- selected literals are complements after any prior `instantiate` steps;
- result is both clauses with pivots removed and remaining literals combined.

Megalodon proof:

- disjunction elimination/case split on the pivot.

Macro expansions:

- unit-resulting resolution becomes a chain of `instantiate`, `flip`, and
  `resolve`.
- hyper-like resolution should lower similarly.

### `factor`

Deletes duplicate literals.

Fields:

- `id`
- `parent`
- `left_literal_index`
- `right_literal_index`
- `result_clause`

Side condition:

- selected literals are identical after prior instantiation;
- result removes one duplicate.

Megalodon proof:

- rebuild disjunction without duplicate branch.

### `equality_resolution`

Removes a negative reflexive equality.

Fields:

- `id`
- `parent`
- `literal_index`
- `result_clause`

Side condition:

- selected literal is negative typed equality `t != t`;
- result removes it.

Megalodon proof:

- contradiction from reflexivity.

### `equality_factoring`

Vampire equality factoring over typed equalities.

Fields:

- `id`
- `parent`
- `selected_index`
- `other_index`
- `selected_side`
- `other_side`
- `substitution` if needed;
- `result_clause`.

Side condition:

- selected and other are positive typed equality literals;
- supplied side terms and substitution produce the Vampire equality factoring
  conclusion.

Megalodon proof:

- typed equality transitivity/symmetry plus disjunction rebuilding.

Current state:

- committed support exists for constrained seed cases.
- all broad cases should be driven by Vampire-emitted side terms and
  substitutions.

### `paramodulate`

Performs one equality replacement at one occurrence.

Fields:

- `id`
- `equality_parent`
- `target_parent`
- `equality_index`
- `target_index`
- `position`
- `from`
- `to`
- `result_clause`

Side condition:

- equality parent selected literal is positive typed equality;
- `from`/`to` match one orientation of that equality;
- position selects an occurrence of `from` inside the target literal;
- result is exactly the target literal with that occurrence replaced, plus
  side literals from both parents.

Megalodon proof:

- equality transport / Leibniz replacement.

Macro expansions:

- superposition lowers to instantiate + flip + paramodulate + factor/rename.
- demodulation lowers to one paramodulate per rewrite occurrence.
- definition rewrite lowers similarly, but may live in preprocessing if it is
  formula-level rather than clause-level.

### `truth_conflict`

Handles explicit `true = false` / FOOL truth contradiction cases over
Megalodon's typed equality.

Fields:

- `id`
- `parent`
- `literal_index`
- `result_clause`

Side condition:

- selected positive literal is a typed equality contradicting the truth
  constants.

Megalodon proof:

- contradiction from distinct truth values or library truth principle.

This rule may eventually move to preprocessing/FOOL if that is cleaner.

### `contradiction`

Marks the empty clause as the final refutation.

Fields:

- `id`
- `parent`

Side condition:

- parent clause is empty.

Megalodon proof:

- parent proof already proves false.

## Macro Expansion Plan

### Unit-resulting resolution

Current issue:

- helper steps like `u459_current_subst0` are non-identity `substitute` steps.
- The previous missing-metadata issue for synthetic-current-clause helpers is
  fixed on the current branch, but the expansion is still implemented as
  local exporter code rather than through a reusable primitive builder.

Target expansion:

```text
current parent
  -> instantiate current parent if needed
  -> instantiate unit parent if needed
  -> flip current or unit equality if needed
  -> resolve
  -> repeat for each unit trace step
  -> rename/factor if needed
```

Required Vampire data:

- current parent id;
- current clause before each trace step;
- selected literal index;
- selected literal after substitution;
- current substitution;
- unit parent id;
- unit substitution;
- unit pivot index;
- result clause after each resolve.

Immediate task:

- move the URR expansion into a reusable Vampire-side primitive-step builder;
- keep the existing metadata audit as a guard against regressions.

### Demodulation and rewrite

Current issue:

- repeated-target rewriting is handled by tracking the target literal index
  through the primitive chain;
- this is correct but still implemented locally in the exporter.

Target expansion:

```text
instantiate equality parent if needed
instantiate target parent if needed
flip equality if rewrite direction requires it
for each rewritten occurrence:
  paramodulate at exact target position
factor/rename if needed
```

Required Vampire data:

- demodulator/equality parent;
- target parent;
- direction;
- occurrence position in the printed Megalodon term shape;
- from/to terms;
- active substitutions for both parents;
- intermediate result clause for each rewrite.

Immediate task:

- move the target-index-aware rewrite expansion onto the shared primitive
  builder;
- add or preserve regression tests for repeated occurrence rewrites.

### Superposition

Target expansion:

```text
instantiate equality parent
instantiate target parent
flip if orientation differs
paramodulate once at exact position
factor/rename if Vampire result differs only by duplicate/order/renaming
```

Required Vampire data:

- equality parent/id/index;
- target parent/id/index;
- selected sides;
- target position;
- unifier/substitution for each parent;
- target literal after substitution;
- result clause.

Implementation note:

- superposition and demodulation should share the same primitive
  paramodulation builder.

### Subsumption resolution

Target expansion:

```text
instantiate side parent
flip side pivot if equality orientation differs
resolve selected main literal against side pivot
check side remainder literals are covered by result
```

Required Vampire data:

- main parent;
- side parent;
- selected main literal/index;
- side pivot/index;
- side substitution;
- side remainder coverage map or explicit remaining side literals.

Current state:

- metadata exists for some side substitutions;
- native proof-term support exists for a bounded binary/unit style.

Next step:

- generalize the native proof-term checker only after Vampire emits explicit
  side remainder data for all needed cases.

### Condensation

Target expansion:

```text
instantiate parent
factor duplicate literals
rename if needed
```

Required Vampire data:

- substitution;
- duplicate literal pairs or a sequence of factor steps;
- result clause after each factor.

Current state:

- there are already local helpers for condensation-like paths.
- this should be folded into the general instantiate/factor primitive builder.

### Equality factoring

Target expansion:

```text
instantiate parent if needed
apply equality_factoring with explicit selected/other sides
factor/rename if needed
```

Required Vampire data:

- selected equality index;
- other equality index;
- selected side;
- other side;
- substitution;
- constraints or side equalities as needed.

Current state:

- typed side terms are now emitted for supported cases;
- native proof-term support exists for seed cases.

### AVATAR

AVATAR should not be part of the clausal kernel.

Target handling:

- either ask Vampire for proofs that avoid AVATAR for the first core gates;
- or define a separate SAT/split certificate layer later.

For the small-kernel milestone, AVATAR is out of scope.

### FOOL, ENNF, CNF, rectification, definitions

These are preprocessing transformations, not clausal kernel rules.

Target handling:

- define a transformation certificate layer with formula-level steps;
- each step produces a `Syntax.pf`;
- the final transformed clauses become `input` assumptions for the clausal
  kernel.

Priority order:

1. set-generated equality/reflexivity facts;
2. conjecture negation;
3. definition unfolding/folding for simple equations;
4. FOOL boolean lifts;
5. ENNF implication/negation steps;
6. CNF conjunction projection and disjunction clauses;
7. rectification;
8. skolemization.

### Skolemization

Skolemization needs its own certificate rule, not ad-hoc name recovery.

Fields should include:

- source formula before skolemization;
- result formula after skolemization;
- existential variable;
- surrounding universal variables / dependencies;
- generated Skolem symbol;
- choice/epsilon term used in Megalodon;
- proof term showing the transformation is classically valid.

Implemented narrow case, 2026-07-17:

- direct source formula `exists X:tp, P X`;
- one introduced nullary Skolem symbol;
- `introduced_0_dependency_count=0`;
- `introduced_0_choice_principle=classical_choice`;
- generated declaration from Vampire metadata is imported into the native
  symbol table;
- Megalodon defines the symbol by the appropriate epsilon operator and proves
  `P sk` by applying the fixed choice theorem to the parent existential proof.

Remaining Megalodon proof work:

- use classical choice/epsilon principle already accepted in Megalodon;
- make dependencies explicit.

The dependent case should generalize the same pattern by abstracting the
surrounding universal variables into the generated Skolem definition, then
applying the appropriate choice theorem under those binders. It should still
be driven by Vampire-emitted source/result formulae, dependency metadata,
sorts, generated declarations, and witness terms; Megalodon should reject any
case where those fields are absent or inconsistent.

This should not block the first small clausal kernel milestone. It is required
for full larger-development reconstruction.

## Migration Plan

### Phase 0: Freeze and classify

Status: partially done.

Actions:

- stop adding broad textual replay cases except correctness fixes;
- classify every certificate step by:
  - kernel primitive;
  - macro that should lower to kernel;
  - preprocessing transformation;
  - source/original-context glue;
  - out of scope for current milestone.

Deliverables:

- committed design document;
- current core whitelist;
- current first-blocker lists from audits.

### Phase 1: Make every current helper substitute explicit

Goal:

- no non-identity `substitute` certificate step without instantiation metadata.

Status: complete for the current strict 100-case live gate; keep as a
regression invariant.

Actions:

- audit all `certificateSubstituteStepSexpr` call sites;
- ensure every emitted non-identity substitute is either:
  - a kernel `instantiate` step; or
  - accompanied by complete `kernel_v1 rule=instantiation` metadata.

Regression gates:

```sh
TMPDIR=/project/tmp \
PROBLEM_DIR=/project/Megalodon/tests/vampire_certificate/closed_cases \
PROBLEMS_FILE=/project/Megalodon/tests/vampire_certificate/source_linked_strict_100.list \
LIMIT=100 JOBS=20 VAMPIRE_SECONDS=10 WALL_SECONDS=15 MIN_PASS=100 \
CHECK_SOURCE_MAP=1 REQUIRE_SOURCE_ORIGIN=1 STRICT_CERT_V1=1 \
AUDIT_NATIVE_PRIMITIVES=1 AUDIT_KERNEL_V1_METADATA=1 \
AUDIT_SUBSTITUTE_METADATA=1 \
WORK_DIR=/project/tmp/live_strict_100_metadata_fix \
tests/vampire_certificate/run_native_live_parallel.sh
```

and focused live reruns for known substitute-heavy examples such as
`hammer.11453.77.th0`.

### Phase 2: Factor a primitive builder in Vampire

Goal:

- replace local string construction with an internal primitive-step builder.

Actions:

- introduce C++ helper records for:
  - rendered clauses;
  - substitutions;
  - selected literals;
  - result clauses;
  - metadata fields;
  - origin macro id.
- make `certificateSubstituteStepPartsSexpr` the model for other primitive
  builders.
- add builders:
  - `makeInstantiateStep`;
  - `makeFlipStep`;
  - `makeResolveStep`;
  - `makeFactorStep`;
  - `makeParamodulateStep`;
  - `makeEqualityResolutionStep`;
  - `makeEqualityFactoringStep`.

Gates:

- existing smoke suite passes;
- generated certificates are byte-stable or semantically equivalent for known
  core fixtures;
- metadata audit passes.

### Phase 3: Move URR and demodulation onto the builder

Goal:

- two frequent macro classes lower through the shared primitive layer.

Actions:

- rewrite URR expansion to emit primitive builder steps;
- rewrite demodulation/rewrite expansion to emit primitive builder steps;
- add self-checks that final primitive result equals Vampire's actual unit
  clause;
- keep original macro id as final substep when useful.

Gates:

- focused `hammer.11453.77.th0` live check passes;
- six-case previous failure set passes;
- metadata audit passes;
- native primitive audit counts instantiate/resolve/paramodulate/factor
  records.

### Phase 4: Make Megalodon `corepfcheck` cover the same primitive kernel

Goal:

- every primitive emitted by the kernel builder has a native `Syntax.pf`
  elaborator.

Actions:

- align certificate parser names with primitive kernel names;
- make `substitute`/`equality_symmetry` either aliases or migrated to
  `instantiate`/`flip`;
- keep unsupported macros out of `corepfcheck`;
- add negative tests for missing metadata and untyped equality.

Gates:

```sh
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_core_pf_audit.sh
```

### Phase 5: Produce first original-context native proofs

Goal:

- at least ten E1 examples:
  original-context, source-bound, closed native proof terms.

Actions:

- choose simple Megalodon theorems after `xm` in the library;
- export THF;
- solve with Vampire at 10s;
- lower proof to primitive certificate;
- import with native proof-term path;
- replace source assumptions by original Megalodon facts;
- prove set-generated equalities by reflexivity where present.

Gates:

- no textual fallback;
- no bridge assumptions;
- no `admit`, `aby`, or incomplete QED;
- `check_propofpf` succeeds;
- source-context checker confirms every input is original, generated
  reflexivity, approved library principle, or conjecture negation.

### Phase 6: Add preprocessing certificate layer

Goal:

- stop treating source-to-clause transformations as opaque inputs.

Actions:

- define formula transformation primitives;
- implement set equality/reflexivity first;
- implement conjecture negation;
- implement simple definition unfolding/folding;
- implement FOOL and ENNF fragments;
- implement CNF projection;
- only then implement skolemization.

Gates:

- each transformation has positive and negative fixtures;
- transformation proofs compose with clausal kernel proofs;
- original-context examples use this layer.

### Phase 7: Fresh 100-case native gate

Goal:

- satisfy the original 100 theorem requirement in the intended architecture.

Actions:

- export a fresh or held-out 100-problem THF suite from Megalodon;
- run Vampire with:

```text
VAMPIRE_SECONDS=10
JOBS=10..20
TMPDIR=/project/tmp
```

- lower every successful Vampire proof to primitive certificates;
- check with Megalodon native proof-term path;
- classify failures by first unsupported primitive/macro/transformation.

Success criteria:

- at least 100 checked proofs;
- no proof holes;
- no broad textual fallback in counted results;
- source/original-context checks enabled;
- committed harness and reproducible problem list.

## Test Strategy

### Unit fixtures

For every primitive:

- one positive fixture;
- one malformed-parent fixture;
- one malformed-result fixture;
- one missing-metadata fixture if metadata is required;
- one untyped-equality negative fixture for equality rules.

### Focused live cases

Maintain small lists under `/project/tmp` or committed test lists for:

- FOOL lift failures;
- demodulation repeated rewrite;
- non-identity substitute metadata;
- equality factoring;
- subsumption side substitution;
- paramodulation into larger target clauses.

Focused runs should not use broad coverage thresholds unless the slice is
expected to cover the relevant primitive.

### Cached regression corpus

Use the committed closed corpus to prevent regressions, but do not treat it as
final success unless it uses the native proof-term path and original-context
source glue.

### Live regenerated gates

Use live regenerated gates for current evidence:

```sh
TMPDIR=/project/tmp \
PROBLEM_DIR=... \
PROBLEMS_FILE=... \
LIMIT=100 \
JOBS=20 \
VAMPIRE_SECONDS=10 \
WALL_SECONDS=15 \
CHECK_SOURCE_MAP=1 \
REQUIRE_SOURCE_ORIGIN=1 \
STRICT_CERT_V1=1 \
AUDIT_NATIVE_PRIMITIVES=1 \
AUDIT_KERNEL_V1_METADATA=1 \
AUDIT_SUBSTITUTE_METADATA=1 \
WORK_DIR=/project/tmp/... \
tests/vampire_certificate/run_native_live_parallel.sh
```

### Scoreboard

Report results by evidence class and test stage:

1. E1: original-context, source-bound, closed native proof terms.
2. E2: exported-THF-bound closed checked proofs.
3. E3: synthetic or live primitive-kernel native proof-term checks.
4. E4: structural certificate/source/metadata validation and transitional
   preprocessing diagnostics.
5. Non-qualifying: anything with admissions, bridges, unsupported source
   assumptions, or textual fallback counted as final proof reconstruction.

Use T0-T4 for test stages, with T4 reserved for original-context checking.

## Concrete Next Tasks

The immediate engineering queue should be:

1. Factor the Vampire primitive builder for instantiate, flip, resolve,
   factor, paramodulate, equality resolution, equality factoring, and
   contradiction.
2. Move URR and demodulation/rewrite expansion onto that builder.
3. Preserve the substitute metadata, native primitive, and core proof-term
   audits as non-negotiable regression gates.
4. Extend the core proof-term frontier only through fixed primitive rules, not
   through broader textual replay.
5. Add the first original-context `corepfcheck` examples after `xm` in the
   library.
6. Implement set-generated equality inputs by reflexivity/definitional
   conversion.
7. Generalize the 2026-07-17 direct Skolem proof-term rule to dependent
   Skolem functions and multiple introductions, still from explicit Vampire
   metadata.
8. Define the remaining preprocessing certificate rules for conjecture
   negation, simple definition unfolding, FOOL/ENNF fragments, and CNF
   projection in the same proof-producing style.

## Alignment Checklist

Before accepting a change as aligned, answer yes to at least one:

- Does it make Vampire emit more exact primitive proof data?
- Does it shrink or replace heuristic replay in Megalodon?
- Does it add native `Syntax.pf` coverage for a fixed primitive?
- Does it strengthen source/original-context checking?
- Does it add a negative test that prevents an unsound certificate from
  passing?
- Does it improve reproducible live/cached testing without changing the trust
  boundary?

Warning signs:

- new Python proof-producing logic;
- new broad OCaml normalization that guesses a missing Vampire choice;
- arity-specific helper lemmas as the main solution;
- accepting a certificate because the generated script happens to check with
  extra assumptions;
- treating exported THF source linkage as original-context proof without
  additional evidence;
- weakening audits to hide missing primitive data.

## Expected End State

The final successful system should look like this:

```text
Megalodon theorem/context
  -> THF export with source map
  -> Vampire proof
  -> Vampire primitive expansion certificate
  -> Megalodon source/preprocess proof terms
  -> Megalodon clausal kernel proof terms
  -> checked proof of original theorem
```

The broad textual emitter may still exist for debugging, but counted success
should come from the native proof-term path.

The project should be considered complete only when:

- at least 100 representative Megalodon theorems are solved from THF by
  Vampire under the agreed timeout;
- their proofs are reconstructed by the primitive certificate path;
- Megalodon checks the resulting native proofs without holes;
- source assumptions are connected to original Megalodon context;
- set-generated equalities are proved, not assumed;
- skolemization and other preprocessing steps are certified where present;
- tests and artifacts are committed or reproducibly generated.

## 2026-07-17 Implementation Update

No `reports/audit-REPORT-2026-07-16.md` file was present in the workspace when
this update was made. The implementation work therefore followed the standing
small-kernel plan above and the cached frontier data.

Committed Megalodon change `c2b11a4` extends the native certificate checker in
the planned direction:

- generated Skolem symbols are no longer treated as original proof variables;
- Vampire's `kernel_v1` Skolem metadata is used to admit metadata-backed
  Skolem steps into the core fragment;
- Skolem definitions are built from explicit dependency metadata and classical
  choice, including dependent Skolem functions;
- the core Skolem proof path now handles universal/disjunctive context around
  an existential and uses the formula-orientation proof builder for equality
  orientation;
- `RectifyFormula` in the core proof path now uses the general formula
  orientation proof builder instead of a variable-only wrapper.

The fast regression gates passed after this change:

- `TMPDIR=/project/tmp ./makeopt`
- `TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh`
- `TMPDIR=/project/tmp VAMPIRE_BIN=/project/tmp/vampire-build-megalodon5/vampire tests/vampire_certificate/run_vampire_skolem_metadata_smoke.sh`
- `TMPDIR=/project/tmp JOBS=10 tests/vampire_certificate/run_native_cert_v1_core_pf_audit.sh`
- `TMPDIR=/project/tmp JOBS=10 MIN_CORE=114 tests/vampire_certificate/run_native_cert_v1_core_closed_audit.sh`
- `TMPDIR=/project/tmp JOBS=10 MIN_REAL_CORE=91 tests/vampire_certificate/run_native_cert_v1_real_core_frontier.sh`

The focused regenerated `hammer.1007.43` certificate now passes the first
metadata-backed Skolem step and the following rectify step, but still fails
later at `u210`, a paramodulation step over an expanded dependent Skolem. The
next work item is to avoid ad hoc expansion in later clausal steps and instead
make the paramodulation/transport primitive handle dependent Skolem definitions
with the correct local de Bruijn context.
