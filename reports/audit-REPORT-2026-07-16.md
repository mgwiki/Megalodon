## Verdict

The design direction is now substantially better, but I would not approve the current execution plan unchanged. There is a real `Syntax.pf` kernel seed, yet the broader native preprocessing path has recreated the old bridge-assumption problem in a subtler form: it dynamically installs the proposition it wants as a `Known` theorem and then applies it.

So the current state is:

* genuine progress: the small clausal `corepfcheck` path;
* useful integration evidence: the live 100-certificate run;
* non-qualifying evidence: the claimed 94/100 preprocessing proof-term frontier;
* still no original-context reconstruction;
* still rapidly expanding monoliths on both sides.

The plans should continue, but only after a trust-boundary reset and revised milestone order.

## Audit of the report’s principal claims

The [July 16 report](https://github.com/mgwiki/Megalodon/blob/vampire/megalodon4/reports/REPORT-2026-07-16.md) is candid about many limitations, but it overclassifies some evidence.

| Claim                                                     | Assessment                                                                                                     |
| --------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------- |
| A real `Syntax.pf` seed exists                            | Confirmed                                                                                                      |
| 23 core cases pass native proof checking                  | Confirmed, but all 23 are synthetic `core.cnf.*` fixtures                                                      |
| The live 100 run is strong reconstruction evidence        | It is strong certificate-generation and structural-validation evidence, not proof reconstruction               |
| The branch has meaningful Tier 2 evidence                 | Not from the live 100 run as invoked; previous textual closed results may be Tier 2                            |
| The 94/100 preprocessing frontier uses native proof terms | Syntactically yes, but it relies extensively on dynamically trusted `Known` propositions and is non-qualifying |
| Vampire is moving toward primitive expansion              | Partly confirmed, but no separate primitive IR/builder exists yet                                              |
| The broad importer has been frozen                        | Not in practice: it grew by another ~7,400 net lines                                                           |
| Original-context reconstruction remains incomplete        | Confirmed                                                                                                      |
| Python is no longer qualifying                            | Confirmed                                                                                                      |

The current heads I audited are Megalodon `2ecdcdc` and Vampire `f353b28`; both checkouts were clean.

## The good part: `corepfcheck` is genuine progress

`-vampirecertv1corepfcheck` sets strict, closed, core-fragment, and native-proof flags. It:

* requires source and origin metadata;
* performs semantic source-formula checks;
* accepts only the core whitelist;
* constructs actual `Syntax.pf` values;
* checks each step with `check_propofpf`;
* constructs a final implication from its source assumptions to `False`;
* performs another closed proof-term check in an empty proof context.

This is materially different from the textual emitter and is the right architectural seed. The implementation is visible in [`vampire_cert_v1.ml`](https://github.com/mgwiki/Megalodon/blob/2ecdcdcd786dc4f7d3e8a40ec6908c4d241fe48b/src/vampire_cert_v1.ml).

Its approved logical basis is also much better controlled than the old generated-script prelude: the native core explicitly installs a small fixed collection including proposition extensionality, double-negation elimination, and several typed not-forall/existence principles.

The 23 eligible corpus cases exercise:

* resolution: 23 cases;
* factor: 5;
* paramodulation: 4;
* equality symmetry: 3;
* subsumption resolution: 3;
* equality resolution: 1;
* substitution: 1.

Equality factoring has a focused smoke fixture but is not represented in the 23-case corpus.

The limitation is that all 23 are synthetic `core.cnf.*` examples. No real live hammer proof currently passes the complete `corepfcheck` gate. Thus this is credible Tier 3 evidence, not evidence that the small kernel yet handles real exported proofs.

## Critical defect: `preprocesspfcheck` injects arbitrary known theorems

The new `elaborate_preprocess_refutation_native` path frequently does this:

1. Constructs the proposition that would justify a transformation.
2. Creates a name such as `vampire_rectify_formula_u123`.
3. Inserts that name and proposition into `proof_delta`.
4. Returns `Known "vampire_rectify_formula_u123"`.
5. Merges that table into the proof-checker environment.
6. Reports that the resulting `Syntax.pf` checked.

This occurs for, among others:

* predicate definitions and folds;
* rectification;
* FOOL formula transformations;
* ENNF;
* Skolemization;
* CNF projection following transitional transformations;
* AVATAR components, splits, definitions, and refutations;
* some substitution, resolution, factor, equality-resolution, equality-symmetry, and paramodulation steps whose parents are already “transitional.”

For example, the code effectively constructs:

```ocaml
let primitive_prop = Imp (parent_prop, result_prop) in
Hashtbl.replace proof_delta primitive (0, primitive_prop);
...
PPfAp (Known primitive, parent_proof)
```

`check_propofpf` then succeeds because the desired implication has just been declared known.

That is not proof reconstruction. It is equivalent to introducing a bridge axiom, except that the assumption is hidden inside the dynamically extended known-theorem table rather than appearing as an `assume bridge_*` line.

The [implementation design](https://github.com/mgwiki/Megalodon/blob/vampire/megalodon4/reports/VAMPIRE-MEGALODON-IMPLEMENTATION-DESIGN-2026-07-16.md) says the native preprocessing frontier is 94/100. That number must be reclassified as:

> 94/100 structural/native-AST plumbing checks with transitional trusted primitives.

It must not be counted as native proof-term reconstruction. The design documents say “no unsupported axiom injection”; the implementation currently violates that principle.

This is the most important correction for the next report.

## The live `PASS 100` is also misclassified

The reported command uses:

```text
STRICT_CERT_V1=1
```

In [`run_native_live_parallel.sh`](https://github.com/mgwiki/Megalodon/blob/2ecdcdcd786dc4f7d3e8a40ec6908c4d241fe48b/tests/vampire_certificate/run_native_live_parallel.sh), that becomes:

```text
-vampirecertv1strict
```

The harness does not invoke:

* `-vampirecertv1closed`;
* `-vampirecertv1emit`;
* `-vampirecertv1corepfcheck`; or
* `-vampirecertv1preprocesspfcheck`.

It runs Vampire, extracts a certificate, structurally validates it, validates source mappings and metadata, and reports `PASS`.

That is valuable. It proves that Vampire can regenerate 100 certificates in the timeout and that Megalodon accepts their structure, sources, and audited metadata. But it does not prove the certificates’ inferences by either textual or native proof terms.

Therefore the small-kernel plan’s statement that this is “Tier 2 … closed certificate checking” is incorrect. It is not closed mode and is not a checked proof. Under the report’s own evidence scoreboard, it belongs in the integration tier.

The report itself later calls it “strong integration evidence,” which is the accurate description.

## Code growth shows the pivot has not happened yet

Since `megalodon3`:

* `src/vampire_cert_v1.ml` grew from 14,774 to 22,216 lines—about 7,442 net new lines.
* The step datatype grew from 42 to 45 constructors.
* `MegalodonChecker.cpp` grew from 21,529 to 24,426 lines—about 2,897 net new lines.
* The Megalodon branch contains 181 intervening commits.
* The Vampire branch contains 69.
* The four report/design documents total 3,629 lines.

See the [Megalodon comparison](https://github.com/mgwiki/Megalodon/compare/vampire/megalodon3...vampire/megalodon4) and [Vampire comparison](https://github.com/JUrban/vampire/compare/vampire/megalodon3...vampire/megalodon4).

Moving proof detail into Vampire is directionally correct, so some C++ growth is expected. But no `MegalodonKernelStep` or equivalent isolated primitive IR exists yet. Everything is still embedded in the 24,000-line exporter.

Likewise, the new native OCaml work was added inside the same 22,000-line module as the parser, structural checker, textual prover, THF parser, preprocessing reconstruction, and trust policy.

The plans describe a refactor; the branch still shows extension of the old system.

## Review of the three design plans

The [small-kernel plan](https://github.com/mgwiki/Megalodon/blob/vampire/megalodon4/reports/VAMPIRE-MEGALODON-SMALL-KERNEL-PLAN-2026-07-16.md) has the right high-level separation:

1. source/preprocessing proof;
2. Vampire-side macro expansion;
3. small clausal kernel;
4. original-context composition.

It also correctly puts AVATAR outside the first kernel milestone and correctly demands exact substitutions, literal indices, rewrite positions, directions, and variable sorts.

The proposed kernel is reasonable:

* input;
* instantiate;
* rename;
* flip;
* resolve;
* factor;
* equality resolution;
* equality factoring;
* paramodulation;
* truth conflict;
* contradiction.

I would simplify its conceptual presentation:

* `input` is a boundary from preprocessing, not an inference.
* `rename` should preferably be checked alpha-conversion rather than a logical kernel rule.
* `contradiction` is merely a final marker for an already empty clause.
* `truth_conflict` should probably live in the FOOL/preprocessing layer unless real clausal proofs demonstrate that it belongs in the stable kernel.

That leaves a very plausible seven- or eight-rule logical core.

### Problems in the plans

#### 1. Milestones are ordered incorrectly

The implementation design proposes first taking the preprocessing frontier from 94/100 to 100/100 and only afterward replacing transitional metadata with real primitives.

Given the dynamic-`Known` issue, this is backwards. Pursuing 100/100 now will reward further propagation of trusted synthetic primitives.

The first milestone must be:

> Eliminate all certificate-derived `Known` declarations from the counted native path.

Only then should preprocessing pass counts resume.

#### 2. “Original context” remains underspecified

All three plans mention:

```ocaml
source_context -> certificate -> Syntax.tm * Syntax.pf
```

but none defines `source_context` concretely or explains the lifecycle of local hypotheses across the external Vampire round trip.

The design needs an actual type resembling:

```ocaml
type source_proof =
  | GlobalKnown of hash * Syntax.tm
  | LocalHyp of int * Syntax.tm
  | Definitional of Syntax.tm * Syntax.pf
  | Generated of Syntax.tm * Syntax.pf

type source_context = source_id -> source_proof
```

It must specify:

* how global theorem hashes are resolved;
* how local `Hyp` indices survive export/import;
* how binder scopes are represented;
* how definitions are supplied to conversion;
* how the negated conjecture refutation is converted into the original goal;
* whether reconstruction happens inside the exporting Megalodon process or through a serialized context sidecar.

Without that, the Tier 1 milestone is still aspirational.

#### 3. The plans lack an enforceable monolith freeze

They repeatedly say “freeze” and “shrink,” but contain no measurable rule preventing another 7,000-line increment.

I recommend:

* no new qualifying implementation in `vampire_cert_v1.ml`;
* place the new work in separate `vampire_kernel_syntax.ml`, `vampire_kernel_check.ml`, `vampire_kernel_elab.ml`, and `vampire_source_context.ml`;
* freeze the textual emitter except correctness/security fixes;
* prohibit dependencies from the kernel elaborator into textual replay functions;
* factor the Vampire primitive builder and printer out of `MegalodonChecker.cpp`.

#### 4. Tier terminology is inconsistent

The report’s evidence tiers call original-context proof “Tier 1.” The execution plan’s testing tiers call original-context testing “Tier 4.”

Both systems are individually understandable, but using the same word “Tier” with opposite ordering is asking for future misreporting. Use:

* evidence classes: E1–E4;
* test stages: T0–T4.

## Required trust invariants

Before more pass-count work, add mechanically enforced invariants:

1. Every `Known h` in a qualifying proof must resolve to either:

   * a theorem already present in the original Megalodon context;
   * an exact reviewed logical-basis hash; or
   * a separately checked conservative definition.

2. No theorem name or theorem proposition may be added to `sgdelta` based on a certificate step ID.

3. The final proof should be traversed and its `Known` provenance audited.

4. “Definitions” must be distinguished from “known propositions.” A conservative term definition may extend delta; an arbitrary implication cannot.

5. `preprocesspfcheck` should fail on unsupported transformations, not install a transitional known.

Until then, rename its successes to something like `PREPROCESS_STRUCTURAL_PASS`, not `PREPROCESS_PF_PASS`.

## Recommended revised execution order

1. **Trust reset**

   Remove dynamic `Known` injection from the counted preprocessing mode. Reclassify the 94/100 and strict 100 results.

2. **Isolated clausal kernel**

   Move the genuine `corepfcheck` implementation into new modules. Preserve the 22,000-line file only as the legacy oracle.

3. **Real Vampire primitive IR**

   Introduce an internal typed `MegalodonKernelStep` list and a single printer. Make URR the first macro lowered through it.

4. **Real-case core gate**

   Obtain at least ten live, regenerated Vampire proofs containing only the primitive kernel. The existing 23 synthetic fixtures are not enough.

5. **Concrete original-context API**

   Implement `GlobalKnown`, `LocalHyp`, definitional, and generated-source proof bindings. Produce ten original-context theorems.

6. **Certified preprocessing**

   Add rectification, FOOL, ENNF, CNF and Skolemization one at a time, with actual proof terms—not dynamic knowns.

7. **Held-out evaluation**

   Only after the above, run the fresh 100-theorem original-context gate.

## Bottom line

I approve the architectural intent of the plans, especially the decision to expand macros in Vampire and use native `Syntax.pf` in Megalodon. I do not approve the current evidence classification or milestone order.

The project has one genuinely promising result: the small synthetic `corepfcheck` kernel. It should now be extracted, isolated and applied to real Vampire proofs. The 100 strict certificates are useful integration data, while the 94 preprocessing proof terms are currently non-qualifying because they depend on dynamically injected known theorems.

The next worker report should lead with removal of that trust loophole—not with 100/100 preprocessing passes.
