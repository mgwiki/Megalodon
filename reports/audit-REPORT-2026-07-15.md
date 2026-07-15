## Verdict

This is the first report where I would accept the reported results as meaningful closed proof reconstruction—not merely integration success. The worker has substantially repaired the two worst defects from the July 14 audit:

* `-vampirecertv1closed` genuinely rejects bridge and derived premises.
* Source clauses are now structurally compared with their exported THF formulas for the supported fragment, and unsupported source syntax fails closed.

However, the architectural trajectory remains poor. The project is succeeding experimentally while moving further away from the intended small Prover9/Ivy-style proof object. I recommend preserving the current work as a regression oracle, but immediately freezing broad replay development and replacing the central emitter with a small native proof-term elaborator.

## Audit of the report’s claims

The [July 15 report](https://github.com/mgwiki/Megalodon/blob/vampire/megalodon3/reports/REPORT-2026-07-15.md) is unusually candid and mostly accurate.

| Report claim                                                                | Audit result                                                                          |
| --------------------------------------------------------------------------- | ------------------------------------------------------------------------------------- |
| Closed mode rejects non-source premises                                     | Confirmed                                                                             |
| Sources are formula-checked                                                 | Confirmed for the supported THF/TPTP fragment; unsupported syntax is rejected         |
| 157-case closed corpus exists                                               | Confirmed: 157 committed certificate/problem pairs—147 hammer cases and 10 core cases |
| Python is no longer on the qualifying path                                  | Confirmed, although 88,084 lines of legacy Python remain                              |
| Importer is still textual rather than `Syntax.pf`                           | Confirmed                                                                             |
| Original-context reconstruction is incomplete                               | Confirmed                                                                             |
| Architecture is still too Megalodon-heavy                                   | Strongly confirmed                                                                    |
| 95-case source-linked frontier is not a random fresh 100-theorem evaluation | Correctly disclosed                                                                   |

The fresh clones were clean and mutually consistent at Megalodon commit `7d1f6f7` and Vampire commit `77a0538`. The report’s discussion of an uncommitted `FormulaTermInput` experiment concerns the worker’s local environment; that experiment is not present in the auditable branch.

I could not independently execute the corpus because this checkout contains no Megalodon binary and the audit environment lacks the OCaml compiler. Thus, the numerical outcomes remain reported results, but their inputs and harness are now committed and reproducible by someone with the normal build environment.

## What has genuinely improved

### 1. Closed mode is now real

In the current [`vampire_cert_v1.ml`](https://github.com/mgwiki/Megalodon/blob/7d1f6f705261a604a575192c8123f4c5f47d1d5b/src/vampire_cert_v1.ml), ordinary theorem assumptions are introduced only by `Input`, `FormulaInput`, and `FormulaTermInput`. Failed reconstruction paths go into explicit `derived_assumptions` or `bridge_assumptions`.

When `closed=true`, either category causes emission to fail with:

> closed certificate v1 emission requires zero non-source premises

This closes the principal loophole from the previous branch. There are also targeted regression tests showing that substitution bridges and similar fallbacks are rejected.

### 2. The `$true` source-map loophole is fixed

The source map now records the declared formula. Strict/closed validation parses supported THF formulas into `Syntax.tm`-like structures and compares them with the certificate input. A nontrivial certificate premise cannot simply be associated with a `$true` declaration anymore.

Unsupported formulas return an error when formula matching is required, rather than silently succeeding. That is the correct fail-closed policy.

This remains a transitional implementation: it parses exported THF again instead of resolving the original Megalodon `Syntax.tm`. Nevertheless, it is a real semantic improvement.

### 3. Evidence is finally committed

The [`closed_cases` corpus](https://github.com/mgwiki/Megalodon/tree/7d1f6f705261a604a575192c8123f4c5f47d1d5b/tests/vampire_certificate/closed_cases) contains 157 certificate/source pairs. The [closed-corpus harness](https://github.com/mgwiki/Megalodon/blob/7d1f6f705261a604a575192c8123f4c5f47d1d5b/tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh):

* invokes closed mode;
* requires formula-checked source bindings;
* rejects `admit`, `aby`, incomplete proofs, bridges, and derived assumptions;
* checks the emitted proof with Megalodon;
* checks for unindexed axioms.

This is much better evidence than inaccessible `/project/tmp` summaries alone.

### 4. A useful nine-rule core exists

`-vampirecertv1coreclosed` restricts certificates to:

* input;
* substitution;
* resolution;
* subsumption resolution;
* factoring;
* equality resolution;
* equality factoring;
* paramodulation;
* contradiction.

That is reasonably close to the original clausal MVP. Unfortunately, the reported 95/157 frontier is driven by the much broader 42-constructor format, not by this core.

## Main problems

### 1. The architectural growth is still alarming

Between `megalodon2` and `megalodon3`, `src/vampire_cert_v1.ml` grew from approximately 6,663 to 14,774 lines: 8,575 additions and 464 deletions. The whole branch comparison has 91,523 insertions, much of that committed corpus data. See the [Megalodon branch comparison](https://github.com/mgwiki/Megalodon/compare/vampire/megalodon2...vampire/megalodon3).

The module now has 42 certificate-step constructors and simultaneously performs:

* S-expression parsing;
* certificate checking;
* THF parsing;
* source binding;
* normalization;
* type and symbol handling;
* inference reconstruction;
* proof generation;
* proof pretty-printing;
* trust-policy enforcement.

That is not a small proof checker. It is becoming another reconstruction prover—now in OCaml rather than Python.

Switching to OCaml was correct, and the interface already reuses `Syntax.tm`. But there is still no use of `Syntax.pf`; the public result is:

```ocaml
certificate -> string
```

rather than something like:

```ocaml
source_context -> certificate -> Syntax.tm * Syntax.pf
```

The report recognizes this accurately.

### 2. Corpus-driven textual specialization is visible

The proof prelude contains helpers such as:

* `vampire_or_left5_to_right5`;
* `vampire_or_rotate6`;
* `vampire_or_map5_7`;
* `vampire_or_map5_8`;
* `vampire_or_map6_8`;
* `vampire_or_drop_head7`;
* `vampire_or_paramod_suffix7`;
* `vampire_or_rotate_last_first6_extend`;
* `vampire_or_eqsym5_7_set`.

These are not theorem-specific hacks, but they are strong evidence of representation-driven overfitting. A native AST elaborator would recursively construct the appropriate disjunction proof. It would not require a growing catalogue of arity-five-to-eight textual lemmas.

This pattern is precisely how another 60,000-line reconstruction subsystem develops.

### 3. Work is still accumulating on the wrong side

During this iteration:

* Megalodon gained over 8,000 net lines in the central importer.
* Vampire gained only about 165 lines.
* Vampire’s exporter is already roughly 21,529 lines in [`MegalodonChecker.cpp`](https://github.com/JUrban/vampire/blob/77a053854e385fff1744a30ba1c57fba72ad5c85/Shell/MegalodonChecker/MegalodonChecker.cpp).

For Ivy-style architecture, Vampire should expand complicated internal inferences into small primitive steps while it still has occurrence positions, substitutions, selected literals, ordering information, and AVATAR state. Megalodon should check those explicit steps—not rediscover transformations from large before/after formulas.

### 4. “Closed” still depends on a shell-enforced axiom policy

Generated scripts unconditionally declare several axioms, including double-negation elimination and choice principles, plus conditional proposition extensionality.

The corpus harness sensibly uses `-hf` and rejects “not indexed as previously known” warnings. Thus, the reported passes appear closed relative to Megalodon’s indexed logical/library basis.

But the invariant is partly enforced by the shell harness, not by `-vampirecertv1closed` itself. A user can emit a “closed” script and check it differently.

The importer should instead:

* reference known principles by verified hash;
* resolve them from the original context; or
* internally reject every non-source axiom not on an exact approved-hash list.

This is trust-boundary hardening, not evidence that the current corpus is unsound.

### 5. Source linkage is not original-context linkage

The 95 cases establish approximately:

> The certificate refutes assumptions semantically matching the exported THF problem.

They do not yet establish:

> The proof term inhabits the original Megalodon theorem in its original local context.

Definitions, local facts, generated reflexive equalities, conjecture negation, and source hashes still need to be connected directly to the original Megalodon environment.

Therefore the appropriate scoreboard is:

1. Original-context, source-bound, closed proof.
2. Exported-THF-bound closed proof.
3. Synthetic/core closed proof.
4. Integration proof with bridges.

The current report provides substantial Tier 2 evidence and ten synthetic Tier 3 core examples, but apparently zero Tier 1 proofs.

## Recommended decision

Do not terminate or discard the project. The closed harness, source checks, native certificate parser, and 157-case corpus are valuable. But stop approving additional pass-count chasing under the current architecture.

The next iteration should be constrained to:

1. Freeze the broad textual replay engine except for correctness fixes.
2. Preserve it as an oracle/regression implementation.
3. Split out the nine-rule `coreclosed` certificate.
4. Implement that core directly as `Syntax.pf`, reusing Megalodon’s existing term, proof, S-expression, and context machinery.
5. Make Vampire emit exact primitive data rather than asking Megalodon to infer it.
6. Produce ten committed original-context proofs using the native AST path.
7. Run a held-out or freshly regenerated corpus after those ten pass.
8. Add no new Python reconstruction logic; archive the legacy 88,084 lines once diagnostic parity is no longer needed.

My assessment is therefore: **substantial correctness progress, but architectural convergence has not occurred**. The worker’s own final recommendation is right. This branch should become the test oracle for a smaller redesign, not the foundation for another round of thousands of lines of textual replay code.
