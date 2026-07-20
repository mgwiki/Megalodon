## Bottom line

The report is admirably candid, but its own late findings invalidate the headline “28-command” result as qualifying E1 evidence.

The project has made real progress in OCaml source linking and proof-term checking. However, it has recreated the original Python architectural problem in OCaml: a large, stateful reconstruction/search engine has grown around the certificate instead of converging on a small Ivy-style elaborator.

My recommendation is now firmer:

> Stop work on `UnionI`, AVATAR breadth, and new inference coverage. Fix certificate-state isolation first, disable all heuristic fallback in the qualifying mode, and implement a genuinely small deterministic elaborator in separate modules. Do not count the 28-prefix result until it passes with transactionally scoped certificate definitions.

I audited Megalodon at `10c40025` and Vampire at `6f3977d81`. The uncommitted `src/megalodon.ml` experiment described in the report is not present in the current branch, so I exclude it from implemented results.

## Principal findings

| Area                      | Judgment                                                         |
| ------------------------- | ---------------------------------------------------------------- |
| Reporting honesty         | Good: failures, altered contexts and non-E1 tests are disclosed  |
| 28-command prefix         | Strong harness, but currently not sound E1 evidence              |
| Focused `UnionI`          | Useful E3 source-composition experiment, not original-context E1 |
| Source provenance         | Substantially improved, still incomplete                         |
| Hidden `Known` policy     | Better and fail-closed by default                                |
| Python quarantine         | Successful: no new Python reconstruction growth                  |
| Small-kernel architecture | Not implemented                                                  |
| Scope control             | Serious regression                                               |
| 100-theorem objective     | Still remote                                                     |

## 1. The 28-prefix result has been invalidated by hidden certificate state

The harness is substantially better than previous tests. It:

* mechanically replaces 28 actual `aby` commands with `vampire`;
* uses a 10-second Vampire limit;
* rejects `aby`, `admit`, incomplete QED and bridge-like artifacts;
* requires 28 proof files and 28 “reconstructed proof term” messages;
* runs through normal final `Qed`.

That is all good engineering in the [prefix harness](https://github.com/mgwiki/Megalodon/blob/10c40025eacd0996dd6fc6949582273219e7a954/tests/vampire_reconstruction/run_live_hammer_prefix_no_incomplete.sh).

But the committed compact-QED implementation calls `vampire_register_reconstruction_delta_for_qed`, which inserts certificate reconstruction definitions and symbol types directly into the global `sigdelta` and `sigtmof` tables. There is no corresponding scoped rollback in the committed code: [registration implementation](https://github.com/mgwiki/Megalodon/blob/10c40025eacd0996dd6fc6949582273219e7a954/src/megalodon.ml#L1143-L1153), [use in returned-proof handling](https://github.com/mgwiki/Megalodon/blob/10c40025eacd0996dd6fc6949582273219e7a954/src/megalodon.ml#L4368-L4382).

The report’s late refresh then supplies the decisive counterexample: after experimentally clearing that temporary data, `and3I` no longer closes because its previously accepted candidate depended on certificate-local `#sK1`.

That means the passing sequential prefix can depend on certificate definitions that have leaked from reconstruction into the global checking environment. Normal `Qed` checking is not sufficient if the signature supplied to `check_propofpf` has itself been polluted.

Therefore:

* The 28 commands are genuine reconstruction attempts.
* The harness is much stronger than earlier structural tests.
* But they cannot currently be classified as E1.
* The late refresh should supersede the earlier executive-summary wording that calls the prefix the strongest source-development evidence without this qualification.

This is a soundness/isolation defect, not merely a performance problem.

### Required fix

Every `vampire` command needs a transaction:

1. Record the pre-command `sigdelta`, `sigtmof` and related live tables.
2. Install certificate-local definitions only within reconstruction and checking.
3. Check the complete theorem proof.
4. Remove every certificate-local entry in a `finally` path, on success or failure.
5. Retain only the ordinary newly proved theorem after `Qed`.

Add an invariant test:

```text
signature_after_vampire - signature_before_vampire
    = exactly the normal theorem declaration produced by Qed
```

Also test every theorem in a fresh process or add an order-independence regression. A sequential prefix alone is specifically unable to detect this kind of contamination.

## 2. The architectural freeze was not followed

The July 16 design plan explicitly said that qualifying implementation should stop growing `vampire_cert_v1.ml` and move into separate syntax, checker, elaborator and source-context modules: [freeze rule](https://github.com/mgwiki/Megalodon/blob/vampire/megalodon5/reports/VAMPIRE-MEGALODON-DESIGN-PLAN-2026-07-16.md#concrete-freeze-rule).

Since the previous audited Megalodon head `03a1fbef`:

* `src/vampire_cert_v1.ml` gained 18,013 lines and lost 4,216: net **+13,797**.
* It is now **36,088 lines**, up from about 22,291.
* `src/megalodon.ml` gained another **6,076 net lines**.
* `vampire_kernel_syntax.ml` is only 121 lines.
* `vampire_source_context.ml` is 926 lines.
* The planned `vampire_kernel_check.ml` and `vampire_kernel_elab.ml` do not exist.

So the language switch to OCaml happened, but the architectural switch did not. The large Python reconstructor has effectively been replaced by a large OCaml reconstructor plus several thousand lines in Megalodon’s main module.

The qualifying path still contains:

* candidate enumeration;
* constructive goal search;
* source-audit proof search;
* term harvesting and instantiation;
* double-negation/CPS variants;
* proof expansion and alias heuristics;
* multiple fallback orders.

These routines may eventually return a proof that `check_propofpf` accepts, so this is not equivalent to blindly trusting Python. But it is still a new Megalodon-side theorem prover, which was exactly what the Ivy-style reset was intended to avoid. It also explains the difficult performance behaviour: a small unsupported certificate step falls into large combinatorial search.

## 3. Vampire has a better typed boundary, but not yet the promised primitive builder

The Vampire branch has meaningful progress. `MegalodonKernelSyntax.{cpp,hpp}` now supplies typed records and primitive-step construction helpers. But inference-specific extraction, normalization and printing remain extensively embedded in the 26,582-line `MegalodonChecker.cpp`.

Since the July 16 Vampire baseline, `Shell/MegalodonChecker` has approximately:

* 5,614 insertions;
* 937 deletions;
* 29,290 total C++/header lines at the current head.

This is better structured than raw string concatenation, but it is not yet the clean architecture promised by the plan:

```text
Vampire inference
    → primitive proof-object builder
    → single S-expression printer
```

The typed syntax module is a useful seed. It should now become the only route to qualifying output, with the old rich metadata path treated as diagnostic compatibility data.

## 4. `UnionI` is the wrong next architectural milestone

The focused `UnionI` experiment is useful, but it is not E1:

* it uses a temporary file;
* `dneg` is inserted before `UnionI`, unlike the original development;
* detached checking retains a library assumption and conjecture assumption;
* replay takes roughly 49 seconds and final QED another 12 seconds;
* the actual original prefix still times out.

More importantly, `UnionI` exercises FOOL processing, Skolemization, choice, AVATAR, equality and source aliases simultaneously. It is a poor first milestone for proving that a small kernel architecture works.

The next target should be the smallest five original-source proofs whose Vampire proofs use a deliberately restricted calculus. `andEL`, `andER`, simple implication/conjunction results and elementary equality are much better architectural tests. Once those pass without fallback or leaked state, add one transformation case at a time.

## 5. Positive findings worth preserving

Several parts should be retained:

* The Python files did not grow in this interval. Python is no longer on the counted execution path.
* `Vampire_source_context.resolve` now performs substantive proposition/hash checking rather than accepting source labels.
* Missing or mismatched known facts fail in strict mode.
* Certificate-derived `Known` primitives beginning with `vampire_` are rejected by default, apart from a small fixed logical basis. The transitional escape requires an explicit environment variable.
* The report correctly separates E1–E4 and does not count target-stop tests as E1.
* The discovery of the `and3I` hidden dependency is excellent diagnostic work. It should be treated as the pivotal result of this iteration.

## Recommended work order

1. **Fix state isolation.**
   Commit only the transactional QED-scoping part of the experiment. Do not commit unchecked-candidate caps or skip switches as qualifying behaviour.

2. **Make qualifying mode deterministic.**
   It must never call `vampire_constructive_goal_search`, source-audit candidate search, `native_aby_direct`, `megaauto`, or unchecked refutation finishing.

3. **Extract the actual elaborator.**
   Implement:

   * `vampire_kernel_syntax.ml`: minimal parsed certificate types;
   * `vampire_kernel_check.ml`: deterministic clause/substitution checks;
   * `vampire_kernel_elab.ml`: construction of `Syntax.pf`;
   * `vampire_source_context.ml`: live source proof resolution.

   Megalodon’s existing `check_propofpf` remains the authoritative kernel; there is no need to build another general theorem prover.

4. **Freeze both monoliths.**
   No new rule coverage in `vampire_cert_v1.ml` or broad proof-search code in `megalodon.ml`. Prefer net deletion. Treat the old route as a regression oracle.

5. **Establish five clean E1 proofs.**
   For each proof require:

   * exact source site;
   * fresh/scoped certificate state;
   * Vampire ≤10 seconds;
   * zero fallback calls;
   * zero certificate-local symbols after elaboration;
   * every `Known` hash attributable to the live source context or fixed logical basis;
   * normal final QED;
   * reproducible binary commit identity.

6. **Then grow 5 → 10 → 100.**
   Add clausification/Skolem transformation support as a separate Smolka-style layer. Add AVATAR only with explicit SAT/RUP proof objects, or exclude it from the first corpus.

## Overall judgment

I would continue the project, but I would reject this iteration as completion of even the first E1 milestone.

The worker has produced valuable infrastructure and, importantly, found and disclosed a real hidden-state counterexample. But the implementation is again diverging from the intended Prover9/Ivy simplicity. The decisive correction is no longer “fix `UnionI`.” It is:

> Make certificate replay local, deterministic and state-isolated; prove five simple original theorems through that route; and forbid the legacy OCaml search engine from participating in anything counted.
