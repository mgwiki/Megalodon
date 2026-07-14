# Response to `audit-REPORT-2026-07-14.md`

Date: 2026-07-14

The audit is correct on the main point. The previous branch had useful native
OCaml integration evidence, but the word "strict" was overloaded. It meant
certificate/source-map structure validation, not closed proof reconstruction.
Generated scripts could still pass Megalodon while relying on bridge premises or
other derived theorem assumptions.

This branch starts the requested architectural reset.

## Implemented Here

- Added `-vampirecertv1closed`.
- Closed mode implies strict certificate checking.
- Closed mode fails emission if any bridge premise would be added.
- Closed mode also fails if any non-bridge derived premise would be added, such
  as FOOL theory exhaustiveness, FOOL distinctness, predicate definitions,
  definition inputs, AVATAR components/refutations, or the current
  `vampire_eq_prop_ext` helper premise.
- The cached emit harness now supports `CLOSED_CERT_V1=1`.
- Closed harness successes are reported as `CLOSED_PASS`, not `PASS`.
- The native smoke suite now has closed positive and negative coverage.
- README language now distinguishes ordinary integration `PASS` from qualifying
  closed `CLOSED_PASS`.
- Source-map parsing now records the raw THF declaration formula for each mapped
  source name.
- Hashed global source entries whose THF declaration is `$true` are rejected
  unless the certificate input is actually true. This turns the audit's concrete
  "`p \/ q` attached to `$true`" example into a negative smoke test.
- Hashed global source entries with simple first-order THF clauses are now
  compared against the certificate source input clause. This is deliberately
  narrow: it handles atoms, negation, disjunction, and equality, and leaves
  richer THF syntax for the later canonical `Syntax.tm` binding. The smoke suite
  now rejects a certificate clause `(p \/ q)` mapped to a THF declaration
  `(p \/ r)`.
- Source-map validation now also parses a larger emitted-THF fragment for hashed
  global source entries: typed `!`/`?` binders, `=>`, `&`, `|`, `~`, equality,
  `@` application, and THF lambda terms. Parsed THF source formulas are compared
  to the native Vampire certificate terms, modulo equality symmetry, and THF
  lambdas are mapped to the same `vLAM` representation used by Vampire's native
  certificate output. The smoke suite now includes formula-backed known inputs
  and a quantified formula mismatch.

Validation performed on this branch:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh

PASS 213
/project/tmp/source_linked_slice_1_400_emit_closed_mode_regression_093857

CLOSED_PASS 1
/project/tmp/closed_mode_smoke_emit_093949

PASS 213
/project/tmp/source_linked_slice_1_400_emit_source_true_guard_094615

CLOSED_PASS 1
/project/tmp/closed_mode_source_true_emit_094705

PASS 213
/project/tmp/source_linked_slice_1_400_emit_source_formula_guard_095205

CLOSED_PASS 1
/project/tmp/closed_mode_source_formula_emit_095258/work

PASS 213
/project/tmp/source_linked_slice_1_400_emit_thf_formula_lam_guard_100234

CLOSED_PASS 1
/project/tmp/closed_mode_thf_formula_lam_emit_100319/work
```

The 213-case run is still ordinary strict integration evidence, not a closed
proof result. Its bridge profile remains:

```text
bridge_total 5669
1477 cnf
841 paramodulate
708 resolve
619 substitute
508 normal_form
353 rectify_formula
338 skolem_formula
237 fool
211 formula_term_copy
135 equality_symmetry
78 predicate_definition_fold
69 equality_resolution
46 factor
28 condensation
15 predicate_definition_fold_chain
2 inequality_name_intro
2 inequality_split
1 definition_rewrite
1 equality_factoring
```

Closed-mode frontier measurement on the same cached source-linked corpus:

```text
CLOSED_PASS 2
EMIT_FAIL 211
/project/tmp/source_linked_slice_1_400_closed_frontier_100422
```

The two current cached closed passes are:

```text
hammer.10823.92.th0.p
hammer.11560.31.th0.p
```

The first blockers in the failed cases are concentrated in the expected
non-closed classes: `vampire_eq_prop_ext`, FOOL/normal-form/CNF/skolem bridges,
AVATAR component/refutation assumptions, predicate-definition assumptions, and
definition-input assumptions.

Additional source-linking work on `vampire/megalodon3` now records the original
Megalodon obligation location in exported THF problems. `-createabyprobs` emits
a `% megalodon_origin` comment with source file, line, character, and obligation
kind; the native certificate source parser preserves this metadata; and the
simple proof emitter writes it into the generated Megalodon reconstruction file.
This is not yet full context replay, but it gives every generated proof artifact
a machine-checkable anchor back to the exact original development site rather
than only to the generated THF filename.

Validation for this provenance change:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_source_map_export_smoke.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh

PASS 213
/project/tmp/source_linked_slice_1_400_emit_origin_metadata_101311
```

The parallel harnesses now also have a `REQUIRE_SOURCE_ORIGIN=1` gate. Fresh
source-linked corpus runs enable it by default, so origin metadata cannot
silently disappear between export, Vampire proof generation, and cached
Megalodon emit/check replay. A small fresh validation run exercised both stages:

```text
PASS 1
TIMEOUT 4
/project/tmp/source_origin_gate_live_101553

PASS 1
/project/tmp/source_origin_gate_emit_retry_101639
```

The emitted Megalodon proof artifacts now also contain machine-readable
`vampire_source_assumption` comments for every original source premise. Each
binding records the generated theorem parameter, certificate step, certificate
source kind, TPTP source name, original Megalodon source name, source-map kind,
source hash, and rendered proposition. This still does not discharge the
premises inside the original context, but it removes another hidden naming step:
the next replay stage can tell exactly which theorem parameter is supposed to be
filled by which original lemma, local fact, conjecture edge, definition, or
set-reflexivity fact.

Validation for source-assumption bindings:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_source_map_export_smoke.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh

PASS 213
/project/tmp/source_linked_slice_1_400_emit_source_bindings_101934
```

This branch now also discharges one real closed blocker class instead of only
classifying it. Vampire `function_definition` metadata for first-order
`set`-sorted introduced symbols is used to emit a Megalodon `Definition` for
the introduced symbol, and the corresponding `definition_input` equality is
emitted as a checked `claim` proved by `reflexivity` rather than as a theorem
premise. The implementation is deliberately guarded: if the native definition
mentions Vampire `db*` aliases or is not an orientable first-order `set`
definition, it remains a non-source premise and closed mode rejects the case.
That is intentional; scoped Smolka-style transformations still need a real
replay path.

Validation for the guarded function-definition path:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_source_map_export_smoke.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh

PASS 213
/project/tmp/source_linked_slice_1_400_emit_definput_guarded_102853

CLOSED_PASS 6
EMIT_FAIL 207
/project/tmp/source_linked_slice_1_400_closed_definput_guarded_102927
```

The additional closed cases are:

```text
hammer.11555.42.th0.p
hammer.11572.88.th0.p
hammer.11578.57.th0.p
hammer.11706.270.th0.p
```

Closed source-linking is now stricter than ordinary source-map diagnostics. If
a hashed original THF formula is outside the checked source-linking fragment,
ordinary `-vampirecertv1source` still accepts the case for corpus inspection,
but `-vampirecertv1closed` rejects it before emission. This prevents a
zero-bridge script from being counted when the source proposition was only
label-linked. The smoke suite contains an explicit negative case using a THF
connective outside the current parser.

Validation for the closed-only unsupported-source rejection:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_source_map_export_smoke.sh

CLOSED_PASS 6
EMIT_FAIL 207
/project/tmp/source_linked_slice_1_400_closed_source_strict_104208
```

The guarded `definition_input` replay now also covers introduced symbols whose
type is a `set`-only arrow sort, such as `set->set`. The emitter turns these
fresh symbols into Megalodon `Definition`s and proves the corresponding Vampire
Leibniz function equality by the identity proof after unfolding. This is still
guarded against de-Bruijn aliases and non-`set` arrow types.

Validation for arrow-valued function definitions:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_source_map_export_smoke.sh

PASS 213
/project/tmp/source_linked_slice_1_400_emit_arrow_def_104840

CLOSED_PASS 7
EMIT_FAIL 206
/project/tmp/source_linked_slice_1_400_closed_arrow_def_104829
```

The new closed case is:

```text
hammer.11203.25.th0.p
```

The current seven real closed cases are now committed under
`tests/vampire_certificate/closed_cases/`, together with
`tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh`. This is still
short of the requested 10-case milestone, but the existing frontier is no longer
only a `/project/tmp` artifact.

Validation for the committed closed corpus:

```text
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh

CLOSED_PASS 7
/project/tmp/native_cert_v1_closed_corpus.e5Xqkc
```

The committed closed corpus now also carries explicit source-origin metadata
for each case, pointing back to the original `examples/hammer/100thms_12_h.mg`
obligation location. The closed-corpus harness rejects committed cases with no
`% megalodon_origin` line, rejects emitted Megalodon files that do not preserve
that origin as a `// Vampire certificate source origin:` comment, and rejects
emitted files without machine-readable `// vampire_source_assumption` bindings.
This is still not full original-context replay, but it prevents the reproducible
closed corpus from regressing to anonymous THF-only artifacts.

Validation for the provenance-gated committed corpus:

```text
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh

CLOSED_PASS 7
/project/tmp/native_cert_v1_closed_corpus.iiXKls

TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh
native certificate v1 smoke test passed

TMPDIR=/project/tmp tests/vampire_certificate/run_source_map_export_smoke.sh
Megalodon TH0 source-map export smoke passed
```

I also tried to regenerate these seven origin-enabled certificates live with
`/project/vampire-leancheck/vampire_rel_vampire/megalodon_10835`, seven-way
parallelism, and the required 10s Vampire cap. That run produced six `NO_CERT`
results and one timeout, so I did not replace the committed certificates with
new ones. The current committed corpus should be treated as fixed reproducible
certificate fixtures until Vampire-side deterministic regeneration is repaired
or a current build reproduces them under the agreed limits.

The branch now also closes the small FOOL Boolean-lifting class that previously
blocked cases such as `hammer.1032.16`. The generated proof prelude defines
`vampire_eq_prop` as Megalodon's equality on `prop`, emits the library-shaped
`prop_ext` axiom before problem-local symbols, and checks generated scripts with
`-hf` so that this axiom is trusted by the indexed HF hash rather than by a local
unindexed assumption. The FOOL replay then proves `A -> A = True` and extracts
`A` from `A = True` using ordinary Megalodon equality eliminators.

This is a real closed-proof improvement, not a bridge-count-only change. The
cached source-linked closed replay over the first 213 previously solvable
certificates moved from 7 to 11 closed passes:

```text
TMPDIR=/project/tmp \
PROBLEM_DIR=/project/tmp/source_linked_strict_100_corpus_fresh_041947 \
WORK_DIR=/project/tmp/source_linked_slice_1_400_closed_fool_prop_ext_111720 \
JOBS=20 MIN_PASS=0 CLOSED_CERT_V1=1 EMIT_TIMEOUT=30 CHECK_TIMEOUT=45 \
tests/vampire_certificate/run_native_emit_cached_parallel.sh \
  /project/tmp/source_linked_slice_1_400_fresh_042040

CLOSED_PASS 11
EMIT_FAIL 202
/project/tmp/source_linked_slice_1_400_closed_fool_prop_ext_111720
```

The four new closed cases are committed in the closed corpus:

```text
hammer.1032.16.th0.p
hammer.1049.20.th0.p
hammer.10809.92.th0.p
hammer.11696.239.th0.p
```

Validation for the 11-case committed corpus and smoke gates:

```text
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh
CLOSED_PASS 11
/project/tmp/native_cert_v1_closed_corpus.B8KYWJ

TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh
native certificate v1 smoke test passed

TMPDIR=/project/tmp tests/vampire_certificate/run_source_map_export_smoke.sh
Megalodon TH0 source-map export smoke passed
```

The next increment on `vampire/megalodon3` closes a larger, frequent
FOOL/ENNF/CNF class. The generated prelude now uses the indexed classical
`dneg` axiom to derive `vampire_xm`, replays Vampire
`fool_exhaustiveness` by case analysis, replays the common ENNF
`A -> B` to `~A \/ B` transformation, normalizes `vampire_or`/`\/` and
`vampire_false`/`False` for CNF identity projections, and fixes
prop-sort paramodulation/truth-conflict proof terms to use Megalodon's binary
equality eliminator.

This moved the cached source-linked closed frontier from 11 to 42 closed
passes:

```text
TMPDIR=/project/tmp \
PROBLEM_DIR=/project/tmp/source_linked_strict_100_corpus_fresh_041947 \
WORK_DIR=/project/tmp/source_linked_slice_1_400_closed_ennf_fool_114054 \
JOBS=20 MIN_PASS=0 CLOSED_CERT_V1=1 EMIT_TIMEOUT=30 CHECK_TIMEOUT=45 \
tests/vampire_certificate/run_native_emit_cached_parallel.sh \
  /project/tmp/source_linked_slice_1_400_fresh_042040

CLOSED_PASS 42
EMIT_FAIL 171
/project/tmp/source_linked_slice_1_400_closed_ennf_fool_114054
```

The committed closed corpus has been promoted to all 42 current closed passes.
The added cases retain `% megalodon_origin` links back to
`examples/hammer/100thms_12_h.mg`.

Validation for this increment:

```text
TMPDIR=/project/tmp ./makeopt

TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh
native certificate v1 smoke test passed
/project/tmp/native_cert_v1.oEKExp

TMPDIR=/project/tmp tests/vampire_certificate/run_source_map_export_smoke.sh
Megalodon TH0 source-map export smoke passed

TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh
CLOSED_PASS 42
/project/tmp/native_cert_v1_closed_corpus.4W9xr6
```

## July 14 Increment: Prop-Valued Definition Inputs

The native emitter now treats Vampire `definition_input` steps with
`function_definition` metadata as checked Megalodon definitions even when the
introduced symbol has a proposition-valued sort such as `set->prop` or `prop`.
Previously only all-set function definitions were converted to definitions, so
some cases still carried `derived:definition_input` assumptions. These are now
emitted as definitions plus reflexivity-style equality proofs.

This moved the cached source-linked closed frontier from 42 to 45 closed
passes:

```text
TMPDIR=/project/tmp \
PROBLEM_DIR=/project/tmp/source_linked_strict_100_corpus_fresh_041947 \
WORK_DIR=/project/tmp/source_linked_slice_1_400_closed_definput_final_121351 \
JOBS=20 MIN_PASS=0 CLOSED_CERT_V1=1 EMIT_TIMEOUT=30 CHECK_TIMEOUT=45 \
tests/vampire_certificate/run_native_emit_cached_parallel.sh \
  /project/tmp/source_linked_slice_1_400_fresh_042040

CLOSED_PASS 45
EMIT_FAIL 168
/project/tmp/source_linked_slice_1_400_closed_definput_final_121351
```

The three new committed closed cases are:

```text
hammer.11577.51.th0.p
hammer.11669.25.th0.p
hammer.11671.25.th0.p
```

Validation for this increment:

```text
TMPDIR=/project/tmp ./makeopt

TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh
native certificate v1 smoke test passed
/project/tmp/native_cert_v1.NMdhO6

TMPDIR=/project/tmp tests/vampire_certificate/run_source_map_export_smoke.sh
Megalodon TH0 source-map export smoke passed

TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh
CLOSED_PASS 45
/project/tmp/native_cert_v1_closed_corpus.tZAxBx
```

## July 14 Increment: Negated Implication ENNF

The native emitter now replays the common ENNF transformation
`~(A -> B)` to `A /\ ~B`.  The proof term is direct and classical: it derives
`A` by `dneg` using the parent contradiction, and derives `B -> False` by
feeding a constant `A -> B` proof back to the parent contradiction.  Universal
binders continue to be handled by the existing ENNF binder recursion.

This moved the cached source-linked closed frontier from 45 to 47 closed
passes:

```text
TMPDIR=/project/tmp \
PROBLEM_DIR=/project/tmp/source_linked_strict_100_corpus_fresh_041947 \
WORK_DIR=/project/tmp/source_linked_slice_1_400_closed_ennf_neg_imp_121949 \
JOBS=20 MIN_PASS=0 CLOSED_CERT_V1=1 EMIT_TIMEOUT=30 CHECK_TIMEOUT=45 \
tests/vampire_certificate/run_native_emit_cached_parallel.sh \
  /project/tmp/source_linked_slice_1_400_fresh_042040

CLOSED_PASS 47
EMIT_FAIL 166
/project/tmp/source_linked_slice_1_400_closed_ennf_neg_imp_121949
```

The two new committed closed cases are:

```text
hammer.10497.10.th0.p
hammer.10587.10.th0.p
```

Validation for this increment:

```text
TMPDIR=/project/tmp ./makeopt

TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh
native certificate v1 smoke test passed
/project/tmp/native_cert_v1.UI7WfV

TMPDIR=/project/tmp tests/vampire_certificate/run_source_map_export_smoke.sh
Megalodon TH0 source-map export smoke passed

TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh
CLOSED_PASS 47
/project/tmp/native_cert_v1_closed_corpus.FBArvw
```

## July 14 Increment: Nested ENNF and CNF Clause Projection

The ENNF implication-to-or replay now uses fresh hypothesis names at each
recursive implication step. This fixes nested implications where the previous
generated proof could accidentally reuse the inner positive hypothesis for both
premises.

The native emitter also treats a `formula_term_copy` whose native formula AST is
unchanged as an exact proof copy, even when Vampire's metadata pretty-prints an
associated variant. CNF formula-clause replay can now project and permute a
single disjunctive source clause with the existing Megalodon disjunction
eliminator instead of requiring an identical rendered clause order.

This moved the cached source-linked closed frontier from 47 to 60 closed
passes:

```text
TMPDIR=/project/tmp \
PROBLEM_DIR=/project/tmp/source_linked_strict_100_corpus_fresh_041947 \
WORK_DIR=/project/tmp/source_linked_slice_1_400_closed_cnf_or_projection_122448 \
JOBS=20 MIN_PASS=0 CLOSED_CERT_V1=1 EMIT_TIMEOUT=30 CHECK_TIMEOUT=45 \
tests/vampire_certificate/run_native_emit_cached_parallel.sh \
  /project/tmp/source_linked_slice_1_400_fresh_042040

CLOSED_PASS 60
EMIT_FAIL 153
/project/tmp/source_linked_slice_1_400_closed_cnf_or_projection_122448
```

The thirteen new committed closed cases are:

```text
hammer.10455.26.th0.p
hammer.10546.26.th0.p
hammer.10791.28.th0.p
hammer.10988.26.th0.p
hammer.10995.40.th0.p
hammer.11281.32.th0.p
hammer.11287.64.th0.p
hammer.11531.26.th0.p
hammer.11703.242.th0.p
hammer.11808.21.th0.p
hammer.11810.25.th0.p
hammer.11849.21.th0.p
hammer.11851.25.th0.p
```

Validation for this increment:

```text
TMPDIR=/project/tmp ./makeopt

TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh
native certificate v1 smoke test passed
/project/tmp/native_cert_v1.yyHqq4

TMPDIR=/project/tmp tests/vampire_certificate/run_source_map_export_smoke.sh
Megalodon TH0 source-map export smoke passed

TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh
CLOSED_PASS 60
/project/tmp/native_cert_v1_closed_corpus.wPRsO6
```

## July 14 Increment: Nested Forall CNF Projection

The native emitter now handles the next CNF projection shape where Vampire's
ENNF target contains nested universal binders under the right side of an
implication-to-disjunction transformation. The ENNF target-text renderer can
print nested `forall` formulas when they occur inside generated disjunction
branches, and CNF clause projection now applies only the source formula's
prefix universal binders before recursively instantiating nested binders under
`vampire_or`.

This is still a guarded replay for a simple, single-clause projection class; it
does not attempt a general Smolka/CNF proof object yet. It does remove one more
bridge assumption from a real cached Vampire proof.

The cached source-linked closed frontier moved from 60 to 61 closed passes:

```text
TMPDIR=/project/tmp \
PROBLEM_DIR=/project/tmp/source_linked_strict_100_corpus_fresh_041947 \
WORK_DIR=/project/tmp/source_linked_slice_1_400_closed_nested_forall_cnf_final_123524 \
JOBS=20 MIN_PASS=0 CLOSED_CERT_V1=1 EMIT_TIMEOUT=30 CHECK_TIMEOUT=45 \
tests/vampire_certificate/run_native_emit_cached_parallel.sh \
  /project/tmp/source_linked_slice_1_400_fresh_042040

CLOSED_PASS 61
EMIT_FAIL 151
CHECK_FAIL 1
/project/tmp/source_linked_slice_1_400_closed_nested_forall_cnf_final_123524
```

The new committed closed case is:

```text
hammer.10795.33.th0.p
```

Validation for this increment:

```text
TMPDIR=/project/tmp ./makeopt

TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh
native certificate v1 smoke test passed
/project/tmp/native_cert_v1.1a8CTl

TMPDIR=/project/tmp tests/vampire_certificate/run_source_map_export_smoke.sh
Megalodon TH0 source-map export smoke passed

TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh
CLOSED_PASS 61
/project/tmp/native_cert_v1_closed_corpus.3iMfeo
```

## July 14 Increment: CNF Nested Binder Discipline

The recursive CNF clause projection replay now tracks which universal binders
have already been applied from the source formula prefix. When a remaining
nested `forall` occurs under a disjunction branch, the emitter chooses a fresh
target binder of the right sort that occurs in that nested body, rather than
accidentally reusing an outer binder that also appears in the body.

This fixes a generated proof-term error in `hammer.11523.29.th0.p`, where the
previous replay instantiated an inner clause binder with `m`'s outer variable
position. The cached closed frontier now has no `CHECK_FAIL` cases and moved
from 61 to 62 closed passes:

```text
TMPDIR=/project/tmp \
PROBLEM_DIR=/project/tmp/source_linked_strict_100_corpus_fresh_041947 \
WORK_DIR=/project/tmp/source_linked_slice_1_400_closed_cnf_binder_fix_124216 \
JOBS=20 MIN_PASS=0 CLOSED_CERT_V1=1 EMIT_TIMEOUT=30 CHECK_TIMEOUT=45 \
tests/vampire_certificate/run_native_emit_cached_parallel.sh \
  /project/tmp/source_linked_slice_1_400_fresh_042040

CLOSED_PASS 62
EMIT_FAIL 151
/project/tmp/source_linked_slice_1_400_closed_cnf_binder_fix_124216
```

The new committed closed case is:

```text
hammer.11523.29.th0.p
```

Validation for this increment:

```text
TMPDIR=/project/tmp ./makeopt

Direct focused checks:
hammer.11523.29.th0 CLOSED_PASS
hammer.10795.33.th0 CLOSED_PASS
/project/tmp/cnf_binder_fix_focus_124205

TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh
CLOSED_PASS 62
/project/tmp/native_cert_v1_closed_corpus.GmTSWl

TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh
native certificate v1 smoke test passed
/project/tmp/native_cert_v1.bjo36c

TMPDIR=/project/tmp tests/vampire_certificate/run_source_map_export_smoke.sh
Megalodon TH0 source-map export smoke passed
```

## July 14 Increment: Inequality Splitting Replay

The native emitter now replays Vampire's `inequality_name_intro` and
`inequality_split` steps for the common split-predicate shape exported in the
native certificate.  Instead of treating the fresh `sP...` predicate as an
unconstrained variable, the emitter turns it into a Megalodon definition of the
form:

```text
Definition sP... : ...->prop :=
  fun ... cert_splitN => cert_splitN = <named side> -> False.
```

The name-introduction clause is then proved from that definition as equality to
`False`, and the split step is replayed by case-analysis over the source
clause, replacing exactly the Vampire-provided negative equality literal by the
corresponding equality-to-`True` split-name literal.  The replay supports both
orientations of the source equality by reusing the existing native equality
symmetry proof generator.

This moved the cached source-linked closed frontier from 62 to 63 closed
passes:

```text
TMPDIR=/project/tmp \
PROBLEM_DIR=/project/tmp/source_linked_strict_100_corpus_fresh_041947 \
WORK_DIR=/project/tmp/source_linked_slice_1_400_closed_ineq_split_125611 \
JOBS=20 MIN_PASS=0 CLOSED_CERT_V1=1 EMIT_TIMEOUT=30 CHECK_TIMEOUT=45 \
tests/vampire_certificate/run_native_emit_cached_parallel.sh \
  /project/tmp/source_linked_slice_1_400_fresh_042040

CLOSED_PASS 63
EMIT_FAIL 150
/project/tmp/source_linked_slice_1_400_closed_ineq_split_125611
```

The new committed closed case is:

```text
hammer.11453.77.th0.p
```

Validation for this increment:

```text
TMPDIR=/project/tmp ./makeopt

Direct focused check:
hammer.11453.77.th0 CLOSED_PASS
/project/tmp/ineq_split_focus_125441

TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh
CLOSED_PASS 63
/project/tmp/native_cert_v1_closed_corpus.1Ta23E

TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh
native certificate v1 smoke test passed
/project/tmp/native_cert_v1.eHQz5x

TMPDIR=/project/tmp tests/vampire_certificate/run_source_map_export_smoke.sh
Megalodon TH0 source-map export smoke passed
```

## July 14 Increment: Existential ENNF and Skolem Replay

The native emitter now replays the common classical transformation
`~(forall x, A x -> B x)` to `exists x, A x /\ ~B x`, and it can replay the
matching one-variable `skolem_formula` step when Vampire gives an explicit
substitution from the existential variable to a fresh Skolem constant.

The Skolem constant is emitted as a Megalodon definition using the existing
library choice operator:

```text
Definition sK... : set := Eps_i (fun x:set => ...).
```

The generated proof uses the standard hashed `Eps_i` declaration and derives
the local helper `vampire_exists_set_choice` from `Eps_i_ax`. This avoids the
earlier local `vampire_choice_set` axiom experiment: Skolem replay now depends
on Megalodon's existing classical choice primitive, which is already present in
the original developments, rather than on a new unindexed axiom.

This moved the cached source-linked closed frontier from 63 to 66 closed
passes:

```text
TMPDIR=/project/tmp \
PROBLEM_DIR=/project/tmp/source_linked_strict_100_corpus_fresh_041947 \
WORK_DIR=/project/tmp/source_linked_slice_1_400_closed_skolem_131501 \
JOBS=20 MIN_PASS=0 CLOSED_CERT_V1=1 EMIT_TIMEOUT=30 CHECK_TIMEOUT=45 \
tests/vampire_certificate/run_native_emit_cached_parallel.sh \
  /project/tmp/source_linked_slice_1_400_fresh_042040

CLOSED_PASS 66
EMIT_FAIL 147
/project/tmp/source_linked_slice_1_400_closed_skolem_131501
```

The three new committed closed cases are:

```text
hammer.10699.43.th0.p
hammer.1098.23.th0.p
hammer.11374.48.th0.p
```

Validation for this increment:

```text
TMPDIR=/project/tmp ./makeopt

Direct focused checks for the two minimal Skolem blockers:
hammer.10699.43.th0 CLOSED_PASS
hammer.1098.23.th0 CLOSED_PASS
/project/tmp/skolem_eps_focus_10699_131453
/project/tmp/skolem_eps_focus_1098_131453

Cached closed replay also closed:
hammer.11374.48.th0 CLOSED_PASS

TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh
CLOSED_PASS 66
/project/tmp/native_cert_v1_closed_corpus.KUn3ge

TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh
native certificate v1 smoke test passed
/project/tmp/native_cert_v1.WAIHzB

TMPDIR=/project/tmp tests/vampire_certificate/run_source_map_export_smoke.sh
Megalodon TH0 source-map export smoke passed
```

## Increment: Nested ENNF And Skolem Choice Replay

The next update extends the native certificate checker for two more
Smolka-style transformations that appear in the cached Hammer proofs:

- negated universal formulas with more than one universally quantified binder
  and more than one implication premise, replayed as nested
  `vampire_exists_set` terms with nested `vampire_and` witnesses;
- Skolemization of nested set-valued existentials, replayed by defining each
  introduced Skolem symbol as an `Eps_i` choice term under the substitutions for
  the earlier Skolem symbols.

This is still implemented in `src/vampire_cert_v1.ml`, i.e. in the native
Vampire-certificate-to-Megalodon replay path. It is not a Python-side recovery
heuristic. The implementation also generalizes CNF projection from nested
conjunctions such as `A /\ (B /\ C)`.

Focused checks that previously required bridge assumptions now close:

```text
hammer.11602.25.th0 CLOSED_PASS
/project/tmp/ennf_multi_11602_132415

hammer.10609.51.th0 CLOSED_PASS
/project/tmp/nested_skolem_10609_132947
```

Cached parallel replay over the same source-linked frontier, without rerunning
Vampire:

```text
TMPDIR=/project/tmp \
PROBLEM_DIR=/project/tmp/source_linked_strict_100_corpus_fresh_041947 \
WORK_DIR=/project/tmp/source_linked_slice_1_400_closed_nested_skolem_132955 \
JOBS=20 MIN_PASS=0 CLOSED_CERT_V1=1 EMIT_TIMEOUT=30 CHECK_TIMEOUT=45 \
tests/vampire_certificate/run_native_emit_cached_parallel.sh \
  /project/tmp/source_linked_slice_1_400_fresh_042040

CLOSED_PASS 68
EMIT_FAIL 145
/project/tmp/source_linked_slice_1_400_closed_nested_skolem_132955
```

The two new committed closed cases are:

```text
hammer.10609.51.th0.p
hammer.11602.25.th0.p
```

## Increment: Functional Skolem Choice and Distributed CNF Projection

The latest update closes a more complex member of the same Smolka-style family.
The Skolem replay now transports through universal quantifiers, disjunctions,
and existential subformulas rather than only handling a top-level existential.
This permits functional Skolem definitions whose arguments are the surrounding
Vampire variables, for example a symbol of sort
`prop->set->(set->set)->set->set` defined by an `Eps_i` choice term.

The ENNF replay also handles the implication-to-disjunction case where the
left disjunct is not syntactically `A -> False`, but is instead the classical
existential form produced from a negated universal.  The CNF formula-clause
projection was generalized from one exact source clause to selecting a target
clause out of the source formula's computed CNF clauses and projecting through
the relevant conjunction branch.  Two generated proof-term bugs found by the
focused checker were fixed at the same time: quantified branch types are now
parenthesized in Skolem `vampire_or` eliminators, and formula text rendering no
longer picks constants such as `vampire_false` as recovered forall binders.

The representative focused case now emits with no bridge/admit/aby dependency
and checks in Megalodon:

```text
hammer.11888.36.th0 CLOSED_PASS
/project/tmp/functional_skolem_cnf_11888_134609
```

Cached parallel replay over the same source-linked frontier, without rerunning
Vampire:

```text
TMPDIR=/project/tmp \
PROBLEM_DIR=/project/tmp/source_linked_strict_100_corpus_fresh_041947 \
WORK_DIR=/project/tmp/source_linked_slice_1_400_closed_functional_skolem_cnf_134618 \
JOBS=20 MIN_PASS=0 CLOSED_CERT_V1=1 EMIT_TIMEOUT=30 CHECK_TIMEOUT=45 \
tests/vampire_certificate/run_native_emit_cached_parallel.sh \
  /project/tmp/source_linked_slice_1_400_fresh_042040

CLOSED_PASS 70
EMIT_FAIL 143
/project/tmp/source_linked_slice_1_400_closed_functional_skolem_cnf_134618
```

The two new committed closed cases are:

```text
hammer.11870.37.th0.p
hammer.11888.36.th0.p
```

Validation for this increment:

```text
TMPDIR=/project/tmp ./makeopt

TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh
native certificate v1 smoke test passed
/project/tmp/native_cert_v1.KETmLX

TMPDIR=/project/tmp tests/vampire_certificate/run_source_map_export_smoke.sh
Megalodon TH0 source-map export smoke passed

TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh
CLOSED_PASS 70
/project/tmp/native_cert_v1_closed_corpus.jsSYbu
```

## Remaining P0 Work

Closed mode is necessary but not sufficient.

The audit's source-linking criticism is only partially addressed. Current
source-map validation now rejects the worst placeholder case, where a non-true
certificate input is mapped to a THF `$true` declaration, and also rejects simple
hashed global formula mismatches and a substantial fragment of real emitted THF
formulas. It still does not prove in general that the certificate input
proposition is the proposition exported from the original Megalodon development:
unsupported THF constructs are now rejected in closed mode, but ordinary
diagnostic runs still treat them as unknown. The comparison also still happens
after textual THF parsing rather than by resolving directly to the original
Megalodon `Syntax.tm`. A zero-bridge proof cannot count as fully source-semantic
until full canonical source binding is implemented.

The next required correction is therefore full source proposition binding,
preferably by resolving certificate inputs to original Megalodon `Syntax.tm`
declarations or by independently recomputing canonical exported-formula hashes.

The audit is also right that the current emitter is still a source-text
generator. The intended endpoint is native elaboration toward `Syntax.pf`, with
source text as a debugging artifact rather than the trusted representation.

## Policy Going Forward

New aggregate bridge reductions should not be treated as the main milestone.
The next milestone should be:

```text
10 committed, reproducible, source-semantically-linked first-order cases
with CLOSED_PASS and zero non-source premises.
```

Only after that should the project resume broadening rule coverage.
