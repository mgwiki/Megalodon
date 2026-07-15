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

## Increment: Definition Rewrite, Irrelevant Substitution Entries, and Pure Rectification

This update closes one more no-derived proof by replaying two smaller native
certificate classes:

- `definition_rewrite_chain` is emitted as a checked definitional equality step
  when the folded symbols have already been introduced as Megalodon
  `Definition`s.  The representative case folds a large `If_i` term through a
  sequence of `sF...` definitions; Megalodon accepts `exact parent` after
  unfolding those definitions.
- `substitute` replay now ignores substitution entries whose source variable is
  not quantified by the parent clause.  Vampire sometimes carries these
  irrelevant entries in the proof trace; the actual clause instantiation should
  be computed from the parent-bound variables only.

The same patch also adds a guarded native replay for pure `rectify_formula`
steps.  Direct `exact parent` is used only when the target is a scoped variable
renaming of the parent formula.  Rectifications that also change Boolean
equality orientation remain bridges until they have an explicit transport proof;
for example `hammer.1007.43.th0` is now reduced to the single remaining
`bridge_rectify_formula__u98` rather than being counted prematurely.

Focused check:

```text
hammer.11635.105.th0 CLOSED_PASS
/project/tmp/subst_filter_11635_135826
```

Cached parallel replay over the same source-linked frontier, without rerunning
Vampire:

```text
TMPDIR=/project/tmp \
PROBLEM_DIR=/project/tmp/source_linked_strict_100_corpus_fresh_041947 \
WORK_DIR=/project/tmp/source_linked_slice_1_400_closed_defrewrite_subst_rectify_135840 \
JOBS=20 MIN_PASS=0 CLOSED_CERT_V1=1 EMIT_TIMEOUT=30 CHECK_TIMEOUT=45 \
tests/vampire_certificate/run_native_emit_cached_parallel.sh \
  /project/tmp/source_linked_slice_1_400_fresh_042040

CLOSED_PASS 71
EMIT_FAIL 142
/project/tmp/source_linked_slice_1_400_closed_defrewrite_subst_rectify_135840
```

The new committed closed case is:

```text
hammer.11635.105.th0.p
```

Validation for this increment:

```text
TMPDIR=/project/tmp ./makeopt

TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh
native certificate v1 smoke test passed
/project/tmp/native_cert_v1.deIhWK

TMPDIR=/project/tmp tests/vampire_certificate/run_source_map_export_smoke.sh
Megalodon TH0 source-map export smoke passed

TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh
CLOSED_PASS 71
/project/tmp/native_cert_v1_closed_corpus.VIAlNW
```

## Increment: Orientation-Changing Rectification Under Or and Existentials

The native rectification replay now handles the next non-trivial
`rectify_formula` class: scoped variable renaming combined with Boolean
equality orientation changes under `vampire_or` and Church-style existential
formulas.  The proof generator now transports formulas through disjunctions and
existentials, recovers source and target binder names from the native
certificate variable environment, substitutes source binder names onto target
binders before recurring, and uses the existing equality-symmetry proof at
atomic leaves.

This closes the remaining bridge in `hammer.1007.43.th0`.  The previous guarded
pure-rectification replay had reduced that proof to
`bridge_rectify_formula__u98`; this increment proves that step natively instead
of treating it as an assumption.

Focused check:

```text
hammer.1007.43.th0 CLOSED_PASS
/project/tmp/rectify_or_exists_1007_140306
```

Cached parallel replay over the same source-linked frontier, without rerunning
Vampire:

```text
TMPDIR=/project/tmp \
PROBLEM_DIR=/project/tmp/source_linked_strict_100_corpus_fresh_041947 \
WORK_DIR=/project/tmp/source_linked_slice_1_400_closed_rectify_or_exists_140320 \
JOBS=20 MIN_PASS=0 CLOSED_CERT_V1=1 EMIT_TIMEOUT=30 CHECK_TIMEOUT=45 \
tests/vampire_certificate/run_native_emit_cached_parallel.sh \
  /project/tmp/source_linked_slice_1_400_fresh_042040

CLOSED_PASS 72
EMIT_FAIL 141
/project/tmp/source_linked_slice_1_400_closed_rectify_or_exists_140320
```

The new committed closed case is:

```text
hammer.1007.43.th0.p
```

Validation for this increment:

```text
TMPDIR=/project/tmp ./makeopt

TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh
native certificate v1 smoke test passed
/project/tmp/native_cert_v1.EP2blt

TMPDIR=/project/tmp tests/vampire_certificate/run_source_map_export_smoke.sh
Megalodon TH0 source-map export smoke passed

TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh
CLOSED_PASS 72
/project/tmp/native_cert_v1_closed_corpus.8L7vL5
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

## Follow-up: Lambda Substitution Replay

The next closed increment addresses a small but real native-replay failure in
the first-order/lambda boundary, without adding any theorem-specific names.

The failing target was `hammer.10644.15.th0.p`. Its remaining non-source
premises were:

```text
bridge_fool__u204
bridge_substitute__u473_subst0
bridge_paramodulate__u473
```

The native certificate already contained detailed replay steps for the latter
two: an explicit substitution of a quantified `set` variable by
`Repl omega (vLAM ...)`, followed by paramodulation through the equality
introduced from the original `int` definition. The issue was in the Megalodon
emitter:

- rendered `vLAM` binders used a global fresh counter, so identical certificate
  lambdas could be printed as different `vdbN` names in different generated
  propositions;
- substitution-sort inference treated the certificate constructor `vLAM` as a
  free variable in the substitution term;
- FOOL conversion could not replay the case where native `LAMV` had already
  parsed to the same `vLAM` term, but the emitted parent proposition still had a
  redundant unused metadata `forall`.

The implemented correction is general:

- generated clause propositions now render `vLAM` binders with stable local
  names during proposition construction and replay-safety checks;
- substitution-sort inference filters lambda-bound names and treats `vLAM`/`vPI`
  as known certificate constructors;
- FOOL formula replay has a guarded path for parent formulas that are already
  equal to the target after native `LAMV` parsing, while the emitted parent type
  has only unused metadata binders. These binders are instantiated with a
  canonical witness (`Eps_i (fun Xeps:set => vampire_true)` for `set`, and
  `vampire_true` for `prop`).

Focused validation:

```text
/project/tmp/focused_10644_closed_141415
EMIT_STATUS=0
CHECK_STATUS=0
```

Cached 20-way replay over the existing source-linked frontier:

```text
TMPDIR=/project/tmp \
PROBLEM_DIR=/project/tmp/source_linked_strict_100_corpus_fresh_041947 \
WORK_DIR=/project/tmp/source_linked_slice_1_400_closed_vlam_subst_fool_141422 \
JOBS=20 MIN_PASS=0 CLOSED_CERT_V1=1 EMIT_TIMEOUT=30 CHECK_TIMEOUT=45 \
tests/vampire_certificate/run_native_emit_cached_parallel.sh \
  /project/tmp/source_linked_slice_1_400_fresh_042040

CLOSED_PASS 73
EMIT_FAIL 140
```

The new committed closed case is:

```text
hammer.10644.15.th0.p
```

This is still not a broad architectural finish. It is a Prover9-style
increment in the right direction: a summarized Vampire bridge was replaced by
replay of the detailed native certificate steps already present in the proof
object.

## Follow-up: CNF Literal and Unit Resolution Replay

The next focused target was the repeated `.46` family headed by
`hammer.10208.46.th0.p`. After the lambda-substitution work, the representative
proof had only:

```text
bridge_cnf__u239
bridge_resolve__u305
```

The native certificate showed that `u239` is not a theorem-specific step. It is
the standard conversion of a checked singleton formula/clause
`P -> vampire_false` into the negative singleton clause for `P`. The final
`u305` step is ordinary unit resolution between that negative singleton and the
positive unit `u304`.

Implemented general changes:

- `FormulaCopy` now records its singleton clause in the emitter's checked-clause
  map, so later clause inferences can use it as a real parent.
- `cnf_literal` now has native replay for both checked formula parents and
  checked singleton-clause parents.
- `resolve` now renders `vLAM`-containing structural safety checks with stable
  lambda binder names.
- FOOL/equality checks distinguish unscoped `db*` names from `db*` names scoped
  under explicit `vLAM`.

Focused closed emission for `hammer.10208.46.th0.p` now reaches zero non-source
premises and emits native `u239` and `u305` claims. The generated Megalodon
script still fails source-linked checking because the earlier source/rectify
glue for local facts with lambda binders is not yet principled: Vampire's
rectified formula metadata can expose lambda-local binders as outer
`forall`s, while the original Megalodon lemma has only the real theorem
binders. A short attempt to render such source formulas directly from the AST
was backed out because it regressed the committed closed corpus.

Validation kept for this increment:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_source_map_export_smoke.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh

CLOSED_PASS 73
```

The next source-linking step should not be another string-rendering heuristic.
It needs a small, explicit rectification/alpha-conversion proof object for
original Megalodon facts with lambda binders, so the source theorem is connected
to Vampire's rectified formula before FOOL conversion.

## Follow-up: Source Rectification Prefix Replay

That source-linking step has now been implemented for the `.46` family. The
problem was not a missing source map: the original Megalodon assumptions were
linked to the correct Vampire input facts. The failure was proof-term shape.
Vampire's rectification can expose names used inside lambda terms as additional
leading formula binders, while the original Megalodon fact only quantifies the
real theorem variables. A direct `exact src_axiom...` therefore had the right
body proposition up to scoped lambda renaming, but the wrong number of leading
arguments.

Implemented general changes:

- `RectifyFormula` now tries an explicit extra-prefix proof before generic
  formula-orientation replay. It introduces the target prefix binders in the
  emitted order and applies the source theorem to the parent binders that are
  genuinely present there.
- The emitted-prefix parser now preserves the proposition order instead of
  reversing the leading `forall`s.
- Later formula transformations can pre-apply surplus emitted parent binders to
  canonical witnesses before running their ordinary replay. This handles the
  common shape where the emitted parent proposition has lambda-rectification
  binders but the native formula object has only the real formula-level
  `forall`s.

The representative case now emits the intended source-linked skeleton:

```text
claim u228: forall X5:set, forall X4:set, forall X2:set,
  forall X6:set, forall X3:set, forall X1:set, forall X0:set, ...
{ exact (fun X5:set => fun X4:set => fun X2:set => fun X6:set =>
    fun X3:set => fun X1:set => fun X0:set =>
      ((src_axiom_Hv3__u76 X1) X0)). }
```

The following four formerly checking-failing source-linked cases are now part
of the committed closed corpus:

```text
hammer.10208.46
hammer.10269.46
hammer.10304.46
hammer.10363.46
```

Validation:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_source_map_export_smoke.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh

CLOSED_PASS 77
```

Cached 20-way replay over the source-linked frontier, without rerunning Vampire:

```text
TMPDIR=/project/tmp \
WORK_DIR=/project/tmp/rectify_prefix_parent_replay_145107 \
PROBLEM_DIR=/project/tmp/source_linked_strict_100_corpus_fresh_041947 \
JOBS=20 MIN_PASS=0 CLOSED_CERT_V1=1 EMIT_TIMEOUT=30 CHECK_TIMEOUT=45 \
tests/vampire_certificate/run_native_emit_cached_parallel.sh \
  /project/tmp/source_linked_slice_1_400_fresh_042040

CLOSED_PASS 77
EMIT_FAIL 136
```

There were no remaining `CHECK_FAIL` cases in that replay. The remaining
frontier is therefore not source-linking for this family; it is the still-open
closed-mode bridge classes such as normal form, skolem formula, CNF variants,
substitution/paramodulation variants, AVATAR components, and theory-derived
steps.

## Follow-up: CNF Parent Prefix Discipline

The next adjustment follows the audit's recommendation to prefer small,
checked replay corrections over broad bridge-count chasing.

One class of CNF replay failures came from using all metadata variable sorts of
the parent step when replaying `cnf_formula_clause`. Some of those variables are
introduced inside the formula body rather than in the formula's leading `forall`
prefix. Treating them as leading proof arguments makes the emitted Megalodon
term apply a parent theorem to arguments it does not actually take.

The emitter now computes:

```ocaml
take_prefix (prefix_forall_count parent_formula) parent_sorts
```

and passes that restricted prefix to the CNF singleton/projection replay
helpers. This keeps the source proposition and the replay proof aligned with
the native formula shape instead of with unrelated metadata binders.

I also tested a broader higher-order Skolem choice experiment for
`set->prop`. That experiment was deliberately not committed: it could make
`hammer.10654.21` emit without bridges, but the generated proof did not
standalone-check in Megalodon. In particular, the attempted `set->prop` choice
prelude would have required a new trusted axiom. Keeping it would have violated
the audit's trust-boundary recommendation, so this branch leaves those cases as
closed-mode failures with explicit `bridge_normal_form` /
`bridge_skolem_formula` diagnostics.

Validation:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_source_map_export_smoke.sh

TMPDIR=/project/tmp \
WORK_DIR=/project/tmp/closed_cnf_prefix_final_151556 \
PROBLEM_DIR=/project/tmp/source_linked_strict_100_corpus_fresh_041947 \
JOBS=20 MIN_PASS=0 CLOSED_CERT_V1=1 EMIT_TIMEOUT=30 CHECK_TIMEOUT=45 \
tests/vampire_certificate/run_native_emit_cached_parallel.sh \
  /project/tmp/source_linked_slice_1_400_fresh_042040

CLOSED_PASS 77
EMIT_FAIL 136
CHECK_FAIL 0
```

## Follow-up: Equality Handling and Predicate-Definition Frontier

The next investigation targeted a high-frequency remaining blocker:
`theory_predicate_definition`, for example in `hammer.10157.86.th0.p`.
That class is attractive because Vampire emits the defining formulas in the
native certificate metadata and many blocked cases contain the same pattern.

I tested a local-definition replay strategy for these predicate definitions,
but deliberately did not enable or commit it. The native metadata currently
does not give enough stable binder information for the generated predicate
body: in the representative case the printed predicate-definition template
reused variable names in a way that produced free or mis-scoped Megalodon
variables, and the quick AST renderer guessed lambda/existential binders rather
than receiving them explicitly from Vampire. That failed the Megalodon checker.
Keeping it would have moved proof logic back into fragile reconstruction code,
which is exactly what the audit warns against. The right next step is to export
richer binding/type structure from Vampire for these definitions, then replay
them as small checked Megalodon definitions/claims.

The changes kept from this pass are narrower hardening changes needed by that
frontier and by later Smolka-style transformation replay:

- equality is treated as a logical constant during certificate substitution, so
  `=` is not accidentally looked up as an ordinary symbol;
- scoped Vampire-variable renaming now uses explicit option-valued association
  lookup instead of exception-driven `List.assoc`, which made equality-related
  failures easier to diagnose and avoids misleading control flow;
- proposition-valued equality terms are rendered through the proposition
  equality path, including nested equality arguments;
- source-map declaration hashes/formulas are stored with explicit replacement
  semantics instead of mutable hash tables, matching the surrounding functional
  parser style.

Validation:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_source_map_export_smoke.sh

TMPDIR=/project/tmp \
WORK_DIR=/project/tmp/closed_hardened_equality_154626 \
PROBLEM_DIR=/project/tmp/source_linked_strict_100_corpus_fresh_041947 \
JOBS=20 MIN_PASS=0 CLOSED_CERT_V1=1 EMIT_TIMEOUT=30 CHECK_TIMEOUT=45 \
tests/vampire_certificate/run_native_emit_cached_parallel.sh \
  /project/tmp/source_linked_slice_1_400_fresh_042040

CLOSED_PASS 77
EMIT_FAIL 136
```

The result is intentionally not counted as a closed-proof improvement. It
preserves the strict zero-non-source guard while clarifying that the current
predicate-definition route needs more Vampire-side detail, not more guessing in
the Megalodon emitter.

## Follow-up: Scope Reset After Re-Reading the Audit

After re-reading the audit on `vampire/megalodon3`, I removed an uncommitted
attempt to expand the native format with `avatar_definition` and `avatar_split`
constructors. That work exposed useful Vampire metadata, but it was the wrong
near-term move: AVATAR is explicitly outside the audit's recommended qualifying
fragment, and adding importer constructors would have grown the broad path
without producing additional closed Megalodon proofs.

The branch is therefore kept on the closed-corpus milestone:

- no new AVATAR constructors are added to the native certificate datatype;
- the existing AVATAR component/refutation records remain diagnostics and
  closed-mode blockers, not qualifying replay steps;
- closed mode continues to reject every derived AVATAR premise as a non-source
  theorem assumption;
- the next work should target committed, reproducible, source-linked
  `CLOSED_PASS` cases, with any new Vampire-side detail justified by a concrete
  closed replay step rather than by aggregate bridge reduction.

This is a deliberate rollback of scope, not a proof improvement. It aligns the
branch with the audit's main recommendation: keep the trusted result small,
fail closed, and expand only after the source-bound zero-premise corpus grows.

## Follow-up: Predicate Definitions Replayed Under Closed Mode

A later pass revisited the predicate-definition blocker after adding stricter
binder selection. The earlier concern remains valid in general: the emitter must
not guess missing structure. The committed replay is therefore deliberately
narrow. It handles Vampire `predicate_definition` steps whose certificate
formula has the explicit definitional-disjunction shape already checked by the
native certificate validator:

```text
forall args, vampire_or (defined_predicate args -> False) body
```

For such steps the Megalodon emitter now creates a local `Definition` for the
introduced predicate symbol and proves the corresponding disjunction as a
Megalodon `claim`, using classical `vampire_xm` over the defining body. If the
shape or binder information is outside that fragment, the path still falls back
to the old non-source premise, which closed mode rejects.

This is not a broad-metric success criterion. It is a small closed-mode replay
improvement because `theory_predicate_definition` is no longer the first
forbidden premise in the cached frontier; the remaining first blockers are now
mostly AVATAR components, Skolem formulas, FOOL distinctness, definition inputs,
and predicate-definition folds.

Validation for the committed change:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh
TMPDIR=/project/tmp JOBS=10 tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh

CLOSED_PASS 77
/project/tmp/native_cert_v1_closed_corpus.zMxG3a

CLOSED_PASS 92
EMIT_FAIL 121
/project/tmp/predicate_definition_frontier_165159
```

First blockers in the cached frontier after this change:

```text
avatar_component 79
bridge_skolem_formula 18
theory_fool_distinctness 16
definition_input 5
bridge_predicate_definition_fold 2
bridge_fool 1
```

## Follow-up: Source Binding Qualification Status

The audit's strongest correctness objection was that a source-linked proof can
still be only label-linked unless the emitted source formula is compared to the
certificate input. This branch already made closed mode reject unsupported or
mismatching hash-backed source formulas. The generated Megalodon artifact now
also exposes that distinction directly in each `vampire_source_assumption`
comment through a `source_formula_status` field:

```text
source_formula_status "closed_formula_checked"
source_formula_status "decl_formula_present_unhashed"
source_formula_status "local_or_unhashed"
```

The committed closed corpus harness now rejects any 64-hex-hash global source
binding whose emitted status is still unchecked, missing, or missing from the
source map. This does not add a proof rule and does not increase the closed
count; it tightens what can be counted as a reproducible closed proof artifact.

Validation:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh
TMPDIR=/project/tmp JOBS=10 tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh

CLOSED_PASS 77
/project/tmp/native_cert_v1_closed_corpus.othto4
```

Operationally, the audit reset is now interpreted as follows: `CLOSED_PASS`
with zero non-source premises, source-origin metadata, source-assumption
bindings, and checked hash-backed source statuses is the qualifying result.
Ordinary `PASS`, aggregate bridge reduction, and broad frontier movement remain
diagnostic only. The next large architectural step should be to move proof
construction toward native `Syntax.pf` objects or to add richer Vampire-side
atomic proof details, not to resume Python-side reconstruction.

The important audit guard is still intact: these numbers are `CLOSED_PASS`
counts, and closed mode still rejects every remaining bridge or derived
non-source theorem premise.

## Follow-up: Local Function Definition Inputs

The next closed blocker addressed after predicate definitions was Vampire
`definition_input` for introduced function symbols with arguments. The previous
replay handled only zero-argument abbreviations, so clauses such as

```text
forall X1:set, ordsucc X1 = sF10 X1
```

were still theorem premises in closed mode. The emitter now recognizes
introduced-symbol applications on either side of a singleton equality clause,
builds the corresponding Megalodon definition proof under the explicit
argument binders, and keeps the equality as a checked `claim`.

There is an additional scoping issue for higher-order Skolem witnesses. Some
introduced `sF*` abbreviations depend on a witness opened locally by the
existing Church-existential elimination:

```text
apply u293.
let sK7:(set->prop).
assume ...
```

Such abbreviations cannot soundly be emitted as top-level `Definition`s. For
those certificates the emitter instead treats the introduced function symbols
as local aliases while rendering later clauses and formulas, so the generated
claims refer to the locally opened witness rather than to an escaped global
constant.

Focused validation:

```text
TMPDIR=/project/tmp ./makeopt

OUT=/project/tmp/definition_input_10806_final_171218
bin/megalodon -vampirecertv1closed ... hammer.10806.144.th0/native.sexp ...
bin/megalodon -hf $OUT/out.mg

Everything looks good.
```

Regression validation:

```text
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh
TMPDIR=/project/tmp JOBS=10 tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh

CLOSED_PASS 77
/project/tmp/native_cert_v1_closed_corpus.zIrvHC
```

Cached closed frontier after this change:

```text
CLOSED_PASS 93
EMIT_FAIL 120
/project/tmp/definition_input_frontier_171231
```

First blockers in that frontier:

```text
avatar_component 79
bridge_skolem_formula 18
theory_fool_distinctness 16
definition_input 4
bridge_predicate_definition_fold 2
bridge_fool 1
```

This is still not a broad completion claim. It is one additional
source-linked, zero-non-source-premise reconstruction in the cached frontier,
with the closed gate unchanged.

## Follow-up: FOOL Distinctness Replay

The next adjustment removes `theory_fool_distinctness` from the non-source
premise set. Vampire's FOOL distinctness clause has the shape `$true !=
$false`; the Megalodon replay now proves it directly from the existing encoded
definitions of `True`, `False`, and `vampire_eq_prop`, by instantiating the
equality eliminator with the appropriate projection predicate. No new axiom,
choice principle, or Vampire run is involved.

A dedicated native certificate fixture was added for this path:

```text
tests/vampire_certificate/native_cert_v1_fool_distinctness_valid.sexp
tests/vampire_certificate/native_cert_v1_fool_distinctness_valid.th0.p
```

The focused closed fixture emits a Megalodon claim
`theory_fool_distinctness__d1` and `bin/megalodon -hf` checks it. On the cached
frontier, this does not increase `CLOSED_PASS`, because the affected library
cases immediately expose later AVATAR premises. It does, however, remove FOOL
distinctness from the first-blocker list:

```text
CLOSED_PASS 93
EMIT_FAIL 120
/project/tmp/fool_distinctness_frontier_172334

avatar_component 95
bridge_skolem_formula 18
definition_input 4
bridge_predicate_definition_fold 2
bridge_fool 1
```

Validation:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh
TMPDIR=/project/tmp JOBS=10 tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh
```

## Follow-up: Guarded AVATAR Component Replay

The next step targets the largest remaining first-blocker class without
declaring the whole AVATAR SAT refutation trusted. For each guarded AVATAR
component, the emitter now introduces the split atom as a Megalodon definition
of the corresponding component formula and proves the component clause by
classical case analysis over that formula. This is currently limited to
components whose split body is syntactically available from the native
certificate and does not contain unscoped `db*` names; scoped/de-Bruijn
components still remain explicit closed-mode failures until the certificate
carries enough scoped structure to replay them safely.

The small AVATAR component fixture now has closed emit/check coverage. It emits
`Definition split_1 : prop := p.` and a checked `claim avatar_component__c0`,
with no bridge or derived AVATAR premise.

Validation:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh
TMPDIR=/project/tmp JOBS=10 tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh
```

The cached frontier did not increase `CLOSED_PASS`, because most affected cases
now expose `avatar_refutation` or later preprocessing bridges. It did move the
first-blocker profile from AVATAR components to AVATAR refutations:

```text
CLOSED_PASS 93
EMIT_FAIL 120
/project/tmp/avatar_component_frontier_173336

avatar_refutation 87
bridge_skolem_formula 18
avatar_component 8
definition_input 4
bridge_predicate_definition_fold 2
bridge_fool 1
```

## Follow-up: Strict Source Linking Policy

After rereading the audit on `vampire/megalodon3`, one criticism was stale in
implementation but still correct in policy. The concrete `$true` source-map hole
had already been turned into negative tests, and closed mode was already
requiring checked source formulas. However, ordinary strict certificate checking
still used the weaker source-linking policy: formulas outside the checked THF
fragment were accepted for diagnostics instead of rejected.

That was too weak for a mode named strict. This branch now requires semantic
source-formula matching in both strict paths:

- standalone `-vampirecertv1strict`;
- the integrated `-vampireabyproof megalodon` native-certificate checker.

Plain `-vampirecertv1` remains a loose inspection mode so unsupported formulas
can still be triaged without claiming a qualifying reconstruction. The smoke
suite now has an explicit regression: the unsupported-source fixture is accepted
by ordinary inspection, rejected by strict, and rejected by closed mode.

## July 15 Re-read on `vampire/megalodon3`

I re-read `reports/audit-REPORT-2026-07-14.md` after switching both repositories
to `vampire/megalodon3`. Several of the audit's concrete objections have been
addressed on this branch:

- `-vampirecertv1closed` exists and fails emission when any bridge or derived
  non-source theorem premise remains.
- The cached harness reports `CLOSED_PASS` separately from ordinary integration
  `PASS`.
- Strict and closed source-map checking now require semantic source-formula
  matching for the supported THF fragment; the earlier `$true` fixture is no
  longer accepted as a strict/closed source link.
- The closed corpus harness rejects unchecked source-assumption comments and
  generated scripts containing `admit`, `aby`, `bridge_*`, or derived premise
  assumptions.

However, the audit's larger architectural criticism still applies. The branch
continued to improve broad closed replay, including CNF, Skolem, FOOL,
definition-input, and AVATAR cases. Those results are useful diagnostics, but
they are not the audit's recommended MVP milestone.

I therefore tightened `tests/vampire_certificate/run_native_cert_v1_core_closed_audit.sh`
so its whitelist is the restricted clause-level fragment only:

```text
input
substitute
resolve
subsumption_resolution
factor
equality_resolution
equality_factoring
paramodulate
contradiction
```

The gate deliberately excludes formula inputs/copies, rectification, FOOL
elimination, ENNF/CNF projection, Skolemization, definition inputs, inequality
splitting, AVATAR, theory facts, predicate definitions, and other preprocessing
macros. If those steps appear in a closed proof, the proof may still be a
valuable broad closed-mode regression, but it is not a core/audit-qualifying
proof.

After the clausal seed work below, rerunning the tightened core audit on the
committed closed corpus gives the requested restricted threshold:

```text
TMPDIR=/project/tmp JOBS=10 MIN_CORE=10 RUN_CORE_CASES=1 \
  tests/vampire_certificate/run_native_cert_v1_core_closed_audit.sh

CORE_ELIGIBLE 10
EXCLUDED 147
MIN_CORE 10
CLOSED_PASS 10
CORE_CLOSED_PASS 10
```

This is the important accounting correction: the project now has ten
committed, source-linked, zero-non-source-premise core proofs, but they are
already-clausal seed problems. Broad cached `CLOSED_PASS` counts remain
secondary until the same discipline covers THF-exported Megalodon obligations
through a certified preprocessing layer.

I also rebuilt Vampire on this branch with:

```text
TMPDIR=/project/tmp make -j10 vampire_rel
```

The rebuilt binary is:

```text
/project/vampire-leancheck/vampire_rel_vampire/megalodon3_10967
```

A minimal THF probe with source maps still produced native certificates
containing `rectify_formula`, `fool_formula`, `cnf_formula_clause`,
`cnf_literal`, and related preprocessing steps. That confirms the reset should
not be more Megalodon-side special handling for the broad schedule. It should be
a Vampire-side restricted core certificate schedule/export path, or a carefully
selected already-clausal input form, before claiming the audit's restricted
milestone.

## July 15 Increment: Source-Linked Clausal Core Seeds

The first concrete follow-up was to make the source-linking layer accept
already-clausal TPTP declarations.  The native source-map parser already handled
`thf(...)` and `fof(...)` declarations, and the formula checker already had a
simple clause parser.  It did not, however, record formulas and trailing hashes
from `cnf(...)` declarations, so a real Vampire-generated core certificate over
clausal input could not be checked as source-linked.

That gap is now closed:

- `parse_source_map` recognizes `cnf(...)` declarations for declaration name,
  role, formula, and trailing hash.
- The smoke suite has a closed positive regression generated by Vampire from a
  clausal contradiction.
- Ten generated source/certificate pairs are committed as
  `tests/vampire_certificate/closed_cases/core.cnf.*`.

Focused validation:

```text
TMPDIR=/project/tmp ./makeopt

bin/megalodon -vampirecertv1closed \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_cnf_source_map_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_cnf_source_map_valid.th0.p \
  -vampirecertv1emit /project/tmp/cnf_source_map_valid_001549/out.mg ...

Vampire certificate v1 source map checked 3 sources.
Vampire certificate v1 closed checked 5 steps.
bin/megalodon -hf /project/tmp/cnf_source_map_valid_001549/out.mg
Everything looks good.
```

The tightened core audit now reaches the audit's ten-case restricted threshold:

```text
TMPDIR=/project/tmp JOBS=10 MIN_CORE=10 RUN_CORE_CASES=1 \
  tests/vampire_certificate/run_native_cert_v1_core_closed_audit.sh

CORE_ELIGIBLE 10
EXCLUDED 147
MIN_CORE 10
CLOSED_PASS 10
CORE_CLOSED_PASS 10
```

Before the later `prop_ext` tightening below, the full committed closed corpus
also passed with the new cases included:

```text
TMPDIR=/project/tmp JOBS=10 tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh

CLOSED_PASS 157
```

This is deliberately not claimed as a THF/Megalodon-development success.  It
proves a narrower but necessary boundary condition: the clause-level native
certificate path can be source-linked and checked without preprocessing steps
when Vampire starts from already-clausal input.  The next step is to replace or
extend these clausal seeds toward THF-exported Megalodon obligations by adding a
certified preprocessing layer rather than folding preprocessing into the core
count.  The broad `CLOSED_PASS 157` number is historical and is superseded by
the stricter `prop_ext` accounting at the end of this response.

## July 15 Increment: Separate THF Preprocessing Gate

The next adjustment adds an intermediate audit gate between the clausal core and
the broad closed corpus:

```text
tests/vampire_certificate/run_native_cert_v1_preprocess_closed_audit.sh
```

This gate permits the certified formula-preprocessing layer:

```text
formula_input
formula_term_input
formula_term_copy
formula_copy
rectify_formula
fool_formula
fool_bool
ennf_formula
cnf_formula_clause
cnf_literal
```

plus the restricted core clause rules.  It still excludes Skolemization, AVATAR,
introduced definitions, FOOL theory facts, inequality splitting, and other broad
macro steps.  It also requires at least one preprocessing rule in each selected
case, so the ten clausal `core.cnf.*` fixtures cannot satisfy this gate by
themselves.

Validation:

```text
TMPDIR=/project/tmp JOBS=10 MIN_PREPROCESS=10 RUN_PREPROCESS_CASES=1 \
  tests/vampire_certificate/run_native_cert_v1_preprocess_closed_audit.sh

PREPROCESS_ELIGIBLE 15
EXCLUDED_OR_CORE_ONLY 142
PREPROCESS_CLOSED_PASS 15
```

This is still not the full large-development target, but it is a better
staging line than a single broad `CLOSED_PASS` count.  The branch now has three
separate committed gates:

- `CORE_CLOSED_PASS 10` for source-linked clausal core proofs;
- `PREPROCESS_CLOSED_PASS 15` for source-linked THF preprocessing plus core;
- a historical broad `CLOSED_PASS 157` measurement for all committed closed
  cases before the later `prop_ext` tightening below.

## July 15 Tightening on `vampire/megalodon3`

One remaining P0 gap was still present after the initial response above:
generated scripts always declared `Axiom prop_ext`, and closed mode did not
count the derived helper `vampire_eq_prop_ext` as a non-source dependency. This
made some FOOL/equality reconstructions look closed even though they relied on
an unproved propositional-extensionality axiom rather than a Megalodon replay or
an explicitly approved source/library premise.

The branch now makes that dependency visible and non-qualifying:

- `prop_ext` and `vampire_eq_prop_ext` are emitted only when a non-closed
  diagnostic reconstruction actually uses them.
- `-vampirecertv1closed` fails before emission if any step requires that helper,
  reporting `helper:prop_ext` alongside bridge and derived-premise blockers.
- The cached and committed closed harnesses reject leaked `Axiom prop_ext`
  declarations as a defense in depth.
- FOOL exhaustiveness, FOOL distinctness, and formula-CNF smoke fixtures remain
  valid structural/native-certificate tests, but their closed-mode checks are
  now negative until propositional extensionality is discharged in Megalodon or
  accepted as an explicit library theorem by the qualifying policy.
- The closed corpus checker uses `-hf` whenever emitted scripts contain axioms,
  because the project setting explicitly allows classical reasoning (`xm`).
  This does not re-allow `prop_ext`; it is separately forbidden in closed mode.

Validation after this tightening:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh

native certificate v1 smoke test passed
/project/tmp/native_cert_v1.YPgnjU

TMPDIR=/project/tmp JOBS=10 MIN_CORE=10 RUN_CORE_CASES=1 \
  tests/vampire_certificate/run_native_cert_v1_core_closed_audit.sh

CORE_ELIGIBLE 10
EXCLUDED 147
CLOSED_PASS 10
CORE_CLOSED_PASS 10
/project/tmp/native_cert_v1_core_closed_audit.1L1etj

WORK_DIR=/project/tmp/megalodon3_prop_ext_closed_frontier_015640 \
TMPDIR=/project/tmp \
PROBLEM_DIR=/project/tmp/source_linked_strict_100_corpus_fresh_041947 \
JOBS=20 MIN_PASS=0 CLOSED_CERT_V1=1 CHECK_SOURCE_MAP=1 STRICT_CERT_V1=1 \
EMIT_TIMEOUT=30 CHECK_TIMEOUT=45 \
tests/vampire_certificate/run_native_emit_cached_parallel.sh \
  /project/tmp/megalodon3_native_live_current_noorigin_003131

CLOSED_PASS 7
EMIT_FAIL 206
```

The drop in broad cached closed count is intentional. It removes cases whose
only missing dependency was hidden behind `prop_ext`, leaving the audit
milestone focused on the ten committed restricted source-linked proofs.

## July 15 Follow-up: Indexed Library `prop_ext`

The previous tightening was too conservative about propositional extensionality.
It correctly rejected hidden fresh axioms, but it also rejected the actual HF
library theorem `prop_ext`. A direct probe of the generated standalone prelude
under `-hf -v 10` shows that

```text
Axiom prop_ext : forall p q:prop, iff p q -> p = q.
```

is assigned Megalodon's indexed known id

```text
d8c32d0ac70c5760222c9adf1a3ca90f3cb6b5182b0f70a5d82cb9000abc77ef
```

and checks without an "unindexed axiom" warning. The branch now treats this as
an explicit approved library dependency rather than a non-source theorem premise:

- the emitted script marks the dependency with
  `// vampire_approved_library_known ((name "prop_ext") ...)`;
- closed mode no longer fails merely because replayed FOOL/formula steps use
  `vampire_eq_prop_ext`, provided no bridge or derived theorem premise is
  introduced;
- closed harnesses still reject `assume vampire_eq_prop_ext`, bridge premises,
  derived premise assumptions, `admit`, `aby`, and incomplete-QED markers;
- closed harnesses now run axiom-containing scripts with `-hf` and reject any
  `WARNING: The id ... not indexed as previously known` output.

Focused validation:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh

native certificate v1 smoke test passed
/project/tmp/native_cert_v1.OOr1Ae

TMPDIR=/project/tmp JOBS=10 MIN_CORE=10 RUN_CORE_CASES=1 \
  tests/vampire_certificate/run_native_cert_v1_core_closed_audit.sh

CORE_ELIGIBLE 10
EXCLUDED 147
CLOSED_PASS 10
CORE_CLOSED_PASS 10
/project/tmp/native_cert_v1_core_closed_audit.eJeyKx
```

Cached 20-way replay over the same existing source-linked frontier, without
rerunning Vampire, moved broad closed replay from 7 to 141 passes:

```text
WORK_DIR=/project/tmp/megalodon3_prop_ext_indexed_frontier_020834 \
TMPDIR=/project/tmp \
PROBLEM_DIR=/project/tmp/source_linked_strict_100_corpus_fresh_041947 \
JOBS=20 MIN_PASS=0 CLOSED_CERT_V1=1 CHECK_SOURCE_MAP=1 STRICT_CERT_V1=1 \
EMIT_TIMEOUT=30 CHECK_TIMEOUT=45 \
tests/vampire_certificate/run_native_emit_cached_parallel.sh \
  /project/tmp/megalodon3_native_live_current_noorigin_003131

CLOSED_PASS 141
EMIT_FAIL 71
CHECK_FAIL 1
```

The sole `CHECK_FAIL`, `hammer.10847.41.th0.p`, had empty stdout/stderr under
the 45-second check cap. Rechecking that exact emitted script with a 180-second
timeout succeeded:

```text
timeout 180 ./bin/megalodon -hf \
  /project/tmp/megalodon3_prop_ext_indexed_frontier_020834/cases/hammer.10847.41.th0/out.mg

Everything looks good.
```

The cached harness now classifies timeout exits as `CHECK_TIMEOUT` instead of a
blank `CHECK_FAIL`, so future frontier summaries distinguish proof errors from
large-script checking time.

## July 15 Follow-up: Predicate-Definition Fold Chains

The next native-emitter change targets the audit's request to replay Vampire's
own proof object rather than reconstructing by external Python heuristics.
`predicate_definition_fold_chain` is no longer an unconditional bridge: the
emitter now searches the checked certificate's definition sequence, emits
internal Megalodon claims for each body-to-definiendum replacement, and uses the
existing formula-orientation proof when Vampire's metadata proposition is the
left-associated normal form of the native term.

The implementation is intentionally conservative. It replays chains whose
formula shapes are covered by the current fold proof generator, including
set/set->prop existential contexts, and falls back to closed-mode bridges for
prop-binder-heavy or arbitrary true-left FOOL-equality shapes that are known to
need more atomic replay. This avoids producing invalid closed scripts while
leaving the remaining cases visible as explicit bridge blockers.

Focused validation:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh

native certificate v1 smoke test passed

hammer.10794.63.th0:
  closed emit: no predicate_definition_fold(_chain) bridge
  -hf check: Everything looks good.
```

Cached 20-way replay over the same existing native certificates, without
rerunning Vampire:

```text
WORK_DIR=/project/tmp/megalodon3_predfold_single_guard_023237 \
TMPDIR=/project/tmp \
PROBLEM_DIR=/project/tmp/source_linked_strict_100_corpus_fresh_041947 \
JOBS=20 MIN_PASS=0 CLOSED_CERT_V1=1 CHECK_SOURCE_MAP=1 STRICT_CERT_V1=1 \
EMIT_TIMEOUT=30 CHECK_TIMEOUT=45 \
tests/vampire_certificate/run_native_emit_cached_parallel.sh \
  /project/tmp/megalodon3_native_live_current_noorigin_003131

CLOSED_PASS 142
EMIT_FAIL 70
CHECK_TIMEOUT 1
```

The single timeout remains `hammer.10847.41.th0.p`, previously shown to pass
with a 180-second local check. No `CHECK_FAIL` rows remain in this replay.

## July 15 Follow-up: Transparent Predicate Definitions

The next adjustment follows the audit's closed-proof discipline: predicate
definition replay may use a transparent Megalodon `Definition` only when that
definition is compatible with the native certificate's predicate-definition
body. Vampire's native metadata sometimes provides a useful rendered body that
avoids binder-capture bugs in the text emitter; however, it is not always the
same body as the checked native predicate-definition theorem. Some `sP*`
definitions carry a transformed existential metadata body while the certificate
theorem and fold step use a universal body.

The emitter now:

- uses `predicate_definition/formula` as a Megalodon definition body only when
  its outer shape agrees with the rendered native certificate body;
- refuses to replay predicate-definition theorem and fold steps when there is
  no compatible transparent Megalodon definition for the introduced predicate;
- emits the parsed native target proposition for successful fold proofs, so
  metadata pretty-printing differences such as `vampire_or` association are not
  mistaken for proof obligations;
- leaves incompatible cases as closed-mode `derived:theory_predicate_definition`
  or `bridge:bridge_predicate_definition_fold` failures instead of emitting an
  invalid script.

Focused validation:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh

native certificate v1 smoke test passed

hammer.10890.4.th0:
  closed emit: succeeds with no bridge/admit/aby
  -hf check: fails earlier in the generated ENNF/skolem proof:
             Unknown term X7

hammer.10894.19.th0:
  closed emit: rejected
  reason: derived:theory_predicate_definition__u225,
          bridge:bridge_predicate_definition_fold__u226
```

Cached 20-way replay over the same existing native certificates, without
rerunning Vampire:

```text
WORK_DIR=/project/tmp/megalodon3_predfold_transparent_gate_033843
TMPDIR=/project/tmp \
PROBLEM_DIR=/project/tmp/source_linked_strict_100_corpus_fresh_041947 \
JOBS=20 MIN_PASS=0 CLOSED_CERT_V1=1 CHECK_SOURCE_MAP=1 STRICT_CERT_V1=1 \
EMIT_TIMEOUT=30 CHECK_TIMEOUT=45 \
tests/vampire_certificate/run_native_emit_cached_parallel.sh \
  /project/tmp/megalodon3_native_live_current_noorigin_003131

CLOSED_PASS 143
EMIT_FAIL 67
CHECK_FAIL 3
```

Relative to `/project/tmp/megalodon3_skolem_guard_exists_order_031857`, this is
a net increase from 141 to 143 checked closed passes. Three cases became new
checked closed passes:

```text
hammer.11475.33.th0.p
hammer.11505.69.th0.p
hammer.11535.43.th0.p
```

One previous pass, `hammer.10794.63.th0.p`, is no longer counted because the
stricter path exposes a checker failure:

```text
Failure at line 108 char 359: Unknown term X0
```

The remaining `CHECK_FAIL` cases are not counted as closed proofs:

```text
hammer.10794.63.th0.p
hammer.10890.4.th0.p
hammer.10909.19.th0.p
```

This is intentionally not reported as a broad bridge-count milestone. It is a
small closed-mode correction: two net new checked closed proofs, and stricter
rejection of incompatible transparent predicate definitions.
