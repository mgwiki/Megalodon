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
