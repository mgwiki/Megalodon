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

## Remaining P0 Work

Closed mode is necessary but not sufficient.

The audit's source-linking criticism is only partially addressed. Current
source-map validation now rejects the worst placeholder case, where a non-true
certificate input is mapped to a THF `$true` declaration, and also rejects simple
hashed global formula mismatches and a substantial fragment of real emitted THF
formulas. It still does not prove in general that the certificate input
proposition is the proposition exported from the original Megalodon development:
unsupported THF constructs are conservatively treated as unknown, and the
comparison still happens after textual THF parsing rather than by resolving
directly to the original Megalodon `Syntax.tm`. A zero-bridge proof cannot count
as fully source-semantic until full canonical source binding is implemented.

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
