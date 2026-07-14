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

Validation performed on this branch:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh

PASS 213
/project/tmp/source_linked_slice_1_400_emit_closed_mode_regression_093857

CLOSED_PASS 1
/project/tmp/closed_mode_smoke_emit_093949
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

## Remaining P0 Work

Closed mode is necessary but not sufficient.

The audit's source-linking criticism remains open. Current source-map validation
still mostly proves that a label exists and has a compatible role/hash comment;
it does not yet prove that the certificate input proposition is the proposition
exported from the original Megalodon development. A zero-bridge proof cannot
count as source-semantic until this is fixed.

The next required correction is therefore source proposition binding, preferably
by resolving certificate inputs to original Megalodon `Syntax.tm` declarations
or by independently recomputing canonical exported-formula hashes. The current
fixture that maps arbitrary clauses to `$true` should become a negative test
once that binding exists.

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
