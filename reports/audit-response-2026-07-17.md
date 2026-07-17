# Audit Response for REPORT-2026-07-16

Date: 2026-07-17

Branch: `vampire/megalodon5`

Audit file:

- `reports/audit-REPORT-2026-07-16.md`

## Summary

The audit is accepted. The most important correction is the trust-boundary
reset: broad preprocessing runs that relied on certificate-derived `Known`
propositions are structural diagnostics, not proof reconstruction evidence.
The qualifying path is the native small-kernel `Syntax.pf` path, then
source/preprocessing proofs, then original-context theorem reconstruction.

## Changes Already Made on This Branch

- `-vampirecertv1preprocesspfcheck` now fails closed by default when a step
  would require installing a certificate-derived theorem into `Known`.
- The old behavior is available only through
  `MEGALODON_CERT_ALLOW_TRANSITIONAL_PREPROCESS_KNOWN=1`, and the harnesses
  classify such runs as `PREPROCESS_STRUCTURAL_PASS`.
- `tests/vampire_certificate/README.md` now separates `corepfcheck` from
  structural preprocessing diagnostics.
- The main design plans now use evidence classes E1-E4 and test stages T0-T4
  so integration results are not confused with proof reconstruction.
- The real-core frontier is now measured separately from synthetic core
  fixtures.

## Current Technical Reading

The current native proof-term frontier is real but still limited. The good
part is that `corepfcheck` constructs and checks `Syntax.pf` terms for the
source-entry/core subset. The bad part is that most real hammer certificates
still stop before the clausal core because the source/preprocessing layer is
incomplete.

The largest immediate blocker is Skolemization. Vampire emits useful metadata:
the source existential, the result formula, introduced Skolem symbols, and a
`parent_1_formula` implication from the existential to the instantiated body.
However, that implication is currently only annotation data. It is not a
proof-producing certificate step, so Megalodon cannot count it without either:

1. a real proof term based on conservative Skolem definitions and choice, or
2. a Vampire-side primitive expansion that explains the transformation in
   small checked steps.

The project should not solve this by adding another dynamic `Known`
proposition for `parent_1_formula`.

## Revised Work Order

1. Keep certificate-derived `Known` insertion out of every counted native path.
2. Extract the genuine clausal proof-term checker into isolated kernel modules.
3. Make Vampire emit a real primitive-certificate IR, not just ad hoc printer
   branches.
4. Get at least ten live regenerated certificates through the primitive
   `corepfcheck` gate.
5. Implement a concrete original-source context API for global facts, local
   hypotheses, definitional facts, set-command equalities, and conjecture
   negation.
6. Add Smolka-style transformations one by one with actual proof terms:
   source entry, rectification, FOOL/boolean normalization, ENNF, CNF
   projection, and Skolemization.
7. Only then use the 100-theorem original-context gate as the main success
   criterion.

## Non-Goals for Counted Progress

- No `admit`, `aby`, or incomplete QED.
- No Python reconstruction on the qualifying path.
- No private equality or private logical constants.
- No pass-count growth by enabling transitional `Known` propositions.
- No broad Megalodon-side proof search to recover data Vampire could emit.

## Status for Expert Review

The branch is now directionally aligned with the audit, but the architectural
pivot is incomplete. The expert should focus on whether the next code work is
really isolating the small kernel and moving proof detail into Vampire-side
primitive expansion, especially for Skolemization and source/preprocessing
transformations.

## July 17 Skolem/Kernel Update

After the audit response, the counted core path gained a narrow
metadata-backed Skolem proof term for direct existential choice. The accepted
case defines the generated Skolem symbol by a Megalodon delta definition,
uses the fixed choice principle, and checks the resulting `Syntax.pf` without
dynamic `Known` insertion.

The next real hammer frontier is more precise than "Skolemization" in
general. The representative case
`tests/vampire_certificate/closed_cases/hammer.1007.43.th0.p` now reaches
step `u210`, a Prover9-style `paramodulate` step over a clause that contains
dependent Skolem terms. The remaining failure is a proof-term well-formedness
issue:

```text
u210: Term de Bruijn index 15 is out of bounds for context length 15
while checking proof-term application argument: _15
```

This is not an admission gap and not a missing source-map label. It is a
specific retained-variable/term-binder accounting problem in the native
proof-term elaboration for a parent proof reused under paramodulation. Broad
fixes that skipped parent instantiation or changed global proof closing were
tested and rejected because they break earlier checked steps. The next fix
should therefore be local and principled: specify how stored theorem proofs
with step-variable `TLam`s are opened into a result-variable context, then
apply that rule uniformly to paramodulation and the other clausal kernel
rules.

## Later July 17 Structural Certificate Update

A subsequent checker change improved the strict certificate-validation
frontier, but it should be counted as E4 structural progress rather than as
native proof-term reconstruction.

The change adds scoped parameter matching for Vampire
`predicate_definition_fold` and `predicate_definition_fold_chain` steps. The
checker now treats the stripped universal binders of a predicate definition as
pattern parameters, matches the definition body against the actual source
subterm, and instantiates the folded predicate atom with the terms found in
that source context. This handles generated definitions whose parameters are
separated by unrelated source binders. The checker also accepts Vampire's
boolean/proposition equality wrappers around folded predicate atoms.

The same batch adds an ordered Skolemization candidate for structural formula
checking. It consumes Vampire's explicit substitution list through nested
existential binders, which fixes the representative failure that appeared
after the fold-chain blocker was removed.

Validation:

- optimized build passed;
- native certificate v1 smoke passed;
- the cached predicate-definition fold frontier now passes all 6 former
  failures;
- cached recheck of the previous 300-case directory reports 118 real
  certificate passes, 12 real checker failures, and 170 old non-certificate
  placeholders;
- fresh strict live 100 still reports `PASS 100`, with native primitive and
  kernel-v1 metadata audits passing.

This update does not change the revised work order above. It reduces
structural rejection in front of the kernel, but the qualifying path still
requires isolated primitive proof terms, no certificate-derived `Known`
insertion, and original-context source binding.

## Later July 17 Kernel Boundary Update

I made the first small implementation move requested by the audit's monolith
freeze: the `kernel_v1` schema/rule vocabulary and primitive-expansion
contract now live in `src/vampire_kernel_syntax.ml`, with an interface in
`src/vampire_kernel_syntax.mli`.

The strict certificate checker in `src/vampire_cert_v1.ml` uses that module
when validating `kernel_v1` metadata. Unsupported kernel rule names now fail
inside Megalodon's checker. The new negative fixture
`tests/vampire_certificate/native_cert_v1_invalid_kernel_rule.sexp` asserts
that behavior.

Validation:

- `TMPDIR=/project/tmp ./makeopt`
- `TMPDIR=/project/tmp tests/vampire_certificate/run_native_cert_v1_smoke.sh`
- `TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_v1_metadata_audit.sh
  /project/tmp/live_strict_100_megalodon5_after_fold_skolem`

This remains a boundary extraction, not a completed audit response. The larger
work still has to extract the typed kernel syntax/checker/elaborator, remove
certificate-derived `Known` from every counted native path, and add the
Vampire-side primitive builder.

The same boundary was then extracted on the Vampire side. Commit
`2b095b0ae` in `/project/vampire-leancheck` adds
`Shell/MegalodonChecker/MegalodonKernelSyntax.{hpp,cpp}` and makes
`MegalodonChecker.cpp` consume it for the schema string and
rule-to-required-primitive contract. This removes one hardcoded contract
if-chain from the large exporter without changing the emitted certificate
format.

Validation:

- `TMPDIR=/project/tmp make -j10 vampire_rel`
- 5-case live THF run with the new binary:
  `PASS 5`
- `run_native_primitive_audit.sh` on the 5-case artifact with small-sample
  minima
- `run_kernel_v1_metadata_audit.sh` on the same artifact, covering 280
  `kernel_v1` records

Vampire commit `2701d87e4` then moved the fixed
`primitive_expansion` field construction into the same helper. This is still
not a full primitive-step IR, but it reduces the amount of certificate contract
logic embedded directly in `MegalodonChecker.cpp` and gives the next builder
extraction a concrete place to grow.
