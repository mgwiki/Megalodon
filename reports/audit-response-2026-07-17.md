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
