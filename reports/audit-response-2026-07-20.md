# Audit Response, 2026-07-20

This branch accepts the July 20 audit's main criticism.  The previous
28-command prefix result is not a qualifying E1 result because the
reconstruction path could install certificate-local definitions into global
Megalodon state and then let later Qed checking see them.  That is useful
diagnostic evidence, but it is not yet an isolated proof reconstruction result.

## Immediate Policy Change

The `vampire/megalodon6` branch introduces an explicit qualifying mode:

```text
-vampireabyqualifying
```

This mode enables native strict Vampire checking, forces `-vampireabyproof
megalodon`, caps Vampire execution at 10 seconds, and fails closed when the
certificate replay does not explain the proof.

In qualifying mode, the following routes are disabled:

- compact Qed delta registration for certificate-local definitions;
- unchecked final refutation finishing;
- pure-proposition constructive shortcuts;
- constructive goal search fallback;
- source-audit proof-search fallback;
- native `aby` direct/`megaauto` fallback.

The old OCaml reconstruction/search path remains in the tree as a regression
oracle and debugging aid.  It must not be used to claim counted progress.

## State Isolation

The first audit-driven guard is intentionally simple: qualifying mode may not
register certificate-local definitions globally at all.  Any attempt to call
the compact Qed-delta registration path raises immediately.  Qed cleanup now
also checks that no tracked certificate-local Qed state remains.  Qualifying
mode also rejects `MEGALODON_CERT_KEEP_QED_DELTA=1`, since retaining temporary
Qed reconstruction state is incompatible with the isolation invariant.

This is stricter than the previous transactional idea and is the correct
default for the next milestone.  If a proof needs certificate-local helper
definitions, the qualifying path must expand them into the returned proof term
or represent them in a separate checked certificate context, not leak them
through `sigdelta`/`sigtmof`.

## Downgraded Work

The interrupted `UnionE`/source-alias experiment is not part of this branch's
qualifying work.  Continuing to add ad hoc monolithic source-name repairs would
repeat the architecture rejected by the audit.

The branch should also stop treating broad inference coverage as the primary
task.  Rule coverage is only useful after the small deterministic certificate
path exists.

## Next Milestone

The next acceptable milestone is five small original-source proofs that satisfy
all of the following:

- run through `-vampireabyqualifying`;
- use Vampire with `-vampireabytimeout <= 10`;
- use `-vampireabyproof megalodon`;
- resolve assumptions to live Megalodon source lemmas, hypotheses, or explicit
  reflexivity proofs for exported `set` equalities;
- leave no certificate-local global definitions after checking;
- avoid `aby`, admits, incomplete Qed, `megaauto`, constructive fallback, and
  source-audit fallback;
- pass in a fresh process and in a different order.

Only after those five examples pass should the work grow to 10 and then 100
proofs.

## Architecture Direction

The Prover9/Ivy lesson remains binding:

```text
Vampire proof
  -> small explicit primitive certificate
  -> deterministic Megalodon elaborator
  -> Megalodon proof term
  -> ordinary Qed check
```

The qualifying implementation should move out of the large `megalodon.ml` and
`vampire_cert_v1.ml` paths into small modules:

- `vampire_kernel_syntax.ml`
- `vampire_kernel_check.ml`
- `vampire_kernel_elab.ml`
- `vampire_source_context.ml`

Until that extraction is real, this branch's qualifying mode is a guardrail,
not the final architecture.

## Follow-up Extraction, 2026-07-20

After re-reading the audit on `vampire/megalodon6`, the next code changes were
kept deliberately architectural rather than coverage-driven:

- FOOL exhaustiveness and FOOL distinctness structural checks were moved from
  the monolithic certificate importer into `vampire_kernel_check.ml`.
- The shared `open_step_theorem` proof-term operation was moved from
  `vampire_cert_v1.ml` into `vampire_kernel_elab.ml`; the importer now only
  supplies certificate-specific variable lists and term-closing logic.
- Skolem replay now uses the shared result-variable lookup helpers in
  `vampire_kernel_elab.ml` instead of carrying a local duplicate.
- The validating checks were focused: both FOOL fixtures pass, the valid
  derived-resolution open-step proof term still checks, the dropped-parent
  open-step regression still fails closed, and the existing strict smoke case
  still passes.
- The Skolem lookup extraction was validated with the direct Skolem preprocess
  fixture, the `hammer.1032.16` preprocess fixture, and the existing 28-step
  strict smoke case.
- The Vampire emitter was tightened to fail before printing any `kernel_v1`
  rule with a primitive contract but without a `primitive_expansion=prefix`
  marker.  A TH0 smoke proof emitted 34 `kernel_v1` records, all carrying the
  marker.
- The older string-based primitive expansion-chain metadata now also emits the
  singular `primitive_expansion_requires=...` field expected by strict
  Megalodon validation.  A fresh Vampire-emitted TH0 certificate was extracted
  and accepted by Megalodon strict checking for 28 steps.

This still does not make the project complete, and it does not rehabilitate the
old 28-command prefix as E1 evidence.  It is, however, the intended correction
in direction: reduce the monolithic replay path and make the small deterministic
checker/elaborator modules the home for qualifying proof logic.
