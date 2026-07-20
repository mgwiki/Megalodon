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
- Vampire now validates both `primitive_expansion=prefix` and the singular
  required primitive against the rule's allowed primitive set before emitting
  `kernel_v1` metadata.  The same TH0 emission and Megalodon strict check
  passed after this hardening.
- A cross-repository vocabulary sync test now compares Vampire's C++ kernel
  rule/contract declarations with Megalodon's OCaml declarations.  This is a
  diagnostic guard only: it prevents drift in the small-kernel certificate
  interface and is not used to reconstruct proofs.
- Strict Megalodon checking now rejects `primitive_expansion_requires_count`
  lists that omit the singular `primitive_expansion_requires` primitive, and
  Vampire now enforces the same invariant before emission.  The native smoke
  suite includes a negative fixture for the Megalodon side, and a fresh TH0
  Vampire certificate passed strict Megalodon checking for 28 steps after the
  emitter-side hardening.
- Skolem branch-choice contracts are no longer hidden behind
  `MEGALODON_CERT_ENABLE_BRANCH_CHOICE_CONTRACTS=1`.  When Vampire emits
  `skolem_macro_edge_*_contract_branch_choice_*` fields, Megalodon now parses
  and validates the typed choice symbol, replaced variable, predicate, body and
  witness term by default.  This surfaced the current `exactly1of2_I1`
  frontier more honestly: the certificate contains the needed branch-choice
  data, but the replay path still has to use those exact emitted predicates
  rather than reconstructing equivalent-looking epsilon predicates locally.

This still does not make the project complete, and it does not rehabilitate the
old 28-command prefix as E1 evidence.  It is, however, the intended correction
in direction: reduce the monolithic replay path and make the small deterministic
checker/elaborator modules the home for qualifying proof logic.

## Post-audit Correction, 2026-07-20

After switching to `vampire/megalodon6`, I removed the uncommitted
`vampire_cert_v1.ml` Skolem branch-choice replay experiment instead of
committing it.  Even though it consumed real Vampire-emitted branch-choice
metadata, it still added more qualifying-looking behavior to the monolithic
importer.  That conflicts with the audit's freeze rule, so it is not part of
this branch.

I also re-ran a focused original-hammer qualifying prefix probe with
`-vampireabyqualifying` and the current `/project/tmp/vampire-cmake-megalodon6`
Vampire binary.  The result was:

```text
FalseE: reconstructed and Qed-checked
andEL: rejected by qualifying mode
```

The failure is the expected consequence of disabling the global-delta/fallback
routes.  It confirms that the older 28-command hammer prefix remains a
non-qualifying regression oracle, not counted E1 evidence.  The reconstruction
README now says this explicitly, and the live scripts now prefer the current
`megalodon6` Vampire build under `/project/tmp`.

The next implementation target is therefore not `UnionI`, broader AVATAR
coverage, or another Skolem heuristic.  It is the first five small
original-source qualifying proofs, starting with `andEL`, through the extracted
small-kernel/source-context path.

## State-Isolation Hardening, 2026-07-20

The branch now adds a stronger invariant around every qualifying live Vampire
proof command.  Before the command runs, Megalodon snapshots the full
`sigdelta` and `sigtmof` tables.  After native certificate reconstruction,
including failure paths, qualifying mode compares the current tables with the
snapshot and fails if any entry was added, removed, or changed.  This is stricter
than the earlier tracked-list cleanup: it catches untracked certificate-local
global state, not just entries recorded through
`vampire_register_reconstruction_delta_for_qed`.

The focused guard suite passes with this check enabled.  The current committed
frontier is also updated from the earlier note: with the current
`/project/tmp/vampire-cmake-megalodon6` Vampire build, the original-source
qualifying prefix now reconstructs and Qed-checks the first three hammer
commands (`FalseE`, `andEL`, and `andER`) under `-vampireabyqualifying`.
This is useful progress toward the five-proof milestone, but it still should be
reported as a small focused E1 candidate set, not as a revived 28-command or
100-theorem result.
