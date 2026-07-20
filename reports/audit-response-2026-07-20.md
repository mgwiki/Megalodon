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

## Qualifying Search-Cap Correction, 2026-07-20

The next original-source hammer command, `and3I`, exposed two separate issues.
First, the Skolem branch-choice elaborator consumed Vampire-emitted
branch-choice bodies in a different variable representation from the already
closed target formula.  The branch-choice body is now closed under the same live
variables, at one additional local depth for the chosen witness binder, before
it is used to build the proof term.  This removes the immediate
`#P1`-versus-DB-variable orientation mismatch without adding a theorem-name
special case.

Second, after that representation mismatch was removed, qualifying mode could
still spend tens of seconds in guided supplied-refutation search before failing
`and3I`.  That is not acceptable as qualifying evidence and is contrary to the
audit's deterministic replay requirement.  Qualifying mode now defaults the
guided negated-conjecture reconstruction to one supplied-refutation attempt and
depth one unless explicitly overridden by debugging environment variables.  A
focused four-command probe still reconstructs `FalseE`, `andEL`, and `andER`,
then fails at `and3I`, but it does so in about four seconds instead of entering
the long search path.

The frontier therefore remains three original-source qualifying proofs.  The
next real proof milestone is still to make `and3I` close through deterministic
source-goal composition, not to recover it by broad Megalodon-side search.

## Qualifying Candidate-Search Freeze, 2026-07-20

After re-reading the audit again on `vampire/megalodon6`, the source-binding
candidate enumeration path was removed from qualifying mode.  If the direct
guided refutation-to-goal bridge cannot explain the current theorem,
qualifying mode now stops at
`candidate_refutation_fallback:disabled_by_qualifying_mode` instead of trying
candidate source-binding applications.

This is an intentional downgrade, not a loss of useful debugging code.  The old
candidate path remains available outside `-vampireabyqualifying` as a
regression oracle, but it is no longer eligible for counted E1 evidence.  A new
focused guard,
`tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh`,
checks that the first three original hammer commands still reconstruct and
Qed-check, that the fourth command (`and3I`) fails under qualifying mode, and
that the failure is specifically the fail-closed candidate-refutation guard.

The honest qualifying frontier remains the three small original-source proofs:
`FalseE`, `andEL`, and `andER`.  The next real progress must make `and3I` pass
through the extracted small-kernel/Skolem transformation route, not by
re-enabling Megalodon-side candidate search.

## Native Replay Normalization, 2026-07-20

A later `and3I` probe showed that the remaining failure is now concentrated in
native proof replay for Skolem/choice transformations under open proposition
binders.  The branch therefore made two bounded normalization changes, both
kept inside the proof-term replay path rather than Python or name-guessing
code:

- Megalodon's live proposition-extensionality normalizer no longer rewrites the
  live library theorem `prop_ext` into the native-core two-implication shape.
  That direct shape belongs to Vampire's internal prop-ext primitive, whereas
  Megalodon's `prop_ext` expects an `iff` proof.
- Live native-basis proof replacement now tracks term-binder depth when it
  substitutes closed derived proofs such as prop-choice and not-forall/exists
  expansions.
- The direct Skolem helper elaborator now threads the current local term depth
  into helper proof construction and normalization, so helper predicates are
  not silently treated as depth-zero formulas.

These changes are deliberately not reported as new E1 proof coverage.  The
focused four-command original-hammer probe still reconstructs and Qed-checks
`FalseE`, `andEL`, and `andER`, then fails closed at `and3I`.  The value of this
iteration is narrower: it removes invalid replay shapes and makes the next
`and3I` failure more specifically about the Skolem/choice transformation
contract, not leaked global state or broad fallback search.

The audit's central architectural criticism still stands.  The next corrective
step should move the relevant Skolem/choice transformation replay out of the
monolithic importer and into the extracted small-kernel checker/elaborator
modules before claiming additional counted proofs.

## Skolem/Choice Traversal Extraction, 2026-07-20

The first piece of that corrective step is now in place.  Generic proof-term
inspection for certificate-local Skolem/choice witnesses has been moved from
`vampire_cert_v1.ml` into `vampire_kernel_elab.ml`:

- symbol containment in proof terms;
- exact normalized term containment in proof terms;
- first enclosing witness term discovery;
- normalized enclosing witness-term collection;
- binder-depth-aware witness-term collection;
- registered witness-term replacement construction.

The native-core importer now calls these extracted operations with the
Megalodon/Vampire choice-symbol set and native-core normalizer instead of
carrying private traversal copies.  This is not yet a full Smolka-style
transformation checker, but it is the right direction: deterministic
Skolem/choice replay state is migrating into the small-kernel elaboration
boundary, while `vampire_cert_v1.ml` is reduced to native-core adaptation.

Validation for this change:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_elab_unit.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_and_prefix_qualifying.sh
TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_certified_vampire_no_incomplete.sh
TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
```

The honest frontier remains unchanged: the first three original hammer
commands (`FalseE`, `andEL`, `andER`) pass in qualifying mode, and `and3I`
still fails closed.  That is intentional reporting discipline.  The next
architectural step is to extract the actual Skolem/choice transformation
checking/elaboration, not merely the witness-term traversals.

## Branch-Choice Contract Selection Extraction, 2026-07-20

A second Skolem/choice piece has now been moved across the same boundary.  The
logic that selects an emitted Skolem branch-choice contract for a target
witness, checks it by exact witness term or symbol alias, rewrites earlier
witness heads by alias, and substitutes the replaced source variable is now in
`vampire_kernel_elab.ml`.

`vampire_cert_v1.ml` still builds the Megalodon-specific choice proof and
closes the returned body in the native-core context, but it no longer owns the
deterministic branch-choice matching/rewriting operation.  This is a small
step, not a proof-coverage claim, but it moves another part of the
Skolemization replay contract out of the importer and into the extracted
elaboration module.

The focused validation remains:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_elab_unit.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_and_prefix_qualifying.sh
TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_certified_vampire_no_incomplete.sh
```

The frontier is still three original-source qualifying proofs plus a
fail-closed `and3I`.  The next extraction target should be the transformation
driver that consumes these branch-choice bodies and produces the proof-term
orientation, so the eventual `and3I` fix is explained by the small-kernel
Skolem path rather than by local importer search.

## Skolem Helper-Matching Extraction, 2026-07-20

The helper-formula matcher used by Skolem replay has also moved into
`vampire_kernel_elab.ml`.  The extracted code now:

- peels quantified helper implications into explicit helper records;
- detects configured existential-head occurrences;
- performs exact witness-term replacement in formulas;
- checks structural compatibility of helper targets under forall,
  implication, conjunction, disjunction and existential targets;
- selects the first matching helper while preserving the remaining helper list.

`vampire_cert_v1.ml` still supplies the native-core normalizers and continues
to build the actual Megalodon proof term, but the deterministic decision about
which emitted helper implication applies is no longer local importer logic.

The same focused validation passed after the extraction:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_elab_unit.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_and_prefix_qualifying.sh
TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_certified_vampire_no_incomplete.sh
TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
```

This still does not increase the counted proof frontier.  Its purpose is to
make the next `and3I` work happen inside a reviewable Skolem helper and
branch-choice pipeline rather than in unstructured native replay code.

## Live `xm` Negation Alignment, 2026-07-20

A focused `and3I` debug run then exposed a separate live-proof replay mismatch:
the generated case split for `xm` sometimes used implication-to-`False` as the
negative branch even when the loaded Megalodon context provided the library
`not` theorem and the theorem statement was phrased through that live `not`.

The branch now routes all such live case-negation terms through the same
`vampire_live_not_tm` adapter used elsewhere.  This is intentionally a small
normalization fix, not an inference-coverage extension: it aligns the generated
proof term with the available Megalodon logical basis and falls back to
implication-to-`False` only through the existing live-library adapter.

Validation after this change:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_elab_unit.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_certified_vampire_no_incomplete.sh
TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_and_prefix_qualifying.sh
```

The result remains intentionally conservative.  The first three original
hammer commands still pass in qualifying mode, and `and3I` still fails closed.
The failure shape has moved past the earlier proof-of-prop mismatch and is now
concentrated in guided negated-conjecture replay, with candidate fallback still
disabled by qualifying mode.

## Qualifying Supplied-Refutation Depth Cap, 2026-07-20

The next audit-aligned cleanup addresses runtime rather than coverage.  The
guided negated-conjecture wrapper already limited qualifying mode to one
supplied-refutation attempt, but that single attempt still entered the
supplied-refutation bridge with the legacy depth-6 quantified-instantiation
search.  On `and3I` this produced thousands of rejected replay probes before
the intended fail-closed guard fired.

Qualifying mode now defaults the supplied-refutation bridge itself to depth 1.
The depth can still be raised for diagnostics with:

```text
MEGALODON_CERT_SUPPLIED_REFUTATION_DEPTH_LIMIT=<n>
```

This is deliberately a negative-space change: it does not make any new theorem
pass and it does not add a fallback.  It makes the qualifying path less like a
Megalodon-side search engine and closer to the deterministic replay discipline
requested by the audit.

## Skolem Witness-Rewrite Extraction, 2026-07-20

A focused `and3I` debug run confirmed that Vampire's emitted branch-choice
contracts are selected for both introduced proposition witnesses (`sK0` and
`sK1`).  The next issue is therefore in proof-term replay and replacement, not
in missing Vampire metadata.

As a small cleanup in the audit's requested direction, the direct Skolem replay
path no longer carries its own binder-aware witness-term rewriter.  It now
uses the extracted `Vampire_kernel_elab.replace_exact_terms_in_term`
operation.  That keeps another deterministic Skolem/choice operation in the
small-kernel elaboration module and leaves `vampire_cert_v1.ml` as the
native-core adapter.

This is not new proof coverage.  The `and3I` frontier remains a fail-closed
case until the remaining proof-term orientation/replacement mismatch is solved
through the extracted Skolem/choice transformation path.

## Guided Refutation Attempt Scheduling, 2026-07-20

The next `and3I` probe showed a smaller but concrete qualifying-mode bug.  The
guided negated-conjecture path is allowed one supplied-refutation attempt by
default, but `try_guided_proposition_suffix` spent that attempt before the
proposition had any native-refutation, CPS, or double-negation shape for the
matched source target.  Later deterministic suffix instantiations did reach a
ready shape, but the attempt budget had already been exhausted.

The guided path now calls the supplied-refutation bridge only after
`proposition_ready_for_target` succeeds.  This preserves the one-attempt
qualifying policy while making that attempt correspond to an actually
checkable refutation shape.

This still does not close `and3I`.  The next failure is again the substantive
witness-replacement mismatch: the checked live proof expects certificate
Skolem symbols such as `sK1`, while the live-safe proof body contains the
Megalodon choice witness `Eps_prop (...)`.  That is the next Skolem/choice
transformation issue to solve in the extracted path.
