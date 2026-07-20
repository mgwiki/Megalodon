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

## Live Expected-Delta Consistency, 2026-07-20

A subsequent focused `and3I` probe found one small live-checker inconsistency.
`vampire_check_proof_of_prop` expanded the candidate proof with the live-safe
certificate delta, but expanded the expected proposition with the full
certificate delta before applying the live basis.  That is an avoidable
asymmetry for generated Skolem symbols: the proof and the expected proposition
should be compared after the same live-safe filtering.

The branch now expands the live expected proposition with the same live-safe
extra delta used for the proof.  This is a correctness guard for fail-closed
checking, not a new proof-reconstruction feature.  The focused guards still show
the same honest frontier:

```text
vampireaby qualifying guard checks passed
LIVE_HAMMER_AND_PREFIX_QUALIFYING_PASS 3
LIVE_HAMMER_PREFIX4_FAILCLOSED_QUALIFYING_PASS
```

`and3I` still fails closed at the proposition-valued Skolem/choice replay
boundary.  A speculative change to split local and stored branch-choice witness
definitions in `vampire_cert_v1.ml` was tested and removed because it did not
move the failure and would continue growing the monolithic replay path that the
audit warned against.

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

Follow-up hardening: in `-vampireabyqualifying` mode, if this live-safe actual
proposition extraction fails while Vampire extra symbols are present, the
oracle now returns `None` instead of falling back to the full certificate-delta
proposition.  This preserves the three-proof frontier and keeps `and3I` at the
same fail-closed guard, but removes another certificate-local steering route
from counted qualifying reconstruction.

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

## Scoped Choice-Witness Frontier, 2026-07-20

The latest focused `and3I` iteration narrows the remaining failure further.
The branch-choice metadata is present, parsed, selected, and used; the failure
is not caused by missing Vampire-side detail.  It is also not acceptable to
paper over the problem with the old unique-choice expansion heuristic, because
that would reintroduce exactly the Megalodon-side reconstruction/search pattern
the audit rejects.

One small deterministic cleanup was made: generated/native aliases are now
symmetric for `name` and `#name`, and the direct Skolem witness replacement
normalizes only the known choice-witness heads (`Eps_prop`, `Eps_i`, and their
typed variants) before exact comparison.  This is an alias-normalization fix,
not a new inference rule.

The focused validation remains conservative:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
```

The frontier is unchanged: `FalseE`, `andEL`, and `andER` are the only current
original-source qualifying proofs, and `and3I` still fails closed.  The next
implementation step should make the Skolem/choice transformation driver
construct the live witness proof at the same scoped proposition as the emitted
branch-choice predicate, inside the extracted small-kernel elaboration path.
No broader candidate search, source-audit fallback, or monolithic Skolem
heuristic should be counted as progress.

## Exact Choice-Replacement Guard, 2026-07-20

The next correction was deliberately conservative.  The extracted
`registered_witness_term_replacements` helper no longer treats "the proof
contains some choice symbol also mentioned by a registered witness definition"
as enough evidence to build a replacement.  It now emits a replacement only
when the registered witness term itself occurs exactly after normalization.
This removes a symbol-only guessing path from the reusable Skolem/choice
elaboration boundary.

The contract-backed branch-choice candidate collector was also moved into
`vampire_kernel_elab.ml`.  The extracted collector now refuses to lift a choice
term out of a term-binder scope when that term depends on the binder; the unit
test covers both the rejected binder-dependent case and a liftable closed
choice term.  `vampire_cert_v1.ml` still adapts native-core state and checks the
candidate proof, but it no longer owns this traversal.

This is not new proof coverage.  It is an audit-aligned reduction in implicit
Megalodon-side guessing and a guard against manufacturing invalid de Bruijn
templates.  The focused checks still show the honest frontier:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_elab_unit.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_and_prefix_qualifying.sh
TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
```

The first three original hammer commands still pass in qualifying mode, and
`and3I` still fails closed at the Skolem/choice proof-of-proposition boundary.

## Live Actual-Proposition Alignment, 2026-07-20

The next focused probe showed that the goal-reconstruction wrapper could still
ask `vampire_actual_prop_of_proof` for the proposition of a proof under the full
certificate delta, even though the final proof checker would later require the
same proof to survive live-safe expansion.  That is a bad steering signal for
Skolem/choice cases: it can guide reconstruction with a proposition containing
certificate-local Skolem symbols while the live proof body has already expanded
those definitions to choice witnesses.

`vampire_actual_prop_of_proof` now first tries to extract the actual
proposition from the live-expanded proof under the live-safe extra delta when
Vampire supplies extra certificate symbols.  It rejects both proof terms and
actual propositions that still mention certificate-only symbols before falling
back to the older certificate-delta extraction path.

This again does not close `and3I`.  The current failure still shows that the
direct Skolem proof shape obtains `P (Eps P)` from the choice axiom and then
relies on certificate-local definitional equality to use it as `P sK`.  The
remaining fix must make that local definition explicit in the small-kernel
Skolem transformation or avoid returning a proof whose live checking depends on
the `sK := Eps P` delta.  The bounded validation after this change was:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_elab_unit.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_and_prefix_qualifying.sh
TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
```

## Returned-Proof Expansion Order, 2026-07-20

A fresh `and3I` debug probe then exposed an expansion-order problem in the
live checker.  Returned proof terms were first expanded with the certificate
delta and only then passed through the source-map/local-name expander.  If the
source-map pass reintroduced a certificate alias such as `#sK1`, the
certificate delta did not get another chance to expand it before live checking.

`vampire_expand_returned_proof` now applies the reconstruction delta once more
after source-map/local expansion.  This is not a Skolem proof rule and it does
not special-case `and3I`; it is an idempotent returned-proof normalization step
that keeps certificate-local definitions from surviving only because they were
introduced by the later source-map pass.

This does not increase the qualifying proof count.  The first three original
hammer commands still pass, and `and3I` still fails closed.  The failure has
moved to the real scoped Skolem/choice boundary: live-expanded candidates now
reach a de Bruijn-depth mismatch inside expanded choice predicates instead of
stopping only at raw `#sK1` versus `Eps_prop` naming.  The next implementation
step remains an extracted small-kernel Skolem/choice transformation that proves
or eliminates the local witness definitions explicitly, rather than relying on
certificate-local conversion.

## Choice-Witness Coercion Removal, 2026-07-20

The direct Skolem helper replay previously built a choice proof at
`P (Eps P)` and then wrapped it in an identity proof whose declared
proposition was `P sK`.  That made the live proof appear to have the
certificate-local Skolem proposition even though the only real proof produced
by the choice axiom was the epsilon-instantiated proposition.

That coercion has now been removed.  The direct replay continues with the
epsilon-instantiated body, and the final replay no longer rewrites epsilon
witnesses back to Skolem symbols.  This also deleted the local proof-term
replacement helper that existed solely for that final rewrite.

This is still not new proof coverage.  The focused checks pass, but `and3I`
continues to fail closed at the scoped Skolem/choice boundary.  The value of
the change is that the remaining failure is no longer hidden behind a local
Megalodon-side coercion; the next fix has to be a real small-kernel witness
definition transformation.

## Skolem Contract Checking Extraction, 2026-07-20

The typed Skolem branch-choice contract checks have now moved out of
`vampire_cert_v1.ml` and into `vampire_kernel_check.ml`.  The importer still
parses the fields, but the deterministic validation of branch source/target
roles, introduced-symbol membership, choice predicate/body consistency, and
witness-head aliases is now in the small-kernel checker module.

The fast kernel unit test covers both an accepted branch-choice contract and a
rejected predicate/body mismatch.  This does not increase the proof frontier:
the three original-source qualifying proofs still pass, and `and3I` still
fails closed.  The point of the change is architectural alignment with the
audit: Skolem contract validation is now part of the extracted checker, not a
private importer-side rule.

## Branch-Choice Predicate Elaboration, 2026-07-20

The Skolem branch-choice elaborator now returns an explicit
predicate/body instantiation pair instead of only returning the body and
letting `vampire_cert_v1.ml` rebuild the predicate later.  The new API rejects
metadata whose emitted predicate no longer matches the emitted body after
alias and witness-replacement rewriting.  The direct Skolem replay path uses
that emitted predicate when applying the choice theorem, and closes emitted
branch-choice metadata under the same ambient result-variable context used for
the already-closed source and target formulas.

This is an architectural tightening, not a new proof frontier.  The focused
validation passed:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_elab_unit.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_and_prefix_qualifying.sh
WORK_DIR=/project/tmp/and3I_ambient_close.1784555747 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire MEGALODON_CERT_DEBUG=1 MEGALODON_CERT_DEBUG_TIMING=1 tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
```

The first three qualifying proofs still pass.  `and3I` still fails closed; the
new artifact is `/project/tmp/and3I_ambient_close.1784555747`.  The remaining
failure is no longer a missing branch-choice selection: both `#sK0` and
`#sK1` choose emitted branch metadata.  The live-expanded candidate still
checks only with certificate-local delta and is rejected in qualifying mode,
with a proof/proposition mismatch around nested epsilon-expanded Skolem
witnesses.  The next small-kernel step should make the Skolem witness
definition itself an explicit replayed equality/transport step or avoid
producing proof terms whose validity depends on the certificate-local
`sK := Eps P` conversion.

## Branch-Choice DB Lifting, 2026-07-20

The branch-choice elaborator now has an explicit operation for lifting emitted
choice metadata across ambient result binders.  This is deliberately separate
from named-variable closing: closing can abstract named variables, but it does
not shift de Bruijn indices that are already present in Vampire-emitted
predicate/body metadata.  The body is lifted while preserving its implicit
choice argument, and the predicate is lifted through its explicit lambda.  The
kernel elaborator unit test now covers this behavior directly.

This is still a narrowing step, not a frontier increase.  The focused debug run
showed that the failing `and3I` direct choices are selected at `local_depth=0`
with `ambient_shift=0` and `ambient_shift=1`, so the remaining four-index gap
is not explained by result-step ambient lifting alone.  The new artifact is
`/project/tmp/and3I_depth_debug.1784556183`.  The next target remains explicit
transport across the certificate-local Skolem witness definition at the
returned-proof/live-check boundary.

## Post-Read Amendment, 2026-07-20

After re-reading the audit on `vampire/megalodon6`, I tested whether the
existing broad Skolem-CPS fail-fast guard could simply become part of
qualifying mode:

```text
WORK_DIR=/project/tmp/prefix4_skolem_cps_failfast.1784557025 \
TMPDIR=/project/tmp \
VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire \
MEGALODON_CERT_FAIL_FAST_SKOLEM_CPS=1 \
tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
```

That is too coarse.  It regressed the focused original-source prefix from
three reconstructed commands to one, failing already at `andEL`.  So the
correct audit response is not to flip a global debug knob and call that
determinism.  The useful narrowed invariant is:

- keep the first three qualifying proofs as the current source-bound frontier;
- keep broad CPS fail-fast as a diagnostic option only;
- do not add more Skolem heuristics in `vampire_cert_v1.ml`;
- implement the next proof step as an explicit small-kernel
  witness-transport object for `sK := Eps P`, with the transport proof
  constructed in `vampire_kernel_elab.ml` and checked through
  `vampire_kernel_check.ml`;
- make the exported proof independent of certificate-local Skolem delta
  conversion before counting `and3I` or anything after it as E1.

This also corrects the immediate interpretation of the current `and3I`
failure.  Vampire is emitting enough branch-choice metadata for the selected
Skolem witnesses, and Megalodon is selecting it.  The missing piece is not
another branch-choice matcher.  It is a scoped proof-term transport from the
epsilon witness proposition to the Skolem-symbol proposition, or an equivalent
proof construction that eliminates the Skolem symbol before the returned proof
enters live Qed checking.

## Direct Transport Rewrite, 2026-07-20

The latest `vampire/megalodon6` adjustment removes one more dependency on
temporary Skolem-symbol conversion during branch-choice cleanup.  The extracted
kernel elaborator now exposes
`skolem_witness_transport_term_replacements`, which rewrites a Vampire-emitted
local choice occurrence directly to its contract-backed definition.  The
importer uses this extracted operation when cleaning branch-choice witnesses,
instead of first replacing the local choice occurrence by a temporary `sK`
symbol and relying on a temporary delta entry for that symbol.

This is intentionally not counted as new proof coverage.  It is a soundness and
architecture cleanup in the direction requested by the audit: the deterministic
transport fact is represented in `vampire_kernel_elab.ml`, and the monolithic
importer only consumes the resulting exact rewrite list.  The focused
validation passed:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_elab_unit.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
WORK_DIR=/project/tmp/prefix4_direct_transport.1784558035 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
WORK_DIR=/project/tmp/and_prefix_direct_transport.1784558035 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_and_prefix_qualifying.sh
```

The result remains the same source-bound frontier: `FalseE`, `andEL`, and
`andER` reconstruct in qualifying mode; `and3I` fails closed.  A debug probe at
`/project/tmp/prefix4_direct_transport_debug.1784558056` confirms that the
remaining failure is the deeper proof-level mismatch: the live checker still
sees a proof application whose expected implication argument contains `#sK1`,
while the available branch-choice proof is the checked Megalodon epsilon-choice
proof over `Eps_prop (...)`.  The next change should therefore be an explicit
small-kernel proof transport for that scoped proposition, not another cleanup
or fallback.

## Proof-Side Witness Cleanup, 2026-07-20

The branch-choice transport cleanup now rewrites both the emitted local choice
occurrence and the introduced Skolem symbol to the same contract-backed
epsilon witness.  The reusable operation is
`skolem_witness_transport_proof_replacements` in `vampire_kernel_elab.ml`,
with a unit test covering the introduced-symbol rewrite.  The CPS registration
path also no longer rebuilds an epsilon witness from the raw contract source
formula when the branch-choice elaborator has already produced the proof-side
epsilon term; this avoids introducing a second, independently shifted witness
term.

Focused validation passed:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_elab_unit.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
WORK_DIR=/project/tmp/prefix4_elab_witness.1784558414 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
WORK_DIR=/project/tmp/and_prefix_elab_witness.1784558414 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_and_prefix_qualifying.sh
```

This still does not close `and3I`.  The debug artifact
`/project/tmp/prefix4_elab_witness_debug.1784558425` shows the raw
Skolem-symbol cleanup succeeds in some local refutation paths, but the
returned proof still contains a scoped proposition mismatch after live
expansion: both sides use library `not`/`Eps_prop`, but their de Bruijn depths
inside the nested predicate differ.  The next accepted change must therefore
address the branch-choice predicate lifting/closing discipline at the proof
application where the mismatch is created.

## Multi-Choice Cleanup Guard, 2026-07-20

Commit `83da761` removes an artificial restriction in the CPS branch-choice
cleanup path: a Skolem entry no longer has to be the only staged branch witness
before contract-backed local choice transports are considered.  This matters
for the active `and3I` shape, where `u30` has both `sK0` and `sK1`.

The change is still fail-closed.  Before a transport list is used, the checker
groups candidates by the actual local choice occurrence.  If a single
occurrence would be mapped to more than one distinct backed definition, that
occurrence is discarded and the proof must still pass the ordinary final
`check_propofpf` gate.  This is not a new heuristic and it does not count as a
proof frontier increase.

Focused validation:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_elab_unit.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
WORK_DIR=/project/tmp/and_prefix_multi_choice_final.1784559155 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_and_prefix_qualifying.sh
WORK_DIR=/project/tmp/prefix4_multi_choice_final.1784559155 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
```

The result remains three qualifying original-source proofs, and `and3I` still
fails closed.

I also tested a broader explicit-state experiment: storing Skolem formula-table
entries after eagerly replacing generated `#sK` symbols by their `Eps_prop`
definitions.  That is conceptually aligned with removing hidden certificate
delta state, but applying it at formula storage time is too broad and
regresses the first focused proof, `FalseE`.  The experiment was reverted.
The next work should therefore not be another global rewrite table change.  It
should be a scoped transport proof object at the direct Skolem proof
construction boundary, or richer Vampire-emitted small-kernel data from which
that transport is deterministically elaborated.

## CPS Alias Hygiene, 2026-07-20

One further bounded cleanup was made in the CPS Skolem replay path.  Witness
replacement lists are now expanded through the existing generated/native symbol
alias relation before they are applied to propositions and proofs.  This means
a replacement learned for `sK1` is also applied at the corresponding `#sK1`
occurrence, and vice versa, using the same `native_core_symbol_name_aliases`
metadata already used elsewhere.  The local existential-binder propositions
now also include fallback witness replacements, so the proposition introduced
by the local proof abstraction and the proof body use the same witness basis.

This is deliberately not counted as a proof-frontier improvement.  Focused
validation still gives the same honest result: `FalseE`, `andEL`, and `andER`
pass in qualifying mode, while `and3I` fails closed.  The `and3I` debug trace
shows that alias cleanup removes some incidental `#sK`/`sK` disagreement, but
the final failure remains the substantive scoped Skolem/choice transport
problem: a proof over Megalodon's epsilon witness is still being applied where
the expected proposition contains the certificate-local Skolem witness.  The
next accepted step should therefore be an explicit small-kernel transport for
that transformation, not another fallback or search layer.

## Extracted Transport Alias Replacement, 2026-07-20

The branch-choice transport cleanup now exposes alias-expanded proof
replacement construction from `vampire_kernel_elab.ml`.  The importer no
longer constructs only the exact introduced symbol replacement when cleaning a
contract-backed branch-choice transport; it asks the extracted elaborator for
replacement pairs covering the local choice occurrence and every alias of the
introduced Skolem name.  The unit harness now checks this behavior directly.

Focused validation passed:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_elab_unit.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
WORK_DIR=/project/tmp/and_prefix_transport_aliases.1784560771 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_and_prefix_qualifying.sh
WORK_DIR=/project/tmp/prefix4_transport_aliases.1784560771 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
```

This still does not close `and3I`.  The value of the change is that one more
piece of deterministic Skolem/choice proof cleanup has moved into the
extracted elaboration boundary with unit coverage.  The next proof-counting
milestone is unchanged: build the scoped Skolem/choice transport proof object
needed by `and3I`, rather than adding another monolithic fallback.

## Vampire-Emitted Choice Transport Body, 2026-07-20

The next adjustment moves one more Skolem/choice fact from Megalodon-side
inspection into Vampire-emitted certificate data.  Each Vampire branch-choice
record can now carry:

```text
transport_rule=choice_witness_substitution
witnessed_body=<body with replaced variable substituted by Vampire's witness>
```

Megalodon parses these fields into `skolem_branch_choice` and checks them in
`vampire_kernel_check.ml`.  A malformed transport rule, a missing witnessed
body, or a witnessed body that does not match the explicit witness
substitution is rejected before any proof cleanup runs.

This is still not a proof-counting advance.  It is a small-kernel boundary
improvement: Vampire states the source-side proposition needed for the
Skolem/epsilon transport, and Megalodon validates it deterministically.  The
remaining work is to elaborate the checked transport descriptor into a live
Megalodon proof term, not to infer it through broad OCaml search.

Focused validation:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_elab_unit.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
WORK_DIR=/project/tmp/prefix4_choice_transport.1784561533 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
WORK_DIR=/project/tmp/and_prefix_choice_transport.1784561549 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_and_prefix_qualifying.sh
```

The rebuilt Vampire binary also emitted `choice_witness_substitution` and
`witnessed_body` fields on a real THF Skolem branch-choice probe at
`/project/tmp/choice_transport_emit.1784561523`.

## Branch-Choice Selection Extraction, 2026-07-20

The latest audit-driven cleanup moves branch witness/choice selection out of
`vampire_cert_v1.ml` and into `vampire_kernel_elab.ml`.  The extracted helper
selects a branch choice from typed `skolem_branch_contract` records using the
certificate's introduced witness list and the shared generated/native alias
relation.  The importer now calls that helper from CPS Skolem replay instead
of carrying a local copy of the matching logic.

This is intentionally not a theorem-counting change.  It reduces the
monolithic importer and adds unit coverage at the deterministic elaborator
boundary.  Focused validation still reports the honest frontier:
`FalseE`, `andEL`, and `andER` pass in qualifying mode, while `and3I` fails
closed at the expected guard.

Focused validation:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_elab_unit.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_v1_metadata_audit.sh
WORK_DIR=/project/tmp/and_prefix_elab_extract.1784563483 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_and_prefix_qualifying.sh
WORK_DIR=/project/tmp/prefix4_elab_extract.1784563483 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
```

The next proof-producing step remains the same: use the already validated
Vampire-emitted `choice_witness_substitution`/`witnessed_body` data to build a
small, explicit Skolem/choice transport proof term, rather than broadening
fallback search in the importer.

## Choice Proof Constructor Extraction, 2026-07-20

The next small cleanup extracts the generic proof-term constructor for applying
Megalodon's classical choice theorem to an existential proof:

```text
exists P  ->  P (Eps P)
```

`vampire_kernel_elab.ml` now exposes `skolem_choice_witness_proof`, which
returns both the epsilon witness term and the proof obtained by applying the
typed choice theorem to the emitted predicate and the source existential
proof.  The helper rejects non-lambda predicates and wrong witness types.  The
direct Skolem formula replay and formula-orientation paths now use this helper
instead of constructing the proof term locally in `vampire_cert_v1.ml`.

This is not a proof-frontier increase.  It is another extraction step toward
the audit-requested small Skolem/choice elaborator: the primitive choice proof
operation now lives at the deterministic elaborator boundary, with unit
coverage, and the monolithic importer only supplies the theorem name, epsilon
symbol, predicate and source proof.

Focused validation:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_elab_unit.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
WORK_DIR=/project/tmp/and_prefix_choice_extracted.1784563974 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_and_prefix_qualifying.sh
WORK_DIR=/project/tmp/prefix4_choice_extracted.1784563974 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
```

The current source-bound frontier remains unchanged: three qualifying proofs
pass, and `and3I` still fails closed pending an explicit scoped
Skolem/choice transport proof.

## Explicit Choice Transport Terms, 2026-07-20

The extracted elaborator now makes the two sides of Skolem choice transport
explicit.  `vampire_kernel_elab.ml` exposes
`skolem_choice_transport_terms`, which computes:

- the Megalodon epsilon witness `Eps P`;
- the branch body instantiated with that epsilon witness;
- Vampire's emitted witnessed body, when present, normalized but kept
  separately.

The direct Skolem branch-choice replay now gets its registered epsilon witness
through this extracted helper.  This preserves current behavior, but it
removes another implicit local construction from `vampire_cert_v1.ml` and
gives the next proof-producing step a precise boundary: prove or elaborate the
transport between the epsilon-instantiated body and the Vampire
witness-instantiated body.

Focused validation:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_elab_unit.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
WORK_DIR=/project/tmp/and_prefix_transport_terms.1784564128 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_and_prefix_qualifying.sh
WORK_DIR=/project/tmp/prefix4_transport_terms.1784564128 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
```

This is still not a counted proof-frontier increase.  It is the next small
extraction required before the `and3I` scoped transport proof can be added
without broad importer search.

## CPS Result Alias Consistency, 2026-07-20

The Skolem CPS result-to-target path now applies the same witness-alias
expansion to the checked result proposition that the formula side already
uses.  This is a narrow consistency fix: it prevents the checked proof-target
comparison from seeing a less-expanded witness replacement environment than
the formula builder.

This does not change the counted frontier.  The three qualifying original
source reconstructions still pass, and the fourth theorem (`and3I`) still
fails closed at the expected guard.  The remaining work is still the explicit
scoped Skolem/choice transport proof between the epsilon-instantiated body and
Vampire's witnessed body.

Focused validation:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_elab_unit.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
WORK_DIR=/project/tmp/and_prefix_alias_checked.1784564318 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_and_prefix_qualifying.sh
WORK_DIR=/project/tmp/prefix4_alias_checked.1784564318 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
```

## Existential Binder Accounting Extraction, 2026-07-20

The Skolem CPS path no longer performs its own local recursive scan to count
and type `vampire_exists_prop` binders.  That structural certificate
inspection is now exposed by `vampire_kernel_elab.ml` as
`term_exists_head_types` and `term_exists_head_count`, with unit tests for
nested conjunction/implication shapes.

This is an audit-aligned extraction, not a new proof-frontier claim.  It
removes another deterministic Skolem bookkeeping operation from
`vampire_cert_v1.ml` and puts it behind the small elaborator boundary.  The
frontier remains the same: three qualifying original-source reconstructions
pass and `and3I` still fails closed until the scoped Skolem/choice transport
proof is made explicit.

Focused validation:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_elab_unit.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
WORK_DIR=/project/tmp/and_prefix_exists_extract.1784564519 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_and_prefix_qualifying.sh
WORK_DIR=/project/tmp/prefix4_exists_extract.1784564520 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
```

## Fixed-Basis Alias Normalization, 2026-07-20

The latest `and3I` diagnostic narrowed one more class of false failures before
the real scoped transport mismatch.  Native replay can see both hashed and
unhashed names for fixed logical basis objects and branch witnesses, for
example `vampire_exists_prop_choice`/`#vampire_exists_prop_choice`,
`Eps_prop`/`#Eps_prop`, and `sK0`/`#sK0`.  The checker previously treated
some of these aliases consistently for source symbols but not for fixed
logical `Known`s, term symbol types, or temporary branch-choice delta entries.

The branch now installs the approved native proof delta, native term-symbol
table, fixed logical `Known` guard, and temporary branch-choice delta under the
same alias policy.  The temporary branch-choice delta remains transactional:
all aliases are saved before checking and restored if the candidate is
rejected.  This is not a theorem-specific repair and does not add any broad
fallback route.

The focused `and3I` diagnostic now gets past the earlier missing
`#vampire_exists_prop_choice`/`#Eps_prop` extraction failure.  The remaining
failure is more precise: the candidate is choice-free and has no unbacked
introduced symbols, but a scoped branch proof still supplies a proposition at
`#sK0` where the choice theorem application expects the corresponding
epsilon-instantiated body.  That is the explicit scoped Skolem/choice
transport proof that still needs to be implemented, preferably in
`vampire_kernel_elab.ml` rather than by adding another importer search path.

Focused validation:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_elab_unit.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
WORK_DIR=/project/tmp/and_prefix_temp_alias.1784565717 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_and_prefix_qualifying.sh
WORK_DIR=/project/tmp/prefix4_temp_alias.1784565717 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
```

## Branch-Transport Replacement Priority, 2026-07-20

A focused `and3I` probe showed that branch-choice transports and the older
registered-witness cleanup can point in opposite directions.  The branch
contract justifies replacing an introduced Skolem symbol by its scoped epsilon
definition, while the registered cleanup may replace the exact epsilon witness
back by the introduced symbol.  Sorting both replacement lists together hides
that conflict and lets the importer decide priority implicitly.

The replacement-priority policy has now moved into
`Vampire_kernel_elab.prioritized_skolem_witness_transport_proof_replacements`.
Explicit branch transports shadow registered reverse replacements for the same
witness aliases, while unrelated registered witnesses are still kept.  The
unit harness checks both cases directly.

This is not counted as new proof coverage.  The focused gates still report the
same honest frontier:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_elab_unit.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
WORK_DIR=/project/tmp/prefix4_elab_priority.1784566866 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
WORK_DIR=/project/tmp/and_prefix_elab_priority.1784566877 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_and_prefix_qualifying.sh
```

`FalseE`, `andEL`, and `andER` remain the only qualifying original-source
passes; `and3I` remains fail-closed at the scoped Skolem/choice proof
boundary.

## Extracted Church-Exists Map Proof, 2026-07-20

The scoped Skolem/choice boundary will need explicit transport between
existential predicates.  Earlier code had textual and importer-local versions
of this idea, but the extracted elaborator did not expose a reusable proof-term
constructor for Church-encoded existential mapping.

`Vampire_kernel_elab.church_exists_map_proof` now builds the proof term for
mapping `exists P` to `exists Q` from a pointwise proof `forall x, P x -> Q x`.
The Skolem CPS formula-transport function uses this constructor for matching
`vampire_exists_prop` structures.  The unit harness checks the generated proof
shape directly.

This still does not close `and3I`.  A focused debug run at
`/project/tmp/and3I_exists_map_debug_1784567215` shows the current bad
application remains at the choice-premise boundary (`expected Eps_prop`,
`actual #sK0`), before this existential map case can discharge the mismatch.
The change is therefore counted as proof-term infrastructure only.

Focused validation:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_elab_unit.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
WORK_DIR=/project/tmp/prefix4_exists_map.1784567181 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
WORK_DIR=/project/tmp/and_prefix_exists_map.1784567199 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_and_prefix_qualifying.sh
```

## Transport-Symbol Bad-Application Diagnostics, 2026-07-20

The final refutation checker now reports the first choice/Skolem transport
symbol found on each side of a bad proof application.  This is debug-only
instrumentation, but it removes ambiguity in the current `and3I` failure.

A focused probe at
`/project/tmp/and3I_transport_symbols_debug_1784567604` shows the failing
application precisely:

```text
expected transport symbol ... Eps_prop in (#Eps_prop ...)
actual transport symbol ... #sK0 in ((_0 (forall _:prop, (_0 -> _0))) ##sK0)
```

So the remaining failure is not missing branch-choice metadata, not missing
fixed-basis aliases, and not only an exact epsilon occurrence that can be
rewritten globally.  The proof argument itself is still typed at the
certificate Skolem witness while the choice theorem expects the epsilon
witness.  The next implementation step must construct a local proof transport
for that argument or build the branch proof directly at the epsilon
proposition.

## No Certificate-Local Witnesses In Cleaned Proofs, 2026-07-20

The latest `and3I` diagnostic found a stricter fail-closed issue in the
Skolem-CPS cleanup acceptance predicate.  The cleaned candidate was rejected by
the final checker, but the pre-check guard only rejected unbacked introduced
Skolem symbols.  A backed symbol such as `#sK0` could therefore survive the
cleanup guard and rely on a temporary certificate definition during the later
check.  That is exactly the hidden-state shape the audit warned against.

Qualifying cleanup now rejects every introduced witness alias in the cleaned
proof, not only unbacked aliases.  The debug output also distinguishes two
cases:

- an introduced symbol remains and a direct symbol replacement exists, which
  would indicate a traversal/replacement bug;
- an introduced symbol remains without any direct replacement, which indicates
  that the current certificate only has the reverse registered-witness cleanup
  (`Eps_prop(...) -> #sK0`) and still lacks the explicit small-kernel transport
  proof needed to eliminate the certificate-local Skolem symbol.

A focused probe at
`/project/tmp/and3I_direct_replacement_debug_1784568167` showed the second
case for `and3I`: the registered cleanup had no direct replacement for the
escaping `#sK0`.  The frontier is therefore unchanged, but the failure is now
more honest and more audit-aligned: the next fix must be a real scoped
Skolem/choice transport proof in the extracted elaborator, not acceptance of a
justified local symbol.

Focused validation:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_elab_unit.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
WORK_DIR=/project/tmp/and_prefix_no_local_symbols.1784568292 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_and_prefix_qualifying.sh
WORK_DIR=/project/tmp/prefix4_no_local_symbols.1784568292 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
```

## Introduced-Witness Classification Extraction, 2026-07-20

The next focused `and3I` probe at
`/project/tmp/and3I_transport_classify_1784568409` confirmed the cleanup
orientation problem more precisely.  The surviving `#sK0` is not an original
unreplaced symbol in the candidate; it is introduced by the reverse
registered-witness cleanup that rewrites an exact epsilon witness back to a
certificate-local Skolem symbol.

I also tested a temporary direct-epsilon expansion experiment at
`/project/tmp/and3I_direct_eps_experiment_1784568578`.  That experiment removed
the introduced symbol but failed at a deeper scoped boundary: a proof branch
expected a locally bound witness variable while the globally expanded proof
contained `Eps_prop(...)`.  The experiment was reverted.  The result is useful
because it rules out global `#sK -> Eps` substitution as the next qualifying
fix; the proof has to be rebuilt or transported at the scoped branch
continuation.

The durable code change is an extraction:
`Vampire_kernel_elab.classify_introduced_symbol_replacements` now owns the
deterministic classification of introduced witness aliases that are present in
a proof, those with direct symbol replacements, and those without direct
replacements.  `vampire_cert_v1.ml` uses this helper only for diagnostics and
fail-closed classification; it does not add a new search path or relax the
qualifying guard.

Focused validation:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_elab_unit.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
WORK_DIR=/project/tmp/and_prefix_classify_extract.1784568842 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_and_prefix_qualifying.sh
WORK_DIR=/project/tmp/prefix4_classify_extract.1784568842 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
```

## Church-Exists Eliminator Extraction, 2026-07-20

The scoped `and3I` failure occurs exactly at a Church-encoded existential
continuation boundary.  The CPS replay path was still constructing that
boundary inline as:

```ocaml
PPfAp (PTmAp (exists_proof, target_prop), continuation)
```

That construction now lives in the extracted elaborator as
`Vampire_kernel_elab.church_exists_elim_proof`, with a unit test for the proof
shape.  `vampire_cert_v1.ml` calls the helper from the Skolem-CPS exists case.

This is intentionally behavior-preserving: the focused gates still accept the
first three original-source hammer proofs and fail closed at `and3I`.  The
benefit is architectural.  The exact proof-term operation that must receive the
next scoped witness transport is now isolated in the small elaborator module
instead of being embedded directly in the importer.

Focused validation:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_elab_unit.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
WORK_DIR=/project/tmp/and_prefix_exists_elim_extract.1784569037 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_and_prefix_qualifying.sh
WORK_DIR=/project/tmp/prefix4_exists_elim_extract.1784569038 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
```

## Skolem Witness Cleanup Planning Extraction, 2026-07-20

The latest focused `and3I` diagnostic at
`/project/tmp/and3I_scoped_elab_diag_1784569258` confirmed that the remaining
failure is still at `u30`: Vampire emits branch-choice contracts, Megalodon can
consume them, but the final cleanup plan leaves a nested certificate-local
choice/witness occurrence.  The proof still fails closed; it is not counted as
new E1 coverage.

The code change in this step moves the deterministic cleanup planning out of
`vampire_cert_v1.ml` and into `Vampire_kernel_elab`:

- ambiguous branch-choice transport occurrences are identified and removed by
  `disambiguate_skolem_witness_transports`;
- transport-backed replacements and registered-witness replacements are
  combined by `skolem_witness_cleanup_plan`;
- introduced-witness alias classification is returned by the same plan.

The importer still performs the final live Megalodon proof check, because that
depends on the current theorem environment, but it no longer owns the
certificate-local Skolem/choice cleanup decision.  This is intentionally
behavior-preserving and audit-aligned: no new search path was added, no
certificate-local global definitions are accepted, and the current qualifying
frontier remains the first three original-source hammer proofs (`FalseE`,
`andEL`, `andER`) with `and3I` failing closed.

Focused validation:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_elab_unit.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
WORK_DIR=/project/tmp/and_prefix_cleanup_plan_1784569455 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_and_prefix_qualifying.sh
WORK_DIR=/project/tmp/prefix4_cleanup_plan_1784569455 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
```

## Unique Registered Choice Expansion Extraction, 2026-07-20

The importer still contained one more pure Skolem/choice cleanup search:
detecting whether a cleaned proof had exactly one unresolved registered
choice witness, collecting the local choice terms under binder depth, and
building the replacement list.  That operation is now extracted to
`Vampire_kernel_elab.unique_registered_choice_expansion_plan`.

The extracted helper reports three deterministic cases: no expansion,
ambiguous unresolved names, or a unique expansion with the canonical witness
name, local choice terms, and replacement list.  `vampire_cert_v1.ml` only
applies the returned replacements and performs the live final proof check.

This remains behavior-preserving.  The first three original-source hammer
proofs still qualify, and `and3I` still fails closed.  The value of this step
is architectural: another piece of Skolem/choice witness reasoning has moved
from the importer into the extracted elaborator where it can be reviewed and
tested independently.

Focused validation:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_elab_unit.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
WORK_DIR=/project/tmp/and_prefix_unique_choice_extract_final_1784569856 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_and_prefix_qualifying.sh
WORK_DIR=/project/tmp/prefix4_unique_choice_extract_final_1784569838 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
```

## Branch-Choice Template Plan Extraction, 2026-07-20

A bounded diagnostic with `MEGALODON_CERT_BRANCH_CHOICE_TEMPLATE_LIMIT=12` at
`/project/tmp/and3I_template_limit_probe_1784570013` confirmed that the old
template-expansion path is not the missing `and3I` proof.  It fails at the
same conceptual boundary: the proof checker expects the locally bound witness
variable, while the expanded candidate contains a certificate-local
`Eps_prop(...)`.  I therefore did not enable or count that path.

The durable change is another extraction from `vampire_cert_v1.ml`:
`Vampire_kernel_elab.skolem_branch_choice_template_expansion_plan` now owns
the pure work of selecting local branch-choice templates under a configured
limit and expanding replacement-name aliases.  The importer still only applies
a returned template and runs the live final proof check.

This does not change the qualifying frontier.  It removes another piece of
Skolem/choice planning from the monolithic importer and records that the
current template path is diagnostic only, not a solution for scoped
Skolem/choice transport.

Focused validation:

```text
TMPDIR=/project/tmp ./makeopt
TMPDIR=/project/tmp tests/vampire_certificate/run_kernel_elab_unit.sh
TMPDIR=/project/tmp tests/vampire_certificate/run_vampireaby_qualifying_guards.sh
WORK_DIR=/project/tmp/and_prefix_template_plan_extract_retry_1784570439 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_and_prefix_qualifying.sh
WORK_DIR=/project/tmp/prefix4_template_plan_extract_retry_1784570420 TMPDIR=/project/tmp VAMPIRE=/project/tmp/vampire-cmake-megalodon6/vampire tests/vampire_reconstruction/run_live_hammer_prefix4_failclosed_qualifying.sh
```
