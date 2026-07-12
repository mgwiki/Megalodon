# Response to `audit-REPORT-2026-07-12.md`

Date: 2026-07-12

## Summary

I agree with the audit's central criticism. The current rich-export plus
Python-reconstructor line should be treated as a prototype, not as the
implementation path to the final 100-proof no-admit goal.

The prototype produced useful assets:

- source-linked proof DAGs,
- benchmark corpora and cached Vampire outputs,
- examples of missing proof data,
- source-map requirements,
- skolemization and AVATAR failure modes,
- concrete Megalodon syntax/proof-term lessons.

But the current Python script has crossed the line from translator into a
large heuristic prover. Continuing to add inference recognizers there is not a
convergent plan.

## Decision

On branch `vampire/megalodon1`, the new primary path is a small, versioned
certificate calculus:

- Vampire should export normalized proof steps in that calculus.
- The Megalodon importer should check references, substitutions, pivots, and
  constructor shape, then elaborate each constructor mechanically.
- The Megalodon kernel remains the only final proof checker.
- Existing admitted skeleton generation remains a prototype/debug artifact.

This means the focused `hammer.981.15` work is no longer the milestone for
success. It remains a regression and diagnostic example, but not a reason to
keep adding shape-specific reconstruction logic.

## Immediate Adjustments

The branch now adds:

- `reports/vampire-megalodon-certificate-spec.md`, a first specification of
  the restricted certificate format and staged feature gates.
- `scripts/vampire_certificate.py`, a small certificate linter/checker for the
  first resolution/factoring/contradiction fragment.
- `tests/vampire_certificate/`, including positive and negative smoke tests.

The initial checker deliberately handles only a tiny fragment. That is the
point: each new constructor must be specified, negatively tested, and then
elaborated into Megalodon terms before it is counted as progress.

## Policy Changes

The following policy changes are now in force for this branch:

1. Source-context skeleton checks with `admit` are plumbing checks, not proof
   reconstruction successes.
2. No broad result counts should mix admitted skeletons with no-admit kernel
   checks.
3. No new library-specific proof search should be added to
   `scripts/vampire_reconstruct_megalodon.py`.
4. Any new Vampire metadata should be for a stable certificate constructor, not
   a one-off field for the latest benchmark failure.
5. AVATAR and higher-order lambda/de-Bruijn replay are out of the initial
   qualifying fragment.
6. Demodulation, hyper-resolution, and unit-resulting resolution should first
   be expanded into the small calculus rather than replayed directly.

## Recovery Gates

The next concrete gates are:

1. Expand the certificate checker from propositional resolution to first-order
   clauses with explicit substitutions.
2. Add malformed-substitution and invalid-pivot negative tests for every rule.
3. Make Vampire emit this small certificate format for a restricted
   non-AVATAR/non-HO-heavy schedule.
4. Elaborate the accepted certificate steps into Megalodon proof terms.
5. Obtain 10 real no-admit Megalodon reconstructions in the restricted
   fragment.
6. Only then scale to 100 no-admit reconstructions before adding skolemization
   or AVATAR.

## Comment on the Previous Report

The previous report should be read as a prototype postmortem, not as a defense
of continuing the same implementation. The better conclusion is:

> The rich-export experiment identified necessary source-linking and proof-data
> requirements, but the current exporter/reconstructor pair is not a convergent
> implementation. The project should pivot to a normalized small certificate
> calculus, closer to Prover9/Ivy, with a Smolka-style target-side elaborator.

