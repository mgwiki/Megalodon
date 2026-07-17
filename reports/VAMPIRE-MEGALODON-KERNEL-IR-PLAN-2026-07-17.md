# Vampire to Megalodon Kernel IR Plan

Date: 2026-07-17

Branch: `vampire/megalodon5`

This note is the post-audit execution plan for the Prover9/Ivy-style path.
It supersedes any milestone ordering that tried to raise broad
`preprocesspfcheck` pass counts before removing certificate-derived
`Known` propositions.

## Audit Position

The July 16 audit is accepted.

The project should not be judged by:

- strict live certificate passes that only validate metadata and source maps;
- preprocessing proof-term passes that install certificate-derived `Known`
  implications;
- Python reconstruction or generated proof scripts;
- broad OCaml replay growth in `vampire_cert_v1.ml`.

The qualifying path is:

```text
Vampire primitive certificate IR
  -> canonical S-expression certificate
  -> Megalodon small-kernel parser/checker
  -> native Syntax.pf proof terms
  -> composition with the original Megalodon theorem context
```

## Current Enforced Boundaries

The branch already has several mechanical gates:

- counted native proof-term checking rejects certificate-derived `Known`
  names with the `vampire_` prefix, except for the fixed reviewed logical
  basis such as choice and not-forall/existence principles;
- the old transitional preprocessing behavior is opt-in only through
  `MEGALODON_CERT_ALLOW_TRANSITIONAL_PREPROCESS_KNOWN=1` and is structural
  diagnostic evidence only;
- `Vampire_kernel_syntax` defines the shared schema,
  primitive-contract rules, structural migration rules, and supported rule
  names;
- source-context checking distinguishes global knowns, local hypotheses,
  definitional facts, generated facts, unresolved facts, and set-reflexivity
  obligations;
- strict source-context checking accepts matched local definitions as matched
  source facts, but does not count them as discharged proof obligations unless
  a proof term is supplied.

On the Vampire side, `Shell/MegalodonChecker/MegalodonKernelSyntax.*` is now
the intended vocabulary boundary for `kernel_v1` metadata. It is still a
rendering/checkpoint layer, not yet the full internal primitive proof IR.

## The Small Kernel

The stable clausal kernel should stay small:

- `input`: boundary step from a proved source/preprocessing clause;
- `instantiate`: explicit substitution instance;
- `resolve`: binary resolution;
- `factor`: duplicate literal contraction;
- `equality_resolution`: contradiction from a negative reflexive equality;
- `equality_factoring`: equality-specific factor;
- `paramodulate`: equality rewriting at an explicit position;
- `contradiction`: final empty-clause marker.

Two names need special treatment:

- `rename` should be checked as alpha-conversion or incorporated into
  `instantiate`, not grown into a broad logical rule.
- `truth_conflict` belongs in the FOOL/source-preprocessing layer unless a
  real clausal proof demonstrates that it must be primitive.

AVATAR is outside the first small clausal kernel milestone. It should later be
lowered through explicit SAT/RUP-style objects or through a separately checked
AVATAR layer, not hidden inside an arbitrary bridge theorem.

## Vampire IR Requirement

The next Vampire-side target is an internal typed list of primitive proof
steps before printing:

```text
struct MegalodonPrimitiveStep {
  id;
  rule;
  parent ids;
  conclusion clause/formula;
  selected literal/equality indices;
  rewrite position and direction;
  substitution;
  variable and symbol sorts;
  source/preprocess payload when rule is not clausal;
}
```

The exact C++ type names can differ, but the implementation rule is fixed:

- macro inference handlers build primitive records first;
- one canonical printer serializes those records;
- direct string assembly in individual inference cases is migration-only;
- every macro that remains as `kernel_v1` metadata must declare its
  `primitive_expansion_requires` contract;
- unsupported `kernel_v1` rule names must fail closed in Vampire before the
  certificate is printed.

The first macro-lowering target should be unit-resulting resolution because it
has frequent live coverage and lowers naturally to a chain of binary
`resolve` steps.

## Megalodon Checker Requirement

Megalodon should consume the primitive IR as explicit proof data. It should
not infer missing positions, pivots, substitutions, sorts, or source facts by
search.

New qualifying Megalodon work should go into isolated modules:

- `vampire_kernel_syntax.ml`: shared rule names and contracts;
- `vampire_kernel_check.ml`: structural/kernel certificate checks;
- `vampire_kernel_elab.ml`: `Syntax.pf` elaboration for primitive steps;
- `vampire_source_context.ml`: original-context source proof resolution.

`vampire_cert_v1.ml` remains a legacy parser/oracle until the extraction is
complete. It should not be the place where new broad reconstruction power is
added.

## Source Context Contract

The original-context boundary should expose a concrete API:

```ocaml
type source_proof =
  | GlobalKnown of string * Syntax.tm
  | LocalHyp of int * Syntax.tm
  | Definitional of Syntax.tm * Syntax.pf
  | Generated of Syntax.tm * Syntax.pf
  | Unresolved of string * Syntax.tm

type source_context = source_id -> source_proof
```

Global theorems and lemmas must resolve to existing Megalodon known hashes.
Local hypotheses must be resolved against the current proof context, including
the index shifts introduced by local `set` definitions. Set-generated
equalities without corresponding claims must be proved by reflexivity or
conversion. The negated conjecture must be discharged only at the final
refutation-to-goal composition boundary.

## Smolka-Style Transformation Contract

Source-to-clause transformations are not clausal-kernel rules. They form a
separate proof-producing layer:

- source input and formula-term input;
- definition input/fold/unfold;
- rectification;
- FOOL Boolean lifting and exhaustiveness;
- ENNF;
- CNF literal/formula projection;
- Skolemization with explicit introduced symbols, dependencies, sorts, and
  choice principle.

Each transformation must either produce a checked `Syntax.pf` or be rejected
in counted mode. Transitional `Known` implications are permitted only in
structural diagnostics and must be reported as such.

## Evidence Classes

Use evidence classes, not ambiguous "tiers":

- E1: original Megalodon theorem reconstructed with no `admit`, no `aby`, no
  bridge assumptions, and no certificate-derived `Known`.
- E2: closed native `Syntax.pf` proof of a live Vampire certificate, still
  exported-THF-bound.
- E3: synthetic or focused primitive-kernel native proof-term checks.
- E4: structural certificate/source/metadata validation only.

The strict live 100 run is E4. Old preprocessing-frontier runs with
transitional knowns are E4. The small native core proof-term tests are E3
unless they are live exported proofs that also pass the closed proof-term gate.

## Next Gates

1. Keep all counted proof-term modes free of certificate-derived `Known`.
2. Make Vampire reject unsupported `kernel_v1` rule names at emission time.
3. Lower URR to explicit primitive `resolve` records and keep the macro record
   only as migration metadata.
4. Extract the Megalodon primitive checker/elaborator out of
   `vampire_cert_v1.ml` without adding new replay power during the move.
5. Prove ten live non-synthetic exported certificates through E2.
6. Compose ten source-linked certificates back into the original Megalodon
   theorem context as E1.
7. Only after that, rerun a fresh 100-theorem held-out gate.

This is intentionally stricter than the earlier pass-count-oriented plan. It
prioritizes a small auditable proof object over broader but non-qualifying
frontier numbers.

## 2026-07-17 URR Increment

The URR migration step is now more explicit: when Vampire can lower a
`unit_resulting_resolution` inference to primitive certificate steps, the
corresponding `kernel_v1` macro metadata must include the primitive expansion
chain summary:

- `primitive_expansion_step_count`;
- ordered `primitive_expansion_step_N_rule` / `primitive_expansion_step_N_id`;
- `primitive_expansion_requires_count`;
- at least one `primitive_expansion_step_N_rule=resolve`;
- at least one `primitive_expansion_requires_N=resolve`.

The focused kernel metadata audit requires those fields for every emitted URR
macro record. This still does not make URR a completed Megalodon `Syntax.pf`
macro proof by itself; it makes the Vampire-side lowering contract visible and
checkable so the Megalodon elaborator can consume the primitive chain instead
of relying on a broad URR replay rule.
