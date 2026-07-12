# Vampire to Megalodon Certificate Specification

Status: draft MVP

Date: 2026-07-12

## Purpose

This document defines the replacement proof-reconstruction path for
`vampire/megalodon1`.

The previous prototype exported rich Vampire internals and used a large Python
script to reconstruct many different proof patterns. That path is now treated
as diagnostic infrastructure. The implementation target is a small, versioned
certificate calculus that Vampire can emit and Megalodon can elaborate
mechanically.

## Non-Goals for the MVP

The MVP intentionally excludes:

- AVATAR and SAT split explanations,
- higher-order lambda/de-Bruijn rewriting,
- direct demodulation replay,
- direct hyper-resolution or unit-resulting resolution replay,
- library-specific source proof search,
- `aby`, `admit`, and `-allowincompleteqed` in accepted final proofs.

Those features may be added later only after the restricted calculus produces a
real no-admit suite.

## Trust Boundary

Vampire and the importer are untrusted. The importer may reject malformed
certificates early, but success is counted only when Megalodon kernel-checks the
generated proof without admissions.

The importer must not search for missing logical arguments. It may:

- parse terms, clauses, substitutions, and parent references,
- verify syntactic side conditions for certificate constructors,
- instantiate the exact substitutions supplied by the certificate,
- elaborate each constructor to a fixed Megalodon proof-term template.

It must not:

- discover missing pivots,
- guess substitutions,
- invoke library-specific theorem search,
- repair malformed clauses,
- count admitted skeleton checks as proof reconstruction.

## File Format

The initial interchange format is JSON. It is deliberately boring and
versioned.

```json
{
  "format": "vampire-megalodon-certificate",
  "version": 1,
  "problem": "optional-problem-id",
  "steps": [
    {
      "id": "c1",
      "rule": "input",
      "clause": [
        {"polarity": true, "atom": "P(a)"}
      ],
      "source": {"kind": "axiom", "name": "H1"}
    }
  ]
}
```

Literals have:

- `polarity`: `true` for positive, `false` for negative,
- `atom`: either an opaque string for propositional smoke tests or a structured
  atom object.

Structured terms are:

```json
{"var": "x"}
{"const": "a"}
{"app": "f", "args": [{"var": "x"}]}
```

Structured atoms are:

```json
{"pred": "P", "args": [{"const": "a"}]}
{"eq": [{"var": "x"}, {"var": "x"}]}
```

The prototype checker still accepts opaque atom strings for the first
propositional smoke certificates, but first-order certificates should use the
structured form.

## MVP Constructors

### `input`

Introduces a clause from the THF problem/source map.

Required fields:

- `id`
- `rule: "input"`
- `clause`
- `source`

Megalodon elaboration:

- use an explicit source-map reference,
- for generated `set` facts, use reflexivity/unfolding,
- for conjecture negation, use the generated theorem context.

### `rename`

Alpha-renames variables or reorders a clause.

Required fields:

- `parents`: one parent,
- `renaming`: object from old variable names to new variable names,
- `clause`.

Megalodon elaboration:

- lambda/forall alpha conversion and clause permutation.

### `substitute`

Applies an explicit first-order substitution.

Required fields:

- `parents`: one parent,
- `substitution`: object from variable names to structured terms,
- `clause`.

Side condition:

- the listed clause must equal the parent clause after the exact substitution,
  modulo clause normalization.

### `resolve`

Binary resolution.

Required fields:

- `parents`: two parents,
- `pivot`: a literal object,
- `clause`.

Side condition:

- parent 1 contains `pivot`,
- parent 2 contains the complement of `pivot`,
- the conclusion is the union of the two parent clauses with the pivot pair
  removed, modulo duplicate deletion and clause ordering.

Megalodon elaboration:

- case/analyze the pivot disjunction from parent 1,
- use parent 2's complementary pivot branch to close the resolved branch,
- rebuild the target disjunction.

### `factor`

Duplicate literal deletion.

Required fields:

- `parents`: one parent,
- `clause`.

Side condition:

- the conclusion is the duplicate-free parent clause, modulo ordering.

### `equality_resolution`

Removes a negative reflexive equality literal.

Required fields:

- `parents`: one parent,
- `literal`: the equality literal being removed,
- `substitution`: object from variable names to structured terms,
- `clause`.

Side condition:

- the selected literal is syntactically negative equality of a term with
  itself after the supplied substitution.
- the conclusion is the parent clause after applying the substitution and
  removing that selected literal, modulo clause normalization.

### `paramodulate`

First-order equality replacement.

Required fields:

- `parents`: equality parent and target parent,
- `equality`: selected positive equality literal from the equality parent,
- `from`: selected equality side,
- `to`: selected replacement side,
- `target`: selected literal from the target parent,
- `position`: target position,
- `substitution`,
- `clause`.

Side condition:

- the equality parent contains `equality`,
- the target parent contains `target`,
- `equality` is positive and becomes `from = to` after the exact substitution,
- the selected target position contains `from` after the exact substitution,
- replacing that selected occurrence by `to`, and retaining all other
  substituted parent literals except the selected equality and target literals,
  yields the conclusion modulo clause normalization.

Demodulation must be expanded to this constructor in the MVP.

### `reflexive_simplify`

Definitional/reflexive simplification only.

Allowed cases:

- `t = t`,
- proposition extensionality over identical propositions,
- unfolding a source-mapped `set` definition.

This constructor must remain small. It is not a general simplifier.

### `contradiction`

Concludes false from an empty clause.

Required fields:

- `parents`: one parent,
- `clause`: `[]`.

Side condition:

- the parent clause is empty.

## Deferred Macro Constructor: `skolemize`

Skolemization is not part of the first MVP, but it should be the first macro
after the restricted resolution fragment works.

Required data when added:

- before formula,
- after formula,
- complete quantifier prefix,
- sorts,
- dependency vector,
- generated symbol,
- choice/epsilon principle used,
- source-map context.

The importer must not infer dependencies from generated names.

## Explicitly Deferred: AVATAR

AVATAR is disabled in the first qualifying Vampire schedule. Later it should be
represented by a separate propositional certificate layer, for example a small
resolution proof or LRAT-like object, connected to first-order split clauses.

The focused `hammer.981.15` issue around `S296` is an example of why AVATAR is
not in the MVP: SAT-level nullary split propositions and first-order component
predicates must be represented separately.

## Testing Gates

Every new constructor requires:

- at least one positive hand-written certificate,
- at least one malformed schema test,
- at least one invalid side-condition test,
- one Megalodon elaboration test without `admit`, `aby`, or
  `-allowincompleteqed`.

Project-level success gates:

1. 20 hand-written certificate tests.
2. 10 real no-admit Megalodon reconstructions in the restricted fragment.
3. 100 real no-admit Megalodon reconstructions before AVATAR or higher-order
   replay is reintroduced.

## Current Prototype Elaboration

`scripts/vampire_certificate.py --emit-megalodon OUT.mg` currently elaborates
the opaque propositional subfragment to a Megalodon proof script:

- `input` clauses become theorem assumptions,
- `resolve`, `factor`, and `contradiction` become local `claim`s,
- the final empty clause proves `False`.

This first elaborator is intentionally limited to opaque propositional atoms.
It is a no-admit kernel-checking smoke path, not yet the first-order
Megalodon importer.
