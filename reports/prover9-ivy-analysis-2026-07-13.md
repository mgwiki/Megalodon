# Prover9 Ivy Proof-Object Analysis

Date: 2026-07-13

## Source

The Prover9/LADR source is available locally at `/project/prover9-ladr`.
It is a git checkout of `https://github.com/ai4reason/Prover9.git`, currently
at commit `cdca95a` (`fix: change the precedence of "~" back`).

The relevant files are:

- `apps.src/prooftrans.c`
- `ladr/xproofs.c`
- `ladr/ivy.c`
- `ladr/ivy.h`
- `ladr/just.c`
- `ladr/paramod.c`
- `ladr/demod.c`

## Main Finding

Prover9's Ivy export is not a pretty-printer for the native Prover9 proof.
It is a prover-side proof elaborator. It takes Prover9's compact proof
justifications, replays/expands them with Prover9's own clause machinery, and
prints a lower-level proof object in a small Ivy vocabulary.

That is exactly the pattern we want for Vampire/Megalodon: Vampire should emit
small, explicit, locally checkable certificate steps, and the Megalodon-side
translator/checker should mostly validate and render them. It should not
rediscover pivots, substitutions, positions, hidden split literals, or
orientation choices in Python.

## Entry Point

`prooftrans ivy` is selected in `apps.src/prooftrans.c`. When the `ivy` argument is
present, the program sets `transformation = EXPAND_IVY` and `output_format =
IVY` at lines 258-262.

The transformation itself is at lines 431-433:

```c
Plist proof2 = expand_proof(proof, &jmap);
Plist proof3 = expand_proof_ivy(proof2);
```

So the exported Ivy proof is produced in two stages:

1. `expand_proof` in `ladr/xproofs.c`
2. `expand_proof_ivy` in `ladr/ivy.c`

## Stage 1: Expand Prover9 Proofs

`expand_proof` is documented at `ladr/xproofs.c:239-247`: it returns a more
detailed proof and also returns a map from new intermediate IDs to the old proof
step and substep index.

This first stage keeps the proof in Prover9/LADR terms but makes implicit
substeps explicit:

- Hyper/UR/binary resolution are expanded into a sequence of binary resolution
  steps at `ladr/xproofs.c:312-343`.
- Paramodulation is replayed at the recorded positions using `para_pos` at
  `ladr/xproofs.c:345-353`.
- Factorization is replayed at `ladr/xproofs.c:355-364`.
- Equality resolution against reflexivity is replayed at `ladr/xproofs.c:366-374`.
- Demodulation secondary justifications are converted into paramodulation-like
  steps with explicit from/into positions at `ladr/xproofs.c:397-418`.
- Equality flips are made explicit at `ladr/xproofs.c:420-431`.
- Merge, unit deletion, and `x=x` simplification are expanded at
  `ladr/xproofs.c:436-480`.

The important discipline is at `ladr/xproofs.c:495-503`: after expansion,
Prover9 checks that the expanded current clause is identical to the original
clause. That prevents the proof exporter from silently drifting away from the
native prover proof.

## Stage 2: Lower To Ivy Primitives

`expand_proof_ivy` starts at `ladr/ivy.c:704`. It first copies the expanded
proof and renames symbols for Ivy, then walks the proof and replaces remaining
LADR justifications with Ivy justifications.

The Ivy printer supports only these primitive proof reasons in
`sb_ivy_write_just` at `ladr/ivy.c:217-263`:

- `input`
- `propositional`
- `new_symbol`
- `flip`
- `instantiate`
- `resolve`
- `paramod`

Each printed clause contains:

- the new clause ID;
- the primitive justification;
- parent IDs;
- positions where relevant;
- substitution pairs where relevant;
- the resulting clause.

This is a deliberately small target language. Prover9 does not export
"superposition", "demodulation", "unit result resolution", etc. as opaque
rules for Ivy to understand. It elaborates them into primitive operations.

As a concrete reference artifact, I ran:

```sh
/project/prover9-ladr/bin/prooftrans ivy \
  -f /project/prover9-ladr/apps.src/test-directproof/3.1.out \
  > /project/tmp/prover9-ivy/3.1.ivy
```

The first proof object shows the intended primitive trace shape:

```lisp
(48 (instantiate 24 ((v0 . (A)) (v1 . (B)) (v2 . (B)))) ...)
(44A (paramod 48 (1) 43 (1 1)) ...)
(49 (instantiate 18 ((v0 . (B)))) ...)
(44B (paramod 49 (1) 44A (1 1 2)) ...)
(51 (instantiate 0 ((v0 . (one_for_ivy)))) ...)
(44 (resolve 44C () 51 ()) false NIL)
```

## Explicit Instantiation

`instantiate_inference` is at `ladr/ivy.c:298-307`. It builds an instantiated
copy of a clause, extracts variable-to-term pairs with `context_to_pairs`, and
records an Ivy `instantiate` justification:

```c
d->justification = ivy_just(INSTANCE_JUST, c->id, NULL, 0, NULL, pairs);
```

This is one of the most useful design points for Vampire/Megalodon. Instead of
having Python infer a substitution from parent and child clauses, Vampire should
print the substitution chosen by unification/matching as an explicit primitive
step.

## Resolution Expansion

`resolve2_instances` is at `ladr/ivy.c:523-612`. The comment at
`ladr/ivy.c:509-520` gives the intended shape:

1. instantiate the first parent if needed;
2. instantiate the second parent if needed;
3. optionally flip an equality literal if the recorded literal number is
   negative;
4. resolve identical complementary literals;
5. optionally renumber variables.

The code then constructs the resolvent by copying all literals except the two
resolved pivots at `ladr/ivy.c:576-582`, and records a primitive `resolve`
justification with exact literal positions at `ladr/ivy.c:586-593`.

For Vampire, this argues for printing resolution-like inferences as:

- parent instantiation steps;
- optional equality symmetry/flip;
- one primitive resolve step with explicit pivot locations;
- optional normalize/renumber step if needed.

## Paramodulation And Demodulation

`paramod2_instances` is at `ladr/ivy.c:395-472`. It:

- reads the equality source position and target term position;
- distinguishes demodulation-like matching from full unification at
  `ladr/ivy.c:414-419`;
- emits parent instantiations when needed at `ladr/ivy.c:422-436`;
- calls Prover9's own `paramodulate` at `ladr/ivy.c:445-446`;
- records a primitive `paramod` justification with both positions at
  `ladr/ivy.c:447-457`;
- optionally emits variable renumbering at `ladr/ivy.c:460-464`.

The low-level construction is in `ladr/paramod.c:156-185`. It copies all
non-source literals from the equality parent, copies all non-target literals
from the target parent, and replaces the selected target subterm with the
equality's other side.

Demodulation is not a separate primitive in Ivy. Stage 1 converts each
demodulation into a paramodulation-style step by finding the exact source and
target positions using `particular_demod` in `ladr/demod.c:468-488`.

This maps closely to Vampire superposition/demodulation. The certificate should
contain:

- equality parent ID and equality literal position;
- selected equality side;
- target parent ID and target literal/subterm position;
- substitution/matching data;
- the full post-paramodulation clause.

## Equality Flip

`flip_inference` is at `ladr/ivy.c:480-501`. It copies the entire parent
clause, swaps the two sides of one equality literal, and records a `flip`
justification with the parent ID and literal position.

This is directly relevant to the current Vampire certificate failures where
intermediate equality-symmetry clauses were missing inherited split literals.
The Prover9 pattern says the flip is a whole-clause transformation: copy the
parent clause, swap one equality literal, and keep every other literal and
attribute/bookkeeping dependency.

## Factor And Propositional Simplification

`factor2_instances` is at `ladr/ivy.c:620-673`. It instantiates the parent,
removes a duplicate/unified literal, and records the result as
`propositional`. Merge and copy-like steps are similarly reduced to
`propositional` in `expand_proof_ivy` at `ladr/ivy.c:846-855`.

This suggests that our Megalodon certificate language does not need a large
surface vocabulary for every clause cleanup. It needs a generic, checkable
propositional/structural clause step, plus enough data to confirm the deleted
or merged literal.

## Validation Discipline

Both expansion phases validate parent ordering and clause links:

- `check_parents_and_uplinks_in_proof` is called after `expand_proof`.
- `check_parents_and_uplinks_in_proof` is called again at the end of
  `expand_proof_ivy` at `ladr/ivy.c:922`.

`expand_proof_ivy` also checks that each newly elaborated clause is equivalent
to the original expanded clause by mutual subsumption at `ladr/ivy.c:893-897`.

For Vampire/Megalodon, the analogous discipline is:

- every primitive certificate step should contain the full resulting clause;
- the checker should verify the primitive step locally;
- the exporter should verify that the sequence of primitives reaches the same
  clause as Vampire's original inference;
- Python should reject incomplete primitive clauses instead of guessing.

## Implications For Current Vampire/Megalodon Work

The Prover9/Ivy architecture strongly supports the audit's recommendation. The
right direction is not a larger Python reconstruction engine. The right
direction is a Vampire-side elaborator, modeled on:

- `expand_proof` for decomposing high-level and secondary justifications;
- `expand_proof_ivy` for turning those decomposed steps into a small primitive
  certificate language.

The Megalodon certificate target should be a Prover9/Ivy-like vocabulary:

- `input` / source axiom / source conjecture clause;
- `substitute` / `instantiate`;
- `resolve`;
- `paramodulate`;
- `equality_symmetry` / `flip`;
- `propositional` / structural cleanup;
- `renumber` or alpha-conversion, if needed;
- explicit transformation steps for CNF, definitions, and skolemization.

The current JSON format is moving in this direction, but too many clauses are
still assembled case-by-case in `Shell/MegalodonChecker/MegalodonChecker.cpp`.
The split-literal bugs are a symptom of that. In Prover9 terms, an equality
flip or paramodulation output is a full child clause derived from a full parent
clause. It is not just "the main equality literal after rewriting".

## Recommended Implementation Direction

Short term:

- Fix the remaining equality-symmetry cases by making them whole-clause
  transformations: copy every inherited literal, swap one equality, and preserve
  split literals and other bookkeeping literals.
- Continue checking the embedded JSON with the strict Megalodon-side validator.
  Do not relax the validator to tolerate missing split literals.

Medium term:

- Introduce reusable Vampire-side certificate expansion helpers:
  - render a complete clause including split dependencies;
  - render a substituted complete clause;
  - render a clause after deleting selected literals;
  - render a clause after replacing one subterm by equality reasoning;
  - render whole-clause equality symmetry;
  - emit alpha-renaming/normalization as explicit steps if needed.
- Make each high-level Vampire inference call these helpers rather than
  hand-building JSON fragments.

Longer term:

- Add an internal exporter self-check, mirroring Prover9's equivalence checks:
  after elaborating a Vampire inference into primitive steps, verify that the
  final primitive clause equals the clause Vampire actually derived.
- Extend the same approach to CNF/skolem/definition transformations, so the
  original Megalodon theorem and lemmas are connected through explicit source
  and transformation steps rather than through guessed names or reconstructed
  syntax.

## Practical Use For Later Inspection

When working on a specific Vampire inference class, inspect the analogous
Prover9 routine first:

- Resolution and UR-like steps: `ladr/xproofs.c:312-343` and
  `ladr/ivy.c:523-612`.
- Superposition/paramodulation: `ladr/xproofs.c:345-353`,
  `ladr/ivy.c:395-472`, and `ladr/paramod.c:156-185`.
- Demodulation/rewrite: `ladr/xproofs.c:397-418` and
  `ladr/demod.c:468-488`.
- Equality symmetry: `ladr/ivy.c:480-501`.
- Cleanup/factor/merge: `ladr/ivy.c:620-673` and `ladr/ivy.c:846-855`.

The main architectural lesson is simple: let the prover, not the importer,
explain the proof.

## Concrete Template For Vampire

The Prover9 code suggests a very specific implementation shape for Vampire.
For each Vampire inference that currently prints one high-level proof line, the
Megalodon exporter should build a local primitive trace while Vampire still has
access to the actual parents, selected literals, substitutions, rewrite
positions, split dependencies, and final child clause.

The local trace should look like this:

1. Start from the exact parent clauses used by the inference.
2. Emit explicit `substitute` steps for every non-vacuous parent
   instantiation. The substitution should come from Vampire's own
   unifier/matcher, not from Python.
3. Emit explicit `equality_symmetry` steps when a selected equality side is
   flipped. This must be a whole-clause operation, preserving all other
   literals and dependencies.
4. Emit one primitive `resolve` or `paramodulate` step with exact literal and
   term positions.
5. Emit explicit structural cleanup steps, such as factor/merge/delete, instead
   of hiding them inside the previous primitive.
6. Emit an alpha-renaming step only if the final primitive clause is equivalent
   to, but not syntactically identical with, Vampire's child clause.
7. Check inside Vampire that the last primitive clause is identical to the
   actual child clause. If not, fail the certificate emission for that
   inference instead of printing a guessed trace.

This is close to what Prover9 does in `expand_proof` plus `expand_proof_ivy`:
first split complex justifications into small prover-side substeps, then lower
those substeps to a tiny proof-object vocabulary and validate equivalence after
each elaboration.

For the current Vampire/Megalodon branch, that means the Python side should be
kept as a strict parser/renderer/checker. It can validate and translate the
certificate JSON, but it should not infer missing pivots, substitutions,
positions, skolem links, or symbol origins. Missing data should be added to the
Vampire certificate.

## Immediate Vampire Work Items

- Move the current URR, superposition, and demodulation certificate builders
  toward shared helper routines that operate on complete clauses.
- Add a reusable internal self-check: after a primitive sequence is generated,
  compare the final primitive clause with the real Vampire child clause before
  printing the certificate.
- Add explicit primitive expansion for any remaining high-frequency inference
  class that still appears as an embedded fallback or no-embedded outline
  failure in the 10-second parallel THF test batches.
- Extend the same prover-side-expansion discipline to front-end transformations:
  Megalodon source theorem/lemma linking, set-command equalities, definitions,
  clausification, and skolemization should be explained by printed
  transformation steps rather than reconstructed heuristically downstream.
