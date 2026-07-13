# Prover9 Ivy Proof Expansion Notes

Date: 2026-07-12

Local source checkout: `/project/tmp/Prover9`

Upstream cloned from: `https://github.com/ai4reason/Prover9.git`

Checkout inspected: `cdca95a51d3c3459b8fd2ebbb5ac1504be2172e3`

Build note: source was built locally enough to run the example pipeline:
`/project/tmp/Prover9/bin/prover9` and
`/project/tmp/Prover9/bin/prooftrans`. A full parallel `make -j10 all`
exposes an old Makefile race in the Mace4 install target, but the LADR
library, Prover9 binary, and `prooftrans` app build correctly when targeted
directly.

Concrete sample artifacts:

- `/project/tmp/prover9-x2.ivy`
- `/project/tmp/prover9-x2.tagged`

## Why This Matters

Prover9's Ivy path is a useful model for the Vampire-to-Megalodon work because it does not ask an external script to rediscover unifiers, rewritten terms, or paramodulation sites. Instead, it expands normal prover proof steps into a small replay language while still inside the prover's own clause and substitution machinery.

That is the direction we should prefer for Vampire:

- Keep Vampire responsible for elaborating complex inferences.
- Emit explicit instantiated parent clauses before resolution/paramodulation.
- Emit positions in the rendered clause formula.
- Emit primitive replay steps that Megalodon can check directly.
- Keep Python as a thin adapter/parser, not as a second prover.

## Relevant Prover9 Files

- `/project/tmp/Prover9/apps.src/prooftrans.c`
  - Recognizes `prooftrans ivy`.
  - Reads the ordinary Prover9 proof.
  - Calls the ordinary proof expansion first, then Ivy expansion.

- `/project/tmp/Prover9/ladr/ivy.c`
  - Implements the Ivy-specific proof expansion.
  - Emits the small Ivy proof language.
  - Splits resolution/paramodulation/factoring into explicit instantiation plus primitive steps.

- `/project/tmp/Prover9/ladr/just.h`
  - Defines `struct ivyjust`, the compact internal justification record.

- `/project/tmp/Prover9/ladr/just.c`
  - Allocates and prints justification objects.

- `/project/tmp/Prover9/ladr/xproofs.c`
  - Performs the first proof expansion pass.
  - Breaks mixed/compound Prover9 justifications into a more detailed proof
    before the Ivy lowering pass.

- `/project/tmp/Prover9/ladr/resolve.c`
  - Contains the normal `resolve2` implementation used by proof expansion.

- `/project/tmp/Prover9/ladr/paramod.c`
  - Contains the normal `paramodulate` implementation used by proof expansion.

## Prooftrans Control Flow

In `apps.src/prooftrans.c`, selecting `ivy` sets:

- `transformation = EXPAND_IVY`
- `output_format = IVY`

Then, for each proof, Ivy output performs two expansions:

1. `expand_proof(proof, &jmap)`
2. `expand_proof_ivy(proof2)`

The second phase is the important one for us. It receives an already-normalized proof and further expands it into Ivy-checkable primitives.

Code references:

- `apps.src/prooftrans.c:260-262`: command-line `ivy` selection.
- `apps.src/prooftrans.c:431-437`: ordinary expansion followed by `expand_proof_ivy`.
- `ladr/xproofs.c:251-526`: first expansion pass over the raw proof.
- `ladr/ivy.c:704-897`: Ivy-specific lowering pass.

## Ivy Output Language

The printer emits one line per clause:

```lisp
(id justification literals NIL)
```

The justification vocabulary is intentionally small:

- `(input)`
- `(propositional parent)`
- `(new_symbol parent)`
- `(flip parent position)`
- `(instantiate parent ((v . term) ...))`
- `(resolve parent1 pos1 parent2 pos2)`
- `(paramod parent1 pos1 parent2 pos2)`

Code references:

- `ladr/ivy.c:217-263`: prints Ivy justifications.
- `ladr/ivy.c:275-288`: prints a whole Ivy proof line.

This is close to what our Megalodon certificate should become: a compact step language whose steps map directly to Megalodon proof terms/claims.

The same path can be validated after building Prover9 by running:

```sh
TMPDIR=/project/tmp /project/tmp/Prover9/bin/prover9 \
  -f /project/tmp/Prover9/prover9.examples/x2.in |
  /project/tmp/Prover9/bin/prooftrans ivy \
  > /project/tmp/prover9-x2.ivy
```

For comparison, tagged output can be produced with:

```sh
TMPDIR=/project/tmp /project/tmp/Prover9/bin/prover9 \
  -f /project/tmp/Prover9/prover9.examples/x2.in |
  /project/tmp/Prover9/bin/prooftrans tagged \
  > /project/tmp/prover9-x2.tagged
```

The ordinary parent-only proof has steps such as:

```text
7 x' * (x * y) = y.  [3,4,2].
```

The Ivy proof expands the same high-level step into a sequence like:

```lisp
(33 (instantiate 3 ((v0 . v101))) ...)
(34 (instantiate 4 ((v0 . (quote_for_ivy v101)) ...)) ...)
(35 (paramod 33 (1) 34 (1 1)) ...)
(7A (instantiate 35 ((v102 . v0) (v101 . v1))) ...)
(36 (instantiate 2 ()) ...)
(7B (paramod 36 (1) 7A (1)) ...)
(37 (flip 7B ()) ...)
(7 (instantiate 37 ((v1 . v0) (v0 . v1))) ...)
```

This is the critical behavior: the expanded proof contains explicit parent
instances, exact term positions, primitive paramodulation steps, equality flip,
and final variable renaming.

The tagged proof for the same derivation is much lighter. For example, it says
that step 7 is `para` from parents 3 and 4, then `rewrite` by parent 2, then
`flip`. That is useful provenance, but it does not expose the instantiated
parent clauses, substitution map, source/target positions, or intermediate
clauses. Ivy does expose those. For Megalodon, tagged-style metadata is not
enough if the checker is meant to replay the proof rather than trust a macro
step.

## Key Design: Instantiate First, Then Replay Ground-Like Steps

The central trick is that Ivy resolution and paramodulation do not perform unification during checking. Prover9 performs unification during expansion, emits explicit instantiation steps, and then emits resolution/paramodulation over instantiated parents.

### Instantiation

`instantiate_inference`:

- calls `instantiate_clause(c, subst)`;
- records the substitution pairs with `context_to_pairs`;
- emits an Ivy `instantiate` justification.

Code reference: `ladr/ivy.c:299-307`.

This is directly relevant to Vampire/Megalodon. For every non-ground parent used by a Vampire inference, Vampire should emit the exact instantiated parent clause and substitution map. The checker/translator should not infer that map.

### Resolution

`resolve2_instances`:

- looks up the selected literals;
- unifies them using Prover9's own `unify`;
- emits instantiation steps for non-ground parents;
- handles flipped equality if required;
- constructs the resolvent;
- emits an Ivy `resolve` step over positions;
- optionally emits variable renumbering as another `instantiate` step.

Code reference: `ladr/ivy.c:524-612`.

The underlying normal Prover9 implementation is `resolve2` in
`ladr/resolve.c:827-870`. It uses Prover9's own unifier, applies the two
substitutions to all surviving literals, records a binary-resolution
justification with parent IDs and literal numbers, and optionally renumbers the
result. The Ivy pass repeats the same core operation but exposes the implicit
substitutions as separate proof nodes.

This suggests that Vampire should lower `resolution`, `subsumption_resolution`, and similar steps into:

1. parent instance(s);
2. optional equality flip;
3. primitive binary resolution over explicit literal positions;
4. optional renaming/normalization.

### Paramodulation

`paramod2_instances`:

- finds the equality side and target term by positions;
- uses matching for demod-like cases or unification otherwise;
- emits explicit instantiations of source and target parents;
- calls the existing `paramodulate` constructor;
- emits Ivy `paramod` with source and target positions;
- optionally emits variable renumbering.

Code reference: `ladr/ivy.c:396-470`.

The underlying normal constructor is `paramodulate` in
`ladr/paramod.c:156-186`. It builds the paramodulant from the equality source,
the target clause, a target position, and the two substitutions. The Ivy pass
does not infer this information from printed text; it calls the same prover
machinery and then prints the source/target positions.

This is the closest template for our current Vampire pain point. The output should not just say "superposition" or "paramodulation"; it should expose:

- the equality parent after substitution;
- the into parent after substitution;
- the equality side used;
- the target term position;
- the resulting clause;
- any final renaming.

### Factoring

`factor2_instances`:

- unifies the two factored literals;
- emits the instantiated parent;
- emits the factor as a `propositional` step;
- optionally emits variable renumbering.

Code reference: `ladr/ivy.c:620-673`.

For Vampire, this suggests that equality factoring and ordinary factoring should be elaborated into instantiation plus a simple propositional/duplicate-removal primitive, instead of reconstructed by Python.

## First Expansion Pass

`expand_proof` in `ladr/xproofs.c` is worth copying architecturally. It handles
compound Prover9 justifications before Ivy lowering:

- hyper/UR/binary resolution become a sequence of binary resolvents;
- demodulation steps become explicit paramodulation steps;
- unit deletion becomes binary resolution against the deleting unit;
- equality flips become explicit flip steps;
- merges and `x != x` simplifications become explicit simplification steps;
- each intermediate step receives a fresh ID, while the final expanded clause
  keeps the original proof step ID.

Code references:

- `ladr/xproofs.c:312-344`: hyper/UR/binary resolution expansion.
- `ladr/xproofs.c:345-354`: paramodulation expansion.
- `ladr/xproofs.c:396-419`: demodulation as explicit paramodulation.
- `ladr/xproofs.c:420-435`: equality flip expansion.
- `ladr/xproofs.c:449-467`: unit deletion as resolution.
- `ladr/xproofs.c:495-514`: final identity check and original-ID restoration.

This maps directly to the Vampire situation. Vampire's `superposition`,
`subsumption_resolution`, `unit_resulting_resolution`, simplification, and
normal-form steps should be lowered inside Vampire before Megalodon sees them.

## Clause Position Handling

Prover9 converts internal clause/literal positions into Ivy's formula positions:

- `ivy_lit_position`: maps a literal index into a right-associated `or` tree position.
- `ivy_para_position`: extends that position to a term occurrence inside a literal and accounts for negative literals.

Code references:

- `ladr/ivy.c:339-359`
- `ladr/ivy.c:368-380`

For Megalodon, we need the same idea, but using the exact formula shape that we print as a claim. If we print right-associated disjunctions, we should expose positions relative to that exact right-associated expression. If we print clause claims in another shape, the position convention must match that shape.

## Symbol Renaming

Ivy cannot accept some Prover9 symbols, so Prover9 renames them before Ivy expansion:

- `0 -> zero_for_ivy`
- `1 -> one_for_ivy`
- `' -> quote_for_ivy`
- `\ -> backslash_for_ivy`
- `@ -> at_for_ivy`
- `^ -> meet_for_ivy`

Code references:

- `ladr/ivy.c:24-31`
- `ladr/ivy.c:47-63`
- `ladr/ivy.c:78-84`
- `ladr/ivy.c:681-692`

For Megalodon, the analogous work is our name-linking problem: keep enough metadata to map TPTP/Vampire names back to original Megalodon constants, lemmas, definitions, and generated `set` equalities. This should also happen in the prover-side certificate stream, not by fragile guessing after the fact.

## Safety Check

After expanding each old step, Prover9 checks that the expanded result is the
same as the old proof step. There are two forms of this check.

The first expansion pass checks syntactic clause identity after variable
renumbering:

```c
else if (!clause_ident(current->literals, c->literals)) {
  fprint_clause(stdout, c);
  fprint_clause(stdout, current);
  fatal_error("expand step, result is not identical");
}
```

Code reference: `ladr/xproofs.c:495-503`.

The Ivy lowering pass checks mutual subsumption:

```c
if (!subsumes(c, new_c) || !subsumes(new_c, c))
  fatal_error("expand_proof_ivy, clauses not equivalent");
```

Code reference: `ladr/ivy.c:893-897`.

We should add a similar assertion in Vampire's Megalodon/LeanCheck elaboration mode: every expanded primitive sequence must end in a clause equivalent to the original Vampire step. That catches bugs while keeping the emitted proof detailed.

## Concrete Direction For Vampire/Megalodon

The Prover9 model argues for a radical shift away from Python reconstruction:

1. Add a Vampire proof-output mode or extend the current Megalodon/LeanCheck output to emit "expanded primitive" steps.
2. For each complex Vampire inference, use Vampire's own substitutions, term positions, literal selections, and clause objects to emit:
   - parent clause id(s);
   - instantiated parent clauses;
   - substitution maps with sorted variables;
   - equality flips/symmetry steps;
   - primitive resolve/paramod/factor/propositional steps;
   - exact source and target positions;
   - resulting clause.
3. Preserve high-level source links:
   - original Megalodon theorem/conjecture;
   - original Megalodon lemma/definition names;
   - generated axioms from `set`, with reflexivity proofs where applicable;
   - Skolem symbols and the transformation that introduced them.
4. Make the Python layer consume this stream and print Megalodon proof skeleton/proof terms. It should validate shape and serialize, not discover proof content.

## Immediate Implementation Lessons

The useful part of Prover9 is not the exact Ivy syntax; it is the staging.
For every raw inference that is too large for a kernel/checker to replay
directly, Prover9 uses the prover's own inference code to construct a
sequence of smaller clauses, then verifies that the last expanded clause is
equivalent to the original raw proof step.

For Vampire, this means the Megalodon output should grow an in-prover
expansion layer with the same responsibilities:

- Read the actual Vampire inference object, substitutions, selected literals,
  equality sides, and term positions.
- Emit explicit instantiated parent clauses before emitting resolution or
  paramodulation.
- Emit primitive binary resolution and primitive single-site paramodulation
  steps rather than macro steps such as full superposition, subsumption
  resolution, or unit-resulting resolution.
- Emit final renaming/normalization steps when Vampire's derived clause has
  renamed variables.
- Check inside Vampire that the expanded primitive sequence ends in a clause
  equivalent to the clause Vampire originally derived.

The Python/Megalodon side should then be a checker-facing serializer. It can
still reject malformed certificates, recover original Megalodon names, and
print readable claims, but it should not infer missing pivots, substitutions,
or rewrite sites except as temporary diagnostics while the Vampire-side
certificate is incomplete.

## Immediate Work Items

- Inspect Vampire's existing LeanCheck/Dedukti proof emitters and identify their equivalent of Prover9's `expand_proof_ivy`.
- Add an "expanded proof" layer in Vampire for at least:
  - resolution;
  - superposition/paramodulation;
  - equality resolution;
  - equality factoring;
  - ordinary factoring;
  - subsumption resolution.
- Emit explicit instantiation steps before every primitive inference.
- Emit term/literal positions relative to the printed Megalodon clause formula.
- Keep the existing Python translator only as a temporary consumer of the richer stream.

## Bottom Line

Prover9's Ivy implementation confirms that the right architecture is prover-side elaboration into simple replay primitives. It is not a large external reconstruction script. The Megalodon project should follow this pattern in Vampire: expose enough detail from Vampire that each Megalodon step is a local proof obligation with known parents, substitutions, positions, and result.

## Source-Level Addendum

The direct code inspection gives a concrete template for the Vampire work.

`prooftrans ivy` is not just a pretty-printer. In `apps.src/prooftrans.c:431-437`
it first calls `expand_proof`, then calls `expand_proof_ivy`. This means the
Ivy output is the product of two prover-internal elaboration passes, not an
external reconstruction pass over printed formulas.

The first pass, `ladr/xproofs.c:251-526`, expands Prover9's ordinary
justification chains. It turns compound and secondary justifications into
explicit intermediate clauses:

- hyper/UR/binary resolution are replayed as a sequence of binary resolutions;
- demodulation is converted to explicit paramodulation with source and target
  positions;
- unit deletion is converted to binary resolution against the deleting unit;
- equality flipping, merging, and `x != x` deletion become explicit steps;
- the last expanded substep gets the original clause id again.

The second pass, `ladr/ivy.c:704-923`, lowers those already-expanded steps into
the tiny Ivy calculus. The most important routines are:

- `instantiate_inference` (`ladr/ivy.c:299-307`): materializes the exact
  substituted parent and records the substitution pairs.
- `paramod2_instances` (`ladr/ivy.c:396-472`): uses Prover9's own matcher or
  unifier, emits instantiated parents, then emits one primitive `paramod` node
  with explicit source and target positions.
- `resolve2_instances` (`ladr/ivy.c:524-612`): emits instantiated parents,
  optional equality flip, primitive `resolve`, and optional variable
  renumbering.
- `factor2_instances` (`ladr/ivy.c:621-673`): emits an instantiated parent and
  then a simple propositional duplicate-removal step.

The corresponding Ivy justification object is deliberately small:
`input`, `propositional`, `new_symbol`, `flip`, `instantiate`, `resolve`, and
`paramod` (`ladr/just.h:82-89`, printed in `ladr/ivy.c:217-263`). This is the
right scale for the Megalodon certificate language as well.

The sample confirms this mechanically. The high-level Prover9 proof has a
16-step parent proof; the Ivy object expands it to 38 proof-object lines. A
typical high-level `para + rewrite + flip` step becomes instantiated parent
clauses, primitive `paramod` nodes, a `flip` node, and final instantiation for
renaming. That is the granularity we should target in the Vampire exporter.

For our Vampire branch, the immediate consequence is that the next serious
work should be inside `Shell/MegalodonChecker/MegalodonChecker.cpp`, not in a
larger Python reconstructor. The exporter should add an Ivy-like expansion
stream:

1. emit explicit instantiated parent clauses and substitution maps;
2. emit exact literal and term positions relative to the printed clause shape;
3. split macro inferences into primitive `resolve`, `paramod`, `flip`,
   `factor`, and propositional/normalization steps;
4. keep a high-level link from each primitive sequence back to the original
   Vampire inference id and original Megalodon lemma/conjecture name;
5. assert in Vampire that the final primitive clause is equivalent to the
   original derived clause before printing it.

This also clarifies the remaining bound-lambda and boolean-normal-form
failures. They should not be solved by guessing more in Python. Vampire already
has the relevant scoped term, equality side, instantiated parents, and final
clause; the Megalodon output mode should expose those as explicit primitive
steps, the same way Prover9 exposes them before Ivy ever sees the proof.

## Recheck Note

I rechecked the downloaded source on 2026-07-12. The local clone is current with
`origin/master` at `cdca95a51d3c3459b8fd2ebbb5ac1504be2172e3`.

The old checked-in Prover9 example output is not a reliable input to this build
of `prooftrans ivy`, because it contains an older/unrecognized justification
tag. Regenerating the proof with the local `prover9` binary and immediately
piping it into `prooftrans ivy` works:

```sh
TMPDIR=/project/tmp /project/tmp/Prover9/bin/prover9 \
  -f /project/tmp/Prover9/prover9.examples/x2.in |
  TMPDIR=/project/tmp /project/tmp/Prover9/bin/prooftrans ivy \
  > /project/tmp/prover9-x2-current.ivy
```

The regenerated sample again shows the architecture we should copy in Vampire:
ordinary proof steps are expanded into prover-internal instantiation,
paramodulation, flip, and resolve nodes before any external checker sees them.
For the current Vampire/Megalodon branch, the Prover9 lesson is specifically to
push more explanation into `MegalodonChecker.cpp` and keep Python as a thin
consumer of already-explicit primitive certificates.

## Fresh Inspection: 2026-07-13

I regenerated the `x2.in` sample again from the local Prover9 checkout:

```sh
mkdir -p /project/tmp/prover9_inspect_20260712
TMPDIR=/project/tmp /project/tmp/Prover9/bin/prover9 \
  -f /project/tmp/Prover9/prover9.examples/x2.in |
  TMPDIR=/project/tmp /project/tmp/Prover9/bin/prooftrans ivy \
  > /project/tmp/prover9_inspect_20260712/x2.ivy

TMPDIR=/project/tmp /project/tmp/Prover9/bin/prover9 \
  -f /project/tmp/Prover9/prover9.examples/x2.in |
  TMPDIR=/project/tmp /project/tmp/Prover9/bin/prooftrans tagged \
  > /project/tmp/prover9_inspect_20260712/x2.tagged
```

The result is a useful contrast:

- `x2.tagged` is a readable 16-step proof with parent references and broad
  inference names such as `para`, `rewrite`, `flip`, and `resolve`.
- `x2.ivy` is a 63-line proof object with explicit primitive proof nodes:
  `instantiate`, `paramod`, `flip`, and `resolve`.

A representative tagged step is:

```text
c 7  x' * (x * y) = y
i para
p 3
p 4
i rewrite
p 2
i (flip)
e
```

The corresponding Ivy fragment is more verbose but checkable:

```lisp
(33 (instantiate 3 ((v0 . v101))) ...)
(34 (instantiate 4 ((v0 . (quote_for_ivy v101)) (v1 . v101) (v2 . v102))) ...)
(35 (paramod 33 (1) 34 (1 1)) ...)
(7A (instantiate 35 ((v102 . v0) (v101 . v1))) ...)
(36 (instantiate 2 ()) ...)
(7B (paramod 36 (1) 7A (1)) ...)
(37 (flip 7B ()) ...)
(7 (instantiate 37 ((v1 . v0) (v0 . v1))) ...)
```

This reinforces the split we should use for Vampire:

- the human-readable proof can preserve high-level Vampire inference names;
- the Megalodon-checkable proof needs the Ivy-style expanded stream;
- the expanded stream should be produced from Vampire's internal proof objects,
  not recovered later from text.

The local artifacts for future inspection are:

- `/project/tmp/prover9_inspect_20260712/x2.ivy`
- `/project/tmp/prover9_inspect_20260712/x2.tagged`
