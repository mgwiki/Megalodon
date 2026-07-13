# Prover9 Ivy Proof Object Analysis

Date: 2026-07-13

Source checkout: `/project/prover9-ladr`

Remote: `https://github.com/ai4reason/Prover9.git`

Revision inspected: `cdca95a`

Scratch output: `/project/tmp/prover9_ivy_inspect_20260713`

## Summary

Prover9's Ivy export is a good model for the Vampire/Megalodon work because it does not rely on a large external proof-reconstruction guesser. It has two prover-side proof-detailing stages:

1. `expand_proof` in `ladr/xproofs.c` expands Prover9's normal proof justifications into more explicit clause-to-clause steps.
2. `expand_proof_ivy` in `ladr/ivy.c` lowers those expanded steps into a small Ivy kernel:
   `input`, `instantiate`, `flip`, `resolve`, `paramod`, `propositional`, and limited `new_symbol`.

This is directly aligned with the audit recommendation and with the current project direction: richer Vampire-side certificate objects first, then a relatively mechanical Megalodon proof-term emitter.

## Invocation Path

The user-facing command is:

```sh
prover9 -f prover9.examples/x2.in | prooftrans ivy
```

In `bob/prooftrans.c`, selecting `ivy` forces:

- `transformation = EXPAND_IVY`
- `output_format = IVY`
- `clause_format = CL_FORM_IVY`

The proof pipeline is:

```c
Plist proof2 = expand_proof(proof, &jmap);
Plist proof3 = expand_proof_ivy(proof2);
print_proof(stdout, proof, comment, CL_FORM_IVY, jmap, n);
```

The important point is that Ivy output is not just a printer for the original proof. It first changes the proof into a more atomic proof.

## Ivy Object Shape

`ladr/just.h` defines a dedicated `Ivyjust`:

```c
struct ivyjust {
  Just_type type;
  int parent1;
  int parent2;
  Ilist pos1;
  Ilist pos2;
  Plist pairs;
};
```

This is the minimal data needed for atomic proof replay:

- parent clause IDs
- positions in parent clauses
- substitution pairs for instantiation
- a small inference-rule tag

`ladr/ivy.c` prints these as S-expressions. Example from the inspected sample:

```lisp
(35 (paramod 33 (1) 34 (1 1)) (= (* (e) v102) (* (quote_for_ivy v101) (* v101 v102))) NIL)
(7A (instantiate 35 ((v102 . v0) (v101 . v1))) (= (* (e) v0) (* (quote_for_ivy v1) (* v1 v0))) NIL)
(7B (paramod 36 (1) 7A (1)) (= v0 (* (quote_for_ivy v1) (* v1 v0))) NIL)
(37 (flip 7B ()) (= (* (quote_for_ivy v1) (* v1 v0)) v0) NIL)
```

This is the level of detail we should aim to emit from Vampire for Megalodon.

## Stage 1: Expand Normal Prover9 Proofs

`ladr/xproofs.c:expand_proof` expands complex or secondary justifications into explicit intermediate clauses. It also preserves a map from new intermediate IDs back to the original proof step and substep number.

Important behavior:

- Hyper/UR resolution is expanded into a sequence of binary resolution steps.
- Paramodulation is reconstructed at the recorded positions via `para_pos`.
- Factoring becomes an explicit factor step.
- Secondary rewrites are expanded one by one.
- Unit deletion is expanded as a binary resolution with the unit.
- Merge, flip, and reflexivity simplification are expanded as explicit steps.
- The final substep is renumbered back to the original clause ID so later proof references remain valid.

The demodulation/rewrite case is especially relevant. Prover9 stores demodulation as triples:

```c
/* list of triples: <ID, position, direction> */
```

For each rewrite triple, it:

1. copies the current clause,
2. locates the specific rewrite occurrence with `particular_demod`,
3. records the rewrite as a paramodulation justification:

```c
work->justification = para_just(PARA_JUST, demod, from_pos, current, into_pos);
```

This is the key pattern for our current Vampire `definition_rewrite_chain` blocker. Do not ask the Python script to infer which occurrence was rewritten. Make Vampire emit, or internally expand into, primitive rewrite/paramodulation steps with exact parent, direction, and position.

## Stage 2: Lower to Ivy Kernel

`ladr/ivy.c:expand_proof_ivy` lowers expanded clauses into Ivy rules.

For resolution, `resolve2_instances` decomposes a high-level resolution into:

- instantiate parent 1 if needed,
- instantiate parent 2 if needed,
- optional flip for equality orientation,
- resolve identical opposite literals,
- renumber variables if needed.

For paramodulation, `paramod2_instances` decomposes into:

- instantiate the equality parent if needed,
- instantiate the target parent if needed,
- one primitive `paramod` with positions,
- renumber variables if needed.

For factoring, Prover9 uses:

- instantiate,
- propositional simplification,
- renumber.

The kernel deliberately avoids carrying complicated unification obligations in the checker. It performs unification inside the prover-side expansion, then emits explicit instantiations and a much simpler kernel inference.

## Position Encoding

Ivy positions are adapted to the right-associated `or` tree printed by `sb_ivy_write_literals`.

`ivy_lit_position` maps literal numbers to positions in that tree. `ivy_para_position` combines the literal position, sign handling, and the term position inside the atom.

This is important for Megalodon: if we print clauses as right-associated `or`, we should use the same idea and emit positions relative to that exact printed formula shape. Otherwise the checker/emitter will keep doing fragile structural search.

## Relevance to Vampire/Megalodon

The current Vampire/Megalodon work already moved in this direction for demodulation by expanding `paramodulate_all` into primitive `paramodulate` substeps. The Prover9 code suggests making that the general architecture:

1. In Vampire, define a small Megalodon certificate kernel.
2. Add a certificate-expansion pass before printing:
   - expand superposition/paramodulation into instantiate plus primitive equality transport,
   - expand demodulation and definition rewrite chains into one rewrite/paramodulation per occurrence,
   - expand resolution-like inferences into instantiate plus primitive resolution,
   - expand factoring/condensation into instantiate plus propositional/duplicate-literal steps,
   - keep clausification/skolemization as explicit transformation certificates rather than Python-side guesses.
3. Print exact parents, substitutions, positions, directions, and resulting formulas for every primitive step.
4. Keep Python as a parser/emitter into Megalodon syntax, not as the source of proof search.

## Direct Lessons for Current Blockers

### Definition rewrite chains

The current difficult example `hammer.13251.105.th0` needs exact rewrite occurrences inside large lambda-heavy terms. Prover9 handles analogous rewrite expansion by storing enough data to call `particular_demod`: parent demodulator, target occurrence number/position, and direction. For Vampire we should extend `TweeDefinitionFoldingExtra` beyond `(from, to)` pairs to include:

- definition parent clause/unit ID,
- direction,
- occurrence position in the current clause/formula,
- possibly the matched substitution when the definition is quantified.

The recently added `parent` field is useful but not sufficient. Position and substitution are still needed.

### Superposition and demodulation

Prover9 turns these into `paramod` over already-instantiated parents. This supports the direction we have discussed: Vampire should expose instantiated parents or explicit substitution maps, not force Megalodon/Python to re-run higher-order matching.

### Skolemization and clausification

Prover9 Ivy treats `clausify`, `deny`, and `expand_def` as `input` after expansion and removes parents that Ivy would not accept. That is not enough for our project because Megalodon should eventually connect to the original theorem and lemmas. Still, it gives a useful split:

- treat kernel clause proof replay separately from source-to-clause transformations,
- give Smolka-style transformations their own explicit certificate layer,
- do not mix them with paramodulation/resolution replay.

### Name/link preservation

Prover9's Ivy export renames symbols only for Ivy syntax compatibility. It does not solve source-development linking. For Megalodon, we still need a source map from exported TPTP names back to Megalodon declarations, theorem names, set-generated equalities, and conjecture names.

## Recommended Next Step

Use Prover9 as the concrete template for a Vampire-side expansion module:

- add a small internal `MegalodonKernelJustification` or equivalent JSON schema,
- implement an `expandProofForMegalodon` pass before `MegalodonChecker` prints,
- first target the frequent hard cases:
  `definition_rewrite_chain`, `superposition`, `subsumption_resolution`, `condensation`, `avatar`, and clausification/skolemization transformations,
- require each expanded step to contain exact parents, formula, positions, direction, and substitution.

The practical short-term target should be `definition_rewrite_chain`: modify Vampire's `TweeDefinitionFoldingExtra` so it records the occurrence position and definition parent for each fold at the time the fold is performed. That mirrors Prover9's `particular_demod` path and should remove the need for exponential Python-side rewrite search.

## Source Code Map for Later Implementation

The implementation points worth keeping open while changing Vampire are:

- `bob/prooftrans.c:255-258` selects Ivy mode by setting `transformation = EXPAND_IVY` and `output_format = IVY`.
- `bob/prooftrans.c:404-409` shows the two-stage pipeline: first `expand_proof`, then `expand_proof_ivy`.
- `ladr/just.h:82-89` defines `struct ivyjust`, the compact proof-object record carrying rule tag, parents, positions, and instantiation pairs.
- `ladr/xproofs.c:251-526` implements the first expansion pass over ordinary Prover9 proof justifications.
- `ladr/xproofs.c:397-414` is the key demodulation pattern: each rewrite triple `<ID, position, direction>` is replayed immediately with `particular_demod`, then converted into an explicit `PARA_JUST` using the exact source and target positions.
- `ladr/ivy.c:299-307` creates explicit instantiation steps with a substitution-pair list.
- `ladr/ivy.c:339-380` maps internal clause/literal positions to the concrete printed Ivy formula shape.
- `ladr/ivy.c:396-472` lowers one paramodulation into optional instantiation of the equality parent, optional instantiation of the target parent, one primitive `paramod`, and optional variable renumbering.
- `ladr/ivy.c:524-612` does the analogous lowering for binary resolution.
- `ladr/ivy.c:704-860` applies this lowering across the whole expanded proof while preserving original IDs for the final substep of each expanded original inference.

For Vampire/Megalodon this suggests a strict division of responsibilities:

1. Vampire should perform the expensive, prover-informed expansion: unification, matching, orientation, occurrence selection, and substitutions.
2. The certificate format should contain primitive steps with explicit parents, positions, directions, substitutions, and formulas.
3. The Python layer should remain a syntax adapter and Megalodon script emitter. It should not reconstruct missing proof data by search except as a temporary diagnostic.
4. Megalodon checking should replay a small kernel of explicit proof steps plus a separate source-linking/transformation layer for TPTP export, clausification, definitions, set-generated equalities, and skolemization.
