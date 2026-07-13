## Bottom line

The new [2026-07-13 report](https://github.com/mgwiki/Megalodon/blob/vampire/megalodon1/reports/REPORT-2026-07-13.md) is substantially better than the previous one: it accepts the architectural criticism, proposes a versioned Prover9/Ivy-style certificate, distinguishes kernel checking from reconstruction, and explicitly says that only admission-free proofs should count.

However, the implementation has not really completed that pivot. It has already begun recreating the previous architecture in a nominally “small” path.

My recommendation is:

> Continue the project, but freeze all new rule coverage immediately. Make the current milestone exclusively about a fail-closed, first-order, clause-level certificate path whose only assumptions are traceable to the original problem.

At present I would not count the reported live-outline successes as end-to-end reconstruction successes.

## The critical problem: derived clauses become assumptions

The most serious issue is in [vampire_certificate.py](https://github.com/mgwiki/Megalodon/blob/vampire/megalodon1/scripts/vampire_certificate.py).

When the Python importer cannot reconstruct certain Vampire-derived units, it can emit:

```json
{
  "rule": "input",
  "source": {
    "kind": "vampire_derived_clause"
  }
}
```

The Megalodon emitter then translates every `input` into a theorem assumption. It does not require it to correspond to an original source axiom.

This is not a Megalodon kernel soundness bug: Megalodon proves the resulting theorem from the extra premise. But it is fatal to the project’s success accounting. A no-`admit` theorem of the form

```text
original axioms, unsupported Vampire-derived clause ⊢ goal
```

is not a reconstruction of

```text
original axioms ⊢ goal
```

I rebuilt this Vampire branch and replayed the supplied live examples. Two of the central superposition cases reported:

```text
vampire_outline_smoke_superposition:
  derived_assumptions = 1

vampire_outline_smoke_superposition_substituted:
  derived_assumptions = 1
```

The [live-outline smoke script](https://github.com/mgwiki/Megalodon/blob/vampire/megalodon1/tests/vampire_certificate/run_vampire_outline_smoke.sh) rejects nonzero `inferred_resolution_units`, `inferred_paramodulation_units`, and similar statistics—but it does not reject `derived_assumption_units`.

Consequently, “live Vampire outline passed without `admit`” is currently too weak a criterion. This should be the first P0 fix.

## The “small certificate” is already becoming another monolith

The intended design is good. The [certificate specification](https://github.com/mgwiki/Megalodon/blob/vampire/megalodon1/reports/vampire-megalodon-certificate-spec.md) explicitly excludes, for the MVP:

* AVATAR/SAT reconstruction
* higher-order lambda/de Bruijn machinery
* importer-side pivot or substitution discovery
* library-specific proof search

But the implementation’s `MVP_RULES` already contains 22 constructors, including:

* `avatar_refutation`
* `avatar_component`
* three `cnf_formula_*` rules
* `definition_rewrite_chain`
* `inequality_split`
* equality-constraint and clause-wide paramodulation macros

The new Python file is already about 5,956 lines and mixes at least four different responsibilities:

1. Certificate schema and mechanical validation.
2. Parsing Vampire’s old outline protocol.
3. Recovering omitted proof information.
4. Generating substantial Megalodon proof terms.

It contains pivot and paramodulation inference, formula/CNF projection, equality-chain search, definition-rewrite search, DPLL-style SAT work, lambda handling, symbol recovery, typing, and Megalodon rendering.

That is precisely the architectural slope the previous audit warned about: the “importer” gradually becomes another prover.

The Vampire side shows similar expansion. Relative to the previous branch, [MegalodonChecker.cpp](https://github.com/JUrban/vampire/blob/vampire/megalodon1/Shell/MegalodonChecker/MegalodonChecker.cpp) gained roughly 6,800 lines and is now about 11,400 lines. Its certificate dispatch attempts a long sequence of special cases, including demodulation, AVATAR, CNF, inequality splitting, definition rewriting and superposition. This is much broader than the deliberately small initial calculus described in [CERTIFICATE_PLAN.md](https://github.com/JUrban/vampire/blob/vampire/megalodon1/Shell/MegalodonChecker/CERTIFICATE_PLAN.md).

So the report describes a real conceptual pivot, but the code shows only a partial operational pivot.

## The old path is not actually quarantined

The 81,000-line `vampire_reconstruct_megalodon.py` remains present and gained approximately another 418 lines between the two audited branches, including logical reconstruction work rather than merely compatibility plumbing.

More importantly, the new live smoke test imports that old module to check that its parser understands the new certificate records. Thus the new path is still coupled to the old monolith.

Quarantine should mean:

* no new logical changes to the old file;
* no import of it from qualifying tests;
* no success depending on its parser or recovery mechanisms;
* preferably a CI check that it remains unchanged.

It can remain as a diagnostic and comparison tool, but it should not sit on the dependency path of certificate v1.

## Testing: meaningful progress, but the evidence is overstated

There is good work here:

* I independently confirmed that all 18 positive JSON tests were accepted.
* All 11 negative JSON tests were rejected.
* Explicit substitutions, pivots, positions and conclusions are moving to the Vampire side.
* The exporter performs useful self-checks.
* The report is unusually candid about missing real-problem milestones.

But the test story still has important weaknesses:

* The 22 accepted rule names do not each have positive, negative and elaboration coverage.
* Higher-order lambda tests and AVATAR-related support have entered before the first-order MVP is complete.
* Equality factoring is checked using `-allowincompleteqed`; it therefore should not be included in the strict green suite.
* The live cases are tiny generated examples, not ten real source-linked reconstructions.
* The source-map problem remains open.
* The live suite does not reject derived assumptions.
* One of my rebuilt live runs—the factoring example—produced no certificate-clause records under the current portfolio run. This may be schedule/environment dependent, but the integration suite should eliminate that nondeterminism.

I could rebuild and run Vampire and the Python validator. I could not independently rerun the Megalodon kernel suite because the local environment lacks the OCaml toolchain.

## What I would require next

### 1. Add a strict qualifying mode

For example, `--strict-certificate-v1`, with these invariants:

* Any unsupported derived Vampire unit is a hard error.
* `input` is legal only when backed by a source-map entry.
* An `input` with Vampire parents is always rejected.
* `vampire_derived_clause`, `vampire_unexpanded_derived_clause`, AVATAR-component assumptions and analogous sources are rejected.
* No Python `infer_*` routine may be called.
* No `-allowincompleteqed`.
* No import of the old 81k-line reconstructor.

This one mode should define every reported success number.

### 2. Start with already-clausal first-order problems

Do not solve clausification, Skolemization and source-formula reconstruction simultaneously with the inference calculus.

The first real milestone should be:

```text
original CNF clauses
    → explicit Vampire resolution/superposition certificate
    → small deterministic elaboration
    → Megalodon kernel
```

For this milestone, disable AVATAR, HO, lambda, formula-CNF projection, inequality splitting and complex preprocessing. Once ten real CNF examples pass, add preprocessing as a separate certified layer.

### 3. Reduce the calculus to an actual fixed MVP

Something close to:

* `input`
* `rename` or explicit variable normalization
* `substitute`
* `resolve`
* `factor`
* `equality_resolution`
* `paramodulate`
* `reflexive_simplify`
* `contradiction`

Macros are acceptable only if Vampire expands them into those primitives. Adding another Python reconstruction rule should not be the normal response to a failure.

### 4. Separate the implementation physically

The qualifying Python path should have distinct modules for:

* schema/model;
* mechanical certificate checker;
* Megalodon elaborator;
* transitional outline adapter.

Inference recovery, SAT solving, CNF projection search and experimental HO support should live outside those modules. The exact line count is less important than making it impossible for the strict checker to call heuristic reconstruction accidentally.

### 5. Change the scoreboard

A proof counts only if all are zero:

```text
admissions
incomplete-QED allowances
derived assumptions
unmapped inputs
Python-inferred proof steps
unsupported certificate fallbacks
```

Report separately:

* hand-authored certificate unit tests;
* live synthetic integration tests;
* real source-linked problems;
* failures by first unsupported constructor.

## Overall assessment

The worker responded intelligently to the first audit, and the report’s diagnosis is now largely correct. The project is salvageable and has useful implementation assets.

But the branch currently demonstrates the same underlying tendency in a new form: each unsupported Vampire inference causes another exporter special case, certificate constructor, Python search routine or assumed derived clause. Unless that feedback loop is stopped now, the new 6k-line checker will become the next 60k-line reconstructor.

I would give the project one tightly controlled milestone:

> Within roughly five working days, produce ten real, already-clausal first-order problems that pass through the strict path with zero derived assumptions, zero inference recovery, zero incomplete-QED options, and no dependency on the old reconstructor.

If that succeeds, continue incrementally. If it does not, stop adding constructors and simplify the pipeline further.

Q: shouldnt the worker also switch to ocaml (reusing the megalodon code) rather than hacking new things in python? for example, both Ivy and megalodon have lisp/sexp-format utilities?

A: Yes. I would now make that an explicit architectural requirement.

The qualifying importer should be implemented in OCaml as part of Megalodon, using Megalodon’s existing term, type, substitution, conversion, and proof-term machinery. Python can remain for diagnostics and experiments, but it should not be responsible for accepted proof reconstruction.

The strongest reason is not language preference; it is avoiding a second implementation of Megalodon’s semantics.

The current Python code duplicates or approximates:

* term and type representations;
* binders and de Bruijn handling;
* substitution and variable renaming;
* type inference;
* beta/eta normalization;
* equality encodings;
* proposition rendering;
* proof-term construction;
* Megalodon identifier and declaration management.

Megalodon already exposes much of this in [syntax.mli](https://github.com/mgwiki/Megalodon/blob/vampire/megalodon1/src/syntax.mli):

* `tp`, `tm`, and `pf`;
* `tmshift`, `tmsubst`, and proof shifting/substitution;
* `extr_tpoftm` and `check_tpoftm`;
* `extr_propofpf` and `check_propofpf`;
* `conv`, `headnorm`, and `tm_beta_eta_norm`;
* direct proof constructors such as `Hyp`, `Known`, `PTmAp`, `PPfAp`, `PLam`, and `TLam`.

Reimplementing all of that in Python is both unnecessary and a continuing source of semantic mismatches.

## A better division of responsibility

I would use this architecture:

```text
Vampire
  emits explicit, canonical Ivy-style certificate
        ↓
small OCaml S-expression parser
        ↓
typed certificate AST
        ↓
local mechanical rule checker
        ↓
Megalodon pf/term AST
        ↓
existing Megalodon proof checker
```

Vampire should provide all nondeterministic information:

* parent clauses;
* pivot literals;
* substitutions;
* equality orientation;
* rewritten position;
* explicit resulting clause;
* original source identity.

The OCaml importer should do only deterministic local work:

* parse;
* verify each rule’s stated result;
* translate clauses to Megalodon propositions;
* construct a `Syntax.pf`;
* call Megalodon’s existing type/proof checker.

It should never search for a pivot, infer an omitted substitution, try multiple equality orientations, run SAT, or discover a CNF projection.

## S-expressions are probably preferable here

JSON is not intrinsically wrong, but an Ivy-like S-expression format is a natural fit:

```lisp
(certificate vampire-megalodon 1
  (input c1 source_axiom_17
    (clause (pos p (var 0))))

  (input c2 source_axiom_18
    (clause (neg p (const a))))

  (resolve c3
    (parents c1 c2)
    (pivot 0 0)
    (subst ((var 0) (const a)))
    (result (clause)))

  (contradiction c3))
```

Advantages include:

* trivial production from C++;
* trivial recursive parsing in OCaml;
* straightforward comparison with Ivy;
* no JSON-library question;
* easy versioning;
* readable regression fixtures;
* direct structured terms rather than parsing Vampire’s pretty-printed syntax.

Megalodon already has S-expression serialization functions such as `tp_to_sexpr`, `tm_to_sexpr`, and `pf_to_sexpr` in [syntax.ml](https://github.com/mgwiki/Megalodon/blob/vampire/megalodon1/src/syntax.ml). These appear primarily to be printers, so a small matching generic reader may still be needed. But that reader should be perhaps a few hundred lines, not a reason to build thousands of lines of semantic infrastructure in Python. Ivy’s parser and conventions can inform it, subject to licensing and representation differences.

## Do not port the Python implementation

The worker should not translate the current 6,000 lines of Python into OCaml. That would preserve the architectural mistake in a different language.

They should start again from the small certificate specification and implement only:

1. S-expression reader.
2. Certificate datatypes.
3. Source-map validation.
4. First-order term substitution.
5. Resolution.
6. Factoring.
7. Equality resolution.
8. Paramodulation.
9. Proof-term elaboration using existing Megalodon constructors.

Initially, the certificate datatype should make the earlier loophole impossible:

```ocaml
type input =
  { clause : clause;
    source_id : source_id }
```

There should be no generic “input clause” constructor. Loading an input must perform a lookup in the current Megalodon theorem context and verify that the clause is the declared source proposition or an explicitly certified clausification of it. A derived Vampire clause cannot simply be relabelled as an input.

## What Python should still do

Python is useful outside the qualifying path for:

* inspecting legacy Vampire output;
* diagnosing missing certificate constructors;
* corpus and coverage statistics;
* minimizing failing examples;
* comparing certificates;
* generating test data;
* prototyping a proposed constructor before implementing it properly.

But its output should not count as a certified result. In particular, the strict pipeline should neither import nor invoke either Python reconstructor.

## One caution about “reusing Megalodon”

They should reuse Megalodon’s representations and checking primitives, but not its large heuristic automation routines. Calling existing recursive proof search from the importer would merely relocate reconstruction search from Python to OCaml.

The desired importer is closer to a bytecode verifier than a tactic:

```text
read instruction
→ check its operands
→ verify its stated result
→ emit the corresponding fixed proof-term template
```

I would therefore revise the recommendation to the worker to say:

> Freeze the Python certificate implementation as a prototype. Implement certificate v1 natively in OCaml, using an Ivy-style S-expression format and Megalodon’s `tp`/`tm`/`pf`, substitution, conversion and checking infrastructure. Do not port Python inference recovery. No Python path or generic derived-clause assumption may participate in a counted proof.

That is much closer to the original project idea and gives the work a credible endpoint.
