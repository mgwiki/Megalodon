## Verdict

This is a genuine improvement in direction, but not yet a controlled convergence.

The worker followed the central recommendation in form:

* native S-expression certificates;
* an OCaml importer inside Megalodon;
* Python excluded from the nominal counted path;
* explicit reporting of extra assumptions;
* parallel regression testing.

But the qualifying path is still not closed, the source linkage is not semantic, and the new OCaml/C++ implementation has already expanded far beyond the agreed MVP.

I would continue the project, but stop all new inference classes immediately. The next milestone should be ten genuinely closed proofs—not a lower aggregate bridge count across 213 broad examples.

## What is genuinely better

The [July 14 report](https://github.com/mgwiki/Megalodon/blob/vampire/megalodon2/reports/REPORT-2026-07-14.md) is substantially more honest than its predecessors. It clearly says that the 213 passing scripts contain 6,287 bridge assumptions and therefore do not prove the original theorems.

The operational changes are also real:

* Vampire emits a native S-expression certificate.
* Megalodon parses it in OCaml.
* Derived Vampire clauses are no longer silently labelled as ordinary source inputs.
* There are many positive and negative certificate fixtures.
* The source-map requirement rejects missing names and incompatible roles.
* The 213-case harness is a useful integration and performance test.
* Failed broad experiments are described rather than counted.

The 6,287 figure gives an honest lower bound of approximately 29.5 missing inference proofs per passing script.

## P0: “strict” still allows bridge premises

`-vampirecertv1strict` checks certificate structure and some source-map properties, but it does not mean “the emitted theorem has no additional premises.”

The control flow is:

1. `check_certificate_strict` validates the certificate.
2. `emit_simple_megalodon` tries to elaborate each step.
3. When elaboration fails, it calls functions such as `add_clause_inference_bridge`.
4. The bridge is inserted into the theorem assumptions.
5. Megalodon kernel-checks the theorem with that bridge premise.

This makes the 213 passes useful compilation/integration tests, but not reconstructed proofs. The kernel is checking exactly the stronger theorem the report acknowledges.

The [cached parallel harness](https://github.com/mgwiki/Megalodon/blob/vampire/megalodon2/tests/vampire_certificate/run_native_emit_cached_parallel.sh) rejects `admit`, `aby`, and incomplete-QED tokens, but it does not reject `bridge_*` assumptions. It labels every successfully checked script `PASS`.

A strict qualifying mode must instead fail immediately if emitting any step would require a bridge.

## P0: the bridge count undercounts extra premises

The reported `bridge_total 6287` is not necessarily the total number of non-source assumptions.

The [OCaml emitter](https://github.com/mgwiki/Megalodon/blob/vampire/megalodon2/src/vampire_cert_v1.ml) has three premise lists:

```ocaml
proof_assumptions @ assumptions @ bridge_assumptions
```

Only the third is named and counted as `bridge_*`. Other derived premises can be emitted under names such as:

* `vampire_eq_prop_ext`
* `theory_fool_exhaustiveness__*`
* `theory_fool_distinctness__*`
* `theory_predicate_definition__*`
* `definition_input__*`
* `avatar_component__*`
* `avatar_refutation__*`

For example, AVATAR certificates may be structurally/SAT-checked by OCaml, but their result is still introduced into the Megalodon theorem as an assumption rather than elaborated to a kernel proof.

Under the project’s own trust boundary—the importer is untrusted—an OCaml check is not a substitute for a Megalodon proof term.

The scoreboard must count every theorem premise and classify it as exactly one of:

* semantically verified original source premise;
* explicitly approved logical/library theorem;
* forbidden derived premise.

Anything in the third class makes the case non-qualifying.

## P0: “source-linked” currently means label-linked, not proposition-linked

This is the most important newly discovered correctness gap.

`validate_certificate_sources` checks:

* source name exists;
* source role/kind is compatible;
* hashes printed in two places agree;
* definitions and set-reflexivity sources have an equality-shaped certificate input.

It does not check that the certificate input clause or formula is the proposition declared by the corresponding TPTP source.

The unit fixtures demonstrate this directly:

* [native_cert_v1_valid.sexp](https://github.com/mgwiki/Megalodon/blob/vampire/megalodon2/tests/vampire_certificate/native_cert_v1_valid.sexp) introduces `p ∨ q`, `¬p`, and `¬q`.
* [native_cert_v1_source_map_valid.th0.p](https://github.com/mgwiki/Megalodon/blob/vampire/megalodon2/tests/vampire_certificate/native_cert_v1_source_map_valid.th0.p) declares all three corresponding TPTP axioms as `$true`.
* The strict test expects this combination to be accepted.

Therefore a certificate can attach an arbitrary clause to a valid source name. The source hashes do not repair this: the checker compares hash strings in comments, not the certificate proposition against the source proposition.

This means even “zero bridges” would not yet establish reconstruction from the exported source problem.

The fix should be one of:

1. Parse the relevant TPTP declaration and compare its canonical AST to the certificate input.
2. Put a canonical exported-formula hash in both the source map and certificate input and independently recompute it.
3. Preferably, during final integration, resolve the source identifier directly to the original Megalodon `Syntax.tm` and compare against that.

The current strict fixture should become a negative test.

## The OCaml switch is only partial

The worker did switch to OCaml, but the module is still primarily a textual code generator rather than a native Megalodon proof elaborator.

The new module:

* is 6,663 lines;
* contains 352 top-level functions;
* accepts 40 step constructors;
* returns a generated `string` from `emit_simple_megalodon`;
* constructs proof source using formatted strings;
* does not construct `Syntax.pf`;
* does not call `check_propofpf` or `extr_propofpf`.

It does reuse `Syntax.tm`, which is progress. But it then reimplements substantial infrastructure for:

* type and symbol inference;
* de Bruijn aliases;
* lambda rendering;
* proposition rendering;
* clause encodings;
* proof source generation;
* normalization modulo several custom equivalences.

This is exactly the distinction from the previous recommendation:

> Moving the code to OCaml is not enough; the elaborator should construct Megalodon proof ASTs and use Megalodon’s existing checker interfaces.

The intended endpoint should look more like:

```ocaml
val elaborate :
  source_context ->
  certificate ->
  Syntax.tm * Syntax.pf
```

A textual `.mg` dump can remain as a debugging output derived from the native proof object.

## Scope has escaped the MVP again

The still-current [certificate specification](https://github.com/mgwiki/Megalodon/blob/vampire/megalodon2/reports/vampire-megalodon-certificate-spec.md) says that the MVP excludes:

* AVATAR;
* higher-order lambda/de Bruijn rewriting;
* direct demodulation;
* unit-resulting resolution;
* broad preprocessing reconstruction.

It also says AVATAR should not be introduced before 100 real restricted reconstructions.

Yet the OCaml datatype already has 40 constructors, including:

* AVATAR components and SAT refutations;
* Skolemization;
* FOOL;
* CNF;
* rectification and ENNF;
* predicate definitions;
* inequality splitting;
* unit-resulting resolution;
* superposition;
* Boolean simplification;
* definition rewriting.

The module even contains its own SAT satisfiability/RUP checking and CNF transformation machinery.

On the Vampire side, [MegalodonChecker.cpp](https://github.com/JUrban/vampire/blob/vampire/megalodon2/Shell/MegalodonChecker/MegalodonChecker.cpp) is now approximately 21,373 lines—about 10,000 lines larger than the previous audited branch. It contains both native S-expression and legacy JSON exporters, macro expansion, inference-specific reconstruction and extensive metadata logic.

This is not a small Ivy-style proof format anymore. The specification and implementation have diverged dramatically.

## Python was not fully quarantined

Although Python is no longer nominally counted, `vampire_certificate.py` grew by another 872 lines since the prior branch. Those additions include logical elaboration for:

* Boolean simplification;
* contextual equivalence;
* propositional extensionality;
* function extensionality;
* lifted function proofs;
* native certificate conversion.

This is not merely reporting or corpus analysis. It is continued logical reconstruction work.

The correct quarantine rule should be:

* no new proof-producing Python logic;
* Python may inspect and summarize certificates;
* no generated Python proof term may become part of a qualifying result;
* no duplication of new OCaml constructors in Python.

## Evidence and reproducibility problems

The strongest reported artifact lives under `/project/tmp`, not in the repository. The cached certificates and generated proof scripts needed to reproduce `PASS 213` are not committed.

Moreover:

* The report’s validated Megalodon head is `e03d440`.
* The current branch head is `d59d931`, one later logical commit.
* That later commit reintroduces guarded FOOL implication conversion with helper lemmas.
* There is no corresponding committed 213-case result for the current head.

The change may be correct, but the report’s evidence cannot automatically be transferred to it.

I could not independently rebuild Megalodon in this audit environment because the OCaml toolchain is absent. Static inspection was sufficient to establish the strict/source-linking issues above.

## Recommended intervention

I would reject the report’s proposed near-term milestone:

```text
PASS 213
bridge_total substantially below 6287
```

That objective rewards chasing the broad tail of CNF, FOOL, AVATAR, Skolem and higher-order special cases. It recreates the earlier nontermination dynamic.

Replace it with:

> Ten committed, reproducible, source-semantically-linked first-order proofs with zero non-source premises.

The required sequence should be:

1. Add `-vampirecertv1closed`.
2. Make every bridge-producing path an error in that mode.
3. Reject every derived non-`bridge_*` premise too.
4. Bind certificate inputs to their actual source propositions.
5. Restrict the qualifying datatype/schedule to the original nine constructors.
6. Exclude FOOL, CNF, Skolem, AVATAR, lambdas and preprocessing.
7. Construct `Syntax.pf` directly rather than formatting proof text.
8. Commit ten source files and native certificates so the gate is reproducible.
9. Report `CLOSED_PASS`, not ordinary `PASS`.
10. Only after that reaches 10, expand it to 100 restricted cases.

## Overall assessment

The worker has responded intelligently and the project is healthier. The OCaml/S-expression pivot, explicit bridge accounting and parallel harness are valuable.

But the implementation is again expanding much faster than the trusted result:

* 6,663 new OCaml lines;
* roughly 10,000 new Vampire C++ lines;
* another 872 proof-producing Python lines;
* 40 certificate constructors;
* zero demonstrated semantically source-bound, bridge-free reconstructions.

So my recommendation remains “continue, under a hard architectural reset,” not “continue reducing the aggregate bridge count.” The next good commit should mostly introduce rejection conditions and delete qualifying scope.
