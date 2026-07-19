# Vampire Certificate Tests

This directory tests the replacement certificate path described in
`reports/vampire-megalodon-certificate-spec.md`.

The first smoke tests intentionally cover only binary resolution, factoring,
explicit substitution, equality resolution, paramodulation, and contradiction.
They are not a substitute for
Megalodon kernel checking. Their purpose is to prevent the new path from
accepting malformed certificate constructors while the Vampire exporter and
Megalodon elaborator are built.

Run:

```sh
tests/vampire_certificate/run_native_cert_v1_smoke.sh
```

This is the primary certificate smoke test. It checks the OCaml
`-vampirecertv1` importer against native S-expression fixtures and should be the
first test used for counted reconstruction work.
Use `-vampirecertv1strict` with `-vampirecertv1` for structural certificate
validation plus source-map validation. Strict mode is not a closed proof gate:
it can still emit theorem premises for unsupported reconstruction steps. Use
`-vampirecertv1closed` when a result should count as a zero-extra-premise
reconstruction attempt. Closed mode implies strict checking and fails emission
if any bridge premise, derived-theory premise, AVATAR premise, definition-input
premise, predicate-definition premise, or unproved helper premise would be added
to the generated theorem. Successful cached closed runs are reported as
`CLOSED_PASS`, not `PASS`.

The native checker also has an initial proof-emission path:

```sh
bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_valid.sexp \
  -vampirecertv1emit /project/tmp/native_cert_v1_valid_emit.mg \
  /project/tmp/empty.mg
```

This currently emits a no-admit Megalodon proof only for a small propositional
fragment: input assumptions, unit/binary-tail resolution, two-literal
propositional factoring/condensation, exact no-op substitution copies, and
contradiction. Unsupported rules, non-propositional literals, and
term-changing substitutions fail closed with a `simple Megalodon emitter`
error. Input assumptions are named from their original certificate source, for
example `src_axiom_<source>__<step>`, so the generated proof skeleton remains
connected to the original Megalodon/TPTP lemma or conjecture name instead of
only exposing Vampire unit ids. When `-vampirecertv1source` is supplied, the
emitter uses the Megalodon source-map name rather than a TPTP-escaped fallback.
The path is intentionally small: it is the seed of native proof-term/text
elaboration from the OCaml certificate checker, not a replacement for the
strict certificate gate over larger live corpora.

The default smoke command is native-only:

```sh
tests/vampire_certificate/run_smoke.sh
```

For live corpora, use:

```sh
tests/vampire_certificate/run_native_live_parallel.sh
```

This script runs Vampire in parallel, extracts only the native S-expression
certificate block emitted by Vampire, and checks it with Megalodon's OCaml
`-vampirecertv1` importer. It rejects certificates that contain
Vampire-derived source assumptions; a counted success must be traced through
certificate steps rather than imported as a fresh input. By default it invokes
Vampire with the same extra proof-detail options used by Megalodon's live
`-vampireabyproof megalodon` bridge:
`--proof_extra lean --skolemization standard --shuffle_input off`. Override
`VAMPIRE_PROOF_ARGS` only when intentionally testing another proof-export
configuration.

For the tracked 100-case THF gate over currently known-solvable hammer
exports, use:

```sh
VAMPIRE=/path/to/vampire \
tests/vampire_certificate/run_known_solvable_strict_100.sh
```

This uses `known_solvable_strict_100.list`, runs 20 Vampire jobs in parallel
with `-t 10`, checks every native certificate with strict source-map
validation, and then runs the native primitive and `kernel_v1` metadata audits.
The list is curated from previously solved `examples/hammer/out1` proof-output
filenames rather than the lexicographic first-100 slice, which is known to
spend most of its time on repeat Vampire timeouts.

For fast focused replay of original Megalodon `aby` targets, use:

```sh
VAMPIRE=/path/to/vampire \
tests/vampire_reconstruction/run_native_aby_targets_parallel.sh
```

This runs the selected `examples/hammer/100thms_12_h.mg` targets in parallel
with `-vampireabytargetstop`, `--proof megalodon`, strict native checking, a
10-second Vampire timeout, and `/project/tmp` artifacts. The default target set
contains the current strict-native pass cases `172:4`, `183:4`, and `233:4`.
The `233:4` case covers a Skolem/CPS replay where the delayed sibling branch
must be shifted into the current term context.
For line-233-style Skolem replay debugging, add
`MEGALODON_CERT_DEBUG=1 MEGALODON_CERT_FAIL_FAST_SKOLEM_CPS=1` so Megalodon
stops at the first Skolem CPS candidate rejection instead of continuing through
the slower fallback proof. Add
`MEGALODON_CERT_FAIL_FAST_SKOLEM_CONTRACT=1` when the target is specifically
the shadow result-to-target continuation contract; this diagnostic stops at
the first syntactic post-replacement contract mismatch and is intentionally
stricter than the default final proof checker.

For freshly exported TH0 files containing `% megalodon_source_map` comments,
set `CHECK_SOURCE_MAP=1` to additionally run `-vampirecertv1source` for every
accepted native certificate. Use `PROBLEM_DIR` or `PROBLEMS_FILE` to select the
fresh source-mapped corpus. The script also writes `rule_counts.txt` under the
work directory so broad runs show which native certificate constructors were
actually exercised.

For the fast source-linked gate over known Vampire-solvable THF exports, run:

```sh
tests/vampire_certificate/run_source_linked_strict_100.sh
```

It re-exports the current Megalodon file to `$TMPDIR`, then checks the tracked
`source_linked_strict_100.list` in parallel with strict source-map validation.
The list is intentionally a stable solved subset so normal iteration does not
spend most of its time repeating known Vampire timeouts.

Set `STRICT_CERT_V1=1` to run the live certificates through
`-vampirecertv1strict`; these stricter runs require source maps and traced SAT
proofs for AVATAR refutations.

To measure the current real-case proof-term frontier without rerunning Vampire,
run:

```sh
tests/vampire_certificate/run_native_cert_v1_real_core_frontier.sh
```

This wraps the closed-corpus core audit, splits eligible cases into synthetic
`core.cnf.*` fixtures and real/source-entry certificates, and writes blocker
counts under `/project/tmp/latest_native_cert_v1_real_core_frontier`. On
`vampire/megalodon5` after the checked ENNF/definition-input and annotated
instantiation updates, the expected result is `REAL_CORE_ELIGIBLE 91`,
`SYNTHETIC_CORE_ELIGIBLE 23`, `EXCLUDED 58`. The first blockers are now
`skolem_formula`, unannotated `nonidentity_substitute`, and AVATAR/definition
macro rules. That is not a failure of the clausal kernel; it means the
remaining real examples need proof-producing Skolemization, more Vampire-side
primitive expansion metadata, and AVATAR/definition composition before their
later clausal refutations can count.
The first source-input exception is `set_reflexivity`: when the source map
classifies an input as `set_reflexivity` or `local_set_reflexivity`, the native
proof-term checker proves the reflexive Megalodon equality directly instead of
adding it as a source hypothesis.

To audit source-input obligations without rerunning Vampire, use:

```sh
TMPDIR=/project/tmp JOBS=10 \
tests/vampire_certificate/run_native_cert_v1_source_obligation_audit.sh
```

This runs over the committed closed-corpus list by default and reports how many
certificate source inputs have declaration formulas checked by the supported
THF fragment, how many are unsupported or missing formulas, and how many are
generated equality/`set_reflexivity` obligations. This is a source-linking
measurement gate, not proof reconstruction evidence by itself.

To audit whether hash-backed source inputs are actually available in the loaded
Megalodon context, add:

```sh
-vampirecertv1sourcecontext
```

or the fail-closed variant:

```sh
-vampirecertv1sourcecontextstrict
```

When this flag is present, Megalodon checks the main `.mg` file before the
certificate so the certificate audit can resolve `known`/`axiom` source hashes
through the real `sigdelta` environment. The audit reports resolved knowns,
missing knowns, mismatches, resolved definition hashes, missing definition
hashes, and local/unhashed sources. This is the first original-context source
resolver gate. Standalone certificate checks can resolve hash-backed globals;
the live `vampireaby` path also passes the current theorem-local proof context
to the resolver, so `local_fact` entries can be checked as `Hyp i` bindings.
Conjecture composition and complete original-goal reconstruction remain open.

When native proof-term checking is also enabled, resolved hash-backed source
inputs are passed into the elaborator as `Known hash` proofs and are not added
as lambda-bound source assumptions. The smoke suite covers this with a generated
Megalodon axiom whose real hash is inserted into a tiny THF source map and then
used by `-vampirecertv1corepfcheck`. This currently consumes global
`known`/`axiom` entries in standalone certificate checking. Local theorem
hypotheses are resolved only when the certificate is checked from the live proof
state, where Megalodon still has the original `cxpf` hypothesis list.
Native proof-term checker output also reports the number of source assumptions
remaining after source-context proofs are consumed; the smoke suite asserts
that hash-backed knowns and generated `set_reflexivity` equalities reduce that
count.
Strict source-context mode fails on missing, mismatched, or unresolved source
obligations. A matched `local_definition` is accepted because it has already
been turned into a checked source proof by the resolver.

For repeatable non-overlapping corpus slices, use:

```sh
tests/vampire_certificate/run_native_corpus_slice.sh
```

Set `PROBLEM_DIR`, `SLICE_START`, `SLICE_SIZE` or `SLICE_END`, `WORK_DIR`,
`JOBS`, `VAMPIRE_SECONDS`, `WALL_SECONDS`, and `MIN_PASS` to control the run.
The defaults use `/project/tmp`, `JOBS=20`, `VAMPIRE_SECONDS=10`,
`CHECK_SOURCE_MAP=1`, and `STRICT_CERT_V1=1`. The wrapper writes the selected
filename list to `/project/tmp/native_slice_START_END.list` and then delegates
to `run_native_live_parallel.sh`.

To reuse an existing native live run without rerunning Vampire, emit and check
Megalodon proof scripts from its accepted native certificates:

```sh
PROBLEM_DIR=/project/tmp/native_source_linked_corpus_1000 \
JOBS=20 \
tests/vampire_certificate/run_native_emit_cached_parallel.sh \
  /project/tmp/latest_megalodon_native_live
```

This script filters `PASS` rows from one or more native run `summary.tsv` files,
runs `-vampirecertv1emit`, rejects generated files containing `admit`, `aby`, or
`-allowincompleteqed`, and checks each emitted `.mg` file with `bin/megalodon`.
It defaults to strict source-map validation, 20-way parallelism, and
`/project/tmp`.

To audit the Vampire-side small-kernel metadata without rerunning Vampire, use:

```sh
tests/vampire_certificate/run_kernel_v1_metadata_audit.sh \
  /project/tmp/latest_megalodon_native_live
```

This checks the `step_extra ... kernel_v1` records emitted by Vampire. It
requires the `schema=prover9-small-kernel-v1` marker plus parent/conclusion
clause fields on every record, requires selected/other literals to include
their substituted forms, and requires rewrite-position records to carry the
explicit `from`, `to`, substituted target/equality, and rewritten target fields.
It rejects any `..._unit=uN` metadata reference that does not point to a unit
id present in the same native certificate.
It rejects a `kernel_v1` record unless the surrounding `step_extra` unit id is
the same id as its `conclusion_unit`.
It also rejects premise-like unit references in `kernel_v1` metadata unless
the referenced unit has already appeared earlier in that certificate; only
`conclusion_unit` may name the unit produced by the current kernel record.
For every clausal kernel record with a `conclusion_clause`, it requires
Vampire's explicit `result_clause`, `result_literal_count`, and
`result_literal_i` conclusion map.
For every formula-result kernel record with `result_formula`, it requires
Vampire's explicit `conclusion_formula`.
For every reported parent, it also requires `parent_i_clause`,
`parent_i_literal_count`, and `parent_i_literal_j` fields so replay does not
have to re-parse incomplete parent metadata to recover clause and literal
positions.
Whenever Vampire reports a `parent_i_substitution`, it also requires
`parent_i_substituted_literal_count` and `parent_i_substituted_literal_j` fields
rendered after applying that substitution.
For first-class substitution steps, Vampire may also emit a `kernel_v1`
`rule=instantiation` record.  The metadata audit requires the parent unit,
parent clause, explicit substitution, result clause, substituted parent
literals, and the `primitive_expansion_requires=substitute` contract.  This is
the Prover9/Ivy-style replacement target for opaque non-identity `substitute`
replay: the checker should receive typed instantiation data from Vampire rather
than reconstructing it heuristically.
Set `REQUIRE_SUBSTITUTE_METADATA=1` when auditing freshly regenerated Vampire
certificates to require every non-identity first-class `substitute` step to
have such an instantiation record. Empty `(subst)` aliases are allowed because
they close primitive chains without performing an instantiation. This stricter
mode is intentionally not the default for older cached fixtures produced before
Vampire emitted metadata for generated substitution helpers.
For macro kernel rules currently expanded into first-class certificate steps
(`superposition`, demodulation `rewrite`, `unit_resulting_resolution`,
`subsumption_resolution`, `resolution`, `factoring`, `equality_resolution`,
and `equality_factoring`), it requires the
Vampire-emitted `primitive_expansion=prefix`,
`primitive_expansion_prefix=uN`, and `primitive_expansion_requires=...`
contract. This keeps the broad Vampire rule record tied to an explicit
Prover9/Ivy-style primitive expansion instead of an opaque reconstruction hint.
For formula transformation records with `proof_parent_count`, it requires
`source_unit`, `result_formula`, and every `parent_i_unit`/`parent_i_formula`.
For unit-resulting resolution, it also requires Vampire's trace main parent,
unit parent, selected/substituted selected literal, substituted unit literal,
and remaining clause state after each pivot.
For CNF clause extraction, it requires the source unit/formula or clause,
resulting clause, and clause index/count metadata from Vampire's CNF
transformation extra.
For skolemization, it accepts formula-result kernel records and requires the
source formula, result formula, proof parent count, introduced symbol, replaced
variable when available, and declaration metadata that Vampire already records.
`introduced_count` must enumerate a complete indexed introduced-symbol map.
For formula rectification, it accepts formula-result kernel records and requires
the source formula, result formula, proof parent count, and Vampire's explicit
renaming source/target/substitution metadata when a nonempty renaming is
reported. `renaming_count` must enumerate complete source/target/substitution
triples.
For formula copies, it requires source/result formulas and the
`copy_kind=formula_term_identity` marker that Vampire emits only after comparing
the formula-term S-expressions.
For non-identity formula normalization, it requires source/result formulas,
Vampire's underlying normal-form rule, and explicit source/target/path
transformation pairs computed by the Vampire normal-form traversal.
`transformation_pair_count` must enumerate complete source/target/path triples.
For AVATAR refutations, it requires the emitted SAT input map and SAT proof
data. `sat_input_count` and `sat_proof_step_count` must enumerate complete
indexed maps. Every RUP SAT step must include its parent count, parent ids,
parent clauses, and parent ids that resolve to earlier proof steps in the same
record.
For FOOL formula elimination, it requires source/result formulas and explicit
source/target/path transformation pairs computed by Vampire while it still has
the pre- and post-elimination formula trees.
`transformation_pair_count` must enumerate complete source/target/path triples.
For FOOL exhaustiveness, it requires a parentless
`axiom_kind=all_is_true_or_false` kernel record with the result clause and both
literal fields rendered by Vampire.
For AVATAR components, it requires the result clause, rendered literals, and the
split level/variable/sign fields read from Vampire's component clause split set.
The strict Megalodon importer validates those `avatar_component` `kernel_v1`
fields against the parsed certificate step: the result/conclusion clauses must
match, the component `literal_i` fields must match the non-split literals, and
the single split descriptor must match the actual `split_N` literal using
Vampire's convention that `split_positive=1` is represented by a negative
component split literal. `native_cert_v1_avatar_component_kernel_split_bad.sexp`
is the negative regression for this boundary.
For AVATAR definitions and split dependencies, it requires the component split
level/variable/sign, structured component clause, component variable/de-Bruijn
sort metadata, dependency count, and dependent result clause.
The strict importer validates `avatar_definition` `kernel_v1` records against
the parsed certificate step: split variable and polarity must match, the
component clause sexpr must match the result clause, and the variable and
de-Bruijn sort counts must enumerate present fields.
It also validates `split_dependency` `kernel_v1` records against the
suffixed first-class `split_dependency` certificate step: the owner unit must
match, the result clause must match, dependency count must match, each
dependency split descriptor must match the certificate dependency, component
clause sexprs must match, and component variable/de-Bruijn sort counts must
enumerate present fields.
For AVATAR split clauses, it requires the source clause, result clause or
formula, SAT literals, previous split count, component-parent count,
zero-indexed `component_parent_ref_i` unit/split/clause fields, literal-class
count, and parent variable binding count that Vampire computes during split
reconstruction. The literal-class and parent-variable-binding counts must
enumerate complete indexed maps. The strict Megalodon importer validates
`avatar_split` `kernel_v1` records against the parsed certificate step:
`source_unit` must be the first certificate parent and refer to an earlier
unit, SAT literal variables/polarities must match the split literals in the
certificate result, structured component-parent references must match the
remaining certificate parents, component split clauses must match their
split descriptors, and literal-class/parent-variable-binding counts must
enumerate present fields. `native_cert_v1_avatar_split_kernel_sat_bad.sexp`
is the negative regression for this boundary.
For AVATAR refutations, it requires the empty result clause, SAT input clauses,
input origin units, and SAT proof steps emitted by Vampire.
The strict Megalodon importer also parses those `avatar_refutation` fields as
typed SAT certificate data: input origin units must refer to earlier
certificate steps, the input clauses must match the certificate step, SAT proof
ids must be positive and unique, RUP parents must be earlier SAT proof steps,
recorded RUP parent clauses must match the referenced steps, the RUP
side-condition must hold, and the final SAT proof step must be the empty SAT
clause. `native_cert_v1_avatar_refutation_kernel_bad_parent.sexp` is the
negative regression for this boundary.
For truth conflicts, it requires the selected true/false conflict literal,
selected literal index, parent clause, and result clause.
For predicate definitions and folds, it requires the introduced/defined symbol,
definition formula, source formula, definition parent formula, and result formula
that Vampire used for the fold.
The point of this gate is to keep new work on the Prover9/Ivy-style certificate
path: Vampire must emit primitive replay data, rather than leaving Megalodon to
recover it by broad OCaml-side reconstruction.

To audit the already-emitted native primitive proof records without rerunning
Vampire, use:

```sh
tests/vampire_certificate/run_native_primitive_audit.sh \
  /project/tmp/latest_megalodon_native_live
```

This checks the explicit native records for the frequent clausal small-kernel
steps: `substitute`, `paramodulate`, `equality_symmetry`,
`equality_resolution`, `equality_resolution_constraints`, `resolve`, `factor`,
`equality_factoring`, `equality_factoring_constraints`, `fool_atom_lift`,
`ennf_formula`, `skolem_formula`, `cnf_literal`, `cnf_formula_clause`,
`formula_copy`, `formula_term_copy`, `rectify_formula`,
`fool_exhaustiveness`, and `truth_conflict`, plus the first-class AVATAR records `avatar_component`,
`avatar_definition`, `avatar_split`, `avatar_refutation`, and
`split_dependency`. The gate requires each present rule family to expose the
fields Megalodon should replay
mechanically: parent ids, substitutions, equality/target parents, rewrite
positions, literal or pivot indices, source and target formulas, paths,
introduced Skolem symbols, CNF clause indices, truth-conflict literals, and
result clauses. It also rejects primitive references to missing or later proof
steps, while allowing `step_proposition`, `step_variable_sorts`, and
`step_extra` to reuse ids as metadata. It is intentionally separate from the
`kernel_v1` metadata audit because these are first-class certificate steps, not
`step_extra` annotations.
For any `kernel_v1` macro record with a primitive-expansion contract, this
audit also verifies that the certificate contains a final proof step with the
kernel unit id and at least one required primitive step sharing that unit
prefix. Clausal decompositions often use suffixed ids such as
`u123_paramodulate`, `u123_resolve0`, or `u123_fool_atom_0`; preprocessing
steps such as `ennf_formula`, `skolem_formula`, `cnf_formula_clause`,
`formula_copy`, `formula_term_copy`, `rectify_formula`,
`fool_exhaustiveness`, `truth_conflict`, `avatar_component`, `avatar_split`,
`avatar_refutation`, and `avatar_definition` may reuse the kernel unit id
exactly. `split_dependency` uses a suffixed id such as
`u123_split_dependency` because it records dependency metadata for an owner unit
that may already have a clause-producing primitive step.

Native certificates spell Vampire HOL lambdas and existential formula binders as
`(VLAMV "X" sort body)` in new output. This is parsed as the explicit
`vLAM`/`dbN` term representation used by FOOL, ENNF, and Skolem preprocessing,
not as a Megalodon kernel lambda. The importer still accepts older cached
`(LAMV ...)` certificates as the same representation so the committed closed
corpus remains replayable.

`run_native_live_parallel.sh` runs this primitive audit and the `kernel_v1`
metadata audit by default after a successful live run. Set
`AUDIT_NATIVE_PRIMITIVES=0` or `AUDIT_KERNEL_V1_METADATA=0` only for
deliberately tiny focused experiments, or lower individual minimums such as
`MIN_FACTOR=0` when a selected corpus is not expected to exercise a rule. Use
`MIN_EQUALITY_FACTORING` and `MIN_EQUALITY_FACTORING_CONSTRAINTS` to require
focused coverage of the equality-factoring primitive records.
Because live runs regenerate certificates with the current Vampire exporter,
they also default to `AUDIT_SUBSTITUTE_METADATA=1`, which makes the
`kernel_v1` audit require explicit instantiation metadata for every
non-identity first-class `substitute` step. Set it to `0` only when comparing
against older cached certificates that predate the substitution-helper metadata
emitter.

Set `CLOSED_CERT_V1=1` on the cached emitter harness to request
`-vampirecertv1closed`. In that mode a case passes only when emission introduces
no non-source theorem premises; the summary status is `CLOSED_PASS`. Ordinary
`PASS` rows remain useful integration evidence, but they are not closed proof
reconstruction successes if generated scripts contain bridge or derived
premises. The closed harness also scans emitted scripts for known non-source
assumption prefixes (`bridge_`, `definition_input__`, `avatar_`, `theory_`,
predicate-definition helper assumptions). It checks scripts containing axioms
with `-hf` and rejects any "not indexed as previously known" warning, so an
axiom can count only when Megalodon recognizes it as an indexed library fact
such as the HF `prop_ext` theorem. Other premises must be replayed as Megalodon
claims before the case can count.

Closed emission also performs an importer-side axiom policy check. Every
generated `Axiom` line must match the small approved closed prelude by both name
and exact proposition; unapproved axioms or changed approved axiom statements
are rejected before a proof script is written. This is still transitional: the
audit-preferred endpoint is to resolve approved logical principles from the
original Megalodon context or an exact indexed-hash basis, not to grow this
allowlist.

`run_native_cert_v1_closed_corpus.sh` defaults to the committed
`closed_textual_pass_cases.list`, which records the cases that currently pass
the transitional textual closed-emission gate. The larger
`closed_cases/` directory also contains frontier certificates that are useful
for native proof-term and primitive-certificate development but still fail the
textual emitter because they would require bridge premises. To audit any other
subset, pass `CASE_LIST=...`; to deliberately run the full frontier, provide a
case list containing all tracked case names instead of relying on the default
pass list.

Use `-vampirecertv1coreclosed` for the audit/MVP clausal fragment. This implies
strict and closed checking, then rejects every certificate constructor outside
the core clause proof language before emission. The shell audit below still
pre-filters fixtures for reporting, but the final guard is now enforced by
Megalodon itself.

Use `-vampirecertv1corepfcheck` for the first native proof-term seed. This
implies `-vampirecertv1coreclosed`, then constructs and kernel-checks a
`Syntax.pf` proof term for the currently supported core seed:
unit/unit, binary/unit, and binary/binary resolution, binary/unit
subsumption-resolution with explicit side substitution including binary side
remainders already present in the result, duplicate literal factoring in
larger clauses,
explicit instantiation/substitution, and equality resolution over reflexive disequalities
encoded with Megalodon's actual polymorphic equality, equality symmetry over
typed Megalodon equality literals in unit and binary clauses, plus unit/unit
paramodulation into positive and negative targets, and unit-equality
paramodulation into larger target clauses, using explicit Vampire
position/from/to data. Clauses are represented by native recursive
impredicative false and disjunction terms. It deliberately rejects unsupported
core rules, including non-unit equality parents for paramodulation and untyped
`TMH "="` equality, instead of falling back to textual replay. This is
not yet the full nine-rule core elaborator; it is the initial checked
entrypoint for replacing the broad `certificate -> string` path with a native
`certificate -> Syntax.tm * Syntax.pf` path. This mode also requires
`-vampirecertv1source` to contain `megalodon_origin` metadata, so native
proof-term evidence is tied at least to a specific exported Megalodon source
obligation instead of to a source-less THF artifact. The native proof result
also carries the source binding and exact source-assumption proposition for
each proof-lambda assumption, in assumption order, so the checked proof term can
be audited against the source map rather than only against internal certificate
step IDs.

To run the committed synthetic core seed through that native proof-term path,
use:

```sh
tests/vampire_certificate/run_native_cert_v1_core_pf_audit.sh
```

This gate runs `-vampirecertv1corepfcheck` over either an explicit
`CASE_LIST` or the tracked `core.cnf.*` closed fixtures and requires all
selected cases to report `CORE_PF_PASS`, including source-origin reporting for
every checked proof term. A rule is eligible for `coreclosed` only when it is
intended to have native proof-term support. The gate now includes a narrow
source-entry layer for `formula_input`, `formula_term_input`, identity
`formula_term_copy`, checked `rectify_formula`, checked FOOL Boolean lifting
and exhaustiveness (`fool_atom_lift`, `fool_formula`, `fool_bool`,
`fool_exhaustiveness`), checked `ennf_formula`, checked `definition_input`,
checked inequality intro/split, `formula_copy`, `cnf_literal`,
`cnf_formula_clause`, annotated instantiation `substitute` steps, and
result-context opening for `factor` steps with retained variables, because
those steps are checked by native proof templates and do not use
certificate-derived `Known` propositions. The focused
`native_cert_v1_open_derived_resolve_valid` fixture covers a quantified parent
derived by `factor`, then opened by `resolve` against a closed unit. The
negative fixture `native_cert_v1_open_dropped_parent_bad` locks the opposite
case: a parent step variable that is absent from the result context must be
explained by an explicit Vampire substitution, otherwise theorem opening fails
closed before the primitive rule is tried.

Use `-vampirecertv1preprocesspfcheck` only as a fail-closed native
preprocessing checker. Unlike the older transitional frontier runs, this mode
must not install certificate-derived `Known` propositions. If it reaches a
preprocessing or macro step that still needs such a trusted implication, it
fails and names the offending primitive. This is intentional: the July 16 audit
reclassified the old preprocessing pass counts as structural plumbing evidence,
not proof reconstruction evidence.

The first AVATAR proof-producing seed in this mode is
`native_cert_v1_avatar_split_refutation_pf_valid.sexp`. It proves an identity
`avatar_split` step and a two-parent `avatar_refutation` whose parents are
complementary split-unit clauses, without installing `vampire_avatar_*`
certificate-derived `Known` primitives.

The next seed is `native_cert_v1_avatar_component_pf_valid.sexp`. It proves an
`avatar_definition` by treating the introduced split atom as a conservative
delta definition, derives the matching `avatar_component`, uses native
preprocess `resolve` proof terms to consume split/source units, and closes the
empty clause without `vampire_avatar_*` or `vampire_resolve_*`
certificate-derived `Known` primitives. Multi-step SAT/RUP AVATAR refutations
and original-context composition remain open proof-term work.

`native_cert_v1_avatar_refutation_sat_resolution_pf_valid.sexp` is the first
multi-step SAT trace seed. It accepts the restricted case where every SAT input
is exactly a proved split clause and each RUP step is a binary split-clause
resolution step. The checker replays those SAT steps with the same native
resolution templates used for ordinary `Resolve`, and rejects unsupported RUP
shapes instead of installing trusted implications. General RUP unit-propagation
traces over non-split component clauses remain open.

The focused cached-corpus preprocess gate now runs without the old trusted
primitive opt-in. It reports `PREPROCESS_STRUCTURAL_PASS` for historical
compatibility with earlier audit output, but the selected cached cases are
checked by native proof terms and reject certificate-derived `Known`
propositions by default. The focused gate is:

```sh
tests/vampire_certificate/run_native_cert_v1_preprocess_pf_audit.sh
```

To measure how far that native proof-term path is from the broader
preprocessing-closed corpus, use:

```sh
tests/vampire_certificate/run_native_cert_v1_preprocess_pf_frontier.sh
```

This first selects the `run_native_cert_v1_preprocess_closed_audit.sh`
eligible cases, then runs `-vampirecertv1preprocesspfcheck` over them in
parallel. Passing cases are still cached-corpus evidence rather than final
original-context reconstruction, but they are no longer justified by
transitional preprocess `Known` primitives. Failures are useful for classifying
the next missing proof-term rule or Vampire-side primitive expansion. The final
qualifying path still requires original-context composition and the held-out
100-theorem gate.

For live THF problems, use:

```sh
tests/vampire_certificate/run_native_live_preprocess_pf_frontier.sh
```

On the July 16 100-case source-linked list, the old live frontier structurally
checked 94/100 generated certificates with transitional `Known` primitives
enabled. This is E4 structural evidence only. It should be used to classify
missing transformations and macro expansions, not as proof reconstruction
evidence.

For the audit-recommended restricted milestone, use:

```sh
tests/vampire_certificate/run_native_cert_v1_core_closed_audit.sh
```

This is intentionally stricter than the broad closed corpus. It first filters
tracked closed fixtures to certificates using only the small core clause-proof
constructors plus the narrow proof-producing source-entry rules. The source
entry rules are `formula_input`, `formula_term_input`, identity
`formula_term_copy`, checked `rectify_formula`, checked FOOL Boolean lifting
and exhaustiveness (`fool_atom_lift`, `fool_formula`, `fool_bool`,
`fool_exhaustiveness`), checked `ennf_formula`, checked `definition_input`,
checked inequality intro/split, `formula_copy`, `cnf_literal`,
`cnf_formula_clause`, and annotated instantiation `substitute` steps.
It still excludes unsupported preprocessing-heavy rules such as Skolemization,
AVATAR, predicate definitions, theory FOOL clauses, unannotated non-identity
substitution, and definition rewrite chains. By default it requires at least
ten whitelist-only cases before delegating to the closed corpus checker.
If it fails with
`CORE_ELIGIBLE 0`, that is an honest statement that the current committed closed
fixtures are broad source-linked reconstructions rather than the restricted
first-order milestone requested by the audit.
The audit run also writes `rule_counts.txt`, `excluded_rule_counts.txt`, and
`cases_by_rule/*.list` under `/project/tmp/latest_native_cert_v1_core_closed_audit`
so the next reconstruction work can target repeated blocking classes instead
of isolated examples.  It also writes `first_excluded.tsv`,
`first_excluded_rule_counts.txt`, and `cases_by_first_blocker/*.list`.  These
files preserve the first unsupported constructor in certificate order, which is
the closest audit signal to a Prover9/Ivy frontier: the next Vampire-side
primitive expansion should make that first blocker disappear rather than
adding downstream reconstruction around later consequences.  The
`near_core_nonidentity_substitute.list` file records certificates whose only
core exclusion is non-identity substitution; those are the target set for
redesigning the native core proof-term representation around per-step universal
instantiation.
Selected cases are checked with `-vampirecertv1coreclosed`, not only with the
broader `-vampirecertv1closed` mode.
The same eligible case list is also checked with `-vampirecertv1corepfcheck`,
so the counted core corpus cannot silently drift away from the native
`Syntax.pf` proof-term path.

For the non-identity substitution frontier, use:

```sh
tests/vampire_certificate/run_native_substitution_frontier_audit.sh
```

This scans native certificates for non-identity `substitute` steps and checks
that every substituted parent variable that actually occurs in the parent step
has an explicit sort in the parent `step_variable_sorts` metadata.  Extra
replay bindings for variables absent from the parent are reported separately as
vacuous bindings; they are an emitter-cleanup target, not a typed-instantiation
blocker.  The audit does not make those substitutions core; it identifies
whether fresh Vampire output contains enough typed instantiation data for the
next small-kernel proof-term extension.

For the next layer above the clausal core, use:

```sh
tests/vampire_certificate/run_native_cert_v1_preprocess_closed_audit.sh
```

This gate permits the certified THF preprocessing fragment: formula
inputs/copies, rectification, FOOL elimination, classical FOOL exhaustiveness,
true/false truth conflicts, ENNF/CNF projection, and the same core clause
rules. It still excludes Skolemization, AVATAR, introduced definitions,
inequality splitting, and other broad macro steps. A selected case must contain
at least one preprocessing rule, so the clausal core corpus alone cannot
satisfy it. The summary status for selected and checked cases is
`PREPROCESS_CLOSED_PASS`.  Like the core audit, it writes
`first_excluded.tsv`, `first_excluded_rule_counts.txt`, and
`cases_by_first_blocker/*.list` under
`/project/tmp/latest_native_cert_v1_preprocess_closed_audit`; those files are
the preferred guide for the next preprocessing certificate primitive because
they identify the first unsupported transformation in certificate order.

For the explicit Skolemization layer above preprocessing, use:

```sh
tests/vampire_certificate/run_native_cert_v1_skolem_closed_audit.sh
```

This gate permits the preprocessing fragment plus `skolem_formula` and the
same clausal rules, and it requires each selected case to contain at least one
Skolemization step.  It still excludes AVATAR, introduced definitions,
inequality splitting, and other broader macros.  The summary status for
selected and checked cases is `SKOLEM_CLOSED_PASS`.  Like the lower-layer
audits, it writes `first_excluded.tsv`, `first_excluded_rule_counts.txt`, and
`cases_by_first_blocker/*.list` under
`/project/tmp/latest_native_cert_v1_skolem_closed_audit`, making the next
unsupported layer explicit instead of hiding it in broad closed-corpus counts.

To measure the current Skolem native proof-term frontier without allowing
certificate-derived transitional `Known` primitives, use:

```sh
tests/vampire_certificate/run_native_cert_v1_skolem_pf_frontier.sh
```

This first selects the cached `run_native_cert_v1_skolem_closed_audit.sh`
eligible cases, then runs `-vampirecertv1preprocesspfcheck` over them in
parallel without setting
`MEGALODON_CERT_ALLOW_TRANSITIONAL_PREPROCESS_KNOWN=1`. This is a frontier
diagnostic, not a passing gate. The older cached Skolem cases mostly predate
the current Vampire `VLAMV`/explicit-source Skolem output and are now reported
as `STALE_SKOLEM_NO_SOURCE`; they should be regenerated before being used as
evidence for the current Skolem proof-term path.
The checker phase is strict and bounded by `CHECK_TIMEOUT` seconds per case
(default `30`) so one slow cached proof cannot stall the whole frontier run.
Older cached certificates whose Skolem or rectification proof objects still
use unnamed `ALL`/`LAM` binders instead of current `VLAMV` metadata are
classified as `STALE_UNNAMED_BINDERS`; those should be regenerated with the
current Vampire branch before being treated as reconstruction blockers.

To check the current live Vampire path for nested Skolem proof terms, use:

```sh
tests/vampire_certificate/run_native_live_skolem_pf_smoke.sh
```

This regenerates a representative THF proof with Vampire, requires the native
certificate to contain `skolem_formula` and named `VLAMV` binders, and checks
`-vampirecertv1preprocesspfcheck` without allowing transitional
certificate-derived `Known` primitives.

To regenerate the cached Skolem-selected frontier with the current Vampire
binary and check the resulting proof terms, use:

```sh
tests/vampire_certificate/run_native_live_skolem_pf_frontier.sh
```

This selects the same Skolem-heavy cases as
`run_native_cert_v1_skolem_closed_audit.sh`, runs Vampire once per THF problem
in parallel with a 10-second prover timeout, extracts each native certificate,
and checks `-vampirecertv1preprocesspfcheck -vampirecertv1strict` without
`MEGALODON_CERT_ALLOW_TRANSITIONAL_PREPROCESS_KNOWN=1`. It is the preferred
Skolem frontier signal when the cached certificates are stale.

To check a live Vampire binary's Skolemization metadata emission, use:

```sh
VAMPIRE_BIN=/path/to/vampire TMPDIR=/project/tmp \
  tests/vampire_certificate/run_vampire_skolem_metadata_smoke.sh
```

This focused smoke runs one TH0 problem with a 10 second Vampire timeout and
requires explicit witness, dependency, sort, and choice-principle metadata for
both nullary and dependent Skolem symbols. Megalodon then strictly validates
the generated certificate, including the checked dependency metadata.

For the source/definition fact layer above Skolemization, use:

```sh
tests/vampire_certificate/run_native_cert_v1_definition_closed_audit.sh
```

This gate permits the Skolemization layer plus `definition_input` facts that
closed mode can justify without adding non-source premises.  It still excludes
AVATAR, definition rewrite chains, inequality splitting, and broader macros.
The summary status for selected and checked cases is `DEFINITION_CLOSED_PASS`.
As with the lower staged gates, it writes `first_excluded.tsv`,
`first_excluded_rule_counts.txt`, and `cases_by_first_blocker/*.list` under
`/project/tmp/latest_native_cert_v1_definition_closed_audit`.

For the AVATAR layer above definition inputs, use:

```sh
tests/vampire_certificate/run_native_cert_v1_avatar_closed_audit.sh
```

This gate permits the definition layer plus AVATAR definition, component,
split-dependency, split, contradiction, and refutation records that closed mode
can validate without adding non-source premises.  It still excludes inequality
splitting, definition rewrite chains, and broader macros.  The summary status
for selected and checked cases is `AVATAR_CLOSED_PASS`.  It also writes
`first_excluded.tsv`, `first_excluded_rule_counts.txt`, and
`cases_by_first_blocker/*.list` under
`/project/tmp/latest_native_cert_v1_avatar_closed_audit`.

For the two terminal edge-case layers currently present in the committed
closed corpus, use:

```sh
tests/vampire_certificate/run_native_cert_v1_inequality_closed_audit.sh
tests/vampire_certificate/run_native_cert_v1_definition_rewrite_closed_audit.sh
```

The inequality gate permits the AVATAR layer plus `inequality_name_intro` and
`inequality_split`; the definition-rewrite gate permits the AVATAR layer plus
`definition_rewrite_chain`.  Each default minimum is one because the committed
corpus currently contains one closed case of each kind.  These gates are not
broad milestone evidence; they prevent the final known tracked edge cases from
falling out of closed validation while larger live corpora are expanded.

To run every staged closed gate and prove that the selected layer lists form a
disjoint cover of the committed `closed_cases` corpus, use:

```sh
tests/vampire_certificate/run_native_cert_v1_layered_closed_audit.sh
```

This aggregate gate runs the core, preprocessing, Skolemization, definition,
AVATAR, inequality, and definition-rewrite audits, then assigns each selected
case to its highest applicable layer before comparing the resulting disjoint
cover with all tracked `*.native.sexp` fixtures. It is a staged frontier check,
not a claim that every tracked fixture currently passes the transitional
textual closed-emission gate. The separate `closed_textual_pass_cases.list`
records that smaller textual pass set. The aggregate gate is still not a
substitute for fresh live larger-library evaluation.

For the core layer, the native `-vampirecertv1corepfcheck` gate is the
authoritative proof-term check. The legacy simple Megalodon textual emitter is
still run as a diagnostic because it is useful for inspecting generated
scripts, but its bridge-CNF failures do not by themselves refute the native
core proof-term result.

To export a Megalodon development once and then check the resulting source-mapped
TH0 corpus in parallel, use:

```sh
tests/vampire_certificate/run_source_linked_corpus_parallel.sh
```

Set `MEGALODON_FILE`, `LIMIT`, `JOBS`, `VAMPIRE_SECONDS`, `WALL_SECONDS`, and
`WORK_DIR` to control the corpus and runtime. Temporary corpora and outputs
default to `/project/tmp`. This wrapper enables source-map validation and
strict certificate checking by default; set `STRICT_CERT_V1=0` only for
diagnostic non-counted runs.

The older Python/JSON prototype smoke script is now named
`run_legacy_python_smoke.sh`. It remains useful for diagnostics and regression
comparison, but its successes do not count as accepted Vampire-to-Megalodon
reconstruction.

The legacy smoke script also uses `--emit-megalodon` on the propositional
`valid_resolution.json` certificate and the first-order
`valid_substituted_resolution.json` and
`valid_equality_resolution_refutation.json` and
`valid_paramodulation_refutation.json` and
`valid_paramodulation_negative_refutation.json` and
`valid_paramodulation_side_literals_refutation.json` and
`valid_prop_paramodulation_refutation.json` and
`valid_prop_equality_symmetry_refutation.json` and
`valid_definition_input_refutation.json` certificates, then checks the generated
files with `bin/megalodon`. Those generated proofs are required to contain no
`admit`, no `aby`, and no `-allowincompleteqed`.

The separate `run_vampire_outline_smoke.sh` script runs tiny FOF and THF TPTP
problems through a Vampire binary that emits `megalodon_certificate_clause(...)`
records and explicit `megalodon_certificate_step(...)` records where Vampire
already knows the normalized proof object. It converts the printed outline to
the small JSON certificate fragment, emits Megalodon, and checks it with
`bin/megalodon`. It currently covers the real-output bridge for clause
inputs/derived preprocessing assumptions, Vampire-side `definition_input`
function-definition records, Vampire-side exact `resolve` records,
Vampire-side exact `equality_resolution` records, Vampire-side exact `factor`
records for duplicate-literal contraction, Vampire-side top-level
empty-substitution `paramodulate` records for simple demodulation, and
Vampire-side `paramodulate` plus `equality_symmetry` multi-step records for
definition folding that needs an atomic symmetry step. It also covers
Vampire-side `substitute` plus `resolve` multi-step records for substituted
binary resolution, and Vampire-side `substitute`/optional `equality_symmetry`
plus `paramodulate` expansions for simple superposition. It also covers typed
proposition equality, higher-order application terms, and uniquely determined
resolution-like clause endings. Equality-resolution/factoring/paramodulation
steps that need explicit substitutions or nested or simultaneous rewrite
positions and the remaining unsupported CNF/FOOL transformations are still
recorded or bridged outside the final normalized Vampire certificate until
Vampire exports richer certificate steps for them too.
