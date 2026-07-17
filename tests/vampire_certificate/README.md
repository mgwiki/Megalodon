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
`--proof_extra lean --skolemization syntactic --shuffle_input off`. Override
`VAMPIRE_PROOF_ARGS` only when intentionally testing another proof-export
configuration.

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
For AVATAR definitions and split dependencies, it requires the component split
level/variable/sign, structured component clause, component variable/de-Bruijn
sort metadata, dependency count, and dependent result clause.
For AVATAR split clauses, it requires the source clause, result clause or
formula, SAT literals, previous split count, component-parent count,
zero-indexed `component_parent_ref_i` unit/split/clause fields, literal-class
count, and parent variable binding count that Vampire computes during split
reconstruction. The literal-class and parent-variable-binding counts must
enumerate complete indexed maps.
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
`cnf_formula_clause`, and annotated instantiation `substitute` steps, because
those steps are checked by native proof templates and do not use
certificate-derived `Known` propositions.

Use `-vampirecertv1preprocesspfcheck` only as a fail-closed native
preprocessing checker. Unlike the older transitional frontier runs, this mode
must not install certificate-derived `Known` propositions. If it reaches a
preprocessing or macro step that still needs such a trusted implication, it
fails and names the offending primitive. This is intentional: the July 16 audit
reclassified the old preprocessing pass counts as structural plumbing evidence,
not proof reconstruction evidence.

The legacy structural diagnostic harnesses may opt in to the old trusted
primitive behavior by setting
`MEGALODON_CERT_ALLOW_TRANSITIONAL_PREPROCESS_KNOWN=1`; they report
`PREPROCESS_STRUCTURAL_PASS`, not proof-term passes. The focused diagnostic is:

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
parallel with the explicit transitional-known diagnostic opt-in. Passing cases
are structural/native-AST plumbing checks, not counted reconstruction proofs.
Failures are still useful for classifying the next missing real proof-term rule
or Vampire-side primitive expansion, but the qualifying path is
`-vampirecertv1corepfcheck` plus future certified preprocessing steps that do
not use the transitional-known escape hatch.

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
