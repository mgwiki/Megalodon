# Response to `audit-REPORT-2026-07-15.md`

Date: 2026-07-15

Branch: `vampire/megalodon4`

## Summary

I agree with the audit's main judgment.

The `vampire/megalodon3` branch produced meaningful closed proof
reconstruction evidence: closed mode rejects bridge and derived premises, source
formulas are checked for the supported THF/TPTP fragment, and the committed
closed corpus is useful.  But the implementation is still moving in the wrong
architectural direction.  The Megalodon side is a large textual replay engine,
not a small native proof-term elaborator, and the broad certificate format has
grown well past the Prover9/Ivy-style core.

This branch therefore changes direction:

- stop using broad closed-pass count increases as the main objective;
- preserve the broad textual emitter as an oracle and regression harness;
- focus new work on the audit/MVP core fragment and native proof terms;
- push primitive inference detail into Vampire rather than rediscovering it in
  Megalodon;
- require original-context source glue before claiming Tier 1 success.

## Immediate Adjustment

The inherited local predicate-definition orientation experiment was not carried
forward.  It was a broad textual replay improvement intended to gain a few more
closed passes, and it fits the pattern criticized by the audit.

The concrete code change made on this branch is trust-boundary hardening for
closed textual emission.  `emit_simple_megalodon` now validates the final
generated script against an internal closed-axiom allowlist.  In closed mode,
any generated `Axiom` line must have both an approved name and the exact
approved proposition.  Unknown axioms, or changed propositions for approved
axioms, are rejected by the importer before the `.mg` file is returned.

This does not solve the larger architectural problem, but it moves one audit
concern from a shell-enforced convention into the importer itself.

The next concrete adjustment is the first native proof-term seed:
`-vampirecertv1corepfcheck`.  This mode implies `-vampirecertv1coreclosed`,
constructs a `Syntax.tm * Syntax.pf` result for the currently supported
unit/unit, binary/unit, and binary/binary resolution fragment plus duplicate
binary factoring, and checks it with `Syntax.check_propofpf`.  Unsupported core
rules fail explicitly instead of falling back to textual replay.  This is still
small, but it creates the native elaboration entrypoint that the audit asked
for and covers the committed synthetic clausal-core seed corpus.

The native proof-term seed now also refuses source-less evidence:
`-vampirecertv1corepfcheck` requires `-vampirecertv1source` and a
`megalodon_origin` comment in that source file.  This is not full Tier 1
original-context replay, but it makes the native path provenance-bound and
prevents origin-free exported THF files from being counted as native progress.
The returned native core proof object now carries the source-map binding and
the exact source-assumption proposition for each proof-lambda assumption as
well, so later original-context replay can replace those assumptions by the
corresponding original lemma, local fact, definition, set-reflexivity proof, or
conjecture edge.

The native proof-term seed has also been extended to replay identity
substitution directly.  Non-empty or term-changing substitution still fails
explicitly until Vampire emits enough primitive instantiation data for a native
proof, but no-op substitution steps no longer force the native core path back to
textual replay.

The next native rule is equality resolution for reflexive disequality literals
encoded with Megalodon's real polymorphic equality.  This intentionally does not
prove clauses headed by the old untyped `TMH "="` placeholder; those certificates
must be fixed at the Vampire/export level to carry typed Megalodon equality.

The native core also now has first paramodulation proof-term cases: unit
positive equality into unit positive and negative targets, using the explicit
position/from/to fields emitted by the certificate and Megalodon's Leibniz
equality as the transport principle.  Larger paramodulation clauses still fail
closed until they are decomposed into similarly explicit primitive data.
That support has been generalized to binary target clauses when the equality
parent is still unit: the selected target literal is transported natively, and
the unmodified target literal is reintroduced through the native disjunction
encoding.
The native clause encoding is now recursive rather than binary-only, and the
same unit-equality paramodulation path has a three-literal regression fixture
that rewrites the selected head literal and projects the remaining target tail.

The next core rule added in the same style is binary/unit
subsumption-resolution with an empty side substitution.  The checker validates
the explicit selected literal, side pivot, and result clause before reusing the
same native disjunction-elimination proof term as binary/unit resolution.
Subsumption-resolution steps with non-empty side substitutions still fail closed
until Vampire exports primitive instantiation evidence that can be checked
natively.

## Accepted Audit Criticisms

The following criticisms should be treated as controlling for the next
iteration:

- `-vampirecertv1closed` is meaningful, but it is still an exported-THF-bound
  result, not original-context reconstruction.
- The 157-case corpus and 95-case frontier are regression oracles, not a reason
  to keep adding textual special cases.
- `-vampirecertv1coreclosed` is closer to the intended MVP than the broad
  42-constructor format.
- The current public output shape, effectively `certificate -> string`, should
  be replaced for the core path by a native shape like
  `source_context -> certificate -> Syntax.tm * Syntax.pf`.
- Vampire should emit substitutions, pivots, positions, selected literals, and
  decomposed primitive inference steps explicitly.
- Tier 1 progress requires proofs attached to original Megalodon lemmas,
  definitions, local facts, generated set equalities, and conjectures.

## Next Milestone

The next milestone should be intentionally small:

1. Keep the broad textual emitter compiling and use its closed corpus only as a
   regression oracle.
2. Do not add new broad certificate constructors or arity-specific textual
   helper lemmas.
3. Split the nine-rule core fragment into a small native elaboration layer.
4. Make the native core elaborator construct Megalodon proof terms directly, not
   proof-source strings.
5. Extend Vampire only where necessary to emit exact primitive data for the core
   rules.
6. Produce ten committed original-context, source-bound, closed proofs using
   the core/native path.
7. Only after those ten pass, run held-out or freshly regenerated THF/Vampire
   corpora.

## Scoreboard Going Forward

Results should be reported in this order:

1. Original-context, source-bound, closed proof.
2. Exported-THF-bound closed proof.
3. Synthetic/core closed proof.
4. Integration proof with bridges.

The current branch has substantial Tier 2 and Tier 3 evidence inherited from
`vampire/megalodon3`, but it should not claim Tier 1 success until original
Megalodon context binding is implemented and checked.
