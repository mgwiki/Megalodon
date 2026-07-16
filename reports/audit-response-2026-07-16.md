# Audit Response for REPORT-2026-07-16

Date: 2026-07-16

Branch: `vampire/megalodon5`

Audit file:

- `reports/audit-REPORT-2026-07-16.md`

## Summary

The audit is accepted. Its main correction is that the broad
`-vampirecertv1preprocesspfcheck` frontier was overclassified. Although it
constructs native `Syntax.pf` terms syntactically, many preprocessing and macro
steps were justified by dynamically adding the desired proposition to the
`Known` theorem table and then applying it. That is a hidden bridge assumption.

Therefore:

- the old `PREPROCESS_PF_PASS` results are reclassified as structural
  native-AST plumbing diagnostics;
- the genuine proof-term seed is `-vampirecertv1corepfcheck`;
- counted progress must now focus on trust reset, isolated clausal kernel,
  real live core proofs, original-context source binding, and certified
  preprocessing transformations.

## Code Changes Made

### Dynamic Known Insertion Is No Longer Default

`src/vampire_cert_v1.ml` now routes the native preprocessing path's
certificate-derived `Known` propositions through a single helper:

```ocaml
install_transitional_known
```

By default this helper fails closed with an error naming the offending
primitive. The old behavior is available only for explicitly marked structural
diagnostics by setting:

```sh
MEGALODON_CERT_ALLOW_TRANSITIONAL_PREPROCESS_KNOWN=1
```

This is not a qualifying proof-reconstruction mode.

### Preprocessing Harnesses Are Reclassified

The preprocessing frontier/audit harnesses now opt in to the transitional
behavior explicitly and report:

```text
PREPROCESS_STRUCTURAL_PASS
```

not `PREPROCESS_PF_PASS`.

Affected files:

- `tests/vampire_certificate/run_native_cert_v1_preprocess_pf_audit.sh`
- `tests/vampire_certificate/run_native_cert_v1_preprocess_pf_frontier.sh`
- `tests/vampire_certificate/run_native_live_preprocess_pf_frontier.sh`
- `tests/vampire_certificate/README.md`

### Design Plan Updated

`reports/VAMPIRE-MEGALODON-DESIGN-PLAN-2026-07-16.md` was updated to:

- reclassify the old 97/100 preprocessing run as E4 structural evidence;
- remove the old "make preprocessing 100/100 first" milestone;
- put trust reset first;
- require isolated kernel modules rather than further monolith growth;
- define separate evidence classes E1-E4 and test stages T0-T4;
- specify a concrete `source_context` API shape.

### Source-Obligation Audit Added

The source validator now exposes a structured audit record:

```ocaml
type source_obligation_audit = {
  source_obligations_total : int;
  source_obligations_formula_checked : int;
  source_obligations_formula_unsupported : int;
  source_obligations_formula_missing : int;
  source_obligations_equality_checked : int;
  source_obligations_set_reflexivity_checked : int;
  source_obligations_true_checked : int;
}
```

The new CLI flag:

```sh
-vampirecertv1sourceaudit
```

prints those counts for a certificate/source-map pair. The new parallel
harness:

```sh
TMPDIR=/project/tmp JOBS=10 \
tests/vampire_certificate/run_native_cert_v1_source_obligation_audit.sh
```

ran over the default 96-case committed closed-corpus selection and reported:

```text
AUDIT_PASS 96
cases 96
total 388
formula_checked 388
formula_unsupported 0
formula_missing 0
equality_checked 2
set_reflexivity_checked 0
true_checked 0
```

This is not counted as proof reconstruction. It is an audit boundary for the
next source/preprocessing milestone: the checked source formulas are now
measured explicitly, and generated equality/set-reflexivity obligations are
separated from ordinary source claims.

### Original-Context Source Resolver Added

The new flags:

```sh
-vampirecertv1sourcecontext
-vampirecertv1sourcecontextstrict
```

make Megalodon load the main `.mg` file before checking the certificate, then
audit certificate source bindings against the loaded context. Hash-backed
`known`/`axiom` entries are checked by applying `Known hash` to the certificate
source proposition; definition hashes are checked for presence in the
definition environment; local/unhashed sources are counted separately.

The smoke test now covers both sides:

- strict source-context audit rejects fake hash-backed source-map comments
  when the hashes are not present in the loaded context;
- a generated Megalodon axiom is assigned a real hash, exported into a tiny
  THF source map and native certificate, and accepted with `known_checked=1`.

This is still not full original-context reconstruction. It is the first
mechanical resolver for global source facts and a fail-closed gate before
using those facts to discharge source assumptions in the final proof term.

## Accepted Audit Corrections

### 1. The 100 Strict Live Run Is Integration Evidence

The strict live run proves that Vampire can regenerate certificates and that
Megalodon can structurally validate their syntax, source links, and metadata.
It does not prove those certificates by native proof terms and must not be
reported as closed proof reconstruction.

### 2. The Preprocessing Frontier Was Non-Qualifying

The old preprocessing frontier used dynamic `Known` insertion for
transformations such as rectification, FOOL, ENNF, Skolemization, CNF
projection, AVATAR, and some clausal rules downstream of transitional parents.
Those results are structural diagnostics only.

### 3. The Real Seed Is the Small Core

`-vampirecertv1corepfcheck` is the credible native proof-term seed. Its current
weakness is coverage: it is mostly synthetic. The next target is real live
Vampire proofs through this core or through Vampire-side primitive lowering
into this core.

### 4. The Monolith Must Stop Growing

Future qualifying implementation should be extracted into modules such as:

- `vampire_kernel_syntax.ml`
- `vampire_kernel_check.ml`
- `vampire_kernel_elab.ml`
- `vampire_source_context.ml`

The existing `vampire_cert_v1.ml` remains a legacy parser/oracle location and
may receive trust-boundary fixes, but not broad new reconstruction logic.

### 5. Original-Context Reconstruction Needs a Concrete API

The plan now includes the intended source proof representation:

```ocaml
type source_proof =
  | GlobalKnown of string * Syntax.tm
  | LocalHyp of int * Syntax.tm
  | Definitional of Syntax.tm * Syntax.pf
  | Generated of Syntax.tm * Syntax.pf

type source_context = source_id -> source_proof
```

This is still design, not complete implementation.

## Revised Execution Order

1. Keep dynamic `Known` insertion out of counted native paths.
2. Extract the real clausal core from the legacy module.
3. Add a Vampire primitive builder and use it for at least one frequent macro.
4. Find or create ten real live primitive-core Vampire proofs.
5. Implement original-context source binding.
6. Add proof-producing Smolka-style transformations one at a time.
7. Only then run a fresh 100-theorem original-context or exported-THF-bound
   gate.

## Current Status After Response

Completed in this response:

- branch switched to `vampire/megalodon5` in both repositories;
- audit accepted and committed into the local evidence chain;
- dynamic preprocessing `Known` insertion made fail-closed by default;
- old preprocessing pass labels changed to structural diagnostics;
- design plan updated to match the audit.
- source-obligation auditing added for source-map inputs and committed
  closed-corpus measurement.
- original-context source resolver added for hash-backed source inputs.

Not completed:

- extraction of kernel modules;
- Vampire primitive builder;
- ten real live core proofs;
- original-context source binding;
- certified Skolemization and other Smolka-style transformations;
- final 100-theorem proof-reconstruction gate.

The project is therefore still active and not complete.
