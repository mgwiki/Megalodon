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

The qualifying interchange format is a small Lisp-style S-expression language
emitted by Vampire and parsed directly by Megalodon's OCaml importer. JSON was
used by an earlier diagnostic prototype, but it is not the accepted
certificate path for this branch.

```lisp
(vampire_certificate_v1
  (problem "optional-problem-id")
  (steps
    (formula_input "u1"
      (source axiom "H1")
      (result (formula (atom "P" (const "a")))))
    (clause_input "u2"
      (source axiom "H1")
      (result (clause (pos (atom "P" (const "a"))))))))
```

Literals are S-expressions:

- `(pos <atom>)` for a positive literal,
- `(neg <atom>)` for a negative literal.

Terms and atoms use the same S-expression discipline:

```lisp
(var "x")
(const "a")
(app (const "f") (var "x"))
(atom "P" (const "a"))
(eq (const "a") (const "a"))
```

The OCaml importer may accept a narrow opaque atom form for propositional smoke
tests, but counted Vampire-to-Megalodon reconstruction must use the native
S-expression certificate and Megalodon's checker, not the old Python/JSON
prototype.

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

### `equality_factoring`

Vampire equality factoring. From two positive equalities in one parent,
unify the selected side of the selected equality with the opposite side of the
other equality, delete the selected equality, and add the disequality between
the two remaining sides.

Required fields:

- `parents`: one parent,
- `selected`: selected positive equality,
- `other`: other positive equality,
- `selected_lhs`: the selected side of `selected`,
- `other_rhs`: the side of `other` that is not unified with `selected_lhs`,
- `substitution`: object from variable names to structured terms,
- `clause`.

Side condition:

- `selected` and `other` occur in the parent and are positive equalities,
- the other side of `other` and `selected_lhs` match after `substitution`,
- the conclusion is the substituted parent with `selected` removed plus the
  negative equality between the other side of `selected` and `other_rhs`, modulo
  duplicate deletion and clause ordering.

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

### `subsumption_resolution`

Deletes a main-parent literal justified by a side clause that subsumes the
remaining main clause after resolving against the selected literal.

Required fields:

- `parents`: main parent and side parent,
- `selected`: literal removed from the main parent,
- `side_pivot`: substituted side-parent literal complementary to `selected`,
- `side_substitution`: exact substitution for the side parent,
- `clause`.

Side condition:

- the main parent contains `selected`,
- the side parent contains `side_pivot` after `side_substitution`, modulo
  equality symmetry,
- `side_pivot` is the complement of `selected`,
- the conclusion is the main parent with `selected` removed,
- every remaining literal of the substituted side clause is covered by the
  conclusion, modulo duplicate deletion, clause ordering, and equality symmetry.

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

### `paramodulate_all`

Vampire superposition uses `EqHelper::replace`, which replaces every matching
redex in the selected target literal after the inference substitution. This
constructor records that simultaneous replacement explicitly instead of leaving
the importer to guess which repeated occurrences were rewritten.

Required fields:

- `parents`: equality parent and target parent,
- `equality`: selected positive equality literal from the equality parent,
- `from`: selected equality side,
- `to`: selected replacement side,
- `target`: selected literal from the target parent,
- `positions`: all target positions at which `from` occurs after substitution,
- `substitution`,
- `clause`.

Side condition:

- the equality parent contains `equality`,
- the target parent contains `target`,
- `equality` is positive and becomes `from = to` after the exact substitution,
- `positions` is exactly the complete set of occurrences of `from` in the
  substituted target literal,
- replacing all those occurrences by `to`, and retaining all other substituted
  parent literals except the selected equality and target literals, yields the
  conclusion modulo clause normalization.

### `paramodulate_clause_all`

Vampire simultaneous superposition can also rewrite every matching occurrence
in the non-selected literals of the rewritten parent. This constructor records
that clause-wide replacement explicitly instead of leaving the importer to infer
which other target-parent literals changed.

Required fields:

- `parents`: equality parent and target parent,
- `equality`: selected positive equality literal from the equality parent,
- `from`: selected equality side,
- `to`: selected replacement side,
- `target_rewrites`: list of objects with a target-parent `literal` and all
  `positions` at which `from` occurs in that literal after substitution,
- `substitution`,
- `clause`.

Side condition:

- the equality parent contains `equality`,
- `equality` is positive and becomes `from = to` after the exact substitution,
- `target_rewrites` names exactly the target-parent literals containing `from`
  after substitution, and gives the complete set of matching positions in each,
- replacing every occurrence of `from` by `to` in the substituted target parent,
  and retaining all other substituted equality-parent literals except the
  selected equality, yields the conclusion modulo clause normalization.

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

Current migration fields for branching Skolemization use `branch_v1`
contracts attached to Skolem macro edges. In addition to branch unit,
parent index, binder count, parent instantiations, introduced witnesses, and
source/target formulas, Vampire now emits explicit branch proposition roles:

- `skolem_macro_edge_N_contract_branch_proposition_count`
- `skolem_macro_edge_N_contract_branch_proposition_M_role`
- `skolem_macro_edge_N_contract_branch_proposition_M_formula`

The required roles at this stage are `source` and `target`; additional roles
such as `source_child_body` or `target_child_arg_0` expose immediate
decomposition points of the branch source/target formulas. Megalodon parses
these records and fail-closed validates that the `source` and `target`
propositions match the corresponding branch formulas. These records are not
yet a complete proof object, but they are the next certificate surface needed
to replace Megalodon-side guessing about which branch proposition each local
proof variable proves.

For direct existential branch sources, Vampire also emits explicit branch
choice records:

- `skolem_macro_edge_N_contract_branch_choice_count`
- `skolem_macro_edge_N_contract_branch_choice_M_symbol`
- `skolem_macro_edge_N_contract_branch_choice_M_replaced_var`
- `skolem_macro_edge_N_contract_branch_choice_M_type`
- `skolem_macro_edge_N_contract_branch_choice_M_predicate`
- `skolem_macro_edge_N_contract_branch_choice_M_body`
- `skolem_macro_edge_N_contract_branch_choice_M_witness_term` (optional)
- `skolem_macro_edge_N_contract_branch_choice_M_transport_rule`
- `skolem_macro_edge_N_contract_branch_choice_M_witnessed_body`

The current intended shape is a single direct branch source
`vampire_exists_prop (fun x => body)`, where `symbol` is the Skolem symbol
introduced for `x`, `predicate` is the emitted lambda, and `body` is the
lambda body still open over `replaced_var`. Megalodon parses standalone
`LAMV`/`VLAMV` predicates as real lambda terms and validates these records by
default. The checker verifies that the choice symbol belongs to the
branch-introduced witness set and that the emitted predicate/body/witness data
are mutually consistent after alias rewriting.

The current transport rule is `choice_witness_substitution`.  Under that rule,
`witnessed_body` must be exactly the branch-choice `body` with `replaced_var`
substituted by Vampire's emitted witness term, modulo the importer's normal
term normalization.  This is source-side transport evidence, not a complete
Megalodon proof of the Skolem/epsilon conversion; it prevents the importer from
rediscovering that proposition by heuristic proof inspection.

When a branch-choice occurrence is backed by such a contract, Megalodon now
extracts a typed `skolem_witness_transport` record in `vampire_kernel_elab.ml`.
That record has two deliberately separate projections.  The legacy symbol
projection preserves the Skolem name and local template for diagnostics and
compatibility.  The qualifying-oriented term projection rewrites the emitted
local choice occurrence directly to the contract-backed definition, avoiding a
cleanup path whose correctness depends on a temporary `sK` delta entry.

This metadata is still not enough for a qualifying Skolem proof by itself.  A
qualifying branch-choice step must also include, or deterministically elaborate,
an explicit witness-transport proof object for the local equation
`sK := Eps predicate`.  The returned Megalodon proof must not rely on a
certificate-local global delta entry for that conversion.  Until that transport
object exists, branch-choice records are validation and selection data, not a
license for broad search over local choice terms.

## Deferred from the Clausal Kernel: AVATAR

AVATAR is not part of the first clausal small-kernel milestone. It is handled
as a separate SAT/split certificate layer connected to first-order split
clauses.

The current branch has started that separate layer. Vampire emits named
`kernel_v1` objects for AVATAR component, definition, split dependency, split,
and refutation records. Megalodon now parses selected AVATAR records as typed
certificate data. For `avatar_component`, the result/conclusion clauses,
component literals, and single split descriptor must match the parsed
certificate step. For `avatar_definition`, the component split descriptor,
component clause sexpr, variable sort count, de-Bruijn sort count, and result
clause must match the parsed certificate step. For `split_dependency`, the
owner-to-suffixed-step mapping, result clause, dependency count, each
dependency split descriptor, component clause sexpr, and component sort-count
fields must match the parsed certificate step. For `avatar_split`, the source
unit must be the first certificate parent, SAT literal descriptors must match
the result split literals, component-parent references must match the remaining
certificate parents, component split clauses must match their split descriptors,
and literal-class/parent-variable-binding count fields must enumerate present
records. For `avatar_refutation`, the SAT input map and SAT proof trace are
checked: input origins must name earlier certificate units, SAT proof ids must
be positive and unique, RUP parents must be earlier SAT proof steps, recorded
parent clauses must match, RUP side conditions are checked, and the final SAT
proof step must be the empty clause.

This is still not the final proof reconstruction result. The next spec step is
to define how the checked AVATAR/SAT object is elaborated into Megalodon proof
terms, or to define a tiny dedicated AVATAR/SAT proof kernel whose checker
constructs those terms. Counted proof-reconstruction milestones must not count
AVATAR records merely because their metadata structurally validates.

Current proof-term status: the native preprocess checker now has a direct
proof-producing seed for the AVATAR/SAT layer. It can prove an identity
`avatar_split` step and a two-parent `avatar_refutation` over complementary
split-unit clauses without installing `vampire_avatar_*` certificate-derived
known primitives. It also has a direct proof-producing seed for a positive
`avatar_definition`/`avatar_component` pair: the split atom is excluded from
the local proof-variable spine, installed as a conservative delta definition,
checked through kernel conversion, and then used by native preprocess
`resolve` steps to reach the empty clause without installing
`vampire_avatar_*` or `vampire_resolve_*` certificate-derived known
primitives. This does not yet cover multi-step SAT/RUP AVATAR refutations or
full original-context composition.

The next proof-term seed covers a restricted multi-step SAT trace. When every
SAT input is exactly a proved split clause and every RUP step is a binary
resolution step over earlier SAT clauses, Megalodon now maps SAT literals to
`split_N` propositions and replays the trace with native resolution proof
templates. This is still intentionally smaller than full SAT/RUP checking:
general unit-propagation explanations, non-split component clauses, and
original-context composition remain open.

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
a small checked subfragment to a Megalodon proof script:

- `input` clauses become theorem assumptions,
- opaque propositional `resolve`, `factor`, and `contradiction` steps become
  local `claim`s,
- structured first-order `substitute` steps are elaborated by universal
  instantiation of their parent clause,
- structured first-order `equality_resolution` steps are elaborated by
  instantiating the parent clause and closing the negative reflexive equality
  branch with the local Leibniz reflexivity proof,
- structured first-order `paramodulate` steps are elaborated by transporting
  the selected target atom through the selected Leibniz equality. Positive
  target literals use forward transport; negative target literals transport an
  assumed rewritten atom backward before applying the original negated literal.
  Retained parent literals are reintroduced into the conclusion clause by
  disjunction elimination/introduction,
- the final empty clause proves `False`.

This first elaborator is intentionally limited to set-sorted first-order terms
and ground resolution after substitution. Paramodulation elaboration currently
requires ground instantiated parent clauses. It is a no-admit kernel-checking
smoke path, not yet the full first-order Megalodon importer.

## Branch-Choice Replay Prototype

The native Megalodon checker now has a guarded prototype for consuming parsed
Skolem branch-choice contracts during CPS replay. When a staged branch witness
is backed by an explicit Vampire `skolem_branch_choice` record, the checker
collects the local `Eps_*` choice terms that occur in the candidate proof and
tries them as replacement needles for the introduced witness symbol. The
definition installed for that symbol is still the closed witness term derived
from the Vampire branch-choice contract, not the local proof occurrence.

The checker also records the term-binder depth of each local `Eps_*`
occurrence. This supports an opt-in diagnostic path that unshifts a local
choice occurrence into a template and tries replacing the branch Skolem name by
that scoped choice template. The diagnostic is disabled by default because each
template requires a full proof check and `183:4` showed that speculative
template search can noticeably slow the focused loop without solving the
branch. Set `MEGALODON_CERT_BRANCH_CHOICE_TEMPLATE_LIMIT` to a positive integer
to enable a bounded number of such attempts.

This prototype is intentionally fail-closed:

- branch-choice records are parsed and validated by default, but they do not
  by themselves count as a proof of the Skolem transformation;
- local choice-term candidates are considered only for staged branch witnesses
  whose symbols are named by parsed branch-choice contracts;
- if one local choice occurrence would be transported to multiple distinct
  definitions, that occurrence is discarded before proof checking;
- candidate definitions are installed into the delta tables only while the
  transformed proof is being checked;
- failed candidates restore the previous delta state and are not committed to
  the witness replacement table;
- successful candidates must pass `check_propofpf` through the existing final
  refutation checker.

Current evidence on 2026-07-19: this prototype preserves the focused baseline
but does not yet solve the active `183:4` branch-local witness target. The
parallel four-target gate with branch-choice contracts enabled still reports
`10654:21` and `172:4` passing, with `183:4` and `233:4` failing. Debug output
for `183:4` shows that `u30` stages 20 contract-backed local branch-choice
replacement candidates, but the transformed proof is rejected because the
proof-local `vampire_exists_prop_choice` term and the proposition containing
`sK1` are not convertible under the current closed branch witness definition.
Current evidence on 2026-07-20 supersedes the older `183:4` note.  In the
original-source `and3I` prefix, Vampire emits the needed branch-choice records
for `sK0` and `sK1`, and Megalodon selects them.  The live checker still
rejects the proof because the returned proof depends on the certificate-local
Skolem-to-epsilon conversion at the wrong scoped proposition.  A global
`MEGALODON_CERT_FAIL_FAST_SKOLEM_CPS=1` diagnostic is too coarse: it regresses
the focused prefix from three reconstructed commands to one.  The next design
step is therefore a real small-kernel witness-transport proof object, not
broader default search over local choice terms and not a blanket fail-fast
toggle.

Additional evidence on 2026-07-20: direct term projection for
contract-backed branch-choice transports is implemented and unit-tested, and
the focused qualifying harnesses still pass the three-proof frontier.  The
original-source `and3I` prefix still fails closed.  Its current debug trace
shows the remaining mismatch is proof-level, not selection-level: the expected
implication argument contains `#sK1`, while the available checked proof was
constructed through Megalodon's `Eps_prop` choice witness.  The next accepted
milestone must therefore construct or emit the scoped proof transport between
those propositions.

Follow-up evidence on 2026-07-20: the importer no longer requires there to be
exactly one staged branch witness before it collects contract-backed local
choice transports.  Multi-witness entries are allowed, but the collection is
still fail-closed: any local choice occurrence with conflicting candidate
definitions is filtered out before the temporary delta check.  The focused
frontier remains unchanged at `FalseE`, `andEL`, and `andER`; prefix-4 still
fails closed at `and3I`.

A broader experiment that stored Skolem formula-table entries with generated
symbols eagerly expanded to `Eps_prop` was rejected.  It regressed the first
qualifying proof, showing that explicit witness expansion cannot simply be
applied at formula storage time.  The missing object is still a scoped
proof-term transport at the direct Skolem construction boundary, or equivalent
Vampire-emitted small-kernel certificate data for that transport.

Latest evidence on 2026-07-20: CPS witness replacement application now expands
each replacement through the existing generated/native symbol aliases before
rewriting proof terms or propositions, and local existential binder
propositions include fallback witness replacements.  This fixes an incidental
representation asymmetry between names such as `sK1` and `#sK1`, but it is not
a Skolem proof rule.  The qualifying frontier remains unchanged:
`FalseE`, `andEL`, and `andER` pass, and `and3I` still fails closed at the
scoped Skolem/choice transport boundary.

The extracted elaborator now also provides
`skolem_witness_transport_proof_replacements_with_aliases`.  This is the
canonical way to turn a checked branch-choice transport into proof-term
replacement pairs covering the local choice occurrence and all introduced-name
aliases.  Importer call sites should use this helper rather than rebuilding
alias expansion locally.
