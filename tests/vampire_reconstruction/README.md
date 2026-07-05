# Vampire Reconstruction Suite

This suite checks Megalodon's TH0 hammer obligations against Vampire proof
output.

It uses Megalodon itself to generate the current TH0 files from
`examples/hammer/100thms_12_h.mg`, then selects the first 100 generated
obligations whose source line is listed as HO-Vampire-solvable in
`examples/hammer/ATPresults2025`.  The selector intentionally ignores the
stale character columns in `ATPresults2025`; the current checkout generates the
same line numbers with slightly different columns.

Run generation and selection only:

```sh
python3 scripts/vampire_reconstruct_megalodon.py --generate-only
```

Run the full 100-obligation suite:

```sh
VAMPIRE=/path/to/vampire tests/vampire_reconstruction/run_100_th0.sh
```

The driver exports all TH0 problems first, then keeps several Vampire
subprocesses running in parallel and finally writes/checks a manifest of the
captured proof outputs.  To use a scratch directory outside the repo and more
workers:

```sh
TMPDIR=/project/tmp \
VAMPIRE=/path/to/vampire \
MEGALODON_VAMPIRE_JOBS=20 \
tests/vampire_reconstruction/run_100_th0.sh \
  --work-dir /project/tmp/megalodon_vampire_reconstruction
```

With a Vampire build or schedule that differs from the one used to create
`ATPresults2025`, collect the first 100 successful proofs from the candidate
pool:

```sh
VAMPIRE=/path/to/vampire tests/vampire_reconstruction/run_100_th0.sh --collect-successes
```

Collect Lean proof-reconstruction artifacts from a Vampire build with
`--proof leancheck` support:

```sh
TMPDIR=/project/tmp \
VAMPIRE=/path/to/vampire \
python3 scripts/vampire_reconstruct_megalodon.py \
  --work-dir /project/tmp/megalodon_vampire_leancheck \
  --limit 100 \
  --timeout 10 \
  --jobs 20 \
  --proof-mode leancheck \
  --collect-successes
```

LeanChecker mode asks Vampire for Lean output with the required
`--output_mode lean --proof_extra lean --skolemization syntactic
--shuffle_input off` options.  The manifest check requires a complete Lean
payload (`theorem fullProof` through `end vamproof`) and rejects fatal Vampire
markers.  It does not run the Lean kernel by itself; that requires a local Lean
toolchain and the `VampLean` module imported by Vampire's generated files.
LeanChecker mode is a reference/artifact mode for the existing Vampire
reconstruction code; it is not the target checker for this port.

Collect Megalodon reconstruction artifacts from a Vampire build with
`--proof megalodon` support.  This is the preferred fast path: Megalodon
exports all THF obligations once, then the driver runs Vampire workers in
parallel and records the successful outputs in a manifest.

```sh
TMPDIR=/project/tmp \
VAMPIRE=/path/to/vampire \
python3 scripts/vampire_reconstruct_megalodon.py \
  --work-dir /project/tmp/megalodon_vampire_megalodon \
  --limit 100 \
  --timeout 10 \
  --jobs 20 \
  --proof-mode megalodon \
  --collect-successes
```

The recorded artifacts can be revalidated without rerunning Vampire.  Use
`--jobs` to hash and check payloads concurrently:

```sh
python3 scripts/vampire_reconstruct_megalodon.py \
  --check-existing /project/tmp/megalodon_vampire_megalodon/manifest.jsonl \
  --jobs 20
```

When Vampire emits `megalodon_source_line(...)` candidates, the manifest
checker can extract those source files and check them with Megalodon in
parallel:

```sh
python3 scripts/vampire_reconstruct_megalodon.py \
  --check-existing /project/tmp/megalodon_vampire_megalodon/manifest.jsonl \
  --jobs 20 \
  --check-megalodon-sources
```

Add `--require-megalodon-sources` once the Vampire backend is expected to emit
a checked Megalodon source candidate for every recorded proof.

Vampire's Megalodon backend also emits an admitted claim skeleton when it can
render the original formula-level proof steps and renderable clause steps as
Megalodon propositions.  This is a development artifact, not a trusted
certificate: each rendered Vampire step is written as a `claim S...` with
`admit`, and the file is checked only with `-allowincompleteqed`.
When the Python checker writes skeleton `.mg` files, it adds comments linking
the skeleton back to the source Megalodon file, enclosing theorem, and `aby`
line/column, plus the dependency names parsed from simple `aby ...` source
lines. It also writes `index.jsonl` in the skeleton directory with source,
dependency, theorem, claim, and remaining-admit counts for each file.  The checker performs
a conservative fill pass before writing: claims whose proposition exactly
matches an earlier axiom or claim, up to `forall` binder renaming, are proved
with `exact`; it also fills small proof-term patterns such as `A -> A`,
Leibniz equality reflexivity/transitivity, and one-step applications of earlier
universal implications when all premises are already known or directly
provable.  For Vampire `function definition` proof steps that introduce fresh
set symbols or rendered fresh function aliases, it turns the fresh symbol into
a Megalodon `Definition`, proves the matching claim by definitional
reflexivity, and uses those definitions to fill later definitionally reflexive
equalities.  It also fills finite successor-induction applications of the form
`P Empty -> (forall x, P x -> P (ordsucc x)) -> P (ordsucc ... Empty)`.
When a checked source candidate proves the same proposition as an admitted
skeleton claim, the checker inlines that proof body into the skeleton claim so
the generated file remains connected to the Vampire clause outline.  The fill
pass also uses generated definitions plus one-step Leibniz congruence to prove
simple equality rewrites under a shared function symbol; equality-chain search
can also lift known or instantiated equality rewrites through application
arguments.  For atomic propositions, it can transport a known atom across
proved argument equalities, and it can rewrite one target argument across an
equality before applying a bounded nested rule chain.  For quantified or
implicational claims, it can introduce the binders/premises and then run the
same proof search on the resulting body.

```sh
python3 scripts/vampire_reconstruct_megalodon.py \
  --check-existing /project/tmp/megalodon_vampire_megalodon/manifest.jsonl \
  --jobs 20 \
  --check-claim-skeletons \
  --require-claim-skeletons \
  --claim-skeleton-dir /project/tmp/megalodon_vampire_claim_skeletons
```

For development iterations, avoid rediscovering solvable problems.  First keep
one manifest of Vampire-solvable TH0 files, then rerun only those files with
the current Vampire binary:

```sh
TMPDIR=/project/tmp \
VAMPIRE=/path/to/current/vampire \
python3 scripts/vampire_reconstruct_megalodon.py \
  --from-manifest /project/tmp/megalodon_vampire_megalodon_100/manifest.jsonl \
  --work-dir /project/tmp/megalodon_vampire_iteration \
  --limit 100 \
  --timeout 10 \
  --jobs 20 \
  --proof-mode megalodon \
  --check-megalodon-sources
```

This path does not rescan the full candidate pool; it reruns exactly the known
solvable problem files listed in the manifest. The driver caps Vampire timeouts
at 10 seconds even if a larger `--timeout` is passed, to avoid spending time in
unsuccessful portfolio strategies.

Megalodon mode asks Vampire for the same replay information that LeanChecker
uses (`--proof_extra lean --skolemization syntactic --shuffle_input off`) but
emits a Megalodon reconstruction outline instead of Lean syntax.  The outline
records each proof unit, its Vampire inference rule, parent unit ids, and
whether replay/substitution information was recovered.  For the currently
supported theorem fragment, Vampire also emits Megalodon source candidates
containing an `exact` proof term; the Python driver only extracts and checks
those candidates, it does not translate the proof.

Summarize the Vampire inference rules appearing in a collected manifest:

```sh
python3 scripts/vampire_proof_rule_report.py \
  /project/tmp/megalodon_vampire_reconstruction/manifest.jsonl
```

This report is intended to guide generic reconstruction work by Vampire
inference rule, rather than by Megalodon library theorem names.

Run Megalodon itself with live Vampire certification for each `aby` THF
obligation.  Use `-vampireabyproof megalodon` to exercise Vampire's
Megalodon reconstruction backend directly:

```sh
./bin/megalodon \
  -allowincompleteqed \
  -vampireaby /path/to/vampire \
  -vampireabytimeout 60 \
  -vampireabyoutdir vampire_aby \
  -vampireabyproof megalodon \
  examples/hammer/100thms_12_h.mg
```

The live mode writes the exact THF problem generated at each `aby`, runs
Vampire with the selected `-vampireabyproof` mode, and fails the Megalodon
check unless Vampire reports a proved SZS status and emits a proof payload.  In
`megalodon` mode Megalodon passes Vampire the reconstruction options
`--proof_extra lean --skolemization syntactic --shuffle_input off` and requires
the `megalodon_reconstruction_*` payload markers.  This is a strict
certificate gate for `aby`; it is not yet a native Megalodon kernel proof-term
reconstructor, so `-allowincompleteqed` is still required.  The generated THF
conjecture and selected local hypotheses are head-expanded at transparent
definitions when that exposes `forall` or `->`, while preserving native THF
equality, so definition-only goals such as subset reflexivity remain easy for
Vampire.

For the currently supported native reconstruction fragment, add
`-vampireabynative`.  This tries to turn an `aby` goal into a native Megalodon
proof term using deterministic introduction, hypothesis,
False-elimination, definitional negation introduction/application, bounded
implication-chain application, Church-encoded conjunction
projection/reconstruction, Church-encoded disjunction introduction/elimination,
Church-encoded existential introduction from bound witnesses/elimination from
local existential hypotheses, named `aby` dependencies instantiated over local
variables, and
definition-backed `iff` introduction/projection.  It also handles Leibniz
equality reflexivity plus symmetry/transitivity from matching local equality hypotheses,
unary predicate rewriting from local equality hypotheses,
direct elimination of named `iff` facts such as set constructors, the classical
double-negation pattern used to prove existential De Morgan consequences,
function/proposition extensionality for pointwise proposition equality, and the
classical NAND-to-or pattern used with named excluded middle facts.  It can also
reconstruct the replacement-over-empty argument through `Empty_eq` and
`ReplE_impred`, plus replacement extensionality subset arguments from
`ReplI`, `ReplE_impred`, and pointwise equality hypotheses; combined with
`set_ext`, this reconstructs replacement extensionality equalities.  It also
handles the inverse-replacement equality pattern using nested replacement
elimination/introduction and element-position equality rewriting, and the
`If_i_correct` choice split through `Eps_i_ax` and `xm`.  It also reconstructs
classical excluded-middle case splits that prove disjunctions, including
`If_i_or`, and the unordered-pair replacement patterns behind `UPairE`,
`UPairI1`, and `UPairI2`.  It handles binary-union introduction/elimination and
deterministic membership transport through binary-union subset/equality goals,
including the early associativity, commutativity, identity, and subset-minimality
lemmas.  Transparent definitions that expose Church-encoded disjunctions can be
eliminated as local hypotheses.  It expands the local `neq` definition, plus
transparent definitions that expose `forall` or `->`, before falling back to the
certificate admit.
When both `-vampireaby` and `-vampireabynative` are enabled, Megalodon still
emits and checks Vampire certificates when Vampire succeeds; if Vampire times
out but native reconstruction succeeds, the checked native proof is used.  Use
`-vampireabynativestrict` to fail instead of falling back when the native
fragment cannot reconstruct the goal.

Smoke-test the live Megalodon/Vampire path on the first hammer `aby`:

```sh
VAMPIRE=/path/to/vampire tests/vampire_reconstruction/run_live_aby_smoke.sh
```

Set `MEGALODON_VAMPIRE_PROOF=megalodon` to smoke-test the Vampire Megalodon
reconstruction backend through Megalodon's live `aby` path.

Smoke-test Vampire's checked Megalodon source-term fragment directly:

```sh
VAMPIRE=/path/to/vampire tests/vampire_reconstruction/run_source_fragment_smoke.sh
```

This covers input axioms, Church-encoded conjunction introduction/projection,
and Leibniz equality rewriting without rescanning the hammer problem pool.

Smoke-test the restricted native reconstruction path on the early hammer `aby`
block through the binary-union algebra lemmas:

```sh
VAMPIRE=/path/to/vampire tests/vampire_reconstruction/run_native_aby_smoke.sh
```

Useful overrides:

```sh
MEGALODON_VAMPIRE_LIMIT=100
MEGALODON_VAMPIRE_TIMEOUT=60
MEGALODON_VAMPIRE_JOBS=10
```

Outputs are written under `tests/vampire_reconstruction/work/`, including
`selected_th0.txt`, Vampire proof outputs, and `manifest.jsonl` with hashes for
the generated problems and captured proofs.
