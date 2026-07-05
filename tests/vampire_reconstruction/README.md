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

Megalodon mode asks Vampire for the same replay information that LeanChecker
uses (`--proof_extra lean --skolemization syntactic --shuffle_input off`) but
emits a Megalodon reconstruction outline instead of Lean syntax.  The outline
records each proof unit, its Vampire inference rule, parent unit ids, and
whether replay/substitution information was recovered.  Later reconstruction
passes should replace those outline entries by Megalodon `exact` proof terms.

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
