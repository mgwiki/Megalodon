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

With a Vampire build or schedule that differs from the one used to create
`ATPresults2025`, collect the first 100 successful proofs from the candidate
pool:

```sh
VAMPIRE=/path/to/vampire tests/vampire_reconstruction/run_100_th0.sh --collect-successes
```

Run Megalodon itself with live Vampire certification for each `aby` THF
obligation:

```sh
./bin/megalodon \
  -allowincompleteqed \
  -vampireaby /path/to/vampire \
  -vampireabytimeout 60 \
  -vampireabyoutdir vampire_aby \
  examples/hammer/100thms_12_h.mg
```

The live mode writes the exact THF problem generated at each `aby`, runs
Vampire with `--proof tptp`, and fails the Megalodon check unless Vampire
reports a proved SZS status and emits a proof payload.  This is a strict
certificate gate for `aby`; it is not yet a native Megalodon kernel proof-term
reconstructor, so `-allowincompleteqed` is still required.

For the currently supported native reconstruction fragment, add
`-vampireabynative`.  This tries to turn a certified `aby` goal into a native
Megalodon proof term using deterministic introduction, hypothesis,
False-elimination, definitional negation introduction/application, bounded
implication-chain application, Church-encoded conjunction
projection/reconstruction, Church-encoded disjunction introduction/elimination,
Church-encoded existential introduction from bound witnesses/elimination from
local existential hypotheses, named `aby` dependencies instantiated over local
variables, and
definition-backed `iff` introduction/projection.  It also handles Leibniz
equality symmetry/transitivity from matching local equality hypotheses and expands
the local `neq` definition before falling back to the certificate admit.  Use
`-vampireabynativestrict` to fail instead of falling back when the native
fragment cannot reconstruct the certified proof.

Smoke-test the live Megalodon/Vampire path on the first hammer `aby`:

```sh
VAMPIRE=/path/to/vampire tests/vampire_reconstruction/run_live_aby_smoke.sh
```

Smoke-test the restricted native reconstruction path on the early hammer `aby`
block through `prop_ext_2`:

```sh
VAMPIRE=/path/to/vampire tests/vampire_reconstruction/run_native_aby_smoke.sh
```

Useful overrides:

```sh
MEGALODON_VAMPIRE_LIMIT=100
MEGALODON_VAMPIRE_TIMEOUT=60
```

Outputs are written under `tests/vampire_reconstruction/work/`, including
`selected_th0.txt`, Vampire proof outputs, and `manifest.jsonl` with hashes for
the generated problems and captured proofs.
