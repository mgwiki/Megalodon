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

Useful overrides:

```sh
MEGALODON_VAMPIRE_LIMIT=100
MEGALODON_VAMPIRE_TIMEOUT=60
```

Outputs are written under `tests/vampire_reconstruction/work/`, including
`selected_th0.txt`, Vampire proof outputs, and `manifest.jsonl` with hashes for
the generated problems and captured proofs.
