# NuminaMath Lean sources

One Lean file per supplied proof candidate from the pinned NuminaMath-LEAN
release. Files preserve source bytes, including imports, options, and helpers.
`index.jsonl` maps each module to its upstream row, UUID, proof field, and hash.
Repeated UUIDs remain separate rows. Human and model variants remain separate
unless their source strings are identical within a row.

These are unverified sources, not replay-checked training records. The upstream
dataset targeted Mathlib v4.15.0; this project pins Lean v4.34.1 and a matching
Mathlib revision. Some candidates will fail to compile or replay on this version.

## Reproduce

Install uv, Git, and Elan, then run:

```sh
uv run render.py
lake exe cache get
lake env lean Numina/Human/FILE.lean
```

Choose a file from `index.jsonl`. `Numina.lean` is an empty library root;
individual candidates are independent modules and do not import one another.
Compiling that root alone does not validate the dataset.

The renderer selects human proofs marked `complete` and nonempty model proofs.
It does not rewrite proofs, repair errors, or check agreement with the upstream
problem statement. `provenance.json` records the source pin and rendering counts.

## Attribution and license

Derived from [NuminaMath-LEAN](https://huggingface.co/datasets/AI-MO/NuminaMath-LEAN)
by Project Numina, under Apache-2.0. See LICENSE and UPSTREAM.md for
attribution and the Kimina-Prover citation. The upstream dataset revision is
`51fa67f1f647ae1ecd81eef9f19306aa8a7b3a94`.
