# Locked Lean environment and local verification

Target: https://doi.org/10.5281/zenodo.23754698, first paper; Lean 4.30.0 and the exact manifest revisions below. `lake-manifest.json` SHA-256: `ab0911ef870c1e4193db513c9766a9be167085f6222f4381f7a2aae4a0094642`.

| Package | Exact Git revision |
|---|---|
| `mathlib` | `c5ea00351c28e24afc9f0f84379aa41082b1188f` |
| `plausible` | `a456461b368b71d2accd95234832cd9c174b5437` |
| `LeanSearchClient` | `c5d5b8fe6e5158def25cd28eb94e4141ad97c843` |
| `importGraph` | `515cf9d0c00ece5e661f6de4326a53dedc1e8ea1` |
| `proofwidgets` | `a84b3e2475d5c5ab979567b1ad8aea21b764bcf8` |
| `aesop` | `558915ae105bfd8074e22d597613d1961822adc2` |
| `Qq` | `a6e6c34c4ef182f83b219a3a5a385f51f44bdc4c` |
| `batteries` | `32dc18cde3684679f3c003de608743b57498c56f` |
| `Cli` | `6b907cf12b2e445ccb7c24bc208ef04a1f39e84c` |

`lake update` completed successfully with `MATHLIB_NO_CACHE_ON_UPDATE=1`. The Mathlib source was initially populated from a local shallow mirror at the pinned commit; the tracked manifest retains the official HTTPS Git URL and exact revision. Each local checkout's HEAD was independently compared to its manifest revision. Automatic `.olean` cache download was deliberately disabled; no Mathlib source or cache is included in this repository's artifact manifest.

With this manifest in place, `lake build` exited 0 with `Build completed successfully (5 jobs)`, and `lake env lean Audit.lean` exited 0 with the same three elaborated declarations and axiom results as the core-only audit. The helper sources import `Std`, so this verifies dependency resolution and the project's core Lean modules; it does not assert a build of Mathlib's library modules.

A separate clean-checkout replay of the earlier core-only commit `6b5e070` is recorded in `clean-core-replay.md`. A fresh clean checkout of this locked nine-package environment has not yet been replayed and remains an S181 obligation. No published paper theorem or implementation correctness is certified by this setup.
