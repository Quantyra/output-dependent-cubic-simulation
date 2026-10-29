# Published certification target

- Paper version DOI: https://doi.org/10.5281/zenodo.23754698; concept DOI: https://doi.org/10.5281/zenodo.23754697.
- Frozen GitHub release `v0.1.0`, commit `6250927ef656b03242dc7b25848bc743d8078629`; source/evidence inventory in that commit's `MANIFEST.json` and `PROVENANCE.json`.
- Published standalone PDF SHA-256: `417256a6dcbe3b42562104a2cf7302500c713257e13c5e0f5420b179f6dd0c6d`.
- DOI application and publication receipt: commit `cd9c2eeb6c1ad57208a27f8fbe1f80d610f875f1`, `publication/PUBLICATION-RECEIPT.md`.
- Target compiler: Lean 4.30.0. Compatible Mathlib revision `c5ea00351c28e24afc9f0f84379aa41082b1188f` declares Lean 4.30.0. `lakefile.toml` and `lake-manifest.json` pin it and eight transitive dependencies. The helper modules currently import Lean's `Std` only; the presence of Mathlib in the lock does not mean any Mathlib-based theorem has been built. A fresh checkout replay of the locked environment remains an S181 obligation.
- Baseline permitted axioms for later exports: `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`, project axioms or native-evaluation trust.

The statement and bridge inventory is in `CLAIMS.json`; source and bit-cost semantics are specified in `SEMANTICS.md`. `python tools/check_claims.py` checks that the published theorem labels appear in the inventory and that claimed helper proofs have audit receipts. It is not a proof or a semantic-equivalence check. Every manuscript theorem remains open. The explicitly identified auxiliary derivative lemma has been kernel checked and has no axioms, as documented in `evidence/derivative-core-audit.md`. It is only a small bridge toward Proposition 2.2, not a proof of the proposition or of any headline theorem. Empirical timings, prior-work novelty and Python implementation correctness are outside Lean's proof scope.

Source semantics must represent the literal canonical descriptor/header and replayed native body, basis input, output, Boolean ANF phases and symmetric invertible Fourier matrix. Algorithm semantics must include the actual discovery/refusal behavior and finite random tapes. The cost model must account for encoded bit length, time, storage, random bits, exact arithmetic, accuracy and confidence; unit-cost Gaussian or state-access oracles are not sufficient. These definitions and all statement bridges remain open.
