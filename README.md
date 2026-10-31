# Classical Simulation of Two-Layer Quantum Circuits via Output-Dependent Cubic Structure

**Daniel Fredriksen Â· Quantyra Inc. Â· [ORCID 0009-0002-9123-7435](https://orcid.org/0009-0002-9123-7435)**

[Read the manuscript PDF](manuscript/main.pdf) Â· [LaTeX source](manuscript/main.tex) Â· [Reproduce the checks](REPRODUCING.md) Â· [Review and limitations](REVIEW.md)

Version **0.1.0**, published as an informal methods preprint with internal mathematical and executable checks. Paper version DOI: [10.5281/zenodo.23754698](https://doi.org/10.5281/zenodo.23754698); paper concept DOI: [10.5281/zenodo.23754697](https://doi.org/10.5281/zenodo.23754697). Lean certification is in progress against the frozen paper; the current claim inventory and audit receipts are in [lean/CLAIMS.json](lean/CLAIMS.json) and [lean/evidence](lean/evidence). At Lean source commit [`a335d89`](https://github.com/Quantyra/output-dependent-cubic-simulation/commit/a335d89), the interleaved-to-canonical block assignment and phase helpers pass the dedicated Google Cloud build and exact axiom audit; [the receipt](lean/evidence/gcp/sector-52f4b4a-20261030/integrated-a335d89-02-evidence.tar.sha256) records the run. Bijection of the layout map, Walsh-sum evaluation and every manuscript theorem remain open.

The paper constructs an estimator for one output probability of a specified two-layer Boolean cubic-phase circuit. An output-derived displacement space can have a small restricted cubic control count even when specified global controls grow. Using established stabilizer norm estimation reduces the readout factor from `4^k` to `2^k`, with all source, discovery, arithmetic, random-bit and precision costs included.

General discovery retains a full-rank-anchor promise and `2^O(q^2)` cost. The implementation accepts a verified canonical native encoding; it is not a general circuit-equivalence recognizer. The larger sampling constant loses on the executed small-control examples. No practical superiority, quantum advantage, universal simulation, peer review or formal certification is claimed.

The package contains the self-contained paper, bibliography, required source dependencies, exact test receipt, historical comparison notes and provenance inventory. The current manuscript is canonical here. The private research repository remains private; all files needed by the documented reproduction command are included.

```sh
python src/check_sector_norm_sampling.py
python tools/check_package.py
tectonic --keep-logs manuscript/main.tex
```

The first command regenerates the evidence receipt, including machine-dependent timings. Follow [REPRODUCING.md](REPRODUCING.md) for clean-checkout verification without overwriting the frozen receipt.

Cite: Daniel Fredriksen, *Classical Simulation of Two-Layer Quantum Circuits via Output-Dependent Cubic Structure*, version 0.1.0, Zenodo, 2026, [doi:10.5281/zenodo.23754698](https://doi.org/10.5281/zenodo.23754698). [CITATION.cff](CITATION.cff) contains the preferred paper citation.

The [publication sequence](publication/README.md) uses a PDF-first Zenodo preprint record for the paper. GitHub's automatic Zenodo archive is its separately identified source/software companion. The independently archived [source/software companion](https://doi.org/10.5281/zenodo.23754675) has concept DOI `10.5281/zenodo.23754674`. The [Lean plan](publication/LEAN-PLAN.md) starts only after those gates.

The manuscript, bibliography, prose and evidence are **CC BY 4.0**; code in `src/` and `tools/`, and build/check configuration, is **Apache 2.0**. See [LICENSE](LICENSE), [NOTICE](NOTICE), [SOURCES.md](SOURCES.md), [INTEGRITY.md](INTEGRITY.md) and [PROVENANCE.json](PROVENANCE.json).
