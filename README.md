# Classical Simulation of Two-Layer Quantum Circuits via Output-Dependent Cubic Structure

**Daniel Fredriksen · Quantyra Inc. · [ORCID 0009-0002-9123-7435](https://orcid.org/0009-0002-9123-7435)**

[Read the manuscript PDF](manuscript/main.pdf) · [LaTeX source](manuscript/main.tex) · [Reproduce the checks](REPRODUCING.md) · [Review and limitations](REVIEW.md)

Version **0.1.0 candidate**, prepared October 28, 2026. This is an informal methods preprint with internal mathematical and executable checks. The first tagged release and Zenodo publication are pending; no paper DOI has been assigned or verified. Lean certification has not started.

The paper constructs an estimator for one output probability of a specified two-layer Boolean cubic-phase circuit. An output-derived displacement space can have a small restricted cubic control count even when specified global controls grow. Using established stabilizer norm estimation reduces the readout factor from `4^k` to `2^k`, with all source, discovery, arithmetic, random-bit and precision costs included.

General discovery retains a full-rank-anchor promise and `2^O(q^2)` cost. The implementation accepts a verified canonical native encoding; it is not a general circuit-equivalence recognizer. The larger sampling constant loses on the executed small-control examples. No practical superiority, quantum advantage, universal simulation, peer review or formal certification is claimed.

The package contains the self-contained paper, bibliography, required source dependencies, exact test receipt, historical comparison notes and provenance inventory. The current manuscript is canonical here. The private research repository remains private; all files needed by the documented reproduction command are included.

```sh
python src/check_sector_norm_sampling.py
python tools/check_package.py
tectonic --keep-logs manuscript/main.tex
```

The first command regenerates the evidence receipt, including machine-dependent timings. Follow [REPRODUCING.md](REPRODUCING.md) for clean-checkout verification without overwriting the frozen receipt.

For citation before a DOI exists: Daniel Fredriksen, *Classical Simulation of Two-Layer Quantum Circuits via Output-Dependent Cubic Structure*, version 0.1.0 candidate, Quantyra Inc., 2026, this repository and its exact commit. [CITATION.cff](CITATION.cff) identifies the manuscript as the preferred citation. It does not fabricate a DOI or release date.

The [publication sequence](publication/README.md) uses a PDF-first Zenodo preprint record for the paper. GitHub's automatic Zenodo archive is its separately identified source/software companion. The actual paper DOI will be applied only after publication and verification. The [Lean plan](publication/LEAN-PLAN.md) starts only after those gates.

The manuscript, bibliography, prose and evidence are **CC BY 4.0**; code in `src/` and `tools/`, and build/check configuration, is **Apache 2.0**. See [LICENSE](LICENSE), [NOTICE](NOTICE), [SOURCES.md](SOURCES.md), [INTEGRITY.md](INTEGRITY.md) and [PROVENANCE.json](PROVENANCE.json).
