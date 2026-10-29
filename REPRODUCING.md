# Reproducing the paper and evidence

The finite mathematical checker requires Python 3.10 or newer and the standard library. The preparation environment used Python 3.13.7. Start at this repository's root. A clean checkout is recommended because the original research checker regenerates `artifacts/s175-sector-norm-checks.json`.

```sh
python tools/check_package.py
python tools/reproduce.py
```

`reproduce.py` copies only `src/` and the frozen receipt into a temporary directory, executes `check_sector_norm_sampling.py`, and compares every non-timing mathematical field against the frozen receipt. It writes a separate result under `build/` and leaves the archived evidence unchanged. Both commands are offline; no private research access or external count backend is required. Dependency modules contain earlier optional entrypoints, but those are outside this documented reproduction command.

The checker performs independent dense Z4 sums, affine pullbacks, full sector/operator identities, exhaustive equatorial moments and eight complete native-source outputs. It compares the new and retained readouts on identical descriptors, precision and confidence. The independent reference uses exact Fourier-state evolution and literal gate checks for small examples. Seeds and descriptors are in the frozen receipt. Large-b cases inspect schedules and refuse with zero sample budget; they are not completed high-precision Monte Carlo runs. Timings are single local observations and are excluded from deterministic comparison.

Build the PDF with Tectonic 0.17.0:

```sh
tectonic --keep-logs manuscript/main.tex
```

Tectonic resolves the standard TeX packages on first use; subsequent cached builds can be offline. A standard LaTeX/BibTeX toolchain can also build `manuscript/main.tex`. Changes to engine/bundle or PDF metadata can change binary hashes without changing mathematics. The distributed PDF's exact hash is in `MANIFEST.json`; release verification compares those frozen bytes rather than assuming all toolchains emit identical PDF bytes.

Metadata checks additionally use PyYAML and jsonschema, with the official CFF 1.2.0 schema. The verification receipt records the schema URL/hash and actual result; no schema is needed to execute the mathematical checks. PDF text/layout inspection used PyMuPDF 1.28.2 and rendered-page review. Source/provenance and distribution manifests use canonical Git LF bytes for text files, preventing platform newline conversions from being mistaken for source changes.

The check workflow runs package validation, mathematical reproduction and metadata validation on commits/PRs. It has no release, Zenodo or deployment step. PDF build success and visual inspection are recorded for the frozen candidate; no cloud or physical quantum experiment is involved.
