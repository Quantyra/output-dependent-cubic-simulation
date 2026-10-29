# Validation-order regression example

Target: source interface in section 2 of https://doi.org/10.5281/zenodo.23754698.
SHA-256 `lean/ModeledRecognizerExamples.lean`: `708389762fb88d2a1ed1b064f0258194aead96fb07c82135a54f701eaee46620`.
SHA-256 `tools/check_python_lean_bridge.py`: `368aba779d796e247424a0e46cfdc2556a00b1e45adf573604d6dbce58fd56db`.

For the width-one raw descriptor with first phase `[2, 2]`, Lean rejects the original descriptor, accepts the descriptor after those masks are normalized away, and its validation-first wrapper rejects the original. Python `normalize_descriptor` also rejects the original. The Lean example and the existing five Python-generated native bridge examples passed locally. These are finite regression checks, not a proof of general Python/Lean correspondence or normalized-validator preservation. All paper theorem labels remain open.
