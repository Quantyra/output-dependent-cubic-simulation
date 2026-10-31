# Recorded pair phase on interleaved coordinates

Source commit: [`33130b7d029893862fffe2d8361bb76b2ad62dbe`](https://github.com/Quantyra/output-dependent-cubic-simulation/commit/33130b7d029893862fffe2d8361bb76b2ad62dbe).

The dedicated Google Cloud builder `quantyra-sector-lean-builder-02` replayed the commit archive with Lean 4.30.0. The fresh extraction completed the integrated 2,173-job Lake build with exit code 0. The integrated `Audit.lean` run and exact `tools/check_lean_audit.py` check also passed. The new declaration reports `propext`, `Classical.choice` and `Quot.sound`; the audit contains no `sorryAx`.

The [evidence archive](gcp/sector-52f4b4a-20261031/recorded-interleaved-phase-33130b7-evidence.tar) contains the audited source files, full Lean audit output, exact axiom-checker result, source commit, source archive hash, and the completed build result excerpt. Its SHA-256 is `351b74438aa8ffec24a13613a73aa7db07f357aba9471936ed5d0eafd38e1479`, recorded in the adjacent `.sha256` file. The source archive SHA-256 is `4504414473c5707e314f3621067dd8afa557778c9788cc7d83c84e5d8ff44b54`.

This verifies the helper under its explicit bijective recorded-coordinate hypotheses. It does not prove the source phase/character bridge for the full Walsh sum, Gaussian evaluation, normalization, boundedness, or any of the seven labeled manuscript theorems.
