# Source Walsh sum in interleaved coordinates

Source commit: [`85e375aba1f97609d0e785d2911427d6226701e7`](https://github.com/Quantyra/output-dependent-cubic-simulation/commit/85e375aba1f97609d0e785d2911427d6226701e7).

The dedicated Google Cloud builder replayed this exact commit archive. The integrated `lake build SectorSimulation.InterleavedCharacter SectorSimulation` completed successfully (2,174 jobs). The full `Audit.lean` run and `tools/check_lean_audit.py` passed. The audit reports no `sorryAx`. `booleanListSum_perm` and `booleanListSum_map` use no axioms; `coordinateMap_finRange_perm`, `walshWireParity_coordinateReindex`, `recordedPairInterleavedWalshSum`, and `sourceWalshSum_recorded_interleaved` report `propext`, `Classical.choice`, and `Quot.sound`.

The source Walsh theorem states that every degree-at-most-two source phase, for every binary character and a sufficient elimination fuel bound, has a generated recorded coordinate bijection under which its complete integer Walsh sum equals the corresponding interleaved even/odd pair-phase sum with transformed character. This closes the source-to-interleaved phase and character reindexing bridge for the constructed coordinates. It does not evaluate that sum in closed form, prove estimator normalization or boundedness, establish a cost bound, or certify a labeled manuscript theorem.

The [GCP evidence archive](gcp/sector-85e375a-20261031/sector-85e375a-evidence.tar) contains the audited source files, complete audit output, exact checker, build log and result, pinned environment, and source archive hash. Its SHA-256 is `e27793175e8ba6c572820cbc96bebd43d6ff7e3baf8709225896b59d4e8ea345`, recorded in the adjacent `.sha256` file. The exact source archive SHA-256 is `8e39d2a96178fcb4128ea0840f7faedb53898f5ec314c7c87d1ce195d2f310be`.

This is a helper bridge only. The frozen paper and first Zenodo release remain unchanged, and no paper theorem is certified.
