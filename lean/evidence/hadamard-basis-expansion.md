# Computational-basis expansion for Hadamard kernel

Target: Fourier bridge in section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/HadamardBasisExpansion.lean` SHA-256 `7d3a450037b646f36aafda4235d4bf8ca9506eb3a047615ccfd60017a8f5dd4d`.

The locked Lean 4.30.0 build passed (122 jobs); nine declarations have exact transitive axioms in the project audit baseline. Lean constructs a duplicate-free exhaustive finite binary-vector list from the existing enumerator and proves it contains every vector. Any exact amplitude function equals the finite sum of its point-supported basis contributions, including at width zero. The recursive Hadamard kernel is therefore the sum of its values on those basis contributions.

The construction is an exhaustive mathematical expansion, not a polynomial-time algorithm or a cost claim. The individual basis outputs have not yet been identified with Walsh characters, nor has the exact representation been embedded in complex amplitudes. Python correspondence, sector identities, costs and all paper theorem labels remain open.
